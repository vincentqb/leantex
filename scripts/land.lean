/-
`land` — the landing procedure, as a one-shot scriptable command.

  land new <name>          create and seed a worktree for agent/<name>
  land check <name>        preconditions and gates, no merge
  land <name> [--push]     land agent/<name> onto main
  land retire <name>       remove a merged, clean worktree and its branch
  land status              porcelain listing of the agent worktrees
  land --selftest          drive the pure core over scripted observations

Output is porcelain and nothing else: one `land: step=… result=…` line per
step, one `land: result=…` line at the end. Exit 0 ok, 1 gate failed,
2 precondition or conflict, 3 internal. Composition is left to the caller —
this tool never drives a terminal, never prompts, and never loops.

The decisions live in `scripts/Land.lean`; this file is only the boundary.
Every command's output is written to `$(git rev-parse --git-common-dir)/land
/<run-id>/<step>.log` and every fact the core acts on is *read back from a
file* — never from a return value a summarizer could have shortened. That is
the whole point: a coordinating agent once reported three merges, a push and
three worktrees that did not exist, having read narration instead of state.
-/
import scripts.Land

open Land

/-- Whitespace trim, spelled locally so the driver depends on nothing. -/
def trimWs (s : String) : String :=
  let cs := s.toList.dropWhile (·.isWhitespace)
  String.ofList (cs.reverse.dropWhile (·.isWhitespace)).reverse

/-- Split on runs of whitespace. Spelled over characters rather than through
a split combinator so the driver depends on no iterator API. -/
def wsSplit (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur : String := ""
  for c in s.toList do
    if c.isWhitespace then
      if !cur.isEmpty then out := cur :: out; cur := ""
    else cur := cur.push c
  if !cur.isEmpty then out := cur :: out
  return out.reverse

structure Env where
  common : String
  mainWt : String
  runDir : String
  runId : String
  /-- ISO-8601 UTC, for the ledger. -/
  ts : String
  leanEnv : Array (String × Option String)

/-- One porcelain step line. -/
def say (step : String) (result : String) (kvs : List (String × String) := []) : IO Unit :=
  IO.println <| s!"land: step={step} result={result}"
    ++ String.join (kvs.map fun (k, v) => s!" {k}={v}")

def sayFinal (v : Verdict) (kvs : List (String × String) := []) : IO Unit :=
  IO.println <| s!"land: result={v.name}"
    ++ String.join (kvs.map fun (k, x) => s!" {k}={x}")

/-- Run a command; write its output to a file inside the run directory, read
that file back, and return what the file said. The read-back is the contract:
the core is fed bytes that survived a round trip through the filesystem. -/
def sh (e : Env) (ctr : IO.Ref Nat) (step cmd : String) (args : Array String)
    (cwd : Option String := none) : IO (Nat × String) := do
  let n ← ctr.modifyGet (fun k => (k + 1, k))
  let outPath := s!"{e.runDir}/{step}.{n}.out"
  -- Flush before the spawn. Measured on the scratch repository: when an exec
  -- fails, the child flushes its inherited copy of this process' unflushed
  -- stdout buffer into the captured pipe, and those bytes come back *as the
  -- child's stdout* — the porcelain lines appeared inside a gate log, and a
  -- probe parsed that way would have read narration for state. The refusal
  -- path held (the text is not a sha, so `isSha` rejects it), but the cause
  -- is removed rather than relied upon.
  (← IO.getStdout).flush
  let r ← try
      IO.Process.output { cmd, args, cwd := cwd.map System.FilePath.mk, env := e.leanEnv }
    catch ex =>
      pure { exitCode := 127, stdout := "", stderr := s!"spawn failed: {ex}" }
  IO.FS.writeFile outPath (r.stdout ++ r.stderr)
  let back ← IO.FS.readFile outPath
  let h ← IO.FS.Handle.mk s!"{e.runDir}/{step}.log" .append
  h.putStr s!"$ ({cwd.getD "."}) {cmd} {String.intercalate " " args.toList}\n"
  h.putStr s!"exit={r.exitCode}\n{back}\n"
  return (r.exitCode.toNat, back)

def git (e : Env) (ctr : IO.Ref Nat) (step : String) (args : Array String)
    (cwd : Option String := none) : IO (Nat × String) :=
  sh e ctr step "git" args cwd

-- ## Discovery

def leanEnvVars : IO (Array (String × Option String)) := do
  let cc ← IO.getEnv "LEAN_CC"
  let lp ← IO.getEnv "LIBRARY_PATH"
  let mut out : Array (String × Option String) := #[]
  if cc.isNone then
    out := out.push ("LEAN_CC", some "/home/linuxbrew/.linuxbrew/bin/clang")
  if lp.isNone then
    let r ← try IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
            catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if r.exitCode == 0 then
      let p := trimWs r.stdout
      out := out.push ("LIBRARY_PATH", some s!"{p}/lib:{p}/lib/lean")
  return out

def mkEnv : IO (Except String Env) := do
  let leanEnv ← leanEnvVars
  let one (args : Array String) : IO (Nat × String) := do
    let r ← try IO.Process.output { cmd := "git", args }
            catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }
    return (r.exitCode.toNat, trimWs (r.stdout ++ r.stderr))
  let (c1, common) ← one #["rev-parse", "--path-format=absolute", "--git-common-dir"]
  if c1 != 0 then return .error "not inside a git repository"
  let (c2, top) ← one #["rev-parse", "--path-format=absolute", "--show-toplevel"]
  if c2 != 0 then return .error "no working tree"
  -- The main worktree is the first block of `worktree list --porcelain`.
  let (c3, wl) ← one #["worktree", "list", "--porcelain"]
  if c3 != 0 then return .error "cannot list worktrees"
  let mainWt :=
    match (wl.splitOn "\n").find? (·.startsWith "worktree ") with
    | some l => trimWs ((l.drop "worktree ".length).toString)
    | none => top
  let d ← try
      IO.Process.output
        { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%S %Y-%m-%dT%H:%M:%SZ"] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let stamps := wsSplit (if d.exitCode == 0 then d.stdout else "run -")
  let nanos ← IO.monoNanosNow
  let runId := (stamps.headD "run") ++ s!"-{nanos % 100000}"
  let ts := stamps.getD 1 "-"
  let runDir := s!"{common}/land/{runId}"
  IO.FS.createDirAll runDir
  return .ok { common, mainWt, runDir, runId, ts, leanEnv }

-- ## Worktree discovery

structure Wt where
  path : String
  branch : String
  deriving Repr, Inhabited

/-- Every worktree with its checked-out branch, parsed from the porcelain
listing written to a file. -/
def worktrees (e : Env) (ctr : IO.Ref Nat) (step : String) : IO (Array Wt) := do
  let (_, txt) ← git e ctr step #["worktree", "list", "--porcelain"]
  let mut out : Array Wt := #[]
  let mut path := ""
  for raw in txt.splitOn "\n" do
    let l := trimWs raw
    if l.startsWith "worktree " then path := trimWs ((l.drop 9).toString)
    else if l.startsWith "branch " then
      let b := trimWs ((l.drop 7).toString)
      let short := if b.startsWith "refs/heads/" then (b.drop 11).toString else b
      out := out.push { path, branch := short }
  return out

def worktreeOf (e : Env) (ctr : IO.Ref Nat) (step name : String) : IO (Option String) := do
  let wts ← worktrees e ctr step
  return (wts.find? (·.branch == s!"agent/{name}")).map (·.path)

/-- The directory a new worktree for `name` takes: a sibling of the main
worktree, prefixed `lt-`. Derived, never hardcoded, so a scratch repository
exercises the same code path. -/
def newWorktreePath (e : Env) (name : String) : IO String := do
  let pre := (← IO.getEnv "LAND_WORKTREE_PREFIX").getD "lt-"
  let parent :=
    match (e.mainWt.splitOn "/").dropLast with
    | [] => "."
    | ps => String.intercalate "/" ps
  return s!"{parent}/{pre}{name}"

-- ## Gates

/-- The gate list: the common contract's gates, then the scoreboard's check.
`absentIf` names a program whose absence makes the gate a recorded skip —
the scoreboard is built concurrently by a sibling agent. -/
structure Gate where
  name : String
  cmd : String
  args : Array String
  absentIf : Option String
  deriving Repr, Inhabited

/-- `--wfail` is how this project spells "zero warnings": scanning output for
`warning:` is unsound on a warm cache, where nothing recompiles and nothing
prints. `gates-build` does *not* take it — `Obligations` is the staging area
for open proofs and warns once per staged statement by design, which is why
the pre-commit hook builds it as a separate step without the flag. -/
def gateList : Array Gate := #[
  { name := "build", cmd := "lake", args := #["build", "--wfail"], absentIf := none },
  { name := "test", cmd := "lake", args := #["test"], absentIf := none },
  { name := "gates-build", cmd := "lake",
    args := #["build", "precommit", "owed", "cites", "Obligations"], absentIf := none },
  { name := "precommit-selftest", cmd := ".lake/build/bin/precommit",
    args := #["--selftest"], absentIf := none },
  { name := "precommit-tree", cmd := ".lake/build/bin/precommit",
    args := #["--tree"], absentIf := none },
  { name := "cites-selftest", cmd := ".lake/build/bin/cites",
    args := #["--selftest"], absentIf := none },
  { name := "cites-check", cmd := ".lake/build/bin/cites",
    args := #["--check"], absentIf := none },
  { name := "owed", cmd := "lake",
    args := #["env", "lean", "--run", "scripts/owed.lean"], absentIf := none },
  { name := "scoreboard", cmd := ".lake/build/bin/scoreboard",
    args := #["--check"], absentIf := some ".lake/build/bin/scoreboard" }]

/-- `LAND_GATES` replaces the gate list: `name=cmd arg arg;name=cmd …`, run
in the branch worktree. It exists so the whole procedure can be exercised on
a scratch repository — the brief forbids testing a landing against a real
worktree, and a scratch clone cannot afford the real gates on every scenario.
It never weakens a landing silently: an overridden run says so on its `run`
line and in its ledger record, and the core still observes each gate, so the
merge guard and its theorem are untouched. -/
def parseGateOverride (spec : String) : Array Gate :=
  let entries := (spec.splitOn ";").map trimWs |>.filter (!·.isEmpty)
  (entries.filterMap fun ent =>
    match (ent.splitOn "=") with
    | k :: rest =>
      let cmdline := wsSplit (String.intercalate "=" rest)
      match cmdline with
      | [] => none
      | c :: as => some { name := trimWs k, cmd := c, args := as.toArray,
                          absentIf := none }
    | [] => none).toArray

def effectiveGates : IO (Array Gate × Bool) := do
  match ← IO.getEnv "LAND_GATES" with
  | none => return (gateList, false)
  | some spec =>
    let gs := parseGateOverride spec
    if gs.isEmpty then return (gateList, false) else return (gs, true)

def runGate (e : Env) (ctr : IO.Ref Nat) (wt : String) (g : Gate) : IO Obs := do
  if let some probe := g.absentIf then
    if !(← System.FilePath.pathExists s!"{wt}/{probe}") then
      return .gateAbsent g.name
  let cmd := if g.cmd.startsWith "." then s!"{wt}/{g.cmd}" else g.cmd
  let (code, _) ← sh e ctr s!"gate-{g.name}" cmd g.args (some wt)
  if code != 0 then return .gateFail g.name
  return .gateOk g.name

-- ## The ledger
--
-- A JSONL file in the git common directory, not a git note on the landed
-- tip. Both survive across worktrees and add no commit to `main`; the note
-- would also travel with `git push origin refs/notes/land`. Three reasons
-- the file wins here. The query is "what happened to agent/<name> last",
-- keyed by agent name — a note is keyed by commit, so that query becomes a
-- walk. Each record points at `<run-id>/<step>.log`, which is local, so a
-- record that travelled would carry a dangling reference to evidence the
-- remote does not have. And `git notes add` is a second ref two worktrees
-- can race on, where an `O_APPEND` line to one file in the shared common
-- dir cannot. The landed tip is a *field*, so if the record must one day
-- travel, a one-way projection onto `refs/notes/land` reads this file —
-- keeping a single writer, which is the property that matters.

def jsonStr (s : String) : String :=
  let esc := s.toList.flatMap fun c =>
    if c == '"' then ['\\', '"'] else if c == '\\' then ['\\', '\\']
    else if c == '\n' then ['\\', 'n'] else [c]
  "\"" ++ String.ofList esc ++ "\""

def ledgerPath (e : Env) : String := s!"{e.common}/land/ledger.jsonl"

def writeLedger (e : Env) (rec : List (String × String)) : IO Bool := do
  try
    let line := "{" ++ String.intercalate ","
      (rec.map fun (k, v) => s!"{jsonStr k}:{jsonStr v}") ++ "}\n"
    IO.FS.createDirAll s!"{e.common}/land"
    let h ← IO.FS.Handle.mk (ledgerPath e) .append
    h.putStr line
    let back ← IO.FS.readFile (ledgerPath e)
    return (back.splitOn line).length > 1
  catch _ => return false

/-- The last ledger line for `name`, read back from the file. -/
def lastLedger (e : Env) (name : String) : IO (Option String) := do
  try
    let txt ← IO.FS.readFile (ledgerPath e)
    let key := s!"\"name\":{jsonStr name}"
    let hits := (txt.splitOn "\n").filter fun l => (l.splitOn key).length > 1
    return hits.getLast?
  catch _ => return none

def jsonField (line key : String) : Option String :=
  match (line.splitOn s!"{jsonStr key}:\"").drop 1 |>.head? with
  | none => none
  | some rest => (rest.splitOn "\"").head?

-- ## Probes

def statusClean (e : Env) (ctr : IO.Ref Nat) (step wt : String) : IO (Option Bool) := do
  let (code, out) ← git e ctr step #["status", "--porcelain"] (some wt)
  if code != 0 then return none
  return some (trimWs out).isEmpty

def revParse (e : Env) (ctr : IO.Ref Nat) (step rev : String)
    (cwd : Option String := none) : IO String := do
  let (code, out) ← git e ctr step #["rev-parse", rev] cwd
  if code != 0 then return "" else return trimWs out

-- ## The landing run

def landRun (e : Env) (name : String) (mode : Mode) (wantPush : Bool) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  let (gates, overridden) ← effectiveGates
  let mut st := State.init name mode (gates.map (·.name)) wantPush
  let mut act : Act := .probeMain
  let mut wt : String := ""
  let mut prevTip : String := ""
  say "run" "ok" [("id", e.runId), ("dir", e.runDir), ("mode",
    if mode == .check then "check" else "land"),
    ("gates", if overridden then "override" else "default")]
  while true do
    let obs : Obs ← match act with
      | .probeMain => do
        let (ch, ho) ← git e ctr "pre-main" #["rev-parse", "--abbrev-ref", "HEAD"]
          (some e.mainWt)
        let headName := if ch == 0 then trimWs ho else ""
        let clean? ← statusClean e ctr "pre-main" e.mainWt
        match clean? with
        | none => pure (.garbled "git status in the main worktree")
        | some clean => do
          prevTip := ← revParse e ctr "pre-main" "HEAD" (some e.mainWt)
          say "pre-main" (if clean && headName == "main" then "ok" else "fail")
            [("head", if headName.isEmpty then "?" else headName),
             ("dirty", if clean then "no" else "yes"),
             ("tip", if prevTip.isEmpty then "?" else prevTip)]
          pure (.mainStatus (clean && headName == "main"))
      | .probeBranch => do
        let (c, _) ← git e ctr "pre-branch"
          #["show-ref", "--verify", "--quiet", s!"refs/heads/agent/{name}"]
        if c != 0 then
          say "pre-branch" "fail" [("branch", s!"agent/{name}"), ("present", "no")]
          pure (.branchStatus false 0 0 false)
        else match ← worktreeOf e ctr "pre-branch" name with
        | none =>
          say "pre-branch" "fail" [("branch", s!"agent/{name}"), ("worktree", "none")]
          pure (.branchStatus false 0 0 false)
        | some p => do
          wt := p
          let (cc, counts) ← git e ctr "pre-branch"
            #["rev-list", "--left-right", "--count", s!"main...agent/{name}"] (some p)
          if cc != 0 then
            pure (.garbled "git rev-list --count")
          else
            match wsSplit counts with
            | [b, a] =>
              match b.toNat?, a.toNat? with
              | some behind, some ahead => do
                let clean? ← statusClean e ctr "pre-branch" p
                match clean? with
                | none => pure (.garbled "git status in the branch worktree")
                | some clean => do
                  say "pre-branch" (if ahead > 0 && clean then "ok" else "fail")
                    [("worktree", p), ("ahead", toString ahead),
                     ("behind", toString behind),
                     ("dirty", if clean then "no" else "yes")]
                  pure (.branchStatus true ahead behind clean)
              | _, _ => pure (.garbled "rev-list counts are not numbers")
            | other => pure (.garbled s!"rev-list counts: {other.length} fields")
      | .rebase => do
        let (c, _) ← git e ctr "rebase" #["rebase", "main"] (some wt)
        if c == 0 then
          say "rebase" "ok" [("onto", "main")]
          pure .rebaseOk
        else
          let (_, u) ← git e ctr "rebase"
            #["diff", "--name-only", "--diff-filter=U"] (some wt)
          let files := (u.splitOn "\n").map trimWs |>.filter (!·.isEmpty)
          if files.isEmpty then
            say "rebase" "fail" [("conflict", "none"), ("note", "rebase-failed-without-conflict")]
            pure (.garbled "rebase failed with no unmerged path")
          else
            say "rebase" "fail" [("conflict", String.intercalate "," files)]
            pure (.rebaseConflict files.toArray)
      | .gate g => do
        match gates.find? (·.name == g) with
        | none => pure (.garbled s!"no such gate {g}")
        | some gd => do
          let o ← runGate e ctr wt gd
          match o with
          | .gateOk n => say s!"gate-{n}" "ok"; pure o
          | .gateFail n => say s!"gate-{n}" "fail" [("log", s!"gate-{n}.log")]; pure o
          | .gateAbsent n =>
            say s!"gate-{n}" "skip" [("why", "program-not-built")]; pure o
          | _ => pure o
      | .fastForward => do
        let (c, _) ← git e ctr "fast-forward" #["merge", "--ff-only", s!"agent/{name}"]
          (some e.mainWt)
        if c == 0 then say "fast-forward" "ok"; pure .ffOk
        else
          say "fast-forward" "fail" [("log", "fast-forward.log")]
          pure (.garbled "git merge --ff-only")
      | .readTips => do
        let bt ← revParse e ctr "verify" s!"refs/heads/agent/{name}" (some e.mainWt)
        let mt ← revParse e ctr "verify" "HEAD" (some e.mainWt)
        say "verify" (if bt == mt && isSha mt then "ok" else "fail")
          [("branch", if bt.isEmpty then "?" else bt), ("main", if mt.isEmpty then "?" else mt)]
        pure (.tips bt mt)
      | .writeLedger => do
        let t1 ← IO.monoMsNow
        let ok ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name),
           ("verdict", "landed"), ("tip", st.landedTip), ("prev", prevTip),
           ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
           ("skipped", String.intercalate "," st.skipped.toList),
           ("pushed", if wantPush then "pending" else "no"),
           ("gateset", if overridden then "override" else "default"),
           ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        say "ledger" (if ok then "ok" else "fail") [("file", ledgerPath e)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .push => do
        let (c, _) ← git e ctr "push" #["push", "origin", "main"] (some e.mainWt)
        if c == 0 then say "push" "ok"; pure .pushOk
        else say "push" "fail" [("log", "push.log")]; pure (.garbled "git push")
      | .readOrigin => do
        let ot ← revParse e ctr "verify-push" "refs/remotes/origin/main" (some e.mainWt)
        let mt ← revParse e ctr "verify-push" "refs/heads/main" (some e.mainWt)
        say "verify-push" (if ot == mt && isSha mt then "ok" else "fail")
          [("origin", if ot.isEmpty then "?" else ot), ("main", if mt.isEmpty then "?" else mt)]
        pure (.originTips ot mt)
      | .halt .. => pure (.garbled "halt")
    let (st', act') := step st obs
    st := st'
    act := act'
    match act with
    | .halt v code why abort =>
      if abort then
        let (_, _) ← git e ctr "rebase-abort" #["rebase", "--abort"] (some wt)
        say "rebase-abort" "ok"
      let t1 ← IO.monoMsNow
      -- One record per distinct fact. The push confirmation is its own
      -- verdict, never a second `landed` row for the same run: a structured
      -- record doubled is the defect this whole tool exists to refuse.
      if v == .landed && wantPush then
        let _ ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "pushed"),
           ("tip", st.landedTip), ("remote", "origin/main"),
           ("ms", toString (t1 - t0)), ("dir", e.runDir)]
      if v != .landed && v != .checked then
        let _ ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", v.name),
           ("why", why), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
      sayFinal v <|
        [("name", name), ("gates", toString st.gates.size),
         ("skipped", toString st.skipped.size), ("ms", toString (t1 - t0))]
        ++ (if st.landedTip.isEmpty then [] else [("tip", st.landedTip)])
        ++ (if why.isEmpty then [] else [("why", why)])
      return code
    | _ => pure ()
  return 3

-- ## land new

def landNew (e : Env) (name : String) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  let path ← newWorktreePath e name
  say "run" "ok" [("id", e.runId), ("dir", e.runDir), ("mode", "new")]
  if ← System.FilePath.pathExists path then
    say "pre" "fail" [("path", path), ("why", "exists")]
    sayFinal .refused [("name", name)]
    return 2
  let (c, _) ← git e ctr "pre" #["show-ref", "--verify", "--quiet", s!"refs/heads/agent/{name}"]
  if c == 0 then
    say "pre" "fail" [("branch", s!"agent/{name}"), ("why", "exists")]
    sayFinal .refused [("name", name)]
    return 2
  say "pre" "ok" [("path", path)]
  let (ca, _) ← git e ctr "worktree-add"
    #["worktree", "add", "-b", s!"agent/{name}", path, "main"] (some e.mainWt)
  if ca != 0 then
    say "worktree-add" "fail" [("log", "worktree-add.log")]
    sayFinal .failed [("name", name)]
    return 3
  say "worktree-add" "ok" [("branch", s!"agent/{name}")]
  -- Seed the build cache from the main worktree: a seeded clean worktree
  -- builds in seconds where an unseeded one recompiles the tree. Copy, never
  -- hardlink — lake rewrites files in place, and a hardlink would corrupt the
  -- cache it was seeded from.
  if ← System.FilePath.pathExists s!"{e.mainWt}/.lake" then
    let (cs, _) ← sh e ctr "seed" "cp"
      #["-a", "--reflink=auto", s!"{e.mainWt}/.lake", s!"{path}/.lake"]
    say "seed" (if cs == 0 then "ok" else "fail") [("from", s!"{e.mainWt}/.lake")]
  else
    say "seed" "skip" [("why", "no-cache-in-main")]
  let (cb, _) ← sh e ctr "build" "lake" #["build", "--wfail"] (some path)
  if cb != 0 then
    say "build" "fail" [("log", "build.log")]
    sayFinal .failed [("name", name)]
    return 1
  let t1 ← IO.monoMsNow
  say "build" "ok" [("ms", toString (t1 - t0))]
  let head ← do
    let (c2, o) ← git e ctr "verify" #["rev-parse", "--abbrev-ref", "HEAD"] (some path)
    pure (if c2 == 0 then trimWs o else "")
  let clean ← statusClean e ctr "verify" path
  let ok := head == s!"agent/{name}" && clean == some true
  say "verify" (if ok then "ok" else "fail")
    [("head", head), ("dirty", if clean == some true then "no" else "yes")]
  if !ok then sayFinal .failed [("name", name)]; return 3
  let _ ← writeLedger e
    [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "created"),
     ("path", path), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
  sayFinal .created [("name", name), ("path", path), ("ms", toString (t1 - t0))]
  return 0

-- ## land retire

def landRetire (e : Env) (name : String) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  say "run" "ok" [("id", e.runId), ("dir", e.runDir), ("mode", "retire")]
  match ← worktreeOf e ctr "pre" name with
  | none =>
    say "pre" "fail" [("branch", s!"agent/{name}"), ("worktree", "none")]
    sayFinal .refused [("name", name)]
    return 2
  | some p =>
    match ← statusClean e ctr "pre" p with
    | none => say "pre" "fail" [("why", "status-unreadable")]
              sayFinal .failed [("name", name)]; return 3
    | some clean =>
      if !clean then
        say "pre" "fail" [("worktree", p), ("dirty", "yes")]
        sayFinal .refused [("name", name)]
        return 2
      let (cm, _) ← git e ctr "pre"
        #["merge-base", "--is-ancestor", s!"agent/{name}", "main"] (some e.mainWt)
      if cm != 0 then
        say "pre" "fail" [("branch", s!"agent/{name}"), ("merged", "no")]
        sayFinal .refused [("name", name)]
        return 2
      say "pre" "ok" [("worktree", p), ("merged", "yes")]
      let (cr, _) ← git e ctr "worktree-remove" #["worktree", "remove", p] (some e.mainWt)
      if cr != 0 then
        say "worktree-remove" "fail" [("log", "worktree-remove.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "worktree-remove" "ok" [("path", p)]
      let (cd, _) ← git e ctr "branch-delete" #["branch", "-d", s!"agent/{name}"] (some e.mainWt)
      if cd != 0 then
        say "branch-delete" "fail" [("log", "branch-delete.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "branch-delete" "ok" [("branch", s!"agent/{name}")]
      let _ ← writeLedger e
        [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "retired"),
         ("dir", e.runDir)]
      sayFinal .retired [("name", name)]
      return 0

-- ## land status

def landStatus (e : Env) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let wts ← worktrees e ctr "status"
  for w in wts do
    if !w.branch.startsWith "agent/" then continue
    let name := (w.branch.drop 6).toString
    let (cc, counts) ← git e ctr "status"
      #["rev-list", "--left-right", "--count", s!"main...{w.branch}"] (some e.mainWt)
    let (behind, ahead) :=
      if cc != 0 then ("?", "?") else
      match wsSplit counts with
      | [b, a] => (b, a)
      | _ => ("?", "?")
    let clean ← statusClean e ctr "status" w.path
    let last ← lastLedger e name
    let lastV := match last with
      | none => "none"
      | some l => (jsonField l "verdict").getD "?"
    let lastRun := match last with
      | none => "-"
      | some l => (jsonField l "run").getD "-"
    say "worktree" "ok"
      [("name", name), ("branch", w.branch), ("path", w.path),
       ("ahead", ahead), ("behind", behind),
       ("dirty", match clean with | some true => "no" | some false => "yes" | none => "?"),
       ("last", lastV), ("run", lastRun)]
  let n := (wts.filter (·.branch.startsWith "agent/")).size
  sayFinal .listed [("worktrees", toString n)]
  return 0

-- ## The selftest
--
-- The pure core, driven over scripted observation sequences. No repository is
-- touched: the point is that every refusal is a property of values.

structure Case where
  label : String
  mode : Mode
  push : Bool
  obs : List Obs
  verdict : Verdict
  code : UInt32
  /-- Must the run have proposed no ref change at all? -/
  noMutation : Bool

def gateNames : Array String := gateList.map (·.name)

def okGates : List Obs := gateNames.toList.map Obs.gateOk

def sha1s : Sha := "1111111111111111111111111111111111111111"
def sha2s : Sha := "2222222222222222222222222222222222222222"

def cases : List Case :=
  let pre := [Obs.mainStatus true, Obs.branchStatus true 1 0 true, Obs.rebaseOk]
  [ { label := "lands with every gate ok", mode := .land, push := false
    , obs := pre ++ okGates ++ [.ffOk, .tips sha1s sha1s, .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "lands and pushes, origin reads back", mode := .land, push := true
    , obs := pre ++ okGates ++ [.ffOk, .tips sha1s sha1s, .ledgerOk, .pushOk,
        .originTips sha1s sha1s]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "check stops before the merge", mode := .check, push := false
    , obs := pre ++ okGates, verdict := .checked, code := 0, noMutation := true }
  , { label := "rebase conflict in a non-union file", mode := .land, push := false
    , obs := [.mainStatus true, .branchStatus true 3 2 true,
        .rebaseConflict #["LeanTex/Core/Ir.lean", "Tests/Diag.lean"]]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a gate fails", mode := .land, push := false
    , obs := pre ++ [.gateOk "build", .gateFail "test"]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the last gate fails", mode := .land, push := true
    , obs := pre ++ (gateNames.toList.dropLast.map Obs.gateOk) ++ [.gateFail "scoreboard"]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the tip does not read back", mode := .land, push := false
    , obs := pre ++ okGates ++ [.ffOk, .tips sha1s sha2s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "a truncated sha is not a sha", mode := .land, push := false
    , obs := pre ++ okGates ++ [.ffOk, .tips "11111111" "11111111"]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "garbled status at the first probe", mode := .land, push := false
    , obs := [.garbled "git status --porcelain"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled rev-list at the branch probe", mode := .land, push := false
    , obs := [.mainStatus true, .garbled "rev-list counts"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled output mid-gate", mode := .land, push := false
    , obs := pre ++ [.gateOk "build", .garbled "gate output"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the main worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus false], verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch does not exist", mode := .land, push := false
    , obs := [.mainStatus true, .branchStatus false 0 0 false]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch is not ahead", mode := .land, push := false
    , obs := [.mainStatus true, .branchStatus true 0 4 true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus true, .branchStatus true 2 0 false]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "every gate absent proves nothing", mode := .land, push := false
    , obs := pre ++ gateNames.toList.map Obs.gateAbsent
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "an observation out of order", mode := .land, push := false
    , obs := [.mainStatus true, .ffOk]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "origin does not read back after the push", mode := .land, push := true
    , obs := pre ++ okGates ++ [.ffOk, .tips sha1s sha1s, .ledgerOk, .pushOk,
        .originTips sha2s sha1s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "the ledger was not written", mode := .land, push := true
    , obs := pre ++ okGates ++ [.ffOk, .tips sha1s sha1s, .ledgerFail]
    , verdict := .failed, code := 3, noMutation := false } ]

/-- The final halt of a scripted run: verdict and exit code. -/
def finalOf (acts : Array Act) : Option (Verdict × UInt32) :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .halt v c _ _ => some (v, c)
    | _ => acc

/-- What is wrong with a scripted case, or nothing. Pure, so the whole
selftest verdict is a function of values. -/
def caseFault (c : Case) : Option String :=
  let (fin, acts) := Land.run (State.init "probe" c.mode gateNames c.push) c.obs
  let mutated := acts.any Act.mutates
  match finalOf acts with
  | none => some "the run never halted"
  | some (v, code) =>
    if v != c.verdict then some s!"verdict-{v.name}-wanted-{c.verdict.name}"
    else if code != c.code then some s!"exit-{code}-wanted-{c.code}"
    else if c.noMutation && mutated then some "proposed a ref change"
    else if mutated && !fin.proven then some "mutated with an unproven run"
    else none

def selftest : IO UInt32 := do
  let mut bad := 0
  for c in cases do
    match caseFault c with
    | some why =>
      bad := bad + 1
      say "selftest" "fail" [("case", c.label), ("why", why)]
    | none => say "selftest" "ok" [("case", c.label)]
  -- The theorem, exercised: no scripted run proposes a ref change whose
  -- state is not `proven`. The proof is in Land.lean; this is the witness
  -- that the cases reach the guarded branch at all.
  let anyMutating := cases.any fun c =>
    (Land.run (State.init "probe" c.mode gateNames c.push) c.obs).2.any Act.mutates
  if !anyMutating then
    bad := bad + 1
    say "selftest" "fail" [("case", "coverage"), ("why", "no case reaches a merge")]
  else say "selftest" "ok" [("case", "a merge is reachable")]
  if bad == 0 then sayFinal .checked [("cases", toString cases.length)]; return 0
  else sayFinal .failed [("cases", toString cases.length), ("bad", toString bad)]; return 1

-- ## Entry

def usage : String :=
  "usage: land new <name> | land check <name> | land <name> [--push] | \
land retire <name> | land status | land --selftest"

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] => IO.eprintln usage; return 3
  | ["--selftest"] => selftest
  | args => do
    match ← mkEnv with
    | .error e => IO.eprintln s!"land: {e}"; return 3
    | .ok env =>
      match args with
      | ["status"] => landStatus env
      | ["new", n] => landNew env n
      | ["retire", n] => landRetire env n
      | ["check", n] => landRun env n .check false
      | [n] => landRun env n .land false
      | [n, "--push"] => landRun env n .land true
      | _ => IO.eprintln usage; return 3
