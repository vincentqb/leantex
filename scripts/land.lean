/-
`land` — the landing procedure, as a one-shot scriptable command.

  land new <name>          create and seed a worktree for agent/<name>
  land check <name>        preconditions and gates, no merge
  land <name> [--push]     land agent/<name> onto main
  land retire <name>       remove a merged, clean worktree and its branch
  land status              porcelain listing of the agent worktrees
  land --selftest          drive the pure core over scripted observations
  land --scratch-selftest  drive the driver against throwaway repositories

Output is porcelain and nothing else: one `land: step=… result=…` line per
step, one `land: result=…` line at the end. A value carrying whitespace or a
quote is quoted, so a `k=v` reader cannot be walked off the end of a value.
Exit 0 ok, 1 gate failed, 2 precondition or conflict, 3 internal.
Composition is left to the caller — this tool never drives a terminal, never
prompts, and never loops.

The decisions live in `scripts/LandCore.lean`; this file is only the
boundary. Every command's output is written to
`$(git rev-parse --git-common-dir)/land/<run-id>/<step>.log` and every fact
the core acts on is *read back from a file* — never from a return value a
summarizer could have shortened. Standard output and standard error go to
separate files and only standard output is parsed: a git warning on stderr
once became part of a "fact" and reported a clean worktree as dirty.
-/
import scripts.LandCore

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
  childEnv : Array (String × Option String)

/-- A porcelain value: quoted when it holds whitespace, a quote, or nothing
at all. Every `why` holds spaces and a conflicted path may, so an unquoted
`k=v` line cannot be parsed back. -/
def pv (v : String) : String :=
  let needs := v.isEmpty || v.any fun c => c.isWhitespace || c == '"' || c == '\\'
  if !needs then v else
    let esc := v.toList.flatMap fun c =>
      if c == '"' || c == '\\' then ['\\', c]
      else if c == '\n' then ['\\', 'n']
      else if c == '\t' then ['\\', 't']
      else [c]
    "\"" ++ String.ofList esc ++ "\""

/-- One porcelain step line. -/
def say (step : String) (result : String) (kvs : List (String × String) := []) : IO Unit :=
  IO.println <| s!"land: step={step} result={result}"
    ++ String.join (kvs.map fun (k, v) => s!" {k}={pv v}")

def sayFinal (v : Verdict) (kvs : List (String × String) := []) : IO Unit :=
  IO.println <| s!"land: result={v.name}"
    ++ String.join (kvs.map fun (k, x) => s!" {k}={pv x}")

/-- What one command produced: its exit code, its standard output, and its
standard error — kept apart, because only the first is a fact about the
repository. -/
structure Ran where
  code : Nat
  out : String
  err : String

/-- Run a command; write its two streams to separate files inside the run
directory, read them back, and return what the files said. The read-back is
the contract: the core is fed bytes that survived a round trip through the
filesystem. Children get a null standard input and `GIT_TERMINAL_PROMPT=0`,
so a command that would ask a human instead fails. -/
def sh (e : Env) (ctr : IO.Ref Nat) (step cmd : String) (args : Array String)
    (cwd : Option String := none) : IO Ran := do
  let n ← ctr.modifyGet (fun k => (k + 1, k))
  let outPath := s!"{e.runDir}/{step}.{n}.out"
  let errPath := s!"{e.runDir}/{step}.{n}.err"
  -- Flush before the spawn. Measured on the scratch repository: when an exec
  -- fails, the child flushes its inherited copy of this process' unflushed
  -- stdout buffer into the captured pipe, and those bytes come back *as the
  -- child's stdout* — the porcelain lines appeared inside a gate log, and a
  -- probe parsed that way would have read narration for state. The refusal
  -- path held (the text is not a sha, so `isSha` rejects it), but the cause
  -- is removed rather than relied upon.
  (← IO.getStdout).flush
  let r ← try
      IO.Process.output
        { cmd, args, cwd := cwd.map System.FilePath.mk, env := e.childEnv,
          stdin := .null }
    catch ex =>
      pure { exitCode := 127, stdout := "", stderr := s!"spawn failed: {ex}" }
  IO.FS.writeFile outPath r.stdout
  IO.FS.writeFile errPath r.stderr
  let out ← IO.FS.readFile outPath
  let err ← IO.FS.readFile errPath
  let h ← IO.FS.Handle.mk s!"{e.runDir}/{step}.log" .append
  h.putStr s!"$ ({cwd.getD "."}) {cmd} {String.intercalate " " args.toList}\n"
  h.putStr s!"exit={r.exitCode}\n--- stdout\n{out}--- stderr\n{err}\n"
  h.flush
  return { code := r.exitCode.toNat, out, err }

def git (e : Env) (ctr : IO.Ref Nat) (step : String) (args : Array String)
    (cwd : Option String := none) : IO Ran :=
  sh e ctr step "git" args cwd

-- ## Discovery

def childEnvVars : IO (Array (String × Option String)) := do
  let cc ← IO.getEnv "LEAN_CC"
  let lp ← IO.getEnv "LIBRARY_PATH"
  -- Never inherited: a child that can prompt can hang a scripted landing.
  let mut out : Array (String × Option String) := #[("GIT_TERMINAL_PROMPT", some "0")]
  if cc.isNone then
    out := out.push ("LEAN_CC", some "/home/linuxbrew/.linuxbrew/bin/clang")
  if lp.isNone then
    let r ← try IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
            catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if r.exitCode == 0 then
      let p := trimWs r.stdout
      out := out.push ("LIBRARY_PATH", some s!"{p}/lib:{p}/lib/lean")
  return out

/-- The run directory has to exist before anything can be logged, so the
three probes that locate it are the only commands outside `sh`. They are
written back to `bootstrap.log` as soon as the directory exists, which is
what keeps the "every fact from a file" claim true of them too. -/
def mkEnv : IO (Except String Env) := do
  let childEnv ← childEnvVars
  let trace ← IO.mkRef ""
  let one (args : Array String) : IO (Nat × String) := do
    let r ← try IO.Process.output { cmd := "git", args, env := childEnv, stdin := .null }
            catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }
    trace.modify fun t =>
      t ++ s!"$ git {String.intercalate " " args.toList}\nexit={r.exitCode}\n"
        ++ s!"--- stdout\n{r.stdout}--- stderr\n{r.stderr}\n"
    return (r.exitCode.toNat, trimWs r.stdout)
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
  IO.FS.writeFile s!"{runDir}/bootstrap.log" (← trace.get)
  return .ok { common, mainWt, runDir, runId, ts, childEnv }

/-- Keep the newest run directories and drop the rest. Eleven directories
and 58 KB of gate logs accumulated in one scratch session with nothing
removing them; run ids are timestamp-prefixed, so newest is last by name. -/
def rmQuiet (p : System.FilePath) : IO Unit := do
  try IO.FS.removeDirAll p catch _ => pure ()

def retainRuns (e : Env) (keep : Nat) : IO Unit := do
  let base : System.FilePath := s!"{e.common}/land"
  let entries ← try base.readDir catch _ => pure #[]
  let mut names : Array String := #[]
  for d in entries do
    let n := d.fileName
    if n != "lock" && n != "ledger.jsonl" then
      let isDir ← try (base / n).isDir catch _ => pure false
      if isDir then names := names.push n
  let sorted := names.qsort (· < ·)
  if sorted.size > keep then
    for i in [0:sorted.size - keep] do
      rmQuiet (base / sorted[i]!)

-- ## Worktree discovery

structure Wt where
  path : String
  branch : String
  deriving Repr, Inhabited

/-- Every worktree with its checked-out branch, parsed from the porcelain
listing written to a file. -/
def worktrees (e : Env) (ctr : IO.Ref Nat) (step : String) : IO (Array Wt) := do
  let r ← git e ctr step #["worktree", "list", "--porcelain"]
  let mut out : Array Wt := #[]
  let mut path := ""
  for raw in r.out.splitOn "\n" do
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

/-- One gate. `needsTarget` names a lake target whose *absence from the
branch's lakefile* makes the gate a recorded skip — the only permitted
absence, and the one a sibling agent's unlanded target needs. A binary that
is merely unbuilt is not an absence: the gate builds what it runs. -/
structure Gate where
  name : String
  cmd : String
  args : Array String
  needsTarget : Option String
  deriving Repr, Inhabited

/-- `--wfail` is how this project spells "zero warnings": scanning output for
`warning:` is unsound, because a warm cache replays a module's logged warning
without recompiling it and a scan of a quiet build proves nothing about the
module that did not rebuild. The flag is written out here per gate rather
than inherited from another gate's internals: `land`'s own theorem and the
gate scripts are built under it, and `Obligations` — the staging area for
open proofs, which warns once per staged statement by design — is a separate
build without it, as the pre-commit hook already does. -/
def gateList : Array Gate := #[
  { name := "build", cmd := "lake",
    args := #["build", "--wfail", "leantex", "precommit", "owed", "cites", "land"],
    needsTarget := none },
  { name := "obligations-build", cmd := "lake",
    args := #["build", "Obligations"], needsTarget := none },
  { name := "test", cmd := "lake", args := #["test"], needsTarget := none },
  { name := "land-selftest", cmd := ".lake/build/bin/land",
    args := #["--selftest"], needsTarget := none },
  { name := "land-scenarios", cmd := ".lake/build/bin/land",
    args := #["--scratch-selftest"], needsTarget := none },
  { name := "precommit-selftest", cmd := ".lake/build/bin/precommit",
    args := #["--selftest"], needsTarget := none },
  { name := "precommit-tree", cmd := ".lake/build/bin/precommit",
    args := #["--tree"], needsTarget := none },
  { name := "cites-selftest", cmd := ".lake/build/bin/cites",
    args := #["--selftest"], needsTarget := none },
  { name := "cites-check", cmd := ".lake/build/bin/cites",
    args := #["--check"], needsTarget := none },
  { name := "owed", cmd := "lake",
    args := #["env", "lean", "--run", "scripts/owed.lean"], needsTarget := none },
  { name := "scoreboard-build", cmd := "lake",
    args := #["build", "scoreboard"], needsTarget := some "scoreboard" },
  { name := "scoreboard-check", cmd := ".lake/build/bin/scoreboard",
    args := #["--check"], needsTarget := some "scoreboard" }]

/-- Malformed entries in a `LAND_GATES` override, or the empty array. -/
inductive GateSpecError where
  | empty
  | malformed (entry : String)
  | duplicate (name : String)

def GateSpecError.why : GateSpecError → String
  | .empty => "LAND_GATES is set but declares no gate"
  | .malformed e => s!"LAND_GATES entry is not name=command: {e}"
  | .duplicate n => s!"LAND_GATES names {n} twice"

/-- `LAND_GATES` replaces the gate list: `name=cmd arg arg;name=cmd …`, run
in the branch worktree. It exists so the whole procedure can be exercised on
a scratch repository — a landing may not be tested against a real worktree,
and a scratch clone cannot afford the real gates on every scenario. Parsing
is strict: an entry without `=` and a repeated name are refusals, because a
dropped entry once ran one gate under a report of two and a repeated name
ran the first gate twice while the second never ran at all. -/
def parseGateOverride (spec : String) : Except GateSpecError (Array Gate) := do
  let entries := (spec.splitOn ";").map trimWs |>.filter (!·.isEmpty)
  let mut out : Array Gate := #[]
  for ent in entries do
    match ent.splitOn "=" with
    | k :: rest =>
      let nm := trimWs k
      match wsSplit (String.intercalate "=" rest) with
      | [] => throw (.malformed ent)
      | c :: as =>
        if nm.isEmpty then throw (.malformed ent)
        if out.any (·.name == nm) then throw (.duplicate nm)
        out := out.push { name := nm, cmd := c, args := as.toArray, needsTarget := none }
    | [] => throw (.malformed ent)
  if out.isEmpty then throw .empty
  return out

/-- Is the gate override permitted here? Only in a repository that opted in
with `git config --local land.allowGateOverride true`. An exported variable
is inherited by every later command in a shell, so an override that any
repository honoured was one stray `export` away from weakening every landing
on the machine. -/
def overrideAllowed (e : Env) (ctr : IO.Ref Nat) : IO Bool := do
  let r ← git e ctr "gateset" #["config", "--local", "--get", "land.allowGateOverride"]
  return r.code == 0 && trimWs r.out == "true"

/-- Does the branch's lakefile declare this lake target? The scoreboard's
gate is skipped only when the answer is no — never because its binary
happens to be unbuilt, which would have skipped it forever once the
scoreboard landed. -/
def lakefileDeclares (wt target : String) : IO Bool := do
  try
    let txt ← IO.FS.readFile s!"{wt}/lakefile.toml"
    return (txt.splitOn s!"name = \"{target}\"").length > 1
  catch _ => return false

def runGate (e : Env) (ctr : IO.Ref Nat) (wt : String) (g : Gate) (idx : Nat) : IO Obs := do
  if let some tgt := g.needsTarget then
    if !(← lakefileDeclares wt tgt) then
      return .gateAbsent idx
  let cmd := if g.cmd.startsWith "." then s!"{wt}/{g.cmd}" else g.cmd
  let r ← sh e ctr s!"gate-{g.name}" cmd g.args (some wt)
  if r.code != 0 then return .gateFail idx
  return .gateOk idx

-- ## The ledger

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A JSON string. Every control character is escaped, not only the three a
first draft covered: one stray byte in a git message made the whole ledger
unparseable. -/
def jsonStr (s : String) : String :=
  let esc := s.toList.flatMap fun c =>
    if c == '"' then ['\\', '"']
    else if c == '\\' then ['\\', '\\']
    else if c == '\n' then ['\\', 'n']
    else if c == '\r' then ['\\', 'r']
    else if c == '\t' then ['\\', 't']
    else if c.toNat < 0x20 || c.toNat == 0x7f then
      ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
    else [c]
  "\"" ++ String.ofList esc ++ "\""

def ledgerPath (e : Env) : String := s!"{e.common}/land/ledger.jsonl"

def writeLedger (e : Env) (rec : List (String × String)) : IO Bool := do
  try
    let line := "{" ++ String.intercalate ","
      (rec.map fun (k, v) => s!"{jsonStr k}:{jsonStr v}") ++ "}\n"
    IO.FS.createDirAll s!"{e.common}/land"
    let h ← IO.FS.Handle.mk (ledgerPath e) .append
    h.putStr line
    -- Flushed rather than left to the handle going out of scope: the
    -- read-back below is the check that the row is on disk.
    h.flush
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
  let r ← git e ctr step #["status", "--porcelain"] (some wt)
  if r.code != 0 then return none
  return some (trimWs r.out).isEmpty

def revParse (e : Env) (ctr : IO.Ref Nat) (step rev : String)
    (cwd : Option String := none) : IO String := do
  let r ← git e ctr step #["rev-parse", rev] cwd
  if r.code != 0 then return "" else return trimWs r.out

/-- Is the worktree's `HEAD` the named branch? Read from `symbolic-ref`, so a
detached `HEAD` is a no rather than a name that happens not to match. -/
def headIs (e : Env) (ctr : IO.Ref Nat) (step wt branchRef : String) : IO Bool := do
  let r ← git e ctr step #["symbolic-ref", "--quiet", "HEAD"] (some wt)
  return r.code == 0 && trimWs r.out == branchRef

/-- Is a rebase in progress in this worktree? -/
def midRebase (e : Env) (ctr : IO.Ref Nat) (step wt : String) : IO Bool := do
  let a ← git e ctr step #["rev-parse", "--git-path", "rebase-merge"] (some wt)
  let b ← git e ctr step #["rev-parse", "--git-path", "rebase-apply"] (some wt)
  let ex (r : Ran) : IO Bool := do
    if r.code != 0 then return false
    let p := trimWs r.out
    if p.isEmpty then return false
    -- `--git-path` answers relative to the worktree it ran in.
    let abs := if p.startsWith "/" then p else s!"{wt}/{p}"
    System.FilePath.pathExists abs
  return (← ex a) || (← ex b)

-- ## The landing run

def landRun (e : Env) (name : String) (mode : Mode) (wantPush : Bool)
    (gates : Array Gate) (gateset : String) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  let plan : Array GateSpec :=
    gates.map fun g => { name := g.name, mayAbsent := g.needsTarget.isSome }
  let mut st := State.init name mode plan wantPush
  let mut act : Act := .probeMain
  let mut wt : String := ""
  let mut branchBefore : String := ""
  say "run" "ok" [("id", e.runId), ("dir", e.runDir), ("mode",
    if mode == .check then "check" else "land"), ("gateset", gateset)]
  while true do
    let obs : Obs ← match act with
      | .probeMain => do
        let onMain ← headIs e ctr "pre-main" e.mainWt "refs/heads/main"
        let clean? ← statusClean e ctr "pre-main" e.mainWt
        match clean? with
        | none => pure (.garbled "git status in the main worktree")
        | some clean => do
          let tip ← revParse e ctr "pre-main" "refs/heads/main" (some e.mainWt)
          say "pre-main" (if onMain && clean then "ok" else "fail")
            [("head", if onMain then "main" else "not-main"),
             ("dirty", if clean then "no" else "yes"),
             ("tip", if tip.isEmpty then "?" else tip)]
          pure (.mainStatus onMain clean tip)
      | .probeBranch => do
        let r ← git e ctr "pre-branch"
          #["show-ref", "--verify", "--quiet", s!"refs/heads/agent/{name}"]
        if r.code != 0 then
          say "pre-branch" "fail" [("branch", s!"agent/{name}"), ("present", "no")]
          pure (.branchAbsent .noBranch)
        else match ← worktreeOf e ctr "pre-branch" name with
        | none =>
          say "pre-branch" "fail" [("branch", s!"agent/{name}"), ("worktree", "none")]
          pure (.branchAbsent .noWorktree)
        | some p => do
          wt := p
          let rc ← git e ctr "pre-branch"
            #["rev-list", "--left-right", "--count", s!"main...agent/{name}"] (some p)
          if rc.code != 0 then
            pure (.garbled "git rev-list --count")
          else
            match wsSplit rc.out with
            | [b, a] =>
              match b.toNat?, a.toNat? with
              | some behind, some ahead => do
                let clean? ← statusClean e ctr "pre-branch" p
                match clean? with
                | none => pure (.garbled "git status in the branch worktree")
                | some clean => do
                  let tip ← revParse e ctr "pre-branch" s!"refs/heads/agent/{name}" (some p)
                  branchBefore := tip
                  say "pre-branch" (if ahead > 0 && clean then "ok" else "fail")
                    [("worktree", p), ("ahead", toString ahead),
                     ("behind", toString behind),
                     ("dirty", if clean then "no" else "yes"),
                     ("tip", if tip.isEmpty then "?" else tip)]
                  pure (.branchStatus ahead behind clean tip)
              | _, _ => pure (.garbled "rev-list counts are not numbers")
            | other => pure (.garbled s!"rev-list counts: {other.length} fields")
      | .rebase => do
        let r ← git e ctr "rebase" #["rebase", "main"] (some wt)
        if r.code == 0 then
          let tip ← revParse e ctr "rebase" s!"refs/heads/agent/{name}" (some wt)
          say "rebase" "ok" [("onto", "main"), ("tip", if tip.isEmpty then "?" else tip)]
          pure (.rebaseOk tip)
        else
          -- Any non-zero rebase: collect the unmerged paths, abort if a
          -- rebase is in progress, then *read back* what was left behind.
          -- A signing failure or an I/O error mid-pick stops the rebase
          -- with no unmerged path, and reporting that as garbled output
          -- once left a worktree detached with a staged file.
          let ru ← git e ctr "rebase" #["diff", "--name-only", "--diff-filter=U"] (some wt)
          let files := (ru.out.splitOn "\n").map trimWs |>.filter (!·.isEmpty)
          if ← midRebase e ctr "rebase-abort" wt then
            let _ ← git e ctr "rebase-abort" #["rebase", "--abort"] (some wt)
            pure ()
          let headTip ← revParse e ctr "rebase-abort" "HEAD" (some wt)
          let onBranch ← headIs e ctr "rebase-abort" wt s!"refs/heads/agent/{name}"
          let clean? ← statusClean e ctr "rebase-abort" wt
          let clean := clean? == some true
          let restored := onBranch && clean && headTip == branchBefore
          say "rebase-abort" (if restored then "ok" else "fail")
            [("head", if headTip.isEmpty then "?" else headTip),
             ("was", if branchBefore.isEmpty then "?" else branchBefore),
             ("branch", if onBranch then "yes" else "no"),
             ("dirty", if clean then "no" else "yes")]
          say "rebase" "fail"
            [("conflict", if files.isEmpty then "none" else String.intercalate "," files)]
          pure (.rebaseFailed files.toArray headTip onBranch clean)
      | .gate i g => do
        match gates[i]? with
        | none => pure (.garbled s!"no gate at index {i}")
        | some gd => do
          let o ← runGate e ctr wt gd i
          match o with
          | .gateOk _ => say s!"gate-{g}" "ok" [("idx", toString i)]; pure o
          | .gateFail _ =>
            say s!"gate-{g}" "fail" [("idx", toString i), ("log", s!"gate-{g}.log")]; pure o
          | .gateAbsent _ =>
            say s!"gate-{g}" "skip"
              [("idx", toString i), ("why", "the lakefile declares no such target")]
            pure o
          | _ => pure o
      | .recheckBranch => do
        let tip ← revParse e ctr "post-gate" s!"refs/heads/agent/{name}" (some wt)
        let clean? ← statusClean e ctr "post-gate" wt
        let clean := clean? == some true
        say "post-gate" (if tip == st.gatedTip && clean then "ok" else "fail")
          [("tip", if tip.isEmpty then "?" else tip), ("gated", st.gatedTip),
           ("dirty", if clean then "no" else "yes")]
        pure (.branchRecheck tip clean)
      | .recheckMain => do
        let onMain ← headIs e ctr "pre-merge" e.mainWt "refs/heads/main"
        let tip ← revParse e ctr "pre-merge" "refs/heads/main" (some e.mainWt)
        say "pre-merge" (if onMain && tip == st.prevMainTip then "ok" else "fail")
          [("head", if onMain then "main" else "not-main"),
           ("tip", if tip.isEmpty then "?" else tip), ("was", st.prevMainTip)]
        pure (.mainRecheck onMain tip)
      | .writeLanding => do
        let t1 ← IO.monoMsNow
        let ok ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "landing"),
           ("gated", st.gatedTip), ("prev", st.prevMainTip),
           ("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        say "announce" (if ok then "ok" else "fail") [("gated", st.gatedTip)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .fastForward tip => do
        let r ← git e ctr "fast-forward" #["merge", "--ff-only", tip] (some e.mainWt)
        if r.code == 0 then say "fast-forward" "ok" [("to", tip)]; pure .ffOk
        else
          say "fast-forward" "fail" [("to", tip), ("log", "fast-forward.log")]
          pure .ffRejected
      | .readMain => do
        let mt ← revParse e ctr "verify" "refs/heads/main" (some e.mainWt)
        say "verify" (if mt == st.gatedTip && isSha mt then "ok" else "fail")
          [("main", if mt.isEmpty then "?" else mt), ("gated", st.gatedTip)]
        pure (.mainTip mt)
      | .writeLanded => do
        let t1 ← IO.monoMsNow
        let ok ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name),
           ("verdict", "landed"), ("tip", st.mainAt), ("gated", st.gatedTip),
           ("prev", st.prevMainTip),
           ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
           ("skipped", String.intercalate "," st.skipped.toList),
           ("pushed", if wantPush then "pending" else "no"),
           ("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        say "ledger" (if ok then "ok" else "fail") [("file", ledgerPath e)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .push => do
        let r ← git e ctr "push" #["push", "origin", "main"] (some e.mainWt)
        if r.code == 0 then say "push" "ok"; pure .pushOk
        else say "push" "fail" [("log", "push.log")]; pure .pushRejected
      | .readRemote => do
        -- `git ls-remote`, not the tracking ref: git updates `origin/main`
        -- from its own push result, so comparing against it asks the push
        -- whether the push worked.
        let r ← git e ctr "verify-push"
          #["ls-remote", "origin", "refs/heads/main"] (some e.mainWt)
        let ot := match wsSplit r.out with
          | sha :: _ => sha
          | [] => ""
        say "verify-push" (if ot == st.mainAt && isSha ot then "ok" else "fail")
          [("remote", if ot.isEmpty then "?" else ot), ("landed", st.mainAt)]
        pure (.remoteTip ot)
      | .halt .. => pure (.garbled "halt")
    let (st', act') := step st obs
    st := st'
    act := act'
    match act with
    | .halt v code why =>
      let t1 ← IO.monoMsNow
      -- One record per distinct fact. The push confirmation is its own
      -- verdict, never a second `landed` row for the same run: a structured
      -- record doubled is the defect this whole tool exists to refuse.
      let base := [("ts", e.ts), ("run", e.runId), ("name", name)]
      let tail := [("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
      if v == .landed && wantPush then
        let ok ← writeLedger e (base ++ [("verdict", "pushed"), ("tip", st.mainAt),
          ("gated", st.gatedTip), ("remote", "origin/main")] ++ tail)
        if !ok then say "ledger" "fail" [("row", "pushed")]
      if v == .checked then
        let ok ← writeLedger e (base ++ [("verdict", "checked"), ("gated", st.gatedTip),
          ("prev", branchBefore),
          ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
          ("skipped", String.intercalate "," st.skipped.toList)] ++ tail)
        if !ok then say "ledger" "fail" [("row", "checked")]
      if v == .refused || v == .failed || v == .landedUnpushed then
        let ok ← writeLedger e (base ++ [("verdict", v.name), ("why", why),
          ("gated", st.gatedTip)] ++ tail)
        if !ok then say "ledger" "fail" [("row", v.name)]
      sayFinal v <|
        [("name", name), ("gateset", gateset), ("gates", toString st.gates.size),
         ("skipped", toString st.skipped.size), ("ms", toString (t1 - t0))]
        ++ (if st.gatedTip.isEmpty then [] else [("gated", st.gatedTip)])
        ++ (if st.mainAt.isEmpty then [] else [("tip", st.mainAt)])
        ++ (if branchBefore.isEmpty || mode != .check then []
            else [("was", branchBefore)])
        ++ (if why.isEmpty then [] else [("why", why)])
      return code
    | _ => pure ()
  return 3

/-- One landing at a time. The lock is a directory, because creating one is
atomic where a "does it exist" check followed by a write is not; a second
concurrent landing used to reach the fast-forward and fail there under a
misdiagnosis. -/
def withLock (e : Env) (act : IO UInt32) : IO UInt32 := do
  let lock : System.FilePath := s!"{e.common}/land/lock"
  let got ← try
      IO.FS.createDir lock
      pure true
    catch _ => pure false
  if !got then
    let owner ← try IO.FS.readFile (lock / "owner") catch _ => pure "?"
    say "lock" "fail" [("path", lock.toString), ("owner", trimWs owner)]
    sayFinal .refused [("why", "another landing holds the lock")]
    return 2
  try IO.FS.writeFile (lock / "owner") s!"{e.runId}\n" catch _ => pure ()
  let r ← try act catch ex => do
    IO.eprintln s!"land: {ex}"
    pure 3
  try IO.FS.removeDirAll lock catch _ => pure ()
  return r

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
  let r ← git e ctr "pre" #["show-ref", "--verify", "--quiet", s!"refs/heads/agent/{name}"]
  if r.code == 0 then
    say "pre" "fail" [("branch", s!"agent/{name}"), ("why", "exists")]
    sayFinal .refused [("name", name)]
    return 2
  say "pre" "ok" [("path", path)]
  let ra ← git e ctr "worktree-add"
    #["worktree", "add", "-b", s!"agent/{name}", path, "main"] (some e.mainWt)
  if ra.code != 0 then
    say "worktree-add" "fail" [("log", "worktree-add.log")]
    sayFinal .failed [("name", name)]
    return 3
  say "worktree-add" "ok" [("branch", s!"agent/{name}")]
  -- Seed the build cache from the main worktree: a seeded clean worktree
  -- builds in seconds where an unseeded one recompiles the tree. Copy, never
  -- hardlink — lake rewrites files in place, and a hardlink would corrupt the
  -- cache it was seeded from.
  if ← System.FilePath.pathExists s!"{e.mainWt}/.lake" then
    let rs ← sh e ctr "seed" "cp"
      #["-a", "--reflink=auto", s!"{e.mainWt}/.lake", s!"{path}/.lake"]
    say "seed" (if rs.code == 0 then "ok" else "fail") [("from", s!"{e.mainWt}/.lake")]
  else
    say "seed" "skip" [("why", "no cache in the main worktree")]
  let rb ← sh e ctr "build" "lake" #["build", "--wfail"] (some path)
  if rb.code != 0 then
    say "build" "fail" [("log", "build.log")]
    sayFinal .failed [("name", name)]
    return 1
  let t1 ← IO.monoMsNow
  say "build" "ok" [("ms", toString (t1 - t0))]
  let onBranch ← headIs e ctr "verify" path s!"refs/heads/agent/{name}"
  let clean ← statusClean e ctr "verify" path
  let ok := onBranch && clean == some true
  say "verify" (if ok then "ok" else "fail")
    [("head", if onBranch then s!"agent/{name}" else "?"),
     ("dirty", if clean == some true then "no" else "yes")]
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
    | none => say "pre" "fail" [("why", "the status could not be read")]
              sayFinal .failed [("name", name)]; return 3
    | some clean =>
      if !clean then
        say "pre" "fail" [("worktree", p), ("dirty", "yes")]
        sayFinal .refused [("name", name)]
        return 2
      let rm ← git e ctr "pre"
        #["merge-base", "--is-ancestor", s!"agent/{name}", "main"] (some e.mainWt)
      if rm.code != 0 then
        say "pre" "fail" [("branch", s!"agent/{name}"), ("merged", "no")]
        sayFinal .refused [("name", name)]
        return 2
      say "pre" "ok" [("worktree", p), ("merged", "yes")]
      let rr ← git e ctr "worktree-remove" #["worktree", "remove", p] (some e.mainWt)
      if rr.code != 0 then
        say "worktree-remove" "fail" [("log", "worktree-remove.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "worktree-remove" "ok" [("path", p)]
      let rd ← git e ctr "branch-delete" #["branch", "-d", s!"agent/{name}"] (some e.mainWt)
      if rd.code != 0 then
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
    let rc ← git e ctr "status"
      #["rev-list", "--left-right", "--count", s!"main...{w.branch}"] (some e.mainWt)
    let (behind, ahead) :=
      if rc.code != 0 then ("?", "?") else
      match wsSplit rc.out with
      | [b, a] => (b, a)
      | _ => ("?", "?")
    let clean ← statusClean e ctr "status" w.path
    let last ← lastLedger e name
    let fld (k d : String) : String :=
      match last with
      | none => d
      | some l => (jsonField l k).getD d
    say "worktree" "ok"
      [("name", name), ("branch", w.branch), ("path", w.path),
       ("ahead", ahead), ("behind", behind),
       ("dirty", match clean with | some true => "no" | some false => "yes" | none => "?"),
       ("last", fld "verdict" "none"), ("run", fld "run" "-"),
       ("gateset", fld "gateset" "-"), ("gated", fld "gated" "-")]
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
  /-- The gate plan the run is driven against; the shipped list unless a case
  needs a plan of its own. -/
  plan : Option (Array GateSpec) := none

def planOf (gs : Array Gate) : Array GateSpec :=
  gs.map fun g => { name := g.name, mayAbsent := g.needsTarget.isSome }

def gatePlan : Array GateSpec := planOf gateList

def okGates : List Obs := (List.range gatePlan.size).map Obs.gateOk

def sha1s : Sha := "1111111111111111111111111111111111111111"
def sha2s : Sha := "2222222222222222222222222222222222222222"
def sha3s : Sha := "3333333333333333333333333333333333333333"

/-- A plan every one of whose gates may be absent: the vacuity case. -/
def allSkippablePlan : Array GateSpec :=
  #[{ name := "a", mayAbsent := true }, { name := "b", mayAbsent := true }]

/-- The indices of the gates the shipped plan permits to be absent. -/
def skippableIdx : List Nat :=
  (List.range gatePlan.size).filter fun i => (gatePlan[i]?.map (·.mayAbsent)).getD false

def cases : List Case :=
  let pre := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
    Obs.rebaseOk sha3s]
  let landOk := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha1s,
    .ledgerOk, .ffOk, .mainTip sha3s, .ledgerOk]
  [ { label := "lands with every gate ok", mode := .land, push := false
    , obs := landOk, verdict := .landed, code := 0, noMutation := false }
  , { label := "lands and pushes, the remote reads back at the landed tip"
    , mode := .land, push := true
    , obs := landOk ++ [.pushOk, .remoteTip sha3s]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "the remote reads back at another commit", mode := .land, push := true
    , obs := landOk ++ [.pushOk, .remoteTip sha1s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "the push is rejected after main moved", mode := .land, push := true
    , obs := landOk ++ [.pushRejected]
    , verdict := .landedUnpushed, code := 1, noMutation := false }
  , { label := "check stops before the merge", mode := .check, push := false
    , obs := pre ++ okGates, verdict := .checked, code := 0, noMutation := true }
  , { label := "the branch moved during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha1s true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a gate left the branch worktree dirty", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s false]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "main moved during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the main worktree left main during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck false sha1s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "main reads back at another commit after the merge"
    , mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha1s,
        .ledgerOk, .ffOk, .mainTip sha1s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "a truncated sha is not a sha", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk "33333333"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the fast-forward is rejected", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha1s,
        .ledgerOk, .ffRejected]
    , verdict := .refused, code := 2, noMutation := false }
  , { label := "a rebase conflict, the branch restored", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 3 2 true sha2s,
        .rebaseFailed #["LeanTex/Core/Ir.lean", "Tests/Diag.lean"] sha2s true true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a rebase that stopped with no unmerged path", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 3 2 true sha2s,
        .rebaseFailed #[] sha2s true true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a rebase left in progress is an internal failure"
    , mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 3 2 true sha2s,
        .rebaseFailed #[] sha1s false false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a gate fails", mode := .land, push := false
    , obs := pre ++ [.gateOk 0, .gateFail 1]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the last gate fails", mode := .land, push := true
    , obs := pre ++ (List.range (gatePlan.size - 1)).map Obs.gateOk
        ++ [.gateFail (gatePlan.size - 1)]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "a gate answering out of turn is an internal failure"
    , mode := .land, push := false
    , obs := pre ++ [.gateOk 0, .gateOk 0]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a gate claiming an index past the plan", mode := .land, push := false
    , obs := pre ++ okGates ++ [.gateOk gatePlan.size]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "an absence the plan does not permit", mode := .land, push := false
    , obs := pre ++ [.gateAbsent 0]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "every gate absent proves nothing", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s, .gateAbsent 0, .gateAbsent 1]
    , verdict := .failed, code := 1, noMutation := true
    , plan := some allSkippablePlan }
  , { label := "a permitted absence still lands", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s]
        ++ ((List.range gatePlan.size).map fun i =>
              if skippableIdx.contains i then Obs.gateAbsent i else Obs.gateOk i)
        ++ [.branchRecheck sha3s true, .mainRecheck true sha1s, .ledgerOk, .ffOk,
            .mainTip sha3s, .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "garbled status at the first probe", mode := .land, push := false
    , obs := [.garbled "git status --porcelain"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled rev-list at the branch probe", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .garbled "rev-list counts"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled output mid-gate", mode := .land, push := false
    , obs := pre ++ [.gateOk 0, .garbled "gate output"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the main worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus true false sha1s], verdict := .refused, code := 2
    , noMutation := true }
  , { label := "the main worktree is not on main", mode := .land, push := false
    , obs := [.mainStatus false true sha1s], verdict := .refused, code := 2
    , noMutation := true }
  , { label := "the branch does not exist", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchAbsent .noBranch]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch has no worktree", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchAbsent .noWorktree]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch is not ahead", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 0 4 true sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 2 0 false sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "an observation out of order", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .ffOk]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the write-ahead row was not written", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha1s,
        .ledgerFail]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the landed row was not written", mode := .land, push := true
    , obs := pre ++ okGates ++ [.branchRecheck sha3s true, .mainRecheck true sha1s,
        .ledgerOk, .ffOk, .mainTip sha3s, .ledgerFail]
    , verdict := .failed, code := 3, noMutation := false } ]

/-- The final halt of a scripted run: verdict and exit code. -/
def finalOf (acts : Array Act) : Option (Verdict × UInt32) :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .halt v c _ => some (v, c)
    | _ => acc

/-- What is wrong with a scripted case, or nothing. Pure, so the whole
selftest verdict is a function of values. -/
def caseFault (c : Case) : Option String :=
  let (fin, acts) := Land.run (State.init "probe" c.mode (c.plan.getD gatePlan) c.push) c.obs
  let mutated := acts.any Act.mutates
  match finalOf acts with
  | none => some "the run never halted"
  | some (v, code) =>
    if v != c.verdict then some s!"verdict-{v.name}-wanted-{c.verdict.name}"
    else if code != c.code then some s!"exit-{code}-wanted-{c.code}"
    else if c.noMutation && mutated then some "proposed a ref change"
    else if mutated && !fin.proven then some "mutated with an unproven run"
    else if fin.landedVerdict && !fin.landedIsGated then
      some "claimed a landing that is not the gated tip"
    else none

/-- The fast-forward a scripted run proposed, if any: the tip it names must
be the tip the rebase reported, never a branch name. -/
def ffTipOf (acts : Array Act) : Option Sha :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .fastForward t => some t
    | _ => acc

def selftest : IO UInt32 := do
  let mut bad := 0
  for c in cases do
    match caseFault c with
    | some why =>
      bad := bad + 1
      say "selftest" "fail" [("case", c.label), ("why", why)]
    | none => say "selftest" "ok" [("case", c.label)]
  -- The theorems, exercised: some case must reach a merge, and every merge a
  -- case reaches must name the gated tip. The proofs are in LandCore.lean;
  -- these are the witnesses that the cases reach the guarded branch at all.
  let runs := cases.map fun c =>
    (c, Land.run (State.init "probe" c.mode (c.plan.getD gatePlan) c.push) c.obs)
  let anyMutating := runs.any fun (_, r) => r.2.any Act.mutates
  if !anyMutating then
    bad := bad + 1
    say "selftest" "fail" [("case", "coverage"), ("why", "no case reaches a merge")]
  else say "selftest" "ok" [("case", "a merge is reachable")]
  for (c, r) in runs do
    match ffTipOf r.2 with
    | none => pure ()
    | some t =>
      if t != r.1.gatedTip || !isSha t then
        bad := bad + 1
        say "selftest" "fail" [("case", c.label), ("why", "the merge does not name the gated tip")]
  say "selftest" "ok" [("case", "every merge names the gated tip")]
  -- The override parser, which no repository state reaches.
  let badSpecs := ["a=true;b", "a=true;a=false", "", "=true"]
  for spec in badSpecs do
    match parseGateOverride spec with
    | .ok gs =>
      bad := bad + 1
      say "selftest" "fail" [("case", s!"override {spec}"),
        ("why", s!"parsed {gs.size} gates instead of refusing")]
    | .error _ => say "selftest" "ok" [("case", s!"override refuses {spec}")]
  match parseGateOverride "a=true;b=false arg" with
  | .ok gs =>
    if gs.size == 2 && gs[1]!.args == #["arg"] then
      say "selftest" "ok" [("case", "override parses two gates")]
    else
      bad := bad + 1
      say "selftest" "fail" [("case", "override parses two gates"), ("why", "wrong shape")]
  | .error e =>
    bad := bad + 1
    say "selftest" "fail" [("case", "override parses two gates"), ("why", e.why)]
  -- Porcelain quoting: a value with a space must come back as one value.
  if pv "a b" != "\"a b\"" || pv "ab" != "ab" || pv "" != "\"\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "porcelain quoting"), ("why", "wrong form")]
  else say "selftest" "ok" [("case", "porcelain quoting")]
  if jsonStr "a\u0001b" != "\"a\\u0001b\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "ledger escaping"), ("why", "a control byte survived")]
  else say "selftest" "ok" [("case", "ledger escaping")]
  if bad == 0 then sayFinal .checked [("cases", toString cases.length)]; return 0
  else sayFinal .failed [("cases", toString cases.length), ("bad", toString bad)]; return 1


-- ## The scratch scenarios
--
-- The selftest above drives the core over values; this drives the *driver*
-- over a repository. It needs git and nothing else: every scenario builds a
-- throwaway repository under a temporary directory, runs this very binary
-- against it with a one-command gate list, and asserts the verdict and the
-- refs. Each scenario is one the reviewer reproduced against a landing that
-- reported what had not happened, so a regression here is that defect back.
-- No real worktree is ever named: the tool under test may not be pointed at
-- one, and this harness structurally cannot be.

/-- Run a command for the harness. Not `sh`: there is no run directory yet,
and the harness asserts on exit codes rather than on parsed facts. -/
def hrun (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) := do
  let r ← try
      IO.Process.output
        { cmd, args, cwd := cwd.map System.FilePath.mk, env := extraEnv, stdin := .null }
    catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }
  return (r.exitCode.toNat, trimWs (r.stdout ++ r.stderr))

def hgit (args : Array String) (cwd : String) : IO (Nat × String) :=
  hrun "git" args (some cwd)

/-- A scratch repository on `main` with one commit, opted in to gate
overrides, plus a worktree for `agent/<name>` carrying one commit. -/
structure Scratch where
  root : String
  repo : String
  wt : String

def writeExe (path body : String) : IO Unit := do
  IO.FS.writeFile path body
  let _ ← hrun "chmod" #["+x", path] none
  pure ()

def mkScratch (root name : String) : IO Scratch := do
  let repo := s!"{root}/repo"
  IO.FS.createDirAll repo
  let _ ← hgit #["init", "-q", "-b", "main", "."] repo
  let _ ← hgit #["config", "user.name", "Scratch"] repo
  let _ ← hgit #["config", "user.email", "scratch@example.org"] repo
  let _ ← hgit #["config", "--local", "land.allowGateOverride", "true"] repo
  IO.FS.writeFile s!"{repo}/base.txt" "base\n"
  let _ ← hgit #["add", "base.txt"] repo
  let _ ← hgit #["commit", "-qm", "Base"] repo
  let wt := s!"{root}/lt-{name}"
  let _ ← hgit #["worktree", "add", "-q", "-b", s!"agent/{name}", wt, "main"] repo
  IO.FS.writeFile s!"{wt}/{name}.txt" s!"{name}\n"
  let _ ← hgit #["add", s!"{name}.txt"] wt
  let _ ← hgit #["commit", "-qm", s!"Add {name}"] wt
  return { root, repo, wt }

def revOf (repo rev : String) : IO String := do
  let (c, o) ← hgit #["rev-parse", rev] repo
  return if c == 0 then o else ""

/-- One scenario's verdict: what it expected, and what it got. -/
structure Outcome where
  label : String
  ok : Bool
  detail : String

/-- Run `land` (this binary) in a scratch repository under a gate override. -/
def landIn (self repo : String) (args : Array String) (gates : String) :
    IO (Nat × String) :=
  hrun self args (some repo) #[("LAND_GATES", some gates),
    ("GIT_TERMINAL_PROMPT", some "0")]

def scenarioBranchMoves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/moves" "moves"
  writeExe s!"{s.root}/race.sh"
    "#!/bin/sh\necho bad > BAD && git add BAD && git commit -qm concurrent\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["moves"] s!"race={s.root}/race.sh"
  let after ← revOf s.repo "refs/heads/main"
  let moved := (out.splitOn "moved during the gates").length > 1
  return { label := "a commit during the gates is refused"
         , ok := code == 2 && before == after && moved
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioMainLeaves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/leaves" "leaves"
  let _ ← hgit #["branch", "side", "main"] s.repo
  writeExe s!"{s.root}/switch.sh"
    s!"#!/bin/sh\ngit -C {s.repo} checkout -q side\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["leaves"] s!"switch={s.root}/switch.sh"
  let after ← revOf s.repo "refs/heads/main"
  let _ ← hgit #["checkout", "-q", "main"] s.repo
  let left := (out.splitOn "left main during the gates").length > 1
  return { label := "the main worktree leaving main is refused"
         , ok := code == 2 && before == after && left
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioConflict (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/conflict" "conflict"
  IO.FS.writeFile s!"{s.repo}/shared.txt" "theirs\n"
  let _ ← hgit #["add", "shared.txt"] s.repo
  let _ ← hgit #["commit", "-qm", "main writes shared"] s.repo
  IO.FS.writeFile s!"{s.wt}/shared.txt" "ours\n"
  let _ ← hgit #["add", "shared.txt"] s.wt
  let _ ← hgit #["commit", "-qm", "branch writes shared"] s.wt
  let bBefore ← revOf s.repo "refs/heads/agent/conflict"
  let mBefore ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["conflict"] "t=true"
  let bAfter ← revOf s.repo "refs/heads/agent/conflict"
  let mAfter ← revOf s.repo "refs/heads/main"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  let named := (out.splitOn "rebase conflict: shared.txt").length > 1
  let restored := (out.splitOn "step=rebase-abort result=ok").length > 1
  return { label := "a rebase conflict is refused and the branch restored"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && named && restored
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}]" }

def scenarioLands (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/lands" "lands"
  let tip ← revOf s.repo "refs/heads/agent/lands"
  let (code, out) ← landIn self s.repo #["lands"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  let pinned := (out.splitOn s!"gated={tip} tip={tip}").length > 1
  return { label := "a clean landing moves main to the gated tip"
         , ok := code == 0 && after == tip && pinned
         , detail := s!"exit={code} gated={tip} main-after={after}" }

def scenarioNoOptIn (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/optin" "optin"
  let _ ← hgit #["config", "--local", "--unset", "land.allowGateOverride"] s.repo
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["optin"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  let named := (out.splitOn "does not allow gate overrides").length > 1
  return { label := "a gate override needs the repository to opt in"
         , ok := code == 2 && before == after && named
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioReserved (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/reserved" "check"
  let before ← revOf s.repo "refs/heads/main"
  -- `land check` with no name: the branch `agent/check` exists, so a
  -- fall-through to the bare-name form would land it.
  let (code, _) ← landIn self s.repo #["check"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a subcommand word is not an agent name"
         , ok := code == 3 && before == after
         , detail := s!"exit={code} main-before={before} main-after={after}" }

/-- Drive the driver against throwaway repositories. -/
def scratchSelftest : IO UInt32 := do
  let self := (← IO.appPath).toString
  let nanos ← IO.monoNanosNow
  let root := ((← IO.getEnv "LAND_SCRATCH_DIR").getD "/tmp") ++ s!"/land-scenarios-{nanos % 1000000}"
  IO.FS.createDirAll root
  let (gv, _) ← hrun "git" #["--version"] none
  if gv != 0 then
    say "scenario" "skip" [("why", "git is not available")]
    sayFinal .checked [("scenarios", "0")]
    return 0
  let outcomes ← do
    let a ← scenarioLands self root
    let b ← scenarioBranchMoves self root
    let c ← scenarioMainLeaves self root
    let d ← scenarioConflict self root
    let e ← scenarioNoOptIn self root
    let f ← scenarioReserved self root
    pure [a, b, c, d, e, f]
  let mut bad := 0
  for o in outcomes do
    if o.ok then say "scenario" "ok" [("case", o.label)]
    else
      bad := bad + 1
      say "scenario" "fail" [("case", o.label), ("detail", o.detail)]
  rmQuiet root
  if bad == 0 then
    sayFinal .checked [("scenarios", toString outcomes.length)]
    return 0
  else
    sayFinal .failed [("scenarios", toString outcomes.length), ("bad", toString bad)]
    return 1

-- ## Entry

def usage : String :=
  "usage: land new <name> | land check <name> | land <name> [--push] | \
land retire <name> | land status | land --selftest | land --scratch-selftest"

/-- The subcommand words, which are not agent names. `land check` with no
name once fell through to the bare-name form and would have landed
`agent/check`. -/
def reserved : List String := ["new", "check", "retire", "status"]

def resolveGates (e : Env) : IO (Except String (Array Gate × String)) := do
  let ctr ← IO.mkRef 0
  match ← IO.getEnv "LAND_GATES" with
  | none => return .ok (gateList, "default")
  | some spec =>
    if !(← overrideAllowed e ctr) then
      return .error "LAND_GATES is set, and this repository does not allow \
gate overrides (git config --local land.allowGateOverride true)"
    match parseGateOverride spec with
    | .error err => return .error err.why
    | .ok gs => return .ok (gs, "override")

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [] => IO.eprintln usage; return 3
  | ["--selftest"] => selftest
  | ["--scratch-selftest"] => scratchSelftest
  | args => do
    match ← mkEnv with
    | .error e => IO.eprintln s!"land: {e}"; return 3
    | .ok env =>
      retainRuns env 50
      let landing (n : String) (m : Mode) (p : Bool) : IO UInt32 := do
        if reserved.contains n then
          IO.eprintln s!"land: {n} is a subcommand, not an agent name"
          return 3
        match ← resolveGates env with
        | .error why =>
          say "gateset" "fail" [("why", why)]
          sayFinal .refused [("name", n), ("why", why)]
          return 2
        | .ok (gs, gateset) => withLock env (landRun env n m p gs gateset)
      let named (n : String) (act : IO UInt32) : IO UInt32 := do
        if reserved.contains n then
          IO.eprintln s!"land: {n} is a subcommand, not an agent name"
          return 3
        act
      match args with
      | ["status"] => landStatus env
      | ["new", n] => named n (landNew env n)
      | ["retire", n] => named n (landRetire env n)
      | ["check", n] => landing n .check false
      | [n] => landing n .land false
      | [n, "--push"] => landing n .land true
      | _ => IO.eprintln usage; return 3
