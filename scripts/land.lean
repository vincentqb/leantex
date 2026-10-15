/-
`land`: the landing procedure as a porcelain command over `scripts/LandCore.lean`; exit 0 ok, 1
gate failed, 2 precondition, conflict or another's turn, 3 internal or misuse, 4 landed, not pushed.
Usage: land new <name> | check <name> | <name> [--push] | push | retire <name> | status | --selftest | --scratch-selftest | --help
-/
import scripts.LandCore
import scripts.GitGuard
import Std.Data.HashMap
import Std.Data.HashSet

open Land

structure Env where
  common : String
  mainWt : String
  runDir : String
  runId : String
  /-- ISO-8601 UTC, for the ledger. -/
  ts : String
  childEnv : Array (String × Option String)
  /-- An exclusive lock on `<run dir>/alive`, held for the whole run, which tells a live
  run's directory from a dead one's. -/
  alive : IO.FS.Handle

/-- A porcelain value, quoted when it holds whitespace, a quote, a backslash or nothing at
all. -/
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

/-- What one command produced: its exit code, standard output and standard error, kept
apart since only the first two are facts about the repository. -/
structure Ran where
  code : Nat
  out : String
  err : String
  /-- The standard output's bytes, as the run directory holds them. -/
  bytes : ByteArray := .empty
  /-- Whether those bytes were UTF-8, so `out` is them unchanged. -/
  exact : Bool := true

/-- Bytes spelled one-to-one as text: each well-formed UTF-8 sequence as its character
with backslashes doubled, every other byte as `\xHH`. -/
def spelledText (bs : ByteArray) : String := Id.run do
  let hex (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)
  let mut out := ""
  let mut i := 0
  for _ in [0:bs.size] do
    if i ≥ bs.size then break
    match bs.utf8DecodeChar? i with
    | some c =>
      out := if c == '\\' then out ++ "\\\\" else out.push c
      i := i + c.utf8Size
    | none =>
      let b := (bs[i]?.getD 0).toNat
      out := ((out ++ "\\x").push (hex (b / 16))).push (hex (b % 16))
      i := i + 1
  return out

/-- A command's output as the core reads it: UTF-8 as itself, anything else as
`spelledText` spells it. -/
def outputText (bs : ByteArray) : String :=
  match String.fromUTF8? bs with
  | some s => s
  | none => spelledText bs

/-- Run a command with its two streams written to separate files in the run directory and
read back; children get a null standard input and `GIT_TERMINAL_PROMPT=0`. -/
def sh (e : Env) (ctr : IO.Ref Nat) (step cmd : String) (args : Array String)
    (cwd : Option String := none) : IO Ran := do
  let n ← ctr.modifyGet (fun k => (k, k + 1))
  let outPath := s!"{e.runDir}/{step}.{n}.out"
  let errPath := s!"{e.runDir}/{step}.{n}.err"
  -- Flush first: a failed exec writes the inherited stdout buffer into the captured pipe.
  (← IO.getStdout).flush
  let r : UInt32 × ByteArray × ByteArray ← try
      let child ← IO.Process.spawn
        { cmd, args, cwd := cwd.map System.FilePath.mk, env := e.childEnv,
          stdin := .null, stdout := .piped, stderr := .piped }
      let o ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
      let x ← IO.asTask child.stderr.readBinToEnd Task.Priority.dedicated
      let o ← IO.ofExcept o.get
      let x ← IO.ofExcept x.get
      pure (← child.wait, o, x)
    catch ex =>
      pure (127, ByteArray.empty, s!"spawn failed: {ex}".toUTF8)
  IO.FS.writeBinFile outPath r.2.1
  IO.FS.writeBinFile errPath r.2.2
  let outBytes ← IO.FS.readBinFile outPath
  let out := outputText outBytes
  let err := outputText (← IO.FS.readBinFile errPath)
  let h ← IO.FS.Handle.mk s!"{e.runDir}/{step}.log" .append
  h.putStr s!"$ ({cwd.getD "."}) {cmd} {String.intercalate " " args.toList}\n"
  h.putStr s!"exit={r.1}\n--- stdout\n{out}--- stderr\n{err}\n"
  h.flush
  return { code := r.1.toNat, out, err, bytes := outBytes, exact := outBytes.validateUTF8 }

def git (e : Env) (ctr : IO.Ref Nat) (step : String) (args : Array String)
    (cwd : Option String := none) : IO Ran :=
  sh e ctr step "git" args cwd

def childEnvVars : IO (Array (String × Option String)) := do
  let cc ← IO.getEnv "LEAN_CC"
  let lp ← IO.getEnv "LIBRARY_PATH"
  -- Never inherited: a variable naming another repository, as git exports to hooks.
  let scrub0 : Array (String × Option String) := repoVarsFixed.map (·, none)
  let r ← try
      IO.Process.output
        { cmd := "git", args := #["rev-parse", "--local-env-vars"], env := scrub0,
          stdin := .null }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let asked := if r.exitCode == 0 then (wsSplit r.stdout).toArray else #[]
  let names := asked.foldl (init := repoVarsFixed) fun acc n =>
    if acc.contains n then acc else acc.push n
  -- Never inherited either: a child that can prompt can hang a scripted landing.
  let mut out : Array (String × Option String) :=
    names.map (·, none) |>.push ("GIT_TERMINAL_PROMPT", some "0")
  if cc.isNone then
    out := out.push ("LEAN_CC", some "/home/linuxbrew/.linuxbrew/bin/clang")
  if lp.isNone then
    let r ← try IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
            catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if r.exitCode == 0 then
      let p := trimWs r.stdout
      out := out.push ("LIBRARY_PATH", some s!"{p}/lib:{p}/lib/lean")
  return out

/-- The three probes that locate the run directory run before it exists, and are written
back to `bootstrap.log` once it does. -/
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
        { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%S%N %Y-%m-%dT%H:%M:%SZ"] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let stamps := wsSplit (if d.exitCode == 0 then d.stdout else "run -")
  -- Fixed-width nanoseconds sort run ids within a second; the pid separates equal ones.
  let runId := (stamps.headD "run") ++ s!"-{← IO.Process.getPID}"
  let ts := stamps.getD 1 "-"
  let runDir := s!"{common}/land/{runId}"
  IO.FS.createDirAll runDir
  let alive ← IO.FS.Handle.mk s!"{runDir}/alive" .append
  let _ ← alive.tryLock
  IO.FS.writeFile s!"{runDir}/bootstrap.log" (← trace.get)
  return .ok { common, mainWt, runDir, runId, ts, childEnv, alive }

def rmQuiet (p : System.FilePath) : IO Unit := do
  try IO.FS.removeDirAll p catch _ => pure ()

/-- Whether the run owning this directory still runs, by the exclusive lock it holds on `alive`
for its whole life, tried shared so that two probes never read each other as it; `none` when
the lock cannot be tried. -/
def runProbe (d : System.FilePath) : IO (Option Bool) := do
  if !(← (d / "alive").pathExists) then return some false
  try
    let h ← IO.FS.Handle.mk (d / "alive") .read
    let got ← h.tryLock (exclusive := false)
    if got then h.unlock
    return some !got
  catch _ => return none

/-- `runProbe`, a lock that cannot be tried reading as live. -/
def runLive (d : System.FilePath) : IO Bool := return (← runProbe d).getD true

/-- Keep the newest run directories and drop the rest, never a live run's or this run's
own, unregistering a dead run's gate tree first. -/
def retainRuns (e : Env) (keep : Nat) : IO Unit := do
  let base : System.FilePath := s!"{e.common}/land"
  let entries ← try base.readDir catch _ => pure #[]
  let mut names : Array String := #[]
  for d in entries do
    let n := d.fileName
    let isDir ← try (base / n).isDir catch _ => pure false
    if isDir && n != "lock" then names := names.push n
  let sorted := names.qsort (· < ·)
  if sorted.size > keep then
    for i in [0:sorted.size - keep] do
      let d := base / sorted[i]!
      if d.toString == e.runDir then continue
      if ← runLive d then continue
      if ← (d / "tree").pathExists then
        let _ ← try
            IO.Process.output
              { cmd := "git", args := #["worktree", "remove", "--force", (d / "tree").toString],
                cwd := some e.mainWt, env := e.childEnv, stdin := .null }
          catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
      rmQuiet d

structure Wt where
  path : String
  branch : String
  deriving Repr, Inhabited

/-- Every worktree with its checked-out branch, parsed from the porcelain listing written
to a file. -/
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

/-- The directory a new worktree for `name` takes: a sibling of the main worktree,
prefixed `LAND_WORKTREE_PREFIX` (default `lt-`). -/
def newWorktreePath (e : Env) (name : String) : IO String := do
  let pre := (← IO.getEnv "LAND_WORKTREE_PREFIX").getD "lt-"
  let parent :=
    match (e.mainWt.splitOn "/").dropLast with
    | [] => "."
    | ps => String.intercalate "/" ps
  return s!"{parent}/{pre}{name}"

/-- One gate: a name, and the command it runs in the gate tree. -/
structure Gate where
  name : String
  cmd : String
  args : Array String
  deriving Repr, Inhabited

/-- Malformed entries in a gate list, or the empty list. -/
inductive GateSpecError where
  | empty
  | malformed (entry : String)
  | duplicate (name : String)

def GateSpecError.why : GateSpecError → String
  | .empty => "the gate list declares no gate"
  | .malformed e => s!"a gate list entry is not name=command: {e}"
  | .duplicate n => s!"the gate list names {n} twice"

/-- A gate list, `name=cmd arg arg;name=cmd …`, run in order in the gate tree, one parser
for the shipped list and a `LAND_GATES` override; an entry without `=` and a repeated name
are refusals. -/
def parseGates (spec : String) : Except GateSpecError (Array Gate) := do
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
        out := out.push { name := nm, cmd := c, args := as.toArray }
    | [] => throw (.malformed ent)
  if out.isEmpty then throw .empty
  return out

/-- The gates every landing runs, in order, in the gate-list syntax, `{main}` standing for
the sha of `main` the run read and `{tip}` for the gated tip; none may be absent, and
`--wfail` fails a build on any warning. -/
def defaultGates : List String := [
  "build=lake build --wfail LeanTex TestsModules ScriptsModules leantex Tests precommit proofcheck \
lint cites land scoreboard",
  "conventions=.lake/build/bin/precommit --range {main}...{tip} --conventions",
  "test=lake test",
  "lint=lake lint",
  "land-selftest=.lake/build/bin/land --selftest",
  "land-scenarios=.lake/build/bin/land --scratch-selftest",
  "scoreboard-check=.lake/build/bin/scoreboard --check",
  "scoreboard-base=.lake/build/bin/scoreboard --check --base {main}",
  "scoreboard-selftest=.lake/build/bin/scoreboard --selftest"]

/-- The shipped list, parsed; a list that does not parse is empty, so no landing gets past
it. -/
def gateList : Array Gate :=
  match parseGates (String.intercalate ";" defaultGates) with
  | .ok gs => gs
  | .error _ => #[]

/-- The plan the core is driven against: the gates' names in order, none permitted to be
absent. -/
def planOf (gs : Array Gate) : Array GateSpec :=
  gs.map fun g => { name := g.name, mayAbsent := false }

/-- Whether the gate override is permitted: only in a repository that opted in with `git
config --local land.allowGateOverride true`. -/
def overrideAllowed (e : Env) (ctr : IO.Ref Nat) : IO Bool := do
  let r ← git e ctr "gateset" #["config", "--local", "--get", "land.allowGateOverride"]
  return r.code == 0 && trimWs r.out == "true"

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A JSON string, every control character escaped. -/
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

/-- A ledger row as `writeLedger` writes it, without its newline. -/
def ledgerLine (rec : List (String × String)) : String :=
  "{" ++ String.intercalate "," (rec.map fun (k, v) => s!"{jsonStr k}:{jsonStr v}") ++ "}"

def writeLedger (e : Env) (rec : List (String × String)) : IO Bool := do
  try
    let line := ledgerLine rec ++ "\n"
    IO.FS.createDirAll s!"{e.common}/land"
    let h ← IO.FS.Handle.mk (ledgerPath e) .append
    h.putStr line
    -- Flushed so the read-back below checks the row is on disk.
    h.flush
    let back ← IO.FS.readFile (ledgerPath e)
    return (back.splitOn line).length > 1
  catch _ => return false

def jsonField (line key : String) : Option String :=
  match (line.splitOn s!"{jsonStr key}:\"").drop 1 |>.head? with
  | none => none
  | some rest => (rest.splitOn "\"").head?

/-- The write-ahead row's riders: each name, read tip and commit in the train, which no ref name
can split. -/
def ridersField (rs : List (String × Sha × Sha)) : String :=
  String.intercalate " " (rs.map fun (n, t, c) => s!"{n}:{t}:{c}")

/-- The landed rows a write-ahead row names, as `writeLanded` writes them: the run's own branch at
its commit, then each rider at its commit in the train. -/
def owedRows (row : String) : List String :=
  let f (k : String) := (jsonField row k).getD ""
  let riders := (f "riders").splitOn " " |>.filterMap fun m =>
    match m.splitOn ":" with
    | [n, t, c] => some (n, t, c)
    | _ => none
  let train := if riders.isEmpty then [] else [("train", f "run")]
  let landed (n tip branch : String) := ledgerLine ([("ts", f "ts"), ("run", f "run"),
    ("name", n), ("verdict", "landed"), ("tip", tip), ("gated", f "gated"), ("prev", f "prev"),
    ("branch", branch)] ++ train ++ [("owed", "yes")])
  landed (f "name") ((jsonField row "tip").getD (f "gated")) (f "branch")
    :: riders.map fun (n, t, c) => landed n c t

/-- Whether `main`, at each tip it was read at, holds each gated tip asked about. -/
initialize heldTips : IO.Ref (Std.HashMap (Sha × Sha) Bool) ← IO.mkRef {}

/-- Whether `main` at `tip` holds commit `g`; a commit git cannot place reads as not held. -/
def mainHolds (e : Env) (tip g : Sha) : IO Bool := do
  if let some held := (← heldTips.get)[(tip, g)]? then return held
  let ctr ← IO.mkRef 0
  let held ← try
      pure ((← git e ctr "ledger" #["merge-base", "--is-ancestor", g, tip] (some e.mainWt)).code
        == 0)
    catch _ => pure false
  heldTips.modify (·.insert (tip, g) held)
  return held

/-- The ledger's rows, each run that died after its fast-forward followed, after its own last row,
by the landed rows its write-ahead row names and it did not write: the run halted on no other
verdict and no longer runs, and `main` holds its gated tip. -/
def ledgerLines (e : Env) : IO (List String) := do
  let txt ← IO.FS.readFile (ledgerPath e)
  let ls := ((txt.splitOn "\n").filter (!·.isEmpty)).toArray
  let field (l k : String) := (jsonField l k).getD ""
  let verdict (l : String) (vs : List Verdict) := (jsonField l "verdict").any (vs.map (·.name)).contains
  let landed : Std.HashSet (String × String) := ls.foldl (init := {}) fun acc l =>
    if verdict l [.landed] then acc.insert (field l "run", field l "name") else acc
  let halted : Std.HashSet String := ls.foldl (init := {}) fun acc l =>
    if verdict l [.refused, .failed, .landedUnpushed, .checked] then acc.insert (field l "run")
    else acc
  -- Each run's own last row; an abandoned row names the dead run, but another run wrote it.
  let last : Std.HashMap String Nat := ls.zipIdx.foldl (init := {}) fun acc (l, i) =>
    if jsonField l "verdict" == some "abandoned" then acc else acc.insert (field l "run") i
  let ctr ← IO.mkRef 0
  let mut mainTip : Option Sha := none
  let mut owed : Std.HashMap Nat (Array String) := {}
  for l in ls do
    if jsonField l "verdict" == some "landing" then
      let run := field l "run"
      let g := field l "gated"
      let rows := (owedRows l).filter fun r => !landed.contains (run, field r "name")
      if !rows.isEmpty && !halted.contains run && isSha g then
        if !((← runProbe s!"{e.common}/land/{run}").getD false) then
          let tip ← match mainTip with
            | some t => pure t
            | none => do
              let r ← try git e ctr "ledger" #["rev-parse", "refs/heads/main"] (some e.mainWt)
                catch _ => pure { code := 1, out := "", err := "" }
              pure (if r.code == 0 then trimWs r.out else "")
          mainTip := some tip
          if isSha tip then
            if ← mainHolds e tip g then
              let at_ := last.getD run 0
              owed := owed.insert at_ (owed.getD at_ #[] ++ rows.toArray)
  let mut out : Array String := #[]
  for (l, i) in ls.zipIdx do
    out := out.push l
    if let some rows := owed[i]? then out := out ++ rows
  return out.toList

/-- The last ledger row for `name`. -/
def lastLedger (e : Env) (name : String) : IO (Option String) := do
  try
    let key := s!"\"name\":{jsonStr name}"
    return ((← ledgerLines e).filter fun l => (l.splitOn key).length > 1).getLast?
  catch _ => return none

/-- The last ledger line whose `verdict` is one of `vs`, for one agent or, when `name` is
`none`, any, read back from the file. -/
def lastVerdictIn (e : Env) (vs : List String) (name : Option String) : IO (Option String) := do
  try
    let hits := (← ledgerLines e).filter fun l =>
      (jsonField l "verdict").any vs.contains
        && match name with
          | none => true
          | some n => (l.splitOn s!"\"name\":{jsonStr n}").length > 1
    return hits.getLast?
  catch _ => return none

/-- The last ledger line whose `verdict` is `v`, for one agent or any. -/
def lastVerdict (e : Env) (v : String) (name : Option String) : IO (Option String) :=
  lastVerdictIn e [v] name

/-- Whether a worktree is clean, read without git refreshing its index. -/
def statusClean (e : Env) (ctr : IO.Ref Nat) (step wt : String) : IO (Option Bool) := do
  let r ← git e ctr step #["--no-optional-locks", "status", "--porcelain"] (some wt)
  if r.code != 0 then return none
  return some (trimWs r.out).isEmpty

def revParse (e : Env) (ctr : IO.Ref Nat) (step rev : String)
    (cwd : Option String := none) : IO String := do
  let r ← git e ctr step #["rev-parse", rev] cwd
  if r.code != 0 then return "" else return trimWs r.out

/-- Whether the worktree's `HEAD` is the named branch, read from `symbolic-ref` so a
detached `HEAD` is a no. -/
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

/-- The tip an earlier landing of `name` read and the commit it landed as, when that
landing rebased the branch and the branch still carries that tip, with whether `mainTip`
holds that commit; `none` when git cannot say. -/
def landedFromRow (e : Env) (ctr : IO.Ref Nat) (name tip mainTip : String) :
    IO (Option (String × String × Bool)) := do
  match ← lastVerdict e "landed" (some name) with
  | none => return some ("", "", false)
  | some row =>
    let b := (jsonField row "branch").getD ""
    let g := (jsonField row "tip").getD ((jsonField row "gated").getD "")
    if !isSha b || !isSha g || b == g then return some ("", "", false)
    let r ← git e ctr "pre-branch" #["merge-base", "--is-ancestor", b, tip] (some e.mainWt)
    if r.code != 0 then return some ("", "", false)
    -- A commit this repository no longer has is on no `main`.
    let v ← git e ctr "pre-branch" #["cat-file", "-e", g ++ "^{commit}"] (some e.mainWt)
    if v.code != 0 then return some (b, g, false)
    let m ← git e ctr "pre-branch" #["merge-base", "--is-ancestor", g, mainTip] (some e.mainWt)
    return (if m.code == 0 then some (b, g, true)
      else if m.code == 1 then some (b, g, false) else none)

/-- The commit the last `landed` row for `name` landed as, when that row read exactly
`tip` and `main` holds its commit; empty otherwise. -/
def landedTipOf (e : Env) (ctr : IO.Ref Nat) (name tip : String) : IO String := do
  match ← lastVerdict e "landed" (some name) with
  | none => return ""
  | some row =>
    let b := (jsonField row "branch").getD ""
    let g := (jsonField row "tip").getD ""
    if b != tip || !isSha g then return ""
    let r ← git e ctr "pre" #["merge-base", "--is-ancestor", g, "main"] (some e.mainWt)
    return (if r.code == 0 then g else "")

/-- The `landed` row of a branch `main` already holds, unmoved since: no later row made the
name new or retired it, the branch reads at the commit that row landed it as or at the tip it
read, its worktree is clean, and `main` holds that commit. -/
def alreadyLanded (e : Env) (name : String) : IO (Option String) := do
  let ctr ← IO.mkRef 0
  match ← lastVerdictIn e ["landed", "created", "retired"] (some name) with
  | none => return none
  | some row =>
    if jsonField row "verdict" != some "landed" then return none
    let t := (jsonField row "tip").getD ""
    let b := (jsonField row "branch").getD ""
    let cur ← revParse e ctr "pre" s!"refs/heads/agent/{name}" (some e.mainWt)
    if !isSha t || !isSha cur || (cur != t && cur != b) then return none
    let some wt ← worktreeOf e ctr "pre" name | return none
    if (← statusClean e ctr "pre" wt) != some true then return none
    let r ← git e ctr "pre" #["merge-base", "--is-ancestor", t, "refs/heads/main"] (some e.mainWt)
    return if r.code == 0 then some row else none

/-- The gate tree: a detached worktree this run makes in its own run directory, which
nothing else writes. -/
def treePath (e : Env) : String := s!"{e.runDir}/tree"

/-- The gate tree read back: its `HEAD` and whether it is clean; a directory that is not a
work tree reads as no sha. -/
def readTree (e : Env) (ctr : IO.Ref Nat) (step : String) : IO (Sha × Bool) := do
  let tree := treePath e
  let inside ← git e ctr step #["rev-parse", "--is-inside-work-tree"] (some tree)
  if inside.code != 0 || trimWs inside.out != "true" then return ("", false)
  let head ← revParse e ctr step "HEAD" (some tree)
  let clean ← statusClean e ctr step tree
  return (head, clean == some true)

/-- Make the gate tree at `tip` and seed its build cache with a copy (never a hardlink) of
the branch worktree's `.lake`, else the main worktree's. -/
def makeTree (e : Env) (ctr : IO.Ref Nat) (wt tip : String) : IO String := do
  let tree := treePath e
  let ra ← git e ctr "gate-tree" #["worktree", "add", "--detach", tree, tip] (some e.mainWt)
  if ra.code != 0 then return "no-tree"
  let src ← if ← System.FilePath.pathExists s!"{wt}/.lake" then pure (some s!"{wt}/.lake")
    else if ← System.FilePath.pathExists s!"{e.mainWt}/.lake" then pure (some s!"{e.mainWt}/.lake")
    else pure none
  match src with
  | none => return "none"
  | some from_ =>
    let rs ← sh e ctr "seed" "cp" #["-a", "--reflink=auto", from_, s!"{tree}/.lake"]
    if rs.code == 0 then return from_
    rmQuiet s!"{tree}/.lake"
    return "failed"

/-- Remove the gate tree, forced, and read back that it is gone from the disk and the
worktree list. -/
def removeTree (e : Env) (ctr : IO.Ref Nat) : IO Unit := do
  let tree := treePath e
  let _ ← git e ctr "tree-remove" #["worktree", "remove", "--force", tree] (some e.mainWt)
  let gone := !(← System.FilePath.pathExists tree)
  let wl ← git e ctr "tree-remove" #["worktree", "list", "--porcelain"] (some e.mainWt)
  let listed := (wl.out.splitOn "\n").any (trimWs · == s!"worktree {tree}")
  say "tree-remove" (if gone && !listed then "ok" else "fail")
    [("path", tree), ("gone", if gone then "yes" else "no"),
     ("listed", if listed then "yes" else "no")]

/-- A gate's arguments with `{main}` and `{tip}` spelled as the shas of `main` the run read
and of the gated tip. -/
def gateArgs (mainTip tip : Sha) (args : Array String) : Array String :=
  args.map fun a => (a.replace "{main}" mainTip).replace "{tip}" tip

/-- Run one gate in the gate tree, reading the tree back before and after it, its arguments
spelled by `gateArgs`. -/
def runGate (e : Env) (ctr : IO.Ref Nat) (g : Gate) (idx : Nat) (mainTip tip : Sha) :
    IO Obs := do
  let tree := treePath e
  let step := s!"gate-{g.name}"
  let (hb, cb) ← readTree e ctr step
  let cmd := if g.cmd.startsWith "." then s!"{tree}/{g.cmd}" else g.cmd
  let args := gateArgs mainTip tip g.args
  let r ← sh e ctr step cmd args (some tree)
  let (ha, ca) ← readTree e ctr step
  -- The tree as read around the gate: the head both reads agree on, and clean only if both were.
  let head := if hb == ha then ha else ""
  let clean := cb && ca
  if r.code != 0 then return .gateFail idx head clean
  return .gateOk idx head clean

/-- The landing lock, and the record of who holds it. -/
def lockPath (e : Env) : String := s!"{e.common}/land/landing.lock"
def ownerPath (e : Env) : String := s!"{e.common}/land/landing.owner"

/-- A `key=value` field of an owner record; empty when absent. -/
def recField (rec key : String) : String :=
  match (wsSplit rec).find? (·.startsWith s!"{key}=") with
  | some w => (w.drop (key.length + 1)).toString
  | none => ""

/-- The landing queue, one waiter a line in arrival order, and the lock its readers and writers
take. -/
def queuePath (e : Env) : String := s!"{e.common}/land/queue"
def queueLockPath (e : Env) : String := s!"{e.common}/land/queue.lock"

/-- A name the queue holds: one a branch can carry, with no whitespace or control character. -/
def queueable (name : String) : Bool :=
  !name.isEmpty && name.all fun c =>
    !c.isWhitespace && c.toNat ≥ 0x20 && (c.toNat < 0x7f || c.toNat > 0x9f)

def waiterLine (w : Waiter) : String :=
  s!"name={w.name} run={w.run} pid={w.pid} since={w.since} fare={w.fare} train={w.train}"

/-- A run id the queue may name: one a run directory can carry, naming no path. -/
def runName (r : String) : Bool := queueable r && !r.contains '/' && !r.startsWith "."

/-- A queue line read back, or nothing for one that is not a waiter's, a run naming a path
among them. -/
def waiterOfLine? (l : String) : Option Waiter := do
  let name := recField l "name"
  let run := recField l "run"
  let train := recField l "train"
  let pid ← (recField l "pid").toNat?
  if !queueable name || !runName run || !(train.isEmpty || runName train) then none
  else some { name, run, pid, since := recField l "since", fare := recField l "fare", train }

/-- The queue a file holds, a line that is not a waiter's dropped, and a name's later lines. -/
def queueOfText (txt : String) : List Waiter := Id.run do
  let mut out : Array Waiter := #[]
  for l in txt.splitOn "\n" do
    if let some w := waiterOfLine? l then
      unless out.any (·.name == w.name) do out := out.push w
  return out.toList

/-- The queue, empty when its file is absent; a file that cannot be read is an error, never an
empty queue. -/
def readQueueAt (common : String) : IO (List Waiter) := do
  let p := s!"{common}/land/queue"
  if !(← System.FilePath.pathExists p) then return []
  queueOfText <$> IO.FS.readFile p

/-- Replace the queue file whole, by a rename, so a reader sees one queue or the next. -/
def writeQueue (e : Env) (q : List Waiter) : IO Unit := do
  let next := s!"{queuePath e}.next"
  IO.FS.writeFile next (String.join (q.map (waiterLine · ++ "\n")))
  IO.FS.rename next (queuePath e)

/-- Whether a run still runs, by the lock on its `alive`, which a reused pid does not hold; a
lock that cannot be tried reads as dead, so it cannot stall the queue. -/
def runLiveAt (common run : String) : IO Bool :=
  return (← runProbe s!"{common}/land/{run}").getD false

def waiterLiveAt (common : String) (w : Waiter) : IO Bool := runLiveAt common w.run

def waiterLive (e : Env) (w : Waiter) : IO Bool := waiterLiveAt e.common w

/-- The pause between a waiting run's asks for its turn. -/
def turnBeatMs : UInt32 := 500

/-- The asks a waiting run makes before it refuses: eight hours of beats, the span a landing's
retries are given. -/
def turnBeats : Nat := 8 * 60 * 60 * 1000 / turnBeatMs.toNat

/-- Settle a train's riders under the queue's lock: the landed and the refused leave, the rest
wait again in their places. -/
def settleRiders (e : Env) (gone stay : List String) : IO Unit := do
  if gone.isEmpty && stay.isEmpty then return
  try
    let qh ← IO.FS.Handle.mk (queueLockPath e) .append
    qh.lock
    try
      let q ← readQueueAt e.common
      let q' := Queue.alight (q.filter fun w => !gone.contains w.name) stay
      if q' != q then writeQueue e q'
    finally qh.unlock
  catch ex => say "queue" "fail" [("why", s!"the riders' places could not be settled: {ex}")]

/-- A branch as the pre-checks read it: its worktree, how far ahead and behind `main`, whether
the worktree is clean, its tip, and what an earlier landing of it read and landed as. -/
structure BranchRead where
  wt : String
  ahead : Nat
  behind : Nat
  clean : Bool
  tip : Sha
  landedFrom : Sha
  landedAs : Sha
  landedOnMain : Bool

/-- Read `agent/<name>` for the pre-checks, under the step's name in the porcelain; `.error` for
output that does not parse. -/
def readAgent (e : Env) (ctr : IO.Ref Nat) (step name : String) (mainTip : Sha) :
    IO (Except String (Except BranchMiss BranchRead)) := do
  let r ← git e ctr step #["show-ref", "--verify", "--quiet", s!"refs/heads/agent/{name}"]
  if r.code != 0 then
    say step "fail" [("branch", s!"agent/{name}"), ("present", "no")]
    return .ok (.error .noBranch)
  match ← worktreeOf e ctr step name with
  | none =>
    say step "fail" [("branch", s!"agent/{name}"), ("worktree", "none")]
    return .ok (.error .noWorktree)
  | some p =>
    let rc ← git e ctr step #["rev-list", "--left-right", "--count", s!"main...agent/{name}"] (some p)
    if rc.code != 0 then return .error "git rev-list --count"
    match wsSplit rc.out with
    | [b, a] =>
      match b.toNat?, a.toNat? with
      | some behind, some ahead =>
        match ← statusClean e ctr step p with
        | none => return .error "git status in the branch worktree"
        | some clean =>
          let tip ← revParse e ctr step s!"refs/heads/agent/{name}" (some p)
          let row ← if isSha tip then landedFromRow e ctr name tip mainTip
            else pure (some ("", "", false))
          match row with
          | none => return .error "git merge-base --is-ancestor for the landed commit"
          | some (landedFrom, landedAs, onMain) =>
            let barred := landedBars landedFrom onMain
            say step (if ahead > 0 && clean && !barred then "ok" else "fail")
              ([("worktree", p), ("ahead", toString ahead), ("behind", toString behind),
                ("dirty", if clean then "no" else "yes"), ("tip", if tip.isEmpty then "?" else tip)]
               ++ (if landedFrom.isEmpty then []
                   else [("landed-from", landedFrom), ("landed-as", landedAs),
                     ("landed-on-main", if onMain then "yes" else "no")]))
            return .ok (.ok { wt := p, ahead, behind, clean, tip, landedFrom, landedAs, landedOnMain := onMain })
      | _, _ => return .error "rev-list counts are not numbers"
    | other => return .error s!"rev-list counts: {other.length} fields"

/-- Rebase the gate tree from exactly `tip` onto exactly `onto`, a tip containing the base kept as
it is: the tree read back, its head and whether it is clean and detached, or the unmerged paths of
a rebase that failed and was aborted. -/
def rebaseTree (e : Env) (ctr : IO.Ref Nat) (step : String) (tip onto : Sha) :
    IO (Except (Array String) (Sha × Bool)) := do
  -- A tip containing the base keeps its merges; else only the captured sha is replayed.
  let tree := treePath e
  let contains ← git e ctr s!"{step}-base" #["merge-base", "--is-ancestor", onto, tip] (some tree)
  -- premise: scenarioMergedTip — the reviewed tip, tree and ancestry land unchanged
  let r ← if contains.code == 0 then
      git e ctr step #["checkout", "--detach", tip] (some tree)
    else if contains.code == 1 then
      git e ctr step #["rebase", "--no-update-refs", "--no-autosquash", "--no-autostash", onto, tip]
        (some tree)
    else pure contains
  if r.code == 0 then
    let head ← revParse e ctr step "HEAD" (some tree)
    let clean? ← statusClean e ctr step tree
    let onRef ← git e ctr step #["symbolic-ref", "--quiet", "HEAD"] (some tree)
    let detached := onRef.code != 0
    let ok := clean? == some true && detached && (contains.code != 0 || head == tip)
    say step (if ok && isSha head then "ok" else "fail")
      [("from", tip), ("onto", onto), ("tip", if head.isEmpty then "?" else head),
       ("dirty", if clean? == some true then "no" else "yes"),
       ("detached", if detached then "yes" else "no"),
       ("mode", if contains.code == 0 then "preserve" else "replay")]
    return .ok (head, ok)
  -- A failed rebase: the unmerged paths for the refusal, then an abort.
  let ru ← git e ctr step #["diff", "--name-only", "--diff-filter=U"] (some tree)
  let files := (ru.out.splitOn "\n").map trimWs |>.filter (!·.isEmpty)
  if ← midRebase e ctr s!"{step}-abort" tree then
    let _ ← git e ctr s!"{step}-abort" #["rebase", "--abort"] (some tree)
    pure ()
  say step "fail" [("from", tip), ("onto", onto),
    ("conflict", if files.isEmpty then "none" else String.intercalate "," files)]
  return .error files.toArray

/-- List a change's two net forms for the comparison: the branch's own, from its fork point with
`newBase` to `oldTip`, and the rebase's, from `newBase` to `newTip`; `.error` when git cannot. -/
def netListings (e : Env) (ctr : IO.Ref Nat) (step : String) (oldTip newBase newTip : Sha) :
    IO (Except String (String × String)) := do
  -- The branch's change from its fork point with the new base, through plumbing.
  let rf ← git e ctr step #["merge-base", newBase, oldTip] (some e.mainWt)
  let fork := trimWs rf.out
  if rf.code != 0 || !isSha fork then return .error "git merge-base for the net comparison"
  let listing (a b : String) : Array String :=
    #["diff-tree", "-r", "-p", "--no-color", "--no-ext-diff", "--no-textconv",
      "--no-renames", "--binary", "-U0", a, b]
  let rb ← git e ctr step (listing fork oldTip) (some e.mainWt)
  let ra ← git e ctr step (listing newBase newTip) (some e.mainWt)
  if rb.code != 0 || ra.code != 0 then return .error "git diff-tree for the net comparison"
  -- Where either listing is not UTF-8, both are read through one one-to-one spelling.
  let (before, after) := if rb.exact && ra.exact then (rb.out, ra.out)
    else (spelledText rb.bytes, spelledText ra.bytes)
  let drift := netDrift (netOf before) (netOf after)
  say step (if drift.isEmpty then "ok" else "fail")
    ([("fork", fork), ("base", newBase), ("files", toString (netOf before).size)]
      ++ (if drift.isEmpty then [] else [("drift", String.intercalate "," drift.toList)]))
  return .ok (before, after)

/-- The landing loop: feed the core one observation per action until it halts; `treeLive`
lets the caller's `finally` remove a tree an exception left. -/
def landLoop (e : Env) (ctr : IO.Ref Nat) (treeLive : IO.Ref Bool) (name : String)
    (mode : Mode) (wantPush : Bool) (gates : Array Gate) (gateset : String)
    (riders : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let plan : Array GateSpec := planOf gates
  let mut st := State.init name mode plan wantPush riders.toArray
  let mut act : Act := .probeMain
  let mut wt : String := ""
  say "run" "ok" ([("id", e.runId), ("dir", e.runDir), ("mode",
    if mode == .check then "check" else "land"), ("gateset", gateset)]
    ++ (if riders.isEmpty then [] else [("riders", String.intercalate "," riders)]))
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
        match ← readAgent e ctr "pre-branch" name st.prevMainTip with
        | .error what => pure (.garbled what)
        | .ok (.error m) => pure (.branchAbsent m)
        | .ok (.ok b) =>
          wt := b.wt
          pure (.branchStatus b.ahead b.behind b.clean b.tip b.landedFrom b.landedAs b.landedOnMain)
      | .probeRider i n => do
        match ← readAgent e ctr "rider-pre" n st.prevMainTip with
        | .error what => pure (.riderUnread i what)
        | .ok (.error m) => pure (.riderAbsent i m)
        | .ok (.ok b) =>
          pure (.riderStatus i b.ahead b.clean b.tip b.landedFrom b.landedAs b.landedOnMain)
      | .rebase tip onto => do
        match ← rebaseTree e ctr "rebase" tip onto with
        | .ok (head, ok) => pure (.rebaseOk head ok)
        | .error files => pure (.rebaseFailed files)
      | .rebaseRider i tip onto => do
        match ← rebaseTree e ctr "rider-rebase" tip onto with
        | .ok (head, ok) => pure (.riderRebaseOk i head ok)
        | .error files => pure (.riderRebaseFailed i files)
      | .netDiff oldTip newBase newTip => do
        match ← netListings e ctr "net" oldTip newBase newTip with
        | .ok (before, after) => pure (.netDiffs before after)
        | .error what => pure (.garbled what)
      | .netRider i oldTip newBase newTip => do
        match ← netListings e ctr "rider-net" oldTip newBase newTip with
        | .ok (before, after) => pure (.riderNetDiffs i before after)
        | .error what => pure (.riderUnread i what)
      | .recheckRiders => do
        let mut tips : Array Sha := #[]
        for r in st.riders do
          let t ← if r.standing == .riding then
              revParse e ctr "riders-recheck" s!"refs/heads/agent/{r.name}" (some e.mainWt)
            else pure ""
          if r.standing == .riding then
            say "riders-recheck" (if t == r.tip then "ok" else "fail")
              [("name", r.name), ("tip", if t.isEmpty then "?" else t), ("read", r.tip)]
          tips := tips.push t
        pure (.ridersRead tips)
      | .retree tip => do
        let tree := treePath e
        let r ← git e ctr "retree" #["checkout", "--detach", "--force", tip] (some tree)
        -- What a gate left in the tree goes, its ignored build output kept.
        let c ← git e ctr "retree" #["clean", "-fdq"] (some tree)
        let (head, clean) ← readTree e ctr "retree"
        let ok := r.code == 0 && c.code == 0 && head == tip && clean
        say "retree" (if ok then "ok" else "fail")
          [("tip", tip), ("head", if head.isEmpty then "?" else head),
           ("dirty", if clean then "no" else "yes")]
        pure (.retreed head clean)
      | .makeTree tip => do
        treeLive.set true
        let seed ← makeTree e ctr wt tip
        let (head, clean) ← readTree e ctr "gate-tree"
        say "gate-tree" (if head == tip && clean then "ok" else "fail")
          [("path", treePath e), ("head", if head.isEmpty then "?" else head),
           ("dirty", if clean then "no" else "yes"), ("seed", seed)]
        pure (.treeReady head clean)
      | .gate i g => do
        match gates[i]? with
        | none => pure (.garbled s!"no gate at index {i}")
        | some gd => do
          let o ← runGate e ctr gd i st.prevMainTip st.gatedTip
          let tail (head : Sha) (clean : Bool) : List (String × String) :=
            [("idx", toString i), ("head", if head.isEmpty then "?" else head),
             ("dirty", if clean then "no" else "yes")]
          match o with
          | .gateOk _ head clean =>
            -- A gate whose command passed but whose tree moved or was dirtied is a failed gate.
            let held := head == st.gatedTip && clean
            say s!"gate-{g}" (if held then "ok" else "fail")
              (tail head clean ++ (if held then [] else [("why", "the gate tree moved or was dirtied")]))
            pure o
          | .gateFail _ head clean =>
            say s!"gate-{g}" "fail" (tail head clean ++ [("log", s!"gate-{g}.log")]); pure o
          | _ => pure o
      | .recheckBranch => do
        -- The owner's branch as it reads now; this run never wrote it.
        let tip ← revParse e ctr "post-gate" s!"refs/heads/agent/{name}" (some e.mainWt)
        say "post-gate" (if tip == st.branchTip then "ok" else "fail")
          [("tip", if tip.isEmpty then "?" else tip), ("read", st.branchTip)]
        pure (.branchRecheck tip)
      | .recheckMain => do
        let onMain ← headIs e ctr "pre-merge" e.mainWt "refs/heads/main"
        let tip ← revParse e ctr "pre-merge" "refs/heads/main" (some e.mainWt)
        say "pre-merge" (if onMain && tip == st.prevMainTip then "ok" else "fail")
          [("head", if onMain then "main" else "not-main"),
           ("tip", if tip.isEmpty then "?" else tip), ("was", st.prevMainTip)]
        pure (.mainRecheck onMain tip)
      | .writeLanding => do
        let t1 ← IO.monoMsNow
        -- Each rider still riding, by name, read tip and commit in the train.
        let riding := st.riders.toList.filter (·.standing == .riding)
        let ok ← writeLedger e
          ([("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "landing"),
           ("gated", st.gatedTip), ("prev", st.prevMainTip), ("branch", st.branchTip)]
           ++ (if riding.isEmpty then [] else [("tip", st.headTip),
             ("riders", ridersField (riding.map fun r => (r.name, r.tip, r.rebased)))])
           ++ [("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)])
        say "announce" (if ok then "ok" else "fail") [("gated", st.gatedTip)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .fastForward tip => do
        -- `refs/heads/main` to exactly this commit by a local fast-forward push (`updateInstead`).
        let r ← git e ctr "fast-forward"
          #["push", "--porcelain",
            "--receive-pack=git -c receive.denyCurrentBranch=updateInstead receive-pack",
            ".", s!"{tip}:refs/heads/main"] (some e.mainWt)
        let onMain ← headIs e ctr "fast-forward" e.mainWt "refs/heads/main"
        let clean? ← statusClean e ctr "fast-forward" e.mainWt
        let facts := [("to", tip), ("head", if onMain then "main" else "not-main"),
          ("dirty", match clean? with | some true => "no" | some false => "yes" | none => "?")]
        if r.code == 0 then say "fast-forward" "ok" facts; pure .ffOk
        else
          say "fast-forward" "fail" (facts ++ [("log", "fast-forward.log")])
          pure .ffRejected
      | .readMain => do
        let mt ← revParse e ctr "verify" "refs/heads/main" (some e.mainWt)
        say "verify" (if mt == st.gatedTip && isSha mt then "ok" else "fail")
          [("main", if mt.isEmpty then "?" else mt), ("gated", st.gatedTip)]
        pure (.mainTip mt)
      | .writeLanded => do
        let t1 ← IO.monoMsNow
        -- One row per member, each naming the commit it landed as, the train's top last.
        let landedRiders := st.riders.toList.filter (·.standing == .landed)
        let train := if landedRiders.isEmpty then [] else [("train", e.runId)]
        let row (n tip branch : String) : List (String × String) :=
          [("ts", e.ts), ("run", e.runId), ("name", n),
           ("verdict", "landed"), ("tip", tip), ("gated", st.gatedTip),
           ("prev", st.prevMainTip), ("branch", branch),
           ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
           ("skipped", String.intercalate "," st.skipped.toList),
           ("pushed", if wantPush then "pending" else "no")] ++ train
          ++ [("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        let mut ok ← writeLedger e (row name (if landedRiders.isEmpty then st.mainAt else st.headTip)
          st.branchTip)
        for r in landedRiders do
          ok := ok && (← writeLedger e (row r.name r.rebased r.tip))
        say "ledger" (if ok then "ok" else "fail")
          ([("file", ledgerPath e)] ++ (if landedRiders.isEmpty then []
            else [("members", toString (landedRiders.length + 1))]))
        pure (if ok then .ledgerOk else .ledgerFail)
      | .push tip => do
        -- The gated tip, by sha, to the remote's `main`, never forced.
        let r ← git e ctr "push" #["push", "origin", s!"{tip}:refs/heads/main"] (some e.mainWt)
        if r.code == 0 then say "push" "ok" [("tip", tip)]; pure .pushOk
        else say "push" "fail" [("tip", tip), ("log", "push.log")]; pure .pushRejected
      | .readRemote => do
        -- `git ls-remote`, not the tracking ref, read by the exact refname `refs/heads/main`.
        let r ← git e ctr "verify-push"
          #["ls-remote", "origin", "refs/heads/main"] (some e.mainWt)
        let ot := lsRemoteTip r.out "refs/heads/main"
        say "verify-push" (if ot == st.mainAt && isSha ot then "ok" else "fail")
          [("remote", if ot.isEmpty then "?" else ot), ("landed", st.mainAt)]
        pure (.remoteTip ot)
      | .halt .. => pure (.garbled "halt")
    let (st', act') := step st obs
    st := st'
    act := act'
    match act with
    | .halt v code why =>
      -- The tree goes before the final line, so the line stays last.
      if ← treeLive.get then
        removeTree e ctr
        treeLive.set false
      let t1 ← IO.monoMsNow
      -- One record per distinct fact; the push confirmation is its own verdict.
      let base := [("ts", e.ts), ("run", e.runId), ("name", name)]
      let tail := [("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
      if v == .landed && wantPush then
        let ok ← writeLedger e (base ++ [("verdict", "pushed"), ("tip", st.mainAt),
          ("gated", st.gatedTip), ("remote", "origin/main")] ++ tail)
        if !ok then say "ledger" "fail" [("row", "pushed")]
      if v == .checked then
        let ok ← writeLedger e (base ++ [("verdict", "checked"), ("gated", st.gatedTip),
          ("branch", st.branchTip),
          ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
          ("skipped", String.intercalate "," st.skipped.toList)] ++ tail)
        if !ok then say "ledger" "fail" [("row", "checked")]
      if v == .refused || v == .failed || v == .landedUnpushed then
        let ok ← writeLedger e (base ++ [("verdict", v.name), ("why", why),
          ("gated", st.gatedTip), ("branch", st.branchTip)] ++ tail)
        if !ok then say "ledger" "fail" [("row", v.name)]
      -- Each rider's verdict before its place is settled, so its own run reads it there.
      for r in st.riders do
        match r.standing with
        | .refused rwhy =>
          let ok ← writeLedger e ([("ts", e.ts), ("run", e.runId), ("name", r.name),
            ("verdict", "refused"), ("why", rwhy), ("branch", r.tip), ("train", e.runId)] ++ tail)
          say "rider" "refused" [("name", r.name), ("why", rwhy),
            ("ledger", if ok then "ok" else "fail")]
        | .landed => say "rider" "landed" [("name", r.name), ("tip", r.rebased)]
        | _ => say "rider" "stays" [("name", r.name)]
      settleRiders e (st.riders.toList.filterMap fun r => match r.standing with
          | .landed | .refused _ => some r.name
          | _ => none)
        (st.riders.toList.filterMap fun r => match r.standing with
          | .landed | .refused _ => none
          | _ => some r.name)
      sayFinal v <|
        [("name", name), ("gateset", gateset), ("gates", toString st.gates.size),
         ("skipped", toString st.skipped.size), ("ms", toString (t1 - t0))]
        ++ (if st.branchTip.isEmpty then [] else [("branch", st.branchTip)])
        ++ (if st.gatedTip.isEmpty then [] else [("gated", st.gatedTip)])
        ++ (if st.mainAt.isEmpty then [] else [("tip", st.mainAt)])
        ++ (if why.isEmpty then [] else [("why", why)])
      return code
    | _ => pure ()
  return 3

/-- One landing run with its riders, the gate tree removed on every path out. -/
def landRun (e : Env) (name : String) (mode : Mode) (wantPush : Bool)
    (gates : Array Gate) (gateset : String) (riders : List String) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let treeLive ← IO.mkRef false
  try landLoop e ctr treeLive name mode wantPush gates gateset riders
  finally
    if ← treeLive.get then removeTree e ctr

/-- One ask for the lock under the queue's lock: enter or read the queue, decide this run's turn
with the runs' liveness and a train's `reach`, and on a take hold the landing lock, leave and
board the riders; a run that `holds` no place decides as if last and writes nothing. -/
def askTurn (e : Env) (queueH lockH : IO.FS.Handle) (me : Waiter) (enter holds : Bool)
    (reach : Nat) : IO (Turn × List Waiter) := do
  queueH.lock
  try
    let q0 ← readQueueAt e.common
    let mut liveRuns : Array String := #[]
    for r in (q0.map (·.run) ++ q0.map (·.train)).eraseDups do
      if !r.isEmpty && r != me.run && (← runLiveAt e.common r) then liveRuns := liveRuns.push r
    let live : String → Bool := (liveRuns.contains ·)
    let q := if !enter then q0
      else if holds then Queue.enter q0 live me
      else Queue.enter (Queue.leave q0 me.name) live me
    let t ← match Queue.turn q live me.name me.run true reach with
      | .take rs => do
        if ← lockH.tryLock then pure (Turn.take rs)
        else pure (Queue.turn q live me.name me.run false reach)
      | t => pure t
    let q' := if !holds then q0 else match t with
      | .take rs => Queue.board (Queue.leave q me.name) rs me.run
      | _ => q
    if q' != q0 then writeQueue e q'
    return (t, q')
  finally
    queueH.unlock

/-- The most branches a train takes in this repository: `land.trainCap` in its local config,
else `trainCap`. -/
def trainReach (e : Env) : IO Nat := do
  let ctr ← IO.mkRef 0
  let r ← git e ctr "queue" #["config", "--local", "--get", "land.trainCap"]
  return (if r.code == 0 then (trimWs r.out).toNat? else none).getD trainCap |>.max 1

/-- A gate list's fare: a digest of its gates, which a train's riders share with its head. -/
def fareOf (gates : Array Gate) : String := Id.run do
  let text := String.intercalate ";" (gates.toList.map fun g =>
    g.name ++ "=" ++ String.intercalate " " (g.cmd :: g.args.toList))
  let mut h : UInt64 := 14695981039346656037
  for b in text.toUTF8.toList do
    h := (h ^^^ b.toUInt64) * 1099511628211
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  return String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Hold the landing lock for `act`: a record found from a holder that died is marked
`abandoned` and its gate tree removed, this run's record written, and both released after. -/
def holdLock (e : Env) (h : IO.FS.Handle) (name : String) (act : IO UInt32) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let prev := trimWs (← try IO.FS.readFile (ownerPath e) catch _ => pure "")
  if prev.isEmpty then say "lock" "ok" [("path", lockPath e)]
  else
    let deadDir := recField prev "dir"
    let tree := s!"{deadDir}/tree"
    if !deadDir.isEmpty && (← System.FilePath.pathExists tree) then
      let _ ← git e ctr "lock" #["worktree", "remove", "--force", tree] (some e.mainWt)
      pure ()
    let ok ← writeLedger e [("ts", e.ts), ("run", recField prev "run"),
      ("name", recField prev "name"), ("verdict", "abandoned"), ("found", e.runId),
      ("pid", recField prev "pid"), ("dir", deadDir)]
    say "lock" "ok" [("path", lockPath e), ("abandoned", recField prev "run"),
      ("ledger", if ok then "ok" else "fail")]
  let record := s!"run={e.runId} pid={← IO.Process.getPID} name={name} dir={e.runDir}\n"
  try IO.FS.writeFile (ownerPath e) record catch _ => pure ()
  let r ← try act catch ex => do
    IO.eprintln s!"land: {ex}"
    pure 3
  try IO.FS.removeFile (ownerPath e) catch _ => pure ()
  h.unlock
  return r

/-- Drop `name`'s waiter under the queue's lock (`QueueOp.drop`), whether it was waiting. -/
def leaveQueue (e : Env) (name : String) : IO Bool := do
  try
    let qh ← IO.FS.Handle.mk (queueLockPath e) .append
    qh.lock
    try
      let q ← readQueueAt e.common
      let q' := Queue.leave q name
      if q' != q then writeQueue e q'
      return q' != q
    finally qh.unlock
  catch _ => return false

/-- The verdict a train's run recorded for a rider, by name and run: its last row there. -/
def riderVerdict (e : Env) (name train : String) : IO (Option String) := do
  match ← lastLedger e name with
  | some row => return if jsonField row "run" == some train then some row else none
  | none => return none

/-- One lock taker at a time, in arrival order among the live: the first takes the lock once free
with its riders, one in a train's reach waits, one beyond refuses with exit 2 keeping its place, a
rider waits for its train's verdict, and a taker that `holds` no place never waits. -/
def withTurn (e : Env) (name : String) (fare : String) (act : List String → IO UInt32)
    (holds : Bool := true) : IO UInt32 := do
  IO.FS.createDirAll s!"{e.common}/land"
  let fail (step path why : String) : IO UInt32 := do
    say step "fail" [("path", path), ("why", why)]
    sayFinal .failed [("name", name), ("why", why)]
    return 3
  let refuse (why : String) (kvs : List (String × String) := []) : IO UInt32 := do
    say "queue" "fail" ([("name", name)] ++ kvs ++ [("why", why)])
    sayFinal .refused [("name", name), ("why", why)]
    return 2
  let some h ← try some <$> IO.FS.Handle.mk (lockPath e) .append catch _ => pure none
    | fail "lock" (lockPath e) "the lock file cannot be opened"
  let some qh ← try some <$> IO.FS.Handle.mk (queueLockPath e) .append catch _ => pure none
    | fail "queue" (queueLockPath e) "the queue's lock file cannot be opened"
  if !queueable name then
    return ← refuse s!"agent/{name} names no branch: it holds whitespace or a control character"
  let reach ← trainReach e
  let me : Waiter :=
    { name, run := e.runId, pid := (← IO.Process.getPID).toNat, since := e.ts, fare, train := "" }
  let owner : IO String := do pure (trimWs (← try IO.FS.readFile (ownerPath e) catch _ => pure ""))
  let busy := "another landing holds the lock"
  let t0 ← IO.monoMsNow
  let mut said : Option Turn := none
  let mut rode : Option String := none
  -- The row the train this run rode wrote for this name, once the train is over, is the verdict.
  let trainVerdict (t : String) : IO (Option UInt32) := do
    let some row ← riderVerdict e name t | return none
    let fld (k : String) := (jsonField row k).getD ""
    if fld "verdict" == "landed" then
      let _ ← leaveQueue e name
      sayFinal .landed [("name", name), ("train", t), ("tip", fld "tip"), ("gated", fld "gated")]
      return some 0
    if fld "verdict" == "refused" then
      let _ ← leaveQueue e name
      sayFinal .refused [("name", name), ("train", t), ("why", fld "why")]
      return some 2
    return none
  let mut consulted : List String := []
  -- The train a dead place this run took over carried, whose verdict was another run's.
  let mut inherited : Option String := none
  for i in [0:turnBeats] do
    -- The trains this run saw itself ride, or its own place boarded, once each is over.
    let boarded := (((← try readQueueAt e.common catch _ => pure []).find? fun w =>
      w.name == name && w.run == e.runId).map (·.train)).filter fun t =>
        !t.isEmpty && inherited != some t
    for t in (rode.toList ++ boarded.toList).eraseDups do
      if !consulted.contains t && !(← runLiveAt e.common t) then
        if let some code ← trainVerdict t then return code
        consulted := consulted ++ [t]
        if rode == some t then rode := none
    let asked ← try pure (Except.ok (← askTurn e qh h me (i == 0) holds reach))
      catch ex => pure (Except.error (toString ex))
    if i == 0 then
      if let .ok (_, q) := asked then
        inherited := ((q.find? fun w => w.name == name && w.run == e.runId).map (·.train)).filter
          (!·.isEmpty)
    match asked with
    | .error why =>
      h.unlock
      return ← fail "queue" (queuePath e) s!"the queue could not be read or written: {why}"
    | .ok (.take rs, q) =>
      say "queue" "ok" ([("waited-ms", toString ((← IO.monoMsNow) - t0)),
        ("waiters", toString q.length)]
        ++ (if rs.isEmpty then [] else [("riders", String.intercalate "," rs)]))
      return ← holdLock e h name (act rs)
    | .ok (.wait, q) =>
      if !holds then
        say "lock" "fail" [("path", lockPath e), ("owner", ← owner)]
        return ← refuse s!"{busy} ({← owner}), and {name} takes no place in the queue: ask \
again once it is free"
      unless said == some .wait do
        say "queue" "wait" [("position", toString ((Queue.ahead q name).length + 1)),
          ("waiters", toString q.length), ("holder", recField (← owner) "name")]
        (← IO.getStdout).flush
        said := some .wait
      IO.sleep turnBeatMs
    | .ok (.rides t, _) =>
      unless said == some (.rides t) do
        say "queue" "ride" [("train", t), ("head", recField (← owner) "name")]
        (← IO.getStdout).flush
        said := some (.rides t)
      if inherited != some t then rode := some t
      IO.sleep turnBeatMs
    | .ok (.behind p hd, q) =>
      say "queue" "behind" [("position", toString p), ("head", hd),
        ("waiters", toString q.length)]
      say "lock" "fail" [("path", lockPath e), ("owner", ← owner)]
      let place := if holds then s!"agent/{name} keeps place {p}, behind {hd}; ask again to keep it"
        else s!"{name} takes no place in the queue, behind {hd}; ask again once it is free"
      sayFinal .refused [("name", name), ("why", s!"{busy} or is first in the queue: {place}")]
      return 2
    | .ok (.held r, _) =>
      return ← refuse s!"{busy} or waits for it: agent/{name} already waits for the lock in run \
{r}; ask again once that run ends" [("run", r)]
    | .ok (.gone, _) =>
      if let some t := rode then
        if let some code ← trainVerdict t then return code
      -- A train that took this name while this run did not run: main's landing of it answers.
      if let some row ← alreadyLanded e name then
        let fld (k : String) := (jsonField row k).getD ""
        sayFinal .landed [("name", name), ("train", (jsonField row "train").getD (fld "run")),
          ("tip", fld "tip"), ("gated", fld "gated")]
        return 0
      return ← refuse s!"agent/{name} left the queue while this run waited: it landed, retired \
or was made new (land new <name>)"
  refuse s!"{busy} ({← owner}) after agent/{name} waited {turnBeats * turnBeatMs.toNat / 60000} \
minutes in the queue: it keeps its place; ask again to keep it"

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
  -- A waiter under this name was a deleted branch's.
  if ← leaveQueue e name then say "queue" "ok" [("left", name)]
  -- Seed the build cache by copy, never hardlink: lake rewrites files in place.
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
      let tip ← revParse e ctr "pre" s!"refs/heads/agent/{name}" (some e.mainWt)
      if !isSha tip then
        say "pre" "fail" [("why", "the branch tip did not read back as a sha")]
        sayFinal .failed [("name", name)]
        return 3
      let rm ← git e ctr "pre"
        #["merge-base", "--is-ancestor", tip, "main"] (some e.mainWt)
      -- Rebased copies landed, so the ledger, not ancestry, says what it landed as.
      let landedAs ← if rm.code == 0 then pure "" else landedTipOf e ctr name tip
      if rm.code != 0 && landedAs.isEmpty then
        say "pre" "fail" [("branch", s!"agent/{name}"), ("merged", "no")]
        sayFinal .refused [("name", name)]
        return 2
      say "pre" "ok" ([("worktree", p), ("merged", "yes")]
        ++ (if landedAs.isEmpty then [] else [("landed-as", landedAs)]))
      let rr ← git e ctr "worktree-remove" #["worktree", "remove", p] (some e.mainWt)
      if rr.code != 0 then
        say "worktree-remove" "fail" [("log", "worktree-remove.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "worktree-remove" "ok" [("path", p)]
      -- Deleted by compare-and-swap against the tip read above.
      let rd ← git e ctr "branch-delete"
        #["update-ref", "-d", s!"refs/heads/agent/{name}", tip] (some e.mainWt)
      if rd.code != 0 then
        say "branch-delete" "fail" [("log", "branch-delete.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "branch-delete" "ok" [("branch", s!"agent/{name}"), ("was", tip)]
      if ← leaveQueue e name then say "queue" "ok" [("left", name)]
      let _ ← writeLedger e
        [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "retired"),
         ("branch", tip), ("dir", e.runDir)]
      sayFinal .retired [("name", name)]
      return 0

/-- Publish the last landing: `main` must read at the last `landed` row's tip, its gated
tip; the push names that sha, never forced, and the remote is read back by its exact
refname. -/
def landPush (e : Env) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  say "run" "ok" [("id", e.runId), ("dir", e.runDir), ("mode", "push")]
  let row ← lastVerdict e "landed" none
  let fld (k : String) : String := match row with
    | some l => (jsonField l k).getD ""
    | none => ""
  let name := fld "name"
  let mt ← revParse e ctr "pre" "refs/heads/main" (some e.mainWt)
  match pushPlan (fld "tip") (fld "gated") mt with
  | .error why =>
    say "pre" "fail" [("main", if mt.isEmpty then "?" else mt),
      ("landed", if (fld "tip").isEmpty then "?" else fld "tip"), ("why", why)]
    sayFinal .refused [("why", why)]
    return 2
  | .ok tip =>
    say "pre" "ok" [("main", mt), ("landed", tip), ("name", name), ("run", fld "run")]
    let r0 ← git e ctr "pre" #["ls-remote", "origin", "refs/heads/main"] (some e.mainWt)
    if r0.code != 0 then
      say "pre" "fail" [("why", "the remote cannot be read"), ("log", "pre.log")]
      sayFinal .refused [("why", "the remote cannot be read")]
      return 2
    if lsRemoteTip r0.out "refs/heads/main" == tip then
      -- Nothing to publish, so nothing to record.
      sayFinal .pushed [("name", name), ("tip", tip), ("already", "yes")]
      return 0
    let rp ← git e ctr "push" #["push", "origin", s!"{tip}:refs/heads/main"] (some e.mainWt)
    say "push" (if rp.code == 0 then "ok" else "fail") [("tip", tip), ("log", "push.log")]
    let r1 ← git e ctr "verify-push" #["ls-remote", "origin", "refs/heads/main"] (some e.mainWt)
    let after := lsRemoteTip r1.out "refs/heads/main"
    let v := pushVerdict (rp.code == 0) after tip
    say "verify-push" (if v == .pushed then "ok" else "fail")
      [("remote", if after.isEmpty then "?" else after), ("landed", tip)]
    let why := if v == .pushed then ""
      else "the push was rejected, or the remote's main did not read back at the landed tip"
    let t1 ← IO.monoMsNow
    let ok ← writeLedger e ([("ts", e.ts), ("run", e.runId), ("name", name),
      ("verdict", v.name), ("tip", tip), ("gated", tip), ("remote", "origin/main"),
      ("landed-run", fld "run"), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
      ++ (if why.isEmpty then [] else [("why", why)]))
    if !ok then say "ledger" "fail" [("row", v.name)]
    sayFinal v ([("name", name), ("tip", tip), ("remote", if after.isEmpty then "?" else after),
      ("ms", toString (t1 - t0))] ++ (if why.isEmpty then [] else [("why", why)]))
    return (if v == .pushed then 0 else 4)

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
  let holder := trimWs (← try IO.FS.readFile (ownerPath e) catch _ => pure "")
  if holder.isEmpty then say "lock" "free" []
  else
    let live ← runLive (recField holder "dir")
    say "lock" "held" [("name", recField holder "name"), ("run", recField holder "run"),
      ("pid", recField holder "pid"), ("live", if live then "yes" else "no")]
  let q ← readQueueAt e.common
  for (w, i) in q.zipIdx do
    let live ← waiterLive e w
    say "queue" "ok" [("position", toString (i + 1)), ("name", w.name), ("run", w.run),
      ("pid", toString w.pid), ("since", w.since), ("live", if live then "yes" else "no")]
  let n := (wts.filter (·.branch.startsWith "agent/")).size
  sayFinal .listed [("worktrees", toString n), ("waiters", toString q.length)]
  return 0

structure Case where
  label : String
  mode : Mode
  push : Bool
  obs : List Obs
  verdict : Verdict
  code : UInt32
  /-- Must the run have proposed no ref change at all? -/
  noMutation : Bool
  /-- The gate plan the run is driven against; the shipped list unless a case needs its
  own. -/
  plan : Option (Array GateSpec) := none
  /-- The branches riding behind the run's own. -/
  riders : Array String := #[]
  /-- Where each rider must stand at the end. -/
  standings : List String := []

def gatePlan : Array GateSpec := planOf gateList

def sha1s : Sha := "1111111111111111111111111111111111111111"
def sha2s : Sha := "2222222222222222222222222222222222222222"
def sha3s : Sha := "3333333333333333333333333333333333333333"
def sha4s : Sha := "4444444444444444444444444444444444444444"
def sha5s : Sha := "5555555555555555555555555555555555555555"
def sha6s : Sha := "6666666666666666666666666666666666666666"
def sha7s : Sha := "7777777777777777777777777777777777777777"

def okGates : List Obs := (List.range gatePlan.size).map fun i => Obs.gateOk i sha3s true

/-- One file's change as `git diff-tree -p -U0` prints it. -/
def netListing (idx hunk : String) (body : List String) : String :=
  s!"diff --git a/PLAN.md b/PLAN.md\nindex {idx} 100644\n--- a/PLAN.md\n+++ b/PLAN.md\n{hunk}\n"
    ++ String.join (body.map (· ++ "\n"))

/-- The branch's change: a new entry under a heading its second commit renamed. -/
def netBranch : String :=
  netListing "1a2b3c4..5d6e7f8" "@@ -4,0 +5,3 @@ body a" ["+", "+### b-final", "+body b"]

/-- The same change replayed onto a base that appended an entry first. -/
def netMoved : String :=
  netListing "9f8e7d6..c5b4a39" "@@ -7,0 +8,3 @@ body m" ["+", "+### b-final", "+body b"]

/-- The union driver's keep-both: the heading the branch renamed away came back with no
conflict. -/
def netUnion : String :=
  netListing "9f8e7d6..d4c3b2a" "@@ -7,0 +8,4 @@ body m"
    ["+### b-draft", "+", "+### b-final", "+body b"]

def netSame : Obs := .netDiffs netBranch netMoved

/-- A plan every one of whose gates may be absent: the vacuity case. -/
def allSkippablePlan : Array GateSpec :=
  #[{ name := "a", mayAbsent := true }, { name := "b", mayAbsent := true }]

/-- A plan whose second gate may be absent. -/
def oneSkippablePlan : Array GateSpec :=
  #[{ name := "a", mayAbsent := false }, { name := "b", mayAbsent := true }]

/-- Scripted trains behind the run's own branch, read at `sha2s` and rebased to `sha3s`. -/
def trainCases (pre : List Obs) : List Case :=
  let rider (i : Nat) (tip kept : Sha) : List Obs :=
    [.riderStatus i 1 true tip "" "" false, .riderRebaseOk i kept true,
      .riderNetDiffs i netBranch netMoved]
  let gatesAt (t : Sha) : List Obs := (List.range gatePlan.size).map fun i => Obs.gateOk i t true
  let merge (tips : Array Sha) (top : Sha) : List Obs :=
    [.branchRecheck sha2s, .ridersRead tips, .mainRecheck true sha1s, .ledgerOk, .ffOk,
      .mainTip top, .ledgerOk]
  let alone : List Obs :=
    [.branchRecheck sha2s, .mainRecheck true sha1s, .ledgerOk, .ffOk, .mainTip sha3s, .ledgerOk]
  let first := rider 0 sha4s sha5s
  let second := rider 1 sha6s sha7s
  let read := Obs.riderStatus 0 1 true sha4s "" "" false
  let at3 := gatesAt sha3s
  let at5 := gatesAt sha5s
  let at7 := gatesAt sha7s
  let both := merge #[sha4s, sha6s] sha7s
  let onlySecond := merge #["", sha6s] sha7s
  let onlyFirst := merge #[sha4s, ""] sha5s
  let two := #["r1", "r2"]
  [ { label := "a train of three lands on the train's tip", mode := .land
    , push := false, riders := two, obs := pre ++ first ++ second ++ at7 ++ both
    , verdict := .landed, code := 0, noMutation := false, standings := ["landed", "landed"] }
  , { label := "a rider's conflict leaves it refused, and the train goes on", mode := .land
    , push := false, riders := two
    , obs := pre ++ [read, .riderRebaseFailed 0 #["PLAN.md"], .retreed sha3s true] ++ second
        ++ at7 ++ onlySecond
    , verdict := .landed, code := 0, noMutation := false, standings := ["refused", "landed"] }
  , { label := "a rider's rebase that left the tree dirty leaves it refused, the tree put back"
    , mode := .land, push := false, riders := #["r1"]
    , obs := pre ++ [read, .riderRebaseOk 0 sha5s false, .retreed sha3s true] ++ at3 ++ alone
    , verdict := .landed, code := 0, noMutation := false, standings := ["refused"] }
  , { label := "a rider's rebase whose head reads as no sha leaves it refused, the tree put back"
    , mode := .land, push := false, riders := #["r1"]
    , obs := pre ++ [read, .riderRebaseOk 0 "" true, .retreed sha3s true] ++ at3 ++ alone
    , verdict := .landed, code := 0, noMutation := false, standings := ["refused"] }
  , { label := "a red train falls back to the run's own branch, the rider staying queued"
    , mode := .land, push := false, riders := #["r1"]
    , obs := pre ++ first ++ [.gateFail 0 sha5s true, .retreed sha3s true] ++ at3 ++ alone
    , verdict := .landed, code := 0, noMutation := false, standings := ["stays"] }
  , { label := "a train's gate that dirtied the tree falls back to the run's own branch"
    , mode := .land, push := false, riders := #["r1"]
    , obs := pre ++ first ++ [.gateOk 0 sha5s false, .retreed sha3s true] ++ at3 ++ alone
    , verdict := .landed, code := 0, noMutation := false, standings := ["stays"] }
  , { label := "a rider that moved during the gates is cut, and the train before it gated again"
    , mode := .land, push := false, riders := two
    , obs := pre ++ first ++ second ++ at7
        ++ [.branchRecheck sha2s, .ridersRead #[sha4s, sha1s], .retreed sha5s true]
        ++ at5 ++ onlyFirst
    , verdict := .landed, code := 0, noMutation := false, standings := ["landed", "stays"] }
  , { label := "a rider git could not read leaves the train before its rebase", mode := .land
    , push := false, riders := two
    , obs := pre ++ [.riderUnread 0 "git rev-list --count"] ++ second ++ at7 ++ onlySecond
    , verdict := .landed, code := 0, noMutation := false, standings := ["refused", "landed"] }
  , { label := "a rider git could not compare leaves the train, the tree put back"
    , mode := .land, push := false, riders := #["r1"]
    , obs := pre ++ [read, .riderRebaseOk 0 sha5s true, .riderUnread 0 "git diff-tree",
        .retreed sha3s true] ++ at3 ++ alone
    , verdict := .landed, code := 0, noMutation := false, standings := ["refused"] }
  , { label := "a rider answering out of turn is an internal failure", mode := .land
    , push := false, riders := two
    , obs := pre ++ [.riderStatus 1 1 true sha4s "" "" false]
    , verdict := .failed, code := 3, noMutation := true, standings := ["riding", "riding"] } ]

def cases : List Case :=
  let bs (ahead behind : Nat) : Obs := .branchStatus ahead behind true sha2s "" "" false
  let pre := [Obs.mainStatus true true sha1s, bs 1 0, Obs.treeReady sha2s true,
    Obs.rebaseOk sha3s true, netSame]
  let landOk := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
    .ledgerOk, .ffOk, .mainTip sha3s, .ledgerOk]
  let trains := trainCases pre
  [ { label := "lands with every gate ok", mode := .land, push := false
    , obs := landOk, verdict := .landed, code := 0, noMutation := false }
  , { label := "lands and pushes, the remote reads back at the landed tip"
    , mode := .land, push := true
    , obs := landOk ++ [.pushOk, .remoteTip sha3s]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "the remote reads back at another commit: landed, not pushed"
    , mode := .land, push := true
    , obs := landOk ++ [.pushOk, .remoteTip sha1s]
    , verdict := .landedUnpushed, code := 4, noMutation := false }
  , { label := "the push is rejected: landed, not pushed", mode := .land, push := true
    , obs := landOk ++ [.pushRejected]
    , verdict := .landedUnpushed, code := 4, noMutation := false }
  , { label := "the remote's main does not read back: landed, not pushed"
    , mode := .land, push := true
    , obs := landOk ++ [.pushOk, .remoteTip ""]
    , verdict := .landedUnpushed, code := 4, noMutation := false }
  , { label := "check stops before the merge", mode := .check, push := false
    , obs := pre ++ okGates, verdict := .checked, code := 0, noMutation := true }
  , { label := "the branch moved during the landing", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha1s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch reads at the gated tip, which it never was", mode := .land
    , push := false, obs := pre ++ okGates ++ [.branchRecheck sha3s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a gate moved the gate tree", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha1s true]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "a gate left the gate tree dirty", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha3s false]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the tree moved around a gate reads as no sha", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 "" true]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "a failing gate that also moved the tree", mode := .land, push := false
    , obs := pre ++ [.gateFail 0 sha1s false]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the last gate moved the tree", mode := .land, push := true
    , obs := pre ++ (List.range (gatePlan.size - 1)).map (fun i => Obs.gateOk i sha3s true)
        ++ [.gateOk (gatePlan.size - 1) sha2s true]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the gate tree was not made at the branch tip", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady sha1s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the gate tree was dirty when made", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady sha2s false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the gate tree did not read back", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady "" false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a gate before the rebase", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady sha2s true,
        .gateOk 0 sha2s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a rebase before the gate tree", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .rebaseOk sha3s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the gate tree dirty or on a branch after the rebase", mode := .land
    , push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady sha2s true,
        .rebaseOk sha3s false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the rebase kept a line the branch deleted: refused, nothing put back"
    , mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 1, .treeReady sha2s true,
        .rebaseOk sha3s true, .netDiffs netBranch netUnion]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a drifted rebase in check mode is refused too", mode := .check, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 1, .treeReady sha2s true,
        .rebaseOk sha3s true, .netDiffs netBranch netUnion]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a file only the rebase touched is drift", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 1, .treeReady sha2s true,
        .rebaseOk sha3s true, .netDiffs "" netMoved]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a branch already landed, and not moved since", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, .branchStatus 1 1 true sha2s sha2s sha3s true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a landed branch continued after its landing", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, .branchStatus 2 1 true sha2s sha1s sha3s true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a landing main no longer holds bars nothing: the unmoved branch lands"
    , mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, .branchStatus 1 1 true sha2s sha2s sha4s false,
        .treeReady sha2s true, .rebaseOk sha3s true, netSame] ++ okGates
        ++ [.branchRecheck sha2s, .mainRecheck true sha1s, .ledgerOk, .ffOk, .mainTip sha3s,
            .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "a landing main no longer holds bars nothing: the continued branch lands"
    , mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, .branchStatus 2 1 true sha2s sha1s sha4s false,
        .treeReady sha2s true, .rebaseOk sha3s true, netSame] ++ okGates
        ++ [.branchRecheck sha2s, .mainRecheck true sha1s, .ledgerOk, .ffOk, .mainTip sha3s,
            .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false }
  , { label := "main moved during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the main worktree left main during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck false sha1s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "main reads back at another commit after the merge"
    , mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
        .ledgerOk, .ffOk, .mainTip sha1s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "a truncated sha is not a sha", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, bs 1 0, .treeReady sha2s true,
        .rebaseOk "33333333" true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the fast-forward is rejected", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
        .ledgerOk, .ffRejected]
    , verdict := .refused, code := 2, noMutation := false }
  , { label := "a rebase conflict in the gate tree", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, bs 3 2, .treeReady sha2s true,
        .rebaseFailed #["LeanTex/Core/Ir.lean", "Tests/Diag.lean"]]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a rebase that stopped with no unmerged path", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, bs 3 2, .treeReady sha2s true, .rebaseFailed #[]]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a gate fails", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha3s true, .gateFail 1 sha3s true]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "the last gate fails", mode := .land, push := true
    , obs := pre ++ (List.range (gatePlan.size - 1)).map (fun i => Obs.gateOk i sha3s true)
        ++ [.gateFail (gatePlan.size - 1) sha3s true]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "a gate answering out of turn is an internal failure"
    , mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha3s true, .gateOk 0 sha3s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a gate claiming an index past the plan", mode := .land, push := false
    , obs := pre ++ okGates ++ [.gateOk gatePlan.size sha3s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "an absence the plan does not permit", mode := .land, push := false
    , obs := pre ++ [.gateAbsent 0]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "every gate absent proves nothing", mode := .land, push := false
    , obs := pre ++ [.gateAbsent 0, .gateAbsent 1]
    , verdict := .failed, code := 1, noMutation := true
    , plan := some allSkippablePlan }
  , { label := "a permitted absence still lands", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha3s true, .gateAbsent 1]
        ++ [.branchRecheck sha2s, .mainRecheck true sha1s, .ledgerOk, .ffOk,
            .mainTip sha3s, .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false
    , plan := some oneSkippablePlan }
  , { label := "the shipped list permits no absence", mode := .land, push := false
    , obs := pre ++ (List.range (gatePlan.size - 1)).map (fun i => Obs.gateOk i sha3s true)
        ++ [.gateAbsent (gatePlan.size - 1)]
    , verdict := .failed, code := 1, noMutation := true }
  , { label := "garbled status at the first probe", mode := .land, push := false
    , obs := [.garbled "git status --porcelain"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled rev-list at the branch probe", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .garbled "rev-list counts"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "garbled output mid-gate", mode := .land, push := false
    , obs := pre ++ [.gateOk 0 sha3s true, .garbled "gate output"]
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
    , obs := [.mainStatus true true sha1s, bs 0 4]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 2 0 false sha2s "" "" false]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "an observation out of order", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .ffOk]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the write-ahead row was not written", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
        .ledgerFail]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the landed row was not written", mode := .land, push := true
    , obs := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
        .ledgerOk, .ffOk, .mainTip sha3s, .ledgerFail]
    , verdict := .failed, code := 3, noMutation := false } ] ++ trains

/-- The final halt of a scripted run: verdict and exit code. -/
def finalOf (acts : Array Act) : Option (Verdict × UInt32) :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .halt v c _ => some (v, c)
    | _ => acc

/-- Where a rider stands, as a case names it. -/
def standingLabel : Standing → String
  | .riding => "riding"
  | .landed => "landed"
  | .refused _ => "refused"
  | .stays => "stays"

/-- The run a scripted case drives. -/
def caseInit (c : Case) : State := State.init "probe" c.mode (c.plan.getD gatePlan) c.push c.riders

/-- What is wrong with a scripted case, or nothing. -/
def caseFault (c : Case) : Option String :=
  let (fin, acts) := Land.run (caseInit c) c.obs
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
    else if fin.riders.toList.map (standingLabel ·.standing) != c.standings then
      some s!"standings {fin.riders.toList.map (standingLabel ·.standing)}"
    else none

/-- The fast-forward a scripted run proposed, if any. -/
def ffTipOf (acts : Array Act) : Option Sha :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .fastForward t => some t
    | _ => acc

/-- The push a scripted run proposed, if any: its sha, as `ffTipOf`. -/
def pushTipOf (acts : Array Act) : Option Sha :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .push t => some t
    | _ => acc

/-- The net comparison over hand-written listings: (before, after, the files the drift
must name). -/
def netCases : List (String × String × String × Array String) :=
  let modeLine (m : String) :=
    s!"diff --git a/run.sh b/run.sh\nold mode 100644\nnew mode {m}\n"
  [ ("the same change at another position", netBranch, netMoved, #[])
  , ("a line the union driver kept", netBranch, netUnion, #["PLAN.md"])
  , ("a file the rebase alone touched", "", netMoved, #["PLAN.md"])
  , ("a file the rebase dropped", netBranch, "", #["PLAN.md"])
  , ("a mode the rebase changed", modeLine "100755", modeLine "100644", #["run.sh"])
  , ("two files, one drifted", netBranch ++ modeLine "100755", netMoved ++ modeLine "100644",
      #["run.sh"])
  , ("a missing newline at the end is content",
      netBranch, netMoved ++ "\\ No newline at end of file\n", #["PLAN.md"]) ]

def selftest : IO UInt32 := do
  let mut bad := 0
  -- A command's output reads one-to-one: UTF-8 as itself, a Latin-1 byte by
  -- its value, a backslash doubled only where it must be told from one.
  let latin : ByteArray := ⟨#[0x43, 0x61, 0x66, 0xE9]⟩
  let spelled : ByteArray := "Caf\\xE9".toUTF8
  for (why, ok) in [("UTF-8 output reads as itself", outputText "Café \\x".toUTF8 == "Café \\x"),
      ("a byte UTF-8 does not claim is spelled by its value", outputText latin == "Caf\\xE9"),
      ("a backslash in a spelled output is doubled", spelledText spelled == "Caf\\\\xE9"),
      ("a byte and the text of its spelling spell apart", spelledText latin != spelledText spelled)] do
    if ok then say "selftest" "ok" [("case", why)]
    else
      bad := bad + 1
      say "selftest" "fail" [("case", why)]
  for c in cases do
    match caseFault c with
    | some why =>
      bad := bad + 1
      say "selftest" "fail" [("case", c.label), ("why", why)]
    | none => say "selftest" "ok" [("case", c.label)]
  -- Some case must reach a merge, and every merge a case reaches must name the gated tip.
  let runs := cases.map fun c => (c, Land.run (caseInit c) c.obs)
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
    match pushTipOf r.2 with
    | none => pure ()
    | some t =>
      if t != r.1.gatedTip || t != r.1.mainAt || !isSha t then
        bad := bad + 1
        say "selftest" "fail" [("case", c.label), ("why", "the push does not name the gated tip")]
  say "selftest" "ok" [("case", "every merge and every push names the gated tip")]
  if !(runs.any fun (_, r) => (pushTipOf r.2).isSome) then
    bad := bad + 1
    say "selftest" "fail" [("case", "coverage"), ("why", "no case reaches a push")]
  -- The write statement over every case's trace, both shared writes reached.
  let traces := cases.map fun c => (c, Land.trace (caseInit c) c.obs)
  let allWrites := traces.flatMap fun (_, tr) =>
    tr.flatMap fun (st, a) => a.writes.map (st, ·)
  let unowned := allWrites.filter fun (st, w) => !w.owned st
  let reaches (p : Writes → Bool) := allWrites.any fun (_, w) => p w
  if !unowned.isEmpty then
    bad := bad + 1
    say "selftest" "fail" [("case", "every write owned"),
      ("why", s!"{unowned.length} writes not owned")]
  else if !(reaches fun w => match w with | .mainTo _ => true | _ => false)
      || !(reaches fun w => match w with | .remoteTo _ => true | _ => false) then
    bad := bad + 1
    say "selftest" "fail" [("case", "every write owned"),
      ("why", "no case reaches the fast-forward's write, or the push's")]
  else if reaches fun w => match w with | .foreign => true | _ => false then
    bad := bad + 1
    say "selftest" "fail" [("case", "every write owned"),
      ("why", "a case writes a ref or a worktree the run does not own")]
  else say "selftest" "ok" [("case", "every write owned, and none to a branch or worktree it does \
not own")]
  -- The landed refusal sends the next unit to a new branch and writes this one nowhere.
  let barredCases : List (String × Obs × Bool) :=
    [ ("unmoved", .branchStatus 1 1 true sha2s sha2s sha3s true, false)
    , ("continued", .branchStatus 2 1 true sha2s sha1s sha3s true, true) ]
  for (label, o, since) in barredCases do
    let (_, acts) := Land.run (State.init "probe" .land gatePlan false)
      [.mainStatus true true sha1s, o]
    let has (w t : String) : Bool := (w.splitOn t).length > 1
    match acts.back? with
    | some (.halt v c why) =>
      if v == .refused && c == 2 && has why "land new <name>" && !has why "rebase"
          && has why s!"as {sha3s}" && (has why s!"{sha1s}..{sha2s}" == since) then
        say "selftest" "ok" [("case", s!"the landed refusal names a new branch: {label}")]
      else
        bad := bad + 1
        say "selftest" "fail" [("case", s!"the landed refusal: {label}"), ("why", why)]
    | _ =>
      bad := bad + 1
      say "selftest" "fail" [("case", s!"the landed refusal: {label}"), ("why", "no halt")]
  -- The remote read-back reads exactly `refs/heads/main`.
  let lsCases : List (String × String × Sha) :=
    [ ("the decoy sorts first", s!"{sha1s}\trefs/heads/a/refs/heads/main\n{sha2s}\trefs/heads/main\n",
        sha2s)
    , ("only a decoy", s!"{sha1s}\trefs/heads/a/refs/heads/main\n", "")
    , ("nothing printed", "", "")
    , ("the ref twice", s!"{sha1s}\trefs/heads/main\n{sha2s}\trefs/heads/main\n", "")
    , ("one exact line", s!"{sha3s}\trefs/heads/main\n", sha3s) ]
  for (label, out, want) in lsCases do
    if lsRemoteTip out "refs/heads/main" != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"ls-remote: {label}"),
        ("why", s!"read {lsRemoteTip out "refs/heads/main"}")]
    else say "selftest" "ok" [("case", s!"ls-remote: {label}")]
  -- `land push`'s two decisions, which the scenarios reach only through git.
  let planCases : List (String × Sha × Sha × Sha × Option Sha) :=
    [ ("publishes the last landed tip", sha3s, sha3s, sha3s, some sha3s)
    , ("no landed row", "", "", sha3s, none)
    , ("a landed row whose tip is not its gated tip", sha3s, sha2s, sha3s, none)
    , ("a commit on main no landing gated", sha3s, sha3s, sha1s, none) ]
  for (label, lt, lg, mt, want) in planCases do
    let got := match pushPlan lt lg mt with
      | .ok t => some t
      | .error _ => none
    if got != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"push plan: {label}"), ("why", "wrong answer")]
    else say "selftest" "ok" [("case", s!"push plan: {label}")]
  let verdictCases : List (String × Bool × Sha × Sha × Verdict) :=
    [ ("pushed and read back", true, sha3s, sha3s, .pushed)
    , ("rejected", false, sha3s, sha3s, .landedUnpushed)
    , ("read back at another commit", true, sha1s, sha3s, .landedUnpushed)
    , ("nothing read back", true, "", "", .landedUnpushed) ]
  for (label, ok, r, t, want) in verdictCases do
    if pushVerdict ok r t != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"push verdict: {label}"), ("why", "wrong verdict")]
    else say "selftest" "ok" [("case", s!"push verdict: {label}")]
  -- The net comparison, which the scenarios reach only through git.
  for (label, before, after, want) in netCases do
    let got := netDrift (netOf before) (netOf after)
    if got != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"net: {label}"),
        ("why", s!"drift [{String.intercalate "," got.toList}]")]
    else say "selftest" "ok" [("case", s!"net: {label}")]
  -- The gate-list parser, which no repository state reaches.
  let badSpecs := ["a=true;b", "a=true;a=false", "", "=true"]
  for spec in badSpecs do
    match parseGates spec with
    | .ok gs =>
      bad := bad + 1
      say "selftest" "fail" [("case", s!"override {spec}"),
        ("why", s!"parsed {gs.size} gates instead of refusing")]
    | .error _ => say "selftest" "ok" [("case", s!"override refuses {spec}")]
  match parseGates "a=true;b=false arg" with
  | .ok gs =>
    if gs.size == 2 && gs[1]!.args == #["arg"] then
      say "selftest" "ok" [("case", "override parses two gates")]
    else
      bad := bad + 1
      say "selftest" "fail" [("case", "override parses two gates"), ("why", "wrong shape")]
  | .error e =>
    bad := bad + 1
    say "selftest" "fail" [("case", "override parses two gates"), ("why", e.why)]
  -- The shipped list reads back through that parser, every line as one gate, in order.
  match parseGates (String.intercalate ";" defaultGates) with
  | .ok gs =>
    let names := defaultGates.map fun l => trimWs ((l.splitOn "=").headD "")
    if gs.toList.map (·.name) == names && gateList.size == defaultGates.length
        && gatePlan.all (!·.mayAbsent) && (gateList.any (·.name == "scoreboard-check"))
        && (gateList.any (·.name == "scoreboard-selftest")) then
      say "selftest" "ok" [("case", "the shipped gate list parses, one gate per line")]
    else
      bad := bad + 1
      say "selftest" "fail" [("case", "the shipped gate list parses, one gate per line"),
        ("why", s!"{gs.size} gates from {defaultGates.length} lines")]
  | .error e =>
    bad := bad + 1
    say "selftest" "fail" [("case", "the shipped gate list parses, one gate per line"),
      ("why", e.why)]
  -- Every source area shares the strict build, the added lines' conventions, then the test and
  -- lint drivers.
  let grouped : Bool := match gateList.toList with
    | build :: conventions :: test :: lint :: _ =>
      build.cmd == "lake" && build.args[0]? == some "build"
        && build.args.contains "--wfail"
        && #["LeanTex", "TestsModules", "ScriptsModules", "leantex", "Tests", "precommit",
            "proofcheck", "lint", "cites", "land", "scoreboard"].all
          (build.args.contains ·)
        && conventions.name == "conventions"
        && test.cmd == "lake" && test.args == #["test"]
        && lint.cmd == "lake" && lint.args == #["lint"]
        && (gateList.filter fun g => g.cmd == "lake" && g.args[0]? == some "build").size == 1
    | _ => false
  if grouped then
    say "selftest" "ok" [("case", "strict maintained-source build, conventions, test and lint")]
  else
    bad := bad + 1
    say "selftest" "fail"
      [("case", "strict maintained-source build, conventions, test and lint")]
  let conventions := match (gateList.filter (·.name == "conventions")).toList with
    | [g] => g.cmd == ".lake/build/bin/precommit" &&
      g.args == #["--range", "{main}...{tip}", "--conventions"] &&
      gateArgs "m" "t" g.args == #["--range", "m...t", "--conventions"]
    | _ => false
  if conventions && gateArgs "m" "t" #["--base", "{main}"] == #["--base", "m"] then
    say "selftest" "ok" [("case", "the conventions gate reads the lines the landing adds")]
  else
    bad := bad + 1
    say "selftest" "fail" [("case", "the conventions gate reads the lines the landing adds")]
  let baseline := gateList.filter (·.name == "scoreboard-base")
  if baseline.size == 1 &&
      baseline[0]!.cmd == ".lake/build/bin/scoreboard" &&
      baseline[0]!.args == #["--check", "--base", "{main}"] then
    say "selftest" "ok" [("case", "scoreboard compares against the pinned landing base")]
  else
    bad := bad + 1
    say "selftest" "fail" [("case", "scoreboard compares against the pinned landing base")]
  -- Porcelain quoting: a value with a space must come back as one value.
  if pv "a b" != "\"a b\"" || pv "ab" != "ab" || pv "" != "\"\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "porcelain quoting"), ("why", "wrong form")]
  else say "selftest" "ok" [("case", "porcelain quoting")]
  if jsonStr "a\u0001b" != "\"a\\u0001b\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "ledger escaping"), ("why", "a control byte survived")]
  else say "selftest" "ok" [("case", "ledger escaping")]
  -- The queue's file and its decisions, which the scenarios reach only through processes.
  let wtr (n r : String) (p : Nat := 7) (fare : String := "") (train : String := "") : Waiter :=
    ⟨n, r, p, "2026-10-14T00:00:00Z", fare, train⟩
  let ws := [wtr "a" "20261014T000000000000000-11" 11,
    wtr "b-2" "20261014T000000000000001-22" 22 "f00d" "20261014T000000000000000-11"]
  let txt := String.join (ws.map (waiterLine · ++ "\n"))
  let q3 := [wtr "a" "ra", wtr "b" "rb", wtr "c" "rc"]
  let liveB : String → Bool := (· == "rb")
  let all : String → Bool := fun _ => true
  let qf := [wtr "a" "ra" 7 "f", wtr "b" "rb" 7 "f", wtr "c" "rc" 7 "f", wtr "d" "rd" 7 "g"]
  let queueCases : List (String × Bool) :=
    [ ("the queue's lines read back as the waiters written", queueOfText txt == ws)
    , ("a line that is not a waiter's is dropped",
        queueOfText ("garbage\nname=x run=y\n" ++ txt) == ws)
    , ("a name's later line is dropped",
        queueOfText (txt ++ waiterLine (wtr "a" "r9") ++ "\n") == ws)
    , ("a run naming a path is no waiter",
        (waiterOfLine? "name=a run=../x pid=1 since=t").isNone
          && (waiterOfLine? "name=a run=x/y pid=1 since=t").isNone
          && (waiterOfLine? "name=a run=x pid=1 since=t train=../y").isNone)
    , ("a name holding a space is not queued", !queueable "a b" && queueable "a-b")
    , ("the first waiter takes a free lock", Queue.turn q3 all "a" "ra" true 1 == .take [])
    , ("the first waiter waits on a held one", Queue.turn q3 all "a" "ra" false 1 == .wait)
    , ("a waiter behind a live one keeps its place",
        Queue.turn q3 liveB "c" "rc" true 1 == .behind 3 "b")
    , ("a dead first waiter is skipped", Queue.turn q3 liveB "b" "rb" true 1 == .take [])
    , ("a name another live run waits under is held from this one",
        Queue.turn q3 liveB "b" "rx" true 1 == .held "rb")
    , ("a name a dead run waited under, entered by no one, is gone",
        Queue.turn q3 liveB "a" "rx" true 1 == .gone)
    , ("entering again keeps the place and the arrival",
        Queue.enter q3 liveB { wtr "a" "ra2" 8 with since := "later" }
          == [wtr "a" "ra2" 8, wtr "b" "rb", wtr "c" "rc"])
    , ("entering under a name a live run waits under leaves that run's",
        Queue.enter q3 liveB (wtr "b" "rx") == q3)
    , ("a new name arrives last",
        (Queue.enter q3 liveB (wtr "d" "rd")).map (·.name) == ["a", "b", "c", "d"])
    , ("a name holding a C1 control character is not queued", !queueable "a\u0085b")
    , ("a head takes the live waiters behind it under its fare as riders",
        Queue.turn qf all "a" "ra" true 4 == .take ["b", "c"])
    , ("a train takes a train's worth at most",
        Queue.turn qf all "a" "ra" true 2 == .take ["b"])
    , ("a dead waiter rides no train", Queue.turn qf (· != "rb") "a" "ra" true 4 == .take ["c"])
    , ("a waiter within a train's reach waits", Queue.turn qf all "c" "rc" true 4 == .wait)
    , ("a waiter past a train's reach is refused",
        Queue.turn qf all "c" "rc" true 2 == .behind 3 "a")
    , ("a head riding no train takes no riders",
        Queue.turn ((qf.take 1).map ({ · with fare := "" }) ++ qf.drop 1) all "a" "ra" true 4
          == .take [])
    , ("a rider of a live train waits for its verdict",
        Queue.turn (Queue.board qf ["b"] "rt") (fun r => r != "rx") "b" "rb" true 4 == .rides "rt")
    , ("a rider of a dead train waits again in its place",
        Queue.turn (Queue.board qf ["b"] "rt") (· != "rt") "b" "rb" false 4 == .wait)
    , ("a train's riders are no waiters ahead",
        Queue.turn (Queue.board qf ["b", "c"] "rt") all "d" "rd" true 2 == .wait
          && Queue.turn qf all "d" "rd" true 2 == .behind 4 "a")
    , ("a gate list's fare is a digest of its gates",
        fareOf #[{ name := "t", cmd := "true", args := #[] }]
          == fareOf #[{ name := "t", cmd := "true", args := #[] }]
        && fareOf #[{ name := "t", cmd := "true", args := #[] }]
          != fareOf #[{ name := "t", cmd := "false", args := #[] }]
        && (fareOf #[]).length == 16) ]
  for (why, ok) in queueCases do
    if ok then say "selftest" "ok" [("case", s!"queue: {why}")]
    else
      bad := bad + 1
      say "selftest" "fail" [("case", s!"queue: {why}")]
  -- The scenario harness's guard over the argv shapes the harness runs and the ones it must refuse.
  let g : HGuard := { root := "/tmp/r", made := ["/tmp/r/s/remote.git"] }
  let rp := "/tmp/r/s/repo"
  let rg := "/tmp/r/s/repo/.git"
  let guardCases : List (String × HCall × Bool) :=
    [ ("init a scratch repository", classify rp "" #["init", "-q", "-b", "main", "."], true)
    , ("init from outside the root", classify "/srv/elsewhere" "" #["init", "-q", "."], false)
    , ("init a bare repository in the root",
        classify "/tmp/r/s" "" #["init", "-q", "--bare", "-b", "main", "/tmp/r/s/remote.git"], true)
    , ("init a repository outside the root", classify "/tmp/r/s" "" #["init", "-q", "/elsewhere"],
        false)
    , ("commit in a scratch repository", classify rp rg #["commit", "-qm", "x"], true)
    , ("commit under a hook's GIT_DIR", classify rp "/real/.git/worktrees/w" #["commit", "-qm", "x"],
        false)
    , ("commit where git named no repository", classify rp "" #["commit", "-qm", "x"], false)
    , ("push by a remote's name", classify rp rg #["push", "-q", "origin", "main"], false)
    , ("push to the run's bare repository by path",
        classify rp rg #["push", "-q", "/tmp/r/s/remote.git", "main"], true)
    , ("push to it spelled with // and .",
        classify rp rg #["push", "-q", "/tmp/r//s/./remote.git", "main"], true)
    , ("push to a repository the run did not make",
        classify rp rg #["push", "-q", "/tmp/r/s/other.git", "main"], false)
    , ("push with --repo", classify rp rg #["push", "--repo=/tmp/r/s/remote.git"], false)
    , ("a global option", classify rp rg #["-C", "/", "status"], false)
    , ("a fetch", classify rp rg #["fetch", "/tmp/r/s/remote.git"], false)
    , ("remote update", classify rp rg #["remote", "update"], false)
    , ("remote add", classify rp rg #["remote", "add", "origin", "/tmp/r/s/remote.git"], true)
    , ("worktree add inside the root",
        classify rp rg #["worktree", "add", "-q", "-b", "agent/x", "/tmp/r/s/lt-x", "main"], true)
    , ("worktree add outside the root",
        classify rp rg #["worktree", "add", "-q", "/tmp/other/lt-x", "main"], false)
    , ("clone inside the root",
        classify "/tmp/r/s" "" #["clone", "-q", "/tmp/r/s/remote.git", "/tmp/r/s/other"], true)
    , ("clone of a repository outside the root",
        classify "/tmp/r/s" "" #["clone", "-q", "/real/repo", "/tmp/r/s/other"], false)
    , ("git --version", classify "/tmp/r" "" #["--version"], true)
    , ("the tool under test, its origin the run's", .drive rp rg ["/tmp/r/s/remote.git"], true)
    , ("the tool under test, its origin a real remote",
        .drive rp rg ["https://github.com/example/repo"], false)
    , ("the tool under test, no remote", .drive rp rg [], true) ]
  for (label, c, want) in guardCases do
    if c.allowed g != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"guard: {label}"),
        ("why", if want then "refused" else "allowed")]
    else say "selftest" "ok" [("case", s!"guard: {label}")]
  let withinCases : List (String × String × String × Bool) :=
    [ ("inside", "/tmp/r", "/tmp/r/x", true), ("itself", "/tmp/r", "/tmp/r", true)
    , ("a sibling sharing a prefix", "/tmp/r", "/tmp/rx", false)
    , ("a path that climbs", "/tmp/r", "/tmp/r/../x", false)
    , ("a relative path", "/tmp/r", "tmp/r/x", false)
    , ("the filesystem root holds nothing", "/", "/tmp", false)
    , ("// and . spell one path", "/tmp/r", "/tmp//r/./x", true) ]
  for (label, r, p, want) in withinCases do
    if within r p != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"within: {label}"), ("why", "wrong answer")]
    else say "selftest" "ok" [("case", s!"within: {label}")]
  if bareCreated "/tmp/r/s" #["init", "-q", "--bare", "-b", "main", "/tmp/r/s/remote.git"]
        != some "/tmp/r/s/remote.git"
      || bareCreated rp #["init", "-q", "-b", "main", "."] != none
      || rootFault "/tmp/r" "" != none || (rootFault "/tmp/r" "/srv/checkout/.git").isNone
      || (rootFault "/" "").isNone || (rootFault "tmp/r" "").isNone then
    bad := bad + 1
    say "selftest" "fail" [("case", "guard: made repositories and the scratch root"),
      ("why", "wrong answer")]
  else say "selftest" "ok" [("case", "guard: made repositories and the scratch root")]
  -- The write-ahead row's riders read back as the landed rows it names, the run's own first.
  let ahead := ledgerLine [("run", "r"), ("name", "head"), ("verdict", "landing"),
    ("gated", sha7s), ("branch", sha2s), ("tip", sha3s),
    ("riders", ridersField [("r1", sha4s, sha5s), ("r2", sha6s, sha7s)])]
  let owed := (owedRows ahead).map fun l =>
    ((jsonField l "name").getD "", (jsonField l "tip").getD "", (jsonField l "branch").getD "",
      (jsonField l "verdict").getD "", (jsonField l "gated").getD "")
  if owed != [("head", sha3s, sha2s, "landed", sha7s), ("r1", sha5s, sha4s, "landed", sha7s),
      ("r2", sha7s, sha6s, "landed", sha7s)] then
    bad := bad + 1
    say "selftest" "fail" [("case", "the write-ahead row's members"), ("why", s!"{owed}")]
  else say "selftest" "ok" [("case", "the write-ahead row's members")]
  if bad == 0 then sayFinal .checked [("cases", toString cases.length)]; return 0
  else sayFinal .failed [("cases", toString cases.length), ("bad", toString bad)]; return 1


-- The scratch scenarios: this binary driven against throwaway repositories, guarded.

/-- A scratch repository on `main` with one commit, opted in to gate overrides, and a
worktree for `agent/<name>` carrying one commit. -/
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
  hgitOk #["init", "-q", "-b", "main", "."] repo
  hgitOk #["config", "user.name", "Scratch"] repo
  hgitOk #["config", "user.email", "scratch@example.org"] repo
  hgitOk #["config", "--local", "land.allowGateOverride", "true"] repo
  IO.FS.writeFile s!"{repo}/base.txt" "base\n"
  hgitOk #["add", "base.txt"] repo
  hgitOk #["commit", "-qm", "Base"] repo
  let wt := s!"{root}/lt-{name}"
  hgitOk #["worktree", "add", "-q", "-b", s!"agent/{name}", wt, "main"] repo
  IO.FS.writeFile s!"{wt}/{name}.txt" s!"{name}\n"
  hgitOk #["add", s!"{name}.txt"] wt
  hgitOk #["commit", "-qm", s!"Add {name}"] wt
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
def landIn (self repo : String) (args : Array String) (gates : String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) :=
  runTool self repo args (#[("LAND_GATES", some gates),
    ("GIT_TERMINAL_PROMPT", some "0")] ++ extraEnv)

/-- Does `out` carry `s`? -/
def says (out s : String) : Bool := (out.splitOn s).length > 1

/-- The worktrees a scratch repository has registered, by path. -/
def worktreePaths (repo : String) : IO (Array String) := do
  let (_, o) ← hgit #["worktree", "list", "--porcelain"] repo
  return ((o.splitOn "\n").filter (·.startsWith "worktree ")).toArray.map
    fun l => (l.drop "worktree ".length).toString

/-- A bare `origin` holding the scratch repository's `main`, pushed to by its path. -/
def addRemote (s : Scratch) : IO String := do
  let remote := s!"{s.root}/remote.git"
  hgitOk #["init", "-q", "--bare", "-b", "main", remote] s.root
  hgitOk #["remote", "add", "origin", remote] s.repo
  hgitOk #["push", "-q", remote, "main"] s.repo
  return remote

def scenarioBranchMoves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/moves" "moves"
  -- The author commits on the branch while the gates run.
  writeExe s!"{s.root}/race.sh"
    s!"#!/bin/sh\necho bad > {s.wt}/BAD && git -C {s.wt} add BAD && git -C {s.wt} commit -qm concurrent\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["moves"] s!"race={s.root}/race.sh"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a commit on the branch during the gates is refused"
         , ok := code == 2 && before == after && says out "moved during the"
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioMainLeaves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/leaves" "leaves"
  hgitOk #["branch", "side", "main"] s.repo
  writeExe s!"{s.root}/switch.sh"
    s!"#!/bin/sh\ngit -C {s.repo} checkout -q side\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["leaves"] s!"switch={s.root}/switch.sh"
  let after ← revOf s.repo "refs/heads/main"
  let _ ← hgit #["checkout", "-q", "main"] s.repo
  return { label := "the main worktree leaving main is refused"
         , ok := code == 2 && before == after && says out "left main during the gates"
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioConflict (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/conflict" "conflict"
  IO.FS.writeFile s!"{s.repo}/shared.txt" "theirs\n"
  hgitOk #["add", "shared.txt"] s.repo
  hgitOk #["commit", "-qm", "main writes shared"] s.repo
  IO.FS.writeFile s!"{s.wt}/shared.txt" "ours\n"
  hgitOk #["add", "shared.txt"] s.wt
  hgitOk #["commit", "-qm", "branch writes shared"] s.wt
  let bBefore ← revOf s.repo "refs/heads/agent/conflict"
  let mBefore ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["conflict"] "t=true"
  let bAfter ← revOf s.repo "refs/heads/agent/conflict"
  let mAfter ← revOf s.repo "refs/heads/main"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  let wts ← worktreePaths s.repo
  return { label := "a rebase conflict is refused, and the branch was never touched"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && says out "rebase conflict: shared.txt" && wts.size == 2
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}] worktrees={wts.size}" }

/-- A rebase that stops with nothing unmerged: a commit that cannot be signed stops the
pick. -/
def scenarioStoppedRebase (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/stopped" "stopped"
  IO.FS.writeFile s!"{s.repo}/main.txt" "main\n"
  hgitOk #["add", "main.txt"] s.repo
  hgitOk #["commit", "-qm", "main moves on"] s.repo
  hgitOk #["config", "commit.gpgSign", "true"] s.repo
  hgitOk #["config", "gpg.program", "false"] s.repo
  let bBefore ← revOf s.repo "refs/heads/agent/stopped"
  let mBefore ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["stopped"] "t=true"
  let bAfter ← revOf s.repo "refs/heads/agent/stopped"
  let mAfter ← revOf s.repo "refs/heads/main"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  let wts ← worktreePaths s.repo
  return { label := "a rebase stopped with nothing unmerged is refused, the branch never touched"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && says out "the rebase failed" && wts.size == 2
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}] worktrees={wts.size}" }

def scenarioLands (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/lands" "lands"
  let tip ← revOf s.repo "refs/heads/agent/lands"
  let (code, out) ← landIn self s.repo #["lands"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  let wts ← worktreePaths s.repo
  return { label := "a clean landing moves main to the gated tip and removes its gate tree"
         , ok := code == 0 && after == tip && says out s!"gated={tip} tip={tip}"
             && says out "step=gate-tree result=ok" && says out "step=tree-remove result=ok"
             && wts.size == 2
         , detail := s!"exit={code} gated={tip} main-after={after} worktrees={wts.size}" }

/-- A branch whose change holds a file that is not UTF-8 lands. -/
def scenarioLatin1 (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/latin1" "latin1"
  IO.FS.writeBinFile s!"{s.wt}/latin1.tex" ("Caf".toUTF8 ++ ⟨#[0xE9, 0x0A]⟩)
  hgitOk #["add", "latin1.tex"] s.wt
  hgitOk #["commit", "-qm", "Add a Latin-1 file"] s.wt
  let tip ← revOf s.repo "refs/heads/agent/latin1"
  let (code, out) ← landIn self s.repo #["latin1"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a branch holding a file that is not UTF-8 lands, its bytes compared exactly"
         , ok := code == 0 && after == tip && says out "step=net result=ok"
             && says out "result=landed"
         , detail := s!"exit={code} tip={tip} main-after={after}" }

/-- A branch that already contains `main` keeps its reviewed merge, its tree and its
ancestry on the remote. -/
def scenarioMergedTip (self root : String) (reconciled : Bool) : IO Outcome := do
  let name := if reconciled then "merge-reconciled" else "merge-kept"
  let s ← mkScratch s!"{root}/{name}" name
  let remote ← addRemote s
  hgitOk #["checkout", "-q", "-b", "side", "main"] s.wt
  IO.FS.writeFile s!"{s.wt}/side.txt" "side\n"
  hgitOk #["add", "side.txt"] s.wt
  hgitOk #["commit", "-qm", "Side work"] s.wt
  let side ← revOf s.repo "refs/heads/side"
  hgitOk #["checkout", "-q", s!"agent/{name}"] s.wt
  let strategy := if reconciled then #["-s", "ours"] else #[]
  hgitOk (#["merge", "-q", "--no-ff"] ++ strategy ++ #["side", "-m", "Reviewed merge"]) s.wt
  let tip ← revOf s.repo s!"refs/heads/agent/{name}"
  let tree ← revOf s.repo (tip ++ "^{tree}")
  let (code, out) ← landIn self s.repo #[name, "--push"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  let onRemote ← revOf remote "refs/heads/main"
  let afterTree ← revOf s.repo "main^{tree}"
  let (ancestor, _) ← hgit #["merge-base", "--is-ancestor", side, "main"] s.repo
  let branch ← revOf s.repo s!"refs/heads/agent/{name}"
  let present ← System.FilePath.pathExists s!"{s.repo}/side.txt"
  return { label := s!"an already-based {name} keeps its exact tree and ancestry when published"
         , ok := code == 0 && after == tip && onRemote == tip && afterTree == tree
             && ancestor == 0 && branch == tip && present == !reconciled
             && says out "result=landed"
         , detail := s!"exit={code} tip={tip} main={after} remote={onRemote} \
tree={tree}->{afterTree} side-ancestor={ancestor == 0} side-file={present}" }

/-- The branch's own commit adds `BAD`, which a gate that refuses `BAD` must see. -/
def badBranch (root name : String) : IO Scratch := do
  let s ← mkScratch root name
  IO.FS.writeFile s!"{s.wt}/BAD" "bad\n"
  hgitOk #["add", "BAD"] s.wt
  hgitOk #["commit", "-qm", "Add BAD"] s.wt
  writeExe s!"{s.root}/no-bad.sh" "#!/bin/sh\ntest ! -e BAD\n"
  return s

def scenarioWorktreeSwitched (self root : String) : IO Outcome := do
  let s ← badBranch s!"{root}/switched" "switched"
  writeExe s!"{s.root}/switch.sh" s!"#!/bin/sh\ngit -C {s.wt} checkout -q -b elsewhere main\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["switched"]
    s!"switch={s.root}/switch.sh;no-bad={s.root}/no-bad.sh"
  let after ← revOf s.repo "refs/heads/main"
  let (_, ls) ← hgit #["ls-tree", "--name-only", "main"] s.repo
  return { label := "a branch worktree switched mid-landing does not change what the gates see"
         , ok := code == 1 && before == after && !says ls "BAD" && says out "gate no-bad failed"
         , detail := s!"exit={code} main-before={before} main-after={after}" }

def scenarioTreeMoved (self root : String) : IO Outcome := do
  let s ← badBranch s!"{root}/treemoved" "treemoved"
  writeExe s!"{s.root}/switch.sh" "#!/bin/sh\ngit checkout -q -b elsewhere main\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["treemoved"]
    s!"switch={s.root}/switch.sh;no-bad={s.root}/no-bad.sh"
  let after ← revOf s.repo "refs/heads/main"
  let wts ← worktreePaths s.repo
  return { label := "a gate that moves the gate tree fails the landing"
         , ok := code == 1 && before == after && says out "moved the gate tree off the gated tip"
             && says out "step=gate-switch result=fail" && wts.size == 2
         , detail := s!"exit={code} main-before={before} main-after={after} worktrees={wts.size}" }

/-- A commit lands on `main` the instant `git push` starts: the push sends the gated tip,
and the ungated commit stays off the remote. -/
def scenarioPushNamesTip (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushtip" "pushtip"
  let remote ← addRemote s
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  IO.FS.createDirAll s!"{s.root}/wrap"
  -- Only the push to `origin`, since the fast-forward is a push into this repository.
  writeExe s!"{s.root}/wrap/git"
    s!"#!/bin/sh\nif [ \"$1\" = push ] && [ \"$2\" = origin ]; then\n  \"{realGit}\" -C {s.repo} commit -q --allow-empty -m ungated\nfi\nexec \"{realGit}\" \"$@\"\n"
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let tip ← revOf s.repo "refs/heads/agent/pushtip"
  let (code, out) ← landIn self s.repo #["pushtip", "--push"] "t=true"
    #[("PATH", some s!"{s.root}/wrap:{path}")]
  let onRemote ← revOf remote "refs/heads/main"
  let (_, ungated) ← hgit #["log", "--format=%s", "-1", "refs/heads/main"] s.repo
  return { label := "the push sends the gated tip, not whatever main is by then"
         , ok := code == 0 && onRemote == tip && ungated == "ungated" && says out "result=landed"
         , detail := s!"exit={code} gated={tip} remote={onRemote} local-main-top={ungated}" }

/-- The remote's `main` moved where this repository cannot see it: the push is no
fast-forward and fails loudly. -/
def scenarioPushNotFastForward (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushff" "pushff"
  let remote ← addRemote s
  let other := s!"{s.root}/other"
  hgitOk #["clone", "-q", remote, other] s.root
  hgitOk #["config", "user.name", "Scratch"] other
  hgitOk #["config", "user.email", "scratch@example.org"] other
  hgitOk #["commit", "-q", "--allow-empty", "-m", "elsewhere"] other
  hgitOk #["push", "-q", remote, "main"] other
  let theirs ← revOf remote "refs/heads/main"
  let tip ← revOf s.repo "refs/heads/agent/pushff"
  let (code, out) ← landIn self s.repo #["pushff", "--push"] "t=true"
  let onRemote ← revOf remote "refs/heads/main"
  let localMain ← revOf s.repo "refs/heads/main"
  return { label := "a push that is not a fast-forward is landed-unpushed, never forced"
         , ok := code == 4 && onRemote == theirs && localMain == tip
             && says out "result=landed-unpushed"
         , detail := s!"exit={code} remote={theirs}->{onRemote} main={localMain} gated={tip}" }

/-- A `merge=union` file keeps a heading the branch renamed away, with no conflict
reported: the drift is refused. -/
def scenarioUnionDrift (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/union" "union"
  IO.FS.writeFile s!"{s.repo}/.gitattributes" "PLAN.md merge=union\n"
  IO.FS.writeFile s!"{s.repo}/PLAN.md" "# plan\n\n### a\nbody a\n"
  hgitOk #["add", ".gitattributes", "PLAN.md"] s.repo
  hgitOk #["commit", "-qm", "Add the plan"] s.repo
  hgitOk #["rebase", "-q", "main"] s.wt
  IO.FS.writeFile s!"{s.wt}/PLAN.md" "# plan\n\n### a\nbody a\n\n### b-draft\nbody b\n"
  hgitOk #["commit", "-qam", "Draft b"] s.wt
  IO.FS.writeFile s!"{s.wt}/PLAN.md" "# plan\n\n### a\nbody a\n\n### b-final\nbody b\n"
  hgitOk #["commit", "-qam", "Final b"] s.wt
  IO.FS.writeFile s!"{s.repo}/PLAN.md" "# plan\n\n### a\nbody a\n\n### m\nbody m\n"
  hgitOk #["commit", "-qam", "Main m"] s.repo
  let bBefore ← revOf s.repo "refs/heads/agent/union"
  let mBefore ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["union"] "t=true"
  let bAfter ← revOf s.repo "refs/heads/agent/union"
  let mAfter ← revOf s.repo "refs/heads/main"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  return { label := "a rebase that changed a file's net content is refused, with nothing to put back"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && says out "the rebase changed the net content of: PLAN.md"
             && !says out "step=restore"
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}]" }

def scenarioNoOptIn (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/optin" "optin"
  hgitOk #["config", "--local", "--unset", "land.allowGateOverride"] s.repo
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
  -- `land check` with no name, beside an existing branch `agent/check`.
  let (code, _) ← landIn self s.repo #["check"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a subcommand word is not an agent name"
         , ok := code == 3 && before == after
         , detail := s!"exit={code} main-before={before} main-after={after}" }

/-- `--help` and `-h` print the usage and exit 0, and an unknown option prints its error and the
usage and exits 3, all with no run directory, lock or ledger row. -/
def scenarioUsage (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/usage" "usage"
  let tries : List (Array String × Nat) :=
    [ (#["--help"], 0), (#["-h"], 0), (#["check", "usage", "--help"], 0), (#["usage", "-h"], 0)
    , (#["--scenarios"], 3), (#["usage", "--pushh"], 3), (#["new", "-x"], 3)
    , (#["-"], 3), (#["--push"], 3) ]
  let before ← revOf s.repo "refs/heads/main"
  let mut wrong : Array String := #[]
  for (args, want) in tries do
    let (code, out) ← landIn self s.repo args "t=true"
    unless code == want && says out "usage: land" do
      wrong := wrong.push s!"{String.intercalate " " args.toList}: exit {code}"
  let after ← revOf s.repo "refs/heads/main"
  let made ← System.FilePath.pathExists s!"{s.repo}/.git/land"
  return { label := "--help and -h print the usage, an unknown option prints it too, and none \
of them makes a run, takes the lock or writes the ledger"
         , ok := wrong.isEmpty && !made && before == after
         , detail := s!"wrong=[{String.intercalate "; " wrong.toList}] land-dir={made} \
main={before}->{after}" }

/-- The regular files a git index (versions 2 to 4, SHA-1 names) holds at stage 0, in order, each
with whether it is executable; `none` for bytes that do not read as one, or a split index. -/
def indexFiles (b : ByteArray) : Option (Array (String × Bool)) := Id.run do
  let byte (i : Nat) : Nat := (b[i]?.getD 0).toNat
  let u16 (i : Nat) : Nat := byte i * 256 + byte (i + 1)
  let u32 (i : Nat) : Nat := u16 i * 65536 + u16 (i + 2)
  if b.size < 12 || b.extract 0 4 != "DIRC".toUTF8 then return none
  let version := u32 4
  if version < 2 || version > 4 then return none
  let mut pos := 12
  let mut prev : ByteArray := .empty
  let mut out : Array (String × Bool) := #[]
  for _ in [0:u32 8] do
    if pos + 62 > b.size then return none
    let mode := u32 (pos + 24)
    let flags := u16 (pos + 60)
    let start := pos + 62 + (if version ≥ 3 && flags &&& 0x4000 != 0 then 2 else 0)
    let mut p := start
    let mut strip := 0
    if version == 4 then
      let mut c := byte p
      p := p + 1
      strip := c &&& 127
      for _ in [0:9] do
        if c &&& 128 == 0 then break
        c := byte p
        p := p + 1
        strip := ((strip + 1) <<< 7) + (c &&& 127)
      if strip > prev.size then return none
    let mut nul := b.size
    for k in [p:b.size] do
      if byte k == 0 then
        nul := k
        break
    if nul ≥ b.size then return none
    let suffix := b.extract p nul
    let path := if version != 4 then suffix else prev.extract 0 (prev.size - strip) ++ suffix
    let some name := String.fromUTF8? path | return none
    if name.isEmpty then return none
    if (flags >>> 12) &&& 3 == 0 && mode &&& 0xF000 == 0x8000 then
      out := out.push (name, mode &&& 0o111 != 0)
    prev := path
    pos := if version == 4 then nul + 1 else pos + (nul - pos + 8) / 8 * 8
  for _ in [0:b.size] do
    if pos + 28 > b.size then break
    if b.extract pos (pos + 4) == "link".toUTF8 then return none
    pos := pos + 8 + u32 (pos + 4)
  return some out

/-- The index of the checkout at `tree`, whose `.git` is a directory or names one. -/
def indexOf (tree : System.FilePath) : IO ByteArray := do
  let dotGit := tree / ".git"
  let dir ← if ← dotGit.isDir then pure dotGit else do
    let line := trimWs (← IO.FS.readFile dotGit)
    let some named := line.dropPrefix? "gitdir: " | throw (IO.userError s!"{dotGit} names no gitdir")
    let d := System.FilePath.mk named.toString
    pure (if d.isAbsolute then d else tree / d)
  IO.FS.readBinFile (dir / "index")

/-- Copy the regular files the index of `src` stages into `dst`, keeping their executable bit; a
path that is no longer a regular file inside `src` is skipped. -/
def copyTracked (src dst : System.FilePath) : IO (Except String Nat) := do
  let some files := indexFiles (← indexOf src) | return .error s!"the index of {src} does not read"
  let root ← IO.FS.realPath src
  let mut n := 0
  for (path, exec) in files do
    let from_ := src / path
    let md? ← try some <$> from_.symlinkMetadata catch _ => pure none
    unless md?.any (·.type == .file) do continue
    unless (← IO.FS.realPath from_) == root / path do continue
    let target := dst / path
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile target (← IO.FS.readBinFile from_)
    if exec then
      IO.setAccessRights target
        { user := ⟨true, true, true⟩, group := ⟨true, false, true⟩, other := ⟨true, false, true⟩ }
    n := n + 1
  return .ok n

/-- The regular files `git ls-files -s -z` lists at stage 0 in `repo`, each with whether it is
executable. -/
def gitStagedFiles (repo : String) : IO (Array (String × Bool)) := do
  let o ← hgitRun #["ls-files", "-s", "-z"] repo
  if o.exitCode != 0 then throw (IO.userError s!"fixture: git ls-files exited {o.exitCode}")
  return ((o.stdout.splitOn "\x00").filterMap fun e =>
    match e.splitOn "\t" with
    | [head, path] =>
      match wsSplit head with
      | [mode, _, "0"] =>
        if mode == "100644" then some (path, false) else if mode == "100755" then some (path, true)
        else none
      | _ => none
    | _ => none).toArray

/-- `indexFiles` against git's own listing of an index git wrote in versions 2, 3 and 4, over names
sharing prefixes, one past 128 bytes, a non-ASCII and an executable one, a symlink, and an entry
with extended flags. -/
def indexReaderFailure (root : String) : IO (Option String) := do
  let repo := s!"{root}/narrative/index-oracle"
  let long := "sub/abc/" ++ String.ofList (List.replicate 130 'q') ++ ".txt"
  IO.FS.createDirAll s!"{repo}/sub/abc"
  hgitOk #["init", "-q", "-b", "main", "."] repo
  for f in ["plain.txt", "sub/a.lean", "sub/ab.lean", "sub/abc/x.lean", long, "z-é.lean"] do
    IO.FS.writeFile s!"{repo}/{f}" s!"{f}\n"
  writeExe s!"{repo}/run.sh" "#!/bin/sh\nexit 0\n"
  let _ ← hrun "ln" #["-s", "plain.txt", s!"{repo}/link.txt"] none
  hgitOk #["add", "-A"] repo
  let want ← gitStagedFiles repo
  unless want.size == 7 && want.any (·.2) do
    return some s!"git staged {repr want}"
  for v in ["2", "3", "4"] do
    if v == "3" then hgitOk #["update-index", "--skip-worktree", "sub/ab.lean"] repo
    hgitOk #["update-index", "--index-version", v] repo
    let got := indexFiles (← IO.FS.readBinFile s!"{repo}/.git/index")
    unless got == some want do
      return some s!"index v{v} read as {repr got}, git lists {repr want}"
  return none

/-- A branch whose commit adds a comment telling history, made without the hook, fails the shipped
conventions gate over a copy of the tracked files of the checkout under test, which a plain commit
passes though the base holds a fault only the whole tree shows. -/
def scenarioNarrative (self root : String) : IO Outcome := do
  let label := "a commit telling history in a comment, made without the hook, fails the \
conventions gate, and a plain one lands over a base faulted only as a whole tree"
  let fail (detail : String) : IO Outcome := pure { label, ok := false, detail }
  if let some why ← indexReaderFailure root then return ← fail why
  let bin := (System.FilePath.mk self).parent.getD "."
  let tree := ((bin.parent.bind (·.parent)).bind (·.parent)).getD "."
  let precommit := tree / ".lake" / "build" / "bin" / "precommit"
  let real (p : System.FilePath) : IO String := do
    try pure (← IO.FS.realPath p).toString catch _ => pure ""
  let layout := (← (tree / "lakefile.toml").pathExists) && (← (tree / "scripts" / "land.lean").pathExists)
    && (← precommit.pathExists)
  let same := !(← real self).isEmpty && (← real (tree / ".lake" / "build" / "bin" / "land")) == (← real self)
  unless layout && same do
    return ← fail s!"{self} is not the build of a checkout at {tree}"
  let some gate := defaultGates.find? (·.startsWith "conventions=")
    | return ← fail "the shipped list has no conventions gate"
  let repo := s!"{root}/narrative/repo"
  IO.FS.createDirAll repo
  match ← copyTracked tree repo with
  | .error why => return ← fail why
  | .ok _ => pure ()
  IO.FS.createDirAll s!"{repo}/.lake/build/bin"
  let _ ← hrun "ln" #["-s", ← real precommit, s!"{repo}/.lake/build/bin/precommit"] none
  -- One helper in two test files, which only the tree's reading of every test file finds.
  for f in ["ScratchA", "ScratchB"] do
    IO.FS.writeFile s!"{repo}/Tests/{f}.lean" "def scratchHelper : Nat := 0\n"
  hgitOk #["init", "-q", "-b", "main", "."] repo
  hgitOk #["config", "user.name", "Scratch"] repo
  hgitOk #["config", "user.email", "scratch@example.org"] repo
  hgitOk #["config", "--local", "land.allowGateOverride", "true"] repo
  hgitOk #["add", "-A"] repo
  hgitOk #["commit", "-qm", "Base"] repo
  let branch (name file text : String) : IO Unit := do
    let wt := s!"{root}/narrative/lt-{name}"
    hgitOk #["worktree", "add", "-q", "-b", s!"agent/{name}", wt, "main"] repo
    IO.FS.writeFile s!"{wt}/{file}" text
    hgitOk #["add", file] wt
    hgitOk #["commit", "-qm", s!"Add {file}"] wt
  branch "told" "Told.lean" "-- Previously this file used to hold a parser.\ndef told : Nat := 2\n"
  branch "plain" "Plain.lean" "def plain : Nat := 1\n"
  let before ← revOf repo "refs/heads/main"
  let (told, toldOut) ← landIn self repo #["told"] gate
  let afterTold ← revOf repo "refs/heads/main"
  let (plain, _) ← landIn self repo #["plain"] gate
  let afterPlain ← revOf repo "refs/heads/main"
  let plainTip ← revOf repo "refs/heads/agent/plain"
  let runDir := ((toldOut.splitOn "\n").find? (·.startsWith "land: step=run ")).bind fun l =>
    ((wsSplit l).find? (·.startsWith "dir=")).map fun w => (w.drop "dir=".length).toString
  let log ← match runDir with
    | some d => try IO.FS.readFile s!"{d}/gate-conventions.log" catch _ => pure ""
    | none => pure ""
  let refused := says toldOut "step=gate-conventions result=fail" &&
    says log "Told.lean:1: \"Previously\""
  return { label
         , ok := told == 1 && refused && afterTold == before && plain == 0
             && afterPlain == plainTip
         , detail := s!"told={told} refused={refused} main={before}->{afterTold}->{afterPlain} \
plain={plain} plain-tip={plainTip}" }

/-- A landing started with `GIT_DIR` naming another repository lands the one its working
directory names and writes nothing into the other. -/
def scenarioForeignGitDir (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/foreign" "foreign"
  let target := s!"{s.root}/target"
  IO.FS.createDirAll target
  hgitOk #["init", "-q", "-b", "main", "."] target
  hgitOk #["config", "user.name", "Target"] target
  hgitOk #["config", "user.email", "target@example.org"] target
  hgitOk #["commit", "-q", "--allow-empty", "-m", "The target's own commit"] target
  let tBefore ← revOf target "refs/heads/main"
  let tip ← revOf s.repo "refs/heads/agent/foreign"
  writeExe s!"{s.root}/no-git-dir.sh" "#!/bin/sh\ntest -z \"$GIT_DIR\" && test -z \"$GIT_INDEX_FILE\"\n"
  let (code, _) ← landIn self s.repo #["foreign"] s!"env={s.root}/no-git-dir.sh"
    #[("GIT_DIR", some s!"{target}/.git"), ("GIT_INDEX_FILE", some s!"{target}/.git/index")]
  let after ← revOf s.repo "refs/heads/main"
  let tAfter ← revOf target "refs/heads/main"
  let touched ← System.FilePath.pathExists s!"{target}/.git/land"
  return { label := "a landing under another repository's GIT_DIR lands its own and leaves that one alone"
         , ok := code == 0 && after == tip && tAfter == tBefore && !touched
         , detail := s!"exit={code} main={after} gated={tip} target={tBefore}->{tAfter} \
target-land-dir={touched}" }

/-- Retention and listings run while a landing is inside its gates, its own directory
sorted first for pruning: it survives and the landing finishes. -/
def scenarioRetention (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/retain" "retain"
  for i in [0:60] do
    IO.FS.createDirAll s!"{s.repo}/.git/land/zz-newer-{i}"
  writeExe s!"{s.root}/prune.sh"
    s!"#!/bin/sh\ni=0\nwhile [ $i -lt 3 ]; do \"{self}\" retire nope >/dev/null 2>&1; i=$((i+1)); done\n\
i=0\nwhile [ $i -lt 2 ]; do \"{self}\" status >/dev/null 2>&1; i=$((i+1)); done\n"
  let tip ← revOf s.repo "refs/heads/agent/retain"
  let (code, out) ← landIn self s.repo #["retain"] s!"prune={s.root}/prune.sh"
  let after ← revOf s.repo "refs/heads/main"
  let run := match (out.splitOn "step=run result=ok id=").drop 1 |>.head? with
    | some rest => (wsSplit rest).headD ""
    | none => ""
  let kept ← System.FilePath.pathExists s!"{s.repo}/.git/land/{run}"
  return { label := "pruning and listings during a landing leave its directory, and it lands"
         , ok := code == 0 && after == tip && !run.isEmpty && kept
         , detail := s!"exit={code} main={after} gated={tip} run={run} kept={kept}" }

/-- A landing killed inside a gate does not wedge the next one, which records the dead run
and removes its gate tree. -/
def scenarioKilled (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/killed" "k1"
  let wt2 := s!"{s.root}/lt-k2"
  hgitOk #["worktree", "add", "-q", "-b", "agent/k2", wt2, "main"] s.repo
  IO.FS.writeFile s!"{wt2}/k2.txt" "k2\n"
  hgitOk #["add", "k2.txt"] wt2
  hgitOk #["commit", "-qm", "Add k2"] wt2
  writeExe s!"{s.root}/die.sh" "#!/bin/sh\nkill -TERM $PPID\nsleep 1\n"
  let (c1, _) ← landIn self s.repo #["k1"] s!"die={s.root}/die.sh"
  let tip2 ← revOf s.repo "refs/heads/agent/k2"
  let (c2, out2) ← landIn self s.repo #["k2"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  let ledger ← try IO.FS.readFile s!"{s.repo}/.git/land/ledger.jsonl" catch _ => pure ""
  let wts ← worktreePaths s.repo
  return { label := "a landing killed in its gates leaves no lock and no tree for the next"
         , ok := c1 != 0 && c2 == 0 && after == tip2 && says out2 "abandoned="
             && says ledger "\"verdict\":\"abandoned\"" && wts.size == 3
         , detail := s!"first-exit={c1} second-exit={c2} main={after} gated={tip2} \
worktrees={wts.size}" }

/-- Another agent branch in a scratch repository, its worktree carrying one commit. -/
def addAgent (s : Scratch) (name : String) : IO Unit := do
  let wt := s!"{s.root}/lt-{name}"
  hgitOk #["worktree", "add", "-q", "-b", s!"agent/{name}", wt, "main"] s.repo
  IO.FS.writeFile s!"{wt}/{name}.txt" s!"{name}\n"
  hgitOk #["add", s!"{name}.txt"] wt
  hgitOk #["commit", "-qm", s!"Add {name}"] wt

/-- A gate list whose one gate marks `held-<name>` in the scratch root, then holds the lock until
`release-<name>` appears there, five minutes at most. -/
def holdGate (s : Scratch) (name : String) : IO String := do
  writeExe s!"{s.root}/hold-{name}.sh" s!"#!/bin/sh\ntouch {s.root}/held-{name}\ni=0\n\
while [ ! -e {s.root}/release-{name} ] && [ $i -lt 3000 ]; do sleep 0.1; i=$((i+1)); done\n"
  return s!"hold={s.root}/hold-{name}.sh"

def release (s : Scratch) (name : String) : IO Unit :=
  IO.FS.writeFile s!"{s.root}/release-{name}" ""

abbrev Pending := Task (Except IO.Error (Nat × String))

/-- `landIn` started in the background. -/
def landAsync (self repo : String) (args : Array String) (gates : String)
    (env : Array (String × Option String) := #[]) : IO Pending :=
  IO.asTask (landIn self repo args gates env) .dedicated

def awaitRun (t : Pending) : IO (Nat × String) := do
  match ← IO.wait t with
  | .ok r => pure r
  | .error ex => pure (255, toString ex)

/-- A retry loop as an agent runs one: `land <name>` again after `pauseMs` while it is
refused for the lock, `tries` times at most. -/
def landRetrying (self repo name gates : String) (pauseMs : UInt32) (tries : Nat := 600) :
    IO Pending :=
  IO.asTask (prio := .dedicated) do
    let mut last := (255, "")
    for _ in [0:tries] do
      last ← landIn self repo #[name] gates
      unless last.1 == 2 && says last.2 "another landing holds the lock" do return last
      IO.sleep pauseMs
    return last

/-- Poll for `p`, thirty seconds at most; whether it came to hold. -/
def awaitTrue (p : IO Bool) : IO Bool := do
  for _ in [0:600] do
    if ← p then return true
    IO.sleep 50
  return false

def queueOf (s : Scratch) : IO (List Waiter) := readQueueAt s!"{s.repo}/.git"

def awaitQueued (s : Scratch) (name : String) : IO Bool :=
  awaitTrue do return (← queueOf s).any (·.name == name)

/-- Wait until `name` is the first live waiter: entered, and waiting for the lock. -/
def awaitHead (s : Scratch) (name : String) : IO Bool := awaitTrue do
  for w in ← queueOf s do
    if ← waiterLiveAt s!"{s.repo}/.git" w then return w.name == name
  return false

/-- Wait until every one of `names` waits in the queue under a live run. -/
def awaitLive (s : Scratch) (names : List String) : IO Bool := awaitTrue do
  let q ← queueOf s
  let mut all := true
  for n in names do
    all := all && (← match q.find? (·.name == n) with
      | some w => waiterLiveAt s!"{s.repo}/.git" w
      | none => pure false)
  return all

/-- Hand the lock on: wait until `next` waits first in line, release `held`, and wait until `next`
runs its own gate, holding the lock. -/
def handOn (s : Scratch) (held next : String) : IO Bool := do
  let first ← awaitHead s next
  release s held
  return first && (← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-{next}"))

/-- The subjects of `main`'s commits, oldest first, which the scratch landings name by their
branches. -/
def mainSubjects (repo : String) : IO (List String) := do
  let (_, o) ← hgit #["log", "--reverse", "--format=%s", "refs/heads/main"] repo
  return (o.splitOn "\n").filter (!·.isEmpty)

/-- Whether a porcelain output carries `key=value` as one field. -/
def saysField (out key value : String) : Bool := says (out ++ " ") s!" {key}={value} "

/-- Three landings wait while another holds the lock, each later one asking more often: each
landing ends only once the next waiter in arrival order waits first in line, and they land in
the order they arrived. -/
def scenarioQueueOrder (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/fifo" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  let names := ["first", "second", "third"]
  for n in names do addAgent s n
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let mut loops : Array Pending := #[]
  let mut arrived := true
  for (n, pause) in names.zip [900, 400, 100] do
    loops := loops.push (← landRetrying self s.repo n (← holdGate s n) pause.toUInt32)
    arrived := arrived && (← awaitQueued s n)
  let mut handed := true
  for (a, b) in ("holder" :: names).zip names do
    handed := handed && (← handOn s a b)
  release s "third"
  let (ch, _) ← awaitRun th
  let codes ← loops.mapM fun t => (·.1) <$> awaitRun t
  let order ← mainSubjects s.repo
  return { label := "three waiting landings land in the order they arrived, the latest asking most often"
         , ok := held && arrived && handed && ch == 0 && codes.all (· == 0)
             && order == ["Base", "Add holder"] ++ names.map (s!"Add {·}")
         , detail := s!"held={held} arrived={arrived} handed={handed} holder={ch} \
contenders={codes} main={order}" }

/-- The first waiter is killed while it waits: the one behind it, asking once, waits and takes
the lock when it frees, and the dead one keeps its place, listed dead. -/
def scenarioQueueDeadHead (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/deadhead" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  for n in ["dead", "next"] do addAgent s n
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let td ← landAsync self s.repo #["dead"] "t=true"
  let entered ← awaitHead s "dead"
  let pid := (((← queueOf s).find? (·.name == "dead")).map (·.pid)).getD 0
  let (killed, _) ← if pid > 0 then hrun "kill" #["-KILL", toString pid] none else pure (1, "")
  let (cd, _) ← awaitRun td
  let tn ← landAsync self s.repo #["next"] "t=true"
  let first ← awaitHead s "next"
  let (_, status) ← landIn self s.repo #["status"] "t=true"
  let listed := says status "step=lock result=held name=holder"
    && says status "result=ok position=1 name=dead" && says status "live=no"
    && says status "result=ok position=2 name=next"
  release s "holder"
  let (ch, _) ← awaitRun th
  let (cn, _) ← awaitRun tn
  let order ← mainSubjects s.repo
  let after := (← queueOf s).map (·.name)
  -- The dead waiter's work reaches main another way, and its retirement leaves the queue.
  hgitOk #["merge", "-q", "--no-edit", "agent/dead"] s.repo
  let (cr, _) ← landIn self s.repo #["retire", "dead"] "t=true"
  let retired := (← queueOf s).map (·.name)
  return { label := "a waiter killed first in line is skipped, keeps its place, listed dead, and \
leaves the queue when it retires"
         , ok := held && entered && killed == 0 && cd != 0 && first && listed && ch == 0
             && cn == 0 && order == ["Base", "Add holder", "Add next"] && after == ["dead"]
             && cr == 0 && retired.isEmpty
         , detail := s!"held={held} entered={entered} pid={pid} killed={killed} dead-exit={cd} \
next-first={first} listed={listed} holder={ch} next={cn} main={order} queue={after} \
retire={cr} after-retire={retired}" }

/-- Two waiters refused behind a third ask again: the earlier keeps its place and its arrival,
and lands before the later, which asks more often. -/
def scenarioQueueRepoll (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/repoll" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  for n in ["head", "early", "late"] do addAgent s n
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tp ← landAsync self s.repo #["head"] (← holdGate s "head")
  let headIn ← awaitHead s "head"
  let (c1, o1) ← landIn self s.repo #["early"] (← holdGate s "early")
  let (c2, _) ← landIn self s.repo #["late"] (← holdGate s "late")
  let q1 ← queueOf s
  let (c3, o3) ← landIn self s.repo #["early"] (← holdGate s "early")
  let q2 ← queueOf s
  let arrival (q : List Waiter) := (q.find? (·.name == "early")).map fun w => (w.since, w.run)
  let kept := q1.map (·.name) == ["head", "early", "late"] && q2.map (·.name) == q1.map (·.name)
    && (arrival q1).map (·.1) == (arrival q2).map (·.1)
    && (arrival q1).map (·.2) != (arrival q2).map (·.2)
  let placed := c1 == 2 && c2 == 2 && c3 == 2 && saysField o1 "position" "2"
    && saysField o3 "position" "2" && saysField o3 "head" "head"
  let te ← landRetrying self s.repo "early" (← holdGate s "early") 400
  let tl ← landRetrying self s.repo "late" (← holdGate s "late") 100
  let mut handed := true
  for (a, b) in [("holder", "head"), ("head", "early"), ("early", "late")] do
    handed := handed && (← handOn s a b)
  release s "late"
  let (ch, _) ← awaitRun th
  let codes ← [tp, te, tl].mapM fun t => (·.1) <$> awaitRun t
  let order ← mainSubjects s.repo
  return { label := "a refused waiter asking again keeps its place and its arrival, and lands \
before a later one asking more often"
         , ok := held && headIn && kept && placed && handed && ch == 0 && codes.all (· == 0)
             && order == ["Base", "Add holder", "Add head", "Add early", "Add late"]
         , detail := s!"held={held} head-in={headIn} kept={kept} placed={placed} handed={handed} \
queue={q1.map (·.name)}->{q2.map (·.name)} holder={ch} others={codes} main={order}" }

/-- The first waiter asks once and takes the lock as the holder frees it, within seconds, so it
lands with no next ask. -/
def scenarioQueuePrompt (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/prompt" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  addAgent s "waiter"
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tw ← landAsync self s.repo #["waiter"] (← holdGate s "waiter")
  let first ← awaitHead s "waiter"
  release s "holder"
  let (ch, _) ← awaitRun th
  let t1 ← IO.monoMsNow
  let took ← awaitTrue do
    let r ← try IO.FS.readFile s!"{s.repo}/.git/land/landing.owner" catch _ => pure ""
    return recField r "name" == "waiter"
  let ms := (← IO.monoMsNow) - t1
  let gated ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-waiter")
  release s "waiter"
  let (cw, ow) ← awaitRun tw
  return { label := "the first waiter takes the lock within seconds of its freeing and lands \
with no next ask"
         , ok := held && first && ch == 0 && took && ms ≤ 20 * turnBeatMs.toNat && gated && cw == 0
             && says ow "step=queue result=wait" && says ow "result=landed"
         , detail := s!"held={held} first={first} holder={ch} took={took} \
took-ms-after-holder-exit={ms} gated={gated} waiter={cw}" }

/-- A gate list whose one gate, shared by a train's members, counts its runs in `gate-runs`, runs
`body`, then holds the lock until it takes the `release-<label>` that appears, five minutes at
most, and passes as `body` did. -/
def trainGate (s : Scratch) (label : String) (body : String := "true") : IO String := do
  writeExe s!"{s.root}/{label}.sh" s!"#!/bin/sh\necho run >> {s.root}/gate-runs\n({body}); st=$?\n\
touch {s.root}/held-{label}\ni=0\nwhile [ ! -e {s.root}/release-{label} ] && [ $i -lt 3000 ]; do \
sleep 0.1; i=$((i+1)); done\nrm -f {s.root}/held-{label} {s.root}/release-{label}\nexit $st\n"
  return s!"{label}={s.root}/{label}.sh"

/-- How many times the scratch's train gate ran. -/
def gateRuns (s : Scratch) : IO Nat := do
  let t ← try IO.FS.readFile s!"{s.root}/gate-runs" catch _ => pure ""
  return ((t.splitOn "\n").filter (· == "run")).length

/-- A holder holds the lock while `names` wait, each asking once under one gate list and `env`:
the head takes the rest as riders, and the scenario runs `before`, releases the holder, then each
gate run of the train as it starts, `runs` at most; the members' exits and outputs. -/
def runTrain (self : String) (s : Scratch) (names : List String) (gates : String)
    (runs : Nat := 1) (before : IO Unit := pure ()) (env : Array (String × Option String) := #[]) :
    IO (Bool × List (Nat × String)) := do
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let mut tasks : List Pending := []
  let mut queued := held
  for n in names do
    tasks := tasks ++ [← landAsync self s.repo #[n] gates env]
    queued := queued && (← awaitQueued s n)
  let first ← awaitHead s (names.headD "")
  -- Every member waits, live, before the lock frees.
  let waiting ← awaitLive s names
  before
  release s "holder"
  let label := (gates.splitOn "=").headD ""
  for _ in [0:runs] do
    unless ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-{label}") do break
    release s label
    let _ ← awaitTrue do return !(← System.FilePath.pathExists s!"{s.root}/release-{label}")
  let (ch, _) ← awaitRun th
  let outs ← tasks.mapM awaitRun
  return (queued && first && waiting && ch == 0, outs)

/-- Three branches waiting behind a landing land in one run: one gate run on the train's tip,
main over all three in arrival order, each branch left at its own tip, each rider told it landed
in that run, and each retires by the commit it landed as. -/
def scenarioTrainThree (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/train3" "holder"
  let remote ← addRemote s
  let names := ["first", "second", "third"]
  for n in names do addAgent s n
  let tips ← names.mapM fun n => revOf s.repo s!"refs/heads/agent/{n}"
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
  let (cp, op) ← landIn self s.repo #["push"] "t=true"
  let published := cp == 0 && says op "result=pushed"
    && (← revOf remote "refs/heads/main") == (← revOf s.repo "refs/heads/main")
  let order ← mainSubjects s.repo
  let runs ← gateRuns s
  let run := match (((outs.headD (0, "")).2.splitOn "step=run result=ok id=").drop 1).head? with
    | some rest => (wsSplit rest).headD ""
    | none => ""
  let told := (outs.drop 1).all fun (c, o) => c == 0 && says o "result=landed"
    && saysField o "train" run
  let unmoved := (← names.mapM fun n => revOf s.repo s!"refs/heads/agent/{n}") == tips
  let mut retired := true
  for n in names do
    let (c, o) ← landIn self s.repo #["retire", n] "t=true"
    retired := retired && c == 0 && says o "landed-as="
  return { label := "three waiting branches land in one gate run, each left at its own tip, each \
rider told so, the train published, and each retires by the commit it landed as"
         , ok := ready && (outs.headD (0, "")).1 == 0 && told && runs == 1 && unmoved && retired
             && published
             && order == ["Base", "Add holder"] ++ names.map (s!"Add {·}") && !run.isEmpty
         , detail := s!"ready={ready} exits={outs.map (·.1)} told={told} gate-runs={runs} \
unmoved={unmoved} retired={retired} published={published} main={order} run={run}" }

/-- The middle of three branches conflicts with the first: it alone leaves the train, refused as
a conflict is, its branch untouched and its place gone, and the others land in one run. -/
def scenarioTrainConflict (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/trainconf" "holder"
  let names := ["first", "middle", "last"]
  for n in names do addAgent s n
  for (n, body) in [("first", "first"), ("middle", "middle")] do
    IO.FS.writeFile s!"{s.root}/lt-{n}/shared.txt" s!"{body}\n"
    hgitOk #["add", "shared.txt"] s!"{s.root}/lt-{n}"
    hgitOk #["commit", "-qm", s!"{n} writes shared"] s!"{s.root}/lt-{n}"
  let mid ← revOf s.repo "refs/heads/agent/middle"
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
  let order ← mainSubjects s.repo
  let midAfter ← revOf s.repo "refs/heads/agent/middle"
  let (cm, om) := outs.getD 1 (0, "")
  let q := (← queueOf s).map (·.name)
  return { label := "a middle member that conflicts leaves the train refused, and the others land"
         , ok := ready && (outs.headD (0, "")).1 == 0 && cm == 2
             && says om "rebase conflict: shared.txt" && (outs.getD 2 (0, "")).1 == 0
             && midAfter == mid && !q.contains "middle" && (← gateRuns s) == 1
             && order == ["Base", "Add holder", "Add first", "first writes shared", "Add last"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} middle={mid}->{midAfter} queue={q} \
main={order}" }

/-- A gate that fails on the second branch's file turns the train red: the head alone is gated
again and lands, and the others stay queued in their order, the second failing alone after and
the third landing. -/
def scenarioTrainRed (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/trainred" "holder"
  let names := ["first", "second", "third"]
  for n in names do addAgent s n
  let gates ← trainGate s "train" "test ! -e second.txt"
  let (ready, outs) ← runTrain self s names gates 5
  let order ← mainSubjects s.repo
  let o1 := (outs.headD (0, "")).2
  return { label := "a red train falls back to its head alone, and the rest stay queued in order"
         , ok := ready && (outs.headD (0, "")).1 == 0 && says o1 "step=retree result=ok"
             && (outs.getD 1 (0, "")).1 == 1 && (outs.getD 2 (0, "")).1 == 0
             && order == ["Base", "Add holder", "Add first", "Add third"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} gate-runs={← gateRuns s} main={order}" }

/-- The last of three branches moves while the train is gated: it leaves the train and stays
queued, the two before it are gated again and land, and it lands after with its new commit. -/
def scenarioTrainMoved (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/trainmoved" "holder"
  let names := ["first", "second", "third"]
  for n in names do addAgent s n
  let wt := s!"{s.root}/lt-third"
  let body := s!"if [ ! -e {s.root}/moved ]; then touch {s.root}/moved; \
git -C {wt} commit -q --allow-empty -m \"third moves\"; fi"
  let (ready, outs) ← runTrain self s names (← trainGate s "train" body) 3
  let order ← mainSubjects s.repo
  let o1 := (outs.headD (0, "")).2
  return { label := "a member that moves during the gates leaves the train, the rest land, and it \
lands after with its new commit"
         , ok := ready && outs.all (·.1 == 0) && says o1 "step=riders-recheck result=fail"
             && order == ["Base", "Add holder", "Add first", "Add second", "Add third", "third moves"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} gate-runs={← gateRuns s} main={order}" }

/-- A land built before the queue, which takes the lock without asking it, holds the lock and
lands a commit while a train waits: the train waits, then lands on top of it. -/
def scenarioTrainPreQueue (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/prequeue" "holder"
  let names := ["first", "second"]
  for n in names do addAgent s n
  IO.FS.createDirAll s!"{s.repo}/.git/land"
  let lock ← IO.FS.Handle.mk s!"{s.repo}/.git/land/landing.lock" .append
  lock.lock
  let gates ← trainGate s "train"
  let mut tasks : List Pending := []
  for n in names do
    tasks := tasks ++ [← landAsync self s.repo #[n] gates]
    let _ ← awaitQueued s n
  let first ← awaitHead s "first"
  -- The old land's own landing, as it would make it while holding the lock.
  IO.FS.writeFile s!"{s.repo}/old.txt" "old\n"
  hgitOk #["add", "old.txt"] s.repo
  hgitOk #["commit", "-qm", "An old land's landing"] s.repo
  lock.unlock
  let started ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-train")
  release s "train"
  let outs ← tasks.mapM awaitRun
  let order ← mainSubjects s.repo
  return { label := "a land that ignores the queue takes the lock out of turn, and the train lands \
on top of its landing"
         , ok := first && started && outs.all (·.1 == 0) && (← gateRuns s) == 1
             && order == ["Base", "An old land's landing", "Add first", "Add second"]
         , detail := s!"first={first} started={started} exits={outs.map (·.1)} main={order}" }

/-- The head of a train is killed in its gate: its riders wait again and land in the next run,
and the head lands when it asks again. -/
def scenarioTrainHeadKilled (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/trainkill" "holder"
  let names := ["head", "r1", "r2"]
  for n in names do addAgent s n
  writeExe s!"{s.root}/die.sh" s!"#!/bin/sh\nif [ ! -e {s.root}/died ]; then touch {s.root}/died; \
kill -TERM $PPID; sleep 1; fi\n"
  let gates := s!"die={s.root}/die.sh"
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let mut tasks : List Pending := []
  for n in names do
    tasks := tasks ++ [← landAsync self s.repo #[n] gates]
    let _ ← awaitQueued s n
  let first ← awaitHead s "head"
  let waiting ← awaitLive s names
  release s "holder"
  let (ch, _) ← awaitRun th
  let outs ← tasks.mapM awaitRun
  let (cr, or_) ← landIn self s.repo #["head"] gates
  let order ← mainSubjects s.repo
  return { label := "a train's head killed in its gate: the riders land in the next run, and the \
head when it asks again"
         , ok := held && first && waiting && ch == 0 && (outs.headD (0, "")).1 != 0
             && (outs.drop 1).all (·.1 == 0) && cr == 0 && says or_ "result=landed"
             && order == ["Base", "Add holder", "Add r1", "Add r2", "Add head"]
         , detail := s!"held={held} first={first} waiting={waiting} exits={outs.map (·.1)} \
retry={cr} main={order}" }

/-- A rider's own run dies while its train is gated: a push run for that name takes no place on
the train, refused, and the train still lands the rider. -/
def scenarioTrainPushHeld (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/trainpush" "holder"
  let _ ← addRemote s
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let gates ← trainGate s "train"
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let mut tasks : List Pending := []
  for n in names do
    tasks := tasks ++ [← landAsync self s.repo #[n] gates]
    let _ ← awaitQueued s n
  let first ← awaitHead s "first"
  let both ← awaitLive s names
  release s "holder"
  let gating ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-train")
  let rider := (← queueOf s).find? (·.name == "rider")
  let killed ← match rider with
    | some w => do pure ((← hrun "kill" #["-KILL", toString w.pid] none).1 == 0)
    | none => pure false
  let dead ← awaitTrue do
    match (← queueOf s).find? (·.name == "rider") with
    | some w => return !(← waiterLiveAt s!"{s.repo}/.git" w) && !w.train.isEmpty
    | none => return false
  let (cp, op) ← landIn self s.repo #["rider", "--push"] gates
  release s "train"
  let (ch, _) ← awaitRun th
  let outs ← tasks.mapM awaitRun
  let cf := (outs.headD (255, "")).1
  let order ← mainSubjects s.repo
  return { label := "a push run takes no place on a live train under another fare, and the train \
lands the rider whose run died"
         , ok := held && first && both && gating && killed && dead && cp == 2
             && says op "already waits for the lock in run" && ch == 0 && cf == 0
             && order == ["Base", "Add holder", "Add first", "Add rider"]
         , detail := s!"held={held} first={first} gating={gating} killed={killed} dead={dead} \
push={cp} first-exit={cf} main={order}" }

/-- A landed branch reads as landed only while its worktree is clean and no later row retired its
name: an uncommitted edit is refused as dirty, and a branch made again from main is not ahead. -/
def scenarioLandedDirty (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/landeddirty" "foo"
  IO.FS.writeFile s!"{s.repo}/other.txt" "other\n"
  hgitOk #["add", "other.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let (c1, _) ← landIn self s.repo #["foo"] "t=true"
  IO.FS.writeFile s!"{s.wt}/foo.txt" "foo, edited\n"
  let (c2, o2) ← landIn self s.repo #["foo"] "t=true"
  hgitOk #["checkout", "--", "foo.txt"] s.wt
  let (c3, o3) ← landIn self s.repo #["foo"] "t=true"
  let (c4, _) ← landIn self s.repo #["retire", "foo"] "t=true"
  hgitOk #["worktree", "add", "-q", "-b", "agent/foo", s.wt, "main"] s.repo
  IO.FS.writeFile s!"{s.wt}/notes.txt" "notes\n"
  let (c5, o5) ← landIn self s.repo #["foo"] "t=true"
  return { label := "a landed branch is answered as landed only clean and unretired: an edit is \
refused as dirty, and a branch made again is not ahead"
         , ok := c1 == 0 && c2 == 2 && says o2 "is dirty" && !says o2 "already=yes"
             && c3 == 0 && says o3 "already=yes" && c4 == 0
             && c5 == 2 && says o5 "is not ahead of main" && !says o5 "already=yes"
         , detail := s!"land={c1} dirty={c2} clean={c3} retire={c4} again={c5}" }

/-- A rider whose worktree vanished while it waited leaves the train refused, its reason named,
and the head lands. -/
def scenarioRiderVanished (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/vanished" "holder"
  let names := ["first", "gone"]
  for n in names do addAgent s n
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
    (before := rmQuiet s!"{s.root}/lt-gone")
  let (cg, og) := outs.getD 1 (0, "")
  let order ← mainSubjects s.repo
  return { label := "a rider git cannot read leaves the train refused, and the head lands"
         , ok := ready && (outs.headD (0, "")).1 == 0 && cg == 2
             && says og "agent/gone could not be read" && order == ["Base", "Add holder", "Add first"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} main={order}" }

/-- What an owner sees of a member: its branch tip, its worktree's `HEAD` and index, and every
file in its worktree, byte for byte. -/
def memberState (s : Scratch) (name : String) : IO (List (String × ByteArray)) := do
  let wt := s!"{s.root}/lt-{name}"
  let path (p : String) : String := if p.startsWith "/" then p else s!"{wt}/{p}"
  let (_, head) ← hgit #["rev-parse", "--git-path", "HEAD"] wt
  let (_, index) ← hgit #["rev-parse", "--git-path", "index"] wt
  let mut out : List (String × ByteArray) :=
    [("tip", (← revOf s.repo s!"refs/heads/agent/{name}").toUTF8),
     ("HEAD", ← IO.FS.readBinFile (path head)), ("index", ← IO.FS.readBinFile (path index))]
  for p in ← (System.FilePath.mk wt).walkDir do
    unless ← p.isDir do out := out ++ [(p.toString, ← IO.FS.readBinFile p)]
  return out

/-- A train writes no member's branch or worktree: each member's branch, index and files read as
before, an ignored local file at a path the train tracks among them, and each retires by the
commit it landed as. -/
def scenarioTrainUntouched (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/untouched" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  IO.FS.writeFile s!"{s.repo}/.git/info/exclude" "local.cfg\n"
  IO.FS.writeFile s!"{s.root}/lt-first/local.cfg" "first's tracked settings\n"
  hgitOk #["add", "-f", "local.cfg"] s!"{s.root}/lt-first"
  hgitOk #["commit", "-qm", "first tracks local.cfg"] s!"{s.root}/lt-first"
  IO.FS.writeFile s!"{s.root}/lt-rider/local.cfg" "the rider owner's local settings\n"
  -- Rewritten unchanged a second after its commit, a git status that refreshes would write the index.
  IO.sleep 1100
  IO.FS.writeFile s!"{s.root}/lt-rider/rider.txt" "rider\n"
  let before ← names.mapM (memberState s)
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
  let after ← names.mapM (memberState s)
  let same := before.zip after |>.all fun (b, a) =>
    b.length == a.length && (b.zip a).all fun ((k, x), (l, y)) => k == l && x.data == y.data
  let mut retired := true
  for n in names do
    let (c, o) ← landIn self s.repo #["retire", n] "t=true"
    retired := retired && c == 0 && says o "landed-as="
  return { label := "a train writes no member's branch or worktree, and each member retires by the \
commit it landed as"
         , ok := ready && outs.all (·.1 == 0) && same && retired
         , detail := s!"ready={ready} exits={outs.map (·.1)} unchanged={same} retired={retired}" }

/-- A rider whose rebase leaves the tree dirty, a hook its content sets off, leaves the train
refused, the tree put back, and the others land. -/
def scenarioTrainRiderDirty (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/riderdirty" "holder"
  let names := ["first", "mid", "bad"]
  for n in names do addAgent s n
  IO.FS.writeFile s!"{s.root}/lt-bad/dirty-marker.txt" "marker\n"
  hgitOk #["add", "dirty-marker.txt"] s!"{s.root}/lt-bad"
  hgitOk #["commit", "-qm", "bad adds a marker"] s!"{s.root}/lt-bad"
  writeExe s!"{s.repo}/.git/hooks/post-rewrite"
    "#!/bin/sh\nif [ -e dirty-marker.txt ]; then touch stray-from-hook.txt; fi\nexit 0\n"
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
  let order ← mainSubjects s.repo
  let (cb, ob) := outs.getD 2 (0, "")
  return { label := "a rider whose rebase leaves the tree dirty leaves the train refused, and the \
others land"
         , ok := ready && (outs.take 2).all (·.1 == 0) && cb == 2
             && says ob "dirty or on a branch after agent/bad's rebase"
             && order == ["Base", "Add holder", "Add first", "Add mid"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} main={order}" }

/-- Stop the live run waiting under `name`, holding the queue's lock so that it is never stopped
holding it; the pid stopped, if any. -/
def stopWaiter (s : Scratch) (name : String) : IO (Option Nat) := do
  let ql ← IO.FS.Handle.mk s!"{s.repo}/.git/land/queue.lock" .append
  ql.lock
  try
    let some w := (← queueOf s).find? (·.name == name) | return none
    if w.pid == 0 || !(← waiterLiveAt s!"{s.repo}/.git" w) then return none
    let (c, _) ← hrun "kill" #["-STOP", toString w.pid] none
    return if c == 0 then some w.pid else none
  finally ql.unlock

/-- A rider whose run is stopped across its whole train is told the train's verdict once it runs
again: landed, with exit 0. -/
def scenarioTrainRiderStopped (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/riderstopped" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tf ← landAsync self s.repo #["first"] "t=true"
  let _ ← awaitQueued s "first"
  let tr ← landAsync self s.repo #["rider"] "t=true"
  let live ← awaitLive s names
  let stopped ← if live then stopWaiter s "rider" else pure none
  let (cf, landed) ← try
      release s "holder"
      let _ ← awaitRun th
      let (cf, _) ← awaitRun tf
      pure (cf, (← mainSubjects s.repo).contains "Add rider")
    finally
      if let some pid := stopped then
        let _ ← hrun "kill" #["-CONT", toString pid] none
  let (cr, or_) ← awaitRun tr
  return { label := "a rider stopped across its whole train is told it landed once it runs again"
         , ok := held && live && stopped.isSome && cf == 0 && landed && cr == 0
             && says or_ "result=landed"
         , detail := s!"held={held} live={live} stopped={stopped.isSome} head={cf} \
rider-on-main={landed} rider={cr}" }

/-- A train's gate that dirties the tree once falls back to the head, which lands, and the rider,
queued again, lands after. -/
def scenarioTrainGateDirtied (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/gatedirtied" "holder"
  let names := ["first", "second"]
  for n in names do addAgent s n
  let body := s!"if [ ! -e {s.root}/dirtied ]; then touch {s.root}/dirtied; touch stray.txt; fi"
  let (ready, outs) ← runTrain self s names (← trainGate s "train" body) 3
  let order ← mainSubjects s.repo
  return { label := "a train's gate that dirties the tree falls back to the head, and the rider \
lands after"
         , ok := ready && outs.all (·.1 == 0) && order == ["Base", "Add holder", "Add first", "Add second"]
         , detail := s!"ready={ready} exits={outs.map (·.1)} main={order}" }

/-- A check waits its turn like a landing, while a push takes no place: refused at once behind a
waiting check, it publishes once the lock is free and no one waits. -/
def scenarioQueueTurns (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/turns" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  let remote ← addRemote s
  addAgent s "checked"
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tc ← landAsync self s.repo #["check", "checked"] (← holdGate s "checked")
  let first ← awaitHead s "checked"
  let (cp, op) ← landIn self s.repo #["push"] "t=true"
  let q := (← queueOf s).map (·.name)
  let refused := cp == 2 && says op "another landing holds the lock" && says op "takes no place"
    && q == ["checked"]
  let handed ← handOn s "holder" "checked"
  release s "checked"
  let (ch, _) ← awaitRun th
  let (cc, oc) ← awaitRun tc
  let landedTip ← revOf s.repo "refs/heads/main"
  let (cp2, op2) ← landIn self s.repo #["push"] "t=true"
  let onRemote ← revOf remote "refs/heads/main"
  return { label := "a check waits its turn, and a push takes no place and never waits"
         , ok := held && first && refused && handed && ch == 0 && cc == 0
             && says oc "result=checked" && cp2 == 0 && says op2 "result=pushed"
             && onRemote == landedTip
         , detail := s!"held={held} check-first={first} push-refused={refused} queue={q} \
handed={handed} holder={ch} check={cc} push={cp2} remote={onRemote} main={landedTip}" }

/-- Four waiters enter at one moment: the queue holds each once in one order, each refusal
names its own place behind the one head, and they land in that order. -/
def scenarioQueueTies (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/ties" "holder"
  hgitOk #["config", "--local", "land.trainCap", "1"] s.repo
  let names := ["tie-a", "tie-b", "tie-c", "tie-d"]
  for n in names do addAgent s n
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let gates ← names.mapM (holdGate s)
  let firsts ← (names.zip gates).mapM fun (n, g) => landAsync self s.repo #[n] g
  let all4 ← awaitTrue do
    let q ← queueOf s
    return names.all fun n => q.any (·.name == n)
  let settled ← awaitTrue do return (← firsts.filterM fun t => IO.hasFinished t).length == 3
  let order := (← queueOf s).map (·.name)
  let mut placed := settled && order.length == 4
  let mut loops : List Pending := []
  for (n, t) in names.zip firsts do
    if ← IO.hasFinished t then
      let (c, o) ← awaitRun t
      let p := order.idxOf n + 1
      placed := placed && c == 2 && p ≥ 2 && saysField o "position" (toString p)
        && saysField o "head" (order.headD "")
    else
      placed := placed && order.head? == some n
      loops := loops ++ [t]
  for (n, i) in (order.drop 1).zipIdx do
    let g ← holdGate s n
    loops := loops ++ [← landRetrying self s.repo n g (900 - 300 * i).toUInt32]
  let mut handed := true
  for (a, b) in ("holder" :: order).zip order do
    handed := handed && (← handOn s a b)
  release s (order.getLastD "")
  let (ch, _) ← awaitRun th
  let codes ← loops.mapM fun t => (·.1) <$> awaitRun t
  let landed ← mainSubjects s.repo
  return { label := "four waiters entering at one moment get one order, each its own place, \
and land in it"
         , ok := held && all4 && placed && handed && ch == 0 && codes.all (· == 0)
             && landed == ["Base", "Add holder"] ++ order.map (s!"Add {·}")
         , detail := s!"held={held} all-entered={all4} settled={settled} placed={placed} \
handed={handed} queue={order} holder={ch} codes={codes} main={landed}" }

/-- A `git` on `PATH` that runs `hook` once, when the landing invokes `git` with arguments
`cond` accepts, then the real git. -/
def gitWrapper (s : Scratch) (cond hook : String) (after : Bool := false) : IO String := do
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  IO.FS.createDirAll s!"{s.root}/wrap"
  let body := if after then
      s!"  \"{realGit}\" \"$@\"; rc=$?\n{hook}\n  touch {s.root}/fired\n  exit $rc\n"
    else s!"{hook}\n  touch {s.root}/fired\n"
  writeExe s!"{s.root}/wrap/git"
    s!"#!/bin/sh\nif {cond} && [ ! -e {s.root}/fired ]; then\n{body}fi\nexec \"{realGit}\" \"$@\"\n"
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  return s!"{s.root}/wrap:{path}"

/-- The owner's next unit, committed in the owner's own worktree by the wrapper. -/
def ownerCommit (s : Scratch) (realGit : String) : String :=
  s!"  echo \"the owner's next unit\" > {s.wt}/owner-work.txt\n\
  \"{realGit}\" -C {s.wt} add owner-work.txt\n\
  \"{realGit}\" -C {s.wt} commit -qm \"The owner's next unit\"\n\
  \"{realGit}\" -C {s.wt} rev-parse HEAD > {s.root}/owner-commit.txt"

/-- Whether the owner's commit is still on the owner's branch, and its file in the owner's
clean worktree. -/
def ownerKept (s : Scratch) (branch : String) : IO (Bool × String) := do
  let oc := trimWs (← try IO.FS.readFile s!"{s.root}/owner-commit.txt" catch _ => pure "")
  let (anc, _) ← hgit #["merge-base", "--is-ancestor", oc, branch] s.repo
  let present ← System.FilePath.pathExists s!"{s.wt}/owner-work.txt"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  return (isSha oc && anc == 0 && present && st.isEmpty,
    s!"owner-commit={oc} reachable={anc == 0} file={present} status=[{st}]")

/-- The owner commits just before the gated tip is prepared: the landing keeps that commit
and refuses. -/
def scenarioOwnerCommitsBeforeRebase (self root : String) (diverged : Bool := false) :
    IO Outcome := do
  let name := if diverged then "ownerbefore-rebase" else "ownerbefore"
  let s ← mkScratch s!"{root}/{name}" "own"
  if diverged then
    IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
    hgitOk #["add", "m.txt"] s.repo
    hgitOk #["commit", "-qm", "Main moves"] s.repo
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  let cond := "{ { [ \"$1\" = rebase ] && [ \"$2\" != --abort ]; } || \
{ [ \"$1\" = checkout ] && [ \"$2\" = --detach ]; }; }"
  let path ← gitWrapper s cond (ownerCommit s realGit)
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["own"] "t=true" #[("PATH", some path)]
  let after ← revOf s.repo "refs/heads/main"
  let (kept, facts) ← ownerKept s "refs/heads/agent/own"
  return { label := s!"an owner's commit made while preparing the tip is kept ({name})"
         , ok := code == 2 && kept && before == after && says out "moved during the"
         , detail := s!"exit={code} main={before}->{after} {facts}" }

/-- As above, the owner's commit the instant the rebase ends, under `land check`, which
must write nothing of the owner's. -/
def scenarioOwnerCommitsAfterRebase (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/ownerafter" "own"
  IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
  hgitOk #["add", "m.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  let path ← gitWrapper s "[ \"$1\" = rebase ] && [ \"$2\" != --abort ]" (ownerCommit s realGit)
    (after := true)
  let before ← revOf s.repo "refs/heads/main"
  let (code, _) ← landIn self s.repo #["check", "own"] "t=true" #[("PATH", some path)]
  let after ← revOf s.repo "refs/heads/main"
  let (kept, facts) ← ownerKept s "refs/heads/agent/own"
  return { label := "an owner's commit made as a check's rebase ends is kept"
         , ok := code == 0 && kept && before == after
         , detail := s!"exit={code} main={before}->{after} {facts}" }

/-- The main worktree switched to another branch at the fast-forward: only
`refs/heads/main` moves. -/
def scenarioMainSwitchedAtMerge (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/switchff" "switchff"
  hgitOk #["branch", "side", "main"] s.repo
  let side0 ← revOf s.repo "refs/heads/side"
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  let cond := "{ [ \"$1\" = merge ] || { [ \"$1\" = push ] && [ \"$4\" = . ]; }; }"
  let path ← gitWrapper s cond s!"  \"{realGit}\" -C {s.repo} checkout -q side"
  let tip ← revOf s.repo "refs/heads/agent/switchff"
  let (code, _) ← landIn self s.repo #["switchff"] "t=true" #[("PATH", some path)]
  let side1 ← revOf s.repo "refs/heads/side"
  let main1 ← revOf s.repo "refs/heads/main"
  let fired ← System.FilePath.pathExists s!"{s.root}/fired"
  return { label := "a main worktree switched at the fast-forward moves main, and only main"
         , ok := fired && code == 0 && side1 == side0 && main1 == tip
         , detail := s!"exit={code} fired={fired} side={side0}->{side1} main={main1} \
gated={tip}" }

/-- The remote holds a ref ending in `refs/heads/main` that sorts first; the read-back
reads `refs/heads/main` itself. -/
def scenarioLsRemoteDecoy (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/decoy" "decoy"
  let remote ← addRemote s
  let base ← revOf remote "refs/heads/main"
  hgitOk #["update-ref", "refs/heads/a/refs/heads/main", base] remote
  let tip ← revOf s.repo "refs/heads/agent/decoy"
  let (code, out) ← landIn self s.repo #["decoy", "--push"] "t=true"
  let onRemote ← revOf remote "refs/heads/main"
  let ledger ← try IO.FS.readFile s!"{s.repo}/.git/land/ledger.jsonl" catch _ => pure ""
  return { label := "the push is read back from refs/heads/main itself"
         , ok := code == 0 && onRemote == tip && says out "result=landed"
             && says ledger "\"verdict\":\"pushed\""
         , detail := s!"exit={code} remote={onRemote} gated={tip}" }

/-- `main` moved, so the branch lands as rebased copies; asking again to land the unmoved branch
answers that `main` holds it, landing nothing. -/
def scenarioRelandRefused (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/reland" "reland"
  IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
  hgitOk #["add", "m.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let bTip ← revOf s.repo "refs/heads/agent/reland"
  let (c1, _) ← landIn self s.repo #["reland"] "t=true"
  let main1 ← revOf s.repo "refs/heads/main"
  let bAfter ← revOf s.repo "refs/heads/agent/reland"
  let (c2, out2) ← landIn self s.repo #["reland"] "t=true"
  let main2 ← revOf s.repo "refs/heads/main"
  return { label := "a rebased landing leaves the branch alone, and asking again answers it landed"
         , ok := c1 == 0 && bAfter == bTip && main1 != bTip && c2 == 0 && main2 == main1
             && says out2 "result=landed" && says out2 "already=yes"
         , detail := s!"first={c1} second={c2} branch={bTip}->{bAfter} main={main1}->{main2}" }

/-- `main` put back past a landing: the unmoved branch lands again, and after another undo
so does a continued one; while `main` holds the landing, the unmoved branch is answered landed
and the continued one is refused and sent to a new branch. -/
def scenarioMainPutBack (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/putback" "own"
  IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
  hgitOk #["add", "m.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let m0 ← revOf s.repo "refs/heads/main"
  let bTip ← revOf s.repo "refs/heads/agent/own"
  let onMain (path : String) : IO Bool := do
    let (c, _) ← hgit #["cat-file", "-e", s!"refs/heads/main:{path}"] s.repo
    return c == 0
  let (c1, _) ← landIn self s.repo #["own"] "t=true"
  let g1 ← revOf s.repo "refs/heads/main"
  hgitOk #["reset", "-q", "--hard", m0] s.repo
  -- Put back: the unmoved branch lands again.
  let (c2, _) ← landIn self s.repo #["own"] "t=true"
  let own2 ← onMain "own.txt"
  let g2 ← revOf s.repo "refs/heads/main"
  -- `main` holds that landing: the unmoved branch is answered landed, the continued one sent on.
  let (c3, out3) ← landIn self s.repo #["own"] "t=true"
  IO.FS.writeFile s!"{s.wt}/next.txt" "next\n"
  hgitOk #["add", "next.txt"] s.wt
  hgitOk #["commit", "-qm", "Next unit"] s.wt
  let nTip ← revOf s.repo "refs/heads/agent/own"
  let (c4, out4) ← landIn self s.repo #["own"] "t=true"
  let g4 ← revOf s.repo "refs/heads/main"
  -- Put back again: the continued branch lands both units.
  hgitOk #["reset", "-q", "--hard", m0] s.repo
  let (c5, _) ← landIn self s.repo #["own"] "t=true"
  let own5 ← onMain "own.txt"
  let next5 ← onMain "next.txt"
  let bAfter ← revOf s.repo "refs/heads/agent/own"
  let pointed (out : String) : Bool := says out "land new <name>" && !says out "git rebase"
  return { label := "main put back after a rebased landing: the branch lands again, and a \
continued branch is not told to drop what main lacks"
         , ok := c1 == 0 && g1 != bTip && c2 == 0 && own2 && c3 == 0 && says out3 "already=yes"
             && c4 == 2 && pointed out4 && g4 == g2 && c5 == 0 && own5 && next5
             && bAfter == nTip
         , detail := s!"land={c1} put-back-land={c2} own-on-main={own2} again={c3} \
pointed={pointed out3} continued={c4} pointed={pointed out4} main={g2}->{g4} \
put-back-continued={c5} own-on-main={own5} next-on-main={next5} branch={nTip}->{bAfter}" }

/-- A branch landed as rebased copies is retired by the ledger's word and deleted by
compare-and-swap. -/
def scenarioRetireRebased (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/retireb" "retireb"
  IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
  hgitOk #["add", "m.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let (c1, _) ← landIn self s.repo #["retireb"] "t=true"
  let (c2, out2) ← landIn self s.repo #["retire", "retireb"] "t=true"
  let (hasRef, _) ← hgit #["show-ref", "--verify", "--quiet", "refs/heads/agent/retireb"] s.repo
  let wtGone := !(← System.FilePath.pathExists s.wt)
  return { label := "a branch landed as rebased copies retires"
         , ok := c1 == 0 && c2 == 0 && hasRef != 0 && wtGone && says out2 "result=retired"
         , detail := s!"land={c1} retire={c2} ref-left={hasRef == 0} worktree-gone={wtGone}" }

/-- A landing made without `--push` is published later by `land push`, while a second
`land <name> --push` refuses. -/
def scenarioPushLater (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushlater" "later"
  let remote ← addRemote s
  let base ← revOf remote "refs/heads/main"
  let tip ← revOf s.repo "refs/heads/agent/later"
  let (c1, _) ← landIn self s.repo #["later"] "t=true"
  let mid ← revOf remote "refs/heads/main"
  let (c2, out2) ← landIn self s.repo #["push"] "t=true"
  let onRemote ← revOf remote "refs/heads/main"
  let ledger ← try IO.FS.readFile s!"{s.repo}/.git/land/ledger.jsonl" catch _ => pure ""
  return { label := "land push publishes the last landing and records it"
         , ok := c1 == 0 && mid == base && c2 == 0 && onRemote == tip
             && says out2 "result=pushed" && says ledger "\"verdict\":\"pushed\""
         , detail := s!"land={c1} push={c2} remote={base}->{mid}->{onRemote} gated={tip}" }

/-- A commit put on `main` by hand after the last landing: `land push` refuses to publish
it. -/
def scenarioPushUngated (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushungated" "ungated"
  let remote ← addRemote s
  let base ← revOf remote "refs/heads/main"
  let (c1, _) ← landIn self s.repo #["ungated"] "t=true"
  hgitOk #["commit", "-q", "--allow-empty", "-m", "ungated"] s.repo
  let (c2, out2) ← landIn self s.repo #["push"] "t=true"
  let onRemote ← revOf remote "refs/heads/main"
  return { label := "land push refuses a main that holds a commit no landing gated"
         , ok := c1 == 0 && c2 == 2 && onRemote == base
             && says out2 "a commit no landing gated"
         , detail := s!"land={c1} push={c2} remote={base}->{onRemote}" }

/-- A repository whose `main` is one commit ahead of its origin's, with a linked worktree
whose hook is handed `GIT_DIR` and `GIT_INDEX_FILE`. -/
structure Victim where
  root : String
  repo : String
  origin : String
  wt : String
  /-- The linked worktree's git directory, which a hook there is handed as
  `GIT_DIR`. -/
  gitDir : String

def mkVictim (root : String) : IO Victim := do
  let repo := s!"{root}/victim"
  IO.FS.createDirAll repo
  hgitOk #["init", "-q", "-b", "main", "."] repo
  hgitOk #["config", "user.name", "Victim"] repo
  hgitOk #["config", "user.email", "victim@example.org"] repo
  IO.FS.writeFile s!"{repo}/v.txt" "v\n"
  hgitOk #["add", "v.txt"] repo
  hgitOk #["commit", "-qm", "The victim's own commit"] repo
  let origin := s!"{root}/victim-origin.git"
  hgitOk #["init", "-q", "--bare", "-b", "main", origin] root
  hgitOk #["remote", "add", "origin", origin] repo
  hgitOk #["push", "-q", origin, "main"] repo
  hgitOk #["update-ref", "refs/remotes/origin/main", "main"] repo
  IO.FS.writeFile s!"{repo}/w.txt" "w\n"
  hgitOk #["add", "w.txt"] repo
  hgitOk #["commit", "-qm", "Ahead of the origin"] repo
  let wt := s!"{root}/victim-wt"
  hgitOk #["worktree", "add", "-q", "-b", "agent/victim", wt, "main"] repo
  let gitDir ← gitDirOf wt
  if !within root gitDir then
    throw (IO.userError s!"fixture: the victim's worktree names the repository {gitDir}")
  return { root, repo, origin, wt, gitDir }

/-- Everything a command could have written in the victim and its origin: refs, config,
worktrees, and the linked worktree's `HEAD` and index as bytes. -/
structure VictimState where
  origin : String
  refs : String
  config : String
  worktrees : String
  head : String
  index : Array UInt8
  deriving BEq

def victimState (v : Victim) : IO VictimState := do
  let (_, origin) ← hgit #["for-each-ref", "--format=%(objectname) %(refname)"] v.origin
  let (_, refs) ← hgit #["for-each-ref", "--format=%(objectname) %(refname)"] v.repo
  let (_, worktrees) ← hgit #["worktree", "list", "--porcelain"] v.repo
  let config ← IO.FS.readFile s!"{v.repo}/.git/config"
  let head ← IO.FS.readFile s!"{v.gitDir}/HEAD"
  let index := (← IO.FS.readBinFile s!"{v.gitDir}/index").data
  return { origin, refs, config, worktrees, head, index }

/-- The parts of the victim that differ between two reads, for a detail. -/
def VictimState.changed (a b : VictimState) : String :=
  let parts := [("origin", a.origin == b.origin), ("refs", a.refs == b.refs),
    ("config", a.config == b.config), ("worktrees", a.worktrees == b.worktrees),
    ("head", a.head == b.head), ("index", a.index == b.index)]
  match parts.filter (!·.2) with
  | [] => "none"
  | bad => String.intercalate "," (bad.map (·.1))

/-- A harness started the way a hook in a linked worktree starts a program, `GIT_DIR` and
`GIT_INDEX_FILE` naming its repository, leaves it and its origin as they were. -/
def scenarioHookGitDir (self root : String) : IO Outcome := do
  let v ← mkVictim s!"{root}/hookdir"
  let before ← victimState v
  let nested := s!"{v.root}/nested"
  IO.FS.createDirAll nested
  let (code, out) ← runTool self v.wt #["--scratch-selftest"]
    #[("GIT_DIR", some v.gitDir), ("GIT_INDEX_FILE", some s!"{v.gitDir}/index"),
      ("GIT_EDITOR", some ":"), ("GIT_PREFIX", some ""),
      ("LAND_SCRATCH_DIR", some nested), ("LAND_SCENARIO_NESTED", some "1")]
  let after ← victimState v
  let ran := (out.splitOn "step=scenario result=").length - 1
  let pushed := says out "the push sends the gated tip, not whatever main is by then"
  let failed := (out.splitOn "\n").filter (says · "step=scenario result=fail")
  return { label := "a harness started under a hook's GIT_DIR runs, and leaves that repository \
and its origin as they were"
         , ok := code == 0 && ran ≥ 10 && pushed && before == after
         , detail := s!"exit={code} scenarios={ran} push-scenario={pushed} \
changed={before.changed after} failed={failed}" }

/-- A harness whose scratch root lies inside a checkout refuses to start and leaves the
checkout and the directory as they were. -/
def scenarioRootInCheckout (self root : String) : IO Outcome := do
  let v ← mkVictim s!"{root}/incheckout"
  let inside := s!"{v.repo}/scratch"
  IO.FS.createDirAll inside
  let before ← victimState v
  let (code, out) ← runTool self v.repo #["--scratch-selftest"]
    #[("LAND_SCRATCH_DIR", some inside), ("LAND_SCENARIO_NESTED", some "1")]
  let after ← victimState v
  let left := (← System.FilePath.readDir inside).size
  let named := says out "is inside the checkout"
  return { label := "a harness whose scratch root lies inside a checkout refuses to start"
         , ok := code == 2 && named && before == after && left == 0
         , detail := s!"exit={code} refused={named} left={left} changed={before.changed after}" }

/-- The guard refuses each command whose writes the run does not own before git runs,
while a push by path to the run's own bare repository goes through. -/
def scenarioGuardRefuses (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/guard" "guard"
  let remote ← addRemote s
  let unmade := s!"{s.root}/unmade.git"
  hgitOk #["init", "-q", "-b", "main", unmade] s.root
  let tries : List (String × Array String × String) :=
    [ ("outside", #["status", "--porcelain"], "/")
    , ("by-name", #["push", "-q", "origin", "main:refs/heads/by-name"], s.repo)
    , ("unmade", #["push", "-q", unmade, "main:refs/heads/other"], s.repo)
    , ("global", #["-C", s.repo, "status"], s.repo)
    , ("fetch", #["fetch", "-q", remote], s.repo) ]
  let mut refused : Array String := #[]
  for (key, args, cwd) in tries do
    let (c, _) ← hgit args cwd
    if c == refusedCode then refused := refused.push key
  hgitOk #["remote", "add", "elsewhere", unmade] s.repo
  let (tool, _) ← runTool self s.repo #["status"] #[]
  let (byPath, _) ← hgit #["push", "-q", remote, "main:refs/heads/by-path"] s.repo
  let (_, onRemote) ← hgit #["for-each-ref", "--format=%(refname)"] remote
  let (_, onUnmade) ← hgit #["for-each-ref", "--format=%(refname)"] unmade
  let wrote := says onRemote "by-name" || says onUnmade "refs/heads/other"
  return { label := "the guard refuses each command whose writes the run does not own, before \
git runs"
         , ok := refused.size == tries.length && tool == refusedCode && byPath == 0
             && says onRemote "refs/heads/by-path" && !wrote
         , detail := s!"refused=[{String.intercalate "," refused.toList}] tool={tool} \
by-path={byPath} wrote={wrote}" }

/-- No harness command can use a network transport: a gate asking for a loopback remote
passes only when git refused the transport before connecting. -/
def scenarioNoNetwork (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/nonet" "nonet"
  writeExe s!"{s.root}/probe.sh"
    s!"#!/bin/sh\nunset http_proxy https_proxy HTTP_PROXY HTTPS_PROXY ALL_PROXY all_proxy\n\
git ls-remote https://127.0.0.1:9/probe.git 2> {s.root}/probe.err\n\
grep -q \"transport 'https' not allowed\" {s.root}/probe.err\n"
  let tip ← revOf s.repo "refs/heads/agent/nonet"
  let (code, _) ← landIn self s.repo #["nonet"] s!"probe={s.root}/probe.sh"
  let after ← revOf s.repo "refs/heads/main"
  let said := trimWs (← try IO.FS.readFile s!"{s.root}/probe.err" catch _ => pure "")
  return { label := "no command the harness starts can use a network transport"
         , ok := code == 0 && after == tip
         , detail := s!"exit={code} main={after} gated={tip} git-said=[{said}]" }

/-- A train's head killed after its landed rows, before it settles its riders: each rider is
told it landed, with exit 0. -/
def scenarioTrainKilledAfterRows (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/killedrows" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let wrap ← gitWrapper s "[ \"$1\" = worktree ] && [ \"$2\" = remove ]" "  kill -KILL $PPID"
  let (ready, outs) ← runTrain self s names (← trainGate s "train") (env := #[("PATH", some wrap)])
  let fired ← System.FilePath.pathExists s!"{s.root}/fired"
  let (cr, or_) := outs.getD 1 (0, "")
  return { label := "a train's head killed after its landed rows leaves each rider told it landed"
         , ok := ready && fired && (outs.headD (0, "")).1 != 0 && cr == 0 && says or_ "result=landed"
             && (← mainSubjects s.repo) == ["Base", "Add holder", "Add first", "Add rider"]
         , detail := s!"ready={ready} fired={fired} exits={outs.map (·.1)}" }

/-- A rider stopped across its whole train, whose head is killed after its landed rows before it
settles the rider's place, is told it landed once it runs again. -/
def scenarioTrainStoppedKilled (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/stoppedkilled" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let wrap ← gitWrapper s "[ \"$1\" = worktree ] && [ \"$2\" = remove ]" "  kill -KILL $PPID"
  let env := #[("PATH", some wrap)]
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tf ← landAsync self s.repo #["first"] "t=true" env
  let _ ← awaitQueued s "first"
  let tr ← landAsync self s.repo #["rider"] "t=true" env
  let live ← awaitLive s names
  let stopped ← if live then stopWaiter s "rider" else pure none
  let cf ← try
      release s "holder"
      let _ ← awaitRun th
      pure (← awaitRun tf).1
    finally
      if let some pid := stopped then
        let _ ← hrun "kill" #["-CONT", toString pid] none
  let (cr, or_) ← awaitRun tr
  return { label := "a rider stopped across its train, whose head dies after its landed rows, is \
told it landed"
         , ok := held && live && stopped.isSome && cf != 0 && cr == 0 && says or_ "result=landed"
             && (← mainSubjects s.repo) == ["Base", "Add holder", "Add first", "Add rider"]
         , detail := s!"held={held} live={live} stopped={stopped.isSome} head={cf} rider={cr}" }

/-- A rider's run killed while its train's head dies after the landed rows leaves its place boarded
on a dead train: a new run of that name after a new commit is not told that train's verdict, but
refused as a landed branch continued, the new commit not on main. -/
def scenarioTrainStaleBoarding (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/staleboarding" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let wrap ← gitWrapper s "[ \"$1\" = worktree ] && [ \"$2\" = remove ]" "  kill -KILL $PPID"
  let env := #[("PATH", some wrap)]
  let th ← landAsync self s.repo #["holder"] (← holdGate s "holder")
  let held ← awaitTrue (System.FilePath.pathExists s!"{s.root}/held-holder")
  let tf ← landAsync self s.repo #["first"] "t=true" env
  let _ ← awaitQueued s "first"
  let tr ← landAsync self s.repo #["rider"] "t=true" env
  let live ← awaitLive s names
  let stopped ← if live then stopWaiter s "rider" else pure none
  let cf ← try
      release s "holder"
      let _ ← awaitRun th
      pure (← awaitRun tf).1
    finally
      if let some pid := stopped then
        let _ ← hrun "kill" #["-KILL", toString pid] none
  let (cr, _) ← awaitRun tr
  let boarded := ((← queueOf s).find? (·.name == "rider")).any (!·.train.isEmpty)
  IO.FS.writeFile s!"{s.root}/lt-rider/next.txt" "next\n"
  hgitOk #["add", "next.txt"] s!"{s.root}/lt-rider"
  hgitOk #["commit", "-qm", "The owner's next unit"] s!"{s.root}/lt-rider"
  let (ca, oa) ← landIn self s.repo #["rider"] "t=true"
  let order ← mainSubjects s.repo
  return { label := "a new run of a name whose place a dead train boarded is not told that \
train's verdict"
         , ok := held && live && stopped.isSome && cf != 0 && cr != 0 && boarded && ca == 2
             && says oa "is already landed" && !says oa "result=landed"
             && order == ["Base", "Add holder", "Add first", "Add rider"]
         , detail := s!"held={held} live={live} stopped={stopped.isSome} head={cf} rider={cr} \
boarded={boarded} again={ca} main={order}" }

/-- A train's head killed right after its fast-forward, before any landed row: the write-ahead row
lands each member, its rider told so, and each lands as already landed and retires. -/
def scenarioTrainKilledAfterFF (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/killedff" "holder"
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let wrap ← gitWrapper s "[ \"$1\" = push ] && [ \"$2\" = --porcelain ]" "  kill -KILL $PPID"
    (after := true)
  let (ready, outs) ← runTrain self s names (← trainGate s "train") (env := #[("PATH", some wrap)])
  let fired ← System.FilePath.pathExists s!"{s.root}/fired"
  let (cr, or_) := outs.getD 1 (0, "")
  let mut again := true
  for n in names do
    let (c, o) ← landIn self s.repo #[n] "t=true"
    let (cr, orr) ← landIn self s.repo #["retire", n] "t=true"
    again := again && c == 0 && says o "already=yes" && cr == 0 && says orr "landed-as="
  return { label := "a train's head killed after its fast-forward leaves each member landed by its \
write-ahead row, and each retires"
         , ok := ready && fired && (outs.headD (0, "")).1 != 0 && cr == 0 && says or_ "result=landed"
             && again && (← mainSubjects s.repo) == ["Base", "Add holder", "Add first", "Add rider"]
         , detail := s!"ready={ready} fired={fired} exits={outs.map (·.1)} again={again}" }

/-- A train whose run ended after its own landed row and before a rider's, its rider's row missing,
lands that rider by its write-ahead row: asked again it answers landed, and it retires. -/
def scenarioTrainPartialRows (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/partialrows" "holder"
  let remote ← addRemote s
  let names := ["first", "rider"]
  for n in names do addAgent s n
  let (ready, outs) ← runTrain self s names (← trainGate s "train")
  let ledger := s!"{s.repo}/.git/land/ledger.jsonl"
  let rows ← IO.FS.readFile ledger
  let kept := (rows.splitOn "\n").filter fun l =>
    !(says l "\"name\":\"rider\"" && says l "\"verdict\":\"landed\"")
  IO.FS.writeFile ledger (String.intercalate "\n" kept)
  let (cp, op) ← landIn self s.repo #["push"] "t=true"
  let published := (← revOf remote "refs/heads/main") == (← revOf s.repo "refs/heads/main")
  let (c1, o1) ← landIn self s.repo #["rider"] "t=true"
  let (c2, o2) ← landIn self s.repo #["retire", "rider"] "t=true"
  return { label := "a rider whose landed row its train never wrote is landed by the write-ahead \
row, the push publishes the train, and the rider retires"
         , ok := ready && outs.all (·.1 == 0) && kept.length < (rows.splitOn "\n").length
             && cp == 0 && says op "result=pushed" && published
             && c1 == 0 && says o1 "already=yes" && c2 == 0 && says o2 "landed-as="
         , detail := s!"ready={ready} exits={outs.map (·.1)} push={cp} published={published} \
again={c1} retire={c2}" }

/-- A landing killed right after its fast-forward, before its landed row, is landed by its
write-ahead row: asked again it answers landed, and it retires. -/
def scenarioKilledAfterFF (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/soloff" "solo"
  IO.FS.writeFile s!"{s.repo}/m.txt" "m\n"
  hgitOk #["add", "m.txt"] s.repo
  hgitOk #["commit", "-qm", "Main moves"] s.repo
  let wrap ← gitWrapper s "[ \"$1\" = push ] && [ \"$2\" = --porcelain ]" "  kill -KILL $PPID"
    (after := true)
  let (c0, _) ← landIn self s.repo #["solo"] "t=true" #[("PATH", some wrap)]
  let order ← mainSubjects s.repo
  let (c1, o1) ← landIn self s.repo #["solo"] "t=true"
  let (c2, o2) ← landIn self s.repo #["retire", "solo"] "t=true"
  return { label := "a landing killed after its fast-forward is landed by its write-ahead row, and \
retires"
         , ok := c0 != 0 && order == ["Base", "Main moves", "Add solo"] && c1 == 0
             && says o1 "already=yes" && c2 == 0 && says o2 "landed-as="
         , detail := s!"killed={c0} main={order} again={c1} retire={c2}" }

/-- Drive the driver against throwaway repositories under a fresh root in
`LAND_SCRATCH_DIR` (else `/tmp`), refusing with exit 2 when a repository encloses it;
`LAND_SCENARIO_BINARY` names another build to drive. -/
def scratchSelftest : IO UInt32 := do
  let self ← do
    match ← IO.getEnv "LAND_SCENARIO_BINARY" with
    | some b => pure b
    | none => pure (← IO.appPath).toString
  let nested := (← IO.getEnv "LAND_SCENARIO_NESTED").isSome
  let parent := (← IO.getEnv "LAND_SCRATCH_DIR").getD "/tmp"
  let root ← match ← guardRoot parent "land-scenarios" with
    | .ok root => pure root
    | .error (.unmade parent) =>
      say "scratch-root" "fail" [("parent", parent), ("why", "no fresh directory could be made")]
      sayFinal .refused [("why", s!"no fresh scratch root under {parent}")]
      return 2
    | .error (.enclosed root why) =>
      say "scratch-root" "fail" [("root", root), ("why", why)]
      sayFinal .refused [("why", why)]
      return 2
  say "scratch-root" "ok" [("root", root)]
  let (gv, _) ← hgit #["--version"] root
  if gv != 0 then
    rmQuiet root
    say "scenario" "skip" [("why", "git is not available")]
    sayFinal .checked [("scenarios", "0")]
    return 0
  let starting : List (String × (String → String → IO Outcome)) :=
    [("hookdir", scenarioHookGitDir), ("incheckout", scenarioRootInCheckout),
     ("narrative", scenarioNarrative)]
  let scenarios : List (String × (String → String → IO Outcome)) :=
    [ ("lands", scenarioLands), ("latin1", scenarioLatin1), ("moves", scenarioBranchMoves)
    , ("leaves", scenarioMainLeaves)
    , ("merge-kept", fun self root => scenarioMergedTip self root false)
    , ("merge-reconciled", fun self root => scenarioMergedTip self root true)
    , ("conflict", scenarioConflict), ("optin", scenarioNoOptIn), ("reserved", scenarioReserved)
    , ("usage", scenarioUsage)
    , ("stopped", scenarioStoppedRebase), ("switched", scenarioWorktreeSwitched)
    , ("treemoved", scenarioTreeMoved), ("pushtip", scenarioPushNamesTip)
    , ("pushff", scenarioPushNotFastForward), ("union", scenarioUnionDrift)
    , ("foreign", scenarioForeignGitDir), ("retain", scenarioRetention)
    , ("killed", scenarioKilled), ("fifo", scenarioQueueOrder), ("deadhead", scenarioQueueDeadHead)
    , ("repoll", scenarioQueueRepoll), ("prompt", scenarioQueuePrompt), ("ties", scenarioQueueTies)
    , ("turns", scenarioQueueTurns)
    , ("train3", scenarioTrainThree), ("trainconf", scenarioTrainConflict)
    , ("trainred", scenarioTrainRed), ("trainmoved", scenarioTrainMoved)
    , ("prequeue", scenarioTrainPreQueue), ("trainkill", scenarioTrainHeadKilled)
    , ("trainpush", scenarioTrainPushHeld), ("landeddirty", scenarioLandedDirty)
    , ("vanished", scenarioRiderVanished), ("untouched", scenarioTrainUntouched)
    , ("riderdirty", scenarioTrainRiderDirty), ("riderstopped", scenarioTrainRiderStopped)
    , ("killedrows", scenarioTrainKilledAfterRows), ("stoppedkilled", scenarioTrainStoppedKilled)
    , ("staleboarding", scenarioTrainStaleBoarding)
    , ("killedff", scenarioTrainKilledAfterFF), ("partialrows", scenarioTrainPartialRows)
    , ("soloff", scenarioKilledAfterFF), ("gatedirtied", scenarioTrainGateDirtied)
    , ("ownerbefore", fun self root => scenarioOwnerCommitsBeforeRebase self root false)
    , ("ownerbefore-rebase", fun self root => scenarioOwnerCommitsBeforeRebase self root true)
    , ("ownerafter", scenarioOwnerCommitsAfterRebase), ("switchff", scenarioMainSwitchedAtMerge)
    , ("decoy", scenarioLsRemoteDecoy), ("reland", scenarioRelandRefused)
    , ("putback", scenarioMainPutBack)
    , ("retireb", scenarioRetireRebased), ("pushlater", scenarioPushLater)
    , ("pushungated", scenarioPushUngated), ("guard", scenarioGuardRefuses)
    , ("nonet", scenarioNoNetwork) ] ++ (if nested then [] else starting)
  let mut outcomes : Array Outcome := #[]
  for (key, sc) in scenarios do
    -- A fixture that could not be built fails its scenario, named, and the rest still run.
    let o ← try sc self root
      catch ex => pure { label := key, ok := false, detail := toString ex }
    outcomes := outcomes.push o
  let mut bad := 0
  for o in outcomes do
    if o.ok then say "scenario" "ok" [("case", o.label)]
    else
      bad := bad + 1
      say "scenario" "fail" [("case", o.label), ("detail", o.detail)]
  rmQuiet root
  if bad == 0 then
    sayFinal .checked [("scenarios", toString outcomes.size)]
    return 0
  else
    sayFinal .failed [("scenarios", toString outcomes.size), ("bad", toString bad)]
    return 1

def usage : String :=
  "usage: land new <name> | land check <name> | land <name> [--push] | land push | \
land retire <name> | land status | land --selftest | land --scratch-selftest | land --help\n\
A land built before the landing queue ignores it, and can take the lock out of turn."

def resolveGates (e : Env) : IO (Except String (Array Gate × String)) := do
  let ctr ← IO.mkRef 0
  match ← IO.getEnv "LAND_GATES" with
  | none => return .ok (gateList, "default")
  | some spec =>
    if !(← overrideAllowed e ctr) then
      return .error "LAND_GATES is set, and this repository does not allow \
gate overrides (git config --local land.allowGateOverride true)"
    match parseGates spec with
    | .error err => return .error s!"LAND_GATES: {err.why}"
    | .ok gs => return .ok (gs, "override")

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .help => IO.println usage; return 0
  | .misuse why => IO.eprintln s!"land: {why}\n{usage}"; return 3
  | .selftest => selftest
  | .scratchSelftest => scratchSelftest
  | .run r => do
    match ← mkEnv with
    | .error e => IO.eprintln s!"land: {e}"; return 3
    | .ok env =>
      let landing (n : String) (m : Mode) (p : Bool) : IO UInt32 := do
        if m == .land && !p then
          if let some row ← alreadyLanded env n then
            let f (k : String) := (jsonField row k).getD ""
            say "pre" "ok" [("branch", s!"agent/{n}"), ("landed", f "tip"), ("run", f "run")]
            sayFinal .landed [("name", n), ("run", f "run"), ("tip", f "tip"),
              ("gated", f "gated"), ("already", "yes")]
            return 0
        match ← resolveGates env with
        | .error why =>
          say "gateset" "fail" [("why", why)]
          sayFinal .refused [("name", n), ("why", why)]
          return 2
        | .ok (gs, gateset) =>
          withTurn env n (if m == .land && !p then fareOf gs else "") fun rs => do
            -- A branch that landed while this run waited lands nothing, its riders queued again.
            if m == .land && !p then
              if let some row ← alreadyLanded env n then
                settleRiders env [] rs
                let f (k : String) := (jsonField row k).getD ""
                sayFinal .landed [("name", n), ("run", f "run"), ("tip", f "tip"),
                  ("gated", f "gated"), ("already", "yes")]
                return 0
            landRun env n m p gs gateset rs
      let retained (act : IO UInt32) : IO UInt32 := do
        retainRuns env 50
        act
      let code ← match r with
        | .status => do
          -- A listing is no run: it prunes nothing and leaves no directory.
          let c ← landStatus env
          rmQuiet env.runDir
          pure c
        | .new n => retained (landNew env n)
        | .retire n => retained (landRetire env n)
        | .push => retained (withTurn env "push" "" (fun _ => landPush env) (holds := false))
        | .land n m p => retained (landing n m p)
      env.alive.unlock
      return code
