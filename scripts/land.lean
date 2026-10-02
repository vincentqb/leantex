/-
`land` — the landing procedure, as a one-shot scriptable command.

  land new <name>          create and seed a worktree for agent/<name>
  land check <name>        preconditions and gates, no merge
  land <name> [--push]     land agent/<name> onto main
  land push                publish the last landing to the remote's main
  land retire <name>       remove a merged, clean worktree and its branch
  land status              porcelain listing of the agent worktrees
  land --selftest          drive the pure core over scripted observations
  land --scratch-selftest  drive the driver against throwaway repositories

Output is porcelain and nothing else: one `land: step=… result=…` line per
step, one `land: result=…` line at the end. A value carrying whitespace or a
quote is quoted, so a `k=v` reader cannot be walked off the end of a value.
Exit 0 ok, 1 gate failed, 2 precondition or conflict, 3 internal, 4 landed on
`main` but not known to be on the remote (`result=landed-unpushed`).
Composition is left to the caller — this tool never drives a terminal, never
prompts, and never loops.

The decisions live in `scripts/LandCore.lean`; this file is only the
boundary. Every command's output is written to
`$(git rev-parse --git-common-dir)/land/<run-id>/<step>.log` and every fact
the core acts on is *read back from a file* — never from a return value a
summarizer could have shortened. Standard output and standard error go to
separate files and only standard output is parsed: a git warning on stderr
once became part of a "fact" and reported a clean worktree as dirty.

The gates run in the run's own gate tree — a detached worktree,
`<run dir>/tree`, made at the branch's tip as the run read it, rebased there
onto `main` as the run read it, seeded with a copy of a `.lake`, and removed
when the run ends — never in the branch's worktree, whose owner may commit,
switch or edit while the landing runs. The landing never writes the branch
or its worktree: it reads them.
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
  /-- An exclusive lock on `<run dir>/alive`, held for the whole run: how
  retention tells a live run's directory from a dead one's. Unlocked at the
  very end of `main`, which is also what keeps the handle — and so the lock
  — alive until then. -/
  alive : IO.FS.Handle

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
  let n ← ctr.modifyGet (fun k => (k, k + 1))
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

/-- The variables that point git at a repository, an index, an object store,
a ref namespace or a config other than the ones a command's working
directory names. git's own list (`rev-parse --local-env-vars`, as of git
2.47) plus `GIT_NAMESPACE`, which moves every ref a command reads. The driver
asks git for the list as well, so a later git's addition is scrubbed too. -/
def repoVarsFixed : Array String := #[
  "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS",
  "GIT_CONFIG_COUNT", "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE",
  "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE", "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS",
  "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE", "GIT_COMMON_DIR",
  "GIT_NAMESPACE"]

/-- The name of every environment variable of this process that starts with
`GIT_`, read from `/proc/self/environ` (NUL-separated `name=value`); empty
where that file cannot be read. -/
def gitVarsInEnv : IO (Array String) := do
  let bytes ← try IO.FS.readBinFile "/proc/self/environ" catch _ => pure ByteArray.empty
  let mut out : Array String := #[]
  let mut name : String := ""
  let mut inName := true
  for b in bytes.toList do
    if b == 0 then
      if name.startsWith "GIT_" && !out.contains name then out := out.push name
      name := ""; inName := true
    else if inName then
      if b == 61 then inName := false  -- '='
      else name := name.push (Char.ofNat b.toNat)
  if name.startsWith "GIT_" && !out.contains name then out := out.push name
  return out

def childEnvVars : IO (Array (String × Option String)) := do
  let cc ← IO.getEnv "LEAN_CC"
  let lp ← IO.getEnv "LIBRARY_PATH"
  -- Never inherited: a variable naming another repository. git exports
  -- `GIT_DIR` and `GIT_INDEX_FILE` to a hook in every linked worktree, so a
  -- landing started from a hook would otherwise probe, rebase and gate the
  -- hook's repository — and a gate running `git` in the gate tree would read
  -- the hook's index. The repository is the one the working directory names.
  let scrub0 : Array (String × Option String) := repoVarsFixed.map (·, none)
  let r ← try
      IO.Process.output
        { cmd := "git", args := #["rev-parse", "--local-env-vars"], env := scrub0,
          stdin := .null }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let asked := if r.exitCode == 0 then (wsSplit r.stdout).toArray else #[]
  let names := asked.foldl (init := repoVarsFixed) fun acc n =>
    if acc.contains n then acc else acc.push n
  -- Never inherited either: a child that can prompt can hang a scripted
  -- landing.
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
        { cmd := "date", args := #["-u", "+%Y%m%dT%H%M%S%N %Y-%m-%dT%H:%M:%SZ"] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let stamps := wsSplit (if d.exitCode == 0 then d.stdout else "run -")
  -- Nanoseconds after the seconds, fixed width, so run ids sort by time
  -- within a second too; the pid, so two runs in one nanosecond still differ.
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

/-- Is the run that owns this directory still running? It holds the lock on
`alive` for its whole life, and the kernel drops that lock when the process
ends, however it ends. A directory without the file is an older run's. A
lock that cannot be tried is answered "live": keeping a dead run's logs a
while longer costs disk, deleting a live run's cost a landing. -/
def runLive (d : System.FilePath) : IO Bool := do
  if !(← (d / "alive").pathExists) then return false
  try
    let h ← IO.FS.Handle.mk (d / "alive") .read
    let got ← h.tryLock
    if got then h.unlock
    return !got
  catch _ => return true

/-- Keep the newest run directories and drop the rest — never a live run's,
and never this run's own. Eleven directories and 58 KB of gate logs
accumulated in one scratch session with nothing removing them; run ids are
timestamp-prefixed, so newest is last by name. Fifty-five `status` calls
during one landing once deleted that landing's directory, and the landing
died on its next log write. A dead run's gate tree is unregistered first,
so the directory's removal leaves git no stale worktree. -/
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

/-- A gate list: `name=cmd arg arg;name=cmd …`, run in order in the gate
tree. One syntax and one parser for the shipped list and for a `LAND_GATES`
override. Parsing is strict: an entry without `=` and a repeated name are
refusals, because a dropped entry once ran one gate under a report of two
and a repeated name ran the first gate twice while the second never ran at
all. -/
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

/-- The gates every landing runs, in order, one per line, in the gate-list
syntax: a new gate is one line here. An argument spelled `{main}` becomes
the sha of `main` the run read. None may be absent: the scoreboard is on
every base a branch can now be rebased onto, and a skip that read the
lakefile for its name was a substring test a valid lakefile defeated.

`--wfail` is how this project spells "zero warnings": scanning output for
`warning:` is unsound, because a warm cache replays a module's logged warning
without recompiling it and a scan of a quiet build proves nothing about the
module that did not rebuild. The flag is written out per gate rather than
inherited from another gate's internals: `land`'s own theorem and the gate
scripts are built under it, and `Obligations` — the staging area for open
proofs, which warns once per staged statement by design — is a separate build
without it, as the pre-commit hook already does. -/
def defaultGates : List String := [
  "build=lake build --wfail leantex precommit owed cites land",
  "obligations-build=lake build Obligations",
  "test=lake test",
  "land-selftest=.lake/build/bin/land --selftest",
  "land-scenarios=.lake/build/bin/land --scratch-selftest",
  "precommit-selftest=.lake/build/bin/precommit --selftest",
  "precommit-tree=.lake/build/bin/precommit --tree",
  "cites-selftest=.lake/build/bin/cites --selftest",
  "cites-check=.lake/build/bin/cites --check",
  "owed=lake env lean --run scripts/owed.lean",
  "scoreboard-build=lake build --wfail scoreboard",
  "scoreboard-check=.lake/build/bin/scoreboard --check",
  "scoreboard-base=.lake/build/bin/scoreboard --check --base {main}",
  "scoreboard-selftest=.lake/build/bin/scoreboard --selftest"]

/-- The shipped list, parsed. A list that does not parse is empty, and an
empty plan proves nothing, so no landing gets past it; the selftest names
the fault. -/
def gateList : Array Gate :=
  match parseGates (String.intercalate ";" defaultGates) with
  | .ok gs => gs
  | .error _ => #[]

/-- The plan the core is driven against: the gates' names, in order, none
permitted to be absent. -/
def planOf (gs : Array Gate) : Array GateSpec :=
  gs.map fun g => { name := g.name, mayAbsent := false }

/-- Is the gate override permitted here? Only in a repository that opted in
with `git config --local land.allowGateOverride true`. An exported variable
is inherited by every later command in a shell, so an override that any
repository honoured was one stray `export` away from weakening every landing
on the machine. -/
def overrideAllowed (e : Env) (ctr : IO.Ref Nat) : IO Bool := do
  let r ← git e ctr "gateset" #["config", "--local", "--get", "land.allowGateOverride"]
  return r.code == 0 && trimWs r.out == "true"

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

/-- The last ledger line whose `verdict` is `v` — for one agent, or for any
agent when `name` is `none` — read back from the file. -/
def lastVerdict (e : Env) (v : String) (name : Option String) : IO (Option String) := do
  try
    let txt ← IO.FS.readFile (ledgerPath e)
    let hits := (txt.splitOn "\n").filter fun l =>
      jsonField l "verdict" == some v
        && match name with
          | none => true
          | some n => (l.splitOn s!"\"name\":{jsonStr n}").length > 1
    return hits.getLast?
  catch _ => return none

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

/-- The tip an earlier landing of `name` read and the commit it landed as,
when that landing rebased the branch — so the two differ — and the branch
still carries that tip; two empty strings otherwise. With them, whether
`mainTip`, `main` as this run read it, holds the landed commit: the core
counts the row only then (`landedBars`), so a landing undone by putting
`main` back bars nothing, as `landedTipOf` already required of a retire.
From the ledger's last `landed` row for the name, and the ancestry from git;
`none` when git could not say whether `mainTip` holds the commit. A row
written before rows carried `branch` answers empty. -/
def landedFromRow (e : Env) (ctr : IO.Ref Nat) (name tip mainTip : String) :
    IO (Option (String × String × Bool)) := do
  match ← lastVerdict e "landed" (some name) with
  | none => return some ("", "", false)
  | some row =>
    let b := (jsonField row "branch").getD ""
    let g := (jsonField row "gated").getD ""
    if !isSha b || !isSha g || b == g then return some ("", "", false)
    let r ← git e ctr "pre-branch" #["merge-base", "--is-ancestor", b, tip] (some e.mainWt)
    if r.code != 0 then return some ("", "", false)
    -- A commit this repository no longer has is on no `main`: the landing
    -- was undone long enough ago for git to prune it.
    let v ← git e ctr "pre-branch" #["cat-file", "-e", g ++ "^{commit}"] (some e.mainWt)
    if v.code != 0 then return some (b, g, false)
    let m ← git e ctr "pre-branch" #["merge-base", "--is-ancestor", g, mainTip] (some e.mainWt)
    return (if m.code == 0 then some (b, g, true)
      else if m.code == 1 then some (b, g, false) else none)

/-- The commit the last `landed` row for `name` landed as, when that row
read exactly `tip` and the commit it landed is on `main`; empty otherwise.
A landing onto a `main` that had moved lands rebased copies and leaves the
branch where it was, so this — not ancestry — is what "merged" means for
such a branch. -/
def landedTipOf (e : Env) (ctr : IO.Ref Nat) (name tip : String) : IO String := do
  match ← lastVerdict e "landed" (some name) with
  | none => return ""
  | some row =>
    let b := (jsonField row "branch").getD ""
    let g := (jsonField row "tip").getD ""
    if b != tip || !isSha g then return ""
    let r ← git e ctr "pre" #["merge-base", "--is-ancestor", g, "main"] (some e.mainWt)
    return (if r.code == 0 then g else "")

-- ## The gate tree

/-- The gate tree: a detached worktree this run makes at the gated tip, in
its own run directory, which nothing else writes. -/
def treePath (e : Env) : String := s!"{e.runDir}/tree"

/-- The gate tree, read back: its `HEAD`, and whether it is clean. A
directory that is not a work tree reads as no sha: inside the git directory
— where the run directory lives — `rev-parse HEAD` walks up and answers with
the *main* worktree's `HEAD`, which is a sha, only not this tree's. -/
def readTree (e : Env) (ctr : IO.Ref Nat) (step : String) : IO (Sha × Bool) := do
  let tree := treePath e
  let inside ← git e ctr step #["rev-parse", "--is-inside-work-tree"] (some tree)
  if inside.code != 0 || trimWs inside.out != "true" then return ("", false)
  let head ← revParse e ctr step "HEAD" (some tree)
  let clean ← statusClean e ctr step tree
  return (head, clean == some true)

/-- Make the gate tree at `tip` and seed its build cache: a copy of the
branch worktree's `.lake`, else the main worktree's. A copy, never a
hardlink — lake rewrites files in place. A failed copy is removed rather
than built on. -/
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

/-- Remove the gate tree, and read back that it is gone from the disk and
from the worktree list. Forced, because a tree a gate dirtied must go too:
it is this run's, and nothing else writes it. -/
def removeTree (e : Env) (ctr : IO.Ref Nat) : IO Unit := do
  let tree := treePath e
  let _ ← git e ctr "tree-remove" #["worktree", "remove", "--force", tree] (some e.mainWt)
  let gone := !(← System.FilePath.pathExists tree)
  let wl ← git e ctr "tree-remove" #["worktree", "list", "--porcelain"] (some e.mainWt)
  let listed := (wl.out.splitOn "\n").any (trimWs · == s!"worktree {tree}")
  say "tree-remove" (if gone && !listed then "ok" else "fail")
    [("path", tree), ("gone", if gone then "yes" else "no"),
     ("listed", if listed then "yes" else "no")]

/-- Run one gate in the gate tree, reading the tree back before and after
it. An argument spelled `{main}` becomes `mainTip`, the sha of `main` this
run read. -/
def runGate (e : Env) (ctr : IO.Ref Nat) (g : Gate) (idx : Nat) (mainTip : Sha) : IO Obs := do
  let tree := treePath e
  let step := s!"gate-{g.name}"
  let (hb, cb) ← readTree e ctr step
  let cmd := if g.cmd.startsWith "." then s!"{tree}/{g.cmd}" else g.cmd
  let args := g.args.map fun a => if a == "{main}" then mainTip else a
  let r ← sh e ctr step cmd args (some tree)
  let (ha, ca) ← readTree e ctr step
  -- The tree as read around the gate: the head both reads agree on, and
  -- clean only if both were, so a tree moved between two gates and moved
  -- back inside the next one still reads as moved.
  let head := if hb == ha then ha else ""
  let clean := cb && ca
  if r.code != 0 then return .gateFail idx head clean
  return .gateOk idx head clean

-- ## The landing run

/-- The landing loop: feed the core one observation per action until it
halts. `treeLive` is set once the gate tree was asked for and cleared once
it is removed, so the caller's `finally` removes a tree an exception left. -/
def landLoop (e : Env) (ctr : IO.Ref Nat) (treeLive : IO.Ref Bool) (name : String)
    (mode : Mode) (wantPush : Bool) (gates : Array Gate) (gateset : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let plan : Array GateSpec := planOf gates
  let mut st := State.init name mode plan wantPush
  let mut act : Act := .probeMain
  let mut wt : String := ""
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
                  let row ← if isSha tip then landedFromRow e ctr name tip st.prevMainTip
                    else pure (some ("", "", false))
                  match row with
                  | none => pure (.garbled "git merge-base --is-ancestor for the landed commit")
                  | some (landedFrom, landedAs, onMain) => do
                    let barred := landedBars landedFrom onMain
                    say "pre-branch" (if ahead > 0 && clean && !barred then "ok" else "fail")
                      ([("worktree", p), ("ahead", toString ahead),
                       ("behind", toString behind),
                       ("dirty", if clean then "no" else "yes"),
                       ("tip", if tip.isEmpty then "?" else tip)]
                       ++ (if landedFrom.isEmpty then []
                           else [("landed-from", landedFrom), ("landed-as", landedAs),
                             ("landed-on-main", if onMain then "yes" else "no")]))
                    pure (.branchStatus ahead behind clean tip landedFrom landedAs onMain)
              | _, _ => pure (.garbled "rev-list counts are not numbers")
            | other => pure (.garbled s!"rev-list counts: {other.length} fields")
      | .rebase tip onto => do
        -- A tip that already contains the base is the reviewed result,
        -- including its merge resolutions. Rebase would flatten those
        -- merges and could restore deliberately discarded side changes.
        -- Otherwise replay only the captured sha, never a moving branch.
        -- `--no-update-refs` keeps every owner's branch outside this write.
        let tree := treePath e
        let contains ← git e ctr "rebase-base" #["merge-base", "--is-ancestor", onto, tip]
          (some tree)
        -- premise: scenarioMergedTip — both retained and discarded side
        -- changes keep the reviewed tip, tree and ancestry on the remote.
        let r ← if contains.code == 0 then
            git e ctr "rebase" #["checkout", "--detach", tip] (some tree)
          else if contains.code == 1 then
            git e ctr "rebase"
              #["rebase", "--no-update-refs", "--no-autosquash", "--no-autostash", onto, tip]
              (some tree)
          else pure contains
        if r.code == 0 then
          let head ← revParse e ctr "rebase" "HEAD" (some tree)
          let clean? ← statusClean e ctr "rebase" tree
          let onRef ← git e ctr "rebase" #["symbolic-ref", "--quiet", "HEAD"] (some tree)
          let detached := onRef.code != 0
          let ok := clean? == some true && detached && (contains.code != 0 || head == tip)
          say "rebase" (if ok && isSha head then "ok" else "fail")
            [("from", tip), ("onto", onto), ("tip", if head.isEmpty then "?" else head),
             ("dirty", if clean? == some true then "no" else "yes"),
             ("detached", if detached then "yes" else "no"),
             ("mode", if contains.code == 0 then "preserve" else "replay")]
          pure (.rebaseOk head ok)
        else
          -- Any non-zero rebase: the unmerged paths, for the refusal, and an
          -- abort so the tree's removal starts from a tree git knows. The
          -- tree is this run's; the owner's branch and worktree were never
          -- touched, so there is nothing of theirs to read back or put back.
          let ru ← git e ctr "rebase" #["diff", "--name-only", "--diff-filter=U"] (some tree)
          let files := (ru.out.splitOn "\n").map trimWs |>.filter (!·.isEmpty)
          if ← midRebase e ctr "rebase-abort" tree then
            let _ ← git e ctr "rebase-abort" #["rebase", "--abort"] (some tree)
            pure ()
          say "rebase" "fail"
            [("from", tip), ("onto", onto),
             ("conflict", if files.isEmpty then "none" else String.intercalate "," files)]
          pure (.rebaseFailed files.toArray)
      | .netDiff oldTip newBase newTip => do
        -- The branch's own change runs from its fork point with the base it
        -- was replayed onto; plumbing, so no `color.diff`, external diff or
        -- textconv of this host's configuration reaches the listing.
        let rf ← git e ctr "net" #["merge-base", newBase, oldTip] (some e.mainWt)
        let fork := trimWs rf.out
        if rf.code != 0 || !isSha fork then
          pure (.garbled "git merge-base for the net comparison")
        else
          let listing (a b : String) : Array String :=
            #["diff-tree", "-r", "-p", "--no-color", "--no-ext-diff", "--no-textconv",
              "--no-renames", "--binary", "-U0", a, b]
          let rb ← git e ctr "net" (listing fork oldTip) (some e.mainWt)
          let ra ← git e ctr "net" (listing newBase newTip) (some e.mainWt)
          if rb.code != 0 || ra.code != 0 then
            pure (.garbled "git diff-tree for the net comparison")
          else
            let drift := netDrift (netOf rb.out) (netOf ra.out)
            say "net" (if drift.isEmpty then "ok" else "fail")
              ([("fork", fork), ("base", newBase), ("files", toString (netOf rb.out).size)]
                ++ (if drift.isEmpty then [] else [("drift", String.intercalate "," drift.toList)]))
            pure (.netDiffs rb.out ra.out)
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
          let o ← runGate e ctr gd i st.prevMainTip
          let tail (head : Sha) (clean : Bool) : List (String × String) :=
            [("idx", toString i), ("head", if head.isEmpty then "?" else head),
             ("dirty", if clean then "no" else "yes")]
          match o with
          | .gateOk _ head clean =>
            -- The line says what the core will judge: a gate whose command
            -- passed but whose tree moved or was dirtied is a failed gate.
            let held := head == st.gatedTip && clean
            say s!"gate-{g}" (if held then "ok" else "fail")
              (tail head clean ++ (if held then [] else [("why", "the gate tree moved or was dirtied")]))
            pure o
          | .gateFail _ head clean =>
            say s!"gate-{g}" "fail" (tail head clean ++ [("log", s!"gate-{g}.log")]); pure o
          | _ => pure o
      | .recheckBranch => do
        -- The owner's branch as it reads now. This run never wrote it, so a
        -- move is the owner's, and the branch is left as they left it.
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
        let ok ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "landing"),
           ("gated", st.gatedTip), ("prev", st.prevMainTip), ("branch", st.branchTip),
           ("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        say "announce" (if ok then "ok" else "fail") [("gated", st.gatedTip)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .fastForward tip => do
        -- `refs/heads/main`, by that name, to exactly this commit, as a push
        -- into this repository: git's receiving side moves only the ref it is
        -- named, accepts nothing but a fast-forward, and with `updateInstead`
        -- brings along the worktree that has `main` checked out — refusing,
        -- with nothing moved, when that worktree has changes. `merge
        -- --ff-only` moved whatever ref the main worktree's `HEAD` named, so a
        -- switch just before it fast-forwarded another branch to the gated
        -- tip.
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
        let ok ← writeLedger e
          [("ts", e.ts), ("run", e.runId), ("name", name),
           ("verdict", "landed"), ("tip", st.mainAt), ("gated", st.gatedTip),
           ("prev", st.prevMainTip), ("branch", st.branchTip),
           ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
           ("skipped", String.intercalate "," st.skipped.toList),
           ("pushed", if wantPush then "pending" else "no"),
           ("gateset", gateset), ("ms", toString (t1 - t0)), ("dir", e.runDir)]
        say "ledger" (if ok then "ok" else "fail") [("file", ledgerPath e)]
        pure (if ok then .ledgerOk else .ledgerFail)
      | .push tip => do
        -- The gated tip, by sha, to the remote's `main`: never the local
        -- `main`, which another party may have moved since it was read back.
        -- No force of any kind, so a remote that moved on rejects it.
        let r ← git e ctr "push" #["push", "origin", s!"{tip}:refs/heads/main"] (some e.mainWt)
        if r.code == 0 then say "push" "ok" [("tip", tip)]; pure .pushOk
        else say "push" "fail" [("tip", tip), ("log", "push.log")]; pure .pushRejected
      | .readRemote => do
        -- `git ls-remote`, not the tracking ref: git updates `origin/main`
        -- from its own push result, so comparing against it asks the push
        -- whether the push worked. The line whose refname is exactly
        -- `refs/heads/main`: the pattern also matches any ref ending in it.
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
          ("branch", st.branchTip),
          ("gates", String.intercalate "," (st.gates.toList.map (·.name))),
          ("skipped", String.intercalate "," st.skipped.toList)] ++ tail)
        if !ok then say "ledger" "fail" [("row", "checked")]
      if v == .refused || v == .failed || v == .landedUnpushed then
        let ok ← writeLedger e (base ++ [("verdict", v.name), ("why", why),
          ("gated", st.gatedTip), ("branch", st.branchTip)] ++ tail)
        if !ok then say "ledger" "fail" [("row", v.name)]
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

/-- One landing run. The gate tree is removed on every path out: at the
halt, before the final line, and here after an exception. -/
def landRun (e : Env) (name : String) (mode : Mode) (wantPush : Bool)
    (gates : Array Gate) (gateset : String) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  let treeLive ← IO.mkRef false
  try landLoop e ctr treeLive name mode wantPush gates gateset
  finally
    if ← treeLive.get then removeTree e ctr

/-- The landing lock, and the record of who holds it. -/
def lockPath (e : Env) : String := s!"{e.common}/land/landing.lock"
def ownerPath (e : Env) : String := s!"{e.common}/land/landing.owner"

/-- A `key=value` field of an owner record; empty when absent. -/
def recField (rec key : String) : String :=
  match (wsSplit rec).find? (·.startsWith s!"{key}=") with
  | some w => (w.drop (key.length + 1)).toString
  | none => ""

/-- One landing at a time. The lock is `flock` on a file, which the kernel
releases when the holder ends however it ends: the directory it replaced
outlived a landing stopped by `timeout`, and refused every landing after it
with nothing to say whether its owner lived. The owner record beside it
names the holding run and its pid. A record found by a run that *got* the
lock was left by a run that died holding it: that run is recorded as
`abandoned`, and its gate tree removed. -/
def withLock (e : Env) (name : String) (act : IO UInt32) : IO UInt32 := do
  let ctr ← IO.mkRef 0
  IO.FS.createDirAll s!"{e.common}/land"
  let h? ← try some <$> IO.FS.Handle.mk (lockPath e) .append catch _ => pure none
  let some h := h?
    | say "lock" "fail" [("path", lockPath e), ("why", "the lock file cannot be opened")]
      sayFinal .failed [("name", name), ("why", "the lock file cannot be opened")]
      return 3
  let got ← try h.tryLock catch _ => pure false
  let prev := trimWs (← try IO.FS.readFile (ownerPath e) catch _ => pure "")
  if !got then
    say "lock" "fail" [("path", lockPath e), ("owner", prev)]
    sayFinal .refused [("name", name), ("why", s!"another landing holds the lock ({prev}); \
it is running: wait for it to end, or stop that process")]
    return 2
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
      let tip ← revParse e ctr "pre" s!"refs/heads/agent/{name}" (some e.mainWt)
      if !isSha tip then
        say "pre" "fail" [("why", "the branch tip did not read back as a sha")]
        sayFinal .failed [("name", name)]
        return 3
      let rm ← git e ctr "pre"
        #["merge-base", "--is-ancestor", tip, "main"] (some e.mainWt)
      -- A landing onto a `main` that had moved lands rebased copies and never
      -- writes the branch, so ancestry alone would call every such branch
      -- unmerged; the ledger says what it landed as.
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
      -- Deleted by compare-and-swap against the tip read above: a branch that
      -- moved since is someone's work, and `update-ref` refuses to delete it.
      let rd ← git e ctr "branch-delete"
        #["update-ref", "-d", s!"refs/heads/agent/{name}", tip] (some e.mainWt)
      if rd.code != 0 then
        say "branch-delete" "fail" [("log", "branch-delete.log")]
        sayFinal .failed [("name", name)]
        return 3
      say "branch-delete" "ok" [("branch", s!"agent/{name}"), ("was", tip)]
      let _ ← writeLedger e
        [("ts", e.ts), ("run", e.runId), ("name", name), ("verdict", "retired"),
         ("branch", tip), ("dir", e.runDir)]
      sayFinal .retired [("name", name)]
      return 0

-- ## land push

/-- Publish the last landing: the way to push a landing made without
`--push`, which a second `land <name> --push` cannot do — the branch is no
longer ahead. `main` must read at the last `landed` row's tip, which is also
its gated tip, so a commit on `main` that no landing gated is refused rather
than published; the push names that sha, never `main`, and is never forced;
and the remote is read back by its exact refname. A remote already at the
tip is reported, and nothing is written. -/
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

def gatePlan : Array GateSpec := planOf gateList

def sha1s : Sha := "1111111111111111111111111111111111111111"
def sha2s : Sha := "2222222222222222222222222222222222222222"
def sha3s : Sha := "3333333333333333333333333333333333333333"
def sha4s : Sha := "4444444444444444444444444444444444444444"

def okGates : List Obs := (List.range gatePlan.size).map fun i => Obs.gateOk i sha3s true

/-- One file's change, as `git diff-tree -p -U0` prints it: the same change
at two positions differs only in its `index` line and hunk headers, which
is the comparison's whole allowance. -/
def netListing (idx hunk : String) (body : List String) : String :=
  s!"diff --git a/PLAN.md b/PLAN.md\nindex {idx} 100644\n--- a/PLAN.md\n+++ b/PLAN.md\n{hunk}\n"
    ++ String.join (body.map (· ++ "\n"))

/-- The branch's change: a new entry under a heading its second commit
renamed. -/
def netBranch : String :=
  netListing "1a2b3c4..5d6e7f8" "@@ -4,0 +5,3 @@ body a" ["+", "+### b-final", "+body b"]

/-- The same change replayed onto a base that appended an entry first. -/
def netMoved : String :=
  netListing "9f8e7d6..c5b4a39" "@@ -7,0 +8,3 @@ body m" ["+", "+### b-final", "+body b"]

/-- The union driver's keep-both: the draft heading the branch renamed away
came back, and git reported no conflict. -/
def netUnion : String :=
  netListing "9f8e7d6..d4c3b2a" "@@ -7,0 +8,4 @@ body m"
    ["+### b-draft", "+", "+### b-final", "+body b"]

def netSame : Obs := .netDiffs netBranch netMoved

/-- A plan every one of whose gates may be absent: the vacuity case. -/
def allSkippablePlan : Array GateSpec :=
  #[{ name := "a", mayAbsent := true }, { name := "b", mayAbsent := true }]

/-- A plan whose second gate may be absent: the core's permission, which
the shipped list no longer grants, still holds exactly where a plan does. -/
def oneSkippablePlan : Array GateSpec :=
  #[{ name := "a", mayAbsent := false }, { name := "b", mayAbsent := true }]

def cases : List Case :=
  let bs (ahead behind : Nat) : Obs := .branchStatus ahead behind true sha2s "" "" false
  let pre := [Obs.mainStatus true true sha1s, bs 1 0, Obs.treeReady sha2s true,
    Obs.rebaseOk sha3s true, netSame]
  let landOk := pre ++ okGates ++ [.branchRecheck sha2s, .mainRecheck true sha1s,
    .ledgerOk, .ffOk, .mainTip sha3s, .ledgerOk]
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

/-- The push a scripted run proposed, if any: its sha, as `ffTipOf`. -/
def pushTipOf (acts : Array Act) : Option Sha :=
  acts.foldl (init := none) fun acc a =>
    match a with
    | .push t => some t
    | _ => acc

/-- The net comparison over hand-written listings: the change it must see
through, and the changes it must not. Each pair is (before, after, the
files the drift must name). -/
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
  -- The write statement, exercised over every case's trace: each write owned
  -- in the state it was proposed from, both shared writes reached, and no
  -- case proposing a write to a branch or a worktree the run does not own.
  let traces := cases.map fun c =>
    (c, Land.trace (State.init "probe" c.mode (c.plan.getD gatePlan) c.push) c.obs)
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
  else if reaches fun w => match w with | .branchCas .. => true | .foreign => true | _ => false then
    bad := bad + 1
    say "selftest" "fail" [("case", "every write owned"),
      ("why", "a case writes a branch or a worktree the run does not own")]
  else say "selftest" "ok" [("case", "every write owned, and none to the owner's branch")]
  -- The landed refusal sends the next unit to a new branch from `main` and
  -- names no command that writes this one: the rebase it named before
  -- dropped the landed work from a branch whose `main` had been put back.
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
  -- The remote read-back reads exactly `refs/heads/main`: a query pattern
  -- also matches a ref ending in it, which sorts first.
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
  -- The shipped list is read by that parser: every line must come back as
  -- one gate, in order, or the landing would run a list nobody wrote.
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
  -- Porcelain quoting: a value with a space must come back as one value.
  if pv "a b" != "\"a b\"" || pv "ab" != "ab" || pv "" != "\"\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "porcelain quoting"), ("why", "wrong form")]
  else say "selftest" "ok" [("case", "porcelain quoting")]
  if jsonStr "a\u0001b" != "\"a\\u0001b\"" then
    bad := bad + 1
    say "selftest" "fail" [("case", "ledger escaping"), ("why", "a control byte survived")]
  else say "selftest" "ok" [("case", "ledger escaping")]
  -- The scenario harness's guard, over the argv shapes the harness runs and
  -- the ones it must refuse. `hcall_writes_owned` says an allowed command
  -- writes only what the run owns; these say the classifier and the path
  -- comparison answer what that statement reads.
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
-- one, and this harness structurally cannot be: every git command it runs,
-- and every run of the tool under test, passes the guard in
-- `scripts/LandCore.lean` first (`hcall_writes_owned`).

/-- The environment every harness child gets: each `GIT_` variable this
process inherited removed, git's global and system configuration out of
reach, and no transport but a local path. git exports `GIT_DIR` and
`GIT_INDEX_FILE` to a hook in every linked worktree, so a harness started
from one once committed its fixtures into the repository `GIT_DIR` named,
rewrote its config and pushed its `main` to its origin; a host's
`commit.gpgsign` or `core.hooksPath` would change what a scenario tests; and
every repository a scenario makes is a local path, while a real remote never
is — so `GIT_ALLOW_PROTOCOL=file` leaves git itself refusing `https`, `ssh`
and `git://` to this process's every descendant, the tool under test and its
gates included. -/
-- premise: scenarioNoNetwork — the variable reaches a gate the tool under test
-- runs, and git refuses the transport before it connects.
def harnessEnv : IO (Array (String × Option String)) := do
  let set : Array (String × Option String) := #[("GIT_CONFIG_GLOBAL", some "/dev/null"),
    ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_TERMINAL_PROMPT", some "0"),
    ("GIT_ALLOW_PROTOCOL", some "file")]
  let inherited ← gitVarsInEnv
  let names := repoVarsFixed.foldl (init := inherited) fun acc n =>
    if acc.contains n then acc else acc.push n
  let unset := (names.filter fun n => !(set.any (·.1 == n))).map (·, none)
  return unset.append set

/-- The guard every command of the harness is checked against: installed once
the run's scratch root is made, canonical, and inside no checkout. Until then,
and in any process that is not a harness run, `hgit` and `runTool` refuse
everything. -/
initialize harnessGuard : IO.Ref (Option HGuard) ← IO.mkRef none

/-- The exit status of a command the guard refused: it never ran. -/
def refusedCode : Nat := 126

/-- Spawn a command in the harness's environment, standard input closed; its
exit code, and its standard output and error joined. Git reaches it only
through `hgit`, and the tool under test only through `runTool`. -/
private def hspawn (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) := do
  let env ← harnessEnv
  let r ← try
      IO.Process.output
        { cmd, args, cwd := cwd.map System.FilePath.mk, env := env.append extraEnv,
          stdin := .null }
    catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }
  return (r.exitCode.toNat, trimWs (r.stdout ++ r.stderr))

/-- Run a command for the harness that is not git and not the tool under
test. Not `sh`: there is no run directory yet, and the harness asserts on
exit codes rather than on parsed facts. -/
def hrun (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) := do
  if cmd == "git" then
    return (refusedCode, "land-harness: refused: git runs only through the guard (hgit)")
  hspawn cmd args cwd extraEnv

/-- What `git rev-parse --absolute-git-dir` names from `cwd` in the harness's
environment extended by `extraEnv`: the repository a command run there, so,
would read and write. Standard output only; empty when git names none. -/
-- premise: scenarioHookGitDir — the repository named here is the one the
-- command then writes: the same binary, environment and directory.
def gitDirOf (cwd : String) (extraEnv : Array (String × Option String) := #[]) : IO String := do
  let env ← harnessEnv
  let r ← try
      IO.Process.output
        { cmd := "git", args := #["rev-parse", "--absolute-git-dir"],
          cwd := some cwd, env := env.append extraEnv, stdin := .null }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  return if r.exitCode == 0 then trimWs r.stdout else ""

/-- Run git for the harness, after the guard: the argv classified from its
directory and what git names there, and run only when every write it may make
is the run's. A refused command never runs; it answers `refusedCode` and why.
A bare repository `init --bare` made becomes one the run may push to. -/
-- The statement is `hcall_writes_owned` in scripts/LandCore.lean.
-- premise: scenarioGuardRefuses — a command from outside the root, a push by a
-- remote's name, a push to a repository the run did not make, a global option
-- and a fetch are each refused, and none of them wrote anything.
def hgit (args : Array String) (cwd : String) : IO (Nat × String) := do
  let some g ← harnessGuard.get
    | return (refusedCode, "land-harness: refused: no scratch root is guarded")
  let gitDir ← if within g.root cwd then gitDirOf cwd else pure ""
  let c := classify cwd gitDir args
  if !c.allowed g then
    return (refusedCode, s!"land-harness: refused git {String.intercalate " " args.toList} \
from {cwd}: {c.refusal g}")
  let r ← hspawn "git" args (some cwd)
  if r.1 == 0 then
    if let some b := bareCreated cwd args then
      harnessGuard.modify (·.map fun g => { g with made := g.made ++ [b] })
  return r

/-- The URLs a push from the repository `cwd` names could reach: every
remote's `url` and `pushurl`, read from `cwd` in the given environment. A
`url.*.insteadOf` or `pushInsteadOf` rewrites a URL at push time, so any
such key answers with a URL no run owns. -/
def remoteUrlsOf (cwd : String) (extraEnv : Array (String × Option String)) :
    IO (List String) := do
  let env ← harnessEnv
  let cfg (re : String) : IO (Nat × String) := do
    let r ← try
        IO.Process.output
          { cmd := "git", args := #["config", "--get-regexp", re], cwd := some cwd,
            env := env.append extraEnv, stdin := .null }
      catch _ => pure { exitCode := 2, stdout := "", stderr := "" }
    return (r.exitCode.toNat, r.stdout)
  let (ci, _) ← cfg "^url\\."
  let (cr, out) ← cfg "^remote\\..*\\.(push)?url$"
  let urls := (out.splitOn "\n").filterMap fun l =>
    match wsSplit l with
    | [_, u] => some (fromDir cwd u)
    | [] => none
    | _ => some "(a remote URL that does not read as one word)"
  return (if ci != 1 then ["(a url.*.insteadOf rewrite, or a config git could not read)"] else [])
    ++ (if cr == 0 || cr == 1 then urls else ["(a config git could not read)"])

/-- Run the tool under test from `cwd`, after the guard: its repository — as
git names it in the environment the tool will get — inside the root, every
remote that repository names a bare repository the run made, and a
`LAND_SCRATCH_DIR` it is handed inside the root. -/
def runTool (self cwd : String) (args : Array String)
    (extraEnv : Array (String × Option String)) : IO (Nat × String) := do
  let some g ← harnessGuard.get
    | return (refusedCode, "land-harness: refused: no scratch root is guarded")
  let gitDir ← if within g.root cwd then gitDirOf cwd extraEnv else pure ""
  let remotes ← if within g.root gitDir then remoteUrlsOf cwd extraEnv else pure []
  let c := HCall.drive cwd gitDir remotes
  let scratch := extraEnv.find? (·.1 == "LAND_SCRATCH_DIR") |>.bind (·.2)
  if !(scratch.all (within g.root)) then
    return (refusedCode, s!"land-harness: refused {self} from {cwd}: its scratch directory \
{scratch.getD ""} is outside the scratch root {g.root}")
  if !c.allowed g then
    return (refusedCode, s!"land-harness: refused {self} from {cwd}: {c.refusal g}")
  hspawn self args (some cwd) extraEnv

/-- A fixture step that must succeed: a scenario built on a failed setup
command would assert about a repository it never made. -/
def hgitOk (args : Array String) (cwd : String) : IO Unit := do
  let (c, o) ← hgit args cwd
  if c != 0 then
    throw (IO.userError s!"fixture: git {String.intercalate " " args.toList} exited {c}: {o}")

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

/-- A bare `origin` holding the scratch repository's `main`. Pushed to by its
path: the guard lets a push through only to a bare repository this run made,
which a remote's name does not show. -/
def addRemote (s : Scratch) : IO String := do
  let remote := s!"{s.root}/remote.git"
  hgitOk #["init", "-q", "--bare", "-b", "main", remote] s.root
  hgitOk #["remote", "add", "origin", remote] s.repo
  hgitOk #["push", "-q", remote, "main"] s.repo
  return remote

def scenarioBranchMoves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/moves" "moves"
  -- The author commits on the branch, in its own worktree, while the gates
  -- run: the branch no longer names the tip the landing read.
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

/-- A rebase that stops with nothing unmerged: a commit that cannot be
signed stops the pick with its change staged. -/
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

/-- A branch that already contains `main` carries its reviewed merge result,
including a side commit deliberately reconciled without its old content.
Landing preserves that exact tip, its tree and its ancestry on the remote.
Replaying such a merge used to flatten it and could restore discarded code. -/
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

/-- The branch's own commit adds `BAD`; a gate that refuses `BAD` must see
it. The gates once ran in the branch worktree, whose owner switched it to
another branch mid-landing, and `BAD` landed under a passing gate. -/
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

/-- A commit lands on `main` the instant `git push` starts — a deterministic
stand-in for a concurrent commit in the main worktree. The push must send
the gated tip, and the ungated commit must not reach the remote. -/
def scenarioPushNamesTip (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushtip" "pushtip"
  let remote ← addRemote s
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  IO.FS.createDirAll s!"{s.root}/wrap"
  -- Only the push to `origin`: the fast-forward is a push too, into this
  -- repository, and a commit there would make the landing refuse instead.
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

/-- The remote's `main` moved on where this repository cannot see it: the
push is not a fast-forward, and must fail loudly, never force. -/
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

/-- The shape a landing found by hand: through a `merge=union` file the
rebase kept a heading the branch had renamed away, git reported no conflict,
and every gate passed. -/
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
  -- `land check` with no name: the branch `agent/check` exists, so a
  -- fall-through to the bare-name form would land it.
  let (code, _) ← landIn self s.repo #["check"] "t=true"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a subcommand word is not an agent name"
         , ok := code == 3 && before == after
         , detail := s!"exit={code} main-before={before} main-after={after}" }

/-- A landing started with `GIT_DIR` naming another repository — as every
hook in a linked worktree is — lands the repository its working directory
names, runs its gates with no `GIT_DIR`, and writes nothing into the other
one. -/
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

/-- Retention and listings run while a landing is inside its gates. Sixty
directories whose names sort after any run id stand in the run directory
first, so the landing's own directory is the oldest there and the first a
pruning pass would take: a gate then calls this very binary three times as
`retire` (which prunes run directories) and twice as `status`. The
landing's own directory must survive, and the landing finish. The first
form of this scenario relied on fifty-five `retire` runs outnumbering the
landing's directory, and passed against the defective build in two runs of
five, because run ids within one second did not sort by time. -/
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

/-- A landing killed inside a gate — a timeout, Ctrl-C, a killed agent —
must not wedge the next one: the lock dies with it, and the next landing
records the dead run and removes its gate tree. -/
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

/-- A `git` on `PATH` that runs `hook` (shell text) once, when the landing
invokes `git` with arguments `cond` accepts, then runs the real git. A
deterministic stand-in for a party acting at one instant of a landing, as the
reviewer's probes are. -/
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

/-- The owner's next unit, committed in the owner's own worktree by the
wrapper: shell text for `gitWrapper`, which records the commit's sha. -/
def ownerCommit (s : Scratch) (realGit : String) : String :=
  s!"  echo \"the owner's next unit\" > {s.wt}/owner-work.txt\n\
  \"{realGit}\" -C {s.wt} add owner-work.txt\n\
  \"{realGit}\" -C {s.wt} commit -qm \"The owner's next unit\"\n\
  \"{realGit}\" -C {s.wt} rev-parse HEAD > {s.root}/owner-commit.txt"

/-- Is the owner's commit still on the owner's branch, and its file in the
owner's worktree, which reads clean? -/
def ownerKept (s : Scratch) (branch : String) : IO (Bool × String) := do
  let oc := trimWs (← try IO.FS.readFile s!"{s.root}/owner-commit.txt" catch _ => pure "")
  let (anc, _) ← hgit #["merge-base", "--is-ancestor", oc, branch] s.repo
  let present ← System.FilePath.pathExists s!"{s.wt}/owner-work.txt"
  let (_, st) ← hgit #["status", "--porcelain"] s.wt
  return (isSha oc && anc == 0 && present && st.isEmpty,
    s!"owner-commit={oc} reachable={anc == 0} file={present} status=[{st}]")

/-- The branch's owner commits in their own worktree after the landing read
the branch and just before the gated tip is prepared. The landing must keep that
commit: a run once replayed it, read it as drift, and put the branch back at
the tip it read first — erasing the commit from the branch and the file from
the owner's worktree. Both a preserved tip and a replay onto changed main
must retain the owner's subsequent commit and refuse the landing. -/
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

/-- As above, with the owner's commit the instant the rebase ends, under
`land check`, which lands nothing and must write nothing of the owner's. -/
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

/-- The main worktree is switched to another branch at the instant of the
fast-forward. Only `refs/heads/main` may move: the fast-forward once moved
whatever the main worktree's `HEAD` named. -/
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

/-- The remote holds a ref whose name ends in `refs/heads/main` and sorts
before it. The read-back must read `refs/heads/main` itself: the first line
`ls-remote` printed once recorded a pushed landing as unpushed. -/
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

/-- `main` moved, so the landing replays the branch's commits onto it and
the branch keeps the originals. A decoy of the whole flow: a second landing
of the same, unmoved branch must refuse, rather than replay commits `main`
already holds. -/
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
  return { label := "a rebased landing leaves the branch alone, and landing it again refuses"
         , ok := c1 == 0 && bAfter == bTip && main1 != bTip && c2 == 2 && main2 == main1
             && says out2 "already landed"
         , detail := s!"first={c1} second={c2} branch={bTip}->{bAfter} main={main1}->{main2}" }

/-- The review's q12. A landing onto a moved `main` replays the branch as
rebased copies and leaves the branch where it was; `main` is then put back
where it stood before that landing — a local undo, before any push. The
branch's work is then on the branch and not on `main`, so that landing's row
bars nothing: the unmoved branch lands again, and so, after one more undo,
does a continued one, with both its units. The build this scenario was
written against refused the first as "already landed" and told the second
to `git rebase --onto main <tip>`, which dropped the landed unit from the
branch. While `main` does hold a landing, the branch takes no further
landing, and the refusal sends the next unit to a new branch from `main`,
never through a rebase of this one. -/
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
  -- `main` holds that landing: the unmoved branch, and then the continued
  -- one, are refused, and pointed at a new branch.
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
         , ok := c1 == 0 && g1 != bTip && c2 == 0 && own2 && c3 == 2 && pointed out3
             && c4 == 2 && pointed out4 && g4 == g2 && c5 == 0 && own5 && next5
             && bAfter == nTip
         , detail := s!"land={c1} put-back-land={c2} own-on-main={own2} again={c3} \
pointed={pointed out3} continued={c4} pointed={pointed out4} main={g2}->{g4} \
put-back-continued={c5} own-on-main={own5} next-on-main={next5} branch={nTip}->{bAfter}" }

/-- A branch landed as rebased copies is retired: the ledger, not ancestry,
says it is merged, and the branch is deleted by compare-and-swap. -/
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

/-- A landing made without `--push` is published later by `land push`, which
names the landed sha and reads the remote back: a second `land <name>
--push` refuses, because the branch is no longer ahead, and a hand push has
no read-back and leaves no row. -/
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

/-- A commit lands on `main` by hand after the last landing: `land push`
must refuse to publish it, and the remote stays where it was. -/
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

/-- A repository with an origin, as the real one stood when its `main` was
pushed unasked: `main` one commit ahead of its origin's, and a linked
worktree on its own branch — the worktree whose hook is handed `GIT_DIR` and
`GIT_INDEX_FILE` naming this repository. -/
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

/-- Everything a command could have written in the victim and its origin: the
origin's refs; the victim's refs, config and worktrees; the linked worktree's
`HEAD` and index, as bytes. -/
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

/-- The incident's shape. The harness is started the way a hook in a linked
worktree starts a program — `GIT_DIR` and `GIT_INDEX_FILE` naming that
worktree's repository, whose `main` is ahead of its origin's — and must run
its scenarios and leave that repository and its origin as they were: the
origin's `main` unmoved, no ref, config or worktree written. The build before
the scrub (cfd060d3), started so on a scratch copy, pushed that repository's
`main` to its origin, added thirteen branches and twelve worktrees, and
rewrote its config down to `core.bare`. -/
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
  return { label := "a harness started under a hook's GIT_DIR runs, and leaves that repository \
and its origin as they were"
         , ok := code == 0 && ran ≥ 10 && pushed && before == after
         , detail := s!"exit={code} scenarios={ran} push-scenario={pushed} \
changed={before.changed after}" }

/-- A harness whose scratch root lies inside a checkout refuses to start: git
discovers that checkout from any directory under the root that is not a
repository itself, and a fixture command there would write it. The checkout
is left as it was, and the directory holds nothing afterwards. -/
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

/-- The guard refuses, before git runs, each command whose writes the run does
not own: one run from outside the root, a push by a remote's name, a push to
a repository the run did not make bare, a global option, a fetch, and the
tool under test in a repository with a remote the run did not make. None of
them writes anything, and a push by path to the run's own bare repository
still goes through. -/
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

/-- No command the harness starts can use a network transport. Every
repository a scenario makes is a local path and a real remote never is, so
the harness's environment leaves git itself refusing `https`. The tool under
test runs one gate that asks for a remote at the loopback address, on a port
nothing answers, and that passes only when git refused the transport before
it tried to connect. -/
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

/-- Drive the driver against throwaway repositories. `LAND_SCENARIO_BINARY`
names another build to drive instead of this one — how a scenario is shown
to fail on the tip before its fix. The scratch root is a fresh directory
this run creates, by its real path, under `LAND_SCRATCH_DIR` (else `/tmp`),
and the run refuses to start, exit 2, when a repository encloses it. Under
`LAND_SCENARIO_NESTED` — how the two scenarios that start a harness start
it — those two are left out, so a harness never starts itself again. -/
def scratchSelftest : IO UInt32 := do
  let self ← do
    match ← IO.getEnv "LAND_SCENARIO_BINARY" with
    | some b => pure b
    | none => pure (← IO.appPath).toString
  let nested := (← IO.getEnv "LAND_SCENARIO_NESTED").isSome
  -- A fresh directory, named by its real path: git names directories by
  -- their real path, and the guard compares what git names.
  let parent := (← IO.getEnv "LAND_SCRATCH_DIR").getD "/tmp"
  let made ← try
      IO.FS.createDirAll parent
      let d := s!"{parent}/land-scenarios-{← IO.Process.getPID}-{← IO.monoNanosNow}"
      IO.FS.createDir d
      pure (some (← IO.FS.realPath d).toString)
    catch _ => pure none
  let some root := made
    | say "scratch-root" "fail" [("parent", parent), ("why", "no fresh directory could be made")]
      sayFinal .refused [("why", s!"no fresh scratch root under {parent}")]
      return 2
  -- premise: scenarioRootInCheckout — a root a repository encloses is refused
  -- here, before any command runs, and the directory is left empty.
  match rootFault root (← gitDirOf root) with
  | some why =>
    rmQuiet root
    say "scratch-root" "fail" [("root", root), ("why", why)]
    sayFinal .refused [("why", why)]
    return 2
  | none => pure ()
  harnessGuard.set (some { root, made := [] })
  say "scratch-root" "ok" [("root", root)]
  let (gv, _) ← hgit #["--version"] root
  if gv != 0 then
    rmQuiet root
    say "scenario" "skip" [("why", "git is not available")]
    sayFinal .checked [("scenarios", "0")]
    return 0
  let starting : List (String × (String → String → IO Outcome)) :=
    [("hookdir", scenarioHookGitDir), ("incheckout", scenarioRootInCheckout)]
  let scenarios : List (String × (String → String → IO Outcome)) :=
    [ ("lands", scenarioLands), ("moves", scenarioBranchMoves), ("leaves", scenarioMainLeaves)
    , ("merge-kept", fun self root => scenarioMergedTip self root false)
    , ("merge-reconciled", fun self root => scenarioMergedTip self root true)
    , ("conflict", scenarioConflict), ("optin", scenarioNoOptIn), ("reserved", scenarioReserved)
    , ("stopped", scenarioStoppedRebase), ("switched", scenarioWorktreeSwitched)
    , ("treemoved", scenarioTreeMoved), ("pushtip", scenarioPushNamesTip)
    , ("pushff", scenarioPushNotFastForward), ("union", scenarioUnionDrift)
    , ("foreign", scenarioForeignGitDir), ("retain", scenarioRetention)
    , ("killed", scenarioKilled)
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
    -- A fixture that could not be built is the scenario's failure, named,
    -- never a harness that stops with the rest unrun.
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

-- ## Entry

def usage : String :=
  "usage: land new <name> | land check <name> | land <name> [--push] | land push | \
land retire <name> | land status | land --selftest | land --scratch-selftest"

/-- The subcommand words, which are not agent names. `land check` with no
name once fell through to the bare-name form and would have landed
`agent/check`. -/
def reserved : List String := ["new", "check", "retire", "status", "push"]

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
  match argv with
  | [] => IO.eprintln usage; return 3
  | ["--selftest"] => selftest
  | ["--scratch-selftest"] => scratchSelftest
  | args => do
    match ← mkEnv with
    | .error e => IO.eprintln s!"land: {e}"; return 3
    | .ok env =>
      let landing (n : String) (m : Mode) (p : Bool) : IO UInt32 := do
        if reserved.contains n then
          IO.eprintln s!"land: {n} is a subcommand, not an agent name"
          return 3
        match ← resolveGates env with
        | .error why =>
          say "gateset" "fail" [("why", why)]
          sayFinal .refused [("name", n), ("why", why)]
          return 2
        | .ok (gs, gateset) => withLock env n (landRun env n m p gs gateset)
      let named (n : String) (act : IO UInt32) : IO UInt32 := do
        if reserved.contains n then
          IO.eprintln s!"land: {n} is a subcommand, not an agent name"
          return 3
        act
      let code ← match args with
        | ["status"] => do
          -- A listing is no run: it prunes nothing and leaves no directory,
          -- so any number of them cannot crowd a landing's out.
          let c ← landStatus env
          rmQuiet env.runDir
          pure c
        | _ => do
          retainRuns env 50
          match args with
          | ["new", n] => named n (landNew env n)
          | ["retire", n] => named n (landRetire env n)
          | ["push"] => withLock env "push" (landPush env)
          | ["check", n] => landing n .check false
          | [n] => landing n .land false
          | [n, "--push"] => landing n .land true
          | _ => IO.eprintln usage; return 3
      env.alive.unlock
      return code
