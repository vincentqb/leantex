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

The gates run in the run's own gate tree — a detached worktree at the
rebased tip, `<run dir>/tree`, seeded with a copy of a `.lake` and removed
when the run ends — never in the branch's worktree, whose checkout its
owner may switch while the gates run.
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
it. -/
def runGate (e : Env) (ctr : IO.Ref Nat) (g : Gate) (idx : Nat) : IO Obs := do
  let tree := treePath e
  if let some tgt := g.needsTarget then
    if !(← lakefileDeclares tree tgt) then
      return .gateAbsent idx
  let step := s!"gate-{g.name}"
  let (hb, cb) ← readTree e ctr step
  let cmd := if g.cmd.startsWith "." then s!"{tree}/{g.cmd}" else g.cmd
  let r ← sh e ctr step cmd g.args (some tree)
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
      | .rebase onto => do
        -- Onto the sha this run read, never the name `main`, so the base the
        -- net comparison reads is the base the commits were replayed onto.
        -- `--no-update-refs`: a rebase that also moved another branch's ref
        -- would be a ref change no gate earned.
        let r ← git e ctr "rebase"
          #["rebase", "--no-update-refs", "--no-autosquash", "--no-autostash", onto] (some wt)
        if r.code == 0 then
          let tip ← revParse e ctr "rebase" s!"refs/heads/agent/{name}" (some wt)
          say "rebase" "ok" [("onto", onto), ("tip", if tip.isEmpty then "?" else tip)]
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
      | .restoreBranch rebased original => do
        -- Only a branch still at the rebased tip, on its branch and clean, is
        -- put back: anything else is someone's work, and is left alone.
        let branchRef := s!"refs/heads/agent/{name}"
        let h0 ← revParse e ctr "restore" "HEAD" (some wt)
        let on0 ← headIs e ctr "restore" wt branchRef
        let c0 ← statusClean e ctr "restore" wt
        if h0 == rebased && on0 && c0 == some true then
          let _ ← git e ctr "restore" #["reset", "--keep", original] (some wt)
          pure ()
        let headTip ← revParse e ctr "restore" "HEAD" (some wt)
        let onBranch ← headIs e ctr "restore" wt branchRef
        let clean := (← statusClean e ctr "restore" wt) == some true
        say "restore" (if onBranch && clean && headTip == original then "ok" else "fail")
          [("head", if headTip.isEmpty then "?" else headTip), ("was", original),
           ("branch", if onBranch then "yes" else "no"),
           ("dirty", if clean then "no" else "yes")]
        pure (.branchRestored headTip onBranch clean)
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
          let o ← runGate e ctr gd i
          let tail (head : Sha) (clean : Bool) : List (String × String) :=
            [("idx", toString i), ("head", if head.isEmpty then "?" else head),
             ("dirty", if clean then "no" else "yes")]
          match o with
          | .gateOk _ head clean => say s!"gate-{g}" "ok" (tail head clean); pure o
          | .gateFail _ head clean =>
            say s!"gate-{g}" "fail" (tail head clean ++ [("log", s!"gate-{g}.log")]); pure o
          | .gateAbsent _ =>
            say s!"gate-{g}" "skip"
              [("idx", toString i), ("why", "the lakefile declares no such target")]
            pure o
          | _ => pure o
      | .recheckBranch => do
        -- The gates ran in the run's own tree; this asks whether the author
        -- still names the commit they ran on.
        let tip ← revParse e ctr "post-gate" s!"refs/heads/agent/{name}" (some e.mainWt)
        say "post-gate" (if tip == st.gatedTip then "ok" else "fail")
          [("tip", if tip.isEmpty then "?" else tip), ("gated", st.gatedTip)]
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

def sha1s : Sha := "1111111111111111111111111111111111111111"
def sha2s : Sha := "2222222222222222222222222222222222222222"
def sha3s : Sha := "3333333333333333333333333333333333333333"

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

/-- The indices of the gates the shipped plan permits to be absent. -/
def skippableIdx : List Nat :=
  (List.range gatePlan.size).filter fun i => (gatePlan[i]?.map (·.mayAbsent)).getD false

def cases : List Case :=
  let pre := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
    Obs.rebaseOk sha3s, netSame, Obs.treeReady sha3s true]
  let landOk := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha1s,
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
  , { label := "the branch moved during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha1s]
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
  , { label := "the gate tree was not made at the gated tip", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s, netSame, .treeReady sha1s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the gate tree was dirty when made", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s, netSame, .treeReady sha3s false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the gate tree did not read back", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s, netSame, .treeReady "" false]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a gate before the gate tree exists", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk sha3s, netSame, .gateOk 0 sha3s true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the rebase kept a line the branch deleted: restored, refused"
    , mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 1 true sha2s,
        Obs.rebaseOk sha3s, .netDiffs netBranch netUnion, .branchRestored sha2s true true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a drifted rebase in check mode is refused too", mode := .check, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 1 true sha2s,
        Obs.rebaseOk sha3s, .netDiffs netBranch netUnion, .branchRestored sha2s true true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "a drifted rebase that could not be put back", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 1 true sha2s,
        Obs.rebaseOk sha3s, .netDiffs netBranch netUnion, .branchRestored sha3s true true]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "a file only the rebase touched is drift", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 1 true sha2s,
        Obs.rebaseOk sha3s, .netDiffs "" netMoved, .branchRestored sha2s true true]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "main moved during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the main worktree left main during the gates", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck false sha1s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "main reads back at another commit after the merge"
    , mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha1s,
        .ledgerOk, .ffOk, .mainTip sha1s]
    , verdict := .failed, code := 3, noMutation := false }
  , { label := "a truncated sha is not a sha", mode := .land, push := false
    , obs := [Obs.mainStatus true true sha1s, Obs.branchStatus 1 0 true sha2s,
        Obs.rebaseOk "33333333"]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the fast-forward is rejected", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha1s,
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
    , obs := pre
        ++ ((List.range gatePlan.size).map fun i =>
              if skippableIdx.contains i then Obs.gateAbsent i else Obs.gateOk i sha3s true)
        ++ [.branchRecheck sha3s, .mainRecheck true sha1s, .ledgerOk, .ffOk,
            .mainTip sha3s, .ledgerOk]
    , verdict := .landed, code := 0, noMutation := false }
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
    , obs := [.mainStatus true true sha1s, .branchStatus 0 4 true sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "the branch worktree is dirty", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .branchStatus 2 0 false sha2s]
    , verdict := .refused, code := 2, noMutation := true }
  , { label := "an observation out of order", mode := .land, push := false
    , obs := [.mainStatus true true sha1s, .ffOk]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the write-ahead row was not written", mode := .land, push := false
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha1s,
        .ledgerFail]
    , verdict := .failed, code := 3, noMutation := true }
  , { label := "the landed row was not written", mode := .land, push := true
    , obs := pre ++ okGates ++ [.branchRecheck sha3s, .mainRecheck true sha1s,
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
  -- The net comparison, which the scenarios reach only through git.
  for (label, before, after, want) in netCases do
    let got := netDrift (netOf before) (netOf after)
    if got != want then
      bad := bad + 1
      say "selftest" "fail" [("case", s!"net: {label}"),
        ("why", s!"drift [{String.intercalate "," got.toList}]")]
    else say "selftest" "ok" [("case", s!"net: {label}")]
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

/-- The environment every harness child gets: each `GIT_` variable this
process inherited removed, and git's global and system configuration out of
reach. git exports `GIT_DIR` and `GIT_INDEX_FILE` to a hook in every linked
worktree, so a harness started from one once committed its fixtures into the
repository `GIT_DIR` named and opted that repository in to gate overrides;
and a host's `commit.gpgsign` or `core.hooksPath` would change what a
scenario tests. -/
def harnessEnv : IO (Array (String × Option String)) := do
  let set : Array (String × Option String) := #[("GIT_CONFIG_GLOBAL", some "/dev/null"),
    ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_TERMINAL_PROMPT", some "0")]
  let inherited ← gitVarsInEnv
  let names := repoVarsFixed.foldl (init := inherited) fun acc n =>
    if acc.contains n then acc else acc.push n
  let unset := (names.filter fun n => !(set.any (·.1 == n))).map (·, none)
  return unset.append set

/-- Run a command for the harness. Not `sh`: there is no run directory yet,
and the harness asserts on exit codes rather than on parsed facts. -/
def hrun (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) := do
  let env ← harnessEnv
  let r ← try
      IO.Process.output
        { cmd, args, cwd := cwd.map System.FilePath.mk, env := env.append extraEnv,
          stdin := .null }
    catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }
  return (r.exitCode.toNat, trimWs (r.stdout ++ r.stderr))

def hgit (args : Array String) (cwd : String) : IO (Nat × String) :=
  hrun "git" args (some cwd)

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
  hrun self args (some repo) (#[("LAND_GATES", some gates),
    ("GIT_TERMINAL_PROMPT", some "0")] ++ extraEnv)

/-- Does `out` carry `s`? -/
def says (out s : String) : Bool := (out.splitOn s).length > 1

/-- The worktrees a scratch repository has registered, by path. -/
def worktreePaths (repo : String) : IO (Array String) := do
  let (_, o) ← hgit #["worktree", "list", "--porcelain"] repo
  return ((o.splitOn "\n").filter (·.startsWith "worktree ")).toArray.map
    fun l => (l.drop "worktree ".length).toString

/-- A bare `origin` holding the scratch repository's `main`. -/
def addRemote (s : Scratch) : IO String := do
  let remote := s!"{s.root}/remote.git"
  hgitOk #["init", "-q", "--bare", "-b", "main", remote] s.root
  hgitOk #["remote", "add", "origin", remote] s.repo
  hgitOk #["push", "-q", "origin", "main"] s.repo
  return remote

def scenarioBranchMoves (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/moves" "moves"
  -- The author commits on the branch, in its own worktree, while the gates
  -- run: the gated commit is no longer the one the branch names.
  writeExe s!"{s.root}/race.sh"
    s!"#!/bin/sh\necho bad > {s.wt}/BAD && git -C {s.wt} add BAD && git -C {s.wt} commit -qm concurrent\n"
  let before ← revOf s.repo "refs/heads/main"
  let (code, out) ← landIn self s.repo #["moves"] s!"race={s.root}/race.sh"
  let after ← revOf s.repo "refs/heads/main"
  return { label := "a commit on the branch during the gates is refused"
         , ok := code == 2 && before == after && says out "moved during the gates"
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
  return { label := "a rebase conflict is refused and the branch restored"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && says out "rebase conflict: shared.txt" && says out "step=rebase-abort result=ok"
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}]" }

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
  let (_, rm) ← hgit #["rev-parse", "--git-path", "rebase-merge"] s.wt
  let mid ← System.FilePath.pathExists (if rm.startsWith "/" then rm else s!"{s.wt}/{rm}")
  return { label := "a rebase stopped with nothing unmerged is refused and the branch restored"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty && !mid
             && says out "the rebase failed and was aborted"
         , detail := s!"exit={code} branch={bBefore}->{bAfter} main={mBefore}->{mAfter} \
status=[{st}] mid-rebase={mid}" }

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
             && wts.size == 2
         , detail := s!"exit={code} main-before={before} main-after={after} worktrees={wts.size}" }

/-- A commit lands on `main` the instant `git push` starts — a deterministic
stand-in for a concurrent commit in the main worktree. The push must send
the gated tip, and the ungated commit must not reach the remote. -/
def scenarioPushNamesTip (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/pushtip" "pushtip"
  let remote ← addRemote s
  let (_, realGit) ← hrun "sh" #["-c", "command -v git"] none
  IO.FS.createDirAll s!"{s.root}/wrap"
  writeExe s!"{s.root}/wrap/git"
    s!"#!/bin/sh\nif [ \"$1\" = push ]; then\n  \"{realGit}\" -C {s.repo} commit -q --allow-empty -m ungated\nfi\nexec \"{realGit}\" \"$@\"\n"
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
  hgitOk #["push", "-q", "origin", "main"] other
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
  return { label := "a rebase that changed a file's net content is refused and the branch restored"
         , ok := code == 2 && bBefore == bAfter && mBefore == mAfter && st.isEmpty
             && says out "the rebase changed the net content of: PLAN.md"
             && says out "step=restore result=ok"
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

/-- Retention and listings run while a landing is inside its gates: a
gate calls this very binary 55 times as `retire` (which prunes run
directories) and 5 as `status`. The landing's own directory must survive,
and the landing finish. -/
def scenarioRetention (self root : String) : IO Outcome := do
  let s ← mkScratch s!"{root}/retain" "retain"
  writeExe s!"{s.root}/prune.sh"
    s!"#!/bin/sh\ni=0\nwhile [ $i -lt 55 ]; do \"{self}\" retire nope >/dev/null 2>&1; i=$((i+1)); done\n\
i=0\nwhile [ $i -lt 5 ]; do \"{self}\" status >/dev/null 2>&1; i=$((i+1)); done\n"
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

/-- Drive the driver against throwaway repositories. `LAND_SCENARIO_BINARY`
names another build to drive instead of this one — how a scenario is shown
to fail on the tip before its fix. -/
def scratchSelftest : IO UInt32 := do
  let self ← do
    match ← IO.getEnv "LAND_SCENARIO_BINARY" with
    | some b => pure b
    | none => pure (← IO.appPath).toString
  let nanos ← IO.monoNanosNow
  let root := ((← IO.getEnv "LAND_SCRATCH_DIR").getD "/tmp") ++ s!"/land-scenarios-{nanos % 1000000}"
  IO.FS.createDirAll root
  let (gv, _) ← hrun "git" #["--version"] none
  if gv != 0 then
    say "scenario" "skip" [("why", "git is not available")]
    sayFinal .checked [("scenarios", "0")]
    return 0
  let scenarios : List (String × (String → String → IO Outcome)) :=
    [ ("lands", scenarioLands), ("moves", scenarioBranchMoves), ("leaves", scenarioMainLeaves)
    , ("conflict", scenarioConflict), ("optin", scenarioNoOptIn), ("reserved", scenarioReserved)
    , ("stopped", scenarioStoppedRebase), ("switched", scenarioWorktreeSwitched)
    , ("treemoved", scenarioTreeMoved), ("pushtip", scenarioPushNamesTip)
    , ("pushff", scenarioPushNotFastForward), ("union", scenarioUnionDrift)
    , ("foreign", scenarioForeignGitDir), ("retain", scenarioRetention)
    , ("killed", scenarioKilled) ]
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
          | ["check", n] => landing n .check false
          | [n] => landing n .land false
          | [n, "--push"] => landing n .land true
          | _ => IO.eprintln usage; return 3
      env.alive.unlock
      return code
