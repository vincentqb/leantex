/-
The guard a script harness runs each command through in repositories it makes: git only where every
write the call may make is the run's (`Land.hcall_writes_owned`), from a fresh root, file transport
only.
-/
import scripts.LandCore

open Land

def trimWs (s : String) : String :=
  let cs := s.toList.dropWhile (·.isWhitespace)
  String.ofList (cs.reverse.dropWhile (·.isWhitespace)).reverse

/-- Split on runs of whitespace. -/
def wsSplit (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur : String := ""
  for c in s.toList do
    if c.isWhitespace then
      if !cur.isEmpty then out := cur :: out; cur := ""
    else cur := cur.push c
  if !cur.isEmpty then out := cur :: out
  return out.reverse

/-- The variables that point git at another repository, index, object store, ref namespace
or config: git's own list plus `GIT_NAMESPACE`. -/
def repoVarsFixed : Array String := #[
  "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS",
  "GIT_CONFIG_COUNT", "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE",
  "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE", "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS",
  "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE", "GIT_COMMON_DIR",
  "GIT_NAMESPACE"]

/-- The name of every `GIT_` environment variable of this process, read from
`/proc/self/environ`; empty where it cannot be read. -/
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

/-- The environment every harness child gets: each inherited `GIT_` variable removed,
global and system configuration out of reach, and `GIT_ALLOW_PROTOCOL=file`. -/
-- premise: scenarioNoNetwork — git refuses a network transport before connecting
def harnessEnv : IO (Array (String × Option String)) := do
  let set : Array (String × Option String) := #[("GIT_CONFIG_GLOBAL", some "/dev/null"),
    ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_TERMINAL_PROMPT", some "0"),
    ("GIT_ALLOW_PROTOCOL", some "file")]
  let inherited ← gitVarsInEnv
  let names := repoVarsFixed.foldl (init := inherited) fun acc n =>
    if acc.contains n then acc else acc.push n
  let unset := (names.filter fun n => !(set.any (·.1 == n))).map (·, none)
  return unset.append set

/-- The guard every harness command is checked against, installed once the scratch root is
made; until then `hgit` and `runTool` refuse everything. -/
initialize harnessGuard : IO.Ref (Option HGuard) ← IO.mkRef none

/-- The exit status of a command the guard refused: it never ran. -/
def refusedCode : Nat := 126

/-- A command the guard refused, as its ending reads. -/
def refusedRun (why : String) : IO.Process.Output :=
  { exitCode := refusedCode.toUInt32, stdout := "", stderr := why }

/-- A command's exit code, and its output and error joined. -/
def joined (o : IO.Process.Output) : Nat × String :=
  (o.exitCode.toNat, trimWs (o.stdout ++ o.stderr))

/-- Spawn a command in the harness's environment, standard input closed; a spawn that raised
ends with exit 127 and its words on standard error. -/
private def hspawn (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let env ← harnessEnv
  try
    IO.Process.output
      { cmd, args, cwd := cwd.map System.FilePath.mk, env := env.append extraEnv,
        stdin := .null }
  catch ex => pure { exitCode := 127, stdout := "", stderr := toString ex }

/-- Run a harness command that is neither git nor the tool under test. -/
def hrun (cmd : String) (args : Array String) (cwd : Option String)
    (extraEnv : Array (String × Option String) := #[]) : IO (Nat × String) := do
  if cmd == "git" then
    return joined (refusedRun "harness: refused: git runs only through the guard (hgit)")
  joined <$> hspawn cmd args cwd extraEnv

/-- What `git rev-parse --absolute-git-dir` names from `cwd` in the harness's environment
extended by `extraEnv`; empty when git names none. -/
-- premise: scenarioHookGitDir — the repository named is the one the command writes
def gitDirOf (cwd : String) (extraEnv : Array (String × Option String) := #[]) : IO String := do
  let env ← harnessEnv
  let r ← try
      IO.Process.output
        { cmd := "git", args := #["rev-parse", "--absolute-git-dir"],
          cwd := some cwd, env := env.append extraEnv, stdin := .null }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  return if r.exitCode == 0 then trimWs r.stdout else ""

/-- Run git for the harness after the guard, only when every write the classified argv may
make is the run's; a refused command ends with `refusedCode` and why. -/
-- premise: scenarioGuardRefuses — each unowned write is refused before git runs
def hgitRun (args : Array String) (cwd : String) : IO IO.Process.Output := do
  let some g ← harnessGuard.get
    | return refusedRun "harness: refused: no scratch root is guarded"
  let gitDir ← if within g.root cwd then gitDirOf cwd else pure ""
  let c := classify cwd gitDir args
  if !c.allowed g then
    return refusedRun s!"harness: refused git {String.intercalate " " args.toList} \
from {cwd}: {c.refusal g}"
  let r ← hspawn "git" args (some cwd)
  if r.exitCode == 0 then
    if let some b := bareCreated cwd args then
      harnessGuard.modify (·.map fun g => { g with made := g.made ++ [b] })
  return r

/-- `hgitRun`, its output and error joined. -/
def hgit (args : Array String) (cwd : String) : IO (Nat × String) :=
  joined <$> hgitRun args cwd

/-- The URLs a push from the repository `cwd` could reach: every remote's `url` and
`pushurl`; any `insteadOf` rewrite answers with a URL no run owns. -/
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

/-- Run the tool under test from `cwd` after the guard: its repository inside the root,
every remote a bare repository the run made, and every `*_SCRATCH_DIR` it is handed inside
the root. -/
def runToolRun (self cwd : String) (args : Array String)
    (extraEnv : Array (String × Option String)) : IO IO.Process.Output := do
  let some g ← harnessGuard.get
    | return refusedRun "harness: refused: no scratch root is guarded"
  let gitDir ← if within g.root cwd then gitDirOf cwd extraEnv else pure ""
  let remotes ← if within g.root gitDir then remoteUrlsOf cwd extraEnv else pure []
  let c := HCall.drive cwd gitDir remotes
  let outside := extraEnv.filterMap fun (n, v) =>
    if n.endsWith "_SCRATCH_DIR" then v.filter (!within g.root ·) else none
  if let some d := outside[0]? then
    return refusedRun s!"harness: refused {self} from {cwd}: its scratch directory {d} is \
outside the scratch root {g.root}"
  if !c.allowed g then
    return refusedRun s!"harness: refused {self} from {cwd}: {c.refusal g}"
  hspawn self args (some cwd) extraEnv

/-- `runToolRun`, its output and error joined. -/
def runTool (self cwd : String) (args : Array String)
    (extraEnv : Array (String × Option String)) : IO (Nat × String) :=
  joined <$> runToolRun self cwd args extraEnv

/-- A fixture step that must succeed. -/
def hgitOk (args : Array String) (cwd : String) : IO Unit := do
  let (c, o) ← hgit args cwd
  if c != 0 then
    throw (IO.userError s!"fixture: git {String.intercalate " " args.toList} exited {c}: {o}")

/-- Why no guarded root could be made: no fresh directory under the parent, or one a
repository encloses. -/
inductive RootFault where
  | unmade (parent : String)
  | enclosed (root why : String)

/-- A fresh directory under `parent` only its owner may read, named by its real path since the
guard compares the paths git names, refused and removed when a repository encloses it, else
installed as the guard's root. -/
-- premise: scenarioRootInCheckout — an enclosed root is refused before any command runs
def guardRoot (parent label : String) : IO (Except RootFault String) := do
  let made ← try
      IO.FS.createDirAll parent
      let d := s!"{parent}/{label}-{← IO.Process.getPID}-{← IO.monoNanosNow}"
      IO.FS.createDir d
      IO.setAccessRights d { user := ⟨true, true, true⟩ }
      pure (some (← IO.FS.realPath d).toString)
    catch _ => pure none
  let some root := made | return .error (.unmade parent)
  match rootFault root (← gitDirOf root) with
  | some why =>
    try IO.FS.removeDirAll root catch _ => pure ()
    return .error (.enclosed root why)
  | none =>
    harnessGuard.set (some { root, made := [] })
    return .ok root
