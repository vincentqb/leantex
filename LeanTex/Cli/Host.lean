module

public import LeanTex.Cli.World
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.RunBounded
import all Init.System.ST
import LeanTex.Core.Hex

/-! The one interpreter of `World`'s questions: a `BaseIO` action whose every `IO.Error`
is reply data, with sorted listings, reads refused for anything but a regular file, and
budgeted runs in scratch they own. -/

namespace LeanTex.Cli.Host

open LeanTex.Cli.World

/-- The monad laws of `BaseIO`, a state transition over an opaque world token. -/
public instance : LawfulMonad BaseIO := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => funext fun s => by
    show ST.bind (ST.bind x f) g s = ST.bind x (fun a => ST.bind (f a) g) s
    simp only [ST.bind])

private def failure : IO.Error → Failure
  | .noFileOrDirectory .. | .noSuchThing .. => .absent
  | .permissionDenied .. => .denied
  | e => .other (toString e)

private def kindOf : IO.FS.FileType → Kind
  | .dir => .dir
  | .file => .file
  | .symlink => .symlink
  | .other => .other

private def caught {α : Type} (act : IO α) : BaseIO (Except Failure α) := do
  match ← act.toBaseIO with
  | .ok a => return .ok a
  | .error e => return .error (failure e)

private def statOf (path : String) : BaseIO (Except Failure Stat) := caught do
  let md ← System.FilePath.metadata path
  let real ← IO.FS.realPath path
  return { kind := kindOf md.type, size := md.byteSize.toNat, mtimeSec := md.modified.sec,
           mtimeNsec := md.modified.nsec.toNat, real := real.toString }

private def metadataOf (path : String) : BaseIO (Except Failure Metadata) := caught do
  let md ← System.FilePath.metadata path
  return { kind := kindOf md.type, size := md.byteSize.toNat, mtimeSec := md.modified.sec,
           mtimeNsec := md.modified.nsec.toNat, links := md.numLinks.toNat }

private def readRegular (path : String) : BaseIO (Except Failure ByteArray) := do
  match ← caught (System.FilePath.metadata path) with
  | .error f => return .error f
  | .ok md =>
    if md.type != .file then return .error .notRegular
    caught (IO.FS.readBinFile path)

private def listing (path : String) : BaseIO (Except Failure (Array (String × Kind))) := do
  match ← caught (System.FilePath.readDir path) with
  | .error f => return .error f
  | .ok entries =>
    let mut out := #[]
    for entry in entries do
      let kind := match ← caught entry.path.symlinkMetadata with
        | .ok md => kindOf md.type
        | .error _ => .other
      out := out.push (entry.fileName, kind)
    return .ok (out.qsort fun a b => a.1 < b.1)

/-- A name a run may write or read: relative, and never leaving the scratch
directory. -/
private def scratchName (name : String) : Bool :=
  !name.isEmpty && !name.startsWith "/" &&
    (name.splitOn "/").all fun part => !part.isEmpty && part != "." && part != ".."

/-- Where scratch directories are made and what chose it: the first set, nonempty one of
TMPDIR, TMP, TEMP and TEMPDIR, else /tmp. -/
private def scratchRoot : BaseIO (System.FilePath × String) := do
  for name in ["TMPDIR", "TMP", "TEMP", "TEMPDIR"] do
    if let some dir ← IO.getEnv name then
      unless dir.isEmpty do return (dir, name)
  return ("/tmp", "the default")

/-- An error's kind in words, without the path it carried. -/
public def describe : IO.Error → String
  | .noFileOrDirectory .. => "no such file or directory"
  | .permissionDenied .. => "permission denied"
  | .alreadyExists .. => "a file of that name is in the way"
  | .inappropriateType .. => "a file is where a directory should be"
  | .resourceExhausted .. => "the system ran out of a resource it needs, such as space"
  | e => ((toString e).splitOn "\n").headD (toString e)

private def hex (bytes : ByteArray) : String := bytes.foldl (· ++ LeanTex.Core.Hex.byte false ·) ""

/-- A fresh, empty directory only this user can enter, under the scratch root's real path;
`IO.FS.createTempDir` instead crashes where no directory can be made. -/
private def scratchDir : IO System.FilePath := do
  let (named, chosen) ← scratchRoot
  let root := (← (IO.FS.realPath named).toBaseIO).toOption.getD named
  let unmade (why : String) : IO.Error := IO.userError
    s!"no scratch directory can be made in the temporary directory '{named}' ({chosen}): {why}"
  for _ in [0:16] do
    let dir := root / ("leantex-" ++ hex (← IO.getRandomBytes 8))
    match ← (IO.FS.createDir dir).toBaseIO with
    | .ok () =>
      match ← (IO.setAccessRights dir { user := ⟨true, true, true⟩ }).toBaseIO with
      | .error e =>
        discard <| (IO.FS.removeDir dir).toBaseIO
        throw (unmade (describe e))
      | .ok () =>
        if (← dir.symlinkMetadata).type == .dir && (← dir.readDir).isEmpty then return dir
    | .error (.alreadyExists ..) => continue
    | .error e => throw (unmade (describe e))
  throw (unmade "every fresh name was taken")

/-- A declared output when it is a regular file inside the scratch directory once links
are followed; `real` is the directory's real path before the tool ran. -/
private def ownOutput (dir real : System.FilePath) (name : String) : BaseIO (Option ByteArray) := do
  match ← caught (IO.FS.realPath (dir / name)) with
  | .ok path =>
    if path.toString.startsWith (real.toString ++ "/") then return (← readRegular path.toString).toOption
    else return none
  | .error _ => return none

/-- Remove the scratch directory and what the run left in it, without following a link at
its root. -/
private def removeScratch (dir : System.FilePath) : IO Unit := do
  if (← dir.symlinkMetadata).type == .dir then IO.FS.removeDirAll dir
  else IO.FS.removeFile dir

/-- `f` in a fresh scratch directory of its own, removed afterwards whatever `f` returns
or raises. -/
public def withScratch {α : Type} (f : System.FilePath → IO α) : IO α := do
  let dir ← scratchDir
  try f dir finally discard <| (removeScratch dir).toBaseIO

/-- `text` with the scratch directory's names, as made and as resolved,
spelled `<scratch>`. -/
private def scrubbed (dir real : System.FilePath) (text : String) : String :=
  (text.replace real.toString "<scratch>").replace dir.toString "<scratch>"

private def runCall (call : ToolCall) : BaseIO Ended := do
  let unstarted (why : String) : Ended :=
    { ran := .unstarted why, out := "", err := "", complete := false,
      outputs := call.outputs.map (·, none) }
  unless call.inputs.all (scratchName ·.1) && call.outputs.all scratchName do
    return unstarted "a run reads and writes only names inside its scratch directory"
  match ← scratchDir.toBaseIO with
  | .error e => return unstarted (toString e)
  | .ok dir =>
    match ← (IO.FS.realPath dir).toBaseIO with
    | .error e =>
      discard <| (IO.FS.removeDir dir).toBaseIO
      return unstarted (scrubbed dir dir (toString e))
    | .ok real =>
      let attempt : IO Ended := do
        for (name, bytes) in call.inputs do
          let file := dir / name
          if let some parent := file.parent then IO.FS.createDirAll parent
          IO.FS.writeBinFile file bytes
        let got ← RunBounded.runBounded call.tool call.args
          ((call.cwd.map System.FilePath.mk).getD dir) call.budgetMs call.graceMs
          call.captureLimit call.env
        let mut outputs := #[]
        for name in call.outputs do
          outputs := outputs.push (name, ← ownOutput dir real name)
        return { ran := got.ran, out := scrubbed dir real got.out, err := scrubbed dir real got.err,
                 complete := got.complete, outputs }
      let result ← attempt.toBaseIO
      discard <| (removeScratch dir).toBaseIO
      match result with
      | .ok ended => return ended
      | .error e => return unstarted (scrubbed dir real (toString e))

/-- The host's answer to one question, the one place the driver's host access is
answered. -/
public def answer : (q : Ask) → BaseIO (Reply q)
  | .env name => IO.getEnv name
  | .cwd => caught do return (← IO.currentDir).toString
  | .stat path => statOf path
  | .metadata path => metadataOf path
  | .readFile path => readRegular path
  | .listDir path => listing path
  | .run call => runCall call
  | .writeAtomic path bytes => caught (AtomicFile.write path bytes)
  | .createDirAll path => caught (IO.FS.createDirAll path)

public def runIO {α : Type} (p : Prog α) : BaseIO α := p.runM answer

public def recordIO {α : Type} (p : Prog α) : BaseIO (α × List Fact) := p.record answer

/-- The host with every run refused: a run is answered as one that never
started, and every other question as `answer` answers it. -/
public def answerRunless : (q : Ask) → BaseIO (Reply q)
  | .run call => pure {
      ran := .unstarted "no process starts here", out := "", err := "", complete := false
      outputs := call.outputs.map (·, none) }
  | q => answer q

public theorem answer_runless_exact (q : Ask) (h : ToolPath.Lookup q) :
    answer q = answerRunless q := by
  cases q <;> first | rfl | exact absurd h id

public theorem record_replay_exact {α : Type} (p : Prog α) :
    (fun x => (x, p.replay x.2 = some x.1)) <$> recordIO p =
      (fun x => (x, True)) <$> recordIO p :=
  Prog.record_replay_exact answer p

public theorem recordIO_fst_exact {α : Type} (p : Prog α) : Prod.fst <$> recordIO p = runIO p :=
  Prog.record_fst_exact answer p

public theorem located_runless_exact (tool : String) :
    runIO (ToolPath.located tool) = (ToolPath.located tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.located_only tool) answer answerRunless answer_runless_exact

public theorem resolve_runless_exact (tool : String) :
    runIO (ToolPath.resolve tool) = (ToolPath.resolve tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.resolve_only tool) answer answerRunless answer_runless_exact

public theorem witness_runless_exact (tool : String) :
    runIO (ToolPath.witness tool) = (ToolPath.witness tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.witness_only tool) answer answerRunless answer_runless_exact

end LeanTex.Cli.Host
