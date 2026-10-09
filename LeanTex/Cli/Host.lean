module

public import LeanTex.Cli.World
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.RunBounded
import all Init.System.ST

/-! The one interpreter of `World`'s questions. `answer` is a `BaseIO`
action, so no exception leaves it: every `IO.Error` becomes a `Failure` in
the reply. A listing is sorted, because the order a filesystem returns names
in is not a fact a program may read; a read refuses what its stat does not
show as a regular file, so a FIFO is refused rather than opened; a run is
budgeted by `RunBounded` and owns the scratch directory it runs in. -/

namespace LeanTex.Cli.Host

open LeanTex.Cli.World

/-- `BaseIO` is `ST IO.RealWorld`, a state transition over an opaque world
token, so the monad laws hold of it. Core does not expose `ST.bind` to
module importers, so this module reads it through `import all`: a toolchain
that made it opaque would fail this proof at build time, never silently. -/
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

private def runCall (call : ToolCall) : BaseIO Ended := do
  let unstarted (why : String) : Ended :=
    { ran := .unstarted why, out := "", err := "", complete := false,
      outputs := call.outputs.map (·, none) }
  unless call.inputs.all (scratchName ·.1) && call.outputs.all scratchName do
    return unstarted "a run reads and writes only names inside its scratch directory"
  match ← IO.FS.createTempDir.toBaseIO with
  | .error e => return unstarted (toString e)
  | .ok dir =>
    let attempt : IO Ended := do
      for (name, bytes) in call.inputs do
        let file := dir / name
        if let some parent := file.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile file bytes
      let got ← RunBounded.runBounded call.tool call.args dir call.budgetMs call.graceMs
        call.captureLimit call.env
      let mut outputs := #[]
      for name in call.outputs do
        outputs := outputs.push (name, (← readRegular (dir / name).toString).toOption)
      return { ran := got.ran, out := got.out, err := got.err, complete := got.complete, outputs }
    let result ← attempt.toBaseIO
    discard <| (IO.FS.removeDirAll dir).toBaseIO
    match result with
    | .ok ended => return ended
    | .error e => return unstarted (toString e)

/-- The host's answer to one question. -/
public def answer : (q : Ask) → BaseIO (Reply q)
  | .env name => IO.getEnv name
  | .cwd => caught do return (← IO.currentDir).toString
  | .stat path => statOf path
  | .readFile path => readRegular path
  | .listDir path => listing path
  | .run call => runCall call
  | .writeAtomic path bytes => caught (AtomicFile.write path bytes)
  | .createDirAll path => caught (IO.FS.createDirAll path)

public def runIO {α : Type} (p : Prog α) : BaseIO α := p.runM answer

public def recordIO {α : Type} (p : Prog α) : BaseIO (α × List Fact) := p.record answer

/-- The host with no way to start a process: a run is answered as one that
never started, and every other question as `answer` answers it. -/
public def answerRunless : (q : Ask) → BaseIO (Reply q)
  | .run call => pure {
      ran := .unstarted "no process starts here", out := "", err := "", complete := false
      outputs := call.outputs.map (·, none) }
  | q => answer q

public theorem answer_runless_exact (q : Ask) (h : ToolPath.Lookup q) :
    answer q = answerRunless q := by
  cases q <;> first | rfl | exact absurd h id

/-- **The host's result is the replay of its own trace.** `record_replay_exact`
at `BaseIO` with the shipped interpreter: whatever the machine answered, the
program's result is what its recorded facts give back. -/
public theorem record_replay_exact {α : Type} (p : Prog α) :
    (fun x => (x, p.replay x.2 = some x.1)) <$> recordIO p =
      (fun x => (x, True)) <$> recordIO p :=
  Prog.record_replay_exact answer p

/-- **The shipped interpreter's result is the recorded run's**, so what
`runIO` returns is the replay of the trace `recordIO` keeps of the same run
(`record_replay_exact`). -/
public theorem recordIO_fst_exact {α : Type} (p : Prog α) : Prod.fst <$> recordIO p = runIO p :=
  Prog.record_fst_exact answer p

/-- **Taking the stat-only lookup starts no process**: the host's run of it is
the run of an interpreter that cannot start one. -/
public theorem located_runless_exact (tool : String) :
    runIO (ToolPath.located tool) = (ToolPath.located tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.located_only tool) answer answerRunless answer_runless_exact

/-- **Resolving starts no process**, for the same reason. -/
public theorem resolve_runless_exact (tool : String) :
    runIO (ToolPath.resolve tool) = (ToolPath.resolve tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.resolve_only tool) answer answerRunless answer_runless_exact

/-- **Taking a witness starts no process**, for the same reason. -/
public theorem witness_runless_exact (tool : String) :
    runIO (ToolPath.witness tool) = (ToolPath.witness tool).runM answerRunless :=
  Prog.runM_only_exact (ToolPath.witness_only tool) answer answerRunless answer_runless_exact

end LeanTex.Cli.Host
