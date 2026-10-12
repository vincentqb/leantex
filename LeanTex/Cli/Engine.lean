module

public import LeanTex.Cli.World
import LeanTex.Cli.Host

/-! The engine's identity, as every cache of the engine's own answers keys
them: the flate streams, the image plans, the converters' faces and the
figure faces are each a function of their input and of the engine that
computed them, so each slot holds the identity of the engine that wrote it
(`SlotRecord.lookup_exact`, `FigureFace.lookup_exact`) and another engine's
slot is a miss. The release version is no such identity: it names every
build of one release alike. -/

namespace LeanTex.Cli.Engine

/-- An engine binary's identity from its stat: its resolved path, its size
and its modification time. A rebuild moves the time, a build elsewhere the
path; what keeps all three is read as the binary it replaced
(`engine-identity`). -/
public def identity (st : World.Stat) : String :=
  s!"{st.real}\u0000{st.size}\u0000{st.mtimeSec}.{st.mtimeNsec}"

/-- The identity this process read, once. -/
private initialize processEngine : IO.Ref (Option (Option String)) ← IO.mkRef none

/-- The image a process runs, stated: `/proc/self/exe` where the system has
it, else the binary at `path`, the one the process was started from. -/
public def imageStat (path : String) : World.Prog (Option World.Stat) :=
  .ask (.stat "/proc/self/exe") fun
    | .ok st => .pure (some st)
    | .error _ => .ask (.stat path) fun
      | .ok st => .pure (some st)
      | .error _ => .pure none

/-- The running engine's identity: `identity` of the image the process
runs (`imageStat`), read once per process and kept, so a long run whose
binary is rebuilt under it keeps writing as the engine it is — `main` reads
it first. `none` where the image cannot be stated, a binary replaced before
the read included, and then no cache keyed by it is read or written. -/
public def engineId : IO (Option String) := do
  if let some known ← processEngine.get then return known
  let read ← match ← IO.appPath.toBaseIO with
    | .ok path => pure ((← Host.runIO (imageStat path.toString)).map identity)
    | .error _ => pure none
  processEngine.set (some read)
  return read

/-- A cache of the engine's own answers: where it stands, and the engine
whose answers it serves (`engineId`). -/
public structure Cache where
  dir : System.FilePath
  engine : String

/-- The running engine's cache in `dir`, or none where there is no
directory or the engine cannot be stated. -/
public def cache (dir : Option System.FilePath) : IO (Option Cache) := do
  let some dir := dir | return none
  let some engine ← engineId | return none
  return some { dir, engine }

end LeanTex.Cli.Engine
