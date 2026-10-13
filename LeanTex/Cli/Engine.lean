module

public import LeanTex.Cli.World
import LeanTex.Cli.Host

/-! The engine's identity, which keys every cache of the engine's own answers. -/

namespace LeanTex.Cli.Engine

/-- An engine binary's identity: its resolved path, size and modification time. -/
public def identity (st : World.Stat) : String :=
  s!"{st.real}\u0000{st.size}\u0000{st.mtimeSec}.{st.mtimeNsec}"

/-- The identity this process read, once. -/
private initialize processEngine : IO.Ref (Option (Option String)) ← IO.mkRef none

/-- The stat of the image this process runs: `/proc/self/exe`, else the binary at `path`.
-/
public def imageStat (path : String) : World.Prog (Option World.Stat) :=
  .ask (.stat "/proc/self/exe") fun
    | .ok st => .pure (some st)
    | .error _ => .ask (.stat path) fun
      | .ok st => .pure (some st)
      | .error _ => .pure none

/-- The running engine's identity, read once per process; `none` where the image cannot be
stated, and then no cache keyed by it is read or written. -/
public def engineId : IO (Option String) := do
  if let some known ← processEngine.get then return known
  let read ← match ← IO.appPath.toBaseIO with
    | .ok path => pure ((← Host.runIO (imageStat path.toString)).map identity)
    | .error _ => pure none
  processEngine.set (some read)
  return read

public structure Cache where
  dir : System.FilePath
  engine : String

/-- The running engine's cache in `dir`; none without a directory or an engine identity.
-/
public def cache (dir : Option System.FilePath) : IO (Option Cache) := do
  let some dir := dir | return none
  let some engine ← engineId | return none
  return some { dir, engine }

end LeanTex.Cli.Engine
