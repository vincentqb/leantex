module

public import LeanTex.Cli.PicCache
import LeanTex.Cli.Host
import LeanTex.Core.Flate

/-! Asking the boundary tool who it is: the effect half of PicCache's
version policy. The decisions are values there (`PicCache.probed`,
`PicCache.versionStep`) and the questions are programs in `World.ToolPath`;
here they are put to the host. `identify` takes the probe as an argument so
the one invariant that matters — a run that can reuse the remembered version
does not start the tool — is checkable with no tool installed. -/

namespace LeanTex.Cli.ToolProbe

open LeanTex.Core
open LeanTex.Cli.World

/-- The first regular file the command name reaches on PATH, including
relative and empty (working-directory) entries; a name with a slash is
itself (`ToolPath.select_exact`), and no process is started
(`ToolPath.resolve_asks_mem`). An unset PATH has a platform-defined
fallback, so supplies no identity. -/
public def onPath (tool : String) : IO (Option System.FilePath) := do
  return (← Host.runIO (ToolPath.resolve tool)).map System.FilePath.mk

/-- The witness of the executable selected above: the resolved path
(a distribution that versions its install directory changes it), the size
and the modification time (a distribution that replaces the binary in place
changes those) — the three facts the font cache already keys a face on.
Empty when PATH reaches nothing, which is a witness no memo matches, so a
machine with no tool asks again on every build and installing the tool takes
effect at once. It is taken from stats alone (`ToolPath.witness_asks_mem`). -/
public def witness (tool : String) : IO String :=
  Host.runIO (ToolPath.witness tool)

/-- Ask the tool, bounded (`ToolPath.versionBudgetMs`) and with no input.
A candidate the OS refuses to execute is passed over for the next one on
PATH, as execvp passes it (`ToolPath.probeGo_exact`). Only the exit code
decides whether there is an answer to read: a spawn that fails at `exec`
returns nonzero with whatever the forked child inherited on its stdout. -/
public def probeVersion (tool : String) : IO PicCache.Tool :=
  Host.runIO (ToolPath.version tool)

private def encodeMemo (stamp version : String) : ByteArray :=
  let payload := PicCache.versionMemo stamp version
  ("tool-version-v2\n" ++ Flate.contentKey payload.toUTF8 ++ "\n" ++ payload).toUTF8

private def decodeMemo (text : String) : Option (String × String) :=
  match text.splitOn "\n" with
  | ["tool-version-v2", checksum, stamp, version] =>
    let payload := PicCache.versionMemo stamp version
    if checksum == Flate.contentKey payload.toUTF8 then PicCache.readVersionMemo payload
    else none
  | _ => none

/-- The memo reuses the tool's identity while its witness still matches
(`PicCache.versionStep`), and `probe` runs on a miss. Concurrent misses may
each probe; each publication replaces the complete checked memo. A moved
witness forces a new probe, whose version names the next picture slots.
A witness that could not be taken is written nowhere: nothing would ever
match it. Legacy raw memos are misses: they may contain a valid-looking
prefix from an interrupted writer. -/
public def identify (memoPath : System.FilePath) (stamp : String)
    (probe : IO PicCache.Tool) : IO PicCache.Tool := do
  let memo? := match ← Host.runIO (ask (.readFile memoPath.toString)) with
    | .ok bytes => (String.fromUTF8? bytes).bind decodeMemo
    | .error _ => none
  match PicCache.versionStep memo? stamp with
  | .remembered version => return .present version
  | .probe =>
    match ← probe with
    | .present version =>
      unless stamp.isEmpty do
        discard <| Host.runIO (ask (.writeAtomic memoPath.toString (encodeMemo stamp version)))
      return .present version
    | .absent why => return .absent why

end LeanTex.Cli.ToolProbe
