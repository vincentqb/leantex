module

public import LeanTex.Cli.PicCache
import LeanTex.Cli.Host
import LeanTex.Core.Flate
public import Std.Sync.Mutex
public import Std.Data.HashMap

/-! Asking a boundary tool who it is: the host half of `PicCache`'s version policy. -/

namespace LeanTex.Cli.ToolProbe

open LeanTex.Core
open LeanTex.Cli.World

/-- `probe`'s answer, asked once, the first time it is needed, however many ask at once. -/
public def once (probe : IO Bool) : BaseIO (IO Bool) := do
  let found ← Std.Mutex.new (none : Option Bool)
  return found.atomically do
    match ← get with
    | some p => pure p
    | none =>
      let p ← probe
      set (some p)
      pure p

/-- What a run has heard tools say they are, by tool and witness. -/
public abbrev Versions := Std.Mutex (Std.HashMap (String × String) String)

/-- `probe`'s answer for `tool` under `stamp`, asked once however many ask at once, a present
version remembered in `memo` and an absence asked again. -/
public def rememberedIn (memo : Versions) (tool stamp : String) (probe : IO PicCache.Tool) :
    IO PicCache.Tool :=
  memo.atomically do
    if let some version := (← get).get? (tool, stamp) then return .present version
    let answer ← probe
    if let .present version := answer then modify (·.insert (tool, stamp) version)
    return answer

/-- The first regular file `tool` reaches on PATH, relative entries anchored to the
working directory; mode bits are not read, and no run is asked. -/
public def onPath (tool : String) : IO (Option System.FilePath) := do
  return (← Host.runIO (ToolPath.resolve tool)).map System.FilePath.mk

/-- The stamp (resolved path, size, modification time) of every regular file `tool`
reaches on PATH, in order; empty when PATH reaches none. -/
public def witness (tool : String) : IO String :=
  Host.runIO (ToolPath.witness tool)

/-- Ask the tool its version, bounded and with no input, passing over candidates the OS
refuses to execute as execvp does. -/
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

/-- The tool's identity: the memo's while its witness matches, else `probe`'s, a present
version published as a checked memo under a nonempty witness. -/
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
