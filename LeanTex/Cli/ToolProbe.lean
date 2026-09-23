import LeanTex.Cli.PicCache

/-! Asking the boundary tool who it is: the effect half of PicCache's
version policy. The decisions are values there (`PicCache.probed`,
`PicCache.versionStep`); here is the spawn, the stat, and the memo file.
`identify` takes the probe as an argument so the one invariant that matters
— a run that can reuse the remembered version does not start the tool — is
checkable with no tool installed. -/

namespace LeanTex.Cli.ToolProbe

open LeanTex.Core

/-- The file PATH would reach for this tool name, or nothing when no entry
holds it. A name with a separator in it is a path already and is taken as
one. -/
def onPath (tool : String) : IO (Option System.FilePath) := do
  if tool.contains '/' then
    let p := System.FilePath.mk tool
    return if ← p.pathExists then some p else none
  let entries := ((← IO.getEnv "PATH").getD "").splitOn ":"
  for dir in entries do
    unless dir.isEmpty do
      let p := System.FilePath.mk dir / tool
      if ← p.pathExists then return some p
  return none

/-- The stat-only witness of which binary is installed: the resolved path
(a distribution that versions its install directory changes it), the size
and the modification time (a distribution that replaces the binary in place
changes those) — the three facts the font cache already keys a face on.
Empty when PATH reaches nothing, which is a witness no memo matches, so a
machine with no tool asks again on every build and installing the tool
takes effect at once. -/
def witness (tool : String) : IO String := do
  match ← onPath tool with
  | none => return ""
  | some p =>
    try
      let real ← IO.FS.realPath p
      let md ← p.metadata
      return String.intercalate "\t"
        [real.toString, toString md.byteSize, toString md.modified.sec,
          toString md.modified.nsec]
    catch _ => return ""

/-- Ask the tool. Only the exit code decides whether there is an answer to
read: a spawn that reaches `exec` and fails there returns nonzero with
whatever the forked child inherited on its stdout, so reading the version
without reading the code reads the parent's own output back as a tool
identity. -/
def probeVersion (tool : String) : IO PicCache.Tool := do
  let (ran, said) ← try
      let out ← IO.Process.output { cmd := tool, args := #["--version"] }
      pure (PicCache.Ran.exited out.exitCode.toNat, out.stdout)
    catch e =>
      pure (PicCache.Ran.unstarted (toString e), "")
  return PicCache.probed ran (((said.splitOn "\n").headD "").trimAscii.toString)

/-- The tool's identity, asked at most once per tool binary rather than
once per build: the memo beside the slots answers when its witness still
matches (`PicCache.versionStep`), and `probe` runs when it does not. What
the tool says is written back under the witness it was observed with, so
the next build reuses it and an upgraded tool — a moved witness — is asked
again and re-renders every picture. A witness that could not be taken is
written nowhere: nothing would ever match it. -/
def identify (memoPath : System.FilePath) (stamp : String)
    (probe : IO PicCache.Tool) : IO PicCache.Tool := do
  let memo? ← try
      pure (PicCache.readVersionMemo (← IO.FS.readFile memoPath))
    catch _ => pure (none : Option (String × String))
  match PicCache.versionStep memo? stamp with
  | .remembered version => return .present version
  | .probe =>
    match ← probe with
    | .present version =>
      unless stamp.isEmpty do
        try IO.FS.writeFile memoPath (PicCache.versionMemo stamp version)
        catch _ => pure ()
      return .present version
    | .absent why => return .absent why

end LeanTex.Cli.ToolProbe
