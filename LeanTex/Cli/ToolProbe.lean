module

public import LeanTex.Cli.PicCache
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.RunBounded
import LeanTex.Core.Flate

/-! Asking the boundary tool who it is: the effect half of PicCache's
version policy. The decisions are values there (`PicCache.probed`,
`PicCache.versionStep`); here is the spawn, the stat, and the memo file.
`identify` takes the probe as an argument so the one invariant that matters
— a run that can reuse the remembered version does not start the tool — is
checkable with no tool installed. -/

namespace LeanTex.Cli.ToolProbe

open LeanTex.Core

/-- The first executable regular file on PATH, including relative and
empty (current-directory) entries. Explicit paths get the same check.
An unset PATH has a platform-defined fallback, so supplies no identity. -/
public def onPath (tool : String) : IO (Option System.FilePath) := do
  let mut candidates := #[tool]
  unless tool.contains '/' do
    let some path ← IO.getEnv "PATH" | return none
    candidates := (path.splitOn ":").toArray.map
      (fun dir => (System.FilePath.mk (if dir.isEmpty then "." else dir) / tool).toString)
  -- POSIX test asks the OS about execution rights, including ACLs. Keep the
  -- whole lookup bounded (one second plus 100 ms cleanup); an incomplete
  -- lookup grants no identity. Candidate paths are arguments, never code.
  let got ← RunBounded.runBounded "/bin/sh"
    (#["-c", "for candidate do\n\
if test -f \"$candidate\" && test -x \"$candidate\"; then\n\
  printf '%s' \"$candidate\"; exit 0\n\
fi\n\
done\n\
exit 1", "tool-probe"] ++ candidates) (← IO.currentDir) 1000 100
  return if got.ran == .exited 0 then some (System.FilePath.mk got.out) else none

/-- The witness of the executable selected above: the resolved path
(a distribution that versions its install directory changes it), the size
and the modification time (a distribution that replaces the binary in place
changes those) — the three facts the font cache already keys a face on.
Empty when PATH reaches nothing or its cwd/filesystem lookup fails, which
is a witness no memo matches, so a machine with no tool asks again on every
build and installing the tool takes effect at once. -/
public def witness (tool : String) : IO String := do
  try
    match ← onPath tool with
    | none => return ""
    | some p =>
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
public def probeVersion (tool : String) : IO PicCache.Tool := do
  let (ran, said) ← try
      let out ← IO.Process.output { cmd := tool, args := #["--version"] }
      pure (PicCache.Ran.exited out.exitCode.toNat, out.stdout)
    catch e =>
      pure (PicCache.Ran.unstarted (toString e), "")
  return PicCache.probed ran (((said.splitOn "\n").headD "").trimAscii.toString)

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
  let memo? ← try
      pure (decodeMemo (← IO.FS.readFile memoPath))
    catch _ => pure (none : Option (String × String))
  match PicCache.versionStep memo? stamp with
  | .remembered version => return .present version
  | .probe =>
    match ← probe with
    | .present version =>
      unless stamp.isEmpty do
        try AtomicFile.write memoPath (encodeMemo stamp version)
        catch _ => pure ()
      return .present version
    | .absent why => return .absent why

end LeanTex.Cli.ToolProbe
