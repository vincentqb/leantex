import LeanTex

open LeanTex.Core

/-! Is the font cache ever stale? Two caches sit in front of the scan and
each has its own way to go stale, so both are exercised: the probe cache
(keyed per file) against an in-place replacement, and the listing cache
(keyed per directory mtime) against membership changes — a file added, a
file removed, a new subdirectory. The answer must follow the disk in every
case. Run with `lake env lean --run`. -/

def familyAt (dir path : String) : IO (Option String) := do
  let faces ← FontDb.scanRoots [dir]
  return (faces.find? (·.path == path)).map (·.family)

def familiesAt (dir : String) : IO (Array String) := do
  return FontDb.families (← FontDb.scanRoots [dir])

def main : IO UInt32 := do
  let dir := "/tmp/leantex-fontcache-check"
  let face := dir ++ "/Face.otf"
  IO.FS.createDirAll dir
  -- The faces the repository ships, so the oracle runs on any host.
  let serif ← IO.FS.readBinFile "tests/corpus/fonts/SourceSerifPro-Regular.otf"
  let sans ← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.writeBinFile face serif
  let first ← familyAt dir face
  let again ← familyAt dir face
  IO.sleep 1100  -- past mtime resolution
  -- In place, same name: the listing is unchanged, the probe key must move.
  IO.FS.writeBinFile face sans
  let after ← familyAt dir face
  -- Membership: a new file, in the root and in a fresh subdirectory, then
  -- its removal. Each changes only a directory's entries, which is exactly
  -- what the listing cache is keyed on.
  IO.sleep 1100
  IO.FS.writeBinFile (dir ++ "/Other.otf") serif
  let added := (← familiesAt dir).contains "Source Serif Pro"
  IO.sleep 1100
  IO.FS.createDirAll (dir ++ "/sub")
  IO.FS.writeBinFile (dir ++ "/sub/Third.otf") serif
  let subFound ← familyAt dir (dir ++ "/sub/Third.otf")
  IO.sleep 1100
  IO.FS.removeFile (dir ++ "/Other.otf")
  IO.FS.removeDirAll (dir ++ "/sub")
  let gone := (← familiesAt dir) == #["Open Sans"]
  IO.FS.removeDirAll dir
  IO.println s!"first={first} cached={again} after-replace={after}"
  IO.println s!"added-file-seen={added} new-subdir-seen={subFound} removed-gone={gone}"
  if first == some "Source Serif Pro" && again == first && after == some "Open Sans"
      && added && subFound == some "Source Serif Pro" && gone then
    IO.println "fontcache-check: the cache follows the disk"
    return 0
  else
    IO.println "fontcache-check: STALE"
    return 1
