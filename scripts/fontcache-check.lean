import LeanTex

open LeanTex.Core

/-! Is the font cache ever stale? Scan a directory holding one font, replace
the file with a different face under the same name, scan again. The family
reported for that path must follow the file. Run with `lake env lean --run`. -/

def familyAt (dir path : String) : IO (Option String) := do
  let faces ← FontDb.scanRoots [dir]
  return (faces.find? (·.path == path)).map (·.family)

def main : IO UInt32 := do
  let dir := "/tmp/leantex-fontcache-check"
  let face := dir ++ "/Face.otf"
  IO.FS.createDirAll dir
  -- The faces the repository ships, so the oracle runs on any host.
  IO.FS.writeBinFile face (← IO.FS.readBinFile "tests/corpus/fonts/SourceSerifPro-Regular.otf")
  let first ← familyAt dir face
  let again ← familyAt dir face
  IO.sleep 1100  -- past mtime resolution
  IO.FS.writeBinFile face (← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf")
  let after ← familyAt dir face
  IO.FS.removeDirAll dir
  IO.println s!"first={first} cached={again} after-replace={after}"
  if first == some "Source Serif Pro" && again == first && after == some "Open Sans" then
    IO.println "fontcache-check: the cache follows the file"
    return 0
  else
    IO.println "fontcache-check: STALE"
    return 1
