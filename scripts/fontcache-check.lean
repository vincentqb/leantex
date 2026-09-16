import LeanTex

open LeanTex.Core

/-! Is the font cache ever stale? Scan a directory holding one font, replace
the file with a different face under the same name, scan again. The family
reported for that path must follow the file. Run with `lake env lean --run`. -/

def familyAt (dir path : String) : IO (Option String) := do
  let faces ← FontDb.scan [dir]
  return (faces.find? (·.path == path)).map (·.family)

def main : IO UInt32 := do
  let dir := "/tmp/leantex-fontcache-check"
  let face := dir ++ "/Face.otf"
  IO.FS.createDirAll dir
  IO.FS.writeBinFile face (← IO.FS.readBinFile "/usr/share/fonts/urw-base35/NimbusRoman-Regular.otf")
  let first ← familyAt dir face
  let again ← familyAt dir face
  IO.sleep 1100  -- past mtime resolution
  IO.FS.writeBinFile face (← IO.FS.readBinFile "/usr/share/fonts/dejavu/DejaVuSans.ttf")
  let after ← familyAt dir face
  IO.FS.removeDirAll dir
  IO.println s!"first={first} cached={again} after-replace={after}"
  if first == some "Nimbus Roman" && again == first && after == some "DejaVu Sans" then
    IO.println "fontcache-check: the cache follows the file"
    return 0
  else
    IO.println "fontcache-check: STALE"
    return 1
