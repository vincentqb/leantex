import LeanTex

open LeanTex.Core

/-! Is the font cache ever stale? Two caches sit in front of the scan and
each has its own ways to go stale, so each is exercised: the probe cache
(keyed per file) against an in-place replacement, and against a row the
previous classifier wrote — the key names the file, not the classifier, so
only the versioned file name keeps that row out; and the listing cache
(keyed per directory mtime) against membership changes — a file added, a
file removed, a new subdirectory. The answer must follow the disk and the
classifier in every case. The fonts and both caches live in fresh temporary
directories, so no host cache is read or written and two runs cannot share
a path. Run with `lake env lean --run`. -/

def familyAt (cache : System.FilePath) (dir path : String) : IO (Option String) := do
  let faces ← FontDb.scanRootsIn (some cache) [dir]
  return (faces.find? (·.path == path)).map (·.family)

def familiesAt (cache : System.FilePath) (dir : String) : IO (Array String) := do
  return FontDb.families (← FontDb.scanRootsIn (some cache) [dir])

def main : IO UInt32 := do
  let root ← IO.FS.createTempDir
  let cache := root / "cache"
  let dir := (root / "fonts").toString
  let face := dir ++ "/Face.otf"
  IO.FS.createDirAll dir
  -- The faces the repository ships, so the oracle runs on any host.
  let serif ← IO.FS.readBinFile "tests/corpus/fonts/SourceSerifPro-Regular.otf"
  let sans ← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf"
  let code ← IO.FS.readBinFile "tests/corpus/fonts/SourceCodePro-Regular.otf"
  IO.FS.writeBinFile face serif
  let first ← familyAt cache dir face
  let again ← familyAt cache dir face
  IO.sleep 1100  -- past mtime resolution
  -- In place, same name: the listing is unchanged, the probe key must move.
  IO.FS.writeBinFile face sans
  let after ← familyAt cache dir face
  -- Membership: a new file, in the root and in a fresh subdirectory, then
  -- its removal. Each changes only a directory's entries, which is exactly
  -- what the listing cache is keyed on.
  IO.sleep 1100
  IO.FS.writeBinFile (dir ++ "/Other.otf") serif
  let added := (← familiesAt cache dir).contains "Source Serif Pro"
  IO.sleep 1100
  IO.FS.createDirAll (dir ++ "/sub")
  IO.FS.writeBinFile (dir ++ "/sub/Third.otf") serif
  let subFound ← familyAt cache dir (dir ++ "/sub/Third.otf")
  IO.sleep 1100
  IO.FS.removeFile (dir ++ "/Other.otf")
  IO.FS.removeDirAll (dir ++ "/sub")
  let gone := (← familiesAt cache dir) == #["Open Sans"]
  -- The classifier: a monospace face, and beside the cache this classifier
  -- writes, the unversioned file every earlier one wrote, holding that
  -- face's row as an offset-16 reader left it — proportional, under a
  -- family no scan answers. A fresh cache, so no row of this classifier's
  -- own stands in front of it.
  let mono := dir ++ "/Mono.otf"
  IO.FS.writeBinFile mono code
  let fresh := root / "cache-classifier"
  IO.FS.createDirAll fresh
  let some key ← FontDb.probeKey mono
    | IO.println "fontcache-check: the monospace face cannot be stat'd"; return 1
  IO.FS.writeFile (fresh / "fontdb.tsv")
    (key ++ "\tOld Classifier\tRegular\tfalse\tfalse\tfalse\t400\n")
  let monoFace := (← FontDb.scanRootsIn (some fresh) [dir]).find? (·.path == mono)
  let classifierFollowed :=
    (monoFace.map fun f => (f.family, f.fixedPitch)) == some ("Source Code Pro", true)
  let wroteOwn ← (fresh / FontDb.probeCacheName).pathExists
  IO.FS.removeDirAll root
  IO.println s!"first={first} cached={again} after-replace={after}"
  IO.println s!"added-file-seen={added} new-subdir-seen={subFound} removed-gone={gone}"
  IO.println s!"old-classifier-row-ignored={classifierFollowed} wrote-{FontDb.probeCacheName}={wroteOwn}"
  if first == some "Source Serif Pro" && again == first && after == some "Open Sans"
      && added && subFound == some "Source Serif Pro" && gone
      && classifierFollowed && wroteOwn then
    IO.println "fontcache-check: the cache follows the disk and the classifier"
    return 0
  else
    IO.println "fontcache-check: STALE"
    return 1
