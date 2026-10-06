import LeanTex.Cli.FontDiscovery

open LeanTex.Core LeanTex.Cli

/-! Font discovery's filesystem and metadata boundary. Changed file keys,
directory mtimes and classifier versions must invalidate the caches.
Current-key cache rows are trusted, including rejections and empty listings;
uncached discovery must instead read the files and leave the cache untouched.
Metadata and cmap/MATH candidates need not be fully parseable fonts.

The fonts and both caches live in fresh temporary directories. Only shipped
font bytes and invented sfnt metadata are used. Build
`LeanTex.Cli.FontDiscovery`, then run with `lake env lean --run`. -/

def familyAt (cache : System.FilePath) (dir path : String) : IO (Option String) := do
  let faces ← FontDiscovery.scanRootsIn (some cache) [dir]
  return (faces.find? (·.path == path)).map (·.family)

def familiesAt (cache : System.FilePath) (dir : String) : IO (Array String) := do
  return FontDb.families (← FontDiscovery.scanRootsIn (some cache) [dir])

private def word16 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 256), UInt8.ofNat n]⟩

private def word32 (n : Nat) : ByteArray :=
  let lower := word16 n
  word16 (n / 65536) ++ lower

private def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

private def sfnt (tables : Array (String × ByteArray)) : ByteArray := Id.run do
  let mut directory := ByteArray.empty
  let mut payload := ByteArray.empty
  for (tag, bytes) in tables do
    let offset := 12 + tables.size * 16 + payload.size
    directory := directory ++ tag.toUTF8 ++ word32 0 ++ word32 offset ++ word32 bytes.size
    payload := payload ++ bytes
  return word32 0x00010000 ++ word16 tables.size ++ zeros 6 ++ directory ++ payload

/-- Observable limits of discovery, through its ordinary caller interface.
The seeded current-key rows stand for a cache whose provenance/freshness
premise fails; they must disagree with fresh reads, not certify the bytes. -/
private def boundaryChecks (root : System.FilePath) (font : ByteArray) : IO Bool := do
  let failures ← IO.mkRef (#[] : Array String)
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (·.push name)
  let dir := root / "boundary-fonts"
  let cache := root / "boundary-cache"
  IO.FS.createDirAll dir
  IO.FS.createDirAll cache
  let path := (dir / "Face.otf").toString
  IO.FS.writeBinFile path font
  let some key ← FontDiscovery.probeKey path
    | throw <| IO.userError "fontcache-check: the boundary face cannot be stat'd"
  let probeFile := cache / FontDiscovery.probeCacheName
  let liveFamily := (← FontDiscovery.probe path).map (·.family)
  check "the boundary fixture classifies" liveFamily.isSome

  -- A negative row under a live file's key makes a cache hit observable.
  -- Merely scanning the same rejected bytes twice could hide a re-probe.
  IO.FS.writeFile probeFile (key ++ "\n")
  let rejected ← FontDiscovery.scanRootsIn (some cache) [dir.toString]
  let fresh ← FontDiscovery.scanRootsIn none [dir.toString]
  check "a current-key rejection is replayed" rejected.isEmpty
  check "bypassing the probe cache observes the font"
    (fresh.size == 1 && (fresh[0]?.map (·.family)) == liveFamily)
  check "bypassing the probe cache leaves its rows alone"
    ((← IO.FS.readFile probeFile) == key ++ "\n")
  check "cache bypass did not need a changed file key"
    ((← FontDiscovery.probeKey path) == some key)

  IO.FS.writeFile probeFile
    (key ++ "\tInvented Family\tRegular\tfalse\tfalse\tfalse\t400\n")
  let trusted ← FontDiscovery.scanRootsIn (some cache) [dir.toString]
  check "current-key classification rows are trusted"
    (trusted.size == 1 && (trusted[0]?.map (·.family)) == some "Invented Family")
  check "cached metadata does not certify the current bytes"
    ((trusted[0]?.map (·.family)) != liveFamily)
  IO.FS.writeBinFile path (font.push 0)
  check "changing size changes the file key"
    ((← FontDiscovery.probeKey path) != some key)
  check "a changed key replaces a stale classification"
    ((← familyAt cache dir.toString path) == liveFamily)

  let rejectedDir := root / "rejected-fonts"
  let rejectedPath := (rejectedDir / "Rejected.otf").toString
  IO.FS.createDirAll rejectedDir
  IO.FS.writeBinFile rejectedPath "not an sfnt".toUTF8
  let coldRejection ← FontDiscovery.scanRootsIn (some cache) [rejectedDir.toString]
  let some rejectedKey ← FontDiscovery.probeKey rejectedPath
    | throw <| IO.userError "fontcache-check: the rejected fixture cannot be stat'd"
  check "a rejected font produces no face" coldRejection.isEmpty
  check "a cold rejection writes a key-only row"
    (((← IO.FS.readFile probeFile).splitOn "\n").contains rejectedKey)
  IO.FS.writeBinFile rejectedPath font
  check "replacing rejected bytes moves their key"
    ((← FontDiscovery.probeKey rejectedPath) != some rejectedKey)
  check "a changed key retries a rejection"
    ((← familyAt cache rejectedDir.toString rejectedPath) == liveFamily)

  let md ← dir.metadata
  let emptyListing := s!"{dir}\t{md.modified.sec}.{md.modified.nsec}\n"
  let listingFile := cache / "fontdb-dirs.tsv"
  IO.FS.writeFile listingFile emptyListing
  check "a current-mtime empty listing is replayed"
    ((← FontDiscovery.scanRootsIn (some cache) [dir.toString]).isEmpty)
  let freshListing ← FontDiscovery.scanRootsIn none [dir.toString]
  check "bypassing the listing cache reads directory membership"
    (freshListing.size == 1 && (freshListing[0]?.map (·.family)) == liveFamily)
  check "bypassing the listing cache leaves its rows alone"
    ((← IO.FS.readFile listingFile) == emptyListing)

  -- Format 12 maps only A to glyph ID 1. No metrics or glyph program exists.
  let point := word32 65
  let glyph := word32 1
  let cmap := word16 0 ++ word16 1 ++ word16 3 ++ word16 10 ++ word32 12 ++
    word16 12 ++ word16 0 ++ word32 28 ++ word32 0 ++ word32 1 ++
    point ++ point ++ glyph
  let metadata := sfnt #[("head", zeros 54), ("cmap", cmap), ("MATH", word32 0)]
  let candidate := (root / "Metadata.otf").toString
  IO.FS.writeBinFile candidate metadata
  let face? ← FontDiscovery.probe candidate
  check "metadata discovery need not produce a parseable font" face?.isSome
  check "full parsing still refuses missing font tables"
    (match Font.parse metadata with
     | .error e => e == "font has no 'hhea' table"
     | .ok _ => false)
  let candidates := face?.toArray
  check "MATH probing only nominates a candidate"
    ((← FontDiscovery.firstMathFace candidates).map (·.path) == some candidate)
  check "cmap probing only nominates mapped scalars"
    ((← FontDiscovery.fallbackPicks candidates #['A', 'B']) == #[('A', candidate)])
  IO.FS.removeFile candidate
  check "a supplied face is not evidence its path still exists"
    ((← FontDiscovery.probe candidate).isNone)
  check "an unreadable math candidate is skipped"
    ((← FontDiscovery.firstMathFace candidates).isNone)
  check "an unreadable fallback candidate is skipped"
    ((← FontDiscovery.fallbackPicks candidates #['A']).isEmpty)

  -- More than one 64-file chunk, created in reverse order, with root order
  -- deliberately different from path order. Warm and fresh scans agree.
  let firstRoot := root / "z-first"
  let secondRoot := root / "a-second"
  IO.FS.createDirAll firstRoot
  IO.FS.createDirAll secondRoot
  let paths := ((List.range 70).map fun i =>
    (firstRoot / s!"Face-{100 + i}.otf").toString).toArray
  for p in paths.reverse do IO.FS.writeBinFile p metadata
  let second := (secondRoot / "Face.OTF").toString
  IO.FS.writeBinFile second metadata
  IO.FS.writeBinFile (firstRoot / "Ignored.ttc") metadata
  let expected := paths.push second
  let roots := [firstRoot.toString, secondRoot.toString]
  let cold ← FontDiscovery.scanRootsIn (some cache) roots
  let warm ← FontDiscovery.scanRootsIn (some cache) roots
  let uncached ← FontDiscovery.scanRootsIn none roots
  check "chunked discovery keeps root and sorted entry order"
    (cold.map (·.path) == expected && warm.map (·.path) == expected &&
      uncached.map (·.path) == expected)
  check "selection ties still prefer the first discovered face"
    (((FontDb.resolve cold "Embedded" {}).map (·.1.path)) == paths[0]?)

  let failures ← failures.get
  for failure in failures do IO.eprintln s!"fontcache-check: {failure}"
  IO.println s!"discovery-boundary-checks={failures.isEmpty}"
  return failures.isEmpty

private def run (root : System.FilePath) : IO UInt32 := do
  let cache := root / "cache"
  let dir := (root / "fonts").toString
  let face := dir ++ "/Face.otf"
  IO.FS.createDirAll dir
  -- The faces the repository ships, so the oracle runs on any host.
  let serif ← IO.FS.readBinFile "tests/corpus/fonts/SourceSerifPro-Regular.otf"
  let sans ← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf"
  let code ← IO.FS.readBinFile "tests/corpus/fonts/SourceCodePro-Regular.otf"
  IO.FS.writeBinFile face serif
  let beforeKey ← FontDiscovery.probeKey face
  let first ← familyAt cache dir face
  let again ← familyAt cache dir face
  IO.sleep 1100  -- past mtime resolution
  -- In place, same name: the listing is unchanged, the probe key must move.
  IO.FS.writeBinFile face sans
  let afterKey ← FontDiscovery.probeKey face
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
  let some key ← FontDiscovery.probeKey mono
    | IO.println "fontcache-check: the monospace face cannot be stat'd"; return 1
  IO.FS.writeFile (fresh / "fontdb.tsv")
    (key ++ "\tOld Classifier\tRegular\tfalse\tfalse\tfalse\t400\n")
  let monoFace := (← FontDiscovery.scanRootsIn (some fresh) [dir]).find? (·.path == mono)
  let classifierFollowed :=
    (monoFace.map fun f => (f.family, f.fixedPitch)) == some ("Source Code Pro", true)
  let wroteOwn ← (fresh / FontDiscovery.probeCacheName).pathExists
  let boundaryOk ← boundaryChecks root serif
  let keyChanged := beforeKey.isSome && afterKey.isSome && beforeKey != afterKey
  IO.println s!"first={first} cached={again} after-replace={after}"
  IO.println s!"replacement-key-changed={keyChanged}"
  IO.println s!"added-file-seen={added} new-subdir-seen={subFound} removed-gone={gone}"
  IO.println s!"old-classifier-row-ignored={classifierFollowed} wrote-{FontDiscovery.probeCacheName}={wroteOwn}"
  if first == some "Source Serif Pro" && again == first && after == some "Open Sans"
      && added && subFound == some "Source Serif Pro" && gone
      && classifierFollowed && wroteOwn && keyChanged && boundaryOk then
    IO.println "fontcache-check: invalidation and discovery boundary checks passed"
    return 0
  else
    IO.println "fontcache-check: STALE"
    return 1

def main : IO UInt32 := do
  let root ← IO.FS.createTempDir
  try run root
  finally IO.FS.removeDirAll root
