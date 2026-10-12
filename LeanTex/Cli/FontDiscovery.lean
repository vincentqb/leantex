module

import LeanTex.Core.Font
public import LeanTex.Core.FontDb
import Std.Data.HashMap

/-! Filesystem boundary for font discovery. Selection consumes the resulting
`FontDb.Face` values; parsing and artifact checks must still establish what
the selected bytes can render.

Cached discovery assumes that a byte change changes the file's size or mtime,
that a relevant directory-entry change changes its directory's mtime, and
that the paths remain readable and stable during listing, stat and reads.
It also trusts accepted cache rows to come from this classifier. These are
external premises, not consequences of the selection theorems. Restoring a
timestamp, replacing equal-sized bytes without moving it, a concurrent edit,
or a forged cache row can violate them. `scanRootsIn none` bypasses both
caches; it does not lock the filesystem or retain the bytes for later parsing.

`scripts/fontcache-check.lean` exercises changed keys, directory membership,
rejected-font replay, cache bypass, scan order and metadata without a usable font.
The cache format assumes paths and names contain neither tabs nor line
breaks; unrecognized row shapes are skipped. -/

namespace LeanTex.Cli.FontDiscovery

open LeanTex.Core LeanTex.Core.FontDb

public def searchDirs : List String :=
  ["/usr/share/fonts", "/usr/local/share/fonts", "/usr/share/texmf-dist/fonts/opentype",
   "/usr/share/texmf-dist/fonts/truetype",
   -- macOS: its system faces are mostly collections, read face by face
   -- (`memberImage`).
   "/System/Library/Fonts", "/System/Library/Fonts/Supplemental", "/Library/Fonts",
   "/opt/homebrew/share/fonts"]

/-- The roots `LEANTEX_FONT_PATH` names: the engine's alone, which no other
program's font search reads. -/
public def envDirs : IO (List String) := do
  let env := (← IO.getEnv "LEANTEX_FONT_PATH").getD ""
  return (env.splitOn ":").filter (!·.isEmpty)

/-- Where else to look, from `LEANTEX_FONT_PATH` and `$HOME`. A TeX Live tree is
not always at `/usr/share`, and a user's own fonts are never there: without this
a document naming a font it demonstrably has gets told the font does not exist. -/
public def extraDirs : IO (List String) := do
  let home := (← IO.getEnv "HOME").getD ""
  let userDirs :=
    if home.isEmpty then []
    else [home ++ "/.fonts", home ++ "/.local/share/fonts", home ++ "/Library/Fonts"]
  return userDirs ++ (← envDirs)

/-- Read selected sfnt tables at their declared offsets, padding gaps with
zeros. `none` means no candidate image could be read, not that a font was
proved invalid. The image is only for metadata readers: omitted tables,
overlapping entries and short reads do not produce a validated font. -/
public def tableImage (path : String) (want : String → Bool) : IO (Option ByteArray) := do
  try
    let handle ← IO.FS.Handle.mk path .read
    let header ← handle.read 12
    let some numTables :=
      if hheader : 12 ≤ header.size then
        some ((header[4]).toNat * 256 + (header[5]).toNat)
      else none
      | return none
    if numTables == 0 || numTables > 512 then
      return none
    let dir ← handle.read (16 * numTables).toUSize
    let mut wanted : Array (String × Nat × Nat) := #[]
    for k in [0:numTables] do
      let base := 16 * k
      if hdir : base + 16 ≤ dir.size then
        let tag := String.ofList ((dir.extract base (base + 4)).toList.map
          fun c => Char.ofNat c.toNat)
        let off := (((dir[base + 8]).toNat * 256 + (dir[base + 9]).toNat) * 256 +
          (dir[base + 10]).toNat) * 256 + (dir[base + 11]).toNat
        let len := (((dir[base + 12]).toNat * 256 + (dir[base + 13]).toNat) * 256 +
          (dir[base + 14]).toNat) * 256 + (dir[base + 15]).toNat
        if want tag then
          wanted := wanted.push (tag, off, len)
    if wanted.isEmpty then
      return none
    let maxEnd := wanted.foldl (fun acc (e : String × Nat × Nat) =>
      max acc (e.2.1 + e.2.2)) 0
    if maxEnd > 8 * 1024 * 1024 then
      return none
    -- Build a sparse image: zeros everywhere except header, directory, tables.
    let mut image : ByteArray := ByteArray.empty
    image := image ++ header ++ dir
    let mut pos := 12 + dir.size
    let sorted := wanted.qsort fun a b => a.2.1 < b.2.1
    for (_, off, len) in sorted do
      if off ≥ pos then
        image := image ++ (⟨Array.replicate (off - pos) 0⟩ : ByteArray)
        handle.rewind
        discard <| handle.read off.toUSize
        let chunk ← handle.read len.toUSize
        image := image ++ chunk
        pos := off + chunk.size
    return some image
  catch _ =>
    return none

/-- Read `n` bytes forward from the handle's position and drop them, a
mebibyte at a time: a handle has no seek, and one read of the whole gap
would hold all of it. -/
private def skipBytes (h : IO.FS.Handle) (n : Nat) : IO Unit := do
  let chunk := 1024 * 1024
  let mut left := n
  for _ in [0:n / chunk + 1] do
    if left == 0 then break
    let got ← h.read (min left chunk).toUSize
    if got.isEmpty then break
    left := left - got.size

/-- The bytes `[off, off + len)` of the file `h` reads, its position `pos`:
forward from there when the range starts at or past it, else from the start
again. With the position after what was read. -/
private def readAt (h : IO.FS.Handle) (pos off len : Nat) : IO (ByteArray × Nat) := do
  let pos ← if off < pos then do h.rewind; pure 0 else pure pos
  skipBytes h (off - pos)
  let got ← h.read len.toUSize
  return (got, off + got.size)

/-- `tableImage` for face `index` of a font collection: the tables `want`
names, copied out of the collection into a standalone image with a
directory of its own (`Font.assembleSfnt`, the shape `Font.collectionMember`
gives a whole face). The handle has no seek, so it reads forward to the
collection's header, the face's directory and each wanted table in file
order, the bytes between them read and dropped. `none` for bytes that are
no collection, an index past its count, a short read, no wanted table, or
wanted tables past eight mebibytes in all. An Apple `true` face is written
with the OpenType TrueType version, as `Font.collectionMember` writes it. -/
public def memberImage (file : String) (index : Nat) (want : String → Bool) :
    IO (Option ByteArray) := do
  try
    let h ← IO.FS.Handle.mk file .read
    let header ← h.read 12
    if header.size < 12 || Ink.u32 header 0 != 0x74746366 then return none
    let count := Ink.u32 header 8
    if index ≥ count || count > 4096 then return none
    let (offs, pos) ← readAt h 12 (12 + 4 * index) 4
    if offs.size < 4 then return none
    let base := Ink.u32 offs 0
    let (dirHead, pos) ← readAt h pos base 12
    if dirHead.size < 12 then return none
    let numTables := Ink.u16 dirHead 4
    if numTables == 0 || numTables > 512 then return none
    let (dir, pos) ← readAt h pos (base + 12) (16 * numTables)
    if dir.size < 16 * numTables then return none
    let mut wanted : Array (Nat × Nat × Nat × Nat) := #[]
    for k in [0:numTables] do
      let e := 16 * k
      let tag := String.ofList ((dir.extract e (e + 4)).toList.map fun c => Char.ofNat c.toNat)
      if want tag then
        wanted := wanted.push (Ink.u32 dir e, Ink.u32 dir (e + 4), Ink.u32 dir (e + 8),
          Ink.u32 dir (e + 12))
    if wanted.isEmpty || wanted.foldl (fun acc t => acc + t.2.2.2) 0 > 8 * 1024 * 1024 then
      return none
    let mut pos := pos
    let mut tables : Array (Nat × Nat × ByteArray) := #[]
    for (tag, sum, off, len) in wanted.qsort (fun a b => a.2.2.1 < b.2.2.1) do
      let (bytes, after) ← readAt h pos off len
      if bytes.size < len then return none
      pos := after
      tables := tables.push (tag, sum, bytes)
    let version := if Ink.u32 dirHead 0 == 0x74727565 then 0x00010000 else Ink.u32 dirHead 0
    return some (Font.assembleSfnt version tables)
  catch _ =>
    return none

/-- The faces of every font file under `files`, in order: a standalone
file is its own face's path, and a collection is each of its faces'
(`FontDb.memberPath`), as many as its header counts where the file holds
that many offsets — the count `Font.collectionCount` reads. A collection
whose header cannot be read, or counts no face, more than 4096, or more
offsets than the file holds, holds none. -/
private def facePaths (files : Array String) : IO (Array String) := do
  let mut out : Array String := #[]
  for f in files do
    if isCollectionFile f then
      let (header, size) ← try
          let h ← IO.FS.Handle.mk f .read
          pure (← h.read 12, (← System.FilePath.metadata f).byteSize.toNat)
        catch _ => pure (ByteArray.empty, 0)
      let count := Ink.u32 header 8
      if header.size == 12 && Ink.u32 header 0 == 0x74746366 && 0 < count && count ≤ 4096 &&
          12 + 4 * count ≤ size then
        for i in [0:count] do
          out := out.push (memberPath f i)
    else
      out := out.push f
  return out

/-- A face's `tableImage`, whichever file holds it: a collection face's
from its collection (`memberImage`), any other face's from its own file. -/
public def faceImage (path : String) (want : String → Bool) : IO (Option ByteArray) := do
  match splitMember path with
  | some (file, index) => memberImage file index want
  | none => tableImage path want

/-- The bytes of a face's own font file: a collection face copied out of its
collection as the standalone file `Font.parse` reads
(`Font.collectionMember`), any other face's file as it stands. -/
public def faceBytes (path : String) : IO (Except String ByteArray) := do
  match splitMember path with
  | some (file, index) =>
    match ← (IO.FS.readBinFile file).toBaseIO with
    | .ok data => return Font.collectionMember data index
    | .error e => return .error (toString e)
  | none =>
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok data => return .ok data
    | .error e => return .error (toString e)

/-- Read just enough of a font file to classify it: the table directory, then
the `name`, `OS/2`, `head`, and `post` tables. Full files are large (a
megabyte each is common) and a scan touches every installed face — `hmtx`
and `cmap` are what make that expensive, and classification needs neither,
so `probe` calls `classify` rather than `parse`. -/
public def probe (path : String) : IO (Option Face) := do
  let some image ← faceImage path
    (fun tag => tag == "name" || tag == "OS/2" || tag == "head" || tag == "post")
    | return none
  match Font.classify image with
  | .ok f =>
    return some {
      path := path
      family := f.family
      subfamily := f.subfamily
      bold := f.isBold
      italic := f.isItalic
      fixedPitch := f.isFixedPitch
      weight := f.weight
    }
  | .error _ => return none

/-! ## The probe cache

The classification of each file is cached by path, size and mtime. A changed
key is probed again; an absent or unrecognized row is a miss. Both successful
classifications and `none` results are replayed, including transient read
failures whose key has not changed. This is a metadata cache, not a content
hash or an authenticated record: a well-formed row under the current key is
trusted even when it disagrees with the bytes. A caller needing a fresh
observation can disable the cache with `scanRootsIn none`.

The key names the file and not the classifier, and binaries of every
vintage share the cache directory, so the classifier's version is in the
file's name (`probeCacheName`): a row is read only by the classifier that
wrote it. A version line inside one shared file would not hold that: an
older binary rewrites the file without the lines it cannot parse, the line
goes, and each such rewrite would cost the newer binary a full rescan. So
each version keeps a file of its own, and the unversioned `fontdb.tsv`
every earlier classifier wrote is never read. -/

/-- `$XDG_CACHE_HOME/leantex`, or `~/.cache/leantex`; none without a home. -/
public def cacheDir : IO (Option System.FilePath) := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some d => pure (some (System.FilePath.mk d))
    | none => match ← IO.getEnv "HOME" with
      | some h => pure (some (System.FilePath.mk h / ".cache"))
      | none => pure none
  return base.map (· / "leantex")

/-- The probe cache's file name, which carries `Font.classifierVersion`. -/
public def probeCacheName : String := s!"fontdb-{Font.classifierVersion}.tsv"

/-- One line per file, tab-separated: the key (path, size, mtime joined by
tabs), then the classification — or nothing after the key for a file `probe`
rejected, so a rejected font is not read again on every run. Fields use the
delimiter premise stated at this module's boundary. -/
private def faceLine (key : String) (f : Option Face) : String :=
  match f with
  | some f => String.intercalate "\t" [key, f.family, f.subfamily,
      toString f.bold, toString f.italic, toString f.fixedPitch, toString f.weight]
  | none => key

private def parseLine (line : String) : Option (String × Option Face) :=
  match line.splitOn "\t" with
  | [path, size, mtime, family, sub, bold, italic, fixed, weight] =>
    some (path ++ "\t" ++ size ++ "\t" ++ mtime, some
      { path, family, subfamily := sub, bold := bold == "true", italic := italic == "true"
        fixedPitch := fixed == "true", weight := weight.toNat?.getD 400 })
  | [path, size, mtime] => some (path ++ "\t" ++ size ++ "\t" ++ mtime, none)
  | _ => none

private def fileKey (path : String) : IO (Option (String × String)) := do
  try
    let md ← (System.FilePath.mk (faceFile path)).metadata
    return some (toString md.byteSize, s!"{md.modified.sec}.{md.modified.nsec}")
  catch _ => return none

/-- A file's probe-cache key as the scan spells it — path, size and mtime,
tab-joined — so a check can write the row a given classifier would have
left. `none` for a file that cannot be stat'd. -/
public def probeKey (path : String) : IO (Option String) := do
  return (← fileKey path).map fun (size, mtime) => path ++ "\t" ++ size ++ "\t" ++ mtime

/-! ## The listing cache

Each directory's listing is cached by its own mtime. On filesystems that
advance it for membership changes, adding, removing or renaming an entry
invalidates the listing. Editing a font in place is handled separately by
its file key. Timestamp preservation or coarse resolution can hide a change;
the scan is not an atomic snapshot. A directory read failure is treated as
an empty listing and is retried when its key changes or caches are bypassed.

A listing records which entries are font files, an answer of the walk's
filter, so the filter's extensions are in the file's name
(`listingCacheName`): a listing is read only by a walk that keeps the same
files, and the unnamed `fontdb-dirs.tsv` every earlier walk wrote is never
read. -/

/-- The listing cache's file name, which carries the extensions the walk
keeps, `FontDb.fontExtensions` and `FontDb.collectionExtensions`: a listing
an earlier walk wrote, which skipped collections, is never read. -/
public def listingCacheName : String :=
  s!"fontdb-dirs-{"-".intercalate (FontDb.fontExtensions ++ FontDb.collectionExtensions)}.tsv"

/-- One line per directory: path, mtime, then each entry in sorted order
prefixed `F` (a font file) or `D` (a subdirectory). Entries the walk skips
(non-font files) are not recorded; order is kept because resolution breaks
ties by scan order. -/
private def dirLine (path mtime : String) (entries : Array (Bool × String)) : String :=
  String.intercalate "\t" (path :: mtime :: entries.toList.map fun (isFont, n) =>
    (if isFont then "F" else "D") ++ n)

private def parseDirLine (line : String) :
    Option (String × String × Array (Bool × String)) := Id.run do
  match line.splitOn "\t" with
  | path :: mtime :: rest =>
    if path.isEmpty || mtime.isEmpty then
      return none
    let mut entries : Array (Bool × String) := #[]
    for e in rest do
      if e.startsWith "F" then
        entries := entries.push (true, (e.drop 1).toString)
      else if e.startsWith "D" then
        entries := entries.push (false, (e.drop 1).toString)
      else
        return none
    return some (path, mtime, entries)
  | _ => return none

/-- The walk behind `scanRoots`, through the listing cache. Structural on
`depth`: filesystem trees can contain symlink cycles. The scan visits six
directory levels, including the root; deeper entries are outside its search.
Accumulates the font files found, the listing of every directory
visited (for the cache rewrite), and whether any directory had to be listed
fresh. Listings are sorted: `readDir` returns filesystem order, which
differs between hosts, and resolution breaks ties by scan order. -/
private def walkCached (known : Std.HashMap String (String × Array (Bool × String))) :
    Nat → System.FilePath → Array String →
    Array (String × String × Array (Bool × String)) → Bool →
    IO (Array String × Array (String × String × Array (Bool × String)) × Bool)
  | 0, _, files, seen, dirty => pure (files, seen, dirty)
  | depth + 1, dir, files, seen, dirty => do
    match ← dir.metadata.toBaseIO with
    | .error _ => pure (files, seen, dirty)
    | .ok md =>
      let key := dir.toString
      let mtime := s!"{md.modified.sec}.{md.modified.nsec}"
      let hit := match known[key]? with
        | some (m, es) => if m == mtime then some es else none
        | none => none
      let (entries, freshlyListed) ← match hit with
        | some es => pure (es, false)
        | none => do
          let raw := (← try dir.readDir catch _ => pure #[]).qsort
            fun a b => a.fileName < b.fileName
          let mut es : Array (Bool × String) := #[]
          for e in raw do
            if hasFontExtension e.fileName || isCollectionFile e.fileName then
              es := es.push (true, e.fileName)
            else if ← e.path.isDir then
              es := es.push (false, e.fileName)
          pure (es, true)
      let mut files := files
      let mut seen := seen.push (key, mtime, entries)
      let mut dirty := dirty || freshlyListed
      for (isFont, name) in entries do
        if isFont then
          files := files.push (dir / name).toString
        else
          let (f, s, d) ← walkCached known depth (dir / name) files seen dirty
          files := f
          seen := s
          dirty := d
      pure (files, seen, dirty)

/-- The built-in locations plus `dirs`, in resolution order. -/
public def systemRoots (dirs : List String := []) : IO (List String) := do
  return searchDirs ++ (← extraDirs) ++ dirs

/-- The faces within the bounded walk of exactly `roots`, classified, in
root order then sorted directory-entry order. Both caches live under
`cache` (none: every run a fresh walk and probe). Equality with a fresh scan
depends on the filesystem and cache premises stated above. Probing opens and
reads each uncached file, so chunks of files are probed in parallel; joining
in chunk order keeps the face array in sequential order, which matters
because resolution prefers earlier faces on ties. -/
public def scanRootsIn (cache : Option System.FilePath) (roots : List String) :
    IO (Array Face) := do
  -- The walk, through the listing cache: a stat per unchanged directory.
  let dirsFile := cache.map (· / listingCacheName)
  let mut knownDirs : Std.HashMap String (String × Array (Bool × String)) := {}
  if let some df := dirsFile then
    if ← df.pathExists then
      let text ← try IO.FS.readFile df catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (path, mtime, entries) := parseDirLine line then
          knownDirs := knownDirs.insert path (mtime, entries)
  let mut files : Array String := #[]
  let mut seenDirs : Array (String × String × Array (Bool × String)) := #[]
  let mut dirsDirty := false
  for d in roots do
    let p := System.FilePath.mk d
    if ← p.pathExists then
      let (f, s, dirty) ← walkCached knownDirs 6 p files seenDirs dirsDirty
      files := f
      seenDirs := s
      dirsDirty := dirty
  -- Merged, not replaced: a scan of one small root (a document's own font
  -- directory, the test corpus) must not evict what other roots cost to list.
  if dirsDirty then
    if let some df := dirsFile then
      let mut merged := knownDirs
      for (k, m, es) in seenDirs do
        merged := merged.insert k (m, es)
      try
        if let some parent := df.parent then IO.FS.createDirAll parent
        IO.FS.writeFile df (String.intercalate "\n"
          (merged.toList.map fun (k, m, es) => dirLine k m es) ++ "\n")
      catch _ => pure ()
  -- A collection is the faces it holds, each probed and cached on its own.
  files ← facePaths files
  -- What the cache remembers, keyed by path + size + mtime, in the file
  -- this classifier's version names.
  let cacheFile := cache.map (· / probeCacheName)
  let mut known : Std.HashMap String (Option Face) := {}
  if let some cf := cacheFile then
    if ← cf.pathExists then
      let text ← try IO.FS.readFile cf catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (key, face) := parseLine line then
          known := known.insert key face
  -- Hits come from the cache; misses are probed in parallel chunks, in
  -- listing order either way so resolution's tie-breaking is unchanged.
  -- The per-file keys are stats, thousands of them and nothing else touching
  -- the disk while they run, so they go in parallel chunks too.
  let chunk := 64
  let mut keyed : Array (String × Option (String × String)) := #[]
  let mut keyTasks : Array (Task (Except IO.Error
      (Array (String × Option (String × String))))) := #[]
  for c in [0:(files.size + chunk - 1) / chunk] do
    let slice := files.extract (c * chunk) ((c + 1) * chunk)
    keyTasks := keyTasks.push (← IO.asTask do
      let mut out : Array (String × Option (String × String)) := #[]
      for f in slice do
        out := out.push (f, ← fileKey f)
      return out)
  for t in keyTasks do
    match t.get with
    | .ok out => keyed := keyed ++ out
    | .error e => throw e
  let mut toProbe : Array (Nat × String) := #[]
  let mut result : Array (Option Face) := Array.replicate files.size none
  for h : i in [0:keyed.size] do
    let (f, k?) := keyed[i]
    match k? with
    | some (size, mtime) =>
      match known[f ++ "\t" ++ size ++ "\t" ++ mtime]? with
      | some face? => result := result.set! i face?
      | none => toProbe := toProbe.push (i, f)
    | none => toProbe := toProbe.push (i, f)
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × Option Face)))) := #[]
  for c in [0:(toProbe.size + chunk - 1) / chunk] do
    let slice := toProbe.extract (c * chunk) ((c + 1) * chunk)
    tasks := tasks.push (← IO.asTask do
      let mut out : Array (Nat × Option Face) := #[]
      for (i, file) in slice do
        out := out.push (i, ← probe file)
      return out)
  for t in tasks do
    match t.get with
    | .ok out => for (i, face?) in out do result := result.set! i face?
    | .error e => throw e
  -- Rewrite the cache only when something was probed: the common case reads
  -- one file and writes none. Merged like the listing cache, so probing a
  -- new face under one root keeps every other root's classifications.
  if !toProbe.isEmpty then
    if let some cf := cacheFile then
      let mut merged := known
      for (entry, face?) in keyed.zip result do
        match entry with
        | (path, some (size, mtime)) =>
          merged := merged.insert (path ++ "\t" ++ size ++ "\t" ++ mtime) face?
        | _ => pure ()
      try
        if let some parent := cf.parent then IO.FS.createDirAll parent
        IO.FS.writeFile cf (String.intercalate "\n"
          (merged.toList.map fun (key, face?) => faceLine key face?) ++ "\n")
      catch _ => pure ()
  return result.filterMap id

/-- `scanRootsIn` through the host's own cache directory (`cacheDir`). -/
public def scanRoots (roots : List String) : IO (Array Face) := do
  scanRootsIn (← cacheDir) roots

/-- Scan the built-in locations plus `dirs`, within the same depth bound. -/
public def scan (dirs : List String := []) : IO (Array Face) := do
  scanRoots (← systemRoots dirs)

/-- The first face with a readable MATH candidate image under `faceLt`.
This probes metadata only; the caller must parse the selected file and check
its math data before using it. `none` also covers unreadable candidates. -/
public def firstMathFace (faces : Array Face) : IO (Option Face) := do
  for f in faces.qsort faceLt do
    if (← faceImage f.path (· == "MATH")).isSome then
      return some f
  return none

/-- The math face for a document that declares none: the body family's
designed companion when the host has it (with its table row), else the
first MATH-table candidate, else `none`. A companion match comes solely from
the supplied family metadata; it is not evidence of a usable MATH table.
The driver and test harness share this provisional decision. -/
public def pickMathFace (faces : Array Face) (body : String) :
    IO (Option (Face × Option Pairing)) := do
  match pickCompanion faces body with
  | some (row, face) => return some (face, some row)
  | none => return (← firstMathFace faces).map ((·, none))

/-- For each needed scalar, a candidate whose cmap maps it to a glyph ID.
This does not verify glyph outlines, actual ink or successful full parsing.
The order is documented, never scan luck: candidates are every scanned
face sorted by family name (normalised), upright before italic, weight
nearest regular, then subfamily and path — and the first whose cmap holds
the scalar wins. Only candidate cmaps are read, and only until every scalar
has a candidate; a scalar with no mapping found is absent from the result. -/
public def fallbackPicks (faces : Array Face) (needed : Array Char) :
    IO (Array (Char × String)) := do
  let sorted := faces.qsort faceLt
  let mut remaining := needed
  let mut out : Array (Char × String) := #[]
  for f in sorted do
    if remaining.isEmpty then
      break
    let some image ← faceImage f.path (· == "cmap") | continue
    let ranges := Font.cmapRanges image
    if ranges.isEmpty then
      continue
    let mut still : Array Char := #[]
    for c in remaining do
      if (Font.gidIn ranges c).isSome then
        out := out.push (c, f.path)
      else
        still := still.push c
    remaining := still
  return out

/-- `fallbackPicks` with the document's own faces outranking the host's:
a face under a `\fonts{ dir = ... }` the document ships answers first for
every scalar its cmap maps, and only what it leaves uncovered goes to the full
scan. Without this a host face could displace a shipped one in the
documented pick order — the site port's shipped icon faces lost to a TeX
Live FontAwesome — and "a document that carries its fonts renders the
same on every host" would be false exactly for fallback-resolved
scalars. -/
public def fallbackPicksPreferring (preferred : String → Bool) (faces : Array Face)
    (needed : Array Char) : IO (Array (Char × String)) := do
  let docFaces := faces.filter (fun f => preferred f.path)
  let first ← fallbackPicks docFaces needed
  let got := first.map (·.1)
  let rest := needed.filter (fun c => !got.contains c)
  return first ++ (← fallbackPicks faces rest)

end LeanTex.Cli.FontDiscovery
