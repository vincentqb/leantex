module

import LeanTex.Core.Font
public import LeanTex.Core.FontDb
import Std.Data.HashMap

/-! Filesystem font discovery: the bounded scan of font roots into `FontDb.Face` values,
cached by file and directory keys that `scanRootsIn none` bypasses. -/

namespace LeanTex.Cli.FontDiscovery

open LeanTex.Core LeanTex.Core.FontDb

public def searchDirs : List String :=
  ["/usr/share/fonts", "/usr/local/share/fonts", "/usr/share/texmf-dist/fonts/opentype",
   "/usr/share/texmf-dist/fonts/truetype",
   -- macOS system faces are mostly collections, read face by face.
   "/System/Library/Fonts", "/System/Library/Fonts/Supplemental", "/Library/Fonts",
   "/opt/homebrew/share/fonts"]

/-- The roots `LEANTEX_FONT_PATH` names: the engine's alone, which no other
program's font search reads. -/
public def envDirs : IO (List String) := do
  let env := (← IO.getEnv "LEANTEX_FONT_PATH").getD ""
  return (env.splitOn ":").filter (!·.isEmpty)

/-- Further roots from `LEANTEX_FONT_PATH` and `$HOME`, where a TeX tree or the user's own
fonts may stand. -/
public def extraDirs : IO (List String) := do
  let home := (← IO.getEnv "HOME").getD ""
  let userDirs :=
    if home.isEmpty then []
    else [home ++ "/.fonts", home ++ "/.local/share/fonts", home ++ "/Library/Fonts"]
  return userDirs ++ (← envDirs)

/-- Selected sfnt tables read at their declared offsets into a zero-padded image for
metadata readers; `none` when no candidate image could be read. -/
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

/-- Read and drop `n` bytes a mebibyte at a time, since a handle has no seek. -/
private def skipBytes (h : IO.FS.Handle) (n : Nat) : IO Unit := do
  let chunk := 1024 * 1024
  let mut left := n
  for _ in [0:n / chunk + 1] do
    if left == 0 then break
    let got ← h.read (min left chunk).toUSize
    if got.isEmpty then break
    left := left - got.size

/-- The bytes `[off, off + len)` of the file `h` reads from position `pos`, rewinding when
the range starts before it, with the position after the read. -/
private def readAt (h : IO.FS.Handle) (pos off len : Nat) : IO (ByteArray × Nat) := do
  let pos ← if off < pos then do h.rewind; pure 0 else pure pos
  skipBytes h (off - pos)
  let got ← h.read len.toUSize
  return (got, off + got.size)

/-- `tableImage` for face `index` of a font collection, copied into a standalone image;
`none` for no collection, an index past its count, a short read, no wanted table, or
wanted tables past eight mebibytes. -/
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

/-- The face paths of the font files `files`, in order: a standalone file is its own face,
a collection each face its header counts, and a collection whose header is unreadable or
counts none or more than 4096 holds none. -/
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

/-- Classify a font file from its table directory and its `name`, `OS/2`, `head` and
`post` tables alone. -/
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

/-- One cache line per file: the tab-joined key (path, size, mtime), then the
classification, or nothing for a rejected file; paths and names hold no tab or line break.
-/
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

/-- A file's probe-cache key as the scan spells it, or `none` for a file that cannot be
stat'd. -/
public def probeKey (path : String) : IO (Option String) := do
  return (← fileKey path).map fun (size, mtime) => path ++ "\t" ++ size ++ "\t" ++ mtime

/-- The listing cache's file name, which carries the extensions the walk keeps. -/
public def listingCacheName : String :=
  s!"fontdb-dirs-{"-".intercalate (FontDb.fontExtensions ++ FontDb.collectionExtensions)}.tsv"

/-- One line per directory: path, mtime, then each sorted entry prefixed `F` (a font file)
or `D` (a subdirectory). -/
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

/-- The walk behind `scanRoots`, six directory levels deep through the listing cache: the
font files found, every listing visited, and whether any was listed fresh. -/
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

/-- The classified faces within the bounded walk of exactly `roots`, in root order then
sorted entry order, cached under `cache` (none: a fresh walk and probe). -/
public def scanRootsIn (cache : Option System.FilePath) (roots : List String) :
    IO (Array Face) := do
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
  -- Merged, not replaced, so a scan of one root keeps every other root's listings.
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
  files ← facePaths files
  let cacheFile := cache.map (· / probeCacheName)
  let mut known : Std.HashMap String (Option Face) := {}
  if let some cf := cacheFile then
    if ← cf.pathExists then
      let text ← try IO.FS.readFile cf catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (key, face) := parseLine line then
          known := known.insert key face
  -- Misses are probed in parallel chunks, joined in listing order so tie-breaking is unchanged.
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
  -- Rewritten only when something was probed, and merged like the listing cache.
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

/-- The first face under `faceLt` with a readable MATH candidate image; the caller still
parses and checks it. -/
public def firstMathFace (faces : Array Face) : IO (Option Face) := do
  for f in faces.qsort faceLt do
    if (← faceImage f.path (· == "MATH")).isSome then
      return some f
  return none

/-- The math face for a document declaring none: the body family's designed companion when
the host has it, else the first MATH-table candidate. -/
public def pickMathFace (faces : Array Face) (body : String) :
    IO (Option (Face × Option Pairing)) := do
  match pickCompanion faces body with
  | some (row, face) => return some (face, some row)
  | none => return (← firstMathFace faces).map ((·, none))

/-- For each needed scalar, the first candidate whose cmap maps it, candidates ordered by
normalised family, upright before italic, weight nearest regular, then subfamily and path;
an unmapped scalar is absent. -/
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

/-- `fallbackPicks` with the preferred faces answering first for every scalar their cmaps
map. -/
public def fallbackPicksPreferring (preferred : String → Bool) (faces : Array Face)
    (needed : Array Char) : IO (Array (Char × String)) := do
  let docFaces := faces.filter (fun f => preferred f.path)
  let first ← fallbackPicks docFaces needed
  let got := first.map (·.1)
  let rest := needed.filter (fun c => !got.contains c)
  return first ++ (← fallbackPicks faces rest)

end LeanTex.Cli.FontDiscovery
