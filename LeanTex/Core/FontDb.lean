import Std.Data.HashMap
import Std.Data.HashSet
import LeanTex.Core.Font

namespace LeanTex.Core.FontDb

open LeanTex.Core.Font

/-- One installed face: the family it belongs to and which variant it is. -/
structure Face where
  path : String
  family : String
  subfamily : String
  bold : Bool
  italic : Bool
  fixedPitch : Bool
  /-- OS/2 usWeightClass: 400 is regular, 700 bold, 600 "Demi"/"Semibold". -/
  weight : Nat
  deriving Repr, Inhabited

/-- Which face of a family a piece of text wants. -/
structure Variant where
  bold : Bool := false
  italic : Bool := false
  deriving Repr, BEq, Inhabited

def searchDirs : List String :=
  ["/usr/share/fonts", "/usr/local/share/fonts", "/usr/share/texmf-dist/fonts/opentype",
   "/usr/share/texmf-dist/fonts/truetype",
   -- macOS. System faces are mostly .ttc collections, which the scan skips
   -- (see isFontFile); Supplemental and /Library hold plain .ttf/.otf.
   "/System/Library/Fonts", "/System/Library/Fonts/Supplemental", "/Library/Fonts",
   "/opt/homebrew/share/fonts"]

/-- Where else to look, from `LEANTEX_FONT_PATH` and `$HOME`. A TeX Live tree is
not always at `/usr/share`, and a user's own fonts are never there: without this
a document naming a font it demonstrably has gets told the font does not exist. -/
def extraDirs : IO (List String) := do
  let home := (← IO.getEnv "HOME").getD ""
  let userDirs :=
    if home.isEmpty then []
    else [home ++ "/.fonts", home ++ "/.local/share/fonts", home ++ "/Library/Fonts"]
  let env := (← IO.getEnv "LEANTEX_FONT_PATH").getD ""
  let fromEnv := (env.splitOn ":").filter (!·.isEmpty)
  return userDirs ++ fromEnv

private def isFontFile (p : String) : Bool :=
  -- Compare the extension only: lowercasing the whole path allocated a copy
  -- of every one of 3000 names and was most of the listing's time.
  -- `.ttc` and `.dfont` collections (macOS system fonts) are skipped here by
  -- construction: the scan never opens them, so they can never be reported
  -- as broken fonts. Parsing collections is out of scope (PLAN.md).
  let ext := (p.splitOn ".").getLast? |>.map String.toLower
  ext == some "ttf" || ext == some "otf"

/-- Font files under `dir`, `depth` levels deep. Structural on `depth`: a
directory tree is not an inductive type the checker can see, so the bound is
the recursion measure, and four is deeper than any font tree goes. -/
def listFonts (dir : System.FilePath) : Nat → IO (Array String)
  | 0 => pure #[]
  | depth + 1 => do
    -- Threads the accumulator: `out ++ (← recurse)` copied it at every
    -- subdirectory, and a font tree has hundreds.
    go dir depth #[]
where
  go (dir : System.FilePath) : Nat → Array String → IO (Array String)
    | 0, acc => pure acc
    | depth + 1, acc => do
      -- Sorted: `readDir` returns filesystem order, which differs between
      -- hosts, and resolution breaks ties by scan order. The same files must
      -- give the same faces in the same order everywhere.
      let entries := (← try dir.readDir catch _ => pure #[]).qsort
        fun a b => a.fileName < b.fileName
      let mut acc := acc
      for e in entries do
        let p := e.path
        -- A name with a font extension is a file; nothing else is worth a stat.
        if isFontFile p.toString then
          acc := acc.push p.toString
        else if ← p.isDir then
          acc ← go p depth acc
      return acc

/-- Read just enough of a font file to classify it: the table directory, then
the `name`, `OS/2`, `head`, and `post` tables. Full files are large (a
megabyte each is common) and a scan touches every installed face. -/
def probe (path : String) : IO (Option Face) := do
  try
    let handle ← IO.FS.Handle.mk path .read
    let header ← handle.read 12
    if header.size < 12 then
      return none
    let numTables := (header[4]!).toNat * 256 + (header[5]!).toNat
    if numTables == 0 || numTables > 512 then
      return none
    let dir ← handle.read (16 * numTables).toUSize
    -- Keep the header + directory, then splice each wanted table at its own
    -- offset so `Font.parse`-style readers see a consistent file image.
    let mut wanted : Array (String × Nat × Nat) := #[]
    for k in [0:numTables] do
      let base := 16 * k
      if base + 16 ≤ dir.size then
        let tag := String.ofList ((dir.extract base (base + 4)).toList.map
          fun c => Char.ofNat c.toNat)
        let off := (((dir[base + 8]!).toNat * 256 + (dir[base + 9]!).toNat) * 256 +
          (dir[base + 10]!).toNat) * 256 + (dir[base + 11]!).toNat
        let len := (((dir[base + 12]!).toNat * 256 + (dir[base + 13]!).toNat) * 256 +
          (dir[base + 14]!).toNat) * 256 + (dir[base + 15]!).toNat
        -- Only the metadata tables. A scan touches every installed face, and
        -- `hmtx` and `cmap` are what make that expensive -- classification
        -- needs neither, so `probe` calls `classify` rather than `parse`.
        if tag == "name" || tag == "OS/2" || tag == "head" || tag == "post" then
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
  catch _ =>
    return none

/-! ## The probe cache

Probing a face reads and classifies its tables; on a host with a TeX Live tree
that is ~2900 files and ~400 ms, the whole cost of a small build. Listing them
is 25 ms. So the classification of each file is cached on disk, keyed by the
file's path, size, and mtime: a face that changed on disk misses and is
probed again, one that vanished is never read, and a corrupt or missing cache
is a full rescan. Nothing about the cache can make the answer differ from a
scan, which is the property that lets it exist. -/

/-- `$XDG_CACHE_HOME/leantex`, or `~/.cache/leantex`; none without a home. -/
def cacheDir : IO (Option System.FilePath) := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some d => pure (some (System.FilePath.mk d))
    | none => match ← IO.getEnv "HOME" with
      | some h => pure (some (System.FilePath.mk h / ".cache"))
      | none => pure none
  return base.map (· / "leantex")

private def cachePath : IO (Option System.FilePath) := do
  return (← cacheDir).map (· / "fontdb.tsv")

/-- One line per file, tab-separated: the key fields, then the classification
-- or nothing after the key for a file `probe` rejected, so a rejected font is
not read again on every run. Family names may hold spaces and never tabs,
which is why the format is TSV and not something that needs an escaper. -/
private def faceLine (path size mtime : String) (f : Option Face) : String :=
  match f with
  | some f => String.intercalate "\t" [path, size, mtime, f.family, f.subfamily,
      toString f.bold, toString f.italic, toString f.fixedPitch, toString f.weight]
  | none => String.intercalate "\t" [path, size, mtime]

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
    let md ← (System.FilePath.mk path).metadata
    return some (toString md.byteSize, s!"{md.modified.sec}.{md.modified.nsec}")
  catch _ => return none

/-- The built-in locations plus `dirs`, in resolution order. -/
def systemRoots (dirs : List String := []) : IO (List String) := do
  return searchDirs ++ (← extraDirs) ++ dirs

/-- The faces under exactly `roots`, classified, in root order then sorted
path order — so the result is a function of the directories' contents alone,
which is what lets a test suite scan a directory it ships and get the same
faces on every host. Cached by the caller. Probing opens and reads every
face, so chunks of files are probed in parallel; joining in chunk order keeps
the face array exactly what the sequential scan produced, which matters
because resolution prefers earlier faces on ties. -/
def scanRoots (roots : List String) : IO (Array Face) := do
  let mut files : Array String := #[]
  for d in roots do
    let p := System.FilePath.mk d
    if ← p.pathExists then
      files := files ++ (← listFonts p 6)
  -- What the cache remembers, keyed by path + size + mtime.
  let cacheFile ← cachePath
  let mut known : Std.HashMap String (Option Face) := {}
  if let some cf := cacheFile then
    if ← cf.pathExists then
      let text ← try IO.FS.readFile cf catch _ => pure ""
      for line in text.splitOn "\n" do
        if let some (key, face) := parseLine line then
          known := known.insert key face
  -- Hits come from the cache; misses are probed in parallel chunks, in
  -- listing order either way so resolution's tie-breaking is unchanged.
  let mut keyed : Array (String × Option (String × String)) := #[]
  for f in files do
    keyed := keyed.push (f, ← fileKey f)
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
  let chunk := 64
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
  -- one file and writes none.
  if !toProbe.isEmpty then
    if let some cf := cacheFile then
      let mut lines : Array String := #[]
      for h : i in [0:keyed.size] do
        match keyed[i] with
        | (path, some (size, mtime)) => lines := lines.push (faceLine path size mtime result[i]!)
        | _ => pure ()
      try
        if let some parent := cf.parent then IO.FS.createDirAll parent
        IO.FS.writeFile cf (String.intercalate "\n" lines.toList ++ "\n")
      catch _ => pure ()
  return result.filterMap id

/-- All installed faces: the built-in locations plus `dirs`. -/
def scan (dirs : List String := []) : IO (Array Face) := do
  scanRoots (← systemRoots dirs)

private def norm (s : String) : String :=
  String.ofList ((s.toLower.toList).filter fun c => c.isAlphanum)

/-- Canonical subfamily names. A face whose subfamily is exactly one of these
is the family's plain face; anything else carries an extra descriptor
("Condensed Bold", "ExtraLight"), which must not win over the plain one —
condensed faces commonly share the typographic family name. -/
private def canonicalSubfamily (s : String) : Bool :=
  ["regular", "bold", "italic", "oblique", "bolditalic", "boldoblique",
   "book", "normal"].contains (norm s)

/-- Target weight for the requested variant. Real families ship a weight
axis, so "bold" means "as close to 700 as this family gets". -/
private def targetWeight (bold : Bool) : Nat := if bold then 700 else 400

/-- Rank candidates for a target weight: closest weight wins; ties prefer the
plain face over one carrying an extra descriptor ("Condensed Bold"), because
condensed faces commonly share the typographic family name. A remaining tie
(the same family installed twice, e.g. a system copy and a TeX Live copy)
goes to the earlier face in scan order — the property `scan`'s ordered join
exists to provide — so the first search directory that holds a family owns it. -/
private def pickWeighted (cands : Array Face) (target : Nat) : Option Face :=
  let sorted := cands.zipIdx.qsort fun (a, ia) (b, ib) =>
    let da := if a.weight ≥ target then a.weight - target else target - a.weight
    let db := if b.weight ≥ target then b.weight - target else target - b.weight
    if da != db then da < db
    else
      let ca := if canonicalSubfamily a.subfamily then 0 else 1
      let cb := if canonicalSubfamily b.subfamily then 0 else 1
      if ca != cb then ca < cb
      else if a.subfamily.length != b.subfamily.length then
        a.subfamily.length < b.subfamily.length
      else ia < ib
  sorted[0]?.map (·.1)

/-- The family a name denotes. A family name denotes itself. A font file name
(`LibertinusSerif-Regular.otf`) — fontspec's way of naming a font that ships
beside the document — denotes the family of the scanned face with that file
name, so its bold and italic are found the way every other family's are. -/
def familyOf (faces : Array Face) (name : String) : String :=
  if isFontFile name then
    match faces.find? fun f => (f.path.splitOn "/").getLast? == some name with
    | some f => f.family
    | none => name
  else name

/-- Best face for a family name and variant, plus whether the family really
offers what was asked for. A family whose heaviest face is "Demi" (600) is
serving a genuine bold, so that counts as satisfied; one with no italic at
all does not, and the caller warns. -/
def resolve (faces : Array Face) (family : String) (v : Variant) :
    Option (Face × Bool) :=
  let target := norm (familyOf faces family)
  let inFamily := faces.filter fun f => norm f.family == target
  if inFamily.isEmpty then
    none
  else
    let want := targetWeight v.bold
    -- Italic is categorical: never substitute upright for italic silently.
    let matchingSlant := inFamily.filter fun f => f.italic == v.italic
    let pool := if matchingSlant.isEmpty then inFamily else matchingSlant
    match pickWeighted pool want with
    | none => none
    | some face =>
      let slantOk := face.italic == v.italic
      let weightOk :=
        if v.bold then face.weight ≥ 550 else face.weight ≤ 550
      some (face, slantOk && weightOk)

/-- Installed families that resemble a name: sharing a word, or within an
edit or two of it. `Nimbus Roman` finds `Nimbus Sans L` and `Nimbus Mono`;
`Libertinus` finds every Libertinus face. At most eight, closest first. -/
def nearest (families : Array String) (wanted : String) : Array String :=
  let words (s : String) : List String :=
    (s.toLower.splitOn " ").filter fun w => !w.isEmpty && w.length > 1
  let want := words wanted
  let score (fam : String) : Nat :=
    let got := words fam
    let shared := (want.filter got.contains).length
    -- Prefix of the first word counts too: `Nimbus` vs `NimbusSans`.
    let prefixHit := match want.head?, got.head? with
      | some a, some b => a.startsWith b || b.startsWith a
      | _, _ => false
    shared * 2 + (if prefixHit then 1 else 0)
  let scored := families.filterMap fun f =>
    let sc := score f
    if sc > 0 then some (sc, f) else none
  let sorted := scored.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)
  (sorted.extract 0 8).map (·.2)

/-- Family names present, sorted, for diagnostics and . -/
def families (faces : Array Face) : Array String := Id.run do
  -- One normalised key per face, kept in a set. The earlier `seen.any` with
  -- `norm` on both sides re-normalised every prior name for every face:
  -- four million string allocations and two seconds on a 2856-face host,
  -- paid on every failed font lookup.
  let mut keys : Std.HashSet String := {}
  let mut out : Array String := #[]
  for f in faces do
    let k := norm f.family
    unless keys.contains k do
      keys := keys.insert k
      out := out.push f.family
  return out.qsort (· < ·)

/-- Families tried, in order, when a document declares no `\fonts`. -/
def defaultFamilies : List String :=
  ["DejaVu Sans", "Helvetica Neue", "Helvetica", "Arial", "Liberation Sans",
   "Nimbus Sans", "Inter"]

/-- The family a document with no `\fonts` uses: the first preferred name
that resolves, else the first family calling itself sans, else the first
face of any kind. `none` only when no face is installed at all — so the
default exists on any host with any scannable font, by construction. -/
def defaultFamily (faces : Array Face) : Option String :=
  match defaultFamilies.find? fun n => (resolve faces n {}).isSome with
  | some n => some n
  | none =>
    match faces.find? fun f => ((norm f.family).splitOn "sans").length > 1 with
    | some f => some f.family
    | none => faces[0]?.map (·.family)

end LeanTex.Core.FontDb
