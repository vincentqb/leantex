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
   "/usr/share/texmf-dist/fonts/truetype"]

/-- Where else to look, from `LEANTEX_FONT_PATH` and `$HOME`. A TeX Live tree is
not always at `/usr/share`, and a user's own fonts are never there: without this
a document naming a font it demonstrably has gets told the font does not exist. -/
def extraDirs : IO (List String) := do
  let home := (← IO.getEnv "HOME").getD ""
  let userDirs :=
    if home.isEmpty then []
    else [home ++ "/.fonts", home ++ "/.local/share/fonts"]
  let env := (← IO.getEnv "LEANTEX_FONT_PATH").getD ""
  let fromEnv := (env.splitOn ":").filter (!·.isEmpty)
  return userDirs ++ fromEnv

private def isFontFile (p : String) : Bool :=
  let lower := p.toLower
  lower.endsWith ".ttf" || lower.endsWith ".otf"

/-- Recursively list font files, bounded so a symlink cycle cannot hang us. -/
partial def listFonts (dir : System.FilePath) (depth : Nat) : IO (Array String) := do
  if depth == 0 then
    return #[]
  let mut out : Array String := #[]
  let entries ← try dir.readDir catch _ => pure #[]
  for e in entries do
    let p := e.path
    if ← p.isDir then
      out := out ++ (← listFonts p (depth - 1))
    else if isFontFile p.toString then
      out := out.push p.toString
  return out

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

/-- All installed faces, classified. Cached by the caller. `dirs` adds to the
built-in locations rather than replacing them. -/
def scan (dirs : List String := []) : IO (Array Face) := do
  let mut faces : Array Face := #[]
  for d in searchDirs ++ (← extraDirs) ++ dirs do
    let p := System.FilePath.mk d
    if ← p.pathExists then
      for file in ← listFonts p 4 do
        if let some face ← probe file then
          faces := faces.push face
  return faces

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
condensed faces commonly share the typographic family name. -/
private def pickWeighted (cands : Array Face) (target : Nat) : Option Face :=
  let sorted := cands.qsort fun a b =>
    let da := if a.weight ≥ target then a.weight - target else target - a.weight
    let db := if b.weight ≥ target then b.weight - target else target - b.weight
    if da != db then da < db
    else
      let ca := if canonicalSubfamily a.subfamily then 0 else 1
      let cb := if canonicalSubfamily b.subfamily then 0 else 1
      if ca != cb then ca < cb
      else if a.subfamily.length != b.subfamily.length then
        a.subfamily.length < b.subfamily.length
      else a.path < b.path
  sorted[0]?

/-- Best face for a family name and variant, plus whether the family really
offers what was asked for. A family whose heaviest face is "Demi" (600) is
serving a genuine bold, so that counts as satisfied; one with no italic at
all does not, and the caller warns. -/
def resolve (faces : Array Face) (family : String) (v : Variant) :
    Option (Face × Bool) :=
  let target := norm family
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

/-- Family names present, for diagnostics that suggest alternatives. -/
def families (faces : Array Face) : Array String := Id.run do
  let mut seen : Array String := #[]
  for f in faces do
    unless seen.any (fun s => norm s == norm f.family) do
      seen := seen.push f.family
  return seen.qsort (· < ·)

end LeanTex.Core.FontDb
