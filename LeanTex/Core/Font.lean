import LeanTex.Core.Diag

namespace LeanTex.Core.Font

/-- A parsed sfnt font: the metrics the layout engine needs, the char→glyph
map, and the raw bytes for embedding. Pure data; loading the file is the
driver's job. -/
structure Font where
  data : ByteArray
  isCff : Bool
  unitsPerEm : Nat
  ascent : Int
  descent : Int
  lineGap : Int
  psName : String
  family : String
  subfamily : String
  isBold : Bool
  isItalic : Bool
  isFixedPitch : Bool
  weight : Nat
  xHeight : Int
  cmap : Array (UInt32 × UInt32 × UInt32)  -- (startChar, endChar, startGid), sorted
  widths : Array Nat                        -- advance width per gid, font units
  numGlyphs : Nat
  /-- `post` underline metrics, font units. Zero means the font said nothing;
  the consumer supplies a fallback. -/
  underlinePosition : Int
  underlineThickness : Int
  /-- Per-gid: does the glyph reach below the underline's top edge? A missing
  or short `glyf`/`loca` means no glyph descends, never a panic. -/
  descenders : Array Bool
  deriving Inhabited

/-- A bounded byte read. Out of range is 0 rather than a panic: this parser is
fed arbitrary files, and a reader that aborts the process on a short table is
not a parser. `parse` separately rejects a font whose tables do not fit, so a
truncated file gets a diagnostic instead of quietly reading zeros. -/
private def u8 (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (b[i]).toNat else 0

private def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i + 1)

private def u32 (b : ByteArray) (i : Nat) : Nat :=
  ((u8 b i * 256 + u8 b (i + 1)) * 256 + u8 b (i + 2)) * 256 + u8 b (i + 3)

private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 0x8000 then (v : Int) - 0x10000 else v

private structure Table where
  offset : Nat
  length : Nat

private def findTable (b : ByteArray) (tag : String) : Option Table := Id.run do
  if b.size < 12 then
    return none
  let n := u16 b 4
  let tagBytes := tag.toUTF8
  for k in [0:n] do
    let entry := 12 + 16 * k
    if entry + 16 > b.size then
      return none
    if b.extract entry (entry + 4) == tagBytes then
      return some ⟨u32 b (entry + 8), u32 b (entry + 12)⟩
  return none

/-- Does a table's declared extent fit inside the file? A table that does not is
a broken font, and saying so beats reading zeros off the end of it. -/
private def fits (b : ByteArray) (t : Table) : Bool :=
  t.offset + t.length ≤ b.size

private def parseCmap4 (b : ByteArray) (off : Nat) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  let segX2 := u16 b (off + 6)
  let seg := segX2 / 2
  let endBase := off + 14
  let startBase := endBase + segX2 + 2
  let deltaBase := startBase + segX2
  let rangeBase := deltaBase + segX2
  let mut out : Array (UInt32 × UInt32 × UInt32) := #[]
  for k in [0:seg] do
    let endC := u16 b (endBase + 2 * k)
    let startC := u16 b (startBase + 2 * k)
    let delta := u16 b (deltaBase + 2 * k)
    let rangeOff := u16 b (rangeBase + 2 * k)
    if startC == 0xFFFF then
      continue
    if rangeOff == 0 then
      let gid := (startC + delta) % 0x10000
      out := out.push (UInt32.ofNat startC, UInt32.ofNat endC, UInt32.ofNat gid)
    else
      -- glyphIdArray ranges: expand per char (rare segments, bounded)
      for c in [startC:endC+1] do
        let idx := rangeBase + 2 * k + rangeOff + 2 * (c - startC)
        if idx + 1 < b.size then
          let g := u16 b idx
          if g != 0 then
            let gid := (g + delta) % 0x10000
            out := out.push (UInt32.ofNat c, UInt32.ofNat c, UInt32.ofNat gid)
  return out

private def parseCmap12 (b : ByteArray) (off : Nat) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  let n := u32 b (off + 12)
  let mut out : Array (UInt32 × UInt32 × UInt32) := #[]
  for k in [0:n] do
    let g := off + 16 + 12 * k
    out := out.push (UInt32.ofNat (u32 b g), UInt32.ofNat (u32 b (g + 4)),
      UInt32.ofNat (u32 b (g + 8)))
  return out

private def parseCmap (b : ByteArray) (t : Table) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  let n := u16 b (t.offset + 2)
  let mut best4 : Option Nat := none
  let mut best12 : Option Nat := none
  for k in [0:n] do
    let entry := t.offset + 4 + 8 * k
    let platform := u16 b entry
    let encoding := u16 b (entry + 2)
    let sub := t.offset + u32 b (entry + 4)
    let unicodeish := platform == 0 || (platform == 3 && (encoding == 1 || encoding == 10))
    if unicodeish && sub + 2 ≤ b.size then
      match u16 b sub with
      | 4 => best4 := best4 <|> some sub
      | 12 => best12 := best12 <|> some sub
      | _ => pure ()
  match best12 with
  | some off => return parseCmap12 b off
  | none =>
    match best4 with
    | some off => return parseCmap4 b off
    | none => return #[]

/-- Read one `name` table record. Prefers the typographic name (id 16/17)
over the legacy family/subfamily (id 1/2) when both are present. -/
private def parseNameId (b : ByteArray) (t : Table) (wanted : Nat) : Option String := Id.run do
  let n := u16 b (t.offset + 2)
  let strBase := t.offset + u16 b (t.offset + 4)
  let mut best : Option String := none
  for k in [0:n] do
    let entry := t.offset + 6 + 12 * k
    if u16 b (entry + 6) == wanted then
      let len := u16 b (entry + 8)
      let off := strBase + u16 b (entry + 10)
      let platform := u16 b entry
      if off + len ≤ b.size then
        let s :=
          if platform == 1 then
            String.ofList ((b.extract off (off + len)).toList.map fun c => Char.ofNat c.toNat)
          else Id.run do
            -- UTF-16BE; font names here are effectively Latin-1
            let mut acc := ""
            for j in [0:len / 2] do
              let cp := u16 b (off + 2 * j)
              if cp != 0 then
                acc := acc.push (Char.ofNat cp)
            return acc
        if best.isNone then
          best := some s
  return best

private def nameOf (b : ByteArray) (t : Option Table) (ids : List Nat)
    (fallback : String) : String :=
  match t with
  | none => fallback
  | some tbl =>
    match ids.findSome? (parseNameId b tbl) with
    | some s => if s.isEmpty then fallback else s
    | none => fallback

/-- Identity and style of a face, from the metadata tables only. Split out
because classifying a font for a family scan needs none of its metrics: a
scan touches every installed face, and `hmtx` and `cmap` are the two tables
that make that expensive. `parse` uses the same code so the two can never
disagree about what a face is called. -/
structure Class where
  psName : String
  family : String
  subfamily : String
  isBold : Bool
  isItalic : Bool
  isFixedPitch : Bool
  weight : Nat
  deriving Repr, Inhabited

/-- Classify a face. Needs only `head`; `name`, `OS/2`, and `post` refine it. -/
def classify (data : ByteArray) : Except String Class := do
  if data.size < 12 then
    throw "not a font file"
  let tag := u32 data 0
  if tag != 0x4F54544F && tag != 0x00010000 then
    throw "unsupported font format (need TrueType or CFF OpenType)"
  let some head := findTable data "head" | throw "font has no 'head' table"
  unless fits data head do
    throw "font table 'head' extends past the end of the file"
  let nameT := findTable data "name"
  let psName := nameOf data nameT [6] "Embedded"
  let family := nameOf data nameT [16, 1] psName
  let subfamily := nameOf data nameT [17, 2] "Regular"
  let lowerSub := subfamily.toLower
  -- OS/2 fsSelection is authoritative when present; the subfamily string is
  -- the fallback, and covers fonts that call oblique faces "Oblique".
  let fsSelection := match findTable data "OS/2" with
    | some t => if t.offset + 64 ≤ data.size then some (u16 data (t.offset + 62)) else none
    | none => none
  let macStyle := u16 data (head.offset + 44)
  let isBold := match fsSelection with
    | some fs => fs % 64 ≥ 32 || macStyle % 2 == 1
    | none => (lowerSub.splitOn "bold").length > 1 || macStyle % 2 == 1
  let isItalic := match fsSelection with
    | some fs => fs % 2 == 1 || macStyle / 2 % 2 == 1
    | none =>
      (lowerSub.splitOn "italic").length > 1 || (lowerSub.splitOn "oblique").length > 1
        || macStyle / 2 % 2 == 1
  let isFixedPitch := match findTable data "post" with
    | some t => if t.offset + 20 ≤ data.size then u32 data (t.offset + 16) != 0 else false
    | none => false
  -- OS/2 usWeightClass (100–900). Families ship weights, not a bold flag:
  -- "Demi" at 600 is a family's bold face even when the BOLD bit is clear.
  let weight := match findTable data "OS/2" with
    | some t =>
      if t.offset + 6 ≤ data.size then
        let w := u16 data (t.offset + 4)
        if w == 0 then (if isBold then 700 else 400) else w
      else if isBold then 700 else 400
    | none => if isBold then 700 else 400
  return { psName, family, subfamily, isBold, isItalic, isFixedPitch, weight }

/-- Characters whose glyphs hang below an underline in an ordinary text face:
the descending letters, the punctuation that reaches down, and letters
carrying a below-attached diacritic. The CFF stand-in: CFF charstrings have
no cheap per-glyph bounding box, so the character answers for its glyph. -/
def descenderChars : String :=
  "gjpqy,;()[]{}@QçÇşŞţŢņŅģĢķĶļĻŗŖșȘțȚąĄęĘįĮųŲḑḐṣṢẉẈ"

/-- Descender bits for a CFF face: mark the glyph of every descender
character the cmap can reach. -/
private def cffDescenders (cmap : Array (UInt32 × UInt32 × UInt32))
    (numGlyphs : Nat) : Array Bool := Id.run do
  let mut out : Array Bool := Array.replicate numGlyphs false
  for c in descenderChars.toList do
    let x := UInt32.ofNat c.toNat
    for (s, e, g) in cmap do
      if s ≤ x && x ≤ e then
        let gid := (g + (x - s)).toNat % 0x10000
        if gid < out.size then
          out := out.set! gid true
  return out

/-- Descender bits for a TrueType face, from each glyph header's own `yMin`
(byte offset 4: after numberOfContours and xMin). A missing or short table
means "no glyph descends" -- this is decoration, not correctness. -/
private def trueTypeDescenders (data : ByteArray) (head : Table)
    (numGlyphs : Nat) (threshold : Int) : Array Bool := Id.run do
  let none' := Array.replicate numGlyphs false
  let some loca := findTable data "loca" | return none'
  let some glyf := findTable data "glyf" | return none'
  unless fits data loca && fits data glyf do return none'
  let longFormat := u16 data (head.offset + 50) == 1
  let entrySize := if longFormat then 4 else 2
  unless (numGlyphs + 1) * entrySize ≤ loca.length do return none'
  let offAt (g : Nat) : Nat :=
    if longFormat then u32 data (loca.offset + 4 * g)
    else 2 * u16 data (loca.offset + 2 * g)
  let mut out : Array Bool := Array.mkEmpty numGlyphs
  for g in [0:numGlyphs] do
    let o1 := offAt g
    let o2 := offAt (g + 1)
    -- An empty glyph (space) has no outline and no descender; a header that
    -- overruns its table is read as one.
    if o2 ≤ o1 || o1 + 10 > glyf.length then
      out := out.push false
    else
      out := out.push (i16 data (glyf.offset + o1 + 4) < threshold)
  return out

def parse (data : ByteArray) : Except String Font := do
  if data.size < 12 then
    throw "not a font file"
  let tag := u32 data 0
  let isCff := tag == 0x4F54544F  -- 'OTTO'
  if !isCff && tag != 0x00010000 then
    throw "unsupported font format (need TrueType or CFF OpenType)"
  let some head := findTable data "head" | throw "font has no 'head' table"
  let some hhea := findTable data "hhea" | throw "font has no 'hhea' table"
  let some maxp := findTable data "maxp" | throw "font has no 'maxp' table"
  let some hmtx := findTable data "hmtx" | throw "font has no 'hmtx' table"
  let some cmapT := findTable data "cmap" | throw "font has no 'cmap' table"
  for (name, t) in [("head", head), ("hhea", hhea), ("maxp", maxp),
                    ("hmtx", hmtx), ("cmap", cmapT)] do
    unless fits data t do
      throw s!"font table '{name}' extends past the end of the file"
  let unitsPerEm := u16 data (head.offset + 18)
  let ascent := i16 data (hhea.offset + 4)
  let descent := i16 data (hhea.offset + 6)
  let lineGap := i16 data (hhea.offset + 8)
  let numH := u16 data (hhea.offset + 34)
  let numGlyphs := u16 data (maxp.offset + 4)
  let widths : Array Nat := Id.run do
    let mut w : Array Nat := Array.mkEmpty numGlyphs
    let mut last := 0
    for g in [0:numGlyphs] do
      if g < numH then
        last := u16 data (hmtx.offset + 4 * g)
      w := w.push last
    return w
  let cmap := parseCmap data cmapT
  let cmap := cmap.qsort fun a b => a.1 < b.1
  let cls ← classify data
  let psName := cls.psName
  let family := cls.family
  let subfamily := cls.subfamily
  let isBold := cls.isBold
  let isItalic := cls.isItalic
  let isFixedPitch := cls.isFixedPitch
  let weight := cls.weight
  -- OS/2 sxHeight (version 2+); tokens in `ex` need it. Falls back to half
  -- the em, which is the conventional approximation.
  let xHeight := match findTable data "OS/2" with
    | some t =>
      let version := if t.offset + 2 ≤ data.size then u16 data t.offset else 0
      if version ≥ 2 && t.offset + 88 ≤ data.size then
        let v := i16 data (t.offset + 86)
        if v > 0 then v else (unitsPerEm : Int) / 2
      else (unitsPerEm : Int) / 2
    | none => (unitsPerEm : Int) / 2
  let upem := if unitsPerEm == 0 then 1000 else unitsPerEm
  -- post underline metrics: FWords at offsets 8 and 10.
  let (upos, uthick) := match findTable data "post" with
    | some t =>
      if t.offset + 12 ≤ data.size then (i16 data (t.offset + 8), i16 data (t.offset + 10))
      else ((0 : Int), (0 : Int))
    | none => (0, 0)
  -- A glyph descends when its box reaches below the rule's top edge; a font
  -- that declares no position gets the conventional tenth of an em.
  let threshold := if upos == 0 then -((upem : Int) / 10) else upos
  let descenders := if isCff then cffDescenders cmap numGlyphs
    else trueTypeDescenders data head numGlyphs threshold
  return {
    data := data
    isCff := isCff
    unitsPerEm := if unitsPerEm == 0 then 1000 else unitsPerEm
    ascent := ascent
    descent := descent
    lineGap := lineGap
    psName := psName
    family := family
    subfamily := subfamily
    isBold := isBold
    isItalic := isItalic
    isFixedPitch := isFixedPitch
    weight := weight
    xHeight := xHeight
    cmap := cmap
    widths := widths
    numGlyphs := numGlyphs
    underlinePosition := upos
    underlineThickness := uthick
    descenders := descenders
  }

/-- Glyph id for a scalar, or `none` (missing glyph). Binary search. -/
def Font.gid (f : Font) (c : Char) : Option Nat := Id.run do
  let x := UInt32.ofNat c.toNat
  let mut lo := 0
  let mut hi := f.cmap.size
  for _ in [0:32] do
    if lo >= hi then
      break
    let mid := (lo + hi) / 2
    let (s, e, g) := f.cmap[mid]!
    if x < s then
      hi := mid
    else if x > e then
      lo := mid + 1
    else
      return some ((g + (x - s)).toNat % 0x10000)
  return none

/-- Advance width of a scalar in font units (0 when the glyph is missing). -/
def Font.advance (f : Font) (c : Char) : Nat :=
  match f.gid c with
  | some g => f.widths[g]?.getD 0
  | none => 0

/-- Does this glyph reach below the underline's top edge? Decides where the
rule is interrupted; a gid past the table does not descend. -/
def Font.descends (f : Font) (g : Nat) : Bool :=
  f.descenders[g]?.getD false

/-- The faces a document typesets with. Index 0 is always the body regular
face; `Style` resolves to an index at layout time. -/
structure FontSet where
  fonts : Array Font
  /-- (family slot, bold, italic) → index into `fonts`. -/
  index : Array ((Nat × Bool × Bool) × Nat) := #[]
  deriving Inhabited

namespace FontSet

def body (fs : FontSet) : Font := fs.fonts[0]!

def get (fs : FontSet) (i : Nat) : Font := fs.fonts[i]?.getD fs.body

/-- Slot 0 = body/serif, 1 = sans, 2 = mono. -/
def lookup (fs : FontSet) (slot : Nat) (bold italic : Bool) : Nat :=
  match fs.index.find? fun e => e.1 == (slot, bold, italic) with
  | some (_, i) => i
  | none =>
    match fs.index.find? fun e => e.1 == (slot, false, false) with
    | some (_, i) => i
    | none => 0

end FontSet
end LeanTex.Core.Font
