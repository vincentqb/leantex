module

public import LeanTex.Cli.FontDiscovery
public import Tests.Backends

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj Entry)

/-! The artifact tier: what the produced PDF bytes paint and where, read by a viewer's arithmetic
from the file alone and judged against the declared geometry. -/

/-- One token of a content stream (ISO 32000-2 §7.2); a number carries its value in sp beside its
raw spelling. -/
inductive CTok where
  | num (v : Dim.Length) (raw : String)
  | name (n : String)
  /-- A hexadecimal string's digits, whitespace removed. -/
  | hex (digits : String)
  /-- A literal string's bytes, one backslash escape resolved per byte. -/
  | lit (raw : String)
  | arrOpen
  | arrClose
  | dictOpen
  | dictClose
  | op (name : String)
  deriving Repr, BEq, Inhabited

/-- A string operand as the flat reading spells it: a hexadecimal string's
digits, whitespace removed, or a literal string's bytes as characters. -/
private def ctStr (raw : ByteArray) : CTok :=
  if raw[0]? == some 60 then
    .hex (String.ofList ((raw.extract 1 (raw.size - 1)).toList.filterMap fun b =>
      if b == 0 || b == 9 || b == 10 || b == 12 || b == 13 || b == 32 then none else some (Char.ofNat b.toNat)))
  else
    .lit (String.ofList (((PdfContentLex.strBytes? (.str raw)).getD ByteArray.empty).toList.map
      fun b => Char.ofNat b.toNat))

mutual

/-- An operand's flat tokens onto `acc`: an array or dictionary as its delimiters around its
contents, a keyword as an operator-shaped token. -/
private def ctOfObj (acc : Array CTok) : Obj → Array CTok
  | .null => acc.push (.op "null")
  | .bool b => acc.push (.op (if b then "true" else "false"))
  | .int n => acc.push (.num ((Obj.int n).sp?.getD 0) (toString n))
  | .real raw => acc.push (.num ((Obj.real raw).sp?.getD 0) raw)
  | .str raw => acc.push (ctStr raw)
  | .name n => acc.push (.name n)
  | .arr xs => (ctOfList (acc.push .arrOpen) xs.toList).push .arrClose
  | .dict es => (ctOfEntries (acc.push .dictOpen) es.toList).push .dictClose
  | .ref n g =>
    acc.push (.num ((Obj.int n).sp?.getD 0) (toString n)) |>.push (.num ((Obj.int g).sp?.getD 0) (toString g))
      |>.push (.op "R")

private def ctOfList (acc : Array CTok) : List Obj → Array CTok
  | [] => acc
  | o :: rest => ctOfList (ctOfObj acc o) rest

private def ctOfEntries (acc : Array CTok) : List (String × Obj) → Array CTok
  | [] => acc
  | (k, v) :: rest => ctOfEntries (ctOfObj (acc.push (.name k)) v) rest

end

/-- A content stream's tokens in order, read through `PdfContentLex.scan` and flattened, so an
operator's operands are the tokens since the last operator. -/
def scanContent (b : ByteArray) : Array CTok :=
  (PdfContentLex.scan b).foldl (fun acc t => match t with
    | .val o => ctOfObj acc o
    | .op n => acc.push (.op n)
    | .inline d _ => (ctOfEntries (acc.push (.op "BI")) d.toList).push (.op "ID") |>.push (.op "EI")) #[]

/-- A hexadecimal string read as two-byte codes: the CIDs an Identity-H
string spells (§9.7.4.2), and the code units a `/ToUnicode` value
spells. -/
def artCodes (digits : String) : Array Nat := Id.run do
  let cs := digits.toList.toArray
  let mut out : Array Nat := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if cs.size < i + 4 then break
    let nib (k : Nat) : Nat := (Hex.digit? cs[k]!).getD 0
    out := out.push ((((nib i) * 16 + nib (i + 1)) * 16 + nib (i + 2)) * 16 + nib (i + 3))
    i := i + 4
  return out

/-- A `/ToUnicode` value as text: UTF-16BE code units, surrogate pairs
joined (§9.10.3). -/
def artUtf16 (digits : String) : String := Id.run do
  let us := artCodes digits
  let mut out := ""
  let mut i := 0
  for _ in [0:us.size + 1] do
    if us.size ≤ i then break
    let u := us[i]!
    if 0xD800 ≤ u && u ≤ 0xDBFF && i + 1 < us.size then
      out := out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (us[i + 1]! - 0xDC00)))
      i := i + 2
    else
      out := out.push (Char.ofNat u)
      i := i + 1
  return out

/-- One face as the file describes it: its `/ToUnicode` map, its `/W` widths and its
`/FontDescriptor` extent. -/
structure ArtFont where
  toUni : Std.HashMap Nat String
  /-- Glyph advances, in thousandths of the em, each read as a length of that many points — the
  units `artMille` reads. -/
  widths : Std.HashMap Nat Dim.Length
  defaultWidth : Dim.Length
  ascent : Dim.Length
  descent : Dim.Length
  /-- `/CapHeight`: the height a line of text measures from its glyphs, the engine's text-area
  measure. -/
  capHeight : Dim.Length
  deriving Inhabited

/-- The `bfchar` pairs of a `/ToUnicode` CMap: CID, then its text. -/
def artToUniMap (toks : Array CTok) : Std.HashMap Nat String := Id.run do
  let mut m : Std.HashMap Nat String := {}
  let mut inBf := false
  let mut pend : Option String := none
  for t in toks do
    match t with
    | .op "beginbfchar" =>
      inBf := true
      pend := none
    | .op "endbfchar" =>
      inBf := false
      pend := none
    | .hex d =>
      if inBf then
        match pend with
        | none => pend := some d
        | some g =>
          m := m.insert ((artCodes g)[0]?.getD 0) (artUtf16 d)
          pend := none
    | _ => pure ()
  return m

/-- A font-dictionary metric in thousandths of the em, read as that many points; a real number is
not truncated. -/
def artMille (o : Obj) : Option Dim.Length := o.sp?

/-- A `/W` array (§9.7.4.3) in both forms, the range form capped so a malformed pair cannot make the
reading unbounded. -/
def artWidthMap (o : Obj) : Std.HashMap Nat Dim.Length := Id.run do
  let mut m : Std.HashMap Nat Dim.Length := {}
  let .arr xs := o | return m
  let mut i := 0
  for _ in [0:xs.size + 1] do
    if xs.size ≤ i then break
    match xs[i]!, xs[i + 1]? with
    | .int c, some (.arr ws) =>
      for k in [0:ws.size] do
        if let some w := artMille ws[k]! then m := m.insert (c.toNat + k) w
      i := i + 2
    | .int c1, some (.int c2) =>
      match (xs[i + 2]?).bind artMille with
      | some w =>
        if c1 ≤ c2 && c2 - c1 ≤ 65535 then
          for g in [c1.toNat:c2.toNat + 1] do m := m.insert g w
        i := i + 3
      | _ => i := i + 1
    | _, _ => i := i + 1
  return m

/-- A Type0 font dictionary read as an `ArtFont`, every composite value dereferenced. -/
def artFontOf (es : Array Entry) (o : Obj) : ArtFont :=
  let deref := PdfCensus.deref es
  let toUni := match o.get? "ToUnicode" with
    | some (.ref n _) =>
      match es.find? (·.num == n) with
      | some e =>
        match e.decoded with
        | .ok (some data) => artToUniMap (scanContent data)
        | _ => {}
      | none => {}
    | _ => {}
  let cid := match deref ((o.get? "DescendantFonts").getD .null) with
    | .arr xs => deref (xs[0]?.getD .null)
    | d => d
  let fd := deref ((cid.get? "FontDescriptor").getD .null)
  let milleOf (d : Obj) (k : String) (dflt : Dim.Length) : Dim.Length :=
    (((d.get? k).map deref).bind artMille).getD dflt
  { toUni
    widths := artWidthMap (deref ((cid.get? "W").getD .null))
    defaultWidth := milleOf cid "DW" (Dim.bp 1000)
    ascent := milleOf fd "Ascent" (Dim.bp 1000)
    descent := milleOf fd "Descent" (Dim.bp (-300))
    capHeight := milleOf fd "CapHeight" (milleOf fd "Ascent" (Dim.bp 1000)) }

/-- The marked-content sequence a painting operator stands inside (§14.6): content with its
structure type and identifier, or an artifact with its declared type. -/
inductive ArtMark where
  | artifact (kind : Option String)
  | content (tag : String) (mcid : Nat)
  deriving Repr, BEq, Inhabited

def ArtMark.isArtifact : ArtMark → Bool
  | .artifact _ => true
  | .content _ _ => false

def ArtMark.render : ArtMark → String
  | .artifact none => "/Artifact"
  | .artifact (some k) => s!"/Artifact /{k}"
  | .content t n => s!"/{t} /MCID {n}"

/-- One glyph run the file paints: the pen `Tm` and `TJ` put it at, its glyphs' own advance, and the
text its `/ToUnicode` spells. -/
structure ArtRun where
  marks : Array ArtMark
  x : Dim.Length
  y : Dim.Length
  w : Dim.Length
  size : Dim.Length
  /-- The face's declared `/Ascent` at this size: the generous box, which
  the page-box claim reads. -/
  ascent : Dim.Length
  /-- The face's declared `/CapHeight` at this size: the measure the
  engine judges its own text area by. -/
  inkAscent : Dim.Length
  descent : Dim.Length
  /-- The widest advance among the run's glyphs: the slack character protrusion may hang into the
  margin. -/
  widest : Dim.Length
  text : String
  /-- Where each glyph starts, in PDF user space, with its `/ToUnicode` text. -/
  glyphs : Array (Dim.Length × String) := #[]
  /-- The font resource the run's `Tf` named. -/
  face : String := ""
  deriving Repr, Inhabited

/-- One non-text mark the file paints, as its bounding box in PDF user
space: a fill, a stroked or filled path, an image, or the outlined box
standing where an image did not load. -/
structure ArtBox where
  marks : Array ArtMark
  kind : String
  x0 : Dim.Length
  y0 : Dim.Length
  x1 : Dim.Length
  y1 : Dim.Length
  deriving Repr, Inhabited

def ArtRun.x1 (r : ArtRun) : Dim.Length := r.x + r.w

/-- A run's top edge under the generous box: the baseline plus the
declared `/Ascent` at the set size. -/
def ArtRun.top (r : ArtRun) : Dim.Length := r.y + r.ascent

/-- A run's top edge under the engine's own ink measure: the baseline plus
the declared `/CapHeight`. -/
def ArtRun.inkTop (r : ArtRun) : Dim.Length := r.y + r.inkAscent

/-- A run's bottom edge: the baseline plus the descriptor's descent
(negative) at the set size. -/
def ArtRun.bottom (r : ArtRun) : Dim.Length := r.y + r.descent

def ArtRun.isArtifact (r : ArtRun) : Bool := r.marks.any ArtMark.isArtifact

def ArtBox.isArtifact (b : ArtBox) : Bool := b.marks.any ArtMark.isArtifact

private def ctName? : CTok → Option String
  | .name n => some n
  | _ => none

/-- The name following `/key` among an operator's operands: how `/Type`
is read out of an artifact's property dictionary. -/
private def artNameAfter (stack : Array CTok) (key : String) : Option String := do
  let i ← stack.findIdx? (· == CTok.name key)
  (stack[i + 1]?).bind ctName?

private def artIntAfter (stack : Array CTok) (key : String) : Option Int := do
  let i ← stack.findIdx? (· == CTok.name key)
  match stack[i + 1]? with
  | some (.num _ raw) => raw.toInt?
  | _ => none

/-- The evaluation's state: the marked-content stack, the pen, the face and size, the horizontal
scale in per mille, the open path's box, the last `cm`, and the text state each `q` saves. -/
private structure ArtSt where
  runs : Array ArtRun := #[]
  boxes : Array ArtBox := #[]
  marks : Array ArtMark := #[]
  stack : Array CTok := #[]
  x : Dim.Length := 0
  y : Dim.Length := 0
  size : Dim.Length := 0
  th : Int := 1000
  font : Option ArtFont := none
  face : String := ""
  path : Option (Dim.Length × Dim.Length × Dim.Length × Dim.Length) := none
  cm : Option (Dim.Length × Dim.Length × Dim.Length × Dim.Length) := none
  saved : Array (Dim.Length × Int × Option ArtFont × String) := #[]

private def artExtend (p : Option (Dim.Length × Dim.Length × Dim.Length × Dim.Length))
    (x y : Dim.Length) : Option (Dim.Length × Dim.Length × Dim.Length × Dim.Length) :=
  match p with
  | none => some (x, y, x, y)
  | some (x0, y0, x1, y1) => some (min x0 x, min y0 y, max x1 x, max y1 y)

/-- The numeric operands of an operator, in order. -/
private def artNums (stack : Array CTok) : Array Dim.Length :=
  stack.filterMap fun t => match t with
    | .num v _ => some v
    | _ => none

/-- The painting operators that put ink on the page (§8.5.3, Table 60);
`n` ends a path without painting and is not among them. -/
private def artPaintOps : List String :=
  ["f", "F", "f*", "B", "B*", "b", "b*", "S", "s"]

/-- The face a `TJ` with no `Tf` in force sets in: its glyphs unmapped and its box zero-height,
still recorded. -/
def artNoFont : ArtFont :=
  { toUni := {}, widths := {}, defaultWidth := Dim.bp 1000, ascent := 0
    descent := 0, capHeight := 0 }

/-- What a CID with no `/ToUnicode` entry reads as: U+FFFD, so an
unmapped glyph is visible to a text claim rather than silently absent. -/
def artUnmapped : String := String.singleton (Char.ofNat 0xFFFD)

/-- What a content stream paints, by §9.4.4's arithmetic: every glyph run, fill, path and image with
its box. -/
def evalContent (fonts : Std.HashMap String ArtFont) (toks : Array CTok) :
    Array ArtRun × Array ArtBox := Id.run do
  let mut s : ArtSt := {}
  for t in toks do
    match t with
    | .op o =>
      let ns := artNums s.stack
      if o == "BT" then
        s := { s with x := 0, y := 0 }
      else if o == "Tm" then
        if 6 ≤ ns.size then s := { s with x := ns[4]!, y := ns[5]! }
      else if o == "Td" then
        if 2 ≤ ns.size then s := { s with x := s.x + ns[0]!, y := s.y + ns[1]! }
      else if o == "Tf" then
        let nm := (s.stack.findSome? ctName?).getD ""
        s := { s with font := fonts[nm]?, face := nm, size := (ns[0]?).getD s.size }
      else if o == "Tz" then
        -- The operand is a percentage, kept in per mille and rounded.
        s := { s with th := (((ns[0]?).getD (Dim.bp 100)) * (10 : Int) + Dim.bp 1 / 2) / Dim.bp 1 }
      else if o == "TJ" || o == "Tj" then
        for it in s.stack do
          match it with
          | .hex d =>
            let f := s.font.getD artNoFont
            let cids := artCodes d
            let mut adv : Dim.Length := 0
            let mut widest : Dim.Length := 0
            let mut txt := ""
            let mut gs : Array (Dim.Length × String) := #[]
            for g in cids do
              let one := ((f.widths[g]?.getD f.defaultWidth) * s.th).mulDiv s.size
                ((1000000 : Int) * Dim.bp 1)
              gs := gs.push (s.x + adv, f.toUni[g]?.getD artUnmapped)
              adv := adv + one
              widest := max widest one
              txt := txt ++ (f.toUni[g]?.getD artUnmapped)
            s := { s with
              runs := s.runs.push
                { marks := s.marks, x := s.x, y := s.y, w := adv, size := s.size,
                  ascent := f.ascent.mulDiv s.size ((1000 : Int) * Dim.bp 1),
                  inkAscent := f.capHeight.mulDiv s.size ((1000 : Int) * Dim.bp 1),
                  descent := f.descent.mulDiv s.size ((1000 : Int) * Dim.bp 1)
                  widest := widest, text := txt, glyphs := gs, face := s.face }
              x := s.x + adv }
          | .num _ raw =>
            let d := raw.toInt?.getD 0
            s := { s with x := s.x - s.size * (d * s.th) / (1000000 : Int) }
          | _ => pure ()
      else if o == "m" || o == "l" then
        if 2 ≤ ns.size then s := { s with path := artExtend s.path ns[0]! ns[1]! }
      else if o == "c" then
        if 6 ≤ ns.size then
          let mut p := s.path
          for k in [0:3] do p := artExtend p (ns[2 * k]!) (ns[2 * k + 1]!)
          s := { s with path := p }
      else if o == "v" || o == "y" then
        if 4 ≤ ns.size then
          let mut p := s.path
          for k in [0:2] do p := artExtend p (ns[2 * k]!) (ns[2 * k + 1]!)
          s := { s with path := p }
      else if o == "re" then
        if 4 ≤ ns.size then
          let p := artExtend s.path (ns[0]!) (ns[1]!)
          s := { s with path := artExtend p (ns[0]! + ns[2]!) (ns[1]! + ns[3]!) }
      else if artPaintOps.contains o then
        if let some (x0, y0, x1, y1) := s.path then
          let kind := if o == "S" || o == "s" then "stroke" else "fill"
          s := { s with
            boxes := s.boxes.push { marks := s.marks, kind := kind
                                    x0 := x0, y0 := y0, x1 := x1, y1 := y1 }
            path := none }
      else if o == "n" then
        s := { s with path := none }
      else if o == "cm" then
        if 6 ≤ ns.size then s := { s with cm := some (ns[0]!, ns[3]!, ns[4]!, ns[5]!) }
      else if o == "Do" then
        if let some (a, d, e, f) := s.cm then
          s := { s with
            boxes := s.boxes.push { marks := s.marks, kind := "image"
                                    x0 := min e (e + a), y0 := min f (f + d)
                                    x1 := max e (e + a), y1 := max f (f + d) } }
      else if o == "q" then
        s := { s with cm := none, saved := s.saved.push (s.size, s.th, s.font, s.face) }
      else if o == "Q" then
        match s.saved.back? with
        | some (size, th, font, face) =>
          s := { s with cm := none, size, th, font, face, saved := s.saved.pop }
        | none => s := { s with cm := none }
      else if o == "BMC" || o == "BDC" then
        let tag := (s.stack.findSome? ctName?).getD ""
        let m : ArtMark := if tag == "Artifact" then .artifact (artNameAfter s.stack "Type")
          else .content tag ((artIntAfter s.stack "MCID").getD 0).toNat
        s := { s with marks := s.marks.push m }
      else if o == "EMC" then
        s := { s with marks := s.marks.pop }
      s := { s with stack := #[] }
    | other => s := { s with stack := s.stack.push other }
  return (s.runs, s.boxes)

/-- One page as the file describes it: its declared media box, the faces
its resources name, its content stream's bytes, and the ink those bytes
paint. -/
structure ArtPage where
  media : Dim.Length × Dim.Length × Dim.Length × Dim.Length
  runs : Array ArtRun
  boxes : Array ArtBox
  content : ByteArray
  deriving Inhabited

def ArtPage.mediaH (p : ArtPage) : Dim.Length := p.media.2.2.2 - p.media.2.1

/-- A rectangle array read in sp, or the null rectangle. -/
private def artRect (o : Obj) : Dim.Length × Dim.Length × Dim.Length × Dim.Length :=
  match o with
  | .arr xs =>
    let v (k : Nat) : Dim.Length := ((xs[k]?).bind Obj.sp?).getD 0
    (v 0, v 1, v 2, v 3)
  | _ => (0, 0, 0, 0)

/-- Every page in page-tree order; `/Kids` is followed one level deep, as the writer emits a flat
tree. -/
private def artPageDicts (es : Array Entry) (trailer : Obj) : Array Obj := Id.run do
  let deref := PdfCensus.deref es
  let root := deref (((PdfCensus.catalogOf es trailer).get? "Pages").getD .null)
  let mut out : Array Obj := #[]
  let .arr kids := deref ((root.get? "Kids").getD .null) | return out
  for k in kids do
    let d := deref k
    if PdfCensus.kindOf d == .pages then
      if let .arr inner := deref ((d.get? "Kids").getD .null) then
        for j in inner do out := out.push (deref j)
    else out := out.push d
  return out

/-- A produced file read as pages of ink through the engine's own reader; a file the reader refuses
is a named error. -/
def readArtifact (pdf : ByteArray) : Except String (Array ArtPage) := do
  let es ← PdfRead.objects pdf
  let trailer ← PdfRead.trailer pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let mut out : Array ArtPage := #[]
  for page in artPageDicts esv trailer do
    let mut fonts : Std.HashMap String ArtFont := {}
    let resources := deref ((page.get? "Resources").getD .null)
    if let .dict fs := deref ((resources.get? "Font").getD .null) then
      for (nm, v) in fs do fonts := fonts.insert nm (artFontOf esv (deref v))
    let content ← match page.get? "Contents" with
      | some (.ref n _) =>
        match esv.find? (·.num == n) with
        | some e =>
          match e.decoded with
          | .ok (some data) => pure data
          | .ok none => throw "page content stream: not a stream"
          | .error err => throw s!"page content stream: {err}"
        | none => throw s!"page /Contents names object {n}, which the cross-reference does not list"
      | _ => throw "page has no /Contents reference"
    let (runs, boxes) := evalContent fonts (scanContent content)
    out := out.push { media := artRect ((page.get? "MediaBox").getD .null)
                      runs, boxes, content }
  return out

/-- The bytes the driver writes: the structure tree, the typed operators built from it, and
`Pdf.write` given both. -/
def driverPdf (fs : Font.FontSet) (geom : Layout.Geom) (doc : Ir.Doc)
    (out : Layout.Out) (store : Image.Store := {}) : ByteArray :=
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let ops := Pdf.pageOps geom fs out.pages store tree
  Pdf.write geom fs out.pages doc.info store out.outline #[] tree ops

/-- Each page's folio as its bytes show it: its last run of arabic or lower-case roman numerals
alone, none where the page inks no number. -/
def artFolios (pdf : ByteArray) : Array (Option String) :=
  let folio (r : ArtRun) : Option String :=
    let tx := r.text.trimAscii.toString
    if !tx.isEmpty && (tx.all Char.isDigit || tx.all fun c => "ivxlcdm".toList.contains c) then some tx
    else none
  match readArtifact pdf with
  | .ok pages => pages.map fun (p : ArtPage) => (p.runs.filterMap folio).back?
  | .error _ => #[]

/-- A rectangle in PDF user space, as the region vocabulary the claims
read: `x0 ≤ x1` and `y0 ≤ y1`. -/
structure ArtRect where
  x0 : Dim.Length
  y0 : Dim.Length
  x1 : Dim.Length
  y1 : Dim.Length
  deriving Repr, Inhabited

def ArtRect.render (r : ArtRect) : String :=
  s!"[{r.x0.toBpString} {r.y0.toBpString} {r.x1.toBpString} {r.y1.toBpString}]"

/-- Whether the box lies inside `r`, allowing `hslack` left and right and `vslack` above and below. -/
def ArtRect.holds (r : ArtRect) (hslack vslack bx0 by0 bx1 by1 : Dim.Length) : Bool :=
  r.x0 - hslack ≤ bx0 && r.y0 - vslack ≤ by0 && bx1 ≤ r.x1 + hslack && by1 ≤ r.y1 + vslack

/-- Whether two rectangles share area, touching edges not counting. -/
def ArtRect.overlaps (a b : ArtRect) : Bool :=
  a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1

/-- The page's own declared medium, read from `/MediaBox`. -/
def ArtPage.box (p : ArtPage) : ArtRect :=
  { x0 := p.media.1, y0 := p.media.2.1, x1 := p.media.2.2.1, y1 := p.media.2.2.2 }

/-- The body area a geometry declares, in PDF user space; under a drawn chrome footer, beamer's
frame from the paper's top to 4 pt above the footline's ink. -/
def artBodyArea (geom : Layout.Geom) (footline : Bool := false) : ArtRect :=
  { x0 := geom.bleed + geom.hmargin
    y0 := geom.bleed + (if footline then Ir.footline.raise + Ir.footline.sep
      else geom.pageH - geom.bodyBottom)
    x1 := geom.bleed + geom.pageW - geom.hmargin
    y1 := geom.bleed + geom.pageH - (if footline then 0 else geom.bodyTop) }

/-- The least share of the page width, in tenths, a fill must span to read as a furniture band. -/
def artBandWidthShare : Nat := 9

/-- A band is at most a third of the page height; a fill spanning the page is its ground. -/
def artBandHeightShare : Nat := 3

/-- The structure types a furniture band legitimately holds: a frame's title and a poster headline's
headings. -/
def artBandTags : List String := ["Title", "H1", "H2", "H3", "H4", "H5", "H6"]

/-- The furniture bands a page paints, read from the file: fills spanning almost the whole medium at
its top or bottom edge, no taller than `artBandHeightShare` allows. -/
def ArtPage.bands (p : ArtPage) : Array ArtRect :=
  let box := p.box
  let wide := (box.x1 - box.x0) * artBandWidthShare / 10
  let short := (box.y1 - box.y0) / artBandHeightShare
  p.boxes.filterMap fun b =>
    if b.kind == "fill" && b.isArtifact && wide ≤ b.x1 - b.x0 && b.y1 - b.y0 ≤ short
        && (b.y1 ≥ box.y1 || b.y0 ≤ box.y0) then
      some { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
    else none

/-- The structure type content ink sits under, innermost first; none for artifact ink. -/
def ArtMark.tag? : ArtMark → Option String
  | .artifact _ => none
  | .content t _ => some t

def artInnerTag (marks : Array ArtMark) : Option String :=
  (marks.reverse.findSome? ArtMark.tag?)

/-- The precision at which the file can state a coordinate: one hundredth of a point. -/
def artSpellSlack : Dim.Length := Dim.pt 1 / 100

/-- The artifact claims, one per shape, so a recorded offence names the property it breaks. -/
inductive ArtProp where
  /-- Every mark lies inside the page's own `/MediaBox`. -/
  | pageBox
  /-- Every content-marked mark lies inside the declared body area, a
  painted band, or is accounted for by a named loss. -/
  | bodyArea
  /-- No body content stands outside the text area inside a painted furniture band. -/
  | bandFree
  /-- No glyph the file paints decodes to a markup character. -/
  | markupInk
  /-- No two consecutive pages carry identical content streams. -/
  | pageBytes
  /-- Every CID the file shows is named by its own `/ToUnicode`. -/
  | glyphNames
  deriving BEq, Repr, Inhabited

def ArtProp.name : ArtProp → String
  | .pageBox => "ink inside the page box"
  | .bodyArea => "content ink inside the text area"
  | .bandFree => "no body ink outside the text area in a furniture band"
  | .markupInk => "no markup character as ink"
  | .pageBytes => "no two consecutive pages identical"
  | .glyphNames => "every shown glyph is named"

def artProps : List ArtProp :=
  [.pageBox, .bodyArea, .bandFree, .markupInk, .pageBytes, .glyphNames]

/-- The codes whose meaning accounts for ink outside the text area (`bodyArea`): W0005, W0335 and
W0388. -/
def artOverflowCodes : List String := ["W0005", "W0335", "W0388"]

/-- A fixture's reading, with the two facts a claim needs beside it: the
body area the document declared, and whether its build named a loss that
accounts for ink outside it. -/
structure ArtReading where
  pages : Array ArtPage
  area : ArtRect
  accounted : Bool
  deriving Inhabited

/-- Every markup character but the `allowed` ones a page ships as ink. -/
def artMarkupOffences (r : ArtReading) (allowed : List Char) : Array String := Id.run do
  let mut out : Array String := #[]
  for h : i in [0:r.pages.size] do
    for run in r.pages[i].runs do
      for c in inkMarkupWatch.filter (!allowed.contains ·) do
        if run.text.any (· == c) then
          out := out.push s!"p{i + 1} ships '{c}' as ink: {run.text}"
  return out

/-- Every way a reading breaks one claim, each naming the page, the box and the ink; the gate and
the offence ratchet both read it. -/
def artOffences (r : ArtReading) : ArtProp → Array String
  | .pageBox => Id.run do
    let mut out : Array String := #[]
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let box := p.box
      for run in p.runs do
        unless box.holds artSpellSlack artSpellSlack run.x run.bottom run.x1 run.top do
          out := out.push s!"p{i + 1} glyph run [{run.x.toBpString} {run.bottom.toBpString} \
{run.x1.toBpString} {run.top.toBpString}] outside {box.render}: {run.text}"
      for b in p.boxes do
        unless box.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 do
          out := out.push s!"p{i + 1} {b.kind} [{b.x0.toBpString} {b.y0.toBpString} \
{b.x1.toBpString} {b.y1.toBpString}] outside {box.render}"
    return out
  | .bodyArea => Id.run do
    let mut out : Array String := #[]
    if r.accounted then return out
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let bands := p.bands
      for run in p.runs do
        unless run.isArtifact do
          let rect : ArtRect := { x0 := run.x, y0 := run.bottom, x1 := run.x1, y1 := run.inkTop }
          unless r.area.holds run.widest artSpellSlack run.x run.bottom run.x1 run.inkTop
              || bands.any (·.overlaps rect) do
            out := out.push s!"p{i + 1} glyph run {rect.render} outside \
{r.area.render}: {run.text}"
      for b in p.boxes do
        unless b.isArtifact do
          let rect : ArtRect := { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
          unless r.area.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 || bands.any (·.overlaps rect) do
            out := out.push s!"p{i + 1} {b.kind} {rect.render} outside {r.area.render}"
    return out
  | .bandFree => Id.run do
    let mut out : Array String := #[]
    for h : i in [0:r.pages.size] do
      let p := r.pages[i]
      let bands := p.bands
      if bands.isEmpty then continue
      for run in p.runs do
        let tag := artInnerTag run.marks
        unless tag.isNone || (tag.map artBandTags.contains).getD false do
          let rect : ArtRect := { x0 := run.x, y0 := run.bottom, x1 := run.x1, y1 := run.inkTop }
          unless r.area.holds run.widest artSpellSlack run.x run.bottom run.x1 run.inkTop do
            if bands.any (·.overlaps rect) then
              out := out.push s!"p{i + 1} /{tag.getD ""} run {rect.render} stands outside \
{r.area.render} and inside a band: {run.text}"
      for b in p.boxes do
        unless b.isArtifact do
          let rect : ArtRect := { x0 := b.x0, y0 := b.y0, x1 := b.x1, y1 := b.y1 }
          unless r.area.holds artSpellSlack artSpellSlack b.x0 b.y0 b.x1 b.y1 do
            if bands.any (·.overlaps rect) then
              out := out.push s!"p{i + 1} {b.kind} {rect.render} stands outside \
{r.area.render} and inside a band"
    return out
  | .markupInk => artMarkupOffences r []
  | .pageBytes => Id.run do
    let mut out : Array String := #[]
    for h : i in [1:r.pages.size] do
      if r.pages[i - 1]!.content.data == r.pages[i].content.data then
        out := out.push s!"p{i} and p{i + 1} carry identical content streams \
({r.pages[i].content.size} bytes)"
    return out
  | .glyphNames => Id.run do
    let mut out : Array String := #[]
    let repl := Char.ofNat 0xFFFD
    for h : i in [0:r.pages.size] do
      for run in r.pages[i].runs do
        if run.text.any (· == repl) then
          out := out.push s!"p{i + 1} shows a glyph its /ToUnicode does not name: {run.text}"
    return out

/-- The artifact offences the corpus ships, each a routed defect: a row whose offence stops firing
fails, so the table only shrinks. -/
def artKnownOffences : List (String × ArtProp × String) := [
  ("diagram-overflow", .pageBox, "a picture wider than the page paints its fill past the \
page edge; W0335 names it, and a picture should fit the medium or be clipped to it"),
  ("footer-collide", .pageBox, "a footline token with no legal break paints past the page \
edge; W0388 names it, and a footline should break or shrink what it cannot fit")]

def artTagIsArtifact : Pdf.MarkTag → Bool
  | .artifact _ => true
  | .content _ _ _ => false

mutual

/-- Every `Tm` inside a text object displaced, optionally only inside
content sequences (leaving running furniture where it was). -/
def artMoveTextOp (onlyContent : Bool) (dx dy : Dim.Length) : Pdf.TextOp → Pdf.TextOp
  | .move x y => .move (x + dx) (y + dy)
  | .marked t body =>
    if onlyContent && artTagIsArtifact t then .marked t body
    else .marked t (artMoveTextList onlyContent dx dy #[] body.toList)
  | o@(.scale _) => o
  | o@(.font _ _) => o
  | o@(.color _) => o
  | o@(.show _) => o

def artMoveTextList (onlyContent : Bool) (dx dy : Dim.Length) (acc : Array Pdf.TextOp) :
    List Pdf.TextOp → Array Pdf.TextOp
  | [] => acc
  | o :: rest => artMoveTextList onlyContent dx dy (acc.push (artMoveTextOp onlyContent dx dy o)) rest

end

mutual

/-- One page's operators with its text displaced, its fills and paths in place. -/
def artMoveOp (onlyContent : Bool) (dx dy : Dim.Length) : Pdf.ContentOp → Pdf.ContentOp
  | .text ops => .text (artMoveTextList onlyContent dx dy #[] ops.toList)
  | .marked t body => .marked t (artMoveList onlyContent dx dy #[] body.toList)
  | o@(.fill _ _ _ _ _) => o
  | o@(.paint _ _ _ _) => o
  | o@(.group _ _ _ _) => o
  | o@(.shade _ _) => o
  | o@(.outline _ _ _) => o
  | o@(.xobject _ _ _ _) => o
  | o@(.image _ _ _ _ _) => o
  | o@(.imageMissing _ _ _ _) => o

def artMoveList (onlyContent : Bool) (dx dy : Dim.Length) (acc : Array Pdf.ContentOp) :
    List Pdf.ContentOp → Array Pdf.ContentOp
  | [] => acc
  | o :: rest => artMoveList onlyContent dx dy (acc.push (artMoveOp onlyContent dx dy o)) rest

end

mutual

/-- The first glyph of every run replaced by `gid`, a glyph the file's own `/ToUnicode` never names. -/
def artRegidTextOp (gid : Nat) : Pdf.TextOp → Pdf.TextOp
  | .show items => .show (items.map fun it => match it with
      | .glyphs gs => .glyphs (if gs.isEmpty then gs else gs.set! 0 gid)
      | .kerned gs ns => .kerned (if gs.isEmpty then gs else gs.set! 0 gid) ns
      | a@(.adjust _) => a)
  | .marked t body => .marked t (artRegidTextList gid #[] body.toList)
  | o@(.scale _) => o
  | o@(.move _ _) => o
  | o@(.font _ _) => o
  | o@(.color _) => o

def artRegidTextList (gid : Nat) (acc : Array Pdf.TextOp) :
    List Pdf.TextOp → Array Pdf.TextOp
  | [] => acc
  | o :: rest => artRegidTextList gid (acc.push (artRegidTextOp gid o)) rest

end

mutual

def artRegidOp (gid : Nat) : Pdf.ContentOp → Pdf.ContentOp
  | .text ops => .text (artRegidTextList gid #[] ops.toList)
  | .marked t body => .marked t (artRegidList gid #[] body.toList)
  | o@(.fill _ _ _ _ _) => o
  | o@(.paint _ _ _ _) => o
  | o@(.group _ _ _ _) => o
  | o@(.shade _ _) => o
  | o@(.outline _ _ _) => o
  | o@(.xobject _ _ _ _) => o
  | o@(.image _ _ _ _ _) => o
  | o@(.imageMissing _ _ _ _) => o

def artRegidList (gid : Nat) (acc : Array Pdf.ContentOp) :
    List Pdf.ContentOp → Array Pdf.ContentOp
  | [] => acc
  | o :: rest => artRegidList gid (acc.push (artRegidOp gid o)) rest

end

/-- A file written from the fixture's own inputs with one page's operators replaced. -/
def artWriteWith (fs : Font.FontSet) (geom : Layout.Geom) (doc : Ir.Doc)
    (out : Layout.Out) (store : Image.Store)
    (f : Array (Array Pdf.ContentOp) → Array (Array Pdf.ContentOp)) : ByteArray :=
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let ops := Pdf.pageOps geom fs out.pages store tree
  Pdf.write geom fs out.pages doc.info store out.outline #[] tree (f ops)

/-- Page `i`'s operators rewritten, the rest untouched. -/
def artOnPage (i : Nat) (g : Array Pdf.ContentOp → Array Pdf.ContentOp)
    (ops : Array (Array Pdf.ContentOp)) : Array (Array Pdf.ContentOp) :=
  if h : i < ops.size then ops.set i (g ops[i]) else ops

/-- Page `j`'s operators replaced by page `i`'s. -/
def artCopyPage (i j : Nat) (ops : Array (Array Pdf.ContentOp)) :
    Array (Array Pdf.ContentOp) :=
  match ops[i]? with
  | some src => if j < ops.size then ops.set! j src else ops
  | none => ops

/-- A file read as a reading, with the declared area and whether the build
named a loss that accounts for ink outside it. -/
def artReadingOf (geom : Layout.Geom) (accounted : Bool) (pdf : ByteArray)
    (footline : Bool := false) :
    Except String ArtReading :=
  (readArtifact pdf).map fun pages =>
    { pages := pages, area := artBodyArea geom footline, accounted := accounted }

/-- Whether the build's diagnostics, elaboration and layout alike, name a loss accounting for ink
outside the declared area. -/
def artAccounted (diags : Array Diag) : Bool :=
  diags.any fun d => artOverflowCodes.contains d.code ||
    d.carries.any (artOverflowCodes.contains ·.code)

/-- Where the layout put each glyph of a page, in PDF user space and stream order, by
`Layout.setLine`'s scaling rule. -/
def artLaidGlyphs (geom : Layout.Geom) (p : Layout.PageOut) : Array Dim.Length := Id.run do
  let mut out : Array Dim.Length := #[]
  for l in Pdf.paintLines p do
    let mut x := geom.bleed + l.x
    for s in l.segs do
      match s with
      | .run _ _ _ w glyphs _ _ _ _ _ _ =>
        let mut adv : Dim.Length := 0
        for (_, _, a) in glyphs do
          out := out.push (x + adv + adv * l.expand / 1000)
          adv := adv + a
        x := x + w
      | .gap w _ | .decoratedGap w _ _ => x := x + w
      | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
      | .image _ w _ _ _ => x := x + w
      | .poly _ _ => pure ()
  return out

/-- Glyphs whose painted start misses the layout's by more than the file can state (half a
thousandth of the size plus `artSpellSlack`), the pen advanced by the file's own spellings. -/
def artGlyphPlacementOffences (laid : Array Dim.Length) (painted : Array (Dim.Length × Dim.Length)) :
    Array String := Id.run do
  if laid.size != painted.size then
    return #[s!"{painted.size} glyphs painted where the layout placed {laid.size}"]
  let mut out : Array String := #[]
  for h : k in [0:laid.size] do
    let (x, size) := painted[k]!
    let d := x - laid[k]
    if d.abs > (artSpellSlack + size / 2000).abs then
      out := out.push s!"glyph {k}: painted {(d : Dim.Length).toBpString}pt from its layout x"
  return out

/-- A page's painted glyph starts, in stream order, each with its run's size. -/
def artPaintedGlyphs (p : ArtPage) : Array (Dim.Length × Dim.Length) :=
  p.runs.flatMap fun r => r.glyphs.map fun (x, _) => (x, r.size)

/-- A font name without its subset tag, the six capitals and a plus a
subset's name opens with (ISO 32000-2 §9.6.4). -/
def artBaseName (n : String) : String :=
  let cs := n.toList
  if cs.length > 7 && cs[6]? == some '+' && (cs.take 6).all Char.isUpper then
    String.ofList (cs.drop 7)
  else n

/-- Each face the pages' own resources name: its `/FontName`, its embedded program, and every glyph
id the pages paint in it. -/
def artEmbedded (pdf : ByteArray) :
    Except String (Array (String × ByteArray × Array Nat)) := do
  let es := (← PdfRead.objects pdf).val
  let deref := PdfCensus.deref es
  let mut faces : Std.HashMap Nat String := {}
  let mut painted : Std.HashMap Nat (Array Nat) := {}
  for e in es do
    unless e.val.get? "Type" == some (.name "Page") do continue
    let res := deref ((e.val.get? "Resources").getD .null)
    let mut names : Std.HashMap String Nat := {}
    if let .dict fs := deref ((res.get? "Font").getD .null) then
      for (nm, v) in fs do
        let cid := match deref ((deref v).get? "DescendantFonts" |>.getD .null) with
          | .arr xs => deref (xs[0]?.getD .null)
          | d => d
        let fd := deref ((cid.get? "FontDescriptor").getD .null)
        let some (.name fn) := fd.get? "FontName" | throw s!"{nm}: its descriptor has no name"
        let some (.ref pn _) := (fd.get? "FontFile2").orElse fun _ => fd.get? "FontFile3"
          | throw s!"{fn}: no embedded program"
        names := names.insert nm pn
        faces := faces.insert pn fn
    let some (.ref cn _) := e.val.get? "Contents" | throw "a page has no /Contents reference"
    let some c := es.find? (·.num == cn) | throw "a page's /Contents names no object"
    let .ok (some data) := c.decoded | throw "a page content stream does not decode"
    let mut cur : Option Nat := none
    let mut stack : Array CTok := #[]
    for tok in scanContent data do
      match tok with
      | .op o =>
        if o == "Tf" then
          cur := (stack.findSome? fun | .name n => some n | _ => none).bind names.get?
        else if o == "TJ" || o == "Tj" then
          if let some pn := cur then
            for s in stack do
              if let .hex d := s then painted := painted.insert pn (painted.getD pn #[] ++ artCodes d)
        stack := #[]
      | t => stack := stack.push t
  let mut out : Array (String × ByteArray × Array Nat) := #[]
  for (pn, fn) in faces.toArray.qsort (fun a b => a.1 < b.1) do
    let some pe := es.find? (·.num == pn) | throw s!"{fn}: its program names no object"
    let .ok (some bytes) := pe.decoded | throw s!"{fn}: its program does not decode"
    out := out.push (fn, bytes, painted.getD pn #[])
  return out

/-- Every glyph run a file's forms paint, in each form's own text space, by the viewer's arithmetic
over the form's fonts. -/
def artFormRuns (pdf : ByteArray) : Except String (Array ArtRun) := do
  let es ← PdfRead.objects pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let mut out : Array ArtRun := #[]
  for e in esv do
    unless e.val.get? "Subtype" == some (.name "Form") do continue
    let mut fonts : Std.HashMap String ArtFont := {}
    if let .dict fs := deref ((deref ((e.val.get? "Resources").getD .null)).get? "Font" |>.getD .null) then
      for (nm, v) in fs do fonts := fonts.insert nm (artFontOf esv (deref v))
    if fonts.isEmpty then continue
    match e.decoded with
    | .ok (some data) => out := out ++ (evalContent fonts (scanContent data)).1
    | .ok none => throw "a form is not a stream"
    | .error err => throw s!"a form's stream does not decode: {err}"
  return out

/-- Each stretch the store's drawn figures set, with its size and every glyph's pen x from the run's
text origin. -/
def artFigureStretches (store : Image.Store) : Array (Array Dim.Length × Dim.Length) :=
  store.shaped.foldl (fun out fig? => match fig? with
    | some fig =>
      -- A symbol's text is written once, in its own form, however many uses paint it.
      let runs := fig.symbols.foldl (fun acc b => Gfx.Node.labelsList Gfx.Affine.unit acc b.toList)
        (Gfx.Node.labelsList Gfx.Affine.unit #[] fig.nodes.toList)
      runs.foldl (fun out (_, r) =>
        (Pdf.figureStretches r.glyphs).foldl (fun out (_, gs, x0) =>
          let (_, xs) := gs.foldl (fun (x, xs) (_, _, next) => (x + next, xs.push x)) (x0, #[])
          out.push (xs, r.size)) out) out
    | none => out) #[]

/-- Shaped stretches no painted run sets where shaping put them, within what the file can state. -/
def artFigureGlyphOffences (expected : Array (Array Dim.Length × Dim.Length)) (painted : Array ArtRun) :
    Array String := Id.run do
  let mut free := painted
  let mut out : Array String := #[]
  for (xs, size) in expected do
    let near (r : ArtRun) : Bool :=
      r.glyphs.size == xs.size && (r.glyphs.zip xs).all fun ((px, _), x) =>
        (px - x).abs ≤ (artSpellSlack + size / 2000).abs
    match free.findIdx? near with
    | some i => free := free.eraseIdx! i
    | none => out := out.push s!"a stretch of {xs.size} glyphs at {(xs[0]?.getD 0).toBpString}pt is painted nowhere it was shaped"
  return out

/-- A PDF matrix `[a b c d e f]` in points, as `Rat`. -/
abbrev PdfMat := Rat × Rat × Rat × Rat × Rat × Rat

/-- `m` then `n` (§8.3.4): a point maps through `m` first. -/
def PdfMat.then (m n : PdfMat) : PdfMat :=
  let (a, b, c, d, e, f) := m
  let (a', b', c', d', e', f') := n
  (a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d',
   e * a' + f * c' + e', e * b' + f * d' + f')

def PdfMat.apply (m : PdfMat) (x y : Rat) : Rat × Rat :=
  let (a, b, c, d, e, f) := m
  (a * x + c * y + e, b * x + d * y + f)

def PdfMat.unit : PdfMat := (1, 0, 0, 1, 0, 0)

/-- Every glyph a form's text shows, by the viewer's arithmetic, and what the form's clipping
`/BBox` leaves outside; returns the count read and the offences. -/
def formGlyphOffences (pdf : ByteArray) (fs : Font.FontSet)
    (boxOf : Array Rat → Array Rat := id) : Except String (Nat × Array String) := do
  let es ← PdfRead.objects pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let pt (v : Dim.Length) : Rat := v.toRat / (Dim.bp 1).toRat
  let mut seen := 0
  let mut out : Array String := #[]
  for e in esv do
    unless e.val.get? "Subtype" == some (.name "Form") do continue
    let bb : Array Rat := boxOf (match deref ((e.val.get? "BBox").getD .null) with
      | .arr xs => xs.map fun o => pt ((PdfRead.Obj.sp? o).getD 0)
      | _ => #[])
    let some bx0 := bb[0]? | throw "a form has no /BBox"
    let (by0, bx1, by1) := (bb[1]?.getD 0, bb[2]?.getD 0, bb[3]?.getD 0)
    let mut fonts : Std.HashMap String (ArtFont × Option Font) := {}
    if let .dict fd := deref ((deref ((e.val.get? "Resources").getD .null)).get? "Font" |>.getD .null) then
      for (nm, v) in fd do
        let o := deref v
        let base := match o.get? "BaseFont" with
          | some (.name n) => artBaseName n
          | _ => ""
        fonts := fonts.insert nm (artFontOf esv o, fs.fonts.find? (·.psName == base))
    let data ← match e.decoded with
      | .ok (some d) => pure d
      | _ => throw "a form's stream does not decode"
    let mut stack : Array CTok := #[]
    let mut ctm := PdfMat.unit
    let mut saved : Array PdfMat := #[]
    let mut tm := PdfMat.unit
    let mut size : Rat := 0
    let mut th : Rat := 1
    let mut font : Option (ArtFont × Option Font) := none
    let mut penX : Rat := 0
    for t in scanContent data do
      match t with
      | .op o =>
        let ns := stack.filterMap fun t => match t with
          | .num v _ => some (pt v)
          | _ => none
        if o == "q" then saved := saved.push ctm
        else if o == "Q" then
          ctm := saved.back?.getD PdfMat.unit
          saved := saved.pop
        else if o == "cm" && ns.size == 6 then
          ctm := PdfMat.then (ns[0]!, ns[1]!, ns[2]!, ns[3]!, ns[4]!, ns[5]!) ctm
        else if o == "BT" then
          tm := PdfMat.unit
          penX := 0
        else if o == "Tm" && ns.size == 6 then
          tm := (ns[0]!, ns[1]!, ns[2]!, ns[3]!, ns[4]!, ns[5]!)
          penX := 0
        else if o == "Tf" then
          let nm := (stack.findSome? fun t => match t with
            | .name n => some n
            | _ => none).getD ""
          font := fonts[nm]?
          size := ns[0]?.getD 0
        else if o == "Tz" then th := (ns[0]?.getD 100) / 100
        else if o == "TJ" || o == "Tj" then
          for it in stack do
            match it, font with
            | .hex d, some (af, face) =>
              for g in artCodes d do
                let w : Rat := pt (af.widths[g]?.getD af.defaultWidth) / 1000
                match face.bind (·.bounds g) with
                | some b =>
                  let upem : Rat := ((face.map (·.unitsPerEm)).getD 1000 : Nat)
                  let gx (u : Int) : Rat := penX + (u : Rat) / upem * size * th
                  let gy (u : Int) : Rat := (u : Rat) / upem * size
                  let corners := [(gx b.left, gy b.bottom), (gx b.right, gy b.bottom),
                    (gx b.left, gy b.top), (gx b.right, gy b.top)].map fun (x, y) =>
                      let (x, y) := tm.apply x y
                      ctm.apply x y
                  seen := seen + 1
                  let slack : Rat := 1 / 500
                  let inside := corners.all fun (x, y) =>
                    bx0 - slack ≤ x && x ≤ bx1 + slack && by0 - slack ≤ y && y ≤ by1 + slack
                  unless inside do
                    out := out.push s!"glyph {g} of a form paints outside its /BBox [{bx0} {by0} {bx1} {by1}]"
                | none => pure ()
                penX := penX + w * size * th
            | .num _ raw, _ =>
              let n : Rat := ((raw.toInt?.getD 0 : Int) : Rat)
              penX := penX - n / 1000 * size * th
            | _, _ => pure ()
        stack := #[]
      | other => stack := stack.push other
  return (seen, out)

/-- The artifact tier over the golden corpus: each fixture built as the driver builds it and every
claim judged on its bytes; a recorded offence must still fire. -/
def artifactCorpusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  for (n, p, _) in artKnownOffences do
    t s!"artifact offence row {n}/{p.name}: names a golden fixture" (goldenNames.contains n)
  t "artifact offence rows are distinct"
    (artKnownOffences.length ==
      (artKnownOffences.map fun (n, p, _) => s!"{n}/{p.name}").eraseDups.length)
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut bandsSeen := 0
  let mut multiPage := 0
  let mut contentPaths := 0
  let mut subsets := 0
  let mut figureStretches := 0
  let mut formGlyphs := 0
  for n in goldenNames do
    let (doc, diags) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc (some fs)
    let out := layoutOf fs doc geom (some pats) store
    let pdf := driverPdf fs geom doc out store
    let footline := doc.docClass.record.chrome && doc.foot.isNone &&
      (doc.chrome.hasFooter || doc.body.any fun b => match b with
        | .framefoot xs => !xs.isEmpty
        | _ => false)
    match artReadingOf geom (artAccounted (diags ++ out.diags)) pdf footline with
    | .error e => t s!"artifact {n}: the file reads back: {e}" false
    | .ok rd =>
      t s!"artifact {n}: the file's page count is the layout's \
({rd.pages.size} vs {out.pages.size})" (rd.pages.size == out.pages.size)
      if 1 < rd.pages.size then multiPage := multiPage + 1
      for p in rd.pages do
        bandsSeen := bandsSeen + p.bands.size
        contentPaths := contentPaths + (p.boxes.filter fun b => !b.isArtifact).size
      let placed := artGlyphPlacementOffences (out.pages.flatMap (artLaidGlyphs geom))
        (rd.pages.flatMap artPaintedGlyphs)
      t s!"artifact {n}: every glyph starts where the layout put it: {placed.toList.take 3}"
        placed.isEmpty
      let stretches := artFigureStretches store
      if !stretches.isEmpty then figureStretches := figureStretches + stretches.size
      match artFormRuns pdf with
      | .error e => t s!"artifact {n}: the file's forms read back: {e}" false
      | .ok runs =>
        let missed := artFigureGlyphOffences stretches runs
        t s!"artifact {n}: every figure glyph starts where shaping put it: {missed.toList.take 3}"
          missed.isEmpty
        -- A form's box clips, so a glyph outside it is one no viewer shows.
        match formGlyphOffences pdf fs with
        | .ok (glyphs, offs) =>
          if 0 < glyphs then formGlyphs := formGlyphs + glyphs
          t s!"artifact {n}: every glyph a form paints stands inside its box: {offs.toList.take 3}"
            offs.isEmpty
        | .error e => t s!"artifact {n}: the file's forms read back for their boxes: {e}" false
        let moved := stretches.map fun (xs, size) => (xs.map (· + Dim.pt 1), size)
        if !stretches.isEmpty then
          t s!"artifact {n}: a figure glyph a point from where it was painted is an offence"
            ((artFigureGlyphOffences moved runs).size == stretches.size)
      match artEmbedded pdf with
      | .error e => t s!"artifact {n}: its fonts read back: {e}" false
      | .ok faces =>
        for (fn, prog, gids) in faces do
          match fs.fonts.find? (·.psName == artBaseName fn) with
          | none => t s!"artifact {n}: {fn} names a face of the set" false
          | some f =>
            let src := Ink.Src.make f.data f.isCff f.numGlyphs
            let emb := Ink.Src.make prog f.isCff f.numGlyphs
            let lost := gids.filter fun g => emb.cmdsAt g != src.cmdsAt g
            t s!"artifact {n}: {fn} draws every glyph the pages paint as its face does: \
{lost.toList.take 5}" lost.isEmpty
            if artBaseName fn != fn then
              subsets := subsets + 1
              let dropped := (List.range f.numGlyphs).any fun g =>
                g != 0 && !gids.contains g && emb.cmdsAt g == some #[] && src.cmdsAt g != some #[]
              t s!"artifact {n}: {fn} is named a subset and is one"
                (prog.size < f.data.size && dropped)
            else
              let spared := (List.range f.numGlyphs).filter fun g =>
                g != 0 && !gids.contains g && src.cmdsAt g != some #[]
              t s!"artifact {n}: {fn} embeds whole only when its pages paint every glyph \
it draws: {spared.take 5}" spared.isEmpty
      for prop in artProps do
        let offs := match prop with
          | .markupInk => artMarkupOffences rd (inkMarkupAllowed n)
          | p => artOffences rd p
        if artKnownOffences.any fun (f, q, _) => f == n && q == prop then
          t s!"artifact {n}: the recorded offence against {prop.name} no longer \
fires — delete its row from artKnownOffences" (!offs.isEmpty)
        else
          t s!"artifact {n}: {prop.name}: {offs.toList}" offs.isEmpty
  t s!"artifact corpus: furniture bands are reached ({bandsSeen})" (0 < bandsSeen)
  t s!"artifact corpus: multi-page fixtures are read ({multiPage})" (1 < multiPage)
  t s!"artifact corpus: content paths and images are reached ({contentPaths})" (0 < contentPaths)
  t s!"artifact corpus: embedded faces are subsets ({subsets})" (0 < subsets)
  t s!"artifact corpus: drawn figures' text is reached ({figureStretches})" (0 < figureStretches)
  t s!"artifact corpus: glyphs inside figure forms are reached ({formGlyphs})" (0 < formGlyphs)

/-- Each claim broken once on a file the real writer produced, beside its untouched control. -/
def artifactMutantChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let build (n : String) :
      IO (Font.FontSet × Layout.Geom × Ir.Doc × Layout.Out × Image.Store) := do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc (some fs)
    return (fs, geom, doc, layoutOf fs doc geom (some pats) store, store)
  let judge (label : String) (prop : ArtProp) (geom : Layout.Geom) (pdf : ByteArray)
      (wantOffence : Bool) : IO Unit :=
    match artReadingOf geom false pdf with
    | .error e => t s!"artifact mutant {label}: reads back: {e}" false
    | .ok rd =>
      let offs := artOffences rd prop
      if wantOffence then
        t s!"artifact mutant {label}: {prop.name} refuses it" (!offs.isEmpty)
      else
        t s!"artifact mutant {label}: the control passes {prop.name}: {offs.toList}" offs.isEmpty
  let (fs, geom, doc, out, store) ← build "paragraphs"
  let plain := driverPdf fs geom doc out store
  let moved (onlyContent : Bool) (dx dy : Dim.Length) (page : Nat)
      (f : Font.FontSet) (g : Layout.Geom) (d : Ir.Doc) (o : Layout.Out)
      (s : Image.Store) : ByteArray :=
    artWriteWith f g d o s (artOnPage page (artMoveList onlyContent dx dy #[] ·.toList))
  judge "every Tm 200pt left of the page" .pageBox geom
    (moved false (-(Dim.pt 200)) 0 0 fs geom doc out store) true
  match artReadingOf geom true (moved false (-(Dim.pt 200)) 0 0 fs geom doc out store) with
  | .error e => t s!"artifact mutant ink off the page in a build that names it: reads back: {e}" false
  | .ok rd =>
    t "artifact mutant: ink off the page box is refused even where the build names the loss"
      (!(artOffences rd .pageBox).isEmpty)
  judge "paragraphs untouched" .pageBox geom plain false
  judge "content Tm 30pt into the margin" .bodyArea geom
    (moved true (-(Dim.pt 30)) 0 0 fs geom doc out store) true
  judge "paragraphs untouched" .bodyArea geom plain false
  judge "a glyph the /ToUnicode does not name" .glyphNames geom
    (artWriteWith fs geom doc out store (artOnPage 0 (artRegidList 60000 #[] ·.toList))) true
  judge "paragraphs untouched" .glyphNames geom plain false
  -- The lift is read off the layout, never a fitted constant.
  let (cf, cg, cd, co, cs) ← build "chrome"
  let lift : Dim.Length := ((co.pages[2]?).bind fun p => p.band.bind fun band =>
    (p.lines.find? fun l => !l.furniture && l.y > band).map fun l => l.y - band / 2).getD 0
  t "artifact mutant: the chrome fixture's third frame has a band and a body line below it"
    (0 < lift)
  judge "body prose lifted into the middle of a title band" .bandFree cg
    (moved true 0 lift 2 cf cg cd co cs) true
  judge "chrome untouched" .bandFree cg (driverPdf cf cg cd co cs) false
  let (of_, og, od, oo, os) ← build "overlays"
  judge "an overlay step's page replaced by the previous one" .pageBytes og
    (artWriteWith of_ og od oo os (artCopyPage 0 1)) true
  judge "overlays untouched" .pageBytes og (driverPdf of_ og od oo os) false
  -- The check judges the character, not its provenance: an authored `\verb` backslash is a witness.
  for (label, src, want) in [
      ("an authored backslash", dvDoc "" "a \\textbackslash{} b", true),
      ("authored braces", dvDoc "" "a \\{x\\} b", true),
      ("a verbatim run's own code", dvDoc "" "\\verb|\\foo{bar}|", true),
      ("an unmodelled command's argument", dvDoc "" "\\parbox{.25\\textwidth}{x}", false)] do
    let (d, _) := elabStr src
    let g := Layout.Geom.ofPage d.page
    let o := layoutOf oneFace d g (some pats)
    judge s!"markup ink: {label}" .markupInk g (driverPdf oneFace g d o) want

def artifactChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  artifactMutantChecks ref oneFace pats
  artifactCorpusChecks ref oneFace pats

/-- The palette role that declares the band, and the custom property the HTML backend names after
it. -/
def artBandRole : String := "frametitlebg"

/-- The custom property the HTML backend declares the band role under. -/
def artBandProp : String := (Ir.CssName.role .frameTitleBar).ident

/-- Whether a declaration list paints a `background` or `background-color` from the role's property,
bare or with a fallback. -/
def artPaintsFrom (role : String) (decls : String) : Bool :=
  (decls.splitOn ";").any fun d =>
    match d.splitOn ":" with
    | [] => false
    | prop :: rest =>
      let value := String.intercalate ":" rest
      (prop.trimAscii.toString == "background" ||
          prop.trimAscii.toString == "background-color") &&
        (hasStr value s!"var(--{role})" || hasStr value s!"var(--{role},")

/-- An element as the tree carries it: its tag and its classes. -/
abbrev ArtElem := String × Array String

/-- One compound selector and whether it must be a direct child of the one before; a selector is an
array of these, root first. -/
abbrev ArtStep := ArtElem × Bool

/-- One compound selector as the element it names: its tag (empty for classes only) and every class
it requires, pseudo-classes dropped. -/
def artCompound (tok : String) : Option ArtElem :=
  let bare := (tok.splitOn ":").headD tok
  let bits := (bare.splitOn ".").filter fun s => !s.isEmpty
  let tag := if bare.startsWith "." then "" else bits.headD ""
  let classes := (if bare.startsWith "." then bits else bits.drop 1).toArray
  if tag.isEmpty && classes.isEmpty then none else some (tag, classes)

/-- One selector as its chain of compounds, root first; a sibling combinator returns `none`, which
the judge reports. -/
def artSelChain (part : String) : Option (Array ArtStep) := Id.run do
  if part.any fun c => c == '+' || c == '~' then return none
  let toks := ((part.replace ">" " > ").splitOn " ").filter fun s => !s.isEmpty
  let mut steps : Array ArtStep := #[]
  let mut child := false
  for tok in toks.toArray do
    if tok == ">" then
      child := true
    else
      match artCompound tok with
      | none => return none
      | some e =>
        steps := steps.push (e, child)
        child := false
  if steps.isEmpty then return none else return some steps

/-- Every chain a selector list resolves to, one per comma-separated
selector this check can read. -/
def artSelChains (sel : String) : Array (Array ArtStep) :=
  ((sel.splitOn ",").filterMap artSelChain).toArray

/-- Does this element satisfy one compound? -/
def artCompMatches (c : ArtElem) (e : ArtElem) : Bool :=
  (c.1.isEmpty || e.1 == c.1) && c.2.all fun x => e.2.contains x

/-- Whether a selector chain matches an ancestor path ending at the rule's subject, matched right to
left; the greedy walk errs only towards failing. -/
def artChainMatchesPath (chain : Array ArtStep) (path : Array ArtElem) : Bool := Id.run do
  if chain.isEmpty || path.isEmpty then return false
  let subject := chain[chain.size - 1]!
  unless artCompMatches subject.1 path[path.size - 1]! do return false
  let mut ci := chain.size - 1
  let mut pi := path.size - 1
  let mut mustBeChild := subject.2
  for _ in [0:path.size + 1] do
    if ci == 0 then break
    if pi == 0 then return false
    let step := chain[ci - 1]!
    if artCompMatches step.1 path[pi - 1]! then
      ci := ci - 1
      pi := pi - 1
      mustBeChild := step.2
    else if mustBeChild then
      return false
    else
      pi := pi - 1
  return ci == 0

mutual

/-- Whether a subtree ships an element the chain selects, each element judged against its own
ancestors. -/
def artChainInOne (chain : Array ArtStep) (path : Array ArtElem) : Html.Node → Bool
  | .text _ => false
  | .style _ => false
  | .script _ _ => false
  | .elem t attrs kids =>
    let cls := ((attrs.find? fun a => a.1 == "class").map (·.2)).getD ""
    let classes := ((cls.splitOn " ").filter fun s => !s.isEmpty).toArray
    let here := path.push (t, classes)
    artChainMatchesPath chain here || artChainInList chain here kids.toList

def artChainInList (chain : Array ArtStep) (path : Array ArtElem) :
    List Html.Node → Bool
  | [] => false
  | k :: rest => artChainInOne chain path k || artChainInList chain path rest

end

mutual

/-- Every stylesheet a typed tree carries, concatenated, read from its `Html.Node.style` nodes. -/
def artTreeCssOne (acc : String) : Html.Node → String
  | .style css => acc ++ css
  | .text _ => acc
  | .script _ _ => acc
  | .elem _ _ kids => artTreeCssList acc kids.toList

def artTreeCssList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => artTreeCssList (artTreeCssOne acc k) rest

end

/-- The ancestors `emitTree` does not return, so a selector anchored at `body` resolves. -/
def artBodyPath : Array ArtElem := #[("html", #[]), ("body", #[])]

/-- The selectors under which a stylesheet paints a background from a role. -/
def artGroundSelectors (role : String) (css : String) : Array String :=
  (artCssBlocks css).filterMap fun (sel, decls) =>
    if artPaintsFrom role decls then some sel else none

/-- The selectors under which a stylesheet paints the band. -/
def artBandSelectors (css : String) : Array String :=
  artGroundSelectors artBandProp css

/-- Every way a document's two artifacts disagree about its furniture band, each named with the end
that lost it: a painted band implies the declared pair, which implies the HTML rule and element. -/
def artBandOffences (painted declared : Bool) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let sels := artBandSelectors css
  if painted && !declared then
    out := out.push s!"a page paints a top-edge furniture band while the design \
declares no band pair: --{artBandProp} is unset"
  if !sels.isEmpty && !declared then
    out := out.push s!"the stylesheet paints from --{artBandProp} with no band \
pair declared: {sels.toList}"
  if declared then
    if sels.isEmpty then
      out := out.push s!"the design declares a band pair and no rule paints a \
background from --{artBandProp}"
    else
      let readable := sels.filter fun s => !(artSelChains s).isEmpty
      if readable.isEmpty then
        out := out.push s!"no selector painting the band resolves to an element \
this check can read: {sels.toList}"
      else unless readable.any fun s =>
          (artSelChains s).any fun c => artChainInList c artBodyPath body.toList do
        out := out.push s!"every rule painting the band selects an element the \
tree does not ship: {readable.toList}"
  return out

/-- The golden fixtures whose two artifacts disagree about their furniture band: a ratchet read both
ways. -/
def artBandParityOffences : List (String × String) := []

/-- The band judge broken once for each way the band can go, with two controls that must pass:
element and rule renamed together, and a reference carrying a fallback. -/
def artBandMutants : List (String × Bool × Bool × String × Array Html.Node × Bool) :=
  let header := Html.elem "header" #[Html.elem "h2" #[Html.text "Title"]]
  let slide (kid : Html.Node) : Array Html.Node :=
    #[Html.elem "section" #[kid] #[("class", "slide")]]
  let live := slide header
  let bandRule (sel : String) : String :=
    sel ++ " { background: var(--ltx-frametitlebg);\n  color: var(--ltx-frametitlefg); }\n"
  [ ("the shape the backend writes", true, true, bandRule "section.slide > header", live, false),
    ("the poster's own carrier instead", true, true,
      bandRule "body > header.headline",
      #[Html.elem "header" #[] #[("class", "headline")]], false),
    ("the bar declared only inside an at-rule", true, true,
      "@media screen {\n" ++ bandRule "section.slide > header" ++ "}\n", live, false),
    ("the reference carrying a fallback", true, true,
      "section.slide > header { background: var(--ltx-frametitlebg, #333); }\n", live, false),
    ("the element and its rule renamed together", true, true,
      bandRule "section.slide > div.band-top",
      slide (Html.elem "div" #[] #[("class", "band-top")]), false),
    ("nothing declared and nothing painted", false, false, "", live, false),
    ("the rule gone", true, true, "", live, true),
    ("the element gone", true, true, bandRule "section.slide > header",
      slide (Html.elem "p" #[Html.text "body"]), true),
    ("the rule moved and the element left behind", true, true,
      bandRule "section.slide > div.band-top", live, true),
    ("the element lifted out of the slide", true, true,
      bandRule "section.slide > header", #[header], true),
    ("the property misspelled", true, true,
      "section.slide > header { background: var(--ltx-frametitlebackground); }\n", live, true),
    ("the reference off the ground and onto a border", true, true,
      "section.slide > header { border-color: var(--ltx-frametitlebg); }\n", live, true),
    ("a rule painting a band the design never declared", false, false,
      bandRule "section.slide > header", live, true),
    ("bytes painting a band the design never declared", true, false, "", live, true),
    ("the selector unreadable", true, true,
      bandRule "section.slide > header + header", live, true)]

/-- Every fixture's painted furniture band held against the HTML the same document emits, the judge
first refusing its own mutants. -/
def artBandParityChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  t s!"the band's key is a declared consumed role"
    (Ir.Design.consumedRoles.contains artBandRole)
  for (n, _) in artBandParityOffences do
    t s!"band parity offence row {n}: names a golden fixture" (goldenNames.contains n)
  for (label, painted, declared, css, body, wantOffence) in artBandMutants do
    let offs := artBandOffences painted declared css body
    if wantOffence then
      t s!"band parity mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"band parity mutant, {label}: the judge accepts it: {offs.toList}" offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut paintedSeen := 0
  let mut declaredSeen := 0
  let mut carriedSeen := 0
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc (some fs)
    let out := layoutOf fs doc geom (some pats) store
    match readArtifact (driverPdf fs geom doc out store) with
    | .error e => t s!"band parity {n}: the file reads back: {e}" false
    | .ok pages =>
      -- A fill against the top edge; a bottom band is a footer's ground, a different claim.
      let painted := pages.any fun p => p.bands.any fun b => b.y1 ≥ p.box.y1
      let declared := (Ir.Design.ofDoc doc).frametitle.isSome
      let (head, body, _) := HtmlDoc.emitTree {} doc
      let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
      if painted then paintedSeen := paintedSeen + 1
      if declared then declaredSeen := declaredSeen + 1
      if declared && !(artBandSelectors css).isEmpty then carriedSeen := carriedSeen + 1
      let offs := artBandOffences painted declared css body
      if artBandParityOffences.any fun (f, _) => f == n then
        t s!"band parity {n}: the recorded offence no longer fires — its two \
artifacts now agree; delete its row" (!offs.isEmpty)
      else
        t s!"band parity {n}: {offs.toList}" offs.isEmpty
  -- Non-vacuity: each link of the chain needs its own witness.
  t s!"band parity: painted bands are reached ({paintedSeen})" (0 < paintedSeen)
  t s!"band parity: declared band pairs are reached ({declaredSeen})" (0 < declaredSeen)
  t s!"band parity: carried bands are reached ({carriedSeen})" (0 < carriedSeen)

/-- The palette role a page's own ground is declared under, and the property the HTML backend names
after it. -/
def artGroundRole : String := "titlepagebg"

/-- The custom property the HTML backend declares the title-page ground under. -/
def artGroundProp : String := (Ir.CssName.role .titlePageGround).ident

/-- Every way a document's two artifacts disagree about a title page's declared ground, by the
band's three links; `painted` means a full-page fill in the declared colour. -/
def artGroundOffences (painted declared : Bool) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let sels := artGroundSelectors artGroundProp css
  if painted && !declared then
    out := out.push s!"a page paints a full-page ground while the design \
declares no title-page pair: --{artGroundProp} is unset"
  if !sels.isEmpty && !declared then
    out := out.push s!"the stylesheet paints from --{artGroundProp} with no \
title-page pair declared: {sels.toList}"
  if declared then
    unless painted do
      out := out.push s!"the design declares a title-page ground and no page \
ships a full-page fill in it"
    if sels.isEmpty then
      out := out.push s!"the design declares a title-page pair and no rule \
paints a background from --{artGroundProp}"
    else
      let readable := sels.filter fun s => !(artSelChains s).isEmpty
      if readable.isEmpty then
        out := out.push s!"no selector painting the ground resolves to an \
element this check can read: {sels.toList}"
      else unless readable.any fun s =>
          (artSelChains s).any fun c => artChainInList c artBodyPath body.toList do
        out := out.push s!"every rule painting the ground selects an element \
the tree does not ship: {readable.toList}"
  return out

/-- The ground judge broken once for each way the ground can go, with the band's two controls. -/
def artGroundMutants :
    List (String × Bool × Bool × String × Array Html.Node × Bool) :=
  let title := Html.elem "h1" #[Html.text "Title"]
  let page (cls : String) : Array Html.Node :=
    #[Html.elem "section" #[title] #[("class", cls)]]
  let live := page "slide title-page"
  let groundRule (sel : String) : String :=
    sel ++ " { background: var(--ltx-titlepagebg);\n  color: var(--ltx-titlepagefg); }\n"
  [ ("the shape the backend writes", true, true,
      groundRule "section.slide.title-page", live, false),
    ("the ground declared only inside an at-rule", true, true,
      "@media screen {\n" ++ groundRule "section.slide.title-page" ++ "}\n", live, false),
    ("the reference carrying a fallback", true, true,
      "section.slide.title-page { background: var(--ltx-titlepagebg, #101822); }\n",
      live, false),
    ("the element and its rule renamed together", true, true,
      groundRule "section.slide.title-ground",
      page "slide title-ground", false),
    ("nothing declared and nothing painted", false, false, "", live, false),
    ("the rule gone", true, true, "", live, true),
    ("the class gone from the element", true, true,
      groundRule "section.slide.title-page", page "slide", true),
    ("the rule moved and the element left behind", true, true,
      groundRule "section.slide.title-ground", live, true),
    ("the PDF page never painted it", false, true,
      groundRule "section.slide.title-page", live, true),
    ("the property misspelled", true, true,
      "section.slide.title-page { background: var(--ltx-titlepageground); }\n",
      live, true),
    ("the reference off the ground and onto a border", true, true,
      "section.slide.title-page { border-color: var(--ltx-titlepagebg); }\n",
      live, true),
    ("a rule painting a ground the design never declared", false, false,
      groundRule "section.slide.title-page", live, true),
    ("a page painting a ground the design never declared", true, false, "", live, true),
    ("the selector unreadable", true, true,
      groundRule "section.slide.title-page + section", live, true)]

/-- A page's ground is declared once and both artifacts paint it: a full-page fill in the declared
colour, a rule painting the role, and the element it selects. -/
def artGroundParityChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  t s!"the ground's key is a declared consumed role"
    (Ir.Design.consumedRoles.contains artGroundRole)
  for (label, painted, declared, css, body, wantOffence) in artGroundMutants do
    let offs := artGroundOffences painted declared css body
    if wantOffence then
      t s!"ground parity mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"ground parity mutant, {label}: the judge accepts it: {offs.toList}"
        offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut paintedSeen := 0
  let mut declaredSeen := 0
  let mut carriedSeen := 0
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc (some fs)
    let out := layoutOf fs doc geom (some pats) store
    let ground := (Ir.Design.ofDoc doc).titlepage.map (·.bg)
    -- A full-page fill in the declared colour separates a page's own ground from the document's.
    let fullPageIn (c : Ir.Color) (p : Layout.PageOut) : Bool :=
      p.fills.any fun f =>
        f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH &&
          f.color == c
    let painted := match ground with
      | some c => out.pages.any (fullPageIn c)
      | none => false
    if let some c := ground then
      t s!"ground parity {n}: the declared ground is on one page only"
        ((out.pages.filter (fullPageIn c)).size == 1)
    let declared := ground.isSome
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
    if painted then paintedSeen := paintedSeen + 1
    if declared then declaredSeen := declaredSeen + 1
    if declared && !(artGroundSelectors artGroundProp css).isEmpty then
      carriedSeen := carriedSeen + 1
    t s!"ground parity {n}: {(artGroundOffences painted declared css body).toList}"
      (artGroundOffences painted declared css body).isEmpty
  t s!"ground parity: painted grounds are reached ({paintedSeen})" (0 < paintedSeen)
  t s!"ground parity: declared grounds are reached ({declaredSeen})" (0 < declaredSeen)
  t s!"ground parity: carried grounds are reached ({carriedSeen})" (0 < carriedSeen)
  -- Literal text mixed with the title datum keeps the built-in title layout.
  let mixedSrc :=
    "\\documentclass[aspectratio=169]{beamer}\n" ++
    "\\definecolor{probeNight}{HTML}{202833}\n" ++
    "\\setbeamertemplate{title page}{\\begin{tikzpicture}[remember picture,overlay]" ++
    "\\fill[probeNight] (current page.south west) rectangle (current page.north east);" ++
    "\\node[anchor=west,text=white] at (current page.west) {Label: \\inserttitle};" ++
    "\\end{tikzpicture}\\null}\n" ++
    "\\title{Invented Heading}\\begin{document}\\titlepage\\end{document}\n"
  let (mixedDoc, mixedDs) := elabStr mixedSrc
  let mixedGeom := Layout.Geom.ofPage mixedDoc.page
  let mixedOut := layoutOf oneFace mixedDoc mixedGeom
  let mixedGround : Ir.Color := { r := 0x20, g := 0x28, b := 0x33 }
  let mixedPainted := (mixedOut.pages[0]?.bind (·.fills[0]?)).any fun f =>
    f.x == 0 && f.y == 0 && f.w == mixedGeom.pageW && f.h == mixedGeom.pageH &&
      f.color == mixedGround
  let mixedDeclared := (Ir.Design.ofDoc mixedDoc).titlepage.map (·.bg) == some mixedGround
  let (mixedHead, mixedBody, _) := HtmlDoc.emitTree {} mixedDoc
  let mixedCss := artTreeCssList (artTreeCssList "" mixedHead.toList) mixedBody.toList
  let mixedOffences := artGroundOffences mixedPainted mixedDeclared mixedCss mixedBody
  let mixedLayoutDs := mixedDs.filter (·.code == "W0363")
  t "a mixed title node is one accounting for its fallback and retained ground"
    (mixedLayoutDs.size == 1 && mixedLayoutDs.any fun d =>
      hasStr d.message "custom arrangement falls back" &&
      hasStr d.message "readable full-page ground stays")
  t s!"a readable full-page fill survives title-layout fallback in both artifacts: \
{mixedOffences.toList}"
    (mixedPainted && hasStr mixedCss "--ltx-titlepagebg: #202833;" && mixedOffences.isEmpty)

/-- The property a frame's plain ground is declared under: the palette's `bg`. -/
def artStageRole : String := (Ir.CssName.role .page).ident

/-- The last value a declaration list gives one custom property. -/
def artVarIn (decls : String) (name : String) : Option String :=
  ((decls.splitOn ";").filterMap fun d =>
    match d.splitOn ":" with
    | [k, v] => if k.trimAscii.toString == s!"--{name}" then some v.trimAscii.toString else none
    | _ => none).getLast?

/-- The last value the stylesheet's top-level `:root` blocks give a custom property. -/
def artRootVar (css : String) (name : String) : Option String :=
  ((artTopCssBlocks css).filterMap fun (sel, decls) =>
    if sel == ":root" then artVarIn decls name else none).back?

mutual

/-- The plain frames' stages and the stages of content outside every frame, in document order, each
with the value the nearest inline redefinition of the role gives it. -/
def artStagesOne (inl : Option String) (acc : Array (Option String)) :
    Html.Node → Array (Option String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let own := (attrs.find? (·.1 == "style")).bind fun a => artVarIn a.2 artStageRole
    let inl := own.orElse fun _ => inl
    let cs := (((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " "
    let acc := if t == "section" && cs.contains "slide" && !cs.contains "standout" &&
        !cs.contains "title-page" then acc.push inl else acc
    artStagesList inl acc kids.toList

def artStagesList (inl : Option String) (acc : Array (Option String)) :
    List Html.Node → Array (Option String)
  | [] => acc
  | k :: rest => artStagesList inl (artStagesOne inl acc k) rest

end

/-- Each frame's declared ground keyed by its block, read at `Ir.frameGroundOf`; a title page
answers `none`. -/
def artFrameGroundsAt (doc : Ir.Doc) : Array (Nat × Option (Option Ir.Color)) := Id.run do
  -- A page's source index counts the blocks `Layout.pdfView` keeps, so frames are read there.
  let view := Layout.pdfView doc
  let mut pal := view.palette
  let mut out : Array (Nat × Option (Option Ir.Color)) := #[]
  for h : i in [0:view.body.size] do
    match view.body[i] with
    | .setPalette p => pal := p
    | .frame _ standout valign _ _ =>
      out := out.push (i,
        if valign matches .golden then none else some (Ir.frameGroundOf pal standout valign))
    | _ => pure ()
  return out

/-- The frames' declared grounds in document order, read at `Ir.frameGroundOf`, and a deck's run of
content outside every frame at the page's ground in force where the run ships. -/
def artFrameGrounds (doc : Ir.Doc) (includeStandout : Bool := false) :
    Array (Option Ir.Color) := Id.run do
  let deck := doc.docClass.record.model == .frame
  let mut pal := doc.palette
  let mut out : Array (Option Ir.Color) := #[]
  let mut outsideRun := false
  for h : i in [0:doc.body.size] do
    let b := doc.body[i]
    if deck && outsideRun && doc.outside i b == .stage then
      out := out.push (Ir.Design.declared? pal .page)
      outsideRun := false
    match b with
    | .setPalette p => pal := p
    | .frame _ standout valign _ _ =>
      if (includeStandout || !standout) && !(valign matches .golden) then
        out := out.push (Ir.frameGroundOf pal standout valign)
    | _ => pure ()
    if deck && doc.outside i b == .content then outsideRun := true
  if outsideRun then out := out.push (Ir.Design.declared? pal .page)
  return out

/-- The path a plain stage stands on in the emitted tree. -/
def artStagePath : Array ArtElem := artBodyPath ++ #[("main", #[]), ("section", #["slide"])]

/-- Every way the HTML deck disagrees with the palette in force about a plain frame's ground and
ink. -/
def artStageGroundOffences (expected : Array (Option Ir.Color)) (css : String)
    (body : Array Html.Node) : Array String := Id.run do
  let mut out : Array String := #[]
  let stages := artStagesList none #[] body.toList
  if stages.size != expected.size then
    out := out.push s!"{expected.size} plain frames and {stages.size} plain stages"
  if expected.any Option.isSome then
    let blocks := (artCssBlocks css).filter fun (sel, _) =>
      (artSelChains sel).any fun c => artChainMatchesPath c artStagePath
    unless blocks.any fun (_, d) => artPaintsFrom artStageRole d do
      out := out.push s!"no rule paints the plain stage from --{artStageRole}"
    unless blocks.any fun (_, d) => (d.splitOn ";").any fun x =>
        match x.splitOn ":" with
        | [p, v] => p.trimAscii.toString == "color" && hasStr v "var(--ltx-fg"
        | _ => false do
      out := out.push "no rule inks the plain stage from --ltx-fg"
  let root := artRootVar css artStageRole
  for i in [0:min stages.size expected.size] do
    let got := stages[i]!.orElse fun _ => root
    let want := (expected[i]!.orElse fun _ => Ir.Design.at {} .light .page).map HtmlDoc.cssColor
    if got != want then
      out := out.push s!"plain frame {i + 1}: the stage resolves --{artStageRole} to \
{got}, the palette in force declares {want}"
  return out

/-- A deck whose middle frame stands in a body epoch with its own dark ground and light ink,
restored after. -/
def artEpochDeck : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++
  "\\begin{frame}{On the document's ground}\nA first frame.\n\\end{frame}\n" ++
  "\\palette{ bg = #14213D, fg = #F5F5F5, muted = #F5F5F5 }\n" ++
  "\\begin{frame}{On a declared dark ground}\nA second frame.\n\\end{frame}\n" ++
  "\\palette{ bg = #FFFFFF, fg = #000000, muted = #696664 }\n" ++
  "\\begin{frame}{Back on a light ground}\nA third frame.\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- One breakable frame in a dark epoch, taller than its stage, so its continuation page stands on
the epoch's ground too. -/
def artEpochSpillDeck : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++
  "\\palette{ bg = #14213D, fg = #F5F5F5 }\n" ++
  "\\begin{frame}[allowframebreaks]{A frame that continues}\n\\begin{itemize}\n" ++
  String.join ((List.range 24).map fun i => s!"\\item Filler beat {i + 1}.\n") ++
  "\\end{itemize}\n\\end{frame}\n\\end{document}\n"

/-- The judge broken once for each link, and the shape the backend writes
accepted: the rule gone, the rule reading the stylesheet's surface, the
epoch's redefinition dropped, and the ink rule gone. -/
def artStageMutants : List (String × String × Array Html.Node × Bool) :=
  let stage (style : String) : Html.Node :=
    Html.elem "section" #[] (#[("class", "slide")] ++
      (if style.isEmpty then #[] else #[("style", style)]))
  let root := ":root {\n    --ltx-bg: #fdfcf9;\n}\n"
  let rule (bg : String) : String :=
    s!"@media screen \{\nsection.slide, section.section-page \{ background: {bg}; \
color: var(--ltx-fg); }\n}\n"
  let live := #[Html.elem "main" #[stage "", stage "--ltx-bg: #14213d"]]
  [ ("the shape the backend writes", root ++ rule "var(--ltx-bg)", live, false),
    ("the rule gone", root, live, true),
    ("the stage painting the code surface", root ++ rule "var(--ltx-code-surface)", live, true),
    ("the epoch's redefinition dropped", root ++ rule "var(--ltx-bg)",
      #[Html.elem "main" #[stage "", stage ""]], true),
    ("the ink rule gone", root ++
      "section.slide { background: var(--ltx-bg); }\n", live, true)]

/-- Every page of a frame not standing on the frame's declared ground, read off `Layout.Out` and
keyed by the page's source frame. -/
def artPageGroundOffences (geom : Layout.Geom) (expected : Array (Nat × Option (Option Ir.Color)))
    (pages : Array Layout.PageOut) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut i := 0
  for p in pages do
    i := i + 1
    let some origin := p.frameOrigin | continue
    let k := origin.source
    let some (_, entry) := expected.find? (·.1 == k) | do
      out := out.push s!"page {i} names frame {k} without a declared ground entry"
      continue
    let some want := entry | continue
    let ground := p.fills[0]?.bind fun f =>
      if f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH then some f.color
      else none
    if ground != want then
      out := out.push s!"page {i} (frame {k}) ships the ground \
{ground.map HtmlDoc.cssColor}, the palette in force declares {want.map HtmlDoc.cssColor}"
  return out

/-- A plain frame's ground is the palette in force, and both artifacts paint it. -/
def artStageGroundChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let want : Array (Option Ir.Color) :=
    #[some { r := 0xFD, g := 0xFC, b := 0xF9 }, some { r := 0x14, g := 0x21, b := 0x3D }]
  for (label, css, body, wantOffence) in artStageMutants do
    let offs := artStageGroundOffences want css body
    if wantOffence then
      t s!"stage ground mutant, {label}: the judge refuses it" (!offs.isEmpty)
    else
      t s!"stage ground mutant, {label}: the judge accepts it: {offs.toList}" offs.isEmpty
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut judged := 0
  let mut declared := 0
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    unless doc.docClass == .slides do continue
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := artTreeCssList (artTreeCssList "" head.toList) body.toList
    let expected := artFrameGrounds doc
    judged := judged + 1
    if expected.any Option.isSome then declared := declared + 1
    let offs := artStageGroundOffences expected css body
    t s!"stage ground {n}: {offs.toList}" offs.isEmpty
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc geom none (← corpusStore doc (some fs))
    let pageOffs := artPageGroundOffences geom (artFrameGroundsAt doc) out.pages
    t s!"stage ground {n} pdf: {pageOffs.toList}" pageOffs.isEmpty
  t s!"stage ground: slides fixtures are judged ({judged})" (0 < judged)
  t s!"stage ground: declared grounds are reached ({declared})" (0 < declared)
  let (edoc, eds) := elabStr artEpochDeck
  t s!"stage ground epoch deck elaborates clean: {eds.toList.map (·.code)}" eds.isEmpty
  let expected := artFrameGrounds edoc
  t "stage ground epoch deck: the middle frame declares its own ground"
    (expected == #[(edoc.palette.find? "bg"), some { r := 0x14, g := 0x21, b := 0x3D }, some { r := 0xFF, g := 0xFF, b := 0xFF }])
  let (ehead, ebody, _) := HtmlDoc.emitTree {} edoc
  let ecss := artTreeCssList (artTreeCssList "" ehead.toList) ebody.toList
  let offs := artStageGroundOffences expected ecss ebody
  t s!"stage ground epoch deck html: {offs.toList}" offs.isEmpty
  let egeom := Layout.Geom.ofPage edoc.page
  let eout := layoutOf oneFace edoc egeom
  t s!"stage ground epoch deck: one page per frame ({eout.pages.size})" (eout.pages.size == 3)
  let pageOffs := artPageGroundOffences egeom (artFrameGroundsAt edoc) eout.pages
  t s!"stage ground epoch deck pdf: {pageOffs.toList}" pageOffs.isEmpty
  let (sdoc, _) := elabStr artEpochSpillDeck
  let sgeom := Layout.Geom.ofPage sdoc.page
  let sout := layoutOf oneFace sdoc sgeom
  t s!"stage ground spill deck: the frame continues ({sout.pages.size} pages)"
    (sout.pages.size ≥ 2 && sout.pages.all (·.frame == some 1))
  let spillOffs := artPageGroundOffences sgeom (artFrameGroundsAt sdoc) sout.pages
  t s!"stage ground spill deck pdf: {spillOffs.toList}" spillOffs.isEmpty
  let (mixed, _) := elabStr (deck169 "\\theme{moloch}"
    ("\\begin{frame}{Before}FirstBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}\n" ++
     "\\begin{frame}{After}LastBody\\end{frame}"))
  let mgeom := Layout.Geom.ofPage mixed.page
  let mout := layoutOf oneFace mixed mgeom
  let mgrounds := artFrameGroundsAt mixed
  t "stage ground: an unnumbered standout keeps its own inversion between ordinary frames"
    (artFrameGrounds mixed true == #[mixed.palette.find? "bg",
        some (Ir.Design.ofDoc mixed).standout.bg, mixed.palette.find? "bg"] &&
      mout.pages.map (·.frame) == #[some 1, none, some 2] &&
      (artPageGroundOffences mgeom mgrounds mout.pages).isEmpty)
  let missingFill := mout.pages.mapIdx fun i p => if i == 1 then { p with fills := #[] } else p
  t "stage ground: the PDF judge rejects a missing standout fill and an unknown frame"
    (!(artPageGroundOffences mgeom mgrounds missingFill).isEmpty &&
      !(artPageGroundOffences mgeom #[] mout.pages).isEmpty)
  -- beamer's `background canvas` bg: the document's ground in the preamble, an epoch's in the body.
  let canvas := "\\setbeamercolor{background canvas}{bg=#F0E8D8}\n"
  let frame (s : String) := s!"\\begin\{frame}\{{s}}\nx\n\\end\{frame}\n"
  let (pdoc, pds) := elabStr ("\\documentclass{beamer}\n" ++ canvas ++
    "\\begin{document}\n" ++ frame "One" ++ "\\end{document}\n")
  t s!"background canvas in the preamble declares the document's ground: {pds.toList.map (·.code)}"
    (pdoc.palette.find? "bg" == some { r := 0xF0, g := 0xE8, b := 0xD8 } &&
     pds.all (·.severity == .note))
  let (bdoc, bds) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
    frame "One" ++ canvas ++ frame "Two" ++ "\\end{document}\n")
  t s!"background canvas in the body declares the frames after it: {bds.toList.map (·.code)}"
    (artFrameGrounds bdoc == #[bdoc.palette.find? "bg", some { r := 0xF0, g := 0xE8, b := 0xD8 }] &&
     bds.all (·.severity == .note))
  let bgeom := Layout.Geom.ofPage bdoc.page
  let bOffs := artPageGroundOffences bgeom (artFrameGroundsAt bdoc) (layoutOf oneFace bdoc bgeom).pages
  let (bhead, bbody, _) := HtmlDoc.emitTree {} bdoc
  let bcss := artTreeCssList (artTreeCssList "" bhead.toList) bbody.toList
  let bHtml := artStageGroundOffences (artFrameGrounds bdoc) bcss bbody
  t s!"background canvas in the body reaches both artifacts: {bOffs.toList} {bHtml.toList}"
    (bOffs.isEmpty && bHtml.isEmpty)
  -- the page of content outside the frames ships under the ground in force at its end, as TeX's
  let (ldoc, lds) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
    frame "One" ++ "Outside before words.\n\n" ++ canvas ++ "Outside after words.\n\n" ++
    frame "Two" ++ "\\end{document}\n")
  let (lhead, lbody, _) := HtmlDoc.emitTree {} ldoc
  let lHtml := artStageGroundOffences (artFrameGrounds ldoc)
    (artTreeCssList (artTreeCssList "" lhead.toList) lbody.toList) lbody
  let canvasBg : Ir.Color := { r := 0xF0, g := 0xE8, b := 0xD8 }
  let lgeom := Layout.Geom.ofPage ldoc.page
  let lout := layoutOf oneFace ldoc lgeom
  let looseGround := (lout.pages.find? (·.frameOrigin.isNone)).bind fun p => p.fills[0]?.bind fun f =>
    if f.x == 0 && f.y == 0 && f.w == lgeom.pageW && f.h == lgeom.pageH then some f.color else none
  t s!"background canvas in the body grounds the page and stage of content outside frames: {lHtml.toList}"
    (artFrameGrounds ldoc == #[ldoc.palette.find? "bg", some canvasBg, some canvasBg] &&
      lds.all (·.severity == .note) && lHtml.isEmpty && looseGround == some canvasBg)
  t "background canvas has no ink: its fg is named, not taken"
    (warnCodes ("\\documentclass{beamer}\n\\setbeamercolor{background canvas}{fg=#101010}\n" ++
      "\\begin{document}\n" ++ frame "One" ++ "\\end{document}\n") == ["W0104"])

/-- Every font descriptor a written PDF carries: its `/FontName` and its
`/Flags`. -/
def artDescriptorFlags (pdf : ByteArray) : Except String (Array (String × Int)) := do
  let es := (← PdfRead.objects pdf).val
  return es.filterMap fun e =>
    if e.val.get? "Type" == some (.name "FontDescriptor") then
      match e.val.get? "FontName", (e.val.get? "Flags").bind Obj.int? with
      | some (.name n), some f => some (n, f)
      | _, _ => none
    else none

/-- The generic that closes a page's `--font-<slot>` stack, read from the
last declaration — the one the cascade keeps. -/
def artStackGeneric (html slot : String) : Option String := do
  let parts := html.splitOn ("--font-" ++ slot ++ ": ")
  if parts.length < 2 then none
  let decl ← parts.getLast?
  let stack ← (decl.splitOn ";").head?
  ((stack.splitOn ",").getLast?).map (·.trimAscii.toString)

def artifactPitchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"artifact pitch: leantex builds:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode != 0 then return
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.createDirAll (dir / "home")
    for e in ← (System.FilePath.mk testFonts).readDir do
      if e.fileName.endsWith ".otf" || e.fileName.endsWith ".ttf" then
        IO.FS.writeBinFile (dir / "fonts" / e.fileName) (← IO.FS.readBinFile e.path)
    IO.FS.writeFile (dir / "fonts.tex") (← IO.FS.readFile "testdata/corpus/fonts.tex")
    let page (body : String) : String :=
      "\\documentclass{article}\n\\fonts{ dir = \"fonts\", body = \"" ++ body ++ "\" }\n" ++
      "\\output{ formats = html }\n\\begin{document}\nPlain words.\n\\end{document}\n"
    IO.FS.writeFile (dir / "codebody.tex") (page "Source Code Pro")
    IO.FS.writeFile (dir / "serifbody.tex") (page "Source Serif Pro")
    let run (name : String) : IO (UInt32 × String) := do
      let p ← IO.Process.output
        { cmd := ".lake/build/bin/leantex"
          args := #[(dir / s!"{name}.tex").toString, "-o", (dir / "out").toString ++ "/"]
          env := #[("XDG_CACHE_HOME", some (dir / "cache").toString),
            ("HOME", some (dir / "home").toString), ("PATH", some (dir / "no-tools").toString),
            ("LEANTEX_FONT_PATH", none), ("LEANTEX_FONT", none)] }
      return (p.exitCode, p.stdout ++ p.stderr)
    let (code, log) ← run "fonts"
    t s!"artifact pitch: fonts.tex builds: {log}" (code == 0)
    match artDescriptorFlags (← IO.FS.readBinFile (dir / "out" / "fonts.pdf")) with
    | .error e => t s!"artifact pitch: fonts.pdf reads back: {e}" false
    | .ok fds =>
      let flagsOf (n : String) : Option Int := (fds.find? (artBaseName ·.1 == n)).map (·.2)
      t s!"artifact pitch: fonts.pdf declares Source Code Pro fixed-pitch: {fds}"
        ((flagsOf "SourceCodePro-Regular").map (· % 2 == 1) == some true)
      t s!"artifact pitch: fonts.pdf declares Source Serif Pro proportional: {fds}"
        ((flagsOf "SourceSerifPro-Regular").map (· % 2 == 0) == some true)
    for (name, want) in [("codebody", "monospace"), ("serifbody", "serif")] do
      let (code, log) ← run name
      t s!"artifact pitch: {name}.tex builds: {log}" (code == 0)
      let html ← IO.FS.readFile (dir / "out" / s!"{name}.html")
      let got := artStackGeneric html "body"
      t s!"artifact pitch: {name}.html closes the body stack with {want}: {got}"
        (got == some want)

/-- A kerning face and its italic in every slot: Source Serif Pro, whose "Ta" pair is −41/1000 em. -/
def artKernSet : IO Font.FontSet := do
  let load (f : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ f)) with
    | .ok font => pure font
    | .error e => throw (IO.userError s!"{f}: {e}")
  let reg ← load "SourceSerifPro-Regular.otf"
  let ital ← load "SourceSerifPro-RegularIt.otf"
  return { fonts := #[reg, ital]
           index := ((List.range 3).flatMap fun slot =>
             [((slot, 400, false), 0), ((slot, 700, false), 0),
              ((slot, 400, true), 1), ((slot, 700, true), 1)]).toArray }

/-- Pairs the face kerns hard, an italic word right after them, a second
justified line with another, and a centred line of kerned pairs. -/
def artKernSrc : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++
  "Ta Ta Ta To To Te Te Ya Ya AV AV AV Wa Wa \\emph{Tote} end. " ++
  "Yo Yo Tw Tw Ty Vo Vo Wo Wo LT LT Ly Ly To Te Ta and \\emph{Wave} Ta To, Ty Tw Yo.\n" ++
  "\\begin{center}\nTaTaTaTaTaTaTaTaTaTa\n\\end{center}\n\\end{document}\n"

/-- Runs starting inside the rendered extent of the run before them on the same baseline in another
face. -/
def artFaceChangeOffences (pages : Array ArtPage) : Array String := Id.run do
  let mut out : Array String := #[]
  for h : i in [0:pages.size] do
    let rs := pages[i].runs
    for k in [1:rs.size] do
      let a := rs[k - 1]!
      let b := rs[k]!
      if a.y == b.y && a.face != b.face && b.x < a.x1 - artSpellSlack then
        out := out.push
          s!"page {i + 1}: '{b.text}' starts {(a.x1 - b.x).toBpString}pt inside '{a.text}'"
  return out

def kernPlacementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fs ← artKernSet
  let (doc, _) := elabStr artKernSrc
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fs doc geom
  match readArtifact (driverPdf fs geom doc out) with
  | .error e => t s!"kerns: the kerned page reads back: {e}" false
  | .ok pages =>
    t "kerns: the fixture ships one page" (pages.size == 1 && out.pages.size == 1)
    let laid := out.pages.flatMap (artLaidGlyphs geom)
    let offs := artGlyphPlacementOffences laid (pages.flatMap artPaintedGlyphs)
    t s!"kerns: every glyph starts where the layout put it: {offs.toList.take 5}"
      (!laid.isEmpty && offs.isEmpty)
    let faceOffs := artFaceChangeOffences pages
    t s!"kerns: a run after a font change starts at or after the run before it: {faceOffs.toList}"
      faceOffs.isEmpty
    t "kerns: the fixture changes face on a baseline (the claim is not vacuous)"
      (pages.any fun p => (List.range (p.runs.size - 1)).any fun k =>
        p.runs[k]!.y == p.runs[k + 1]!.y && p.runs[k]!.face != p.runs[k + 1]!.face)
    -- The centred line: the page's lowest body baseline.
    let body := pages[0]!.runs.filter (!·.isArtifact)
    let lowest := body.foldl (fun m r => min m r.y) (body[0]?.map (·.y) |>.getD 0)
    let line := body.filter (·.y == lowest)
    let x0 := line.foldl (fun m r => min m r.x) (line[0]?.map (·.x) |>.getD 0)
    let x1 := line.foldl (fun m r => max m r.x1) 0
    let area := artBodyArea geom
    let off := (x0 + x1) - (area.x0 + area.x1)
    t s!"kerns: the centred line is centred as painted ({(off / 2).toBpString}pt off its axis)"
      (!line.isEmpty && off.abs ≤ 2 * artSpellSlack.abs)
