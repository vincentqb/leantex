module

public import Tests.Support
public import LeanTex.Core.PdfTextRead
public import LeanTex.Core.PdfContent
public import LeanTex.Core.PdfContentText

public section

open LeanTex.Core

namespace Tests

/-- A text's characters with white space set aside. -/
def inkOf (s : String) : List Char := s.toList.filter fun c => !c.isWhitespace

/-- A simple font whose byte `k` reads as the `k`-th string of `text`. -/
def textFont (text : Array String) : PdfFont.Loaded :=
  { program := .missing, codes := .simple #[] #[] text, losses := #[] }

/-- The items a content stream yields under resources holding one font `F1`. -/
def readWith (font : PdfFont.Loaded) (src : String) (props : List (String × PdfRead.Obj) := []) :
    Array PdfTextRead.Item :=
  let res : PdfTextRead.Res := { fonts := Std.HashMap.ofList [("F1", font)], props := Std.HashMap.ofList props }
  (PdfTextRead.readToks res .unmarked (PdfContentLex.scan src.toUTF8)).1

/-- The runs' text and marks, for comparison. -/
def itemsView (items : Array PdfTextRead.Item) : List (String × PdfTextRead.Mark) :=
  items.toList.filterMap fun
    | .text m _ s => some (s, m)
    | .form .. => none

/-- The runs' text and breaks, for comparison. -/
def breaksView (items : Array PdfTextRead.Item) : List (String × PdfTextRead.Brk) :=
  items.toList.filterMap fun
    | .text _ b s => some (s, b)
    | .form .. => none

/-- A simple font whose byte `k` reads as the `k`-th string of `text`, each code `w`
thousandths wide. -/
def wideFont (text : Array String) (w : Rat) : PdfFont.Loaded :=
  { program := .missing, codes := .simple #[] (text.map fun _ => w) text, losses := #[] }

/-- A file of numbered objects, the first the catalog, with its cross-reference table. -/
def tinyPdf (objs : Array String) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n"
  let mut offs : Array Nat := #[]
  for (o, i) in objs.zipIdx do
    offs := offs.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{o}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for k in offs do
    let d := toString k
    out := out ++ "".pushn '0' (10 - d.length) ++ d ++ " 00000 n \n"
  out := out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n"
  return out.toUTF8

/-- A stream object holding `data`. -/
def streamObj (dict data : String) : String :=
  s!"<< {dict} /Length {data.utf8ByteSize} >>\nstream\n{data}\nendstream"

/-- A one-page file showing `content` in Helvetica as `F1`, its XObjects `xobjects`, its catalog
carrying `catalog`, and `more` objects numbered from 6. -/
def onePage (content : String) (xobjects catalog : String) (more : Array String) : ByteArray :=
  tinyPdf (#[s!"<< /Type /Catalog /Pages 2 0 R {catalog} >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 100] /Resources << /Font << /F1 4 0 R >> \
/XObject << {xobjects} >> >> /Contents 5 0 R >>",
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
    streamObj "" content] ++ more)

/-- A segment's characters as a viewer reads them: a body line's line-end hyphen as the soft
hyphen its span reads as, a held picture label's as its glyphs. -/
def segReadChars (held : Bool) : Layout.Seg → List Char
  | s@(.run _ _ _ _ glyphs _ _ _ _ _ attr) =>
    if !held && Pdf.lineHyphen attr glyphs then Pdf.generatedHyphen.toList else s.glyphChars
  | s => s.glyphChars

/-- Whether a page line is a picture label the picture sets. -/
def heldLine (p : Layout.PageOut) (l : Layout.LineOut) : Bool :=
  Pdf.heldBy (Pdf.routesLabels p.inks) (Pdf.inkLabelKeys p.inks) l

/-- A page line's characters as a viewer reads them. -/
def lineReadChars (p : Layout.PageOut) (l : Layout.LineOut) : List Char :=
  l.segs.toList.flatMap (segReadChars (heldLine p l))

/-- Tokens as operators, each after its operands. -/
def opGroups (toks : List PdfContentLex.Tok) : List (List PdfRead.Obj × String) :=
  (toks.foldl (fun (acc, vs) t => match t with
    | .val o => (acc, vs.push o)
    | .op n => (acc.push (vs.toList, n), #[])
    | .inline _ _ => (acc, vs)) ((#[] : Array (List PdfRead.Obj × String)), (#[] : Array PdfRead.Obj))).1.toList

/-- The writer's operand spellings as the content tokenizer reads them back: a length's and a
scaling's numbers, a colour's operators with their operands. -/
def writerSpell : PdfContent.Spell where
  len x := (PdfContentLex.numberObj x.toBpString).getD .null
  scale p := (PdfContentLex.numberObj s!"{p / 10}.{p % 10}").getD .null
  color c := opGroups (PdfContentLex.scan c.pdfFill.toUTF8).toList

/-- Tokens compared one by one. -/
def tokEq : PdfContentLex.Tok → PdfContentLex.Tok → Bool
  | .val a, .val b => a == b
  | .op a, .op b => a == b
  | _, _ => false

/-- Token lists compared one by one. -/
def toksEq (a b : List PdfContentLex.Tok) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => tokEq x y

/-- A text with each run of white space one space, none at either end. -/
def wsNorm (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

/-- A page's lines as a viewer reads their glyphs, in paint order: a space where the pen, past a
run's advances under the line's horizontal scaling, falls a fifth of its size short of the next
glyph, and a line feed between lines. -/
def paintWords (p : Layout.PageOut) : String :=
  (Pdf.paintLines p).foldl (fun acc l => Id.run do
    let held := heldLine p l
    let mut out := if acc.isEmpty then acc else acc.push '\n'
    let mut gap : Int := 0
    let mut last : Option Dim.Length := none
    for seg in l.segs do
      match seg with
      | s@(.run _ _ _ w glyphs size _ _ _ _ _) =>
        let sz := if size == 0 then l.size else size
        if glyphs.isEmpty then gap := gap + w.units else
          if let some ls := last then
            if 5 * gap > ls.units then out := out.push ' '
          for c in segReadChars held s do out := out.push c
          let drawn := glyphs.foldl (fun (s : Int) (_, _, a) => s + a.units) 0 * (1000 + l.expand)
          gap := w.units - drawn / 1000
          last := some sz
      | .gap w _ | .decoratedGap w .. | .rule w .. | .decoration _ w .. | .image _ w .. =>
        gap := gap + w.units
      | .poly _ _ => pure ()
    return out) ""

/-- The PDF text reader decodes each shown string under its marked content, and every corpus
page's bytes read back as its lines' glyphs in paint order with their word and line breaks, the
structure tree referencing each identified sequence once. -/
def pdfTextChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let font := textFont #["", "a", "b", "c"]
  t "pdf text: a string reads through its font's codes"
    (itemsView (readWith font "BT /F1 12 Tf [<01>-200<0203>] TJ ET") == [("a", .unmarked), ("bc", .unmarked)])
  t "pdf text: an artifact's text stands under the artifact"
    (itemsView (readWith font "BT /F1 12 Tf /Artifact BMC (\\001) Tj EMC ET") == [("a", .artifact)])
  t "pdf text: a sequence's identifier marks its text, and a nested sequence with none inherits it"
    (itemsView (readWith font "BT /F1 12 Tf /P << /MCID 4 >> BDC (\\001) Tj /Span BMC (\\002) Tj EMC EMC ET") ==
      [("a", .content 4), ("b", .content 4)])
  t "pdf text: ActualText stands for its sequence's shown text, once"
    (itemsView (readWith font
      "BT /F1 12 Tf /Span << /ActualText (xyz) >> BDC (\\001\\002) Tj (\\003) Tj EMC ET") ==
      [("xyz", .unmarked)])
  t "pdf text: a named property list resolves through the resources"
    (itemsView (readWith font "BT /F1 12 Tf /P /MC0 BDC (\\001) Tj EMC ET"
      [("MC0", .dict #[("MCID", .int 7)])]) == [("a", .content 7)])
  t "pdf text: a string shown with no font set is a loss, never text"
    ((PdfTextRead.readToks default .unmarked (PdfContentLex.scan "BT (\\001) Tj ET".toUTF8)).2.size == 1)
  t "pdf text: ActualText stands under its own sequence's identifier"
    (itemsView (readWith font "BT /F1 12 Tf /Span << /MCID 5 /ActualText (fi) >> BDC (\\001) Tj EMC ET") ==
      [("fi", .content 5)])
  t "pdf text: an artifact's content stays an artifact whatever identifier a nested sequence holds"
    (itemsView (readWith font "BT /F1 12 Tf /Artifact BMC /P << /MCID 2 >> BDC (\\001) Tj EMC EMC ET") ==
      [("a", .artifact)])
  t "pdf text: Q restores the font q saved"
    (itemsView (readWith font
      "BT /F1 12 Tf q /F2 8 Tf Q (\\001) Tj ET") == [("a", .unmarked)])
  let wide := wideFont #["", "a", "b", "c"] 500
  t "pdf text: a pen jump past a fifth of the size is a word break, a kern is none"
    (breaksView (readWith wide "BT /F1 10 Tf 1 0 0 1 0 0 Tm [(\\001) -30 (\\002) -300 (\\003)] TJ ET") ==
      [("a", .line), ("b", .none), ("c", .word)])
  t "pdf text: a moved baseline is a line break"
    (breaksView (readWith wide "BT /F1 10 Tf 1 0 0 1 0 0 Tm (\\001) Tj 1 0 0 1 0 -12 Tm (\\002) Tj ET") ==
      [("a", .line), ("b", .line)])
  t "pdf text: the break before a sequence ActualText replaces stands before its text"
    (breaksView (readWith wide
      "BT /F1 10 Tf 1 0 0 1 0 0 Tm (\\001) Tj 1 0 0 1 0 -12 Tm /Span << /ActualText (xy) >> BDC \
(\\002) Tj 1 0 0 1 40 -12 Tm (\\003) Tj EMC ET") == [("a", .line), ("xy", .line)])
  t "pdf text: rotated text breaks along its own baseline"
    (breaksView (readWith wide "BT /F1 10 Tf 0 1 -1 0 100 100 Tm (\\001\\002\\003) Tj ET") ==
      [("abc", .line)])
  t "pdf text: text a transformation moves breaks where it lands on the page"
    (breaksView (readWith wide
      "BT /F1 10 Tf (\\001) Tj ET q 1 0 0 1 0 -20 cm BT /F1 10 Tf (\\002) Tj ET Q \
BT /F1 10 Tf 1 0 0 1 5 -20 Tm (\\003) Tj ET") == [("a", .line), ("b", .line), ("c", .none)])
  let tagged (k : String) (more : Array String) := onePage
    "/P << /MCID 0 >> BDC BT /F1 10 Tf 1 0 0 1 10 50 Tm (first) Tj ET EMC \
/P << /MCID 1 >> BDC BT /F1 10 Tf 1 0 0 1 10 30 Tm (second) Tj ET EMC" ""
    s!"/StructTreeRoot 6 0 R" (#[s!"<< /Type /StructTreeRoot /K {k} >>",
      "<< /Type /StructElem /S /P /Pg 3 0 R /K 1 >>", "<< /Type /StructElem /S /P /Pg 3 0 R /K 0 >>"] ++ more)
  t "pdf text: a tagged file reads in its structure's order, not its paint order"
    (PdfTextRead.structureText (tagged "[7 0 R 8 0 R]" #[]) == .ok "second\nfirst" &&
      ((PdfTextRead.extract (tagged "[7 0 R 8 0 R]" #[])).map (·.contentText true)) == .ok "first\nsecond")
  t "pdf text: a structure element's kids may stand in another object"
    (PdfTextRead.structureText (tagged "9 0 R" #["[8 0 R 7 0 R]"]) == .ok "first\nsecond")
  let selfForm := onePage "/Fm0 Do" "/Fm0 6 0 R" ""
    #[streamObj "/Type /XObject /Subtype /Form /BBox [0 0 1 1] /Resources << /XObject << /Fm0 6 0 R >> >>"
      "/Fm0 Do"]
  t "pdf text: a form painting itself is a loss, read once"
    (match PdfTextRead.extract selfForm with
      | .ok x => x.losses.any (·.endsWith "paints itself")
      | .error _ => false)
  let fan (k : Nat) : String :=
    if k == 11 then streamObj "/Type /XObject /Subtype /Form /BBox [0 0 1 1]"
      "BT /F1 10 Tf (x) Tj ET"
    else streamObj s!"/Type /XObject /Subtype /Form /BBox [0 0 1 1] /Resources << /Font << /F1 4 0 R >> \
/XObject << /Fm {k + 7} 0 R >> >>" "/Fm Do /Fm Do /Fm Do /Fm Do"
  let fanned := onePage "/Fm Do" "/Fm 6 0 R" "" ((List.range 12).toArray.map fan)
  t "pdf text: forms that paint forms many times stop at the reading's budget"
    (match PdfTextRead.extract fanned with
      | .ok x => x.losses.any (·.endsWith "budget")
      | .error _ => false)
  t "pdf text: a code with no text is a loss"
    ((PdfTextRead.readToks { fonts := Std.HashMap.ofList [("F1", font)], props := {} } .unmarked
      (PdfContentLex.scan "BT /F1 12 Tf (\\000) Tj ET".toUTF8)).2.size == 1)
  t "pdf text: a UTF-16 ActualText decodes"
    (PdfTextRead.textString? ⟨#[0xFE, 0xFF, 0x20, 0x10]⟩ == some "‐")
  let ink : Ir.Ink := { name := "Spot", c := 0, m := 1, y := 1, k := 0 }
  let colors : List Ir.Color := [Ir.Color.black, { r := 200, g := 30, b := 30 },
    { r := 10, g := 20, b := 30, cmyk := some (100, 200, 300, 400) },
    { r := 0, g := 0, b := 0, pdfModel := some (.gray "0.5") },
    { r := 0, g := 0, b := 0, pdfModel := some (.rgb "0.1" "0.2" "1") },
    { r := 0, g := 0, b := 0, pdfModel := some (.cmyk "0" "0.25" "1" "0") },
    { r := 0, g := 0, b := 0, pdfModel := some (.separation ink (1 / 2)) }]
  let sample : Array Pdf.TextOp := #[.scale 20, .move (Dim.pt 10) (Dim.bp 80), .font 0 (Dim.pt 12)] ++
    colors.toArray.map Pdf.TextOp.color ++
    #[.show #[.kerned #[0x24, 0x25] #[0, -417], .glyphs #[0x26], .adjust 12],
      .marked (.content "P" 3 0) #[.show #[.glyphs #[1, 2]]],
      .marked (.artifact (some .pagination)) #[.show #[.kerned #[3, 4] #[-50, 0]]],
      .marked (.artifact none) #[.show #[.glyphs #[5]]],
      .marked (.artifact (some .layout)) #[.show #[.glyphs #[6]]],
      .marked (.artifact (some .page)) #[.show #[.glyphs #[7]]],
      .marked (.span Pdf.generatedHyphen) #[.show #[.glyphs #[0x10]]]]
  t "pdf text: the writer's text object scans back as the text-operator tokens the reading is proved over, a colour as its own operators"
    (toksEq (PdfContentLex.scan (Pdf.render #[.text sample]).toUTF8).toList
      ([.op "BT"] ++ PdfContent.TextOp.toksList writerSpell sample.toList ++ [.op "ET"]))
  t "pdf text: every colour model the writer sets in a text object is operators the text reading passes"
    (colors.all fun c => (writerSpell.color c).all fun o => PdfContent.quietOp o.2)
  let cspace : Array (Nat × Nat × Nat) := #[(1, 0, 0x80), (2, 0x8100, 0xFEFF)]
  let ctext : Std.HashMap Nat String := Std.HashMap.ofList [(0x41, "A"), (0x8140, "B")]
  let cfont : PdfFont.Loaded :=
    ⟨.missing, .composite cspace #[(0, 0xFFFF, 0)] none false {} 1000 ctext false, #[]⟩
  t "pdf text: a mixed-width codespace reads each code by the first range length holding it"
    (((cfont.codes? ⟨#[0x41, 0x81, 0x40, 0xFF]⟩).toList.map fun c => (c.code, c.bytes, c.text)) ==
      [(0x41, 1, "A"), (0x8140, 2, "B"), (0xFF, 1, "")])
  let hgeom : Layout.Geom :=
    { pageW := (Dim.pt 90), pageH := (Dim.pt 400), hmargin := (Dim.pt 10), vmargin := (Dim.pt 10)
      fontSize := (Dim.pt 10), hyphenate := true, justify := true }
  let hdoc : Ir.Doc := { body := #[.para #[.text
    "Extraordinarily comprehensive internationalization considerations accompany representative \
documentation throughout"]] }
  let hout := Layout.run hgeom fs (some Hyphen.english.get) hdoc
  let hyphens := hout.pages.toList.foldl (fun n p => p.lines.toList.foldl (fun n l =>
    n + (l.segs.toList.filter fun s => !(segReadChars false s == s.glyphChars)).length) n) 0
  match PdfTextRead.extract (Pdf.write hgeom fs hout.pages hdoc.info) with
  | .error e => t s!"pdf text: the hyphenated paragraph reads ({e})" false
  | .ok x =>
    let text := x.contentText true
    let src := inkOf "Extraordinarily comprehensive internationalization considerations accompany \
representative documentation throughout"
    let soft := (text.splitOn Pdf.generatedHyphen).length - 1
    t "pdf text: each hyphen the breaker sets at a line end reads back as a soft hyphen ending its line"
      (0 < hyphens && soft == hyphens && (text.splitOn (Pdf.generatedHyphen ++ "\n")).length - 1 == hyphens &&
        !text.toList.contains '-' &&
        (inkOf (String.ofList (text.toList.filter (· != '\u00AD')))).take src.length == src)
  t "pdf text: a generated hyphen's span opens with its soft hyphen as UTF-16 ActualText"
    (Pdf.MarkTag.opener (.span Pdf.generatedHyphen) == "/Span << /ActualText <FEFF00AD> >> BDC")
  let mut docs := 0
  for name in goldenNames do
    let (doc, _) ← goldenDoc name
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf fs doc
    let pdf := Pdf.write geom fs out.pages doc.info
    match PdfTextRead.extract pdf with
    | .error e => t s!"pdf text: {name}: the file reads ({e})" false
    | .ok x =>
      docs := docs + 1
      t s!"pdf text: {name}: one text per page" (x.pages.size == out.pages.size)
      t s!"pdf text: {name}: the reading meets no loss" x.losses.isEmpty
      let mut i := 0
      for (p, (_, runs)) in out.pages.zip x.pages do
        t s!"pdf text: {name} page {i}: the bytes read as the lines' glyphs in paint order"
          (inkOf (PdfTextRead.runsText runs) ==
            inkOf (String.ofList ((Pdf.paintLines p).flatMap (lineReadChars p))))
        t s!"pdf text: {name} page {i}: the bytes break words and lines where the layout leaves room"
          (wsNorm (PdfTextRead.runsText runs) == wsNorm (paintWords p))
        i := i + 1
      match PdfRead.Doc.ofBytes pdf with
      | .error e => t s!"pdf text: {name}: the file opens ({e})" false
      | .ok d =>
        match PdfTextRead.leavesOf d with
        | .error e => t s!"pdf text: {name}: the structure tree reads ({e})" false
        | .ok leaves =>
          let refs := leaves.toList.filterMap fun
            | .mcr p m => some (p, m)
            | .actual _ => none
          let shown := x.pages.toList.flatMap fun (num, runs) =>
            ((runs.toList.filterMap fun r => match r.mark, num with
              | .content m, some p => some (p, m)
              | _, _ => none).eraseDups)
          t s!"pdf text: {name}: the structure tree references each identified sequence shown, once"
            (refs.Nodup && shown.all refs.contains && refs.all shown.contains)
  t s!"pdf text: the corpus is read ({docs} documents)" (0 < docs)

end Tests
