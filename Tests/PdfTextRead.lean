module

public import Tests.Support
public import LeanTex.Core.PdfTextRead
public import LeanTex.Core.PdfContent

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
    | .form _ _ => none

/-- The runs' text and breaks, for comparison. -/
def breaksView (items : Array PdfTextRead.Item) : List (String × PdfTextRead.Brk) :=
  items.toList.filterMap fun
    | .text _ b s => some (s, b)
    | .form _ _ => none

/-- A simple font whose byte `k` reads as the `k`-th string of `text`, each code `w`
thousandths wide. -/
def wideFont (text : Array String) (w : Rat) : PdfFont.Loaded :=
  { program := .missing, codes := .simple #[] (text.map fun _ => w) text, losses := #[] }

/-- A text with each run of white space one space, none at either end. -/
def wsNorm (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

/-- A page's lines as a viewer reads their glyphs, in paint order: a space where the pen, past a
run's advances under the line's horizontal scaling, falls a fifth of its size short of the next
glyph, and a line feed between lines. -/
def paintWords (p : Layout.PageOut) : String :=
  (Pdf.paintLines p).foldl (fun acc l => Id.run do
    let mut out := if acc.isEmpty then acc else acc.push '\n'
    let mut gap : Int := 0
    let mut last : Option Dim.Length := none
    for seg in l.segs do
      match seg with
      | .run _ _ _ w glyphs size _ _ _ _ _ =>
        let sz := if size == 0 then l.size else size
        if glyphs.isEmpty then gap := gap + w.units else
          if let some ls := last then
            if 5 * gap > ls.units then out := out.push ' '
          for (_, c, _) in glyphs do out := out.push c
          let drawn := glyphs.foldl (fun (s : Int) (_, _, a) => s + a.units) 0 * (1000 + l.expand)
          gap := w.units - drawn / 1000
          last := some sz
      | .gap w _ | .decoratedGap w _ _ | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ _ _ =>
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
  t "pdf text: a code with no text is a loss"
    ((PdfTextRead.readToks { fonts := Std.HashMap.ofList [("F1", font)], props := {} } .unmarked
      (PdfContentLex.scan "BT /F1 12 Tf (\\000) Tj ET".toUTF8)).2.size == 1)
  t "pdf text: a UTF-16 ActualText decodes"
    (PdfTextRead.textString? ⟨#[0xFE, 0xFF, 0x20, 0x10]⟩ == some "‐")
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
            inkOf (String.ofList ((Pdf.paintLines p).flatMap Layout.LineOut.glyphChars)))
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
