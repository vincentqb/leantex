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

/-- The PDF text reader decodes each shown string under its marked content, and every corpus
page's bytes read back as its lines' glyphs in paint order, the structure tree reaching each
identified sequence once. -/
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
        i := i + 1
      match PdfTextRead.structureText pdf with
      | .error e => t s!"pdf text: {name}: the structure tree reads ({e})" false
      | .ok s =>
        let tagged := x.pages.foldl (fun acc (_, runs) =>
          acc ++ PdfTextRead.runsText (runs.filter fun r => match r.mark with
            | .content _ => true
            | .artifact | .unmarked => false)) ""
        t s!"pdf text: {name}: the structure tree reads every identified sequence once"
          ((inkOf s).mergeSort (fun a b => decide (a ≤ b)) == (inkOf tagged).mergeSort (fun a b => decide (a ≤ b)))
  t s!"pdf text: the corpus is read ({docs} documents)" (0 < docs)

end Tests
