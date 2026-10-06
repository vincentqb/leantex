import LeanTex.Core.Pdf
import LeanTex.Core.Image

open LeanTex.Core
open LeanTex.Core.Dim

/-! The selection invariant: page ordinals follow `/Kids` depth-first,
regardless of object numbers or `/Count`; each selected leaf carries its
nearest inherited boxes, resources, and rotation. A nonzero effective
rotation is refused identically whether direct or indirect, on an ancestor or leaf;
the nearest declaration, including zero, overrides its ancestors without
affecting siblings. A missing ordinal or an encountered cycle is refused,
never replaced by a different page. All PDFs below are invented, with
drawing operators instead of fonts or external files. -/

private def selectionPdf (objs : Array String) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{obj}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    let padded := String.ofList (List.replicate (10 - digits.length) '0') ++ digits
    out := out ++ s!"{padded} 00000 n \n"
  out := out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\n"
  out := out ++ s!"startxref\n{xref}\n%%EOF\n"
  return out.toUTF8

private def selectionStream (content : String) (attrs : String := "") : String :=
  s!"<< /Length {content.utf8ByteSize} {attrs} >>\nstream\n{content}\nendstream"

private def firstInk := "q /Opacity gs 1 0 0 rg 5 7 100 60 re f Q"
private def middleInkA := "q 0 1 0 rg"
private def middleInkB := "15 10 25 15 re f Q"
private def lastInk := "q 0 0 1 rg 20 30 90 40 re f /Tile Do Q"
private def tileInk := "q /Opacity gs 0 0 3 4 re f Q"

/-- Leaves are objects 15, 4, 6, in that order. The empty trailing branch
is deliberate: the final kid is not necessarily a page. Boxes and resource
dictionaries include indirect values, sibling overrides, and an unused
self-reference in a resource form (legal graph sharing, not a page cycle). -/
private def nestedSelectionPdf (cropped : Bool) (count : Nat := 1) : ByteArray :=
  let branchCrop := if cropped then " /CropBox [5 7 105 67]" else ""
  let leafCrop := if cropped then " /CropBox [95 65 15 10]" else ""
  let lastCrop := if cropped then " /CropBox 11 0 R" else ""
  selectionPdf #[
    "<< /Type /Catalog /Pages 2 0 R /PageLabels << /Nums [0 << /St 901 >>] >> >>",
    s!"<< /Type /Pages /Kids [8 0 R 3 0 R 14 0 R] /Count {count} \
      /MediaBox [0 0 120 80] /Resources 12 0 R >>",
    s!"<< /Type /Pages /Parent 2 0 R /Kids [6 0 R] /Count 700 \
      /MediaBox 10 0 R{lastCrop} /Resources 13 0 R >>",
    s!"<< /Type /Page /Parent 8 0 R /Contents [9 0 R 16 0 R] \
      /MediaBox [0 0 400 300]{leafCrop} /Resources << >> >>",
    selectionStream lastInk,
    "<< /Type /Page /Parent 3 0 R /Contents 5 0 R >>",
    selectionStream firstInk,
    s!"<< /Type /Pages /Parent 2 0 R /Kids [15 0 R 4 0 R] /Count 0{branchCrop} >>",
    selectionStream middleInkA,
    "[10 20 210 120]",
    "[20 30 180 90]",
    "<< /ExtGState << /Opacity 17 0 R >> >>",
    "<< /XObject << /Tile 18 0 R >> >>",
    "<< /Type /Pages /Parent 2 0 R /Kids [] /Count 9999 >>",
    "<< /Type /Page /Parent 8 0 R /Contents 7 0 R >>",
    selectionStream middleInkB,
    "<< /Type /ExtGState /CA 0.75 /ca 0.75 >>",
    selectionStream tileInk
      "/Type /XObject /Subtype /Form /BBox [0 0 3 4] \
      /Resources << /ExtGState << /Opacity 17 0 R >> /XObject << /Unused 18 0 R >> >>"]

private def selectedInk (oneBased : Nat) : ByteArray :=
  (match oneBased with
  | 1 => firstInk ++ "\n"
  | 2 => middleInkA ++ "\n" ++ middleInkB ++ "\n"
  | _ => lastInk ++ "\n").toUTF8

private def selectedBox (cropped : Bool) (oneBased : Nat) : Array Sp :=
  let coords : Array Int := if cropped then
    match oneBased with
    | 1 => #[5, 7, 105, 67]
    | 2 => #[15, 10, 95, 65]
    | _ => #[20, 30, 180, 90]
  else
    match oneBased with
    | 1 => #[0, 0, 120, 80]
    | 2 => #[0, 0, 400, 300]
    | _ => #[10, 20, 210, 120]
  coords.map Dim.pt

private def selectedGeometry (f : PdfRead.Form) (cropped : Bool) (n : Nat) : Bool :=
  #[f.x0, f.y0, f.x1, f.y1] == selectedBox cropped n &&
    f.w == (selectedBox cropped n)[2]! - (selectedBox cropped n)[0]! &&
    f.h == (selectedBox cropped n)[3]! - (selectedBox cropped n)[1]!

private def selectedResources (f : PdfRead.Form) (n : Nat) : Bool :=
  f.wf && f.objects.size == (if n == 1 then 2 else if n == 2 then 0 else 3) &&
    (f.objects.filterMap (·.stream)) == (if n == 3 then #[tileInk.toUTF8] else #[])

/-- The writer retains face zero even on an image-only page. Supply a
parsed bundled face so its resource map and embedded program are valid. -/
private def selectedWrapper (font : Font.Font) (f : { f : PdfRead.Form // f.wf }) :
    ByteArray :=
  let plan : Image.Plan := { pxW := 0, pxH := 0, form := some f }
  let imgs : Image.Store := { entries := #[{ src := "poster.pdf", info := some plan }] }
  let line : Layout.LineOut :=
    { x := Dim.pt 10, y := Dim.pt 100, size := Dim.pt 12, setWidth := f.val.w,
      segs := #[.image (some 0) f.val.w f.val.h] }
  Pdf.write {} { fonts := #[font] } #[{ lines := #[line] }] (imgs := imgs)

private def selectionResolve (es : Array PdfRead.Entry) (obj : PdfRead.Obj) :
    Option PdfRead.Obj :=
  match obj with
  | .ref n _ => (es.find? (·.num == n)).map (·.val)
  | other => some other

/-- Inspect the actual form's resource references in the emitted file,
including its transitive, self-referencing resource form. -/
private def wrapperResources (es : Array PdfRead.Entry) (obj : PdfRead.Obj)
    (n : Nat) : Option Bool := do
  let res ← selectionResolve es (← obj.get? "Resources")
  if n == 2 then return res == .dict #[]
  let state ← if n == 1 then
      pure res
    else do
      let xobjs ← res.get? "XObject"
      let .ref tile _ ← xobjs.get? "Tile" | none
      let entry ← es.find? (·.num == tile)
      if entry.decoded.toOption != some (some tileInk.toUTF8) then none
      let tileRes ← entry.val.get? "Resources"
      let unused ← (← tileRes.get? "XObject").get? "Unused"
      if unused != .ref tile 0 then none
      pure tileRes
  let opacity ← selectionResolve es (← (← state.get? "ExtGState").get? "Opacity")
  return opacity.get? "CA" == some (.real "0.75")

private def wrapperMatches (font : Font.Font) (f : { f : PdfRead.Form // f.wf })
    (cropped : Bool) (n : Nat) : Bool :=
  let bytes := selectedWrapper font f
  match PdfRead.objects bytes with
  | .error _ => false
  | .ok entries =>
    let forms := entries.val.filter fun entry =>
      entry.val.get? "Subtype" == some (.name "Form") &&
      entry.decoded.toOption == some (some (selectedInk n))
    forms.size == 1 && forms.all (fun entry =>
      (match entry.val.get? "BBox" with
      | some (.arr coords) => coords.map (·.sp?) == (selectedBox cropped n).map some
      | _ => false) && (wrapperResources entries.val entry.val n).getD false) &&
      (PdfRead.readForm bytes).isOk

private def malformedSelectionPdf (kids : String) (nested : String := "[]") : ByteArray :=
  selectionPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    s!"<< /Type /Pages /Kids {kids} /Count 1 /MediaBox [0 0 10 20] >>",
    "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>",
    selectionStream "0 0 5 10 re f",
    s!"<< /Type /Pages /Parent 2 0 R /Kids {nested} /Count 1 >>"]

/-- The middle page has two ancestors; its siblings only inherit the root.
Keeping content and geometry fixed makes zero overrides comparable over
the emitted wrapper bytes. -/
private def rotationSelectionPdf (root branch leaf : Option Int)
    (indirect : Bool × Bool × Bool := (false, false, false)) : ByteArray :=
  let (rootRef, branchRef, leafRef) := indirect
  let rotate (angle : Option Int) (num : Nat) (asRef : Bool) : String :=
    match angle with
    | none => ""
    | some n => if asRef then s!" /Rotate {num} 0 R" else s!" /Rotate {n}"
  selectionPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    s!"<< /Type /Pages /Kids [3 0 R 4 0 R 7 0 R] /Count 3 \
      /MediaBox [0 0 120 80] /Resources << >>{rotate root 8 rootRef} >>",
    "<< /Type /Page /Parent 2 0 R /Contents 6 0 R >>",
    s!"<< /Type /Pages /Parent 2 0 R /Kids [5 0 R] /Count 1{rotate branch 9 branchRef} >>",
    s!"<< /Type /Page /Parent 4 0 R /Contents 6 0 R{rotate leaf 10 leafRef} >>",
    selectionStream "0 0 20 30 re f",
    "<< /Type /Page /Parent 2 0 R /Contents 6 0 R >>",
    toString (root.getD 0), toString (branch.getD 0), toString (leaf.getD 0)]

private def selectionErrorHas {α : Type} (result : Except String α)
    (words : List String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => words.all fun word => (message.splitOn word).length > 1

/-- Native PDF poster page selection: invented nested trees, inherited
geometry and resources, emitted form read-back, and named refusals.
The wrapper uses a bundled font; the source PDFs carry drawings only. -/
def pdfPageSelectionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (s!"PDF page selection: {name}" :: ·)
  let .ok font := Font.parse
      (← IO.FS.readBinFile "testdata/corpus/fonts/SourceSerifPro-Regular.otf") |
    t "bundled wrapper font parses" false
    return
  let cases : Array (String × PdfRead.PageSelection × Nat) := #[
    ("first", .first, 1), ("number 1", .number 1, 1),
    ("number 2", .number 2, 2), ("number 3", .number 3, 3), ("last", .last, 3)]
  let pdf := nestedSelectionPdf true
  t "default readForm remains first"
    (match PdfRead.readForm pdf with
    | .ok f => f.val.content == selectedInk 1 && selectedGeometry f.val true 1
    | .error _ => false)
  t "default pageNumber resolves to 1" ((PdfRead.pageNumber pdf).toOption == some 1)
  let refusesRotation (bytes : ByteArray) (selection : PdfRead.PageSelection)
      (angle : Int) : Bool :=
    match PdfRead.readForm bytes selection with
    | .error message =>
      message == s!"PDF page /Rotate {angle} is not supported; re-export unrotated"
    | .ok _ => false
  for angle in [90, 180, 270, -90] do
    for (name, bytes) in [
        ("root", rotationSelectionPdf (some angle) none none),
        ("branch", rotationSelectionPdf none (some angle) none),
        ("leaf", rotationSelectionPdf none none (some angle)),
        ("indirect root", rotationSelectionPdf (some angle) none none (true, false, false)),
        ("indirect branch", rotationSelectionPdf none (some angle) none (false, true, false)),
        ("indirect leaf", rotationSelectionPdf none none (some angle) (false, false, true))] do
      t s!"rotation {angle} at {name}: selected page refuses identically"
        (refusesRotation bytes (.number 2) angle)
      t s!"rotation {angle} at {name}: ordinal remains available"
        ((PdfRead.pageNumber bytes (.number 2)).toOption == some 2)
    for (name, selection, _) in cases do
      t s!"rotation {angle} at root: {name} inherits refusal"
        (refusesRotation (rotationSelectionPdf (some angle) none none) selection angle)
      t s!"rotation {angle} at indirect root: {name} inherits refusal"
        (refusesRotation
          (rotationSelectionPdf (some angle) none none (true, false, false)) selection angle)
  for (name, branch, leaf, angle) in [
      ("branch overrides root", some 180, none, 180),
      ("leaf overrides branch", some 180, some 270, 270),
      ("leaf overrides zero branch", some 0, some 270, 270)] do
    t s!"rotation: {name}"
      (refusesRotation (rotationSelectionPdf (some 90) branch leaf) (.number 2) angle)
  for (name, branch, leaf, indirect, angle) in [
      ("indirect branch overrides indirect root", some 180, none, (true, true, false), 180),
      ("direct leaf overrides indirect ancestors", some 180, some 270, (true, true, false), 270),
      ("indirect leaf overrides direct ancestors", some 180, some 270, (false, false, true), 270),
      ("indirect leaf overrides indirect zero branch", some 0, some 270, (true, true, true), 270)] do
    t s!"rotation: {name}"
      (refusesRotation (rotationSelectionPdf (some 90) branch leaf indirect) (.number 2) angle)
  let unrotated := rotationSelectionPdf none none none
  for (name, branch, leaf) in [
      ("zero branch overrides root", some 0, none),
      ("zero leaf overrides ancestors", some 180, some 0)] do
    let bytes := rotationSelectionPdf (some 90) branch leaf
    t s!"rotation: {name} preserves emitted wrapper"
      (match PdfRead.readForm bytes (.number 2), PdfRead.readForm unrotated (.number 2) with
      | .ok f, .ok baseline => selectedWrapper font f == selectedWrapper font baseline
      | _, _ => false)
    t s!"rotation: {name} preserves sibling inheritance"
      (refusesRotation bytes .last 90)
  for (name, branch, leaf, indirect) in [
      ("direct zero branch overrides indirect root", some 0, none, (true, false, false)),
      ("indirect zero branch overrides direct root", some 0, none, (false, true, false)),
      ("indirect zero branch overrides indirect root", some 0, none, (true, true, false)),
      ("direct zero leaf overrides indirect ancestors", some 180, some 0, (true, true, false)),
      ("indirect zero leaf overrides direct ancestors", some 180, some 0, (false, false, true)),
      ("indirect zero leaf overrides indirect ancestors", some 180, some 0, (true, true, true))] do
    let bytes := rotationSelectionPdf (some 90) branch leaf indirect
    t s!"rotation: {name} preserves emitted wrapper"
      (match PdfRead.readForm bytes (.number 2), PdfRead.readForm unrotated (.number 2) with
      | .ok f, .ok baseline => selectedWrapper font f == selectedWrapper font baseline
      | _, _ => false)
    t s!"rotation: {name} preserves sibling inheritance"
      (refusesRotation bytes .last 90)
  for selection in [PdfRead.PageSelection.first, .number 1, .number 3, .last] do
    t s!"rotation: branch does not affect sibling {repr selection}"
      (match PdfRead.readForm (rotationSelectionPdf none (some 90) none) selection,
          PdfRead.readForm unrotated selection with
      | .ok f, .ok baseline => selectedWrapper font f == selectedWrapper font baseline
      | _, _ => false)
  for cropped in [true, false] do
    let bytes := nestedSelectionPdf cropped
    t s!"animated last poster retains first-page canvas, cropped={cropped}"
      (match Image.decodeRequest .default bytes
          { src := "sequence.pdf", page := .last, animated := true } with
      | .ok (plan, canvasSize) =>
        canvasSize == some (if cropped then (Dim.pt 100, Dim.pt 60)
          else (Dim.pt 120, Dim.pt 80)) &&
        (match plan.form with
        | some f => selectedGeometry f.val cropped 3 &&
          f.val.content == selectedInk 3 && selectedResources f.val 3
        | none => false)
      | .error _ => false)
    for (name, selection, n) in cases do
      let label := s!"{name}, cropped={cropped}"
      t s!"{label}: physical ordinal" ((PdfRead.pageNumber bytes selection).toOption == some n)
      match PdfRead.readForm bytes selection with
      | .error message => t s!"{label}: unexpected refusal: {message}" false
      | .ok f =>
        t s!"{label}: selected content" (f.val.content == selectedInk n)
        t s!"{label}: inherited geometry" (selectedGeometry f.val cropped n)
        t s!"{label}: selected resources close" (selectedResources f.val n)
        t s!"{label}: emitted wrapper" (wrapperMatches font f cropped n)
  for count in [0, 3, 1000000] do
    let bytes := nestedSelectionPdf true count
    t s!"last ignores /Count {count}" ((PdfRead.pageNumber bytes .last).toOption == some 3)
    t s!"last content ignores /Count {count}"
      (match PdfRead.readForm bytes .last with
      | .ok f => f.val.content == selectedInk 3
      | .error _ => false)
  for n in [0, 4, 1000000] do
    let words := if n == 0 then ["page", "0", "1"]
      else ["page", toString n, "out of range", "3"]
    t s!"readForm refuses index {n} by name"
      (selectionErrorHas (PdfRead.readForm pdf (.number n)) words)
    t s!"pageNumber refuses index {n} by name"
      (selectionErrorHas (PdfRead.pageNumber pdf (.number n)) words)
  for (label, bytes) in [
      ("self cycle", malformedSelectionPdf "[2 0 R]"),
      ("two-node cycle", malformedSelectionPdf "[5 0 R]" "[2 0 R]")] do
    for (_, selection, _) in cases do
      t s!"readForm refuses {label}, {repr selection}"
        (selectionErrorHas (PdfRead.readForm bytes selection) ["page tree", "cycle"])
      t s!"pageNumber refuses {label}, {repr selection}"
        (selectionErrorHas (PdfRead.pageNumber bytes selection) ["page tree", "cycle"])
  let afterLeaf := malformedSelectionPdf "[3 0 R 5 0 R]" "[5 0 R]"
  for selection in [PdfRead.PageSelection.last, .number 2] do
    t s!"readForm cannot mistake a cycle after a leaf for completion, {repr selection}"
      (selectionErrorHas (PdfRead.readForm afterLeaf selection) ["page tree", "cycle"])
    t s!"pageNumber cannot mistake a cycle after a leaf for completion, {repr selection}"
      (selectionErrorHas (PdfRead.pageNumber afterLeaf selection) ["page tree", "cycle"])
  let repeated := malformedSelectionPdf "[3 0 R 3 0 R]"
  t "repeated page is not counted twice"
    (selectionErrorHas (PdfRead.pageNumber repeated .last) ["page tree", "repeated"])
  t "repeated page is not returned as the last form"
    (selectionErrorHas (PdfRead.readForm repeated .last) ["page tree", "repeated"])
  for (label, bytes, words) in [
      ("empty tree", malformedSelectionPdf "[]", ["no page"]),
      ("missing node", malformedSelectionPdf "[9999 0 R]", ["page tree"])] do
    for selection in [PdfRead.PageSelection.first, .last] do
      t s!"readForm refuses {label}, {repr selection}"
        (selectionErrorHas (PdfRead.readForm bytes selection) words)
      t s!"pageNumber refuses {label}, {repr selection}"
        (selectionErrorHas (PdfRead.pageNumber bytes selection) words)
  let empty := malformedSelectionPdf "[]"
  t "number 1 is out of range on an empty tree"
    (selectionErrorHas (PdfRead.readForm empty (.number 1)) ["page", "1", "out of range", "0"] &&
     selectionErrorHas (PdfRead.pageNumber empty (.number 1)) ["page", "1", "out of range", "0"])
  -- Retain the reader's finite visit bound even for malformed inline
  -- children. Exhausting it after a leaf must not certify that leaf as last.
  let inlineBranches := String.intercalate " " (List.replicate 12 "<< /Kids [] >>")
  let oversized := malformedSelectionPdf s!"[3 0 R {inlineBranches} 3 0 R]"
  t "last refuses an unfinished traversal"
    (selectionErrorHas (PdfRead.readForm oversized .last) ["page tree"] &&
     selectionErrorHas (PdfRead.pageNumber oversized .last) ["page tree"])
  for (_, selection, _) in cases do
    for end_ in [0, 4, pdf.size / 2, pdf.size * 3 / 4] do
      let truncated := pdf.extract 0 end_
      t s!"readForm refuses truncation {end_}, {repr selection}"
        (!(PdfRead.readForm truncated selection).isOk)
      t s!"pageNumber refuses truncation {end_}, {repr selection}"
        (!(PdfRead.pageNumber truncated selection).isOk)
