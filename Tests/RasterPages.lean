import LeanTex.Core.Pdf

open LeanTex.Core
open LeanTex.Core.Dim

/-! Raster readers discard page selection, including zero and ordinals
beyond the image. `luatex.def`'s `Gread@png` clears `Gin@page`, and
`Gread@jpg` aliases it. A synthetic LuaLaTeX probe holds both dimensions
and rendered pixels fixed across numeric page keys; injecting the other
values at the driver entry also leaves the image unchanged. `graphicx`
parses its surface key as a TeX integer before reaching that reader.

The native guard uses invented 3×2 RGB/RGBA PNGs and a JPEG of the RGB
grid. It checks decoded samples, the emitted PDF's image and soft mask,
and byte-identical output under every selection constructor. PDFs retain
physical selection and named refusals. No TeX or external image tool is
needed to run the guard. -/

private def rasterRgb : ByteArray := ⟨#[
  255, 0, 0, 0, 255, 0, 0, 0, 255,
  255, 255, 0, 0, 255, 255, 255, 0, 255]⟩

private def rasterAlpha : ByteArray := ⟨#[255, 128, 0, 64, 192, 255]⟩

-- Filter-zero rows, valid PNG CRCs, and zlib stored blocks.
private def rasterPng : ByteArray := ⟨#[
  137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 3,
  0, 0, 0, 2, 8, 2, 0, 0, 0, 18, 22, 241, 77, 0, 0, 0, 31, 73, 68, 65,
  84, 120, 1, 1, 20, 0, 235, 255, 0, 255, 0, 0, 0, 255, 0, 0, 0, 255, 0, 255,
  255, 0, 0, 255, 255, 255, 0, 255, 74, 201, 8, 248, 136, 24, 233, 212, 0, 0, 0, 0,
  73, 69, 78, 68, 174, 66, 96, 130]⟩

private def rasterRgba : ByteArray := ⟨#[
  137, 80, 78, 71, 13, 10, 26, 10, 0, 0, 0, 13, 73, 72, 68, 82, 0, 0, 0, 3,
  0, 0, 0, 2, 8, 6, 0, 0, 0, 157, 116, 102, 26, 0, 0, 0, 37, 73, 68, 65,
  84, 120, 1, 1, 26, 0, 229, 255, 0, 255, 0, 0, 255, 0, 255, 0, 128, 0, 0, 255,
  0, 0, 255, 255, 0, 64, 0, 255, 255, 192, 255, 0, 255, 255, 139, 157, 12, 118, 106, 14,
  95, 41, 0, 0, 0, 0, 73, 69, 78, 68, 174, 66, 96, 130]⟩

-- Encoded from rasterRgb: ImageMagick, 1×1 sampling, quality 100,
-- stripped metadata, density 72. The JPEG bytes must survive unchanged.
private def rasterJpeg : ByteArray := ⟨#[
  255, 216, 255, 224, 0, 16, 74, 70, 73, 70, 0, 1, 1, 0, 0, 72, 0, 72, 0, 0,
  255, 219, 0, 67, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 255, 219, 0, 67, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 255, 192,
  0, 17, 8, 0, 2, 0, 3, 3, 1, 17, 0, 2, 17, 1, 3, 17, 1, 255, 196, 0,
  20, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 255,
  196, 0, 26, 16, 0, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  3, 4, 5, 2, 6, 7, 8, 255, 196, 0, 20, 1, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 9, 255, 196, 0, 28, 17, 0, 2, 2, 3, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 3, 6, 2, 7, 8, 9, 1, 255,
  218, 0, 12, 3, 1, 0, 2, 17, 3, 17, 0, 63, 0, 59, 247, 207, 17, 226, 235, 250,
  247, 183, 38, 191, 34, 230, 0, 78, 118, 193, 34, 84, 245, 3, 160, 234, 130, 89, 9, 114,
  181, 61, 126, 108, 185, 169, 3, 9, 56, 137, 84, 38, 206, 85, 100, 16, 76, 24, 13, 116,
  210, 92, 10, 174, 49, 128, 35, 30, 45, 247, 146, 246, 107, 26, 111, 51, 248, 118, 21, 22,
  7, 106, 161, 99, 205, 218, 206, 202, 194, 21, 173, 79, 6, 35, 172, 118, 244, 3, 218, 237,
  143, 204, 140, 82, 34, 192, 167, 118, 139, 67, 151, 22, 75, 19, 89, 254, 102, 115, 167, 237,
  89, 56, 101, 57, 44, 78, 40, 153, 92, 127, 44, 180, 134, 150, 218, 252, 129, 6, 195, 218,
  90, 135, 87, 236, 171, 253, 167, 168, 59, 252, 251, 53, 230, 255, 0, 64, 170, 92, 110, 22,
  35, 163, 239, 206, 155, 14, 51, 94, 217, 172, 74, 88, 186, 110, 94, 2, 12, 48, 184, 16,
  192, 210, 38, 196, 97, 224, 131, 28, 254, 69, 20, 120, 227, 255, 217]⟩

private def rasterSelections : Array (String × PdfRead.PageSelection) := #[
  ("first", .first), ("last", .last), ("zero", .number 0),
  ("one", .number 1), ("two", .number 2), ("far", .number 1000000),
  ("max TeX integer", .number 2147483647),
  ("beyond machine integers", .number 184467440737095516160000000000000000000000)]

private def rasterPlan (b : ByteArray) (page : PdfRead.PageSelection)
    (params : Image.PlanParams := {}) : Except String Image.Plan := do
  Image.plan params (← Image.probePage b page)

private def rasterSamples (b : ByteArray) (components : Nat) : Except String ByteArray := do
  let rows ← Flate.inflate b 1024
  Flate.pngUnfilter rows 2 (3 * components) components

private def rasterGeometry (p : Image.Plan) : Bool :=
  p.pxW == 3 && p.pxH == 2 && p.width == pt 3 && p.height == pt 2 &&
    p.dpiX == 72 && p.dpiY == 72 && p.bitDepth == 8 && p.color == .rgb &&
    p.form.isNone && p.losses.isEmpty && p.orientation == 1

private def rasterWrapper (fs : Font.FontSet) (p : Image.Plan) : ByteArray :=
  let imgs : Image.Store := { entries := #[{ src := "invented-raster", info := some p }] }
  let line : Layout.LineOut := {
    x := pt 10, y := pt 20, size := pt 12, setWidth := p.width,
    segs := #[.image (some 0) p.width p.height] }
  Pdf.write { pageW := pt 100, pageH := pt 100 } fs #[{ lines := #[line] }] (imgs := imgs)

private def rasterImageDict (e : PdfRead.Entry) (color : String) : Bool :=
  e.val.get? "Subtype" == some (.name "Image") &&
    e.val.get? "Width" == some (.int 3) && e.val.get? "Height" == some (.int 2) &&
    e.val.get? "BitsPerComponent" == some (.int 8) &&
    e.val.get? "ColorSpace" == some (.name color)

/-- Read the emitted samples through the file's own predictor declaration;
the alpha is reached through the image's actual `/SMask` reference. -/
private def rasterArtifact (b : ByteArray) (jpeg alpha : Bool) : Bool := Id.run do
  let .ok entries := PdfRead.objects b | return false
  let images := entries.val.filter (·.val.get? "Subtype" == some (.name "Image"))
  if images.size != (if alpha then 2 else 1) then return false
  let some image := images.find? (rasterImageDict · "DeviceRGB") | return false
  let pixels := if jpeg then
      image.val.get? "Filter" == some (.name "DCTDecode") &&
        image.stream == some rasterJpeg
    else
      image.val.get? "Filter" == some (.name "FlateDecode") &&
        image.decoded.toOption == some (some rasterRgb)
  let opacity := if alpha then
      match image.val.get? "SMask" with
      | some (.ref n _) =>
        match images.find? (·.num == n) with
        | some mask =>
          rasterImageDict mask "DeviceGray" &&
            mask.decoded.toOption == some (some rasterAlpha)
        | none => false
      | _ => false
    else
      (image.val.get? "SMask").isNone && (image.val.get? "Mask").isNone
  let .ok form := PdfRead.readForm b | return false
  let content := String.fromUTF8! form.val.content
  return pixels && opacity && (content.splitOn "3 0 0 2 10 80 cm /Im1 Do").length == 2

private def rasterPdf (objs : Array String) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{obj}\nendobj\n"
  let start := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    let pad := String.ofList (List.replicate (10 - digits.length) '0')
    out := out ++ s!"{pad}{digits} 00000 n \n"
  return (out ++ s!"trailer\n<< /Root 1 0 R /Size {objs.size + 1} >>\n\
    startxref\n{start}\n%%EOF\n").toUTF8

private def rasterPdfStream (ink : String) : String :=
  s!"<< /Length {ink.utf8ByteSize} >>\nstream\n{ink}\nendstream"

-- Physical first page is object 5, last is object 3. Count is deliberately
-- wrong; the root's media box and resources are inherited by both leaves.
private def rasterTwoPagePdf : ByteArray := rasterPdf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [5 0 R 3 0 R] /Count 900 \
    /MediaBox [0 0 40 60] /Resources << >> >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /CropBox [5 10 35 50] >>",
  rasterPdfStream "0 0 1 rg 5 10 30 40 re f",
  "<< /Type /Page /Parent 2 0 R /Contents 6 0 R >>",
  rasterPdfStream "1 0 0 rg 0 0 40 60 re f"]

private def rasterSameError {α β : Type} (a : Except String α)
    (b : Except String β) : Bool :=
  match a, b with
  | .error x, .error y => !x.isEmpty && x == y
  | _, _ => false

/-- Raster page keys discard exactly: samples, geometry, transparency,
loss ledger, and emitted PDF bytes are unchanged. The supplied bundled
face satisfies the writer's font-slot contract; no text is painted. -/
def rasterPageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (s!"raster page selection: {name}" :: ·)
  if oneFace.fonts.isEmpty then
    t "wrapper needs its bundled font slot" false
    return
  for (name, bytes, jpeg, alpha) in #[
      ("RGB PNG", rasterPng, false, false), ("RGBA PNG", rasterRgba, false, true),
      ("JPEG", rasterJpeg, true, false)] do
    let .ok first := Image.decode bytes |
      t s!"{name}: default decode succeeds" false
      continue
    let firstPdf := rasterWrapper oneFace first
    t s!"{name}: default PDF carries known pixels and placement"
      (rasterArtifact firstPdf jpeg alpha)
    for (label, selection) in rasterSelections do
      let tag := s!"{name}, {label}"
      match rasterPlan bytes selection with
      | .error message => t s!"{tag}: unexpected refusal: {message}" false
      | .ok plan =>
        t s!"{tag}: exact intrinsic geometry and no loss" (rasterGeometry plan)
        t s!"{tag}: exact colour plane"
          (if jpeg then plan.filter == .dct && plan.data == rasterJpeg
           else plan.filter == .flatePredictor &&
             (rasterSamples plan.data 3).toOption == some rasterRgb)
        t s!"{tag}: exact alpha plane"
          (if alpha then
            match plan.alpha with
            | .soft plane 8 => (rasterSamples plane 1).toOption == some rasterAlpha
            | _ => false
           else plan.alpha == .opaque)
        let artifact := rasterWrapper oneFace plan
        t s!"{tag}: emitted PDF is byte-identical" (artifact == firstPdf)
        t s!"{tag}: emitted image, mask and placement" (rasterArtifact artifact jpeg alpha)
  -- A discarded page key must not mask a malformed raster's own error or
  -- override a planner policy. The pre-fix generic PDF-only error did both.
  let alphaDenied := (Image.probe rasterRgba).bind
    (Image.plan { softMaskPermitted := false })
  for (label, selection) in rasterSelections do
    for (name, bad) in #[
        ("truncated PNG", rasterPng.extract 0 12), ("truncated JPEG", rasterJpeg.extract 0 8),
        ("unknown signature", "invented invalid image".toUTF8)] do
      t s!"{name}, {label}: original refusal survives"
        (rasterSameError (Image.probe bad) (Image.probePage bad selection))
    t s!"RGBA PNG, {label}: soft-mask policy still refuses"
      (rasterSameError alphaDenied (rasterPlan rasterRgba selection { softMaskPermitted := false }))
  for (label, selection, last) in #[
      ("first", PdfRead.PageSelection.first, false), ("one", .number 1, false),
      ("last", .last, true), ("two", .number 2, true)] do
    t s!"PDF, {label}: physical page content and inherited geometry"
      (match rasterPlan rasterTwoPagePdf selection with
      | .ok plan =>
        match plan.form with
        | some form =>
          plan.width == pt (if last then 30 else 40) &&
            plan.height == pt (if last then 40 else 60) &&
            form.val.x0 == pt (if last then 5 else 0) &&
            form.val.y0 == pt (if last then 10 else 0) &&
            form.val.content == (if last then "0 0 1 rg 5 10 30 40 re f\n"
                                else "1 0 0 rg 0 0 40 60 re f\n").toUTF8
        | none => false
      | .error _ => false)
  for (n, expected) in #[
      (0, "PDF page number 0 is invalid; page numbers start at 1"),
      (3, "PDF page 3 is out of range (the file has 2 pages)"),
      (1000000, "PDF page 1000000 is out of range (the file has 2 pages)")] do
    t s!"PDF, number {n}: named refusal"
      (rasterSameError (rasterPlan rasterTwoPagePdf (.number n))
        (Except.error expected : Except String Unit))
