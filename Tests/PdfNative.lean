module

public import Tests.Support
public import Tests.GfxMatrix
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Cli

/-! # PDF figures drawn natively

The reading of a PDF page onto the vector model (`PdfGfx.importPage`) and
the web face the driver ships from it (`PdfFaces.face`): the content
tokenizer's round trip, the faces the route decides, the closure of a
native face, the synthetic matrix written by the engine's own PDF writer
and read back, and the committed tool-made fixtures — cairo through
rsvg-convert, lualatex in the shipped faces, the engine's writer — drawn
with nothing lost. Invented content throughout. -/

namespace Tests.PdfNative

/-- A committed fixture of the pdf-native tier. -/
def fixture (name : String) : IO ByteArray := IO.FS.readBinFile ("testdata/pdf-native/" ++ name)

/-- An import's losses, or why it refused. -/
def lossesOf (pdf : ByteArray) : Except String (Array Gfx.Loss) :=
  (PdfGfx.importPage pdf).map (·.figure.losses)

/-- Every attribute of a tree with its element. -/
def attrsAll (nodes : Array Html.Node) : Array (String × String × String) :=
  (elemAttrsList (fun _ => true) #[] nodes.toList).flatMap fun (tag, attrs) =>
    attrs.map fun (k, v) => (tag, k, v)

/-- A native face's typed tree, as `PdfFaces.svgOf` spells it. -/
def faceTree (fig : Gfx.Figure Gfx.Run) : Array Html.Node :=
  GfxSvg.spell 0 (GfxSvg.tree (fun _ (_ : Gfx.Run) => Html.text "")
    (fig.rasters.map fun r => { href := PdfFaces.rasterHref r, smooth := r.smooth })
    (GfxSvg.documentIso fig.box) fig)

/-- **A mark on the PDF writer's grid**: the values its operators spell in
the frame they stand in — coordinates, widths and dashes at the thousandth
of a point, an ellipse as its four arcs (`GfxPdf.geomOps`), a pattern's
matrix and coordinates as the file states them — what a reader of the bytes
gets back. Frames are composed by the reader from each `cm` as spelled, so
they are the figure's own exactly when its transforms are on the
nine-decimal grid, as the matrix's are. -/
def pdfGrid : Gfx.Mark → Gfx.Mark
  | .paint ctm g fl st clips alphas =>
    .paint ctm g.normal.quantize (fl.map Gfx.Fill.quantize) (st.map Gfx.Stroke.quantize)
      (gridClips clips) alphas
  | .raster ctm k clips alphas => .raster ctm k (gridClips clips) alphas
  | .shading g clips alphas => .shading g.quantize (gridClips clips) alphas
where
  gridClips (clips : Array (Gfx.Affine × Gfx.Clip)) : Array (Gfx.Affine × Gfx.Clip) :=
    clips.map fun (m, c) => (m, { c with geom := c.geom.normal.quantize })

/-- A content stream's tokens spelled back by the tokenizer's own writer,
then read: the round trip `scan_render_exact` states. -/
def roundTrips (toks : Array PdfContentLex.Tok) : Bool :=
  let again := PdfContentLex.scan (PdfContentLex.render toks)
  again.size == toks.size && (again.zip toks).all fun (a, b) => match a, b with
    | .val x, .val y => x == y
    | .op x, .op y => x == y
    | .inline d x, .inline e y => d.size == e.size && x == y
    | _, _ => false

end Tests.PdfNative

open Tests.PdfNative in
/-- **The content tokenizer** (ISO 32000-2 §7.8.2): operands read by the
object reader — numbers keeping their spelling, strings their bytes,
arrays and dictionaries whole — operators as their characters, an inline
image's dictionary and bytes, comments and stray delimiters skipped; and
what it reads spelled back reads the same. -/
def pdfContentLexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let toks := PdfContentLex.scan "q 1 0 0 1 72.5 -3 cm % a comment\n/F1 12 Tf [(a\\)b) -250 <0041>] TJ Q".toUTF8
  let ops := toks.filterMap fun t => match t with
    | .op n => some n
    | _ => none
  t "content lex: operators in order, the comment skipped" (ops == #["q", "cm", "Tf", "TJ", "Q"])
  t "content lex: a real keeps its spelling" (toks.any fun t => match t with
    | .val (.real "72.5") => true
    | _ => false)
  t "content lex: an array operand is one token" (toks.any fun t => match t with
    | .val (.arr xs) => xs.size == 3
    | _ => false)
  t "content lex: a literal string's escape resolves" ((toks.findSome? fun t => match t with
    | .val (.arr xs) => (xs[0]?).bind PdfContentLex.strBytes?
    | _ => none) == some "a)b".toUTF8)
  let img := PdfContentLex.scan "BI /W 4 /H 1 /BPC 8 /CS /G ID a EI\nEI Q".toUTF8
  t "content lex: an inline image's data is its stated length, an EI inside it kept"
    (match (img[0]? : Option PdfContentLex.Tok), (img[1]? : Option PdfContentLex.Tok) with
      | some (.inline d data), some (.op "Q") => d.size == 4 && data == "a EI".toUTF8
      | _, _ => false)
  t "content lex: a content stream holds no references, so `1 0 R` is three tokens"
    (match (PdfContentLex.scan "1 0 R".toUTF8).toList with
      | [.val (.int 1), .val (.int 0), .op "R"] => true
      | _ => false)
  t "content lex: stray delimiters are skipped, the stream still read"
    ((PdfContentLex.scan ") ] } q Q".toUTF8).size == 2)
  t "content lex: what the tokenizer reads, its writer spells back"
    (roundTrips toks && roundTrips img)
  for name in ["cairo-chart.pdf", "lualatex-text.pdf"] do
    let pdf ← fixture name
    let content := (PdfRead.Doc.ofBytes pdf >>= fun d => d.page .first >>= fun (_, p) => d.content p)
    t s!"content lex: the {name} page reads back through its own spelling"
      (match content with
        | .ok c => roundTrips (PdfContentLex.scan c)
        | .error _ => false)

open Tests.PdfNative in
/-- **A PDF figure's web face is native first** (`Boundary.route`, whose
premise this is): an exact import ships the engine's drawing and never asks
the converter; one that names a loss ships the converter's drawing with
each loss noted (N0024) when the converter draws a face the page's check
keeps, and the engine's lossy drawing with each loss named (W0609) when it
does not — no converter, a failed one, or a face the check refuses or does
not finish, whose words the line carries; a page the importer cannot read
takes the converter's answer, a refused face kept for publication to
refuse, or none. The premise is two builds apart: with the converter and
without it, a lossless figure's face is the same bytes and no converter
ran, and a lossy one names the same subjects. A face stretches onto the box
it is shown in exactly where the PDF face does. -/
def figureRouteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let keeps : ByteArray → IO PicCache.Outcome := fun _ => pure .drawn
  for (name, pdf, lossless) in [("cairo-chart.pdf", ← fixture "cairo-chart.pdf", true),
      ("lualatex-text.pdf", ← fixture "lualatex-text.pdf", true), ("lossy.pdf", type1FigurePdf, false)] do
    let runs ← IO.mkRef 0
    let present ← PdfFaces.face name pdf .first (do
      runs.modify (· + 1)
      return some (.ok (svgDocument "<path d=\"M0 0L20 20\"/>"))) keeps
    let absent ← PdfFaces.face name pdf .first (do
      runs.modify (· + 1)
      return none) keeps
    let bytesOf (f : PdfFaces.Face) : Option ByteArray := f.bytes.toOption
    let subjects (f : PdfFaces.Face) : Array (Option String) := f.diags.map (·.subject)
    if lossless then
      t s!"face route: {name} ships the same face with and without the converter, which never ran"
        (bytesOf present == bytesOf absent && (bytesOf present).isSome && (← runs.get) == 0 &&
          present.diags.isEmpty && absent.diags.isEmpty)
    else
      t s!"face route: {name} names the same loss subjects with and without the converter"
        (!(subjects present).isEmpty && subjects present == subjects absent &&
          present.route == .tool && absent.route == .nativeWithLoss)
  let asked ← IO.mkRef 0
  let converted := svgDocument "<path d=\"M0 0L20 20\"/>"
  let drawing : IO (Option (Except PicCache.Outcome ByteArray)) := do
    asked.modify (· + 1)
    return some (.ok converted)
  let failing : IO (Option (Except PicCache.Outcome ByteArray)) := do
    asked.modify (· + 1)
    return some (.error (.inconclusive "the converter was stopped"))
  let chart ← fixture "cairo-chart.pdf"
  let f ← PdfFaces.face "chart.pdf" chart .first failing keeps
  t "face route: an exact import is native, the converter never asked"
    (f.route == .native && f.native && f.bytes.isOk && f.diags.isEmpty && (← asked.get) == 0)
  let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first drawing keeps
  t "face route: a lossy import goes to the converter, each loss noted"
    (f.route == .tool && !f.native && (← asked.get) == 1 &&
      f.diags.size == 1 && f.diags.all (·.kind == .N0024) &&
      f.diags.all (·.subject == some "figure:pdf:font:type1"))
  let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first failing keeps
  t "face route: a lossy import the converter does not draw ships its lossy drawing, the loss named"
    (f.route == .nativeWithLoss && f.native && f.bytes.isOk &&
      f.diags.size == 1 && f.diags.all (·.kind == .W0609))
  -- The converter drew, and the page's own check refused its face, or
  -- could not finish checking it: the page carries the engine's drawing,
  -- never a face it would refuse or omit.
  for (said, check) in [("refuses", (fun _ => pure (.refused "an external reference") :
      ByteArray → IO PicCache.Outcome)), ("does not finish", fun _ => pure (.inconclusive "the check was killed"))] do
    let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first drawing check
    t s!"face route: a lossy import whose converted face the check {said} ships its lossy drawing, in the check's words"
      (f.route == .nativeWithLoss && f.native && f.bytes.isOk && f.bytes.toOption != some converted &&
        f.diags.size == 1 && f.diags.all fun d => d.kind == .W0609 &&
          (hasStr (diagWords d) "external reference" || hasStr (diagWords d) "killed"))
  let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first drawing keeps .declared
  t "face route: a document that refuses the converter keeps the lossy drawing, never asking it"
    (f.route == .nativeWithLoss && f.native && (← asked.get) == 4)
  -- The remedy follows the reason: installing the converter changes a page
  -- on a machine without it, and repairing it one whose run did not finish;
  -- lifting the declaration changes one the document refused it for; and
  -- nothing changes one where the converter refused the figure, or drew a
  -- face the page's check refuses.
  let helpOf (f : PdfFaces.Face) : String := String.join (f.diags.filterMap (·.help)).toList
  let noFace ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure none) keeps
  t s!"face route: with no converter on the machine, installing it is the remedy ({helpOf noFace})"
    (hasStr (helpOf noFace) "install poppler's pdftocairo" && noFace.diags.all (·.detail.isNone))
  let stopped ← PdfFaces.face "lossy.pdf" type1FigurePdf .first
    (pure (some (.error (.inconclusive "pdftocairo exited 137")))) keeps
  t s!"face route: a run that did not finish names its repair conditionally, in the run's words ({helpOf stopped})"
    (hasStr (helpOf stopped) "if the reason says it cannot start" &&
      stopped.diags.all (·.detail == some "pdftocairo exited 137"))
  let verdict ← PdfFaces.face "lossy.pdf" type1FigurePdf .first
    (pure (some (.error (.refused "pdftocairo exited 1: an invented refusal")))) keeps
  t s!"face route: a converter's own verdict offers accepting the drawing, never an install ({helpOf verdict})"
    (!verdict.diags.isEmpty && !hasStr (helpOf verdict) "install" &&
      hasStr (helpOf verdict) "\\allow{W0609}" && verdict.diags.all (·.detail == some "pdftocairo exited 1: an invented refusal"))
  let unfit ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure (some (.ok converted)))
    fun _ => pure (.refused "an external reference")
  t s!"face route: where the page's check refuses the converter's face, its line offers only accepting the drawing ({helpOf unfit})"
    (((helpOf unfit).splitOn "install").length == 1 && ((helpOf unfit).splitOn "convert = none").length == 1 &&
      ((helpOf unfit).splitOn "\\allow{W0609}").length > 1)
  let declared ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure (some (.ok converted))) keeps .declared
  t s!"face route: where the document refuses the converter, its line names the declaration to lift, or accepting ({helpOf declared})"
    (((helpOf declared).splitOn "install").length == 1 &&
      ((helpOf declared).splitOn "convert = none").length > 1 &&
      ((helpOf declared).splitOn "\\allow{W0609}").length > 1)
  let f ← PdfFaces.face "locked.pdf" encryptedCanvasPdf .first failing keeps
  t "face route: a page the importer refuses and nothing draws has no face"
    (f.route == .refused && f.bytes.isOk == false)
  let f ← PdfFaces.face "locked.pdf" encryptedCanvasPdf .first drawing keeps
  t "face route: a page the importer refuses takes the converter's drawing"
    (f.route == .tool && f.bytes.isOk)
  let f ← PdfFaces.face "locked.pdf" encryptedCanvasPdf .first drawing fun _ => pure (.refused "x")
  t "face route: a page the importer refuses keeps a refused face for publication to refuse"
    (f.route == .refused && f.bytes.toOption == some converted)
  t "face route: the route is the boundary's one decision"
    (Boundary.route .exact .notAsked .none == .native &&
      Boundary.route (.lossy #[.font "type1"]) .drew .none == .tool &&
      Boundary.route (.lossy #[.font "type1"]) (.failed "x") .none == .nativeWithLoss &&
      Boundary.route (.refused "x") (.failed "x") .none == .refused)
  let losses := (lossesOf type1FigurePdf).toOption.getD #[]
  t "face route: every loss is named once, under its feature"
    (losses.size == 1 && (FigureLoss.diags (FigureLoss.pdfLostDiag "x.pdf" .refused) losses).all
      (·.subject == some "figure:pdf:font:type1"))
  -- The stretch rule: a sequence's poster page differs in shape from its
  -- first frame, whose canvas the PDF form stretches it onto.
  let root (f : PdfFaces.Face) : String := match f.bytes.toOption.bind (String.fromUTF8? ·) with
    | some svg => ((svg.splitOn "<svg").getD 1 "").takeWhile (· != '>') |>.toString
    | none => ""
  let poster ← PdfFaces.face "sequence.pdf" svgCanvasPdf .last failing keeps (stretch := true)
  let plain ← PdfFaces.face "sequence.pdf" svgCanvasPdf .last failing keeps
  t s!"face route: a stretched face fills its box as the PDF form does ({root poster})"
    (poster.native && ((root poster).splitOn "preserveAspectRatio=\"none\"").length == 2 &&
      ((root poster).splitOn "viewBox=\"0 0 60 120\"").length == 2)
  t s!"face route: an unstretched face keeps SVG's fit ({root plain})"
    (plain.native && ((root plain).splitOn "preserveAspectRatio").length == 1)

open Tests.PdfNative in
/-- **A native face is closed by construction**, what lets publication take
it without the converter's validation (`Publication.prepareHtml`'s
premise): every reference a fixture's face spells is a fragment of its own
or a `data:` raster, every attribute has a value — an XML document, which a
bare attribute is not — and no script, style or foreign object appears. -/
def nativeFaceClosedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for name in ["cairo-chart.pdf", "lualatex-text.pdf", "lualatex-shade.pdf",
      "matplotlib-dialect.pdf", "leantex-strokes.pdf", "geometry-dialect.pdf", "text-dialect.pdf",
      "lualatex-strokedtext.pdf"] do
    match PdfGfx.importPage (← fixture name) with
    | .error e => t s!"native face: {name} imports ({e})" false
    | .ok imp =>
      let attrs := attrsAll (faceTree imp.figure)
      let refs := attrs.filter fun (_, k, _) => k == "href"
      t s!"native face: {name} references only its own fragments and data rasters"
        (refs.all fun (_, _, v) => v.startsWith "#" || v.startsWith "data:image/")
      t s!"native face: {name} spells every attribute with a value"
        (attrs.all fun (_, _, v) => !v.isEmpty)
      t s!"native face: {name} carries no script, style or foreign object"
        (attrs.all fun (tag, _, _) => tag != "script" && tag != "style" && tag != "foreignObject")
      let svg := PdfFaces.svgOf imp.figure
      t s!"native face: {name}'s bytes are the tree's spelling, an SVG document"
        ((String.fromUTF8? svg).any fun s => s.startsWith "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<svg ")

open Tests.PdfNative Tests.GfxMatrix in
/-- **The engine's PDF writer reads back** through its bytes: every case of
the synthetic matrix that paints no raster, written as a one-page document
by `Pdf.writeChecked` under the identity placement and imported, paints the
figure's marks on the grid the writer spells them to (`pdfGrid`) — its
operators, its resources and its forms read with PDF's meaning on the
other side. The cases `PdfGfx.readback_id` covers are named, and each is
held to the theorem's statement executed. -/
def pdfReadbackChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let green : Ir.Color := { r := 0, g := 160, b := 0 }
  let threeStops : Array Gfx.Stop :=
    #[{ offset := 0, color := red }, { offset := 32768, color := green }, { offset := 65536, color := blue }]
  let jump : Array Gfx.Stop :=
    #[{ offset := 0, color := red }, { offset := 16384, color := green }, { offset := 16384, color := blue },
      { offset := 65536, color := red }]
  let filled (st : Array Gfx.Stop) : Gfx.Figure Empty :=
    let g : Gfx.Gradient := .linear (0, 0) (Dim.pt 10, 0) st Gfx.Affine.unit
    let fl : Gfx.Fill := { paint := .gradient g, rule := .nonzero, alpha := Gfx.Alpha.opaque }
    figure #[.draw square (some fl) none]
  let more : Array (String × Gfx.Figure Empty) :=
    #[("a gradient of three stops", filled threeStops), ("a gradient whose colour jumps", filled jump)]
  let all := cases ++ more
  for (name, fig) in all do
    unless fig.imageFree do continue
    let ((x0, y0), (x1, y1)) := fig.box
    let geom : Layout.Geom := { pageW := x1 - x0, pageH := y1 - y0 }
    let ink : Layout.InkOut := { fig := fig.lift, place := (Pdf.pageIso geom).inv, leaf := none }
    match Pdf.writeChecked geom fs #[{ inks := #[ink] }] with
    | .error _ => t s!"readback: {name} writes" false
    | .ok pdf =>
      match PdfGfx.importPage pdf with
      | .error e => t s!"readback: {name} imports ({e})" false
      | .ok imp =>
        t s!"readback: {name} reads back with nothing lost" imp.figure.losses.isEmpty
        t s!"readback: {name} paints the figure's marks, on the writer's grid"
          (imp.figure.marks == fig.marks.map pdfGrid)
  -- `PdfGfx.readback_id`'s reach over the matrix: the cases whose nodes it
  -- covers and whose operators stand on the print grid, each held to the
  -- statement executed, the stream read with no resources at all.
  let emitted (fig : Gfx.Figure Empty) := GfxPdf.emit names PdfGfx.noLabels PdfGfx.isoId fig
  let covered := all.filter fun (_, fig) =>
    PdfGfx.nodesPlain fig.nodes.toList && (PdfGfx.opsBack (emitted fig).toList).toArray == emitted fig
  t s!"readback: the theorem covers the matrix's plain cases ({covered.map (·.1)})"
    (covered.map (·.1) == #["an even-odd path", "a turned group clipped twice", "ink-free words"])
  let bare : PdfGfx.Ctx :=
    { doc := { bytes := .empty, locs := {}, memo := {}, memo_ok := fun _ _ h => by simp at h, root := 0
               trailer := .null }
      res := .dict #[], base := Gfx.Affine.unit, off := #[], box := ((0, 0), (0, 0)) }
  for (name, fig) in covered do
    let imp := PdfGfx.readStream bare (Pdf.render (emitted fig)).toUTF8
    t s!"readback: {name} reads back as the theorem states"
      (imp.losses.isEmpty && imp.marks.map PdfGfx.markScreen == fig.marks.map PdfGfx.markScreen)

open Tests.PdfNative in
/-- **The committed fixtures draw with nothing lost**: cairo's chart
(TrueType text, an opacity soft mask, gradients, a transparency group),
lualatex's pictures in the shipped faces (CID-keyed CFF text, a pgf axial
shading, text stroked by FakeBold and in outline mode), the engine's own
writer (OpenType CFF text), the matplotlib-dialect file (Type 3 glyphs,
marker forms, an alpha state, a clip, a soft-masked image) and the
geometry and text dialects (degenerate shapes under each cap, inline
images, the text state's positioning) — each glyph a stamp of its outline
and its recovered text the figure's words. -/
def pdfFixtureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, words) in [("cairo-chart.pdf", "invented chart"), ("lualatex-text.pdf", "Alpha node"),
      ("lualatex-shade.pdf", ""), ("leantex-strokes.pdf", ""), ("matplotlib-dialect.pdf", "ab"),
      ("geometry-dialect.pdf", ""), ("text-dialect.pdf", "abba"), ("lualatex-strokedtext.pdf", "fake bold")] do
    match PdfGfx.importPage (← fixture name) with
    | .error e => t s!"fixture: {name} imports ({e})" false
    | .ok imp =>
      t s!"fixture: {name} draws with nothing lost ({reprStr imp.figure.losses})"
        imp.figure.losses.isEmpty
      t s!"fixture: {name} is a well-formed figure" imp.figure.wf
      unless words.isEmpty do
        t s!"fixture: {name} says '{words}'" ((imp.figure.said (fun _ => "")).contains words)
  match PdfGfx.importPage (← fixture "lualatex-text.pdf") with
  | .ok imp =>
    t "fixture: lualatex's glyphs are stamps of their outlines"
      (!imp.figure.outlines.isEmpty && imp.figure.outlines.all (!·.isEmpty))
  | .error _ => t "fixture: lualatex-text imports" false
  match PdfGfx.importPage (← fixture "geometry-dialect.pdf") with
  | .ok imp =>
    -- SVG draws, and clips to, no rect of zero or negative size, and
    -- paints a square where a square cap meets a dot PDF leaves unpainted.
    let rects := (attrsAll (faceTree imp.figure)).filter fun (tag, k, v) =>
      tag == "rect" && (k == "width" || k == "height") && (v == "0" || v.startsWith "-")
    t s!"fixture: the geometry dialect's face spells no rect SVG draws nothing for ({rects})" rects.isEmpty
    let svg := (String.fromUTF8? (PdfFaces.svgOf imp.figure)).getD ""
    t "fixture: the geometry dialect's square-capped dot is left out, its round one kept"
      (!hasStr svg "M 140 100 L 140 100" && hasStr svg "M 160 100 Z")
  | .error _ => t "fixture: geometry-dialect imports" false
  match PdfGfx.importPage (← fixture "matplotlib-dialect.pdf") with
  | .ok imp =>
    t "fixture: the marker form paints as one symbol, used at every placement"
      (imp.figure.symbols.size ≥ 1)
    t "fixture: the soft-masked image is a raster with alpha"
      (imp.figure.rasters.any fun r => !r.jpeg && r.pxW == 4 && r.pxH == 4)
  | .error _ => t "fixture: matplotlib-dialect imports" false
  t "fixture: a Type 1 program is named, the rest drawn"
    (lossesOf type1FigurePdf == .ok #[.font "type1"])
  t "fixture: an encrypted file is refused, not read as noise"
    ((lossesOf encryptedCanvasPdf).isOk == false)

/-- **A PNG the engine writes reads back**, through the deflating encoder
`PngEncode.probe_encode_exact` reaches only by its stream's size: the probe
sees its size, its colour type and its depth; and the CRC, which the
theorem does not read, is PNG's. -/
def pngEncodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let h : PngEncode.Header := { width := 3, height := 2, bitDepth := 8, colorType := 6 }
  let png := PngEncode.encode h (ByteArray.mk (Array.replicate 24 128))
  match Image.probe png with
  | .ok src =>
    t "png: the probe reads the written size" (src.pxW == 3 && src.pxH == 2)
    t "png: the probe reads the colour type and depth" (src.colorType == 6 && src.bitDepth == 8)
  | .error e => t s!"png: the probe reads the written file ({e})" false
  t "png: CRC-32 of IEND is PNG's" (PngEncode.crc32 "IEND".toUTF8 == 0xAE426082)

open Tests.PdfNative in
/-- **The glyph tables' contract** (`GlyphList` over `GlyphListData`): the
glyph list's names read to their scalars by its naming rules; the three
base encodings' names read through the glyph list to the scalars Unicode's
mapping files give their codes, the one declared divergence aside; the CFF
standard strings hold StandardEncoding's names in code order from 1, which
is what `standardSid` counts; the Expert encoding names standard strings
only. -/
def glyphListChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "glyph list: names read by the list and its conventions"
    (GlyphList.nameText "A" == some "A" && GlyphList.nameText "eacute" == some "é" &&
      GlyphList.nameText "uni00410042" == some "AB" && GlyphList.nameText "u1F600" == some "😀" &&
      GlyphList.nameText "f_f_i" == some "ffi" && GlyphList.nameText "a.sc" == some "a" &&
      GlyphList.nameText "uniD800" == none && GlyphList.nameText "notaglyphname" == none)
  -- The glyph list reads Mac OS Roman's 0xBD name, Omega, as the ohm sign;
  -- Unicode's Mac OS Roman table, as Greek capital omega. Same glyph; the
  -- text follows the encoding's table.
  let divergent : List (GlyphList.Base × Nat) := [(.macRoman, 0xBD)]
  for e in [GlyphList.Base.standard, .winAnsi, .macRoman] do
    let bad := (List.range 256).filter fun c =>
      let n := e.name c
      !divergent.contains (e, c) &&
        (if n.isEmpty then (e.scalar? c).isSome else GlyphList.nameScalar n != e.scalar? c)
    t s!"glyph list: {reprStr e}'s names read to its scalars ({bad.take 5})" bad.isEmpty
  t "glyph list: the one divergence is the one declared"
    (GlyphList.nameScalar (GlyphList.Base.macRoman.name 0xBD) == some (Char.ofNat 0x2126) &&
      GlyphList.Base.macRoman.scalar? 0xBD == some (Char.ofNat 0x03A9))
  t "glyph list: 391 CFF standard strings from .notdef"
    (GlyphListData.cffStandardStrings.size == 391 && GlyphList.cffString? 0 == some ".notdef" &&
      GlyphList.cffString? 390 == some "Semibold")
  t "glyph list: StandardEncoding's names are the standard strings 1–149, in code order"
    ((List.range 256).all fun c =>
      let n := GlyphList.standardName c
      n.isEmpty || (GlyphList.cffSid? n == GlyphList.standardSid c && (GlyphList.standardSid c).all (· ≤ 149)))
  t "glyph list: the Expert encoding names standard strings only"
    ((List.range 256).all fun c =>
      let n := GlyphList.expertName c
      n.isEmpty || (GlyphList.cffSid? n).isSome)

open Tests.PdfNative in
/-- **A PDF's simple and composite fonts select the glyphs they name**
(§9.6.5, §9.7): the shipped Fira Sans's CFF table embedded bare
(`FontFile3` `Type1C`) selects under WinAnsiEncoding, for every code the
encoding names, the glyph the OpenType font's own cmap gives the code's
scalar — through the CFF standard strings and the font's custom ones —
and with no encoding the font's own; its text is the code's scalar.
Vertical writing is named, not set sideways. -/
def pdfFontChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let otf ← IO.FS.readBinFile "testdata/corpus/fonts/FiraSans-Regular.otf"
  let .ok font := Font.parse otf | t "pdf font: the shipped face parses" false
  let some cff := Ink.cffTable otf | t "pdf font: the shipped face carries a CFF table" false
  let docWith (encoding : String) : Except String PdfRead.Doc := PdfRead.Doc.ofBytes (syntheticPdfBin #[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Font << /F1 5 0 R >> >> >>".toUTF8,
    streamObjBin "BT /F1 12 Tf 10 10 Td (Ab) Tj ET".toUTF8,
    s!"<< /Type /Font /Subtype /Type1 /BaseFont /Placeholder {encoding} /FontDescriptor 6 0 R >>".toUTF8,
    "<< /Type /FontDescriptor /FontName /Placeholder /Flags 32 /FontFile3 7 0 R >>".toUTF8,
    streamObjBin cff "/Subtype /Type1C "])
  let loaded (encoding : String) : Option PdfFont.Loaded := do
    let d ← (docWith encoding).toOption
    let (fo, _) ← (d.get 5).toOption
    return PdfFont.load d fo
  let simple (l : PdfFont.Loaded) : Array (Option PdfFont.GlyphRef) × Array String :=
    match l.codes with
    | .simple gs _ text => (gs, text)
    | _ => (#[], #[])
  match loaded "/Encoding /WinAnsiEncoding" with
  | none => t "pdf font: the bare CFF font reads" false
  | some l =>
    let (gs, text) := simple l
    let src := Ink.Src.ofCff cff
    -- A name selects the glyph of that name, which may be another glyph
    -- for the same character than the one the font's cmap picks (`mu` for
    -- the micro sign): the selection holds when it reads to the code's
    -- character.
    let wrong := (List.range 256).filter fun c =>
      match GlyphList.Base.winAnsi.scalar? c with
      | some ch =>
        let byCmap := font.gid ch
        let chosen := gs[c]?.getD none
        let reads := match chosen with
          | some (.gid g) => (src.glyphName g).bind GlyphList.nameScalar == some ch
          | _ => false
        byCmap.isSome && byCmap != some 0 && !(chosen == byCmap.map PdfFont.GlyphRef.gid || reads)
      | none => false
    t s!"pdf font: a bare CFF under WinAnsiEncoding selects a glyph of each code's character by name \
({wrong.take 6})" wrong.isEmpty
    t "pdf font: an accented code selects its glyph and says its letter"
      ((gs[0xE9]?.getD none) == (font.gid 'é').map PdfFont.GlyphRef.gid && text[0xE9]? == some "é")
  match loaded "" with
  | none => t "pdf font: the bare CFF font reads without an encoding" false
  | some l =>
    let (gs, text) := simple l
    t "pdf font: with no encoding the program's own selects the glyph"
      ((gs[0x41]?.getD none) == (font.gid 'A').map PdfFont.GlyphRef.gid &&
        (gs[0x27]?.getD none) == (font.gid '’').map PdfFont.GlyphRef.gid && text[0x41]? == some "A")
  let vertical := syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Font << /F1 5 0 R >> >> >>",
    streamObj "BT /F1 12 Tf 10 10 Td <0001> Tj ET",
    "<< /Type /Font /Subtype /Type0 /BaseFont /Placeholder /Encoding /Identity-V \
      /DescendantFonts [6 0 R] >>",
    "<< /Type /Font /Subtype /CIDFontType0 /BaseFont /Placeholder /FontDescriptor 7 0 R >>",
    "<< /Type /FontDescriptor /FontName /Placeholder /Flags 32 >>"]
  t "pdf font: vertical writing is named"
    ((lossesOf vertical).toOption.any fun ls => ls.contains (.font "vertical"))

open Tests.PdfNative in
/-- **The interpreter keeps PDF's meaning where it is subtle**: optional
content under each visibility policy and through a single group reference
(§8.11.2.2); a Type 3 glyph that sets no colour of its own painting in the
colour of the text that shows it, by `d1` and by `d0` (§9.6.4); a function
held to part of its shading's domain, a stitching held to part of it, and a
domain ending where the colour jumps, drawn with a stop where the line
bends (§7.10); and the shadings the gradient model only approaches named,
not drawn as if exact — an exponential function of another exponent, a
stitching whose bounds are out of order, a colour that leaves its space
between stops, a CMYK colour whose black and inks both change, a radial
shading whose start circle leaves its end circle, a shading pattern that
stops short. -/
def pdfInterpreterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ocDoc (props : String) : ByteArray := syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R /OCProperties << /OCGs [6 0 R 7 0 R] /D << /OFF [6 0 R] >> >> >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Properties << /MC0 5 0 R >> >> >>",
    streamObj "/OC /MC0 BDC 0 0 10 10 re f EMC",
    props,
    "<< /Type /OCG /Name (Off) >>", "<< /Type /OCG /Name (On) >>"]
  let drawn (pdf : ByteArray) : Option Nat := (PdfGfx.importPage pdf).toOption.map (·.figure.marks.size)
  for (policy, shown) in [("/AnyOn", true), ("/AllOn", false), ("/AnyOff", true), ("/AllOff", false)] do
    t s!"interpreter: optional content under {policy} is {if shown then "shown" else "hidden"}"
      (drawn (ocDoc s!"<< /Type /OCMD /OCGs [6 0 R 7 0 R] /P {policy} >>") == some (if shown then 1 else 0))
  t "interpreter: an OCMD naming one group by reference follows it"
    (drawn (ocDoc "<< /Type /OCMD /OCGs 6 0 R >>") == some 0 &&
      drawn (ocDoc "<< /Type /OCMD /OCGs 7 0 R >>") == some 1)
  let type3 (proc : String) : ByteArray := syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Font << /F1 5 0 R >> >> >>",
    streamObj "1 0 0 rg BT /F1 10 Tf 10 10 Td (a) Tj ET 0 0 1 rg BT /F1 10 Tf 40 10 Td (a) Tj ET",
    "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 1000 1000] /FontMatrix [0.001 0 0 0.001 0 0] \
      /CharProcs << /a 6 0 R >> /Encoding << /Type /Encoding /Differences [97 /a] >> \
      /FirstChar 97 /LastChar 97 /Widths [1000] >>",
    streamObj proc]
  let fills (pdf : ByteArray) : Array Ir.Color := ((PdfGfx.importPage pdf).toOption.map fun imp =>
    imp.figure.marks.filterMap fun m => match m with
      | .paint _ _ (some { paint := .solid c, .. }) _ _ _ => some c
      | _ => none).getD #[]
  let red : Ir.Color := { r := 255, g := 0, b := 0 }
  let blue : Ir.Color := { r := 0, g := 0, b := 255 }
  let same (a b : Ir.Color) : Bool := a.r == b.r && a.g == b.g && a.b == b.b
  for (kind, proc) in [("d1", "1000 0 0 0 1000 1000 d1 0 0 1000 1000 re f"),
      ("d0", "1000 0 d0 0 0 1000 1000 re f")] do
    let fs := fills (type3 proc)
    t s!"interpreter: a {kind} glyph paints in the colour of the text that shows it"
      (fs.size == 2 && (fs[0]?.any (same · red)) && (fs[1]?.any (same · blue)))
  let shading (sh : String) (paint : String) : ByteArray := syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Shading << /S0 5 0 R >> /Pattern << /P0 6 0 R >> >> >>",
    streamObj paint, sh, "<< /PatternType 2 /Shading 5 0 R >>"]
  let fn (n : String) := s!"<< /FunctionType 2 /Domain [0 1] /C0 [1 0 0] /C1 [0 0 1] /N {n} >>"
  let axial (n ext : String) :=
    s!"<< /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 100 0] /Function {fn n} /Extend {ext} >>"
  t "interpreter: a linear axial shading is drawn exactly"
    (lossesOf (shading (axial "1" "[true true]") "/S0 sh") == .ok #[])
  t "interpreter: a curved function is named, still drawn"
    (lossesOf (shading (axial "2" "[true true]") "/S0 sh") ==
      .ok #[.resource "shading-function-approximated"])
  t "interpreter: a radial cone is named"
    (lossesOf (shading s!"<< /ShadingType 3 /ColorSpace /DeviceRGB /Coords [10 10 5 60 10 20] \
      /Function {fn "1"} /Extend [true true] >>" "/S0 sh") == .ok #[.resource "shading-radial-cone"])
  t "interpreter: a shading pattern that stops short is named"
    (lossesOf (shading (axial "1" "[false false]") "/Pattern cs /P0 scn 0 0 100 50 re f") ==
      .ok #[.resource "shading-unextended"])
  let faceStops (pdf : ByteArray) : Array (String × String) := match PdfGfx.importPage pdf with
    | .ok imp => (elemAttrsList (· == "stop") #[] (faceTree imp.figure).toList).map fun (_, attrs) =>
        (((attrs.find? (·.1 == "offset")).map (·.2)).getD "",
          ((attrs.find? (·.1 == "stop-color")).map (·.2)).getD "")
    | .error _ => #[]
  let shaded (space fnDict shDom : String) :=
    s!"<< /ShadingType 2 /ColorSpace {space} /Coords [0 0 100 0] /Domain {shDom} /Function {fnDict} \
      /Extend [true true] >>"
  let seg (c0 c1 : String) (dom : String := "[0 1]") :=
    s!"<< /FunctionType 2 /Domain {dom} /C0 {c0} /C1 {c1} /N 1 >>"
  let stitching (dom bounds enc : String) (fns : List String) :=
    s!"<< /FunctionType 3 /Domain {dom} /Bounds {bounds} /Encode {enc} /Functions [{" ".intercalate fns}] >>"
  let narrow := shading (shaded "/DeviceRGB" (seg "[1 0 0]" "[0 0 1]" "[0 0.5]") "[0 1]") "/S0 sh"
  let st := faceStops narrow
  t s!"interpreter: a function held to part of its shading's domain stops where it is held ({st})"
    (lossesOf narrow == .ok #[] && st.map (·.1) == #["0", "0.5", "1"] && st[1]?.map (·.2) == st[2]?.map (·.2))
  let late := shading (shaded "/DeviceRGB" (stitching "[0.25 1]" "[0.5]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 1 0]" "[0 0 1]"]) "[0 1]") "/S0 sh"
  let st := faceStops late
  t s!"interpreter: a stitching held to part of its shading's domain stops where it is held ({st})"
    (lossesOf late == .ok #[] && st.map (·.1) == #["0", "0.25", "0.5", "1"] &&
      st[0]?.map (·.2) == st[1]?.map (·.2))
  let jump := shading (shaded "/DeviceRGB" (stitching "[0 1]" "[0.5]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 0 1]" "[0 0 1]"]) "[0 0.5]") "/S0 sh"
  let st := faceStops jump
  t s!"interpreter: a shading whose domain ends where its colour jumps ends on both colours ({st})"
    (lossesOf jump == .ok #[] && st.map (·.1) == #["0", "1", "1"] && st[1]?.map (·.2) != st[2]?.map (·.2))
  let early := shading (shaded "/DeviceRGB" (stitching "[0 0.75]" "[0.75]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 0 1]" "[0 0 1]"]) "[0 1]") "/S0 sh"
  let st := faceStops early
  t s!"interpreter: a stitching that ends before its shading holds its last colour past its end ({st})"
    (lossesOf early == .ok #[] && st.map (·.1) == #["0", "0.75", "0.75", "1"] &&
      st[2]?.map (·.2) == st[3]?.map (·.2) && st[1]?.map (·.2) != st[2]?.map (·.2))
  let held := shading (shaded "/DeviceRGB" (stitching "[0.25 1]" "[0.25]" "[0 1 0 1]"
    [seg "[0 1 0]" "[0 1 0]", seg "[1 0 0]" "[0 0 1]"]) "[0 1]") "/S0 sh"
  let st := faceStops held
  t s!"interpreter: a stitching held at its start holds the colour it starts with ({st})"
    (lossesOf held == .ok #[] && st.map (·.1) == #["0", "0.25", "1"] && st[0]?.map (·.2) == st[1]?.map (·.2))
  let unordered := shading (shaded "/DeviceRGB" (stitching "[0 1]" "[0.7 0.3]" "[0 1 0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 1 0]" "[0 0 1]", seg "[0 0 1]" "[1 0 0]"]) "[0 1]") "/S0 sh"
  t "interpreter: a stitching whose bounds are out of order is named, still drawn"
    (lossesOf unordered == .ok #[.resource "shading-function-approximated"])
  let leaves := shading (shaded "/DeviceRGB" (seg "[-1 0 0]" "[2 0 0]") "[0 1]") "/S0 sh"
  t "interpreter: a colour that leaves its space between stops is named, still drawn"
    (lossesOf leaves == .ok #[.resource "shading-function-approximated"])
  let inkAndBlack := shading (shaded "/DeviceCMYK" (seg "[1 0 0 0]" "[0 0 0 1]") "[0 1]") "/S0 sh"
  t "interpreter: a CMYK colour whose black and inks both change is named, still drawn"
    (lossesOf inkAndBlack == .ok #[.resource "shading-function-approximated"])
  let twoInks := shading (shaded "/DeviceCMYK" (seg "[1 0 0 0.5]" "[0 1 0 0.5]") "[0 1]") "/S0 sh"
  t "interpreter: a CMYK colour whose two inks change together is named, still drawn"
    (lossesOf twoInks == .ok #[.resource "shading-function-approximated"])
  let oneInk := shading (shaded "/DeviceCMYK" (seg "[1 0 0 0.5]" "[0 0 0 0.5]") "[0 1]") "/S0 sh"
  t "interpreter: a CMYK colour with one changing ink is drawn exactly"
    (lossesOf oneInk == .ok #[])

namespace Tests.PdfNative

/-- A one-page figure of `ink` under `res`, its further objects from 5. -/
def statePdf (res ink : String) (more : Array String) : ByteArray := syntheticPdf (#[
  "<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources {res} >>",
  streamObj ink] ++ more)

/-- The clip geometries a mark is painted under. -/
def clipGeoms : Gfx.Mark → Array Gfx.Geom
  | .paint _ _ _ _ clips _ => clips.map (·.2.geom)
  | .raster _ _ clips _ => clips.map (·.2.geom)
  | .shading _ clips _ => clips.map (·.2.geom)

/-- A figure's marks, none where the import refuses. -/
def marksOf (pdf : ByteArray) : Array Gfx.Mark :=
  ((PdfGfx.importPage pdf).toOption.map (·.figure.marks)).getD #[]

/-- A raster's pixels as 8-bit RGB, where its PNG holds them so: rows
behind filter byte 0, as `PngEncode.encode` writes them. -/
def rgbPixels (r : Gfx.Raster) : Option (Array (UInt8 × UInt8 × UInt8)) := do
  let plan ← (Image.decode r.bytes).toOption
  let rows ← (Flate.inflate plan.data (r.pxW * r.pxH * 4 + r.pxH)).toOption
  let stride := r.pxW * 3 + 1
  return (Array.range (r.pxW * r.pxH)).map fun i =>
    let pos := (i / r.pxW) * stride + 1 + (i % r.pxW) * 3
    (rows[pos]?.getD 0, rows[pos + 1]?.getD 0, rows[pos + 2]?.getD 0)

end Tests.PdfNative

open Tests.PdfNative in
/-- **What the graphics state carries reaches the marks it paints**: a
constant soft mask's box clips what is painted under it, and nothing after
`/SMask /None` or under a second mask, which replaces it (§11.6.5.2); a Type
3 glyph's procedure paints with the alphas and line width in force
(§9.6.4); a shading's `BBox` clips it (§8.7.4.5.1). What the model cannot
say is named: a tiling pattern that strokes a path or fills a glyph, a
stencil mask painted with a pattern, a JPEG under a `Decode` that remaps it.
A CMYK colour, painted or sampled, previews as pdftoppm shows it; a
TrueType program with no cmap shows its glyphs by their 'post' names, as
pdftoppm draws them; a glyph stroked through its frame strokes the width,
dash and phase the state set in user space (`PdfGfx.strokeIn_between`),
where it once stroked them 65,536 times as wide; an `re` of negative extent
keeps the corner order PDF traces, where it was once read as the rectangle
it covers and its dashes moved. Each case once imported with no loss named
and drew otherwise. -/
def pdfStateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let maskGroup (box : String) (ink : String) :=
    streamObj ink s!"/Type /XObject /Subtype /Form /BBox {box} /Group << /S /Transparency /CS /DeviceGray >> "
  let mask (n : Nat) := s!"<< /Type /ExtGState /SMask << /Type /Mask /S /Luminosity /G {n} 0 R >> >>"
  let box (x y w h : Int) : Gfx.Geom := .rect (Dim.pt x) (Dim.pt y) (Dim.pt w) (Dim.pt h)
  let reset := marksOf (statePdf "<< /ExtGState << /M 5 0 R /N 6 0 R >> >>"
    "1 0 0 rg /M gs 0 0 50 50 re f /N gs 0 0 1 rg 100 20 80 60 re f"
    #[mask 7, "<< /Type /ExtGState /SMask /None >>", maskGroup "[0 0 50 50]" "0.5 g 0 0 50 50 re f"])
  t s!"state: a soft mask clips what it masks, and nothing after /SMask /None ({repr (reset.map clipGeoms)})"
    (reset.map clipGeoms == #[#[box 0 0 50 50], #[]])
  let replace := marksOf (statePdf "<< /ExtGState << /M 5 0 R /M2 6 0 R >> >>"
    "1 0 0 rg /M gs 0 0 50 50 re f /M2 gs 0 0 1 rg 100 20 80 60 re f"
    #[mask 7, mask 8, maskGroup "[0 0 50 50]" "0.5 g 0 0 50 50 re f",
      maskGroup "[100 20 180 80]" "0.5 g 100 20 80 60 re f"])
  t s!"state: a second soft mask replaces the first ({repr (replace.map clipGeoms)})"
    (replace.map clipGeoms == #[#[box 0 0 50 50], #[box 100 20 80 60]])
  let restored := marksOf (statePdf "<< /ExtGState << /M 5 0 R /N 6 0 R >> >>"
    "/M gs q /N gs 0 0 10 10 re f Q 0 0 10 10 re f"
    #[mask 7, "<< /Type /ExtGState /SMask /None >>", maskGroup "[0 0 50 50]" "0.5 g 0 0 50 50 re f"])
  t s!"state: Q restores the soft mask a q saved ({repr (restored.map clipGeoms)})"
    (restored.map clipGeoms == #[#[], #[box 0 0 50 50]])
  let type3 (ink proc : String) := statePdf "<< /Font << /F1 5 0 R >> /ExtGState << /A 7 0 R >> >>" ink
    #["<< /Type /Font /Subtype /Type3 /FontBBox [0 0 1000 1000] /FontMatrix [0.001 0 0 0.001 0 0] \
        /CharProcs << /a 6 0 R >> /Encoding << /Type /Encoding /Differences [97 /a] >> \
        /FirstChar 97 /LastChar 97 /Widths [1000] >>",
      streamObj proc, "<< /Type /ExtGState /ca 0.3 /CA 0.3 >>"]
  let fillAlphas (ms : Array Gfx.Mark) : Array Nat := ms.filterMap fun m => match m with
    | .paint _ _ (some f) _ _ _ => some f.alpha.val
    | _ => none
  let glyphAlpha := marksOf (type3 "0 0 1 rg /A gs BT /F1 60 Tf 20 20 Td (a) Tj ET"
    "1000 0 d0 0 0 400 1000 re f 600 0 400 1000 re f")
  t s!"state: a Type 3 glyph paints under the alpha in force ({fillAlphas glyphAlpha})"
    (fillAlphas glyphAlpha == #[300, 300])
  let glyphWidth := marksOf (type3 "7 w BT /F1 60 Tf 20 20 Td (a) Tj ET" "1000 0 d0 0 0 m 1000 1000 l S")
  let widths := glyphWidth.filterMap fun m => match m with
    | .paint _ _ _ (some st) _ _ => some st.width
    | _ => none
  t s!"state: a Type 3 glyph strokes with the line width in force ({widths})" (widths == #[Dim.pt 7])
  let tile := streamObj "1 0 0 rg 0 0 5 5 re f"
    "/PatternType 1 /PaintType 1 /TilingType 1 /BBox [0 0 10 10] /XStep 10 /YStep 10 /Resources << >> "
  t "state: a tiling pattern that strokes is named"
    (lossesOf (statePdf "<< /Pattern << /P1 5 0 R >> >>" "/Pattern CS /P1 SCN 8 w 20 50 m 180 50 l S" #[tile])
      == .ok #[.resource "tiling-paint"])
  t "state: a tiling pattern that fills a glyph is named"
    (lossesOf (statePdf "<< /Pattern << /P1 5 0 R >> /Font << /F1 6 0 R >> >>"
      "/Pattern cs /P1 scn BT /F1 80 Tf 20 10 Td (a) Tj ET"
      #[tile, "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 1000 1000] /FontMatrix [0.001 0 0 0.001 0 0] \
          /CharProcs << /a 7 0 R >> /Encoding << /Type /Encoding /Differences [97 /a] >> \
          /FirstChar 97 /LastChar 97 /Widths [1000] >>",
        streamObj "1000 0 0 0 1000 1000 d1 0 0 1000 1000 re f"]) == .ok #[.resource "tiling-paint"])
  let stencil := syntheticPdfBin #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R \
      /Resources << /Pattern << /P1 5 0 R >> /XObject << /I1 6 0 R >> >> >>".toUTF8,
    (streamObj "/Pattern cs /P1 scn q 80 0 0 80 60 10 cm /I1 Do Q").toUTF8, tile.toUTF8,
    streamObjBin ⟨Array.replicate 8 0xF0⟩ "/Type /XObject /Subtype /Image /Width 8 /Height 8 /ImageMask true /BitsPerComponent 1 "]
  t "state: a stencil mask painted with a pattern is named" (lossesOf stencil == .ok #[.resource "stencil-pattern"])
  let bboxed := marksOf (statePdf "<< /Shading << /S0 5 0 R >> >>" "/S0 sh"
    #["<< /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 200 0] /BBox [50 25 150 75] \
        /Function << /FunctionType 2 /Domain [0 1] /C0 [1 0 0] /C1 [0 0 1] /N 1 >> /Extend [true true] >>"])
  t s!"state: a shading's BBox clips it ({repr (bboxed.map clipGeoms)})"
    (bboxed.map clipGeoms == #[#[box 50 25 100 50]])
  let jpeg ← IO.FS.readBinFile "testdata/corpus/rects.jpg"
  let jpegPdf (decode : String) := syntheticPdfBin #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources << /XObject << /I1 5 0 R >> >> >>".toUTF8,
    (streamObj "q 64 0 0 40 10 10 cm /I1 Do Q").toUTF8,
    streamObjBin jpeg s!"/Type /XObject /Subtype /Image /Width 64 /Height 40 /ColorSpace /DeviceRGB \
      /BitsPerComponent 8 /Filter /DCTDecode {decode}"]
  t "state: a JPEG passes through whole" (match PdfGfx.importPage (jpegPdf "") with
    | .ok imp => imp.figure.losses.isEmpty && imp.figure.rasters.map (·.bytes) == #[jpeg]
    | .error _ => false)
  t "state: a JPEG under a Decode that remaps it is named"
    (lossesOf (jpegPdf "/Decode [1 0 1 0 1 0]") == .ok #[.resource "dct-decode"])
  let cmykFills := (marksOf (statePdf "<< >>" "0 0 0 1 k 0 0 50 50 re f 1 0 0 0 k 50 0 50 50 re f 0.5 0 0 0.5 k 100 0 50 50 re f" #[])).filterMap
    fun m => match m with
      | .paint _ _ (some { paint := .solid c, .. }) _ _ _ => some (c.r, c.g, c.b)
      | _ => none
  -- pdftoppm shows the third (73, 118, 141): its green is 118.5 exactly
  -- here, which its decimal constants put a hair under the half.
  t s!"state: CMYK fills preview as pdftoppm shows them ({cmykFills})"
    (cmykFills == #[(35, 31, 32), (0, 173, 239), (73, 119, 141)])
  let cmykImage := syntheticPdfBin #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources << /XObject << /I1 5 0 R >> >> >>".toUTF8,
    (streamObj "q 20 0 0 10 10 10 cm /I1 Do Q").toUTF8,
    streamObjBin ⟨#[0, 0, 0, 255, 255, 0, 0, 0]⟩
      "/Type /XObject /Subtype /Image /Width 2 /Height 1 /ColorSpace /DeviceCMYK /BitsPerComponent 8 "]
  let samples := ((PdfGfx.importPage cmykImage).toOption.bind fun imp => imp.figure.rasters[0]?.bind rgbPixels).getD #[]
  t s!"state: CMYK samples preview as CMYK fills do ({samples})" (samples == #[(35, 31, 32), (0, 173, 239)])
  let grid : List Nat := [0, 51, 128, 200, 255]
  t "state: a sample's CMYK preview is the exact one, at every grid point of the cube"
    (grid.all fun c => grid.all fun m => grid.all fun y => grid.all fun k =>
      PdfGfx.cmykRgb8 c.toUInt8 m.toUInt8 y.toUInt8 k.toUInt8 ==
        PdfGfx.cmykRgb (mkRat c 255) (mkRat m 255) (mkRat y 255) (mkRat k 255))
  -- The test face, and the same program with its cmap's tag renamed, so the
  -- program holds no cmap at all.
  let face ← IO.FS.readBinFile (testFonts ++ "/OpenSans-Regular.ttf")
  let noCmap := Id.run do
    let mut b := face
    for k in [0:Ink.u16 face 4] do
      let entry := 12 + 16 * k
      if face.extract entry (entry + 4) == "cmap".toUTF8 then b := b.set! entry 0x78
    return b
  let ttPdf (prog : ByteArray) (flags : Nat) := syntheticPdfBin #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> >> >>".toUTF8,
    (streamObj "BT /F1 40 Tf 20 30 Td <242526> Tj ET").toUTF8,
    "<< /Type /Font /Subtype /TrueType /BaseFont /Placeholder /FirstChar 36 /LastChar 38 /Widths [600 600 600] \
      /FontDescriptor 6 0 R >>".toUTF8,
    s!"<< /Type /FontDescriptor /FontName /Placeholder /Flags {flags} /FontBBox [0 0 1000 1000] /ItalicAngle 0 \
      /Ascent 900 /Descent -200 /CapHeight 700 /StemV 80 /FontFile2 7 0 R >>".toUTF8,
    streamObjBin prog s!"/Length1 {prog.size} "]
  let mapped := marksOf (ttPdf face 32)
  let unmapped := marksOf (ttPdf noCmap 4)
  t s!"state: a TrueType program with no cmap draws its glyphs by their 'post' names ({unmapped.size} of {mapped.size})"
    (mapped.size == 3 && unmapped == mapped)
  -- An `re` of negative extent is the path PDF traces, from its corner
  -- toward the negative extents: a dash pattern starts there.
  let inverted := marksOf (statePdf "<< >>" "[4 2] 0 d 2 w 150 80 -100 -50 re S" #[])
  t s!"state: an re of negative extent keeps the corner order PDF traces ({repr (inverted.map fun m => match m with
      | .paint _ g _ _ _ _ => some g | _ => none)})"
    (match inverted.toList with
     | [.paint _ g _ _ _ _] => g == .path #[Gfx.Kit.rectPath (Dim.pt 150) (Dim.pt 80) (Dim.pt (-100)) (Dim.pt (-50))]
     | _ => false)
  -- A stroked glyph's lengths stand in its frame; drawn through it, they
  -- are the user space's: 0.5 pt wide, dashed 2 on 1 from 0.25.
  let inUser (m : Gfx.Affine) (v : Dim.Sp) : Rat := (v : Rat) * m.a / 65536
  let near (x y : Rat) : Bool := x - y ≤ mkRat 1 1000 && y - x ≤ mkRat 1 1000
  for mode in [1, 2] do
    let ttStroked := syntheticPdfBin #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
      "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
      "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> >> >>".toUTF8,
      (streamObj s!"{mode} Tr 0.5 w [2 1] 0.25 d BT /F1 40 Tf 20 30 Td <242526> Tj ET").toUTF8,
      "<< /Type /Font /Subtype /TrueType /BaseFont /Placeholder /FirstChar 36 /LastChar 38 /Widths [600 600 600] \
        /FontDescriptor 6 0 R >>".toUTF8,
      "<< /Type /FontDescriptor /FontName /Placeholder /Flags 32 /FontBBox [0 0 1000 1000] /ItalicAngle 0 \
        /Ascent 900 /Descent -200 /CapHeight 700 /StemV 80 /FontFile2 7 0 R >>".toUTF8,
      streamObjBin face s!"/Length1 {face.size} "]
    let strokes := (marksOf ttStroked).filterMap fun m => match m with
      | .paint ctm _ _ (some st) _ _ => some (inUser ctm st.width, st.dash.map (inUser ctm), inUser ctm st.phase)
      | _ => none
    t s!"state: a glyph stroked in mode {mode} strokes the width, dash and phase in force ({strokes})"
      (strokes.size == 3 && strokes.all fun (w, d, p) =>
        near w (mkRat 1 2) && d.size == 2 && (d[0]?.any (near · 2)) && (d[1]?.any (near · 1)) &&
          near p (mkRat 1 4))

open Tests.PdfNative in
/-- **PDF figures ship native web faces with no converter on the
machine**: an invented cairo-made figure included by `\includegraphics`,
and the corpus' boundary diagram, a stand-in lualatex answering its
picture with a committed boundary PDF (`lualatex-shade.pdf`), build HTML
with no converter on `PATH`. Neither W0605 nor W0378 fires, and the page embeds
exactly the engine's own drawing of each page (`PdfFaces.svgOf`) — before
faces were drawn natively, the first shipped a placeholder (W0605) and the
second had no face at all (W0378). An include's words ride beside its face
for find and copy, hidden from assistive technology, and are no description
(N0376 still names an include with none declared); and a document that
declares `\figures{ convert = none }` is never drawn by the converter — the
premise of the driver's refusal, two builds apart by the declaration. -/
def nativeFigureBuildChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let corpus ← IO.FS.realPath "testdata/corpus/diagram-boundary.tex"
  let chart ← fixture "cairo-chart.pdf"
  let shade ← fixture "lualatex-shade.pdf"
  let faceOf (pdf : ByteArray) (stretch : Bool) : Option String :=
    (PdfGfx.importPage pdf).toOption.map fun imp => HtmlResource.base64 (PdfFaces.svgOf imp.figure stretch)
  IO.FS.withTempDir fun dir => do
    let tools := dir / "bin"
    IO.FS.createDirAll tools
    IO.FS.writeFile (tools / "lualatex") "#!/bin/sh\n\
if [ \"$1\" = \"--version\" ]; then\n\
  printf '%s\\n' 'synthetic lualatex'\n\
  exit 0\n\
fi\n\
exec /bin/cp \"$LEANTEX_NATIVE_PDF\" pic.pdf\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", (tools / "lualatex").toString] }
    unless mode.exitCode == 0 do throw <| IO.userError "could not prepare the stand-in lualatex"
    IO.FS.writeBinFile (dir / "chart.pdf") chart
    IO.FS.writeBinFile (dir / "shade.pdf") shade
    IO.FS.writeFile (dir / "figure.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}",
      "\\includegraphics[alt={An invented chart}]{chart.pdf}", "\\end{document}", ""])
    IO.FS.writeBinFile (dir / "type1.pdf") type1FigurePdf
    let build (src out : System.FilePath) (answer : String := "shade.pdf") :
        IO (UInt32 × Array Lean.Json × String) := do
      let r ← IO.Process.output {
        cmd := binary.toString
        args := #[src.toString, "-o", out.toString, "--porcelain"]
        env := #[("PATH", some tools.toString), ("LEANTEX_FONT", some font.toString),
          ("LEANTEX_NATIVE_PDF", some (dir / answer).toString),
          ("XDG_CACHE_HOME", some (dir / ("cache-" ++ answer)).toString)] }
      let records := ((r.stdout.splitOn "\n").filterMap fun line => (Lean.Json.parse line).toOption).toArray
      let html ← if ← out.pathExists then IO.FS.readFile out else pure ""
      return (r.exitCode, records, html)
    let named (records : Array Lean.Json) (code : String) : Bool :=
      records.any fun record => record.getObjValAs? String "code" == .ok code
    -- An include's face stretches as its PDF form does; a boundary
    -- picture's keeps SVG's fit, as its converted face did.
    for (name, src, out, pdf, stretch) in [("the cairo figure", dir / "figure.tex", dir / "figure.html", chart, true),
        ("the boundary diagram", (corpus : System.FilePath), dir / "diagram.html", shade, false)] do
      let (code, records, html) ← build src out
      t s!"native faces: {name} builds HTML with no converter on PATH" (code == 0)
      t s!"native faces: {name} names no missing face (W0605, W0378) and no loss (W0609)"
        (!named records "W0605" && !named records "W0378" && !named records "W0609")
      t s!"native faces: {name}'s page embeds the engine's own drawing, byte for byte"
        ((faceOf pdf stretch).any fun face => (html.splitOn face).length ≥ 2)
    -- The figure's words ride the page as its PDF form carries them, for
    -- find and copy, hidden from sight and from assistive technology; the
    -- figure's name stays its declared alternative, and an include that
    -- declares none is still named by N0376 — words are no description.
    let (_, _, chartHtml) ← build (dir / "figure.tex") (dir / "figure-words.html")
    let wordsOpen := "<span class=\"" ++ HtmlDoc.figureWordsClass ++ "\" aria-hidden=\"true\">"
    let carried := ((chartHtml.splitOn wordsOpen)[1]?.map fun rest => (rest.splitOn "</span>")[0]?.getD "").getD ""
    t s!"native faces: an include's words ride beside its face, hidden from sight and assistive technology ({carried})"
      ((carried.splitOn "invented chart").length ≥ 2 && (chartHtml.splitOn "alt=\"An invented chart\"").length ≥ 2 &&
        (chartHtml.splitOn ("." ++ HtmlDoc.figureWordsClass ++ " {")).length == 2)
    IO.FS.writeFile (dir / "nameless.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "\\includegraphics{chart.pdf}", "\\end{document}", ""])
    let (code, records, namelessHtml) ← build (dir / "nameless.tex") (dir / "nameless.html")
    t s!"native faces: words are no description: an include with none declared is named by N0376 (exit {code})"
      (code == 0 && named records "N0376" && (namelessHtml.splitOn wordsOpen).length == 2)
    -- A boundary answer whose text is in a font the engine does not draw,
    -- with no converter: a picture the rendered subset draws in part takes
    -- the subset's drawing, its text in the document's faces (W0378 names
    -- the face); one it draws nothing of keeps the engine's drawing, its
    -- loss named (W0609). The first once shipped the drawing without text.
    IO.FS.writeFile (dir / "partial.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "An invented picture follows.", "",
      "\\begin{tikzpicture}", "  \\draw (0,0) rectangle (3,1);", "  \\pattern (0,0) rectangle (1,1);",
      "  \\node at (1.5,0.5) {Mark};", "\\end{tikzpicture}", "", "\\end{document}", ""])
    let (code, records, html) ← build (dir / "partial.tex") (dir / "partial.html") "type1.pdf"
    t s!"native faces: a textless answer for a picture the subset draws in part is the subset's (exit {code})"
      (code == 0 && named records "W0378" && !named records "W0609" && (html.splitOn "<svg").length ≥ 2 &&
        (html.splitOn "Mark").length ≥ 2)
    let (code, records, _) ← build corpus (dir / "diagram-type1.html") "type1.pdf"
    t s!"native faces: a textless answer for a picture the subset cannot draw is the engine's, its loss named (exit {code})"
      (code == 0 && named records "W0609" && !named records "W0378")
    -- The document refuses the converter by declaration: two builds of one
    -- lossy include apart by `\figures{ convert = none }` alone. Open, the
    -- converter is asked; refused, never, and the engine's drawing names the
    -- loss without offering an install.
    let ranLog := dir / "converter.log"
    IO.FS.writeFile (tools / "pdftocairo") ("#!/bin/sh\nif [ \"$1\" = -v ]; then printf '%s\\n' \
'synthetic converter 1' >&2; exit 0; fi\nprintf 'ran\\n' >> " ++ shQuote ranLog.toString ++
      "\nfor last; do :; done\nprintf '%s' '<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 10 10\"/>' > \"$last\"\n")
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", (tools / "pdftocairo").toString] }
    unless mode.exitCode == 0 do throw <| IO.userError "could not prepare the stand-in converter"
    let runs : IO Nat := do
      if ← ranLog.pathExists then
        return ((← IO.FS.readFile ranLog).splitOn "ran").length - 1
      else return 0
    let lossy (declared : Bool) : String := String.intercalate "\n" ([
      "\\documentclass{article}"] ++ (if declared then ["\\figures{ convert = none }"] else []) ++ [
      "\\begin{document}", "\\includegraphics[alt={A lossy figure}]{type1.pdf}", "\\end{document}", ""])
    IO.FS.writeFile (dir / "open.tex") (lossy false)
    IO.FS.writeFile (dir / "refused.tex") (lossy true)
    let before ← runs
    let (openCode, openRecords, _) ← build (dir / "open.tex") (dir / "open.html")
    let afterOpen ← runs
    let (refusedCode, refusedRecords, _) ← build (dir / "refused.tex") (dir / "refused.html")
    let afterRefused ← runs
    let lossHelp (records : Array Lean.Json) : String := String.join (records.filterMap fun r =>
      if r.getObjValAs? String "code" == .ok "W0609" then (r.getObjValAs? String "help").toOption else none).toList
    let subjects (records : Array Lean.Json) : Array String := records.filterMap fun r =>
      if r.getObjValAs? String "code" == .ok "W0609" || r.getObjValAs? String "code" == .ok "N0024" then
        (r.getObjValAs? String "subject").toOption else none
    t s!"native faces: open, the converter is asked for a lossy include (exit {openCode}, {afterOpen - before} runs)"
      (openCode == 0 && afterOpen > before && subjects openRecords == #["figure:pdf:font:type1"])
    t s!"native faces: \\figures\{ convert = none } never asks it, and names the loss on the engine's drawing \
without offering an install (exit {refusedCode}, {afterRefused - afterOpen} runs, {lossHelp refusedRecords})"
      (refusedCode == 0 && afterRefused == afterOpen && subjects refusedRecords == #["figure:pdf:font:type1"] &&
        named refusedRecords "W0609" && ((lossHelp refusedRecords).splitOn "install").length == 1)
