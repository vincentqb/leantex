module

public import Tests.Support
public import Tests.GfxMatrix
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Cli

/-! PDF figures drawn natively: the importer, its web face, and the fixtures drawn with nothing
lost. -/

namespace Tests.PdfNative

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

/-- A mark on the PDF writer's grid: the values its operators spell, as a reader of the bytes gets
them back. -/
def pdfGrid : Gfx.Mark → Gfx.Mark
  | .paint ctm g fl st clips alphas =>
    .paint ctm g.normal.quantize (fl.map Gfx.Fill.quantize) (st.map Gfx.Stroke.quantize)
      (gridClips clips) alphas
  | .raster ctm k clips alphas => .raster ctm k (gridClips clips) alphas
  | .shading g clips alphas => .shading g.quantize (gridClips clips) alphas
where
  gridClips (clips : Array (Gfx.Affine × Gfx.Clip)) : Array (Gfx.Affine × Gfx.Clip) :=
    clips.map fun (m, c) => (m, { c with geom := c.geom.normal.quantize })

/-- A content stream's tokens spelled back by the tokenizer's writer and read again
(`scan_render_exact`). -/
def roundTrips (toks : Array PdfContentLex.Tok) : Bool :=
  let again := PdfContentLex.scan (PdfContentLex.render toks)
  again.size == toks.size && (again.zip toks).all fun (a, b) => match a, b with
    | .val x, .val y => x == y
    | .op x, .op y => x == y
    | .inline d x, .inline e y => d.size == e.size && x == y
    | _, _ => false

end Tests.PdfNative

open Tests.PdfNative in
/-- The content tokenizer reads operands, operators and inline images, skips comments and stray
delimiters, and what it reads spells back the same. -/
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
/-- A PDF figure's web face is native first (`Boundary.route`): the converter is asked only where
the import names a loss. -/
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
      t s!"face route: {name} ships the same face with or without the converter, never run"
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
  t "face route: an undrawn lossy import ships its lossy drawing, loss named"
    (f.route == .nativeWithLoss && f.native && f.bytes.isOk &&
      f.diags.size == 1 && f.diags.all (·.kind == .W0609))
  for (said, check) in [("refuses", (fun _ => pure (.refused "an external reference") :
      ByteArray → IO PicCache.Outcome)), ("does not finish", fun _ => pure (.inconclusive "the check was killed"))] do
    let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first drawing check
    t s!"face route: a converted face the check {said} gives the lossy drawing, in the check's words"
      (f.route == .nativeWithLoss && f.native && f.bytes.isOk && f.bytes.toOption != some converted &&
        f.diags.size == 1 && f.diags.all fun d => d.kind == .W0609 &&
          (hasStr (diagWords d) "external reference" || hasStr (diagWords d) "killed"))
  let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first drawing keeps .declared
  t "face route: refusing the converter keeps the lossy drawing, never asking"
    (f.route == .nativeWithLoss && f.native && (← asked.get) == 4)
  let helpOf (f : PdfFaces.Face) : String := String.join (f.diags.filterMap (·.help)).toList
  let noFace ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure none) keeps
  t s!"face route: with no converter on the machine, installing it is the remedy ({helpOf noFace})"
    (hasStr (helpOf noFace) "install poppler's pdftocairo" && noFace.diags.all (·.detail.isNone))
  let stopped ← PdfFaces.face "lossy.pdf" type1FigurePdf .first
    (pure (some (.error (.inconclusive "pdftocairo exited 137")))) keeps
  t s!"face route: an unfinished run names its repair conditionally, in its words ({helpOf stopped})"
    (hasStr (helpOf stopped) "if the reason says it cannot start" &&
      stopped.diags.all (·.detail == some "pdftocairo exited 137"))
  let verdict ← PdfFaces.face "lossy.pdf" type1FigurePdf .first
    (pure (some (.error (.refused "pdftocairo exited 1: an invented refusal")))) keeps
  t s!"face route: a converter's verdict offers acceptance, not an install ({helpOf verdict})"
    (!verdict.diags.isEmpty && !hasStr (helpOf verdict) "install" &&
      hasStr (helpOf verdict) "\\allow{W0609}" && verdict.diags.all (·.detail == some "pdftocairo exited 1: an invented refusal"))
  let unfit ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure (some (.ok converted)))
    fun _ => pure (.refused "an external reference")
  t s!"face route: a face the check refuses offers only acceptance ({helpOf unfit})"
    (((helpOf unfit).splitOn "install").length == 1 && ((helpOf unfit).splitOn "convert = none").length == 1 &&
      ((helpOf unfit).splitOn "\\allow{W0609}").length > 1)
  let declared ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (pure (some (.ok converted))) keeps .declared
  t s!"face route: a declared refusal names the declaration to lift, or acceptance ({helpOf declared})"
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
  t "face route: an unimportable page keeps a refused face for publication to refuse"
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
  -- A sequence's poster page differs in shape from its first frame, whose canvas it stretches onto.
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
/-- A face asks the host for its converter once, and only when it needs it (`PdfFaces.doorWith`). -/
def converterDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let probes ← IO.mkRef 0
  let runs ← IO.mkRef 0
  -- A probe slow enough that every face asking at once reaches it before the first answer.
  let probe (present : Bool) : IO Bool := do
    IO.sleep 20
    probes.modify (· + 1)
    return present
  let convert : IO (Except PicCache.Outcome ByteArray) := do
    runs.modify (· + 1)
    return .ok (svgDocument "<path d=\"M0 0L20 20\"/>")
  let keeps : ByteArray → IO PicCache.Outcome := fun _ => pure .drawn
  let chart ← fixture "cairo-chart.pdf"
  let door ← PdfFaces.doorWith (probe true)
  for _ in [0:3] do
    let _ ← PdfFaces.face "chart.pdf" chart .first (door convert) keeps
  t "converter door: faces imported exactly never probe the host"
    ((← probes.get) == 0 && (← runs.get) == 0)
  let asked ← (List.range 8).mapM fun _ =>
    IO.asTask (prio := .dedicated) (PdfFaces.face "lossy.pdf" type1FigurePdf .first (door convert) keeps)
  let faces ← asked.mapM fun task => IO.ofExcept task.get
  t s!"converter door: eight lossy faces asking at once probe the host once ({← probes.get})"
    ((← probes.get) == 1 && faces.all (·.route == .tool))
  probes.set 0
  runs.set 0
  let bare ← PdfFaces.doorWith (probe false)
  let f ← PdfFaces.face "lossy.pdf" type1FigurePdf .first (bare convert) keeps
  t "converter door: a host without the converter answers none, with no run"
    ((← probes.get) == 1 && (← runs.get) == 0 && f.route == .nativeWithLoss && !f.diags.isEmpty &&
      f.diags.all fun d => d.detail.isNone && d.help.any (hasStr · "install poppler's pdftocairo"))

open Tests.PdfNative in
/-- A native face is closed by construction: own fragments or `data:` rasters only, every attribute
valued, and no script, style or foreign object. -/
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
/-- The engine's PDF writer reads back: each raster-free matrix case imports to its marks on the
writer's grid (`pdfGrid`). -/
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
  -- The cases `PdfGfx.readback_id` covers, each held to its statement executed.
  let emitted (fig : Gfx.Figure Empty) := GfxPdf.emit names PdfGfx.noLabels PdfGfx.isoId fig
  let covered := all.filter fun (_, fig) =>
    PdfGfx.nodesPlain fig.nodes.toList && (PdfGfx.opsBack (emitted fig).toList).toArray == emitted fig
  t s!"readback: the theorem covers the matrix's plain cases ({covered.map (·.1)})"
    (covered.map (·.1) == #["an even-odd path", "a turned group clipped twice", "ink-free words"])
  let bare : PdfGfx.Ctx :=
    { doc := { bytes := .empty, locs := {}, memo := {}, memo_ok := fun _ _ h => by simp at h, root := 0
               trailer := .null }
      res := .dict #[], base := Gfx.Affine.unit, oc := none, box := ((0, 0), (0, 0)) }
  for (name, fig) in covered do
    let imp := PdfGfx.readStream bare (Pdf.render (emitted fig)).toUTF8
    t s!"readback: {name} reads back as the theorem states"
      (imp.losses.isEmpty && imp.marks.map PdfGfx.markScreen == fig.marks.map PdfGfx.markScreen)

open Tests.PdfNative in
/-- The committed fixtures from cairo, lualatex, the engine's writer and the dialect files draw with
nothing lost. -/
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
    -- SVG draws no rect of zero or negative size, and paints a square-capped dot PDF leaves unpainted.
    let rects := (attrsAll (faceTree imp.figure)).filter fun (tag, k, v) =>
      tag == "rect" && (k == "width" || k == "height") && (v == "0" || v.startsWith "-")
    t s!"fixture: the geometry dialect's face spells no rect SVG draws nothing for ({rects})" rects.isEmpty
    let svg := (String.fromUTF8? (PdfFaces.svgOf imp.figure)).getD ""
    t "fixture: the dialect's square-capped dot is left out, the round one kept"
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

/-- A PNG the engine writes reads back with its size, colour type and depth, under PNG's CRC. -/
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
/-- The glyph tables' contract: glyph-list names, the three base encodings and the CFF standard
strings read to Unicode's scalars. -/
def glyphListChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "glyph list: names read by the list and its conventions"
    (GlyphList.nameText "A" == some "A" && GlyphList.nameText "eacute" == some "é" &&
      GlyphList.nameText "uni00410042" == some "AB" && GlyphList.nameText "u1F600" == some "😀" &&
      GlyphList.nameText "f_f_i" == some "ffi" && GlyphList.nameText "a.sc" == some "a" &&
      GlyphList.nameText "uniD800" == none && GlyphList.nameText "notaglyphname" == none)
  -- The declared divergence: Mac OS Roman 0xBD is the ohm sign by name, Greek capital omega by Unicode's table.
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
/-- A PDF's simple and composite fonts select the glyphs they name, and vertical writing is
named. -/
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
    -- A name may select another glyph of the same character than the cmap's (`mu` for the micro sign).
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
    t s!"pdf font: bare CFF under WinAnsi selects each code's character by name ({wrong.take 6})" wrong.isEmpty
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
/-- Optional content shows as the default configuration and its membership dictionary decide, a
malformed visibility expression named once where it could decide. -/
def pdfOptionalContentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let cfg (dflt : String) : String := s!"/OCProperties << /OCGs [6 0 R 7 0 R] /D << {dflt} >> >>"
  let ocPdf (ocp mc props : String) (content : String) (extra : Array String) : ByteArray :=
    syntheticPdf (#[
      s!"<< /Type /Catalog /Pages 2 0 R {ocp} >>",
      "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
      s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
        /Resources << /Properties << /MC0 {mc} /MC1 6 0 R >> /XObject << /Fm0 8 0 R >> >> >>",
      streamObj content,
      props,
      "<< /Type /OCG /Name (Off) >>", "<< /Type /OCG /Name (On) >>"] ++ extra)
  let marked := "/OC /MC0 BDC 0 0 10 10 re f EMC"
  let ocDoc (props : String) (extra : Array String) : ByteArray :=
    ocPdf (cfg "/OFF [6 0 R]") "5 0 R" props marked extra
  let drawn (pdf : ByteArray) : Option Nat := (PdfGfx.importPage pdf).toOption.map (·.figure.marks.size)
  let malformed : Gfx.Loss := .property "malformed-visibility-expression"
  let named (pdf : ByteArray) : Option Nat :=
    (lossesOf pdf).toOption.map fun ls => (ls.filter (· == malformed)).size
  for (policy, shown) in [("/AnyOn", true), ("/AllOn", false), ("/AnyOff", true), ("/AllOff", false)] do
    t s!"optional content: under {policy} it is {if shown then "shown" else "hidden"}"
      (drawn (ocDoc s!"<< /Type /OCMD /OCGs [6 0 R 7 0 R] /P {policy} >>" #[]) == some (if shown then 1 else 0))
  t "optional content: a membership dictionary naming one group by reference follows it"
    (drawn (ocDoc "<< /Type /OCMD /OCGs 6 0 R >>" #[]) == some 0 &&
      drawn (ocDoc "<< /Type /OCMD /OCGs 7 0 R >>" #[]) == some 1)
  let held : List (String × String × Nat) := [
    ("/AnyOn over a group that is off and one naming no object hides", "/AnyOn", 0),
    ("/AllOff over a group that is off and one naming no object shows", "/AllOff", 1)]
  for (what, policy, shown) in held do
    t s!"optional content: {what}"
      (drawn (ocDoc s!"<< /Type /OCMD /OCGs [6 0 R 12 0 R] /P {policy} >>" #[]) == some shown)
  t "optional content: a membership dictionary naming only objects that do not exist has no effect"
    (drawn (ocDoc "<< /Type /OCMD /OCGs [12 0 R] /P /AllOff >>" #[]) == some 1)
  let unlisted : List (String × String × Array String × Nat) := [
    ("/AllOff over a group that is off and the page shows", "<< /Type /OCMD /OCGs [6 0 R 3 0 R] /P /AllOff >>",
      #[], 1),
    ("/AnyOn over a group that is off and the page hides", "<< /Type /OCMD /OCGs [6 0 R 3 0 R] /P /AnyOn >>",
      #[], 0),
    ("/AllOff over a group the document does not list has no effect",
      "<< /Type /OCMD /OCGs [9 0 R] /P /AllOff >>", #["<< >>", "<< /Type /OCG /Name (Unlisted) >>"], 1)]
  for (what, props, extra, shown) in unlisted do
    t s!"optional content: {what}" (drawn (ocDoc props extra) == some shown)
  t "optional content: under a document listing no groups a membership dictionary has no effect"
    (drawn (ocPdf "/OCProperties << /OCGs [] /D << >> >>" "5 0 R" "<< /Type /OCMD /OCGs [7 0 R] /P /AllOff >>"
      marked #[]) == some 1)
  let ve (expr : String) : String := s!"<< /Type /OCMD /VE {expr} >>"
  let decided : List (String × String × Array String × Nat) := [
    ("Not over the group that is on hides", ve "[/Not 7 0 R]", #[], 0),
    ("Not over the group that is off shows", ve "[/Not 6 0 R]", #[], 1),
    ("And over a group that is off hides", ve "[/And 7 0 R 6 0 R]", #[], 0),
    ("And over groups that are on shows", ve "[/And 7 0 R 7 0 R]", #[], 1),
    ("Or over a group that is on shows", ve "[/Or 6 0 R 7 0 R]", #[], 1),
    ("Or over a group that is off hides", ve "[/Or 6 0 R]", #[], 0),
    ("a nested expression decides", ve "[/Or [/Not 7 0 R] 6 0 R]", #[], 0),
    ("a nested expression shows", ve "[/And [/Not 6 0 R] 7 0 R]", #[], 1),
    ("a nested expression by reference decides", ve "[/Or 9 0 R 6 0 R]",
      #["<< >>", "[/Not 7 0 R]"], 0),
    ("an expression by reference decides", ve "9 0 R", #["<< >>", "[/Not 7 0 R]"], 0),
    ("an expression read twice is no cycle", ve "[/And 9 0 R 9 0 R]", #["<< >>", "[/Not 6 0 R]"], 1),
    ("the expression hides where the policy shows",
      "<< /Type /OCMD /OCGs [7 0 R] /P /AnyOn /VE [/Not 7 0 R] >>", #[], 0),
    ("the expression shows where the policy hides",
      "<< /Type /OCMD /OCGs [6 0 R] /P /AnyOn /VE [/Not 6 0 R] >>", #[], 1)]
  for (what, props, extra, shown) in decided do
    t s!"optional content: {what}"
      (drawn (ocDoc props extra) == some shown && named (ocDoc props extra) == some 0)
  let chain : Array String := (Array.range 40).map fun i => s!"[/And {i + 10} 0 R {i + 10} 0 R]"
  let shared := ocDoc (ve "9 0 R") (#["<< >>"] ++ chain ++ #["[/Not 6 0 R]"])
  t "optional content: forty expressions each naming the next twice decide"
    (drawn shared == some 1 && named shared == some 0)
  let partly : List (String × String × Nat) := [
    ("And over a group that is off and an unreadable operand hides", ve "[/And 6 0 R 3]", 0),
    ("Or over a group that is on and an unreadable operand shows", ve "[/Or 3 7 0 R]", 1),
    ("Not over an And its readable operand decides shows", ve "[/Not [/And 6 0 R 3]]", 1)]
  for (what, props, shown) in partly do
    t s!"optional content: {what}, naming nothing"
      (drawn (ocDoc props #[]) == some shown && named (ocDoc props #[]) == some 0)
  let unreadable : List (String × String × Array String) := [
    ("an unknown operator", ve "[/Xor 7 0 R]", #[]),
    ("an unknown operator beside a policy that hides",
      "<< /Type /OCMD /OCGs [6 0 R] /VE [/Xor 7 0 R] >>", #[]),
    ("Not over two operands", ve "[/Not 6 0 R 7 0 R]", #[]),
    ("Or over no operand", ve "[/Or]", #[]),
    ("And over a group that is on and an operand that is a number", ve "[/And 7 0 R 3]", #[]),
    ("And over a group that is on and an operand naming no object", ve "[/And 7 0 R 12 0 R]", #[]),
    ("Not over a dictionary that is no group", ve "[/Not 3 0 R]", #[]),
    ("an expression that refers to itself", ve "9 0 R", #["<< >>", "[/Not 9 0 R]"])]
  for (what, props, extra) in unreadable do
    t s!"optional content: {what} shows, named"
      (drawn (ocDoc props extra) == some 1 && named (ocDoc props extra) == some 1)
  let noArray := ocDoc "<< /Type /OCMD /OCGs [6 0 R] /VE 7 0 R >>" #[]
  t "optional content: an expression that is no array leaves the policy to decide, named"
    (drawn noArray == some 0 && named noArray == some 1)
  for (what, expr) in [("null", "null"), ("a reference naming no object", "12 0 R")] do
    let absent := ocDoc s!"<< /Type /OCMD /OCGs [6 0 R] /VE {expr} >>" #[]
    t s!"optional content: an expression that is {what} is absent, the policy deciding"
      (drawn absent == some 0 && named absent == some 0)
  let twice (props : String) : ByteArray :=
    ocPdf (cfg "/OFF [6 0 R]") "5 0 R" props (marked ++ " " ++ marked) #[]
  t "optional content: a membership dictionary met twice decides both, a malformed one named once"
    (drawn (twice (ve "[/Not 7 0 R]")) == some 0 && drawn (twice (ve "[/Xor 7 0 R]")) == some 2 &&
      named (twice (ve "[/Xor 7 0 R]")) == some 1)
  let within := ocPdf (cfg "/OFF [6 0 R]") "5 0 R" (ve "[/Xor 7 0 R]")
    "/OC /MC1 BDC /OC /MC0 BDC 0 0 10 10 re f EMC EMC" #[]
  t "optional content: a malformed expression inside hidden content shows nothing and names nothing"
    (drawn within == some 0 && named within == some 0 &&
      drawn (ocDoc (ve "[/Xor 7 0 R]") #[]) == some 1 && named (ocDoc (ve "[/Xor 7 0 R]") #[]) == some 1)
  let thenShown := ocPdf (cfg "/OFF [6 0 R]") "5 0 R" (ve "[/Xor 7 0 R]")
    ("/OC /MC1 BDC /OC /MC0 BDC 0 0 10 10 re f EMC EMC " ++ marked) #[]
  t "optional content: a malformed expression met hidden and then shown is named"
    (drawn thenShown == some 1 && named thenShown == some 1)
  let tiling (content : String) : ByteArray := syntheticPdf #[
    s!"<< /Type /Catalog /Pages 2 0 R {cfg "/OFF [6 0 R]"} >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
      /Resources << /Properties << /MC1 6 0 R >> /Pattern << /P1 8 0 R >> >> >>",
    streamObj content, ve "[/Xor 7 0 R]",
    "<< /Type /OCG /Name (Off) >>", "<< /Type /OCG /Name (On) >>",
    streamObj "/OC /MC0 BDC 0 0 5 5 re f EMC" "/PatternType 1 /PaintType 1 /TilingType 1 \
      /BBox [0 0 10 10] /XStep 10 /YStep 10 /Resources << /Properties << /MC0 5 0 R >> >> "]
  let painted := tiling "/Pattern cs /P1 scn 0 0 50 50 re f"
  let hiddenTiles := tiling "/OC /MC1 BDC /Pattern cs /P1 scn 0 0 50 50 re f EMC"
  t "optional content: a tiling's malformed expression is named where the tiling shows, not where it is hidden"
    (named painted == some 1 && drawn hiddenTiles == some 0 && named hiddenTiles == some 0)
  let byResources := ocPdf (cfg "/OFF [6 0 R]") "5 0 R" (ve "[/Not 7 0 R]") (marked ++ " /Fm0 Do")
    #[streamObj "/OC /MC0 BDC 20 0 10 10 re f EMC" "/Type /XObject /Subtype /Form /BBox [0 0 100 50] \
      /Resources << /Properties << /MC0 9 0 R >> >> ", ve "[/Not 6 0 R]"]
  t "optional content: one property name in a page's and a form's resources decides each by its own"
    (drawn byResources == some 1)
  t "optional content: a membership dictionary written in place decides"
    (drawn (ocPdf (cfg "/OFF [6 0 R]") "<< /Type /OCMD /OCGs [6 0 R] >>" "<< >>" marked #[]) == some 0 &&
      drawn (ocPdf (cfg "/OFF [6 0 R]") "<< /Type /OCMD /VE [/Not 6 0 R] >>" "<< >>" marked #[]) == some 1)
  let form (oc : String) : ByteArray :=
    ocPdf (cfg "/OFF [6 0 R]") "5 0 R" "<< >>" "/Fm0 Do"
      #[streamObj "0 0 10 10 re f" s!"/Type /XObject /Subtype /Form /BBox [0 0 100 50] /OC {oc}"]
  t "optional content: a form's expression decides, and a malformed one is named"
    (drawn (form "<< /Type /OCMD /VE [/Not 7 0 R] >>") == some 0 &&
      drawn (form "<< /Type /OCMD /VE [/Not 6 0 R] >>") == some 1 &&
      drawn (form "<< /Type /OCMD /VE [/Xor 6 0 R] >>") == some 1 &&
      named (form "<< /Type /OCMD /VE [/Xor 6 0 R] >>") == some 1)
  let based : List (String × String × String × Array String × Nat) := [
    ("a base state of OFF hides a group ON does not list", "/BaseState /OFF /ON [7 0 R]", "6 0 R", #[], 0),
    ("a base state of OFF keeps a group ON lists", "/BaseState /OFF /ON [7 0 R]", "7 0 R", #[], 1),
    ("OFF overrides ON", "/BaseState /OFF /ON [7 0 R] /OFF [7 0 R]", "7 0 R", #[], 0),
    ("a base state of ON hides what OFF lists", "/BaseState /ON /OFF [6 0 R]", "6 0 R", #[], 0),
    ("an unchanged base state keeps groups on", "/BaseState /Unchanged", "7 0 R", #[], 1),
    ("a base state of OFF leaves a group the document does not list", "/BaseState /OFF", "9 0 R",
      #["<< >>", "<< /Type /OCG /Name (Unlisted) >>"], 1),
    ("OFF leaves a group the document does not list", "/OFF [9 0 R]", "9 0 R",
      #["<< >>", "<< /Type /OCG /Name (Unlisted) >>"], 1)]
  for (what, dflt, mc, extra, shown) in based do
    t s!"optional content: {what}"
      (drawn (ocPdf (cfg dflt) mc "<< >>" marked extra) == some shown)
  let unconfigured : List (String × String) := [
    ("no optional content properties", ""),
    ("properties with no default configuration", "/OCProperties << /OCGs [6 0 R 7 0 R] >>"),
    ("properties whose groups are no array", "/OCProperties << /OCGs 6 0 R /D << /OFF [6 0 R] >> >>"),
    ("properties whose default configuration is no dictionary", "/OCProperties << /OCGs [6 0 R 7 0 R] /D 5 >>")]
  for (what, ocp) in unconfigured do
    t s!"optional content: under {what} nothing is hidden"
      (drawn (ocPdf ocp "5 0 R" (ve "[/Not 7 0 R]") marked #[]) == some 1 &&
        drawn (ocPdf ocp "5 0 R" "<< /Type /OCMD /OCGs [7 0 R] /P /AllOff >>" marked #[]) == some 1)

open Tests.PdfNative in
/-- The interpreter keeps PDF's meaning where it is subtle, and names the shadings the gradient
model only approaches. -/
def pdfInterpreterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
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
  t s!"interpreter: a function held to part of the domain stops where held ({st})"
    (lossesOf narrow == .ok #[] && st.map (·.1) == #["0", "0.5", "1"] && st[1]?.map (·.2) == st[2]?.map (·.2))
  let late := shading (shaded "/DeviceRGB" (stitching "[0.25 1]" "[0.5]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 1 0]" "[0 0 1]"]) "[0 1]") "/S0 sh"
  let st := faceStops late
  t s!"interpreter: a stitching held to part of the domain stops where held ({st})"
    (lossesOf late == .ok #[] && st.map (·.1) == #["0", "0.25", "0.5", "1"] &&
      st[0]?.map (·.2) == st[1]?.map (·.2))
  let jump := shading (shaded "/DeviceRGB" (stitching "[0 1]" "[0.5]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 0 1]" "[0 0 1]"]) "[0 0.5]") "/S0 sh"
  let st := faceStops jump
  t s!"interpreter: a domain ending at a colour jump ends on both colours ({st})"
    (lossesOf jump == .ok #[] && st.map (·.1) == #["0", "1", "1"] && st[1]?.map (·.2) != st[2]?.map (·.2))
  let early := shading (shaded "/DeviceRGB" (stitching "[0 0.75]" "[0.75]" "[0 1 0 1]"
    [seg "[1 0 0]" "[0 1 0]", seg "[0 0 1]" "[0 0 1]"]) "[0 1]") "/S0 sh"
  let st := faceStops early
  t s!"interpreter: a stitching ending early holds its last colour past its end ({st})"
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

/-- A raster's pixels as 8-bit RGB, where its PNG holds them so (rows behind filter byte 0). -/
def rgbPixels (r : Gfx.Raster) : Option (Array (UInt8 × UInt8 × UInt8)) := do
  let plan ← (Image.decode r.bytes).toOption
  let rows ← (Flate.inflate plan.data (r.pxW * r.pxH * 4 + r.pxH)).toOption
  let stride := r.pxW * 3 + 1
  return (Array.range (r.pxW * r.pxH)).map fun i =>
    let pos := (i / r.pxW) * stride + 1 + (i % r.pxW) * 3
    (rows[pos]?.getD 0, rows[pos + 1]?.getD 0, rows[pos + 2]?.getD 0)

end Tests.PdfNative

open Tests.PdfNative in
/-- What the graphics state carries reaches the marks it paints, and what the model cannot say is
named. -/
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
  -- pdftoppm shows (73, 118, 141): green is exactly 118.5 here, which its constants put just under.
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
  t "state: a sample's CMYK preview is exact at every grid point of the cube"
    (grid.all fun c => grid.all fun m => grid.all fun y => grid.all fun k =>
      PdfGfx.cmykRgb8 c.toUInt8 m.toUInt8 y.toUInt8 k.toUInt8 ==
        PdfGfx.cmykRgb (mkRat c 255) (mkRat m 255) (mkRat y 255) (mkRat k 255))
  -- The test face, and the same program with its cmap tag renamed so it holds no cmap.
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
  t s!"state: a cmap-less TrueType program draws glyphs by 'post' names ({unmapped.size} of {mapped.size})"
    (mapped.size == 3 && unmapped == mapped)
  -- An `re` of negative extent traces from its corner toward the negative extents, where a dash starts.
  let inverted := marksOf (statePdf "<< >>" "[4 2] 0 d 2 w 150 80 -100 -50 re S" #[])
  t s!"state: an re of negative extent keeps the corner order PDF traces ({repr (inverted.map fun m => match m with
      | .paint _ g _ _ _ _ => some g | _ => none)})"
    (match inverted.toList with
     | [.paint _ g _ _ _ _] => g == .path #[Gfx.Kit.rectPath (Dim.pt 150) (Dim.pt 80) (Dim.pt (-100)) (Dim.pt (-50))]
     | _ => false)
  -- A stroked glyph's lengths stand in its frame: in user space 0.5 pt wide, dashed 2 on 1 from 0.25.
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
/-- Each filter's output stops at the cap its chain passes, a cap hit told from malformed data,
and a figure names the loss of a stream that does not decode as what stopped it: an image's data,
a form's content, an image's mask, an indexed lookup, a ToUnicode map and a CID-to-glyph map. -/
def pdfStreamLossChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let filter (names : List String) : PdfRead.Obj :=
    .dict #[("Filter", .arr (names.map PdfRead.Obj.name).toArray)]
  let decoded (dict : PdfRead.Obj) (raw : ByteArray) (cap : Nat) : Option ByteArray :=
    match PdfFilters.decodeCapped dict raw cap with
    | .ok (.bytes b) => some b
    | _ => none
  let zs := "zzzzz~>".toUTF8
  let isBudget (r : Except Flate.Error PdfFilters.Decoded) : Bool := r matches .error .budget
  let isMalformed (r : Except Flate.Error PdfFilters.Decoded) : Bool := r matches .error (.malformed _)
  t "filters: a cap hit is the budget and broken data malformed, in every expanding filter"
    (isBudget (PdfFilters.decodeCapped (filter ["A85"]) zs 19) &&
      isBudget (PdfFilters.decodeCapped (filter ["RL"]) (bytes [0xFB, 0x41, 0x80]) 5) &&
      isBudget (PdfFilters.decodeCapped (filter ["LZW"])
        (bytes [0x80, 0x10, 0x60, 0x50, 0x38, 0x24, 0x04]) 9) &&
      isBudget (PdfFilters.decodeCapped (filter ["Fl"]) (Flate.deflate ⟨Array.replicate 32 0⟩) 31) &&
      isMalformed (PdfFilters.decodeCapped (filter ["A85"]) "x~>".toUTF8 100) &&
      isMalformed (PdfFilters.decodeCapped (filter ["Fl"]) (bytes [0x78, 0x01, 7]) 100))
  let page (res ink : String) (extra : Array ByteArray) : ByteArray := syntheticPdfBin (#[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 100] /Contents 4 0 R /Resources {res} >>".toUTF8,
    (streamObj ink).toUTF8] ++ extra)
  let zeros := overBudgetZeros ()
  let over (dict : String) : ByteArray := streamObjBin zeros dict
  t "figures: an image whose data inflates past the budget names the budget"
    (lossesOf (page "<< /XObject << /I1 5 0 R >> >>" "q 20 0 0 10 10 10 cm /I1 Do Q"
      #[over "/Type /XObject /Subtype /Image /Width 1 /Height 1 /ColorSpace /DeviceGray \
        /BitsPerComponent 8 /Filter /FlateDecode "]) == .ok #[.budget "image-data"])
  t "figures: a form whose content inflates past the budget names the budget"
    (lossesOf (page "<< /XObject << /X1 5 0 R >> >>" "/X1 Do"
      #[over "/Type /XObject /Subtype /Form /BBox [0 0 10 10] /Filter /FlateDecode "]) ==
      .ok #[.budget "form-data"])
  t "figures: a font whose ToUnicode stream inflates past the budget names the budget"
    ((lossesOf (page "<< /Font << /F1 5 0 R >> >>" "BT /F1 12 Tf 10 10 Td (A) Tj ET"
      #["<< /Type /Font /Subtype /TrueType /BaseFont /Placeholder /ToUnicode 6 0 R >>".toUTF8,
        over "/Filter /FlateDecode "])).toOption.any (·.contains (.budget "tounicode")))
  t "filters: ASCII85 past its cap is refused" ((decoded (filter ["A85"]) zs 19).isNone)
  t "filters: ASCII85 up to its cap decodes"
    (decoded (filter ["A85"]) zs 20 == some ⟨Array.replicate 20 0⟩)
  t "filters: an ASCII85 final group past the cap is refused"
    ((decoded (filter ["A85"]) "zzzz9jq~>".toUTF8 17).isNone &&
      (decoded (filter ["A85"]) "zzzz9jq~>".toUTF8 18).isSome)
  t "filters: the chain passes its cap to ASCII85 after another filter"
    ((decoded (filter ["AHx", "A85"]) "7A7A7A7A7A7E3E>".toUTF8 19).isNone &&
      (decoded (filter ["AHx", "A85"]) "7A7A7A7A7A7E3E>".toUTF8 20).isSome)
  t "filters: run-length and Flate stop at the chain's cap"
    ((decoded (filter ["RL"]) (bytes [0xFB, 0x41, 0x80]) 5).isNone &&
      (decoded (filter ["RL"]) (bytes [0xFB, 0x41, 0x80]) 6).isSome &&
      (decoded (filter ["Fl"]) (Flate.deflate ⟨Array.replicate 32 0⟩) 31).isNone &&
      (decoded (filter ["Fl"]) (Flate.deflate ⟨Array.replicate 32 0⟩) 32).isSome)
  let lzw := bytes [0x80, 0x10, 0x60, 0x50, 0x38, 0x24, 0x04]
  t "filters: LZW stops at the chain's cap"
    ((decoded (filter ["LZW"]) lzw 9).isNone &&
      decoded (filter ["LZW"]) lzw 10 == some ⟨Array.replicate 10 65⟩)
  let broken := streamObj "x~>" "/Filter /ASCII85Decode "
  let image (mask : String) := statePdf "<< /XObject << /I1 5 0 R >> >>" "q 20 0 0 10 10 10 cm /I1 Do Q"
    #[streamObj "AB" "/Type /XObject /Subtype /Image /Width 2 /Height 1 /ColorSpace /DeviceGray \
        /BitsPerComponent 8 /Mask 6 0 R ",
      streamObj "?" s!"/Type /XObject /Subtype /Image /Width 2 /Height 1 /ImageMask true \
        /BitsPerComponent 1 {mask}"]
  t "figures: an image whose mask stream decodes is drawn with no loss" (lossesOf (image "") == .ok #[])
  t "figures: an image whose mask stream does not decode is named"
    (lossesOf (image "/Filter /ASCII85Decode ") == .ok #[.resource "mask-image"])
  let keyed := statePdf "<< /XObject << /I1 5 0 R >> >>" "q 20 0 0 10 10 10 cm /I1 Do Q"
    #[streamObj "AB" "/Type /XObject /Subtype /Image /Width 2 /Height 1 /ColorSpace /DeviceGray \
        /BitsPerComponent 8 /Mask 6 0 R ", "[65 65]"]
  t "figures: an image whose colour-key mask stands behind a reference is drawn with no loss"
    (lossesOf keyed == .ok #[])
  let indexed (lookup : String) := statePdf "<< /XObject << /I1 5 0 R >> >>"
    "q 20 0 0 10 10 10 cm /I1 Do Q"
    #[streamObj "\x00\x01" "/Type /XObject /Subtype /Image /Width 2 /Height 1 \
        /ColorSpace [/Indexed /DeviceRGB 1 6 0 R] /BitsPerComponent 8 ", lookup]
  t "figures: an indexed image whose lookup stream decodes is drawn with no loss"
    (lossesOf (indexed (streamObj "\x00\x00\x7F\x7F\x00\x00")) == .ok #[])
  let palette := (PdfGfx.importPage (indexed "<00007F7F0000>")).toOption.any fun imp =>
    imp.figure.rasters.any fun r => bytesContain r.bytes "PLTE\x00\x00\x7F\x7F\x00\x00"
  t "figures: an indexed image reads a lookup string standing as its own object"
    (lossesOf (indexed "<00007F7F0000>") == .ok #[] && palette)
  t "figures: an indexed image whose lookup stream does not decode is named"
    (lossesOf (indexed broken) == .ok #[.resource "indexed-lookup"])
  let simple (toUnicode : String) := statePdf "<< /Font << /F1 5 0 R >> >>"
    "BT /F1 12 Tf 10 10 Td (A) Tj ET"
    #["<< /Type /Font /Subtype /TrueType /BaseFont /Placeholder /ToUnicode 6 0 R >>", toUnicode]
  let names (pdf : ByteArray) (l : Gfx.Loss) : Bool := (lossesOf pdf).toOption.any (·.contains l)
  t "figures: a font whose ToUnicode stream decodes names no ToUnicode loss"
    (!names (simple (streamObj "")) (.font "tounicode-unreadable"))
  t "figures: a font whose ToUnicode stream does not decode is named"
    (names (simple broken) (.font "tounicode-unreadable"))
  let composite (gidMap : String) := statePdf "<< /Font << /F1 5 0 R >> >>"
    "BT /F1 12 Tf 10 10 Td <0001> Tj ET"
    #["<< /Type /Font /Subtype /Type0 /BaseFont /Placeholder /Encoding /Identity-H \
        /DescendantFonts [6 0 R] >>",
      "<< /Type /Font /Subtype /CIDFontType2 /BaseFont /Placeholder /FontDescriptor 7 0 R \
        /CIDToGIDMap 8 0 R >>",
      "<< /Type /FontDescriptor /FontName /Placeholder /Flags 32 >>", gidMap]
  t "figures: a font whose CID-to-glyph stream decodes names no CID-to-glyph loss"
    (!names (composite (streamObj "\x00\x00\x00\x01")) (.font "cidtogid-unreadable"))
  t "figures: a font whose CID-to-glyph stream does not decode is named"
    (names (composite broken) (.font "cidtogid-unreadable"))
  t "figures: a font whose CID-to-glyph map is the identity behind a reference names no loss"
    (!names (composite "/Identity") (.font "cidtogid-unreadable"))

open Tests.PdfNative in
/-- PDF figures ship native web faces with no converter on the machine, and `\figures{ convert =
none }` never runs the converter. -/
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
    -- An include's face stretches as its PDF form does; a boundary picture's keeps SVG's fit.
    for (name, src, out, pdf, stretch) in [("the cairo figure", dir / "figure.tex", dir / "figure.html", chart, true),
        ("the boundary diagram", (corpus : System.FilePath), dir / "diagram.html", shade, false)] do
      let (code, records, html) ← build src out
      t s!"native faces: {name} builds HTML with no converter on PATH" (code == 0)
      t s!"native faces: {name} names no missing face (W0605, W0378) and no loss (W0609)"
        (!named records "W0605" && !named records "W0378" && !named records "W0609")
      t s!"native faces: {name}'s page embeds the engine's own drawing, byte for byte"
        ((faceOf pdf stretch).any fun face => (html.splitOn face).length ≥ 2)
    let (_, _, chartHtml) ← build (dir / "figure.tex") (dir / "figure-words.html")
    let wordsOpen := "<span class=\"" ++ HtmlDoc.figureWordsClass ++ "\" aria-hidden=\"true\">"
    let carried := ((chartHtml.splitOn wordsOpen)[1]?.map fun rest => (rest.splitOn "</span>")[0]?.getD "").getD ""
    t s!"native faces: an include's words ride beside its face, hidden from sight and assistive technology ({carried})"
      ((carried.splitOn "invented chart").length ≥ 2 && (chartHtml.splitOn "alt=\"An invented chart\"").length ≥ 2 &&
        (chartHtml.splitOn ("." ++ HtmlDoc.figureWordsClass ++ " {")).length == 2)
    IO.FS.writeFile (dir / "nameless.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "\\includegraphics{chart.pdf}", "\\end{document}", ""])
    let (code, records, namelessHtml) ← build (dir / "nameless.tex") (dir / "nameless.html")
    t s!"native faces: an include with no declared description is named by N0376 (exit {code})"
      (code == 0 && named records "N0376" && (namelessHtml.splitOn wordsOpen).length == 2)
    IO.FS.writeFile (dir / "partial.tex") (String.intercalate "\n" [
      "\\documentclass{article}", "\\begin{document}", "An invented picture follows.", "",
      "\\begin{tikzpicture}", "  \\draw (0,0) rectangle (3,1);", "  \\pattern (0,0) rectangle (1,1);",
      "  \\node at (1.5,0.5) {Mark};", "\\end{tikzpicture}", "", "\\end{document}", ""])
    let (code, records, html) ← build (dir / "partial.tex") (dir / "partial.html") "type1.pdf"
    t s!"native faces: a textless answer for a partly drawn picture is the subset's (exit {code})"
      (code == 0 && named records "W0378" && !named records "W0609" && (html.splitOn "<svg").length ≥ 2 &&
        (html.splitOn "Mark").length ≥ 2)
    let (code, records, _) ← build corpus (dir / "diagram-type1.html") "type1.pdf"
    t s!"native faces: a textless answer for an undrawable picture is the engine's, named (exit {code})"
      (code == 0 && named records "W0609" && !named records "W0378")
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
    t s!"native faces: \\figures\{ convert = none } never converts, names the loss, offers no install (exit {refusedCode}, {afterRefused - afterOpen} runs, {lossHelp refusedRecords})"
      (refusedCode == 0 && afterRefused == afterOpen && subjects refusedRecords == #["figure:pdf:font:type1"] &&
        named refusedRecords "W0609" && ((lossHelp refusedRecords).splitOn "install").length == 1)
