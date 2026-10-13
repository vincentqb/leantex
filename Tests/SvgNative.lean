module

public import LeanTex.Core.SvgImport
public import LeanTex.Core.SvgPoster
public import LeanTex.Core.WhatwgEncoding
public import LeanTex.Core.GfxSvg
public import Tests.Support

public section

/-! The native SVG reader's boundary and import, hermetic: the resource
boundary libxml's SAX events and XPath used to state, held over the parsed
tree with the same verdicts — the one widening is a `data:` PNG or JPEG
image — and the importer's reading of invented figures, asserted over the
figure's marks, never a dump. -/

namespace Tests

open LeanTex.Core LeanTex.Core.Gfx

/-- The judge's verdict, as the boundary error the old checks read. -/
def svgJudged (bytes : ByteArray) : Except String Unit :=
  match Svg.judge bytes with
  | .ok _ => .ok ()
  | .error r => .error r.message

/-- The boundary matrix the XPath/SAX boundary held, ported: every construct
it admitted is admitted, every one it refused is refused, with the boundary
named in the reason. -/
def svgNativeBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, body) in svgBoundaryAdmitted do
    check ref s!"native SVG boundary admits {name}" (svgJudged (svgDocument body)).toBool
  for (name, body) in svgBoundaryRefused do
    check ref s!"native SVG boundary refuses {name}" (svgBoundaryError (svgJudged (svgDocument (svgRedSquare ++ body))))
  let drawing := String.fromUTF8! (svgDocument svgRedSquare)
  for (name, source) in svgBoundaryMalformed drawing do
    check ref s!"native SVG reader refuses the {name} source" !(svgJudged source.toUTF8).toBool
  -- An exporter's doctype identifies its DTD; it does not load it.
  for (name, prolog) in [
      ("public", "<!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\" \
        \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">"),
      ("missing", "<!DOCTYPE svg SYSTEM \"missing.dtd\">"),
      ("empty subset", "<!DOCTYPE svg [ <!-- nothing --> ]>"),
      ("declaration", "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>")] do
    check ref s!"native SVG reader drops the inert {name} prolog"
      (svgJudged (prolog ++ drawing).toUTF8).toBool
  check ref "native SVG reader refuses a parsed entity reference even with a DTD named"
    !(svgJudged ("<!DOCTYPE svg SYSTEM \"outside.dtd\">" ++
      String.fromUTF8! (svgDocument "<rect fill=\"&outside;\"/>")).toUTF8).toBool
  check ref "native SVG reader names the DTD boundary"
    (match Svg.judge ("<!DOCTYPE svg [<!ENTITY x 'y'>]>" ++ drawing).toUTF8 with
      | .error r => hasStr r.message "DTD declarations and external entities"
      | .ok _ => false)

/-- The invented figures, in name order: every SVG under `testdata/svg`
and `testdata/corpus/figures`. -/
def svgFixtureFiles : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for dir in ["testdata/svg", "testdata/corpus/figures"] do
    for e in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
      if e.fileName.endsWith ".svg" then out := out.push e.path
  return out

/-- A tree written by the canonical writer reads back as it stands, for
every construct the writer spells: references in attributes and text,
white space the reader would normalize, empty and nested elements. -/
def xmlRoundTripChecks (ref : IO.Ref (List String)) : IO Unit := do
  let trees : List Xml.Node := [
    .elem "svg" #[("xmlns", "http://www.w3.org/2000/svg")] #[],
    .elem "a" #[("x", "1\n2\t3\r4"), ("y", "\"<&>'")] #[.text "a<b>&c\r\nd]]>e", .elem "b" #[] #[]],
    .elem "p:q" #[("xmlns:p", "urn:x"), ("p:r", "é ✓")] #[.elem "s" #[] #[.text " "], .text "t"]]
  for t in trees do
    check ref s!"XML round trip: {repr t}" (Xml.parse (Xml.render t) == .ok t)
  -- Every invented figure's parse reads back from its canonical spelling,
  -- and so does its judged tree — what the converter reads in place of the
  -- authored bytes, so the converter draws the tree the engine judged.
  for f in ← svgFixtureFiles do
    let bytes ← IO.FS.readBinFile f
    match Xml.parse bytes, Svg.judge bytes with
    | .ok n, .ok t =>
      check ref s!"XML round trip: {f.fileName.getD ""} reads back from its spelling"
        (Xml.parse (Xml.render n) == .ok n)
      check ref s!"XML round trip: {f.fileName.getD ""}'s judged tree reads back from its spelling"
        (match Svg.judge (Xml.renderItem t) with
         | .ok t' => t' == t
         | .error _ => false)
    | _, _ => check ref s!"XML round trip: {f.fileName.getD ""} parses" false

/-- What one invented figure's import paints. -/
def svgMarks (body : String) (w h : Nat := 20) : Array Mark × Array Gfx.Loss :=
  match Svg.importBytes (svgDocument body w h) with
  | .exact i | .lossy i => (i.fig.marks, i.fig.losses)
  | .refused _ => (#[], #[.element "refused"])

/-- The importer's reading of invented figures, over their marks. -/
def svgImportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let px (n : Int) : Int := n * Svg.pxSp
  -- A rect: one fill mark, its geometry in user space under the root's
  -- flip into the figure's y-up frame.
  let (ms, ls) := svgMarks "<rect x=\"2\" y=\"3\" width=\"4\" height=\"5\" fill=\"#ff0000\"/>"
  check ref "SVG import: a rect is one exact mark" (ls.isEmpty && ms.size == 1)
  check ref "SVG import: the rect's geometry is its attributes in user space"
    (ms.any fun m => match m with
      | .paint ctm (.rect x y w h) (some f) none _ _ =>
        x == px 2 && y == px 3 && w == px 4 && h == px 5 &&
          ctm == ⟨1, 0, 0, -1, 0, (px 20 : Rat)⟩ &&
          (match f.paint with | .solid c => c.r == 255 && c.g == 0 && c.b == 0 | _ => false)
      | _ => false)
  -- Stroke defaults are SVG's, stated in full: miter limit 4.
  let (ms, _) := svgMarks "<path d=\"M0 0L10 10\" fill=\"none\" stroke=\"blue\" stroke-width=\"2\"/>"
  check ref "SVG import: a stroke states SVG's miter limit and width"
    (ms.any fun m => match m with
      | .paint _ _ none (some s) _ _ => s.width == px 2 && s.miterLimit == 4 && s.join == .miter
      | _ => false)
  -- A gradient fill, resolved against the shape's box.
  let (ms, ls) := svgMarks "<defs><linearGradient id=\"g\"><stop offset=\"0\" stop-color=\"red\"/>\
    <stop offset=\"1\" stop-color=\"blue\"/></linearGradient></defs>\
    <rect width=\"20\" height=\"10\" fill=\"url(#g)\"/>"
  check ref "SVG import: a linear gradient paints its stops"
    (ls.isEmpty && ms.any fun m => match m with
      | .paint _ _ (some f) _ _ _ => match f.paint with
        | .gradient (.linear _ _ stops _) => stops.size == 2
        | _ => false
      | _ => false)
  -- A clip path and a group opacity reach the marks as clips and alphas.
  let (ms, ls) := svgMarks "<clipPath id=\"c\"><rect width=\"5\" height=\"5\"/></clipPath>\
    <g opacity=\"0.5\" clip-path=\"url(#c)\"><rect width=\"20\" height=\"20\"/></g>"
  check ref "SVG import: a clip and an opacity reach the mark"
    (ls.isEmpty && ms.any fun m => match m with
      | .paint _ _ _ _ clips alphas => clips.size == 1 && alphas.size == 1 && alphas[0]?.map (·.val) == some 500
      | _ => false)
  -- A use paints its symbol once per use.
  let (ms, ls) := svgMarks "<defs><path id=\"p\" d=\"M0 0h4v4z\"/></defs>\
    <use href=\"#p\" fill=\"green\"/><use href=\"#p\" x=\"10\" fill=\"green\"/>"
  check ref "SVG import: two uses paint the shared symbol twice" (ls.isEmpty && ms.size == 2)
  -- A reference cycle is named, never followed for ever.
  let (_, ls) := svgMarks "<g id=\"a\"><use href=\"#b\"/></g><g id=\"b\"><use href=\"#a\"/></g>"
  check ref "SVG import: a use cycle is a named loss" (ls.contains (.element "use cycle"))
  -- A raster image.
  let (ms, ls) := svgMarks s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" \
    width=\"10\" height=\"10\"/>"
  check ref "SVG import: a data PNG is one raster mark" (ls.isEmpty && ms.any fun m => match m with
    | .raster _ 0 _ _ => true
    | _ => false)
  -- Text is a run with its face request.
  match Svg.importBytes (svgDocument "<text x=\"1\" y=\"10\" font-family=\"Example Sans, sans-serif\" \
      font-weight=\"bold\" text-anchor=\"middle\">Hi <tspan fill=\"red\">there</tspan></text>") with
  | .exact i =>
    let runs := i.fig.labels.map (·.2)
    check ref "SVG import: text sets one run per styled piece" (runs.size == 2)
    check ref "SVG import: a run asks for its families in order, its weight and anchor"
      (runs.any fun r => r.text == "Hi " && r.face.families == #["Example Sans", "sans-serif"] &&
        r.face.weight == 700 && r.anchor == .middle && !r.follows)
    check ref "SVG import: a run with no position of its own follows the one before"
      (runs.any fun r => r.text == "there" && r.follows)
  | _ => check ref "SVG import: text imports exactly" false
  -- What the importer does not give its meaning is a keyed loss.
  for (name, body, loss) in [
      ("filter", "<filter id=\"f\"/><rect width=\"5\" height=\"5\" filter=\"url(#f)\"/>", Gfx.Loss.property "filter"),
      ("mask", "<mask id=\"m\"/><rect width=\"5\" height=\"5\" mask=\"url(#m)\"/>", .property "mask"),
      ("marker", "<path d=\"M0 0L5 5\" stroke=\"red\" marker-end=\"url(#m)\"/>", .property "marker-end"),
      ("pattern", "<pattern id=\"p\"/><rect width=\"5\" height=\"5\" fill=\"url(#p)\"/>", .element "pattern"),
      ("translucent stop", "<linearGradient id=\"g\"><stop stop-color=\"red\" stop-opacity=\"0.5\"/>\
        <stop offset=\"1\" stop-color=\"blue\"/></linearGradient><rect width=\"5\" height=\"5\" fill=\"url(#g)\"/>",
        .property "stop-opacity"),
      ("reflected spread", "<linearGradient id=\"g\" spreadMethod=\"reflect\"><stop stop-color=\"red\"/>\
        <stop offset=\"1\" stop-color=\"blue\"/></linearGradient><rect width=\"5\" height=\"5\" fill=\"url(#g)\"/>",
        .attribute "spreadMethod"),
      ("blend mode", "<rect width=\"5\" height=\"5\" style=\"mix-blend-mode: multiply\"/>", .property "mix-blend-mode"),
      ("text on a path", "<text><textPath href=\"#p\">a</textPath></text>", .element "textPath in text"),
      ("vector effect", "<path d=\"M0 0L5 5\" stroke=\"red\" vector-effect=\"non-scaling-stroke\"/>",
        .property "vector-effect"),
      ("paint order", "<text paint-order=\"stroke\">a</text>", .property "paint-order")] do
    let (_, ls) := svgMarks body
    check ref s!"SVG import names the {name} it does not draw" (ls.contains loss)


/-- A tree's marks, after an optional projection to its terminal pose. -/
def svgPose (bytes : ByteArray) (last : Bool) : Except String (Array Mark) := do
  let t ← match Svg.judge bytes with
    | .ok t => pure t
    | .error r => throw r.message
  let t ← if last then SvgPoster.terminal t else pure t
  return (Svg.importTree t).fig.marks

/-- The terminal-pose matrix the XSLT stylesheet held, ported: a timeline
the projection does not read is refused, naming it; an accepted one paints
exactly the independently authored static pose, and not the base drawing. -/
def svgPosterNativeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let doc (body : String) := svgDocument (width := 32) (height := 16) body
  for (name, body) in svgTerminalRefused do
    let source := doc body
    check ref s!"native SVG poster {name}: the base pose stays readable" (svgPose source false).toBool
    check ref s!"native SVG poster {name}: the last pose is refused, named"
      (match svgPose source true with
        | .error err => hasStr err "SVG last poster"
        | .ok _ => false)
  for (name, body, expected) in svgTerminalAccepted do
    match svgPose (doc body) false, svgPose (doc body) true, svgPose (doc expected) false with
    | .ok first, .ok last, .ok target =>
      check ref s!"native SVG poster {name}: the last pose is the expected static drawing" (last == target)
      check ref s!"native SVG poster {name}: the last pose differs from the base drawing" (first != last)
    | _, _, _ => check ref s!"native SVG poster {name}: every pose reads" false

/-- Symbols nested `depth` deep, each using the one below it twice: the
figure paints 2^(depth-1) copies of one square once expanded. -/
def nestedUses (depth : Nat) : ByteArray := Id.run do
  let mut defs := "<g id=\"s0\"><rect width=\"1\" height=\"1\"/></g>"
  for i in [1:depth] do
    defs := defs ++ s!"<g id=\"s{i}\"><use href=\"#s{i - 1}\"/><use href=\"#s{i - 1}\" x=\"0.5\"/></g>"
  return svgDocument (width := 40) (height := 40) s!"<defs>{defs}</defs><use href=\"#s{depth - 1}\"/>"

/-- **Uses that multiply are bounded.** A figure whose nested uses expand
past the import's budget keeps what it paints itself and drops its uses,
the drop named — its drawing, and every walk a backend makes over it,
stays within the budget however deep the nesting — while a figure within
the budget keeps every use. -/
def svgExpansionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let small := Svg.importTree ((Svg.judge (nestedUses 8)).toOption.getD (.text ""))
  let deep := Svg.importTree ((Svg.judge (nestedUses 24)).toOption.getD (.text ""))
  check ref "expansion: a figure within its budget keeps every use"
    (small.fig.losses.isEmpty && !small.fig.symbols.isEmpty && small.fig.marks.size == 128)
  check ref "expansion: a figure past its budget drops its uses, the drop named"
    (deep.fig.losses.contains (.budget "expanded uses") && deep.fig.symbols.isEmpty &&
      deep.fig.marks.size ≤ Svg.Budget.standard.expanded)


/-- **Every property the importer meets keeps its treatment**
(`Svg.propertyTable`): one that is a loss unless harmless is named when
declared otherwise and silent at each harmless value; an inert one moves
no mark and names nothing, whatever it is set to. The invariant whose
absence let a figure import exact while the importer ignored its
`transform-origin`, its `linearRGB` gradients and its preserved white
space. -/
def propertyTreatmentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let rect (style : String) := s!"<rect width=\"10\" height=\"10\" fill=\"red\" style=\"{style}\"/>"
  let (m0, l0) := svgMarks (rect "")
  for (p, t) in Svg.propertyTable do
    match t with
    | .lossUnless harmless =>
      let (_, ls) := svgMarks (rect s!"{p}: example-value")
      check ref s!"property {p}: a value that changes the drawing is named" (ls.contains (.property p))
      for h in harmless do
        let (_, ls) := svgMarks (rect s!"{p}: {h}")
        check ref s!"property {p}: '{h}' changes nothing and names nothing" (!ls.contains (.property p))
    | .inert =>
      let (ms, ls) := svgMarks (rect s!"{p}: example-value")
      check ref s!"property {p}: inert, it moves no mark and names nothing" (ms == m0 && ls == l0)
    | .honoured => pure ()
  for (p, harmless) in Svg.cssLost do
    let (_, ls) := svgMarks (rect s!"{p}: 3px")
    check ref s!"CSS property {p}: a sheet's value the importer does not read is named"
      (ls.contains (.property p))
    for h in harmless do
      let (_, ls) := svgMarks (rect s!"{p}: {h}")
      check ref s!"CSS property {p}: '{h}' names nothing" (!ls.contains (.property p))

/-- `transform-origin` is a transform about a point, in every spelling:
lengths, keywords, percentages of the viewport — the drawing of the same
transform written about the point. -/
def transformOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let about := svgMarks "<rect x=\"40\" y=\"40\" width=\"20\" height=\"20\" transform=\"rotate(45 50 50)\"/>"
    (w := 100) (h := 100)
  for (name, style) in [("lengths", "transform-origin: 50px 50px"), ("unitless", "transform-origin: 50 50"),
      ("keyword", "transform-origin: center"), ("percentages", "transform-origin: 50% 50%"),
      ("mixed", "transform-origin: center 50%"), ("with a z", "transform-origin: 50px 50px 0")] do
    let got := svgMarks s!"<rect x=\"40\" y=\"40\" width=\"20\" height=\"20\" transform=\"rotate(45)\" \
      style=\"{style}\"/>" (w := 100) (h := 100)
    check ref s!"transform-origin {name}: the transform turns about the point" (got == about)
  let attr := svgMarks "<rect x=\"40\" y=\"40\" width=\"20\" height=\"20\" transform=\"rotate(45)\" \
    transform-origin=\"50 50\"/>" (w := 100) (h := 100)
  check ref "transform-origin: the presentation attribute is the property" (attr == about)
  let (_, ls) := svgMarks "<rect width=\"20\" height=\"20\" transform=\"rotate(45)\" \
    style=\"transform-box: fill-box; transform-origin: center\"/>" (w := 100) (h := 100)
  check ref "transform-box: a box other than the viewport's is named" (ls.contains (.property "transform-box"))
  let (_, ls) := svgMarks "<linearGradient id=\"g\" color-interpolation=\"linearRGB\"><stop stop-color=\"red\"/>\
    <stop offset=\"1\" stop-color=\"blue\"/></linearGradient><rect width=\"20\" height=\"20\" fill=\"url(#g)\" \
    style=\"color-interpolation: linearRGB\"/>"
  check ref "color-interpolation: a linearRGB interpolation is named" (ls.contains (.property "color-interpolation"))
  let (_, ls) := svgMarks "<text x=\"1\" y=\"10\" style=\"white-space: pre\">a  b</text>"
  check ref "white-space: preserved white space is named" (ls.contains (.property "white-space"))

/-- The `font` shorthand is its longhands, each unsaid one reset; a system
font or a variant the importer does not set is named. -/
def fontShorthandChecks (ref : IO.Ref (List String)) : IO Unit := do
  match Svg.importBytes (svgDocument "<text x=\"1\" y=\"10\" font-weight=\"bold\" \
      style=\"font: italic 12px/1.5 'Example Sans', sans-serif\">Hi</text>") with
  | .exact i =>
    check ref "font shorthand: sets the style, size and families, and resets the weight"
      (i.fig.labels.any fun (_, r) => r.text == "Hi" && r.face.italic && r.face.weight == 400 &&
        r.face.families == #["Example Sans", "sans-serif"] && r.size == Svg.spOf 12)
  | _ => check ref "font shorthand: a shorthand the importer reads imports exactly" false
  match Svg.importBytes (svgDocument "<text x=\"1\" y=\"10\" style=\"font: 700 10px serif\">Hi</text>") with
  | .exact i =>
    check ref "font shorthand: a numeric weight before the size"
      (i.fig.labels.any fun (_, r) => r.face.weight == 700 && r.face.families == #["serif"])
  | _ => check ref "font shorthand: a numeric weight reads" false
  let (_, ls) := svgMarks "<text x=\"1\" y=\"10\" style=\"font: caption\">Hi</text>"
  check ref "font shorthand: a system font is named" (ls.contains (.property "font"))
  let (_, ls) := svgMarks "<text x=\"1\" y=\"10\" style=\"font: small-caps 12px serif\">Hi</text>"
  check ref "font shorthand: small capitals are named" (ls.contains (.property "font-variant"))

/-- Path data reads linearly, whatever its numbers spell: a number keeps
`maxSig` significant digits and reads the rest as a shift of its point; one
past the reader's range stops the path, named; a fraction below it reads
as zero; and a long path reads whole. -/
def pathDataBudgetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let long := String.ofList (List.replicate 60 '7')
  check ref "path data: a number keeps its significant digits and its magnitude"
    (match PathData.number long.toList with
      | some (d, []) => d.m == ((String.ofList (List.replicate 40 '7')).toNat!) * 10 ^ 20 && d.e == 0
      | _ => false)
  check ref "path data: digits past the kept ones in a fraction are dropped"
    (match PathData.number ("0." ++ long).toList with
      | some (d, []) => d.m == (String.ofList (List.replicate 40 '7')).toNat! && d.e == 40
      | _ => false)
  let huge := "M0 0L" ++ String.ofList (List.replicate 300000 '1') ++ " 0"
  let (cmds, stop) := PathData.parse huge
  check ref "path data: a number past the reader's range stops the path, its range named"
    (stop == .range && cmds.size == 1)
  let (_, ls) := svgMarks s!"<path d=\"{huge}\" stroke=\"red\"/>"
  check ref "path data: the importer names a path cut short by its range" (ls.contains Svg.pathRangeLoss)
  let tiny := "M0." ++ String.ofList (List.replicate 300000 '0') ++ "1 0L5 5"
  check ref "path data: a fraction below the range reads as zero, and the path reads on"
    (match PathData.parse tiny with
      | (#[.move false x _, .line false _ _], .done) => x.toRat == 0
      | _ => false)
  let segments := String.join (List.replicate 50000 "l1 1")
  let (cmds, stop) := PathData.parse ("M0 0" ++ segments)
  check ref "path data: a path of fifty thousand segments reads whole" (stop == .done && cmds.size == 50001)
  -- Writing reads back as written.
  let samples : List (Array PathData.Cmd) := [
    #[.move false ⟨0, 0⟩ ⟨-15, 1⟩, .line true ⟨1234567, 3⟩ ⟨-5, 0⟩, .close],
    #[.move true ⟨7, 0⟩ ⟨7, 2⟩, .arc false ⟨5, 0⟩ ⟨25, 1⟩ ⟨-30, 0⟩ true false ⟨1, 0⟩ ⟨0, 4⟩,
      .cubic false ⟨1, 0⟩ ⟨2, 0⟩ ⟨3, 0⟩ ⟨4, 0⟩ ⟨5, 0⟩ ⟨6, 0⟩, .smooth true ⟨0, 3⟩ ⟨1, 3⟩ ⟨-2, 0⟩ ⟨3, 0⟩,
      .quad false ⟨1, 1⟩ ⟨2, 1⟩ ⟨3, 1⟩ ⟨4, 1⟩, .smoothQuad true ⟨9, 0⟩ ⟨9, 0⟩, .horiz false ⟨100, 2⟩,
      .vert true ⟨-1, 0⟩]]
  for cs in samples do
    check ref s!"path data: a written path reads back as written: {PathData.render cs}"
      (PathData.parse (PathData.render cs) == (cs, .done))


/-- **An SVG's bytes read in the encoding they name** (`svgBoundaryEncodings`):
each admitted source's drawing sets its text as spelled, and each refused
one is refused with what refused it named — a narrowed one with the advice
to save it as UTF-8. The tables the decoders read hold their contract. -/
def svgEncodingChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref s!"WHATWG tables hold their contract: {WhatwgEncoding.dataFaults.toList.take 3}"
    WhatwgEncoding.dataFaults.isEmpty
  check ref "WHATWG labels: a label is trimmed and folded before it is looked up"
    (WhatwgEncoding.lookup "  Latin1\t" == some "windows-1252" &&
      WhatwgEncoding.lookup "SHIFT_JIS" == some "Shift_JIS" && WhatwgEncoding.lookup "latin-9" == none)
  let w1252 := WhatwgEncoding.scalarsOf ((WhatwgEncoding.singleByteIndex? "windows-1252").getD "")
  check ref "WHATWG windows-1252: 0x80 is the euro sign, 0x9F Ÿ, 0xFF ÿ, and 0x81 its control"
    (w1252[0]? == some 0x20AC && w1252[0x1F]? == some 0x178 && w1252[0x7F]? == some 0xFF &&
      w1252[1]? == some 0x81)
  for (name, bytes, text?) in svgBoundaryEncodings do
    match text?, Svg.importBytes bytes with
    | some t, .exact i =>
      check ref s!"encoding {name}: read, its text set as spelled"
        (i.fig.labels.any fun (_, r) => r.text == t)
    | none, .refused r =>
      let m := r.message
      check ref s!"encoding {name}: refused, what refused it named"
        (if svgBoundaryNarrowed name then hasStr m "save it as UTF-8"
         else hasStr m "encoding" || hasStr m "does not map" || hasStr m "code unit")
    | some _, _ => check ref s!"encoding {name}: read exactly" false
    | none, _ => check ref s!"encoding {name}: refused" false

/-- Whether two paints are one: a colour exactly; a gradient by kind, its
stops and frame respelled. -/
def paintAgrees : Paint → Paint → Bool
  | .solid a, .solid b => a == b
  | .gradient _, .gradient _ => true
  | _, _ => false

/-- How far the spelling's half-thousandth of a unit moves a mark's box,
through its frame: each coordinate the writer spells is within half a
thousandth of a user unit of its value, `pxSp` sp of the importer's local
frame per unit, imaged by the mark's own matrix; plus a sp each way for
`Box.image`'s outward rounding. -/
def readbackBound (ctm : Affine) : Int :=
  let abs (q : Rat) : Rat := if q < 0 then -q else q
  let scale := max (abs ctm.a + abs ctm.c) (abs ctm.b + abs ctm.d)
  Rat.ceil (scale * (Svg.pxSp : Rat) / 2000) + 2

/-- Two marks agree under the readback: one kind, one paint, rule, alphas
and clip count, and the readback's geometry box within its bound of the
source's. -/
def marksAgree (a b : Mark) : Bool :=
  let near (x y : Option Box) (t : Int) : Bool := match x, y with
    | some ((x0, y0), (x1, y1)), some ((u0, v0), (u1, v1)) =>
      (x0 - u0).natAbs ≤ t.toNat && (y0 - v0).natAbs ≤ t.toNat &&
        (x1 - u1).natAbs ≤ t.toNat && (y1 - v1).natAbs ≤ t.toNat
    | none, none => true
    | _, _ => false
  match a, b with
  | .paint _ _ fa sa ca aa, .paint cb _ fb sb cb' ab =>
    (match fa, fb with
     | some x, some y => paintAgrees x.paint y.paint && x.rule == y.rule && x.alpha == y.alpha
     | none, none => true
     | _, _ => false) &&
    (match sa, sb with
     | some x, some y => paintAgrees x.paint y.paint && x.cap == y.cap && x.join == y.join &&
         x.alpha == y.alpha && x.dash.size == y.dash.size
     | none, none => true
     | _, _ => false) &&
    ca.size == cb'.size && aa == ab && near (a.geomBox rasterUnit) (b.geomBox rasterUnit) (readbackBound cb)
  | .shading _ ca aa, .shading _ cb ab => ca.size == cb.size && aa == ab
  | .raster _ _ ca aa, .raster _ _ cb ab => ca.size == cb.size && aa == ab
  | _, _ => false

/-- **The writer's SVG reads back through the reader** — the executable
oracle the readback statement waits on: every invented figure the importer
draws whole, written as a standalone document with its labels left out
(`GfxSvg.document`), imports exactly again, its box within the spelling's
half-thousandth of a point and its marks the same marks in order
(`marksAgree`). A drawing the HTML page inlines is that
spelling, so a construct the writer spells and the reader refuses or
reads otherwise is a page the engine could not read back. -/
def svgReadbackChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut read := 0
  for f in ← svgFixtureFiles do
    let name := f.fileName.getD ""
    match Svg.importBytes (← IO.FS.readBinFile f) with
    | .exact i =>
      if !i.fig.rasters.isEmpty then continue
      let doc := (GfxSvg.document (fun _ _ => Html.text "") #[] i.fig).toUTF8
      match Svg.importBytes doc with
      | .exact j =>
        read := read + 1
        -- The writer spells the box in points to a thousandth, so a box off
        -- that grid (a size in millimetres) reads back within half of one.
        let ((x0, y0), (x1, y1)) := i.fig.box
        let ((u0, v0), (u1, v1)) := j.fig.box
        check ref s!"SVG readback {name}: the box reads back within the spelling's half-thousandth of a point"
          ([x0 - u0, y0 - v0, x1 - u1, y1 - v1].all fun d => d.natAbs ≤ 33)
        check ref s!"SVG readback {name}: {i.fig.marks.size} marks read back as {j.fig.marks.size}, each agreeing"
          (j.fig.marks.size == i.fig.marks.size &&
            (i.fig.marks.zip j.fig.marks).all fun (a, b) => marksAgree a b)
      | .lossy j => check ref s!"SVG readback {name}: read back with losses {repr j.fig.losses}" false
      | .refused r => check ref s!"SVG readback {name}: refused: {r.message}" false
    | .lossy _ | .refused _ => pure ()
  check ref s!"SVG readback: {read} figures read back" (read ≥ 9)
  -- The bound bites: a mark moved by twice its bound no longer agrees.
  let moved (m : Mark) : Mark := match m with
    | .paint c g fl st cl al =>
      .paint { c with e := c.e + 2 * ((readbackBound c : Int) : Rat) + 1 } g fl st cl al
    | m => m
  let probe := Svg.importBytes (svgDocument "<rect x=\"2\" y=\"3\" width=\"4\" height=\"5\"/>")
  match probe with
  | .exact i =>
    check ref "SVG readback: a mark moved past its bound disagrees"
      (i.fig.marks.all fun m => marksAgree m m && !marksAgree m (moved m))
  | _ => check ref "SVG readback: the probe imports" false

def svgNativeChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgNativeBoundaryChecks ref
  xmlRoundTripChecks ref
  svgImportChecks ref
  svgPosterNativeChecks ref
  svgExpansionChecks ref
  propertyTreatmentChecks ref
  transformOriginChecks ref
  fontShorthandChecks ref
  pathDataBudgetChecks ref
  svgEncodingChecks ref
  svgReadbackChecks ref

end Tests
