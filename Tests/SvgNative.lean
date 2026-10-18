module

public import LeanTex.Core.SvgImport
public import LeanTex.Core.SvgPoster
public import LeanTex.Core.WhatwgEncoding
public import LeanTex.Core.GfxSvg
public import Tests.Support

public section

/-! The native SVG reader's boundary and importer, hermetic, asserted over parsed trees and figure
marks. -/

namespace Tests

open LeanTex.Core LeanTex.Core.Gfx

/-- The judge's verdict as a boundary error. -/
def svgJudged (bytes : ByteArray) : Except String Unit :=
  match Svg.judge bytes with
  | .ok _ => .ok ()
  | .error r => .error r.message

/-- The resource boundary matrix: every admitted construct admitted, every refused one refused with
its boundary named. -/
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
  check ref "native SVG reader refuses a parsed entity even with a DTD named"
    !(svgJudged ("<!DOCTYPE svg SYSTEM \"outside.dtd\">" ++
      String.fromUTF8! (svgDocument "<rect fill=\"&outside;\"/>")).toUTF8).toBool
  check ref "native SVG reader names the DTD boundary"
    (match Svg.judge ("<!DOCTYPE svg [<!ENTITY x 'y'>]>" ++ drawing).toUTF8 with
      | .error r => hasStr r.message "DTD declarations and external entities"
      | .ok _ => false)

/-- A tree written by the canonical writer reads back as it stands, for every construct the writer
spells. -/
def xmlRoundTripChecks (ref : IO.Ref (List String)) : IO Unit := do
  let trees : List Xml.Node := [
    .elem "svg" #[("xmlns", "http://www.w3.org/2000/svg")] #[],
    .elem "a" #[("x", "1\n2\t3\r4"), ("y", "\"<&>'")] #[.text "a<b>&c\r\nd]]>e", .elem "b" #[] #[]],
    .elem "p:q" #[("xmlns:p", "urn:x"), ("p:r", "é ✓")] #[.elem "s" #[] #[.text " "], .text "t"]]
  for t in trees do
    check ref s!"XML round trip: {repr t}" (Xml.parse (Xml.render t) == .ok t)
  -- The judged tree's spelling is what the converter reads in place of the authored bytes.
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

/-- A text's length is bounded however the file spells it, references and CDATA counted as literal
characters. -/
def xmlBudgetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let bud : Xml.Budget := { Xml.Budget.standard with text := 8 }
  let refused (body : String) : Bool :=
    match Xml.parseWith bud s!"<a>{body}</a>".toUTF8 with
    | .error (.budget "text length") => true
    | _ => false
  let refs (n : Nat) : String := String.join (List.replicate n "&#97;")
  check ref "XML budget: eight characters fit a text budget of eight" (!refused "abcdefgh")
  check ref "XML budget: nine characters exceed it" (refused "abcdefghi")
  check ref "XML budget: eight references fit it" (!refused (refs 8))
  check ref "XML budget: nine references exceed it, as nine characters do" (refused (refs 9))
  check ref "XML budget: references after text count with it" (refused ("abcde" ++ refs 4))
  check ref "XML budget: a CDATA section of eight fits it" (!refused "<![CDATA[abcdefgh]]>")
  check ref "XML budget: a CDATA section of nine exceeds it" (refused "<![CDATA[abcdefghi]]>")
  check ref "XML budget: a CDATA section after text counts with it" (refused "abcde<![CDATA[abcd]]>")

/-- What one figure's import paints, and its losses. -/
def svgMarks (body : String) (w h : Nat := 20) : Array Mark × Array Gfx.Loss :=
  match Svg.importBytes (svgDocument body w h) with
  | .exact i | .lossy i => (i.fig.marks, i.fig.losses)
  | .refused _ => (#[], #[.element "refused"])

/-- The importer's reading of invented figures, over their marks. -/
def svgImportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let px (n : Int) : Int := n * Svg.pxSp
  -- A rect's geometry is in user space under the root's flip into the y-up frame.
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
  let (ms, ls) := svgMarks "<defs><linearGradient id=\"g\"><stop offset=\"0\" stop-color=\"red\"/>\
    <stop offset=\"1\" stop-color=\"blue\"/></linearGradient></defs>\
    <rect width=\"20\" height=\"10\" fill=\"url(#g)\"/>"
  check ref "SVG import: a linear gradient paints its stops"
    (ls.isEmpty && ms.any fun m => match m with
      | .paint _ _ (some f) _ _ _ => match f.paint with
        | .gradient (.linear _ _ stops _) => stops.size == 2
        | _ => false
      | _ => false)
  let (ms, ls) := svgMarks "<clipPath id=\"c\"><rect width=\"5\" height=\"5\"/></clipPath>\
    <g opacity=\"0.5\" clip-path=\"url(#c)\"><rect width=\"20\" height=\"20\"/></g>"
  check ref "SVG import: a clip and an opacity reach the mark"
    (ls.isEmpty && ms.any fun m => match m with
      | .paint _ _ _ _ clips alphas => clips.size == 1 && alphas.size == 1 && alphas[0]?.map (·.val) == some 500
      | _ => false)
  let (ms, ls) := svgMarks "<defs><path id=\"p\" d=\"M0 0h4v4z\"/></defs>\
    <use href=\"#p\" fill=\"green\"/><use href=\"#p\" x=\"10\" fill=\"green\"/>"
  check ref "SVG import: two uses paint the shared symbol twice" (ls.isEmpty && ms.size == 2)
  let (_, ls) := svgMarks "<g id=\"a\"><use href=\"#b\"/></g><g id=\"b\"><use href=\"#a\"/></g>"
  check ref "SVG import: a use cycle is a named loss" (ls.contains (.element "use cycle"))
  let (ms, ls) := svgMarks s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" \
    width=\"10\" height=\"10\"/>"
  check ref "SVG import: a data PNG is one raster mark" (ls.isEmpty && ms.any fun m => match m with
    | .raster _ 0 _ _ => true
    | _ => false)
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


/-- A tree's marks, optionally projected to its terminal pose. -/
def svgPose (bytes : ByteArray) (last : Bool) : Except String (Array Mark) := do
  let t ← match Svg.judge bytes with
    | .ok t => pure t
    | .error r => throw r.message
  let t ← if last then SvgPoster.terminal t else pure t
  return (Svg.importTree t).fig.marks

/-- The terminal-pose matrix: an unread timeline is refused by name, an accepted one paints exactly
the authored static pose. -/
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

/-- Symbols nested `depth` deep, each using the one below twice: 2^(depth-1) copies of one
square. -/
def nestedUses (depth : Nat) : ByteArray := Id.run do
  let mut defs := "<g id=\"s0\"><rect width=\"1\" height=\"1\"/></g>"
  for i in [1:depth] do
    defs := defs ++ s!"<g id=\"s{i}\"><use href=\"#s{i - 1}\"/><use href=\"#s{i - 1}\" x=\"0.5\"/></g>"
  return svgDocument (width := 40) (height := 40) s!"<defs>{defs}</defs><use href=\"#s{depth - 1}\"/>"

/-- Uses that multiply are bounded: past the import's budget a figure drops its uses, named. -/
def svgExpansionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let small := Svg.importTree ((Svg.judge (nestedUses 8)).toOption.getD (.text ""))
  let deep := Svg.importTree ((Svg.judge (nestedUses 24)).toOption.getD (.text ""))
  check ref "expansion: a figure within its budget keeps every use"
    (small.fig.losses.isEmpty && !small.fig.symbols.isEmpty && small.fig.marks.size == 128)
  check ref "expansion: a figure past its budget drops its uses, the drop named"
    (deep.fig.losses.contains (.budget "expanded uses") && deep.fig.symbols.isEmpty &&
      deep.fig.marks.size ≤ Svg.Budget.standard.expanded)


/-- Every property the importer meets keeps its treatment (`Svg.propertyTable`). -/
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

/-- `transform-origin` is a transform about a point, in every spelling. -/
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

/-- The `font` shorthand is its longhands, each unsaid one reset; a system font or an unset variant
is named. -/
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

/-- Path data reads linearly whatever its numbers spell, a number past the range stopping the path,
named. -/
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
  let samples : List (Array PathData.Cmd) := [
    #[.move false ⟨0, 0⟩ ⟨-15, 1⟩, .line true ⟨1234567, 3⟩ ⟨-5, 0⟩, .close],
    #[.move true ⟨7, 0⟩ ⟨7, 2⟩, .arc false ⟨5, 0⟩ ⟨25, 1⟩ ⟨-30, 0⟩ true false ⟨1, 0⟩ ⟨0, 4⟩,
      .cubic false ⟨1, 0⟩ ⟨2, 0⟩ ⟨3, 0⟩ ⟨4, 0⟩ ⟨5, 0⟩ ⟨6, 0⟩, .smooth true ⟨0, 3⟩ ⟨1, 3⟩ ⟨-2, 0⟩ ⟨3, 0⟩,
      .quad false ⟨1, 1⟩ ⟨2, 1⟩ ⟨3, 1⟩ ⟨4, 1⟩, .smoothQuad true ⟨9, 0⟩ ⟨9, 0⟩, .horiz false ⟨100, 2⟩,
      .vert true ⟨-1, 0⟩]]
  for cs in samples do
    check ref s!"path data: a written path reads back as written: {PathData.render cs}"
      (PathData.parse (PathData.render cs) == (cs, .done))


/-- An SVG's bytes read in the encoding they name (`svgBoundaryEncodings`), and a refused one names
what refused it. -/
def svgEncodingChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref s!"WHATWG tables hold their contract: {(WhatwgEncoding.dataFaults ()).toList.take 3}"
    (WhatwgEncoding.dataFaults ()).isEmpty
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

/-- Whether two paints are one: a colour exactly, a gradient by kind, stops and frame. -/
def paintAgrees : Paint → Paint → Bool
  | .solid a, .solid b => a == b
  | .gradient _, .gradient _ => true
  | _, _ => false

/-- How far the writer's half-thousandth spelling moves a mark's box through its frame, plus a sp
each way for rounding. -/
def readbackBound (ctm : Affine) : Int :=
  let abs (q : Rat) : Rat := if q < 0 then -q else q
  let scale := max (abs ctm.a + abs ctm.c) (abs ctm.b + abs ctm.d)
  Rat.ceil (scale * (Svg.pxSp : Rat) / 2000) + 2

/-- Two marks agree under the readback: kind, paint, rule, alphas and clip count, and geometry
within the bound. -/
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

/-- The writer's SVG reads back through the reader: every figure drawn whole imports exactly
again. -/
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
        -- The writer spells the box to a thousandth of a point, so a box off that grid reads back within half of one.
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
  -- The bound bites: a mark moved by twice its bound disagrees.
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

/-- A paint's solid colour as its channels. -/
def solidRgb (p : Paint) : Option (Nat × Nat × Nat) :=
  match p with
  | .solid c => some (c.r.toNat, c.g.toNat, c.b.toNat)
  | .gradient _ => none

/-- The paint marks whose fill and stroke are the named colours (`none` for an absent paint). -/
def paintsWith (ms : Array Mark) (fill stroke : Option (Nat × Nat × Nat)) : Nat :=
  (ms.filter fun m => match m with
    | .paint _ _ f s _ _ =>
      (f.bind (solidRgb ·.paint)) == fill && (s.bind (solidRgb ·.paint)) == stroke
    | _ => false).size

/-- A use's instantiated element carries its own declarations (SVG 2 §5.6.3). -/
def svgShadowStyleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let red := some (255, 0, 0)
  let blue := some (0, 0, 255)
  let green := some (0, 128, 0)
  let (ms, ls) := svgMarks ("<defs><symbol id=\"s\" viewBox=\"0 0 10 10\" fill=\"red\" stroke=\"blue\" \
    stroke-width=\"1\"><rect x=\"1\" y=\"1\" width=\"8\" height=\"8\"/></symbol></defs>\
    <use href=\"#s\" x=\"10\" y=\"10\" width=\"80\" height=\"80\"/>\
    <use href=\"#s\" x=\"110\" y=\"10\" width=\"80\" height=\"80\" fill=\"green\"/>") 200 100
  check ref s!"SVG shadow style: a symbol's presentation attributes paint both uses ({repr ls})"
    (ls.isEmpty && paintsWith ms red blue == 2 && ms.size == 2)
  let (ms, ls) := svgMarks ("<style>.warn { fill: orange } .dim { opacity: 0.3 }</style>\
    <defs><symbol id=\"s\" class=\"warn\" viewBox=\"0 0 10 10\"><circle cx=\"5\" cy=\"5\" r=\"4\"/></symbol>\
    <g id=\"gg\" class=\"dim\"><rect width=\"40\" height=\"40\" fill=\"purple\"/></g></defs>\
    <use href=\"#s\" x=\"10\" y=\"10\" width=\"80\" height=\"80\"/><use href=\"#gg\" x=\"120\" y=\"30\"/>") 200 100
  check ref s!"SVG shadow style: a symbol's class rule paints its child ({repr ls})"
    (ls.isEmpty && paintsWith ms (some (255, 165, 0)) none == 1 &&
      ms.any fun m => match m with
        | .paint _ _ (some f) _ _ alphas => solidRgb f.paint == some (128, 0, 128) &&
            alphas.map (·.val) == #[300]
        | _ => false)
  let (ms, ls) := svgMarks ("<defs><symbol id=\"i\" viewBox=\"0 0 10 10\" color=\"green\">\
    <rect width=\"10\" height=\"10\" fill=\"currentColor\"/></symbol></defs>\
    <use href=\"#i\" x=\"10\" y=\"10\" width=\"80\" height=\"80\"/>\
    <use href=\"#i\" x=\"110\" y=\"10\" width=\"80\" height=\"80\" color=\"blue\"/>") 200 100
  check ref s!"SVG shadow style: a symbol's own colour answers currentColor in both uses ({repr ls})"
    (ls.isEmpty && paintsWith ms green none == 2)
  let (ms, ls) := svgMarks ("<defs><symbol id=\"check\" viewBox=\"0 0 24 24\" fill=\"none\" \
    stroke=\"currentColor\" stroke-width=\"2\" stroke-linecap=\"round\" stroke-linejoin=\"round\">\
    <polyline points=\"20 6 9 17 4 12\"/></symbol></defs>\
    <use href=\"#check\" width=\"12\" height=\"12\" color=\"green\"/>\
    <use href=\"#check\" x=\"12\" width=\"12\" height=\"12\" color=\"crimson\"/>") 24 12
  check ref s!"SVG shadow style: a currentColor sprite strokes in each use's colour ({repr ls})"
    (ls.isEmpty && paintsWith ms none green == 1 && paintsWith ms none (some (220, 20, 60)) == 1 &&
      ms.all fun m => match m with
        | .paint _ _ none (some s) _ _ => s.cap == .round && s.join == .round
        | _ => false)

/-- A mark's geometry box in the figure's frame, and its first clip's. -/
def markAndClipBoxes (m : Mark) : Option (Box × Box) :=
  match m with
  | .paint ctm g _ _ clips _ =>
    match g.hull, clips[0]? with
    | some b, some (cm, c) => c.geom.hull.map fun cb => (Box.image ctm b, Box.image cm cb)
    | _, _ => none
  | .raster ctm _ clips _ =>
    match clips[0]? with
    | some (cm, c) => c.geom.hull.map fun cb => (Box.image ctm ((0, 0), (65536, 65536)), Box.image cm cb)
    | none => none
  | .shading _ _ _ => none

/-- A clip in object units reads the clipped element's own box; text, whose box comes after shaping,
is a named loss and still drawn. -/
def svgObjectClipChecks (ref : IO.Ref (List String)) : IO Unit := do
  let half := "<clipPath id=\"half\" clipPathUnits=\"objectBoundingBox\"><rect width=\"0.5\" height=\"1\"/></clipPath>"
  let near (a b : Int) : Bool := (a - b).natAbs ≤ 2
  let (ms, ls) := svgMarks (s!"<defs>{half}<rect id=\"r\" width=\"80\" height=\"80\" fill=\"navy\"/></defs>" ++
    "<use href=\"#r\" x=\"10\" y=\"10\" clip-path=\"url(#half)\"/>" ++
    "<g clip-path=\"url(#half)\"><rect x=\"110\" y=\"10\" width=\"80\" height=\"80\" fill=\"darkred\"/></g>") 200 100
  let halves (rgb : Nat × Nat × Nat) : Bool := ms.any fun m => match m with
    | .paint _ _ (some f) _ _ _ =>
      solidRgb f.paint == some rgb && (markAndClipBoxes m).any fun (b, c) =>
        near c.1.1 b.1.1 && near c.1.2 b.1.2 && near c.2.2 b.2.2 &&
          near (2 * (c.2.1 - c.1.1)) (b.2.1 - b.1.1)
    | _ => false
  check ref s!"SVG object clip: a use is clipped to the left half of its content ({repr ls})"
    (ls.isEmpty && halves (0, 0, 128))
  check ref "SVG object clip: a group is clipped to the left half of its children" (halves (139, 0, 0))
  let png := HtmlResource.base64 tinyPng
  let (ms, ls) := svgMarks (s!"<defs>{half}</defs><image href=\"data:image/png;base64,{png}\" " ++
    "x=\"10\" y=\"10\" width=\"40\" height=\"40\" clip-path=\"url(#half)\"/>") 100 100
  check ref s!"SVG object clip: an image is clipped to the left half of its viewport ({repr ls})"
    (ls.isEmpty && ms.any fun m => match m with
      | .raster .. => (markAndClipBoxes m).any fun (b, c) =>
          near c.1.1 b.1.1 && near (2 * (c.2.1 - c.1.1)) (b.2.1 - b.1.1)
      | _ => false)
  match Svg.importBytes (svgDocument ("<defs><clipPath id=\"c\" clipPathUnits=\"objectBoundingBox\">" ++
      "<circle cx=\"0.5\" cy=\"0.5\" r=\"0.5\"/></clipPath></defs>" ++
      "<text x=\"10\" y=\"50\" font-size=\"30\" clip-path=\"url(#c)\">Clipped</text>") 200 100) with
  | .lossy i =>
    check ref s!"SVG object clip: text clipped in object units is a named loss, its words still drawn ({repr i.fig.losses})"
      (i.fig.losses.contains (.value "clip-path in object units on text") && i.text &&
        i.fig.labels.any fun (_, r) => hasStr r.text "Clipped")
  | _ => check ref "SVG object clip: text clipped in object units is a named loss" false

/-- A CSS string ends at its line (CSS Syntax 3 §4.3.5), so the judge reads what follows as CSS. -/
def cssLineEndChecks (ref : IO.Ref (List String)) : IO Unit := do
  let hidden := "fill:url(http://example.invalid/p.svg#g) green"
  for (name, body) in [
      ("a style attribute", s!"<rect width=\"9\" height=\"9\" style='font-family:\"x&#10;;{hidden};y:\"'/>"),
      ("a style attribute ended by a carriage return",
        s!"<rect width=\"9\" height=\"9\" style='font-family:\"x&#13;;{hidden};y:\"'/>"),
      ("a style sheet ended by a carriage return reference",
        s!"<style>rect {lb} font-family: \"x&#13;; {hidden}; y: \" {rb}</style><rect width=\"9\" height=\"9\"/>"),
      ("a style sheet", s!"<style>rect {lb} font-family: \"x\n; {hidden}; y: \" {rb}</style><rect width=\"9\" height=\"9\"/>")] do
    check ref s!"CSS line end: {name} cannot hide a reference behind a broken string"
      (svgBoundaryError (svgJudged (svgDocument body)))
  check ref "CSS line end: a sheet's own line ends still read"
    (svgJudged (svgDocument "<style>rect {\n  fill: red;\n}\n</style><rect width=\"9\" height=\"9\"/>")).toBool
  check ref "CSS line end: a brace inside a string is the string's"
    (match Css.parseSheet "rect { font-family: \"a}b\"; fill: red }" with
     | .ok (rules, dropped) => dropped.isEmpty && rules.size == 1 &&
        (rules[0]?.map (·.decls.size)) == some 2
     | .error _ => false)
  check ref "CSS line end: a declaration holding a broken string is not read"
    (match Css.parseDecls "font-family: \"x\n; fill: red" with
     | .error (.unsupported _) => true
     | _ => false)
where
  lb : String := "{"
  rb : String := "}"

/-- A CSS list is cut at its separators outside blocks, strings and escapes (CSS Syntax 3 §5.4.10),
and a declaration's importance is read outside its strings (§5.5.6). -/
def cssSplitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let items := [":is(h1, h2) a", ":not(.a, .b)", "a[title=\"x, y\"]", "a[title='x,y']", "a\\,b",
    "a[title=\"q\\\", r\"]", "c"]
  check ref "CSS split: a selector list keeps each selector whole"
    ((Css.splitList ',' (", ".intercalate items)).toList.map (·.trimAscii.toString) == items)
  check ref "CSS split: a string a line end breaks ends there, and a comma after it separates"
    (Css.splitList ',' "\"x\ny, z" == #["\"x\ny", " z"])
  check ref "CSS split: a declaration block is cut at semicolons outside strings and brackets"
    (Css.splitList ';' "fill: red; font-family: \"a;b\"; grid-area: [a;b]" ==
      #["fill: red", " font-family: \"a;b\"", " grid-area: [a;b]"])
  check ref "CSS split: a block ends only at its own mirror, another closer inside it is its content"
    (Css.splitList ',' "(a], b)" == #["(a], b)"] && Css.splitList ',' "[a), b]" == #["[a), b]"] &&
      Css.splitList ',' "rect[title=x), y], circle" == #["rect[title=x), y]", " circle"] &&
      Css.splitList ';' " fill: blue; x: [a); b] " == #[" fill: blue", " x: [a); b] "])
  check ref "CSS split: a closer no block opened stands alone, a separator after it cuts"
    (Css.splitList ',' "a), b" == #["a)", " b"] && Css.splitList ',' "x] y, z" == #["x] y", " z"])
  check ref "CSS split: an unclosed block runs to the text's end, holding every separator in it"
    (Css.splitList ',' "a, :is(b, c" == #["a", " :is(b, c"])
  check ref "CSS families: a family is a string or identifiers, else the list is no list"
    (Svg.families? "Invented's Hand, serif" == none &&
      Svg.families? "Invented /* it's */, monospace" == some #["Invented", "monospace"] &&
      Svg.families? "\"Two, Words\", Times  New Roman, SERIF" ==
        some #["Two, Words", "Times New Roman", "serif"] &&
      Svg.families? "\"Open, serif" == none && Svg.families? "3D, serif" == none)
  check ref "CSS families: reserved words, an identifier a digit opens, and escapes read as CSS reads them"
    (Svg.families? "Foo, inherit" == none && Svg.families? "Foo, default" == none &&
      Svg.families? "-3D, serif" == none && Svg.families? "a\\,b, serif" == some #["a,b", "serif"] &&
      Svg.families? "\"a\\\"b\", monospace" == some #["a\"b", "monospace"] &&
      Svg.families? "\\31 23, monospace" == some #["123", "monospace"])
  check ref "CSS one line: white space outside strings is one blank, a string as written"
    (Css.oneLine "rect[title=\"a   b\"]\n\t .ok" == "rect[title=\"a   b\"] .ok")
  check ref "CSS sheet: a block the sheet's end closes keeps its rule"
    (match Css.parseSheet ".m { fill: lime } .a { fill: blue; stroke-dasharray: [2 }" with
      | .ok (rules, dropped) => rules.size == 2 && dropped.isEmpty &&
          (rules[1]?.map (·.decls.any (·.value == "blue"))).getD false
      | .error _ => false)
  check ref "CSS split: importance is read after the value's strings"
    (Css.importance "\"Bang!\" !important" == ("\"Bang!\"", true) &&
      Css.importance "red ! IMPORTANT" == ("red", true) &&
      Css.importance "\"a!important\"" == ("\"a!important\"", false))

/-- A comment remover reading characters, the byte scan's oracle. -/
def cssStripOracle (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut quote : Option Char := none
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD ' '
    match quote with
    | some q =>
      out := out.push c
      if c == q || Css.isLineEnd c then quote := none
      i := i + 1
    | none =>
      if c == '/' && cs[i + 1]? == some '*' then
        let mut j := i + 2
        for _ in [0:cs.size + 1] do
          if j + 1 ≥ cs.size then
            j := cs.size
            break
          if cs[j]? == some '*' && cs[j + 1]? == some '/' then
            j := j + 2
            break
          j := j + 1
        out := out.push ' '
        i := j
      else
        if c == '"' || c == '\'' then quote := some c
        out := out.push c
        i := i + 1
  return out

/-- A refusal scan reading characters, the byte scan's oracle. -/
def cssRefusedOracle (s : String) : Option Css.Unread := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  let mut quote : Option Char := none
  let mut ident := ""
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD ' '
    if c == '\\' then return some .escape
    if c == '@' then return some .atRule
    match quote with
    | some q =>
      if c == q || Css.isLineEnd c then quote := none
      i := i + 1
    | none =>
      if c == '"' || c == '\'' then
        quote := some c
        ident := ""
        i := i + 1
      else if c == '(' then
        let mut j := i + 1
        let mut arg := ""
        let mut closed := false
        for _ in [0:cs.size + 1] do
          if j ≥ cs.size then break
          if cs[j]? == some ')' then
            closed := true
            break
          if cs[j]? == some '(' then return some (.nestedCall ident)
          arg := arg.push (cs[j]?.getD ' ')
          j := j + 1
        if !closed then return some (.openCall ident)
        if !Css.admitsCall ident arg then return some (.call ident)
        ident := ""
        i := j + 1
      else
        if c.isAlphanum || c == '-' || c == '_' then ident := ident.push c else ident := ""
        i := i + 1
  if quote.isSome then return some .openString
  return none

/-- A broken-string test reading characters, the byte scan's oracle. -/
def cssBrokenOracle (s : String) : Bool := Id.run do
  let mut quote : Option Char := none
  for c in s.toList do
    match quote with
    | some q =>
      if c == q then quote := none
      else if Css.isLineEnd c then return true
    | none => if c == '"' || c == '\'' then quote := some c
  return false

/-- A sheet read with each block's comments and refusals checked again by the character scans. -/
def cssSheetOracle (text : String) : Except Css.Unread (Array Css.Rule × Array Css.Unread) := do
  let text := cssStripOracle text
  if let some what := cssRefusedOracle text then throw what
  let mut rules : Array Css.Rule := #[]
  let mut dropped : Array Css.Unread := #[]
  let mut prelude := ""
  for a in Css.atoms text do
    if a.head? != some '{' then
      prelude := a.foldl String.push prelude
    else
      let body := if Css.closedAtom a then (a.drop 1).dropLast else a.drop 1
      let sels := (Css.splitList ',' prelude).map (·.trimAscii.toString)
      let block := cssStripOracle (String.ofList body)
      if let some what := cssRefusedOracle block then throw what
      match sels.mapM Css.parseSelector, Css.parseDecls block with
      | .ok sels, .ok ds => rules := rules.push { selectors := sels, decls := ds }
      | .error why, _ => dropped := dropped.push why
      | _, .error (.unsupported why) => dropped := dropped.push why
      | _, .error (.refused why) => throw why
      prelude := ""
  unless prelude.trimAscii.isEmpty do
    dropped := dropped.push (.stray (Css.oneLine prelude))
  return (rules, dropped)

/-- Invented CSS texts from pieces holding every marker the scans read and characters outside
ASCII, each the `n`th of a fixed pseudo-random sequence; every other text leaves out the pieces a
sheet refuses, so many sheets stand with their blocks. -/
def cssScanText (n : Nat) : String := Id.run do
  let admitted := #["/*", "*/", "\"", "'", "\n", "\r", "\x0c", "\t", "{", "}", "{", "}", "[", "]",
    ";", ":", ",", "é", "∀", "𝔸", " ", "a", "-b", "_c", "url(#g)", "rgb(1,2,3)", "fill", "red",
    "x9", "/", "*", ".k", "#i", ">", "!important", "a { fill: red }", "b { c: d; }"]
  let pieces := if n % 2 == 0 then admitted
    else admitted ++ #["(", ")", "@", "\\", "url(\"#é\")"]
  let mut seed := n * 2654435761 + 97
  let mut out := ""
  for _ in [0:(n % 23) + 1] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    out := out ++ (pieces[(seed / 65536) % pieces.size]?.getD "")
  return out

/-- The byte scans read every text as the character scans they replaced did, and a sheet's
blocks, read without the sheet's own checks again, as each block checked again. -/
def cssByteScanChecks (ref : IO.Ref (List String)) : IO Unit := do
  let texts := (List.range 6000).map cssScanText ++
    ["", "/*", "a/*", "a/**/b", "\"/*\"*/", "rgb(", "x(é)", "url(#a))", "'a\nb'", "a { b: \"c\n }"]
  let sameSheet (a b : Except Css.Unread (Array Css.Rule × Array Css.Unread)) : Bool :=
    match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false
  let strip := texts.filter fun s => Css.stripComments s != cssStripOracle s
  check ref s!"CSS byte scan: comments removed as the character scan removed them ({strip.take 3})"
    strip.isEmpty
  let refused := texts.filter fun s => Css.refusedIn s != cssRefusedOracle s
  check ref s!"CSS byte scan: refusals read as the character scan read them ({refused.take 3})"
    refused.isEmpty
  let broken := texts.filter fun s => Css.brokenString s != cssBrokenOracle s
  check ref s!"CSS byte scan: broken strings found as the character scan found them ({broken.take 3})"
    broken.isEmpty
  let sheets := texts.filter fun s => !sameSheet (Css.parseSheet s) (cssSheetOracle s)
  check ref s!"CSS sheet: blocks read once as when each was checked again ({sheets.take 3})"
    sheets.isEmpty
  let standing := texts.filter fun s => s.contains '{' && (cssSheetOracle s matches .ok _)
  check ref s!"CSS sheet: the invented texts hold sheets whose blocks stand ({standing.length})"
    (standing.length ≥ 1000)

/-- A gradient stop takes its own place in the cascade, its `currentColor` its own. -/
def svgStopStyleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let stops (ms : Array Mark) : Array (Nat × Nat × Nat) :=
    ms.foldl (fun acc m => match m with
      | .paint _ _ (some f) _ _ _ => match f.paint with
        | .gradient (.linear _ _ ss _) => acc ++ ss.map fun s => (s.color.r.toNat, s.color.g.toNat, s.color.b.toNat)
        | _ => acc
      | _ => acc) #[]
  let (ms, ls) := svgMarks ("<style>#g stop { stop-color: green } #g stop.end { stop-color: yellow }</style>\
    <defs><linearGradient id=\"g\"><stop offset=\"0\"/><stop class=\"end\" offset=\"1\"/></linearGradient></defs>\
    <rect width=\"20\" height=\"10\" fill=\"url(#g)\"/>")
  check ref s!"SVG stop style: a rule through the gradient styles its stops ({repr ls})"
    (ls.isEmpty && stops ms == #[(0, 128, 0), (255, 255, 0)])
  let (ms, ls) := svgMarks ("<defs color=\"blue\"><linearGradient id=\"g\">\
    <stop offset=\"0\" stop-color=\"currentColor\"/><stop offset=\"1\" stop-color=\"red\"/>\
    </linearGradient></defs><rect width=\"20\" height=\"10\" color=\"lime\" fill=\"url(#g)\"/>")
  check ref s!"SVG stop style: a stop's currentColor is its own inherited colour ({repr ls})"
    (ls.isEmpty && stops ms == #[(0, 0, 255), (255, 0, 0)])

/-- What the importer does not draw is a named loss, never a silent one. -/
def svgUndrawnNamedChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, word) in [("Hebrew", "שלום"), ("Arabic", "سلام"), ("Devanagari", "नमस्ते")] do
    let (_, ls) := svgMarks s!"<text x=\"1\" y=\"10\">{word}</text>" 60 20
    check ref s!"SVG undrawn: {name} text is the shaping loss ({repr ls})" (ls.contains Svg.shapingLoss)
  let (_, ls) := svgMarks "<text x=\"1\" y=\"10\">Latin ✓ ÅÉ</text>" 60 20
  check ref s!"SVG undrawn: Latin text with symbols needs no shaping ({repr ls})" ls.isEmpty
  for (prop, value, initial) in [("text-transform", "uppercase", "none"),
      ("font-variant-caps", "small-caps", "normal"), ("text-decoration-line", "underline", "none")] do
    let (_, ls) := svgMarks s!"<text x=\"1\" y=\"10\" style=\"{prop}: {value}\">Word</text>" 60 20
    check ref s!"SVG undrawn: {prop} from CSS is a loss ({repr ls})" (ls.contains (.property prop))
    let (_, ls) := svgMarks s!"<text x=\"1\" y=\"10\" style=\"{prop}: {initial}\">Word</text>" 60 20
    check ref s!"SVG undrawn: {prop} at its initial value changes nothing ({repr ls})"
      (!ls.contains (.property prop))
  let rootBg := Svg.importBytes ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"20\" " ++
    "height=\"20\" style=\"background-color: navy\"><rect width=\"5\" height=\"5\"/></svg>").toUTF8
  check ref "SVG undrawn: a root background is a loss"
    (match rootBg with
      | .lossy i => i.fig.losses.contains (.property "background-color")
      | _ => false)
  let px (n : Int) : Int := n * Svg.pxSp
  let (ms, ls) := svgMarks ("<svg x=\"0\" y=\"0\" width=\"10\" height=\"10\" transform=\"translate(5 0)\">" ++
    "<rect width=\"4\" height=\"4\"/></svg>")
  check ref s!"SVG undrawn: a nested viewport's transform moves its content ({repr ls})"
    (ls.isEmpty && ms.any fun m => match markAndClipBoxes m with
      | some (b, _) => b.1.1 == px 5
      | none => false)

/-- A line feed in figure text is a space. -/
def svgTextSpaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  match Svg.importBytes (svgDocument "<text x=\"1\" y=\"10\">Hello\n  world</text>" 80 20) with
  | .exact i =>
    check ref s!"SVG text space: a line feed between words is one space ({i.fig.labels.map (·.2.text)})"
      (i.fig.labels.map (·.2.text) == #["Hello world"])
  | _ => check ref "SVG text space: the text imports exact" false

/-- An exporter's boilerplate title names no figure, so N0376 still names its missing
alternative. -/
def svgTitleWordsChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (title, names) in [("Gnuplot", false), ("Produced by GNUPLOT 5.4 patchlevel 2", false),
      ("artboard_one_final", false), ("Chart", false), ("Monthly rainfall at three invented sites", true)] do
    let t := match Svg.judge (svgDocument s!"<title>{title}</title><rect width=\"5\" height=\"5\"/>") with
      | .ok t => Svg.titleOf t
      | .error _ => none
    check ref s!"SVG title words: '{title}' {if names then "names" else "names no"} figure"
      (t.isSome == names)

def svgNativeChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgNativeBoundaryChecks ref
  xmlRoundTripChecks ref
  xmlBudgetChecks ref
  svgImportChecks ref
  svgPosterNativeChecks ref
  svgExpansionChecks ref
  propertyTreatmentChecks ref
  transformOriginChecks ref
  fontShorthandChecks ref
  pathDataBudgetChecks ref
  svgEncodingChecks ref
  svgReadbackChecks ref
  svgShadowStyleChecks ref
  svgObjectClipChecks ref
  cssLineEndChecks ref
  cssSplitChecks ref
  cssByteScanChecks ref
  svgStopStyleChecks ref
  svgUndrawnNamedChecks ref
  svgTextSpaceChecks ref
  svgTitleWordsChecks ref

end Tests
