module

public import LeanTex.Cli.Driver
public import LeanTex.Cli.Publication
public import LeanTex.Core.FigureSvg
public import LeanTex.Core.FigureOutline
public import LeanTex.Core.FigureStore
public import LeanTex.Core.FigureAlt
public import Tests.SvgRoute
public import Tests.Support
public import Tests.CorpusStore

public section

/-! The native SVG route on the HTML page: a still figure the engine draws
whole and that sets text ships as the page's own SVG with live text in the
document's role families; one that moves, draws with a loss, embeds a
raster or sets no text keeps its authored bytes in an `<img>`; a moving
figure's still face is the engine's drawing of its pose with its text as
the faces' outlines. Asserted over the typed tree the page serializes and
the bytes it embeds. -/

namespace Tests

open LeanTex.Core LeanTex.Cli

/-- A face set with the three roles apart: the serif body, the sans, the
mono — so a figure's family list visibly picks its role. -/
def threeRoleFonts : IO (Option Font.FontSet) := do
  let load (name : String) : IO (Option Font.Font) := do
    let bytes ← IO.FS.readBinFile ("testdata/corpus/fonts/" ++ name)
    return (Font.parse bytes).toOption
  let some body ← load "SourceSerifPro-Regular.otf" | return none
  let some sans ← load "FiraSans-Regular.otf" | return none
  let some mono ← load "SourceCodePro-Regular.otf" | return none
  return some { fonts := #[body, sans, mono]
                index := #[((0, 400, false), 0), ((0, 700, false), 0), ((1, 400, false), 1),
                  ((1, 700, false), 1), ((2, 400, false), 2), ((2, 700, false), 2)] }

/-- One source's store, as the driver builds it: fetched natively with no
converter, fulfilled, shaped, and — when it moves — given its still face. -/
def svgStore (fs : Font.FontSet) (src : String) (bytes : ByteArray)
    (page : PdfRead.PageSelection := .first) (convert : Option Driver.Converter := none) :
    IO Image.Store := do
  let f ← Driver.svgFetch src bytes page "en" convert
  let req : Image.Request := { src, page }
  let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some bytes) none)
  let imgs := FigureStore.attach { entries := #[en] } #[some f.drawn]
  return (FigureStore.settle fs imgs).1

/-- The page's body for one image of `src`, under the store. -/
def svgPage (fs : Font.FontSet) (imgs : Image.Store) (src : String) : Array Html.Node :=
  let doc := (elabStr s!"\\includegraphics[width=200pt,alt=\{An invented chart}]\{{src}}").1
  let (_, body, _) := HtmlDoc.emitTree { imgs, fonts := some fs } doc
  body

/-- Every `<text>` under a tree, with its attributes and its characters. -/
def svgTexts (body : Array Html.Node) : Array (Array (String × String) × String) :=
  (elemNodesList (· == "text") #[] body.toList).filterMap fun n => match n with
    | .elem _ attrs kids => some (attrs, nodeTextList "" kids.toList)
    | _ => none

/-- **A still figure that sets text is the page's own SVG**: no `<img>`, a
named `<svg>` whose every run is a `<text>` in its role's family, at the
resolved face's weight, each glyph at the pen x the shaping gave — the
same scalars the PDF sets. Its tree closes as a page, and the judge finds
no unnamed SVG. -/
def svgInlineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "inline figure: the three shipped role faces parse" false
  let imgs ← svgStore fs "chart.svg" svgTextFixture
  let body := svgPage fs imgs "chart.svg"
  let svgs := elemAttrsList (· == "svg") #[] body.toList
  let imgsShipped := elemAttrsList (· == "img") #[] body.toList
  check ref "inline figure: the figure ships as inline SVG, not an image"
    (svgs.size == 1 && imgsShipped.isEmpty)
  check ref "inline figure: the SVG is named by the image's alternative"
    (svgs.all fun (_, a) => a.contains ("role", "img") && a.contains ("aria-label", "An invented chart"))
  check ref "inline figure: the SVG reserves the figure's box in CSS pixels"
    (match (imgs.entries[0]?).bind (·.vector) with
      | some v => svgs.all fun (_, a) =>
          HtmlDoc.attrOf? a "width" == some (toString (HtmlDoc.cssPxOfSp (v.box.2.1 - v.box.1.1)))
      | none => false)
  let texts := svgTexts body
  let shaped := (imgs.shaped[0]?).join
  let runs : Array Gfx.Shaped := match shaped with
    | some fig => fig.labels.map (·.2)
    | none => #[]
  check ref "inline figure: every run is one text element setting the shaped scalars"
    (texts.size == runs.size && runs.size == 2 &&
      runs.all fun r => texts.any fun (_, t) => t == FigureSvg.runText r)
  check ref "inline figure: each run names its role's family and its face's weight"
    (texts.any (fun (a, t) => t == "Invented label" &&
        hasStr ((HtmlDoc.attrOf? a "style").getD "") "var(--font-sans)") &&
      texts.any (fun (a, t) => t == "axis" &&
        hasStr ((HtmlDoc.attrOf? a "style").getD "") "var(--font-mono)") &&
      texts.all fun (a, _) => hasStr ((HtmlDoc.attrOf? a "style").getD "") "font-weight: 400")
  check ref "inline figure: each glyph sits at the pen x the shaping gave"
    (runs.all fun r => texts.any fun (a, t) =>
      t == FigureSvg.runText r && HtmlDoc.attrOf? a "x" == some (FigureSvg.penList r))
  check ref "inline figure: the page's accessibility judge finds no unnamed SVG"
    (let facts := HtmlDoc.a11yFacts true false body
     facts.svgs ≥ 1 && facts.svgsUnnamed == 0)
  let doc := (elabStr "\\includegraphics[width=200pt,alt={An invented chart}]{chart.svg}").1
  let (closed, _) ← Publication.prepareHtml "figure.tex" { imgs, fonts := some fs } doc
  check ref "inline figure: the page closes over its resources" closed.toBool

/-- **What keeps its authored bytes**: a figure that sets no text, one the
engine draws with a loss, and one embedding a raster each ship as an
`<img>` of the authored source, never as inline SVG. -/
def svgImgChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "img figure: the role faces parse" false
  let raster := svgDocument
    (s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" width=\"10\" height=\"10\"/>" ++
     "<text x=\"2\" y=\"18\">Invented</text>")
  for (name, bytes) in [
      ("text-free", svgDocument svgRedSquare),
      ("lossy", svgFilterFixture),
      ("raster", raster)] do
    let imgs ← svgStore fs "figure.svg" bytes
    let body := svgPage fs imgs "figure.svg"
    let imgsShipped := elemAttrsList (· == "img") #[] body.toList
    check ref s!"img figure {name}: ships as an image of its authored bytes"
      ((elemAttrsList (· == "svg") #[] body.toList).isEmpty && imgsShipped.size == 1 &&
        (HtmlDoc.imageResources imgs).any (·.bytes == bytes))

/-- An invented moving figure with a clipped ground and a line of sans
text holding a space. -/
def svgMovingTextFixture : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"120\" height=\"30\">" ++
   "<defs><clipPath id=\"half\"><rect width=\"60\" height=\"30\"/></clipPath></defs>" ++
   "<g clip-path=\"url(#half)\"><rect width=\"120\" height=\"30\" fill=\"#eef\"/></g>" ++
   "<rect width=\"20\" height=\"20\" fill=\"red\" opacity=\"0\">" ++
   "<animate attributeName=\"opacity\" values=\"0;1\" dur=\"2s\"/></rect>" ++
   "<text x=\"24\" y=\"20\" font-family=\"sans-serif\">Moving text</text></svg>").toUTF8

/-- **A moving figure keeps its animation, and its still face is the
engine's drawing**: the `<img>` carries the authored bytes inside the print
and reduced-motion switch, whose source is a static SVG the native judge
admits, its text the faces' outlines — one definition per distinct glyph,
one use per glyph set, and no `<text>`. -/
def svgPosterFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "moving figure: the role faces parse" false
  let imgs ← svgStore fs "moving.svg" svgMovingTextFixture
  let body := svgPage fs imgs "moving.svg"
  check ref "moving figure: the image ships inside the still-face switch"
    ((elemAttrsList (· == "picture") #[] body.toList).size == 1 &&
      (elemAttrsList (· == "img") #[] body.toList).size == 1 &&
      (elemAttrsList (· == "source") #[] body.toList).any fun (_, a) =>
        a.contains ("media", "print, (prefers-reduced-motion: reduce)"))
  check ref "moving figure: the browser receives the authored animation"
    ((HtmlDoc.imageResources imgs).any (·.bytes == svgMovingTextFixture))
  -- Drawn at the end of its animation, the figure still moves: the pose
  -- holds no animation, the authored tree does.
  let atEnd ← svgStore fs "moving.svg" svgMovingTextFixture (page := .last)
  check ref "moving figure: drawn at its last pose, it still has its still face"
    ((atEnd.entries[0]?).any fun en => en.moving && en.posterSvg.isSome)
  match imgs.entries[0]?.bind (·.posterSvg), (imgs.shaped[0]?).join with
  | some poster, some fig =>
    let inked (f g : Nat) := !(FigureOutline.glyphOutline fs f g).isEmpty
    let glyphs := fig.labels.foldl (fun n (_, r) => n + r.glyphs.size) 0
    let stamps := fig.labels.foldl (fun n (_, r) =>
      n + (r.glyphs.filter fun (f, g, _, _) => inked f g).size) 0
    let distinct := ((FigureOutline.glyphTable fig).filter fun (f, g) => inked f g).size
    let text := String.fromUTF8! poster
    check ref "moving figure: the still face is a static SVG the native judge admits"
      (match Svg.judge poster with
        | .ok t => (SvgPoster.tracksOne #[] t).isEmpty
        | .error _ => false)
    check ref "moving figure: the still face sets its text as outlines, one use per inked glyph"
      (!hasStr text "<text" && glyphs == 11 && stamps == 10 &&
        (text.splitOn "<use ").length - 1 == stamps &&
        (text.splitOn "<path id=\"f0~o").length - 1 == distinct)
    check ref "moving figure: the still face is the pose the PDF draws, in its box"
      ((FigureOutline.outlined fs fig).box == fig.box)
  | _, _ => check ref "moving figure: the store carries a still face and a shaped figure" false

/-- **A run that would paint in a way the engine-set text does not is a
loss**: a gradient fill and an outline stroke on text are named, so the
figure is not drawn as though they were there. -/
def svgTextPaintLossChecks (ref : IO.Ref (List String)) : IO Unit := do
  let gradient := svgDocument
    ("<defs><linearGradient id=\"g\"><stop stop-color=\"red\"/><stop offset=\"1\" stop-color=\"blue\"/>" ++
     "</linearGradient></defs><text x=\"2\" y=\"15\" fill=\"url(#g)\">Shaded</text>")
  let stroked := svgDocument "<text x=\"2\" y=\"15\" stroke=\"blue\">Outlined</text>"
  for (name, bytes, loss) in [
      ("gradient", gradient, Gfx.Loss.value "gradient on text"),
      ("stroke", stroked, Gfx.Loss.property "stroke on text")] do
    match SvgPoster.pose bytes false with
    | .ok t =>
      check ref s!"text paint {name}: the import names the loss"
        ((Svg.importTree t).fig.losses.contains loss)
    | .error e => check ref s!"text paint {name}: the figure reads ({e})" false

/-- **A figure that names itself is the alternative the document did not
declare** — the driver's gate, two builds apart. Two figures differing only
by their `<title>`: with it, the shipped document's image is described by
the title (one IR value, so both artifacts' name), the page names the
figure by it, and N0376 stays silent; without it, N0376 names the image and
the alternative stays undeclared. A declared alternative wins over a
title. -/
def svgTitleAltChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "figure title: the role faces parse" false
  let figure (title : String) : ByteArray :=
    (s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"60\" height=\"20\">{title}" ++
     "<text x=\"2\" y=\"15\">Invented</text></svg>").toUTF8
  let built (bytes : ByteArray) (body : String) : IO (Ir.Doc × Array Diag × Array Html.Node) := do
    let (doc, diags) := elabStr body
    let f ← Driver.svgFetch "named.svg" bytes .first "en" none
    let titles := (f.title.map fun t => #[("named.svg", t)]).getD #[]
    let doc := FigureAlt.titled titles doc
    let diags := FigureAlt.unanswered titles doc diags
    let imgs ← svgStore fs "named.svg" bytes
    let (_, page, _) := HtmlDoc.emitTree { imgs, fonts := some fs } doc
    return (doc, diags, page)
  let alts (doc : Ir.Doc) : Array Ir.Alt :=
    Ir.foldBlocks (fun a _ => a) (fun a x => match x with
      | .image _ _ alt => a.push alt
      | _ => a) #[] doc.body
  let named (page : Array Html.Node) (label : String) : Bool :=
    (elemAttrsList (· == "svg") #[] page.toList).any fun (_, a) => a.contains ("aria-label", label)
  let plain := "\\includegraphics[width=60pt]{named.svg}"
  let (withDoc, withDiags, withPage) ← built (figure "<title>An invented title</title>") plain
  let (sansDoc, sansDiags, sansPage) ← built (figure "") plain
  check ref "figure title: the title is the shipped document's alternative"
    (alts withDoc == #[.described "An invented title"] && alts sansDoc == #[.undeclared])
  check ref "figure title: the page names the figure by its title"
    (named withPage "An invented title" && !named sansPage "An invented title")
  check ref "figure title: N0376 is answered by the title, and only by it"
    (!withDiags.any (·.kind == .N0376) && sansDiags.any fun d =>
      d.kind == .N0376 && d.subject == some "named.svg")
  let (declDoc, declDiags, _) ← built (figure "<title>An invented title</title>")
    "\\includegraphics[width=60pt,alt={A declared name}]{named.svg}"
  check ref "figure title: a declared alternative stands over the title"
    (alts declDoc == #[.described "A declared name"] && !declDiags.any (·.kind == .N0376))

/-- **A figure's words are the words it shows.** A wholly transparent group
and a wholly transparent fill paint nothing, so neither the PDF's text nor
the page's live text carries them — an animated figure's frames that its
still pose hides once all reached a reader's text extraction — while a
hidden run still moves the run that follows it in its chunk. -/
def svgInvisibleTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "invisible text: the role faces parse" false
  let bytes := svgDocument (width := 120) (height := 40)
    ("<g opacity=\"0\"><text x=\"2\" y=\"12\">hidden</text></g>" ++
     "<text x=\"2\" y=\"30\">A<tspan fill-opacity=\"0\">gone</tspan>B</text>")
  let imgs ← svgStore fs "words.svg" bytes
  let runs : Array Gfx.Shaped := match (imgs.shaped[0]?).join with
    | some fig => fig.labels.map (·.2)
    | none => #[]
  let painted := runs.filter fun r => r.fill.isSome
  check ref "invisible text: a transparent group sets no run, a transparent fill paints none"
    (!runs.any (·.text == "hidden") && runs.any (·.text == "gone") &&
      painted.map (·.text) == #["A", "B"])
  check ref "invisible text: the hidden run still moves the one after it"
    (match runs.find? (·.text == "A"), runs.find? (·.text == "B") with
      | some a, some b => b.xf.e > a.xf.e + 20 * 65536
      | _, _ => false)
  let body := svgPage fs imgs "words.svg"
  check ref "invisible text: the page sets only the words the figure shows"
    ((svgTexts body).map (·.2) == #["A", "B"])
  let doc := (elabStr "\\includegraphics[width=120pt,alt={Invented words}]{words.svg}").1
  let out := layoutOf fs doc (imgs := imgs)
  let ops := Pdf.pageOps (Layout.Geom.ofPage doc.page) fs out.pages imgs
  let shows := (ops.flatMap allOps).filterMap fun o => match o with
    | .text tops => some (tops.filter fun t => match t with
        | .show _ => true
        | _ => false).size
    | _ => none
  check ref "invisible text: the PDF sets one text object per painted run"
    (shows.foldl (· + ·) 0 == 2)


/-- An invented moving figure with a filter the engine does not draw. -/
def svgMovingFilterFixture : ByteArray :=
  svgDocument ("<filter id=\"soft\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
    "<circle cx=\"10\" cy=\"10\" r=\"5\" fill=\"red\" filter=\"url(#soft)\">" ++
    "<animate attributeName=\"r\" values=\"5;8;5\" dur=\"2s\" repeatCount=\"indefinite\"/></circle>")

/-- **A figure's loss is named in every output its drawing ships in**, and
only there — the premise `FigureLoss.shipsIn` states. Two builds of a still
lossy figure differing only by the converter ship the same HTML, its
authored bytes in an image, and name nothing for the HTML; a moving one's
still face (print, reduced motion) is the drawing its route chose, so with
no converter the engine's drawing — without the feature — and its loss is
named for the HTML too, and with one the converter's, the reason named. -/
def svgOutputScopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "output scope: the role faces parse" false
  -- A converter that draws, answering the figure's own natural size, so the
  -- page cannot tell which drew it by its box.
  let natural ← Driver.svgFetch "f.svg" svgFilterFixture .first "en" none
  let fake : Driver.Converter := .always fun _ _ => return natural.res.mapError .inconclusive
  let page (imgs : Image.Store) (src : String) : String :=
    String.join ((svgPage fs imgs src).toList.map (Html.render · 0))
  let without ← svgStore fs "still.svg" svgFilterFixture
  let withTool ← svgStore fs "still.svg" svgFilterFixture (convert := some fake)
  check ref "output scope: a still lossy figure's HTML is the same with or without the converter"
    (page without "still.svg" == page withTool "still.svg" &&
      (HtmlDoc.imageResources without).any (·.bytes == svgFilterFixture))
  let quiet ← Driver.svgFetch "still.svg" svgFilterFixture .first "en" none
  let quietTool ← Driver.svgFetch "still.svg" svgFilterFixture .first "en" (some fake)
  check ref "output scope: a still lossy figure names nothing for the HTML, its loss for the PDF"
    ((Diag.forOutputs #[.html] quiet.diags).isEmpty && (Diag.forOutputs #[.html] quietTool.diags).isEmpty &&
      (Diag.forOutputs #[.pdf] quiet.diags).any (·.code == "W0609") &&
      (Diag.forOutputs #[.pdf] quietTool.diags).any (·.code == "N0024"))
  let moving ← Driver.svgFetch "moving.svg" svgMovingFilterFixture .first "en" none
  check ref "output scope: a moving figure's lost filter is named for the HTML"
    ((Diag.forOutputs #[.html] moving.diags).any fun d =>
      d.code == "W0609" && d.subject == some "figure:svg:property:filter")
  let movingTool ← Driver.svgFetch "moving.svg" svgMovingFilterFixture .first "en" (some fake)
  check ref "output scope: a moving figure the converter drew names its reason for the HTML"
    ((Diag.forOutputs #[.html] movingTool.diags).any fun d =>
      d.code == "N0024" && d.subject == some "figure:svg:property:filter")
  -- What the HTML's still face is: the engine's drawing, without the filter.
  let imgs ← svgStore fs "moving.svg" svgMovingFilterFixture
  check ref "output scope: the moving figure's still face is the engine's drawing, unfiltered"
    ((imgs.entries[0]?.bind (·.posterSvg)).any fun p =>
      !hasStr (String.fromUTF8! p) "filter" && hasStr (String.fromUTF8! p) "<circle")


/-- **The corpus's figures ship as the page's own SVG where they can**: in
the HTML of the SVG corpus fixture, each still figure that sets text is an
inline `<svg>` named by its `<title>`, the moving one keeps its authored
bytes in an image inside the print and reduced-motion switch, its still
face a source the native judge admits, and the one embedding a raster
keeps its authored bytes in an image of its own. -/
def svgCorpusHtmlChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let src ← IO.FS.readFile "testdata/corpus/svg-figures.tex"
  let (doc, _) ← elabFixture "svg-figures" src
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let fs ← fixtureFontSet oneFace mathSet shipped doc
  let store ← corpusStore doc (some fs)
  -- A figure's own title is the alternative the document leaves undeclared,
  -- as the driver reads it off the figure it drew.
  let doc := corpusTitled doc store
  let (_, body, _) := HtmlDoc.emitTree { imgs := store, fonts := some fs } doc
  let svgs := elemAttrsList (· == "svg") #[] body.toList
  let named (label : String) := svgs.any fun (_, a) => a.contains ("role", "img") && a.contains ("aria-label", label)
  check ref s!"corpus HTML: three still figures ship as inline SVG ({svgs.size})" (svgs.size == 3)
  check ref "corpus HTML: each inline figure is named by its title"
    (named "An invented line chart of a measured value" && named "Three invented captions" &&
      named "Two invented shaded squares")
  check ref "corpus HTML: the moving figure keeps an image inside its still-face switch, the raster figure its own"
    ((elemAttrsList (· == "picture") #[] body.toList).size == 1 &&
      (elemAttrsList (· == "img") #[] body.toList).size == 2)
  check ref "corpus HTML: the moving figure's still face is a source the native judge admits"
    (store.entries.any fun en => en.moving && (en.posterSvg.any fun p => (Svg.judge p).toBool))


/-- **A glyph past the Basic Multilingual Plane cannot shift the pens after
it**: a run setting one places every glyph in a `tspan` of its own, at its
pen, whatever a browser counts a surrogate pair as; a run within the plane
keeps one `x` per character. -/
def svgAstralTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let ink : Option Gfx.Fill := some { paint := .solid { r := 0, g := 0, b := 0 }, rule := .nonzero, alpha := Gfx.Alpha.opaque }
  let run (cs : List (Char × Dim.Sp)) : Gfx.Shaped :=
    { size := Dim.pt 10, xf := Gfx.Affine.unit, glyphs := (cs.map fun (c, x) => (0, 1, c, x)).toArray
      text := String.ofList (cs.map (·.1)), fill := ink, stroke := none, lang := none, role := 0
      weight := 400, italic := false }
  let astral := FigureSvg.textNode { iso := none } (run [('a', 0), ('𝐀', Dim.pt 5), ('b', Dim.pt 12)])
  let plain := FigureSvg.textNode { iso := none } (run [('a', 0), ('b', Dim.pt 5)])
  let spans := elemAttrsList (· == "tspan") #[] [astral]
  let attr (a : Array (String × String)) (k : String) : Option String := (a.find? (·.1 == k)).map (·.2)
  check ref "astral text: each glyph of a run past the plane sits in a tspan at its pen"
    (spans.size == 3 && spans.toList.map (fun (_, a) => attr a "x") == [some "0", some "5", some "12"])
  check ref "astral text: the run's text element carries no x list of its own"
    ((elemAttrsList (· == "text") #[] [astral]).all fun (_, a) => (attr a "x").isNone)
  check ref "astral text: a run within the plane keeps its x list, one value per glyph"
    (((elemAttrsList (· == "text") #[] [plain]).all fun (_, a) => attr a "x" == some "0 5") &&
      (elemAttrsList (· == "tspan") #[] [plain]).isEmpty)

def svgHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgInlineChecks ref
  svgImgChecks ref
  svgPosterFaceChecks ref
  svgTextPaintLossChecks ref
  svgInvisibleTextChecks ref
  svgOutputScopeChecks ref
  svgAstralTextChecks ref

end Tests
