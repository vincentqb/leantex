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

/-! The native SVG route on the HTML page: inline SVG for still text figures, authored bytes
otherwise, and a moving figure's still face drawn by the engine. -/

namespace Tests

open LeanTex.Core LeanTex.Cli

/-- A face set with the serif body, sans and mono roles apart. -/
def threeRoleFonts : IO (Option Font.FontSet) := do
  let load (name : String) : IO (Option Font) := do
    let bytes ← IO.FS.readBinFile ("testdata/corpus/fonts/" ++ name)
    return (Font.parse bytes).toOption
  let some body ← load "SourceSerifPro-Regular.otf" | return none
  let some sans ← load "FiraSans-Regular.otf" | return none
  let some mono ← load "SourceCodePro-Regular.otf" | return none
  return some { fonts := #[body, sans, mono]
                index := #[((0, 400, false), 0), ((0, 700, false), 0), ((1, 400, false), 1),
                  ((1, 700, false), 1), ((2, 400, false), 2), ((2, 700, false), 2)] }

/-- One source's store as the driver builds it: fetched natively, fulfilled, shaped, and given a
still face when it moves. -/
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

/-- A still figure that sets text is the page's own SVG, each run a `<text>` in its role's family at
the shaped pen positions. -/
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

/-- A textless figure, a lossy one and one embedding a raster ship as an `<img>` of the authored
source. -/
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

/-- A moving figure with a clipped ground and a line of sans text holding a space. -/
def svgMovingTextFixture : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"120\" height=\"30\">" ++
   "<defs><clipPath id=\"half\"><rect width=\"60\" height=\"30\"/></clipPath></defs>" ++
   "<g clip-path=\"url(#half)\"><rect width=\"120\" height=\"30\" fill=\"#eef\"/></g>" ++
   "<rect width=\"20\" height=\"20\" fill=\"red\" opacity=\"0\">" ++
   "<animate attributeName=\"opacity\" values=\"0;1\" dur=\"2s\"/></rect>" ++
   "<text x=\"24\" y=\"20\" font-family=\"sans-serif\">Moving text</text></svg>").toUTF8

/-- A moving figure keeps its animation, and its still face is the engine's drawing, its text as
outlines. -/
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

/-- A run painted with a gradient fill or an outline stroke is a named loss. -/
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

/-- A figure's `<title>` is the alternative the document did not declare, two builds apart; a
declared alternative wins. -/
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

/-- A figure's words are the words it shows: transparent text sets no run but still moves the
next. -/
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


/-- A moving figure with a filter the engine does not draw. -/
def svgMovingFilterFixture : ByteArray :=
  svgDocument ("<filter id=\"soft\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
    "<circle cx=\"10\" cy=\"10\" r=\"5\" fill=\"red\" filter=\"url(#soft)\">" ++
    "<animate attributeName=\"r\" values=\"5;8;5\" dur=\"2s\" repeatCount=\"indefinite\"/></circle>")

/-- A figure's loss is named in every output its drawing ships in, and only there. -/
def svgOutputScopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "output scope: the role faces parse" false
  -- A converter drawing at the figure's natural size, so the box cannot tell which drew it.
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
  let imgs ← svgStore fs "moving.svg" svgMovingFilterFixture
  check ref "output scope: the moving figure's still face is the engine's drawing, unfiltered"
    ((imgs.entries[0]?.bind (·.posterSvg)).any fun p =>
      !hasStr (String.fromUTF8! p) "filter" && hasStr (String.fromUTF8! p) "<circle")
  let linked (extra : String) : ByteArray := svgDocument
    ("<rect id=\"x\" width=\"1\" height=\"1\"/>" ++ extra ++
      "<a href=\"#x\"><text x=\"2\" y=\"15\" font-family=\"Example Grotesk\">Label 漢</text></a>")
  let blur := "<filter id=\"soft\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
    "<rect width=\"4\" height=\"4\" filter=\"url(#soft)\"/>"
  for (name, bytes, inline) in [("inline", linked "", true), ("authored", linked blur, false)] do
    let f ← Driver.svgFetch s!"{name}.svg" bytes .first "en" none
    let req : Image.Request := { src := s!"{name}.svg" }
    let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some bytes) none)
    let (imgs, shaped) := FigureStore.settle fs (FigureStore.attach { entries := #[en] } #[some f.drawn])
    let notes := f.diags ++ shaped.map (·.2)
    let html := page imgs s!"{name}.svg"
    let namedIn (o : Diag.Output) (code : String) := (Diag.forOutputs #[o] notes).any (·.code == code)
    let glyphIn (o : Diag.Output) := (Diag.forOutputs #[o] notes).any fun d =>
      d.code == "W0609" && d.subject == some "figure:svg:font:U+6F22"
    check ref s!"output scope: the {name} figure ships {if inline then "inline" else "as its authored bytes"} ({hasStr html "<svg"})"
      (hasStr html "<svg" == inline)
    check ref s!"output scope: the {name} figure's family and uncovered-glyph notes are {if inline then "" else "not "}named for the HTML"
      (namedIn .html "N0026" == inline && glyphIn .html == inline)
    check ref s!"output scope: the {name} figure's link note is named for the HTML and the PDF"
      (namedIn .html "N0027" && namedIn .pdf "N0027")
    check ref s!"output scope: the {name} figure's family and uncovered-glyph notes are named for the PDF"
      (namedIn .pdf "N0026" && glyphIn .pdf)


/-- A figure's CSS lists are cut only at separators outside nesting and strings, so its diagnostics
name whole selectors and families, and the rest of its sheet still paints. -/
def cssListChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← threeRoleFonts | check ref "CSS lists: the role faces parse" false
  let selectors := ["rect[title=\"x, y\"]", "rect[title='p,q']", "rect[title=p,q]", "rect .ok..bad"]
  let sheet := String.join (selectors.map (· ++ ", circle { fill: red } ")) ++
    ".keep { fill: blue; shape-rendering: [a;b] } .bang { font-family: \"Bang!\" !important }"
  let bytes := svgDocument ("<style>" ++ sheet ++ "</style>" ++
    "<rect class=\"keep\" width=\"5\" height=\"5\"/><circle cx=\"12\" cy=\"12\" r=\"3\"/>" ++
    "<text x=\"1\" y=\"18\" style=\"font-family: 'Invented Grotesk, Narrow'\">Hi</text>" ++
    "<text class=\"bang\" x=\"20\" y=\"18\" style=\"font-family: serif\">Ho</text>") 40 20
  let f ← Driver.svgFetch "lists.svg" bytes .first "en" none
  let req : Image.Request := { src := "lists.svg" }
  let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some bytes) none)
  let (imgs, shaped) := FigureStore.settle fs (FigureStore.attach { entries := #[en] } #[some f.drawn])
  let subjects := (f.diags ++ shaped.map (·.2)).filterMap (·.subject)
  let after (pre : String) (s : String) : Option String :=
    if s.startsWith pre then some (s.drop pre.length).toString else none
  let named := subjects.filterMap fun s =>
    (after "figure:svg:property:style: the selector '" s).map (·.dropEnd 1 |>.toString)
  check ref s!"CSS lists: each dropped rule names its whole selector ({named})"
    (named.toList == selectors)
  let families := subjects.filterMap (after "svg:font:")
  check ref s!"CSS lists: a quoted family holding a comma is named whole ({families})"
    (families == #["Invented Grotesk, Narrow", "Bang!"])
  check ref s!"CSS lists: a semicolon inside brackets ends no declaration ({subjects})"
    (subjects.all fun s => !hasStr s "the declaration")
  let fills := ((f.vector.map (·.marks)).getD #[]).filterMap fun m => match m with
    | .paint _ _ (some fl) _ _ _ => match fl.paint with
      | .solid c => some (c.r.toNat, c.g.toNat, c.b.toNat)
      | _ => none
    | _ => none
  check ref s!"CSS lists: the sheet's whole rules paint and its dropped ones nothing ({fills})"
    (fills.contains (0, 0, 255) && !fills.contains (255, 0, 0))
  let body := svgPage fs imgs "lists.svg"
  check ref "CSS lists: the lossy figure ships its authored bytes, every list as written"
    ((HtmlDoc.imageResources imgs).any (·.bytes == bytes) &&
      (elemAttrsList (· == "svg") #[] body.toList).isEmpty)
  let blocks := svgDocument ("<style>rect[title=x), y], circle { fill: red } " ++
    ".k { fill: blue; x: [a); b] } .m { fill: green } .w { x: [}]; fill: yellow }" ++
    "rect\n\t .ok..bad, rect { fill: red }</style>" ++
    "<rect class=\"k\" width=\"5\" height=\"5\"/><rect class=\"m\" x=\"10\" width=\"5\" height=\"5\"/>" ++
    "<rect class=\"w\" x=\"20\" width=\"5\" height=\"5\"/>" ++
    "<text x=\"1\" y=\"18\" font-family=\"Invented's Hand, serif\">Hi</text>" ++
    "<text x=\"20\" y=\"18\" font-family=\"Invented /* it's */, monospace\">Ho</text>") 40 20
  let bf ← Driver.svgFetch "blocks.svg" blocks .first "en" none
  let (ben, _) := Image.fulfilOne { src := "blocks.svg" } (.decoded "" bf.res none none (some blocks) none)
  let (blockStore, blockShaped) :=
    FigureStore.settle fs (FigureStore.attach { entries := #[ben] } #[some bf.drawn])
  let geom : Layout.Geom := {}
  let blockDoc := (elabStr "\\includegraphics[width=200pt]{blocks.svg}").1
  let pdf := pdfText (Pdf.write geom fs (layoutOf fs blockDoc geom none blockStore).pages {} blockStore)
  check ref "CSS lists: a closer inside another kind's block ends neither, so the rule's paint ships"
    (bytesContain pdf "0 0 1 rg" && bytesContain pdf "1 1 0 rg")
  let blockSubjects := (bf.diags ++ blockShaped.map (·.2)).filterMap (·.subject)
  let blockNamed := blockSubjects.filterMap fun s =>
    (after "figure:svg:property:style: the selector '" s).map (·.dropEnd 1 |>.toString)
  check ref s!"CSS lists: a selector is named whole and on one line ({blockNamed})"
    (blockNamed == #["rect[title=x), y]", "rect .ok..bad"])
  check ref s!"CSS lists: a family list CSS reads whole or drops names no family it lacks ({blockSubjects})"
    (blockSubjects.all fun s => !s.startsWith "svg:font:")
  let openSvg := svgDocument ("<style>.m { fill: lime } .a { fill: blue; stroke-dasharray: [2 }</style>" ++
    "<style>.b { fill: yellow; x: { } .c { fill: red }</style><style>.d { fill: aqua; x: [{]}</style>" ++
    "<style>.e { fill: fuchsia; x: [ [ ]</style><style>.f { fill: white</style>" ++
    String.join ((["m", "a", "b", "c", "d", "e", "f"].zipIdx).map fun (c, i) =>
      s!"<rect class=\"{c}\" x=\"{10 * i}\" width=\"5\" height=\"5\"/>")) 70 10
  let of ← Driver.svgFetch "open.svg" openSvg .first "en" none
  let (oen, _) := Image.fulfilOne { src := "open.svg" } (.decoded "" of.res none none (some openSvg) none)
  let (openStore, _) := FigureStore.settle fs (FigureStore.attach { entries := #[oen] } #[some of.drawn])
  let openDoc := (elabStr "\\includegraphics[width=200pt]{open.svg}").1
  let openPdf := pdfText (Pdf.write geom fs (layoutOf fs openDoc geom none openStore).pages {} openStore)
  check ref "CSS lists: a block the sheet's end closes keeps its rule's paint, as CSS and rsvg paint it"
    (["0 1 0 rg", "0 0 1 rg", "1 1 0 rg", "0 1 1 rg", "1 0 1 rg", "1 1 1 rg"].all (bytesContain openPdf ·) &&
      !bytesContain openPdf "1 0 0 rg")


/-- The corpus's figures ship as the page's own SVG where they can, the moving and raster ones as
images. -/
def svgCorpusHtmlChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let src ← IO.FS.readFile "testdata/corpus/svg-figures.tex"
  let (doc, _) ← elabFixture "svg-figures" src
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let fs ← fixtureFontSet oneFace mathSet shipped doc
  let store ← corpusStore doc (some fs)
  let doc := corpusTitled doc store
  let (_, body, _) := HtmlDoc.emitTree { imgs := store, fonts := some fs } doc
  let svgs := elemAttrsList (· == "svg") #[] body.toList
  let named (label : String) := svgs.any fun (_, a) => a.contains ("role", "img") && a.contains ("aria-label", label)
  check ref s!"corpus HTML: three still figures ship as inline SVG ({svgs.size})" (svgs.size == 3)
  check ref "corpus HTML: each inline figure is named by its title"
    (named "An invented line chart of a measured value" && named "Three invented captions" &&
      named "Two invented shaded squares")
  check ref "corpus HTML: the moving figure's image is in its switch, the raster figure's alone"
    ((elemAttrsList (· == "picture") #[] body.toList).size == 1 &&
      (elemAttrsList (· == "img") #[] body.toList).size == 2)
  check ref "corpus HTML: the moving figure's still face is a source the native judge admits"
    (store.entries.any fun en => en.moving && (en.posterSvg.any fun p => (Svg.judge p).toBool))


/-- A glyph past the Basic Multilingual Plane cannot shift the pens after it. -/
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
  cssListChecks ref
  svgAstralTextChecks ref

end Tests
