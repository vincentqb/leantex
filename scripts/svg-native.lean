/-
How much SVG the engine reads and draws itself, as a tier. Run from the
repository root:

  lake env lean --run scripts/svg-native.lean              regenerate the baseline
  lake env lean --run scripts/svg-native.lean --check      gate against the committed one
  lake env lean --run scripts/svg-native.lean --selftest   the measures

Every row is a count or a 0–2 score over committed, invented inputs, read
by the pure core — no converter, no font the repository does not ship, no
network — so `--check` is hermetic:

* `boundary.*`: the resource boundary's matrix (`svgBoundaryAdmitted`,
  `svgBoundaryRefused`, `svgBoundaryMalformed`), each case judged as the
  matrix says;
* `terminal.*`: the terminal-pose projection's matrix
  (`svgTerminalRefused`, `svgTerminalAccepted`), each refused, or ending in
  its static pose;
* `boundary.encodings`: the encoded sources (`svgBoundaryEncodings`), each
  read or refused as the matrix says;
* `feature.<name>`: one invented probe per SVG feature, 2 when the importer
  draws it whole, 1 when it draws it with its losses named, 0 when it
  refuses it or draws nothing — a feature the engine stops drawing is a
  fall. A score of 2 will also require the drawing to read back equal to
  the converter's PDF of the same probe once the PDF importer lands;
* `fixtures.exact` / `fixtures.text`: the invented figures under
  `testdata/svg` and `testdata/corpus/figures` the importer draws without a
  loss, and those whose text sets in the shipped faces with nothing missing.
-/
import scripts.Board
import Tests.Support
import Tests.SvgHtml
import LeanTex.Core.SvgImport
import LeanTex.Core.SvgPoster
import LeanTex.Core.LayoutFigure

open Scoreboard LeanTex.Core

/-- One feature's probe: a body on a 40×40 document. -/
def featureProbes : List (String × String) := [
  ("rect", "<rect x=\"2\" y=\"2\" width=\"30\" height=\"20\" fill=\"#1f77b4\"/>"),
  ("rect-rounded", "<rect x=\"2\" y=\"2\" width=\"30\" height=\"20\" rx=\"4\" fill=\"#1f77b4\"/>"),
  ("circle", "<circle cx=\"20\" cy=\"20\" r=\"10\" fill=\"#d62728\"/>"),
  ("ellipse", "<ellipse cx=\"20\" cy=\"20\" rx=\"15\" ry=\"8\" fill=\"#2ca02c\"/>"),
  ("line", "<line x1=\"2\" y1=\"2\" x2=\"38\" y2=\"38\" stroke=\"black\"/>"),
  ("polyline", "<polyline points=\"2,38 12,10 22,30 38,4\" fill=\"none\" stroke=\"black\"/>"),
  ("polygon", "<polygon points=\"20,2 38,38 2,38\" fill=\"#9467bd\"/>"),
  ("path-lines", "<path d=\"M2 2 L38 2 H20 V38 Z\" fill=\"none\" stroke=\"black\"/>"),
  ("path-relative", "<path d=\"m2 2 l10 0 h10 v10 z\" fill=\"none\" stroke=\"black\"/>"),
  ("path-cubic", "<path d=\"M2 20 C10 2 30 2 38 20 S30 38 20 38\" fill=\"none\" stroke=\"black\"/>"),
  ("path-quadratic", "<path d=\"M2 20 Q20 2 38 20 T38 38\" fill=\"none\" stroke=\"black\"/>"),
  ("path-arc", "<path d=\"M10 20 A10 10 0 1 1 30 20 a10 5 30 0 0 -20 0\" fill=\"none\" stroke=\"black\"/>"),
  ("path-compact-numbers", "<path d=\"M2.5.5L10-2.5e1.5 20\" fill=\"none\" stroke=\"black\"/>"),
  ("fill-rule", "<path d=\"M2 2H38V38H2ZM10 10H30V30H10Z\" fill-rule=\"evenodd\"/>"),
  ("stroke-style", "<path d=\"M2 20H38\" stroke=\"black\" stroke-width=\"3\" stroke-linecap=\"round\" stroke-linejoin=\"bevel\" stroke-miterlimit=\"2\"/>"),
  ("stroke-dash", "<path d=\"M2 20H38\" stroke=\"black\" stroke-dasharray=\"4 2\" stroke-dashoffset=\"1\"/>"),
  ("opacity", "<g opacity=\"0.5\"><rect width=\"20\" height=\"20\"/></g>"),
  ("fill-stroke-opacity", "<rect width=\"20\" height=\"20\" fill=\"red\" fill-opacity=\"0.4\" stroke=\"blue\" stroke-opacity=\"0.6\"/>"),
  ("transform-list", "<g transform=\"translate(5 5) scale(2) rotate(10)\"><rect width=\"5\" height=\"5\"/></g>"),
  ("transform-skew", "<rect width=\"10\" height=\"10\" transform=\"skewX(10) skewY(5)\"/>"),
  ("transform-matrix", "<rect width=\"10\" height=\"10\" transform=\"matrix(1 0.2 0 1 3 4)\"/>"),
  ("use-element", "<defs><circle id=\"c\" r=\"5\"/></defs><use href=\"#c\" x=\"10\" y=\"10\"/><use href=\"#c\" x=\"30\" y=\"30\"/>"),
  ("use-xlink", "<defs><circle id=\"c\" r=\"5\"/></defs><use xmlns:xlink=\"http://www.w3.org/1999/xlink\" xlink:href=\"#c\" x=\"10\" y=\"10\"/>"),
  ("symbol-viewbox", "<defs><symbol id=\"s\" viewBox=\"0 0 10 10\"><rect width=\"10\" height=\"10\"/></symbol></defs><use href=\"#s\" x=\"5\" y=\"5\" width=\"20\" height=\"20\"/>"),
  ("nested-svg", "<svg x=\"5\" y=\"5\" width=\"20\" height=\"20\" viewBox=\"0 0 10 10\"><rect width=\"10\" height=\"10\"/></svg>"),
  ("clip-path", "<defs><clipPath id=\"k\"><rect width=\"20\" height=\"20\"/></clipPath></defs><circle cx=\"20\" cy=\"20\" r=\"15\" clip-path=\"url(#k)\"/>"),
  ("linear-gradient", "<defs><linearGradient id=\"g\"><stop offset=\"0\" stop-color=\"red\"/><stop offset=\"1\" stop-color=\"blue\"/></linearGradient></defs><rect width=\"40\" height=\"40\" fill=\"url(#g)\"/>"),
  ("radial-gradient", "<defs><radialGradient id=\"g\"><stop offset=\"0\" stop-color=\"white\"/><stop offset=\"1\" stop-color=\"black\"/></radialGradient></defs><rect width=\"40\" height=\"40\" fill=\"url(#g)\"/>"),
  ("gradient-user-space", "<defs><linearGradient id=\"g\" gradientUnits=\"userSpaceOnUse\" x1=\"0\" y1=\"0\" x2=\"40\" y2=\"40\" gradientTransform=\"rotate(10)\"><stop offset=\"0\" stop-color=\"red\"/><stop offset=\"1\" stop-color=\"blue\"/></linearGradient></defs><rect width=\"40\" height=\"40\" fill=\"url(#g)\"/>"),
  ("gradient-href", "<defs><linearGradient id=\"a\"><stop offset=\"0\" stop-color=\"red\"/><stop offset=\"1\" stop-color=\"blue\"/></linearGradient><linearGradient id=\"b\" href=\"#a\" x2=\"0\" y2=\"1\"/></defs><rect width=\"40\" height=\"40\" fill=\"url(#b)\"/>"),
  ("css-stylesheet", "<style>.k { fill: green } #i { stroke: black } g > rect { opacity: 0.5 } g rect { stroke-width: 2 }</style><g><rect class=\"k\" id=\"i\" width=\"10\" height=\"10\"/></g>"),
  ("css-sibling-combinator", "<style>rect + circle { fill: red }</style><rect width=\"10\" height=\"10\"/><circle cx=\"20\" cy=\"20\" r=\"4\"/>"),
  ("css-style-attribute", "<rect width=\"10\" height=\"10\" style=\"fill: #123456; stroke: rgb(10, 20, 30)\"/>"),
  ("css-important", "<style>rect { fill: red !important }</style><rect width=\"10\" height=\"10\" style=\"fill: blue\"/>"),
  ("inherit-current-color", "<g color=\"#ff7f0e\" fill=\"currentColor\"><rect width=\"10\" height=\"10\" stroke=\"inherit\"/></g>"),
  ("named-colors", "<rect width=\"10\" height=\"10\" fill=\"rebeccapurple\" stroke=\"cornflowerblue\"/>"),
  ("display-visibility", "<rect width=\"10\" height=\"10\" display=\"none\"/><rect width=\"10\" height=\"10\" visibility=\"hidden\"/><rect x=\"20\" width=\"10\" height=\"10\"/>"),
  ("switch", "<switch><rect width=\"10\" height=\"10\" systemLanguage=\"en\"/><circle r=\"5\"/></switch>"),
  ("text", "<text x=\"2\" y=\"20\" font-family=\"sans-serif\" font-size=\"10\">Label</text>"),
  ("text-anchor", "<text x=\"20\" y=\"20\" text-anchor=\"middle\">Mid</text><text x=\"38\" y=\"30\" text-anchor=\"end\">End</text>"),
  ("tspan-offsets", "<text x=\"2\" y=\"20\">A<tspan dx=\"3\" dy=\"-2\">b</tspan><tspan x=\"20\" y=\"30\">c</tspan></text>"),
  ("text-weight-style", "<text x=\"2\" y=\"20\" font-weight=\"bold\" font-style=\"italic\">Bold</text>"),
  ("text-transform", "<text transform=\"translate(20 20) rotate(-90)\">Turned</text>"),
  ("text-space", "<text x=\"2\" y=\"20\" xml:space=\"preserve\">a  b</text>"),
  ("data-png-image", s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" width=\"20\" height=\"20\"/>"),
  ("preserve-aspect-ratio", "<svg width=\"40\" height=\"20\" viewBox=\"0 0 10 10\" preserveAspectRatio=\"xMinYMax slice\"><rect width=\"10\" height=\"10\"/></svg>"),
  ("units", "<rect x=\"1mm\" y=\"2pt\" width=\"1cm\" height=\"0.25in\" fill=\"black\"/>"),
  ("percent-lengths", "<rect width=\"50%\" height=\"25%\"/>"),
  ("transform-origin", "<rect x=\"10\" y=\"10\" width=\"20\" height=\"20\" transform=\"rotate(30)\" style=\"transform-origin: center\"/>"),
  ("font-shorthand", "<text x=\"2\" y=\"20\" style=\"font: italic bold 10px sans-serif\">Label</text>"),
  ("css-url-in-style", "<defs><linearGradient id=\"g\"><stop offset=\"0\" stop-color=\"red\"/><stop offset=\"1\" stop-color=\"blue\"/></linearGradient></defs><rect width=\"40\" height=\"40\" style=\"fill: url(#g)\"/>"),
  ("white-space-pre", "<text x=\"2\" y=\"20\" style=\"white-space: pre\">a  b</text>"),
  ("filter", "<filter id=\"f\"><feGaussianBlur stdDeviation=\"1\"/></filter><rect width=\"20\" height=\"20\" filter=\"url(#f)\"/>")]

/-- Whether the importer draws a probe whole: exact, and something painted
or set. -/
def drawnWhole (bytes : ByteArray) : Bool :=
  match Svg.importBytes bytes with
  | .exact i => !i.fig.marks.isEmpty || !i.fig.labels.isEmpty
  | .lossy _ | .refused _ => false

/-- A probe's score: 2 drawn whole, 1 drawn with its losses named, 0
refused or drawing nothing. -/
def score (bytes : ByteArray) : Nat :=
  match Svg.importBytes bytes with
  | .exact i => if !i.fig.marks.isEmpty || !i.fig.labels.isEmpty then 2 else 0
  | .lossy i => if !i.fig.marks.isEmpty || !i.fig.labels.isEmpty then 1 else 0
  | .refused _ => 0

/-- The invented figures the tier reads: every SVG under `testdata/svg` and
`testdata/corpus/figures`, in name order. -/
def fixtureFiles : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for dir in ["testdata/svg", "testdata/corpus/figures"] do
    for e in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
      if e.fileName.endsWith ".svg" then out := out.push e.path
  return out

def measureTier : IO (Array String × Array Row) := do
  let drawing := String.fromUTF8! (svgDocument svgRedSquare)
  let admitted := svgBoundaryAdmitted.filter fun (_, b) => (Svg.judge (svgDocument b)).toBool
  let refused := svgBoundaryRefused.filter fun (_, b) =>
    !(Svg.judge (svgDocument (svgRedSquare ++ b))).toBool
  let malformed := (svgBoundaryMalformed drawing).filter fun (_, src) => !(Svg.judge src.toUTF8).toBool
  let doc (b : String) := svgDocument (width := 32) (height := 16) b
  let pose (b : ByteArray) (atEnd : Bool) :=
    (SvgPoster.pose b atEnd).map fun t => (Svg.importTree t).fig.marks
  let tRefused := svgTerminalRefused.filter fun (_, b) => !(SvgPoster.pose (doc b) true).toBool
  let tAccepted := svgTerminalAccepted.filter fun (_, b, e) =>
    match pose (doc b) true, pose (doc e) false with
    | .ok a, .ok z => a == z
    | _, _ => false
  let files ← fixtureFiles
  let fonts ← Tests.threeRoleFonts
  let mut exact := 0
  let mut text := 0
  for f in files do
    let bytes ← IO.FS.readBinFile f
    match Svg.importBytes bytes with
    | .exact i =>
      exact := exact + 1
      if let some fs := fonts then
        let (_, notes) := Layout.shapeFigure fs i.fig
        if notes.missing.isEmpty && notes.substs.isEmpty then text := text + 1
    | .lossy _ | .refused _ => pure ()
  let features := featureProbes.map fun (name, body) =>
    { item := s!"feature.{name}", value := score (svgDocument body 40 40) : Row }
  let encodings := svgBoundaryEncodings.filter fun (_, b, text?) =>
    (Svg.judge b).toBool == text?.isSome
  return (#[s!"# fixtures: {files.size} invented SVGs under testdata/svg and testdata/corpus/figures"],
    #[{ item := "boundary.admitted", value := admitted.length },
      { item := "boundary.encodings", value := encodings.length },
      { item := "boundary.malformed-refused", value := malformed.length },
      { item := "boundary.refused", value := refused.length },
      { item := "fixtures.exact", value := exact },
      { item := "fixtures.text", value := text },
      { item := "terminal.accepted", value := tAccepted.length },
      { item := "terminal.refused", value := tRefused.length }] ++ features.toArray)

def selftest : IO UInt32 := tierSelftest "svg-native" fun no => do
  -- The probe measure: exact and drawing is 1, a loss or a refusal 0.
  no "a drawn probe counts" (drawnWhole (svgDocument "<rect width=\"4\" height=\"4\"/>"))
  no "a lossy probe does not"
    (!drawnWhole (svgDocument "<filter id=\"f\"/><rect width=\"4\" height=\"4\" filter=\"url(#f)\"/>"))
  no "a refused source does not" (!drawnWhole "<html/>".toUTF8)
  no "an empty drawing does not" (!drawnWhole (svgDocument ""))
  no "a whole drawing scores 2" (score (svgDocument "<rect width=\"4\" height=\"4\"/>") == 2)
  no "a lossy drawing scores 1"
    (score (svgDocument "<filter id=\"f\"/><rect width=\"4\" height=\"4\" filter=\"url(#f)\"/>") == 1)
  no "a refusal scores 0" (score "<html/>".toUTF8 == 0)
  no "probe names are unique"
    ((featureProbes.map (·.1)).eraseDups.length == featureProbes.length)

def main (args : List String) : IO UInt32 :=
  tierMain "svg-native" .raw measureTier selftest args
