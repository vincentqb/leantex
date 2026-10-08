module

public import LeanTex.Core.Font
public import LeanTex.Core.Elab
public import LeanTex.Core.Layout
public import LeanTex.Core.HtmlDoc
public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PaletteTextEpoch

def source (body : Bool) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf,html}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodyfg=#004080}\n" ++
  "\\begin{document}\n" ++
  (if body then "\\begin{block}{}\n" else "") ++
  "BEFORE\n\n\\palette{fg=#804000}\nAFTER $x$\n" ++
  "\\begin{verbatim}\nCODEIN\n\\end{verbatim}\n" ++
  (if body then "\\end{block}\n" else "") ++
  "OUTSIDE $y$\n\\begin{verbatim}\nCODEOUT\n\\end{verbatim}\n" ++
  "\\setbeamercolor{normal text}{fg={}}\n" ++
  "DEFAULT $z$\n\\begin{verbatim}\nCODEDEFAULT\n\\end{verbatim}\n" ++
  "\\end{document}\n"

def document (body : Bool) : Ir.Doc :=
  (Elab.run "palette-text-epoch.tex" (source body)).1

private def property (style key : String) : Option String :=
  (style.splitOn ";").foldl (fun old decl =>
    match decl.splitOn ":" with
    | [k, v] => if k.trimAscii.toString == key then some v.trimAscii.toString else old
    | _ => old) none

private structure Ink where
  text : String
  color : Option String
  ownerColor : Option String

-- Inspect inherited concrete paint in the typed artifact. A custom property
-- alone does not repaint an inherited CSS color; the browser witness checks
-- that distinction against the same layout runs.
mutual
  private def htmlInks (color ownerColor : Option String) (out : Array Ink) :
      List Html.Node → Array Ink
    | [] => out
    | node :: rest => htmlInks color ownerColor (htmlInk color ownerColor out node) rest
  private def htmlInk (color ownerColor : Option String) (out : Array Ink) :
      Html.Node → Array Ink
    | .text text => out.push { text := text.trimAscii.toString, color, ownerColor }
    | .elem tag attrs kids =>
      let style := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      let own := property style "color"
      let ownerColor := if ["p", "li", "dt", "dd"].contains tag then own else ownerColor
      htmlInks (own.or color) ownerColor out kids.toList
    | .style _ | .script .. => out
end

private def epochLineForeground (out : Layout.Out) (marker : String) : Option Ir.Color :=
  let lines := out.pages.flatMap (·.lines) |>.filter fun line =>
    !line.furniture && (lineText line false).startsWith marker
  if lines.size != 1 then none else
    let colors := lines.flatMap fun line => line.segs.filterMap fun
      | .run _ c _ glyphWidth glyphs .. =>
        if glyphWidth > 0 && !glyphs.isEmpty then some c else none
      | _ => none
    colors[0]?.filter fun color => colors.all (· == color)

/-- Read the marked source glyphs, excluding generated list markers and
furniture. A paragraph wrapper is optional; its source ink is not. -/
private def markerForeground (out : Layout.Out) (marker : String) : Option Ir.Color :=
  let colors := out.pages.flatMap (·.lines) |>.filter (! ·.furniture) |>.flatMap fun line =>
    line.segs.filterMap fun seg => match seg with
      | .run _ color .. =>
        if (String.ofList seg.glyphChars).contains marker then some color else none
      | _ => none
  if colors.size == 1 then colors[0]? else none

private def listSource (env : String) : String :=
  let item := if env == "description" then "\\item[LABEL]" else "\\item"
  "\\documentclass{article}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodyfg=#004080}\n" ++
  "\\begin{document}\n\\begin{block}{TITLE}\n\\begin{" ++ env ++ "}\n" ++
  item ++ " \\palette{fg=#804000} ITEM\n" ++ item ++ " NEXT\n\\end{" ++ env ++ "}\n" ++
  "LATER\n\\end{block}\nOUTSIDE\n\\end{document}\n"

private def para (text : String) : Ir.Block := .para #[.text text]

/-- Palette declarations follow the same flow boundaries as PDF layout.
The list cases exercise source elaboration and paragraph elision;
the remaining cases cross the ordinary container exits and the isolated
column/note boundaries. Each assertion reads the emitted artifacts. -/
private def containerEpochChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let brown : Ir.Color := { r := 128, g := 64, b := 0 }
  for env in ["itemize", "enumerate", "description"] do
    let (doc, ds) := Elab.run "list-palette-epoch.tex" (listSource env)
    check ref s!"palette list/{env}: source has no errors" (ds.all (·.severity != .error))
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (_, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    let leaves := htmlInks (some (Ir.Design.ofPalette doc.palette).fg.css) none #[] nodes.toList
    for marker in ["ITEM", "NEXT", "LATER", "OUTSIDE"] do
      let pdf := markerForeground out marker
      let ink := leaves.filter (·.text == marker)
      check ref s!"palette list/{env}: PDF {marker}" (pdf == some brown)
      check ref s!"palette list/{env}: HTML {marker} owns the new ink"
        (ink.size == 1 && ink.all fun leaf =>
          leaf.color == some brown.css && leaf.ownerColor == some brown.css)
  let base := document true
  let changed := base.palette.declare "fg" brown
  let wrappers : List (String × (Array Ir.Block → Ir.Block)) :=
    [("center", .center), ("ragged", .ragged .left), ("quote", .quote),
     ("abstract", .abstract), ("role", .role "container"),
     ("link", .link "#target"), ("only", .only #["pdf", "html"]),
     ("list", fun body => .list false #[body]),
     ("nested list", fun body => .list false #[#[.list true #[body]]])]
  for (name, wrap) in wrappers do
    let doc := { base with body := #[
      .titled .block #[] #[wrap #[.setPalette changed, para "ITEM"], para "LATER"],
      para "OUTSIDE"] }
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (_, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    let leaves := htmlInks (some (Ir.Design.ofPalette doc.palette).fg.css) none #[] nodes.toList
    for marker in ["ITEM", "LATER", "OUTSIDE"] do
      let ink := leaves.filter (·.text == marker)
      check ref s!"palette container/{name}: PDF {marker}"
        (markerForeground out marker == some brown)
      check ref s!"palette container/{name}: HTML {marker}"
        (ink.size == 1 && ink.all (·.color == some brown.css))
  for (name, wrap) in [
      ("columns", fun body => Ir.Block.columns #[(.share, body)]),
      ("note", Ir.Block.note)] do
    let doc := { base with body := #[
      .titled .block #[] #[wrap #[.setPalette changed, para "LOCAL"], para "LATER"],
      para "OUTSIDE"] }
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (_, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    let leaves := htmlInks (some (Ir.Design.ofPalette doc.palette).fg.css) none #[] nodes.toList
    for (marker, expected) in [("LATER", "#004080"), ("OUTSIDE", "#101010")] do
      let ink := leaves.filter (·.text == marker)
      check ref s!"palette scope/{name}: PDF {marker}"
        ((markerForeground out marker).map (·.css) == some expected)
      check ref s!"palette scope/{name}: HTML {marker}"
        (ink.size == 1 && ink.all (·.color == some expected))

/-- Foreground epochs repaint inherited plain, math and code ink after a
body exit and in ordinary flow. Erasing the foreground repaints the shared
default. The guard compares actual typed HTML leaves with shipped layout
runs; neither a palette snapshot nor a CSS token by itself can pass it. -/
def paletteTextEpochChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let brown : Ir.Color := { r := 128, g := 64, b := 0 }
  for body in [true, false] do
    let name := if body then "body exit" else "flow"
    let doc := document body
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (_, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    let leaves := htmlInks none none #[] nodes.toList
    for (marker, expected, texts) in [
        ("AFTER", brown, ["AFTER", "𝑥"]),
        ("CODEIN", brown, ["CODEIN"]),
        ("OUTSIDE", brown, ["OUTSIDE", "𝑦"]),
        ("CODEOUT", brown, ["CODEOUT"]),
        ("DEFAULT", Ir.Color.black, ["DEFAULT", "𝑧"]),
        ("CODEDEFAULT", Ir.Color.black, ["CODEDEFAULT"])] do
      let pdf := epochLineForeground out marker
      check ref s!"palette text epoch/{name}: layout {marker}"
        (pdf == some expected)
      for text in texts do
        let ink := leaves.filter (·.text == text)
        check ref s!"palette text epoch/{name}: HTML {text} agrees with layout"
          (ink.size == 1 && pdf.isSome && ink.all fun leaf =>
            leaf.color == pdf.map (·.css))
    let before := if body then "#004080" else "#101010"
    check ref s!"palette text epoch/{name}: earlier layout ink survives"
      ((epochLineForeground out "BEFORE").map (·.css) == some before)
  containerEpochChecks ref fonts

end Tests.PaletteTextEpoch
