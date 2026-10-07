import LeanTex.Core.Font
import LeanTex.Core.Elab
import LeanTex.Core.Layout
import LeanTex.Core.HtmlDoc
import Tests.Support

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

-- Inspect inherited concrete paint in the typed artifact. A custom property
-- alone does not repaint an inherited CSS color; the browser witness checks
-- that distinction against the same layout runs.
mutual
  private def htmlInks (color : Option String) (out : Array Ink) :
      List Html.Node → Array Ink
    | [] => out
    | node :: rest => htmlInks color (htmlInk color out node) rest
  private def htmlInk (color : Option String) (out : Array Ink) :
      Html.Node → Array Ink
    | .text text => out.push { text := text.trimAscii.toString, color }
    | .elem _ attrs kids =>
      let style := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      htmlInks ((property style "color").or color) out kids.toList
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
    let leaves := htmlInks none #[] nodes.toList
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

end Tests.PaletteTextEpoch
