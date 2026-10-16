module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ItemLabels

/-- An article with `pre` in its preamble, three nested itemize levels, and `after` past them. -/
private def labelDoc (pre : String) (after : String := "") : String :=
  "\\documentclass{article}\n\\usepackage{xcolor}\n" ++ pre ++ "\\begin{document}\n" ++
    "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Beta\n\\begin{itemize}\n\\item Gamma\n" ++
    "\\end{itemize}\n\\end{itemize}\n\\end{itemize}\n" ++ after ++ "\\end{document}\n"

/-- Each body line's leading run: its glyphs, its colour and whether it is set in a bold face. -/
private def markers (oneFace : Font.FontSet) (doc : Ir.Doc) : Array (String × Ir.Color) :=
  (bodyLines (layoutOf oneFace doc)).filterMap fun l => match l.segs[0]? with
    | some (Layout.Seg.run _ c _ _ glyphs _ _ _ _ _ _) =>
      some (String.ofList (glyphs.toList.map (·.2.1)), c)
    | _ => none

/-- A class label a preamble redefines (`\labelitemi`…) marks its itemize level in both backends,
its colour and glyph as written, under a declared level style; one redefined in the body is named. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let red := ((default : Ir.Palette).resolve "red").getD Ir.Color.black
  let (doc, ds) := elabStr (labelDoc ("\\renewcommand{\\labelitemi}{\\textcolor{red}{\\textbullet}}\n" ++
    "\\renewcommand{\\labelitemii}{\\textendash}\n"))
  let ms := markers oneFace doc
  t s!"the page marks the first level in the redefined label's red bullet, the second in a dash: {ms.map (·.1)}"
    ((ms[0]?.any fun (g, c) => g == "•" && c == red) && (ms[1]?.any (·.1 == "–")) &&
      (ms[2]?.any (·.1 != "–")))
  t "the redefinitions raise nothing" (ds.all (·.severity != .warning))
  let html := (HtmlDoc.emit {} doc).1
  t "the web page marks the first level in red and the second in a dash"
    (hasStr html "ul > li::marker { content: \"•  \"; color: " && hasStr html "ff0000" &&
      hasStr html "ul ul > li::marker { content: \"–  \"; }")
  let (styled, _) := elabStr (labelDoc ("\\usepackage{enumitem}\n\\setlist[itemize]{label=+}\n" ++
    "\\renewcommand{\\labelitemi}{\\textcolor{red}{\\textbullet}}\n"))
  t "a declared level style marks the level over the redefined label"
    ((markers oneFace styled)[0]?.any (·.1 == "+"))
  let (late, lateDs) := elabStr (labelDoc "" "\\renewcommand{\\labelitemi}{\\textendash}\n")
  t "a label redefined in the body is named once and marks no list"
    ((lateDs.filter (·.code == DiagCode.W0340.code)).size == 1 &&
      (markers oneFace late)[0]?.any (·.1 == "•"))

end Tests.ItemLabels
