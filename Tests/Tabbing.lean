module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.Tabbing

private def linesOf (oneFace : Font.FontSet) (body : String) : Array Layout.LineOut :=
  bodyLines (layoutOf oneFace (elabStr ("\\documentclass{article}\n\\begin{document}\nLead.\n\n" ++
    body ++ "\nTail.\n\\end{document}\n")).1)

/-- The x of the first glyph of the first word `w` on the line holding it. -/
private def xOf (ls : Array Layout.LineOut) (w : String) : Option Dim.Length :=
  (ls.find? fun l => hasStr (lineText l) w).bind fun l => glyphX l w.front

/-- A tabbing's lines set their entries at the tab stops its lines set, a `\kill` line's widths
counting and its text set nowhere, `\+` and `\-` moving the lines after them a stop in and out, as
lualatex sets them. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let rows := "Alpha \\> one \\> first\\\\\nBeta \\> two \\> second\\\\\n\\> only \\> third\\\\\n" ++
    "Gamma \\+\\\\\nindent \\> next\\\\\nmore \\-\\\\\nback \\> end\n\\end{tabbing}"
  let ls := linesOf oneFace ("\\begin{tabbing}\nVariable name wide \\= Value given \\= Note \\kill\n" ++ rows)
  let bare := linesOf oneFace ("\\begin{tabbing}\n" ++ rows)
  let (_, ds) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\begin{tabbing}\n" ++
    "Variable \\= Value \\kill\nAlpha \\> one\n\\end{tabbing}\n\\end{document}\n")
  t s!"tabbing: entries stand at their stops: {ls.map lineText}"
    (xOf ls "one" == xOf ls "two" && xOf ls "two" == xOf ls "only" &&
      xOf ls "first" == xOf ls "second" && xOf ls "second" == xOf ls "third" &&
      xOf ls "Alpha" == xOf ls "Lead" && xOf ls "indent" == xOf ls "one" &&
      xOf ls "back" == xOf ls "Alpha" && xOf ls "end" == xOf ls "one")
  t "tabbing: a kill line's widths set the stops, its text nowhere"
    (!ls.any (fun l => hasStr (lineText l) "Variable") &&
      (match xOf ls "one", xOf bare "one" with
        | some a, some b => b < a
        | _, _ => false))
  t "tabbing: the environment and its commands are known" (!ds.any fun d => d.code == "W0302" || d.code == "W0301")

end Tests.Tabbing
