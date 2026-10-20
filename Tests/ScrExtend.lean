module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.ScrExtend

/-- How far below the line holding `Alpha` the next paragraph's stands, and the first one's text. -/
private def gapOf (oneFace : Font.FontSet) (pre : String) : Option (Dim.Length × String) :=
  let ls := bodyLines (layoutOf oneFace (elabStr ("\\documentclass" ++ pre ++
    "\\begin{document}\nAlpha words.\n\nBravo.\n\\begin{itemize}\n\\item Charlie.\n\\end{itemize}\n" ++
    "\\end{document}\n")).1)
  match ls.find? (fun l => hasStr (lineText l) "Alpha"), ls.find? (fun l => hasStr (lineText l) "Charlie") with
  | some a, some c => some (c.y - a.y, lineText a)
  | _, _ => none

/-- scrextend's fontsize sets the body as a class's size option does, in the preamble by its option
or `\changefontsizes`, and a change in the body is named. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- lualatex: article with scrextend's fontsize=12pt sets lines and lists as article's 12pt option.
  let twelve := gapOf oneFace "[12pt]{article}\n"
  t s!"scrextend: its fontsize sets the 12pt body: {twelve.map (·.2)}"
    (twelve.isSome && gapOf oneFace "{article}\n\\usepackage[fontsize=12pt]{scrextend}\n" == twelve &&
      gapOf oneFace "{article}\n\\usepackage{scrextend}\n\\changefontsizes{12pt}\n" == twelve &&
      gapOf oneFace "{article}\n" != twelve)
  let (_, ds) := elabStr ("\\documentclass{article}\\usepackage{scrextend}\\begin{document}" ++
    "Alpha.\\changefontsizes{14pt}Bravo.\\end{document}")
  t "scrextend: a size changed in the body is named, never unknown"
    (ds.any (·.code == "W0104") && !ds.any (·.code == "W0301"))

end Tests.ScrExtend
