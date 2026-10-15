module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.NestedLedgers

/-- An itemize nested five deep, one past the four levels LaTeX's classes define. -/
private def deepList : String :=
  String.join ((List.range 5).map fun i => s!"\\begin\{itemize}\\item Kilo {i + 1} words.\n") ++
    String.join (List.replicate 5 "\\end{itemize}\n")

/-- A picture wider than any column of the probes, 9 cm across. -/
private def widePicture : String :=
  "\\begin{tikzpicture}\\draw (0,0) rectangle (9cm,1cm);\\end{tikzpicture}\n"

private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def deck (pre body : String) : String :=
  "\\documentclass{beamer}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def columns (left right : String) : String :=
  "\\begin{columns}\n\\begin{column}{0.4\\textwidth}\n" ++ left ++
    "\\end{column}\n\\begin{column}{0.4\\textwidth}\n" ++ right ++ "\\end{column}\n\\end{columns}\n"

/-- The number of the run's diagnostics coded `code`, as layout ships them. -/
private def raised (fonts : Font.FontSet) (src : String) (code : DiagCode) : Nat :=
  ((layoutOf fonts (elabStr src).1).diags.filter (·.kind == code)).size

/-- Every diagnostic a nested walk raises reaches the run once: each container sets its body
through a walk of its own, a column's and a minipage's on a ledger of their own. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let tikz := "\\usepackage{tikz}\n"
  let containers : List (String × String) :=
    [("the page itself", article "" deepList),
     ("a minipage", article "" ("\\begin{minipage}{0.6\\textwidth}\n" ++ deepList ++
        "\\end{minipage}")),
     ("two minipages, the second", article "" ("\\begin{minipage}{0.4\\textwidth}\nLima words.\n" ++
        "\\end{minipage}\\hfill\\begin{minipage}{0.4\\textwidth}\n" ++ deepList ++
        "\\end{minipage}")),
     ("a quote", article "" ("\\begin{quote}\n" ++ deepList ++ "\\end{quote}")),
     ("a centred scope", article "" ("\\begin{center}\n" ++ deepList ++ "\\end{center}")),
     ("an abstract", article "" ("\\begin{abstract}\n" ++ deepList ++ "\\end{abstract}")),
     ("a figure", article "" ("\\begin{figure}[h]\n" ++ deepList ++
        "\\caption{Kilo caption.}\n\\end{figure}")),
     ("an enumerate item", article "" ("\\begin{enumerate}\\item Lima words.\n" ++ deepList ++
        "\\end{enumerate}")),
     ("a frame", deck "" ("\\begin{frame}{Kilo}\n" ++ deepList ++ "\\end{frame}")),
     ("a block", deck "" ("\\begin{frame}{Kilo}\n\\begin{block}{Lima}\n" ++ deepList ++
        "\\end{block}\n\\end{frame}")),
     ("a beamer column", deck "" ("\\begin{frame}{Kilo}\n" ++ columns "Lima words.\n" deepList ++
        "\\end{frame}"))]
  for (name, src) in containers do
    t s!"nested ledgers: a list nested five deep in {name} is named once (W0010)"
      (raised oneFace src .W0010 == 1)
  t "nested ledgers: a picture wider than its beamer column is named (W0335)"
    (raised oneFace (deck tikz ("\\begin{frame}{Kilo}\n" ++ columns widePicture "Lima words.\n" ++
      "\\end{frame}")) .W0335 == 1)
  t "nested ledgers: a picture wider than its minipage is named (W0335)"
    (raised oneFace (article tikz ("\\begin{minipage}{0.3\\textwidth}\n" ++ widePicture ++
      "\\end{minipage}")) .W0335 == 1)
  let navved := article ""
    ("\\begin{minipage}{0.5\\textwidth}\n\\begin{nav}\\href{https://example.org}{Kilo}" ++
      "\\end{nav}\nLima words.\n\\end{minipage}")
  t "nested ledgers: a menu inside a minipage reaches the outline"
    ((layoutOf oneFace (elabStr navved).1).outline.map (·.title) == #["Kilo"])

end Tests.NestedLedgers
