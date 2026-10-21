module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim

/-! enumitem's inline lists and series, csquotes' displayed quotation, colortbl's and multirow's
cell commands, and the appendix package's titled sections, as lualatex sets them. -/

/-- Every body line's text and left edge. -/
private def lineEdges (fonts : Font.FontSet) (src : String) : Array (String × Length) :=
  (bodyLines (layoutOf fonts (elabStr src).1)).map fun l => (lineText l, l.x)

/-- Each list, quotation, cell and appendix construct sets what lualatex sets, and a cell command
whose effect is not drawn prints none of its configuration, named once. -/
def listTablePackageChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (pre body : String) : String := pageTextOf fonts (dvDoc pre body)
  let inline := page "\\usepackage[inline]{enumitem}\n"
    "Steps: \\begin{enumerate*}[label=(\\alph*)] \\item mix, \\item bake, \\item serve.\\end{enumerate*} Done."
  t "an inline enumerate sets its items in the running line after their labels"
    (inline == "Steps: (a) mix, (b) bake, (c) serve. Done.")
  t "an inline itemize sets a bullet before each item, an explicit label in its place"
    (page "\\usepackage[inline]{enumitem}\n"
      "Kinds: \\begin{itemize*}\\item red \\item[--] blue\\end{itemize*}." == "Kinds: • red – blue.")
  let series := page "\\usepackage{enumitem}\n"
    ("\\begin{enumerate}[series=steps, label=S\\arabic*.]\n\\item One\n\\item Two\n\\end{enumerate}\n" ++
     "Between.\n\\begin{enumerate}[resume=steps, label=S\\arabic*.]\n\\item Three\n\\end{enumerate}\n" ++
     "\\begin{enumerate}[resume=steps, label=S\\arabic*.]\n\\item Four\n\\end{enumerate}")
  t "a list resuming a series continues the number the series' last list ended at"
    (hasStr series "S1. One" && hasStr series "S2. Two" && hasStr series "S3. Three" &&
      hasStr series "S4. Four")
  t "a displayed quotation is set as a quotation is"
    (lineEdges fonts (dvDoc "\\usepackage{csquotes}\n"
        "Before.\n\\begin{displayquote}Quoted words stand indented.\\end{displayquote}\nAfter.") ==
      lineEdges fonts (dvDoc "\\usepackage{csquotes}\n"
        "Before.\n\\begin{quote}Quoted words stand indented.\\end{quote}\nAfter."))
  let tableSrc := dvDoc "\\usepackage[table]{xcolor}\n\\usepackage{multirow}\n"
    ("\\begin{tabular}{ll}\n\\rowcolor{gray!10} Head & Cell \\\\\n\\cellcolor{blue!15}Alpha & Beta \\\\\n" ++
     "\\multirow{2}{*}{Gamma} & Delta \\\\\n & Epsilon\n\\end{tabular}")
  let tableText := pageTextOf fonts tableSrc
  let tableDs := (elabStr tableSrc).2
  t "a cell command sets its cell's text and none of its colour or span"
    (hasStr tableText "Alpha" && hasStr tableText "Gamma" && !hasStr tableText "blue" &&
      !hasStr tableText "gray" && !hasStr tableText "*" && !hasStr tableText "15")
  t "each undrawn cell command is named once"
    (["\\cellcolor", "\\rowcolor", "\\multirow"].all fun c =>
      (tableDs.filter fun d => d.code == "W0104" && hasStr d.message c).size == 1)
  let appendixBody := "\\begin{appendices}\n\\section{Tools}\\label{a:tools}\nSee \\ref{a:tools}.\n" ++
    "\\end{appendices}"
  let titled := page "\\usepackage[title]{appendix}\n" appendixBody
  t "the appendix package's title option heads each appendix with its name, its reference the letter"
    (hasStr titled "Appendix ATools" && hasStr titled "See A." &&
      !hasStr (page "\\usepackage{appendix}\n" appendixBody) "Appendix")
