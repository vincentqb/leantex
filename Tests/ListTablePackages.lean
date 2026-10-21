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
  t "an inline list joins its last item by its itemjoin*, the others by its itemjoin"
    (page "\\usepackage{enumitem}\n"
      "\\begin{enumerate*}[itemjoin={,}, itemjoin*={, and}] \\item red \\item green \\item blue\\end{enumerate*}." ==
      "1. red,2. green, and3. blue.")
  t "an inline itemize takes its declared label"
    (page "\\usepackage{enumitem}\n" "Kinds: \\begin{itemize*}[label=+]\\item red \\item blue\\end{itemize*}." ==
      "Kinds: + red + blue.")
  t "an inline list's key the reader does not read is named once"
    (((elabStr (dvDoc "\\usepackage{enumitem}\n"
        "\\begin{enumerate*}[mode=boxed]\\item a\\end{enumerate*}")).2.filter fun d =>
        d.code == "W0104" && hasStr d.message "mode").size == 1)
  t "a starred list is no inline list unless enumitem defines one"
    (!hasStr (page "" "Kinds: \\begin{itemize*}\\item red \\item blue\\end{itemize*}.") "• red • blue")
  t "resume* continues a series, and a series on an itemize is no unread key"
    (hasStr (page "\\usepackage{enumitem}\n"
      ("\\begin{enumerate}[series=s]\n\\item One\n\\end{enumerate}\n" ++
       "\\begin{enumerate}[resume*=s]\n\\item Two\n\\end{enumerate}")) "2. Two" &&
      !(elabStr (dvDoc "\\usepackage{enumitem}\n"
        "\\begin{itemize}[series=b]\n\\item x\n\\end{itemize}")).2.any (·.code == "W0104"))
  t "a displayed quotation's citation follows it and its punctuation, in parentheses"
    (hasStr (page "\\usepackage{csquotes}\n"
      "\\begin{displayquote}[Some One][.]Quoted words\\end{displayquote}") "Quoted words. (Some One)")
  let appendixBody := "\\begin{appendices}\n\\section{Tools}\\label{a:tools}\nSee \\ref{a:tools}.\n" ++
    "\\end{appendices}"
  let titled := page "\\usepackage[title]{appendix}\n" appendixBody
  t "the appendix package's title option heads each appendix with its name, its reference the letter"
    (hasStr titled "Appendix ATools" && hasStr titled "See A." &&
      !hasStr (page "\\usepackage{appendix}\n" appendixBody) "Appendix")
  let contents := page "\\usepackage[title]{appendix}\n" ("\\tableofcontents\n" ++ appendixBody)
  t "the contents line of a titled appendix sets its bare letter"
    ((contents.splitOn "Appendix").length == 2 && hasStr contents "ContentsA Tools")
  let chaptered := pageTextOf fonts ("\\documentclass{report}\n\\usepackage[title]{appendix}\n" ++
    "\\begin{document}\n\\begin{appendices}\n\\chapter{Extra}\n\\section{More}\nx\n" ++
    "\\end{appendices}\n\\end{document}")
  t "a chapter class's appendix sections are numbered without the appendix name"
    (hasStr chaptered "A.1" && !hasStr chaptered "Appendix A.1")
