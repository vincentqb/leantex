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
its colour and glyph as written, under a declared level style; one redefined in the body is named,
one the engine cannot set leaves the class's marker, and its faces are asked for. -/
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
  let (hooked, hookedDs) := elabStr (labelDoc "\\AtBeginDocument{\\renewcommand{\\labelitemi}{\\textendash}}\n")
  t "a label a begin-document hook redefines marks every list, unnamed"
    ((markers oneFace hooked)[0]?.any (·.1 == "–") && !hookedDs.any (·.code == DiagCode.W0340.code))
  let (first, firstDs) := elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
    "\\renewcommand{\\labelitemi}{\\textendash}\nText.\n\\begin{itemize}\n\\item Alpha\n" ++
    "\\end{itemize}\n\\end{document}\n")
  t "a label the body redefines before its first list marks that list, unnamed"
    ((markers oneFace first)[1]?.any (·.1 == "–") && !firstDs.any (·.code == DiagCode.W0340.code))
  -- What a label sets is the document's text: it asks for the faces it sets in.
  let (star, _) := elabStr (labelDoc "\\renewcommand{\\labelitemi}{$\\star$}\n")
  t "a label's formula asks for the math face where the body sets none"
    (!(Layout.docMathScalars star).isEmpty && (Ir.mathFaceRequest star).isSome)
  let (mono, _) := elabStr (labelDoc "\\renewcommand{\\labelitemi}{\\texttt{>}}\n")
  t "a label in the typewriter face asks for the mono slot where the body sets none"
    ((LeanTex.Cli.SlotLoss.slotsUsed mono).contains 2)
  -- A label the engine cannot set leaves the class's marker, its loss named once.
  for (pre, label) in [("\\usepackage{pifont}\n", "\\ding{51}"), ("\\usepackage{amssymb}\n", "\\checkmark"),
      ("", "{}")] do
    let (lost, lostDs) := elabStr (labelDoc (pre ++ s!"\\renewcommand\{\\labelitemi}\{{label}}\n"))
    let named := lostDs.filter (·.subject == some "labelitem:labelitemi")
    t s!"a label of {label} the engine cannot set leaves the class's bullet, named once: {markers oneFace lost |>.map (·.1)}"
      ((markers oneFace lost)[0]?.any (·.1 == "•") && named.size == 1 &&
        named.all (·.code == DiagCode.W0331.code) && !lostDs.any (·.code == DiagCode.W0301.code))
  let (again, againDs) := elabStr (labelDoc ("\\usepackage{pifont}\n\\usepackage{enumitem}\n" ++
    "\\setlist[itemize,2]{label=\\ding{52}}\n\\renewcommand{\\labelitemi}{\\ding{51}}\n"))
  t s!"a label whose loss was named before still leaves the class's bullet: {markers oneFace again |>.map (·.1)}"
    ((markers oneFace again)[0]?.any (·.1 == "•") &&
      againDs.any (·.subject == some "labelitem:labelitemi"))
  let (_, secondDs) := elabStr (labelDoc "\\usepackage{amssymb}\n\\renewcommand{\\labelitemii}{\\checkmark}\n")
  t "a lost label's help names its own level's command"
    (secondDs.any fun d => d.subject == some "labelitem:labelitemii" &&
      (d.help.getD "").contains "\\renewcommand{\\labelitemii}")
  -- The web page carries a label's text as written, its formula as its symbol.
  let (lt, _) := elabStr (labelDoc "\\renewcommand{\\labelitemi}{\\textless/style}\n")
  let (ltHtml, ltDs) := HtmlDoc.emit {} lt
  t "a label spelling a closing style tag stays inside its CSS string"
    (!hasStr ltHtml "content: \"</style" && hasStr ltHtml "content: \"\\3c /style" &&
      ltDs.all (·.severity != .error))
  let (bullet, _) := elabStr (labelDoc "\\renewcommand{\\labelitemi}{$\\bullet$}\n")
  let (bulletHtml, bulletDs) := HtmlDoc.emit {} bullet
  t "a label's formula marks the web page in its symbol, unnamed"
    (hasStr bulletHtml "ul > li::marker { content: \"∙  \"" && !bulletDs.any (·.code == DiagCode.W0331.code))
  let (power, _) := elabStr (labelDoc "\\renewcommand{\\labelitemi}{$x^2$}\n")
  let (powerHtml, powerDs) := HtmlDoc.emit {} power
  t "a structured formula label is named on the web page, not linearized"
    (powerDs.any (·.code == DiagCode.W0331.code) && !hasStr powerHtml "ul > li::marker { content: \"(")

/-- An article whose body is `body`. -/
private def article (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

/-- The body lines' texts, words apart. -/
private def texts (oneFace : Font.FontSet) (src : String) : Array String :=
  (bodyLines (layoutOf oneFace (elabStr src).1)).map fun l =>
    " ".intercalate ((lineText l).splitOn " " |>.filter (· != ""))

/-- The baseline of the first body line holding `w`. -/
private def yOf (oneFace : Font.FontSet) (src w : String) : Option Dim.Length :=
  ((bodyLines (layoutOf oneFace (elabStr src).1)).find? fun l => hasStr (lineText l) w).map (·.y)

/-- An item's label sets on the first line its item sets, as latex.ltx's `\@item` sets its labels,
an `\item[label]`'s in the marker's place stepping no counter. -/
def openerChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (what, opener) in [("a quote", "\\begin{quote}Kilo words.\\end{quote}"),
      ("a center", "\\begin{center}Kilo words.\\end{center}"),
      ("a flushleft", "\\begin{flushleft}Kilo words.\\end{flushleft}"),
      ("a verbatim", "\\begin{verbatim}Kilo words.\\end{verbatim}")] do
    let ls := texts oneFace (article ("\\begin{itemize}\n\\item " ++ opener ++ "\n\\end{itemize}"))
    t s!"item markers: {what} opening an item sets the bullet on its first line: {ls}"
      (ls.any fun l => l.startsWith "•" && hasStr l "Kilo")
  let nested := texts oneFace (article ("\\begin{itemize}\n\\item \\begin{itemize}\n\\item " ++
    "\\begin{quote}Kilo words.\\end{quote}\n\\end{itemize}\n\\end{itemize}"))
  t s!"item markers: a quote opening an inner list's item keeps both lists' markers: {nested}"
    (nested.any fun l => l.startsWith "•" && hasStr l "–" && hasStr l "Kilo")
  -- A label no line of the opener's first block takes sets a line of its own, or passes to its list.
  let tabled := texts oneFace (article ("\\begin{itemize}\n\\item \\begin{quote}\\begin{tabular}{l}" ++
    "Kilo\\end{tabular}\\end{quote}\n\\end{itemize}"))
  t s!"item markers: a quote opening on a table sets the bullet on a line before it: {tabled}"
    (tabled[0]? == some "•" && tabled.any (hasStr · "Kilo"))
  let quoted := texts oneFace (article ("\\begin{itemize}\n\\item \\begin{quote}\\begin{itemize}\n" ++
    "\\item Kilo.\n\\end{itemize}\\end{quote}\n\\end{itemize}"))
  t s!"item markers: a quote opening on a list keeps the outer bullet on its first line: {quoted}"
    (quoted.any fun l => l.startsWith "•" && hasStr l "–" && hasStr l "Kilo")
  let lead := texts oneFace (article ("\\begin{enumerate}\n\\item[y)] \\begin{enumerate}\n" ++
    "\\item Kilo.\n\\end{enumerate}\n\\end{enumerate}"))
  t s!"item labels: a label before a list stands on the list's first line: {lead}"
    (lead == #["y) (a) Kilo."])
  let closed := texts oneFace (article ("\\begin{itemize}\n\\item \\begin{quote}\\vspace{2pt}" ++
    "\\end{quote} Kilo.\n\\item \\begin{quote}\\end{quote}\n\\end{itemize}"))
  t s!"item markers: labels an opener's end leaves waiting set a line of their own: {closed}"
    ((closed.filter (· == "•")).size == 2)
  let (tl, _) := elabStr (article "\\begin{trivlist}\n\\item[\\bfseries Lima.] Kilo.\n\\end{trivlist}")
  t "trivlist: a label's declarations stay in the label"
    (!hasStr (reprStr tl.body) "bold\" \"Kilo" && hasStr (reprStr tl.body) "Kilo")
  let empty := texts oneFace (article "\\begin{itemize}\n\\item\n\\item Kilo.\n\\end{itemize}")
  t s!"item markers: an empty item sets its bullet on a line of its own: {empty}"
    (empty[0]? == some "•" && empty[1]? == some "• Kilo.")
  let shown := texts oneFace (article "\\begin{itemize}\n\\item \\[ x = y \\]\n\\end{itemize}")
  t s!"item markers: a display opening an item follows its bullet's line: {shown}"
    (shown[0]? == some "•" && shown.size == 2)
  let boxed := texts oneFace (article ("\\begin{enumerate}\n\\item \\mbox{}\n\\begin{enumerate}\n" ++
    "\\item Kilo.\n\\end{enumerate}\n\\end{enumerate}"))
  t s!"item markers: an empty \\mbox starts the item's paragraph, its label a line apart: {boxed}"
    (boxed[0]? == some "1." && boxed[1]? == some "(a) Kilo.")
  let desc := texts oneFace (article ("\\begin{description}\n\\item[Lima] text.\n" ++
    "\\begin{itemize}\n\\item Kilo.\n\\end{itemize}\n\\end{description}"))
  t s!"item markers: an itemize in a description marks its first level: {desc}"
    (desc.any (· == "• Kilo."))
  let labels := texts oneFace (article ("\\begin{itemize}\n\\item[+] Kilo.\n\\item[] Lima.\n" ++
    "\\end{itemize}\n\\begin{enumerate}\n\\item Mike.\n\\item[a)] Oscar.\n\\item Papa.\n" ++
    "\\end{enumerate}"))
  t s!"item labels: an \\item[label] sets in the marker's place and steps no counter: {labels}"
    (labels == #["+ Kilo.", "Lima.", "1. Mike.", "a) Oscar.", "2. Papa."])
  let (deck, _) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{enumerate}\n\\item Kilo.\n\\item<2->[x] Lima.\n\\item Mike.\n\\end{enumerate}\n" ++
    "\\end{frame}\n\\end{document}\n")
  t "item labels: an overlay's item label steps no counter and drops the web marker"
    ((bodyLines (layoutOf oneFace deck)).any (fun l => hasStr (lineText l) "2. Mike.") &&
      hasStr (HtmlDoc.emit {} deck).1 "step labelled")
  let (ldoc, lds) := elabStr (article "\\begin{itemize}\n\\item[+] Kilo.\n\\end{itemize}")
  let html := (HtmlDoc.emit {} ldoc).1
  t "item labels: the web page sets the label where the marker stands, unnamed"
    (hasStr html "<li class=\"labelled\"><span class=\"u-item-label\">+</span> Kilo.</li>" &&
      hasStr html "li.labelled::marker { content: none; }" &&
      !lds.any (·.code == DiagCode.W0110.code))
  t "item labels: the twin keeps the label apart from the item's text"
    (hasStr (MarkdownDoc.emit ldoc) "- \\+ Kilo.")
  let (tdoc, tds) := elabStr (article ("Lima words.\n\\begin{trivlist}\n\\item Kilo words.\n" ++
    "\\item[Tag] Mike words.\n\\end{trivlist}\nOscar words."))
  let tl := bodyLines (layoutOf oneFace tdoc)
  let hung := fun (l : Layout.LineOut) => match l.segs[0]? with
    | some (Layout.Seg.gap w _) => w < 0
    | _ => false
  t s!"trivlist: an environment of its own, each item a flush paragraph, a label hung a labelsep: \
{tl.map lineText}"
    (tds.all (·.severity != .error) && !tds.any (·.code == DiagCode.W0302.code) &&
      (tl.map (·.x)).all (· == (tl[0]?.map (·.x)).getD 0) &&
      (tl.any fun l => hasStr (lineText l) "Tag" && hasStr (lineText l) "Mike" && hung l))
  -- A minipage sets `\@listdepth` back to zero, so its list spaces as the outermost does.
  let pitch (src : String) : Option Dim.Length :=
    match yOf oneFace src "Kilo", yOf oneFace src "Lima" with
    | some a, some b => some (b - a)
    | _, _ => none
  let inner := "\\begin{itemize}\n\\item Kilo.\n\\item Lima.\n\\end{itemize}"
  t "lists: a list in a minipage in an item spaces its items as an outermost list does"
    (pitch (article ("\\begin{itemize}\n\\item Mike.\n\\begin{minipage}{0.8\\linewidth}\n" ++
      inner ++ "\n\\end{minipage}\n\\end{itemize}")) == pitch (article inner) &&
     pitch (article ("\\begin{itemize}\n\\item Mike.\n" ++ inner ++ "\n\\end{itemize}")) !=
       pitch (article inner))
  -- A center in a float closes as a trivlist before the caption below it, as `\endtrivlist` does.
  let capGap (opener closer : String) : Option Dim.Length :=
    let src := article ("Lima words.\n\\begin{table}[h]\n" ++ opener ++
      "\\begin{tabular}{l}\nKilo\\\\\n\\end{tabular}\n" ++ closer ++
      "\\caption{Mike.}\n\\end{table}\nOscar words.")
    match yOf oneFace src "Kilo", yOf oneFace src "Mike" with
    | some a, some b => some (b - a)
    | _, _ => none
  t "floats: a center's close stands between a table and the caption after it"
    (match capGap "\\begin{center}\n" "\\end{center}\n", capGap "\\centering\n" "" with
      | some c, some d => d + Dim.pt 8 ≤ c
      | _, _ => false)

end Tests.ItemLabels
