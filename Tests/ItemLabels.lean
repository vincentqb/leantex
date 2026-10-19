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

/-- The first shipped line holding `w`. -/
private def lineOf (ls : Array Layout.LineOut) (w : String) : Option Layout.LineOut :=
  ls.find? fun l => hasStr (lineText l) w

/-- A paragraph column's cell sets its paragraphs and lists as blocks, a list's lines hanging a
leftmargin in, and the first list in a cell spends no `\topsep`, as a minipage's does (latex.ltx
`\@minipagetrue`). -/
def cellChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := article ("\\begin{tabular}{p{4cm}l}\nLead words.\n\\begin{itemize}\n" ++
    "\\item Alpha words long enough to wrap onto a second line in the cell\n\\item Beta\n" ++
    "\\end{itemize}\nTail words. & Xray \\\\\n\\begin{enumerate}\n\\item Yankee\n" ++
    "\\end{enumerate} & Zulu \\\\\nFirst para.\n\nSecond para. & Quebec \\\\\n\\end{tabular}")
  let (doc, ds) := elabStr src
  t "cells: a list in a paragraph column's cell ships with no error"
    (ds.all (·.severity != .error))
  let ls := bodyLines (layoutOf oneFace doc)
  let at? (w : String) : Option Dim.Length := (lineOf ls w).map (·.y)
  let wrapped := (ls.findIdx? fun l => hasStr (lineText l) "Alpha").bind fun i => ls[i + 1]?
  t s!"cells: an item marks its first line and its wrapped lines hang at its text: {ls.map lineText}"
    (match lineOf ls "Alpha", lineOf ls "Lead", wrapped with
      | some a, some lead, some w =>
        (lineText a).startsWith "•" && !(lineText w).startsWith "•" &&
        (match glyphX a 'A', glyphX lead 'L', (lineText w).toList.head?.bind (glyphX w ·) with
          | some ax, some lx, some wx => lx + Dim.pt 20 ≤ ax && (ax - wx).abs ≤ Dim.pt 1
          | _, _, _ => false)
      | _, _, _ => false)
  t "cells: a list after text in its paragraph spends its topsep alone, above and below"
    (match at? "Lead", at? "Alpha", at? "Beta", at? "Tail" with
      | some l, some a, some b, some tl => a - l == tl - b
      | _, _, _, _ => false)
  t "cells: a list opening a cell stands on its row's baseline"
    (at? "Yankee" == at? "Zulu" && (at? "Yankee").isSome)
  t "cells: a paragraph break in a cell opens a line of its own"
    (match at? "First", at? "Second", at? "Quebec" with
      | some f, some s, some q => f < s && f == q
      | _, _, _ => false)
  let html := (HtmlDoc.emit {} doc).1
  let cellsHtml := (html.splitOn "<td").drop 1 |>.map fun c => (c.splitOn "</td>").headD ""
  t "cells: the web page sets the list inside its cell"
    (cellsHtml.any (hasStr · "<ul") && cellsHtml.any (hasStr · "<ol"))
  let box (body : String) : Option Dim.Length :=
    yOf oneFace (article ("Lead words.\n\n\\noindent\\begin{minipage}{4cm}\n" ++ body ++
      "\n\\end{minipage}")) "Kilo"
  t "lists: a list opening a minipage spends no topsep"
    (box "\\begin{itemize}\n\\item Kilo\n\\end{itemize}" == box "Kilo" && (box "Kilo").isSome)
  -- A label moves no ink: one before the list leaves the box's top where it is, where LaTeX's
  -- `\label` ends `\@minipagetrue` (alignment: the first line stands at the box's top).
  t "lists: a label before a minipage's first list leaves its top as it is"
    (box "\\label{x}\n\\begin{itemize}\n\\item Kilo\n\\end{itemize}" == box "Kilo")
  -- A parbox's list opens at its top as a minipage's does, where LaTeX's `\@iiiparbox` spends the
  -- topsep (alignment: the first line stands at the box's top).
  let parbox (body : String) : Option Dim.Length :=
    yOf oneFace (article ("Lead words.\n\n\\noindent\\parbox[t]{4cm}{" ++ body ++ "}")) "Kilo"
  t "lists: a list opening a parbox stands at its top, as a minipage's does"
    (parbox "\\begin{itemize}\\item Kilo\\end{itemize}" == parbox "Kilo" && (parbox "Kilo").isSome)
  let captioned (object : String) : Option Dim.Length :=
    let src := article ("Lead words.\n\n\\begin{table}[h]\n\\caption{Sierra.}\n" ++ object ++
      "\n\\end{table}\n\nTango words.")
    match yOf oneFace src "Sierra", yOf oneFace src "Kilo" with
    | some c, some k => some (k - c)
    | _, _ => none
  -- lualatex sets the item 21.9pt below the caption's baseline.
  t "floats: a list after a caption above its object spends its topsep"
    (match captioned "\\begin{itemize}\\item Kilo\\end{itemize}" with
      | some l => Dim.pt 21 ≤ l
      | none => false)
  let deck := "\\documentclass{beamer}\n\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{columns}[T]\n\\begin{column}{0.4\\textwidth}\n\\begin{itemize}\\item Kilo\n" ++
    "\\end{itemize}\n\\end{column}\n\\begin{column}{0.4\\textwidth}\nMike words.\n" ++
    "\\end{column}\n\\end{columns}\n\\end{frame}\n\\end{document}\n"
  t "lists: a list opening a beamer column spends beamer's topsep, the column no minipage's top"
    (match yOf oneFace deck "Mike", yOf oneFace deck "Kilo" with
      | some m, some k => m + Dim.pt 2 ≤ k
      | _, _ => false)
  let scopedSrc := article ("\\begin{tabular}{p{5cm}l}\n\\bfseries Kilo one.\n\nKilo two. & x\\\\\n" ++
    "\\multicolumn{2}{p{8cm}}{Mike lead \\begin{itemize}\\item Mike item\\end{itemize}}\\\\\n" ++
    "\\end{tabular}\n\nPlain words.")
  let (sd, sds) := elabStr scopedSrc
  let sl := bodyLines (layoutOf oneFace sd)
  let sh := (HtmlDoc.emit {} sd).1
  t "cells: a declaration reaches the end of its cell, across a paragraph break"
    (hasStr sh "<p><strong>Kilo one.</strong></p><p><strong>Kilo two.</strong></p>" &&
      !hasStr sh "<strong>Plain")
  let grouped := (HtmlDoc.emit {} (elabStr (article ("\\begin{tabular}{p{5cm}l}\n" ++
    "{\\bfseries Mike \\begin{itemize}\\item Oscar\\end{itemize} more} after & x\\\\\n" ++
    "plain \\bfseries mid\\par next & y\\\\\n\\multicolumn{2}{p{5cm}}{Papa\\par Quebec}\\\\\n" ++
    "\\end{tabular}"))).1).1
  t "cells: a group's declarations end with the group, its text running on after it"
    (hasStr grouped "<li><strong>Oscar</strong></li>" &&
      hasStr grouped "<p><strong>more</strong> after</p>")
  t "cells: a declaration inside a paragraph reaches the paragraphs after it"
    (hasStr grouped "<p><strong>next</strong></p>")
  t "cells: a paragraph break in a spanning cell's text opens a paragraph"
    (hasStr grouped "<p>Papa</p><p>Quebec</p>")
  t "cells: a list in a spanning paragraph cell ships, its item marked"
    (sds.all (·.severity != .error) &&
      (lineOf sl "Mike item").any fun l => (lineText l).startsWith "•")
  let strutted (cell : String) : Option Dim.Length :=
    let src := article ("\\begin{tabular}{p{5cm}}\n\\hline " ++ cell ++ " \\\\ \\hline nox \\\\ \\hline\n" ++
      "\\end{tabular}")
    let ls := bodyLines (layoutOf oneFace (elabStr src).1)
    match (ls.filter fun l => hasStr (lineText l) "ace").back?, lineOf ls "nox" with
    | some a, some n => some (n.y - a.y)
    | _, _ => none
  t "cells: a cell of paragraphs stands on the row's strut, as one paragraph does"
    (strutted "ace\n\nace" == strutted "ace" && (strutted "ace").isSome)
  let tw := MarkdownDoc.emit doc
  t s!"cells: the twin sets a cell's paragraphs and items over hard breaks: {tw}"
    (hasStr tw "Lead words.<br>• Alpha words" && hasStr tw "<br>• Beta" &&
      (elabMd tw).2.all (·.severity != .error))
  t "cells: the web page zeroes a cell's paragraph gap"
    (hasStr html ":where(:is(td, th) > *) { --parskip: 0rem; }")

/-- The sizes of a line's glyph runs, in order. -/
private def runSizes (l : Layout.LineOut) : Array Dim.Length :=
  l.segs.filterMap fun
    | .run _ _ _ _ glyphs size .. => if glyphs.isEmpty then none else some size
    | _ => none

/-- A list opening in `\small` spaces as size10.clo's `\small` `\@listi`, its marker set at the
item's size; a trivlist's items stand `\itemsep` apart; an abstract leads at `\small`'s
baselineskip; a center's close after its caption stands below the caption. -/
def itemSpaceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pitch (src a b : String) : Option Dim.Length :=
    match yOf oneFace src a, yOf oneFace src b with
    | some x, some y => some (y - x)
    | _, _ => none
  let small := article "{\\small\n\\begin{itemize}\n\\item Kilo\n\\item Lima\n\\end{itemize}\n\\par}"
  t s!"lists: a small list's items stand 15pt apart, the small \\@listi's: {(pitch small "Kilo" "Lima").map (·.toBpString)}"
    (pitch small "Kilo" "Lima" == some (Dim.pt 15))
  t "lists: a small list's marker sets at its item's size"
    ((bodyLines (layoutOf oneFace (elabStr small).1)).all fun l =>
      let ss := runSizes l
      ss.all (· == (ss[0]?.getD 0)))
  let triv := article "Mike.\n\\begin{trivlist}\n\\item Kilo\n\\item Lima\n\\end{trivlist}\nOscar."
  t s!"trivlist: items stand an itemsep apart: {(pitch triv "Kilo" "Lima").map (·.toBpString)}"
    (pitch triv "Kilo" "Lima" == some (Dim.pt 16))
  let abs := article ("\\begin{abstract}\nKilo words " ++
    String.join (List.replicate 40 "lima words ") ++ "\n\\end{abstract}")
  let absLines := (bodyLines (layoutOf oneFace (elabStr abs).1)).filter fun l =>
    hasStr (lineText l) "lima"
  t "abstract: its lines lead at the small baselineskip, 11pt"
    (match absLines[0]?, absLines[1]? with
      | some a, some b => b.y - a.y == Dim.pt 11
      | _, _ => false)
  let cap (opener closer : String) : Option Dim.Length :=
    pitch (article ("Mike.\n\n\\begin{figure}[h]\n" ++ opener ++ "\\rule{2cm}{1cm}\n" ++
      "\\caption{Kilo.}\n" ++ closer ++ "\\end{figure}\n\nLima words.")) "Kilo" "Lima"
  t "floats: a center's close after its caption stands below the caption"
    (match cap "\\begin{center}\n" "\\end{center}\n", cap "\\centering\n" "" with
      | some c, some d => d + Dim.pt 8 ≤ c
      | _, _ => false)
  -- lualatex sets each of these lines 17.9pt below the one before.
  let parskipped := "\\documentclass{article}\n\\usepackage{parskip}\n\\begin{document}\nMike.\n\n" ++
    "\\begin{itemize}\n\\item Kilo\n\\item Lima\n\\end{itemize}\n\nNovember.\n\n" ++
    "\\begin{center}\nOscar.\n\\end{center}\n\nPapa.\n\\end{document}\n"
  let pitches := [("Mike", "Kilo"), ("Kilo", "Lima"), ("Lima", "November"), ("November", "Oscar"),
    ("Oscar", "Papa")].map fun (a, b) => pitch parskipped a b
  t s!"lists: the parskip package's lists and trivlists stand a parskip apart: {pitches.map (·.map (·.toBpString))}"
    (pitches.all (· == some (Dim.pt 18)))
  -- lualatex: items 12pt apart, the list 20pt below its lead line.
  let tight := article ("\\providecommand{\\tightlist}{\\setlength{\\itemsep}{0pt}" ++
    "\\setlength{\\parskip}{0pt}}\nMike.\n\\begin{itemize}\\tightlist\\item Kilo\\item Lima\\end{itemize}")
  t s!"lists: a body's lengths set before its first item space its items: {(pitch tight "Kilo" "Lima").map (·.toBpString)}"
    (pitch tight "Kilo" "Lima" == some (Dim.pt 12) && pitch tight "Mike" "Kilo" == some (Dim.pt 20))
  -- lualatex: each list's items 11.95pt apart, a nested one's too, and a center after the list as
  -- far below it as without the lengths.
  let tl := "\\providecommand{\\tightlist}{\\setlength{\\itemsep}{0pt}\\setlength{\\parskip}{0pt}}\n"
  let twice := article (tl ++ "Mike.\n\\begin{itemize}\\tightlist\\item Kilo\\item Lima\\end{itemize}\n" ++
    "\\begin{itemize}\\tightlist\\item November\\item Oscar\n\\begin{itemize}\\tightlist\\item Papa" ++
    "\\item Quebec\\end{itemize}\\end{itemize}")
  t s!"lists: every list's own body lengths space its items, nested or after another: {[pitch twice "November" "Oscar", pitch twice "Papa" "Quebec"].map (·.map (·.toBpString))}"
    (pitch twice "November" "Oscar" == some (Dim.pt 12) && pitch twice "Papa" "Quebec" == some (Dim.pt 12))
  let leak (lead : String) : String := article ("Mike.\n\\begin{itemize}" ++ lead ++
    "\\item Kilo\\end{itemize}\n\\begin{center}\nLima\n\\end{center}")
  t "lists: a list body's lengths end with the list"
    (pitch (leak "\\setlength{\\topsep}{30pt}\\setlength{\\itemsep}{30pt}") "Kilo" "Lima" ==
      pitch (leak "") "Kilo" "Lima" && (pitch (leak "") "Kilo" "Lima").isSome)
  let before (opener closer : String) : Option Dim.Length :=
    pitch (article ("Mike.\n\n\\begin{figure}[h]\n" ++ opener ++ "\\rule{2cm}{1cm}\n" ++ closer ++
      "\\caption{Kilo.}\n\\end{figure}\n\nLima words.")) "Mike" "Kilo"
  t "floats: a center closing before its caption spends its close above the caption"
    (match before "\\begin{center}\n" "\\end{center}\n", before "\\centering\n" "" with
      | some c, some d => d + Dim.pt 8 ≤ c
      | _, _ => false)
  -- lualatex: a center inside a list under the trivlist scope's topsep of 20pt stands 35.9pt below.
  let trivScoped (pre : String) : String :=
    "\\documentclass{article}\n\\usepackage{enumitem}\n" ++ pre ++ "\\begin{document}\nMike.\n" ++
      "\\begin{itemize}\n\\item Kilo\n\\begin{center}\nLima\n\\end{center}\n\\end{itemize}\n\\end{document}\n"
  t "lists: the trivlist scope's topsep spaces a center inside a list"
    (match pitch (trivScoped "\\setlist[trivlist]{topsep=20pt}\n") "Kilo" "Lima", pitch (trivScoped "") "Kilo" "Lima" with
      | some s, some d => d + Dim.pt 10 ≤ s
      | _, _ => false)
  -- lualatex: under the parskip package a quote's lines stand 17.93pt from the text around it.
  let quoted := "\\documentclass{article}\n\\usepackage{parskip}\n\\begin{document}\nMike.\n\n" ++
    "\\begin{quote}\nKilo\n\\end{quote}\n\nLima.\n\\end{document}\n"
  t s!"lists: the parskip package's quote stands a parskip apart: {(pitch quoted "Mike" "Kilo").map (·.toBpString)}"
    (pitch quoted "Mike" "Kilo" == some (Dim.pt 18) && pitch quoted "Kilo" "Lima" == some (Dim.pt 18))
  let tightDesc := article (tl ++ "Mike.\n\\begin{description}\n\\tightlist\n\\item[Kilo] Lima words.\n" ++
    "\\item[November] Oscar words.\n\\end{description}\nPapa.")
  t "lists: a tight description's label runs into its item's text"
    (yOf oneFace tightDesc "Kilo" == yOf oneFace tightDesc "Lima" &&
      pitch tightDesc "Kilo" "November" == some (Dim.pt 12) && pitch tightDesc "Mike" "Kilo" == some (Dim.pt 20))

end Tests.ItemLabels
