module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.LabelLines

/-- An article whose body is `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def linesOf (oneFace : Font.FontSet) (src : String) : Array Layout.LineOut :=
  bodyLines (layoutOf oneFace (elabStr src).1)

/-- The first body line holding `w`. -/
private def lineWith (ls : Array Layout.LineOut) (w : String) : Option Layout.LineOut :=
  ls.find? fun l => hasStr (lineText l) w

private def runAttr : Layout.Seg → Option Layout.Attribution
  | .run _ _ _ _ glyphs _ _ _ _ _ a => if glyphs.isEmpty then none else some a
  | _ => none

/-- An item's label shares the line of the block opening its item, as latex.ltx's `\@item` sets
its labels on that block's first line: beside a box, aligned as the box stands on its line. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- lualatex: the label at the outer margin, the inner list's first line moved by the label's
  -- width and labelsep less the description's 25pt indent, 10.2pt for Alpha, -12.3pt for A.
  for label in ["Alpha", "A"] do
    let desc := linesOf oneFace (article "" ("\\begin{description}\n\\item[" ++ label ++ "]\n" ++
      "\\begin{itemize}\n\\item Bravo words.\n\\item Charlie words.\n\\end{itemize}\n" ++
      "\\item[" ++ label ++ "] Echo words.\n\\end{description}"))
    let xAt (w : String) (c : Char) : Option Dim.Length := (lineWith desc w).bind (glyphX · c)
    t s!"labels: a description label {label} alone stands on its list's first line: {desc.map lineText}"
      (match lineWith desc "Bravo", lineWith desc "Echo", xAt "Bravo" 'B', xAt "Charlie" 'C',
          xAt "Echo" 'E' with
        | some a, some e, some b, some c, some x =>
          hasStr (lineText a) label && a.x == e.x && b - c == x - e.x - Dim.pt 25
        | _, _, _, _, _ => false)
  -- lualatex: an inner description's label a labelsep past the outer one's end, as text runs in.
  let nested := linesOf oneFace (article "" ("\\begin{description}\n\\item[Alpha]\n" ++
    "\\begin{description}\n\\item[Bravo] Charlie words.\n\\end{description}\n" ++
    "\\item[Alpha] Bravo words.\n\\end{description}"))
  t s!"labels: a description in a description runs its label in after the outer one: {nested.map lineText}"
    (match nested.toList with
      | [l, r] => hasStr (lineText l) "Charlie" && glyphX l 'B' == glyphX r 'B'
      | _ => false)
  -- lualatex: a list's box in a label's chain stands past both labels.
  let chain := linesOf oneFace (article "" ("\\begin{description}\n\\item[Alpha]\n" ++
    "\\begin{itemize}\n\\item \\begin{tabular}{@{}l@{}}Kilo\\end{tabular}\n\\item Lima.\n" ++
    "\\end{itemize}\n\\item[Alpha] Echo words.\n\\end{description}"))
  t s!"labels: a box after two labels stands past both: {chain.map lineText}"
    (match lineWith chain "Kilo", lineWith chain "Lima", lineWith chain "Echo" with
      | some k, some l, some e =>
        match glyphX k 'K', glyphX l 'L', glyphX e 'E' with
        | some kx, some lx, some ex => kx - lx == ex - e.x - Dim.pt 25
        | _, _, _ => false
      | _, _, _ => false)
  for (what, opener) in [("a quote", "\\begin{quote}Bravo words.\\end{quote}"),
      ("a verbatim", "\\begin{verbatim}\nbravo = 1\n\\end{verbatim}")] do
    let ls := linesOf oneFace (article "" ("\\begin{description}\n\\item[Alpha]\n" ++ opener ++
      "\n\\item[Delta] Echo words.\n\\end{description}"))
    t s!"labels: a description label alone stands on {what}'s first line: {ls.map lineText}"
      (match lineWith ls "Alpha", lineWith ls "Delta" with
        | some a, some d => hasStr (lineText a) "ravo" && a.x == d.x
        | _, _ => false)
  -- lualatex: the bullet on the first code line.
  let listing := linesOf oneFace (article "\\usepackage{listings}\n" ("\\begin{itemize}\n\\item " ++
    "\\begin{lstlisting}\nalpha = 1\nbravo = 2\n\\end{lstlisting}\n\\end{itemize}"))
  t s!"labels: a listing opening an item sets the bullet on its first line: {listing.map lineText}"
    (listing.any fun l => hasStr (lineText l) "•" && hasStr (lineText l) "alpha")
  -- lualatex: the bullet centred on a tabular, on a top-aligned minipage's first line.
  let boxed := linesOf oneFace (article "" ("\\begin{itemize}\n\\item \\begin{tabular}{l}Foxtrot\\\\ " ++
    "Golf\\end{tabular}\n\\item \\begin{minipage}[t]{3cm}Hotel words\\\\ India\\end{minipage}\n" ++
    "\\item \\parbox{3cm}{Juliet words\\\\ Kilo\\\\ Lima}\n\\end{itemize}"))
  let bullets := boxed.filter fun l => (lineText l).trimAscii.toString == "•"
  t s!"labels: a box opening an item stands beside its bullet: {boxed.map lineText}"
    (match bullets.toList, lineWith boxed "Foxtrot", lineWith boxed "Golf", lineWith boxed "Hotel",
        lineWith boxed "Kilo" with
      | [b1, b2, b3], some f, some g, some h, some k =>
        (b1.y - (f.y + g.y) / 2).abs ≤ Dim.pt 3 / 2 && b2.y == h.y && b3.y == k.y
      | _, _, _, _, _ => false)
  -- A declared label is the item's text, so its ink is its own leaf's wherever its line stands.
  let lone := linesOf oneFace (article "" ("\\begin{enumerate}\n\\item[y)] \\begin{enumerate}\n" ++
    "\\item Kilo.\n\\end{enumerate}\n\\end{enumerate}"))
  t s!"labels: a lone label's ink is its leaf's: {lone.map lineText}"
    (match lone[0]? with
      | some l => match (l.segs.filterMap runAttr)[0]? with
        | some (Layout.Attribution.leaf _) => hasStr (lineText l) "y)"
        | _ => false
      | none => false)
  -- An ordered list's labelled item counts nothing, in the twin as on the page.
  let (odoc, _) := elabStr (article "" ("\\begin{enumerate}\n\\item Alpha.\n\\item[x)] Bravo.\n" ++
    "\\item Charlie.\n\\end{enumerate}"))
  let md := MarkdownDoc.emit odoc
  t s!"labels: the twin resumes an ordered list's numbering past a labelled item: {md}"
    (hasStr md "1. Alpha.\n* x) Bravo.\n<!-- -->\n2. Charlie.")
  -- A browser wraps beside an inline box, where TeX's empty box joins its neighbours.
  let (bdoc, _) := elabStr (article "" "Alpha\\mbox{}bravo.\n\n\\begin{itemize}\\item \\mbox{}\\end{itemize}")
  let html := (HtmlDoc.emit {} bdoc).1
  t "labels: the web page joins the words an empty box stands between, and keeps a lone one"
    (hasStr html "Alphabravo." && hasStr html "display:inline-block")
  let (wdoc, _) := elabStr (article "" ("\\begin{itemize}\n\\item[(iii)] Hotel.\n" ++
    "\\item[WWWWWW] India.\n\\end{itemize}"))
  let whtml := (HtmlDoc.emit { fonts := some oneFace } wdoc).1
  t "labels: the web page hangs a label its margin holds and runs in one wider"
    (hasStr whtml "<li class=\"labelled\"><span class=\"u-item-label\">(iii)</span>" &&
      hasStr whtml "<li class=\"labelled run-in\"><span class=\"u-item-label\">WWWWWW</span>")
  -- lualatex: \KOMAoptions{fontsize=12pt} sets the 12pt body, its lines 14.5pt apart.
  let koma (pre : String) : Option Dim.Length :=
    let ls := linesOf oneFace ("\\documentclass" ++ pre ++ "\\begin{document}\nAlpha.\n\nBravo.\n" ++
      "\\end{document}\n")
    match lineWith ls "Alpha", lineWith ls "Bravo" with
    | some a, some b => some (b.y - a.y)
    | _, _ => none
  t s!"labels: KOMA-Script's fontsize set after the class sets the body as the class option does"
    (koma "{scrartcl}\n\\KOMAoptions{fontsize=12pt}\n" == koma "[fontsize=12pt]{scrartcl}\n" &&
      koma "{scrartcl}\n\\KOMAoption{fontsize}{12pt}\n" == koma "[fontsize=12pt]{scrartcl}\n" &&
      koma "{scrartcl}\n\\KOMAoptions{fontsize=12pt}\n" != koma "{scrartcl}\n")

end Tests.LabelLines
