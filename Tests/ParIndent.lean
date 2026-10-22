module

public import Tests.Support
import LeanTex.Core.Layout.Quality

public section

open LeanTex.Core

/-- Lengths print as their base-unit counts in failure messages. -/
private instance : ToString Dim.Length := ⟨reprStr⟩

/-! A standard class's paragraphs at lualatex's positions on invented probes: the class's
`\parindent`, none where LaTeX's `\@afterindentfalse`, `\@endpe` or a zero `\parindent` leaves none,
and `\parskip` 0pt plus 1pt; the web page's paragraphs indented as the PDF's. -/

namespace Tests.ParIndent

private def doc (cls pre body : String) : String :=
  s!"\\documentclass{cls}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

/-- The indent the first body line opening on `word` sets before its first glyph; `none` where no
line opens on it. -/
private def indentOf (out : Layout.Out) (word : String) : Option Dim.Length :=
  (bodyLines out).findSome? fun l =>
    if (lineInk l).startsWith word then some (lineIndent l) else none

/-- How far past the page's baselineskip each line opening on `words` stands below the one before,
in tenths of a point; `none` where a word opens no line. -/
private def gaps (oneFace : Font.FontSet) (src : String) (words : List String) : Option (List Int) := do
  let (d, _) := elabStr src
  let c := censusOf (coveredColorsOf d) (layoutOf oneFace d)
  let ys ← words.mapM (lineYOf c 0 ·)
  let bs := Ir.baselineSkipOf d.page
  return (ys.zip ys.tail).map fun (a, b) => ((b - a - bs) * 10 + Dim.pt 1 / 2) / Dim.pt 1

private def indents (oneFace : Font.FontSet) (src : String) (words : List String) :
    List (Option Dim.Length) :=
  let out := layoutOf oneFace (elabStr src).1
  words.map (indentOf out)

/-- Each web page paragraph's text and whether it opens on the page's indent. -/
private def paraWalk : Html.Walk Unit (Array (String × Bool)) where
  enter _ acc tag attrs kids :=
    if tag == "p" then
      acc.push ((nodeTextList "" kids.toList).trimAscii.toString,
        attrs.any fun (k, v) => k == "class" && hasStr v "u-indent")
    else acc

/-- Whether the web page's paragraph opening on `word` is indented; `none` where none opens on it. -/
private def htmlIndented (d : Ir.Doc) (word : String) : Option Bool :=
  ((paraWalk.list () #[] (docNodesOf d).toList).find? (·.1.startsWith word)).map (·.2)

/-- Paragraphs after a heading, a list, a display, a centred block, a verbatim, a float and a
theorem, with and without the blank line that ends the paragraph before, as lualatex sets them. -/
private def contexts : String :=
  "Alpha opens the document.\n\nBravo is the second paragraph.\n\\section{Heading}\n" ++
  "Charlie follows the heading.\n\nDelta follows Charlie.\n\\begin{itemize}\n\\item Echo item.\n\n" ++
  "Foxtrot item paragraph.\n\\end{itemize}\nGolf goes on past the list.\n\\begin{itemize}\n" ++
  "\\item Hotel item.\n\\end{itemize}\n\nIndia follows a blank line.\n\\[ x = y \\]\n" ++
  "Juliet goes on past the display.\n\\[ x = z \\]\n\nKilo follows the display's blank line.\n" ++
  "\\begin{center}\nLima centred.\n\\end{center}\nMike goes on past the centre.\n\n" ++
  "\\noindent November under noindent.\n\nOscar holds \\noindent mid-paragraph.\n" ++
  "\\begin{verbatim}\npapa\n\\end{verbatim}\nQuebec goes on past the verbatim.\n\n" ++
  "Romeo before a float\n\\begin{figure}[h]\n\\centering\n\\rule{1cm}{1cm}\n" ++
  "\\caption{Sierra caption.}\n\\end{figure}\nTango past the float lualatex keeps in its paragraph.\n\n" ++
  "\\begin{minipage}{5cm}\nUniform in a minipage.\n\nVictor second in it.\n\\end{minipage}\n\n" ++
  "\\begin{flushleft}\nWhiskey flush.\n\nXray flush second.\n\\end{flushleft}\n\n" ++
  "Yankee closes.\n\\subsection*{Starred}\nZulu follows a starred heading."

/-- Run-in heads, a float after a heading, `\\noindent` opening a group, and text after a
bibliography, as lualatex sets them. -/
private def heads : String :=
  "\\section{Heads}\n\n\\paragraph{Runin} Alpha after a paragraph head.\n\n" ++
  "\\subparagraph{Sub} Bravo after a subparagraph head.\n\\section{Float}\n" ++
  "\\begin{figure}[t]\n\\centering\n\\rule{1cm}{1cm}\n\\caption{Caption.}\n\\end{figure}\n" ++
  "Charlie after the float.\n\n{\\noindent\\bfseries Delta bold.} rest.\n\n" ++
  "Echo after the group.\n\\begin{thebibliography}{9}\n\\bibitem{k} Foxtrot entry.\n" ++
  "\\end{thebibliography}\nGolf after the list."

/-- The baselines of the first lines opening on `words`, each below the one before. -/
private def pitches (oneFace : Font.FontSet) (src : String) (words : List String) :
    Option (List Dim.Length) := do
  let (d, _) := elabStr src
  let c := censusOf (coveredColorsOf d) (layoutOf oneFace d)
  let ys ← words.mapM (lineYOf c 0 ·)
  return (ys.zip ys.tail).map fun (a, b) => b - a

/-- An amsthm theorem, a kernel one and an article abstract, each before text with no blank line. -/
private def theorems (ams : Bool) : String :=
  s!"\\documentclass\{article}\n{if ams then "\\usepackage{amsthm}\n" else ""}" ++
  "\\newtheorem{thm}{Theorem}\n\\begin{document}\n\\begin{abstract}\nAlpha abstract first.\n\n" ++
  "Bravo abstract second.\n\\end{abstract}\nCharlie after the abstract.\n\nDelta paragraph.\n" ++
  "\\begin{thm}\nEcho head line.\n\nFoxtrot second.\n\\end{thm}\nGolf after the theorem.\n" ++
  "\\end{document}\n"

def parIndentChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let two := "Alpha first paragraph.\n\nBravo second paragraph."
  -- lualatex: each class's size file or class file `\parindent`, KOMA-Script's 1em under
  -- parskip=false and never and none under a skip in lines, acmart's 9pt under acmtog.
  for (cls, want) in [("[10pt]{article}", Dim.pt 15), ("[11pt]{article}", Dim.pt 17),
      ("[12pt]{article}", Dim.pt 18), ("{report}", Dim.pt 15), ("[11pt]{book}", Dim.pt 17),
      ("[12pt]{memoir}", Dim.pt 18), ("{scrartcl}", Dim.pt 1095 / 100),
      ("[parskip=never]{scrartcl}", Dim.pt 1095 / 100), ("[10pt]{scrreprt}", Dim.pt 10),
      ("[parskip=half]{scrartcl}", 0), ("{letter}", 0), ("{ltflow}", Dim.pt 17),
      ("[9pt]{memoir}", Dim.pt 12), ("{amsart}", Dim.pt 12), ("{amsproc}", Dim.pt 18),
      ("{acmart}", Dim.pt 10), ("[acmtog]{acmart}", Dim.pt 9)] do
    let got := indents oneFace (doc cls "" two) ["Alpha", "Bravo"]
    t s!"par indent: {cls} indents a paragraph by its class's parindent ({got})"
      (got == [some want, some want])
  -- lualatex: letter.cls's paragraphs 0.7em apart.
  t "par indent: letter's paragraphs stand 0.7em apart"
    ((gaps oneFace (doc "{letter}" "" two) ["Alpha", "Bravo"]).any fun gs =>
      gs.all fun g => (g - 70).natAbs ≤ 2)
  -- lualatex: `\parskip` 0pt plus 1pt, the paragraphs a baselineskip apart.
  for cls in ["{article}", "[12pt]{report}", "{book}"] do
    t s!"par indent: {cls}'s paragraphs stand one baselineskip apart"
      (gaps oneFace (doc cls "" two) ["Alpha", "Bravo"] == some [0])
  -- lualatex on the same probe: no indent after a heading, where text goes on past an environment
  -- or a display, under `\noindent`, or where a container sets `\parindent` zero.
  let src := doc "[10pt]{article}" "" contexts
  let words := ["Alpha", "Bravo", "Charlie", "Delta", "Foxtrot", "Golf", "India", "Juliet", "Kilo",
    "Mike", "November", "Oscar", "Quebec", "Romeo", "Tango", "Uniform", "Victor", "Whiskey", "Xray",
    "Yankee", "Zulu"]
  let want : List Dim.Length :=
    [15, 15, 0, 15, 0, 0, 15, 0, 15, 0, 0, 15, 0, 15, 0, 0, 0, 0, 0, 15, 0].map Dim.pt
  let got := indents oneFace src words
  for ((w, g), e) in (words.zip got).zip want do
    t s!"par indent: {w} sets lualatex's indent ({g})" (g == some e)
  let (d, _) := elabStr src
  for (w, e) in words.zip want do
    -- An item's paragraph is its list item's text.
    t s!"par indent: the web page indents {w} as the PDF does"
      (match htmlIndented d w with
       | some b => b == (e != 0)
       | none => w == "Foxtrot" && e == 0)
  let hs := doc "[10pt]{article}" "" heads
  let hw := ["Runin", "Sub", "Charlie", "Delta", "Echo", "Golf"]
  let hwant := [0, 15, 0, 0, 15, 0].map Dim.pt
  let (hd, _) := elabStr hs
  for ((w, g), e) in (hw.zip (indents oneFace hs hw)).zip hwant do
    t s!"par indent: {w} sets lualatex's indent past a head, a float, a group or a list ({g})"
      (g == some e && htmlIndented hd w == some (e != 0))
  -- lualatex: `\@startsection`'s skips around each heading, and `\@maketitle`'s around the title's
  -- parts, each line within five points of lualatex's baseline, the engine's line box
  -- below a heading standing deeper than TeX's.
  let near (got : Option (List Dim.Length)) (lua : List Int) : Bool :=
    match got with
    | some gs => gs.length == lua.length &&
        (gs.zip lua).all fun (g, l) => (g - Dim.pt l / 100).abs ≤ Dim.pt 5
    | none => false
  let sections := "Alpha before the section.\n\\section{Bravo}\nCharlie after the section.\n" ++
    "\\subsection{Delta}\nEcho after the subsection.\n\\subsubsection{Foxtrot}\nGolf after it."
  let sp := pitches oneFace (doc "{article}" "" sections)
    ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf"]
  t s!"par indent: headings stand their class's skips apart ({sp})"
    (near sp [3435, 2066, 2858, 1790, 2606, 1841])
  let title := "\\title{Probe Title}\\author{Example Author}\\date{May 2099}"
  let tp := pitches oneFace (doc "{article}" title "\\maketitle\nAlpha after the title.")
    ["Probe", "Example", "May", "Alpha"]
  t s!"par indent: the title's parts stand article's maketitle skips apart ({tp})"
    (near tp [2742, 2340, 3654])
  -- lualatex: an abstract's quotation indents every paragraph by its 1.5em at `\small`, text after
  -- it goes on, a theorem's first paragraph opens on its head and its next is indented, and text
  -- after an amsthm theorem opens a paragraph where the kernel's goes on.
  for (ams, after) in [(true, Dim.pt 15), (false, 0)] do
    let got := indents oneFace (theorems ams) ["Alpha", "Bravo", "Charlie", "Delta", "Theorem",
      "Foxtrot", "Golf"]
    t s!"par indent: an abstract, a theorem and the text after them (amsthm {ams}) ({got})"
      (got == [some (Dim.pt 135 / 10), some (Dim.pt 135 / 10), some 0, some (Dim.pt 15), some 0,
        some (Dim.pt 15), some after])
  -- lualatex: a declared `\parindent` stands, in the preamble or the body to its group's end, a
  -- declared `\parskip` keeps the class's indent, and parskip.sty drops it but under `indent`.
  let body := "Alpha first.\n\nBravo second.\n\\setlength{\\parindent}{0pt}\n\nCharlie after.\n\n" ++
    "{\\setlength{\\parindent}{30pt}\n\nDelta in a group.\n\n}\n\nEcho after it."
  t "par indent: a body parindent sets the paragraphs after it, to its group's end"
    (indents oneFace (doc "{article}" "" body) ["Bravo", "Charlie", "Delta", "Echo"] ==
      [some (Dim.pt 15), some 0, some (Dim.pt 30), some 0])
  let declared : List (String × Dim.Length × Int) := [("\\setlength{\\parindent}{0pt}", 0, 0),
    ("\\setlength{\\parindent}{2em}", Dim.pt 20, 0), ("\\setlength{\\parskip}{6pt}", Dim.pt 15, 60),
    ("\\usepackage{parskip}", 0, 60), ("\\usepackage[indent]{parskip}", Dim.pt 15, 60),
    ("\\page{ parindent = 1em }", Dim.pt 10, 0)]
  for (pre, want, gap) in declared do
    let src := doc "{article}" pre two
    t s!"par indent: {pre} sets lualatex's indent and gap"
      (indents oneFace src ["Bravo"] == [some want] &&
        (gaps oneFace src ["Alpha", "Bravo"]).map (·.all fun g => (g - gap).natAbs ≤ 1) == some true)
  t "par indent: the web page reads a body parindent as the PDF does"
    (hasStr (docHtmlOf (elabStr (doc "{article}" "" body)).1) "--parindent: 0pt" &&
      hasStr (docHtmlOf (elabStr (doc "{article}" "" body)).1) "--parindent: 29.888pt")
  -- A preamble declaration is the page's one value, fixed in the preamble's font.
  let pre := (elabStr (doc "{article}" "\\setlength{\\parindent}{3em}" two)).1
  t "par indent: a preamble parindent is the page's, fixed in its font"
    (pre.page.parindent == some (.ofLength (Dim.pt 30)) && (pre.tokens.find? "parindent").isNone)
  -- A markdown page keeps block paragraphs, half a line apart, where a tex page declaring no class
  -- takes the article's.
  let md := (elabMd "Alpha first paragraph.\n\nBravo second paragraph.\n").1
  let mdOut := layoutOf oneFace md
  t "par indent: a markdown page sets its paragraphs flush, half a line apart"
    (md.page.parindent.isNone && md.page.parskip.isNone && indentOf mdOut "Bravo" == some 0 &&
      (do let c := censusOf (coveredColorsOf md) mdOut
          let a ← lineYOf c 0 "Alpha"
          let b ← lineYOf c 0 "Bravo"
          pure (b - a - Ir.baselineSkipOf md.page)) == some (Dim.pt 6))
  -- A markdown file a LaTeX host includes takes the host's indent, as the markdown package's LaTeX
  -- does, each of its paragraphs one of its own.
  let (host, _) := includedDoc "host.tex" (neutralHost "note.md")
    [("note.md", "note.md", "Alpha first.\n\n- Bravo item.\n\n> Charlie quoted.\n\nDelta after.\n")]
  t "par indent: an included markdown file's paragraphs take the host's indent"
    (let out := layoutOf oneFace host
     indentOf out "Alpha" == some (Dim.pt 15) && indentOf out "Delta" == some (Dim.pt 15))
  t "par indent: a tex page declaring no class sets the article's paragraphs"
    (indents oneFace two ["Bravo"] == [some (Dim.pt 15)] && gaps oneFace two ["Alpha", "Bravo"] == some [0])
  let css := (HtmlDoc.emit {} (elabStr (doc "{article}" "" two)).1).1
  t "par indent: the web page's stylesheet sets the indent and no gap between paragraphs"
    (hasStr css "p.u-indent { text-indent: var(--parindent, 1.5rem); }" && hasStr css "--parskip: 0")
  -- lualatex: under parskip.sty a body `\parindent` indents the paragraphs after it.
  let skipBody := doc "{article}" "\\usepackage{parskip}"
    "Alpha first.\n\n\\setlength{\\parindent}{20pt}\n\nBravo second."
  t "par indent: under parskip a body parindent indents the PDF's and the web page's paragraph"
    (indents oneFace skipBody ["Bravo"] == [some (Dim.pt 20)] &&
      htmlIndented (elabStr skipBody).1 "Bravo" == some true)
  -- `\noindent` in a macro body, an argument or a group past a declaration: no error or warning,
  -- the grouped one setting its paragraph flush as lualatex does.
  let marks := doc "{article}" "\\newcommand{\\y}{\\noindent Yankee macro.}"
    ("Alpha.\n\n\\y\n\n\\textbf{\\noindent Bravo bold.}\n\n" ++
      "{\\bfseries\\noindent Charlie bold.} rest.\n\nDelta\\footnote{\\noindent Echo.}")
  let (_, markDs) := elabStr marks
  t s!"par indent: \\noindent where TeX ignores it neither fails nor warns ({markDs.map (·.code)})"
    (markDs.all (·.severity == .note) &&
      indents oneFace marks ["Charlie"] == [some 0])
  -- The indent's box is never expanded, so a first line shrinking under font expansion keeps its
  -- glue's share and stays on the measure.
  let words := #["Pstart", "theta", "lantern", "harbor", "omicron", "window", "upsilon", "meadow",
    "Thunder", "candle", "epsilon", "gamma", "silver", "kappa", "garden", "river"]
  let para (k : Nat) : String := " ".intercalate ((List.range (40 + k % 7)).map fun i =>
    words[(i * 7 + k * 3) % words.size]?.getD "")
  let long := doc "{article}" "" ("\n\n".intercalate ((List.range 40).map para))
  let (ld, _) := elabStr long
  let lgeom := Layout.Geom.ofPage ld.page
  t "par indent: an indented first line under font expansion stays on the measure"
    ((Layout.Quality.overflows lgeom (layoutOf oneFace ld lgeom).pages).isEmpty)
  t "par indent: \\noindent inside a paragraph leaves it whole"
    ((elabStr (doc "{article}" "" "Alpha \\noindent bravo.")).1.body.size == 1)

end Tests.ParIndent
