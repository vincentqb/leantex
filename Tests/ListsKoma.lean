module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-- Lengths print as their base-unit counts in failure messages. -/
private instance : ToString Dim.Length := ⟨reprStr⟩

/-! KOMA-Script's lists and LaTeX's three quotation environments, at lualatex's positions measured
on the same invented documents. -/

namespace Tests.ListsKoma

/-- An outer list, a second level in its first item and a third in that one's. -/
def nested : String :=
  "Alpha paragraph.\n\n\\begin{itemize}\n\\item Bravo outer.\n\\begin{itemize}\n" ++
  "\\item Charlie inner.\n\\begin{itemize}\n\\item Delta third.\n\\item Echo third.\n" ++
  "\\end{itemize}\n\\item Foxtrot inner.\n\\end{itemize}\n\\item Golf outer.\n\\end{itemize}\n\n" ++
  "Hotel after."

/-- A quote, a quotation and a verse of two stanzas, each of two paragraphs, between paragraphs. -/
def quotes : String :=
  "Alpha paragraph.\n\n\\begin{quote}\nBravo quoted first.\n\nCharlie quoted second.\n" ++
  "\\end{quote}\n\nDelta between.\n\n\\begin{quotation}\nEcho quotation first.\n\n" ++
  "Foxtrot quotation second.\n\\end{quotation}\n\nGolf between.\n\n\\begin{verse}\n" ++
  "Hotel verse one\\\\\nIndia verse two\\\\\nJuliet verse three\n\nKilo verse four\n" ++
  "\\end{verse}\n\nLima after."

/-- A list in a minipage and one in a float, each between paragraphs of its box. -/
def boxed : String :=
  "Alpha paragraph.\n\n\\begin{minipage}{\\textwidth}\nBravo boxed.\n\\begin{itemize}\n" ++
  "\\item Charlie item.\n\\item Delta item.\n\\end{itemize}\nEcho boxed after.\n\\end{minipage}\n\n" ++
  "\\begin{figure}[h]\nFoxtrot floated.\n\\begin{itemize}\n\\item Golf item.\n\\item Hotel item.\n" ++
  "\\end{itemize}\nIndia floated after.\n\\end{figure}"

/-- Paragraphs going on past a display and a list in a quotation, text after a list a quotation opens
with, and a verse line going on past a list. -/
def goesOn : String :=
  "\\begin{quote}\nAlpha plain.\n\\end{quote}\n\n\\begin{quotation}\nBravo first.\n\n" ++
  "Charlie before\n\\[ x = y \\]\nDelta after display.\n\nEcho before.\n\\begin{itemize}\n" ++
  "\\item Foxtrot item.\n\\end{itemize}\nGolf after list.\n\\end{quotation}\n\n" ++
  "\\begin{quotation}\n\\begin{itemize}\n\\item Hotel item.\n\\end{itemize}\nIndia after.\n" ++
  "\\end{quotation}\n\n\\begin{verse}\nJuliet one\n\\begin{itemize}\n\\item Kilo item.\n" ++
  "\\end{itemize}\nLima after list\\\\\nMike next\n\\end{verse}"

/-- A verse whose last line opens on a fill. -/
def signed : String :=
  "\\begin{verse}\nBravo one\\\\\nCharlie two\\\\\n\\hfill Delta signed\n\\end{verse}"

/-- A list opening a quote, one opening a quotation and a quote opening a quote. -/
def opening : String :=
  "Alpha paragraph.\n\n\\begin{quote}\n\\begin{itemize}\n\\item Bravo item.\n" ++
  "\\end{itemize}\nCharlie after.\n\\end{quote}\n\nDelta paragraph.\n\n\\begin{quotation}\n" ++
  "\\begin{itemize}\n\\item Echo item.\n\\end{itemize}\nFoxtrot after.\n\nGolf second.\n" ++
  "\\end{quotation}\n\nHotel paragraph.\n\n\\begin{quote}\n\\begin{quote}\nIndia inner.\n" ++
  "\\end{quote}\nJuliet after.\n\\end{quote}\n\nKilo end."

/-- A frame holding a verse of two stanzas between paragraphs. -/
def stanzas : String :=
  "\\begin{frame}\nAlpha paragraph.\n\\begin{verse}\nBravo verse one\\\\\n" ++
  "Charlie verse two\n\nDelta stanza two\n\\end{verse}\nEcho after.\n\\end{frame}"

/-- A list in a quote, in a quotation and in a verse, each between lines of its own. -/
def webLists : String :=
  "\\begin{quote}\nAlpha quoted.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n" ++
  "Charlie after.\n\\end{quote}\n\n\\begin{quotation}\nDelta quoted.\n\\begin{itemize}\n" ++
  "\\item Echo item.\n\\end{itemize}\nFoxtrot after.\n\\end{quotation}\n\n\\begin{verse}\n" ++
  "Golf line\n\\begin{itemize}\n\\item Hotel item.\n\\end{itemize}\nIndia after\n\\end{verse}"

/-- A frame's verse stepping the line its `\\` ended, before a stanza. -/
def paused : String :=
  "\\begin{frame}\n\\begin{verse}\nAlpha line one\\\\\n\\pause\nBravo line two\n\n" ++
  "Charlie stanza two\n\\end{verse}\n\\end{frame}"

/-- A verse whose lines all stand under one font declaration. -/
def styledVerse : String :=
  "\\begin{quote}\nAlpha plain.\n\\end{quote}\n\n\\begin{verse}\\itshape Bravo one\\\\\n" ++
  "Charlie two\\\\\nDelta three\n\nEcho four\\\\\nFoxtrot five\n\\end{verse}"

/-- A verse a list opens, and a line after the list. -/
def verseOpening : String :=
  "\\begin{verse}\n\\begin{itemize}\n\\item Alpha item.\n\\item Bravo item.\n\\end{itemize}\n" ++
  "Charlie after\n\\end{verse}"

/-- A quotation's paragraphs going on past a verbatim, a skip and a heading, a run-in heading's,
and a paragraph a `\\par` after a display opens. -/
def goesOnMore : String :=
  "\\begin{quote}\nAlpha plain.\n\\end{quote}\n\n\\begin{quotation}\nBravo first.\n\n" ++
  "Charlie before verbatim.\n\\begin{verbatim}\ncode line\n\\end{verbatim}\nDelta after.\n\n" ++
  "Echo before list.\n\\begin{itemize}\n\\item Foxtrot item.\n\\end{itemize}\n\\vspace{2pt}\n" ++
  "Golf after skip.\n\n\\subsection*{Hotel heading}\nIndia after heading.\n\n" ++
  "\\paragraph{Juliet} Kilo run in.\n\nLima before\n\\[ x = y \\]\n\\par\nMike after par.\n" ++
  "\\end{quotation}"

/-- A quotation of paragraphs in `\\small`, and a label before a list opening a quotation. -/
def smallAndLabel : String :=
  "\\begin{quote}\nAlpha plain.\n\\end{quote}\n\nBravo paragraph.\n\\begin{quotation}\n" ++
  "\\small Charlie small one.\n\nDelta small two.\n\\end{quotation}\n\n\\begin{quotation}\n" ++
  "\\label{q}\n\\begin{itemize}\n\\item Echo item.\n\\end{itemize}\nFoxtrot after.\n" ++
  "\\end{quotation}"

def doc (cls pre body : String) : String :=
  s!"\\documentclass{cls}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

/-- The space between consecutive lines starting with `words` on page `page`, past the page's
baselineskip, in tenths of a point; `none` where a word starts no line. -/
def gaps (oneFace : Font.FontSet) (src : String) (words : List String) (page : Nat := 0) :
    Option (List Int) := do
  let (d, _) := elabStr src
  let c := censusOf (coveredColorsOf d) (layoutOf oneFace d)
  let ys ← words.mapM (lineYOf c page ·)
  let bs := Ir.baselineSkipOf d.page
  return (ys.zip ys.tail).map fun (a, b) => ((b - a - bs) * 10 + Dim.pt 1 / 2) / Dim.pt 1

/-- A line's first glyph's x: its start past the glyphless runs and gaps before it. -/
def inkStart (l : Layout.LineOut) : Dim.Length := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ => if glyphs.isEmpty then x := x + w else return x
    | .gap w _ => x := x + w
    | _ => return x
  return x

/-- The first glyph's x of the first body line holding `word`. -/
def inkOf (out : Layout.Out) (word : String) : Option Dim.Length :=
  (bodyLines out).findSome? fun l =>
    let text := String.join (l.segs.toList.map fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ _ => String.ofList (glyphs.toList.map (·.2.1))
      | _ => " ")
    if hasStr text word then some (inkStart l) else none

/-- KOMA-Script's classes as lualatex sets them: 11pt with no size option, `parskip` in lines of
the class's `\baselineskip`, and a list level one to three under a positive `\parskip` taking it as
its `\parsep`, with no `\topsep` and no `\itemsep`. -/
def komaListChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let words := ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel"]
  -- lualatex, each gap over the class's baselineskip of 12pt, 13.6pt or 14.5pt.
  for (cls, want) in [("[10pt]{article}", [100, 80, 40, 20, 40, 80, 100]),
      ("[10pt]{scrartcl}", [100, 40, 40, 40, 40, 80, 100]),
      ("{scrartcl}", [120, 45, 45, 45, 45, 90, 120]), ("{scrreprt}", [120, 45, 45, 45, 45, 90, 120]),
      ("{scrbook}", [120, 45, 45, 45, 45, 90, 120]),
      ("[parskip=never]{scrartcl}", [120, 45, 45, 45, 45, 90, 120]),
      ("[12pt]{scrartcl}", [130, 50, 50, 50, 50, 100, 130]),
      ("[parskip=half]{scrartcl}", [98, 68, 68, 68, 68, 68, 98]),
      ("[parskip=full]{scrartcl}", [166, 136, 136, 136, 136, 136, 166]),
      ("[10pt,parskip=half]{scrartcl}", [80, 60, 60, 60, 60, 60, 80])] do
    t s!"koma lists: {cls}'s nested lists set the gaps lualatex sets"
      (gaps oneFace (doc cls "" nested) words == some want)
  t "koma lists: a KOMA-Script class with no size option sets its body at 11pt"
    ((elabStr (doc "{scrartcl}" "" "Alpha.")).1.page.fontSize == Dim.pt 11 &&
      (elabStr (doc "{scrbook}" "" "Alpha.")).1.page.fontSize == Dim.pt 11)
  let ds := (elabStr (doc "[parskip=half]{scrartcl}" "" "Alpha.")).2
  t "koma lists: a KOMA-Script class's parskip option is read, its paragraphs' end fill named"
    (ds.any (fun d => d.code == "W0110" && d.detail == some "1em free") &&
      !ds.any (fun d => d.code == "W0104"))
  t "koma lists: options passed to a KOMA-Script class before it loads are its own"
    ((elabStr ("\\PassOptionsToClass{titlepage}{scrartcl}\n" ++ doc "{scrartcl}" "" "Alpha.")).1.abstractForm ==
      .titlePage)
  -- A declared parskip stands in a minipage and a float, where `\@parboxrestore` zeroes LaTeX's, so a
  -- list there takes it as its parsep.
  let src := doc "[parskip=half]{scrartcl}" "" boxed
  t "koma lists: a list in a minipage or a float reads the declared parskip, which stands there"
    (gaps oneFace src ["Bravo", "Charlie", "Delta", "Echo"] == some [68, 68, 68] &&
      gaps oneFace src ["Foxtrot", "Golf", "Hotel", "India"] == some [68, 68, 68])
  -- lualatex: the class's written options stand over those passed to it before it loads.
  t "koma lists: a class's written option stands over the one passed to it"
    (((elabStr ("\\PassOptionsToClass{parskip=full}{scrartcl}\n" ++
        doc "[parskip=half]{scrartcl}" "" "Alpha.")).1.page.parskip.map (·.width.fixed)) == some (Dim.pt 68 / 10))
  -- enumitem's keys stand over the level's macro: a declared parsep is the next level's parskip.
  let declared := doc "{scrartcl}" "\\usepackage{enumitem}\n\\setlist[1]{parsep=0pt}" nested
  t "koma lists: a declared level-one parsep of zero leaves the second level's own skips"
    ((gaps oneFace declared words).map (·.take 3) == some [120, 45, 20])

/-- LaTeX's quote, quotation and verse as lualatex sets them, each a list level spaced as one under
what its environment declares: quotation's paragraphs indented and touching, verse's lines hung by
1.5em and touching, a quote's at its level's parsep, under KOMA-Script's parskip as a list's. -/
def quoteKindChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let words := ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel", "India",
    "Juliet", "Kilo", "Lima"]
  for (cls, want) in [("[10pt]{article}", [100, 40, 100, 100, 0, 100, 100, 0, 0, 40, 100]),
      ("[10pt]{scrartcl}", [100, 40, 100, 100, 0, 100, 100, 0, 0, 40, 100]),
      ("[10pt,parskip=half]{scrartcl}", [80, 60, 80, 80, 0, 80, 80, 0, 0, 60, 80]),
      ("[parskip=full]{scrartcl}", [166, 136, 166, 166, 0, 166, 166, 0, 0, 136, 166])] do
    t s!"quote kinds: {cls}'s quote, quotation and verse set the gaps lualatex sets"
      (gaps oneFace (doc cls "" quotes) words == some want)
  -- classes.dtx's quotation \listparindent 1.5em, scrartcl's 1em; verse's 1.5em hang.
  let long := "Hotel verse one that runs on and on with many more words than any measure holds " ++
    "in a single line of this page here and keeps going for a good while yet\\\\\nIndia two"
  let verse := s!"\\begin\{quotation}\nEcho first.\n\nFoxtrot second.\n\\end\{quotation}\n\n" ++
    s!"\\begin\{quote}\nBravo plain.\n\\end\{quote}\n\n\\begin\{verse}\n{long}\n\\end\{verse}"
  for (cls, indent) in [("[10pt]{article}", Dim.pt 15), ("[10pt]{scrartcl}", Dim.pt 10)] do
    let out := layoutOf oneFace (elabStr (doc cls "" verse)).1
    let inkAt (w : String) : Dim.Length := (inkOf out w).getD 0
    t s!"quote kinds: {cls}'s quotation indents each paragraph's first line by its class's parindent"
      (inkAt "Echo" - inkAt "Bravo" == indent && inkAt "Foxtrot" - inkAt "Bravo" == indent)
    let lines := (bodyLines out).filter fun l => l.segs.any fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
      | _ => false
    let verseLines := lines.extract 3 lines.size
    -- A margin kern may stand a continuation's first glyph a little out past the hang.
    t s!"quote kinds: {cls}'s verse hangs a wrapped line 1.5em past its lines, and restarts at each"
      (verseLines.size ≥ 3 && verseLines.toList.zipIdx.all fun (l, i) =>
        let want := if i == 0 || i + 1 == verseLines.size then 0 else Dim.pt 15
        (inkStart l - inkAt "Bravo" - want).abs ≤ Dim.pt 1)
  t "quote kinds: a long verse line wraps as LaTeX's does, naming no declared line"
    (!(elabStr (doc "[10pt]{article}" "" verse)).2.any (·.code == "W0386") &&
      !(layoutOf oneFace (elabStr (doc "[10pt]{article}" "" verse)).1).diags.any (·.code == "W0386"))
  -- lualatex: a quotation inherits the item's declared partopsep, a fifth-level quote its list's
  -- declared topsep and parsep, and a quote's end re-skips a nested list as an item's does.
  let inherit := "Alpha paragraph.\n\n\\begin{itemize}[partopsep=0pt]\n\\item Bravo item.\n\n" ++
    "\\begin{quotation}\nCharlie quoted.\n\\end{quotation}\n\\item Delta item.\n\\end{itemize}\n\n" ++
    "Echo paragraph.\n\n\\begin{itemize}[topsep=7pt,parsep=3pt]\n\\item Foxtrot one.\n" ++
    "\\begin{itemize}[topsep=7pt,parsep=3pt]\n\\item Golf two.\n" ++
    "\\begin{itemize}[topsep=7pt,parsep=3pt]\n\\item Hotel three.\n" ++
    "\\begin{itemize}[topsep=7pt,parsep=3pt]\n\\item India four.\n\n\\begin{quote}\n" ++
    "Juliet quoted first.\n\nKilo quoted second.\n\\end{quote}\n\\end{itemize}\n\\end{itemize}\n" ++
    "\\end{itemize}\n\\end{itemize}\n\nLima after."
  t "quote kinds: a quotation and a deep quote take what their level keeps of the lists around them"
    (gaps oneFace (doc "[10pt]{article}" "\\usepackage{enumitem}" inherit)
      ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf", "Hotel", "India", "Juliet",
        "Kilo", "Lima"] == some [80, 80, 80, 80, 90, 100, 100, 100, 110, 30, 110])
  let closes := "\\begin{itemize}\\item Alpha\n\\begin{quote}Bravo\n\\begin{itemize}\\item Charlie" ++
    "\\end{itemize}\n\\end{quote}\n\\item Delta\\end{itemize}\n\n\\begin{quote}\nEcho quoted.\n\n" ++
    "\\begin{itemize}\n\\item Foxtrot inner.\n\\end{itemize}\n\\end{quote}\n\nGolf after."
  t "quote kinds: a quote closing on a nested list re-skips it with its parsep, less the parskip out"
    (gaps oneFace (doc "[10pt]{article}" "\\usepackage{enumitem}\n\\setlist[itemize,2]{topsep=9pt}"
      closes) ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf"] ==
        some [80, 110, 110, 100, 100, 100])

/-- Where a quotation's paragraphs and its neighbours' skips meet: a paragraph going on past a display
or a list, a list or a quote opening a quotation, a fill in a verse line, beamer's verse and the web
page's quotations, at lualatex's positions. -/
def quoteBoundaryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "quote kinds: the web CV's quote, quotation and verse stand on its grid, a leading apart"
    (gaps oneFace (doc "{webpage}" "" quotes) ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot",
      "Golf", "Hotel", "India", "Juliet", "Kilo", "Lima"] ==
        some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] &&
      (let out := layoutOf oneFace (elabStr (doc "{webpage}" "" quotes)).1
       inkOf out "Echo" == inkOf out "Bravo"))
  -- lualatex: `\@endpe` leaves no indent on text going on past a display or a list, and text after
  -- a list a quotation opens with keeps its paragraph's, the label ending no paragraph.
  let out := layoutOf oneFace (elabStr (doc "[10pt]{article}" "" goesOn)).1
  let past (w : String) : Dim.Length := (inkOf out w).getD 0 - (inkOf out "Alpha").getD 0
  t "quote kinds: a quotation's paragraph going on past a display or a list takes no indent"
    (past "Bravo" == Dim.pt 15 && past "Charlie" == Dim.pt 15 && past "Delta" == 0 &&
      past "Golf" == 0)
  t "quote kinds: text after a list a quotation opens with keeps its paragraph's indent"
    (past "India" == Dim.pt 15)
  t "quote kinds: a verse line going on past a list stands at the hang, the next at its margin"
    (past "Juliet" == 0 && past "Lima" == Dim.pt 15 && past "Mike" == 0)
  let line := (bodyLines (layoutOf oneFace (elabStr (doc "[10pt]{article}" "" signed)).1)).find? fun l =>
    hasStr (lineText l) "Delta"
  t "quote kinds: a fill opening a verse line sets the rest against the verse's right margin"
    (line.any fun l => inkStart l - l.x > l.setWidth / 2)
  -- lualatex: a list or a quote opening a quote stands in its label, with no skip above or below it.
  t "quote kinds: a list or a quote opening a quote sets the gaps lualatex sets"
    (gaps oneFace (doc "[10pt]{article}" "" opening) ["Alpha", "Bravo", "Charlie", "Delta", "Echo",
      "Foxtrot", "Golf", "Hotel", "India", "Juliet", "Kilo"] ==
        some [100, 40, 100, 100, 0, 0, 100, 100, 40, 100])
  let inQuote := "Alpha.\n\n\\begin{quote}\nBravo.\n\\begin{itemize}\n\\item Charlie.\n\\end{itemize}\n" ++
    "\\end{quote}"
  t "quote kinds: a quote is a list level, so a level-two setting reaches a list in it, and is used"
    (!(elabStr (doc "[10pt]{article}" "\\usepackage{enumitem}\n\\setlist[2]{topsep=9pt}" inQuote)).2.any
      (·.code == "W0449"))
  -- lualatex: beamer's verse sets `\parsep .75em plus .25em minus .25em` between its stanzas.
  t "quote kinds: beamer's verse stands its stanzas its own parsep apart"
    (gaps oneFace (doc "{beamer}" "" stanzas) ["Alpha", "Bravo", "Charlie", "Delta", "Echo"] ==
      some [30, 0, 83, 30])
  -- The web page's lists keep the page's rhythm in a quotation and a verse as in a quote.
  let web := doc "{webpage}" "" webLists
  t "quote kinds: a list in the web page's quotation or verse keeps the page's own rhythm"
    (let inQuote := gaps oneFace web ["Alpha", "Bravo", "Charlie"]
     inQuote.isSome && gaps oneFace web ["Delta", "Echo", "Foxtrot"] == inQuote &&
       gaps oneFace web ["Golf", "Hotel", "India"] == inQuote)
  -- lualatex: verse's `\\` takes back the next paragraph's `\parskip`, so the line a step reveals
  -- after it stands at the margin a line below, and a stanza after it its parsep further.
  let stepped := layoutOf oneFace (elabStr (doc "{beamer}" "" paused)).1
  t "quote kinds: a verse line a step reveals after its line's end stands a line below, unhung"
    (gaps oneFace (doc "{beamer}" "" paused) ["Alpha", "Bravo", "Charlie"] (page := 1) ==
        some [0, 83] && inkOf stepped "Bravo" == inkOf stepped "Alpha")
  let styled := layoutOf oneFace (elabStr (doc "[10pt]{article}" "" styledVerse)).1
  t "quote kinds: a verse under a font declaration sets each line at the verse's margin"
    (["Bravo", "Charlie", "Delta", "Echo", "Foxtrot"].all fun w =>
      inkOf styled w == inkOf styled "Alpha")
  -- lualatex: a list opening a verse stands in its label, its first item at its own margin, and
  -- the line after it at the hang.
  let opened := layoutOf oneFace (elabStr (doc "[10pt]{article}" "" ("\\begin{quote}\nAlpha " ++
    "plain.\n\\end{quote}\n\n\\begin{quote}\n\\begin{itemize}\n\\item Echo item.\n" ++
    "\\end{itemize}\n\\end{quote}\n\n" ++ verseOpening.replace "Alpha item" "Delta item"))).1
  t "quote kinds: a list opening a verse sets its first item where one opening a quote stands"
    (inkOf opened "Delta" == inkOf opened "Echo" && inkOf opened "Charlie" == inkOf opened "Alpha")
  -- lualatex: no indent past a verbatim, a skip after a list, a heading or a run-in heading, and
  -- the indent on a paragraph `\\par` opens after a display.
  let more := layoutOf oneFace (elabStr (doc "[10pt]{article}" "" goesOnMore)).1
  let past (w : String) : Dim.Length := (inkOf more w).getD 0 - (inkOf more "Alpha").getD 0
  t "quote kinds: a quotation's text past a verbatim, a skip or a heading takes no indent"
    (past "Bravo" == Dim.pt 15 && past "Delta" == 0 && past "Golf" == 0 && past "India" == 0 &&
      past "Juliet" == 0 && past "Mike" == Dim.pt 15)
  -- lualatex: `\\small` paragraphs in a quotation stand on the small size's line, and a label
  -- before a list opening a quotation leaves the list in its item's label.
  let small := doc "[10pt]{article}" "" smallAndLabel
  let labelled := layoutOf oneFace (elabStr small).1
  t "quote kinds: small paragraphs in a quotation stand on their own size's line"
    (gaps oneFace small ["Charlie", "Delta"] == some [-10])
  t "quote kinds: a label before a list opening a quotation leaves the list in its label"
    (gaps oneFace small ["Echo", "Foxtrot"] == some [0] &&
      (inkOf labelled "Foxtrot").getD 0 - (inkOf labelled "Alpha").getD 0 == Dim.pt 15)

/-- The web page sets each quotation kind by its class: quotation's first-line indent and verse's
hung lines, a quote's declared spacing by its spacing's class, and a KOMA-Script nested list's. -/
def quoteKindHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (cls body : String) : String := (HtmlDoc.emit {} (elabStr (doc cls "" body)).1).1
  let q := page "[10pt]{article}" quotes
  t "html quote kinds: a quotation and a verse carry their kind's class"
    (hasStr q "<blockquote class=\"quotation" && hasStr q "<blockquote class=\"verse" &&
      hasStr q "<blockquote>")
  let indent := "p.quotation-par:not(.u-continues) { text-indent: "
  t "html quote kinds: quotation indents its paragraphs by its class's parindent"
    (hasStr q (indent ++ "1.5rem; }") && hasStr (page "[10pt]{scrartcl}" quotes) (indent ++ "1rem; }"))
  t "html quote kinds: verse hangs each line of a paragraph, each forced line restarting"
    (hasStr q "p.verse-par { padding-left: 1.5rem; text-indent: -1.5rem each-line; }" &&
      (q.splitOn "<p class=\"verse-par\">").length == 3 && (q.splitOn "<br").length ≥ 3 &&
      !hasStr q "verse-line")
  t "html quote kinds: a page without quotation or verse carries neither rule"
    (let plain := page "[10pt]{article}" "Alpha.\n\n\\begin{quote}Bravo.\\end{quote}"
     !hasStr plain "quotation-par" && !hasStr plain "verse-par")
  t "html quote kinds: the web page's quotation and verse take no shape of their kind"
    (let web := page "{webpage}" quotes
     !hasStr web "quotation-par" && !hasStr web "verse-par")
  let g := page "[10pt]{article}" goesOn
  t "html quote kinds: a quotation's or a verse's paragraph going on past a display or a list is marked"
    (hasStr g "<p class=\"quotation-par u-continues\">Delta after display." &&
      hasStr g "<p class=\"quotation-par u-continues\">Golf after list." &&
      hasStr g "<p class=\"quotation-par\">India after." &&
      hasStr g "<p class=\"verse-par u-continues\">Lima after list" &&
      (g.splitOn "u-continues\">").length == 4 &&
      hasStr g "p.verse-par.u-continues::before")
  let more := page "[10pt]{article}" goesOnMore
  t "html quote kinds: a quotation's text past a verbatim, a skip or a heading is marked"
    (hasStr more "<p class=\"quotation-par u-continues\">Delta after." &&
      hasStr more "<p class=\"quotation-par u-continues\">Golf after skip." &&
      hasStr more "<p class=\"quotation-par u-continues\">India after heading." &&
      hasStr more "<p class=\"quotation-par\">Mike after par.")
  t "html quote kinds: a fill in a verse line sets its row against the verse's right margin"
    (hasStr (page "[10pt]{article}" signed) "<p class=\"entry-rows verse-par\">" &&
      hasStr q "p.verse-par:is(.entry, .entry-rows) { padding-left: 0; text-indent: 0; }")
  t "html quote kinds: a list in the web page's quotation or verse declares no spacing of its own"
    (!hasStr (page "{webpage}" webLists) "list-set-")
  let st := page "{beamer}" paused
  t "html quote kinds: a verse line a step reveals after its line's end stands with no gap"
    (hasStr st "class=\"step u-runs-on\"" && hasStr st "* + .u-runs-on")
  let sv := page "[10pt]{article}" styledVerse
  t "html quote kinds: a verse under a font declaration keeps its lines' breaks in one paragraph"
    ((sv.splitOn "<p class=\"verse-par\">").length == 3 && (sv.splitOn "<br").length == 4)
  t "html quote kinds: a list opening a verse takes no hang"
    (hasStr (page "[10pt]{article}" verseOpening)
      "blockquote.verse > :not(p, .step, .step-set, .alt-pair, [data-backend]):not(:first-child)")
  t "html quote kinds: a page without a quotation carries no label rule"
    (!hasStr (page "[10pt]{article}" "Alpha.") "blockquote > :is(")
  t "html quote kinds: a list or a quote opening a quote leaves no skip below it but its parsep"
    (hasStr (page "[10pt]{article}" opening)
      ":first-child + *) { margin-top: calc(0.000rem + var(--parskip, 0rem)); }")
  t "html quote kinds: beamer's verse reads its own parsep"
    (hasStr (page "{beamer}" stanzas) ":where(blockquote.verse > *) { --parskip: ")
  let k := page "[10pt]{scrartcl}" nested
  t "html koma lists: a nested KOMA-Script list reads its level's parskip by its spacing's class"
    ((k.splitOn "<ul>").length == 2 && (k.splitOn "<ul class=\"list-set-1 ").length == 3)
  t "html koma lists: a minipage or a float keeps the declared parskip its lists read"
    (!hasStr (page "[parskip=half]{scrartcl}" boxed) ".column, figure.float {")

/-- An item a list opens, its label kept on the list's first line; an inner first item a centre
opens, then one a description term opens, each before a list; the first shape set flush right; and an
item whose list a label anchor precedes. -/
def labelled : String :=
  "Alpha paragraph.\n\\begin{enumerate}\n\\item \\begin{itemize}\n\\item Bravo inner.\n" ++
  "\\item Charlie inner.\n\\end{itemize}\n\\item Delta outer.\n\\end{enumerate}\n\n" ++
  "\\begin{enumerate}\n\\item \\begin{itemize}\n\\item \\begin{center}\nEcho centred.\n" ++
  "\\end{center}\n\\begin{enumerate}\n\\item India after centre.\n\\end{enumerate}\n" ++
  "\\item Foxtrot inner.\n\\end{itemize}\n\\item Golf outer.\n\\end{enumerate}\n\n" ++
  "\\begin{enumerate}\n\\item \\begin{description}\n\\item[Kilo] term text.\n" ++
  "\\begin{enumerate}\n\\item Lima after term.\n\\end{enumerate}\n\\end{description}\n" ++
  "\\end{enumerate}\n\n\\begin{flushright}\n\\begin{enumerate}\n\\item \\begin{itemize}\n" ++
  "\\item Juliet flush.\n\\end{itemize}\n\\end{enumerate}\n\\end{flushright}\n\n" ++
  "\\begin{enumerate}\n\\item \\label{papa}\\begin{itemize}\n\\item Papa labelled.\n" ++
  "\\end{itemize}\n\\end{enumerate}"

/-- An item an enumerate opens, at a second level narrower than its label. -/
def narrowLabel : String :=
  "\\begin{enumerate}\n\\item \\begin{enumerate}\n\\item Mike first.\n\\item Mint second.\n" ++
  "\\end{enumerate}\n\\end{enumerate}"

/-- A frame whose item opens a list whose first item the second step reveals. -/
def hiddenLabel : String :=
  "\\begin{frame}\n\\begin{enumerate}\n\\item \\begin{itemize}\n\\item<2-> Hotel shown second.\n" ++
  "\\item India shown first.\n\\end{itemize}\n\\end{enumerate}\n\\end{frame}"

/-- The labels of an item a list opens, as `\@donoparitem` keeps them: the item's and the list's
first item's on one line, each at its own item's place, as lualatex sets them. -/
def labelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let find (out : Layout.Out) (w : String) : Option Layout.LineOut :=
    (bodyLines out).find? fun l => hasStr (lineText l) w
  let out := layoutOf oneFace (elabStr (doc "[10pt]{article}" "" labelled)).1
  let line := find out
  t "labels: an item a list opens keeps its label on the list's first line, at its own place"
    (match line "Bravo", line "Delta" with
     | some b, some d => hasStr (lineText b) "1." && b.x == d.x
     | _, _ => false)
  t "labels: an item's label the list's first item cannot take stays off the next item"
    (match line "Foxtrot" with
     | some f => !hasStr (lineText f) "1."
     | none => false)
  t "labels: an item's label its list's first item cannot take stays off a list that item holds"
    (match line "India", line "Lima" with
     | some i, some l => hasStr (lineText i) "(a)" && !hasStr (lineText i) "1." &&
         hasStr (lineText l) "(a)" && !hasStr (lineText l) "1."
     | _, _ => false)
  t "labels: flush right, the labels of an item a list opens stand by its first line's text"
    (match line "Bravo", line "Juliet" with
     | some b, some j =>
       match glyphX b '1', glyphX b 'B', glyphX j '1', glyphX j 'J' with
       | some b1, some bt, some j1, some jt => bt - b1 == jt - j1
       | _, _, _, _ => false
     | _, _ => false)
  t "labels: an item's label waits past a label anchor for the list it opens with"
    (match line "Papa" with
     | some p => hasStr (lineText p) "1."
     | none => false)
  let narrow := layoutOf oneFace
    (elabStr (doc "[10pt]{article}" "\\setlength{\\leftmarginii}{9pt}" narrowLabel)).1
  t "labels: a label wider than its list's indent step overlaps the outer one, the text in place"
    (match find narrow "Mike", find narrow "Mint" with
     | some m, some n => hasStr (lineText m) "1." && glyphX m 'M' == glyphX n 'M'
     | _, _ => false)
  let deck := layoutOf oneFace (elabStr (doc "{beamer}" "" hiddenLabel)).1
  let stepLines (k : Nat) : Array Layout.LineOut :=
    ((deck.pages[k]?.map (·.lines)).getD #[]).filter (!·.furniture)
  t "labels: the item's label hides with the first inner item a later step reveals"
    (deck.pages.size == 2 && (stepLines 0).all (fun l => !hasStr (lineText l) "1.") &&
      (stepLines 1).any fun l => hasStr (lineText l) "1." && hasStr (lineText l) "Hotel")

/-- A list whose enumitem spacing `t` declares, after a paragraph, then a skip of `t`. -/
def exSpaced (t : String) : String × String :=
  (s!"\\usepackage\{enumitem}\n\\setlist\{topsep={t},itemsep=0pt,parsep=0pt,partopsep=0pt}",
   "Alpha paragraph.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n\n" ++
     s!"\\vspace\{{t}}\n\nCharlie after.")

/-- A `calc(⟨rem⟩ + …)` margin's leading length, in thousandths of a rem. -/
def calcRemMilli (v : String) : Option Int :=
  if v.startsWith "calc(" then remMilliOf (((v.drop 5).toString.splitOn " + ").headD "")
  else remMilliOf v

/-- The lengths the equivalence documents declare, each in thousandths of an ex. -/
def exLengths : List (String × Nat) :=
  [("topsep", 1500), ("partopsep", 1000), ("parsep", 500), ("itemsep", 700),
   ("smallskipamount", 800), ("medskipamount", 1600), ("bigskipamount", 3200),
   ("parskip", 600), ("floatsep", 2400)]

/-- An article's body whose lists, quote, centre and skips those lengths space, then a skip. -/
def exArticle (skip : String) : String :=
  "Alpha paragraph.\n\\begin{itemize}\n\\item Bravo item.\n\\begin{itemize}\n" ++
  "\\item Charlie nested.\n\\end{itemize}\n\\item Delta item.\n\\end{itemize}\n\\smallskip\n" ++
  "Echo after.\n\\medskip\n\n\\begin{quote}\nFoxtrot quoted.\n\\end{quote}\n" ++
  "\\begin{center}\nGolf centred.\n\\end{center}\n\\vspace{" ++ skip ++ "}\n\nHotel last."

/-- A deck's frames opening on a list and on a block, with a centre, a float, a skip and a squeezed
list. -/
def exDeck (skip : String) : String :=
  "\\begin{frame}[t]\n\\begin{block}{Romeo title}\nSierra block.\n\\end{block}\n\\end{frame}\n" ++
  "\\begin{frame}[t]\n\\begin{itemize}\n\\item India first.\n\\item Juliet second.\n" ++
  "\\end{itemize}\n\\begin{block}{Kilo title}\nLima block.\n\\end{block}\n\\begin{center}\n" ++
  "Mike centred.\n\\end{center}\n\\begin{figure}\nNovember figure.\n\\end{figure}\n" ++
  "\\vspace{" ++ skip ++ "}\nOscar last.\n\\end{frame}\n\\begin{frame}[squeeze]\n" ++
  "\\begin{itemize}\n\\item Papa squeezed.\n\\begin{itemize}\n\\item Quebec nested.\n" ++
  "\\end{itemize}\n\\end{itemize}\n\\end{frame}"

/-- Lengths declared in ex as both backends read them: at the x-height of the face the page ships,
the one the PDF reads, and at half an em where the page ships none. -/
def exChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let size := Dim.pt 10
  let src (len : String) : String := doc "[10pt]{article}" (exSpaced len).1 (exSpaced len).2
  let drop (len : String) : Option Dim.Length := do
    let lines := bodyLines (layoutOf oneFace (elabStr (src len)).1)
    let y (w : String) := (lines.find? fun l => hasStr (lineText l) w).map (·.y)
    pure ((← y "Bravo") - (← y "Alpha"))
  -- the PDF's 10ex: the list's drop with its topsep, less the drop without
  let pdfEx : Option Dim.Length := do pure ((← drop "10ex") - (← drop "0pt"))
  let xhAt (sz : Dim.Length) : Dim.Length := oneFace.body.xHeight * sz / oneFace.body.unitsPerEm
  let xh := xhAt size
  let d := (elabStr (src "10ex")).1
  let opening (fonts : Option Font.FontSet) : Option Int := do
    let decls ← screenRuleOf (HtmlDoc.baseCss { fonts := fonts } d) ":where(* + .list-set-1)"
    calcRemMilli (← cssProperty decls "margin-top")
  let screen (v : Dim.Length) : Int := (HtmlDoc.screenMilli size v : Int)
  t "ex lengths: the PDF reads a list's declared 10ex at its body face's x-height"
    (pdfEx == some (10 * xh))
  t "ex lengths: the web page opens that list by the PDF's 10ex where it ships the face"
    (match pdfEx with
     | some v => opening (some oneFace) == some (screen v)
     | none => false)
  let (_, tree, _) := HtmlDoc.emitTree { fonts := some oneFace } d
  let skips := (elemAttrsList (· == "div") #[] tree.toList).filterMap fun (_, attrs) =>
    if (((HtmlDoc.attrOf? attrs "class").getD "").splitOn " ").contains HtmlDoc.skipClass then
      (HtmlDoc.attrOf? attrs "style").bind (cssProperty · "--skip") |>.bind remMilliOf
    else none
  t "ex lengths: the web page's skip box stands the PDF's 10ex where it ships the face"
    (match pdfEx with
     | some v => skips == #[screen v]
     | none => false)
  let parDoc := (elabStr (doc "[10pt]{article}" "\\setlength{\\parskip}{1ex}"
    "Delta paragraph.\n\nEcho paragraph.")).1
  let parskip := (screenRootVars (HtmlDoc.baseCss { fonts := some oneFace } parDoc)).lookup
    "--parskip" |>.bind remMilliOf
  t "ex lengths: the web page's declared parskip of 1ex reads the face it ships"
    (parskip == some (screen xh))
  t "ex lengths: a page shipping no face reads an ex as half an em, its x-height unknown"
    (opening none == some (screen (10 * (size / 2))))
  -- Each length in ex against the same in sp at the face's x-height: one document to both backends.
  let pair (cls : String) (body : String → String) : Ir.Doc × Ir.Doc :=
    let spell (m : Nat) : String := s!"{m / 1000}.{((toString (m % 1000 + 1000)).drop 1).toString}ex"
    let pre (sp : Nat → String) : String :=
      String.join (exLengths.map fun (n, m) => "\\setlength{\\" ++ n ++ "}{" ++ sp m ++ "}\n")
    let exDoc := (elabStr (doc cls (pre spell) (body (spell 2500)))).1
    let at_ := xhAt exDoc.page.fontSize
    let inSp (m : Nat) : String := s!"{((m : Int) * at_ / (1000 : Int)).toSp}sp"
    (exDoc, (elabStr (doc cls (pre inSp) (body (inSp 2500)))).1)
  let places (d : Ir.Doc) : List (Nat × Dim.Length × Dim.Length) :=
    (layoutOf oneFace d).pages.toList.zipIdx.flatMap fun (p, i) =>
      (p.lines.filter (!·.furniture)).toList.map fun l => (i, l.x, l.y)
  -- A declared length's custom property keeps the author's spelling for the browser.
  let spelled (line : String) : Bool :=
    exLengths.any (fun (n, _) => line.startsWith ("    --" ++ n ++ ": ")) &&
      (line.splitOn ";").length == 2 && (line.endsWith "ex;" || line.endsWith "pt;")
  let page (d : Ir.Doc) : String :=
    let (head, tree, _) := HtmlDoc.emitTree { fonts := some oneFace } d
    let css := pageSheets (String.join (head.toList.map (Html.render · 0)))
    "\n".intercalate ((css.splitOn "\n").filter (!spelled ·)) ++
      String.join (tree.toList.map (Html.render · 0))
  for (name, cls, body) in [("an article", "[10pt]{article}", exArticle),
      ("a deck", "{beamer}", exDeck)] do
    let (exDoc, spDoc) := pair cls body
    t s!"ex lengths: {name} declaring its spaces in ex sets the PDF of the same spaces in sp"
      (let a := places exDoc
       let b := places spDoc
       -- Each length in sp is TeX's to the scaled point, so a line stands within one per length.
       let near (x y : Dim.Length) : Bool := (x - y).abs ≤ Dim.Length.ofSp (exLengths.length + 1)
       !a.isEmpty && a.length == b.length &&
         (a.zip b).all fun ((i, x, y), (j, u, v)) => i == j && near x u && near y v)
    t s!"ex lengths: {name} declaring its spaces in ex sets the web page of the same spaces in sp"
      (page exDoc == page spDoc)

end Tests.ListsKoma
