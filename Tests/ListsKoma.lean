module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

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

def doc (cls pre body : String) : String :=
  s!"\\documentclass{cls}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

/-- The space between consecutive lines starting with `words`, past the page's baselineskip, in
tenths of a point; `none` where a word starts no line. -/
def gaps (oneFace : Font.FontSet) (src : String) (words : List String) : Option (List Int) := do
  let (d, _) := elabStr src
  let c := censusOf (coveredColorsOf d) (layoutOf oneFace d)
  let ys ← words.mapM (lineYOf c 0 ·)
  let bs := Ir.baselineSkipOf d.page
  return (ys.zip ys.tail).map fun (a, b) => ((b - a - bs) * 10 + Dim.pt 1 / 2) / Dim.pt 1

/-- A line's first glyph's x: its start past the glyphless runs and gaps before it. -/
def inkStart (l : Layout.LineOut) : Int := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ => if glyphs.isEmpty then x := x + w else return x
    | .gap w _ => x := x + w
    | _ => return x
  return x

/-- The first glyph's x of the first body line holding `word`. -/
def inkOf (out : Layout.Out) (word : String) : Option Int :=
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
  t "koma lists: a KOMA-Script class's parskip option is read, not named"
    (!(elabStr (doc "[parskip=half]{scrartcl}" "" "Alpha.")).2.any (·.code == "W0356"))
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
    let inkAt (w : String) : Int := (inkOf out w).getD 0
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
        (inkStart l - inkAt "Bravo" - want).natAbs ≤ (Dim.pt 1).toNat)
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

/-- The web page sets each quotation kind by its class: quotation's first-line indent and verse's
hung lines, a quote's declared spacing by its spacing's class, and a KOMA-Script nested list's. -/
def quoteKindHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (cls body : String) : String := (HtmlDoc.emit {} (elabStr (doc cls "" body)).1).1
  let q := page "[10pt]{article}" quotes
  t "html quote kinds: a quotation and a verse carry their kind's class"
    (hasStr q "<blockquote class=\"quotation" && hasStr q "<blockquote class=\"verse" &&
      hasStr q "<blockquote>")
  t "html quote kinds: quotation indents its paragraphs by its class's parindent"
    (hasStr q "blockquote.quotation > p { text-indent: 1.5em; }" &&
      hasStr (page "[10pt]{scrartcl}" quotes) "blockquote.quotation > p { text-indent: 1em; }")
  t "html quote kinds: verse hangs each line of a paragraph, each a block of its own"
    (hasStr q "blockquote.verse > p > .verse-line { display: block; padding-left: 1.5em; text-indent: -1.5em; }" &&
      (q.splitOn "<span class=\"verse-line\">").length == 5)
  t "html quote kinds: a page without quotation or verse carries neither rule"
    (let plain := page "[10pt]{article}" "Alpha.\n\n\\begin{quote}Bravo.\\end{quote}"
     !hasStr plain "blockquote.quotation" && !hasStr plain "verse-line")
  let k := page "[10pt]{scrartcl}" nested
  t "html koma lists: a nested KOMA-Script list reads its level's parskip by its spacing's class"
    ((k.splitOn "<ul>").length == 2 && (k.splitOn "<ul class=\"list-set-1 ").length == 3)

end Tests.ListsKoma
