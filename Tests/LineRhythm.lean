module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim

namespace Tests.LineRhythm

/-- The line pitches a source's shipped page sets. -/
private def pitchesOf (fs : Font.FontSet) (src : String) : Array Sp :=
  baselinePitches (layoutOf fs (elabStr src).1)

/-- The baselines a source's body lines stand on, in page order. -/
private def baselines (fs : Font.FontSet) (src : String) : Array Sp :=
  (bodyLines (layoutOf fs (elabStr src).1)).map (·.y)

/-- Two lines forced apart inside one paragraph, the paragraph set wholly
in `step`: the line pitch is the step's own. Invented words only. -/
private def stepPara (step : String) : String :=
  s!"\{\\{step} Alpha one\\\\Bravo two\\par}"

/-- **A paragraph set in a named size stands its lines at that size's
`\baselineskip`** (size10.clo's `\@setfontsize` rows, measured under
lualatex by the rhythm tier's `article-steps` and `slides-steps`
fixtures), asserted on the shipped page. Before the step carried its own
leading every line stood on the body's strut: a `\footnotesize`
paragraph's lines 12 pt apart where LaTeX sets 9.5, and a `\LARGE` one's
at 6⁄5 of its size, 1.3 pt tight. A body paragraph keeps the body's pitch
around a small run, a footnote stands at `\footnotesize`'s, and the page's
`\linespread` scales a step's leading as `\selectfont` scales any. -/
def stepLeadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- size10.clo's `\baselineskip` per step, hundredths of a point.
  let skips : List (String × Int) :=
    [("tiny", 600), ("scriptsize", 800), ("footnotesize", 950), ("small", 1100),
     ("normalsize", 1200), ("large", 1400), ("Large", 1800), ("LARGE", 2200),
     ("huge", 2500), ("Huge", 3000)]
  for (name, skip) in skips do
    let ps := pitchesOf oneFace (metricDoc (stepPara name))
    t s!"a paragraph set in '\\{name}' stands its lines at size10.clo's {skip / 100}.{skip % 100} pt"
      (ps == #[pt skip / 100])
  t "a body paragraph keeps the body's pitch around a small run"
    (pitchesOf oneFace (metricDoc
      "Alpha one {\\small Charlie} one\\\\Bravo two\\par") == #[pt 12])
  let frame := "\\documentclass[10pt]{beamer}\n\\begin{document}\n\\begin{frame}[t]\n" ++
    "Opening line.\n\n\\footnotesize\nAlpha one\\\\Bravo two\n\nCharlie three\\\\Delta four\n" ++
    "\\end{frame}\n\\end{document}"
  let fys := baselines oneFace frame
  t "a frame's footnotesize declaration sets every paragraph after it at 9.5 pt"
    (fys.size == 5 && fys[2]! - fys[1]! == pt 95 / 10 && fys[4]! - fys[3]! == pt 95 / 10)
  t "a footnote's lines stand at the footnotesize step's leading"
    (let notes := (layoutOf oneFace (elabStr (metricDoc
        "Alpha words.\\footnote{Bravo note\\\\Charlie note}")).1).pages.flatMap
          (·.lines.filter fun l => l.note && !(lineText l).isEmpty)
     notes.size == 2 && notes[1]!.y - notes[0]!.y == pt 95 / 10)
  t "the page's linespread scales a step's leading"
    (pitchesOf oneFace
      ("\\documentclass{article}\n\\linespread{1.5}\n\\begin{document}\n" ++
        stepPara "small" ++ "\n\\end{document}") == #[pt 165 / 10])

/-- The HTML elements whose class list carries `c`. -/
private def withClassIn (nodes : Array Html.Node) (c : String) : Array Html.Node :=
  (elemNodesList (fun _ => true) #[] nodes.toList).filter fun n => match n with
    | .elem _ attrs _ => attrs.any fun (k, v) => k == "class" && (v.splitOn " ").contains c
    | _ => false

/-- **The HTML sets a paragraph's named size where the page does**: the
step's class on the paragraph element itself, so the element's own line
box is the step's, and on a deck the step's leading as that element's line
height — the page's projection, where a reading page keeps the screen's one
line height. A span inside the element left the body's strut under every
line. A size span states no line height of its own: it inherits its
block's, as the page leads a run in its paragraph's proportion
(`Ir.runLead`), so a smaller span never moves its line. -/
def htmlStepChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (_, body, _) := HtmlDoc.emitTree {} (elabStr (metricDoc (stepPara "small"))).1
  let small := withClassIn body "size-small"
  t "a paragraph set wholly in a step carries the step's class itself"
    (small.size == 1 && small.all (· matches .elem "p" _ _))
  let (_, mixed, _) := HtmlDoc.emitTree {} (elabStr (metricDoc
    "Alpha one {\\small Charlie} one\\\\Bravo two\\par")).1
  t "a body paragraph keeps a small run as a span"
    ((withClassIn mixed "size-small").all (· matches .elem "span" _ _) &&
      (withClassIn mixed "size-small").size == 1)
  let article := (HtmlDoc.emit {} (elabStr (metricDoc (stepPara "small"))).1).1
  t "a reading page's steps keep the screen's line height"
    (hasStr article ".size-small { font-size: 0.900em; }")
  let deckDoc := (elabStr ("\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}[t]\nOpening.\n\n" ++ stepPara "small" ++ "\n\\end{frame}\n\\end{document}")).1
  let deck := (HtmlDoc.emit {} deckDoc).1
  t "a deck's steps set their own leading as line heights of the blocks they set"
    (hasStr deck ".size-small.lead-small { line-height: 1.222; }" &&
      hasStr deck ".size-footnotesize.lead-footnotesize { line-height: 1.188; }" &&
      hasStr deck ".size-LARGE.lead-LARGE { line-height: 1.273; }")
  t "a deck's size class states no line height of its own"
    (hasStr deck ".size-small { font-size: 0.900em; }" &&
      !hasStr deck ".size-small { font-size: 0.900em; line-height")
  let (_, deckNodes, _) := HtmlDoc.emitTree {} deckDoc
  t "a deck's paragraph set wholly in a step carries the step's leading"
    ((withClassIn deckNodes "lead-small").size == 1 &&
      (withClassIn deckNodes "lead-small").all fun n =>
        (n matches .elem "p" _ _) && (withClassIn #[n] "size-small").size == 1)
  let (_, deckMixed, _) := HtmlDoc.emitTree {} (elabStr ("\\documentclass[10pt]{beamer}\n" ++
    "\\begin{document}\n\\begin{frame}[t]\nAlpha one {\\small Charlie} one\\\\Bravo two\\par\n" ++
    "\\end{frame}\n\\end{document}")).1
  t "a deck's small run inside a body paragraph is a span with no leading of its own"
    ((withClassIn deckMixed "size-small").size == 1 &&
      (withClassIn deckMixed "size-small").all (· matches .elem "span" _ _) &&
      (withClassIn deckMixed "lead-small").isEmpty)
  -- The 4:3 stage is 96 mm (272.126 pt) high: the 10 pt body is 3.674% of
  -- it, and the root — the body at 12/14.5 — 3.041%, so the sheet's
  -- quantum `0.725rem` is the page's 6 pt on the stage.
  t "a deck's body sets the page's leading, not the screen's"
    (hasStr deck "font-size: 3.674vh; line-height: 1.200;")
  t "a deck's root size is the stage's rhythm unit"
    (hasStr deck "html { font-size: 3.041vh; }")

/-- **A declared paragraph gap reaches the screen at its length**: `\parskip`
in `em` is evaluated once at the body, as TeX evaluates `\setlength`, and
lands as its multiple of the screen's quantum; reading only the length's
point part dropped every font-relative declaration — `\setlength{\parskip}
{0.5em}`, the parskip package's `0.6em` — to zero. A deck's `\bigskip`
stands its share of the stage, never a fixed CSS length. -/
def htmlGapChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let page (pre : String) := (HtmlDoc.emit {} (elabStr (dvDoc pre "Alpha.\n\nBravo.")).1).1
  t "an em parskip reaches the screen as its multiple of the quantum"
    (hasStr (page "\\setlength{\\parskip}{0.5em}\n") "--parskip: 0.604rem;")
  t "the parskip package's half line reaches the screen"
    (hasStr (page "\\usepackage{parskip}\n") "--parskip: 0.725rem;")
  let deckDoc := (elabStr ("\\documentclass[10pt]{beamer}\n" ++
    "\\setlength{\\parskip}{0.5em}\n\\begin{document}\n\\begin{frame}[t]\nAlpha.\n\n" ++
    "\\bigskip\n\nBravo.\n\\end{frame}\n\\end{document}")).1
  let deck := (HtmlDoc.emit {} deckDoc).1
  t "a deck's em parskip reaches the stage"
    (hasStr deck "--parskip: 0.604rem;")
  t "a deck's bigskip stands its 12 pt share of the 96 mm stage"
    (hasStr deck "margin-top: 4.409vh" && !hasStr deck "margin-top: 12pt")

/-- Invented prose, long enough to break across several lines of a frame. -/
private def longPara : String :=
  String.intercalate " " (List.replicate 6
    "Alder birch cedar dogwood elm fir hazel juniper larch maple oak pine rowan spruce")

/-- Whether a ragged line holds every word that fits: the next line's first
word, one space after this line's end, would stand past the measure. -/
private def lineFillsTo (l : Layout.LineOut) (space : Sp) (next : Layout.LineOut)
    (measure : Sp) : Bool :=
  let first := (next.segs.toList.takeWhile fun sg => match sg with
      | .gap _ _ | .decoratedGap _ _ _ => false
      | _ => true).foldl (fun w sg => match sg with
      | .run _ _ _ rw _ _ _ _ _ _ _ => w + rw
      | _ => w) 0
  measure < l.setWidth + space + first

/-- **A beamer frame sets its text ragged right**, as beamer.cls's own
`\raggedright` does for every frame (measured under lualatex: the lines
of a frame paragraph end where their words end, none hyphenated), while an
article's lines stand justified to the measure; the HTML hyphenates only
where the page would, so a deck's paragraphs break at spaces. Before, a
frame's lines were stretched to the measure and hyphenated, in both
artifacts. -/
def raggedFrameChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deckSrc := "\\documentclass[10pt]{beamer}\n\\begin{document}\n\\begin{frame}[t]\n" ++
    longPara ++ "\n\\end{frame}\n\\end{document}"
  let (deck, _) := elabStr deckSrc
  let measure := deck.page.width - 2 * deck.page.hmargin
  let lines := bodyLines (layoutOf oneFace deck)
  let inner := lines.extract 0 (lines.size - 1)
  t "a frame paragraph breaks across several lines" (lines.size ≥ 3)
  t "a frame's lines stand within the measure" (lines.all (·.setWidth ≤ measure))
  t "a frame's lines end ragged, where their words end"
    (inner.any fun l => l.setWidth < measure - pt 2)
  t "a frame's lines end on whole words" (lines.all fun l => !(lineText l).endsWith "-")
  -- LaTeX's `\raggedright` leaves no line loose (`\rightskip 0pt plus 1fil`),
  -- and TeX keeps the latest of equal demerits: each line takes every word
  -- that fits, so the next line's first word, after one space, would not.
  t "a frame's lines take every word that fits, as LaTeX's raggedright sets them"
    (lines.size ≥ 3 && (List.range (lines.size - 1)).all fun i =>
      let l := lines[i]!
      let space := l.segs.foldl (fun m sg => match sg with
        | .gap w true => max m w
        | _ => m) 0
      lineFillsTo l space (lines[i + 1]!) measure)
  let (art, _) := elabStr (metricDoc longPara)
  let artMeasure := art.page.width - 2 * art.page.hmargin
  let artLines := bodyLines (layoutOf oneFace art)
  t "an article's lines stand justified to the measure"
    (artLines.size ≥ 3 && (artLines.extract 0 (artLines.size - 1)).all fun l =>
      artMeasure - pt 1 ≤ l.setWidth)
  t "a deck's paragraphs hyphenate nothing on their own"
    (hasStr (HtmlDoc.emit {} deck).1 "p { hyphens: manual; }")
  t "an article's paragraphs keep the browser's hyphenation"
    (hasStr (HtmlDoc.emit {} art).1 "p { hyphens: auto; }")
  -- ragged2e is not read: its declarations name the page key that sets a
  -- deck's frames justified, and that key does.
  let deck (pre : String) := "\\documentclass[10pt]{beamer}\n" ++ pre ++
    "\\begin{document}\n\\begin{frame}[t]\n\\justifying\n" ++ longPara ++
    "\n\\end{frame}\n\\end{document}"
  t "ragged2e's justifying names the key that justifies a deck"
    ((dvE (deck "\\usepackage{ragged2e}\n")).any fun d =>
      d.code == "W0301" && hasStr (d.help.getD "") "\\page{ justify = on }")
  let (onDoc, _) := elabStr (deck "\\page{ justify = on }\n")
  let onLines := bodyLines (layoutOf oneFace onDoc)
  t "a deck that declares its text justified sets its frames to the measure"
    (onLines.size ≥ 3 && (onLines.extract 0 (onLines.size - 1)).all fun l =>
      measure - pt 1 ≤ l.setWidth)

/-- **A listing's lines stand at its size's leading, less what its package
takes off each line**: a bare `verbatim` under `\\footnotesize` at the
step's 9.5 pt, as lualatex sets it (9.464 bp), and a minted listing 0.25 pt
tighter, fvextra's overlap after every line (lualatex: 9.215 bp), twice
after its first (8.966 bp); the HTML `pre` states the later pitch over its
font size. Before, both stood at 6⁄5 of 8 pt, 9.6 pt, on both artifacts. -/
def listingPitchChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let code := "alpha = 1\nbravo = 2\ncharlie = 3\n"
  let verbatim := dvDoc "" ("{\\footnotesize\n\\begin{verbatim}\n" ++ code ++ "\\end{verbatim}\n}")
  let minted := dvDoc "\\usepackage{minted}\n\\setminted{fontsize=\\footnotesize}\n"
    ("\\begin{minted}{python}\n" ++ code ++ "\\end{minted}")
  t "a footnotesize verbatim's lines stand at the step's 9.5 pt"
    (pitchesOf oneFace verbatim == #[pt 95 / 10, pt 95 / 10])
  t "a minted listing's lines stand fvextra's 0.25 pt under the step, twice after the first"
    (pitchesOf oneFace minted == #[pt 9, pt 925 / 100])
  t "the HTML sets a verbatim's pitch over its size"
    (hasStr (HtmlDoc.emit {} (elabStr verbatim).1).1 "line-height: 1.187;")
  t "the HTML sets a minted listing's pitch over its size"
    (hasStr (HtmlDoc.emit {} (elabStr minted).1).1 "line-height: 1.156;")

/-- The largest run size a shipped line carries, `0` on a line of none. -/
private def runSize (l : Layout.LineOut) : Sp :=
  l.segs.foldl (fun m s => match s with
    | .run _ _ _ _ _ sz _ _ _ _ _ => max m sz
    | _ => m) 0

/-- Consecutive shipped body lines of one size, with the pitch between them. -/
private def sizedPitches (out : Layout.Out) : Array (Sp × Sp) :=
  let ls := (bodyLines out).filter (0 < runSize ·)
  ((ls.zip (ls.extract 1 ls.size)).filter fun (a, b) => runSize a == runSize b).map
    fun (a, b) => (runSize b, b.y - a.y)

/-- Invented display words, long enough to wrap a heading, a title or a frame
title across lines. -/
private def longTitle : String :=
  "Alder birch cedar dogwood elm fir hazel juniper larch maple oak pine rowan spruce yew"

/-- **A size command inside a display sets its lines in the size file's
proportion to their type**: a heading's, a title's or a frame title's
content set in a named step stands on that step's leading of the display
size the step scales (`Ir.stepLead`), so its wrapped lines clear their
type within the size file's band, 8⁄7 to 9⁄7 (`Ir.stepLead_between`),
asserted on the shipped page. Read off the body's column instead, a
`\LARGE` section title's lines set solid and a `\small` frame title's
lines overlapped; a display under no size command keeps the 6⁄5 rule of
its own size, inside the same band. -/
def displayStepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- 8⁄7 ≤ pitch ⁄ size: a line never stands closer than the size file's
  -- tightest proportion to its type, a sp of rounding per line
  let clears (out : Layout.Out) : Bool :=
    let ps := sizedPitches out
    !ps.isEmpty && ps.all fun (sz, p) => 8 * sz ≤ 7 * p + 8
  -- and, a display wholly in one step, no looser than its loosest, 9⁄7
  let banded (out : Layout.Out) : Bool :=
    clears out && (sizedPitches out).all fun (sz, p) => 7 * p ≤ 9 * sz + 9
  let art (pre body : String) : Layout.Out :=
    layoutOf oneFace (elabStr (dvDoc pre body)).1
  let deck (pre body : String) : Layout.Out :=
    layoutOf oneFace (elabStr ("\\documentclass[10pt]{beamer}\n" ++ pre ++
      "\\begin{document}\n" ++ body ++ "\n\\end{document}")).1
  t "a LARGE section title's lines stand in the step's proportion"
    (banded (art "" ("\\section*{\\LARGE " ++ longTitle ++ "}")))
  t "a small section title's lines stand in the step's proportion"
    (banded (art "" ("\\section*{\\small " ++ longTitle ++ " " ++ longTitle ++ "}")))
  -- a number set beside the title holds the heading's own strut under it
  t "a numbered LARGE section title's lines clear their type"
    (clears (art "" ("\\section{\\LARGE " ++ longTitle ++ "}")))
  t "a numbered small section title's lines clear their type"
    (clears (art "" ("\\section{\\small " ++ longTitle ++ " " ++ longTitle ++ "}")))
  t "a Huge document title's lines stand in the step's proportion"
    (banded (art ("\\title{\\Huge " ++ longTitle ++ "}\n\\author{Kilo Lima}\n\\date{}\n")
      "\\maketitle"))
  t "a small frame title's lines stand in the step's proportion"
    (banded (deck "" ("\\begin{frame}{\\small " ++ longTitle ++ " " ++ longTitle ++ "}\n" ++
      "Body words.\n\\end{frame}")))
  t "a frame title under no size command keeps the six-fifths rule"
    (banded (deck "" ("\\begin{frame}{" ++ longTitle ++ "}\nBody words.\n\\end{frame}")))
  t "a deck title page's LARGE title lines stand in the step's proportion"
    (banded (deck ("\\title{{\\LARGE " ++ longTitle ++ "}}\n\\author{Kilo Lima}\n")
      "\\begin{frame}\n\\titlepage\n\\end{frame}"))

/-- The value the last `sel` rule of a stylesheet's text declares for
`prop`, scanning in source order: what the cascade leaves where the rules
share one specificity and every one of them applies. -/
private def lastDeclared (css sel prop : String) : Option String :=
  ((css.splitOn ("\n" ++ sel ++ " {")).drop 1).foldl (fun acc chunk =>
    let body := (chunk.splitOn "}").head!
    let found := (body.splitOn ";").findSome? fun d =>
      match d.splitOn ":" with
      | k :: v :: _ => if k.trimAscii.toString == prop then some v.trimAscii.toString else none
      | _ => none
    found.orElse fun _ => acc) none

/-- **A deck's listing is the page's**: on the stage a `pre` carries none of
the reading page's code box — no padding, no ground — as the page pads no
listing and paints none under one, where a reading page keeps its box. The
stage's root is its rhythm unit, so the box's rem padding grew with it and
pushed a slide that fits its page past its stage. -/
def deckListingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let code := "alpha = 1\nbravo = 2\n"
  let body := "Opening words.\n\n\\begin{verbatim}\n" ++ code ++ "\\end{verbatim}"
  let deckDoc := (elabStr ("\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}[t]\n" ++ body ++ "\n\\end{frame}\n\\end{document}")).1
  let lines := bodyLines (layoutOf oneFace deckDoc)
  t "the page sets a frame's listing at the text's own edge"
    (lines.size == 3 && lines.all (·.x == lines[0]!.x))
  let deck := (HtmlDoc.emit {} deckDoc).1
  t "the stage pads no listing" (lastDeclared deck "pre" "padding" == some "0")
  t "the stage paints no ground under a listing"
    (lastDeclared deck "pre" "background" == some "none")
  let art := (HtmlDoc.emit {} (elabStr (dvDoc "" body)).1).1
  t "a reading page keeps its code box"
    ((lastDeclared art "pre" "padding").any (· != "0") &&
      lastDeclared art "pre" "background" == some "var(--tint)")

/-- The distinct baselines a source's body lines stand on, in page order, and
the distances between them: a table's row pitch, one per row, whatever the
number of cells a row sets. -/
private def rowPitches (fs : Font.FontSet) (src : String) : Array Sp :=
  let ys := (bodyLines (layoutOf fs (elabStr src).1)).foldl (fun (acc : Array Sp) l =>
    if acc.back? == some l.y then acc else acc.push l.y) #[]
  (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a

/-- **A table's rows stand on the strut of the size the table began under**,
in both artifacts: LaTeX's `\@arstrut` is the strut in force where the
`tabular` opened, so a cell that sets its own size changes its type, never
its row — lualatex keeps three `\small` cells' rows 11.955 bp apart, the
body's 12 pt, and a table opened under `\small` sets its rows at the step's
11 pt (10.955 bp) and its `p`-column paragraphs' wrapped lines at the step's
leading. Before, a cell set wholly in one size took the step's strut, and
its row stood 11 pt below the last. The HTML cell carries the size the row
stands under (`Ir.paraStep?`); a cell's own size stays a span. -/
def cellStepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let perCell := dvDoc "" ("\\begin{tabular}{ll}\n\\small Alpha & \\small one\\\\\n" ++
    "\\small Bravo & \\small two\\\\\n\\small Charlie & \\small three\\\\\n\\end{tabular}")
  t "a table whose cells set their own size keeps the body's row strut"
    (rowPitches oneFace perCell == #[pt 12, pt 12])
  let underSmall := dvDoc "" ("{\\small\n\\begin{tabular}{ll}\nDelta & four\\\\\n" ++
    "Echo & five\\\\\nFoxtrot & six\\\\\n\\end{tabular}\\par}")
  t "a table opened under a size declaration sets its rows at the step's strut"
    (rowPitches oneFace underSmall == #[pt 11, pt 11])
  let wrapped := dvDoc "" ("{\\small\n\\begin{tabular}{p{3cm}}\n" ++ longTitle ++
    "\n\\end{tabular}\\par}")
  t "a p-column under a size declaration wraps at the step's 11 pt"
    (let ps := pitchesOf oneFace wrapped
     !ps.isEmpty && ps.all (· == pt 11))
  let (_, nodes, _) := HtmlDoc.emitTree {} (elabStr perCell).1
  t "the HTML cell that sets its own size keeps the size a span"
    ((withClassIn nodes "size-small").size == 6 &&
      (withClassIn nodes "size-small").all (· matches .elem "span" _ _))
  let (_, nodes, _) := HtmlDoc.emitTree {} (elabStr underSmall).1
  t "the HTML cell under a size declaration carries the step's class itself"
    ((withClassIn nodes "size-small").size == 6 &&
      (withClassIn nodes "size-small").all (· matches .elem "td" _ _))

/-- **A paragraph leads at the size in force where it ends**, on the shipped
page: LaTeX reads `\baselineskip` at `\par`, so a size group closed before
its paragraph ends leaves the body's leading under the paragraph's lines
(lualatex: `{\small A\\B}\par` stands its lines 11.955 bp apart, the body's
12 pt), while `{\small A\\B\par}`, a `\small` declaration over the
paragraph, and a nested size group ending the paragraph inside it lead at
their step (`Ir.paraAt`, `Ir.paraStep_paraAt_exact`). The HTML gives the step
to the paragraph element only where it is in force at the end. Before, the
closed group led at the step, a point tight, and a `\Huge` group at a page's
top stood its line 11.6 bp low. -/
def paraEndChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "a size group closed before the paragraph ends leaves the body's leading"
    (pitchesOf oneFace (metricDoc "{\\small Alpha one\\\\Bravo two}\\par") == #[pt 12])
  t "a size group ending its paragraph inside it leads at the step"
    (pitchesOf oneFace (metricDoc "{\\small Alpha one\\\\Bravo two\\par}") == #[pt 11])
  t "a group closed inside a size declaration leaves the declaration's leading"
    (pitchesOf oneFace (metricDoc "{\\small {\\footnotesize Alpha one\\\\Bravo two}\\par}") ==
      #[pt 11])
  t "the last of nested size declarations in force sets the leading"
    (pitchesOf oneFace (metricDoc "{\\small {\\footnotesize Alpha one\\\\Bravo two\\par}}") ==
      #[pt 95 / 10])
  let (_, closed, _) := HtmlDoc.emitTree {} (elabStr (metricDoc
    "{\\small Alpha one\\\\Bravo two}\\par")).1
  t "the HTML keeps a closed size group a span inside its paragraph"
    ((withClassIn closed "size-small").size == 1 &&
      (withClassIn closed "size-small").all (· matches .elem "span" _ _) &&
      (withClassIn closed "size-normalsize").isEmpty)
  let (_, nested, _) := HtmlDoc.emitTree {} (elabStr (metricDoc
    "{\\small {\\footnotesize Alpha one\\\\Bravo two\\par}}")).1
  t "the HTML sets the last size in force on the paragraph, and only it"
    ((withClassIn nested "size-footnotesize").all (· matches .elem "p" _ _) &&
      (withClassIn nested "size-footnotesize").size == 1 &&
      (withClassIn nested "size-small").isEmpty)

/-- A venue's size ladder as a style it ships declares one: `\@setfontsize`
rows for the body and some of its steps (invented values, in a venue's shape:
a 10/10.95 body, steps that declare their own skips). -/
private def venuePre : String :=
  "\\makeatletter\n" ++
  "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt}\n" ++
  "\\renewcommand{\\footnotesize}{\\@setfontsize\\footnotesize\\@ixpt\\@xpt}\n" ++
  "\\renewcommand{\\scriptsize}{\\@setfontsize\\scriptsize\\@viipt\\@viiipt}\n" ++
  "\\renewcommand{\\tiny}{\\@setfontsize\\tiny\\@vipt\\@viipt}\n" ++
  "\\renewcommand{\\large}{\\@setfontsize\\large{14}{15}}\n" ++
  "\\makeatother\n"

/-- **Under a size ladder a document declares, each step leads at the skip it
declares** (fntguide's `\@setfontsize`, its third argument), measured under
lualatex on the venue probe: `\footnotesize` 9/10 at 9.96 bp, `\scriptsize`
7/8 at 7.97, `\tiny` 6/7 at 6.97, a `\large` declared 14/15 at 15, and a
step the venue leaves alone at size10.clo's own skip (`\small` 11 pt). The
column holds the declared skips (`Ir.setSkip`, `Ir.skipRowOf_between`) and
every step leads in its proportion to the body's (`Ir.stepLead_ratio_between`),
to the page factor's milli rounding. Before, every step read size10.clo's
column under the venue's tighter body factor: `\footnotesize` set 8.68 bp
lines on 9 pt type, `\large` solid. -/
def venueLadderChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let near (a b : Sp) : Bool := (a - b).natAbs ≤ (pt 1 / 100).natAbs
  for (name, skip) in [("tiny", 700), ("scriptsize", 800), ("footnotesize", 1000),
      ("normalsize", 1095), ("large", 1500), ("small", 1100), ("Large", 1800)] do
    let ps := pitchesOf oneFace (dvDoc venuePre (stepPara name))
    t s!"under a declared ladder '\\{name}' leads at {skip / 100}.{skip % 100} pt"
      (ps.size == 1 && near ps[0]! (pt skip / 100))
  let code := "{\\footnotesize\n\\begin{verbatim}\nalpha = 1\nbravo = 2\n\\end{verbatim}\n}"
  t "a listing in a declared step leads at the declared skip"
    (let ps := pitchesOf oneFace (dvDoc venuePre code)
     ps.size == 1 && near ps[0]! (pt 10))
  -- The body's skip declared natively, the spelling a class's `\normalsize`
  -- reads as: the body's lines at it, a step it leaves alone at size10.clo's.
  let native (body : String) := dvDoc "\\page{ fontsize = 10pt, baselineskip = 11pt }\n" body
  t "a declared body skip sets the body's lines at it"
    (let ps := pitchesOf oneFace (native (stepPara "normalsize"))
     ps.size == 1 && near ps[0]! (pt 11))
  t "a declared body skip leaves an undeclared step at size10.clo's skip"
    (let ps := pitchesOf oneFace (native (stepPara "footnotesize"))
     ps.size == 1 && near ps[0]! (pt 95 / 10))
  let (doc, _) := elabStr (dvDoc venuePre "Alpha words.")
  t "the declared skips stand as the document's skip column"
    (doc.page.skipScale.lookup "footnotesize" == some 1000 &&
      doc.page.skipScale.lookup "normalsize" == some 1095 &&
      doc.page.skipScale.lookup "small" == some 1100)
  -- A footnote sets in the document's own `\footnotesize`, its size and its
  -- skip from the one ladder and column: lualatex sets the venue's notes at
  -- 8.97 bp type on a 9.96 bp pitch. Before, the note took the engine's 8 pt
  -- type on the venue's 10 pt skip.
  let notes := (layoutOf oneFace (elabStr (dvDoc venuePre
      "Alpha words.\\footnote{Bravo note\\\\Charlie note}")).1).pages.flatMap
        (·.lines.filter fun l => l.note && !(lineText l).isEmpty)
  let noteSizes := notes.flatMap fun l => l.segs.filterMap fun sg => match sg with
    | .run _ _ _ _ _ sz _ _ _ _ _ => some sz
    | _ => none
  t "a footnote under a declared ladder sets at its declared footnotesize and skip"
    (notes.size == 2 && near (notes[1]!.y - notes[0]!.y) (pt 10) &&
      noteSizes.contains (pt 9) && !noteSizes.contains (pt 8))
  -- The body's skip and `\linespread` compose, as `\selectfont` stretches the
  -- skip a size command sets, whatever order a block or two blocks state
  -- them in: 11 pt stretched 1.5 is 16.5. Before, the skip was read at the
  -- size in force where its key stood, and each overwrote the other.
  let skipped (pre : String) : Array Sp := pitchesOf oneFace (dvDoc pre (stepPara "normalsize"))
  for (name, pre, want) in [
      ("before the size", "\\page{ baselineskip = 14pt, fontsize = 12pt }\n", pt 14),
      ("after the size", "\\page{ fontsize = 12pt, baselineskip = 14pt }\n", pt 14),
      ("before the stretch", "\\page{ baselineskip = 11pt }\n\\linespread{1.5}\n", pt 165 / 10),
      ("after the stretch", "\\linespread{1.5}\n\\page{ baselineskip = 11pt }\n", pt 165 / 10),
      ("beside the stretch", "\\page{ leading = 1.5, baselineskip = 11pt }\n", pt 165 / 10)] do
    let ps := skipped pre
    t s!"a declared body skip {name} sets the body's lines at its stretched length"
      (ps.size == 1 && near ps[0]! want)

/-- A paragraph holding smaller inline runs on every line — a small, a
footnotesize and a scriptsize word, a formula — between forced breaks:
invented words only. -/
private def mixedRuns : String :=
  "Alpha one {\\small Charlie} one\\\\Bravo {\\footnotesize two} words\\\\" ++
    "Delta {\\scriptsize three} $x$ four\\\\Echo five\\par"

/-- **A smaller inline run never moves its line** (`Ir.runLead`), under every
skip column the page reads: size10.clo's, a body skip the document declares
tighter than its 6⁄5 (`\page{ baselineskip = 11pt }`), and a venue's
`\normalsize` of 10/10.95 that leaves `\small` undeclared. LaTeX reads one
`\baselineskip` at a paragraph's `\par`, and a run adds only its ink:
lualatex stands every line of such a paragraph at the body's skip, the closed
`{\small A\\B}\par` group's included (10.91 bp under the venue's 10.95 pt).
Before, each run carried its own step's leading into its line box: under the
tighter columns every line holding a small run stood about 0.35 pt low, and
the closed group led at the step's skip. -/
def inlineRunChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let near (a b : Sp) : Bool := (a - b).natAbs ≤ (pt 1 / 100).natAbs
  let venueBody := "\\makeatletter\n" ++
    "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt}\n\\makeatother\n"
  for (name, pre, lead) in [("size10.clo's column", "", pt 12),
      ("a declared body skip", "\\page{ fontsize = 10pt, baselineskip = 11pt }\n", pt 11),
      ("a venue's body", venueBody, pt 1095 / 100)] do
    let ps := pitchesOf oneFace (dvDoc pre mixedRuns)
    t s!"under {name} every line with a smaller run stands at the body's leading"
      (ps.size == 3 && ps.all (near · lead))
    let closed := pitchesOf oneFace (dvDoc pre "{\\small Alpha one\\\\Bravo two}\\par")
    t s!"under {name} a closed small group leads at the body's leading"
      (closed.size == 1 && closed.all (near · lead))

/-! ### The gap sheet's cascade on the typed tree

What a browser's cascade gives an element's `margin-top`, read off the
emitted tree and its sheet with no browser: compounds of type, class and
attribute selectors (presence, `=`, `~=`), `:first-child`, `:last-child`,
`:not()`, `:is()`, `:where()` and `:has()` with relative selectors, the four
combinators, specificity, source order, and the element's own `style`. A rule
inside an `@media` block or an `@supports not` block is not the screen's
default and is skipped. The subset the engine's sheets are written in, read
as a browser reads it — never the generator's own patterns. -/

/-- One element of a flattened tree. -/
private structure CEl where
  tag : String := ""
  attrs : Array (String × String) := #[]
  parent : Option Nat := none
  text : String := ""
  deriving Inhabited

mutual

private def flatOne (parent : Option Nat) (acc : Array CEl) : Html.Node → Array CEl
  | .elem tag attrs kids =>
    flatList (some acc.size)
      (acc.push { tag, attrs, parent, text := nodeTextList "" kids.toList }) kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def flatList (parent : Option Nat) (acc : Array CEl) : List Html.Node → Array CEl
  | [] => acc
  | n :: rest => flatList parent (flatOne parent acc n) rest

end

/-- A flattened tree: its elements in document order, each one's element
children, and the roots. -/
private structure CTree where
  els : Array CEl
  kids : Array (Array Nat)
  roots : Array Nat

private def CTree.of (nodes : Array Html.Node) : CTree := Id.run do
  let els := flatList none #[] nodes.toList
  let mut kids : Array (Array Nat) := Array.replicate els.size #[]
  let mut roots : Array Nat := #[]
  for i in [0:els.size] do
    match (els[i]?.bind (·.parent)) with
    | some p => kids := kids.modify p (·.push i)
    | none => roots := roots.push i
  return { els, kids, roots }

private def CTree.el (t : CTree) (i : Nat) : CEl := t.els[i]?.getD default

private def CTree.siblings (t : CTree) (i : Nat) : Array Nat :=
  match (t.el i).parent with
  | some p => t.kids[p]?.getD #[]
  | none => t.roots

/-- The element siblings before `i`, nearest first. -/
private def CTree.before (t : CTree) (i : Nat) : List Nat :=
  ((t.siblings i).toList.takeWhile (· != i)).reverse

/-- The element siblings after `i`. -/
private def CTree.after (t : CTree) (i : Nat) : List Nat :=
  ((t.siblings i).toList.dropWhile (· != i)).drop 1

/-- `i`'s ancestors, nearest first. -/
private def CTree.ancestors (t : CTree) (i : Nat) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut cur := (t.el i).parent
  for _ in [0:t.els.size] do
    match cur with
    | some p =>
      out := out.push p
      cur := (t.el p).parent
    | none => break
  return out.toList

private def CTree.descendants (t : CTree) (i : Nat) : List Nat :=
  ((List.range t.els.size).filter fun j => (t.ancestors j).contains i)

private def CTree.attr? (t : CTree) (i : Nat) (k : String) : Option String :=
  ((t.el i).attrs.find? (·.1 == k)).map (·.2)

/-- `s`'s parts at the separators `sep` no parenthesis or bracket encloses. -/
private def cssSplit (sep : Char) (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth : Nat := 0
  for c in s.toList do
    if c == sep && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else
      if c == '(' || c == '[' then depth := depth + 1
      if c == ')' || c == ']' then depth := depth - 1
      cur := cur.push c
  return ((out.push cur.trimAscii.toString).filter (!·.isEmpty)).toList

/-- One simple selector of a compound. -/
private inductive CPart where
  | type (t : String)
  | cls (c : String)
  | attr (name op value : String)
  | pseudo (name arg : String)

private def cssIdent (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- The identifier starting at `j`, and where it ends. -/
private def cssIdentAt (cs : Array Char) (j : Nat) : String × Nat := Id.run do
  let mut k := j
  let mut s := ""
  for _ in [0:cs.size] do
    match cs[k]? with
    | some ch =>
      if cssIdent ch then
        s := s.push ch
        k := k + 1
      else break
    | none => break
  return (s, k)

/-- `s` without the double quotes around it. -/
private def cssUnquote (s : String) : String :=
  String.ofList ((s.trimAscii.toString.toList.dropWhile (· == '"')).reverse.dropWhile
    (· == '"')).reverse

/-- A compound's simple selectors, scanned left to right. -/
private def cssCompound (c : String) : List CPart := Id.run do
  let cs := c.toList.toArray
  let mut out : Array CPart := #[]
  let mut i := 0
  -- the type, or the universal selector
  if cs[0]? == some '*' then
    out := out.push (.type "*")
    i := 1
  else
    let (s, j) := cssIdentAt cs 0
    if !s.isEmpty then
      out := out.push (.type s)
      i := j
  for _ in [0:cs.size] do
    match cs[i]? with
    | some '.' =>
      let (s, j) := cssIdentAt cs (i + 1)
      out := out.push (.cls s)
      i := j
    | some '[' =>
      let close := ((List.range cs.size).find? fun k => i < k && cs[k]? == some ']').getD cs.size
      let body := String.ofList (cs.extract (i + 1) close).toList
      let (name, op, value) := match body.splitOn "~=" with
        | [n, v] => (n, "~=", v)
        | _ => match body.splitOn "=" with
          | [n, v] => (n, "=", v)
          | _ => (body, "", "")
      out := out.push (.attr name.trimAscii.toString op (cssUnquote value))
      i := close + 1
    | some ':' =>
      let (name, j) := cssIdentAt cs (i + 1)
      if cs[j]? == some '(' then
        -- the argument runs to the parenthesis that closes this one
        let mut depth : Nat := 0
        let mut k := j
        for _ in [0:cs.size] do
          match cs[k]? with
          | some '(' => depth := depth + 1
          | some ')' => depth := depth - 1
          | _ => pure ()
          if depth == 0 then break
          k := k + 1
        out := out.push (.pseudo name (String.ofList (cs.extract (j + 1) k).toList))
        i := k + 1
      else
        out := out.push (.pseudo name "")
        i := j
    | _ => break
  return out.toList

/-- A complex selector's compounds and combinators, right to left: subject
first, each combinator before the compound it reaches. -/
private def cssChain (m : String) : List String :=
  let words := cssSplit ' ' m
  let comb (w : String) : Bool := w == ">" || w == "+" || w == "~"
  let spaced := words.foldl (fun (acc : List String) w =>
    match acc.head? with
    | some prev => if comb w || comb prev then w :: acc else w :: " " :: acc
    | none => [w]) []
  spaced

mutual

/-- Whether element `i` matches the selector list `sel`, `scope` the element
a `:has()` argument is relative to. -/
private def cssMatchList (fuel : Nat) (t : CTree) (scope : Option Nat) (sel : String)
    (i : Nat) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 => (cssSplit ',' sel).any fun m => cssMatchChain f t scope (cssChain m) i

private def cssMatchChain (fuel : Nat) (t : CTree) (scope : Option Nat) (chain : List String)
    (i : Nat) : Bool :=
  match fuel, chain with
  | 0, _ => false
  | _, [] => true
  | f + 1, c :: rest =>
    cssMatchParts f t scope (cssCompound c) i && match rest with
      | [] => true
      | op :: rest' =>
        let cands : List Nat := match op with
          | ">" => (t.el i).parent.toList
          | "+" => (t.before i).take 1
          | "~" => t.before i
          | _ => t.ancestors i
        cands.any (cssMatchChain f t scope rest')

private def cssMatchParts (fuel : Nat) (t : CTree) (scope : Option Nat) (ps : List CPart)
    (i : Nat) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 => ps.all fun p => match p with
    | .type ty => ty == "*" || (t.el i).tag == ty
    | .cls c => (((t.attr? i "class").getD "").splitOn " ").contains c
    | .attr n op v => match t.attr? i n with
      | none => false
      | some a => op == "" || (op == "=" && a == v) || (op == "~=" && (a.splitOn " ").contains v)
    | .pseudo "first-child" _ => (t.before i).isEmpty
    | .pseudo "last-child" _ => (t.after i).isEmpty
    | .pseudo "scope" _ => scope == some i
    | .pseudo "not" a => !cssMatchList f t scope a i
    | .pseudo "is" a | .pseudo "where" a => cssMatchList f t scope a i
    | .pseudo "has" a =>
      let rel := ", ".intercalate ((cssSplit ',' a).map (":scope " ++ ·))
      (t.descendants i).any (cssMatchList f t (some i) rel)
    | .pseudo _ _ => false

end

/-- A specificity triple's order, as the cascade compares. -/
private def specLe (a b : Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))

private def specAdd (a b : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

mutual

/-- A complex selector's specificity: `:where()` none, `:is()`, `:not()` and
`:has()` their most specific argument's. -/
private def cssSpec (fuel : Nat) (m : String) : Nat × Nat × Nat :=
  match fuel with
  | 0 => (0, 0, 0)
  | f + 1 => ((cssChain m).filter (fun w => w != " " && w != ">" && w != "+" && w != "~")).foldl
      (fun acc c => specAdd acc (cssPartsSpec f (cssCompound c))) (0, 0, 0)

private def cssPartsSpec (fuel : Nat) (ps : List CPart) : Nat × Nat × Nat :=
  match fuel with
  | 0 => (0, 0, 0)
  | f + 1 => ps.foldl (fun acc p => specAdd acc (match p with
    | .type ty => if ty == "*" then (0, 0, 0) else (0, 0, 1)
    | .cls _ | .attr .. => (0, 1, 0)
    | .pseudo "where" _ => (0, 0, 0)
    | .pseudo "is" a | .pseudo "not" a | .pseudo "has" a =>
      (cssSplit ',' a).foldl (fun best m =>
        let s := cssSpec f m
        if specLe best s then s else best) (0, 0, 0)
    | .pseudo _ _ => (0, 1, 0))) (0, 0, 0)

end

/-- A sheet's rules in source order with the at-rules around each: the
screen's default reads a rule inside no `@media` and no `@supports not`. -/
private def cssRules (css : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut heads : Array String := #[]
  let mut cur := ""
  for c in css.toList do
    if c == '{' then
      heads := heads.push cur.trimAscii.toString
      cur := ""
    else if c == '}' then
      let decls := cur.trimAscii.toString
      let screen := (heads.pop).all fun h =>
        !h.startsWith "@media" && !h.startsWith "@supports not" && !h.startsWith "@keyframes"
      if decls.contains ':' && screen && !(heads.back?.getD "").startsWith "@" then
        out := out.push ((heads.back?.getD "").trimAscii.toString, decls)
      heads := heads.pop
      cur := ""
    else
      cur := cur.push c
  return out

/-- The `margin-top` a declaration block states, the shorthand's first value
included. -/
private def marginTopOf (decls : String) : Option String :=
  (decls.splitOn ";").foldl (fun acc d =>
    match d.splitOn ":" with
    | k :: v :: more =>
      let value := (":".intercalate (v :: more)).trimAscii.toString
      match k.trimAscii.toString with
      | "margin-top" => some value
      | "margin" => (cssSplit ' ' value).head?
      | _ => acc
    | _ => acc) none

/-- The `margin-top` the cascade gives element `i`: its own `style` first,
then the matching rule of highest specificity, the later of equals. -/
private def cascadeMarginTop (t : CTree) (rules : Array (String × String)) (i : Nat) :
    Option String := Id.run do
  if let some own := (t.attr? i "style").bind marginTopOf then return some own
  let mut best : Option ((Nat × Nat × Nat) × String) := none
  for (sel, decls) in rules do
    if let some v := marginTopOf decls then
      let matched := (cssSplit ',' sel).filter fun m => cssMatchChain 64 t none (cssChain m) i
      unless matched.isEmpty do
        let s := matched.foldl (fun b m =>
          let s := cssSpec 64 m
          if specLe b s then s else b) (0, 0, 0)
        best := match best with
          | some (bs, bv) => if specLe bs s then some (s, v) else some (bs, bv)
          | none => some (s, v)
  return best.map (·.2)

/-- The value a declaration block states for `prop`, no shorthand read. -/
private def declOf (decls prop : String) : Option String :=
  (decls.splitOn ";").foldl (fun acc d =>
    match d.splitOn ":" with
    | k :: v :: more =>
      if k.trimAscii.toString == prop then some (":".intercalate (v :: more)).trimAscii.toString
      else acc
    | _ => acc) none

/-- The value the cascade gives element `i` for an inherited `prop`: its own
`style` first, then the matching rule of highest specificity, the later of
equals, and where neither states one, its parent's. -/
private def cascadeInherited (t : CTree) (rules : Array (String × String)) (prop : String)
    (i : Nat) : Option String := Id.run do
  let mut at? : Option Nat := some i
  for _ in [0:t.els.size + 1] do
    match at? with
    | none => return none
    | some j =>
      if let some own := (t.attr? j "style").bind (declOf · prop) then return some own
      let mut best : Option ((Nat × Nat × Nat) × String) := none
      for (sel, decls) in rules do
        if let some v := declOf decls prop then
          let matched := (cssSplit ',' sel).filter fun m => cssMatchChain 64 t none (cssChain m) j
          unless matched.isEmpty do
            let s := matched.foldl (fun b m =>
              let s := cssSpec 64 m
              if specLe b s then s else b) (0, 0, 0)
            best := match best with
              | some (bs, bv) => if specLe bs s then some (s, v) else some (bs, bv)
              | none => some (s, v)
      if let some (_, v) := best then return some v
      at? := (t.el j).parent
  return none

/-- A unitless CSS number to the milli: `1.222` is 1222, `0` is 0. -/
private def milliOf (v : String) : Option Int :=
  match v.splitOn "." with
  | [w] => w.toNat?.map fun n => ((n * 1000 : Nat) : Int)
  | [w, f] =>
    let f3 := (f ++ "000").take 3
    match w.toNat?, f3.toString.toNat? with
    | some a, some b => some ((a * 1000 + b : Nat) : Int)
    | _, _ => none
  | _ => none

/-- **A deck's heading set in a named size leads at the page's leading**, as
the page leads a display's lines at the step's `\baselineskip` on the base
the step scales: the title's element carries `lead-<step>` and stands no
line of its own, and the step's span inside it, at the step's size, takes
the leading over that size — the page's own pitch over its own type, to the
milli, for a step below the title's size and one above it. Before, the
element took the leading over its own size and the span inherited that
factor, so a step above the title's size stood every line that step's
factor too loose: 37.3 bp per line for a `\Large` frame title the page sets
at 25.9. -/
def headingLeadChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for step in ["small", "Large"] do
    let deckDoc := (elabStr ("\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}{\\" ++ step ++ " " ++ longTitle ++ " " ++ longTitle ++ "}\n" ++
      "Body words.\n\\end{frame}\n\\end{document}")).1
    let (head, nodes, _) := HtmlDoc.emitTree {} deckDoc
    let tree := CTree.of nodes
    let rules := cssRules (treeCssList "" head.toList)
    let has (i : Nat) (c : String) : Bool :=
      (((tree.attr? i "class").getD "").splitOn " ").contains c
    let heads := (List.range tree.els.size).filter fun i =>
      (tree.el i).tag == "h2" && has i ("lead-" ++ step)
    let inHead (i : Nat) : Bool := Id.run do
      let mut at? := (tree.el i).parent
      for _ in [0:tree.els.size] do
        match at? with
        | none => return false
        | some j => if heads.contains j then return true else at? := (tree.el j).parent
      return false
    let spans := (List.range tree.els.size).filter fun i => has i ("size-" ++ step) && inHead i
    let page := (sizedPitches (layoutOf oneFace deckDoc)).map fun (sz, p) => p * 1000 / sz
    t s!"a {step} frame title's element carries the step's leading and stands no line"
      (heads.length == 1 &&
        heads.all fun i => cascadeInherited tree rules "line-height" i == some "0")
    t s!"a {step} frame title's lines lead at the page's leading over their type"
      (spans.length == 1 && !page.isEmpty && spans.all fun i =>
        match (cascadeInherited tree rules "line-height" i).bind milliOf with
        | some v => page.all fun q => (v - q).natAbs ≤ 1
        | none => false)
  let plain := (elabStr ("\\documentclass[10pt]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{" ++ longTitle ++ "}\nBody words.\n\\end{frame}\n\\end{document}")).1
  let (_, plainNodes, _) := HtmlDoc.emitTree {} plain
  t "a frame title under no size command keeps the heading's leading"
    ((elemNodesList (· == "h2") #[] plainNodes.toList).size == 1 &&
      Ir.sizeScale.all fun (n, _) => (withClassIn plainNodes ("lead-" ++ n)).isEmpty)

/-- The flow blocks of each frame a deck's tree ships, seeing through overlay
carriers and skipping the frame's furniture, each block's tag, its text and
the `margin-top` the cascade gives it. -/
private def frameFlow (nodes : Array Html.Node) (css : String) :
    Array (String × String × Option String) := Id.run do
  let t := CTree.of nodes
  let rules := cssRules css
  let classes (i : Nat) : List String := ((t.attr? i "class").getD "").splitOn " "
  let carrier (i : Nat) : Bool :=
    (t.el i).tag == "div" && ((t.attr? i "data-backend").isSome ||
      ["step", "step-set", "step-end", "alt-pair", "alt"].any (classes i).contains)
  let furniture (i : Nat) : Bool :=
    ["header", "footer", "aside"].contains (t.el i).tag || (t.attr? i "hidden").isSome ||
      ["fill", "slide-logo", "snap"].any (classes i).contains
  let mut out : Array (String × String × Option String) := #[]
  for s in [0:t.els.size] do
    if (t.el s).tag == "section" &&
        (((t.attr? s "class").getD "").splitOn " ").contains "slide" then
      -- the frame's children, carriers opened in place, in document order
      let mut stack : List Nat := (t.kids[s]?.getD #[]).toList
      for _ in [0:t.els.size] do
        match stack with
        | [] => break
        | k :: rest =>
          if furniture k then stack := rest
          else if carrier k then stack := (t.kids[k]?.getD #[]).toList ++ rest
          else
            out := out.push ((t.el k).tag, (t.el k).text.trimAscii.toString,
              cascadeMarginTop t rules k)
            stack := rest
  return out

/-- Overlay content as the page shows it at its last step, paragraph by
paragraph: invented words in paragraphs, two beamer blocks, a list, a
quotation and a display. -/
private def gapBlocks : List String :=
  ["Alder words open the frame.", "Birch words follow it.",
   "Cedar words stand after a pause.",
   "\\begin{block}{Kilo}Kilo words in a block.\\end{block}",
   "\\begin{itemize}\n\\item Dogwood item\n\\item Elm item\n\\end{itemize}",
   "Fir words follow the list.", "\\begin{quote}\nHazel words quoted.\n\\end{quote}",
   "\\[ x + y = z \\]", "Juniper words follow the display.",
   "\\begin{block}{Lima}Lima words close a step.\\end{block}", "Larch words end the frame."]

/-- The same blocks with overlays between them: `\pause` twice, the second
opening on a block, an open `\uncover` holding a paragraph and the quotation
it closes on, and a closed range's `\uncover<2-3>` (its declared end a second
carrier) opening on the display right after that quotation and closing on a
block. lualatex stands every line of its last step where the flat frame
stands it. -/
private def gapOverlaid : String :=
  match gapBlocks with
  | [a, b, c, k, l, f, q, d, j, m, e] =>
    a ++ "\n\n" ++ b ++ "\n\\pause\n\n" ++ c ++ "\n\n\\pause\n" ++ k ++ "\n\n" ++ l ++ "\n\n" ++
      "\\uncover<3->{" ++ f ++ "\n\n" ++ q ++ "}\n\n" ++
      "\\uncover<2-3>{" ++ d ++ "\n\n" ++ j ++ "\n\n" ++ m ++ "}\n\n" ++ e
  | _ => ""

/-- A one-item list of invented words. -/
private def gapList (w : String) : String :=
  "\\begin{itemize}\n\\item " ++ w ++ " item\n\\end{itemize}"

/-- Two readings of a frame's flow agree block for block: tag, text and the
cascade's `margin-top`. -/
private def agree3 (a b : Array (String × String × Option String)) : Bool :=
  !a.isEmpty && a.size == b.size && (a.zip b).all fun (x, y) => x == y

/-- One frame of a deck whose paragraphs stand a declared `\parskip` apart. -/
private def gapDeck (body : String) : String :=
  "\\documentclass{beamer}\n\\setlength{\\parskip}{6pt}\n\\begin{document}\n" ++
    "\\begin{frame}{Overlay gaps}\n" ++ body ++ "\n\\end{frame}\n\\end{document}"

/-- **An overlay changes no gap between the blocks it carries**: built with
and without its `\pause`, `\uncover` and closed-range carriers, every flow
block of the frame takes the same `margin-top` in the cascade — the
declared `\parskip` between paragraphs, a list's and a quotation's space,
the display's skip — and every step of the page stands every line where the
flat frame does: a display opening a carrier keeps the `\@endpe` the
quotation before it left (`Ir.openAfterEnv`), and a covered display stays a
display (`Ir.displayParts` reads through the cover's colour). A carrier is an element of its own (one element animates
one opacity), so the sheet's sibling boundaries read through it
(`HtmlDoc.GapRule.throughCarriers`, `HtmlDoc.blockGapThrough_owner_contract`);
before, the first block in each carrier took no margin and the declared gap
vanished at every step (measured in Chromium: 14.1 px gaps with holes of 0).
The judge itself is checked to see the hole: the same tree under the sheet
read through no carriers differs. -/
def overlayGapChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (flatDoc, _) := elabStr (gapDeck ("\n\n".intercalate gapBlocks))
  let (ovDoc, _) := elabStr (gapDeck gapOverlaid)
  let (fh, fn, _) := HtmlDoc.emitTree {} flatDoc
  let (oh, on, _) := HtmlDoc.emitTree {} ovDoc
  let flat := frameFlow fn (treeCssList "" fh.toList)
  let ovCss := treeCssList "" oh.toList
  let ov := frameFlow on ovCss
  let agree (a b : Array (String × String × Option String)) : Bool :=
    a.size == b.size && a.size == gapBlocks.length &&
      (a.zip b).all fun (x, y) => x == y
  t "the frame's blocks stand in the same order with and without overlays"
    (flat.map (·.2.1) == ov.map (·.2.1) && flat.size == gapBlocks.length)
  t "every block keeps its gap through the overlay carriers" (agree flat ov)
  t "the paragraphs after a step take the declared parskip"
    ((ov.filter fun (tag, _, _) => tag == "p").all fun (_, _, m) => m.isSome)
  -- the judge sees the hole the carriers left: the same tree under the
  -- sheet read through no carriers
  let d := HtmlDoc.carrierPairs on
  let lists := ovDoc.docClass.record.lists
  let through := HtmlDoc.blockGapCss lists ovDoc.page.fontSize ovDoc.tokens d
  let plain := HtmlDoc.blockGapCss lists ovDoc.page.fontSize ovDoc.tokens
  t "the overlay deck's carriers stand between its blocks, so its sheet reads through them"
    (!d.isEmpty && hasStr ovCss through && through != plain)
  t "without reading through carriers the judge finds the gaps that vanish"
    (!agree flat (frameFlow on (ovCss.replace through plain)))
  -- the page: every step of the overlaid frame is the flat frame, covered
  -- or shown
  let pages (doc : Ir.Doc) : Array (Array (String × Sp)) :=
    (layoutOf oneFace doc).pages.map fun p =>
      (p.lines.filter (!·.furniture)).map fun l => (lineText l, l.y)
  let flatPages := pages flatDoc
  let ovPages := pages ovDoc
  t "every step of the page stands every line where the flat frame does"
    (!flatPages.isEmpty && ovPages.size == 3 * flatPages.size &&
      (List.range ovPages.size).all fun i => ovPages[i]? == flatPages[i % flatPages.size]?)
  -- an alternation: the page at each step is the flat frame of the group
  -- it shows, and the screen with no snap shows the first; where the groups
  -- end apart the block after them reads neither, where alike either
  for (alike, label) in [(false, "a paragraph and a list"), (true, "two lists")] do
    let groups := if alike then (gapList "Kilo", gapList "Lima")
      else ("Kilo words in a paragraph.", gapList "Lima")
    let around (mid : String) : String :=
      "Alder words open the frame.\n\n" ++ mid ++ "\n\nLarch words end the frame."
    let altDoc := (elabStr (gapDeck (around ("\\alt<2>{" ++ groups.2 ++ "}{" ++
      groups.1 ++ "}")))).1
    let firstDoc := (elabStr (gapDeck (around groups.1))).1
    let otherDoc := (elabStr (gapDeck (around groups.2))).1
    let (ah, an, _) := HtmlDoc.emitTree {} altDoc
    let (fh1, fn1, _) := HtmlDoc.emitTree {} firstDoc
    t s!"an alternation of {label} marks its pair alike exactly when its groups end alike"
      ((withClassIn an "alt-alike").isEmpty == !alike && (withClassIn an "alt-pair").size == 1)
    t s!"the screen with no snap gives an alternation of {label} the first group's gaps"
      (agree3 (frameFlow fn1 (treeCssList "" fh1.toList)) (frameFlow an (treeCssList "" ah.toList)))
    t s!"each step of an alternation of {label} is the flat frame of the group it shows"
      (pages altDoc == (pages firstDoc ++ pages otherDoc) && (pages altDoc).size == 2)
  -- the sheet reads the boundary shapes the tree has, not every depth its
  -- carriers nest to: forty pauses read through the one link a single
  -- pause does
  let pausesDoc (n : Nat) : Ir.Doc :=
    (elabStr (gapDeck ("\n\\pause\n".intercalate
      ((List.range (n + 1)).map fun i => s!"Words of paragraph {i}.\n")))).1
  let pausePairs (n : Nat) : List (Nat × Nat) :=
    let (_, nodes, _) := HtmlDoc.emitTree {} (pausesDoc n)
    HtmlDoc.carrierPairs nodes
  t "forty nested pauses read through the boundary shapes one pause does"
    (pausePairs 40 == pausePairs 1 && !(pausePairs 1).isEmpty)
  let sheetOf (n : Nat) : String :=
    let doc := pausesDoc n
    HtmlDoc.blockGapCss doc.docClass.record.lists doc.page.fontSize doc.tokens (pausePairs n)
  t "a frame of forty pauses ships the gap sheet of one"
    (sheetOf 40 == sheetOf 1)

/-- Displays meeting an overlay carrier, each with its flat reading: a
display opening a `\pause` or an `\uncover` after a list, opening a
`\pause` inside a running paragraph or after a quotation, a `\pause` after
a display inside a paragraph, and an `\uncover` holding a display in
mid-paragraph. Invented words only. -/
private def carrierDisplayCases : List (String × String × String) :=
  [("a display opening a pause after a list",
     gapList "Elm" ++ "\n\\pause\n\\[ a = b \\]\n\nAlder words stand here.",
     gapList "Elm" ++ "\n\\[ a = b \\]\n\nAlder words stand here."),
   ("a display opening an uncover after a list",
     gapList "Elm" ++ "\n\\uncover<2->{\\[ a = b \\]}\n\nAlder words stand here.",
     gapList "Elm" ++ "\n\\[ a = b \\]\n\nAlder words stand here."),
   ("a display opening a pause inside a paragraph",
     "Alder words stand here.\n\\pause\n\\[ a = b \\]\nBirch words stand here.",
     "Alder words stand here.\n\\[ a = b \\]\nBirch words stand here."),
   ("a pause after a display inside a paragraph",
     "Alder words stand here.\n\\[ a = b \\]\n\\pause\nBirch words stand here.",
     "Alder words stand here.\n\\[ a = b \\]\nBirch words stand here."),
   ("a display opening a pause after a quotation",
     "\\begin{quote}\nHazel quoted.\n\\end{quote}\n\\pause\n\\[ a = b \\]\n" ++
       "Birch words stand here.",
     "\\begin{quote}\nHazel quoted.\n\\end{quote}\n\\[ a = b \\]\nBirch words stand here."),
   ("an uncover holding a display inside a paragraph",
     "Alder words stand here.\n\\uncover<2->{\\[ a = b \\]}\nBirch words stand here.",
     "Alder words stand here.\n\\[ a = b \\]\nBirch words stand here.")]

/-- **A carrier stands its displays in their paragraph**
(`Ir.carrierDisplays`): a display opening or closing a `\pause` or an
`\uncover` stands, at every step of the page and on the screen, where it
stands with no overlay there, as lualatex stands it — inside the paragraph
its text runs on in, right after the environment end that left `\@endpe`,
before the break that does or does not follow. Elaborated alone, the
carrier's body saw neither side: a display after a list opened a new
paragraph about 13 pt lower, one in a running paragraph about 8 pt, and
every covered step set the display as a centred paragraph, the cover's
colour hiding its shape (`Ir.displayParts`). -/
def carrierDisplayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pages (doc : Ir.Doc) : Array (Array (String × Sp)) :=
    (layoutOf oneFace doc).pages.map fun p =>
      (p.lines.filter (!·.furniture)).map fun l => (lineText l, l.y)
  for (label, overlaid, flat) in carrierDisplayCases do
    let ovDoc := (elabStr (gapDeck overlaid)).1
    let flatDoc := (elabStr (gapDeck flat)).1
    let o := pages ovDoc
    let f := pages flatDoc
    t s!"{label} stands at every step where the flat frame stands it"
      (!f.isEmpty && o.size == 2 * f.size &&
        (List.range o.size).all fun i => o[i]? == f[i % f.size]?)
    let (oh, on, _) := HtmlDoc.emitTree {} ovDoc
    let (fh, fn, _) := HtmlDoc.emitTree {} flatDoc
    t s!"{label} takes the flat frame's gaps on the screen"
      (agree3 (frameFlow fn (treeCssList "" fh.toList)) (frameFlow on (treeCssList "" oh.toList)))

end Tests.LineRhythm
