import Tests.Support

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
box is the step's, and on a deck each step's leading as a line height —
the page's projection, where a reading page keeps the screen's one line
height. A span inside the element left the body's strut under every
line. -/
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
  t "a deck's steps set their own leading as line heights"
    (hasStr deck ".size-small { font-size: 0.900em; line-height: 1.222; }" &&
      hasStr deck ".size-footnotesize { font-size: 0.800em; line-height: 1.187; }" &&
      hasStr deck ".size-LARGE { font-size: 1.728em; line-height: 1.273; }")
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

/-- **A listing's lines stand at its size's leading, less what its package
takes off each line**: a bare `verbatim` under `\\footnotesize` at the
step's 9.5 pt, as lualatex sets it (9.464 bp), and a minted listing 0.25 pt
tighter, fvextra's overlap after every line (lualatex: 9.215 bp); the
HTML `pre` states the same pitch over its font size. Before, both stood at
6⁄5 of 8 pt, 9.6 pt, on both artifacts. -/
def listingPitchChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let code := "alpha = 1\nbravo = 2\ncharlie = 3\n"
  let verbatim := dvDoc "" ("{\\footnotesize\n\\begin{verbatim}\n" ++ code ++ "\\end{verbatim}\n}")
  let minted := dvDoc "\\usepackage{minted}\n\\setminted{fontsize=\\footnotesize}\n"
    ("\\begin{minted}{python}\n" ++ code ++ "\\end{minted}")
  t "a footnotesize verbatim's lines stand at the step's 9.5 pt"
    (pitchesOf oneFace verbatim == #[pt 95 / 10, pt 95 / 10])
  t "a minted listing's lines stand fvextra's 0.25 pt under the step"
    (pitchesOf oneFace minted == #[pt 925 / 100, pt 925 / 100])
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

/-- **A table cell set in one named size stands on the step's line box in
both artifacts**: the page sets the cell's paragraph at the step's strut
and leading (`Ir.paraStep?`), and the HTML gives the cell element the
step's class, the content lifted out of the scope (`Ir.liftParaStep`) — a
size span inside the cell left the body's strut under every line. -/
def cellStepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "" ("\\begin{tabular}{p{3cm}}\n\\small " ++ longTitle ++ "\n\\end{tabular}")
  let (doc, _) := elabStr src
  t "a small cell's wrapped lines stand at the step's 11 pt"
    (let ps := pitchesOf oneFace src
     !ps.isEmpty && ps.all (· == pt 11))
  let (_, nodes, _) := HtmlDoc.emitTree {} doc
  let cells := withClassIn nodes "size-small"
  t "the HTML cell carries the step's class itself"
    (cells.size == 1 && cells.all (· matches .elem "td" _ _))

end Tests.LineRhythm
