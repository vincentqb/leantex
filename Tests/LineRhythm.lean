import Tests.Support

open LeanTex.Core LeanTex.Core.Dim

namespace Tests.LineRhythm

/-- The baselines a source's body lines stand on, in page order. -/
private def baselines (fs : Font.FontSet) (src : String) : Array Sp :=
  (bodyLines (layoutOf fs (elabStr src).1)).map (·.y)

/-- The distances between consecutive baselines. -/
private def pitches (ys : Array Sp) : Array Sp :=
  (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a

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
    let ps := pitches (baselines oneFace (metricDoc (stepPara name)))
    t s!"a paragraph set in '\\{name}' stands its lines at size10.clo's {skip / 100}.{skip % 100} pt"
      (ps == #[pt skip / 100])
  t "a body paragraph keeps the body's pitch around a small run"
    (pitches (baselines oneFace (metricDoc
      "Alpha one {\\small Charlie} one\\\\Bravo two\\par")) == #[pt 12])
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
    (pitches (baselines oneFace
      ("\\documentclass{article}\n\\linespread{1.5}\n\\begin{document}\n" ++
        stepPara "small" ++ "\n\\end{document}")) == #[pt 165 / 10])

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

end Tests.LineRhythm
