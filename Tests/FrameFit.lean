module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameFit

/-- `n` invented paragraphs, one line each. -/
private def paras (n : Nat) : String :=
  "\n\n".intercalate ((List.range n).map fun i => s!"Kilo {i + 1} words.")

/-- An invented list of `n` one-line items. -/
private def items (n : Nat) : String :=
  "\\begin{itemize}\n" ++
    "\n".intercalate ((List.range n).map fun i => s!"\\item Kilo {i + 1} words.") ++
    "\n\\end{itemize}"

/-- The physical pages the frame at body index `source` ships. -/
private def framePages (out : Layout.Out) (source : Nat) : Nat :=
  (out.pages.filter fun p => p.frameOrigin.any (·.source == source)).size

/-- The baselines of a page's body lines, in order. -/
private def bodyBaselines (out : Layout.Out) (page : Nat) : Array Dim.Sp :=
  (((out.pages[page]?.map (·.lines)).getD #[]).filter (!·.furniture)).map (·.y)

/-- The ladder's decision for the frame at body index `source`, step `step`. -/
private def decision (f : Layout.Fitted) (source step : Nat) : Option Ir.FrameFit :=
  (f.decisions.find? (·.1 == ⟨source, step⟩)).map (·.2)

/-- The overflow ladder's diagnostics naming frame `label`. -/
private def ladderNamed (out : Layout.Out) (label : String) : Array Diag :=
  out.diags.filter fun d => (d.code == "W0384" || d.code == "W0400") && d.subject == some label

/-- **A frame a little taller than its page stands overfull on it; one that
reaches past the gap above its footline continues, named with its whole
overrun, each frame once** (`Layout.runFitted`, `Ir.frameFit`,
`Layout.frameAccount`): every overlay step of a frame not declared
breakable is set once to measure how far past its text area its content
reaches beyond what its glue shrinks, and decided by that overrun. Within
the gap beamer's `\footheight` keeps above the footline (4 pt,
beamerbaseframecomponents.sty:165-167) the step ships on its one page, its
ink above the footline's; past it, or where footnotes stand at the floor and
the overhang would reach them, the step continues on the next page as
before. Each frame is named once: by W0400 with its largest overhang, or by
W0384 with the whole overrun a continuing step measured, which one more line
grows by exactly one baselineskip, an overfull step beside it said in the
same message. Over `Layout.Out` on an invented moloch deck (10 pt, the
shipped Fira Sans for every face): twenty-one lines below a 2 pt skip
overrun by about 1.6 pt here — a frame lualatex fits, its text area ending
lower than this engine's (owed) — two overlay steps as tall, two steps a
point apart, an alternation's short side beside a long side that reaches
past the gap, and a picture below seventeen lines; twenty-five and
twenty-six lines continue; twenty-one alone fit; a point's overrun below a
footnote continues. At `ee2dec5d` every one of these frames that ran past
its page shipped a continuation page, and W0384 stated only the first line
past the page. Invented words. -/
def overhangChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "overhang: the shipped Fira Sans parses" false
  let pic := "\\begin{tikzpicture}\\draw (0,0) rectangle (2,1.2);\\end{tikzpicture}"
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t", "\\vspace*{2pt}\n" ++ paras 21), ("t", paras 25), ("t", paras 26), ("t", paras 21),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++ "\n\n\\pause\nKilo words."),
     ("t", "\\vspace*{5pt}\nKilo words.\\footnote{Lima words.}\n\n" ++ paras 19),
     ("t", "\\vspace*{14pt}\n" ++ paras 17 ++ "\n\n" ++ pic),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++
       "\n\n\\alt<2>{Kilo words.\n\nLima words.\n\nMike words.\n\nNovember words.}{Kilo words.}"),
     ("t", "\\vspace*{1pt}\n" ++ paras 20 ++
       "\n\n\\alt<2>{\\vspace*{2pt}Kilo words.}{Kilo words.}")])
  t "overhang: the deck elaborates clean" (ds.all (·.severity != .error))
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  let gap := Dim.pt 4
  t "overhang: a frame 1.6 pt past its text area ships one page, overfull within the gap"
    (framePages out 0 == 1 && match decision f 0 1 with
      | some (.overfull o) => 0 < o && o ≤ gap
      | _ => false)
  t "overhang: the overfull frame is named once, by W0400"
    ((ladderNamed out "1").map (·.code) == #["W0400"])
  t "overhang: a frame far past its page continues, named once by W0384 with its overrun"
    (framePages out 1 == 2 && match decision f 1 1 with
      | some (.continued o) =>
        (ladderNamed out "2").map (·.message) == #[(Layout.continuedDiag (some "2") none o).message]
      | _ => false)
  -- The whole overrun, not the first line past the page: one more line
  -- grows it by one baselineskip, the pitch of the fitting frame's lines.
  let pitch := match (out.pages.findIdx? fun p => p.frameOrigin.any (·.source == 3)) with
    | some i => let ys := bodyBaselines out i; (ys[1]?.getD 0) - (ys[0]?.getD 0)
    | none => 0
  t "overhang: W0384 states the whole overrun: one more line adds one baselineskip"
    (0 < pitch && match decision f 1 1, decision f 2 1 with
      | some (.continued a), some (.continued b) => withinSp (ptMilli 100) (b - a) pitch
      | _, _ => false)
  t "overhang: a frame that fits ships one page, unnamed"
    (framePages out 3 == 1 && (ladderNamed out "4").isEmpty && decision f 3 1 == none)
  t "overhang: an overlay frame within the gap ships one page per step, named once"
    (framePages out 4 == 2 && (ladderNamed out "5").map (·.code) == #["W0400"])
  t "overhang: a frame a point past its page below a footnote continues rather than reach it"
    (framePages out 5 == 2 && (ladderNamed out "6").map (·.code) == #["W0384"] &&
      match decision f 5 1 with
      | some (.continued o) => 0 < o && o ≤ gap
      | _ => false)
  -- On every page of that frame the body's ink stays above the notes'.
  t "overhang: the body's ink never reaches the footnotes"
    (out.pages.all fun p => !p.frameOrigin.any (·.source == 5) ||
      let notes := p.lines.filter (·.note)
      let body := p.lines.filter fun l => !l.note && !l.furniture
      notes.all fun n => body.all fun l =>
        l.y + (Layout.segsInk fira l.segs).2 < n.y - (Layout.segsInk fira n.segs).1)
  t "overhang: a picture a point past the text area stands on its frame's one page"
    (framePages out 6 == 1 && (ladderNamed out "7").map (·.code) == #["W0400"])
  t "overhang: each overlay step is decided on its own, the frame named once"
    (framePages out 7 == 3 && match decision f 7 1, decision f 7 2 with
      | some (.overfull v), some (.continued c) =>
        (ladderNamed out "8").map (·.message) ==
          #[(Layout.continuedDiag (some "8") none c (some v)).message]
      | _, _ => false)
  t "overhang: steps overfull by different amounts name their frame once, by the larger"
    (framePages out 8 == 2 && match decision f 8 1, decision f 8 2 with
      | some (.overfull a), some (.overfull b) =>
        a < b && (ladderNamed out "9").map (·.message) ==
          #[(Layout.overfullDiag (some "9") none b).message]
      | _, _ => false)
  -- The overhang stays above the footline's ink: the last body line's
  -- deepest glyph against the frame number's tallest.
  let page := out.pages[0]?.getD {}
  let body := page.lines.filter (!·.furniture)
  let foot := page.lines.filter (·.furniture)
  t "overhang: the last line's ink stays above the footline's"
    (match body.back?, foot.back? with
     | some l, some f =>
       l.y + (Layout.segsInk fira l.segs).2 < f.y - (Layout.segsInk fira f.segs).1
     | _, _ => false)
  t "overhang: the shipped pages are the setting the ladder recorded"
    (out.pages.size == (Layout.run (Layout.Geom.ofPage doc.page) fira none f.setting).pages.size)

/-- **A running foot owns the bottom margin, so a frame there continues
rather than stand in it** (`Layout.Spacing.Page.clearance`): a deck whose
`\runningfoot` owns the foot takes the slides margins, where nothing keeps a
gap between the text area and the foot's ink, so a frame a few points past
its text area continues on the next page, named by W0384, and on every page
the body's ink stays above the running foot's. Over `Layout.Out` on an
invented moloch deck with an invented running foot: eighteen lines below a
6 pt skip. A ladder that gave the slides margins the gap stood this frame
in it, its last line's descenders on the running foot's ascenders. Invented
words. -/
def runningFootChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "running foot: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n\\runningfoot{Hikl gypsy words}\n"
    [("t", "\\vspace*{6pt}\n" ++ paras 17 ++ "\n\nKilo gypsy words jumping."),
     ("t", paras 3)])
  t "running foot: the deck elaborates clean" (ds.all (·.severity != .error))
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  t "running foot: a frame a few points past its text area continues"
    (framePages out 0 == 2 && (ladderNamed out "1").map (·.code) == #["W0384"] &&
      match decision f 0 1 with
      | some (.continued o) => 0 < o && o ≤ Dim.pt 4
      | _ => false)
  t "running foot: the body's ink stays above the running foot's on every page"
    (out.pages.all fun p =>
      let foot := p.lines.filter (·.furniture)
      let body := p.lines.filter fun l => !l.furniture && !l.note
      foot.all fun r => body.all fun l =>
        l.y + (Layout.segsInk fira l.segs).2 < r.y - (Layout.segsInk fira r.segs).1)

/-- **A declared `[squeeze]` marks the frame as it stands once flattened**
(`Elab.closeFramePalette`, `Ir.Block.markFrame`): a frame holding only
`\titlepage` is flattened into the title page's own frame, and a squeeze
declared on it marks that frame, so the title page sets as it sets
undeclared — over `Layout.Out` the same lines at the same places, and over
the typed HTML tree one slide stage per frame, none inside another. A mark
set before the flatten kept the frame from flattening: the title page's
stage stood inside the squeezed one, its matter moved down and right, and
its page gained a footline number. Invented words. -/
def titlePageSqueezeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "title page squeeze: the shipped Fira Sans parses" false
  let deck (opt : String) : String :=
    "\\documentclass[10pt]{beamer}\n\\title{Kilo invented title}\n\\author{Lima Author}\n" ++
      "\\begin{document}\n\\begin{frame}" ++ opt ++ "\n\\titlepage\n\\end{frame}\n" ++
      "\\begin{frame}{Bravo}\nLima words.\n\\end{frame}\n\\end{document}\n"
  let (sq, sds) := elabStr (deck "[squeeze]")
  let (plain, _) := elabStr (deck "")
  t "title page squeeze: the deck elaborates clean, the option read"
    (sds.all (·.severity != .error) && !sds.any fun d => d.code == "N0102")
  let lines (doc : Ir.Doc) : Array (String × Dim.Sp × Dim.Sp) :=
    ((fittedOf fira doc (Layout.Geom.ofPage doc.page)).out.pages.flatMap (·.lines)).map
      fun l => (lineText l, l.x, l.y)
  t "title page squeeze: the title page sets as it sets undeclared"
    (lines sq == lines plain)
  let stages (doc : Ir.Doc) : Nat := (slideStages (HtmlDoc.emitTree {} doc).2.1).size
  t "title page squeeze: one slide stage per frame, none inside another"
    (stages sq == 2 && stages plain == 2)

/-- **A frame's declared `[squeeze]` sets its lists as beamer's squeeze sets
them, and the web deck squeezes the lists of a frame the page could not set
at its glue's natural size** (`Ir.frameSqueeze`, `Layout.runFitted`):
beamer's `\beamer@cramped` sets `\itemsep0pt\topsep0.5pt` in every list the
frame opens (beamerbaseframesize.sty:21-22), so nineteen invented items
stand one baselineskip apart, lualatex's 11.955 bp, held to a tenth of a
point; a web stage has no glue to shrink, so a frame the page fitted only
by shrinking its glue — nineteen items on a page their itemsep shrinks to
fit, lualatex's 13.317 bp apart, which the page keeps — sets its lists
squeezed on the web, the floor that glue shrinks to, and a frame of
paragraphs with no list is left alone. Over `Layout.Out` and the typed HTML
tree: the squeezed stages' class, and the sheet's rules setting their items
with no gap and a trivlist inside an item at its half point. At `ee2dec5d`
`[squeeze]` was named and ignored, and the web stage of the nineteen-item
frame scrolled two items out of view. Invented words. -/
def squeezeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "squeeze: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,squeeze", items 19), ("t", items 19), ("t", "\\vspace*{2pt}\n" ++ paras 21)])
  t "squeeze: the deck elaborates clean, the option read"
    (ds.all (·.severity != .error) && !ds.any fun d => d.code == "N0102" && hasStr d.message "squeeze")
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  let gaps (page : Nat) : Array Dim.Sp :=
    let ys := bodyBaselines out page
    (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a
  t "squeeze: a squeezed frame's items stand one baselineskip apart, as lualatex's"
    ((gaps 0).size == 18 && (gaps 0).all (withinSp (ptMilli 100) · (ptMilli 11955)))
  t "squeeze: the page keeps an unsqueezed frame's shrunk itemsep, as lualatex's"
    ((gaps 1).size == 18 &&
      withinSp (ptMilli 100) ((gaps 1).foldl (· + ·) 0 / 18) (ptMilli 13317))
  t "squeeze: the web squeezes the frame the page shrank, and no other"
    (f.webSqueeze == #[1])
  let web := { doc with body := Ir.squeezeFrames doc.body f.webSqueeze }
  let (head, body, _) := HtmlDoc.emitTree {} web
  let classes := (slideStages body).map fun n => match n with
    | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "class").getD ""
    | .text _ | .style _ | .script .. => ""
  t "squeeze: the declared and the shrunk frame's stages carry the squeeze class"
    (classes.map (hasStr · "squeeze") == #[true, true, false])
  let css := treeCssList "" head.toList
  let rules := (css.splitOn "}").filterMap fun chunk => match chunk.splitOn "{" with
    | [sel, decls] => some (sel, decls)
    | _ => none
  t "squeeze: the sheet sets a squeezed frame's items with no gap between them"
    (rules.any fun (sel, decls) =>
      hasStr sel "section.slide.squeeze li + li" && hasStr decls "margin-top: calc(0.000rem")
  t "squeeze: a trivlist in a squeezed frame's item takes the squeeze's half point"
    ((cssRulesOf css
      "section.slide.squeeze li, section.slide.squeeze dd, section.slide.squeeze blockquote").any
      (hasStr · s!"--{Ir.trivlistSkipName}:"))

/-- **A breakable frame keeps a block's title with its body, and flow keeps
LaTeX's own break** (`Layout.Spacing.Page.keepHeading`): beamer's block is
one box, so in a frame declared `[allowframebreaks]` it never leaves its
title alone at a page's foot; nineteen invented paragraphs before a
two-paragraph block put the title on the page's last line, and the title
opens the continuation with its body, as lualatex sets the block whole
there. In an article, beamerarticle's block opens with its title in bold and
no `\nobreak`, so its body may break after its first line, as lualatex's
may: a sweep of invented paragraphs before a block of two lines finds the
title and the first line on one page and the second on the next. Over
`Layout.Out`. At `ee2dec5d` the breakable frame's title stood alone at the
first page's foot. Invented words. -/
def breakableTitleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "breakable title: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,allowframebreaks", paras 19 ++
      "\n\n\\begin{block}{Alpha}\nLima words.\n\nMike words.\n\\end{block}")])
  t "breakable title: the deck elaborates clean" (ds.all (·.severity != .error))
  let out := (fittedOf fira doc (Layout.Geom.ofPage doc.page)).out
  let pageOf (out : Layout.Out) (word : String) : Option Nat :=
    out.pages.findIdx? fun p => p.lines.any fun l => hasStr (lineText l) word
  t "breakable title: the block's title stands on its body's page"
    (match pageOf out "Alpha", pageOf out "Lima" with
     | some a, some l => a == l
     | _, _ => false)
  t "breakable title: the frame continues" (out.pages.size == 2)
  let article (n : Nat) : String :=
    "\\documentclass{article}\n\\usepackage{beamerarticle}\n\\begin{document}\n" ++
      "\n\n".intercalate ((List.range n).map fun i =>
        s!"Kilo {i + 1} words in an invented paragraph long enough to fill a line of the " ++
          "article's measure, more or less.") ++
      "\n\n\\begin{block}{Alpha}\nLima words.\\\\\nMike words.\n\\end{block}\n\\end{document}\n"
  let splits := (List.range 30).filter fun k =>
    let out := (fittedOf fira (elabStr (article (30 + k))).1).out
    match pageOf out "Alpha", pageOf out "Lima", pageOf out "Mike" with
    | some a, some l, some m => a == l && m == l + 1
    | _, _, _ => false
  t "breakable title: in flow a block's body breaks after its first line, as LaTeX's may"
    (!splits.isEmpty)

end Tests.FrameFit
