import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The document title is a level-0 heading (`\maketitle`): one per
document by construction — the elaborator disables a second `\maketitle`
exactly as LaTeX does (classes.dtx: `\global\let\maketitle\relax`) — and
each backend renders the same fact: `<h1>` in HTML, `#` first in markdown
(the metadata preamble never doubles it), the LARGE bold furniture in the
PDF (census rows for outline and the deck fixtures). Own function:
`main`'s elaboration budget. -/
def titleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\title{An Invented Title}\\author{Alex Doe}\\begin{document}" ++
    "\\maketitle Body text.\\section{First}More.\\end{document}")
  t "maketitle source is clean" ds.isEmpty
  t "the title elaborates as a level-0 heading before the sections"
    (Ir.headingLevels doc.body == #[0, 1])
  let page := (HtmlDoc.emit {} doc).1
  t "html sets the title as the one h1"
    ((page.splitOn "<h1>An Invented Title</h1>").length == 2 &&
      (page.splitOn "<h1").length == 2)
  let md := (MarkdownDoc.emit doc)
  t "markdown opens with the title as the one # line"
    (md.startsWith "# An Invented Title\n\n" &&
      (md.splitOn "\n# ").length == 1)
  -- The metadata preamble falls back to the declared \title; with the
  -- body carrying the level-0 heading it must not state the title twice.
  t "markdown never doubles the title"
    ((md.splitOn "# An Invented Title").length == 2)
  -- A second \maketitle is a no-op, named: LaTeX typesets the title once.
  let second := "\\documentclass{article}\\title{Once}\\begin{document}" ++
    "\\maketitle\\maketitle x\\end{document}"
  t "a second maketitle warns W0322" (warnCodes second == ["W0322"])
  t "a second maketitle sets no second level-0 heading"
    (Ir.headingLevels (elabStr second).1.body == #[0])
  -- A \maketitle with nothing declared (W0309) spends nothing: the title
  -- declared later still sets.
  let late := "\\documentclass{article}\\begin{document}" ++
    "\\maketitle\\title{Late}\\maketitle x\\end{document}"
  t "an empty maketitle does not spend the title"
    (warnCodes late == ["W0309"] && Ir.headingLevels (elabStr late).1.body == #[0])
  -- Slides: the title heading stands inside the golden title frame and is
  -- still the deck's one h1.
  let (deck, deckDs) := elabStr ("\\documentclass{slides}" ++
    "\\title{An Invented Deck}\\begin{document}\\maketitle" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "deck title source is clean" deckDs.isEmpty
  t "the deck's title frame carries the one h1"
    ((((HtmlDoc.emit {} deck).1.splitOn "<h1>An Invented Deck</h1>").length == 2) &&
      (((HtmlDoc.emit {} deck).1.splitOn "<h1").length == 2))

/-- The outline diagnostics: heading levels must not skip as the outline
descends (HTML §4.3.11's conformance rule; WCAG G141), and the title comes
first. Warnings over the IR, firing once per document; a proper ladder and
a climb back up fire nothing. Own function: `main`'s elaboration budget. -/
def outlineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body (s : String) := s!"\\documentclass\{article}\\begin\{document}{s}\\end\{document}"
  t "a section-to-subsubsection gap warns W0320 once"
    (warnCodes (body "\\section{A}x\\subsubsection{B}y\\subsubsection{C}z")
      == ["W0320"])
  t "a title-to-subsection gap warns W0320"
    (warnCodes ("\\documentclass{article}\\title{T}\\begin{document}" ++
      "\\maketitle\\subsection{S}x\\end{document}") == ["W0320"])
  t "a title after another heading warns W0321"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\section{A}x\\title{T}\\maketitle\\end{document}") == ["W0321"])
  t "a proper ladder warns nothing"
    (warnCodes (body "\\section{A}x\\subsection{B}y\\subsubsection{C}z") == [])
  t "climbing back up warns nothing"
    (warnCodes (body "\\section{A}x\\subsection{B}y\\section{C}z") == [])
  t "a document whose first heading is deep warns nothing"
    (warnCodes (body "\\subsection{Fragment}x") == [])


/-- `columns`/`column`: side-by-side blocks with declared widths, in the IR
and both backends. Own function: `main`'s do block has no budget left. -/
def columnsChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := deck169Frame ("\\begin{columns}[T]\n\\begin{column}{0.6\\textwidth}\nleft\n\\end{column}\n" ++
    "\\begin{column}{0.4\\textwidth}\nright\n\\end{column}\n\\end{columns}")
  let (doc, ds) := elabStr src
  t "columns elaborate with widths, its option a note" (ds.all (·.severity == .note) &&
    doc.body == #[.frame #[] false .center false #[.columns #[
      (.frac 600, #[.para #[.text "left"]]),
      (.frac 400, #[.para #[.text "right"]])]]])
  -- PDF: the columns' first lines share a baseline, and the second sits
  -- past the first one's measure — visibly two columns, by geometry.
  let out := layoutOf oneFace doc
  t "pdf columns share a baseline side by side"
    (match (out.pages[0]?.map (·.lines)).getD #[] with
     | #[l, r] => l.y == r.y && r.x > l.x && r.x ≥ l.x + l.setWidth
     | _ => false)
  -- A column keeps its measure: its paragraph breaks at the column width,
  -- not the text width.
  let wide := deck169Frame ("\\begin{columns}\\begin{column}{0.5\\textwidth}\n" ++
    "several words that cannot possibly fit one half measure line\n" ++
    "\\end{column}\\begin{column}{0.5\\textwidth}\nright\n\\end{column}\\end{columns}")
  let (wDoc, _) := elabStr wide
  let wOut := layoutOf oneFace wDoc
  t "a column breaks lines at its own measure"
    (((wOut.pages[0]?.map (·.lines)).getD #[]).size > 2)
  -- HTML: a grid whose tracks carry the declared widths.
  let (html, _) := HtmlDoc.emit {} doc
  t "html columns are a grid with the declared widths"
    ((html.splitOn "grid-template-columns: 60% 40%").length == 2)
  -- An absolute width is a width: it rides as a length (`Ir.BoxWidth.abs`)
  -- and is resolved against the measure the box stands in, so nothing is
  -- refused and nothing degrades to a share. The row asserted the opposite
  -- while the carrier spelled a width as per mille only — a length is not a
  -- fraction of anything, so the box took the leftover and W0314 said so.
  let (aDoc, aDs) := elabStr (deck169Frame ("\\begin{columns}\\begin{column}{3cm}\na\n\\end{column}" ++
    "\\begin{column}{0.5\\textwidth}\nb\n\\end{column}\\end{columns}"))
  t "an absolute column width is honoured as a length"
    (!aDs.any (·.code == "W0314") &&
     (match aDoc.body with
      | #[.frame _ _ _ _ #[.columns cols]] =>
        (match cols[0]?.map (·.1), cols[1]?.map (·.1) with
         | some (Ir.BoxWidth.abs l), some (Ir.BoxWidth.frac 500) =>
           -- 3cm, within a point of TeX's 28.45276 pt per cm.
           decide (l > Dim.pt 84) && decide (l < Dim.pt 87)
         | _, _ => false)
      | _ => false))
  -- `\hfill` between `column`s is the gutter, never a paragraph: beamer's
  -- own row opens with `\hbox{}\hfill` and closes every column with
  -- `\hfill` (beamerbaseframecomponents.sty, `beamer@colentrycode` /
  -- `beamer@columnenv`'s end code). Judged over `Layout.Out`: the
  -- fill-separated spelling keeps the side-by-side geometry — treating the
  -- fill as stray content once stacked each column in its own row.
  let sepSrc (sep : String) := deck169Frame ("\\begin{columns}[T]\n" ++ sep ++
    "\n\\begin{column}{0.6\\textwidth}\nleft\n\\end{column}\n" ++ sep ++
    "\n\\begin{column}{0.4\\textwidth}\nright\n\\end{column}\n" ++ sep ++ "\n\\end{columns}")
  let hOut := layoutOf oneFace (elabStr (sepSrc "\\hfill")).1
  t "hfill-separated columns still stand side by side"
    (hOut.pages.size == 1 &&
     (match (hOut.pages[0]?.map (·.lines)).getD #[] with
      | #[l, r] => l.y == r.y && r.x ≥ l.x + l.setWidth
      | _ => false))
  t "an hfill inside stray column content stays ordinary content"
    (let (sDoc, _) := elabStr (deck169Frame
      ("\\begin{columns}\nstray \\hfill words\n\\begin{column}{0.5\\textwidth}\n" ++
       "left\n\\end{column}\n\\end{columns}"))
     match sDoc.body with
     | #[.frame _ _ _ _ body] =>
       body.any fun b => match b with
         | .para xs => xs.any (fun x => x matches .fill)
         | _ => false
     | _ => false)
  -- Inside a `column`, `width=\textwidth` is the column's width: a column
  -- is a minipage of its declared width (beamerbaseframecomponents.sty,
  -- `beamer@columnenv`), and a minipage sets `\textwidth` and
  -- `\columnwidth` to its own `\hsize` (latex.ltx, `\@iiiminipage`). The
  -- image box must span exactly the column, never the page's measure.
  let imgSrc := deck169Frame ("\\begin{columns}\n\\begin{column}{0.3\\textwidth}\n" ++
    "\\includegraphics[width=\\textwidth]{missing.png}\n\\end{column}\n" ++
    "\\begin{column}{0.7\\textwidth}\nright\n\\end{column}\n\\end{columns}")
  let (iDoc, _) := elabStr imgSrc
  let iGeom := Layout.Geom.ofPage iDoc.page
  let iOut := layoutOf oneFace iDoc iGeom
  let colW := iGeom.textWidth * 300 / 1000
  t "a column image of width textwidth spans exactly the column"
    ((iOut.pages.flatMap (·.lines)).any fun l => l.segs.any fun s =>
      match s with
      | .image _ w _ => w == colW
      | _ => false)
  -- The joint shape the A0 poster failed on: with the image held to its
  -- column, no ink can start left of the text origin.
  t "a column image never lands past the left margin"
    ((iOut.pages.flatMap (·.lines)).all fun l => l.x ≥ iGeom.hmargin)

/-- Overlays, dim-not-hide (PLAN M5): steps ride the IR, the PDF handout
gets one page per step with pending content dimmed and no reflow, HTML
carries the step data with everything visible (the no-JS deliverable).
Own function: `main`'s do block has no budget left. -/
def overlayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- \item<n-> wraps its item; \uncover<n>{...} wraps inline content.
  let src := deck169Frame ("\\begin{itemize}\n\\item<1-> first\n\\item<2-> second\n\\end{itemize}\n" ++
    "\\uncover<2>{tail}")
  let (doc, ds) := elabStr src
  t "overlay specs elaborate to steps, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center false #[
      .list false #[
        #[.step 1 none #[.para #[.text "first"]]],
        #[.step 2 none #[.para #[.text "second"]]]],
      .para #[.step 2 (some 2) #[.text "tail"]]]])
  -- \pause steps the rest of the scope.
  let (pDoc, pDs) := elabStr (deck169Frame "one\n\n\\pause\ntwo\n\n\\pause\nthree")
  t "pause steps the rest, cumulatively" (pDs.isEmpty &&
    pDoc.body == #[.frame #[] false .center false #[
      .para #[.text "one"],
      .step 2 none #[.para #[.text "two"], .step 3 none #[.para #[.text "three"]]]]])
  -- PDF: one page per step; pending content dims, nothing moves.
  let out := layoutOf oneFace pDoc
  t "pdf emits one page per step" (out.pages.size == 3)
  let coords (p : Layout.PageOut) : Array (Dim.Sp × Dim.Sp) :=
    p.lines.map fun l => (l.x, l.y)
  t "pdf steps do not reflow"
    (match out.pages[0]?, out.pages[2]? with
     | some p1, some p3 => coords p1 == (coords p3).extract 0 (coords p1).size
     | _, _ => false)
  let lineColors (p : Layout.PageOut) : Array Ir.Color :=
    p.lines.filterMap fun l => l.segs.findSome? fun s => match s with
      | .run _ c _ _ _ _ _ _ _ _ => some c
      | _ => none
  t "pdf pending content is dimmed, then undimmed"
    (match out.pages[0]?, out.pages[2]? with
     | some p1, some p3 =>
       let c1 := lineColors p1
       let c3 := lineColors p3
       c1.size == 3 && c3.size == 3 &&
       c1[0]? == some Ir.Color.black && c1[1]? != some Ir.Color.black &&
       c1[2]? != some Ir.Color.black && c3.all (· == Ir.Color.black)
     | _, _ => false)
  -- HTML: the steps ride as data, everything visible.
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries step data"
    ((html.splitOn "data-step=\"2\"").length ≥ 2)
  -- A spec the model cannot number keeps the honest warning.
  t "an unnumberable spec still warns W0105"
    (warnCodes (deck169Frame "\\begin{itemize}\\item<+-> x\\end{itemize}") == ["W0105"])
  -- The range's end is modelled: <2> covers on 1 AND again from 3, exactly
  -- as beamer's transparent covering does; <2-3> reads the same way.
  t "a range spec carries its end"
    ((elabStr (deck169Frame "\\uncover<2-3>{ranged}")).1.body ==
      #[.frame #[] false .center false #[.para #[.step 2 (some 3) #[.text "ranged"]]]])
  let (rDoc, rDs) := elabStr (deck169Frame ("\\begin{itemize}\n\\item<1> opening\n" ++
    "\\item<2-> second\n\\item<3-> third\n\\end{itemize}"))
  let rOut := layoutOf oneFace rDoc
  t "content past its range end dims again" (rDs.isEmpty &&
    rOut.pages.size == 3 &&
    (match rOut.pages[0]?, rOut.pages[2]? with
     | some p1, some p3 =>
       let colorOf (p : Layout.PageOut) (k : Nat) : Option Ir.Color :=
         p.lines[k]?.bind fun l => l.segs.findSome? fun s => match s with
           | .run _ c _ _ _ _ _ _ _ _ => some c
           | _ => none
       -- Page 1: the <1> item crisp, the rest dimmed. Page 3: the <1> item
       -- dimmed again — its range ended — and the rest crisp.
       colorOf p1 0 == some Ir.Color.black && colorOf p1 1 != some Ir.Color.black &&
       colorOf p3 0 != some Ir.Color.black && colorOf p3 1 == some Ir.Color.black &&
       colorOf p3 2 == some Ir.Color.black
     | _, _ => false))
  -- Covered means covered: a pending step's own colours (an alert, a
  -- palette name) are repainted by the shade — beamer's transparent
  -- covering mutes coloured text too — and pending code dims like any
  -- other text.
  let runColors (p : Layout.PageOut) : Array Ir.Color :=
    p.lines.flatMap fun l => l.segs.filterMap fun s => match s with
      | .run _ c _ _ _ _ _ _ _ _ => some c
      | _ => none
  let colorSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ hot = #AA0000 }\n\\begin{document}\n\\begin{frame}\n" ++
    "opening\n\n\\pause\n\\hot{closing beat}\n\\end{frame}\n\\end{document}"
  let (cDoc, cDs) := elabStr colorSrc
  let cOut := layoutOf oneFace cDoc
  let hotCover := (Ir.Design.ofDoc cDoc).cover.of { r := 0xAA, g := 0, b := 0 }
  t "a pending step's explicit colours are covered as themselves, quieter"
    (cDs.isEmpty && cOut.pages.size == 2 &&
     (match cOut.pages[0]?, cOut.pages[1]? with
      | some p1, some p2 =>
        !(runColors p1).contains { r := 0xAA, g := 0, b := 0 } &&
        -- the covered run is the ink's own cover, not the plain grey
        (runColors p1).contains hotCover &&
        hotCover != (Ir.Design.ofDoc cDoc).cover.plain &&
        (runColors p2).contains { r := 0xAA, g := 0, b := 0 }
      | _, _ => false))
  let (vDoc, vDs) := elabStr
    (deck169Frame "opening\n\n\\pause\n\\begin{verbatim}\ncode line\n\\end{verbatim}")
  let vOut := layoutOf oneFace vDoc
  t "pending verbatim dims like any other text"
    (vDs.isEmpty && vOut.pages.size == 2 &&
     (match vOut.pages[0]?, vOut.pages[1]? with
      | some p1, some p2 =>
        (runColors p1).size ≥ 2 &&
        (runColors p1).count Ir.Color.black == 1 &&
        (runColors p2).all (· == Ir.Color.black)
      | _, _ => false))

/-- Block content inside overlay commands, the block/inline agreement, and
`\pause` where a deck169Frame actually puts it. Own function: `main`'s do block has
no budget left. -/
def overlayBlockChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A list inside an overlay group: the step wrapper survives at block
  -- level (this was E0312).
  let (lDoc, lDs) := elabStr (deck169Frame
    "\\onslide<2->{\n\\begin{itemize}\n\\item Stepped item.\n\\end{itemize}\n}")
  t "a list inside an overlay group steps whole, erroring nothing"
    (lDs.isEmpty && lDoc.body == #[.frame #[] false .center false #[
      .step 2 none #[.list false #[#[.para #[.text "Stepped item."]]]]]])
  -- A multi-paragraph group: every paragraph stays inside the step (the
  -- par splice used to strip all but the first).
  let (mDoc, mDs) := elabStr (deck169Frame "\\uncover<2>{\nFirst covered.\n\nSecond covered.\n}")
  t "every paragraph of an overlay group stays inside its step"
    (mDs.isEmpty && mDoc.body == #[.frame #[] false .center false #[
      .step 2 (some 2) #[.para #[.text "First covered."],
        .para #[.text "Second covered."]]]])
  -- Block and inline agree: the same spec around the same words reaches the
  -- same step, whether the content is a paragraph or a list item.
  let (iDoc, _) := elabStr (deck169Frame "\\uncover<2->{same words}")
  let (bDoc, _) := elabStr (deck169Frame
    "\\uncover<2->{\n\\begin{itemize}\n\\item same words\n\\end{itemize}\n}")
  t "block and inline agree on steps"
    (match iDoc.body, bDoc.body with
     | #[.frame _ _ _ _ ib], #[.frame _ _ _ _ bb] =>
       Ir.maxStepBlocks ib == 2 && Ir.maxStepBlocks bb == 2
     | _, _ => false)
  -- The open form between blocks: the rest of the scope steps (it used to
  -- produce an empty step and leave the content unstepped).
  let (oDoc, oDs) := elabStr (deck169Frame "shown\n\n\\onslide<2->\nlater one\n\nlater two")
  t "bare onslide between blocks steps the rest of the scope"
    (oDs.isEmpty && oDoc.body == #[.frame #[] false .center false #[
      .para #[.text "shown"],
      .step 2 none #[.para #[.text "later one"], .para #[.text "later two"]]]])
  -- \pause between items steps the rest of the list, not nothing.
  let (pDoc, pDs) := elabStr (deck169Frame
    "\\begin{itemize}\n\\item first\n\\pause\n\\item second\n\\pause\n\\item third\n\\end{itemize}")
  t "pause between items steps the later items"
    (pDs.isEmpty && pDoc.body == #[.frame #[] false .center false #[
      .list false #[
        #[.para #[.text "first"]],
        #[.step 2 none #[.para #[.text "second"]]],
        #[.step 3 none #[.para #[.text "third"]]]]]])
  let pOut := layoutOf oneFace pDoc
  t "a paused list gets one handout page per step" (pOut.pages.size == 3)
  -- \pause inside a column steps the column's remaining blocks.
  let (cDoc, cDs) := elabStr (deck169Frame
    ("\\begin{columns}\n\\begin{column}{0.5\\textwidth}\nabove\n\n\\pause\nbelow\n" ++
     "\\end{column}\n\\begin{column}{0.5\\textwidth}\nsteady\n\\end{column}\n\\end{columns}"))
  t "pause inside a column steps the column's rest"
    (cDs.isEmpty && (match cDoc.body with
      | #[.frame _ _ _ _ #[.columns cols]] =>
        (match cols[0]? with
         | some (_, body) => body == #[.para #[.text "above"],
             .step 2 none #[.para #[.text "below"]]]
         | none => false) &&
        (match cols[1]? with
         | some (_, body) => body == #[.para #[.text "steady"]]
         | none => false)
      | _ => false))
  -- \alt: one node carrying both alternatives, exactly one of them inked per
  -- step page (`Ir.selectSteps`).
  let (aDoc, aDs) := elabStr (deck169Frame "\\alt<2>{after}{before}")
  t "alt inline yields one alternation node"
    (aDs.isEmpty && aDoc.body == #[.frame #[] false .center false #[.para #[
      .alt 2 (some 2) #[.text "before"] #[.text "after"]]]])
  let (abDoc, abDs) := elabStr (deck169Frame
    "\\alt<2->{\nAfter one.\n\nAfter two.\n}{\nBefore.\n}")
  t "alt with block alternatives alternates at block level"
    (abDs.isEmpty && abDoc.body == #[.frame #[] false .center false #[
      .alt 2 none #[.para #[.text "Before."]]
        #[.para #[.text "After one."], .para #[.text "After two."]]]])
  -- A spec the model cannot number keeps W0105 and shows the block content.
  let (uDoc, uDs) := elabStr (deck169Frame
    "\\onslide<+->{\n\\begin{itemize}\n\\item shown anyway\n\\end{itemize}\n}")
  t "an unnumberable spec on a block group warns and shows the content"
    ((uDs.map (·.code)) == #["W0105"] && uDoc.body == #[.frame #[] false .center false #[
      .list false #[#[.para #[.text "shown anyway"]]]]])

/-- `\alert<spec>{body}` is beamer's own equation,
`\alt<spec>{\alert{body}}{body}` (`Compat.alertOverlay`): the alert style on
the spec's steps, the plain body on every other, and NOTHING covered. Red,
in order — the spec fell through, themed `\textcolor{alert}` read `<2>` as
its content and E0304 fired, unthemed `\textbf` set the spec as text; the
first `\alt` rewrite shipped the body TWICE on every page, because
dim-not-hide kept both alternatives on it and a rendered deck read
"placeplace"; the `\uncover<spec>{\alert{body}}` stopgap that replaced it
kept one copy but carried the alert style on every step and dimmed it
before, so the reader saw undimming where the document said becoming
alert. The invariants this block holds are census ones over the artifacts:
the body's text is inked exactly once per step page, NO page covers it (no
transparency anywhere), the alert ink is painted only on the spec's step
page, and the other page carries the body plain. The plain `\alert{...}`
rewrite stands byte for byte (the themed golden is the witness). -/
def alertOverlayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let themedDeck (body : String) : String :=
    deck169 "\\usetheme{moloch}" ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}")
  -- The one alternation of an `\alert<spec>` frame, and the one styled run
  -- of a plain `\alert` frame, read off the same sentence shape.
  let altOf (doc : Ir.Doc) :
      Option (Nat × Option Nat × Array Ir.Inline × Array Ir.Inline) :=
    match doc.body with
    | #[.frame _ _ _ _ #[.para #[.text _, .alt n last onFirst onOther, .text _]]] =>
      some (n, last, onFirst, onOther)
    | _ => none
  let plainOf (doc : Ir.Doc) : Option Ir.Inline :=
    match doc.body with
    | #[.frame _ _ _ _ #[.para #[.text _, s, .text _]]] => some s
    | _ => none
  for (mode, deck) in [("themed", themedDeck), ("unthemed", deck169Frame)] do
    let (pDoc, pDs) := elabStr (deck "One \\alert{apple} here.")
    let (aDoc, aDs) := elabStr (deck "One \\alert<2>{apple} here.")
    t s!"{mode} alert<2> raises no error and no warning"
      (aDs.all (·.severity == .note) && pDs.all (·.severity == .note))
    match altOf aDoc, plainOf pDoc with
    | some (n, last, onFirst, onOther), some ps =>
      t s!"{mode} alert<2> alternates on step 2 alone" (n == 2 && last == some 2)
      -- Page order: step 1 is outside the spec, so the group stored first
      -- is the plain body — bare text, no style node around it.
      t s!"{mode} alert<2> shows the body plain off its step"
        (onFirst == #[Ir.Inline.text "apple"] && Ir.altShowsFirst n last 1)
      t s!"{mode} alert<2> styles its other alternative as plain alert does"
        (onOther == #[ps])
      t s!"{mode} alert<2> conserves the body text once per alternative"
        (Ir.plainText onFirst == "apple" && Ir.plainText onOther == "apple")
    | _, _ => t s!"{mode} alert<2> elaborates to one alternation" false
  -- The range spellings reach the step model as the `\alt` arm reads them.
  let (oDoc, _) := elabStr (themedDeck "One \\alert<2->{apple} here.")
  t "alert<2-> is alert from step 2 on"
    ((altOf oDoc).map (fun (n, last, _, _) => n == 2 && last.isNone) == some true)
  let (rDoc, _) := elabStr (themedDeck "One \\alert<2-3>{apple} here.")
  t "alert<2-3> is alert within its range"
    ((altOf rDoc).map (fun (n, last, _, _) => n == 2 && last == some 3) == some true)
  -- A spec the model cannot number: the honest W0105, and ONE reading on
  -- the page. The invariant is the alternation's own — exactly one
  -- alternative is inked per step page — and an unnumberable spec does not
  -- lift it: with no step to switch on, the active alternative stands on
  -- every page and the other is never inked. The fallback used to splice
  -- both groups into the stream, so `\alert<+->{apple}` shipped
  -- "appleapple" and `\alt<+->{apple}{banana}` "applebanana" — which only
  -- a census over shipped pages can tell from one copy.
  let (uDoc, uDs) := elabStr (themedDeck "One \\alert<+->{apple} here.")
  t "an unnumberable alert spec warns W0105 once"
    ((uDs.filter (·.severity != .note)).map (·.code) == #["W0105"])
  let uc := censusOf (coveredColorsOf uDoc) (layoutOf oneFace uDoc)
  t "an unnumberable alert spec ships one page, its body inked exactly once"
    (uc.size == 1 && pageOccurs uc 0 "apple" == 1 && pageAllRevealed uc 0)
  -- `\alt` itself reads the same fallback: the active alternative alone,
  -- the other group nowhere on the page — W0105 accounts for it.
  let (nDoc, nDs) := elabStr (deck169Frame "Pick the \\alt<+->{apple}{banana} now.")
  t "an unnumberable alt spec warns W0105 once"
    ((nDs.filter (·.severity != .note)).map (·.code) == #["W0105"])
  let nc := censusOf (coveredColorsOf nDoc) (layoutOf oneFace nDoc)
  t "an unnumberable alt ships its active alternative exactly once, alone"
    (nc.size == 1 && pageOccurs nc 0 "apple" == 1 &&
      pageOccurs nc 0 "banana" == 0 && pageAllRevealed nc 0)
  -- The block-level arm is a second fallback site, reached when either
  -- alternative is block-shaped: it owes the same one reading.
  let (bDoc, bDs) := elabStr (deck169Frame
    "\\alt<+->{\\begin{itemize}\\item Apricot\\end{itemize}}\
{\\begin{itemize}\\item Blueberry\\end{itemize}}")
  t "an unnumberable block-level alt warns W0105 once"
    ((bDs.filter (·.severity != .note)).map (·.code) == #["W0105"])
  let bc := censusOf (coveredColorsOf bDoc) (layoutOf oneFace bDoc)
  t "an unnumberable block-level alt ships its active alternative alone"
    (bc.size == 1 && pageOccurs bc 0 "Apricot" == 1 &&
      pageOccurs bc 0 "Blueberry" == 0 && pageAllRevealed bc 0)
  -- HTML reads the same elaboration: the dropped alternative is not
  -- declared there either, so neither artifact can show a second copy.
  let nHtml := (HtmlDoc.emit {} nDoc).1
  let (_, nBody, _) := HtmlDoc.emitTree {} nDoc
  t "html ships the unnumberable alt's active alternative once, and only it"
    (treeOccurs nBody "apple" == 1 && treeShownOccurs nBody "apple" == 1 &&
      treeOccurs nBody "banana" == 0 && !hasStr nHtml "banana")
  -- Shipped pages: steps are pages, the body is inked ONCE on each, and
  -- no page covers it — alternation replaces, it never dims.
  let (cDoc, _) := elabStr (deck169Frame "One \\alert<2>{apple} here.")
  let c := censusOf (coveredColorsOf cDoc) (layoutOf oneFace cDoc)
  t "alert<2> ships one handout page per step" (c.size == 2)
  t "the body is inked exactly once on every step page"
    (pageOccurs c 0 "apple" == 1 && pageOccurs c 1 "apple" == 1)
  t "no step page covers the body: alternation carries no transparency"
    (!pageCovered c 0 "apple" && !pageCovered c 1 "apple" &&
      pageAllRevealed c 0 && pageAllRevealed c 1)
  -- Which page carries the alert ink: the census reads a run's own colour
  -- through the same channel it reads covering by, given the palette's
  -- alert colour instead of the cover colours.
  let (tDoc, _) := elabStr (themedDeck "One \\alert<2>{apple} here.")
  let alertInk := ((tDoc.palette.entries.find? (·.1 == "alert")).map (·.2))
  let tc := censusOf ((alertInk.map (#[·])).getD #[]) (layoutOf oneFace tDoc)
  let tCov := censusOf (coveredColorsOf tDoc) (layoutOf oneFace tDoc)
  t "the theme declares an alert colour for the census to read" alertInk.isSome
  t "the alert ink is painted on the spec's step page alone"
    (tc.size == 2 && pageAllRevealed tc 0 && pageCovered tc 1 "apple")
  t "the off-step page still inks the body, plain and uncovered"
    (pageOccurs tc 0 "apple" == 1 && pageOccurs tc 1 "apple" == 1 &&
      pageAllRevealed tCov 0 && pageAllRevealed tCov 1)
  -- HTML: both alternatives declared once each, one shown — and the alert
  -- colour rides the crisp group alone. No step wrapper: nothing is
  -- covered, so the covering mechanism is not involved at all.
  let (hDoc, _) := elabStr (themedDeck "One \\alert<2>{quince} here.")
  let html := (HtmlDoc.emit {} hDoc).1
  let (_, hBody, _) := HtmlDoc.emitTree {} hDoc
  t "html declares both alternatives once each and shows one"
    (treeOccurs hBody "quince" == 2 && treeShownOccurs hBody "quince" == 1)
  t "html shows the plain body off the step and hides the styled one"
    (hasStr html "<span class=\"alt alt-pending\" data-step=\"2\" data-step-last=\"2\">quince</span>" &&
      hasStr html ("<span class=\"alt alt-crisp\" data-step=\"2\" data-step-last=\"2\" " ++
        "hidden=\"hidden\"><span style=\"color: var(--alert, "))
  t "html names the alert colour once, on the styled alternative alone"
    ((html.splitOn "color: var(--alert, ").length == 2)
  t "html wraps the alert in no step: an alternation is never covered"
    (!hasStr html "class=\"step\"")
  -- The step-by-step agreement on this fixture: the rules select the group
  -- the shipped page inks (`alt_backend_agree`, read off the artifacts).
  t "alert<2>: the html rules select the group the handout page inks"
    ((List.range 2).all fun i =>
      HtmlDoc.altShownFirstAt 2 2 (some 2) (i + 1) == (pageOccurs tc i "apple" == 1 &&
        !pageCovered tc i "apple"))

/-- The caption-to-alt walk reaches every image of a float's body: a figure
whose body holds its image inside a list still names it by its caption.
The walk is the generic `Ir.mapBlocks`, whose descent is total over the
tree — the hand-rolled walk's wildcard arm skipped list, titled, role,
columns, frame, and float bodies, so a listed image silently kept an empty
alt (the named behaviour change of the `mapBlocks` rehost). Asserted on
the typed HTML tree's rendering, where the alt is reader-visible. -/
def altWalkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{figure}\\begin{itemize}\\item \\includegraphics{one.png}" ++
    "\\end{itemize}\\caption{An invented caption}\\end{figure}\\end{document}")
  t "figure-list source raises no error" (ds.all (·.severity != .error))
  let html := (HtmlDoc.emit {} doc).1
  t "a listed image inherits the figure caption as its alt"
    ((html.splitOn "alt=\"An invented caption\"").length == 2)
  -- The request value covers every image the layout will place: an
  -- `\includegraphics` inside a `\footnote` or a defined role is content
  -- like any other, so it appears in `imageRefs` — the list the driver
  -- loads — and, with the driver's own store, ships as the image rather
  -- than a silent placeholder (the invariant whose absence let a loaded
  -- file beside the document ship as an unexplained box: the collect and
  -- the placement walked different descents; both are one fold now).
  let (idoc, ids) := elabStr ("\\documentclass{article}" ++
    "\\newcommand{\\hl}[1]{\\textbf{#1}}\\begin{document}" ++
    "Seen\\footnote{note \\includegraphics[width=20pt]{notefig.png}} and " ++
    "\\hl{\\includegraphics[width=20pt]{rolefig.png}} here.\\end{document}")
  t "footnote/role image source raises no error" (ids.all (·.severity != .error))
  t "an image inside a footnote is requested"
    ((Ir.imageRefs idoc).contains "notefig.png")
  t "an image inside a defined role is requested"
    ((Ir.imageRefs idoc).contains "rolefig.png")
  let store : Image.Store := { entries := (Ir.imageRefs idoc).map fun s =>
    { src := s, info := some { pxW := 64, pxH := 64 } } }
  let out := layoutOf oneFace idoc (imgs := store)
  let imgSegs := out.pages.flatMap fun p => p.lines.flatMap fun l =>
    l.segs.filterMap fun s => match s with
      | .image store _ _ => some store
      | _ => none
  t "the shipped pages place no unexplained placeholder"
    (!imgSegs.isEmpty && imgSegs.all (·.isSome))

/-- Speaker notes: a side channel — never slide content, omitted from the
PDF handout, an inert hidden aside in HTML for the coming speaker view.
Own function: `main`'s do block has no budget left. -/
def noteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  altWalkChecks ref oneFace
  let (doc, ds) := elabStr (deck169Frame "Visible words.\n\\note{Hidden speaker words.}")
  t "note elaborates to a side channel, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center false #[
      .para #[.text "Visible words."],
      .note #[.para #[.text "Hidden speaker words."]]]])
  -- PDF: the note adds nothing — the page is the page without it.
  let (bare, _) := elabStr (deck169Frame "Visible words.")
  let noted := layoutOf oneFace doc
  let plain := layoutOf oneFace bare
  t "pdf omits the note entirely"
    (noted.pages.map (·.lines.size) == plain.pages.map (·.lines.size))
  -- HTML: an inert hidden aside, available to a speaker view.
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries the note as a hidden aside"
    ((html.splitOn "<aside class=\"note\" hidden=").length == 2 &&
     (html.splitOn "Hidden speaker words.").length == 2)
  -- The generic body-preservation path must never leak a note into
  -- content: inside an argument it vanishes too.
  let (inl, inlDs) := elabStr (deck169Frame "\\textbf{bold \\note{never shown} text}")
  t "a mid-sentence note leaves its paragraph whole and drains to the frame"
    (inlDs.isEmpty &&
     (match inl.body with
      | #[.frame _ _ _ _ #[.para content, .note nbody]] =>
        Ir.plainText content == "bold text" &&
        ((Ir.dumpBlocks "" nbody).splitOn "never shown").length == 2 -- ir tier: note content, not a page claim
      | _ => false))

  -- A note body is absorbed, as beamer absorbs it: a reserved character
  -- there (a bare code-ish underscore is the common case) stays literal
  -- and must not fail the build.
  let (resv, resvDs) := elabStr (deck169Frame "Shown.\n\\note{name_with_underscores & more}")
  t "reserved characters in a note stay literal, erroring nothing"
    (resvDs.isEmpty &&
     (match resv.body with
      | #[.frame _ _ _ _ #[_, .note nbody]] =>
        ((Ir.dumpBlocks "" nbody).splitOn "name_with_underscores & more").length == 2 -- ir tier: note content, not a page claim
      | _ => false))
  -- A note is not slide content, so a frame inside a note cannot carry a
  -- side channel of its own: the inner note is refused, named at the outer
  -- note (E0359), and the frame's visible words survive. An ordinary
  -- note-in-frame (the drain tests above, all `ds.isEmpty`) stays silent.
  let (nested, nestedDs) := elabStr (deck169Body
    "\\note{\\begin{frame}{T}\nspoken \\note{inner aside} words\n\\end{frame}}")
  t "a note inside a note's frame is refused, named"
    ((nestedDs.map (·.code)) == #["E0359"])
  t "the refusal keeps the frame's visible words and drops only the inner note"
    (match nested.body with
     | #[.note #[.frame _ _ _ _ inner]] =>
       ((Ir.dumpBlocks "" inner).splitOn "spoken words").length == 2 && -- ir tier: note content, not a page claim
       ((Ir.dumpBlocks "" inner).splitOn "inner aside").length == 1 -- ir tier: note content, not a page claim
     | _ => false)

/-- The theme × frame-furniture reconciliation invariants: standout and
overlay steps are orthogonal (the flag rides onto every step page), the
furniture belongs to the frame rather than the step (a stepped frame's
pages share one progress position), and a note stays silent through the
themed paths too. -/
def themeReconcileChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let themed (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++
    -- The corrected moloch-lineage values: the original #EB811B alert has
    -- no cover that clears the 3:1 state change on this page (even white
    -- sits at 2.6:1 against it), which is the finding that recoloured the
    -- real bundle — the resolved-design judge (W0345) now holds a shipped
    -- overlay deck to the same bar, so this fixture declares the corrected
    -- alert and the bundle's own 31% fraction.
    "\\palette{ fg = #23373B, bg = #FFFFFF, alert = #A55A13,\n" ++
    "  progressfg = alert, standoutfg = bg, standoutbg = fg, covered = 31\\% }\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- A standout frame carrying steps: one page per step, every page still
  -- inverted, its text still in standoutfg.
  let (soDoc, soDs) := elabStr (themed
    ("\\begin{frame}[standout]\nOne.\n\n\\pause\nTwo.\n\\end{frame}"))
  t "stepped standout source clean" soDs.isEmpty
  let geom := Layout.Geom.ofPage soDoc.page
  let so := layoutOf oneFace soDoc geom
  t "a stepped standout frame gets one page per step" (so.pages.size == 2)
  let fg : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg : Ir.Color := { r := 0xFF, g := 0xFF, b := 0xFF }
  t "every step page of a standout frame stays inverted"
    (so.pages.all fun p => p.fills.any fun f =>
      f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH && f.color == fg)
  t "standout text keeps standoutfg on every step page"
    (so.pages.all fun p => p.lines.any fun l => l.segs.any fun s => match s with
      | .run _ c _ _ _ _ _ _ _ _ => c == bg
      | _ => false)
  -- The furniture is the frame's, not the step's: three step pages advance
  -- the deck position by ONE frame, so the section page after them shows
  -- 1 of 2 elapsed — not 3 of 2.
  let (pDoc, pDs) := elabStr (themed
    ("\\begin{frame}{Steps}\na\n\n\\pause\nb\n\n\\pause\nc\n\\end{frame}\n" ++
     "\\section{Mid}\n\\begin{frame}{After}\nd\n\\end{frame}"))
  t "stepped deck source clean" pDs.isEmpty
  let pOut := layoutOf oneFace pDoc
  t "step pages plus divider plus frame" (pOut.pages.size == 5)
  let alert : Ir.Color := { r := 0xA5, g := 0x5A, b := 0x13 }
  let mp : Dim.Sp := (Layout.Geom.ofPage pDoc.page).textWidth * 7875 / 10000
  t "the progress position belongs to the frame, not the step"
    (match pOut.pages[3]? with
     | some p => p.fills.any fun f => f.w == mp / 2 && f.color == alert
     | none => false)
  -- A note through the themed standout path: the page is the page
  -- without it.
  let (nDoc, _) := elabStr (themed
    "\\begin{frame}[standout]\nShown.\n\\note{never printed}\n\\end{frame}")
  let (bDoc, _) := elabStr (themed "\\begin{frame}[standout]\nShown.\n\\end{frame}")
  let nOut := layoutOf oneFace nDoc
  let bOut := layoutOf oneFace bDoc
  t "a themed standout frame does not print its speaker note"
    (nOut.pages.map (·.lines.size) == bOut.pages.map (·.lines.size))

/-- `\chrome` and the bundles' chrome: page furniture as declared data, a
slot naming a per-page datum, redeclaration merging per slot — a theme's
chrome is a default exactly as its palette is. -/
def chromeDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let frame := "\\begin{frame}{T}\nx\n\\end{frame}"
  let (mDoc, mDs) := elabStr (deck169 "\\theme{moloch}" frame)
  t "chrome moloch source clean" mDs.isEmpty
  -- The dtx footline has two slots, `frame footer` and the number: the
  -- left one is the author's, so the bundle declares none for it
  -- (`Theme.footline_left_contract`).
  t "moloch declares the footer's right slot and leaves the left to \\framefoot"
    (mDoc.chrome.footerLeft == none &&
     mDoc.chrome.footerRight == some .frameNumber)
  t "moloch declares the muted step"
    (mDoc.palette.find? "muted" == some { r := 0x64, g := 0x72, b := 0x74 })
  t "plain declares the same footer"
    ((elabStr (deck169 "\\theme{plain}" frame)).1.chrome.hasFooter)
  t "a deck opted out by name has no chrome"
    (!(elabStr (deck169 "\\theme{default}" frame)).1.chrome.hasFooter)
  t "a themeless deck takes the daylight footer"
    ((elabStr (deck169 "" frame)).1.chrome.hasFooter)
  -- A later \chrome refines the theme's footer per slot, as \palette
  -- entries override per name and keep their siblings: the theme is a
  -- default, never a lock — and never an all-or-nothing one. Clearing the
  -- whole band is `\runningfoot`, which outranks chrome.
  let (oDoc, oDs) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { right = \\slidenumber } }" frame)
  t "a document's chrome refines the theme's footer per slot" (oDs.isEmpty &&
    oDoc.chrome.footerLeft == none &&
    oDoc.chrome.footerRight == some .frameNumber)
  -- The install direction of the same per-slot contract: a bundle fills
  -- the slots it declares and only those (`Theme.apply`), never the band
  -- wholesale. Both shipped bundles declare both slots, so the wholesale
  -- clobber is only observable through a single-slot bundle — which is
  -- exactly what makes this the load-bearing test: it fails under
  -- `chrome := th.chrome`.
  let leftOnly : Theme.Theme := { name := "left-only"
                                  palette := {}
                                  tokens := {}
                                  styles := {}
                                  chrome := { footerLeft := some .sectionTitle } }
  t "a bundle's chrome fills only the slots it declares"
    ((Theme.apply leftOnly { chrome := { footerRight := some .frameNumber } }).chrome ==
      { footerLeft := some .sectionTitle, footerRight := some .frameNumber })
  t "a bundle with no chrome keeps the document's band"
    ((Theme.apply { name := "bare"
                    palette := {}
                    tokens := {}
                    styles := {} }
      { chrome := { footerLeft := some .frameFraction } }).chrome ==
      { footerLeft := some .frameFraction })
  -- The positional rule at the theme site: a theme declared after the
  -- document's \chrome wins the slots it names, per slot, the same
  -- last-writer rule every palette entry follows.
  let (bDoc, _) := elabStr (deck169
    "\\chrome{ footer = { right = \\framefraction } }\\theme{moloch}" frame)
  -- moloch names only the right slot and the document named none for the
  -- left: the left stays empty through the install (`Theme.apply` merges
  -- per slot).
  t "a theme after the document's chrome wins per slot"
    (bDoc.chrome.footerLeft == none &&
     bDoc.chrome.footerRight == some .frameNumber)
  -- The sketch's spelling and the beamer lineage's name one datum.
  t "slidenumber and framenumber are one datum"
    ((elabStr (deck169 "\\chrome{ footer = { right = \\framenumber } }" frame)).1.chrome ==
     (elabStr (deck169 "\\chrome{ footer = { right = \\slidenumber } }" frame)).1.chrome)
  t "unknown chrome key names the known one"
    ((elabStr (deck169 "\\chrome{ logo = x }" frame)).2.any fun d =>
      d.code == "E0322" && ((d.help.getD "").splitOn "footer").length == 2)
  t "unknown slot key names left and right"
    ((elabStr (deck169 "\\chrome{ footer = { top = \\framenumber } }" frame)).2.any
      (·.code == "E0322"))
  t "an unreadable slot names the data"
    ((elabStr (deck169 "\\chrome{ footer = { left = \\pagenumber } }" frame)).2.any fun d =>
      d.code == "E0321" && ((d.help.getD "").splitOn "sectiontitle").length == 2)
  t "a non-block footer is a type error"
    ((elabStr (deck169 "\\chrome{ footer = 3pt }" frame)).2.any (·.code == "E0323"))
  t "chrome outside slides warns"
    ((elabStr ("\\documentclass{article}\\chrome{ footer = { right = \\framenumber } }" ++
      "\\begin{document}x\\end{document}")).2.any (·.code == "W0318"))
  -- FINDINGS F4: the frame and physical sequences share a band only by
  -- declaration. A theme-installed frame slot plus \framefoot{\pagenumber}
  -- is undeclared mixing (W0332); the document naming its own \chrome slots
  -- IS the declaration, so the same band is then silent.
  let mixedBody := "\\framefoot{p. \\pagenumber}\n\\begin{frame}{T}\nx\n\\end{frame}"
  t "undeclared sequence mixing warns by name"
    ((elabStr (deck169 "\\theme{moloch}" mixedBody)).2.any fun d =>
      d.code == "W0332" && d.severity == .warning)
  t "a document that declares its chrome has declared the mixing"
    (!(elabStr (deck169 "\\theme{moloch}\\chrome{ footer = { right = \\framenumber } }"
      mixedBody)).2.any (·.code == "W0332"))
  t "no frame slot, no mixing"
    (!(elabStr (deck169 "\\theme{default}" mixedBody)).2.any (·.code == "W0332"))
  t "a physical-free framefoot mixes nothing"
    (!(elabStr (deck169 "\\theme{moloch}"
      "\\framefoot{note}\n\\begin{frame}{T}\nx\n\\end{frame}")).2.any
      (·.code == "W0332"))
  -- The sequences cannot quietly fuse: the physical pass leaves a rendered
  -- frame slot untouched on every page (`substPage_leaves_frame_slot` is
  -- the theorem; this pins one instance executably).
  t "substPage leaves a rendered frame slot alone"
    (Layout.substPage 7 9 (Ir.ChromeSlot.frameFraction.render #[] 2 5) ==
      Ir.ChromeSlot.frameFraction.render #[] 2 5)
  -- The muted rule is load-bearing: one step weaker (fg!60!bg) fails the
  -- bundle contract the theorems hold.
  let weaker : Ir.Palette := { entries :=
    Theme.moloch.palette.entries.map fun (k, c) =>
      if k == "muted" then (k, { r := 121, g := 133, b := 135 }) else (k, c) }
  t "the palette contract rejects a muted one step weaker"
    (!Contrast.paletteContract weaker)

/-- W0348: a theme replacing a key the document already declared is said,
naming the theme and the key, and pointing past `\theme` — the positional
last-writer rule, out loud (audit item 5). It fires only when the loser is
the document's own declaration with a different value: a theme filling
untouched keys, a document overriding after `\theme`, a same-value repeat,
and a bundle replacing an earlier bundle's values all stay silent. -/
def layerDiagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ds (pre : String) : Array Diag :=
    (elabStr (deck169 pre "\\begin{frame}{T}\nx\n\\end{frame}")).2
  t "a theme replacing a document-declared colour names both"
    ((ds "\\palette{ alert = #112233 }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "'alert'").length == 2 &&
        (d.message.splitOn "moloch").length == 2)
  t "the help points past theme"
    ((ds "\\palette{ alert = #112233 }\\theme{moloch}").any fun d =>
      d.code == "W0348" && ((d.help.getD "").splitOn "\\theme").length == 2)
  t "a theme filling keys the document never declared is silent"
    (!(ds "\\theme{moloch}").any (·.code == "W0348"))
  t "an override after the theme is silent"
    (!(ds "\\theme{moloch}\\palette{ alert = #112233 }").any (·.code == "W0348"))
  t "a declaration the theme agrees with replaces nothing"
    (!(ds "\\palette{ alert = #A55A13 }\\theme{moloch}").any (·.code == "W0348"))
  t "a second theme replacing the first theme's values is silent"
    (!(ds "\\theme{plain}\\theme{moloch}").any (·.code == "W0348"))
  t "a replaced chrome slot is named as its slot"
    ((ds "\\chrome{ footer = { right = \\framefraction } }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "footer.right").length == 2)
  t "a replaced covered fraction is named"
    ((ds "\\palette{ covered = 50\\% }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "'covered'").length == 2)
  t "a replaced element style is named"
    ((ds "\\style{frametitle}{ font = {\\small} }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "frametitle").length == 2)
  t "a replaced token is named"
    ((ds "\\tokens{ progressheight = 3pt }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "progressheight").length == 2)
  t "an untouched element style beside a replaced one stays silent"
    (((ds "\\style{section}{ before = 3pt }\\theme{moloch}").filter
      (·.code == "W0348")).isEmpty)

/-- The footer band is reserved, never overlaid: `Geom.bodyBottom` is the one
place a footer's band comes out of the page, placement reads the bottom only
from there, and `bodyBottom_clears_footer` is the arithmetic that the
reservation suffices. This pins layout to actually reading it, on a page
whose margin is too small to hold the foot line. -/
def footerBandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para := String.intercalate " " (List.replicate 300 "filler words run on")
  let src := "\\page{ vmargin = 2pt }\n\\runningfoot{quiet foot}\n" ++
    "\\begin{document}\n" ++ para ++ "\n\n" ++ para ++ "\n\\end{document}"
  let (doc, ds) := elabStr src
  t "band source clean" (ds.filter (·.severity == .error)).isEmpty
  let geom0 := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom0
  let font := oneFace.body
  let ascent : Dim.Sp := font.ascent * geom0.fontSize / (font.unitsPerEm : Int)
  let descent : Dim.Sp := (-font.descent) * geom0.fontSize / (font.unitsPerEm : Int)
  let band := Layout.furnitureBand geom0.vmargin (ascent + descent) none
  let geom := { geom0 with footBand := band.band }
  t "a 6pt margin cannot hold the foot line, so the band bites"
    (geom.footBand > (0 : Dim.Sp))
  let footY := Layout.furnFootY band geom.pageH descent
  t "the foot line is laid on every page"
    (!out.pages.isEmpty && out.pages.all fun p => p.lines.any (·.y == footY))
  t "body ink stops above the reserved band"
    (out.pages.all fun p => p.lines.all fun l =>
      l.y == footY || l.y + descent ≤ geom.bodyBottom)
  -- The check is load-bearing: without the reservation, this document's
  -- last body line reaches into the footer's band.
  let (bare, _) := elabStr ("\\page{ vmargin = 2pt }\n\\begin{document}\n" ++
    para ++ "\n\n" ++ para ++ "\n\\end{document}")
  let bareOut := layoutOf oneFace bare
  t "the fixture reaches the band it is about"
    (bareOut.pages.any fun p => p.lines.any fun l => l.y + descent > geom.bodyBottom)

/-- The chrome footer through layout and the HTML backend: frame pages carry
the section in force and their frame's own number, furniture pages carry
none, a stepped frame's pages share one number, `\runningfoot` overrides the
whole footer, and an unthemed deck is untouched. -/
def chromeFooterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let body :=
    "\\begin{frame}{One}\na\n\\end{frame}\n" ++
    "\\section{Topic}\n" ++
    "\\begin{frame}{Two}\nb\n\n\\pause\nc\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nQ\n\\end{frame}"
  -- The section title in the left slot is the document's declaration: the
  -- bundle leaves that slot to \\framefoot (`Theme.footline_left_contract`).
  let (doc, ds) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }" body)
  t "chrome deck source clean" ds.isEmpty
  let geom0 := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom0
  t "chrome deck five pages" (out.pages.size == 5)
  t "frame pages carry a footer, furniture pages none"
    (out.pages.map (·.foot.isSome) == #[true, false, true, true, false])
  t "the footer shows the frame's own number"
    ((out.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "1")
  t "the footer shows the section in force beside the number"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic2")
  t "a stepped frame's pages share one footer"
    (out.pages[2]?.bind (·.foot) == out.pages[3]?.bind (·.foot))
  let font := oneFace.body
  let footSize := Ir.scaleStep geom0.fontSize Ir.footline.step
  let descent : Dim.Sp := (-font.descent) * geom0.fontSize / (font.unitsPerEm : Int)
  -- A flat digit's band has no depth: its baseline stands exactly moloch's
  -- closing `\vskip4pt` above the paper's bottom edge.
  let footY := Layout.footBaseline geom0.pageH 0
  t "the foot line stands 4 pt above the paper's edge at the footline's step, in muted"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.y == footY && l.size == footSize &&
         l.segs.any fun s => match s with
           | .run _ c _ _ _ _ _ _ _ _ => c == ({ r := 0x64, g := 0x72, b := 0x74 } : Ir.Color)
           | _ => false
     | none => false)
  -- Invariant (a) of the footer: body ink never reaches the footer's ink,
  -- on a frame whose body demonstrably fills the page.
  let para := String.intercalate " " (List.replicate 120 "filler words run on")
  let (tallDoc, _) := elabStr (deck169 "\\theme{moloch}"
    ("\\begin{frame}{Tall}\n" ++ para ++ "\n\n" ++ para ++ "\n\\end{frame}"))
  let tallOut := layoutOf oneFace tallDoc geom0
  t "a tall frame spills and every spill page keeps its footer"
    (tallOut.pages.size > 1 && tallOut.pages.all (·.foot.isSome))
  t "body ink stays beamer's 4 pt clear of the footer's ink"
    (tallOut.pages.all fun p =>
      match p.lines.find? fun l => l.furniture && l.y == footY with
      | some f => p.lines.all fun l => l.furniture ||
          l.y + descent + Ir.footline.sep ≤ f.y - (Layout.segsInk oneFace f.segs).1
      | none => false)
  t "the tall frame demonstrably fills the body area"
    (tallOut.pages.any fun p => p.lines.any fun l =>
      l.y != footY && l.y + descent + Ir.leadingFor geom0.fontSize >
        (Layout.Geom.ofPage tallDoc.page).bodyBottom)
  -- \runningfoot is the author's whole footer: chrome yields entirely.
  let (rDoc, _) := elabStr (deck169 "\\theme{moloch}\\runningfoot{own foot}" body)
  let rOut := layoutOf oneFace rDoc
  t "runningfoot suppresses the chrome footer"
    (rOut.pages.all (·.foot.isNone))
  -- A declared foot is a body-font line: its ink bottom stands at the same
  -- edge gap, its baseline its own descent higher.
  let runFootY := Layout.furnFootY
    (Layout.furnitureBand geom0.vmargin
      (font.ascent * geom0.fontSize / (font.unitsPerEm : Int) + descent) none)
    geom0.pageH descent
  t "runningfoot itself is laid on every page"
    (rOut.pages.all fun p => p.lines.any (·.y == runFootY))
  -- Bareness by name: `\theme{default}` opts out of the daylight
  -- default, and the deck's output carries no footer.
  let (uDoc, _) := elabStr (deck169 "\\theme{default}" body)
  let uOut := layoutOf oneFace uDoc
  t "an unthemed deck carries no footer at all"
    (uOut.pages.all fun p => p.foot.isNone && p.lines.all (·.y != footY))
  -- The HTML backend reads the same declarations: each non-standout frame
  -- section closes with the footer, styled by the muted token and the
  -- shared size scale.
  let (html, _) := HtmlDoc.emit {} doc
  -- One footer per frame section: the stepped frame is one section now,
  -- so its number appears once — the PDF's step pages still repeat it.
  t "html frames close with the footer, standout none"
    ((html.splitOn ("class=\"slide-foot size-" ++ Ir.footline.step ++ "\"")).length == 3)
  t "html footer carries the stepped frame's one number"
    ((html.splitOn ">2</span>").length == 2)
  t "html footer styling comes from the tokens"
    ((html.splitOn "section.slide > footer.slide-foot").length == 2 &&
     (((html.splitOn "footer.slide-foot {")[1]?.getD "").splitOn
       "var(--muted)").length == 2)
  let (rHtml, _) := HtmlDoc.emit {} rDoc
  t "html drops the chrome footer under runningfoot too"
    ((rHtml.splitOn "slide-foot").length == 1)
  -- \chrome without a theme: the declaration alone is enough.
  let (cDoc, cDs) := elabStr (deck169 "\\chrome{ footer = { right = \\framenumber } }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  let cOut := layoutOf oneFace cDoc
  t "a bare chrome declaration draws its footer" (cDs.isEmpty &&
    ((cOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "1"))

/-- One numbering, every consumer: the numbering audit's constructed
disagreements, pinned. The title page bears no footer and no number and the
first content frame is 1 (moloch: `\maketitle` is
`\frame[plain,noframenumbering]{\titlepage}`); the section-page progress
reads the same numbering, 0/N before any content frame; a stepped frame's
pages share one number and a `\framefoot` note sits beside it; the chrome
frame number and the physical `\pagenumber`/`\pagecount` stay two declared
sequences; and the PDF footer text is the HTML footer text, frame for
frame — both read `Ir.frameNumbers` and neither counts. -/
def numberingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The HTML tree pretty-prints, so tags and indentation are stripped and
  -- the comparison is over the footer's own characters.
  let strip (s : String) : String := Id.run do
    let mut out := ""
    let mut inTag := false
    for c in s.toList do
      if c == '<' then inTag := true
      else if c == '>' then inTag := false
      else if !inTag && !c.isWhitespace then out := out.push c
    return out
  let htmlFoots (html : String) : List String :=
    -- Consecutive sections sharing one footer are one frame: the deck is
    -- one section per frame now, so this collapse is the PDF side's
    -- (steps, spills) mirrored — the frame-level sequence both agree on.
    let raw := ((html.splitOn ("class=\"slide-foot size-" ++ Ir.footline.step ++ "\">")).drop 1).map fun s =>
      strip ((s.splitOn "</footer>")[0]?.getD "")
    (raw.foldl (fun (acc : List String) s =>
      if acc.head? == some s then acc else s :: acc) []).reverse
  -- Consecutive pages sharing one footer are one frame (steps, spills):
  -- the frame-level sequence both backends must agree on.
  let pdfFoots (out : Layout.Out) : List String :=
    (out.pages.foldl (fun (acc : List String) p =>
      match p.foot with
      | some f =>
        let s := strip (Ir.plainText (Ir.bandInlines f))
        if acc.head? == some s then acc else s :: acc
      | none => acc) []).reverse
  -- The headline disagreement: the title page carried footer "1" and the
  -- first content frame showed "2"; the progress fraction counted both.
  let (doc, ds) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n\\begin{frame}{One}\na\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "numbering deck source clean" ds.isEmpty
  t "the numbering skips title and standout and reaches its count"
    (doc.frameCount == 1 && doc.frameNumbers.toList.filterMap id == [1])
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  t "numbering deck four pages" (out.pages.size == 4)
  t "the title page and the standout carry no footer, the content frame does"
    (out.pages.map (·.foot.isSome) == #[false, false, true, false])
  t "the content frame is frame 1, not 2"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "S1")
  t "the progress bar shows 0 of 1 before any content frame"
    (match out.pages[1]? with
     | some p => (p.fills.any fun f => f.color == ({ r := 0xCB, g := 0xC0, b := 0xB6 } : Ir.Color)) &&
         !(p.fills.any fun f => f.color == ({ r := 0xA5, g := 0x5A, b := 0x13 } : Ir.Color))
     | none => false)
  let (html, _) := HtmlDoc.emit {} doc
  t "html gives the title and standout frames no footer"
    ((html.splitOn ("class=\"slide-foot size-" ++ Ir.footline.step ++ "\"")).length == 2)
  t "html numbers the content frame 1"
    ((html.splitOn ">1</span>").length == 2)
  t "html progress is 0% before any content frame"
    ((html.splitOn "width: 0%").length == 2)
  t "pdf and html footers are the same text" (pdfFoots out == htmlFoots html)
  -- Steps, a \framefoot note, and the two-sequences deck: the note takes
  -- the left slot beside the frame's number, a stepped frame's pages share
  -- one number, and the backends agree frame for frame.
  let (dDoc, dDs) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n" ++
     "\\begin{frame}{A}\na\n\n\\pause\nb\n\\end{frame}\n" ++
     "\\section{S}\n\\framefoot{note}\n" ++
     "\\begin{frame}{B}\nc\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "two-sequences deck source clean" dDs.isEmpty
  t "two content frames count 1 and 2"
    (dDoc.frameCount == 2 && dDoc.frameNumbers.toList.filterMap id == [1, 2])
  let dOut := layoutOf oneFace dDoc
  t "two-sequences deck six pages" (dOut.pages.size == 6)
  t "a stepped frame's pages share one footer"
    (dOut.pages[1]?.bind (·.foot) == dOut.pages[2]?.bind (·.foot))
  t "the framefoot note sits beside the frame's own number"
    ((dOut.pages[4]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "note2")
  let (dHtml, _) := HtmlDoc.emit {} dDoc
  t "pdf and html footers agree across steps and notes"
    (pdfFoots dOut == htmlFoots dHtml && htmlFoots dHtml == ["1", "note2"])
  -- \pagenumber/\pagecount stay the physical sequence: a \runningfoot deck
  -- numbers its pages 1..pages.size (title page included), while the frame
  -- count is its own declared sequence — two models, both stated.
  let (rDoc, rDs) := elabStr (deck169
    ("\\theme{moloch}\\title{T}\\author{A}" ++
     "\\runningfoot{page \\pagenumber\\ of \\pagecount}")
    ("\\maketitle\n\\begin{frame}{One}\na\n\\end{frame}"))
  t "physical deck source clean" rDs.isEmpty
  let rOut := layoutOf oneFace rDoc
  t "runningfoot suppresses chrome and the physical count is the page count"
    (rOut.pages.size == 2 && rOut.pages.all (·.foot.isNone) && rDoc.frameCount == 1)
  t "the physical sequence substitutes per page"
    (Ir.plainText (Layout.substPage 2 2 (rDoc.foot.getD #[])) == "page 2 of 2")
  -- The clamps are gone because they cannot fire: the position is a some
  -- of the numbering, ≤ the count by theorem. The bar fills exactly at the
  -- end, and a deck with no countable frame draws no bar at all.
  let (fDoc, _) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    ("\\begin{frame}{One}\na\n\\end{frame}\n\\section{End}"))
  let fGeom := Layout.Geom.ofPage fDoc.page
  let fOut := layoutOf oneFace fDoc fGeom
  let mp : Dim.Sp := fGeom.textWidth * 7875 / 10000
  t "a section after every frame fills the bar exactly"
    (fOut.pages.any fun p => p.fills.any fun f =>
      f.w == mp && f.color == ({ r := 0xA5, g := 0x5A, b := 0x13 } : Ir.Color))
  let (zDoc, zDs) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "zero-count deck source clean" zDs.isEmpty
  t "a deck with no countable frame draws no progress bar"
    (zDoc.frameCount == 0 &&
     (layoutOf oneFace zDoc).pages.all fun p =>
       !(p.fills.any fun f => f.color == ({ r := 0xCB, g := 0xC0, b := 0xB6 } : Ir.Color)))
  t "html draws no progress bar with no countable frame"
    (((HtmlDoc.emit {} zDoc).1.splitOn "class=\"progress\"").length == 1)
  -- The fraction slot: moloch's numbering=fraction, reachable as
  -- \framefraction, rendered by the one Ir.ChromeSlot.render site on both
  -- backends — the denominator is the same frameCount everywhere.
  let (cDoc, cDs) := elabStr (deck169
    "\\chrome{ footer = { right = \\framefraction } }"
    ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}"))
  t "framefraction parses to its slot" (cDs.isEmpty &&
    cDoc.chrome.footerRight == some .frameFraction)
  let cOut := layoutOf oneFace cDoc
  t "the fraction footer reads n / N"
    (cOut.pages.map (fun p => (p.foot.map (fun f => Ir.plainText (Ir.bandInlines f))).getD "") ==
      #["1 / 2", "2 / 2"])
  let (cHtml, _) := HtmlDoc.emit {} cDoc
  t "pdf and html agree on the fraction form"
    (pdfFoots cOut == htmlFoots cHtml && htmlFoots cHtml == ["1/2", "2/2"])
  -- The physical gate does not silence frame furniture: \runninghead's
  -- [from = 2] keeps the head off the opening page (the physical model),
  -- while the opening frame's own chrome footer — the frame model — stays.
  let (gDoc, gDs) := elabStr (deck169
    "\\theme{moloch}\\runninghead[from = 2]{An Invented Head}"
    ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}"))
  t "gated deck source clean" gDs.isEmpty
  let gGeom := Layout.Geom.ofPage gDoc.page
  let gOut := layoutOf oneFace gDoc gGeom
  let gFont := oneFace.body
  let headY := gGeom.vmargin / 2 + gFont.ascent * gGeom.fontSize / (gFont.unitsPerEm : Int)
  let footY := Layout.footBaseline gGeom.pageH 0
  t "runningFrom keeps the head off page 1 and on page 2"
    ((gOut.pages.map fun p => p.lines.any (·.y == headY)) == #[false, true])
  t "runningFrom does not gate the frame's chrome footer"
    (gOut.pages.all fun p => p.lines.any (·.y == footY))
  -- A running line that wraps is a named diagnostic, never a silent
  -- truncation to its first line.
  let longFoot := String.intercalate " " (List.replicate 40 "an overlong footer")
  let (wDoc, _) := elabStr (deck169 s!"\\runningfoot\{{longFoot}}"
    "\\begin{frame}{A}\na\n\\end{frame}")
  let wOut := layoutOf oneFace wDoc
  t "a wrapping running line warns by name"
    (wOut.diags.any (·.code == "W0328"))
  t "a one-line running line does not warn"
    (!rOut.diags.any (·.code == "W0328"))

/-- The deck's own footer route: `\setbeamertemplate{frame footer}` — alone
or expanded from a `\newenvironment` wrapper — reaches the chrome footer's
left slot as `\framefoot`, instead of dying with W0104. The note holds for
the frames that follow, an empty one clears back to the default, and the
frame number keeps its slot throughout. -/
def frameFootChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The wrapper exactly as a beamer deck defines it, through compat.
  let wrapper := "\\newenvironment{framefooter}[1]" ++
    "{\\setbeamertemplate{frame footer}{#1}}{\\setbeamertemplate{frame footer}{}}"
  let body :=
    "\\section{Topic}\n" ++
    "\\begin{frame}{One}\na\n\\end{frame}\n" ++
    "\\begin{framefooter}{origin: example.org}\n" ++
    "\\begin{frame}{Two}\nb\n\\end{frame}\n" ++
    "\\end{framefooter}\n" ++
    "\\begin{frame}{Three}\nc\n\\end{frame}"
  let (doc, ds) := elabStr (deck169
    ("\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }" ++ wrapper) body)
  t "framefooter deck raises no W0104" (!ds.any (·.code == "W0104"))
  t "framefooter deck source clean" (ds.filter (·.severity == .error)).isEmpty
  let out := layoutOf oneFace doc
  -- pages: section page, One, Two, Three
  t "framefooter deck four pages" (out.pages.size == 4)
  t "before the wrapper the default footer stands"
    ((out.pages[1]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic1")
  t "the wrapped frame carries the note beside its number"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "origin: example.org2")
  t "the wrapper's end clears back to the default"
    ((out.pages[3]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic3")
  -- The bare template call, no wrapper, no theme: the note alone is a
  -- footer — an unthemed deck's framefooter is not silently dropped.
  let (bDoc, bDs) := elabStr (deck169 "\\theme{default}"
    ("\\setbeamertemplate{frame footer}{quiet note}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a bare frame footer template is clean" (!bDs.any (·.code == "W0104"))
  let bOut := layoutOf oneFace bDoc
  t "the unthemed note still lands"
    ((bOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "quiet note")
  -- Other templates drop their body; a body carrying content is a dropped
  -- loss (footline carries the frame number), named with the native spelling.
  let (_, fDs) := elabStr (deck169 ""
    ("\\setbeamertemplate{footline}{\\insertframenumber}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a content-carrying template drops as an error naming framefoot"
    (fDs.any fun d => d.code == "E0111" && d.severity == .error &&
      ((d.help.getD "").splitOn "framefoot").length == 2)
  -- The HTML backend reads the same override.
  let (html, _) := HtmlDoc.emit {} doc
  t "html wrapped frame carries the note"
    ((html.splitOn "origin: example.org").length == 2)
  t "html unwrapped frames keep the section title"
    ((html.splitOn ">Topic</span>").length == 3)

/-- The themed slides furniture, keyed on the semantic palette entries: page
background and text colour, the frame-title bar, the section page with its
progress bar. No theme machinery here — the keys are the API, so a theme
stays a table of values. -/
def themeFurnitureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ fg = #23373B, bg = black!2, alert = #EB811B,\n" ++
    "  frametitlefg = bg, frametitlebg = fg,\n" ++
    "  progressfg = alert, progressbg = progressfg!50!black!30 }\n" ++
    "\\tokens{ progressheight = 2pt }\n" ++
    "\\begin{document}\n" ++
    "\\begin{frame}{First}\nalpha\n\\end{frame}\n" ++
    "\\section{Middle}\n" ++
    "\\begin{frame}{Second}\nbeta\n\\end{frame}\n" ++
    "\\end{document}"
  let (doc, ds) := elabStr src
  t "furniture source clean" ds.isEmpty
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  t "furniture three pages: frame, divider, frame" (out.pages.size == 3)
  let bg : Ir.Color := { r := 0xFA, g := 0xFA, b := 0xFA }
  let fg : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  t "every page carries the background"
    (out.pages.all fun p => p.fills.any fun f =>
      f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH && f.color == bg)
  t "frame title is a colour bar"
    (match out.pages[0]? with
     | some p => p.fills.any fun f =>
        f.color == fg && f.w == geom.pageW && f.y == 0 && f.h < geom.pageH / 3
     | none => false)
  t "frame title text takes frametitlefg"
    (match out.pages[0]?.bind (·.lines[0]?) with
     | some l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ _ _ _ => c == bg
        | _ => false
     | none => false)
  t "body text takes fg"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ _ _ _ => c == fg
        | _ => false
     | none => false)
  let mp : Dim.Sp := geom.textWidth * 7875 / 10000
  let alert : Ir.Color := { r := 0xEB, g := 0x81, b := 0x1B }
  t "section page draws the progress track in the mixed colour"
    (match out.pages[1]? with
     | some p => p.fills.any fun f =>
        f.w == mp && f.h == Dim.pt 2 &&
        f.color == ((alert.mix 50 Ir.Color.black).mix 30 Ir.Color.white)
     | none => false)
  t "the elapsed share is the deck position (1 of 2 frames)"
    (match out.pages[1]? with
     | some p => p.fills.any fun f => f.w == mp / 2 && f.h == Dim.pt 2 && f.color == alert
     | none => false)
  t "section page centres vertically"
    (match out.pages[1]?.bind (·.lines[0]?), out.pages[0]?.bind (·.lines[0]?) with
     | some sl, some fl => sl.y > fl.y + geom.pageH / 4
     | _, _ => false)
  let (html, _) := HtmlDoc.emit {} doc
  t "html body takes bg and fg"
    ((html.splitOn "body { background: var(--bg); }").length == 2 &&
     (html.splitOn "body { color: var(--fg); }").length == 2)
  t "html frame header is a bar"
    ((html.splitOn "section.slide > header { background: var(--frametitlebg);").length == 2)
  t "html section page carries its position"
    ((html.splitOn "class=\"section-page\"").length == 2 &&
     (html.splitOn "width: 50%").length == 2)
  -- Output opted out by name is untouched: no keys, no fills, black text.
  let (plainDoc, _) := elabStr ("\\documentclass[aspectratio=169]{slides}\n" ++
    "\\theme{default}\n" ++
    "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")
  let plainOut := layoutOf oneFace plainDoc
  t "unthemed pages carry no fills" (plainOut.pages.all (·.fills.isEmpty))

/-- Frames as first-class blocks: the elaboration shape, the title forms,
the title frame, and the page-per-frame contract in layout. Its own
function: `main`'s do block has no elaboration budget left. -/
def slideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (fDoc, fDs) := elabStr (deck169Body "\\begin{frame}{T}\nbody\n\\end{frame}")
  t "frame source clean" fDs.isEmpty
  t "frame is first-class with its title"
    (fDoc.body == #[.frame #[.text "T"] false .center false #[.para #[.text "body"]]])
  -- A group after a paragraph break is content, not a title: LaTeX's own
  -- argument scanning stops looking there too.
  t "frame title after a blank line is content"
    ((elabStr (deck169Body "\\begin{frame}[plain]\n\n{scope group}\n\\end{frame}")).1.body ==
      #[.frame #[] false .center false #[.para #[.text "scope group"]]])
  -- Options that say how beamer should cope (fragile, plain) are ignored
  -- with a registered note, never silently.
  t "an unmodelled frame option is a note"
    ((elabStr (deck169Body "\\begin{frame}[fragile]{T}\nbody\n\\end{frame}")).2.any
      fun d => d.code == "N0102" && d.severity == .note)
  t "frametitle names the frame"
    ((elabStr (deck169Body "\\begin{frame}\n\\frametitle{Named}\nbody\n\\end{frame}")).1.body ==
      #[.frame #[.text "Named"] false .center false #[.para #[.text "body"]]])
  -- Two titles: the last wins, as in beamer, but never silently.
  let (dupDoc, dupDs) := elabStr
    (deck169Body "\\begin{frame}\n\\frametitle{One}\n\\frametitle{Two}\nbody\n\\end{frame}")
  t "a second frametitle warns and wins"
    (dupDs.any (·.code == "W0311") &&
     match dupDoc.body with
     | #[.frame title _ _ _ _] => Ir.plainText title == "Two"
     | _ => false)
  -- \title and friends may sit in the body, as beamer documents do; an
  -- empty declaration (\date{}) is deliberately blank and sets nothing.
  let titled := deck169Body ("\\title{A Deck}\\subtitle{Sub}\\author{Pat Placeholder}\\date{}\n" ++
    "\\maketitle\n\\begin{frame}{One}\nx\n\\end{frame}")
  let (tDoc, tDs) := elabStr titled
  t "maketitle source clean" tDs.isEmpty
  t "maketitle is a centered title frame with the empty date dropped"
    (match tDoc.body[0]? with
     | some (Ir.Block.frame title _ _ _ #[.center inner]) => title.isEmpty && inner.size == 3
     | _ => false)
  t "pdf metadata falls back to the title declarations"
    (tDoc.info.title == some "A Deck" && tDoc.info.author == some "Pat Placeholder")
  t "slides default to the 16:9 stage"
    (tDoc.page.width == Dim.mm 160 && tDoc.page.height == Dim.mm 90)
  t "slides without the option are 4:3"
    ((elabStr "\\documentclass{slides}\\begin{document}x\\end{document}").1.page.width ==
      Dim.mm 128)
  t "a declared page beats the stage"
    ((elabStr ("\\documentclass{slides}\\page{ width = 300pt, height = 200pt }" ++
      "\\begin{document}x\\end{document}")).1.page.width == Dim.pt 300)
  t "article keeps its page" ((elabStr "x").1.page.width == Dim.pt 612)
  -- Layout: a frame is a page of the handout, a section its own divider
  -- page, and content never flattens into the neighbouring frame.
  let threeFrames := deck169Body ("\\begin{frame}{A}\na\n\\end{frame}\n" ++
    "\\begin{frame}{B}\nb\n\\end{frame}\n\\section{S}\n\\begin{frame}{C}\nc\n\\end{frame}")
  let (dDoc, dDs) := elabStr threeFrames
  t "deck source clean" dDs.isEmpty
  let out := layoutOf oneFace dDoc
  t "one page per frame, one per section divider" (out.pages.size == 4)
  t "every slide leads with its title at the heading size"
    (out.pages.all fun p =>
      p.lines.any (·.size == Layout.sectionSize (Layout.Geom.ofPage dDoc.page) 1))
  let (html, _) := HtmlDoc.emit {} dDoc
  t "html gives each frame its own slide section"
    ((html.splitOn "<section class=\"slide\"").length == 4)
  -- Math environments carry their source whole — elaborating `&` and `\\`
  -- as text would shred the alignment; tables degrade to rows of cells and
  -- `&` never reaches inline elaboration as a reserved-character error.
  t "align* is one display-math grid, cells and rows intact"
    (match (elabStr "\\begin{align*}1 &= 1 \\\\ 2 &= 4\\end{align*}").1.body with
     | #[.center #[.para #[.formula true src
         (.cons (.atom _ (.grid .align rows) _ _ _) .nil)]]] =>
       (src.splitOn "&").length == 3 &&
         rows.rows.map (·.length) == [2, 2]
     | _ => false)
  let tabSrc := "\\begin{tabular}{ll}a & b \\\\ c & d\\end{tabular}"
  t "tabular elaborates to a rectangular table without errors"
    (errCodes tabSrc == [] &&
     match (elabStr tabSrc).1.body with
     | #[.table cols true true rows #[] #[]] =>
       cols == #[{ width := .natural, align := .left },
                 { width := .natural, align := .left }] &&
       rows.map (·.map Ir.plainText) == #[#["a", "b"], #["c", "d"]]
     | _ => false)
  -- The classic rules, not just booktabs: \hline is a light rule, \cline a
  -- full-width subrule, and \multicolumn keeps its cell text without the
  -- span count or alignment spec leaking in beside it.
  let classicTab := "\\begin{tabular}{ll}\\hline\n" ++
    "\\multicolumn{2}{X}{Head} \\\\ \\cline{1-2}\na & b \\\\ \\hline\\end{tabular}"
  let (ctDoc, ctDs) := elabStr classicTab
  t "classic tabular rules are typed rules, not unknown commands"
    (!ctDs.any (·.code == "W0301") &&
     match ctDoc.body with
     | #[.table _ _ _ _ rules _] =>
       rules == #[(0, .mid), (1, .cmid 1 2 false false), (2, .mid)]
     | _ => false)
  t "multicolumn keeps only its cell text"
    (match ctDoc.body with
     | #[.table cols _ _ rows _ _] =>
       let s := String.join (rows.toList.map fun r =>
         String.join (r.toList.map Ir.plainText))
       -- the span is lost, the short row padded to the grid, and W0337 says so
       (s.splitOn "Head").length == 2 && !s.toList.contains '2' &&
         !s.toList.contains 'X' &&
         rows.all (·.size == cols.size) && ctDs.any (·.code == "W0337")
     | _ => false)
  -- [standout]: the one frame option that says what the frame IS. It
  -- inverts, centres, and sets Large bold in both backends; the other
  -- options stay ignored, as notes.
  t "standout option marks the frame"
    (match (elabStr (deck169Body "\\begin{frame}[fragile,standout]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ true _ _ _] => true
     | _ => false)
  t "other frame options do not mark it"
    (match (elabStr (deck169Body "\\begin{frame}[plain]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ false _ _ _] => true
     | _ => false)
  let (sDoc, _) := elabStr (deck169Body ("\\begin{frame}{A}\na\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  let sGeom := Layout.Geom.ofPage sDoc.page
  let sOut := layoutOf oneFace sDoc sGeom
  t "standout page carries a full-page background fill"
    (match sOut.pages[1]? with
     | some p => p.fills.any fun f =>
         f.x == 0 && f.y == 0 && f.w == sGeom.pageW && f.h == sGeom.pageH &&
         f.color == Ir.Color.black
     | none => false)
  t "the plain page beside it carries none"
    (match sOut.pages[0]? with
     | some p => p.fills.isEmpty
     | none => false)
  t "standout text is inverted and Large"
    (match sOut.pages[1]? with
     | some p => p.lines.any fun l =>
         l.size == sGeom.fontSize * 1440 / 1000 &&
         l.segs.any fun s => match s with
           | .run _ c _ _ _ _ _ _ _ _ => c == Ir.Color.white
           | _ => false
     | none => false)
  t "standout content centres vertically"
    (match sOut.pages[1]?.bind (·.lines[0]?), sOut.pages[0]?.bind (·.lines[0]?) with
     | some sl, some pl => sl.y > pl.y + sGeom.pageH / 4
     | _, _ => false)
  let (sHtml, _) := HtmlDoc.emit {} sDoc
  t "html standout section carries the class"
    ((sHtml.splitOn "class=\"slide standout\"").length == 2)

def paletteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \palette and colour
  let palSrc := "\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED, short = #123 }\n" ++
    "\\begin{document}\\textcolor{primary}{x} {\\short y} z\\end{document}"
  let (palDoc, palDs) := elabStr palSrc
  t "palette source clean" palDs.isEmpty
  t "palette parsed" (palDoc.palette.find? "primary" ==
    some { r := 0x7C, g := 0x3A, b := 0xED })
  t "palette short hex expands" (palDoc.palette.find? "short" ==
    some { r := 0x11, g := 0x22, b := 0x33 })
  t "palette textcolor wraps" (palDoc.body.any fun b =>
    match b with
    | .para content => content.any fun x =>
      match x with
      | .colored c name body => c.r == 0x7C && name == some "primary" && body.size == 1
      | _ => false
    | _ => false)
  t "palette unknown name warns and keeps the content"
    (warnCodes ("\\documentclass{article}\\palette{a = #fff}" ++
      "\\begin{document}\\textcolor{nope}{x}\\end{document}") == ["W0304"] &&
     (elabStr ("\\documentclass{article}\\palette{a = #fff}" ++
      "\\begin{document}\\textcolor{nope}{x}\\end{document}")).1.body ==
        #[.para #[.text "x"]])
  -- A palette name binds a following group as its argument. It used to colour
  -- everything to the end of the group, so `\primary{Alex} Doe` painted Doe too.
  let palSrc (body : String) : Ir.Doc :=
    (Elab.run "t" ("\\documentclass{article}\\palette{mut = #666666}" ++
      "\\begin{document}" ++ body ++ "\\end{document}")).1
  t "palette name takes its group as an argument"
    ((palSrc "\\mut{in} out").body == #[.para #[
      .colored { r := 0x66, g := 0x66, b := 0x66 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette name with no group runs to the end of the group"
    ((palSrc "{\\mut in} out").body == #[.para #[
      .colored { r := 0x66, g := 0x66, b := 0x66 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette covered fraction declares" (
    (elabStr ("\\documentclass{article}\\palette{covered = 21\\%}" ++
      "\\begin{document}x\\end{document}")).1.palette.coveredFraction == some 21)
  t "palette covered fraction out of range" (errCodes
    ("\\documentclass{article}\\palette{covered = 100\\%}" ++
     "\\begin{document}x\\end{document}") == ["E0332"])
  t "palette covered still accepts a colour" (
    (elabStr ("\\documentclass{article}\\palette{covered = #808080}" ++
      "\\begin{document}x\\end{document}")).1.palette.find? "covered"
      == some { r := 0x80, g := 0x80, b := 0x80 })
  t "palette wrong type" (errCodes ("\\documentclass{article}\\palette{a = 3pt}" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "palette cannot shadow builtin" (errCodes
    ("\\documentclass{article}\\palette{textbf = #fff}" ++
     "\\begin{document}x\\end{document}") == ["E0303"])
  t "color value parsed" (Decl.parseValue "#7C3AED" == some (.color 0x7C 0x3A 0xED))
  t "color rejects bad hex" (Decl.parseValue "#12345" == none)
  t "color pdf components" ((Ir.Color.mk 255 0 128 none).pdfComponents == "1 0 0.502")
  t "color black components" (Ir.Color.black.pdfComponents == "0 0 0")

/-- xcolor's `!` mixing in the palette. Its own def: `main`'s elaboration
budget is spent (see lineChecks). -/
def contrastChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The channel table against the WCAG formula it tabulates, evaluated in
  -- Float: c' = c/255; c' ≤ 0.04045 → c'/12.92, else ((c'+0.055)/1.055)^2.4,
  -- scaled by 1e7 and rounded (w3.org/TR/WCAG22/#dfn-relative-luminance).
  let lin (c : Nat) : Nat :=
    let s := c.toFloat / 255.0
    let l := if s ≤ 0.04045 then s / 12.92
      else ((s + 0.055) / 1.055) ^ (2.4 : Float)
    (l * 10000000.0).round.toUInt32.toNat
  t "contrast table is the WCAG formula, all 256 channels"
    ((List.range 256).all fun c => Oklab.channelLinear.getD c 0 == lin c)
  -- The definition's own extremes: black on white is 21:1, self is 1:1.
  t "contrast black on white is 21:1"
    (Contrast.contrastMilli .black .white == 21000)
  t "contrast of a colour with itself is 1:1"
    (Contrast.contrastMilli Contrast.light.accent Contrast.light.accent == 1000)
  t "contrast does not care which side is the text"
    (Contrast.contrastMilli Contrast.light.muted Contrast.light.surface ==
     Contrast.contrastMilli Contrast.light.surface Contrast.light.muted)
  t "ratio string" (Contrast.ratioString 4627 == "4.62:1" &&
    Contrast.ratioString 21000 == "21.00:1" && Contrast.ratioString 1005 == "1.00:1")
  -- The contract check fires on a deliberately illegible bundle: the dark
  -- set with the light accent is the exact defect dark_contract guards
  -- against (2.64:1 focus ring, under SC 1.4.11's 3:1).
  t "contract rejects the illegible bundle"
    (!({ Contrast.dark with accent := Contrast.light.accent } :
      Contrast.ThemeColors).contractHolds)
  t "illegible bundle names its ratio" (Contrast.ratioString
    (Contrast.contrastMilli Contrast.light.accent Contrast.dark.surface) == "2.64:1")

  -- The covered contract fires on the finding it encodes: moloch at
  -- Material's 38% leaves alert (2.89:1) and example (2.75:1) under the
  -- 3:1 state change — the fraction is the bundle's, the bound is not.
  t "covered contract rejects moloch at 38%"
    (!Contrast.coveredContract
      { Theme.moloch.palette with coveredFraction := some 38 })
  -- Monotone quieting as a property over pseudo-random colours: covering
  -- never raises contrast against the page, and covering a cover quiets
  -- further (≤: equality is reachable at the page itself). The per-bundle
  -- strict form is the coverMonotone kernel checks.
  let quietingHolds := Id.run do
    let cov := (Ir.Design.ofDoc {}).cover
    let mut seed : Nat := 1
    for _ in [0:400] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let c : Ir.Color := { r := UInt8.ofNat (seed % 256)
                            g := UInt8.ofNat ((seed / 256) % 256)
                            b := UInt8.ofNat ((seed / 65536) % 256) }
      let c1 := cov.of c
      let c2 := cov.of c1
      if Contrast.contrastMilli c1 Ir.Color.white > Contrast.contrastMilli c Ir.Color.white
          || Contrast.contrastMilli c2 Ir.Color.white > Contrast.contrastMilli c1 Ir.Color.white then
        return false
    return true
  t "covering quiets monotonically over random colours" quietingHolds

  -- The stylesheet ships the proven token sets: the dark block overrides
  -- the accent (the light one reads 2.64:1 on the dark surface, under SC
  -- 1.4.11's 3:1), and both spellings come from the constants the
  -- contract theorems cover.
  let (page, _) := HtmlDoc.emit {} (elabStr "x").1
  let darkBlock := ((page.splitOn "prefers-color-scheme: dark")[1]?.getD "").splitOn "}"
    |>.headD ""
  t "dark block re-accents"
    ((darkBlock.splitOn s!"--accent: {HtmlDoc.cssColor Contrast.dark.accent}").length == 2)
  t "light accent comes from the proven constant"
    ((page.splitOn s!"--accent: {HtmlDoc.cssColor Contrast.light.accent}").length == 2)
  -- A page that declares a colour ships one scheme (`HtmlDoc.dualScheme`):
  -- only the engine's own token set has a proven dark variant, and the
  -- dark block once stood a declared ink equal to the light default on
  -- the dark surface at 1.00:1. A themed deck declares its colours through
  -- its bundle, so it too keeps the scheme its colours were judged in.
  -- Judged over the typed head tree the backend emits, never an IR dump.
  let (deckHead, _, _) := HtmlDoc.emitTree {} (elabStr
    ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
     "\\begin{frame}{T}x\\end{frame}\\end{document}")).1
  let headCss (h : Array Html.Node) : String := h.foldl (init := "") fun acc n => match n with
    | Html.Node.style s => acc ++ s
    | _ => acc
  let deckCss := headCss deckHead
  let themeMuted := match Theme.moloch.palette.find? "muted" with
    | some c => s!"--muted: {HtmlDoc.cssColor c};"
    | none => "no muted key"
  let darkMuted := s!"--muted: {HtmlDoc.cssColor Contrast.dark.muted};"
  t "a themed deck declares its muted once and ships no dark variant"
    ((deckCss.splitOn themeMuted).length == 2 && (deckCss.splitOn darkMuted).length == 1 &&
     hasStr deckCss "color-scheme: light;" && !hasStr deckCss "prefers-color-scheme: dark")
  let (inkHead, _, _) := HtmlDoc.emitTree {} (elabStr
    "\\documentclass{article}\\palette{ ink = #18181B }\\begin{document}x\\end{document}").1
  let inkCss := headCss inkHead
  t "a declared ink keeps its page in the one scheme it was judged in"
    (hasStr inkCss "color-scheme: light;" && !hasStr inkCss "prefers-color-scheme: dark" &&
     (HtmlDoc.schemeFailures true {} (elabStr
       "\\documentclass{article}\\palette{ ink = #18181B }\\begin{document}x\\end{document}").1).isEmpty)
  -- A picture's marks paint the colour they declare (black, undeclared),
  -- which the dark surface would swallow: its page keeps one scheme too.
  let (picHead, _, _) := HtmlDoc.emitTree {} (elabStr
    ("\\documentclass{article}\\pictures{ tool = none }\\begin{document}" ++
     "\\begin{tikzpicture}\\draw (0,0) -- (1,0);\\end{tikzpicture}\\end{document}")).1
  let picCss := headCss picHead
  t "a page with a picture ships one scheme"
    (hasStr picCss "color-scheme: light;" && !hasStr picCss "prefers-color-scheme: dark")
  -- A style's own colours and a clear image's ink paint on the ground too
  -- (review S-1): a red heading rule, a red list marker and a link's hover
  -- ink once shipped both schemes with the literal red in the sheet, and a
  -- black mark on a transparent raster stood on the dark surface at about
  -- 1:1. An opaque raster brings its own ground and keeps both.
  let schemeCss (imgs : Image.Store) (src : String) : String :=
    let (h, _, _) := HtmlDoc.emitTree { imgs } (elabStr src).1
    headCss h
  let oneScheme (css : String) : Bool :=
    hasStr css "color-scheme: light;" && !hasStr css "prefers-color-scheme: dark"
  let styled (decl body : String) : String :=
    s!"\\documentclass\{article}{decl}\\begin\{document}{body}\\end\{document}"
  t "a page whose heading rule is a declared colour ships one scheme"
    (oneScheme (schemeCss {} (styled "\\style{section}{ rule = red }" "\\section{A}b")))
  t "a page whose list marker is a declared colour ships one scheme"
    (oneScheme (schemeCss {} (styled "\\style{itemize}{ marker = {\\textcolor{red}{*}} }"
      "\\begin{itemize}\\item a\\end{itemize}")))
  t "a page whose link hover is a declared colour ships one scheme"
    (oneScheme (schemeCss {} (styled "\\style{nav}{ hover = red }" "x")))
  let raster (a : Image.Alpha) : Image.Store :=
    { entries := #[{ src := "mark.png", info := some { pxW := 4, pxH := 4, alpha := a } }] }
  let imgSrc := "\\documentclass{article}\\usepackage{graphicx}\\begin{document}x\n\n" ++
    "\\includegraphics{mark.png}\\end{document}"
  t "a page with a raster that lets the ground through ships one scheme"
    (oneScheme (schemeCss (raster (.soft ByteArray.empty 8)) imgSrc) &&
     oneScheme (schemeCss (raster (.colorKey #[0, 0])) imgSrc) &&
     !HtmlDoc.dualScheme (raster (.soft ByteArray.empty 8)) (elabStr imgSrc).1)
  t "a page with an opaque raster keeps both schemes"
    (hasStr (schemeCss (raster .opaque) imgSrc) "color-scheme: light dark;")
  -- The layering order still holds where a page ships both schemes: a
  -- declared token stands after the dark variant, so no variant beats a
  -- higher layer (the layering audit's clobber 3).
  let (tokHead, _, _) := HtmlDoc.emitTree {} (elabStr
    "\\documentclass{article}\\tokens{ topsep = 3pt }\\begin{document}x\\end{document}").1
  let tokCss := headCss tokHead
  t "a declared token comes after the dark variant in the cascade"
    (hasStr tokCss "color-scheme: light dark;" &&
     match (tokCss.splitOn "prefers-color-scheme: dark")[1]? with
     | some after => hasStr after "--topsep:"
     | none => false)
  t "an undeclared document emits no empty custom-property block"
    (let (plainHead, _, _) := HtmlDoc.emitTree {} (elabStr "x").1
     plainHead.all fun n => match n with
       | Html.Node.style s => !((s.splitOn ":root {\n\n}").length > 1)
       | _ => true)

  -- The pairing warning: a pale tint on the page fires W0315 with the
  -- ratio and threshold; declaring intent silences it; covered is exempt
  -- by role; large-scale text is held to 3:1 instead of 4.5:1; a declared
  -- fg is judged against a declared bg directly.
  let pale := "\\documentclass{article}\\palette{ washed = #DDDDDD }" ++
    "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
  -- #888888 on the shipped surface reaches 4.5:1 at #737373, ΔEOK 0.071:
  -- inside the ink bound, so it realizes. #DDDDDD needs a move past it.
  let quiet := "\\documentclass{article}\\palette{ washed = #888888 }" ++
    "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
  t "a failing role pairing inside the bound realizes, the note naming role and requirement"
    ((elabStr quiet).2.any fun d => d.code == "N0022" &&
      (d.message.splitOn "'washed'").length == 2 &&
      (d.message.splitOn "4.50:1").length == 2)
  t "a pale role past the bound warns, its help naming the nearest legible colour"
    (((elabStr pale).2.any fun d => d.code == "W0315" &&
      d.subject.any (·.startsWith "washed:") &&
      d.help.any fun h => hasStr h "#737373" && hasStr h "past the 0.080") &&
     (elabStr pale).2.all (·.code != "N0022"))
  t "declared intent silences the pairing judge whole"
    (let src := "\\documentclass{article}" ++
      "\\palette[decorative]{ washed = #DDDDDD }" ++
      "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
     !(warnCodes src).contains "W0315" && !(noteCodes src).contains "N0022")
  -- The decorative exemption is a property of the declaration, not of the
  -- key: a plain redeclaration replaces the excused value, so it restores
  -- the contrast check; only redeclaring with the opt-out keeps it.
  t "a plain redeclaration drops the decorative exemption"
    ((warnCodes ("\\documentclass{article}" ++
      "\\palette[decorative]{ washed = #DDDDDD }" ++
      "\\palette{ washed = #DDDDDD }" ++
      "\\begin{document}\\textcolor{washed}{faint}\\end{document}")).contains "W0315")
  t "a decorative redeclaration keeps the exemption"
    (!(warnCodes ("\\documentclass{article}" ++
      "\\palette{ washed = #DDDDDD }" ++
      "\\palette[decorative]{ washed = #DDDDDD }" ++
      "\\begin{document}\\textcolor{washed}{faint}\\end{document}")).contains "W0315")
  -- An anonymous use (a mixed colour) has no name, so the decorative
  -- escape matches it by value — and the help names no key the author did
  -- not write: it states the two steps, with the name left to the author.
  -- Yellow over white is a mix no weight can carry, so it keeps its warning.
  let anon := "\\documentclass{article}\\begin{document}\\textcolor{yellow!50}{quiet}" ++
    "\\end{document}"
  let anonDiag := ((elabStr anon).2.filter (·.code == "W0315"))[0]?
  t "an unreachable mix warns, naming the expression the author wrote"
    (anonDiag.any fun d => d.subject.any (·.startsWith "yellow!50:"))
  t "the anonymous help invents no role name"
    (anonDiag.any fun d => d.help.any fun h => hasStr h "<name>" && !hasStr h "quiet")
  -- A mix of two named colours that fails its ground is re-weighted inside
  -- the ink bound: the note is the mix's own, under the author's
  -- expression (fg!60!bg reaches its nearest legible weight at ΔEOK 0.054).
  let reMix := elabStr ("\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
    "\\begin{document}\\textcolor{fg!60!bg}{quiet}\\end{document}")
  t "a failing mix of two named colours is re-weighted, not warned"
    (reMix.2.all (·.code != "W0315") &&
      reMix.2.any fun d => d.code == "N0022" && d.subject.any (·.startsWith "fg!60!bg:"))
  let mixed := ((({ entries := #[("fg", { r := 0x23, g := 0x37, b := 0x3B }),
      ("bg", { r := 0xFA, g := 0xFA, b := 0xFA })] } : Ir.Palette).resolve "fg!50!bg").getD
    Ir.Color.black)
  t "a decorative entry at the mix's value keeps it low: no re-weighting, no warning"
    (let src := "\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
      "\\palette[decorative]{ dim = #" ++ Ir.Color.hexByte mixed.r ++
      Ir.Color.hexByte mixed.g ++ Ir.Color.hexByte mixed.b ++ " }" ++
      "\\begin{document}\\textcolor{fg!50!bg}{quiet}\\end{document}"
     !(warnCodes src).contains "W0315" && !(noteCodes src).contains "N0022")
  t "covered is exempt by role"
    (!(warnCodes ("\\documentclass{article}\\palette{ covered = #DDDDDD }" ++
      "\\begin{document}\\textcolor{covered}{later}\\end{document}")).contains "W0315")
  -- The resolved design's own pairs (W0345): the bundles are proved, so
  -- only a document's override can land an illegible frame-title bar,
  -- standout, or invisible covering — and it is judged only when the
  -- element ships. p5's archetype: moloch + a near-white frametitlebg
  -- shipped frame titles at 1.07:1 with zero diagnostics.
  let titled := "\\begin{frame}{T}x\\end{frame}"
  t "an overridden frame-title pair inside the bound realizes, the note naming the requirement"
    ((elabStr (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #555555, frametitlefg = #BBBBBB }"
      titled)).2.any
      fun d => d.code == "N0022" && (d.message.splitOn "'frametitlefg'").length == 2 &&
        (d.message.splitOn "4.50:1").length == 2)
  t "an overridden frame-title pair past the bound warns, naming the bound"
    ((elabStr (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }" titled)).2.any
      fun d => d.code == "W0345" && d.help.any (hasStr · "past the 0.080"))
  t "the untouched bundle's frame-title pair is silent"
    (!(warnCodes (dvDeck "\\theme{moloch}" titled)).contains "W0345")
  t "an illegible frame-title pair without a titled frame is silent"
    (!(warnCodes (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }"
      "\\begin{frame}x\\end{frame}")).contains "W0345")
  t "declared decorative intent silences the frame-title pair"
    (!(warnCodes (dvDeck ("\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }" ++
      "\\palette[decorative]{ frametitlefg = #FAFAF9 }") titled)).contains "W0345")
  t "an overridden standout pair realizes at the large-scale threshold"
    ((elabStr (dvDeck "\\palette{ standoutfg = #A0A0A0, standoutbg = #FAFAFA }"
      "\\begin{frame}[standout]S\\end{frame}")).2.any
      fun d => d.code == "N0022" && (d.message.splitOn "'standoutfg'").length == 2 &&
        (d.message.splitOn "3.00:1").length == 2)
  t "an illegible standout pair without a standout frame is silent"
    (!(warnCodes (dvDeck "\\palette{ standoutfg = #DDDDDD, standoutbg = #FAFAFA }"
      titled)).contains "W0345")
  t "a cover as loud as the ink warns when overlays ship"
    ((warnCodes (dvDeck "\\palette{ covered = #000000 }"
      "\\begin{frame}{T}\\uncover<2>{x}\\end{frame}")).contains "W0345")
  t "a cover as loud as the ink is silent with nothing to cover"
    (!(warnCodes (dvDeck "\\palette{ covered = #000000 }" titled)).contains "W0345")
  t "the default covering never warns"
    (!(warnCodes (dvDeck "" "\\begin{frame}{T}\\uncover<2>{x}\\end{frame}")).contains "W0345")
  t "unknown palette option warns and skips the block"
    (warnCodes ("\\documentclass{article}\\palette[dark]{ a = #101010 }" ++
      "\\begin{document}x\\end{document}") == ["W0316"])
  -- #767676 on the shipped surface is 4.34:1 -- under 4.5 but over 3: as
  -- body text it warns, as Huge (24.9pt) large-scale text it passes.
  let grey (body : String) := "\\documentclass{article}" ++
    "\\palette{ grey = #767676 }\\begin{document}" ++ body ++ "\\end{document}"
  t "borderline grey realizes as body text"
    ((noteCodes (grey "\\textcolor{grey}{x}")).contains "N0022")
  t "borderline grey passes as large-scale text"
    (!(warnCodes (grey "{\\Huge \\textcolor{grey}{x}}")).contains "W0315")
  -- The judge reads the layout's own scale (contrast_judges_what_layout_sets):
  -- at a 9 pt base a section sets at 12.96 pt — not WCAG large-scale — while
  -- the old absolute 14 pt bold was, so the judge passed text the page fails.
  -- #767676 reads at 4.34:1 on the shipped surface: over 3:1, under 4.5:1.
  -- At the 10 pt base the section sets at 14.4 pt bold, large-scale either
  -- way: the verdicts agree, which is why the drift went unseen.
  let sizedSection (size : String) := "\\documentclass{article}" ++
    "\\page{ fontsize = " ++ size ++ " }\\palette{ grey = #767676 }" ++
    "\\begin{document}\\section{\\textcolor{grey}{Head}}x\\end{document}"
  t "a 9pt-base section title is judged at the size the layout sets"
    ((noteCodes (sizedSection "9pt")).contains "N0022")
  t "a 10pt-base section title stays large-scale, judge and page agreeing"
    (!(warnCodes (sizedSection "10pt")).contains "W0315" &&
     !(noteCodes (sizedSection "10pt")).contains "N0022")
  t "a declared fg is judged against the declared bg, and realizes there"
    ((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #808080, bg = #F0F0F0 }" ++
      "\\begin{document}x\\end{document}")).2.any fun d =>
        d.code == "N0022" && (d.message.splitOn "'fg'").length == 2 &&
          (d.message.splitOn "#F0F0F0").length == 2)
  -- The effective pair (F3): the contract judges the pair the page ships,
  -- not only the pair the document spelled. A declared dark page with the
  -- ink left defaulted is black-on-dark in both backends — its own code
  -- (W0330), because its remedy is declaring the ink; declaring a legible
  -- ink silences it; a document that declares nothing ships the proven
  -- default pair and is not diagnosed.
  t "a declared dark page with a defaulted ink is diagnosed"
    ((elabStr ("\\documentclass{article}\\palette{ bg = #18181B }" ++
      "\\begin{document}x\\end{document}")).2.any fun d =>
        d.code == "W0330" && (d.message.splitOn "defaulted").length == 2)
  t "declaring a legible ink beside the dark page silences W0330"
    (!(warnCodes ("\\documentclass{article}" ++
      "\\palette{ fg = #FAFAF9, bg = #18181B }" ++
      "\\begin{document}x\\end{document}")).contains "W0330")
  t "an undeclared document is never diagnosed for its default pair"
    (((elabStr "\\documentclass{article}\\begin{document}x\\end{document}").2.filter
      fun d => d.code == "W0330" || d.code == "W0315").isEmpty)
  t "a defaulted ink on an undeclared page is fine: no pairing exists to fail"
    (!(warnCodes ("\\documentclass{article}\\palette{ washed = #DDDDDD }" ++
      "\\begin{document}x\\end{document}")).contains "W0330")
  t "a body use of the effective pair is not reported twice"
    ((((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #808080, bg = #F0F0F0 }" ++
      "\\begin{document}\\textcolor{fg}{x}\\end{document}")).2.filter
        fun d => d.code == "N0022" || d.code == "W0315" || d.code == "W0330").size) == 1)
  t "the built-in themes raise no pairing warning"
    (!(warnCodes ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
      "\\begin{frame}x\\end{frame}\\end{document}")).contains "W0315")

  -- The judge's verdict for a use is a function of its pairing key — the
  -- name it carried, the colour, the ground — and of the whole document's
  -- uses of that key; never of how many uses came before it. Pinned
  -- because the judge answers those questions by key now: it used to
  -- re-scan the uses seen so far and every use again, per use.
  let paleUse (spec : String) : String :=
    "\\documentclass{article}\\palette{ alpha = #C4C4C4 }\\begin{document}" ++
      spec ++ "\\end{document}"
  let pairing (spec : String) : Array String :=
    ((elabStr (paleUse spec)).2.filter fun d =>
      d.code == "W0315" && d.severity == .warning).map (·.message)
  let heldAt (spec needle : String) : Bool :=
    let ms := pairing spec
    ms.size == 1 && ((((ms[0]?).getD "").splitOn needle).length == 2)
  -- Large in every use, so SC 1.4.3's large-scale 3:1 — and said once.
  t "a pairing large in every use is held to the large-scale threshold"
    (heldAt "{\\Huge \\textcolor{alpha!60}{a}} {\\Huge \\textcolor{alpha!60}{b}}"
      "3.00:1")
  -- Small anywhere, so 4.5:1 — in either order, because the large-scale
  -- question ranges over every use of the key and not only the earlier
  -- ones. A per-use scan of what came before would call the second
  -- document large-scale.
  t "a pairing small in one use is held to the text threshold, large first"
    (heldAt "{\\Huge \\textcolor{alpha!60}{a}} \\textcolor{alpha!60}{b}" "4.50:1")
  t "and the same when the small use comes first"
    (heldAt "\\textcolor{alpha!60}{a} {\\Huge \\textcolor{alpha!60}{b}}" "4.50:1")
  -- Once per pairing, however many uses; and distinct pairings each get
  -- their own message, so the dedup is by key and not a global latch.
  t "a repeated pairing is reported once"
    ((pairing ("\\textcolor{alpha!60}{a} \\textcolor{alpha!60}{b} " ++
      "\\textcolor{alpha!60}{c} \\textcolor{alpha!60}{d}")).size == 1)
  -- The one line carries the count: each later coloured run of the pairing
  -- is a note under the same subject, and the tally puts the total on the
  -- first line and 0 on each note, so the lines add up to the runs. A run
  -- whose words split into several leaves is one site.
  let fourRuns := ((elabStr (paleUse ("\\textcolor{alpha!60}{a} " ++
      "\\textcolor{alpha!60}{b \\textbf{bb} b} \\textcolor{alpha!60}{c} " ++
      "\\textcolor{alpha!60}{d}"))).2.filter (·.code == "W0315"))
  t "a repeated pairing's line counts its four coloured runs"
    (fourRuns.size == 4 && (fourRuns.map (·.sites)).toList == [4, 0, 0, 0] &&
      (fourRuns.filter (·.severity == .warning)).size == 1 &&
      (match fourRuns[0]? with
       | some d => d.subject.isSome && fourRuns.all (·.subject == d.subject)
       | none => false))
  t "the pairing warning points at its first run's source"
    ((dvE (dvDoc "\\palette{ alpha = #C4C4C4 }\n" "\\textcolor{alpha!60}{a}")).any fun d =>
      d.code == "W0315" && d.severity == .warning && d.span == some ⟨"t", ⟨4, 1⟩⟩)
  t "distinct pairings are reported separately"
    ((pairing ("\\textcolor{alpha!60}{a} \\textcolor{alpha!50}{b} " ++
      "\\textcolor{alpha!40}{c} \\textcolor{alpha!60}{d}")).size == 3)
  -- One colour under two role names is two pairings; one role on two
  -- grounds is two pairings. Both are the key's doing, not the colour's.
  t "one colour under two names is two pairings"
    (((elabStr ("\\documentclass{article}" ++
      "\\palette{ alpha = #888888, beta = #888888 }\\begin{document}" ++
      "\\textcolor{alpha}{a} \\textcolor{beta}{b} \\textcolor{alpha}{c}" ++
      "\\end{document}")).2.filter (·.code == "N0022")).size == 2)
  t "one role on two grounds is two pairings"
    (((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #303030, bg = #FFFFFF, mid = #818181 }\\begin{document}" ++
      "\\textcolor{mid}{a}\n\n\\palette{ bg = #222222 }\n\n\\textcolor{mid}{b}" ++
      "\\end{document}")).2.filter fun d =>
        d.code == "N0022" && (d.message.splitOn "'mid'").length == 2).size == 2)
  -- The palette write is per epoch even when the note is already said: two
  -- epochs declaring one failing role are two palettes to rewrite and one
  -- message to read. Within a pairing key the only dimension left is the
  -- epoch's palette, which is what the write's dedup is keyed on.
  let twoEpochs := elabStr ("\\documentclass{article}" ++
    "\\palette{ washed = #888888 }\\begin{document}\\textcolor{washed}{a}" ++
    "\n\n\\palette{ washed = #888888 }\n\n\\textcolor{washed}{b}\\end{document}")
  let declared : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  t "two epochs declaring one failing role read one note"
    ((twoEpochs.2.filter fun d =>
      d.code == "N0022" || d.code == "W0315").size == 1)
  t "and both epochs' palettes are realized"
    (twoEpochs.1.palette.find? "washed" != some declared &&
     (twoEpochs.1.body.filterMap fun b => match b with
       | .setPalette p => p.find? "washed"
       | _ => none) == #[(twoEpochs.1.palette.find? "washed").getD declared])
  -- The judge must be linear in the coloured runs. The shape that made the
  -- quadratic version cost seconds is one pairing used everywhere at a
  -- large size: the dedup answers at once, but the large-scale question was
  -- answered by re-reading every use, per use. Measured on this judge:
  -- 20,000 runs cost 2,351 ms that way against 679 ms keyed, so the bound
  -- fails by a third if either question goes back to scanning. Synthesised
  -- as IR, so the clock sees the judge and not the parser.
  let dk : Ir.Color := { r := 0x10, g := 0x10, b := 0x10 }
  let manyUses : Ir.Doc :=
    { palette := { entries := #[("dk", dk)] }
      body := (List.range 20000).toArray.map fun i =>
        Ir.Block.para #[.styled (.size "Huge")
          #[.colored dk (some "dk") #[.text s!"w{i}"]]] }
  let t0 ← IO.monoMsNow
  let judged := Contrast.docDiags manyUses
  -- Consumed before the clock is read again: a pure `let` floats to its
  -- first use, so a timing with nothing between the two reads measures
  -- nothing.
  t "20,000 legible coloured runs are judged silently" judged.isEmpty
  let judgeMs := (← IO.monoMsNow) - t0
  t s!"the contrast judge is linear in the coloured runs ({judgeMs} ms for 20000)"
    (judgeMs < 1500)
  -- A failing pairing is solved once, not once per use: the lightness search
  -- is a pure function of the requirement, the ground and the colour, so the
  -- note one use earns is the note three thousand earn — and the search is
  -- paid once. Measured in the judge: 3,000 uses of one failing role cost
  -- 1,101 ms solved per use.
  let washedNotes (uses : Nat) : Array String :=
    ((elabStr ("\\documentclass{article}\\palette{ washed = #888888 }" ++
      "\\begin{document}" ++
      String.join ((List.range uses).map fun i =>
        "\\textcolor{washed}{w" ++ toString i ++ "} ") ++
      "\\end{document}")).2.filter (·.code == "N0022")).map (·.message)
  t "a repeated failing pairing is solved once, to the same value"
    ((washedNotes 4).size == 1 && washedNotes 4 == washedNotes 1)
  let manyPale : Ir.Doc :=
    { palette := { entries := #[("washed", declared)] }
      body := (List.range 3000).toArray.map fun i =>
        Ir.Block.para #[.colored declared (some "washed") #[.text s!"w{i}"]] }
  let t1 ← IO.monoMsNow
  let paleJudged := Contrast.docDiags manyPale
  t "3,000 uses of one failing pairing read one note" (paleJudged.size == 1)
  let paleMs := (← IO.monoMsNow) - t1
  t s!"a failing pairing is solved once, not per use ({paleMs} ms for 3000)"
    (paleMs < 400)

  -- The built-in theme bundles, held to the same contract. The theorems
  -- range over the bundles' own typed values; this pin closes the chain:
  -- what \theme installs is exactly the bundle the theorems cover, and
  -- the live check passes.
  for th in Theme.builtin do
    let (thDoc, _) := elabStr ("\\documentclass{slides}\\theme{" ++ th.name ++
      "}\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")
    t s!"\\theme installs the {th.name} bundle's own values"
      (thDoc.palette == th.palette)
  -- The check fires on the illegible bundle it exists for: moloch's own
  -- alert (#EB811B, 2.61:1 as body text) fails the contract.
  t "the contract rejects moloch's original alert"
    (let badEntries := (Theme.moloch.palette.entries.filter (·.1 != "alert")).push
        ("alert", ({ r := 0xEB, g := 0x81, b := 0x1B } : Ir.Color))
     !Contrast.paletteContract { entries := badEntries })
  -- Themed \alert is colour AND bold: colour alone would be the run's only
  -- signal (WCAG 2.2 SC 1.4.1); unthemed it stays the bold stand-in.
  let themedAlert := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\begin{frame}\\alert{hot}\\end{frame}\\end{document}")
  t "themed alert is colour and bold" (themedAlert.1.body.any fun b =>
    match b with
    | .frame _ _ _ _ body => body.any fun blk =>
      match blk with
      | .para content => content.any fun x =>
        match x with
        | .colored _ (some "alert") inner => inner.any fun y =>
          match y with
          | .styled .bold _ => true
          | _ => false
        | _ => false
      | _ => false
    | _ => false)

def mixChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pal : Ir.Palette := { entries := #[("base", { r := 0x40, g := 0x00, b := 0x80 })] }
  t "mix toward white" (pal.resolve "base!50" == some { r := 0xA0, g := 0x80, b := 0xC0 })
  t "mix with black" (pal.resolve "base!50!black" == some { r := 0x20, g := 0x00, b := 0x40 })
  t "mix chain folds left" (pal.resolve "base!50!black!30" ==
    some ((({ r := 0x40, g := 0x00, b := 0x80 } : Ir.Color).mix 50 Ir.Color.black).mix 30 Ir.Color.white))
  t "mix black!2 is near-white"
    (({} : Ir.Palette).resolve "black!2" == some { r := 250, g := 250, b := 250 })
  t "mix plain name still resolves" (pal.resolve "base" == some { r := 0x40, g := 0x00, b := 0x80 })
  t "mix pct over 100 rejected" (pal.resolve "base!101" == none)
  t "mix unknown atom rejected" (pal.resolve "nope!50" == none)
  -- xcolor's base colours are always available (xcolor manual §4.1,
  -- Table 1): a document mixing 'gray!30' resolves without declaring
  -- anything, and a declared entry of a base name still wins.
  t "xcolor base names resolve undeclared"
    (({} : Ir.Palette).resolve "gray" == some { r := 128, g := 128, b := 128 } &&
     ({} : Ir.Palette).resolve "gray!30" ==
       some (({ r := 128, g := 128, b := 128 } : Ir.Color).mix 30 Ir.Color.white) &&
     ({} : Ir.Palette).resolve "teal!50!blue" ==
       some (({ r := 0, g := 128, b := 128 } : Ir.Color).mix 50
         { r := 0, g := 0, b := 255 }))
  t "a declared entry wins over a base name"
    (({ entries := #[("gray", { r := 1, g := 2, b := 3 })] } : Ir.Palette).resolve "gray"
      == some { r := 1, g := 2, b := 3 })
  -- One resolving site: a declared entry wins over resolve's own black and
  -- white atoms, so a mix, \textcolor, and the role invocation cannot
  -- disagree about what a name means. Before the rule, a palette naming an
  -- entry 'black' painted the declared colour where find? resolved and
  -- pure black where resolve did — PDF ink and the HTML variable diverged.
  let shadow : Ir.Palette := { entries := #[("black", { r := 0x33, g := 0x33, b := 0x33 })] }
  t "a declared black wins over the built-in atom"
    (shadow.resolve "black" == shadow.find? "black")
  t "undeclared black and white stay available"
    (({} : Ir.Palette).resolve "black" == some Ir.Color.black &&
     ({} : Ir.Palette).resolve "white" == some Ir.Color.white)
  -- Declaration site: a mix value reads the entries declared so far.
  let doc (body : String) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ fg = #000000, bg = #ffffff, dim = bg!50!fg, faint = black!2 }\n" ++
    "\\begin{document}" ++ body ++ "\\end{document}")
  let (pDoc, pDs) := doc "x"
  t "palette mix entry clean" pDs.isEmpty
  t "palette mix entry value" (pDoc.palette.find? "dim" == some { r := 0x80, g := 0x80, b := 0x80 })
  t "palette black!2 entry" (pDoc.palette.find? "faint" == some { r := 250, g := 250, b := 250 })
  -- Use site: \textcolor takes a mix, `fg`/`bg` naming the current semantic
  -- foreground and background. A computed colour carries no var name. The
  -- mix is one that meets the page, so what is read is the resolution and
  -- not a contrast repair of it.
  let (uDoc, uDs) := doc "\\textcolor{fg!70!bg}{x}"
  t "textcolor mix resolves without W0304" (!uDs.any (·.code == "W0304"))
  t "textcolor mix colours the content" (uDoc.body == #[.para #[
    .colored { r := 0x4D, g := 0x4D, b := 0x4D } none #[.text "x"]]])
  t "textcolor mix with unknown base still warns"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\textcolor{quiet!50}{x}\\end{document}") == ["W0304"])
  -- Later declarations override earlier ones, theme defaults included.
  let (oDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ a = #111111 }\\palette{ a = #222222 }\n" ++
    "\\tokens{ s = 4pt }\\tokens{ s = 8pt }\n" ++
    "\\begin{document}x\\end{document}")
  t "palette redeclare overrides" (oDoc.palette.find? "a" == some { r := 0x22, g := 0x22, b := 0x22 })
  t "tokens redeclare overrides"
    ((oDoc.tokens.find? "s").map (·.width) == some (Dim.Length.ofSp (Dim.pt 8)))
  t "palette redeclare keeps one entry"
    ((oDoc.palette.entries.filter (·.1 == "a")).size == 1)

/-- `\theme` and the built-in bundles: a theme is data applied through the
same declarations a document writes, and everything after the site
overrides it. -/
def themeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (mDoc, mDs) := elabStr (deck169 "\\theme{moloch}" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "theme moloch source clean" mDs.isEmpty
  t "theme moloch declares the semantic keys"
    (["fg", "bg", "alert", "frametitlefg", "frametitlebg", "progressfg",
      "progressbg", "standoutfg", "standoutbg"].all
      fun k => (mDoc.palette.find? k).isSome)
  t "theme moloch resolves its own mixes"
    (mDoc.palette.find? "bg" == some { r := 0xFA, g := 0xFA, b := 0xFA } &&
     mDoc.palette.find? "frametitlebg" == some { r := 0x23, g := 0x37, b := 0x3B } &&
     mDoc.palette.find? "progressbg" == some { r := 0xCB, g := 0xC0, b := 0xB6 })
  t "theme moloch declares the progress token"
    (((mDoc.tokens.find? "progressheight").map (·.width)) ==
      some (Dim.Length.ofSp (Dim.pt 1)))
  t "theme moloch styles the frame title"
    ((mDoc.styles.find? "frametitle").bind (·.font) |>.isSome)
  -- The theme is a default: a later declaration replaces its entry, and
  -- only that entry.
  let (oDoc, _) := elabStr (deck169 "\\theme{moloch}\\palette{ alert = #C2185B }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a document overrides the theme"
    (oDoc.palette.find? "alert" == some { r := 0xC2, g := 0x18, b := 0x5B } &&
     oDoc.palette.find? "frametitlebg" == some { r := 0x23, g := 0x37, b := 0x3B })
  -- The second bundle is a table of values, not new code: plainer keys,
  -- no title bar because the key is simply absent.
  let (pDoc, pDs) := elabStr (deck169 "\\theme{plain}" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "theme plain source clean" pDs.isEmpty
  t "theme plain has no title bar key" ((pDoc.palette.find? "frametitlebg").isNone)
  t "theme plain still inverts standout"
    (pDoc.palette.find? "standoutbg" == pDoc.palette.find? "fg")
  -- Unknown names warn and leave the document unthemed.
  let (uDoc, uDs) := elabStr (deck169 "\\theme{vaporwave}" "x")
  t "unknown theme warns naming the bundles"
    (uDs.any fun d => d.code == "W0319" &&
      ((d.help.getD "").splitOn "moloch").length == 2 &&
      ((d.help.getD "").splitOn "plain").length == 2)
  t "unknown theme leaves the palette empty" (uDoc.palette.entries.isEmpty)
  -- \alert through the compat layer: a colour when themed, bold when not.
  let (aDoc, _) := elabStr (deck169 "\\usetheme{moloch}"
    "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")
  t "themed alert is the alert colour"
    (match aDoc.body with
     | #[.frame _ _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .colored c (some "alert") _ => c == { r := 0xA5, g := 0x5A, b := 0x13 }
          | _ => false
        | _ => false
     | _ => false)
  t "unthemed alert stays bold"
    (match (elabStr (deck169 "" "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")).1.body with
     | #[.frame _ _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .styled .bold _ => true
          | _ => false
        | _ => false
     | _ => false)

/-- The resolved `Design`: one construction site applies every default, so
these pin the values the record resolves to — the un-themed document, the
themed one, and the standout inversion a half-declared pair falls back to.
Totality itself is the record type, not a test. -/
def designChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let designOf (pre : String) : Ir.Design :=
    Ir.Design.ofDoc (elabStr ("\\documentclass{slides}" ++ pre ++
      "\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")).1
  -- Bareness is a choice by name now that a deck defaults to `daylight`:
  -- beamer's own `\usetheme{default}` spelling, `\theme{default}` here.
  let bare := designOf "\\theme{default}"
  t "bare design inks black on white, undeclared"
    (bare.fg == Ir.Color.black && bare.bg == Ir.Color.white &&
     !bare.fgDeclared && !bare.bgDeclared)
  t "bare design has no bar and no themed sections"
    (bare.frametitle.isNone && bare.progress.isNone)
  t "bare design standout inverts the page"
    (bare.standout == { fg := Ir.Color.white, bg := Ir.Color.black })
  t "bare design declares no covered constant and takes the 38% fraction"
    (bare.covered == none && bare.coveredFraction == Ir.coveredFractionDefault)
  t "bare design covers plain runs to 38% of black over white"
    (bare.cover.plain == { r := 0x86, g := 0x86, b := 0x86 })
  t "bare design mutes to the ink" (bare.muted == bare.fg)
  t "bare design separator defaults to the ink" (bare.separator == bare.fg)
  t "bare design progress bar is 1pt thick"
    (bare.progressheight == { width := Dim.Length.ofSp (Dim.pt 1) })
  let themed := designOf "\\theme{moloch}"
  t "themed design carries the bundle's bar pair"
    (themed.frametitle == some { fg := { r := 0xFA, g := 0xFA, b := 0xFA }, bg := { r := 0x23, g := 0x37, b := 0x3B } })
  t "themed design carries the progress pair"
    (themed.progress == some { fg := { r := 0xA5, g := 0x5A, b := 0x13 }, bg := { r := 0xCB, g := 0xC0, b := 0xB6 } })
  t "themed design reads the declared separator"
    (themed.separator == { r := 0xA5, g := 0x5A, b := 0x13 })
  t "themed design reads the declared muted step"
    (themed.muted == { r := 0x64, g := 0x72, b := 0x74 })
  -- A half-declared standout keeps the declared half and defaults the rest
  -- from the page's own colours — the fallback Layout applied per site.
  let half := designOf "\\theme{default}\\palette{ standoutbg = #102030 }"
  t "half-declared standout defaults its fg from the page"
    (half.standout == { fg := Ir.Color.white, bg := { r := 0x10, g := 0x20, b := 0x30 } })
  -- A deck that declares nothing takes the daylight bundle, under the
  -- document: warm paper, warm ink, no title bar, an azure progress pair.
  let dflt := designOf ""
  t "a themeless deck resolves to the daylight bundle"
    (dflt.fg == { r := 0x29, g := 0x25, b := 0x24 } &&
     dflt.bg == { r := 0xFD, g := 0xFC, b := 0xF9 } &&
     dflt.frametitle.isNone &&
     (dflt.progress.map (·.fg)) == some { r := 0x0B, g := 0x66, b := 0xC2 })
  t "the document's own declaration wins over the default bundle"
    ((designOf "\\palette{ bg = #FFFFFF }").bg == Ir.Color.white)
  t "a named theme still wins outright"
    ((designOf "\\theme{moloch}").bg == Ir.Color.black.mix 2 Ir.Color.white)

/-- **A title page may declare a ground of its own, and the declaration is
resolved once.** The palette role half of the dark title page: the
resolution's three cases, the contrast contract over it, and the contract
over every shipped bundle.

The ground is never invented (`Ir.Design.titleGround_exact` carries it as a
theorem); this pins the ink's default, which is inversion — the same rule
`standout` follows, because a declared ground is usually the page's opposite
and inverting is what lands light matter on a dark title page with no second
declaration. -/
def titleGroundChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- A title page ships only where the metadata is declared: without these
  -- `\maketitle` sets nothing (W0309) and there is no page to ground.
  let titleMeta := "\\title{A Placeholder Deck}\\author{P. Placeholder}"
  let designOf (pre : String) : Ir.Design :=
    Ir.Design.ofDoc (elabStr (deck169 (titleMeta ++ pre) "\\maketitle")).1
  let deckOf (pre body : String) : String := deck169 (titleMeta ++ pre) body
  -- Undeclared: no pair at all, so no page is painted a colour nobody named.
  t "an undeclared title page resolves to no ground"
    ((designOf "\\theme{default}").titlepage.isNone)
  -- Declared ground, declared ink: both the document's own.
  let both := designOf ("\\theme{default}\\palette{ titlepagebg = #101822, " ++
    "titlepagefg = #F4F6F8 }")
  t "a declared title-page pair resolves to exactly the declared colours"
    (both.titlepage == some { fg := { r := 0xF4, g := 0xF6, b := 0xF8 },
                              bg := { r := 0x10, g := 0x18, b := 0x22 } })
  -- Declared ground alone: the ink inverts from the page, as standout's does.
  let half := designOf "\\palette{ bg = #FFFFFF, titlepagebg = #101822 }"
  t "a half-declared title page inverts its ink from the page"
    (half.titlepage == some { fg := Ir.Color.white,
                              bg := { r := 0x10, g := 0x18, b := 0x22 } })
  -- A declared ink with no ground is not a ground: the page keeps the
  -- document's, so the pair stays absent and nothing is painted.
  t "a title-page ink with no ground declares no ground"
    ((designOf "\\palette{ titlepagefg = #F4F6F8 }").titlepage.isNone)
  -- The judge, on the author's own pair. The ground stands and the ink
  -- moves: a title page whose ink falls just short realizes it lighter
  -- (ΔEOK 0.040, inside the ink bound), naming the body requirement
  -- (4.5:1) because a title page carries body-size matter; a dark-on-dark
  -- ink the bound cannot reach keeps its declared value and warns.
  let dim := "\\palette{ titlepagebg = #101822, titlepagefg = #747474 }"
  t "an illegible title-page pair realizes its ink at the body threshold"
    ((elabStr (deckOf dim "\\maketitle")).2.any fun d =>
      d.code == "N0022" && (d.message.splitOn "'titlepagefg'").length == 2 &&
        (d.message.splitOn "4.50:1").length == 2 &&
        (d.message.splitOn "the title page").length == 2)
  t "the realized note names the declared ground, not an invented one"
    ((elabStr (deckOf dim "\\maketitle")).2.any fun d =>
      d.code == "N0022" && (d.message.splitOn "#101822").length == 2)
  t "a title-page ink past the bound keeps its declared value and warns"
    ((elabStr (deckOf "\\palette{ titlepagebg = #101822, titlepagefg = #2A3038 }"
      "\\maketitle")).2.any fun d =>
        d.code == "W0345" && hasStr d.message "#2A3038" && d.help.any (hasStr · "past the 0.080"))
  -- Only where the page ships: a deck with no \maketitle has no title page,
  -- so an illegible pair is a declaration nothing stands on.
  t "an illegible title-page pair without a title page is silent"
    (!(warnCodes (deckOf dim "\\begin{frame}{T}x\\end{frame}")).contains "W0345" &&
     (elabStr (deckOf dim "\\begin{frame}{T}x\\end{frame}")).2.all
       fun d => d.code != "N0022")
  -- Deliberate low contrast is declared, not defaulted.
  t "declared decorative intent silences the title-page pair"
    ((elabStr (deckOf (dim ++ "\\palette[decorative]{ titlepagefg = #2A3038 }")
      "\\maketitle")).2.all fun d => d.code != "W0345" && d.code != "N0022")
  -- An undeclared title page is judged on the page it really stands on, so
  -- it must stay silent under a bundle whose own pairs pass.
  t "an undeclared title page adds no pair to judge"
    ((elabStr (deckOf "\\theme{moloch}" "\\maketitle")).2.all
      fun d => d.code != "W0345")
  -- The contract over shipped bundles: adding a bundle is entering it.
  -- Vacuous while no bundle declares a title-page ground, and that is the
  -- point of quantifying over `Theme.builtin` rather than over a list of
  -- names — the first bundle to declare one is held without an edit here.
  t "every shipped bundle's title-page pair, where it declares one, is legible"
    (Theme.builtin.all fun th =>
      match (Ir.Design.ofPalette (Theme.apply th {}).palette).titlepage with
      | none => true
      | some p => Contrast.aaText ≤ Contrast.contrastMilli p.fg p.bg)

/-- Every role a built-in bundle declares is read: either a backend consumes
its resolved `Design` field (`Ir.Design.consumedRoles`) or documents use it
as a content colour by name. A declared-but-unread role with a known coming
consumer is a named warning in the build output, never silence; one nobody
expects fails the suite. The ledger is empty today — `separator` left it
when the title-page rule landed with the vertical-distribution slice
(`Elab.titleBlocks` reads it through the titlepage style). -/
def roleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let contentColours := ["alert", "example"]
  let pendingConsumer : List (String × String) := []
  for th in Theme.builtin do
    for (role, _) in th.palette.entries do
      if contentColours.contains role || Ir.Design.consumedRoles.contains role then
        pure ()
      else match pendingConsumer.lookup role with
        | some consumer =>
          IO.println (s!"warning: theme '{th.name}' declares '{role}' and no " ++
            s!"backend reads it yet ({consumer} is its coming consumer)")
        | none =>
          failures ref s!"theme '{th.name}' declares '{role}', which no code reads"
  check ref "pending roles are really unread"
    (pendingConsumer.all fun (r, _) => !Ir.Design.consumedRoles.contains r)

/-- The realization rule's executable census — the cross-ground half of
`Contrast.realized_builtin_contract`, whose kernel check covers the pairs
a bundle's design creates itself: for every shipped bundle, each content
colour that fails the frame-title bar or the standout inversion either
realizes there inside the ink bound or is a row of `beyondBound`, the
bundle pairs whose nearest legible ink lies past it — a registry that
fails in both directions, so a bundle change that brings a pair inside
the bound, or pushes one out, is a decision someone writes down (the
lightness search is not the identity there, and the kernel does not
evaluate it cheaply, so this half is an oracle). And the backend
agreement, `features_agree` shape: the run the PDF path ships and the
scoped custom property the HTML path declares both carry the one
solver's answer. -/
def realizedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Each needs a move past four JNDs (ΔEOK 0.13–0.44) to meet 4.5:1, so a
  -- document that sets the role on that ground keeps the declared ink and
  -- warns. Whether a bundle should ship another ink there is the user's.
  let beyondBound : List (String × String × String) :=
    [("moloch", "alert", "the frame-title bar"), ("moloch", "example", "the frame-title bar"),
     ("moloch", "alert", "the standout frame"), ("moloch", "example", "the standout frame"),
     ("plain", "alert", "the standout frame"), ("plain", "example", "the standout frame"),
     ("daylight", "alert", "the standout frame"), ("daylight", "example", "the standout frame"),
     ("gemini", "alert", "the frame-title bar"), ("gemini", "example", "the frame-title bar")]
  let mut seen : List (String × String × String) := []
  for th in Theme.builtin do
    let d := Ir.Design.ofDoc { palette := th.palette }
    let grounds := (match d.frametitle with
      | some p => [("the frame-title bar", p.bg)]
      | none => []) ++ [("the standout frame", d.standout.bg)]
    for (gname, ground) in grounds do
      for role in ["alert", "example"] do
        if let some c := th.palette.find? role then
          if Contrast.contrastMilli c ground < Contrast.aaText then
            let row := (th.name, role, gname)
            match Contrast.realize Contrast.aaText ground c with
            | some c' =>
              t s!"'{role}' of '{th.name}' realizes on {gname}, inside the bound"
                (Contrast.aaText ≤ Contrast.contrastMilli c' ground &&
                  Contrast.deltaEOkSq c c' ≤ Contrast.inkBoundSq && !beyondBound.contains row)
            | none =>
              seen := row :: seen
              t s!"'{role}' of '{th.name}' on {gname} is past the bound, and registered"
                (beyondBound.contains row)
  t "every registered bundle pair past the bound is one the census meets"
    (beyondBound.all seen.contains)
  -- One solver, two backends: an accent inside a moloch frame title, one
  -- the bar fails by a move inside the bound (ΔEOK 0.061).
  let deck := "\\documentclass{slides}\\theme{moloch}\\palette{ alert = #D8691F }" ++
    "\\begin{document}\\begin{frame}{An \\alert{urgent} word}x\\end{frame}\\end{document}"
  let (doc, ds) := elabStr deck
  let bar := (Theme.moloch.palette.find? "frametitlebg").getD Ir.Color.black
  let alert : Ir.Color := { r := 0xD8, g := 0x69, b := 0x1F }
  match Contrast.realize Contrast.aaText bar alert with
  | some c' =>
    t "the realized run ships the solver's value (the PDF half)"
      (doc.body.any fun b => match b with
        | .frame title _ _ _ _ => title.any fun x => match x with
          | .colored cRun (some "alert") _ => cRun == c'
          | _ => false
        | _ => false)
    t "the realized note names the ground"
      (ds.any fun d => d.code == "N0022" && hasStr d.message "the frame-title bar")
    t "the scoped custom property ships the solver's value (the HTML half)"
      (hasStr (HtmlDoc.themeCss doc)
        ("section.slide > header {\n  --alert: " ++ HtmlDoc.cssColor c' ++ ";"))
  | none => failures ref "moloch alert does not realize on its bar"
  -- The shipped census: the realized deck carries no failing role pair —
  -- every pairing warning either realized away or never fired.
  t "the realized deck ships no failing role pair"
    (ds.all fun d => d.code != "W0315" && d.code != "W0345")

/-- **One realized ink per role and ground, in both artifacts** — N0022's
claim, read off each artifact for a role declared so it fails on the page
and on three local grounds (the frame-title bar, a block-title bar, the
standout inversion): the PDF run's ink and the ground under it off
`Layout.Out`, the HTML token each scope re-points off the stylesheet the
typed tree ships, the note off its structured subject. A failing page pair
rewrites the palette entry, which is what hid the second solver pass the
HTML once ran over it on the bar: this fixture is the one the pair needs
to come apart, where a passing page pair makes the two passes coincide. -/
def realizedAgreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let src := "\\documentclass{slides}\\theme{moloch}" ++
    "\\palette{ alert = #D8691F, frametitlebg = #202633, frametitlefg = #FFFFFF, " ++
    "blocktitlebg = #2B2F36, blocktitlefg = #FFFFFF }\\begin{document}" ++
    "\\begin{frame}{\\textcolor{alert}{Barred Heading}}\\textcolor{alert}{Paged words.}" ++
    "\\begin{block}{\\textcolor{alert}{Block Heading}}Plain body.\\end{block}\\end{frame}" ++
    "\\begin{frame}[standout]\\textcolor{alert}{Inverted words.}\\end{frame}\\end{document}"
  let (doc, ds) := elabStr src
  let out := layoutOf oneFace doc
  let runOf (needle : String) : Option (Ir.Color × Option Ir.Color) :=
    out.pages.findSome? fun p => (p.lines.find? fun l => hasStr (lineText l) needle).bind fun l =>
      l.segs.findSome? fun s => match s with
        | .run _ c _ _ _ _ _ _ g _ => some (c, g)
        | _ => none
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList (treeCssList "" head.toList) body.toList
  let declared : Ir.Color := { r := 0xD8, g := 0x69, b := 0x1F }
  let hexOf (c : Ir.Color) : String :=
    s!"#{Ir.Color.hexByte c.r}{Ir.Color.hexByte c.g}{Ir.Color.hexByte c.b}"
  let design := Ir.Design.ofDoc doc
  let noted (key : String) (ink : Ir.Color) : Bool :=
    ds.any fun d => d.code == "N0022" && d.subject == some key && hasStr d.message (hexOf ink)
  for (needle, sel) in [("Barred", "section.slide > header"),
      ("Block Heading", "section.block-block > header"),
      ("Inverted", "section.slide.standout")] do
    match runOf needle with
    | some (ink, some ground) =>
      t s!"the PDF ships a legible realized alert on {sel}'s ground"
        (ink != declared && Contrast.aaText ≤ Contrast.contrastMilli ink ground)
      t s!"the HTML scope {sel} declares the ink the PDF paints"
        ((cssRulesOf css sel).any (hasStr · s!"--alert: {HtmlDoc.cssColor ink};"))
      t s!"the design records the ink the PDF paints on {sel}'s ground"
        (design.inks.any fun e => e.role == "alert" && e.declared == declared &&
          e.ground == ground && e.ink == ink)
      t s!"the N0022 note for {sel}'s ground names the ink both artifacts ship"
        (noted (Ir.inkKey "alert" declared ground) ink)
    | _ => failures ref s!"no alert run on a painted ground under {sel} in the PDF"
  let page := (doc.palette.find? "bg").getD Ir.Color.white
  -- The ground itself is one value: the paged stage paints the declared
  -- page the PDF paints and the judge reads, not the engine's own surface.
  t "the paged stage paints the declared page the realization was judged on"
    ((cssRulesOf css "section.slide, section.section-page").any
        (hasStr · "background: var(--bg, var(--surface))") &&
      (cssRulesOf css ":root").any (hasStr · s!"--bg: {HtmlDoc.cssColor page};"))
  match runOf "Paged" with
  | some (ink, _) =>
    t "the page's realized alert is the palette entry the HTML root declares"
      (ink != declared && doc.palette.find? "alert" == some ink &&
        (cssRulesOf css ":root").any (hasStr · s!"--alert: {HtmlDoc.cssColor ink};"))
    t "the N0022 note for the page names the ink both artifacts ship"
      (noted (Ir.inkKey "alert" declared page) ink)
  | none => failures ref "no alert run on the page in the PDF"
  -- Both directions of the census: every recorded ink is named by a note,
  -- and every note names a realization some artifact ships.
  let shipped := design.inks.map (fun e => Ir.inkKey e.role e.declared e.ground)
    |>.push (Ir.inkKey "alert" declared page)
  t "every realization the design records is named by an N0022 note"
    (shipped.all fun k => ds.any fun d => d.code == "N0022" && d.subject == some k)
  t "every N0022 note names a realization the artifacts ship"
    (ds.all fun d => d.code != "N0022" || d.subject.any shipped.contains)

/-- **A repair is barely different, and past the bound the declared colour
ships** — the ink bound read off both artifacts (review INK-1: a pale mix
shipped at near full strength, ΔEOK 0.263 from the declared colour, with no
warning). A mix whose nearest legible weight lies inside the bound ships
re-weighted in the PDF run and the HTML span alike, within the bound of
xcolor's value, and notes it; a mix whose nearest legible weight lies past
it ships xcolor's value in both, and warns under its own key, naming the
weight a document can write. -/
def inkBoundChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fg : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg : Ir.Color := { r := 0xFA, g := 0xFA, b := 0xFA }
  let shipOf (w : Nat) : Ir.Doc × Array Diag × Option Ir.Color × Array (String × String) :=
    let (doc, ds) := elabStr ("\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
      "\\begin{document}\\textcolor{fg!" ++ toString w ++ "!bg}{Mixed words here.}" ++
      "\\end{document}")
    let ink := (layoutOf oneFace doc).pages.findSome? fun p =>
      (p.lines.find? fun l => hasStr (lineText l) "Mixed").bind fun l =>
        l.segs.findSome? fun s => match s with
          | .run _ c .. => some c
          | _ => none
    let (_, body, _) := HtmlDoc.emitTree {} doc
    (doc, ds, ink, elemStylesList #[] body.toList)
  let htmlShips (styles : Array (String × String)) (c : Ir.Color) : Bool :=
    styles.any fun (txt, st) => hasStr txt "Mixed" && st == s!"color: {HtmlDoc.cssColor c}"
  -- Inside the bound: ΔEOK 0.054 to the nearest legible weight.
  let near := fg.mix 60 bg
  let (_, nDs, nInk, nStyles) := shipOf 60
  match nInk with
  | some ink =>
    t "a mix inside the bound ships re-weighted, legible on its page"
      (ink != near && Contrast.aaText ≤ Contrast.contrastMilli ink bg &&
        ((List.range 101).any fun q => 60 < q && fg.mix q bg == ink))
    t "the re-weighted mix lies within the ink bound of xcolor's value"
      (Contrast.deltaEOkSq near ink ≤ Contrast.inkBoundSq)
    t "the HTML run carries the re-weighted ink the PDF paints" (htmlShips nStyles ink)
    t "the re-weighting is noted under the mix's key, and nothing warns"
      (nDs.any (fun d => d.code == "N0022" && d.subject.any (·.startsWith "fg!60!bg:")) &&
        nDs.all (·.code != "W0315"))
  | none => failures ref "no mixed run in the PDF (inside the bound)"
  -- Past the bound: the nearest legible weight, 68, is ΔEOK 0.122 away.
  let far := fg.mix 50 bg
  let (_, fDs, fInk, fStyles) := shipOf 50
  t "a mix past the bound ships xcolor's value in the PDF" (fInk == some far)
  t "a mix past the bound ships xcolor's value in the HTML" (htmlShips fStyles far)
  t "a mix past the bound is never noted as realized"
    (fDs.all fun d => !(d.code == "N0022" && d.subject.any (·.startsWith "fg!50!bg:")))
  t "a mix past the bound warns under its key, naming the weight to write"
    (fDs.any fun d => d.code == "W0315" && d.subject.any (·.startsWith "fg!50!bg:") &&
      d.help.any (hasStr · "'fg!68!bg'"))
  -- beamer's `transparent` covering is the key's default opaqueness, 15%,
  -- set as xcolor's mixin of the ink over the page (beamerbaseoverlay.sty):
  -- the covered run ships within the bound of that colour, where the
  -- bundle's own 31% lay ΔEOK 0.114 from it.
  let (covDoc, covDs) := elabStr ("\\documentclass{beamer}\n\\usetheme{moloch}\n" ++
    "\\setbeamercovered{transparent}\n\\begin{document}\n\\begin{frame}\n" ++
    "Shown \\uncover<2>{Pending}\n\\end{frame}\n\\end{document}")
  let covInk := (layoutOf oneFace covDoc).pages[0]?.bind fun p =>
    p.lines.findSome? fun l => l.segs.findSome? fun s => match s with
      | .run _ c _ _ glyphs .. =>
        if hasStr (String.ofList (glyphs.toList.map (·.2.1))) "Pending" then some c else none
      | _ => none
  let covD := Ir.Design.ofDoc covDoc
  t "a transparent covering is beamer's fifteen per cent, and nothing warns"
    (covDoc.palette.coveredFraction == some 15 && covDs.all (·.severity == .note))
  match covInk with
  | some ink =>
    t "the covered run ships within the ink bound of beamer's covered colour"
      (Contrast.deltaEOkSq (covD.fg.mix 15 covD.bg) ink ≤ Contrast.inkBoundSq)
  | none => failures ref "no covered run on the step's first page"

/-- The executable half of `every_role_is_invocable` (Elab.lean): resolution
order lives in `elabInlines`, whose sanctioned recursion no theorem can
range over, so the fact that every shipped bundle's role really reaches the
palette arm — nothing earlier in the chain intercepts the name — is pinned
by elaborating an invocation of every key. An oracle, not a theorem:
reorder resolution or shadow a role with a new engine arm and this fails
naming the key. -/
def roleInvocationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for th in Theme.builtin do
    for (key, c) in th.palette.entries do
      let (doc, ds) := elabStr ("\\documentclass{article}\\theme{" ++ th.name ++
        s!"}\\begin\{document}\\{key}\{x}\\end\{document}")
      -- `\alert` is a compat idiom (colour and bold, W3C SC 1.4.1): the
      -- role must reach the words, whatever wrapper the idiom adds. A
      -- structural role invoked as body text (bg, standoutfg) fails the
      -- page pairing and realizes: the run then carries the realized
      -- value, and the note names the key — invocability is the name
      -- reaching the palette arm either way.
      t s!"role '{key}' of '{th.name}' is invocable"
        (match doc.body with
         | #[.para #[.colored c' (some n) inner]] =>
           n == key && Ir.plainText inner == "x" &&
             (c' == c || ds.any fun d => d.code == "N0022" &&
               (d.message.splitOn s!"'{key}'").length == 2)
         | _ => false)
  -- The two halves of palette-dependence meet on the real page: the use
  -- references the token (role_use_names_its_token) and :root declares it
  -- (paletteVar, the site role_use_is_palette_dependent ranges over).
  let (qDoc, qDs) := elabStr ("\\documentclass{article}\\palette{ quiet = #123456 }" ++
    "\\begin{document}\\quiet{x}\\end{document}")
  t "role page source clean" qDs.isEmpty
  let qPage := (HtmlDoc.emit {} qDoc).1
  t "a role use references its token on the page"
    ((qPage.splitOn "color: var(--quiet, #123456)").length == 2)
  t "the page declares the token the use references"
    ((qPage.splitOn "--quiet: #123456;").length == 2)

/-- W0342: a definition that shadows a palette role is named, with the cost
in the reason — the palette (a variant, a host page's override) and the
contrast judge no longer reach the words the definition styles. Judged
against the final palette, so declaration order cannot hide it; shadowing
any other command stays silent, as in LaTeX. -/
def roleShadowChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let diags (pre : String) : Array Diag :=
    (elabStr ("\\documentclass{article}\n" ++ pre ++
      "\\begin{document}\nx\n\\end{document}")).2
  let fires (ds : Array Diag) : Bool := ds.any fun d =>
    d.code == "W0342" && d.severity == .warning &&
      (d.message.splitOn "palette").length > 1
  t "a definition shadowing a theme role is named"
    (fires (diags "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n"))
  t "declaration order cannot hide the shadow"
    (fires (diags "\\define \\muted(word: content) {\\word}\n\\palette{ muted = #607060 }\n"))
  t "the newcommand spelling is the same shadow"
    (fires (diags "\\palette{ muted = #607060 }\n\\newcommand{\\muted}[1]{\\textbf{#1}}\n"))
  t "a zero-ary shadow is the same freeze"
    (fires (diags "\\palette{ muted = #607060 }\n\\define \\muted {gray words}\n"))
  t "a definition of an unshadowed name is silent"
    (!fires (diags "\\theme{plain}\n\\define \\entry(word: content) {\\word}\n"))
  t "the warning points at the define site"
    (((diags "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n").filterMap
      (·.span)).any (·.pos.line == 3))

/-- Repeat semantics across the settings surface: a second declaration of
the same setting composes predictably — keyed merge for maps, replace for
scalars, and a *conflicting* scalar repeat is said aloud (W0343) while a
same-value repeat stays silent. Each check pins one audited accident:
first-wins faces, chrome's across-block wholesale replace, the shared
running `[from]`, fancyhdr concatenation, and `sawPage` forfeiting the
Bringhurst margin on a rhythm-only block. -/
def composeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (pre : String) : String := dvDoc pre "x"
  let deck (pre body : String) : String := dvDeck (pre ++ "\n") body
  let w0343 (s : String) : Bool := (warnCodes s).contains "W0343"

  -- A redeclared variant face replaces: fontspec's later BoldFont= wins,
  -- and the store keeps one entry per variant (`faceFor_last_declared`).
  let (fDoc, _) := elabStr
    (wrap "\\fonts{ body.bold = \"First Face\" }\n\\fonts{ body.bold = \"Second Face\" }\n")
  t "a redeclared variant face resolves to the second"
    (fDoc.fonts.faceFor 0 700 false == some "Second Face")
  t "a redeclared variant face keeps one entry" (fDoc.fonts.faces.size == 1)

  -- \chrome slots merge across blocks exactly as within one block.
  let frame := "\\begin{frame}{A}\na\n\\end{frame}"
  let (cDoc, _) := elabStr (deck
    ("\\chrome{ footer = { left = \\sectiontitle } }\n" ++
     "\\chrome{ footer = { right = \\framenumber } }") frame)
  let (c1Doc, _) := elabStr (deck
    "\\chrome{ footer = { left = \\sectiontitle, right = \\framenumber } }" frame)
  t "chrome slots merge across blocks as within one"
    (cDoc.chrome == c1Doc.chrome &&
     cDoc.chrome.footerLeft == some .sectionTitle &&
     cDoc.chrome.footerRight == some .frameNumber)

  -- [from] is each running declaration's own, and a redeclare resets it.
  let (rDoc, rDs) := elabStr
    (wrap "\\runningfoot[from = 3]{An Invented Foot}\n\\runninghead{An Invented Head}\n")
  t "running foot's from does not move the head's"
    (rDs.isEmpty && rDoc.footFrom == 3 && rDoc.headFrom == 1)
  let (r2Doc, _) := elabStr
    (wrap "\\runninghead[from = 2]{An Invented Head}\n\\runninghead[from = 2]{An Invented Head}\n")
  let (r3Doc, _) := elabStr
    (wrap "\\runninghead[from = 2]{An Invented Head}\n\\runninghead{An Invented Head}\n")
  t "a redeclared running head resets its own from"
    (r2Doc.headFrom == 2 && r3Doc.headFrom == 1)
  -- The page claim, judged on the shipped pages: the foot's gate leaves
  -- the head standing on page 1.
  let (gDoc, gDs) := elabStr (deck
    "\\runninghead{An Invented Head}\\runningfoot[from = 2]{An Invented Foot}"
    "\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}")
  t "gated running deck source clean" gDs.isEmpty
  let gGeom := Layout.Geom.ofPage gDoc.page
  let gOut := layoutOf oneFace gDoc gGeom
  let gFont := oneFace.body
  let headY := gGeom.vmargin / 2 + gFont.ascent * gGeom.fontSize / (gFont.unitsPerEm : Int)
  let gDescent : Dim.Sp := (-gFont.descent) * gGeom.fontSize / (gFont.unitsPerEm : Int)
  let footY := Layout.furnFootY
    (Layout.furnitureBand gGeom.vmargin
      (gFont.ascent * gGeom.fontSize / (gFont.unitsPerEm : Int) + gDescent) none)
    gGeom.pageH gDescent
  t "the foot's own gate leaves the head on page 1"
    ((gOut.pages.map fun p => p.lines.any (·.y == headY)) == #[true, true] &&
     (gOut.pages.map fun p => p.lines.any (·.y == footY)) == #[false, true])

  -- Compat: a repeated fancyhdr field is redefined (fancyhdr manual:
  -- \lhead redefines), never concatenated.
  let (kDoc, _) := elabStr (wrap "\\lhead{First}\n\\lhead{Second}\n")
  let kText := Ir.plainText (kDoc.head.getD #[])
  t "a repeated fancyhdr field is redefined, not concatenated"
    ((kText.splitOn "Second").length == 2 && (kText.splitOn "First").length == 1)

  -- Only geometry keys claim the page: a rhythm-only \page block keeps the
  -- Bringhurst text-block margin; declared geometry keeps every value.
  let (pDoc, _) := elabStr (wrap "\\page{ parskip = 12pt }\n")
  let (bDoc, _) := elabStr (wrap "")
  t "a rhythm-only page block keeps the Bringhurst margin"
    (pDoc.page.hmargin == bDoc.page.hmargin &&
     pDoc.page.hmargin == (pDoc.page.width - Ir.articleTextBlock) / 2)
  let (hDoc, _) := elabStr (wrap "\\page{ hmargin = 1in }\n")
  t "declared geometry keeps every value it named"
    (hDoc.page.hmargin == Dim.inch 1)

  -- W0343 fires on a conflicting scalar repeat and only there.
  t "a conflicting page repeat warns"
    (w0343 (wrap "\\page{ margin = 20pt }\n\\page{ margin = 30pt }\n"))
  t "a same-value page repeat is silent"
    (!w0343 (wrap "\\page{ margin = 20pt }\n\\page{ margin = 20pt }\n"))
  t "a different-key refinement is silent"
    (!w0343 (wrap "\\page{ margin = 20pt }\n\\page{ hmargin = 30pt }\n"))
  t "a family alias conflict warns"
    (w0343 (wrap "\\fonts{ body = \"A Face\" }\n\\fonts{ rm = \"B Face\" }\n"))
  t "keyed-merge stores never warn"
    (!w0343 (wrap
      "\\tokens{ sep = 6pt }\n\\tokens{ sep = 12pt }\n\\palette{ night = #101010 }\n\\palette{ night = #202020 }\n"))
  let (sDoc, sDs) := elabStr (deck
    ("\\chrome{ footer = { left = \\sectiontitle } }\n" ++
     "\\chrome{ footer = { left = \\framenumber } }") frame)
  t "a conflicting chrome slot warns and the later wins"
    (sDoc.chrome.footerLeft == some .frameNumber &&
     sDs.any (·.code == "W0343"))
  let (s2Doc, s2Ds) := elabStr (deck
    ("\\chrome{ footer = { right = \\framenumber } }\n" ++
     "\\chrome{ footer = { right = \\slidenumber } }") frame)
  t "one datum under two spellings is silent"
    (s2Doc.chrome.footerRight == some .frameNumber &&
     !s2Ds.any (·.code == "W0343"))
  t "a second running head with different content warns"
    (w0343 (wrap "\\runninghead{a}\n\\runninghead{b}\n"))
  t "an identical running head repeat is silent"
    (!w0343 (wrap "\\runninghead{a}\n\\runninghead{a}\n"))
  t "output css conflict warns"
    (w0343 (wrap "\\output{ css = own }\n\\output{ css = bulma }\n"))
  t "output formats accumulate silently"
    (!w0343 (wrap "\\output{ formats = pdf }\n\\output{ formats = html }\n"))
  -- Overriding a theme's default is layering, not a conflict: the theme
  -- installs outside the document's store, so this stays silent.
  t "a document override after a theme never warns"
    (!w0343 (deck "\\theme{moloch}\n\\chrome{ footer = { left = \\sectiontitle } }" frame))


/-- One section per frame — the `frames_sections` census: the deck's HTML
carries exactly one `section` per frame, and the PDF's shipped page count
is that plus the per-step duplicates its handout pagination owes
(`Ir.maxStepBlocks`, the count both backends project). Every step is
visible — the handout state, the reveal's floor — carrying its `--step`
index for the class-gated uncover, a `\label` anchor lands once, and
every section keeps a unique id. -/
def deckStepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n" ++
     "\\begin{frame}{Steps}\n\\label{fr:steps}first\n\n\\pause\n" ++
     "\\alert{second}\n\n\\pause\nthird\n\\end{frame}\n" ++
     "\\begin{frame}{Plain}\nd\n\\end{frame}"))
  t "step deck elaborates clean" (ds.all fun d => d.severity == .note)
  let out := layoutOf oneFace doc
  let (html, _) := HtmlDoc.emit {} doc
  let count (s : String) : Nat := (html.splitOn s).length - 1
  let slideSections := count "<section class=\"slide\""
    + count "<section class=\"slide standout\""
    + count "<section class=\"slide title-page\""
  let frames := doc.body.foldl (fun n b => match b with
    | Ir.Block.frame _ _ _ _ _ => n + 1
    | _ => n) 0
  let stepDup := doc.body.foldl (fun n b => n + (Ir.frameSteps b - 1)) 0
  t "frames_sections: one section per frame, the PDF's page count less step duplicates"
    (slideSections == frames &&
     slideSections + stepDup + count "<section class=\"section-page\"" == out.pages.size)
  t "every step is visible and carries its index, nothing covered or hidden"
    (count "class=\"step\"" == 2 && count "class=\"step covered\"" == 0 &&
     count "--step: 2" == 1 && count "--step: 3" == 1 &&
     count " hidden=\"hidden\"" == 0)
  t "the label anchor has its single site"
    ((html.splitOn s!"id=\"{Ir.labelAnchor "fr:steps"}\"").length == 2)
  -- The frame structure: only a stepped frame rides a `.slide-track` —
  -- one sticky stage over its snap spacers, one spacer per overlay step,
  -- each spacer a deep-link anchor and a `[data-snap]` snap point; a
  -- stepless frame, the title page, and the section page are their own
  -- snap pages, the door attribute on the section itself, the anchor
  -- beside it.
  t "only the stepped frame rides a track; every page carries the snap door"
    (count "class=\"slide-track\"" == 1 && count "class=\"snap\"" == 3 &&
     count "--steps: 3" == 1 && count "--steps: 1" == 0 &&
     count "id=\"steps-1\"" == 1 && count "id=\"steps-2\"" == 1 &&
     count "id=\"steps-3\"" == 1 &&
     count "data-snap>" == 6)
  t "frame anchors keep unique ids, on the track or the section"
    (count "id=\"steps\"" == 1 && count "id=\"plain\" data-snap" == 1)
  t "no step control ships: the constant script is the navigation"
    (count "step-nav" == 0 && count "cluster" == 0 &&
     count "<script" == 1 &&
     count "document.querySelectorAll(\"[data-snap]\")" == 1)
  -- The spacer anchors claim through the same door as every id: a frame
  -- whose slug collides with a step anchor is renamed and named.
  let (cdoc, _) := elabStr (deck169 "\\title{T}\\author{A}"
    ("\\begin{frame}{Steps}\na\n\n\\pause\nb\n\\end{frame}\n" ++
     "\\begin{frame}{Steps 1}\nd\n\\end{frame}"))
  let (chtml, cds) := HtmlDoc.emit {} cdoc
  t "a frame slug colliding with a step anchor is renamed and warned"
    (cds.any (·.code == "W0327") &&
     (chtml.splitOn "id=\"steps-1\"").length - 1 == 1 &&
     (chtml.splitOn "id=\"steps-1-2\"").length - 1 == 1)
  -- The uncover CSS census: the track declares the frame's view
  -- timeline; each step's range is its own snap interval; step 1 is
  -- never covered; the floors stand (no view() support, print, reduced
  -- motion); the from-state is the design's own fraction and the
  -- explicit `to` endpoint is declared (the user's own rule).
  t "the uncover rides the frame's view timeline between snap points"
    (count "view-timeline: --frame x" == 1 &&
     -- the uncover and the range end's recover each ride it once
     count "animation-timeline: --frame;" == 2 &&
     count ".step:not([data-step=\"1\"])" == 3 &&
     count ("animation-range: contain calc((var(--step) - 2) / (var(--steps) - 1) * 100%) " ++
       "contain calc((var(--step) - 1) / (var(--steps) - 1) * 100%)") == 1)
  t "the stage is sticky over its spacers, snap on the door only"
    (count ".slide-track > section.slide { position: sticky; left: 0; margin-right: -100vw; }" == 1 &&
     count ".snap { flex: 0 0 100vw; height: 100dvh; }" == 1 &&
     count "[data-snap] { scroll-snap-align: start; scroll-snap-stop: always; }" == 1 &&
     count "ltx-push" == 0)
  t "the covered from-state has its explicit active endpoint"
    (count ("@keyframes ltx-uncover { to { opacity: 100%; transform: none } " ++
       "from { opacity: 31%; transform: translateX(var(--motiondistance, 1rem)); } }") == 1)
  t "without view() timelines the floor covers only under the script and uncovers by data-snapped"
    (count ("@supports not (animation-timeline: view()) {\n" ++
       "html[data-deck-script] .step:not([data-step=\"1\"]) { opacity: 31%; }") == 1 &&
     count (".slide-track[data-snapped=\"2\"] " ++
       ":is(.step[data-step=\"2\"]) { opacity: 100%; }") == 1 &&
     count (".slide-track[data-snapped=\"3\"] " ++
       ":is(.step[data-step=\"2\"], .step[data-step=\"3\"]) { opacity: 100%; }") == 1 &&
     count ".slide-track > section.slide { scroll-snap-align: start; scroll-snap-stop: always; }" == 2)
  t "reduced motion is the plain row at full colour, one page per frame"
    (count ".step { opacity: 100%; animation: none; }" == 1 &&
     count "html[data-deck-script] .step:not([data-step=\"1\"]) { opacity: 100%; }" == 1 &&
     count ".slide-track { width: 100vw; flex: 0 0 100vw; }" == 1)
  t "print shows every step uncovered on its stage's own sheet, spacers hidden"
    (count ".snap { display: none; }" == 3 &&
     count "section.slide, section.section-page { break-after: page;" == 1 &&
     count ".step { opacity: 100%; }" == 1 &&
     (((html.splitOn "@media print").drop 1).all fun s =>
      (s.splitOn "ltx-uncover").length == 1))

/-- The range's other end, in both artifacts. `\uncover<2-3>` in a
four-step frame is pending on steps 1 and 4 and crisp on 2 and 3
(`Ir.stepPending`), which the PDF handout has always dimmed by; until the
recover rules the HTML deck read the start alone, so a step stayed crisp
past its declared end on both the timeline path and the floor — a
divergence independent of alternation, and the prerequisite for it. The
PDF side is read off the shipped pages, the HTML side off the emitted
stylesheet's own data (`HtmlDoc.htmlStepPendingAt`, held to the predicate
by `html_step_pending_agree`), step by step. -/
def deckRangeEndChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169Frame
    "\\uncover<2-3>{Middle only.}\n\n\\uncover<4>{Fourth only.}")
  t "range-end deck elaborates clean" (ds.all fun d => d.severity == .note)
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let (html, _) := HtmlDoc.emit {} doc
  let has := hasStr html
  t "one handout page per step" (c.size == 4)
  t "the handout dims the range before its start and again past its end"
    (pageCovered c 0 "Middle only." && !pageCovered c 1 "Middle only." &&
     !pageCovered c 2 "Middle only." && pageCovered c 3 "Middle only.")
  t "the range ships on every step, dimmed or crisp"
    ((List.range 4).all fun i => pageOccurs c i "Middle only." == 1)
  -- The agreement, step by step: what the stylesheet says about this range
  -- at snap k and what the shipped page says about it at step k.
  t "the HTML rules cover the range exactly where the handout page does"
    ((List.range 4).all fun i =>
      HtmlDoc.htmlStepPendingAt 4 2 (some 3) (i + 1) == pageCovered c i "Middle only.")
  t "the declared end rides its own carrier in the markup"
    (has "<span class=\"step-end\" data-step-last=\"3\" style=\"--step-last: 3\">" &&
     has "<span class=\"step\" data-step=\"2\" data-step-last=\"3\" style=\"--step: 2\">")
  t "the end carrier dims again past the range, on both paths"
    (has "@keyframes ltx-recover { from { opacity: 100% } to { opacity: " &&
     has ".step-end { animation: ltx-recover linear both; animation-timeline: --frame;" &&
     has ("html[data-deck-script] .slide-track[data-snapped=\"4\"] " ++
       ":is(.step-end[data-step-last=\"1\"], .step-end[data-step-last=\"2\"], " ++
       ".step-end[data-step-last=\"3\"]) { opacity: "))
  t "the floor recover is script-gated, as the covered default is"
    (((html.splitOn "\n").filter fun l =>
        hasStr l ".step-end[data-step-last=\"" && !hasStr l "opacity: 100%").all fun l =>
      hasStr l "html[data-deck-script]")

/-- Overlay alternation in HTML: exactly one group per step, selected by the
same arithmetic the PDF page selects by. Before these rules the HTML arm
put both groups inside one visible wrapper and a page read
"applebanana" — green in every test, because no census could tell one copy
from two on the HTML side (`treeShownOccurs` is that census now). The
agreement row is `alt_backend_agree` read off the artifacts: the group the
shipped page inks and the group the stylesheet selects, step by step. -/
def deckAltChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169Frame
    "\\alt<2-3>{Middle words.}{Outer words.}\n\n\\uncover<4>{Fourth only.}")
  t "alternation deck elaborates clean" (ds.all fun d => d.severity == .note)
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let (html, _) := HtmlDoc.emit {} doc
  let has := hasStr html
  -- The PDF half, restated on this fixture: one alternative per page,
  -- never both, and never covered — an alternative is replacement, not
  -- dimming.
  t "the handout inks exactly one alternative per step page"
    (c.size == 4 &&
     (List.range 4).all fun i =>
       let first := Ir.altShowsFirst 2 (some 3) (i + 1)
       pageOccurs c i "Outer words." == (if first then 1 else 0) &&
         pageOccurs c i "Middle words." == (if first then 0 else 1))
  -- The census that was missing: the HTML page shows one group, and the
  -- tree declares both — each exactly once.
  t "the HTML page shows one alternative, and the tree declares both once each"
    (treeShownOccurs body "Outer words." == 1 &&
     treeShownOccurs body "Middle words." == 0 &&
     treeOccurs body "Outer words." == 1 &&
     treeOccurs body "Middle words." == 1)
  t "each group rides its own wrapper, with the range and its side"
    (has ("<span class=\"alt alt-pending\" data-step=\"2\" data-step-last=\"3\">" ++
       "Outer words.</span>") &&
     has ("<span class=\"alt alt-crisp\" data-step=\"2\" data-step-last=\"3\" " ++
       "hidden=\"hidden\">Middle words.</span>"))
  -- The agreement, step by step, over the artifacts: `altShownFirstAt`
  -- reads the emitted rules' data, `pageOccurs` the shipped page's ink.
  t "alt_backend_agree on the artifacts: the rules select the group the page inks"
    ((List.range 4).all fun i =>
      HtmlDoc.altShownFirstAt 4 2 (some 3) (i + 1) ==
        (pageOccurs c i "Outer words." == 1))
  t "one snap rule per side, start then end correction"
    (has (".slide-track[data-snapped=\"3\"] :is(.alt-crisp[data-step=\"1\"], " ++
       ".alt-crisp[data-step=\"2\"], .alt-crisp[data-step=\"3\"]) { display: contents; }") &&
     has (".slide-track[data-snapped=\"3\"] :is(.alt-pending[data-step=\"1\"], " ++
       ".alt-pending[data-step=\"2\"], .alt-pending[data-step=\"3\"]) { display: none; }") &&
     has ("html .slide-track[data-snapped=\"4\"] :is(.alt-crisp[data-step-last=\"1\"], " ++
       ".alt-crisp[data-step-last=\"2\"], .alt-crisp[data-step-last=\"3\"]) " ++
       "{ display: none; }") &&
     has ("html .slide-track[data-snapped=\"4\"] :is(.alt-pending[data-step-last=\"1\"], " ++
       ".alt-pending[data-step-last=\"2\"], .alt-pending[data-step-last=\"3\"]) " ++
       "{ display: contents; }"))
  -- Selection is display-level and stays out of the covering mechanism:
  -- no alternation rule sets an opacity, no step rule sets a display.
  t "the two mechanisms stay apart: alternation never dims, covering never hides"
    ((((html.splitOn "\n").filter fun l =>
         hasStr l ".alt-crisp" || hasStr l ".alt-pending").all fun l =>
       !hasStr l "opacity") &&
     (((html.splitOn "\n").filter fun l =>
         hasStr l ".step-end[" || hasStr l ".step[data-step").all fun l =>
       !hasStr l "display"))
  -- No script path grows: alternation is CSS over the attribute the one
  -- constant script already writes, and with scripting off the floor shows
  -- step 1's reading, which is the group stored first.
  t "alternation adds no script and degrades to step one's reading"
    (((html.splitOn "<script").length - 1) == 1 &&
     hasStr html HtmlDoc.deckScript &&
     has "hidden=\"hidden\">Middle words.</span>")

/-- Beamer's `{overprint}` is an alternation environment, and this is the
census that says so on the artifacts: three `\onslide` items, three step
pages, and each page carrying exactly ONE of the three readings. Keeping the
body — what an unknown environment does — put all three on every page, so
the row that names the defect is the absence of the other two, not the
presence of the one. n-way alternation is nested binary alternation, so the
nesting's own arithmetic is checked here too: the page that inks an item is
the page `Ir.altShowsFirst` names for that item's spec, and the HTML tree
declares every reading once while showing one. -/
def deckOverprintChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let readings := ["Alpha reading.", "Bravo reading.", "Charlie reading."]
  let (doc, ds) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<1> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\onslide<3> Charlie reading.\n\\end{overprint}")
  t "an overprint elaborates clean: no unknown environment, no kept body"
    (ds.all fun d => d.severity == .note)
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let (_, body, _) := HtmlDoc.emitTree {} doc
  -- Three items name three steps, so the frame ships three pages.
  t "three alternatives give the frame three step pages" (c.size == 3)
  -- The defect this closes, stated as the census: one reading per page and
  -- the other two absent. Against a kept body every row below fails.
  t "each step page inks exactly one of the three readings"
    ((List.range 3).all fun i =>
      (readings.map fun r => pageOccurs c i r) == (List.range 3).map fun j =>
        if i == j then 1 else 0)
  -- The nesting's arithmetic, not a second reading of it: item k rides
  -- `\alt<k>`, and the page that inks it is the page inside that spec —
  -- `Ir.stepPending`, the predicate both backends select by.
  t "the page that inks an item is the page inside that item's spec"
    ((List.range 3).all fun j =>
      (List.range 3).all fun i =>
        (pageOccurs c i (readings.getD j "") == 1) ==
          !Ir.stepPending (j + 1) (some (j + 1)) (i + 1))
  -- The top of the nesting, tied to the one predicate the PDF page and the
  -- HTML rules both read: the first item is the group stored first there.
  t "the outermost alternation inks its first item exactly when altShowsFirst says"
    ((List.range 3).all fun i =>
      (pageOccurs c i (readings.getD 0 "") == 1) == Ir.altShowsFirst 1 (some 1) (i + 1))
  -- The HTML artifact: every reading declared once, exactly one shown —
  -- the floor a page with no snap state shows, which is step one's.
  t "the HTML tree declares each reading once and shows exactly one"
    (readings.all (fun r => treeOccurs body r == 1) &&
     ((readings.map fun r => treeShownOccurs body r) == [1, 0, 0]))
  -- An overprint whose items carry *open* ranges. Chained head-first this
  -- shipped two byte-identical pages: item 1's `<1->` covers every step of
  -- the window, so it won on both and item 2 was reachable from none — an
  -- overlay increment lost with no diagnostic. The chain gives priority to
  -- the item written last, as beamer's overlay area does, so the increment
  -- lands on the step that asked for it.
  let openReadings := ["Delta reading.", "Echo reading."]
  let (odoc, ods) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<1-> Delta reading.\n\
\\onslide<2-> Echo reading.\n\\end{overprint}")
  t "an open-range overprint elaborates clean"
    (ods.all fun d => d.severity == .note)
  let oc := censusOf (coveredColorsOf odoc) (layoutOf oneFace odoc)
  t "two open-range alternatives give the frame two step pages" (oc.size == 2)
  t "an open-range overprint ships a different reading on each step page"
    ((List.range 2).all fun i =>
      (openReadings.map fun r => pageOccurs oc i r) == (List.range 2).map fun j =>
        if i == j then 1 else 0)
  -- The same loss, caught before the pages are built: an alternation group no
  -- step of its own frame can ink is decidable from the range and the window.
  t "no alternation group of an open-range overprint is unreachable"
    (Ir.altUnreachable odoc == 0)
  t "nor of a point-spec overprint" (Ir.altUnreachable doc == 0)
  -- And across the corpus: every shipped fixture reaches both groups of every
  -- alternation it declares. A step page that repeats its predecessor is
  -- either a document that meant it or an engine that lost something, and the
  -- engine cannot tell after the fact — so the decidable shape is the gate.
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (cdoc, _) := Elab.run s!"{n}.tex" src
    t s!"corpus {n}: every alternation reaches both of its groups"
      (Ir.altUnreachable cdoc == 0)

/-- An overprint the rewrite refuses to read as an alternation degrades to
ONE reading with its loss named, never to several stacked: an `\onslide`
with no step specification has no alternation in it (beamer reads a bare
`\onslide` as "on every overlay"), so the body stands as written and W0302
says the body is kept. -/
def deckOverprintDegradeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let bad := deck169Frame
    "\\begin{overprint}\n\\onslide Alpha reading.\n\\onslide<2> Bravo reading.\n\
\\end{overprint}"
  t "an \\onslide with no <spec> leaves the loss named, not guessed"
    ((warnCodes bad).contains "W0302")
  let empty := deck169Frame "\\begin{overprint}\nJust a reading.\n\\end{overprint}"
  t "an overprint with no alternative is named too"
    ((warnCodes empty).contains "W0302")
  let (doc, _) := elabStr empty
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  t "the degraded page ships the reading once, not twice"
    (c.size == 1 && pageOccurs c 0 "Just a reading." == 1)

/-- An overprint item whose overlay specification the step model cannot
number does not cost the items it can number. The invariant absent before:
*refusing an item whose spec names no step never removes an item whose spec
does — every numberable item still alternates, one inked per step page, and
the unnumberable item stands on the steps no other item claims.* The nesting
made the unnumberable item's "otherwise" group the whole rest of the
overprint, and the `\alt` fallback shows one alternative, so an incremental
spec on the first item swallowed every item after it: one page where three
were declared, two readings in neither artifact, with only the
once-per-document W0105 to account for the loss. Numberability is now one
definition below both passes (`Ir.overlayRange`), so the rewrite can place
such an item instead of the elaborator dropping the rest of the deck
with it. Census and HTML tree, never an IR dump. -/
def deckOverprintUnnumberableChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let readings := ["Alpha reading.", "Bravo reading.", "Charlie reading."]
  -- The first item's spec cannot be numbered; the other two name steps 2
  -- and 3, so the unclaimed step is 1 — where the unnumberable item stands.
  let src := deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\onslide<3> Charlie reading.\n\\end{overprint}"
  let (doc, ds) := elabStr src
  let warns := (ds.filter (·.severity != .note)).map (·.code)
  t "an unnumberable overprint item warns W0105 once, and nothing else"
    (warns == #["W0105"])
  t "the environment is read as alternation, not left standing"
    (!(warnCodes src).contains "W0302")
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  -- The defect: this was 1 before, the two numbered items gone with it.
  t "refusing one item leaves the numbered items their step pages"
    (c.size == 3)
  t "each step page inks exactly one of the three readings"
    ((List.range 3).all fun i =>
      (readings.map fun r => pageOccurs c i r) == (List.range 3).map fun j =>
        if i == j then 1 else 0)
  -- The numbered items ride their own specs, by the one predicate both
  -- backends select with: item k inks the page inside `<k>`.
  t "a numbered item inks the page inside its own spec"
    ([1, 2].all fun j =>
      (List.range 3).all fun i =>
        (pageOccurs c i (readings.getD j "") == 1) ==
          !Ir.stepPending (j + 1) (some (j + 1)) (i + 1))
  -- The unnumberable item is the nesting's last resort: it inks exactly the
  -- steps no numbered item's spec claims, read off the one predicate both
  -- backends select with — pending on every numbered spec at once.
  t "the unnumberable item inks the one step no numbered item claims"
    ((List.range 3).all fun i =>
      (pageOccurs c i (readings.getD 0 "") == 1) ==
        (Ir.stepPending 2 (some 2) (i + 1) && Ir.stepPending 3 (some 3) (i + 1)))
  let (_, body, _) := HtmlDoc.emitTree {} doc
  t "the HTML tree declares all three readings and shows exactly one"
    (readings.all (fun r => treeOccurs body r == 1) &&
     ((readings.map fun r => treeShownOccurs body r).foldl (· + ·) 0 == 1))
  -- An unnumberable item in the middle: steps 1 and 3 are claimed, so the
  -- item stands on 2 — no page shows two readings, none shows none.
  let mid := ["Delta reading.", "Echo reading.", "Foxtrot reading."]
  let (mDoc, mDs) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<1> Delta reading.\n\
\\onslide<+-> Echo reading.\n\\onslide<3> Foxtrot reading.\n\\end{overprint}")
  let mc := censusOf (coveredColorsOf mDoc) (layoutOf oneFace mDoc)
  t "an unnumberable item in the middle warns W0105 once"
    (((mDs.filter (·.severity != .note)).map (·.code)) == #["W0105"])
  t "the middle item stands on the step between the two numbered ones"
    (mc.size == 3 &&
     (List.range 3).all fun i =>
      (mid.map fun r => pageOccurs mc i r) == (List.range 3).map fun j =>
        if i == j then 1 else 0)
  -- Two unnumberable items: there is one last resort, so the first stands
  -- and the second is named, never stacked on the page the first holds.
  let (tDoc, tDs) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<.-> Bravo reading.\n\\onslide<2> Charlie reading.\n\\end{overprint}")
  let tc := censusOf (coveredColorsOf tDoc) (layoutOf oneFace tDoc)
  t "a second unnumberable item is named, not stacked"
    (((tDs.filter (·.severity != .note)).map (·.code)) == #["W0105"] &&
     tc.size == 2 &&
     pageOccurs tc 0 "Alpha reading." == 1 && pageOccurs tc 1 "Alpha reading." == 0 &&
     pageOccurs tc 0 "Charlie reading." == 0 && pageOccurs tc 1 "Charlie reading." == 1 &&
     pageOccurs tc 0 "Bravo reading." == 0 && pageOccurs tc 1 "Bravo reading." == 0)
  -- One item, unnumberable: one reading on one page, which is the whole of
  -- what an alternation of one can honestly be.
  let (oDoc, oDs) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Delta reading.\n\\end{overprint}")
  let oc := censusOf (coveredColorsOf oDoc) (layoutOf oneFace oDoc)
  t "a lone unnumberable item ships its reading once, on one page"
    (((oDs.filter (·.severity != .note)).map (·.code)) == #["W0105"] &&
     oc.size == 1 && pageOccurs oc 0 "Delta reading." == 1)

/-- A once-per-document diagnostic fires once for the DOCUMENT, however many
passes meet a cause. The invariant absent before: *the warn-once key set is a
property of the document, not of the pass that first met a cause* — `Compat`
and `Elab` each kept their own set, so a deck spelling both an unnumberable
`{overprint}` item (refused in the rewrite) and an unnumberable `\alt`
(warned in the elaborator) was told twice about one key, `spec:overlay`. The
set now travels out of the rewrite and into the state the elaborator starts
from, one notion of "already said". A diagnostic count, asserted on the
elaborated diagnostics — no claim here about what a page shows. -/
def deckOverlayWarnOnceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bothCauses := deck169Body
    "\\begin{frame}\n\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}\n\\end{frame}\n\
\\begin{frame}\n\\alt<+->{First alternative.}{Second alternative.}\n\\end{frame}"
  t "a deck with an unnumberable overprint item AND an unnumberable \\alt says W0105 once"
    ((warnCodes bothCauses).filter (· == "W0105") == ["W0105"])
  -- The order the passes meet the causes must not decide it either: the
  -- `\alt` frame first, the overprint second.
  let reversed := deck169Body
    "\\begin{frame}\n\\alt<+->{First alternative.}{Second alternative.}\n\\end{frame}\n\
\\begin{frame}\n\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}\n\\end{frame}"
  t "the pass order does not decide how often the document hears it"
    ((warnCodes reversed).filter (· == "W0105") == ["W0105"])
  -- Sharing the set never costs the warning itself: each cause alone still
  -- says it once, so the fix deduplicates rather than silences.
  let overprintOnly := deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}"
  t "the overprint cause alone still says it"
    ((warnCodes overprintOnly).filter (· == "W0105") == ["W0105"])
  let altOnly := deck169Frame "\\alt<+->{First alternative.}{Second alternative.}"
  t "the \\alt cause alone still says it"
    ((warnCodes altOnly).filter (· == "W0105") == ["W0105"])

/-- The deck's logo is frame furniture in HTML too — the executable half
of `logo_frames_agree`, over one deck: the frames whose HTML section
carries the `.slide-logo` strip are exactly the pages whose `Layout.Out`
carries the logo's furniture line, both read from the one declaration
sequence (`Ir.logoInForce`). The strip is decorative by role — its images
ship `alt=""` and the alt census counts them as decorative rather than
missing — the deck's W0007 is gone, the flow classes keep it, and a
declared alignment reaches both backends from the one resolving site
(`Ir.logoAlign`). -/
def deckLogoChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mk (pre : String) := deck169 pre
    ("\\begin{frame}{One}\na\n\\end{frame}\n" ++
     "\\logo{LOGO}\n" ++
     "\\begin{frame}{Two}\nb\n\\end{frame}\n" ++
     "\\logo{}\n" ++
     "\\begin{frame}{Three}\nc\n\\end{frame}")
  let (doc, ds) := elabStr (mk "\\theme{default}")
  t "logo deck elaborates clean" (ds.all fun d => d.severity == .note)
  let out := layoutOf oneFace doc
  t "logo census, PDF half: the furniture line stands on exactly the declared frame's page"
    (out.pages.size == 3 &&
     out.pages.map (fun p => p.lines.any (·.furniture)) == #[false, true, false])
  let (html, hds) := HtmlDoc.emit {} doc
  t "the deck ships the logo instead of naming a drop"
    (!hds.any (·.code == "W0007"))
  let secs := (html.splitOn "<section").toArray
  let logoIn (i : Nat) : Bool := hasStr (secs.getD i "") "class=\"slide-logo\""
  t "logo census, HTML half: the strip stands on frame Two's section alone"
    (secs.size == 4 && !logoIn 1 && logoIn 2 && !logoIn 3)
  t "the strip is decorative furniture at the default alignment, beamer's corner"
    (hasStr html "class=\"slide-logo\" role=\"presentation\" aria-hidden=\"true\"" &&
     hasStr html "justify-content: flex-end")
  let stageBlock :=
    (((html.splitOn "@media screen, print {").getD 1 "").splitOn "@media screen {").headD ""
  t "the stylesheet pins the strip to the stage's bottom band, on paper too"
    (hasStr stageBlock (".slide-logo { position: absolute; bottom: var(--safearea, 6vmin); " ++
       "left: var(--safearea, 6vmin); right: var(--safearea, 6vmin); display: flex; }"))
  -- Alignment is one declared value, projected by each backend.
  let (cdoc, cds) := elabStr (mk "\\theme{default}\\style{logo}{ align = center }")
  let cout := layoutOf oneFace cdoc
  let (chtml, _) := HtmlDoc.emit {} cdoc
  let geom := Layout.Geom.ofPage cdoc.page
  let logoLines := cout.pages.foldl
    (fun acc p => acc ++ p.lines.filter (·.furniture)) #[]
  t "a declared alignment reaches both backends from the one resolving site"
    (cds.all (fun d => d.severity == .note) &&
     hasStr chtml "justify-content: center" &&
     logoLines.size == 1 &&
     logoLines.all (fun l => l.x == (geom.pageW - l.setWidth) / 2))
  -- A logo image is decorative: `alt=""` ships and the no-alternative
  -- census stays silent for it, while a content image is still named.
  let (idoc, _) := elabStr (deck169 "\\theme{default}"
    ("\\logo{\\includegraphics[totalheight=.25\\textheight]{lg.png}}\n" ++
     "\\begin{frame}{T}\n\\includegraphics{pic.png}\n\\end{frame}"))
  let (ihtml, _) := HtmlDoc.emit {} idoc
  t "a logo image ships an empty alt and escapes the no-alt census; content images do not"
    (hasStr ihtml "src=\"lg.png\" alt " &&
     Ir.imagesSansAlt idoc == #["pic.png"])
  -- The flow classes keep W0007: an article's \logo stays paged-media
  -- furniture with no HTML analogue.
  let (adoc, _) := elabStr (dvDoc "\\logo{L}\n" "x")
  let (_, ads) := HtmlDoc.emit {} adoc
  t "an article's logo is still a named drop"
    (ads.any (·.code == "W0007"))
  -- Request exactly where placed, under every shipped bundle: a logo image
  -- is one entry of `imageRefs` (the driver's read, W0601 when the file is
  -- absent) and its box — the placeholder, here, with an empty store —
  -- stands on exactly the pages the declaration is in force for. No bundle
  -- may keep the request while dropping the placement (a warning for
  -- furniture no page shows) or place a logo the census never requested.
  for th in Theme.builtin do
    let (ldoc, _) := elabStr (deck169 ("\\theme{" ++ th.name ++ "}")
      ("\\begin{frame}{One}\na\n\\end{frame}\n" ++
       "\\logo{\\includegraphics[totalheight=.25\\textheight]{nope/absent.png}}\n" ++
       "\\begin{frame}{Two}\nb\n\\end{frame}\n" ++
       "\\logo{}\n" ++
       "\\begin{frame}{Three}\nc\n\\end{frame}"))
    let lout := layoutOf oneFace ldoc
    let boxOn (p : Layout.PageOut) : Bool := p.lines.any fun l =>
      l.furniture && l.segs.any fun sg => match sg with
        | .image _ _ _ => true
        | _ => false
    t s!"{th.name}: the logo image is requested once and its box ships on exactly the declared frame's page"
      (Ir.imageRefs ldoc == #["nope/absent.png"] &&
       lout.pages.size == 3 && lout.pages.map boxOn == #[false, true, false])

/-- The gemini poster bundle: the lineage resolves by name (`\usetheme{gemini}`
and the native `\theme{gemini}` both retire W0319), it installs nothing the
poster class leaves inert (no W0355), and the titled blocks read the
lineage's bars through the one resolving site (`Ir.titledLook`). Values are
pinned by the kernel contracts over `Theme.builtin`; these checks pin the
install reaching a poster document. Own function: `main`'s elaboration
budget. -/
def geminiChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let blue : Ir.Color := { r := 0x40, g := 0x73, b := 0x9E }
  let poster (pre body : String) := "\\documentclass{poster}" ++ pre ++
    "\\begin{document}\\begin{frame}" ++ body ++ "\\end{frame}\\end{document}"
  let blocks := "\\begin{block}{Panel}x\\end{block}\\begin{alertblock}{Hot}y\\end{alertblock}"
  let (doc, ds) := elabStr (poster "\\theme{gemini}" blocks)
  t "gemini resolves by name" (!ds.any (·.code == "W0319"))
  t "gemini installs nothing the poster class leaves inert"
    (!ds.any (·.code == "W0355"))
  t "gemini turns the frame-title band pair on"
    ((Ir.Design.ofDoc doc).frametitle ==
      some { fg := { r := 0xF5, g := 0xF6, b := 0xFA }, bg := blue })
  t "gemini's alert block title is a bar in the band's pair"
    ((Ir.titledLook doc.palette .alert).bar == some blue)
  t "gemini's plain block title is barless in the lineage's blue"
    (Ir.titledLook doc.palette .block ==
      { fg := blue, bar := none })
  t "usetheme gemini reaches the same bundle"
    (!(elabStr (poster "\\usetheme{gemini}" blocks)).2.any (·.code == "W0319"))


/-- A titled block's title is judged on the ground the pages ship it on.
The artifact half is read off `Layout.Out`: with no bar and no declared
page, the title run's declared ground is `none` and the page paints no
fill, so what the reader sees is the surface each backend puts under a
`none` ground — `light.surface` in HTML (`--surface`, `HtmlDoc.baseCss`),
white paper in the PDF. `#757575` sits between the two ratios (4.61:1 on
white, 4.41:1 on `#FAFAF9`), so grounding the judge on white passed a title
the HTML page fails — silently, since neither a theorem nor a census row
read that pair. Own function: `main`'s elaboration budget. -/
def titledGroundChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let grey : Ir.Color := { r := 0x75, g := 0x75, b := 0x75 }
  let surface := Contrast.light.surface
  -- The discriminator: this colour passes on white and fails on the
  -- surface the page ships, so the two groundings cannot both be right.
  t "the probe colour passes on white"
    (Contrast.aaText ≤ Contrast.contrastMilli grey Ir.Color.white)
  t "the probe colour fails on the shipped surface"
    (Contrast.contrastMilli grey surface < Contrast.aaText)
  let pal := ({} : Ir.Palette).declare "blocktitlefg" grey
  let doc : Ir.Doc :=
    { palette := pal
      body := #[.titled .block #[.text "Title"] #[.para #[.text "body text"]]] }
  let out := layoutOf oneFace doc
  -- The artifact half: the title ships on no fill of its own.
  let runs := out.pages.flatMap fun p => p.lines.flatMap fun l =>
    l.segs.filterMap fun seg => match seg with
      | .run _ color _ _ glyphs _ _ _ ground _ =>
        if glyphs.isEmpty then none else some (color, ground)
      | _ => none
  t "the unbarred title run ships on the undeclared page"
    (runs.any fun (color, ground) => color == grey && ground == none)
  t "the undeclared page paints no fill"
    (out.pages.all fun p => p.fills.isEmpty)
  -- The judge half: it speaks for the pair the reader sees. Grounded on
  -- white it said nothing at all.
  let ds := Contrast.docDiags doc
  t "the judge speaks for the shipped titled pair" (!ds.isEmpty)
  t "the judge names the ground the page ships"
    (ds.any fun d => (d.code == "N0022" || d.code == "W0345") &&
      hasStr d.message "#FAFAF9")
  -- And the value it writes clears the requirement on that same ground.
  let realized := (Contrast.realizeDoc doc).1
  t "the realized title clears the requirement on the shipped ground"
    (match realized.palette.find? "blocktitlefg" with
     | some c => Contrast.aaText ≤ Contrast.contrastMilli c surface
     | none => false)
  -- A declared bar is still the ground: the fix resolves the undeclared
  -- page, it does not override a bar.
  let barPal := (pal.declare "blocktitlebg" { r := 0xEE, g := 0xEE, b := 0xEE })
  let barDoc := { doc with palette := barPal }
  let barOut := layoutOf oneFace barDoc
  t "a declared bar is the title's ground"
    (barOut.pages.any fun p => p.lines.any fun l => l.segs.any fun seg =>
      match seg with
      | .run _ color _ _ glyphs _ _ _ ground _ =>
        !glyphs.isEmpty && color == grey &&
          ground == some { r := 0xEE, g := 0xEE, b := 0xEE }
      | _ => false)
  t "the judge grounds the barred title on the bar"
    ((Contrast.docDiags barDoc).all fun d => !hasStr d.message "#FAFAF9")
  -- A declared page is the ground where one is declared, white nowhere.
  let pagePal := (pal.declare "bg" { r := 0xFF, g := 0xFF, b := 0xFF })
  t "a declared white page is judged as declared"
    ((Contrast.docDiags { doc with palette := pagePal }).isEmpty)


/-- A legible document is returned untouched, and a failing one is not: the
executable half of `realizeDoc_id`, over a document that exercises every
family the plan is built from — the effective pair, a mid-document epoch,
role-named and anonymous uses, a titled block, a frame title, a standout
frame, pending overlay content, and page furniture. A write emitted for a
*passing* pair fails the first row here (the returned document differs from
the one handed in) while every single-pair statement stays true, which is
the gap this pins: `realize_id_of_passing` speaks for one pair, not for the
plan the dedup assembles. The second row keeps it honest — the same
machinery does move a document whose pair fails, so the first row is not
passing for want of a mechanism. Own function: `main`'s elaboration
budget. -/
def realizeDocIdChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ink : Ir.Color := { r := 0x11, g := 0x11, b := 0x11 }
  let bar : Ir.Color := { r := 0x20, g := 0x30, b := 0x40 }
  let onBar : Ir.Color := { r := 0xF8, g := 0xF8, b := 0xF8 }
  let legible : Ir.Palette :=
    ((((((({} : Ir.Palette).declare "fg" ink).declare "bg" Ir.Color.white).declare
      "quiet" { r := 0x44, g := 0x44, b := 0x44 }).declare
      "frametitlebg" bar).declare "frametitlefg" onBar).declare
      "blocktitlefg" ink).declare "muted" { r := 0x40, g := 0x40, b := 0x40 }
  let epoch : Ir.Palette :=
    ((({} : Ir.Palette).declare "fg" ink).declare "bg" Ir.Color.white).declare
      "quiet" { r := 0x44, g := 0x44, b := 0x44 }
  let body : Array Ir.Block :=
    #[.para #[.colored { r := 0x44, g := 0x44, b := 0x44 } (some "quiet") #[.text "role ink"]],
      .para #[.colored ink none #[.text "anonymous ink"]],
      .titled .block #[.text "Panel"] #[.para #[.text "panel body"]],
      .frame #[.text "Frame title"] false .center false #[.para #[.text "frame body"]],
      .frame #[.text "Standout"] true .center false #[.para #[.text "standout body"]],
      .para #[.step 2 none #[.text "pending"]],
      .setPalette epoch,
      .para #[.colored ink (some "fg") #[.text "after the epoch"]]]
  let doc : Ir.Doc :=
    { palette := legible, body := body
      head := some #[.text "running head"], foot := some #[.text "running foot"] }
  let (out, ds) := Contrast.realizeDoc doc
  t "a legible document is returned untouched" (out == doc)
  t "a legible document's every judged pair passes"
    ((Contrast.judgedPairs doc).all fun p =>
      Contrast.aaText ≤ Contrast.contrastMilli p.1 p.2)
  t "a legible document draws no realization note and no pairing warning"
    (ds.all fun d => d.code != "N0022" && d.code != "W0315" && d.code != "W0345")
  -- The same machinery moves a document that fails: one quiet role, judged
  -- on the page it sits on, realizes inside the ink bound and the returned
  -- document differs.
  let pale : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  let failing := { doc with
    palette := legible.declare "quiet" pale
    body := #[.para #[.colored pale (some "quiet") #[.text "pale role ink"]]] }
  let (fOut, fDs) := Contrast.realizeDoc failing
  t "a failing pair is judged, not passed over"
    (!(Contrast.judgedPairs failing).all fun p =>
      Contrast.aaText ≤ Contrast.contrastMilli p.1 p.2)
  t "a failing document does move" (!(fOut == failing))
  t "a failing document says so" (fDs.any fun d => d.code == "N0022" || d.code == "W0315")
