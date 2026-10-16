module

public import Tests.Artifact

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The document title is one level-0 heading, rendered as `<h1>`, the markdown `#` and the PDF's
title furniture. -/
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
  t "markdown never doubles the title"
    ((md.splitOn "# An Invented Title").length == 2)
  let second := "\\documentclass{article}\\title{Once}\\begin{document}" ++
    "\\maketitle\\maketitle x\\end{document}"
  t "a second maketitle warns W0322" (warnCodes second == ["W0322"])
  t "a second maketitle sets no second level-0 heading"
    (Ir.headingLevels (elabStr second).1.body == #[0])
  let late := "\\documentclass{article}\\begin{document}" ++
    "\\maketitle\\title{Late}\\maketitle x\\end{document}"
  t "an empty maketitle does not spend the title"
    (warnCodes late == ["W0309"] && Ir.headingLevels (elabStr late).1.body == #[0])
  let (deck, deckDs) := elabStr ("\\documentclass{slides}" ++
    "\\title{An Invented Deck}\\begin{document}\\maketitle" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "deck title source is clean" deckDs.isEmpty
  t "the deck's title frame carries the one h1"
    ((((HtmlDoc.emit {} deck).1.splitOn "<h1>An Invented Deck</h1>").length == 2) &&
      (((HtmlDoc.emit {} deck).1.splitOn "<h1").length == 2))

/-- Heading levels must not skip as the outline descends, and the title comes first, each warned
once. -/
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


/-- `columns` and `column` set side-by-side blocks at their declared widths, in the IR and both
backends. -/
def columnsChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := deck169Frame ("\\begin{columns}[T]\n\\begin{column}{0.6\\textwidth}\nleft\n\\end{column}\n" ++
    "\\begin{column}{0.4\\textwidth}\nright\n\\end{column}\n\\end{columns}")
  let (doc, ds) := elabStr src
  t "columns elaborate with widths, its option a note" (ds.all (·.severity == .note) &&
    match doc.body with
    | #[.frame #[] false .center false #[.columns #[(w1, #[.para #[.text "left"]]),
                                                     (w2, #[.para #[.text "right"]])]]] =>
      w1.resolve 1000 == some 600 && w2.resolve 1000 == some 400
    | _ => false)
  let out := layoutOf oneFace doc
  t "pdf columns share a baseline side by side"
    (match (out.pages[0]?.map (·.lines)).getD #[] with
     | #[l, r] => l.y == r.y && r.x > l.x && r.x ≥ l.x + l.setWidth
     | _ => false)
  let wide := deck169Frame ("\\begin{columns}\\begin{column}{0.5\\textwidth}\n" ++
    "several words that cannot possibly fit one half measure line\n" ++
    "\\end{column}\\begin{column}{0.5\\textwidth}\nright\n\\end{column}\\end{columns}")
  let (wDoc, _) := elabStr wide
  let wOut := layoutOf oneFace wDoc
  t "a column breaks lines at its own measure"
    (((wOut.pages[0]?.map (·.lines)).getD #[]).size > 2)
  let (html, _) := HtmlDoc.emit {} doc
  t "html columns are a grid with the declared widths"
    ((html.splitOn "grid-template-columns: 60% 40%").length == 2)
  let (aDoc, aDs) := elabStr (deck169Frame ("\\begin{columns}\\begin{column}{3cm}\na\n\\end{column}" ++
    "\\begin{column}{0.5\\textwidth}\nb\n\\end{column}\\end{columns}"))
  t "an absolute column width is honoured as a length"
    (!aDs.any (·.code == "W0314") &&
     (match aDoc.body with
      | #[.frame _ _ _ _ #[.columns cols]] =>
        (match cols[0]?.map (·.1), cols[1]?.map (·.1) with
         | some a, some b =>
           let measure := Dim.pt 1000
           match a.resolve measure, b.resolve measure with
           | some l, some half =>
             decide (l > Dim.pt 84) && decide (l < Dim.pt 87) &&
               half == measure / 2
           | _, _ => false
         | _, _ => false)
      | _ => false))
  -- `\hfill` between columns is beamer's own gutter (beamerbaseframecomponents.sty).
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
  -- A column is a minipage, so `\textwidth` inside it is the column's width (latex.ltx `\@iiiminipage`).
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
      | .image _ w _ _ => w == colW
      | _ => false)
  t "a column image never lands past the left margin"
    ((iOut.pages.flatMap (·.lines)).all fun l => l.x ≥ iGeom.hmargin)

/-- Overlay steps ride the IR: the PDF handout gets one page per step with pending content dimmed,
the HTML carries the steps as data. -/
def overlayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := deck169Frame ("\\begin{itemize}\n\\item<1-> first\n\\item<2-> second\n\\end{itemize}\n" ++
    "\\uncover<2>{tail}")
  let (doc, ds) := elabStr src
  t "overlay specs elaborate to steps, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center false #[
      .list false {} #[
        #[.step 1 none #[.para #[.text "first"]]],
        #[.step 2 none #[.para #[.text "second"]]]],
      .para #[.step 2 (some 2) #[.text "tail"]]]])
  let (pDoc, pDs) := elabStr (deck169Frame "one\n\n\\pause\ntwo\n\n\\pause\nthree")
  t "pause steps the rest, cumulatively" (pDs.isEmpty &&
    pDoc.body == #[.frame #[] false .center false #[
      .para #[.text "one"],
      .step 2 none #[.para #[.text "two"], .step 3 none #[.para #[.text "three"]]]]])
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
      | .run _ c _ _ _ _ _ _ _ _ _ => some c
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
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries step data"
    ((html.splitOn "data-step=\"2\"").length ≥ 2)
  t "an unnumberable spec still warns W0105"
    (warnCodes (deck169Frame "\\begin{itemize}\\item<+-> x\\end{itemize}") == ["W0105"])
  -- <2> covers on 1 and again from 3, as beamer's transparent covering does.
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
           | .run _ c _ _ _ _ _ _ _ _ _ => some c
           | _ => none
       colorOf p1 0 == some Ir.Color.black && colorOf p1 1 != some Ir.Color.black &&
       colorOf p3 0 != some Ir.Color.black && colorOf p3 1 == some Ir.Color.black &&
       colorOf p3 2 == some Ir.Color.black
     | _, _ => false))
  let runColors (p : Layout.PageOut) : Array Ir.Color :=
    p.lines.flatMap fun l => l.segs.filterMap fun s => match s with
      | .run _ c _ _ _ _ _ _ _ _ _ => some c
      | _ => none
  let colorSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ hot = #AA0000, covered = 38\\% }\n\\begin{document}\n\\begin{frame}\n" ++
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
        hotCover != (Ir.Design.ofDoc cDoc).inkCover &&
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

/-- Block content inside overlay commands steps as inline content does, and `\pause` steps the rest
of its scope. -/
def overlayBlockChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (lDoc, lDs) := elabStr (deck169Frame
    "\\onslide<2->{\n\\begin{itemize}\n\\item Stepped item.\n\\end{itemize}\n}")
  t "a list inside an overlay group steps whole, erroring nothing"
    (lDs.isEmpty && lDoc.body == #[.frame #[] false .center false #[
      .step 2 none #[.list false {} #[#[.para #[.text "Stepped item."]]]]]])
  let (mDoc, mDs) := elabStr (deck169Frame "\\uncover<2>{\nFirst covered.\n\nSecond covered.\n}")
  t "every paragraph of an overlay group stays inside its step"
    (mDs.isEmpty && mDoc.body == #[.frame #[] false .center false #[
      .step 2 (some 2) #[.para #[.text "First covered."],
        .para #[.text "Second covered."]]]])
  let (iDoc, _) := elabStr (deck169Frame "\\uncover<2->{same words}")
  let (bDoc, _) := elabStr (deck169Frame
    "\\uncover<2->{\n\\begin{itemize}\n\\item same words\n\\end{itemize}\n}")
  t "block and inline agree on steps"
    (match iDoc.body, bDoc.body with
     | #[.frame _ _ _ _ ib], #[.frame _ _ _ _ bb] =>
       Ir.maxStepBlocks ib == 2 && Ir.maxStepBlocks bb == 2
     | _, _ => false)
  let (oDoc, oDs) := elabStr (deck169Frame "shown\n\n\\onslide<2->\nlater one\n\nlater two")
  t "bare onslide between blocks steps the rest of the scope"
    (oDs.isEmpty && oDoc.body == #[.frame #[] false .center false #[
      .para #[.text "shown"],
      .step 2 none #[.para #[.text "later one"], .para #[.text "later two"]]]])
  let (pDoc, pDs) := elabStr (deck169Frame
    "\\begin{itemize}\n\\item first\n\\pause\n\\item second\n\\pause\n\\item third\n\\end{itemize}")
  t "pause between items steps the later items"
    (pDs.isEmpty && pDoc.body == #[.frame #[] false .center false #[
      .list false {} #[
        #[.para #[.text "first"]],
        #[.step 2 none #[.para #[.text "second"]]],
        #[.step 3 none #[.para #[.text "third"]]]]]])
  let pOut := layoutOf oneFace pDoc
  t "a paused list gets one handout page per step" (pOut.pages.size == 3)
  let (cDoc, cDs) := elabStr (deck169Frame
    ("\\begin{columns}\n\\begin{column}{0.5\\textwidth}\nabove\n\n\\pause\nbelow\n" ++
     "\\end{column}\n\\begin{column}{0.5\\textwidth}\nsteady\n\\end{column}\n\\end{columns}"))
  t "pause inside a column steps the rest of the frame, the next column included"
    (cDs.isEmpty && (match cDoc.body with
      | #[.frame _ _ _ _ #[.columns cols]] =>
        (match cols[0]? with
         | some (_, body) => body == #[.para #[.text "above"],
             .step 2 none #[.para #[.text "below"]]]
         | none => false) &&
        (match cols[1]? with
         | some (_, body) => body == #[.step 2 none #[.para #[.text "steady"]]]
         | none => false)
      | _ => false))
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
  let (uDoc, uDs) := elabStr (deck169Frame
    "\\onslide<+->{\n\\begin{itemize}\n\\item shown anyway\n\\end{itemize}\n}")
  t "an unnumberable spec on a block group warns and shows the content"
    ((uDs.map (·.code)) == #["W0105"] && uDoc.body == #[.frame #[] false .center false #[
      .list false {} #[#[.para #[.text "shown anyway"]]]]])

/-- `\alert<spec>{body}` is `\alt<spec>{\alert{body}}{body}`: the body inked once per step page,
never covered, alerted only on the spec's steps. -/
def alertOverlayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let themedDeck (body : String) : String :=
    deck169 "\\usetheme{moloch}" ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}")
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
    t s!"{mode} alert<2> raises no error and no warning but its pairing's report"
      (aDs.all (fun d => d.severity == .note || reportedContrast d) &&
        pDs.all fun d => d.severity == .note || reportedContrast d)
    match altOf aDoc, plainOf pDoc with
    | some (n, last, onFirst, onOther), some ps =>
      t s!"{mode} alert<2> alternates on step 2 alone" (n == 2 && last == some 2)
      t s!"{mode} alert<2> shows the body plain off its step"
        (onFirst == #[Ir.Inline.text "apple"] && Ir.altShowsFirst n last 1)
      t s!"{mode} alert<2> styles its other alternative as plain alert does"
        (onOther == #[ps])
      t s!"{mode} alert<2> conserves the body text once per alternative"
        (Ir.plainText onFirst == "apple" && Ir.plainText onOther == "apple")
    | _, _ => t s!"{mode} alert<2> elaborates to one alternation" false
  let (oDoc, _) := elabStr (themedDeck "One \\alert<2->{apple} here.")
  t "alert<2-> is alert from step 2 on"
    ((altOf oDoc).map (fun (n, last, _, _) => n == 2 && last.isNone) == some true)
  let (rDoc, _) := elabStr (themedDeck "One \\alert<2-3>{apple} here.")
  t "alert<2-3> is alert within its range"
    ((altOf rDoc).map (fun (n, last, _, _) => n == 2 && last == some 3) == some true)
  let (uDoc, uDs) := elabStr (themedDeck "One \\alert<+->{apple} here.")
  t "an unnumberable alert spec warns W0105 once"
    ((uDs.filter fun d => d.severity != .note && !reportedContrast d).map (·.code) == #["W0105"])
  let uc := censusOf (coveredColorsOf uDoc) (layoutOf oneFace uDoc)
  t "an unnumberable alert spec ships one page, its body inked once"
    (uc.size == 1 && pageOccurs uc 0 "apple" == 1 && pageAllRevealed uc 0)
  let (nDoc, nDs) := elabStr (deck169Frame "Pick the \\alt<+->{apple}{banana} now.")
  t "an unnumberable alt spec warns W0105 once"
    ((nDs.filter (·.severity != .note)).map (·.code) == #["W0105"])
  let nc := censusOf (coveredColorsOf nDoc) (layoutOf oneFace nDoc)
  t "an unnumberable alt ships its active alternative exactly once, alone"
    (nc.size == 1 && pageOccurs nc 0 "apple" == 1 &&
      pageOccurs nc 0 "banana" == 0 && pageAllRevealed nc 0)
  let (bDoc, bDs) := elabStr (deck169Frame
    "\\alt<+->{\\begin{itemize}\\item Apricot\\end{itemize}}\
{\\begin{itemize}\\item Blueberry\\end{itemize}}")
  t "an unnumberable block-level alt warns W0105 once"
    ((bDs.filter (·.severity != .note)).map (·.code) == #["W0105"])
  let bc := censusOf (coveredColorsOf bDoc) (layoutOf oneFace bDoc)
  t "an unnumberable block-level alt ships its active alternative alone"
    (bc.size == 1 && pageOccurs bc 0 "Apricot" == 1 &&
      pageOccurs bc 0 "Blueberry" == 0 && pageAllRevealed bc 0)
  let nHtml := (HtmlDoc.emit {} nDoc).1
  let (_, nBody, _) := HtmlDoc.emitTree {} nDoc
  t "html ships only the unnumberable alt's active alternative, once"
    (treeOccurs nBody "apple" == 1 && treeShownOccurs nBody "apple" == 1 &&
      treeOccurs nBody "banana" == 0 && !hasStr nHtml "banana")
  let (cDoc, _) := elabStr (deck169Frame "One \\alert<2>{apple} here.")
  let c := censusOf (coveredColorsOf cDoc) (layoutOf oneFace cDoc)
  t "alert<2> ships one handout page per step" (c.size == 2)
  t "the body is inked exactly once on every step page"
    (pageOccurs c 0 "apple" == 1 && pageOccurs c 1 "apple" == 1)
  t "no step page covers the body: alternation carries no transparency"
    (!pageCovered c 0 "apple" && !pageCovered c 1 "apple" &&
      pageAllRevealed c 0 && pageAllRevealed c 1)
  let (tDoc, _) := elabStr (themedDeck "One \\alert<2>{apple} here.")
  let alertInk := ((tDoc.palette.entries.find? (·.1 == (.role .alert))).map (·.2))
  let tc := censusOf ((alertInk.map (#[·])).getD #[]) (layoutOf oneFace tDoc)
  let tCov := censusOf (coveredColorsOf tDoc) (layoutOf oneFace tDoc)
  t "the theme declares an alert colour for the census to read" alertInk.isSome
  t "the alert ink is painted on the spec's step page alone"
    (tc.size == 2 && pageAllRevealed tc 0 && pageCovered tc 1 "apple")
  t "the off-step page still inks the body, plain and uncovered"
    (pageOccurs tc 0 "apple" == 1 && pageOccurs tc 1 "apple" == 1 &&
      pageAllRevealed tCov 0 && pageAllRevealed tCov 1)
  let (hDoc, _) := elabStr (themedDeck "One \\alert<2>{quince} here.")
  let html := (HtmlDoc.emit {} hDoc).1
  let (_, hBody, _) := HtmlDoc.emitTree {} hDoc
  t "html declares both alternatives once each and shows one"
    (treeOccurs hBody "quince" == 2 && treeShownOccurs hBody "quince" == 1)
  t "html shows the plain body off the step and hides the styled one"
    (hasStr html "<span class=\"alt alt-pending\" data-step=\"2\" data-step-last=\"2\">quince</span>" &&
      hasStr html ("<span class=\"alt alt-crisp\" data-step=\"2\" data-step-last=\"2\" " ++
        "hidden=\"hidden\"><span style=\"color: var(--ltx-alert, "))
  t "html names the alert colour once, on the styled alternative alone"
    ((html.splitOn "color: var(--ltx-alert, ").length == 2)
  t "html wraps the alert in no step: an alternation is never covered"
    (!hasStr html "class=\"step\"")
  t "alert<2>: the html rules select the group the handout page inks"
    ((List.range 2).all fun i =>
      HtmlDoc.altShownFirstAt 2 2 (some 2) (i + 1) == (pageOccurs tc i "apple" == 1 &&
        !pageCovered tc i "apple"))

/-- The caption-to-alt walk reaches every image of a float's body (`Ir.mapBlocks`). -/
def altWalkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{figure}\\begin{itemize}\\item \\includegraphics{one.png}" ++
    "\\end{itemize}\\caption{An invented caption}\\end{figure}\\end{document}")
  t "figure-list source raises no error" (ds.all (·.severity != .error))
  let html := (HtmlDoc.emit {} doc).1
  t "a listed image inherits the figure caption as its alt"
    ((html.splitOn "alt=\"An invented caption\"").length == 2)
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
      | .image store _ _ _ => some store
      | _ => none
  t "the shipped pages place no unexplained placeholder"
    (!imgSegs.isEmpty && imgSegs.all (·.isSome))

/-- Speaker notes are a side channel: absent from the PDF handout, an inert hidden aside in HTML. -/
def noteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  altWalkChecks ref oneFace
  let (doc, ds) := elabStr (deck169Frame "Visible words.\n\\note{Hidden speaker words.}")
  t "note elaborates to a side channel, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center false #[
      .para #[.text "Visible words."],
      .note #[.para #[.text "Hidden speaker words."]]]])
  let (bare, _) := elabStr (deck169Frame "Visible words.")
  let noted := layoutOf oneFace doc
  let plain := layoutOf oneFace bare
  t "pdf omits the note entirely"
    (noted.pages.map (·.lines.size) == plain.pages.map (·.lines.size))
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries the note as a hidden aside"
    ((html.splitOn "<aside class=\"note\" hidden=").length == 2 &&
     (html.splitOn "Hidden speaker words.").length == 2)
  let (inl, inlDs) := elabStr (deck169Frame "\\textbf{bold \\note{never shown} text}")
  t "a mid-sentence note leaves its paragraph whole and drains to the frame"
    (inlDs.isEmpty &&
     (match inl.body with
      | #[.frame _ _ _ _ #[.para content, .note nbody]] =>
        Ir.plainText content == "bold text" &&
        ((Ir.dumpBlocks "" nbody).splitOn "never shown").length == 2 -- ir tier: note content, not a page claim
      | _ => false))

  let (resv, resvDs) := elabStr (deck169Frame "Shown.\n\\note{name_with_underscores & more}")
  t "reserved characters in a note stay literal, erroring nothing"
    (resvDs.isEmpty &&
     (match resv.body with
      | #[.frame _ _ _ _ #[_, .note nbody]] =>
        ((Ir.dumpBlocks "" nbody).splitOn "name_with_underscores & more").length == 2 -- ir tier: note content, not a page claim
      | _ => false))
  let (nested, nestedDs) := elabStr (deck169Body
    "\\note{\\begin{frame}{T}\nspoken \\note{inner aside} words\n\\end{frame}}")
  t "a note inside a note's frame is refused, named"
    ((nestedDs.map (·.code)) == #["E0359"])
  t "the refusal keeps the frame's words, dropping only the inner note"
    (match nested.body with
     | #[.note #[.frame _ _ _ _ inner]] =>
       ((Ir.dumpBlocks "" inner).splitOn "spoken words").length == 2 && -- ir tier: note content, not a page claim
       ((Ir.dumpBlocks "" inner).splitOn "inner aside").length == 1 -- ir tier: note content, not a page claim
     | _ => false)

/-- Standout and overlay steps are orthogonal, furniture belongs to the frame, and notes stay silent
through themed paths. -/
def themeReconcileChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let themed (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++
    -- The fixture declares a corrected alert and the bundle's 31% fraction: #EB811B has no legible cover here.
    "\\palette{ fg = #23373B, bg = #FFFFFF, alert = #A55A13,\n" ++
    "  progressfg = alert, standoutfg = bg, standoutbg = fg, covered = 31\\% }\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"
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
      | .run _ c _ _ _ _ _ _ _ _ _ => c == bg
      | _ => false)
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
  let (nDoc, _) := elabStr (themed
    "\\begin{frame}[standout]\nShown.\n\\note{never printed}\n\\end{frame}")
  let (bDoc, _) := elabStr (themed "\\begin{frame}[standout]\nShown.\n\\end{frame}")
  let nOut := layoutOf oneFace nDoc
  let bOut := layoutOf oneFace bDoc
  t "a themed standout frame does not print its speaker note"
    (nOut.pages.map (·.lines.size) == bOut.pages.map (·.lines.size))

/-- `\chrome` and the bundles' chrome are page furniture as declared data, merged per slot. -/
def chromeDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let frame := "\\begin{frame}{T}\nx\n\\end{frame}"
  let (mDoc, mDs) := elabStr (deck169 "\\theme{moloch}" frame)
  t "chrome moloch source clean" mDs.isEmpty
  t "moloch declares only the footer's right slot, the left \\framefoot's"
    (mDoc.chrome.footerLeft == none &&
     mDoc.chrome.footerRight == some .frameNumber)
  t "moloch derives its muted step from its ink, by the generated rule"
    (mDoc.palette.find? "muted" == some { r := 0x61, g := 0x77, b := 0x7C })
  t "plain declares the same footer"
    ((elabStr (deck169 "\\theme{plain}" frame)).1.chrome.hasFooter)
  t "a deck opted out by name has no chrome"
    (!(elabStr (deck169 "\\theme{default}" frame)).1.chrome.hasFooter)
  t "a themeless deck takes the daylight footer"
    ((elabStr (deck169 "" frame)).1.chrome.hasFooter)
  let (oDoc, oDs) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { right = \\slidenumber } }" frame)
  t "a document's chrome refines the theme's footer per slot" (oDs.isEmpty &&
    oDoc.chrome.footerLeft == none &&
    oDoc.chrome.footerRight == some .frameNumber)
  -- Only a single-slot bundle can observe a wholesale chrome install.
  let leftOnly : Theme := { name := "left-only"
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
  let (bDoc, _) := elabStr (deck169
    "\\chrome{ footer = { right = \\framefraction } }\\theme{moloch}" frame)
  t "a theme after the document's chrome wins per slot"
    (bDoc.chrome.footerLeft == none &&
     bDoc.chrome.footerRight == some .frameNumber)
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
  t "substPage leaves a rendered frame slot alone"
    (Layout.substPage 7 9 (Ir.ChromeSlot.frameFraction.render #[] 2 5) ==
      Ir.ChromeSlot.frameFraction.render #[] 2 5)
  -- The muted rule is load-bearing: one step weaker (fg!60!bg) fails the bundle contract.
  let weaker : Ir.Palette := { entries :=
    (deckBundle Theme.moloch).entries.map fun (k, c) =>
      if k == (.role .muted : Ir.ColorRef) then (k, { r := 121, g := 133, b := 135 }) else (k, c) }
  t "the palette contract rejects a muted one step weaker"
    (!Contrast.paletteContract weaker)

/-- W0348 names a theme replacing a key the document declared with another value, and only that. -/
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
  let molochAlert := (Ir.Design.declared? (deckBundle Theme.moloch) .alert).getD .black
  t "a declaration the theme agrees with replaces nothing"
    (!(ds ("\\palette{ alert = #" ++ molochAlert.hex (hash := false) ++ " }\\theme{moloch}")).any (·.code == "W0348"))
  t "a second theme replacing the first theme's values is silent"
    (!(ds "\\theme{plain}\\theme{moloch}").any (·.code == "W0348"))
  t "a replaced chrome slot is named as its slot"
    ((ds "\\chrome{ footer = { right = \\framefraction } }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "footer.right").length == 2)
  t "a theme declares no covered share, so the document's stands, replaced by nothing"
    (!(ds "\\palette{ covered = 50\\% }\\theme{moloch}").any (fun d =>
      d.code == "W0348" && (d.message.splitOn "'covered'").length == 2) &&
     (elabStr ("\\documentclass{slides}\\palette{ covered = 50\\% }\\theme{moloch}" ++
       "\\begin{document}x\\end{document}")).1.palette.coveredFraction == some 50)
  t "a replaced element style is named"
    ((ds "\\style{frametitle}{ font = {\\small} }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "frametitle").length == 2)
  t "a replaced token is named"
    ((ds "\\tokens{ progressheight = 3pt }\\theme{moloch}").any fun d =>
      d.code == "W0348" && (d.message.splitOn "progressheight").length == 2)
  t "an untouched element style beside a replaced one stays silent"
    (((ds "\\style{section}{ before = 3pt }\\theme{moloch}").filter
      (·.code == "W0348")).isEmpty)

/-- A bundle's element style is installed whole (`Theme.styleMerge`). -/
def styleMergeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ink : Ir.Color := { r := 0x12, g := 0x34, b := 0x56 }
  let linked : Ir.ElementStyle := { color := some (ink, none) }
  let probe : Theme := { name := "probe", styles := { entries := #[("link", linked)] } }
  t "a bundle's link colour survives the install"
    (((Theme.apply probe {}).styles.find? "link").bind (·.color) == some (ink, none))
  t "every style field survives a merge onto an empty entry"
    (Theme.styleMerge linked {} == linked)
  let declared : Theme.Decls := { styles := ({} : Ir.Styles).declare "link" linked }
  t "an install the document already agrees with replaces nothing"
    (Theme.replaces probe declared).isEmpty
  t "an install that changes the link colour is a replacement"
    (Theme.replaces probe
      { styles := ({} : Ir.Styles).declare "link" { color := some (Ir.Color.black, none) } }
      == #[(.style, "link")])
  let exemptPalette := ({} : Ir.Palette).declareKey "alert" ink (decorative := true)
  let exempt : Theme := { name := "exempt", palette := exemptPalette }
  let doc : Theme.Decls := { palette := ({} : Ir.Palette).declareKey "alert" Ir.Color.black }
  t "a class default does not re-exempt a key the document redeclared"
    (!(Theme.applyUnder exempt doc).palette.decorative.contains (.role .alert))
  t "a class default keeps its exemption on a key the document left alone"
    ((Theme.applyUnder exempt {}).palette.decorative.contains (.role .alert))

/-- The footer band is reserved, never overlaid: layout reads the body bottom from
`Geom.bodyBottom`. -/
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
  -- Without the reservation this document's last body line reaches into the footer's band.
  let (bare, _) := elabStr ("\\page{ vmargin = 2pt }\n\\begin{document}\n" ++
    para ++ "\n\n" ++ para ++ "\n\\end{document}")
  let bareOut := layoutOf oneFace bare
  t "the fixture reaches the band it is about"
    (bareOut.pages.any fun p => p.lines.any fun l => l.y + descent > geom.bodyBottom)

/-- The chrome footer through layout and HTML: section and frame number on frame pages, none on
furniture pages, one number per stepped frame. -/
def chromeFooterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let body :=
    "\\begin{frame}{One}\na\n\\end{frame}\n" ++
    "\\section{Topic}\n" ++
    "\\begin{frame}{Two}\nb\n\n\\pause\nc\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nQ\n\\end{frame}"
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
  t "chrome deck: a stepped frame's pages share one footer"
    (out.pages[2]?.bind (·.foot) == out.pages[3]?.bind (·.foot))
  let font := oneFace.body
  let footSize := Ir.footlineSize Ir.sizeScale geom0.fontSize
  let descent : Dim.Sp := (-font.descent) * geom0.fontSize / (font.unitsPerEm : Int)
  -- A flat digit's band has no depth: its baseline stands moloch's closing `\vskip4pt` above the paper's edge.
  let footY := Layout.footBaseline geom0.pageH 0
  t "the foot line stands 4 pt above the paper's edge, at its step, muted"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.y == footY && l.size == footSize &&
         l.segs.any fun s => match s with
           | .run _ c _ _ _ _ _ _ _ _ _ => c == ({ r := 0x61, g := 0x77, b := 0x7C } : Ir.Color)
           | _ => false
     | none => false)
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
  let (rDoc, _) := elabStr (deck169 "\\theme{moloch}\\runningfoot{own foot}" body)
  let rOut := layoutOf oneFace rDoc
  t "runningfoot suppresses the chrome footer"
    (rOut.pages.all (·.foot.isNone))
  let runFootY := Layout.furnFootY
    (Layout.furnitureBand geom0.vmargin
      (font.ascent * geom0.fontSize / (font.unitsPerEm : Int) + descent) none)
    geom0.pageH descent
  t "runningfoot itself is laid on every page"
    (rOut.pages.all fun p => p.lines.any (·.y == runFootY))
  let (uDoc, _) := elabStr (deck169 "\\theme{default}" body)
  let uOut := layoutOf oneFace uDoc
  t "an unthemed deck carries no footer at all"
    (uOut.pages.all fun p => p.foot.isNone && p.lines.all (·.y != footY))
  let (html, _) := HtmlDoc.emit {} doc
  t "html frames close with the footer, standout none"
    ((html.splitOn ("class=\"slide-foot size-" ++ Ir.footline.step ++ "\"")).length == 3)
  t "html footer carries the stepped frame's one number"
    ((html.splitOn ">2</span>").length == 2)
  t "html footer styling comes from the tokens"
    ((html.splitOn "section.slide > footer.slide-foot { position: relative;").length == 2 &&
     (((html.splitOn "footer.slide-foot {")[1]?.getD "").splitOn
       "var(--ltx-foot-ink)").length == 2)
  let (rHtml, _) := HtmlDoc.emit {} rDoc
  t "html drops the chrome footer under runningfoot too"
    ((rHtml.splitOn "slide-foot").length == 1)
  let (cDoc, cDs) := elabStr (deck169 "\\chrome{ footer = { right = \\framenumber } }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  let cOut := layoutOf oneFace cDoc
  t "a bare chrome declaration draws its footer" (cDs.isEmpty &&
    ((cOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "1"))

/-- One frame numbering for every consumer (`Ir.frameNumbers`): the title page unnumbered, PDF and
HTML footers agreeing frame for frame. -/
def numberingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Read the typed footer slots, so a paint attribute cannot hide a visible footer from this comparison.
  let compact (s : String) : String :=
    String.ofList (s.toList.filter (!·.isWhitespace))
  let htmlFoots (doc : Ir.Doc) : List String :=
    let (_, body, _) := HtmlDoc.emitTree {} doc
    (dedupConsecutive (slideFootsList #[] body.toList)).toList.map
      fun (left, right) => compact (left ++ right)
  let pdfFoots (out : Layout.Out) : List String :=
    (out.pages.foldl (fun (acc : List String) p =>
      match p.foot with
      | some f =>
        let s := compact (Ir.plainText (Ir.bandInlines f))
        if acc.head? == some s then acc else s :: acc
      | none => acc) []).reverse
  let (doc, ds) := elabStr (deck169
    "\\theme{moloch}\\chrome{ footer = { left = \\sectiontitle } }\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n\\begin{frame}{One}\na\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "numbering deck source clean" ds.isEmpty
  t "the numbering skips the title and the standout frame"
    (doc.frameCount == 1 && doc.frameNumbers.toList.filterMap id == [1])
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  t "numbering deck four pages" (out.pages.size == 4)
  t "only the content frame carries a footer, not title or standout"
    (out.pages.map (·.foot.isSome) == #[false, false, true, false])
  t "the content frame is frame 1, not 2"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "S1")
  t "the progress bar shows 0 of 1 before any content frame"
    (match out.pages[1]? with
     | some p => (p.fills.any fun f => f.color == (molochProgress ()).2) &&
         !(p.fills.any fun f => f.color == (molochProgress ()).1)
     | none => false)
  let (html, _) := HtmlDoc.emit {} doc
  t "html gives the title and standout frames no footer"
    ((html.splitOn ("class=\"slide-foot size-" ++ Ir.footline.step ++ "\"")).length == 2)
  t "html numbers the content frame 1"
    ((html.splitOn ">1</span>").length == 2)
  t "html progress is 0% before any content frame"
    ((html.splitOn "width: 0%").length == 2)
  t "pdf and html footers are the same text" (pdfFoots out == htmlFoots doc)
  let (dDoc, dDs) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n" ++
     "\\begin{frame}{A}\na\n\n\\pause\nb\n\\end{frame}\n" ++
     "\\section{S}\n\\framefoot{note}\n" ++
     "\\begin{frame}{B}\nc\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "two-sequences deck source clean" dDs.isEmpty
  t "two content frames count 1 and 2, the standout none"
    (dDoc.frameCount == 2 && dDoc.frameNumbers.toList.filterMap id == [1, 2])
  let dOut := layoutOf oneFace dDoc
  t "two-sequences deck six pages" (dOut.pages.size == 6)
  t "two-sequences deck: a stepped frame's pages share one footer"
    (dOut.pages[1]?.bind (·.foot) == dOut.pages[2]?.bind (·.foot))
  t "the framefoot note sits beside the frame's own number"
    ((dOut.pages[4]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "note2")
  t "pdf and html footers agree across steps and notes"
    (pdfFoots dOut == htmlFoots dDoc && htmlFoots dDoc == ["1", "note2"])
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
  let (fDoc, _) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    ("\\begin{frame}{One}\na\n\\end{frame}\n\\section{End}"))
  let fGeom := Layout.Geom.ofPage fDoc.page
  let fOut := layoutOf oneFace fDoc fGeom
  let mp : Dim.Sp := fGeom.textWidth * 7875 / 10000
  t "a section after every frame fills the bar exactly"
    (fOut.pages.any fun p => p.fills.any fun f =>
      f.w == mp && f.color == (molochProgress ()).1)
  let (zDoc, zDs) := elabStr (deck169 "\\theme{moloch}\\title{T}\\author{A}"
    "\\maketitle\n\\section{S}\n")
  t "zero-count deck source clean" zDs.isEmpty
  t "a deck with no countable frame draws no progress bar"
    (zDoc.frameCount == 0 &&
     (layoutOf oneFace zDoc).pages.all fun p =>
       !(p.fills.any fun f => f.color == (molochProgress ()).2))
  t "html draws no progress bar with no countable frame"
    (((HtmlDoc.emit {} zDoc).1.splitOn "class=\"progress\"").length == 1)
  -- appendixnumberbeamer's `\appendix` restarts the count: main frames read n/M, appendix frames n/A.
  let appendixDeck (pkg : Bool) : Ir.Doc × Array Diag :=
    elabStr (deck169
      ((if pkg then "\\usepackage{appendixnumberbeamer}\n" else "") ++
        "\\chrome{ footer = { right = \\framefraction } }")
      ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}\n" ++
       "\\appendix\n\\begin{frame}{C}\nc\n\\end{frame}\n\\begin{frame}{D}\nd\n\\end{frame}"))
  let (aDoc, _) := appendixDeck true
  t "appendixnumberbeamer numbers its appendix from 1"
    (aDoc.frameNumbers.toList.filterMap id == [1, 2, 1, 2])
  let aOut := layoutOf oneFace aDoc
  t "appendixnumberbeamer: each part's frames read n over the part's own count"
    (pdfFoots aOut == ["1/2", "2/2", "1/2", "2/2"])
  t "appendixnumberbeamer: pdf and html footers are the same text"
    (pdfFoots aOut == htmlFoots aDoc)
  let (nDoc, _) := appendixDeck false
  t "without appendixnumberbeamer the appendix numbers on"
    (nDoc.frameNumbers.toList.filterMap id == [1, 2, 3, 4] &&
      pdfFoots (layoutOf oneFace nDoc) == ["1/4", "2/4", "3/4", "4/4"])
  let (cDoc, cDs) := elabStr (deck169
    "\\chrome{ footer = { right = \\framefraction } }"
    ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}"))
  t "framefraction parses to its slot" (cDs.isEmpty &&
    cDoc.chrome.footerRight == some .frameFraction)
  let cOut := layoutOf oneFace cDoc
  t "the fraction footer reads n / N"
    (cOut.pages.map (fun p => (p.foot.map (fun f => Ir.plainText (Ir.bandInlines f))).getD "") ==
      #["1 / 2", "2 / 2"])
  t "pdf and html agree on the fraction form"
    (pdfFoots cOut == htmlFoots cDoc && htmlFoots cDoc == ["1/2", "2/2"])
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
  let longFoot := String.intercalate " " (List.replicate 40 "an overlong footer")
  let (wDoc, _) := elabStr (deck169 s!"\\runningfoot\{{longFoot}}"
    "\\begin{frame}{A}\na\n\\end{frame}")
  let wOut := layoutOf oneFace wDoc
  t "a wrapping running line warns by name"
    (wOut.diags.any (·.code == "W0328"))
  t "a one-line running line does not warn"
    (!rOut.diags.any (·.code == "W0328"))

/-- `\setbeamertemplate{frame footer}`, alone or through a wrapper, reaches the chrome footer's left
slot as `\framefoot`. -/
def frameFootChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
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
  let (bDoc, bDs) := elabStr (deck169 "\\theme{default}"
    ("\\setbeamertemplate{frame footer}{quiet note}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a bare frame footer template is clean" (!bDs.any (·.code == "W0104"))
  let bOut := layoutOf oneFace bDoc
  t "the unthemed note still lands"
    ((bOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "quiet note")
  let (_, fDs) := elabStr (deck169 ""
    ("\\setbeamertemplate{footline}{\\insertframenumber}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a content-carrying template drops as an error naming framefoot"
    (fDs.any fun d => d.code == "E0111" && d.severity == .error &&
      ((d.help.getD "").splitOn "framefoot").length == 2)
  let (html, _) := HtmlDoc.emit {} doc
  t "html wrapped frame carries the note"
    ((html.splitOn "origin: example.org").length == 2)
  t "html unwrapped frames keep the section title"
    ((html.splitOn ">Topic</span>").length == 3)

/-- Themed slides furniture keyed on the semantic palette entries. -/
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
        | .run _ c _ _ _ _ _ _ _ _ _ => c == bg
        | _ => false
     | none => false)
  t "body text takes fg"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ _ _ _ _ => c == fg
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
    (match Ir.Design.declared? doc.palette .page, Ir.Design.declared? doc.palette .ink with
     | some bg, some fg =>
       hasStr html s!"--ltx-bg: {HtmlDoc.cssColor bg};" &&
         hasStr html s!"--ltx-fg: {HtmlDoc.cssColor fg};" &&
         hasStr html "  background: var(--ltx-bg);\n" && hasStr html "  color: var(--ltx-fg);\n"
     | _, _ => false)
  t "html frame header is a bar"
    ((html.splitOn "section.slide > header { background: var(--ltx-frametitlebg);").length == 2)
  t "html section page carries its position"
    ((html.splitOn "class=\"section-page\"").length == 2 &&
     (html.splitOn "width: 50%").length == 2)
  let (plainDoc, _) := elabStr ("\\documentclass[aspectratio=169]{slides}\n" ++
    "\\theme{default}\n" ++
    "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")
  let plainOut := layoutOf oneFace plainDoc
  t "unthemed pages carry no fills" (plainOut.pages.all (·.fills.isEmpty))

/-- `fragile` and `fragile=true` are artifact no-ops over inputs Beamer's external reader
accepts. -/
def fragileNoopChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "Inline \\verb|QuartzInline17| and \\verb*|OpalStar19 gap|.\n\n" ++
    "\\begin{verbatim}\nCedarRaw23 {value} % _\n\\end{verbatim}\n\n" ++
    "\\begin{lstlisting}[language=Lean]\ndef AmberListing29 := 31\n\\end{lstlisting}\n\n" ++
    "\\begin{minted}{lean}\ndef VioletMinted37 := true\n\\end{minted}"
  let markers := #["QuartzInline17", "OpalStar19", "CedarRaw23",
    "AmberListing29", "VioletMinted37"]
  let source (opt : String) : String := deck169Body
    ("\\begin{frame}" ++ opt ++ "{Heading}\n" ++ body ++ "\n\\end{frame}")
  let (plain, plainDs) := elabStr (source "")
  let variants := #["fragile", "fragile=true"].map fun opt =>
    elabStr (source ("[" ++ opt ++ "]"))
  let docs := variants.map fun r => r.1
  let diagss := variants.map fun r => r.2
  let content : Option (Array Ir.Block) := plain.body.findSome? fun
    | .frame title _ _ _ blocks =>
      if Ir.plainText title == "Heading" then some blocks else none
    | _ => none
  t "fragile no-op witness retains every supported raw-capture form"
    (match content with
     | some blocks =>
       blocks.any (fun
         | .para xs => Ir.plainText xs == "Inline QuartzInline17 and OpalStar19␣gap." &&
             xs.any (fun | .styled .mono ys => Ir.plainText ys == "QuartzInline17" | _ => false) &&
             xs.any (fun | .styled .mono ys => Ir.plainText ys == "OpalStar19␣gap" | _ => false)
         | _ => false) &&
       blocks.filterMap (fun
         | .verbatim _ s _ => some s.trimAscii.toString
         | _ => none) == #["CedarRaw23 {value} % _", "def AmberListing29 := 31",
           "def VioletMinted37 := true"]
     | none => false)
  t "supported fragile spellings change neither IR nor diagnostics"
    (plainDs.isEmpty && docs.all (· == plain) && diagss.all (· == plainDs))
  let plainOut : Layout.Out := layoutOf oneFace plain
  let layoutText := String.intercalate "\n" ((allLines plainOut).toList.map lineText)
  t "Layout.Out retains each distinctive fragile raw marker"
    (markers.all fun marker => hasStr layoutText marker)
  let (_, htmlTree, htmlDs) := HtmlDoc.emitTree {} plain
  t "the typed HTML tree retains each distinctive fragile raw marker once"
    (htmlDs.isEmpty && markers.all fun marker => treeOccurs htmlTree marker == 1)
  let plainHtml := (HtmlDoc.emit {} plain).1
  t "supported fragile spellings change no HTML bytes"
    (docs.all fun doc => (HtmlDoc.emit {} doc).1 == plainHtml)
  let pdfOf (doc : Ir.Doc) : ByteArray :=
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf oneFace doc geom
    driverPdf oneFace geom doc out
  let plainPdf := pdfOf plain
  t "supported fragile spellings change no shipped PDF bytes"
    (docs.all fun doc => pdfOf doc == plainPdf)
  let unsupported (opt : String) : Bool :=
    let ds := (elabStr (source ("[" ++ opt ++ "]"))).2
    ds.map (·.code) == #["N0102"] && ds.any fun d =>
      d.severity == .note && hasStr d.message s!"frame option '{opt}'"
  t "fragile=false and page-affecting fragile options stay named losses"
    (unsupported "fragile=false" && unsupported "fragile=singleslide" &&
      unsupported "containsverbatim")
  let extensionMarker := "Intentional reader superset marker"
  let (extension, extensionDs) := elabStr (deck169Body
    ("\\begin{frame}[fragile]{Heading}\n" ++ extensionMarker ++
      "\n\\end{frame}% trailing comment"))
  t "the intentional fragile-reader acceptance superset remains explicit"
    (extensionDs.isEmpty && match extension.body with
      | #[.frame _ _ _ _ #[.para xs]] => Ir.plainText xs == extensionMarker
      | _ => false)

/-- Frames as first-class blocks: elaboration shape, title forms, title frame and one page per
frame. -/
def slideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (fDoc, fDs) := elabStr (deck169Body "\\begin{frame}{T}\nbody\n\\end{frame}")
  t "frame source clean" fDs.isEmpty
  t "frame is first-class with its title"
    (fDoc.body == #[.frame #[.text "T"] false .center false #[.para #[.text "body"]]])
  t "frame title after a blank line is content"
    ((elabStr (deck169Body "\\begin{frame}[plain]\n\n{scope group}\n\\end{frame}")).1.body ==
      #[.frame #[] false .center false #[.para #[.text "scope group"]]])
  t "an unmodelled frame option is a note"
    ((elabStr (deck169Body "\\begin{frame}[plain]{T}\nbody\n\\end{frame}")).2.any
      fun d => d.code == "N0102" && d.severity == .note)
  t "frametitle names the frame"
    ((elabStr (deck169Body "\\begin{frame}\n\\frametitle{Named}\nbody\n\\end{frame}")).1.body ==
      #[.frame #[.text "Named"] false .center false #[.para #[.text "body"]]])
  let (dupDoc, dupDs) := elabStr
    (deck169Body "\\begin{frame}\n\\frametitle{One}\n\\frametitle{Two}\nbody\n\\end{frame}")
  t "a second frametitle warns and wins"
    (dupDs.any (·.code == "W0311") &&
     match dupDoc.body with
     | #[.frame title _ _ _ _] => Ir.plainText title == "Two"
     | _ => false)
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
  let threeFrames := deck169Body ("\\begin{frame}{A}\na\n\\end{frame}\n" ++
    "\\begin{frame}{B}\nb\n\\end{frame}\n\\section{S}\n\\begin{frame}{C}\nc\n\\end{frame}")
  let (dDoc, dDs) := elabStr threeFrames
  t "deck source clean" dDs.isEmpty
  let out := layoutOf oneFace dDoc
  t "one page per frame, none for a section with no section page" (out.pages.size == 3)
  t "every slide leads with its title at the heading size"
    (out.pages.all fun p =>
      p.lines.any (·.size == Layout.sectionSize (Layout.Geom.ofPage dDoc.page) 1))
  let (html, _) := HtmlDoc.emit {} dDoc
  t "html gives each frame its own slide section"
    ((html.splitOn "<section class=\"slide\"").length == 4)
  t "align* is one display-math grid, cells and rows intact"
    (match (elabStr "\\begin{align*}1 &= 1 \\\\ 2 &= 4\\end{align*}").1.body.map unwrapDisplay with
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
  let classicTab := "\\begin{tabular}{ll}\\hline\n" ++
    "\\multicolumn{2}{X}{Head} \\\\ \\cline{1-2}\na & b \\\\ \\hline\\end{tabular}"
  let (ctDoc, ctDs) := elabStr classicTab
  t "classic tabular rules are typed rules, not unknown commands"
    (!ctDs.any (·.code == "W0301") &&
     match ctDoc.body with
     | #[.table _ _ _ _ rules _] =>
       rules == #[(0, .mid), (1, .cmid 1 2 false false), (2, .mid)]
     | _ => false)
  t "multicolumn keeps its cell text and records its span"
    (match ctDoc.body with
     | #[.table cols _ _ rows _ spans] =>
       let s := String.join (rows.toList.map fun r =>
         String.join (r.toList.map Ir.plainText))
       (s.splitOn "Head").length == 2 && !s.toList.contains '2' &&
         !s.toList.contains 'X' &&
         rows.all (·.size == cols.size) && !ctDs.any (·.code == "W0337") &&
         ctDs.any (·.subject == some "tabular:colspec") &&
         spans == #[{ row := 0, col := 0, n := 2, spec := { width := .natural, align := .left } }]
     | _ => false)
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
           | .run _ c _ _ _ _ _ _ _ _ _ => c == Ir.Color.white
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
      | .colored c name body => c.r == 0x7C && name == some (.color "primary") && body.size == 1
      | _ => false
    | _ => false)
  let unknownSrc (body : String) := "\\documentclass{article}\\palette{a = #333}" ++
    "\\begin{document}\\textcolor{a}{y}" ++ body ++ "\\end{document}"
  t "palette unknown name warns and keeps the content"
    (warnCodes (unknownSrc "\\textcolor{nope}{x}") == ["W0304"] &&
     (elabStr (unknownSrc "\\textcolor{nope}{x}")).1.body == (elabStr (unknownSrc "x")).1.body)
  let palSrc (body : String) : Ir.Doc :=
    (Elab.run "t" ("\\documentclass{article}\\palette{mut = #666666}" ++
      "\\begin{document}" ++ body ++ "\\end{document}")).1
  t "palette name takes its group as an argument"
    ((palSrc "\\mut{in} out").body == #[.para #[
      .colored { r := 0x66, g := 0x66, b := 0x66 } (some (.color "mut")) #[.text "in"],
      .text " out"]])
  t "palette name with no group runs to the end of the group"
    ((palSrc "{\\mut in} out").body == #[.para #[
      .colored { r := 0x66, g := 0x66, b := 0x66 } (some (.color "mut")) #[.text "in"],
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
  t "color pdf components" (({ r := 255, g := 0, b := 128 } : Ir.Color).pdfComponents == "1 0 0.502")
  t "color black components" (Ir.Color.black.pdfComponents == "0 0 0")

/-- The palette's contrast arithmetic, xcolor mixing and the contrast judge. -/
def contrastChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- WCAG relative luminance in Float, scaled by 1e7 and rounded: the formula the channel table tabulates.
  let lin (c : Nat) : Nat :=
    let s := c.toFloat / 255.0
    let l := if s ≤ 0.04045 then s / 12.92
      else ((s + 0.055) / 1.055) ^ (2.4 : Float)
    (l * 10000000.0).round.toUInt32.toNat
  t "contrast table is the WCAG formula, all 256 channels"
    ((List.range 256).all fun c => Oklab.channelLinear.getD c 0 == lin c)
  t "contrast black on white is 21:1"
    (Contrast.contrastMilli .black .white == 21000)
  t "contrast of a colour with itself is 1:1"
    (Contrast.contrastMilli (screenColor .light .focus) (screenColor .light .focus) == 1000)
  t "contrast does not care which side is the text"
    (Contrast.contrastMilli (screenColor .light .muted) (screenColor .light .page) ==
     Contrast.contrastMilli (screenColor .light .page) (screenColor .light .muted))
  t "ratio string" (Contrast.ratioString 4627 == "4.62:1" &&
    Contrast.ratioString 21000 == "21.00:1" && Contrast.ratioString 1005 == "1.00:1")
  t "the light focus ring fails the dark page"
    (Contrast.contrastMilli (screenColor .light .focus) (screenColor .dark .page) <
      Contrast.aaNonText)
  t "illegible focus ring names its ratio" (Contrast.ratioString
    (Contrast.contrastMilli (screenColor .light .focus) (screenColor .dark .page)) == "2.70:1")

  t "covered contract rejects moloch at 38%"
    (!Contrast.coveredContract
      { deckBundle Theme.moloch with coveredFraction := some 38 })
  let quietingHolds := Id.run do
    let cov := (Ir.Design.ofDoc { palette := { coveredFraction := some 38 } }).cover
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

  let (page, _) := HtmlDoc.emit {} (elabStr "x").1
  t "the dark screen re-accents through light-dark()"
    (hasStr page s!"{HtmlDoc.roleVar .accent}: light-dark({HtmlDoc.cssColor (screenColor .light .accent)}, \
{HtmlDoc.cssColor (screenColor .dark .accent)})" && hasStr page "color-scheme: light dark;")
  t "light accent comes from the registry's light column"
    ((page.splitOn s!"{HtmlDoc.roleVar .accent}: {HtmlDoc.cssColor (screenColor .light .accent)}").length == 2)
  t "the focus ring follows the accent"
    ((page.splitOn s!"{HtmlDoc.roleVar .focus}: var({HtmlDoc.roleVar .accent})").length == 2)
  t "the printed page restates the print column under @media print"
    (hasStr page "@media print {" &&
      hasStr page s!"{HtmlDoc.roleVar .ink}: {HtmlDoc.cssColor Ir.Color.black};")
  let (deckHead, _, _) := HtmlDoc.emitTree {} (elabStr
    ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
     "\\begin{frame}{T}x\\end{frame}\\end{document}")).1
  let headCss (h : Array Html.Node) : String := h.foldl (init := "") fun acc n => match n with
    | Html.Node.style s => acc ++ s
    | _ => acc
  let deckCss := headCss deckHead
  t "a deck ships no light-dark() unless its document declares schemes"
    (hasStr deckCss "color-scheme: light;" && !hasStr deckCss "light-dark(")
  let (askedHead, _, _) := HtmlDoc.emitTree {} (elabStr
    ("\\documentclass{slides}\\theme{moloch}\\output{ schemes = print, light, dark }" ++
     "\\begin{document}\\begin{frame}{T}x\\end{frame}\\end{document}")).1
  t "a deck that declares its schemes ships them"
    (hasStr (headCss askedHead) "light-dark(")
  let inkSrc := "\\documentclass{article}\\palette{ ink = #18181B }\\begin{document}x\\end{document}"
  let (inkHead, _, _) := HtmlDoc.emitTree {} (elabStr inkSrc).1
  let inkCss := headCss inkHead
  let inkDoc := (elabStr inkSrc).1
  let darkInk := (Ir.Design.inScheme inkDoc.palette (inkDoc.palette.frame .dark) .ink).getD .black
  t "a declared ink ships as is on the light screen, carried on the dark"
    (hasStr inkCss s!"{HtmlDoc.roleVar .ink}: light-dark(#18181b, {HtmlDoc.cssColor darkInk})" &&
      Contrast.aaText ≤ Contrast.contrastMilli darkInk
        ((Ir.Design.inScheme inkDoc.palette (inkDoc.palette.frame .dark) .page).getD .black) &&
      (HtmlDoc.schemeFailures true inkDoc).isEmpty)
  let (picHead, _, _) := HtmlDoc.emitTree {} (elabStr
    ("\\documentclass{article}\\pictures{ tool = none }\\begin{document}" ++
     "\\begin{tikzpicture}\\draw (0,0) -- (1,0);\\end{tikzpicture}\\end{document}")).1
  let picCss := headCss picHead
  let ruleIn (css sel prop : String) (sc : Ir.Scheme) : Option String :=
    let (root, dark) := schemeRoot css sc
    ((sheetRules css).toList.reverse.findSome? fun (conds, sl, decls) =>
      if hasStr sl sel && conds.all (holdsIn sc ·) then (cssDecls decls).lookup prop else none).map
      (schemeRead dark root)
  let darkPage := (Ir.Design.at {} .dark .page).getD Ir.Color.black
  let legibleOnDark (v : Option String) : Bool :=
    v.any fun t => match (({} : Ir.Palette).resolveSource none t).toOption.join with
      | some c => Contrast.aaText ≤ Contrast.contrastMilli c darkPage
      | none => false
  t "a picture stands on the printed page on the dark screen"
    (ruleIn picCss "svg.picture" "background" .dark == some "#ffffff")
  let schemeCss (imgs : Image.Store) (src : String) : String :=
    let (h, _, _) := HtmlDoc.emitTree { imgs } (elabStr src).1
    headCss h
  let styled (decl body : String) : String :=
    s!"\\documentclass\{article}{decl}\\begin\{document}{body}\\end\{document}"
  let ruleCss := schemeCss {} (styled "\\style{section}{ rule = red!50!black }" "\\section{A}b")
  t "a heading rule's literal colour is carried to the dark screen"
    (ruleIn ruleCss "h2" "--rule-color" .light == some "#800000" &&
      legibleOnDark (ruleIn ruleCss "h2" "--rule-color" .dark))
  let hoverCss := schemeCss {} (styled "\\style{nav}{ hover = red!50!black }" "x")
  t "a link hover's literal colour is carried to the dark screen"
    (ruleIn hoverCss "a:hover" "color" .light == some "#800000" &&
      legibleOnDark (ruleIn hoverCss "a:hover" "color" .dark))
  let markerCss := schemeCss {} (styled "\\style{itemize}{ marker = {\\textcolor[HTML]{1A2433}{>}} }"
    "\\begin{itemize}\\item a\\end{itemize}")
  t "a list marker's literal colour is carried to the dark screen"
    (ruleIn markerCss "li::marker" "color" .light == some "#1a2433" &&
      legibleOnDark (ruleIn markerCss "li::marker" "color" .dark))
  let raster (a : Image.Alpha) : Image.Store :=
    { entries := #[{ src := "mark.png", info := some { pxW := 4, pxH := 4, alpha := a } }] }
  let imgSrc := "\\documentclass{article}\\usepackage{graphicx}\\begin{document}x\n\n" ++
    "\\includegraphics{mark.png}\\end{document}"
  let seeThrough (imgs : Image.Store) : Bool :=
    let (_, body, _) := HtmlDoc.emitTree { imgs } (elabStr imgSrc).1
    (elemNodesList (· == "img") #[] body.toList).any fun n => match n with
      | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "see-through"
      | _ => false
  t "a transparent raster stands on a light plate on the dark screen"
    (seeThrough (raster (.soft ByteArray.empty 8)) && seeThrough (raster (.colorKey #[0, 0])) &&
      hasStr (schemeCss (raster (.soft ByteArray.empty 8)) imgSrc) "img.see-through")
  t "an opaque raster stands as it is"
    (!seeThrough (raster .opaque) && hasStr (schemeCss (raster .opaque) imgSrc) "color-scheme: light dark;")
  let (tokHead, _, _) := HtmlDoc.emitTree {} (elabStr
    "\\documentclass{article}\\tokens{ topsep = 3pt }\\begin{document}x\\end{document}").1
  let tokCss := headCss tokHead
  t "a declared token reaches every scheme and no scheme block restates it"
    (hasStr tokCss "--topsep:" && match (tokCss.splitOn "@supports (color: light-dark")[1]? with
     | some after => !hasStr after "--topsep:"
     | none => false)
  t "an undeclared document emits no empty custom-property block"
    (let (plainHead, _, _) := HtmlDoc.emitTree {} (elabStr "x").1
     plainHead.all fun n => match n with
       | Html.Node.style s => !((s.splitOn ":root {\n\n}").length > 1)
       | _ => true)

  let pale := "\\documentclass{article}\\palette{ washed = #DDDDDD }" ++
    "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
  let quiet := "\\documentclass{article}\\palette{ washed = #888888 }" ++
    "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
  t "a failing role pairing warns once, naming role and requirement"
    ((elabStr quiet).2.any fun d => d.code == "W0315" && d.severity == .warning &&
      (d.message.splitOn "'washed'").length == 2 &&
      ((diagWords d).splitOn "4.50:1").length == 2)
  t "a failing role ships its declared value"
    ((elabStr quiet).1.palette.find? "washed" == some { r := 0x88, g := 0x88, b := 0x88 })
  t "a pale role warns on one line, naming no repair"
    ((elabStr pale).2.any fun d => d.code == "W0315" &&
      d.subject.any (·.startsWith "washed:") && d.help.isNone)
  t "declared intent silences the pairing judge whole"
    (let src := "\\documentclass{article}" ++
      "\\palette[decorative]{ washed = #DDDDDD }" ++
      "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
     !(warnCodes src).contains "W0315")
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
  let anon := "\\documentclass{article}\\begin{document}\\textcolor{yellow!50}{quiet}" ++
    "\\end{document}"
  let anonDiag := ((elabStr anon).2.filter (·.code == "W0315"))[0]?
  t "an unreachable mix warns, naming the expression the author wrote"
    (anonDiag.any fun d => d.subject.any (·.startsWith "yellow!50:"))
  t "the anonymous warning invents no role name and names no repair"
    (anonDiag.any fun d => d.help.isNone && !hasStr d.message "quiet")
  let reMix := elabStr ("\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
    "\\begin{document}\\textcolor{fg!60!bg}{quiet}\\end{document}")
  t "a failing mix of two named colours warns under its expression"
    (reMix.2.any fun d => d.code == "W0315" && d.subject.any (·.startsWith "fg!60!bg:"))
  let mixed := ((({ entries := #[((.role .ink), { r := 0x23, g := 0x37, b := 0x3B }),
      ((.role .page), { r := 0xFA, g := 0xFA, b := 0xFA })] } : Ir.Palette).resolve "fg!50!bg").getD
    Ir.Color.black)
  t "a decorative entry at the mix's value keeps it low: no re-weighting, no warning"
    (let src := "\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
      "\\palette[decorative]{ dim = " ++ mixed.hex ++ " }" ++
      "\\begin{document}\\textcolor{fg!50!bg}{quiet}\\end{document}"
     !(warnCodes src).contains "W0315")
  t "covered is exempt by role"
    (!(warnCodes ("\\documentclass{article}\\palette{ covered = #DDDDDD }" ++
      "\\begin{document}\\textcolor{covered}{later}\\end{document}")).contains "W0315")
  let titled := "\\begin{frame}{T}x\\end{frame}"
  -- A deck's title stands at stage size, so it asks large-scale text's 3:1: #BBBBBB on #555555 reads 3.88:1.
  t "an overridden frame-title pair is judged at the stage's size"
    (!(warnCodes (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #555555, frametitlefg = #BBBBBB }"
      titled)).contains "W0345")
  t "an overridden frame-title pair below 3:1 warns once, on one line"
    (((elabStr (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }" titled)).2.filter
      fun d => d.code == "W0345" && d.help.isNone && hasStr (diagWords d) "3.00:1").size == 1)
  t "the untouched bundle's frame-title pair is silent"
    (!(warnCodes (dvDeck "\\theme{moloch}" titled)).contains "W0345")
  t "an illegible frame-title pair without a titled frame is silent"
    (!(warnCodes (dvDeck "\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }"
      "\\begin{frame}x\\end{frame}")).contains "W0345")
  t "declared decorative intent silences the frame-title pair"
    (!(warnCodes (dvDeck ("\\theme{moloch}\\palette{ frametitlebg = #F2F2F0 }" ++
      "\\palette[decorative]{ frametitlefg = #FAFAF9 }") titled)).contains "W0345")
  t "an overridden standout pair warns at the large-scale threshold"
    ((elabStr (dvDeck "\\palette{ standoutfg = #A0A0A0, standoutbg = #FAFAFA }"
      "\\begin{frame}[standout]S\\end{frame}")).2.any
      fun d => d.code == "W0345" && hasStr d.message "the standout frame" &&
        ((diagWords d).splitOn "3.00:1").length == 2)
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
  -- #808080 on the shipped page is 3.95:1: as body text it warns, as Huge large-scale text it passes.
  let grey (body : String) := "\\documentclass{article}" ++
    "\\palette{ grey = #808080 }\\begin{document}" ++ body ++ "\\end{document}"
  t "borderline grey warns as body text"
    ((warnCodes (grey "\\textcolor{grey}{x}")).contains "W0315")
  t "borderline grey passes as large-scale text"
    (!(warnCodes (grey "{\\Huge \\textcolor{grey}{x}}")).contains "W0315")
  for (name, decl, fails) in [
      ("absolute large", "\\fontsize{20pt}{24pt}\\selectfont", false),
      ("absolute small after Huge", "\\Huge\\fontsize{8pt}{10pt}\\selectfont", true),
      ("absolute large after small", "\\small\\fontsize{20pt}{24pt}\\selectfont", false),
      ("unresolved size after Huge", "\\Huge\\fontsize{1ex}{10pt}\\selectfont", true)] do
    t s!"contrast font size: {name}"
      ((warnCodes (grey ("{" ++ decl ++ "\\textcolor{grey}{x}}"))).contains "W0315" ==
        fails)
  let sizedSection (size : String) := "\\documentclass{article}" ++
    "\\page{ fontsize = " ++ size ++ " }\\palette{ grey = #808080 }" ++
    "\\begin{document}\\section{\\textcolor{grey}{Head}}x\\end{document}"
  t "a 9pt-base section title is judged at the size the layout sets"
    ((warnCodes (sizedSection "9pt")).contains "W0315")
  t "a 10pt-base section title stays large-scale, judge and page agreeing"
    (!(warnCodes (sizedSection "10pt")).contains "W0315")
  t "a declared fg is judged against the declared bg"
    ((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #808080, bg = #F0F0F0 }" ++
      "\\begin{document}x\\end{document}")).2.any fun d =>
        d.code == "W0315" && (d.message.splitOn "'fg'").length == 2 &&
          ((diagWords d).splitOn "#F0F0F0").length == 2)
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
        fun d => (d.code == "W0315" || d.code == "W0330") && d.severity == .warning).size) == 1)
  t "the built-in themes raise no pairing warning"
    (!(warnCodes ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
      "\\begin{frame}x\\end{frame}\\end{document}")).contains "W0315")

  let paleUse (spec : String) : String :=
    "\\documentclass{article}\\palette{ alpha = #C4C4C4 }\\begin{document}" ++
      spec ++ "\\end{document}"
  let pairing (spec : String) : Array String :=
    ((elabStr (paleUse spec)).2.filter fun d =>
      d.code == "W0315" && d.severity == .warning).map diagWords
  let heldAt (spec needle : String) : Bool :=
    let ms := pairing spec
    ms.size == 1 && ((((ms[0]?).getD "").splitOn needle).length == 2)
  t "a pairing large in every use is held to the large-scale threshold"
    (heldAt "{\\Huge \\textcolor{alpha!60}{a}} {\\Huge \\textcolor{alpha!60}{b}}"
      "3.00:1")
  t "a pairing small in one use is held to the text threshold, large first"
    (heldAt "{\\Huge \\textcolor{alpha!60}{a}} \\textcolor{alpha!60}{b}" "4.50:1")
  t "and the same when the small use comes first"
    (heldAt "\\textcolor{alpha!60}{a} {\\Huge \\textcolor{alpha!60}{b}}" "4.50:1")
  t "a repeated pairing is reported once"
    ((pairing ("\\textcolor{alpha!60}{a} \\textcolor{alpha!60}{b} " ++
      "\\textcolor{alpha!60}{c} \\textcolor{alpha!60}{d}")).size == 1)
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
      d.code == "W0315" && d.severity == .warning &&
        d.span == some ⟨"t", { line := 4, col := 1 }⟩)
  t "distinct pairings are reported separately"
    ((pairing ("\\textcolor{alpha!60}{a} \\textcolor{alpha!50}{b} " ++
      "\\textcolor{alpha!40}{c} \\textcolor{alpha!60}{d}")).size == 3)
  t "one colour under two names is two pairings"
    (((elabStr ("\\documentclass{article}" ++
      "\\palette{ alpha = #888888, beta = #888888 }\\begin{document}" ++
      "\\textcolor{alpha}{a} \\textcolor{beta}{b} \\textcolor{alpha}{c}" ++
      "\\end{document}")).2.filter fun d =>
        d.code == "W0315" && d.severity == .warning).size == 2)
  t "one role on two grounds is two pairings"
    (((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #303030, bg = #FFFFFF, mid = #818181 }\\begin{document}" ++
      "\\textcolor{mid}{a}\n\n\\palette{ bg = #222222 }\n\n\\textcolor{mid}{b}" ++
      "\\end{document}")).2.filter fun d =>
        d.code == "W0315" && d.severity == .warning &&
          (d.message.splitOn "'mid'").length == 2).size == 2)
  let twoEpochs := elabStr ("\\documentclass{article}" ++
    "\\palette{ washed = #888888 }\\begin{document}\\textcolor{washed}{a}" ++
    "\n\n\\palette{ washed = #888888 }\n\n\\textcolor{washed}{b}\\end{document}")
  let declared : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  t "two epochs declaring one failing role read one warning"
    ((twoEpochs.2.filter fun d => d.code == "W0315" && d.severity == .warning).size == 1)
  t "and both epochs' palettes keep the declared value"
    (twoEpochs.1.palette.find? "washed" == some declared &&
     (twoEpochs.1.body.filterMap fun b => match b with
       | .setPalette p => p.find? "washed"
       | _ => none) == #[declared])
  -- Synthesised as IR, so the clock times the judge and not the parser.
  let dk : Ir.Color := { r := 0x10, g := 0x10, b := 0x10 }
  let manyUses : Ir.Doc :=
    { palette := { entries := #[((.color "dk"), dk)] }
      body := (List.range 20000).toArray.map fun i =>
        Ir.Block.para #[.styled (.size "Huge")
          #[.colored dk (some (.color "dk")) #[.text s!"w{i}"]]] }
  let t0 ← IO.monoMsNow
  let judged := Contrast.docDiags manyUses
  -- Consumed before the clock is read again, since a pure `let` floats to its first use.
  t "20,000 legible coloured runs are judged silently" judged.isEmpty
  let judgeMs := (← IO.monoMsNow) - t0
  t s!"hang guard: the contrast judge over 20000 coloured runs within {hangGuardMs 50} ms ({judgeMs} ms)"
    (judgeMs < hangGuardMs 50)
  let washedNotes (uses : Nat) : Array String :=
    ((elabStr ("\\documentclass{article}\\palette{ washed = #888888 }" ++
      "\\begin{document}" ++
      String.join ((List.range uses).map fun i =>
        "\\textcolor{washed}{w" ++ toString i ++ "} ") ++
      "\\end{document}")).2.filter fun d =>
        d.code == "W0315" && d.severity == .warning).map (·.message)
  t "a repeated failing pairing is reported once, in the same words"
    ((washedNotes 4).size == 1 && washedNotes 4 == washedNotes 1)
  let manyPale : Ir.Doc :=
    { palette := { entries := #[((.color "washed"), declared)] }
      body := (List.range 3000).toArray.map fun i =>
        Ir.Block.para #[.colored declared (some (.color "washed")) #[.text s!"w{i}"]] }
  let t1 ← IO.monoMsNow
  let paleJudged := Contrast.docDiags manyPale
  t "3,000 uses of a failing pairing read one warning with their count"
    ((paleJudged.filter (·.severity == .warning)).size == 1 &&
      (Diag.tallySites paleJudged).any fun d => d.severity == .warning && d.sites == 3000)
  let paleMs := (← IO.monoMsNow) - t1
  t s!"hang guard: 3000 uses of one failing pairing judged within {hangGuardMs 30} ms ({paleMs} ms)"
    (paleMs < hangGuardMs 30)

  for th in Theme.builtin do
    let (thDoc, _) := elabStr ("\\documentclass{slides}\\theme{" ++ th.name ++
      "}\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")
    t s!"\\theme installs the {th.name} bundle's own values"
      ({ thDoc.palette with classColors := {} } == deckBundle th)
  t "the contract rejects moloch's original alert"
    (let badEntries := ((deckBundle Theme.moloch).entries.filter (·.1 != (.role .alert))).push
        ((.role .alert), ({ r := 0xEB, g := 0x81, b := 0x1B } : Ir.Color))
     !Contrast.paletteContract { entries := badEntries })
  let themedAlert := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\begin{frame}\\alert{hot}\\end{frame}\\end{document}")
  t "themed alert is the colour alone" (themedAlert.1.body.any fun b =>
    match b with
    | .frame _ _ _ _ body => body.any fun blk =>
      match blk with
      | .para content => content.any fun x =>
        match x with
        | .colored _ (some (.role .alert)) inner => inner.all fun y =>
          match y with
          | .styled .bold _ => false
          | _ => true
        | _ => false
      | _ => false
    | _ => false)

def mixChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pal : Ir.Palette := { entries := #[((.color "base"), { r := 0x40, g := 0x00, b := 0x80 })] }
  t "mix toward white" (pal.resolve "base!50" == some { r := 0xA0, g := 0x80, b := 0xC0 })
  t "mix with black" (pal.resolve "base!50!black" == some { r := 0x20, g := 0x00, b := 0x40 })
  t "mix chain folds left" (pal.resolve "base!50!black!30" ==
    some ((({ r := 0x40, g := 0x00, b := 0x80 } : Ir.Color).mix 50 Ir.Color.black).mix 30 Ir.Color.white))
  t "mix black!2 is near-white"
    (({} : Ir.Palette).resolve "black!2" == some { r := 250, g := 250, b := 250 })
  t "mix plain name still resolves" (pal.resolve "base" == some { r := 0x40, g := 0x00, b := 0x80 })
  t "mix pct over 100 rejected" (pal.resolve "base!101" == none)
  t "mix unknown atom rejected" (pal.resolve "nope!50" == none)
  -- xcolor's base colours are always available (xcolor manual §4.1, Table 1).
  t "xcolor base names resolve undeclared"
    (({} : Ir.Palette).resolve "gray" == some { r := 128, g := 128, b := 128 } &&
     ({} : Ir.Palette).resolve "gray!30" ==
       some (({ r := 128, g := 128, b := 128 } : Ir.Color).mix 30 Ir.Color.white) &&
     ({} : Ir.Palette).resolve "teal!50!blue" ==
       some (({ r := 0, g := 128, b := 128 } : Ir.Color).mix 50
         { r := 0, g := 0, b := 255 }))
  t "a declared entry wins over a base name"
    (({ entries := #[((.color "gray"), { r := 1, g := 2, b := 3 })] } : Ir.Palette).resolve "gray"
      == some { r := 1, g := 2, b := 3 })
  let shadow : Ir.Palette := { entries := #[((.color "black"), { r := 0x33, g := 0x33, b := 0x33 })] }
  t "a declared black wins over the built-in atom"
    (shadow.resolve "black" == shadow.find? "black")
  t "undeclared black and white stay available"
    (({} : Ir.Palette).resolve "black" == some Ir.Color.black &&
     ({} : Ir.Palette).resolve "white" == some Ir.Color.white)
  let doc (body : String) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ fg = #000000, bg = #ffffff }\\palette[decorative]{ dim = bg!50!fg, faint = black!2 }\n" ++
    "\\begin{document}" ++ body ++ "\\end{document}")
  let (pDoc, pDs) := doc "\\textcolor{dim}{x} \\textcolor{faint}{y}"
  t "palette mix entry clean" pDs.isEmpty
  t "palette mix entry value" (pDoc.palette.find? "dim" == some { r := 0x80, g := 0x80, b := 0x80 })
  t "palette black!2 entry" (pDoc.palette.find? "faint" == some { r := 250, g := 250, b := 250 })
  let (uDoc, uDs) := doc "\\textcolor{fg!70!bg}{x}"
  t "textcolor mix resolves without W0304" (!uDs.any (·.code == "W0304"))
  t "textcolor mix colours the content" (uDoc.body == #[.para #[
    .colored { r := 0x4D, g := 0x4D, b := 0x4D } none #[.text "x"]]])
  t "textcolor mix with unknown base still warns"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\textcolor{quiet!50}{x}\\end{document}") == ["W0304"])
  let (oDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ a = #111111 }\\palette{ a = #222222 }\n" ++
    "\\tokens{ s = 4pt }\\tokens{ s = 8pt }\n" ++
    "\\begin{document}x\\end{document}")
  t "palette redeclare overrides" (oDoc.palette.find? "a" == some { r := 0x22, g := 0x22, b := 0x22 })
  t "tokens redeclare overrides"
    ((oDoc.tokens.find? "s").map (·.width) == some (Dim.Length.ofSp (Dim.pt 8)))
  t "palette redeclare keeps one entry"
    ((oDoc.palette.entries.filter (·.1 == (.color "a"))).size == 1)

/-- `\theme` installs a bundle through the declarations a document writes, and everything after it
overrides. -/
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
     mDoc.palette.find? "progressbg" ==
       some ((Ir.Color.ofHtml 0xEB 0x81 0x1B |>.mix 50 .black).mix 30 .white))
  t "theme moloch declares the progress token"
    (((mDoc.tokens.find? "progressheight").map (·.width)) ==
      some (Dim.Length.ofSp (Dim.pt 1)))
  t "theme moloch styles the frame title"
    ((mDoc.styles.find? "frametitle").bind (·.font) |>.isSome)
  let (oDoc, _) := elabStr (deck169 "\\theme{moloch}\\palette{ alert = #C2185B }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a document overrides the theme"
    (oDoc.palette.find? "alert" == some { r := 0xC2, g := 0x18, b := 0x5B } &&
     oDoc.palette.find? "frametitlebg" == some { r := 0x23, g := 0x37, b := 0x3B })
  let (pDoc, pDs) := elabStr (deck169 "\\theme{plain}" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "theme plain source clean" pDs.isEmpty
  t "theme plain has no title bar key" ((pDoc.palette.find? "frametitlebg").isNone)
  t "theme plain still inverts standout"
    (pDoc.palette.find? "standoutbg" == pDoc.palette.find? "fg")
  let (uDoc, uDs) := elabStr (deck169 "\\theme{vaporwave}" "x")
  t "unknown theme warns naming the bundles"
    (uDs.any fun d => d.code == "W0319" &&
      ((d.help.getD "").splitOn "moloch").length == 2 &&
      ((d.help.getD "").splitOn "plain").length == 2)
  t "unknown theme leaves the palette empty" (uDoc.palette.entries.isEmpty)
  let (aDoc, _) := elabStr (deck169 "\\usetheme{moloch}"
    "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")
  t "themed alert is the alert colour"
    (match aDoc.body with
     | #[.frame _ _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .colored c (some (.role .alert)) _ => some c == Ir.Design.declared? (deckBundle Theme.moloch) .alert
          | _ => false
        | _ => false
     | _ => false)
  t "a deck naming no theme takes its default bundle's alert colour"
    (match (elabStr (deck169 "" "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")).1.body with
     | #[.frame _ _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .colored c (some (.role .alert)) _ => some c == Ir.Design.declared? (deckBundle Theme.daylight) .alert
          | _ => false
        | _ => false
     | _ => false)
  t "unthemed alert stands apart from its neighbours"
    (match (elabStr (deck169 "\\theme{default}"
        "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")).1.body with
     | #[.frame _ _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .styled .bold _ | .colored .. => true
          | _ => false
        | _ => false
     | _ => false)

/-- The resolved `Design`'s values for an unthemed document, a themed one and a half-declared
standout. -/
def designChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let designOf (pre : String) : Ir.Design :=
    Ir.Design.ofDoc (elabStr ("\\documentclass{slides}" ++ pre ++
      "\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")).1
  let bare := designOf "\\theme{default}"
  t "bare design inks black on white, undeclared"
    (bare.fg == Ir.Color.black && bare.bg == Ir.Color.white &&
     !bare.fgDeclared && !bare.bgDeclared)
  t "bare design has no bar and no themed sections"
    (bare.frametitle.isNone && bare.progress.isNone)
  t "bare design standout inverts the page"
    (bare.standout == { fg := Ir.Color.white, bg := Ir.Color.black })
  t "bare design declares no covered constant and hides its pending steps"
    (bare.covered == none && bare.coveredFraction == Ir.coveredFractionDefault && bare.cover.hidden)
  t "a design declaring 38% covers plain runs to 38% of black over white"
    ((designOf "\\theme{default}\\palette{ covered = 38\\% }").inkCover == { r := 0x86, g := 0x86, b := 0x86 })
  t "bare design mutes to the ink" (bare.muted == bare.fg)
  t "bare design separator defaults to the ink" (bare.separator == bare.fg)
  t "bare design progress bar is 1pt thick"
    (bare.progressheight == { width := Dim.Length.ofSp (Dim.pt 1) })
  let themed := designOf "\\theme{moloch}"
  t "themed design carries the bundle's bar pair"
    (themed.frametitle == some { fg := { r := 0xFA, g := 0xFA, b := 0xFA }, bg := { r := 0x23, g := 0x37, b := 0x3B } })
  -- moloch's lineage colour, exactly as lualatex draws its progress bar and title separator.
  let lineage := Ir.Color.ofHtml 0xEB 0x81 0x1B
  t "themed design carries the progress pair"
    (themed.progress == some { fg := lineage, bg := (lineage.mix 50 .black).mix 30 .white })
  t "themed design reads the declared separator"
    (themed.separator == lineage)
  t "themed design reads the muted step the bundle derives"
    (themed.muted == { r := 0x61, g := 0x77, b := 0x7C })
  let half := designOf "\\theme{default}\\palette{ standoutbg = #102030 }"
  t "half-declared standout defaults its fg from the page"
    (half.standout == { fg := Ir.Color.white, bg := { r := 0x10, g := 0x20, b := 0x30 } })
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

/-- A title page may declare a ground of its own, resolved once, its ink inverting by default. -/
def titleGroundChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let titleMeta := "\\title{A Placeholder Deck}\\author{P. Placeholder}"
  let designOf (pre : String) : Ir.Design :=
    Ir.Design.ofDoc (elabStr (deck169 (titleMeta ++ pre) "\\maketitle")).1
  let deckOf (pre body : String) : String := deck169 (titleMeta ++ pre) body
  t "an undeclared title page resolves to no ground"
    ((designOf "\\theme{default}").titlepage.isNone)
  let both := designOf ("\\theme{default}\\palette{ titlepagebg = #101822, " ++
    "titlepagefg = #F4F6F8 }")
  t "a declared title-page pair resolves to exactly the declared colours"
    (both.titlepage == some { fg := { r := 0xF4, g := 0xF6, b := 0xF8 },
                              bg := { r := 0x10, g := 0x18, b := 0x22 } })
  let half := designOf "\\palette{ bg = #FFFFFF, titlepagebg = #101822 }"
  t "a half-declared title page inverts its ink from the page"
    (half.titlepage == some { fg := Ir.Color.white,
                              bg := { r := 0x10, g := 0x18, b := 0x22 } })
  t "a title-page ink with no ground declares no ground"
    ((designOf "\\palette{ titlepagefg = #F4F6F8 }").titlepage.isNone)
  let dim := "\\palette{ titlepagebg = #101822, titlepagefg = #3A4048 }"
  t "an illegible title-page pair warns at the stage's threshold"
    ((elabStr (deckOf dim "\\maketitle")).2.any fun d =>
      d.code == "W0345" && ((diagWords d).splitOn "3.00:1").length == 2 &&
        (d.message.splitOn "the title page").length == 2 && d.help.isNone)
  t "the warning names the declared ground, not an invented one"
    ((elabStr (deckOf dim "\\maketitle")).2.any fun d =>
      d.code == "W0345" && ((diagWords d).splitOn "#101822").length == 2)
  t "a title-page ink keeps its declared value"
    ((designOf dim).titlepage.any (·.fg == { r := 0x3A, g := 0x40, b := 0x48 }))
  t "an illegible title-page pair without a title page is silent"
    (!(warnCodes (deckOf dim "\\begin{frame}{T}x\\end{frame}")).contains "W0345")
  t "declared decorative intent silences the title-page pair"
    ((elabStr (deckOf (dim ++ "\\palette[decorative]{ titlepagefg = #3A4048 }")
      "\\maketitle")).2.all fun d => d.code != "W0345")
  t "an undeclared title page adds no pair to judge"
    ((elabStr (deckOf "\\theme{moloch}" "\\maketitle")).2.all
      fun d => d.code != "W0345")
  -- Quantified over `Theme.builtin`, so a bundle declaring a title-page ground is held without an edit.
  t "every shipped bundle's declared title-page pair is legible"
    (Theme.builtin.all fun th =>
      match (Ir.Design.ofPalette (Theme.apply th {}).palette).titlepage with
      | none => true
      | some p => Contrast.aaText ≤ Contrast.contrastMilli p.fg p.bg)

/-- Every role a built-in bundle declares is read, by a backend or as a content colour. -/
def roleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let contentColours := ["alert", "example"] ++
    SeedPalette.tierRoles.map fun r => (Ir.ColorRef.role r).key
  let pendingConsumer : List (String × String) := []
  for th in Theme.builtin do
    for (named, _) in (deckBundle th).entries do
      let role := named.key
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

/-- Every shipped bundle's role reaches the palette arm when invoked (`every_role_is_invocable`'s
executable half). -/
def roleInvocationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for th in Theme.builtin do
    -- What an article installs, each role a command spells; a key with a hyphen names its colour only.
    for (named, c) in (th.realize .documents).entries do
      let key := named.key
      if SeedPalette.derivedRoles.any (fun r => (Ir.ColorRef.role r).key == key) then continue
      unless key.all Char.isAlpha do continue
      let (doc, _) := elabStr ("\\documentclass{article}\\theme{" ++ th.name ++
        s!"}\\begin\{document}\\{key}\{x}\\end\{document}")
      t s!"role '{key}' of '{th.name}' is invocable"
        (match doc.body with
         | #[.para #[.colored c' (some n) inner]] =>
           n.key == key && Ir.plainText inner == "x" && c' == c
         | _ => false)
  let (qDoc, qDs) := elabStr ("\\documentclass{article}\\palette{ quiet = #123456 }" ++
    "\\begin{document}\\quiet{x}\\end{document}")
  t "role page source clean" qDs.isEmpty
  let qPage := (HtmlDoc.emit {} qDoc).1
  t "a role use references its token on the page"
    ((qPage.splitOn "color: var(--ltx-c-quiet, #123456)").length == 2)
  let qCss := treeCssList "" (HtmlDoc.emitTree {} qDoc).1.toList
  t "the page declares the token the use references"
    ((sheetRules qCss).toList.any (fun (conds, sel, decls) => conds.isEmpty && sel == ":root" &&
        (cssDecls decls).lookup "--ltx-c-quiet" == some "#123456") &&
     schemeRead (schemeRoot qCss .light).2 (schemeRoot qCss .light).1 "var(--ltx-c-quiet)" ==
       "#123456")

/-- W0342 names a definition shadowing a palette role, judged against the final palette. -/
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

/-- A repeated setting composes predictably: maps merge, scalars replace, and a conflicting scalar
repeat is named (W0343). -/
def composeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (pre : String) : String := dvDoc pre "x"
  let deck (pre body : String) : String := dvDeck (pre ++ "\n") body
  let w0343 (s : String) : Bool := (warnCodes s).contains "W0343"

  let (fDoc, _) := elabStr
    (wrap "\\fonts{ body.bold = \"First Face\" }\n\\fonts{ body.bold = \"Second Face\" }\n")
  t "a redeclared variant face resolves to the second"
    (fDoc.fonts.faceFor 0 700 false == some "Second Face")
  t "a redeclared variant face keeps one entry" (fDoc.fonts.faces.size == 1)

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

  let (kDoc, _) := elabStr (wrap "\\lhead{First}\n\\lhead{Second}\n")
  let kText := Ir.plainText (kDoc.head.getD #[])
  t "a repeated fancyhdr field is redefined, not concatenated"
    ((kText.splitOn "Second").length == 2 && (kText.splitOn "First").length == 1)

  let (pDoc, _) := elabStr (wrap "\\page{ parskip = 12pt }\n")
  let (bDoc, _) := elabStr (wrap "")
  t "a rhythm-only page block keeps the Bringhurst margin"
    (pDoc.page.hmargin == bDoc.page.hmargin &&
     pDoc.page.hmargin == (pDoc.page.width - Ir.articleTextBlock) / 2)
  let (hDoc, _) := elabStr (wrap "\\page{ hmargin = 1in }\n")
  t "declared geometry keeps every value it named"
    (hDoc.page.hmargin == Dim.inch 1)

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
  t "a document override after a theme never warns"
    (!w0343 (deck "\\theme{moloch}\n\\chrome{ footer = { left = \\sectiontitle } }" frame))


/-- One section per frame, the `frames_sections` census: the HTML has one `section` per frame and
the PDF that plus its step pages. -/
def deckStepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169
    ("\\theme{moloch}\\palette{ covered = 31\\% }\\chrome{ footer = { left = \\sectiontitle } }" ++
      "\\title{T}\\author{A}")
    ("\\maketitle\n\\section{S}\n" ++
     "\\begin{frame}{Steps}\n\\label{fr:steps}first\n\n\\pause\n" ++
     "\\alert{second}\n\n\\pause\nthird\n\\end{frame}\n" ++
     "\\begin{frame}{Plain}\nd\n\\end{frame}"))
  t "step deck elaborates clean" (ds.all fun d => d.severity == .note || reportedContrast d)
  let out := layoutOf oneFace doc
  let (html, _) := HtmlDoc.emit {} doc
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let snapCount := (elemAttrsList (fun _ => true) #[] body.toList).filter
    (fun (_, attrs) => attrs.contains ("data-snap", "")) |>.size
  let count (s : String) : Nat := ((stepCssResolved html).splitOn s).length - 1
  let slideSections := count "<section class=\"slide\""
    + count "<section class=\"slide titlebar\""
    + count "<section class=\"slide standout\""
    + count "<section class=\"slide title-page\""
  let frames := doc.body.foldl (fun n b => match b with
    | Ir.Block.frame _ _ _ _ _ => n + 1
    | _ => n) 0
  let stepDup := doc.body.foldl (fun n b => n + (Ir.frameSteps b - 1)) 0
  t "frames_sections: one section per frame, the PDF's page count less step duplicates"
    (slideSections == frames &&
     slideSections + stepDup + count "<section class=\"section-page\"" == out.pages.size)
  let classTokens := (attrValuesOf (fun _ => true) "class" (Html.elem "body" body #[])).map
    (·.splitOn " ")
  t "every step is visible and carries its index, nothing covered or hidden"
    ((classTokens.filter (·.contains "step")).size == 2 &&
     (classTokens.filter (·.contains "covered")).size == 0 &&
     count "--step: 2" == 1 && count "--step: 3" == 1 &&
     count " hidden=\"hidden\"" == 0)
  t "the label anchor has its single site"
    ((html.splitOn s!"id=\"{Ir.labelAnchor "fr:steps"}\"").length == 2)
  t "only the stepped frame rides a track; every page carries the snap door"
    (count "class=\"slide-track\"" == 1 && count "class=\"snap\"" == 3 &&
     count "--steps: 3" == 1 && count "--steps: 1" == 0 &&
     count "id=\"steps-1\"" == 1 && count "id=\"steps-2\"" == 1 &&
     count "id=\"steps-3\"" == 1 &&
     snapCount == 6)
  t "frame anchors keep unique ids, on the track or the section"
    (count "id=\"steps\"" == 1 && count "id=\"plain\" data-snap" == 1)
  t "no step control ships: the constant script is the navigation"
    (count "step-nav" == 0 && count "cluster" == 0 &&
     count "<script" == 1 &&
     count "document.querySelectorAll(\"[data-snap]\")" == 1)
  let (cdoc, _) := elabStr (deck169 "\\title{T}\\author{A}"
    ("\\begin{frame}{Steps}\na\n\n\\pause\nb\n\\end{frame}\n" ++
     "\\begin{frame}{Steps 1}\nd\n\\end{frame}"))
  let (chtml, cds) := HtmlDoc.emit {} cdoc
  t "a frame slug colliding with a step anchor is renamed and warned"
    (cds.any (·.code == "W0327") &&
     (chtml.splitOn "id=\"steps-1\"").length - 1 == 1 &&
     (chtml.splitOn "id=\"steps-1-2\"").length - 1 == 1)
  t "the uncover rides the frame's view timeline between snap points"
    (count "view-timeline: --frame x" == 1 &&
     count "animation-timeline: --frame, --frame;" == 2 &&
     count (".step.step-end:not([data-step=\"1\"]) { animation: ltx-uncover linear both, " ++
       "ltx-recover linear forwards, ltx-unhide linear both, ltx-rehide linear forwards; " ++
       "animation-timeline: --frame, --frame, --frame, --frame;") == 1 &&
     count ".step:not([data-step=\"1\"])" == 3 &&
     count ("animation-range: contain calc((var(--step) - 2) / (var(--steps) - 1) * 100%) " ++
       "contain calc((var(--step) - 1) / (var(--steps) - 1) * 100%)") == 2)
  t "the stage is sticky over its spacers, snap on the door only"
    (count ".slide-track > section.slide { position: sticky; left: 0; margin-right: -100vw; }" == 1 &&
     count ".snap { flex: 0 0 100vw; height: 100dvh; }" == 1 &&
     count "[data-snap] { scroll-snap-align: start; scroll-snap-stop: always; }" == 1 &&
     count "ltx-push" == 0)
  t "the covered from-state has its explicit active endpoint, a fade alone"
    (count "@keyframes ltx-uncover { to { opacity: 100% } from { opacity: 31%; } }" == 1)
  t s!"no step keyframe moves content: each fades opacity alone or reaches visibility alone \
({stepAnimations html})"
    (stepAnimations html == ["ltx-uncover", "ltx-unhide", "ltx-recover", "ltx-rehide"] &&
      stepsStandStill html && count "motiondistance" == 0)
  t "at a covered share a pending step stays in reach, its reveal's visibility its parent's"
    (count "@keyframes ltx-unhide { to { visibility: inherit } from { visibility: inherit; } }" == 1 &&
      !stepsFadeFromNothing html && !pendingStepsOutOfReach html)
  t "no view(): the floor covers only under script and uncovers by data-snapped"
    (count ("@supports not (animation-timeline: view()) {\n" ++
       "html[data-deck-script] .step:not([data-step=\"1\"]) { opacity: 31%; visibility: inherit; }")
       == 1 &&
     count (".slide-track[data-snapped=\"2\"] " ++
       ":is(.step[data-step=\"2\"]) { opacity: 100%; visibility: inherit; }") == 1 &&
     count (".slide-track[data-snapped=\"3\"] " ++
       ":is(.step[data-step=\"2\"], .step[data-step=\"3\"]) { opacity: 100%; visibility: inherit; }")
       == 1 &&
     count ".slide-track { scroll-snap-align: start; scroll-snap-stop: always; }" == 2 &&
     count ".slide-track > section.slide { scroll-snap-align: start;" == 0)
  t "reduced motion is the plain row at full colour, one page per frame"
    (count ".step { opacity: 100%; animation: none; }" == 1 &&
     count ("html[data-deck-script] .step:not([data-step=\"1\"]) { opacity: 100%; " ++
       "visibility: inherit; animation: none; }") == 1 &&
     count ".slide-track { width: 100vw; flex: 0 0 100vw; }" == 1)
  t "print shows every step uncovered on its stage's sheet, spacers hidden"
    (count ".snap { display: none; }" == 3 &&
     count "section.slide, section.section-page { break-after: page;" == 1 &&
     count ".step { opacity: 100%; }" == 1 &&
     (((html.splitOn "@media print").drop 1).all fun s =>
      ((((s.splitOn "\n}\n").headD "").splitOn "ltx-uncover").length == 1)))

/-- Every corpus deck's steps fade in and out where they stand, at their share or from nothing. -/
def deckStillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut stepped := 0
  for name in goldenNames do
    let (doc, _) ← goldenDoc name
    if doc.docClass != .slides then continue
    let (html, _) := HtmlDoc.emit {} doc
    if !(stepAnimations html).isEmpty then stepped := stepped + 1
    check ref s!"still steps: {name}'s step keyframes set opacity alone ({stepAnimations html})"
      (stepsStandStill html)
  check ref s!"still steps: the corpus ships stepped decks ({stepped})" (0 < stepped)

/-- A range's end is honoured in both artifacts: `\uncover<2-3>` is pending on steps 1 and 4. -/
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
  t "the HTML rules cover the range exactly where the handout page does"
    ((List.range 4).all fun i =>
      HtmlDoc.htmlStepPendingAt 4 2 (some 3) (i + 1) == pageCovered c i "Middle only.")
  t "the declared end rides its own carrier in the markup"
    (has "<span class=\"step-end\" data-step-last=\"3\" style=\"--step-last: 3\">" &&
     (let (_, tree, _) := HtmlDoc.emitTree {} doc
      (elemAttrsList (· == "span") #[] tree.toList).any fun (_, attrs) =>
        attrs.contains ("class", "step") && attrs.contains ("data-step", "2") &&
        attrs.contains ("data-step-last", "3") && attrs.contains ("style", "--step: 2") &&
        attrs.contains ("data-steps", "2 3")))
  t s!"the range's steps fade in and out where they stand ({stepAnimations html})"
    (stepAnimations html == ["ltx-uncover", "ltx-unhide", "ltx-recover", "ltx-rehide"] &&
      stepsStandStill html)
  t "the end carrier dims again past the range, on both paths"
    (has "@keyframes ltx-recover { from { opacity: 100% } to { opacity: " &&
     has (".step-end { animation: ltx-recover linear both, ltx-rehide linear forwards; " ++
       "animation-timeline: --frame, --frame;") &&
     has ("html[data-deck-script] .slide-track[data-snapped=\"4\"] " ++
       ":is(.step-end[data-step-last=\"1\"], .step-end[data-step-last=\"2\"], " ++
       ".step-end[data-step-last=\"3\"]) { opacity: "))
  t "the floor recover is script-gated, as the covered default is"
    (((html.splitOn "\n").filter fun l =>
        hasStr l ".step-end[data-step-last=\"" && !hasStr l "opacity: 100%").all fun l =>
      hasStr l "html[data-deck-script]")

/-- Overlay alternation in HTML shows exactly one group per step, selected as the PDF page
selects. -/
def deckAltChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (deck169Frame
    "\\alt<2-3>{Middle words.}{Outer words.}\n\n\\uncover<4>{Fourth only.}")
  t "alternation deck elaborates clean" (ds.all fun d => d.severity == .note)
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let (html, _) := HtmlDoc.emit {} doc
  let has := hasStr html
  t "the handout inks exactly one alternative per step page"
    (c.size == 4 &&
     (List.range 4).all fun i =>
       let first := Ir.altShowsFirst 2 (some 3) (i + 1)
       pageOccurs c i "Outer words." == (if first then 1 else 0) &&
         pageOccurs c i "Middle words." == (if first then 0 else 1))
  t "the HTML shows one alternative and declares both once each"
    (treeShownOccurs body "Outer words." == 1 &&
     treeShownOccurs body "Middle words." == 0 &&
     treeOccurs body "Outer words." == 1 &&
     treeOccurs body "Middle words." == 1)
  t "each group rides its own wrapper, with the range and its side"
    (has ("<span class=\"alt alt-pending\" data-step=\"2\" data-step-last=\"3\">" ++
       "Outer words.</span>") &&
     has ("<span class=\"alt alt-crisp\" data-step=\"2\" data-step-last=\"3\" " ++
       "hidden=\"hidden\">Middle words.</span>"))
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
  t "the two mechanisms stay apart: alternation never dims, covering never hides"
    ((((html.splitOn "\n").filter fun l =>
         hasStr l ".alt-crisp" || hasStr l ".alt-pending").all fun l =>
       !hasStr l "opacity") &&
     (((html.splitOn "\n").filter fun l =>
         hasStr l ".step-end[" || hasStr l ".step[data-step").all fun l =>
       !hasStr l "display"))
  t "alternation adds no script and degrades to step one's reading"
    (((html.splitOn "<script").length - 1) == 1 &&
     hasStr html HtmlDoc.deckScript &&
     has "hidden=\"hidden\">Middle words.</span>")

/-- Beamer's `{overprint}` is an alternation: one reading per step page, as `Ir.altShowsFirst`
names. -/
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
  t "three alternatives give the frame three step pages" (c.size == 3)
  t "each step page inks exactly one of the three readings"
    ((List.range 3).all fun i =>
      (readings.map fun r => pageOccurs c i r) == (List.range 3).map fun j =>
        if i == j then 1 else 0)
  t "the page that inks an item is the page inside that item's spec"
    ((List.range 3).all fun j =>
      (List.range 3).all fun i =>
        (pageOccurs c i (readings.getD j "") == 1) ==
          !Ir.stepPending (j + 1) (some (j + 1)) (i + 1))
  t "the outer alternation inks item one exactly when altShowsFirst says"
    ((List.range 3).all fun i =>
      (pageOccurs c i (readings.getD 0 "") == 1) == Ir.altShowsFirst 1 (some 1) (i + 1))
  t "the HTML tree declares each reading once and shows exactly one"
    (readings.all (fun r => treeOccurs body r == 1) &&
     ((readings.map fun r => treeShownOccurs body r) == [1, 0, 0]))
  -- The chain gives priority to the item written last, as beamer's overlay area does.
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
  t "no alternation group of an open-range overprint is unreachable"
    (Ir.altUnreachable odoc == 0)
  t "nor of a point-spec overprint" (Ir.altUnreachable doc == 0)
  for n in goldenNames do
    let (cdoc, _) ← goldenDoc n
    t s!"corpus {n}: every alternation reaches both of its groups"
      (Ir.altUnreachable cdoc == 0)

/-- An overprint the rewrite refuses degrades to one reading with its loss named. -/
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

/-- An unnumberable overprint item costs no numberable item, standing on the steps no other item
claims. -/
def deckOverprintUnnumberableChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let readings := ["Alpha reading.", "Bravo reading.", "Charlie reading."]
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
  t "refusing one item leaves the numbered items their step pages"
    (c.size == 3)
  t "with one item refused, each step page inks exactly one of the three readings"
    ((List.range 3).all fun i =>
      (readings.map fun r => pageOccurs c i r) == (List.range 3).map fun j =>
        if i == j then 1 else 0)
  t "a numbered item inks the page inside its own spec"
    ([1, 2].all fun j =>
      (List.range 3).all fun i =>
        (pageOccurs c i (readings.getD j "") == 1) ==
          !Ir.stepPending (j + 1) (some (j + 1)) (i + 1))
  t "the unnumberable item inks the one step no numbered item claims"
    ((List.range 3).all fun i =>
      (pageOccurs c i (readings.getD 0 "") == 1) ==
        (Ir.stepPending 2 (some 2) (i + 1) && Ir.stepPending 3 (some 3) (i + 1)))
  let (_, body, _) := HtmlDoc.emitTree {} doc
  t "the HTML tree declares all three readings and shows exactly one"
    (readings.all (fun r => treeOccurs body r == 1) &&
     ((readings.map fun r => treeShownOccurs body r).foldl (· + ·) 0 == 1))
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
  let (oDoc, oDs) := elabStr (deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Delta reading.\n\\end{overprint}")
  let oc := censusOf (coveredColorsOf oDoc) (layoutOf oneFace oDoc)
  t "a lone unnumberable item ships its reading once, on one page"
    (((oDs.filter (·.severity != .note)).map (·.code)) == #["W0105"] &&
     oc.size == 1 && pageOccurs oc 0 "Delta reading." == 1)

/-- A once-per-document diagnostic fires once for the document, whichever pass meets its cause. -/
def deckOverlayWarnOnceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bothCauses := deck169Body
    "\\begin{frame}\n\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}\n\\end{frame}\n\
\\begin{frame}\n\\alt<+->{First alternative.}{Second alternative.}\n\\end{frame}"
  t "an unnumberable overprint item and \\alt in one deck say W0105 once"
    ((warnCodes bothCauses).filter (· == "W0105") == ["W0105"])
  let reversed := deck169Body
    "\\begin{frame}\n\\alt<+->{First alternative.}{Second alternative.}\n\\end{frame}\n\
\\begin{frame}\n\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}\n\\end{frame}"
  t "the pass order does not decide how often the document hears it"
    ((warnCodes reversed).filter (· == "W0105") == ["W0105"])
  let overprintOnly := deck169Frame
    "\\begin{overprint}\n\\onslide<+-> Alpha reading.\n\
\\onslide<2> Bravo reading.\n\\end{overprint}"
  t "the overprint cause alone still says it"
    ((warnCodes overprintOnly).filter (· == "W0105") == ["W0105"])
  let altOnly := deck169Frame "\\alt<+->{First alternative.}{Second alternative.}"
  t "the \\alt cause alone still says it"
    ((warnCodes altOnly).filter (· == "W0105") == ["W0105"])

/-- The deck's logo is frame furniture in both artifacts, on exactly the frames its declaration
covers (`Ir.logoInForce`). -/
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
  t "the strip is decorative furniture in beamer's default corner"
    (hasStr html "class=\"slide-logo\" role=\"presentation\" aria-hidden=\"true\"" &&
     hasStr html "justify-content: flex-end")
  let stageBlock :=
    (((html.splitOn "@media screen, print {").getD 1 "").splitOn "@media screen {").headD ""
  t "the stylesheet pins the strip to the stage's bottom band, on paper too"
    (hasStr stageBlock (".slide-logo { position: absolute; bottom: var(--safearea, 6vmin); " ++
       "left: var(--safearea, 6vmin); right: var(--safearea, 6vmin); display: flex; }"))
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
  let (idoc, _) := elabStr (deck169 "\\theme{default}"
    ("\\logo{\\includegraphics[totalheight=.25\\textheight]{lg.png}}\n" ++
     "\\begin{frame}{T}\n\\includegraphics{pic.png}\n\\end{frame}"))
  let (ihtml, _) := HtmlDoc.emit {} idoc
  t "a logo ships an empty alt the no-alt census skips; content images are named"
    (hasStr ihtml "src=\"lg.png\" alt " &&
     Ir.imagesSansAlt idoc == #["pic.png"])
  let (adoc, _) := elabStr (dvDoc "\\logo{L}\n" "x")
  let (_, ads) := HtmlDoc.emit {} adoc
  t "an article's logo is still a named drop"
    (ads.any (·.code == "W0007"))
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
        | .image _ _ _ _ => true
        | _ => false
    t s!"{th.name}: the logo is requested once, its box on exactly the declared frame's page"
      (Ir.imageRefs ldoc == #["nope/absent.png"] &&
       lout.pages.size == 3 && lout.pages.map boxOn == #[false, true, false])

/-- The gemini poster bundle resolves by name, installs nothing inert, and its titled blocks read
the lineage's bars. -/
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


/-- A titled block's title is judged on the ground the pages ship it on. -/
def titledGroundChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let surface := screenColor .light .page
  t "the HTML page an undeclared document ships is the printed page"
    (surface == Ir.Color.white)
  let titled (grey : Ir.Color) : Ir.Doc :=
    { palette := ({} : Ir.Palette).declareKey "blocktitlefg" grey
      body := #[.titled .block #[.text "Title"] #[.para #[.text "body text"]]] }
  let passing : Ir.Color := { r := 0x75, g := 0x75, b := 0x75 }
  let grey : Ir.Color := { r := 0x80, g := 0x80, b := 0x80 }
  t "a title legible on the page both artifacts ship draws nothing"
    (Contrast.docDiags (titled passing)).isEmpty
  let doc := titled grey
  let out := layoutOf oneFace doc
  let runs := out.pages.flatMap fun p => p.lines.flatMap fun l =>
    l.segs.filterMap fun seg => match seg with
      | .run _ color _ _ glyphs _ _ _ _ ground _ =>
        if glyphs.isEmpty then none else some (color, ground)
      | _ => none
  t "the unbarred title run ships on the undeclared page"
    (runs.any fun (color, ground) => color == grey && ground == none)
  t "the undeclared page paints no fill"
    (out.pages.all fun p => p.fills.isEmpty)
  let ds := Contrast.docDiags doc
  t "the judge speaks for the shipped titled pair" (!ds.isEmpty)
  t "the judge names the ground the page ships"
    (ds.any fun d => d.code == "W0345" && hasStr (diagWords d) "#FFFFFF")
  let barPal := (doc.palette.declareKey "blocktitlebg" { r := 0xEE, g := 0xEE, b := 0xEE })
  let barDoc := { doc with palette := barPal }
  let barOut := layoutOf oneFace barDoc
  t "a declared bar is the title's ground"
    (barOut.pages.any fun p => p.lines.any fun l => l.segs.any fun seg =>
      match seg with
      | .run _ color _ _ glyphs _ _ _ _ ground _ =>
        !glyphs.isEmpty && color == grey &&
          ground == some { r := 0xEE, g := 0xEE, b := 0xEE }
      | _ => false)
  t "the judge grounds the barred title on the bar"
    ((Contrast.docDiags barDoc).any fun d => hasStr (diagWords d) "#EEEEEE")


/-- A legible document draws no contrast report and a failing one does, over every family the report
reads. -/
def docReportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ink : Ir.Color := { r := 0x11, g := 0x11, b := 0x11 }
  let bar : Ir.Color := { r := 0x20, g := 0x30, b := 0x40 }
  let onBar : Ir.Color := { r := 0xF8, g := 0xF8, b := 0xF8 }
  let legible : Ir.Palette :=
    ((((((({} : Ir.Palette).declareKey "fg" ink).declareKey "bg" Ir.Color.white).declareKey
      "quiet" { r := 0x44, g := 0x44, b := 0x44 }).declareKey
      "frametitlebg" bar).declareKey "frametitlefg" onBar).declareKey
      "blocktitlefg" ink).declareKey "muted" { r := 0x40, g := 0x40, b := 0x40 }
  let epoch : Ir.Palette :=
    ((({} : Ir.Palette).declareKey "fg" ink).declareKey "bg" Ir.Color.white).declareKey
      "quiet" { r := 0x44, g := 0x44, b := 0x44 }
  let body : Array Ir.Block :=
    #[.para #[.colored { r := 0x44, g := 0x44, b := 0x44 } (some (.color "quiet")) #[.text "role ink"]],
      .para #[.colored ink none #[.text "anonymous ink"]],
      .titled .block #[.text "Panel"] #[.para #[.text "panel body"]],
      .frame #[.text "Frame title"] false .center false #[.para #[.text "frame body"]],
      .frame #[.text "Standout"] true .center false #[.para #[.text "standout body"]],
      .para #[.step 2 none #[.text "pending"]],
      .setPalette epoch,
      .para #[.colored ink (some (.role .ink)) #[.text "after the epoch"]]]
  let doc : Ir.Doc :=
    { palette := legible, body := body
      head := some #[.text "running head"], foot := some #[.text "running foot"] }
  let ds := Contrast.docDiags doc
  t "a legible document's every judged pair passes"
    ((Contrast.judgedPairs doc).all fun p =>
      Contrast.aaText ≤ Contrast.contrastMilli p.1 p.2)
  t "a legible document draws no pairing warning"
    (ds.all fun d => d.code != "W0315" && d.code != "W0345")
  let pale : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  let failing := { doc with
    palette := legible.declareKey "quiet" pale
    body := #[.para #[.colored pale (some (.color "quiet")) #[.text "pale role ink"]]] }
  let fDs := Contrast.docDiags failing
  t "a failing pair is judged, not passed over"
    (!(Contrast.judgedPairs failing).all fun p =>
      Contrast.aaText ≤ Contrast.contrastMilli p.1 p.2)
  t "a failing document says so, once"
    ((fDs.filter fun d => d.code == "W0315" && d.severity == .warning).size == 1)
