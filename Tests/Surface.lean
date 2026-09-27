import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- **The extent a node registers, and the separation it buys.** The site
`Ir.Pic.nodeExtent` is the one answer to "how far does this node reach",
and the defect it closes is that the answer used to be the declared minimum
alone — zero for a node body that declared none, so `right =of` parted node
*centres* and a row of labels landed on top of one another.

The measurement is a stated invention here, not this host's face: the
statements (`nodeExtent_covers`, `nodeExtent_separates`) are quantified over
every `Ir.Pic.LabelMetric`, so what a test adds is the site's arithmetic on
real numbers — and a fixture that measured with an installed font would be
pinning the font, not the site. -/
def nodeExtentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- An invented face: every character 6 pt wide, ink 7 pt over the
  -- baseline and 2 pt under it, scaled per mille as a real metric is.
  let metric : Ir.Pic.LabelMetric := fun content scale =>
    let n := (Ir.plainText content).length
    { w := Dim.pt 6 * n * scale / 1000
      height := Dim.pt 7 * scale / 1000
      depth := Dim.pt 2 * scale / 1000 }
  let label (text : String) : Array Ir.Inline := #[.text text]
  let extent (text : String) (declA declB : Dim.Sp) : Dim.Sp × Dim.Sp :=
    Ir.Pic.nodeExtent metric (label text) 1000 .center declA declB
  -- The input the placement was given before there was a face to ask.
  t "a node body with no declared minimum still registers an extent"
    (extent "Placeholder" 0 0 == (Dim.pt 33, Dim.pt 9 / 2))
  -- The declared minimum is a floor, never a ceiling (pgf's own reading:
  -- extent = max(minimum, text extent)).
  t "a declared minimum wider than the text keeps its own extent"
    ((extent "Tiny" (Dim.pt 40) (Dim.pt 30)).1 == Dim.pt 40)
  t "a declared minimum narrower than the text loses to the text"
    ((extent "A Very Wide Label Indeed" (Dim.pt 10) 0).1 == Dim.pt 72)
  -- An anchored label is not symmetric about its anchor: a `west` label
  -- puts its whole width to the right, so a centred extent must hold the
  -- whole of it, not half.
  t "an anchored label asks for its whole width, not half of it"
    ((Ir.Pic.nodeExtent metric (label "Placeholder") 1000 .west 0 0).1 == Dim.pt 66)
  -- The scale a node's `font=` sets reaches the measurement.
  t "a smaller label asks for less"
    ((extent "Placeholder" 0 0).1 > (Ir.Pic.nodeExtent metric (label "Placeholder") 700 .center 0 0).1)
  -- **The fact the site exists for**, on numbers rather than in general:
  -- two nodes whose centres stand one separation plus both half-extents
  -- apart — which is what `right =of` computes — set label ink that does
  -- not overlap. With the extents at zero, as they were, the same
  -- arithmetic puts the second label's ink 47 pt left of where the first
  -- one's ends.
  let inkRight (x : Dim.Sp) (text : String) : Dim.Sp :=
    (Ir.Pic.labelInkBox x 0 .center (metric (label text) 1000)).2.1
  let inkLeft (x : Dim.Sp) (text : String) : Dim.Sp :=
    (Ir.Pic.labelInkBox x 0 .center (metric (label text) 1000)).1.1
  let sep := Dim.mm 10
  let placed (declA : Dim.Sp) : Dim.Sp :=
    sep + (extent "Widest Placeholder" declA 0).1 + (extent "Second Placeholder" declA 0).1
  t "two measured nodes one separation apart do not overlap"
    (inkRight 0 "Widest Placeholder" < inkLeft (placed 0) "Second Placeholder")
  t "the gap the placement leaves is the separation the document declared"
    (inkLeft (placed 0) "Second Placeholder" - inkRight 0 "Widest Placeholder" == sep)
  -- The defect, as the number it was: with no extent registered, the
  -- separation is measured from the anchors and the text overlaps.
  let unmeasured : Dim.Sp := sep
  t "with no extent registered the same arithmetic overlaps the text"
    (inkLeft unmeasured "Second Placeholder" < inkRight 0 "Widest Placeholder")

/-- `\newenvironment` wrappers: the definition binds, the halves contribute
around the content, and nothing warns. Its own function: `main` is one `do`
block and its elaboration budget is spent. -/
def wrapperChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (defs body : String) : String :=
    "\\documentclass{article}\n" ++ defs ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (doc, ds) := elabStr (pre
    "\\newenvironment{labeled}[1]{\\textbf{#1:}}{\\emph{(end)}}"
    "\\begin{labeled}{First} body \\end{labeled}")
  t "newenvironment defines a wrapper, warning nothing"
    (ds.all (·.severity == .note))
  t "wrapper argument binds and both halves contribute"
    (doc.body.size == 1 && (doc.body[0]?.map fun b => match b with
      | .para content =>
        Ir.plainText content == "First: body (end)" &&
        content.any (fun x => x == .styled .bold #[.text "First:"]) &&
        content.any (fun x => x == .styled .emph #[.text "(end)"])
      | _ => false) == some true)  -- The optional-argument spelling binds like \newcommand's.
  let (opt, optDs) := elabStr (pre
    "\\newenvironment{tag}[2][?]{\\textbf{#1/#2}}{}"
    "\\begin{tag}[a]{b} body\\end{tag}")
  t "wrapper optional argument binds" (optDs.all (·.severity == .note) &&
    (opt.body[0]?.map fun b => match b with
      | .para content => Ir.plainText content == "a/b body"
      | _ => false) == some true)
  -- \renewenvironment redefines: the last definition wins.
  let (re, _) := elabStr (pre
    "\\newenvironment{aside}{old:}{}\\renewenvironment{aside}{new:}{}"
    "\\begin{aside} body\\end{aside}")
  t "renewenvironment wins"
    ((re.body[0]?.map fun b => match b with
      | .para content => Ir.plainText content == "new: body"
      | _ => false) == some true)
  -- A built-in environment cannot be redefined, and says so.
  t "a built-in environment cannot be redefined"
    (warnCodes (pre "\\newenvironment{itemize}{x}{y}" "z") == ["W0303"])
  -- A wrapper whose content is block-shaped keeps its blocks.
  let (blk, blkDs) := elabStr (pre
    "\\newenvironment{boxed}{}{}"
    "\\begin{boxed}first\n\nsecond\\end{boxed}")
  t "wrapper around block content keeps the blocks"
    (blkDs.all (·.severity == .note) && blk.body.size == 2)

/-- Units and control-name lexing: TeX's `true` units, the didot pair, and
`@` as a name character. -/
def unitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  -- TeX's true units are unscaled-by-\mag spellings of their plain
  -- counterparts (TeXbook ch. 10); with no magnification they are equal.
  t "truein is in: a \\setlength in true units declares the token"
    (let (doc, ds) := elabStr (pre "\\newlength{\\a}\\setlength{\\a}{1.75truein}\
\\newlength{\\b}\\setlength{\\b}{1.75in}")
     ds.all (·.severity != .error) &&
       (doc.tokens.find? "a").isSome && doc.tokens.find? "a" == doc.tokens.find? "b")
  t "truebp scales a decimal exactly like bp"
    (Decl.parseLength "0.5truebp" == Decl.parseLength "0.5bp")
  -- The didot and cicero keep TeX's own relation: 1 cc = 12 dd.
  t "a cicero is twelve didots"
    ((Decl.parseLength "1cc").isSome &&
      Decl.parseLength "12dd" == Decl.parseLength "1cc")
  -- `@` is a control-name character always: `\vqb@bp` is one (unknown)
  -- name, never `\vqb` followed by stray text `@bp`.
  t "@ in a control name lexes as one name"
    (toks "\\vqb@bp" == [.ctrl "vqb@bp"])
  t "an unknown @-name is one diagnostic naming it, with no stray text"
    (let (doc, ds) := elabStr "x \\vqb@bp y"
     ds.any (fun d => d.code == "W0301" && (d.message.splitOn "vqb@bp").length > 1) &&
       doc.body == #[.para #[.text "x y"]])
  -- LaTeX's starred forms: the star means "no \par in the arguments"
  -- (definers) or "survives a page break" (\vspace*) — neither modelled,
  -- so the star is consumed with its command, never left as content.
  t "newcommand* defines like newcommand"
    ((elabStr "\\newcommand*{\\hi}{world}\\begin{document}\\hi\\end{document}").1.body
      == #[.para #[.text "world"]])
  t "renewcommand* redefines like renewcommand"
    ((elabStr "\\newcommand{\\x}{a}\\renewcommand*{\\x}{b}\\begin{document}\\x\\end{document}").1.body
      == #[.para #[.text "b"]])
  t "DeclareRobustCommand* defines like newcommand"
    ((elabStr "\\DeclareRobustCommand*{\\x}{a}\\begin{document}\\x\\end{document}").1.body
      == #[.para #[.text "a"]])
  t "vspace* becomes the same block as vspace"
    ((elabStr "\\begin{document}a\\vspace*{4pt}\nb\\end{document}").1.body ==
     (elabStr "\\begin{document}a\\vspace{4pt}\nb\\end{document}").1.body)
  -- The recovery invariant: best-effort recovery never turns a warning
  -- into an error. An unknown starred command in the preamble is one
  -- W0301; its star and arguments go with it, never surviving as content
  -- that E0313 then rejects.
  t "an unknown starred command in the preamble stays a warning"
    (let ds := (elabStr (pre "\\mystery*{a}{b}")).2
     ds.any (·.code == "W0301") && ds.all (·.severity != .error))
  t "an unknown starred command in the body keeps its argument text only"
    ((elabStr "\\begin{document}x \\mystery*{y} z\\end{document}").1.body ==
      #[.para #[.text "x y z"]])

/-- The length expression language: `\dimexpr`'s shape over declared
tokens — sums, differences, coefficients, parentheses — with eager
resolution, so absence is diagnosed and cycles are unrepresentable. -/
def exprChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  -- The chain the brief's card writes: sum of tokens, difference, TeX's
  -- coefficient form, and parentheses, all exact in sp.
  let (doc, ds) := elabStr (pre
    "\\tokens{ bleed = 9pt, safe = 9pt, w = 240pt, margin = bleed + safe, \
full = w + 2bleed, gap = bleed - 3pt, half = 0.5 * (bleed + safe) }")
  t "token arithmetic evaluates without errors" (ds.all (·.severity != .error))
  t "a + b is exact in sp"
    (doc.tokens.find? "margin" == some { width := .ofSp (Dim.pt 18) })
  t "a + 2b reads TeX's coefficient form"
    (doc.tokens.find? "full" == some { width := .ofSp (Dim.pt 258) })
  t "a - b subtracts exactly"
    (doc.tokens.find? "gap" == some { width := .ofSp (Dim.pt 6) })
  t "parentheses group before scaling"
    (doc.tokens.find? "half" == some { width := .ofSp (Dim.pt 9) })
  -- Precedence without parentheses: `*` and `/` bind tighter than `+` and
  -- `-`, on either side of the operator. Every row above parenthesizes, so
  -- the drain rule itself was unmeasured.
  t "multiplication and division bind tighter than addition"
    (let d := (elabStr (pre "\\tokens{ a = 4pt, l = a + 2 * a, r = 2 * a + a, \
d = a - a / 2 }")).1
     d.tokens.find? "l" == some { width := .ofSp (Dim.pt 12) } &&
       d.tokens.find? "r" == some { width := .ofSp (Dim.pt 12) } &&
       d.tokens.find? "d" == some { width := .ofSp (Dim.pt 2) })
  -- Absent is diagnosed, never defaulted: the unknown name appears in the
  -- message, and nothing resolves to zero.
  t "an unknown token in an expression is named"
    (let ds := (elabStr (pre "\\tokens{ a = b + 1pt }")).2
     ds.any fun d => d.code == "E0321" && (d.message.splitOn "'b' is not a declared token").length > 1)
  -- References resolve eagerly against what is declared so far, the
  -- \setlength{\x}{2\x} rule — so a would-be cycle is a forward
  -- reference, and a forward reference is diagnosed by name.
  t "a token cycle is a diagnosed forward reference, not a hang"
    (let ds := (elabStr (pre "\\tokens{ a = b + 1pt, b = a + 1pt }")).2
     ds.any fun d => d.code == "E0321" && (d.message.splitOn "'b'").length > 1)
  t "a self-reference reads the earlier value, as TeX's 2\\x does"
    ((elabStr (pre "\\tokens{ a = 4pt, a = 2a }")).1.tokens.find? "a"
      == some { width := .ofSp (Dim.pt 8) })
  t "a bare number in an expression needs a unit"
    (let ds := (elabStr (pre "\\tokens{ a = 3 + 2pt }")).2
     ds.any (·.code == "E0321"))
  t "expressions work through \\setlength's TeX spelling"
    (let (d2, ds2) := elabStr (pre
      "\\newlength{\\ca}\\setlength{\\ca}{4pt}\\newlength{\\cb}\
\\setlength{\\cb}{2pt}\\newlength{\\cm}\\setlength{\\cm}{\\ca+\\cb}\
\\newlength{\\ch}\\setlength{\\ch}{\\ca+2\\cb}")
     ds2.all (·.severity != .error) &&
       d2.tokens.find? "cm" == some { width := .ofSp (Dim.pt 6) } &&
       d2.tokens.find? "ch" == some { width := .ofSp (Dim.pt 8) })
  -- Division: calc's `/` on a length is TeX's \divide, truncation toward
  -- zero (TeXbook ch. 24) — the one rounding of the whole language. A
  -- parenthesized numeric subexpression is a scalar divisor.
  let (d3, ds3) := elabStr (pre
    "\\tokens{ bleed = 9pt, safe = 9pt, w = 240pt, q = (bleed + safe) / 2, \
r = w / 2.5, neg = 0pt - 3sp, negh = neg / 2 }")
  t "division by a numeric factor evaluates without errors"
    (ds3.all (·.severity != .error))
  t "a length divides by an integer"
    (d3.tokens.find? "q" == some { width := .ofSp (Dim.pt 9) })
  t "a length divides by a decimal"
    (d3.tokens.find? "r" == some { width := .ofSp (Dim.pt 96) })
  t "a negative length truncates toward zero, as TeX's \\divide does"
    (d3.tokens.find? "negh" == some { width := .ofSp (-1) })
  t "a parenthesized numeric divisor evaluates as a scalar (the beamerposter shape)"
    (let (d4, ds4) := elabStr (pre
      "\\newlength{\\cw}\\setlength{\\cw}{100pt}\\newlength{\\cb}\
\\setlength{\\cb}{24pt}\\newlength{\\sw}\\setlength{\\sw}{(\\cw - 3\\cb) / (3+1)}")
     ds4.all (·.severity != .error) &&
       d4.tokens.find? "sw" == some { width := .ofSp (Dim.pt 7) })
  t "division by zero is refused with a diagnostic, never a silent 0"
    (let (d5, ds5) := elabStr (pre "\\tokens{ a = 4pt, b = a / 0 }")
     d5.tokens.find? "b" == none &&
       ds5.any fun d => d.code == "E0321" &&
         (d.message.splitOn "division by zero").length > 1)
  t "a number divided by a length is refused"
    (let ds6 := (elabStr (pre "\\tokens{ a = 4pt, b = 8 / a }")).2
     ds6.any fun d => d.code == "E0321" && (d.message.splitOn "no meaning").length > 1)
  -- e-TeX's \dimexpr division rounds to nearest — different arithmetic,
  -- refused by name (E0375), never mis-rounded silently; plain division
  -- outside \dimexpr stays clean of it.
  t "\\dimexpr division is refused by name"
    (let ds7 := (elabStr (pre
      "\\newlength{\\x}\\setlength{\\x}{\\dimexpr\\textwidth/2\\relax}")).2
     ds7.any (·.code == "E0375"))
  t "native division does not fire the \\dimexpr refusal"
    (let ds8 := (elabStr (pre
      "\\newlength{\\y}\\setlength{\\y}{4pt}\\newlength{\\z}\\setlength{\\z}{\\y/2}")).2
     ds8.all (·.code != "E0375") && ds8.all (·.severity != .error))

/-- The run-in headings: `\paragraph`/`\subparagraph` are run-in in article
(clsguide §2.2; classes.dtx gives both a negative afterskip), so the title
joins its own text's paragraph — bold, an em quad after — and never makes a
display heading, keeping `heading_hierarchy`'s levels what they were. -/
def runinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (doc, ds) := elabStr (wrap "\\paragraph{Setup} The details follow.")
  t "a run-in heading sources clean" ds.isEmpty
  t "run-in title and text share one paragraph, an em quad between"
    (match doc.body[0]? with
     | some (Ir.Block.para xs) =>
       (match xs[0]? with
        | some (Ir.Inline.styled .bold ttl) => Ir.plainText ttl == "Setup"
        | _ => false) &&
       (Ir.plainText xs) == "Setup\u2003The details follow."
     | _ => false)
  let (doc2, ds2) := elabStr (wrap "\\subparagraph*{Aside} Runs in too.")
  t "a starred subparagraph runs in the same way"
    (ds2.isEmpty && (match doc2.body[0]? with
     | some (Ir.Block.para xs) => (Ir.plainText xs) == "Aside\u2003Runs in too."
     | _ => false))
  let (_, ds3) := elabStr (wrap "\\paragraph{A}[short] kept")
  t "a bracket after the title group is content, not an argument"
    (ds3.isEmpty)

/-- The abstract environment: its own titled block (article.cls §abstract —
`\small`, a centred bold `\abstractname`, quotation margins), a `<section>`
with a heading in HTML, so a reader's tooling can find it. -/
def abstractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{abstract} Invented summary text. \\end{abstract}\\end{document}")
  t "abstract sources clean" ds.isEmpty
  t "abstract elaborates to its own block"
    (match doc.body[0]? with
     | some (Ir.Block.abstract body) => !body.isEmpty
     | _ => false)
  let page := (HtmlDoc.emit {} doc).1
  t "HTML sets the abstract as a classed section with a centred heading"
    ((page.splitOn "class=\"abstract size-small\"").length == 2 &&
     (page.splitOn "<h2 style=\"text-align: center\">").length == 2 &&
     (page.splitOn "Abstract").length == 2)
  let md := MarkdownDoc.emit doc
  t "the markdown twin carries the heading and the body"
    ((md.splitOn "## Abstract").length == 2 &&
     (md.splitOn "Invented summary text.").length == 2)
  -- The heading follows the section heading: a reference, not a copy
  -- (`Ir.abstract_heading_follows_section` is the equation; these are its
  -- runtime instances), so a venue or theme that restyles sections
  -- carries the abstract heading with it.
  let (sDoc, _) := elabStr ("\\documentclass{article}" ++
    "\\style{section}{ font = {\\large\\bfseries} }" ++
    "\\begin{document}\\begin{abstract}Words.\\end{abstract}\\end{document}")
  t "the abstract heading derives the styled section's font, centred"
    ((Ir.abstractHeadingStyle sDoc.styles).font ==
      ((sDoc.styles.find? "section").bind (·.font)) &&
     (Ir.abstractHeadingStyle sDoc.styles).align == some "center")
  t "an explicit style abstract key wins over the derivation"
    ((Ir.abstractHeadingStyle (sDoc.styles.declare "abstract"
        { align := some "left" })).align == some "left")
  -- The venue's \renewenvironment{abstract}: refused (W0303, the
  -- protection code for a built-in environment), its declarative
  -- appearance read — \large\bf and \centerline land as the heading's
  -- style, in W0361's voice; \begin{quote} is the built-in's own shape
  -- and the \vskips the engine's rhythm, both stay refused.
  let (vDoc, vDs) := elabStr ("\\documentclass{article}" ++
    "\\renewenvironment{abstract}{\\vskip 0.1in\\centerline{\\large\\bf Abstract}" ++
    "\\vspace{1ex}\\begin{quote}}{\\par\\end{quote}\\vskip 1ex}" ++
    "\\begin{document}\\begin{abstract}Words.\\end{abstract}\\end{document}")
  t "a refused abstract redefinition says the built-in stands styled"
    (vDs.any fun d => d.code == "W0303" &&
      (d.message.splitOn "heading and body size style it").length > 1)
  t "the refused redefinition's large bold centreline lands on the heading"
    ((Ir.abstractHeadingStyle vDoc.styles).font ==
      some #[.styled (.size "large") #[.styled .bold #[]]] &&
     (Ir.abstractHeadingStyle vDoc.styles).align == some "center")

/-- Heading numbers: article numbers unstarred levels 1–3 in flow order
(classes.dtx §Sectioning), `\appendix` letters from A and restarts the
counter, starred forms neither number nor step, slides never number — and
a number never moves a section's HTML anchor, which reads the title text
alone. -/
def headingNumberChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let art (body : String) : Ir.Doc :=
    (elabStr ("\\documentclass{article}\\begin{document}\n" ++ body ++ "\n\\end{document}")).1
  let nums (doc : Ir.Doc) : List (Option String) :=
    doc.body.toList.filterMap fun b => match b with
      | .section _ _ n _ => some n
      | _ => none
  t "article numbers unstarred headings in flow order"
    (nums (art "\\section{A}\\subsection{B}\\subsection{C}\\subsubsection{D}\\section*{S}\\section{E}\\subsection{F}") ==
      [some "1", some "1.1", some "1.2", some "1.2.1", none, some "2", some "2.1"])
  t "a subsection before any section prefixes zero, as LaTeX does"
    (nums (art "\\subsection{B}") == [some "0.1"])
  t "appendix letters level 1 and restarts the counter"
    (nums (art "\\section{A}\\appendix\\section{B}\\subsection{C}\\section{D}") ==
      [some "1", some "A", some "A.1", some "B"])
  -- appendix.sty scopes the mark to the environment and restores the
  -- counter after (\@ppsavesec/\@pprestoresec): before this arm the
  -- environment fired W0302 and its sections numbered 2, 2.1, 3.
  t "the appendices environment scopes the mark and restores the counter"
    (nums (art "\\section{A}\\begin{appendices}\\section{B}\\subsection{C}\\end{appendices}\\section{D}") ==
      [some "1", some "A", some "A.1", some "2"])
  let deck := (elabStr ("\\documentclass{slides}\\begin{document}\\section{Only}\\begin{frame}x\\end{frame}\\end{document}")).1
  t "slides sections never number" (nums deck == [none])
  -- \the<counter> is the counter's printed format (classes.dtx
  -- §Sectioning), so its \renewcommand restyles heading numbers from
  -- where it stands instead of binding a macro (which also fired E0312
  -- for every renew standing inline).
  t "a renew of \\thesubsection is the heading-number format"
    (nums (art "\\renewcommand*{\\thesubsection}{FAQ \\arabic{subsection}.}\\section{A}\\subsection{B}\\subsection{C}") ==
      [some "1", some "FAQ 1.", some "FAQ 2."])
  t "a format may reference the parent level's own format"
    (nums (art "\\renewcommand{\\thesubsection}{\\thesection-\\alph{subsection}}\\section{A}\\subsection{B}") ==
      [some "1", some "1-a"])
  let pre := (elabStr ("\\documentclass{article}\\renewcommand{\\thesection}{S\\arabic{section}}\\begin{document}\n\\section{A}\n\\end{document}")).1
  t "a preamble renew of \\thesection numbers the first heading"
    (nums pre == [some "S1"])
  let viaMacro := "\\documentclass{article}\\newcommand{\\fmt}{\\renewcommand{\\thesubsection}{Q\\arabic{subsection}}}\\begin{document}\n\\section{A}\\subsection{B}\n\\fmt\n\\subsection{C}\n\\end{document}"
  t "a renew inside a macro body applies from the call site, without E0312"
    (errCodes viaMacro == [] &&
      nums (elabStr viaMacro).1 == [some "1", some "1.1", some "Q2"])
  -- The label hack every FAQ-styled document writes: retarget the label
  -- to the bare counter while the headings keep their prefixed format.
  let faq := "\\documentclass{article}" ++
    "\\newcommand{\\qlabel}[1]{\\renewcommand{\\thesubsection}{\\arabic{subsection}}" ++
    "\\addtocounter{subsection}{-1}\\refstepcounter{subsection}\\label{#1}" ++
    "\\renewcommand{\\thesubsection}{FAQ \\arabic{subsection}.}}" ++
    "\\begin{document}\n\\renewcommand{\\thesubsection}{FAQ \\arabic{subsection}.}" ++
    "\\section{Q}\\subsection{A}\\qlabel{q:one_two}\n\\subsection{B}\nSee \\ref{q:one_two}.\n\\end{document}"
  t "refstepcounter retargets a label under the format in force"
    (errCodes faq == [] && !(warnCodes faq).contains "W0349" &&
      nums (elabStr faq).1 == [some "1", some "FAQ 1.", some "FAQ 2."])
  t "a counter the engine does not model is named and its arguments consumed"
    ((warnCodes (dvDoc "" "x\\setcounter{tocdepth}{2}y")).contains "W0104" &&
      (errCodes (dvDoc "" "x\\setcounter{tocdepth}{2}y")) == [])
  let (doc, _) := elabStr ("\\documentclass{article}\\begin{document}\\section{Introduction}\nBody.\n\\end{document}")
  t "a number never moves the section anchor"
    ((((HtmlDoc.emit {} doc).1).splitOn "<section id=\"introduction\">").length == 2)

/-- cleveref resolves through the one label table with the kind's locale
name (`Ir.refText`; names from cleveref.sty v0.21.4's language blocks):
the reference forms, the equation parentheses, the locale switch, and
W0380's judge. -/
def crefChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (pre body : String) : String :=
    s!"\\documentclass\{article}{pre}\\begin\{document}\n{body}\n\\end\{document}"
  let refTexts (src : String) : List String :=
    (Ir.foldBlocks (fun a _ => a)
      (fun a x => match x with | .ref _ _ t _ => a.push t | _ => a)
      #[] (elabStr src).1.body).toList
  let secs := "\\section{A}\\label{s}x\\subsection{B}\\label{t}\n\n"
  t "cref and Cref set the section name from the locale"
    (refTexts (wrap "" (secs ++ "\\cref{s} \\Cref{s}")) ==
      ["section\u00A01", "Section\u00A01"])
  t "an equation keeps its parentheses in every cleveref form, bare under \\ref"
    (refTexts (wrap "" ("\\begin{equation}\\label{e}x=1\\end{equation}\n\n" ++
        "\\cref{e} \\labelcref{e} \\ref{e} \\eqref{e}")) ==
      ["eq.\u00A0(1)", "(1)", "1", "(1)"])
  t "crefrange sets the plural, the conjunction, and the pair's numbers"
    (refTexts (wrap "" (secs ++ "\\crefrange{s}{t}")) ==
      ["sections\u00A01 to\u00A0", "1.1"])
  t "namecref sets the name alone"
    (refTexts (wrap "" (secs ++ "\\namecref{s} \\nameCref{t}")) ==
      ["section", "Section"])
  t "the document language picks the cref names (cleveref's german block)"
    (refTexts (wrap "\\usepackage[ngerman]{babel}" (secs ++ "\\cref{s}")) ==
      ["Abschnitt\u00A01"])
  t "the french equation name keeps its accent, capitalised under \\Cref"
    (refTexts (wrap "\\usepackage[french]{babel}"
        ("\\begin{equation}\\label{e}x=1\\end{equation}\n\n\\cref{e} \\Cref{e}")) ==
      ["équation\u00A0(1)", "Équation\u00A0(1)"])
  -- W0380: a bare counter step numbers no node, so its kind is unknowable
  -- — the cref-form reference degrades to the plain number, named; the
  -- same document under \ref is silent, and a heading-bound cref is too.
  let stepped := wrap "" "\\refstepcounter{section}\n\\label{k} \\cref{k}"
  t "a cref to a bare counter step fires W0380 and sets the plain number"
    ((warnCodes stepped).contains "W0380" && refTexts stepped == ["1"])
  t "\\ref to the same binding stays silent"
    (!(warnCodes (wrap "" "\\refstepcounter{section}\n\\label{k} \\ref{k}")).contains "W0380")
  t "a heading-bound cref never fires W0380"
    (!(warnCodes (wrap "" (secs ++ "\\cref{s}"))).contains "W0380")

/-- A user command's argument is the caller's token list: a reserved
character in it is content where the definition places it — a `\label` key
reads it verbatim — never an error at the binding. Dropping it there
mangled every key that travelled through a macro parameter, so the label
never matched its `\ref`. -/
def argTokenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let keyed := dvDoc "\\define \\lbl(k: content) {\\label{\\k}}\n"
    "\\section{A}\\lbl{faq:a_b}\nSee \\ref{faq:a_b}."
  t "underscore through an argument reaches a label key verbatim"
    (errCodes keyed == [] && !(warnCodes keyed).contains "W0349")
  let texty := dvDoc "\\define \\x(a: content) {\\a}\n" "\\x{p_q}"
  t "underscore through an argument placed in text is kept, not dropped"
    (errCodes texty == [] &&
      (((elabStr texty).1.body.toList.filterMap fun b => match b with
        | .para xs => some (Ir.plainText xs)
        | _ => none).any fun s => (s.splitOn "p_q").length > 1))
  t "a reserved character directly in text still errors"
    (errCodes (dvDoc "" "a_b") == ["E0311"])

/-- The beamerposter rewrite lands on the poster class: the synthesized
`\documentclass{poster}` stands after the beamer→slides rewrite in stream
order, and the last `\documentclass` wins in `applyDecl` — the fact the
whole compat arm rides on, pinned here (the audit verified it in code;
this is its test). The board and body size carry the sty's own table:
size/orientation/scale from beamerposter.sty v1.13, fontsize = 24.88pt ×
scale × fontscale rounded to two decimals as the sty rounds. -/
def posterCompatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (opts : String) : String :=
    s!"\\documentclass[final,t]\{beamer}\n\\usepackage[{opts}]\{beamerposter}\n" ++
    "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}"
  let (d, ds) := elabStr (deck "orientation=portrait,size=a1,scale=1.4")
  t "the later synthesized poster class wins over the beamer→slides rewrite"
    (d.docClass == .poster)
  t "the a1 board carries the sty's landscape values, axes swapped for portrait"
    (d.page.width == Dim.mm 594 && d.page.height == Dim.mm 841)
  -- a1 fontscale (1/√2), × 1.4, rounded to two decimals = 0.99;
  -- 24.88pt × 0.99 = 24.6312pt.
  t "fontsize is 24.88 × scale × the size's fontscale, rounded as the sty rounds"
    (d.page.fontSize == Dim.pt 246312 / 10000)
  t "the carried options fire no beamerposter drop" (!ds.any (·.code == "W0367"))
  let (d0, _) := elabStr (deck "size=a0")
  t "the default a0 board is the poster record's own"
    (d0.page.width == Dim.mm 1189 && d0.page.height == Dim.mm 841 &&
      d0.page.fontSize == Dim.pt 2488 / 100)
  let (dc, _) := elabStr (deck "size=custom,width=84,height=59.4,scale=1.2")
  t "a custom board reads width/height as cm at fontscale 1"
    (dc.page.width == (84 : Int) * (7200 * Dim.spPerPt) / 254 &&
      dc.page.fontSize == Dim.pt (2488 * 120) / 10000)
  let (_, dd) := elabStr (deck "debug,size=a2")
  t "an option outside the model is dropped by name (W0367)"
    (dd.any (·.code == "W0367"))
  -- The engine length tokens: a preamble \setlength reads the page the
  -- class record fixes, the declared token then names a column width —
  -- the two constructs the beamerposter idiom is written in.
  let src := "\\documentclass{poster}\n" ++
    "\\newlength{\\colwidth}\n\\setlength{\\colwidth}{0.3\\paperwidth}\n" ++
    "\\begin{document}\n\\begin{frame}{T}\n\\begin{columns}\n" ++
    "\\begin{column}{\\colwidth}\nx\n\\end{column}\n" ++
    "\\begin{column}{\\colwidth}\ny\n\\end{column}\n" ++
    "\\end{columns}\n\\end{frame}\n\\end{document}"
  let (dp, dps) := elabStr src
  t "a preamble \\setlength reads the engine's paperwidth from the class board"
    ((dp.tokens.find? "colwidth").map (·.width.sp) == some (Dim.mm 1189 * 3 / 10))
  t "the token names the column width: E0321 closes and W0314 retires"
    (!dps.any (·.code == "E0321") && !dps.any (·.code == "W0314"))
  let (_, da) := elabStr ("\\documentclass{article}\n\\newlength{\\x}\n" ++
    "\\setlength{\\x}{0.5\\textwidth}\n\\begin{document}\nx\n\\end{document}")
  t "a flow class's preamble textwidth stays a named error: the text block is set after the fold"
    (da.any (·.code == "E0321"))
  let (_, db) := elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
    "\\setlength{\\y}{0.5\\textwidth}\nx\n\\end{document}")
  t "a body \\setlength resolves textwidth from the finished page"
    (!db.any (·.code == "E0321"))


/-- beamer's two column spellings are one construct (user guide §12.7):
`\column{w}` at the top level of a `{columns}` body starts a column where
it stands, exactly as `\begin{column}{w}` does, so both reach the elaborator
as the environment form and land in one `.columns` row. A `\column`
anywhere else starts no column and is named, never dropped in silence. -/
def columnFormChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let colsOf (src : String) : Option (Array (Ir.BoxWidth × Array Ir.Block)) :=
    (elabStr (deck169Frame src)).1.body.findSome? fun
      | .frame _ _ _ _ body => body.findSome? fun
        | .columns cols => some cols
        | _ => none
      | _ => none
  let cmd := "\\begin{columns}[T,onlytextwidth]\n\\column{0.32\\textwidth}\nfirst\n" ++
    "\\column{0.32\\textwidth}\nsecond\n\\column{0.32\\textwidth}\nthird\n\\end{columns}"
  let env := "\\begin{columns}[T,onlytextwidth]\n\\begin{column}{0.32\\textwidth}\nfirst\n" ++
    "\\end{column}\n\\begin{column}{0.32\\textwidth}\nsecond\n\\end{column}\n" ++
    "\\begin{column}{0.32\\textwidth}\nthird\n\\end{column}\n\\end{columns}"
  t "three command-form columns are one three-column row"
    ((colsOf cmd).map (·.size) == some 3)
  t "the command form elaborates to the environment form's document"
    ((elabStr (deck169Frame cmd)).1 == (elabStr (deck169Frame env)).1)
  t "the command form inside columns is no longer a refusal"
    (!(warnCodes (deck169Frame cmd)).contains "W0104")
  -- The two spellings mixed in one body: the command form's column runs
  -- to the environment form's start, as beamer closes it there.
  t "a mixed body keeps every column"
    ((colsOf ("\\begin{columns}\\column{0.5\\textwidth}a\n" ++
      "\\begin{column}{0.5\\textwidth}b\\end{column}\\end{columns}")).map (·.size) == some 2)
  t "a \\column outside {columns} is named, its argument consumed"
    (let ds := (elabStr (deck169Frame "\\column{0.5\\textwidth}\nx")).2
     (ds.any fun d => d.code == "W0104" && hasStr d.message "top level") &&
       !ds.any (·.code == "W0301") && !ds.any (·.code == "E0313"))
/-- Listings apparatus and the siunitx spellings: \lstset propagation and
precedence, listing numbering, minted's language argument, and the number
and unit texts under each locale — including the digit-conservation
oracle the census obligation names. -/
def listingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let firstBlock (src : String) : Option Ir.Block := ((elabStr src).1.body)[0]?
  let bodyText (src : String) : String := Ir.blocksText (elabStr src).1.body
  -- \lstset travels into the listings that follow; the environment's own
  -- keys win, listings' precedence.
  t "\\lstset{numbers=left} numbers the next listing"
    (match firstBlock (dvDoc "" "\\lstset{numbers=left}\n\\begin{lstlisting}\nx = 1\n\\end{lstlisting}") with
     | some (.verbatim _ _ spec) => spec.numbers
     | _ => false)
  t "the environment's own numbers=none overrides \\lstset"
    (match firstBlock (dvDoc "" "\\lstset{numbers=left}\n\\begin{lstlisting}[numbers=none]\nx = 1\n\\end{lstlisting}") with
     | some (.verbatim _ _ spec) => !spec.numbers
     | _ => false)
  -- captioned listings number in flow order; a captionless one takes none
  t "captioned listings number 1, 2 and a captionless takes no number"
    (let body : Array Ir.Block := (elabStr (dvDoc "" ("\\begin{lstlisting}[caption={A}]\na\n\\end{lstlisting}\n" ++
      "\\begin{lstlisting}\nb\n\\end{lstlisting}\n" ++
      "\\begin{lstlisting}[caption={B}]\nc\n\\end{lstlisting}"))).1.body
     match body[0]?, body[1]?, body[2]? with
     | some (Ir.Block.verbatim _ _ s1), some (Ir.Block.verbatim _ _ s2),
         some (Ir.Block.verbatim _ _ s3) =>
       (s1.caption.map (·.1)) == some 1 && s2.caption == none
         && (s3.caption.map (·.1)) == some 2
     | _, _, _ => false)
  -- minted: the language argument is data, never body text
  t "minted's language argument never reaches the code body"
    (match firstBlock (dvDoc "" "\\begin{minted}{python}\nprint(1)\n\\end{minted}") with
     | some (.verbatim _ s _) =>
       (s.splitOn "python").length == 1 && s.trimAscii.toString == "print(1)"
     | _ => false)
  -- the language is one IR fact, normalized: listings' key and minted's
  -- argument land on the same token; verbatim and a bare listing carry none
  let langOf (src : String) : Option (Option String) :=
    match firstBlock src with
    | some (.verbatim _ _ spec) => some spec.langToken
    | _ => none
  t "language=Python normalizes to the token python"
    (langOf (dvDoc "" "\\begin{lstlisting}[language=Python]\nx\n\\end{lstlisting}")
      == some (some "python"))
  t "\\lstset{language=Python} reaches the listings that follow"
    (langOf (dvDoc "" "\\lstset{language=Python}\n\\begin{lstlisting}\nx\n\\end{lstlisting}")
      == some (some "python"))
  t "minted's {C++} normalizes to the same token shape"
    (langOf (dvDoc "" "\\begin{minted}{C++}\nx\n\\end{minted}") == some (some "c++"))
  t "a bare listing and verbatim carry no language"
    (langOf (dvDoc "" "\\begin{lstlisting}\nx\n\\end{lstlisting}") == some none &&
      langOf (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}") == some none)
  -- a spelling outside the token grammar is named and carries nothing
  t "a dialect spelling is named W0110 and carries no language"
    (let src := dvDoc "" "\\begin{lstlisting}[language={[LaTeX]TeX}]\nx\n\\end{lstlisting}"
     langOf src == some none && (warnCodes src).contains "W0110")
  t "minted's spaced language is named W0110 and carries no language"
    (let src := dvDoc "" "\\begin{minted}{Python 3}\nx\n\\end{minted}"
     langOf src == some none && (warnCodes src).contains "W0110")
  -- the grammar itself, at the one minting site
  t "listingLang? admits the plain names and refuses the rest"
    ((Ir.listingLang? " C++ ").map (·.val) == some "c++" &&
      (Ir.listingLang? "F#").map (·.val) == some "f#" &&
      (Ir.listingLang? "objective-c").map (·.val) == some "objective-c" &&
      (Ir.listingLang? "").isNone && (Ir.listingLang? "1c").isNone &&
      (Ir.listingLang? "[LaTeX]TeX").isNone && (Ir.listingLang? "c sharp").isNone &&
      (Ir.listingLang? "a\"b").isNone && (Ir.listingLang? "a`b").isNone)
  -- siunitx: the digits of a rewritten number survive into the text —
  -- the census obligation, checked as an executable oracle
  t "\\num conserves its digits"
    ((bodyText (dvDoc "" "\\num{12345.678}")).toList.filter (·.isDigit)
      == "12345678".toList)
  t "\\num groups by the locale and keeps the en decimal point"
    (bodyText (dvDoc "" "\\num{12345.678}") == "12\u2009345.678")
  t "a french document takes its comma and narrow-space grouping"
    (bodyText ("\\documentclass{article}\n\\usepackage[french]{babel}\n" ++
      "\\begin{document}\n\\num{12345.678}\n\\end{document}")
      == "12\u202F345,678")
  t "an e exponent sets as ×10ⁿ with a real superscript"
    (bodyText (dvDoc "" "\\num{1e5}") == "1\u2009×\u200910⁵")
  t "a quantity joins number and unit by a no-break thin space"
    (bodyText (dvDoc "" "\\qty{1.5}{\\kilo\\gram}") == "1.5\u202Fkg")
  t "per-mode power: a rate sets with a superscript minus"
    (bodyText (dvDoc "" "\\si{\\metre\\per\\second}") == "m\u2009s⁻¹")
  t "a document's own \\num definition wins over the rewrite"
    ((bodyText (dvDoc "\\newcommand{\\num}[1]{N#1}\n" "\\num{7}")) == "N7")

/-- LaTeX idioms translate to native declarations. Own function, same reason. -/
def compatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- TeX register arithmetic is one statement: the `by` and the value go
  -- with the skipped command, never left behind as stray preamble
  -- content (E0313 came from the bare word `by`).
  let adv := dvDoc "\\advance \\footskip by \\ht\\strutbox\n" "x"
  t "register arithmetic is skipped whole, named W0104"
    (errCodes adv == [] && (warnCodes adv).contains "W0104")
  -- geometry's per-side margins: an equal pair is the symmetric margin
  -- the engine centres with; unequal or lone sides stay named (W0101).
  let folded := dvDoc "\\usepackage[top=0.5in, bottom=0.5in, left=0.5in, right=0.5in]{geometry}\n" "x"
  let direct := dvDoc "\\page{ vmargin = 0.5in, hmargin = 0.5in }\n" "x"
  t "equal geometry sides fold to the symmetric margins"
    (!(warnCodes folded).contains "W0101" &&
      (elabStr folded).1.page.vmargin == (elabStr direct).1.page.vmargin &&
      (elabStr folded).1.page.hmargin == (elabStr direct).1.page.hmargin)
  t "unequal geometry sides stay named"
    ((warnCodes (dvDoc "\\usepackage[top=1in, bottom=0.5in]{geometry}\n" "x")).contains
      "W0101")
  -- LaTeX idioms translate to native declarations, each with a note that
  -- shows the shorter spelling. The document compiles as written.
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  let (geoDoc, geoDs) := elabStr (pre "\\usepackage[letterpaper,vmargin=0.5in,hmargin=0.75in,headsep=1in]{geometry}")
  t "compat geometry becomes page" (geoDs.all (·.severity != .error) &&
    geoDoc.page.vmargin == Dim.inch 1 / 2 && geoDoc.page.hmargin == Dim.inch 3 / 4)
  t "compat geometry carries headsep to the page keys"
    (geoDoc.page.headsep == some (Dim.inch 1) &&
      geoDs.all (·.code != "W0101"))
  -- The one-sided margins map as a pair or are dropped named; footskip
  -- rides through; headheight is satisfied by construction (the head's
  -- band reserves its line's whole ink) and goes quietly.
  let (pairDoc, pairDs) := elabStr
    (pre "\\usepackage[top=0.5in,bottom=0.5in,left=0.5in,right=0.5in,footskip=0.2in,headheight=12pt]{geometry}")
  t "compat geometry pairs equal one-sided margins"
    (pairDoc.page.vmargin == Dim.inch 1 / 2 && pairDoc.page.hmargin == Dim.inch 1 / 2 &&
     pairDoc.page.footskip == some (Dim.inch 1 / 5) &&
     pairDs.all (·.code != "W0101"))
  t "compat geometry drops an unequal pair named"
    ((elabStr (pre "\\usepackage[top=1in,bottom=0.5in]{geometry}")).2.any fun d =>
      d.code == "W0101" && hasStr d.message "top" && hasStr d.message "bottom")
  -- A \dimexpr value is TeX arithmetic the mapping cannot carry (its
  -- operands may be registers): a named drop, never a synthesized
  -- unreadable \page value (E0321) — and the warning names the whole
  -- assignment, because "footskip" alone points at a key the engine does
  -- read and hides that the value is the problem.
  let dimexprDs := (elabStr
    (pre "\\usepackage[footskip=\\dimexpr 0.25in + \\ht\\strutbox\\relax]{geometry}")).2
  t "compat geometry drops a dimexpr value named with its spelling"
    ((dimexprDs.any fun d => d.code == "W0101" &&
        hasStr d.message "footskip = \\dimexpr 0.25in" &&
        hasStr d.message "\\strutbox" &&
        (d.help.map (hasStr · "literal")).getD false) &&
      dimexprDs.all (·.severity != .error))
  -- Dropped geometry keys change the page: a config loss, a warning, never
  -- a note buried behind -v.
  t "compat geometry names what it dropped as a warning"
    ((elabStr (pre "\\usepackage[voffset=1in]{geometry}")).2.any fun d =>
      d.code == "W0101" && d.severity == .warning && d.message.endsWith "voffset")
  t "compat known package is a note, unknown a warning"
    ((elabStr (pre "\\usepackage{hyperref}")).2.all (·.severity == .note) &&
     warnCodes (pre "\\usepackage{nosuchpkg}") == ["W0103"])
  -- A picture package's load is the boundary's while the door is open
  -- (the default): the load rides each wrapped standalone, so W0103 would
  -- misname a load the engine consumes. The declared refusal restores it.
  t "compat a picture package's load rides the boundary, not W0103"
    (warnCodes (pre "\\usepackage{pgfplots}") == [] &&
     warnCodes (pre "\\pictures{ tool = none }\\usepackage{pgfplots}") == ["W0103"])
  -- A body-position \usepackage is LaTeX's own refusal ("\usepackage can
  -- be used only in preamble", ltclass.dtx \@onlypreamble): the placement
  -- is the defect, whatever the package's support — W0103 'not supported;
  -- skipped' was the wrong diagnosis, for the supported and the local-.sty
  -- package alike.
  let bodyUse (p : String) : Array Diag :=
    (elabStr ("\\documentclass{article}\n\\begin{document}\nx\n\n" ++
      "\\usepackage{" ++ p ++ "}\n\\end{document}")).2
  t "compat a body usepackage is a placement refusal, never W0103"
    ((bodyUse "pgfplots").any (·.code == "W0340") &&
     (bodyUse "pgfplots").all (·.code != "W0103") &&
     (bodyUse "geometry").any (·.code == "W0340"))
  -- Kernel machinery is consumed whole, never leaked as page content:
  -- \DocumentMetadata's key list and \AddToHook's code once printed on
  -- the page as text. The one modelled key (`lang`) lands on the
  -- \pdfmeta door; the writer keys and the hook are dropped by name.
  let onlyX (d : Ir.Doc) : Bool :=
    match d.body with | #[.para xs] => Ir.plainText xs == "x" | _ => false
  let (dmDoc, dmDs) := elabStr ("\\DocumentMetadata{lang=en, pdfversion=1.7, uncompress}\n" ++
    "\\documentclass{article}\n\\begin{document}\nx\n\\end{document}")
  t "compat DocumentMetadata: lang lands on pdfmeta, nothing leaks"
    (dmDoc.info.language == some "en" && onlyX dmDoc &&
      dmDs.all (·.severity != .error))
  t "compat DocumentMetadata: a version the writer writes lands on pdfmeta"
    (dmDoc.info.pdfVersion == some "1.7")
  t "compat DocumentMetadata names the writer keys it drops"
    (dmDs.any fun d => d.code == "W0101" &&
      !hasStr d.message "pdfversion" && hasStr d.message "uncompress")
  let (hookDoc, hookDs) := elabStr ("\\documentclass{article}\n" ++
    "\\AddToHook{shipout/background}[me]{\\put(0,0){leak}}\n" ++
    "\\begin{document}\nx\n\\end{document}")
  t "compat AddToHook skips whole, named W0104"
    (onlyX hookDoc && (hookDs.map (·.code)).contains "W0104" &&
      hookDs.all (·.severity != .error))
  let (nisDoc, nisDs) := elabStr
    "\\documentclass{article}\n\\begin{document}\n\\nointerlineskip x\n\\end{document}"
  t "compat nointerlineskip is meaning-free: no warning, no content"
    (onlyX nisDoc && nisDs.all (fun d => d.code != "W0301" && d.code != "W0104"))
  -- Package/class diagnostics address TeX's log, never the page. A deferred
  -- style hook once recovered both groups as body text, so the package name's
  -- underscore became E0311 even though the command itself was only W0301.
  --
  -- Two checks, because they catch different regressions. The first reads the
  -- rows from the table, so a row added later is covered by construction —
  -- but a row *deleted* would simply stop being iterated, so it cannot see
  -- one go missing. The second names the LaTeX diagnostic family with the
  -- arity LaTeX's own definitions give it (latex.ltx:8773-8947, from
  -- lterror.dtx §"Error handling and tracing"), so a deletion or a changed
  -- count fails here. Neither check can confirm the arity against LaTeX —
  -- that is what the citation is for; what the first pins is that a row
  -- consumes exactly the count it declares, leaking no group and eating no
  -- following one, which is the property the ink defect turned on.
  let diagFamily : List (String × Nat) :=
    [("PackageWarning", 2), ("PackageWarningNoLine", 2), ("PackageInfo", 2),
     ("PackageNote", 2), ("PackageNoteNoLine", 2),
     ("ClassWarning", 2), ("ClassWarningNoLine", 2), ("ClassInfo", 2),
     ("ClassNote", 2), ("ClassNoteNoLine", 2),
     ("GenericWarning", 2), ("GenericInfo", 2), ("MessageBreak", 0),
     ("@latex@warning", 1), ("@latex@warning@no@line", 1),
     ("@latex@info", 1), ("@latex@info@no@line", 1),
     ("@latex@note", 1), ("@latex@note@no@line", 1),
     ("PackageError", 3), ("ClassError", 3), ("GenericError", 4),
     ("@latex@error", 2)]
  for row in diagFamily do
    let (name, arity) := row
    t s!"compat {name} is a log-only row at LaTeX's own arity {arity}"
      ((Compat.meaningFree.lookup name).map (·.1) == some arity)
  -- Every row of the table, whatever it is: its groups are consumed exactly,
  -- no reserved character of them reaches the page, and the no-op is paid
  -- for. N0100 is matched on its structured subject, never on the message and
  -- never on "some N0100 exists" — the hook's own deferral note is an N0100
  -- too, so the weaker form holds even when the row does nothing at all.
  for row in Compat.meaningFree do
    let (name, arity, note) := row
    let groups := String.join (List.replicate arity "{ignored_message_}")
    let (diagDoc, diagDs) := elabStr ("\\documentclass{article}\n" ++
      "\\AtBeginDocument{\\" ++ name ++ groups ++ "{SENTINEL}}\n" ++
      "\\begin{document}\nx\n\\end{document}")
    -- the sentinel is one group past the declared arity: it must survive
    t s!"compat {name} consumes exactly its {arity} log-only groups"
      (diagDoc.body == #[.para #[.text "SENTINEL x"]])
    t s!"compat {name} lets no reserved character of a log group reach the page"
      (diagDs.all fun d => d.code != "W0301" && d.code != "E0311" &&
        d.severity != .error)
    -- a row carrying a reason earns its silence through a named N0100; a row
    -- carrying none is named by the silence guard instead (W0387)
    if note.isSome then
      t s!"compat {name} accounts for its no-op as N0100 naming the command"
        (diagDs.any fun d => d.code == "N0100" &&
          d.subject == some ("ctrl:nothing:" ++ name))
    else
      t s!"compat {name} is consumed with its loss named"
        (diagDs.any fun d => d.code == "W0387")
  -- The other half of the rule: an arbitrary unknown command still preserves
  -- its argument content, so the table is a named exception and not a licence
  -- to swallow groups.
  let (unkDoc, unkDs) := elabStr ("\\documentclass{article}\n" ++
    "\\begin{document}\n\\zzzNotAControl{kept one}{kept two} x\n\\end{document}")
  let unkText := Ir.plainText (match unkDoc.body with
    | #[.para xs] => xs | _ => #[])
  t "compat an unknown command still keeps its groups as text"
    (hasStr unkText "kept one" && hasStr unkText "kept two" &&
      unkDs.any (·.code == "W0301"))
  -- The font-selection packages: each names families for the generic
  -- slots (psnfss §2; carlito README), landing on \fonts — the same door
  -- \setmainfont uses. carlito's sfdefault promotes sans to body; a
  -- psnfss scale option is a dropped loss, named.
  let fontsOf (decls : String) : Ir.FontSpec := (elabStr (pre decls)).1.fonts
  t "compat times fills all three slots"
    (fontsOf "\\usepackage{times}" ==
      { body := some "TeX Gyre Termes", sans := some "TeX Gyre Heros",
        mono := some "TeX Gyre Cursor" })
  t "compat mathptmx carries the matching math face"
    ((fontsOf "\\usepackage{mathptmx}").math == some "TeX Gyre Termes Math")
  t "compat carlito is the sans face, sfdefault promotes it to body"
    ((fontsOf "\\usepackage{carlito}") ==
      { sans := some "Carlito" } &&
     (fontsOf "\\usepackage[sfdefault]{carlito}").body == some "Carlito")
  t "compat helvet names its dropped scale option"
    ((elabStr (pre "\\usepackage[scaled=0.9]{helvet}")).2.any fun d =>
      d.code == "W0101" && hasStr d.message "scaled")
  -- \xspace: a space unless punctuation follows (xspace documentation) —
  -- the lexer has already eaten any typed space after the control word,
  -- so dropping it would silently glue words. Through a macro, the
  -- body-end boundary takes the package's default action (a space).
  let paraText (body : String) : String :=
    match (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++ body ++
      "\n\\end{document}")).1.body with
    | #[.para xs] => Ir.plainText xs
    | _ => "<not one para>"
  t "compat xspace inserts the space a word needs"
    (paraText "a\\xspace b" == "a b")
  t "compat xspace stays out before punctuation"
    (paraText "a\\xspace." == "a.")
  t "compat xspace through a macro keeps the word boundary"
    (paraText "\\define \\foo {ab\\xspace}\\foo c" == "ab c")
  -- The picture subset renders, so loading tikz loses nothing at the load:
  -- a shape outside the subset is named where it is drawn (W0334, E0333),
  -- never at the `\usepackage` line.
  t "compat tikz package is native; the loss lives at the picture"
    ((elabStr (pre "\\usepackage{tikz}")).2.all (·.severity == .note))
  -- The paper packages: xurl is url with better breaking, amsfonts a
  -- subset of amssymb/unicode-math, nicefrac and multirow name their
  -- commands where a document uses them — nothing is lost at the load.
  t "compat xurl, amsfonts, nicefrac, multirow, caption, subcaption are native"
    ((elabStr (pre ("\\usepackage{xurl}\\usepackage{amsfonts}\\usepackage{nicefrac}" ++
      "\\usepackage{multirow}\\usepackage{caption}\\usepackage{subcaption}"))).2.all
      (·.severity == .note))
  -- The caption package's option interface: a position declaration is
  -- honoured by construction (the caption gap binds to the object side
  -- wherever the source puts the caption — caption manual §2.2, the
  -- option does not move the caption); any other key is named and
  -- ignored, once per key, and never silently.
  t "compat caption tableposition=top is honoured silently"
    ((elabStr (pre "\\usepackage[tableposition=top]{caption}")).2.all
      (·.severity == .note))
  t "compat captionsetup position keys are honoured silently"
    ((elabStr (pre "\\captionsetup{tableposition=top}")).2.all
      (·.severity == .note))
  t "compat captionsetup names an unhonoured key once"
    (warnCodes (pre ("\\captionsetup[table]{labelfont=bf}\n" ++
      "\\captionsetup[subtable]{labelfont=bf}")) == ["W0354"] &&
     ((elabStr (pre "\\captionsetup[table]{labelfont=bf}")).2.map (·.message)).any
      (fun m => (m.splitOn "'labelfont'").length == 2))
  -- A `[float type]` scope declares the kind's own token, which only that
  -- kind reads (`Ir.captionTokenOf`): a table-only skip never reaches the
  -- document's `captionsep`, so no figure moves.
  t "compat captionsetup skip declares the scoped caption gap"
    ((elabStr (pre "\\captionsetup[table]{skip=10pt}")).1.tokens.find? "tablecaptionsep"
        == some { width := { sp := Dim.pt 10 } } &&
     ((elabStr (pre "\\captionsetup[table]{skip=10pt}")).1.tokens.find? "captionsep").isNone &&
     (elabStr (pre "\\captionsetup[table]{skip=10pt}")).2.all (·.severity == .note))
  -- The caption package applies an option where a caption is set, so a
  -- skip set to `\abovecaptionskip` is that gap set to itself: honoured,
  -- and it moves nothing.
  t "compat captionsetup skip set to the caption skip itself is honoured"
    (warnCodes (pre ("\\captionsetup[table]{skip=\\abovecaptionskip}\n" ++
      "\\captionsetup[subtable]{skip=\\abovecaptionskip}")) == [])
  -- margin= is the caption's both-side margin (caption manual §2.4): one
  -- token, read by the float caption's measure and the HTML figcaption
  -- padding alike; the package-option spelling routes through the same
  -- arm. A {left,right} pair is not one length and stays named.
  t "compat captionsetup margin declares the caption margin"
    ((elabStr (pre "\\captionsetup{margin=12pt}")).1.tokens.find? "captionmargin"
        == some { width := { sp := Dim.pt 12 } } &&
     (elabStr (pre "\\captionsetup{margin=12pt}")).2.all (·.severity == .note) &&
     (elabStr (pre "\\usepackage[margin=12pt]{caption}")).1.tokens.find? "captionmargin"
        == some { width := { sp := Dim.pt 12 } } &&
     (warnCodes (pre "\\captionsetup{margin={1em,2em}}")).contains "W0354")
  -- The geometry text-block spelling: `textwidth`/`textheight` size the
  -- body (geometry manual §5.2) and the engine centres it, whichever of
  -- the three spellings (package options, \geometry, \newgeometry)
  -- carried the keys.
  t "compat newgeometry textwidth/textheight centre the text block"
    (let doc := (elabStr (pre "\\newgeometry{textwidth=396pt, textheight=576pt}")).1
     doc.page.hmargin == Dim.pt 108 && doc.page.vmargin == Dim.pt 108)
  -- A skipped package that is a local .sty beside the document is \input
  -- of its text (ltfiles.dtx \@onefilewithoptions: \usepackage IS "find
  -- p.sty on the input path and read it"): options resolve
  -- (\DeclareOption/\ProcessOptions), \AtBeginDocument unwraps, \geometry
  -- reaches \page, and what the engine refuses is named at the .sty's own
  -- file — never W0103, which is for the package that is not there to read.
  let parseRaws (file s : String) : Array Parse.Raw :=
    (Parse.parse file (Lex.lex file s).1).1
  let sty :=
    "\\NeedsTeXFormat{LaTeX2e}\n\\ProvidesPackage{guide}[2026/01/01 venue guide]\n" ++
    "\\newif\\if@final\\@finalfalse\n\\DeclareOption{final}{\\@finaltrue}\n" ++
    "\\ProcessOptions\\relax\n" ++
    "\\if@final\\RequirePackage{natbib}\\fi\n" ++
    "\\AtBeginDocument{\n\\newgeometry{\ntextheight=576pt,\ntextwidth=396pt\n}\n}\n" ++
    "\\setlength{\\abovecaptionskip}{7\\p@}\n" ++
    "\\def\\x#1,#2\\relax{#1}\n"
  let docRaws := parseRaws "t"
    ("\\documentclass{article}\n\\usepackage[final]{guide}\n" ++
     "\\begin{document}\nx\n\\end{document}")
  let (raws2, spliced) := Compat.applyLocalSty docRaws #[("guide", parseRaws "guide.sty" sty)]
  let (doc2, elabDs) := Elab.runRaws "t" raws2
  t "a local .sty is \\input of its text: its \\geometry reaches \\page"
    (doc2.page.hmargin == Dim.pt 108 && doc2.page.vmargin == Dim.pt 108 &&
     doc2.tokens.find? "captionsep" == some { width := { sp := Dim.pt 7 } } &&
     elabDs.all (·.code != "W0103"))
  t "what of the .sty's text is refused is named at the .sty's own file"
    ((elabDs.filter fun d => d.code == "W0357" &&
        d.span.any (·.file == "guide.sty")).size == 1)
  t "the read is named once, with the honoured, named, and refused counts"
    (spliced.toList.map (·.1) == ["guide.sty"] &&
     Compat.styCounts "guide.sty" elabDs == (4, 0, 1))
  t "a def-only local .sty is still read; its \\def is a definition — never W0103"
    (let (raws3, spl3) := Compat.applyLocalSty docRaws
      #[("guide", parseRaws "guide.sty" "\\def\\x#1{#1}\n")]
     let ds3 := (Elab.runRaws "t" raws3).2
     spl3.size == 1 && ds3.all (·.code != "W0103") &&
     Compat.styCounts "guide.sty" ds3 == (1, 0, 0))
  -- Monotone expansion visibility: a definition inside an expanded body
  -- binds at the visibility boundary and never re-exposes the command
  -- being expanded to its own body. The venue-style \maketitle — it
  -- renews \thefootnote and then names itself in \let — used to diverge
  -- here; the self-name now resolves to the definition before it.
  t "a body define never exposes the expanding command to its own body"
    ((elabStr ("\\documentclass{article}\n" ++
      "\\providecommand{\\mktitle}{}\n" ++
      "\\renewcommand{\\mktitle}{\\renewcommand{\\theftn}{y}\\let\\mktitle\\relax t}\n" ++
      "\\begin{document}\n\\mktitle\nx\n\\end{document}")).1.body.size > 0)
  t "compat appendixnumberbeamer is native; \\appendix is too"
    ((elabStr (pre "\\usepackage{appendixnumberbeamer}")).2.all (·.severity == .note) &&
     warnCodes ("\\documentclass{article}\n\\usepackage{appendixnumberbeamer}\n" ++
       "\\begin{document}\n\\appendix\nx\n\\end{document}") == [])
  t "compat definecolor" ((elabStr (pre "\\definecolor{c}{HTML}{0F766E}")).1.palette.find? "c" ==
    some { r := 0x0F, g := 0x76, b := 0x6E })
  -- \setbeamercovered{transparent} is beamer's fifteen per cent, the key's
  -- default: it sets the covered fraction, as any percentage does, and
  -- warns nothing (the artifact half is `inkBoundChecks`). Anything else
  -- (invisible, dynamic) keeps the warning naming the divergence.
  let themedPre (decls : String) : String :=
    "\\documentclass{beamer}\n\\usetheme{moloch}\n" ++ decls ++
    "\n\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  t "compat setbeamercovered transparent agrees, warning nothing"
    (warnCodes (themedPre "\\setbeamercovered{transparent}") == [] &&
     (elabStr (themedPre "\\setbeamercovered{transparent}")).1.palette.coveredFraction
       == some 15)
  t "compat setbeamercovered transparent=n sets the covered fraction"
    ((elabStr (themedPre "\\setbeamercovered{transparent=25}")).1.palette.coveredFraction
      == some 25)
  -- The boundary: labMix above 100 extrapolates with a negative surface
  -- weight (color-factor F9), so no parse path may hand a fraction past
  -- the clamp. The palette route errors E0332 (tested with the palette
  -- key); this pins the compat route: out-of-range keeps the fraction
  -- unset and warns instead of forwarding the number. Unthemed, so the
  -- only possible source of a fraction is the rejected declaration.
  let barePre (decls : String) : String :=
    "\\documentclass{beamer}\n\\usetheme{default}\n" ++ decls ++
    "\n\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  t "compat setbeamercovered transparent=100 never reaches the fraction"
    ((elabStr (barePre "\\setbeamercovered{transparent=100}")).1.palette.coveredFraction
      == none &&
     (warnCodes (barePre "\\setbeamercovered{transparent=100}")).contains "W0104")
  t "compat setbeamercovered transparent=0 never reaches the fraction"
    ((elabStr (barePre "\\setbeamercovered{transparent=0}")).1.palette.coveredFraction
      == none)
  t "compat setbeamercovered invisible keeps the honest warning"
    (warnCodes (themedPre "\\setbeamercovered{invisible}") == ["W0104"])
  -- `professionalfonts` and `hide notes` each ask for what the engine
  -- already does — declared fonts kept, notes off the delivered pages —
  -- so both are agreement; any other argument keeps the warning.
  t "compat usefonttheme professionalfonts agrees, warning nothing"
    (warnCodes (themedPre "\\usefonttheme{professionalfonts}") == [])
  t "compat usefonttheme serif keeps the honest warning"
    (warnCodes (themedPre "\\usefonttheme{serif}") == ["W0104"])
  t "compat setbeameroption hide notes agrees, warning nothing"
    (warnCodes (themedPre "\\setbeameroption{hide notes}") == [])
  t "compat setbeameroption show notes keeps the honest warning"
    (warnCodes (themedPre "\\setbeameroption{show notes on second screen=right}")
      == ["W0104"])
  -- `\ifdefined` is decidable from the document's own definitions, so it
  -- resolves to its taken branch with a note — nothing nothing defines is
  -- undefined, which is the honest answer for another engine's primitives
  -- too. A head TeX defines that the document cannot decide is tracked, and
  -- where its branch is reached it keeps the skip-whole warning; an `\if…`
  -- name the pass does not know leaves the whole extent unresolved.
  t "compat ifdefined undefined keeps the else branch"
    (let (doc, ds) := elabStr "\\ifdefined\\nope A\\else B\\fi"
     doc.body == #[.para #[.text "B"]] && ds.any (·.code == "N0114") &&
       ds.all (·.severity == .note))
  t "compat ifdefined defined keeps the first branch"
    ((elabStr "\\def\\yep{1}\\ifdefined\\yep A\\else B\\fi").1.body ==
      #[.para #[.text "A"]])
  t "compat ifdefined nested resolves inside the kept branch"
    ((elabStr "\\ifdefined\\nope A\\else\\ifdefined\\nada B\\else C\\fi\\fi").1.body ==
      #[.para #[.text "C"]])
  t "compat a foreign conditional inside a taken branch keeps the skip-whole warning"
    (let ds := (elabStr "\\def\\a{}\\ifdefined\\a\\ifx\\b\\c\\fi\\fi x").2
     ds.any (·.code == "W0104") && ds.any (·.code == "N0114"))
  t "compat an unknown if-name inside leaves the whole extent unresolved"
    (let ds := (elabStr "\\ifdefined\\a\\ifsomething\\fi\\fi x").2
     ds.all (·.code != "N0114"))
  -- `\newif` joins the same pass: `\ifX` resolves from the flag's flow
  -- state, `\Xtrue`/`\Xfalse` set it, the initial value is false (plain
  -- TeX's `\newif` ends by setting the false branch). A flag's `\ifX`
  -- also counts as decidable inside an `\ifdefined` extent.
  t "compat newif starts false: the else branch is kept"
    (let (doc, ds) := elabStr "\\newif\\ifdtl\\ifdtl A\\else B\\fi"
     doc.body == #[.para #[.text "B"]] && ds.all (·.severity == .note))
  t "compat a flag setter flips the taken branch"
    ((elabStr "\\newif\\ifdtl\\dtltrue\\ifdtl A\\else B\\fi").1.body ==
      #[.para #[.text "A"]])
  t "compat a later setter flips it back, in flow order"
    ((elabStr "\\newif\\ifdtl\\dtltrue\\dtlfalse\\ifdtl A\\else B\\fi").1.body ==
      #[.para #[.text "B"]])
  t "compat a setter in an untaken branch does not fire"
    ((elabStr "\\newif\\ifdtl\\ifdtl\\dtltrue A\\else B\\fi\\ifdtl C\\else D\\fi").1.body ==
      #[.para #[.text "BD"]])
  t "compat newif inside an ifdefined extent stays decidable"
    ((elabStr "\\newif\\ifdtl\\ifdefined\\nope A\\else\\ifdtl B\\else C\\fi\\fi").1.body ==
      #[.para #[.text "C"]])
  t "compat an undeclared if-name is not a flag: the extent stays skipped"
    (let ds := (elabStr "\\ifsomething A\\else B\\fi x").2
     ds.all (·.code != "N0114"))
  t "compat definecolor rgb" ((elabStr (pre "\\definecolor{c}{rgb}{1,0,0.5}")).1.palette.find? "c" ==
    some { r := 255, g := 0, b := 127 })
  t "compat colorlet aliases"
    ((elabStr (pre "\\definecolor{a}{HTML}{112233}\\colorlet{b}{a}")).1.palette.find? "b" ==
      some { r := 0x11, g := 0x22, b := 0x33 })
  t "compat setlength becomes a token"
    ((elabStr (pre "\\newlength{\\r}\\setlength{\\r}{2ex}\\setlength{\\s}{0.5\\r}")).1.tokens.find? "s" ==
      some { width := { ex := 1000 } })
  t "compat hypersetup becomes pdfmeta"
    ((elabStr (pre "\\hypersetup{pdfauthor={A. Doe},pdftitle=T,colorlinks=false}")).1.info.author ==
      some "A. Doe")
  t "compat scrartcl is article"
    ((elabStr "\\documentclass{scrartcl}\\begin{document}x\\end{document}").1.docClass == .article)
  t "compat moderncv is resume"
    ((elabStr "\\documentclass{moderncv}\\begin{document}x\\end{document}").1.docClass == .resume)
  t "compat res is resume"
    ((elabStr "\\documentclass{res}\\begin{document}x\\end{document}").1.docClass == .resume)
  t "compat linespread is leading"
    ((elabStr (pre "\\linespread{1.04}")).1.page.leading == 1040)
  -- A class's \renewcommand\normalsize opening with \@setfontsize: the
  -- body size and its leading, honoured as the page's own — 10/10.95
  -- (\@xpt/\@xipt) lands the baselines at 10.95pt over the engine's 6/5
  -- base, so the factor is 10.95/12 = 0.9125, carried at milli precision.
  t "compat @setfontsize normalsize sets size and leading"
    (let d := (elabStr (pre
      "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt}")).1
     d.page.fontSize == Dim.pt 10 && d.page.leading == 913)
  t "compat @setfontsize literal leading"
    ((elabStr (pre
      "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize{12}{14.5}}")).1.page.leading
      == 1007)
  -- Rule (b) extended to the ladder: every other refused size command's
  -- \@setfontsize is a declaration too, read at the preamble's end as a
  -- per-mille step of the body in force — the venue's own normalsize —
  -- through Ir.setStep's ordered door. A landed step drops its W0361;
  -- a step that would disorder the named sizes keeps the built-in, named.
  let ladderPre (decls : String) : String :=
    pre ("\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt}" ++ decls)
  t "a refused size command's @setfontsize lands as the ladder step"
    (let (d, ds) := elabStr (ladderPre
      "\\renewcommand{\\footnotesize}{\\@setfontsize\\footnotesize\\@ixpt\\@xpt}")
     (d.page.scale.lookup "footnotesize") == some 900 &&
       ds.all (·.severity != .warning))
  t "the ladder step is relative to the venue's own normalsize"
    (let d := (elabStr (pre
      ("\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xiipt{14}}" ++
       "\\renewcommand{\\small}{\\@setfontsize\\small\\@xipt{12}}"))).1
     (d.page.scale.lookup "small") == some 913)
  t "equal neighbouring sizes are the lineage's own and land"
    (let d := (elabStr (ladderPre
      ("\\renewcommand{\\small}{\\@setfontsize\\small\\@ixpt\\@xpt}" ++
       "\\renewcommand{\\footnotesize}{\\@setfontsize\\footnotesize\\@ixpt\\@xpt}"))).1
     (d.page.scale.lookup "small") == some 900 &&
       (d.page.scale.lookup "footnotesize") == some 900)
  t "a size step that disorders the named sizes keeps the built-in, named"
    (let (d, ds) := elabStr (ladderPre
      "\\renewcommand{\\small}{\\@setfontsize\\small\\@xiipt{14}}")
     (d.page.scale.lookup "small") == some 900 &&
       ds.any fun dg => dg.code == "W0361" &&
         (dg.message.splitOn "out of order").length > 1)
  -- The venue's ladder is one declaration: steps that only order against
  -- *each other* — a shrink written top-down would fail any one-at-a-time
  -- reading against the engine's still-standing neighbours — land whole.
  t "a venue ladder ordered against itself lands whole"
    (let d := (elabStr (ladderPre
      ("\\renewcommand{\\small}{\\@setfontsize\\small{7.5}{9}}" ++
       "\\renewcommand{\\footnotesize}{\\@setfontsize\\footnotesize{7}{8}}" ++
       "\\renewcommand{\\scriptsize}{\\@setfontsize\\scriptsize{6}{7}}"))).1
     (d.page.scale.lookup "small") == some 750 &&
       (d.page.scale.lookup "footnotesize") == some 700 &&
       (d.page.scale.lookup "scriptsize") == some 600)
  t "the display-skip tail after @setfontsize does not block the read"
    (let d := (elabStr (ladderPre
      ("\\renewcommand{\\small}{\\@setfontsize\\small\\@ixpt\\@xpt " ++
       "\\abovedisplayskip 6\\p@ \\@plus 1.5\\p@}"))).1
     (d.page.scale.lookup "small") == some 900)
  t "compat heads become one running head"
    ((elabStr (pre "\\ihead{L}\\ohead{\\thepage}")).1.head.map (·.any (· == .pageNumber)) == some true)
  -- fancyhdr's primary interface: [places] cross L/C/R with E/O; the slots
  -- land beside \lhead's, one replace policy, and \fancyhf{} clears.
  t "compat fancyhead places its slots"
    ((elabStr (pre "\\fancyhead[L]{A}\\fancyhead[R]{\\thepage}")).1.head.map
      (·.any (· == .pageNumber)) == some true)
  t "compat fancyhf clears the gathered fields"
    ((elabStr (pre "\\lhead{A}\\cfoot{B}\\fancyhf{}")).1.head == none &&
     (elabStr (pre "\\lhead{A}\\cfoot{B}\\fancyhf{}")).1.foot == none)
  t "compat fancyhead even-odd places collapse with a note"
    (let (doc, ds) := elabStr (pre "\\fancyhead[LE,RO]{A}")
     doc.head.isSome && ds.any (fun d => d.code == "N0102") &&
       ds.all (·.severity == .note))
  t "compat pagestyle fancy is agreement, not a missing model"
    ((elabStr (pre "\\fancyhead[L]{A}\\pagestyle{fancy}")).2.all (·.severity == .note))
  t "compat pagestyle empty clears the furniture"
    ((elabStr (pre "\\lhead{A}\\pagestyle{empty}")).1.head == none)
  t "compat pagestyle plain declares the numbers on, natively"
    (let (doc, ds) := elabStr (pre "\\pagestyle{plain}")
     doc.page.numbers == some true && ds.all (·.severity == .note))
  t "compat pagestyle empty declares the numbers off"
    ((elabStr (pre "\\pagestyle{empty}")).1.page.numbers == some false)
  t "compat thispagestyle empty gates the default number without a declared field"
    (let (doc, ds) := elabStr (pre "\\thispagestyle{empty}")
     doc.footFrom == 2 && doc.headFrom == 2 && doc.foot == none &&
       ds.all (·.severity == .note))
  t "the gate only defers: a declaration's own later from stands"
    ((elabStr (pre "\\runningfoot[from = 3]{note}\\thispagestyle{empty}")).1.footFrom == 3)
  t "compat pagestyle headings keeps the honest warning"
    (warnCodes (pre "\\pagestyle{headings}") == ["W0104"])
  -- `\par` ends a paragraph inside a scope group, with the group's
  -- declarations carried into what follows; a command's argument group is
  -- not a scope and is left to the command.
  t "par in a scope group ends the paragraph"
    ((elabStr "{\\Huge a \\par} b").1.body ==
      #[.para #[.styled (.size "Huge") #[.text "a "]], .para #[.text "b"]])
  t "par in a scope group carries the declarations"
    ((elabStr "{\\bfseries a \\par b}").1.body ==
      #[.para #[.styled .bold #[.text "a "]], .para #[.styled .bold #[.text "b"]]])
  t "a blank line in a scope group is a paragraph end too"
    ((elabStr "{\\bfseries a\n\nb}").1.body.size == 2)
  t "par in an argument group is the command's"
    ((elabStr "\\emph{a \\par b}").1.body.size == 1)
  -- A defined command whose body ends its paragraph produces one when
  -- called between paragraphs, as LaTeX's `\newcommand{\entry}[1]{...\par}`
  -- does; and a forced break at a paragraph's end is dropped, since the end
  -- already says it (it was an empty line in the PDF, an empty row in HTML).
  let (entry, _) := elabStr ("\\documentclass{article}\\define \\entry(a: content) {\\textbf{\\a}\\par}" ++
    "\\begin{document}\\entry{x}\\entry{y}\\end{document}")
  t "a body ending in par is a block" (entry.body ==
    #[.role "entry" #[.para #[.styled .bold #[.text "x"]]],
      .role "entry" #[.para #[.styled .bold #[.text "y"]]]])
  t "a trailing forced break is dropped" ((elabStr "a\\\\ \n\nb").1.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  -- The document's definitions win over every built-in it may redefine;
  -- the ones it may not are refused with W0303, never shadowed silently.
  let (own, ownDs) := elabStr ("\\documentclass{article}" ++
    "\\define \\link(u: text, l: text) {\\href{\\u}{\\underline{\\l}}}" ++
    "\\begin{document}\\link{https://example.org}{here}\\end{document}")
  t "a defined link wins over the built-in"
    (ownDs.isEmpty && own.body ==
      #[.para #[.role "link" #[.link "https://example.org" #[.underline #[.text "here"]]]]])
  t "a parameter inside a URL is the caller's text"
    (own.body == #[.para #[.role "link"
      #[.link "https://example.org" #[.underline #[.text "here"]]]]])
  t "a structural built-in cannot be redefined"
    ((warnCodes ("\\documentclass{article}\\define \\underline(x: content) {\\emph{\\x}}" ++
      "\\begin{document}\\underline{a}\\end{document}")) == ["W0303"])
  -- Text superscripts are owed, not implemented (PLAN 2026-09-20: the
  -- raise will come from OS/2 ySuperscript metrics, unparsed today), and
  -- the refusal stays loud: a construct that quietly stopped warning
  -- while unimplemented is worse than one that never worked.
  t "textsuperscript refuses loudly while owed"
    ((warnCodes ("\\documentclass{article}" ++
      "\\begin{document}a\\textsuperscript{2}\\end{document}")) == ["W0301"])
  -- The font commands are rendered built-ins: a runnable redefinition of
  -- \textbf wins, as \renewcommand intends, and its role names the use.
  let (bfDoc, bfDs) := elabStr ("\\documentclass{article}" ++
    "\\define \\textbf(x: content) {\\emph{\\x}}" ++
    "\\begin{document}\\textbf{a}\\end{document}")
  t "a runnable redefinition of textbf wins"
    (bfDs.isEmpty && bfDoc.body ==
      #[.para #[.role "textbf" #[.styled .emph #[.text "a"]]]])
  -- Rule (b): a rendered built-in yields only to a redefinition the engine
  -- can run. The venue shape — a \maketitle body of kernel internals — is
  -- refused with W0361 naming the first losing construct, and the built-in
  -- still sets the title heading. A runnable body wins, as in LaTeX; an
  -- empty body (`\providecommand{\maketitle}{}`) would erase the title as
  -- silently as an unrunnable one, so it is refused too.
  let venue := "\\documentclass{article}\\title{Kept Probe}" ++
    "\\renewcommand{\\maketitle}{\\begingroup\\venuetitlebox\\endgroup}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  t "a maketitle redefinition the engine cannot run is refused, named"
    (warnCodes venue == ["W0361"])
  t "the built-in maketitle stands: the title is still the level-0 heading"
    (Ir.headingLevels (elabStr venue).1.body == #[0])
  let winner := "\\documentclass{article}" ++
    "\\renewcommand{\\maketitle}{\\textbf{T-wins}}" ++
    "\\begin{document}\\maketitle\\end{document}"
  t "a maketitle redefinition the engine can run wins"
    ((elabStr winner).2.all (·.severity == .note) &&
     (elabStr winner).1.body == #[.para #[.styled .bold #[.text "T-wins"]]])
  let emptied := "\\documentclass{article}\\title{Kept Probe}" ++
    "\\renewcommand{\\maketitle}{}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  t "an empty maketitle redefinition renders nothing and is refused"
    (warnCodes emptied == ["W0361"] &&
     Ir.headingLevels (elabStr emptied).1.body == #[0])
  -- `\providecommand` of a built-in is LaTeX's documented no-op (usrguide,
  -- "Defining commands": provide keeps an existing definition, and every
  -- rendered built-in exists): the built-in stands silently — the venue
  -- shim `\providecommand{\section}{}` is a guarantee of renewability,
  -- never an erasure — and a non-empty provide body never wins either.
  let provided := "\\documentclass{article}\\title{Kept Probe}" ++
    "\\providecommand{\\maketitle}{}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  t "a providecommand of a built-in keeps the built-in without a warning"
    (warnCodes provided == [] &&
     Ir.headingLevels (elabStr provided).1.body == #[0])
  let providedBody := "\\documentclass{article}" ++
    "\\providecommand{\\section}{\\textbf{not a heading}}" ++
    "\\begin{document}\\section{Kept}\\end{document}"
  t "a non-empty providecommand of a built-in still keeps the built-in"
    (warnCodes providedBody == [] &&
     Ir.headingLevels (elabStr providedBody).1.body == #[1])
  -- The author block's styling joins the refused-body scan: the lineage's
  -- tabular — \bf, a zero-width \rule strut, \@author — lands the venue's
  -- weight and the engine's rhythm strut on the built-in author line, and
  -- the trailing \vskip the engine's rhythm gap after the whole block
  -- (`Ir.titleAuthorStrut`/`Ir.titleBlockAfter`: the venue chooses that
  -- the furniture exists, the engine chooses where it sits).
  let authorVenue := "\\documentclass{article}\\title{T}\\author{A. Name}" ++
    "\\renewcommand{\\maketitle}{\\begingroup\\@maketitle\\endgroup}" ++
    "\\providecommand{\\@maketitle}{}" ++
    "\\renewcommand{\\@maketitle}{\\vbox{\\centering{\\Large\\bf \\@title\\par}" ++
    "\\begin{tabular}[t]{c}\\bf\\rule{\\z@}{24\\p@}\\@author\\end{tabular}" ++
    "\\vskip 0.3in \\@minus 0.1in}}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  let (aDoc, _) := elabStr authorVenue
  -- The title block may stand inside its alignment wrapper; the probe
  -- looks one level into `.center` for the styled author line and the gap.
  t "the refused body's author tabular styles the built-in author line"
    (inTitleBlock aDoc fun b => match b with
      | .para #[.strut h, .styled .bold _] => h == Ir.titleAuthorStrut
      | _ => false)
  t "the trailing vskip becomes the engine's rhythm gap after the block"
    (inTitleBlock aDoc fun b => match b with
      | .spaced g #[] => g.value == Ir.titleBlockAfter
      | _ => false)
  -- beamer's spelling of the very same declared data, inside the canvas
  -- environment a theme writes its title page in. The read-out knew
  -- latex.ltx's `\@title` alone, so a theme-authored title page read as no
  -- title page at all: the refusal stood by itself and the appearance the
  -- body *declared* went out with the arrangement that cannot be expressed.
  -- One resolving site now answers for both spellings
  -- (`Elab.barScan_alias_agree`), and an environment is descended into like
  -- any other grouping.
  let insertVenue := "\\documentclass{article}\\title{T}\\author{A. Name}" ++
    "\\renewcommand{\\maketitle}{\\begingroup\\@maketitle\\endgroup}" ++
    "\\providecommand{\\@maketitle}{}" ++
    "\\renewcommand{\\@maketitle}{\\begin{minipage}{\\textwidth}" ++
    "\\hrule height 3pt" ++
    "{\\raggedright\\Large\\bf\\inserttitle\\par}" ++
    "\\hrule height 1pt" ++
    "\\bf\\rule{\\z@}{24\\p@}\\insertauthor" ++
    "\\vskip 0.3in\\end{minipage}}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  let (iDoc, iDs) := elabStr insertVenue
  t "beamer's inserts refuse like the internals: the built-in still stands"
    (warnCodes insertVenue == ["W0361"] &&
     Ir.headingLevels iDoc.body == #[0])
  t "the refusal says what the declared appearance gave it"
    (iDs.any fun d => d.code == "W0361" &&
      (d.message.splitOn "styled by the redefinition's rules and spacing").length == 2)
  t "an insert-spelled title reads its rules onto the built-in title page"
    (inTitleBlock iDoc fun b => match b with
      | .rule _ _ g => g.value.width == Dim.Length.ofSp (Dim.pt 3)
      | _ => false)
  t "an insert-spelled author reads its strut and weight, inside the canvas"
    (inTitleBlock iDoc fun b => match b with
      | .para #[.strut h, .styled .bold _] => h == Ir.titleAuthorStrut
      | _ => false)
  -- The native spellings, as rule-above fell out for the bars.
  let (nDoc, nDs) := elabStr ("\\documentclass{article}\\title{T}\\author{A. Name}" ++
    "\\style{titlepage}{ author-font = {\\bfseries}, author-strut = 18pt, after = 30pt }" ++
    "\\begin{document}\\maketitle\\end{document}")
  t "style titlepage author-strut and author-font reach the author line"
    (nDs.isEmpty && (inTitleBlock nDoc fun b => match b with
      | .para #[.strut h, .styled .bold _] =>
        h == { width := Dim.Length.ofSp (Dim.pt 18) }
      | _ => false))
  t "style titlepage after gaps the whole title block"
    (inTitleBlock nDoc fun b => match b with
      | .spaced g #[] => g.value.width == Dim.Length.ofSp (Dim.pt 30)
      | _ => false)
  -- A body that only echoes its parameter is not "empty": the probe
  -- binding sees the echo, so LaTeX's identity-renew idiom wins.
  t "an argument-echoing redefinition of a rendered built-in wins"
    ((elabStr ("\\documentclass{article}" ++
      "\\renewcommand{\\href}[2]{#2}" ++
      "\\begin{document}\\href{https://example.org}{kept}\\end{document}")).2.all
        (·.severity == .note))
  -- The sectioning idiom (ltsect.dtx): a definer whose body is one
  -- \@startsection call is a declarative rule over an existing heading,
  -- read as \style — never a refused redefinition. A negative afterskip
  -- is a run-in heading, not modelled: named and skipped.
  let secRule := "\\documentclass{article}\\renewcommand{\\section}{" ++
    "\\@startsection{section}{1}{\\z@}{-2.0ex \\@plus -0.5ex \\@minus -0.2ex}" ++
    "{1.5ex \\@plus 0.3ex}{\\large\\bf\\raggedright}}" ++
    "\\begin{document}\\section{A}\nx\\end{document}"
  let (secDoc, secDs) := elabStr secRule
  t "a \\@startsection renew is read as \\style, warning nothing"
    (secDs.all (·.severity == .note) &&
     ((secDoc.styles.find? "section").bind (·.after)).map (·.width) ==
       some { ex := 1500 })
  t "a negative beforeskip declares its magnitude"
    (((secDoc.styles.find? "section").bind (·.before)).map (·.width) ==
       some { ex := 2000 })
  t "the style group's plain forms spell out; alignment is not font"
    (((secDoc.styles.find? "section").bind (·.font)).isSome)
  -- A negative afterskip declares a run-in heading (ltsect.dtx). The
  -- engine's \paragraph *is* one — bold at the body size, an em quad —
  -- so a redefinition asking for exactly that is a declaration of what
  -- already renders (N0100, no warning); a foreign font or a run-in at a
  -- display level stays named and skipped.
  t "a run-in paragraph redefinition in the built-in's own font is satisfied"
    (let src := "\\documentclass{article}\\renewcommand{\\paragraph}{" ++
      "\\@startsection{paragraph}{4}{\\z@}{1.5ex}{-1em}{\\normalsize\\bf}}" ++
      "\\begin{document}\\paragraph{P}\nx\\end{document}"
     warnCodes src == [] &&
       (elabStr src).1.body ==
         #[.para #[.styled .bold #[.text "P"], .text "\u2003x"]])
  t "a run-in redefinition in a foreign font is named, skipped"
    (warnCodes ("\\documentclass{article}\\renewcommand{\\paragraph}{" ++
      "\\@startsection{paragraph}{4}{\\z@}{1.5ex}{-1em}{\\normalsize\\it}}" ++
      "\\begin{document}\\paragraph{P}\nx\\end{document}") == ["W0104"])
  t "a run-in section is not modelled at a display level: named, skipped"
    (warnCodes ("\\documentclass{article}\\renewcommand{\\section}{" ++
      "\\@startsection{section}{1}{\\z@}{1.5ex}{-1em}{\\normalsize\\bf}}" ++
      "\\begin{document}\\section{S}\nx\\end{document}") == ["W0104"])
  -- LaTeX classes space paragraphs by indent: their parskip is zero unless
  -- KOMA's option or the parskip package says otherwise.
  t "compat koma class declares parskip zero"
    ((elabStr ("\\documentclass{scrartcl}\\begin{document}x\\end{document}")).1.page.parskip ==
      some { width := Dim.Length.ofSp 0 })
  t "compat koma parskip=half is half a line"
    (((elabStr ("\\documentclass[parskip=half]{scrartcl}\\begin{document}x\\end{document}")).1.page.parskip.map
      (·.width.em)) == some 600)
  t "compat parskip package"
    (((elabStr ("\\documentclass{article}\\usepackage{parskip}\\begin{document}x\\end{document}")).1.page.parskip.map
      (·.width.em)) == some 600)
  t "compat setlength parskip"
    ((elabStr (pre "\\setlength{\\parskip}{4pt}")).1.page.parskip == some { width := Dim.Length.ofSp (Dim.pt 4) })
  t "a native article keeps the engine's parskip"
    ((elabStr "\\documentclass{article}\\begin{document}x\\end{document}").1.page.parskip == none)
  -- \newcommand and \NewDocumentCommand become \define, with #k as \ak.
  let (ndc, ndcDs) := elabStr ("\\documentclass{article}" ++
    "\\NewDocumentCommand{\\role}{m o}{\\textbf{#1}\\IfValueT{#2}{ (#2)}}" ++
    "\\begin{document}\\role{A}[B] \\role{C}\\end{document}")
  t "compat xparse command clean" (ndcDs.all (·.severity == .note))
  t "compat xparse command expands with optional"
    (ndc.body == #[.para #[.role "role" #[.styled .bold #[.text "A"], .text " (B)"],
      .text " ", .role "role" #[.styled .bold #[.text "C"]]]])
  let (nc, _) := elabStr ("\\documentclass{article}\\newcommand{\\two}[2]{#1+#2}" ++
    "\\begin{document}\\two{a}{b}\\end{document}")
  t "compat newcommand expands" (nc.body == #[.para #[.role "two" #[.text "a+b"]]])
  -- Outside a macro body, # is a colour, not a parameter.
  t "compat hash outside a body is literal"
    ((elabStr (pre "\\palette{ p = #7C3AED }")).1.palette.find? "p" == some { r := 0x7C, g := 0x3A, b := 0xED })
  -- Body-side idioms.
  t "compat color is the declaration form"
    ((elabStr ("\\documentclass{article}\\palette{m = #666666}\\begin{document}" ++
      "a {\\color{m}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0x66, g := 0x66, b := 0x66 } (some "m") #[.text "b"], .text " c"]])
  -- `\color`'s argument is a palette *expression*: the `!`-mix grammar lives
  -- once, in `Palette.resolve`, and the bare-name arm routes through it.
  -- Before, `\color{m!50!black}` minted '\m!50!black' as a control word and
  -- the mix warned W0301 with its content losing the colour (run-verified
  -- wrong output). A computed mix carries no CSS var name, as `\textcolor`
  -- already holds.
  t "compat color mix routes through the palette resolver"
    ((elabStr ("\\documentclass{article}\\palette{m = #666666}\\begin{document}" ++
      "a {\\color{m!50!black}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0x33, g := 0x33, b := 0x33 } none #[.text "b"],
        .text " c"]])
  t "compat color black needs no declaration"
    ((elabStr ("\\documentclass{article}\\begin{document}" ++
      "a {\\color{black}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0, g := 0, b := 0 } none #[.text "b"],
        .text " c"]])
  t "compat text symbols" ((elabStr "a\\textbar b\\textperiodcentered c").1.body ==
    #[.para #[.text "a|b·c"]])
  -- The fixed text spaces are table rows with TeXbook widths as Unicode's
  -- own space characters; the logos set as their plain words.
  t "compat quad family are fixed spaces"
    ((elabStr "a\\quad b\\qquad c\\enspace d").1.body ==
      #[.para #[.text "a\u2003b\u2003\u2003c\u2002d"]])
  t "compat logos and textcomp symbols are text"
    ((elabStr "\\LaTeX{} and \\TeX{}, 90\\textdegree, 5\\texteuro").1.body ==
      #[.para #[.text "LaTeX and TeX, 90°, 5€"]])
  -- \url is \href's one-argument mono sibling: the URL is its own text,
  -- set typewriter (url.sty's \urlstyle{tt} default).
  t "url is a mono self-link"
    ((elabStr "\\url{https://example.org/a_b}").1.body ==
      #[.para #[.link "https://example.org/a_b"
        #[.styled .mono #[.text "https://example.org/a_b"]]]])
  -- \urlstyle names the family, honoured where \url elaborates (url.sty's
  -- own semantics): tt the mono family, rm the roman, sf the sans, same the
  -- face in force — no family style at all. url.sty's default is tt, so the
  -- selector-free form above is the tt form.
  t "urlstyle picks the family, and same picks none"
    (let bodyOf (v : String) : Array Ir.Block :=
       (elabStr ("\\documentclass{article}\\usepackage{url}\\urlstyle{" ++ v ++
         "}\\begin{document}\\url{https://example.org/a}\\end{document}")).1.body
     bodyOf "tt" == #[.para #[.link "https://example.org/a"
         #[.styled .mono #[.text "https://example.org/a"]]]] &&
       bodyOf "rm" == #[.para #[.link "https://example.org/a"
         #[.styled .roman #[.text "https://example.org/a"]]]] &&
       bodyOf "sf" == #[.para #[.link "https://example.org/a"
         #[.styled .sans #[.text "https://example.org/a"]]]] &&
       bodyOf "same" == #[.para #[.link "https://example.org/a"
         #[.text "https://example.org/a"]]])
  t "urlstyle (fails on base): a selector url.sty defines draws no warning"
    (let diagsOf (v : String) : Array Diag :=
       (elabStr (dvDoc ("\\usepackage{url}\\urlstyle{" ++ v ++ "}") "x")).2
     ["tt", "rm", "sf", "same"].all fun v =>
       (diagsOf v).all (·.severity != .warning))
  -- A definition standing between paragraphs binds from there on (the
  -- corpus's mid-document \newcommand); inline positions keep E0312.
  t "body define binds for the rest of the flow"
    (let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}Before.\n\n" ++
      "\\define \\hi(w: content) {Hello \\w}\n\\hi{there}\n\\end{document}")
     ds.all (·.severity == .note) &&
       doc.body.any (fun b => match b with
         | .para inls => inls.any (fun x => match x with
           | .role "hi" _ => true
           | _ => false)
         | _ => false))
  t "body newcommand rewrites and binds"
    ((elabStr ("\\documentclass{article}\\begin{document}a\n\n" ++
      "\\newcommand{\\x}{X}\n\\x\n\\end{document}")).2.all (·.severity == .note))
  -- \today is an input, not content the document carries: the artifact is
  -- a function of the document alone, so the clock is refused deliberately
  -- with its own message, never the generic unknown-command fall-through.
  t "compat today is refused deliberately"
    (let ds := (elabStr "Dated \\today.").2
     ds.any (fun d => d.code == "W0104") && ds.all (fun d => d.code != "W0301"))
  t "compat vspace is a spaced block"
    ((elabStr "a\n\n\\vspace{3pt}\nb").1.body.any fun b => match b with
      | .spaced _ _ => true
      | _ => false)
  t "compat expl3 is skipped whole"
    (warnCodes (pre "\\ExplSyntaxOn \\cs_new:Npn \\x { } \\ExplSyntaxOff") == ["W0106"])
  -- Inert commands vanish from the output but never wordlessly: a drop
  -- that is the construct's whole meaning is a note (\relax; \noindent,
  -- which asks for the no-indent every paragraph here already has), one
  -- the engine simply does not act on is the guard's W0387
  -- (\thispagestyle{plain}) — rewriteCtrl_accounts is the contract.
  t "compat inert commands vanish, accounted"
    (let ds := (elabStr "a\\noindent\\relax\\thispagestyle{plain} b").2
     ds.all (fun d => d.code == "N0100" || d.code == "W0387") &&
     ds.any (fun d => d.code == "W0387") &&
     (ds.filter (·.code == "N0100")).size == 2)
  t "compat noindent is agreement, never the guard's W0387"
    (let ds := (elabStr (dvDoc "" "\\noindent x")).2
     ds.all (·.code != "W0387") &&
     ds.any (fun d => d.code == "N0100" && hasStr d.message "noindent"))
  -- The silent list is only for constructs that change nothing the engine
  -- models; one that does (justification, hyphenation language, furniture)
  -- must name its loss instead of vanishing — or, once implemented, map.
  t "compat raggedright maps mid-flow instead of naming a loss"
    ((elabStr "a\\raggedright b").1.body ==
      #[.para #[.text "a"], .ragged .left #[.para #[.text "b"]]])
  t "compat pagestyle names its loss and eats its argument"
    (let (doc, ds) := elabStr "\\pagestyle{headings}a"
     ds.any (·.code == "W0104") && doc.body == #[.para #[.text "a"]])
  -- Unsupported configuration is skipped as a whole construct — command,
  -- options, arguments — with one warning naming it. It must never leak its
  -- arguments into elaboration as stray content (that was an E0313 per
  -- construct, an error cascade from a preamble the body never needed).
  -- \usetheme is no longer skipped: it rewrites to \theme (M5b).
  -- The deck class, where beamer configuration belongs: under article the
  -- install would now (rightly) add W0355 for the bundle's inert furniture.
  let beamerPre := "\\documentclass{slides}\n" ++
    ("\\usetheme{moloch}\\usefonttheme{professionalfonts}" ++
    "\\setbeamercovered{transparent}\\addtobeamertemplate{block begin}{}{\\smallskip}" ++
    "\\setbeameroption{hide notes}") ++ "\n\\begin{document}x\\end{document}"
  t "compat beamer config skipped without errors" (errCodes beamerPre == [])
  -- \setbeamercovered{transparent}, \usefonttheme{professionalfonts}, and
  -- \setbeameroption{hide notes} no longer count: each agrees with what
  -- the engine already does and warns nothing. \addtobeamertemplate is
  -- the one construct left asking for templating that is not here.
  t "compat beamer config warns once per construct"
    ((warnCodes beamerPre).length == 1 && (warnCodes beamerPre).all (· == "W0104"))
  t "compat usetheme selects the bundle instead of warning"
    ((elabStr beamerPre).1.palette.find? "frametitlebg" |>.isSome)
  -- moloch is the maintained metropolis fork: both metropolis spellings
  -- select the shipped bundle instead of leaving the deck unthemed (W0319).
  -- The fixture is slides-class, where \usetheme belongs: under article the
  -- same install rightly warns W0355 (inert slides furniture).
  let slidesPre (decls : String) : String :=
    "\\documentclass{slides}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  t "compat usetheme metropolis is the moloch bundle"
    (((elabStr (slidesPre "\\usetheme{metropolis}")).1.palette.find? "frametitlebg" |>.isSome) &&
     ((elabStr (slidesPre "\\usetheme{m}")).1.palette.find? "frametitlebg" |>.isSome) &&
     warnCodes (slidesPre "\\usetheme{metropolis}") == [])
  t "compat beamer warnings name the native spelling"
    ((elabStr (pre "\\setbeamercolor{structure}{fg=black}")).2.any fun d =>
      d.code == "W0104" && ((d.help.getD "").splitOn "\\palette").length == 2)
  t "compat ifdefined resolves instead of skipping; untaken branch is silent"
    (warnCodes (pre "\\ifdefined\\x\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") == [])
  t "compat undecidable tex conditional skipped whole, contents included"
    (warnCodes (pre "\\ifx\\x\\y\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") ==
      ["W0104"])
  t "compat def defines through its body"
    (errCodes (pre "\\makeatletter\\def\\verbatim@font{\\footnotesize\\ttfamily}\\makeatother") == [])
  -- The declarative/programmable line: a plain \def with undelimited
  -- #1..#n parameters declares what \define declares and rewrites onto
  -- it; \edef and a delimited parameter text are expansion-time TeX,
  -- refused by name (W0357), never the blanket W0104 skip.
  t "compat plain def with parameters expands at its uses"
    ((elabStr ("\\documentclass{article}\\def\\both#1#2{#1 and #2}" ++
      "\\begin{document}\\both{a}{b}\\end{document}")).1.body ==
      #[.para #[.role "both" #[.text "a and b"]]])
  t "compat edef is refused by name"
    (warnCodes (pre "\\edef\\x{y}") == ["W0357"])
  t "compat delimited def is refused by name"
    (warnCodes (pre "\\def\\pair#1.#2{#1 and #2}") == ["W0357"])
  -- usrguide's triple: \providecommand keeps an existing definition —
  -- the one policy of the three that changes what a correct document
  -- means (the others need kernel names this pass cannot see).
  t "compat providecommand keeps the existing definition"
    ((elabStr ("\\documentclass{article}\\newcommand{\\v}{first}" ++
      "\\providecommand{\\v}{second}\\begin{document}\\v\\end{document}")).1.body ==
      #[.para #[.text "first"]])
  t "compat providecommand defines when nothing is bound"
    ((elabStr ("\\documentclass{article}\\providecommand{\\v}{only}" ++
      "\\begin{document}\\v\\end{document}")).1.body ==
      #[.para #[.text "only"]])
  t "compat renewcommand replaces through the one arm"
    ((elabStr ("\\documentclass{article}\\newcommand{\\v}{first}" ++
      "\\renewcommand{\\v}{second}\\begin{document}\\v\\end{document}")).1.body ==
      #[.para #[.text "second"]])
  -- enumitem's per-instance [keys] and \item's [marker] override are
  -- consumed and named: the bracket used to land as content before the
  -- first \item (a false E0310 error) or as the item's own text (silent
  -- wrong output).
  t "list instance options are consumed and named, never E0310"
    (let src := "\\documentclass{article}\\begin{document}\\begin{itemize}[leftmargin=2em]" ++
      "\\item a\\end{itemize}\\end{document}"
     errCodes src == [] && (elabStr src).2.any (fun d => d.code == "N0102"))
  t "item marker override is consumed and named"
    (let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}\\begin{itemize}" ++
      "\\item[--] a\\end{itemize}\\end{document}")
     warnCodes ("\\documentclass{article}\\begin{document}\\begin{itemize}" ++
       "\\item[--] a\\end{itemize}\\end{document}") == ["W0110"] &&
     doc.body == #[.list false #[#[.para #[.text "a"]]]] && ds.all (·.code != "E0310"))
  -- All four ragged spellings are the engine's own, on both sides: neither
  -- unknown (W0301) nor a named loss (W0104). The row was written when the
  -- right pair was refused and asserted only that it was refused *by name*;
  -- the carrier retires the refusal, so the row asserts the whole claim.
  t "every alignment declaration is implemented, not refused"
    (let ds := (elabStr "{\\flushleft a} {\\raggedleft b} {\\flushright c}").2
     ds.all fun d => d.code != "W0301" && d.code != "W0104")
  -- \flushleft/\raggedright as commands map onto the alignment their
  -- environment sets (ltmiscen.dtx: {flushleft} is a trivlist under
  -- \raggedright), scoped by the group exactly as \centering is.
  t "flushleft as a command sets the rest of its scope ragged"
    (let (doc, ds) := elabStr "{\\flushleft one} two"
     doc.body == #[.ragged .left #[.para #[.text "one"]], .para #[.text "two"]] &&
       ds.all (fun d => d.code != "W0104" && d.code != "W0301"))
  t "raggedright maps as flushleft does"
    ((elabStr "{\\raggedright a}").1.body == #[.ragged .left #[.para #[.text "a"]]])
  -- The right-side twins, through the same one naming site
  -- (`Ir.raggedSideOf?`): the declaration and the environment both land on
  -- the mirror side, and neither reports a loss.
  t "raggedleft sets the rest of its scope flush right"
    (let (doc, ds) := elabStr "{\\raggedleft one} two"
     doc.body == #[.ragged .right #[.para #[.text "one"]], .para #[.text "two"]] &&
       ds.all (fun d => d.code != "W0104" && d.code != "W0301"))
  -- The environments are trivlists and open `\topsep` (ltlists.dtx), so
  -- their scope rides in the engine's trivlist role; the declarations open
  -- the same scope and no space.
  t "the flushright environment sets the mirror block"
    (let (doc, ds) := elabStr "\\begin{flushright}a\\end{flushright}"
     doc.body == #[.role Ir.trivlistRole #[.ragged .right #[.para #[.text "a"]]]] &&
       ds.all (fun d => d.code != "W0302" && d.code != "W0104"))
  t "flushright as a command maps as raggedleft does"
    ((elabStr "{\\flushright a}").1.body == #[.ragged .right #[.para #[.text "a"]]])
  t "the flushleft environment sets the same block"
    (let (doc, ds) := elabStr "\\begin{flushleft}a\\end{flushleft}"
     doc.body == #[.role Ir.trivlistRole #[.ragged .left #[.para #[.text "a"]]]] &&
       ds.all (fun d => d.code != "W0302"))
  t "flushleft inside an argument aligns nothing, named W0108"
    ((warnCodes "\\textbf{\\flushleft a}").contains "W0108")
  t "ragged text is census content"
    (Ir.blockTextList "" [.ragged .left #[.para #[.text "a b"]]] == "a b")
  t "compat newenvironment defines; its titlegraphic content is a dropped loss"
    (let src := pre "\\newenvironment{wrap}[1]{\\titlegraphic{#1}}{\\titlegraphic{}}"
     errCodes src == ["E0112"] && warnCodes src == ["W0104"])
  -- Overlay specifications elaborate to steps; the content stays.
  t "uncover wraps its content in a step"
    ((elabStr "a \\uncover<2>{shown} b").1.body ==
      #[.para #[.text "a ", .step 2 (some 2) #[.text "shown"], .text " b"]])
  t "pause between words steps the rest of the scope"
    ((elabStr "a \\pause b").1.body ==
      #[.para #[.text "a"], .step 2 none #[.para #[.text "b"]]])
  t "unnumbered overlay specs warn once for the whole document"
    ((warnCodes "\\uncover<+->{a} \\uncover<.->{b}").length == 1)
  t "item overlay spec wraps the item"
    ((elabStr "\\begin{itemize}\\item<1-> one\\end{itemize}").1.body ==
      #[.list false #[#[.step 1 none #[.para #[.text "one"]]]]])
  t "compat alert is textbf"
    ((elabStr "\\alert{hot}").1.body == #[.para #[.styled .bold #[.text "hot"]]])
  t "compat bigskip is a spaced block"
    ((elabStr "a\n\n\\bigskip\nb").1.body.any fun b => match b with
      | .spaced _ _ => true
      | _ => false)
  let koma := elabStr (pre ("\\definecolor{ink}{HTML}{112233}\\newlength{\\s}\\setlength{\\s}{3pt}" ++
    "\\setkomafont{section}{\\large\\sffamily\\color{ink}}" ++
    "\\RedeclareSectionCommand[beforeskip=2\\s,afterskip=1\\s]{section}" ++
    "\\setlist[itemize]{leftmargin=1.2em,itemsep=\\s,label={\\color{ink}\\textendash}}" ++
    "\\makeatletter\\renewcommand\\sectionlinesformat[4]{#3#4 \\textcolor{ink}{\\leaders\\hrule\\hfill}}\\makeatother" ++
    "\\thispagestyle{empty}\\ihead{L}"))
  t "compat koma section font" ((koma.1.styles.find? "section").bind (·.font) ==
    some #[.styled (.size "large") #[.styled .sans #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[]]]])
  -- KOMA's disposition element is every sectioning level's font at once
  -- (KOMA-Script manual ch. 4): one declaration fans out to the heading
  -- elements the engine draws; a later per-level \setkomafont wins per
  -- key, the engine's replace-on-redeclare.
  let dispo := elabStr (pre ("\\setkomafont{disposition}{\\bfseries}" ++
    "\\setkomafont{section}{\\sffamily}"))
  t "compat koma disposition styles every heading level"
    (((dispo.1.styles.find? "subsection").bind (·.font) ==
        some #[.styled .bold #[]]) &&
      ((dispo.1.styles.find? "subsubsection").bind (·.font) ==
        some #[.styled .bold #[]]) &&
      ((dispo.1.styles.find? "section").bind (·.font) ==
        some #[.styled .sans #[]]) &&
      dispo.2.all (·.code != "W0111"))
  t "compat koma section spacing"
    (((koma.1.styles.find? "section").bind (·.before)).map (·.width) == some { sp := Dim.pt 6 })
  t "compat koma section rule" (((koma.1.styles.find? "section").bind (·.rule)).map (·.2) == some (some "ink"))
  -- The TeX rule's own geometry rides along: `\hrule` has zero depth, so
  -- the reading is a baseline rule, and its `height` is the thickness —
  -- TeX's 0.4 pt default when none is written (TeXbook p. 221). A height
  -- the length grammar cannot read is said (E0321), never defaulted.
  t "compat koma section rule is a baseline rule at TeX's default height"
    ((koma.1.styles.find? "section").map (fun st => (st.rulePosition, st.ruleThickness.map (·.width.sp)))
      == some (some .baseline, some (Dim.pt 4 / 10)))
  let ruleH (h : String) := elabStr (pre ("\\definecolor{ink}{HTML}{112233}\\makeatletter" ++
    s!"\\renewcommand\\sectionlinesformat[4]\{#3#4 \\textcolor\{ink}\{\\leaders\\hrule{h}\\hfill\\kern\\z@}}\\makeatother"))
  let thickOf (d : Ir.Doc × Array Diag) : Option Int :=
    ((d.1.styles.find? "section").bind (·.ruleThickness)).map (·.width.sp)
  t "compat koma section rule reads its declared height"
    (thickOf (ruleH " height 1.5pt") == some (Dim.pt 3 / 2))
  t "compat koma section rule reads a \\p@ height"
    (thickOf (ruleH " height .6\\p@") == some (Dim.pt 6 / 10))
  t "compat koma section rule with an unreadable height is said, colour kept"
    ((ruleH " height 0.6zz").2.any (·.code == "E0321") &&
      (((ruleH " height 0.6zz").1.styles.find? "section").bind (·.rule)).isSome)
  t "compat koma section rule with a depth is not the idiom"
    (errCodes (pre ("\\definecolor{ink}{HTML}{112233}\\makeatletter\\renewcommand\\sectionlinesformat[4]" ++
      "{#3#4 \\textcolor{ink}{\\leaders\\hrule height 1pt depth 1pt\\hfill}}\\makeatother")) == ["E0113"])
  t "compat enumitem list" (((koma.1.styles.find? "itemize").bind (·.gap)).map (·.width) == some { sp := Dim.pt 3 } &&
    ((koma.1.styles.find? "itemize").bind (·.marker)).isSome)
  t "compat thispagestyle empty starts running content on page 2" (koma.1.headFrom == 2)
  -- A \sectionlinesformat body that is not the rule idiom is a dropped
  -- loss and errors; an empty body asks for no decoration and is silent.
  t "compat unrecognised sectionlinesformat body is a dropped loss"
    (errCodes (pre "\\renewcommand\\sectionlinesformat[4]{\\raisebox{-1pt}{#3}}") ==
      ["E0113"])
  t "compat empty sectionlinesformat body is deliberate silence"
    ((elabStr (pre "\\renewcommand\\sectionlinesformat[4]{}")).2.all
      (·.severity == .note))
  -- Silence is fidelity (rewriteCtrl_accounts): a construct the dispatcher
  -- consumed either has an effect or is named. The two once-silent drops
  -- name their loss precisely; the generic residue is W0387, once per name.
  t "compat setlist on a non-styleable element is named, never silent"
    (warnCodes (pre "\\setlist[description]{leftmargin=2em}") == ["W0111"])
  t "compat RedeclareSectionCommand on a non-styleable element is named"
    (warnCodes (pre "\\RedeclareSectionCommand[beforeskip=1ex]{part}") == ["W0111"])
  t "compat RedeclareSectionCommand with no mappable key names its drop"
    (warnCodes (pre "\\RedeclareSectionCommand[font=\\large]{section}") == ["W0101"])
  t "compat silence guard warns W0387 once per name"
    (warnCodes ("\\documentclass{article}\\thispagestyle{plain}\\begin{document}" ++
      "a \\thispagestyle{plain} b\\end{document}") == ["W0387"])
  t "compat relax and makeatletter earn their silence as notes"
    (let ds := (elabStr (pre "\\makeatletter\\relax\\makeatother")).2
     ds.all (·.severity != .warning) && (ds.filter (·.code == "N0100")).size ≥ 3)
  t "compat clearpairofpagestyles clears the gathered fields"
    ((elabStr (pre "\\ihead{L}\\clearpairofpagestyles")).1.head == none)
  t "compat fields declared after clearpairofpagestyles apply"
    ((elabStr (pre "\\clearpairofpagestyles\\ihead{L}")).1.head != none)
  t "a bare note with no body is named, never silent"
    (errCodes (dvDeck "" "\\begin{frame}{T}\nx \\note\n\\end{frame}") == ["E0304"])

  -- A diagnostic inside an \input file names that file, not the including
  -- one, in the body and in the preamble both.
  let sub (file src : String) : Array Parse.Raw :=
    (Parse.parse file (Lex.lex file src).1).1
  let (inDoc, inDs) := Elab.runRaws "main.tex"
    #[Parse.Raw.env (Parse.inputEnv "sub.tex")
        (sub "sub.tex" "\\begin{mystery}kept\\end{mystery}") ⟨1, 1⟩]
  t "input body diagnostics name the included file"
    ((inDs.filterMap (·.span)).any (·.file == "sub.tex") &&
     inDoc.body == #[.para #[.text "kept"]])
  let (_, preDs) := Elab.runRaws "main.tex"
    (#[Parse.Raw.env (Parse.inputEnv "pre.tex") (sub "pre.tex" "\\mystery{x}") ⟨1, 1⟩] ++
      sub "main.tex" "\\begin{document}y\\end{document}")
  t "input preamble diagnostics name the included file"
    ((preDs.filterMap (·.span)).any (·.file == "pre.tex") &&
     !(preDs.filterMap (·.span)).any (·.file == "main.tex"))

/-- Class options and `\page` keys are one vocabulary: `*paper` names a size
from the same `pageSizes` table `\page{ size = ... }` reads, `landscape`
swaps the axes, and a `\page` declaration wins. `twocolumn` and `draft` are
refused by name (W0356) — the silent drop was the defect class (an a4paper
request quietly shipped on letter). -/
def classOptionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pageOf (opts : String) (pre : String := "") : Ir.PageSpec :=
    (elabStr s!"\\documentclass[{opts}]\{article}{pre}\\begin\{document}x\\end\{document}").1.page
  t "class option a4paper sets the page size"
    (let p := pageOf "a4paper"
     p.width == Dim.pt 595 && p.height == Dim.pt 842)
  t "class option letterpaper and KOMA paper= set the page size"
    ((pageOf "letterpaper").width == Dim.pt 612 && (pageOf "paper=a5").width == Dim.pt 420)
  t "class option landscape swaps the axes"
    (let p := pageOf "a4paper,landscape"
     p.width == Dim.pt 842 && p.height == Dim.pt 595)
  t "a declared page wins over the class option"
    ((pageOf "a4paper" "\\page{ size = a5 }").width == Dim.pt 420)
  t "class options twocolumn and draft are refused by name"
    ((warnCodes "\\documentclass[twocolumn,draft]{article}\\begin{document}x\\end{document}")
      == ["W0356", "W0356"])
  t "class option a4paper warns nothing"
    ((elabStr "\\documentclass[a4paper,11pt]{article}\\begin{document}x\\end{document}").2.all
      (·.severity == .note))
  -- The slides stage is the same one-key vocabulary: every beamer
  -- `aspectratio=` option resolves through `Ir.slidesStages`, and
  -- `\page{ size = 16:9 }` names the same row natively (`141` — beamer's
  -- √2:1 digits — arrives as an int and still names its row).
  let deckOf (opts : String) (pre : String := "") : Ir.PageSpec :=
    (elabStr s!"\\documentclass[{opts}]\{slides}{pre}\\begin\{document}x\\end\{document}").1.page
  t "every beamer aspectratio option selects its documented stage"
    (Ir.slidesStages.all fun r =>
      let p := deckOf s!"aspectratio={String.ofList (r.1.toList.filter (· != ':'))}"
      p.width == r.2.1 && p.height == r.2.2)
  t "an unknown aspectratio keeps beamer's 4:3 default"
    ((deckOf "aspectratio=679").height == Ir.slidesStage43.2)
  t "the native size key names the stage the option names"
    (let p := deckOf "" "\\page{ size = 16:10 }"
     p.width == Dim.mm 160 && p.height == Dim.mm 100 &&
       p == deckOf "aspectratio=1610")
  t "beamer's bare digits name the root-two stage"
    (let p := deckOf "" "\\page{ size = 141 }"
     p.width == Dim.mm100 14850 && p.height == Dim.mm 105)
  t "an unknown ratio size is refused by name"
    (errCodes ("\\documentclass{slides}\\page{ size = 17:9 }" ++
      "\\begin{document}x\\end{document}") == ["E0324"])

/-- The lineno page keys at the elaboration tier: the declared flag and
its modulus land on the spec, the LaTeX spellings translate onto them, and
a bad value is refused by name. The drawn contract — every counted line
numbered at its baseline, consecutively across pages — lives in the census
(`censusTable`'s lineno rows), never here: goldens and specs witness
elaboration only. -/
def linenoChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pageOf (pre : String) : Ir.PageSpec :=
    (elabStr s!"\\documentclass\{article}{pre}\\begin\{document}x\\end\{document}").1.page
  t "the declared flag lands on the spec"
    ((pageOf "\\page{ linenumbers = on }").linenumbers == some true)
  t "linenumbers translates on, nolinenumbers off, the last declaration wins"
    ((pageOf "\\usepackage{lineno}\\linenumbers").linenumbers == some true &&
     (pageOf "\\usepackage{lineno}\\linenumbers\\nolinenumbers").linenumbers
       == some false)
  t "modulolinenumbers lands its modulus; the bare form is the documented five"
    ((pageOf "\\usepackage{lineno}\\modulolinenumbers[4]").lineModulo == some 4 &&
     (pageOf "\\usepackage{lineno}\\modulolinenumbers").lineModulo == some 5)
  t "the modulo package option is the same five"
    ((pageOf "\\usepackage[modulo]{lineno}").lineModulo == some 5)
  t "a bad flag and a zero modulus are refused by name"
    (errCodes ("\\documentclass{article}\\page{ linenumbers = maybe, modulo = 0 }" ++
      "\\begin{document}x\\end{document}") == ["E0323", "E0323"])
  t "the pagewise option is refused named"
    ((warnCodes ("\\documentclass{article}\\usepackage[pagewise]{lineno}" ++
      "\\begin{document}x\\end{document}")) == ["W0101"])
  t "no class turns line numbers on"
    ((pageOf "").linenumbers == none &&
     !(elabStr "\\documentclass{article}\\begin{document}x\\end{document}").1.lineNumbersOn)

/-- The row spelling the effect check reads as its counterfactual: every
control word in the call becomes a name the engine cannot know (`\emph` →
`\emphZq`; digits are not name characters, so no package spells one). The
call's literal text, braces and structure are untouched, so the two arms of
the comparison differ in exactly one thing — whether the engine recognises
the commands. A control symbol (`\\`, `\;`, `\$`) is left alone: renaming
one would insert a control word the source never had. -/
def compatUnknown (call : String) : String := Id.run do
  let mut out := ""
  let mut st : Nat := 0
  for c in call.toList do
    if st == 2 && !c.isAlpha then
      out := out ++ "Zq"
      st := 0
    if st == 1 then
      st := if c.isAlpha then 2 else 0
      out := out.push c
    else if c == '\\' then
      st := 1
      out := out.push c
    else
      out := out.push c
  if st == 2 then out := out ++ "Zq"
  return out

/-- The one predicate every `impl` row answers to: recognising this call
changes the elaborated document. Both arms elaborate the same source; the
baseline's control words are the same call with names the engine does not
know, so a command that contributes nothing lands in the same `Ir.Doc` as
the command the engine never heard of, and the row fails. Silence about
W0301 says only that the name was consumed — a native command that
regressed to a no-op keeps that silence, which is how
`\AtBeginDocument{}` held an `impl` claim while the hook body was never
deferred anywhere. The claim is about the call as written: a call naming
several commands is witnessed as a whole, so a row that wants one
command's effect attributed to it writes a call with one command. -/
def compatRowEffect (pkg place call : String) : Bool :=
  (elabStr (compatRowSrc pkg place call)).1
    != (elabStr (compatRowSrc pkg place (compatUnknown call))).1

/-- The invariant whose absence left the hook inert: a hook is a DEFERRED
declaration, so its body is not read where it stands but replayed at the
point the hook names. Read where it stood — in the preamble — an empty body
changed nothing, text in it was refused as preamble material and a `\section`
in it went unknown and vanished, and the index could not see any of that
through the one argument it probed.

The claim about what the page shows is read off `Layout.Out`, never off the
IR: a hook body carrying content has to arrive as ink.

`\AtEndPreamble` is the same mechanism at the other point, which is what
makes the two distinguishable: a declaration deferred to the end of the
preamble applies, and content deferred there is still not body content. -/
def hookChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let face ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"hook fixture: {e}")
  let fs := oneFaceOf face
  -- Every glyph the page ships, in page order: what "it landed in the body"
  -- means when the question is about ink.
  let shippedText (src : String) : String :=
    let out := layoutOf fs (elabStr src).1
    ((allLines out).flatMap (·.segs)).foldl (init := "") fun s seg => match seg with
      | .run _ _ _ _ gs _ _ _ _ _ => s ++ String.ofList (gs.map (·.2)).toList
      | _ => s
  let hook (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- (1) A hook body carrying content ships, on the page, before the body's
  -- own first paragraph. Before: E0313, and nothing shipped.
  let textHook := hook "\\AtBeginDocument{hooked}" "written"
  t "a hook body's text ships on the page" (hasStr (shippedText textHook) "hooked")
  t "the hook's text ships before the document's own"
    (let s := shippedText textHook
     match (s.splitOn "hooked").head?, (s.splitOn "written").head? with
     | some a, some b => a.length < b.length
     | _, _ => false)
  t "a hook body carrying text is no longer refused as preamble material"
    (errCodes textHook == [] && warnCodes textHook == [])
  -- (2) A heading in a hook body is a heading, not an unknown command.
  let secHook := hook "\\AtBeginDocument{\\section{Hooked}}" "written"
  t "a hook body's section is a section, not an unknown command"
    (warnCodes secHook == [] &&
      (elabStr secHook).1.body.any fun b => match b with
        | .section .. => true
        | _ => false)
  t "the hooked section ships its own text" (hasStr (shippedText secHook) "Hooked")
  -- (3) The declaration half still reaches the preamble: the seam has two
  -- sides, and a hook carrying configuration is why.
  let geoHook := hook "\\AtBeginDocument{\\newgeometry{textwidth=396pt, textheight=576pt}}" "x"
  t "a hook body's declaration reaches the preamble"
    ((elabStr geoHook).1.page.hmargin == Dim.pt 108 &&
      (elabStr geoHook).1.page.vmargin == Dim.pt 108)
  t "a hook mixing a declaration and content honours both"
    (let mixed := hook
      "\\AtBeginDocument{\\newgeometry{textwidth=396pt, textheight=576pt}seen}" "x"
     (elabStr mixed).1.page.hmargin == Dim.pt 108 && hasStr (shippedText mixed) "seen")
  -- (4) Declaration order is replay order (ltfiles.dtx appends). Interword
  -- space is its own segment, so the claim is over the glyphs' order.
  t "hook bodies replay in declaration order"
    (hasStr (shippedText (hook "\\AtBeginDocument{one}\\AtBeginDocument{two}" "three"))
      "onetwothree")
  -- (5) The second instance of the one mechanism, at the other point.
  t "AtEndPreamble defers a declaration to the end of the preamble"
    ((elabStr (hook "\\AtEndPreamble{\\newgeometry{textwidth=396pt, textheight=576pt}}"
      "x")).1.page.hmargin == Dim.pt 108)
  t "the two points are distinguishable: content deferred to the preamble is not body content"
    (errCodes (hook "\\AtEndPreamble{x}" "y") == ["E0313"])
  -- (6) The self-declaring hook: a replay cannot re-collect. The nested
  -- hook's group is read where it stands — nothing is lost, nothing defers
  -- twice, and elaboration terminates.
  let nested := hook "\\AtBeginDocument{a\\AtBeginDocument{b}c}" "d"
  t "a hook declared inside a replayed hook body does not defer again"
    (warnCodes nested == ["W0340"])
  t "the self-declaring hook loses none of its text"
    (hasStr (shippedText nested) "abc")
  t "a hook written in the body reads its group where it stands"
    (let inBody := hook "" "p\\AtBeginDocument{q}r"
     warnCodes inBody == ["W0340"] && hasStr (shippedText inBody) "pqr")

/-- The seam's preamble side may not drift from the engine's own answer to
"which declarations does the body refuse". `Compat.hookPreambleSide` restates
`Elab.declCtrl ++ Elab.runningCtrl` because it sits below this module and
cannot import it; a name added to either list and not the other would route a
hook's declaration into the body, where it would be named misplaced and
silently lost. Loud in both directions. -/
def hookSeamChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref "the hook seam's preamble side is exactly the engine's preamble-only declarations"
    (Compat.hookPreambleSide == Elab.declCtrl ++ Elab.runningCtrl)

/-- The invariant whose absence lost the face: `\url` and `\nolinkurl`
resolve at ONE site, so on the shipped page their runs agree in everything
but the link. Two sites is how the face went missing — the URL was set as
plain text, which is byte-identical to dropping an unknown command — so the
claim is read off `Layout.Out`, where the face is a fact about the page,
never off the IR. The face is the document's mono family, so the check needs
a set where mono is a *different* index from the body: one face maps every
slot to 0 and could not tell the two apart. Both faces ship in
`tests/corpus/fonts`. -/
def urlFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (p : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ p)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"url face fixture: {p}: {e}")
  let body ← load "SourceSerifPro-Regular.otf"
  let code ← load "SourceCodePro-Regular.otf"
  let twoFace : Font.FontSet :=
    { fonts := #[body, code]
      index := ((List.range 3).flatMap fun slot =>
        let i := if slot == 2 then 1 else 0
        [((slot, 400, false), i), ((slot, 700, false), i),
         ((slot, 400, true), i), ((slot, 700, true), i)]).toArray }
  let url := "https://example.org"
  -- The projection the two commands must agree on: face, metrics, glyphs,
  -- size. The link is the one difference, and the underline is the link's
  -- own affordance (`linkSignalChecks`), so both stay out of the projection.
  let runsOf (call : String) : Array ((Nat × Int × Array (Nat × Char) × Int) × Bool × Bool) :=
    let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\nsee " ++
      call ++ " here\n\\end{document}")).1
    let segs := (allLines (layoutOf twoFace doc)).flatMap (·.segs)
    segs.filterMap fun s => match s with
      | .run fi _ link w gs sz ul _ _ _ =>
        if String.ofList (gs.map (·.2)).toList == url then
          some ((fi, w, gs, sz), link.isSome, ul)
        else none
      | _ => none
  let linked := runsOf s!"\\url\{{url}}"
  let plain := runsOf s!"\\nolinkurl\{{url}}"
  let monoIdx (rs : Array ((Nat × Int × Array (Nat × Char) × Int) × Bool × Bool)) : Bool :=
    !rs.isEmpty && rs.all fun r => r.1.1 == 1
  t "url ships the URL in the mono face" (monoIdx linked)
  -- The gap: \nolinkurl shipped the body face, the same ink an unknown
  -- command's leftover text ships.
  t "nolinkurl ships the URL in the mono face too" (monoIdx plain)
  t "url and nolinkurl agree on the shipped face, metrics and glyphs"
    (linked.map (·.1) == plain.map (·.1))
  t "the link is the one difference: url links and underlines, nolinkurl does neither"
    (!linked.isEmpty && linked.all (fun r => r.2.1 && r.2.2) &&
      !plain.isEmpty && plain.all (fun r => !r.2.1 && !r.2.2))
  -- Neither is an unknown command, and neither loses its group.
  t "nolinkurl is recognised, not dropped"
    (warnCodes (dvDoc "" s!"\\nolinkurl\{{url}}") == [])

/-- The package-claim index: every package in `Compat.nativePackages` ships
`tests/compat-index/<pkg>.txt`, its user-facing command surface as
reviewable data — one line per command, `<place> <annotation> <call>`,
place `pre` | `body` | `frame` (a `beamer` frame body, for the class's own
surface — a class loads by `\documentclass`, never `\usepackage`),
annotation `impl` | `inert:<why>` | `refuse:<code>`. An `impl` call
elaborates without W0301/W0302 — nor W0012, the math parser's answer to a
name it does not know, under which a formula is its own source text and so
differs from the renamed call by its spelling alone — *and* changes the
document by being recognised (`compatRowEffect`); a `refuse:` call fires exactly its named
code, so a refusal that silently stops warning fails too. Adding a package
to the list without its index file fails: the claim and its evidence
arrive together. Every file in the directory is probed, not only the
native list's: a deliberately refused package (todonotes) records its
stance as refuse rows, and those rows are load-bearing the same way.

`inert:<why>` is how a row says its command legitimately moves no ink — a
binding read at a later use site, a value already in force, a construct the
engine answers by design with nothing. The decision is written in the row
that needs it, never as an exception list here, which would drift from the
directory the way a second list always does; and it is loud in both
directions, as a corpus file's own exclusion is: an `inert` row whose
command starts changing the document fails until someone promotes it. The
`why` may not be empty — a row that moves no ink says why it does not. -/
def compatIndexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let dir : System.FilePath := "tests/compat-index"
  for pkg in Compat.nativePackages do
    let found ← (dir / (pkg ++ ".txt")).pathExists
    check ref s!"compat index: '{pkg}' is claimed native but has no index file" found
  for entry in (← dir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless entry.endsWith ".txt" do continue
    let pkg := (entry.dropEnd ".txt".length).toString
    let content ← IO.FS.readFile (dir / entry)
    for line in content.splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      let place := ((line.splitOn " ").headD "")
      let rest := (line.drop place.length).toString.trimAscii.toString
      let ann := ((rest.splitOn " ").headD "")
      let call := (rest.drop ann.length).toString.trimAscii.toString
      let src := compatRowSrc pkg place call
      let codes := (elabStr src).2.map (·.code)
      if place != "pre" && place != "body" && place != "frame" then
        failures ref s!"compat index {pkg}: unreadable place in: {line}"
      else if ann == "impl" then
        check ref s!"compat index {pkg}: '{call}' is marked impl but warns unknown"
          (!codes.contains "W0301" && !codes.contains "W0302" && !codes.contains "W0012")
        check ref s!"compat index {pkg}: '{call}' is marked impl but the document \
is the same one the engine elaborates when it knows none of these commands — \
say why with inert:<why>, or probe the command where its effect lands"
          (compatRowEffect pkg place call)
      else if ann.startsWith "inert:" then
        let why := (ann.drop "inert:".length).toString
        check ref s!"compat index {pkg}: '{call}' is marked inert but says no why"
          (!why.isEmpty)
        check ref s!"compat index {pkg}: '{call}' is marked inert but warns unknown"
          (!codes.contains "W0301" && !codes.contains "W0302" && !codes.contains "W0012")
        check ref s!"compat index {pkg}: '{call}' is marked inert:{why} yet now \
changes the document — promote it to impl"
          (!compatRowEffect pkg place call)
      else if ann.startsWith "refuse:" then
        let code := (ann.drop "refuse:".length).toString
        check ref s!"compat index {pkg}: '{call}' no longer fires {code}"
          (codes.contains code)
      else
        failures ref s!"compat index {pkg}: unreadable annotation in: {line}"

/-- The note is the rewrite: each arm's replacement elaborates to exactly
the document its N0100 note names — whole-`Doc` equality between the LaTeX
spelling and the native spelling, per arm. This is the executable form of
the owed per-arm conservation statement (an oracle, not a theorem: the
statement over the monadic walk needs the applyDecl fold extraction PLAN
names as T1's precondition), and the geometry pair is the template both
audits asked to state first. -/
def compatConservationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (decls body : String) : String :=
    s!"\\documentclass\{article}\n{decls}\n\\begin\{document}\n{body}\n\\end\{document}"
  let pairs : List (String × String × String) := [
    ("geometry options", wrap "\\usepackage[a4paper,margin=2cm]{geometry}" "x",
      wrap "\\page{ size = a4, margin = 2cm }" "x"),
    ("geometry command", wrap "\\usepackage{geometry}\\geometry{margin=1in}" "x",
      wrap "\\page{  }\\page{ margin = 1in }" "x"),
    ("crop cam", wrap "\\usepackage[cam]{crop}" "x",
      wrap "\\page{ marks = cut }" "x"),
    ("linespread", wrap "\\linespread{1.05}" "x", wrap "\\page{ leading = 1.05 }" "x"),
    ("setstretch", wrap "\\setstretch{1.3}" "x", wrap "\\page{ leading = 1.3 }" "x"),
    ("onehalfspacing", wrap "\\onehalfspacing" "x", wrap "\\page{ leading = 1.25 }" "x"),
    ("definecolor", wrap "\\definecolor{c}{HTML}{112233}" "x",
      wrap "\\palette{ c = #112233 }" "x"),
    ("colorlet", wrap "\\definecolor{c}{HTML}{112233}\\colorlet{d}{c}" "x",
      wrap "\\palette{ c = #112233 }\\palette{ d = c }" "x"),
    ("pagecolor", wrap "\\pagecolor{white}" "x",
      wrap "\\palette{ bg = white }" "x"),
    ("vspace", wrap "" "a\n\n\\vspace{3pt}\nb",
      wrap "" "a\n\n\\block[before = 3pt]{}\nb"),
    ("bigskip", wrap "" "a\n\n\\bigskip\nb",
      wrap "" "a\n\n\\block[before = 12pt plus 4pt minus 4pt]{}\nb"),
    ("newcommand", wrap "\\newcommand{\\hi}[1]{H #1}" "\\hi{x}",
      -- Up to parameter renaming: the rewrite mints `a1`, a name a control
      -- word cannot spell (digits are not name characters, as in TeX), so
      -- the arm's own note names a spelling no author can type — found by
      -- this oracle, recorded for a successor. Parameter names do not
      -- survive into the Doc, so the conservation statement itself is
      -- unaffected.
      wrap "\\define \\hi(w: content) {H \\w}" "\\hi{x}"),
    ("url", wrap "" "\\url{https://example.org}",
      wrap "" "\\href{https://example.org}{\\texttt{https://example.org}}"),
    ("enquote", wrap "" "\\enquote{x}", wrap "" "“x”"),
    ("setlist", wrap "\\setlist[itemize]{leftmargin=2em}" "x",
      wrap "\\style{itemize}{ indent = 2em }" "x"),
    ("biblatex", wrap "\\usepackage[style=numeric]{biblatex}\\addbibresource{refs.bib}"
      "\\autocite{k}\n\n\\printbibliography",
      wrap "" "\\citep{k}\n\n\\bibliographystyle{plain}\\bibliography{refs}"),
    ("fontface", wrap "\\setmainfont{Alpha Serif}[FontFace={l}{n}{Alpha Serif Light}]" "x",
      wrap "\\fonts{ body = \"Alpha Serif\", body.l = \"Alpha Serif Light\" }" "x")]
  for (nm, latex, native) in pairs do
    t s!"conserves {nm}" ((elabStr latex).1 == (elabStr native).1)

/-- Dimension evidence beyond the fixed vectors in `main`.

Cross-unit tests: every unit the table relates must parse to the same sp
(the theorem `Decl.unitScale_consistent` pins the table's fractions; these
pin the string-level wiring, including signs and `sp` itself).

Round-trip property test (generator: xorshift64*, 2000 values uniform in
±2³¹ sp): `toPtString` rounds to the nearest thousandth of a pt, so parsing
the printed value back must land within 33 sp (32.768 sp of print rounding
plus under 1 sp of parse truncation) and must never change unit kind. -/
def dimChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "dim 1pc is 12pt" (Decl.parseValue "1pc" == Decl.parseValue "12pt")
  t "dim 6pc is 1in" (Decl.parseValue "6pc" == Decl.parseValue "1in")
  t "dim 72bp is 1in" (Decl.parseValue "72bp" == Decl.parseValue "1in")
  t "dim 65536sp is 1pt" (Decl.parseValue "65536sp" == Decl.parseValue "1pt")
  t "dim 10mm is 1cm" (Decl.parseValue "10mm" == Decl.parseValue "1cm")
  t "dim negative is exact" (Decl.parseValue "-0.5in" == some (.dim (-(Dim.inch 1) / 2)))
  t "dim negative em is exact"
    (Decl.parseLength "-0.25em" == some { em := -250 })

  -- toPtString: exact thirds round to the nearest thousandth, tiny values
  -- collapse to "0" without a stray sign, halves round away from zero.
  t "sp pt string thirds" ((Dim.pt 1 / 3).toPtString == "0.333")
  t "sp pt string negative thirds" ((-(Dim.pt 1) / 3).toPtString == "-0.333")
  t "sp pt string eighth" (((8192 : Dim.Sp)).toPtString == "0.125")
  t "sp pt string tiny is unsigned zero" (((-26 : Dim.Sp)).toPtString == "0")
  t "sp pt string half milli rounds up" (((4096 : Dim.Sp)).toPtString == "0.063")

  let mut s : UInt64 := 0xA0761D6478BD642F
  let mut worst : Nat := 0
  let mut failed : Option String := none
  for _ in [0:2000] do
    let (mag, s') := rand s (2 ^ 32)
    s := s'
    let x : Dim.Sp := (mag : Int) - 2 ^ 31
    match Decl.parseLength (x.toPtString ++ "pt") with
    | some l =>
      let err := (l.sp - x).natAbs
      worst := max worst err
      unless l.em == 0 && l.ex == 0 && err ≤ 33 do
        failed := some s!"dim round-trip: {x} printed {x.toPtString}, reparsed {l.sp} (err {err})"
    | none => failed := some s!"dim round-trip: {x} printed {x.toPtString}, which did not parse"
  if let some msg := failed then failures ref msg
  t "dim round-trip error reaches the print rounding bound" (worst > 20)

/-- Differential fuzz of the UTF-8 validator against the core decoder
(generator: xorshift64*, 400 byte strings — half raw random bytes of length
0–15, half a valid encoded string with one byte overwritten): `validate`
must accept exactly what `String.fromUTF8?` decodes. The fixed vectors in
`main` pin the error kinds and offsets; this pins the accept/reject boundary
where no fixed vector was written. -/
def utf8FuzzChecks (ref : IO.Ref (List String)) : IO Unit := do
  let samples : Array String :=
    #["hello", "naïve", "αβγδε", "🎉🌍", "a\nb\nc", "τεχ — done", "𝔸𝔹ℂ"]
  let mut s : UInt64 := 0xE7037ED1A0B428DB
  let mut failed : Option String := none
  for i in [0:400] do
    let (mode, s') := rand s 2
    s := s'
    let mut v : ByteArray := ByteArray.empty
    if mode == 0 then
      let (len, s') := rand s 16
      s := s'
      for _ in [0:len] do
        let (b, s') := rand s 256
        s := s'
        v := v.push (UInt8.ofNat b)
    else
      let (which, s') := rand s samples.size
      s := s'
      v := samples[which]!.toUTF8
      let (at_, s') := rand s v.size
      s := s'
      let (b, s'') := rand s' 256
      s := s''
      v := v.set! at_ (UInt8.ofNat b)
    unless (validate v == none) == (String.fromUTF8? v).isSome do
      failed := some s!"utf8 fuzz case {i}: validate and core decoder disagree on {v.toList}"
  if let some msg := failed then failures ref msg

/-- The IR-to-IR walks are exhaustive, and each arm below was a wildcard
drop once: the fact checked is the behaviour the walk owes the constructor
it used to drop silently (PLAN 2026-09-17, the obligation table). -/
def walkChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- A font template's hole may sit inside any body-carrying wrapper: a
  -- link or step wrapper is filled exactly like styled/colored/underline.
  t "fillTemplate fills a hole inside a link"
    (Ir.fillTemplate #[.link "https://example.org" #[]] #[.text "x"] ==
      #[.link "https://example.org" #[.text "x"]])
  t "fillTemplate fills a hole inside a step"
    (Ir.fillTemplate #[.step 2 none #[]] #[.text "x"] == #[.step 2 none #[.text "x"]])
  -- Furniture sits outside the overlay model: the dim walks keep a section
  -- title whole, so a step there must not multiply handout pages either.
  -- A deliberate answer, pinned; the wildcard used to decide it silently.
  t "maxStep keeps furniture outside the overlay model"
    (Ir.maxStepBlocks #[.section 1 false none #[.step 2 none #[.text "t"]]] == 1)

/-- The paragraph boundary, judged from a body's shape: an unknown
environment follows the same rule as the `\input` wrapper (`Parse.inputEnv`) —
an inline body stays in its sentence, block content breaks it. -/
def envBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "an inline unknown environment stays in its paragraph"
    (match (elabStr "A sentence with \\begin{highlight}x\\end{highlight} in the middle.").1.body with
     | #[.para xs] => Ir.plainText xs == "A sentence with x in the middle."
     | _ => false)
  t "an unknown environment holding block content is a boundary"
    ((elabStr "before\n\\begin{aside}one\n\ntwo\n\\end{aside}\nafter").1.body ==
      #[.para #[.text "before"], .para #[.text "one"], .para #[.text "two"],
        .para #[.text "after"]])
  -- bodyIsBlock mirrors the boundary rule: verbatim is a first-class block
  -- on this branch, so it is block inside a body too — degrading it to
  -- inline <code> loses the literal lines
  t "a verbatim inside an unknown environment stays a block"
    (match (elabStr
        "\\begin{gizmo}\n\\begin{verbatim}\nliteral line one\n\\end{verbatim}\n\\end{gizmo}").1.body with
     | #[.verbatim none s _] => s.trimAscii.toString == "literal line one"
     | _ => false)
  -- ...and the judgment descends into scope groups: block content one
  -- group deeper is still block content
  t "block content one group deeper still makes a body block"
    ((elabStr "before\n\\begin{gizmo}\n{one \\par two}\n\\end{gizmo}\nafter").1.body ==
      #[.para #[.text "before"], .para #[.text "one"], .para #[.text "two"],
        .para #[.text "after"]])
  t "an inline unknown environment's begin-line argument goes with the wrapper"
    (match (elabStr "Take \\begin{banner}{Logo}the text\\end{banner} along.").1.body with
     | #[.para xs] => Ir.plainText xs == "Take the text along."
     | _ => false)
  -- W0302 says the body is kept; when begin-line groups go with the
  -- wrapper, a warning must say exactly what went (the diagnostic and the
  -- behaviour agree, or one of them is lying)
  t "dropped begin-line groups are named precisely, count included"
    (let ds := (elabStr "Two: \\begin{card}{First}{Second}kept body\\end{card} end.").2
     ds.any fun d => d.code == "E0336" && d.message.startsWith "2 ")
  t "the block path warns about dropped begin-line groups too"
    ((elabStr "\\begin{wrap}{arg}\none\n\ntwo\n\\end{wrap}").2.any (·.code == "E0336"))
  t "no dropped-argument warning without begin-line groups"
    (!(elabStr "Take \\begin{banner}the text\\end{banner} along.").2.any (·.code == "E0336"))
  -- A spliced body's edge space is a separator, not wrapper furniture:
  -- dropping it glued `before` to `inner`, and keeping it twice would
  -- double the gap the author wrote once.
  t "an inline unknown environment's edge spaces still separate words"
    (match (elabStr "Glue check:before\\begin{gizmo} inner \\end{gizmo}after done.").1.body with
     | #[.para xs] => Ir.plainText xs == "Glue check:before inner after done."
     | _ => false)
  t "splicing an unknown environment never doubles a space"
    (match (elabStr "before\n\\begin{gizmo}\ninner\n\\end{gizmo}\nafter").1.body with
     | #[.para xs] => Ir.plainText xs == "before inner after"
     | _ => false)
  t "a paragraph never opens with a spliced body's leading space"
    (match (elabStr "\\begin{gizmo} inner \\end{gizmo} rest.").1.body with
     | #[.para xs] => Ir.plainText xs == "inner rest."
     | _ => false)

/-- The optional-argument recovery, fed the malformed across line breaks:
an unclosed `[` never turns into a fatal error however the lines fall — the
group the author wrote is found on its own line or the next, a command with
no group left is skipped whole (W0312), and a construct sharing the typo's
line is never consumed with it. -/
def optArgChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \title: the group on the NEXT line is the argument too, never a fatal
  -- E0304 + E0313
  let titleNl := "\\title[short never closes\n{The Real Title}\n\\begin{document}x\\end{document}"
  let (tnDoc, tnDs) := elabStr titleNl
  t "title survives an unclosed bracket with its group on the next line"
    (tnDoc.info.title == some "The Real Title")
  t "an unclosed title bracket across lines is a warning, not E0313"
    (!tnDs.any (·.severity == .error) && tnDs.any (·.code == "W0310"))
  -- ...and with no group anywhere, the declaration is skipped whole (W0312)
  -- and the next declaration survives
  let titleSkip := "\\title[never closes\n\\author{A. Placeholder}\n\\begin{document}x\\end{document}"
  let (tsDoc, tsDs) := elabStr titleSkip
  t "a title with no group after its unclosed bracket is skipped, never fatal"
    (!tsDs.any (·.severity == .error) && tsDs.any (·.code == "W0312"))
  t "the declaration after a skipped title survives"
    (tsDoc.info.author == some "A. Placeholder")
  -- ...and a BLANK line between the typo and the group is one more line
  -- arrangement, not a fatal E0313: never fatal means never
  let titleBlank := "\\title[short never closes\n\n{The Real Title}\n\\begin{document}x\\end{document}"
  let (tbDoc, tbDs) := elabStr titleBlank
  t "title survives an unclosed bracket with a blank line before its group"
    (tbDoc.info.title == some "The Real Title")
  t "an unclosed title bracket across a blank line is never fatal"
    (!tbDs.any (·.severity == .error) && tbDs.any (·.code == "W0310"))
  -- \section[short]{long}: the fifth optional-argument site obeys the
  -- shared scanner instead of a fatal E0304
  let (secDoc, secDs) := elabStr "\\section[Short]{Long Title}\n\nBody."
  t "section takes its short form and keeps the long title"
    (secDs.all (·.severity == .note) && match secDoc.body with
     | #[.section 1 false (some "1") title, .para _] => Ir.plainText title == "Long Title"
     | _ => false)
  -- The short title is unused today, and that is registered, never silent.
  t "an unused short title is a note" (secDs.any (·.code == "N0103"))
  t "section recovers its title past an unclosed bracket"
    (match (elabStr "\\section[never closes {Recovered}\nBody.").1.body with
     | #[.para _, .section 1 false (some "1") title, .para _] => Ir.plainText title == "Recovered"
     | _ => false)
  -- Principle 8: the malformed run W0310 calls content IS content in a
  -- content position, exactly as in the scanner's two sibling paths
  t "the malformed run before a recovered section title stays content"
    (match (elabStr "\\section[never closes IMPORTANTWORDS {Recovered}\nBody.").1.body with
     | #[.para junk, .section 1 false (some "1") title, .para _] =>
       (Ir.plainText junk).endsWith "IMPORTANTWORDS" && Ir.plainText title == "Recovered"
     | _ => false)
  t "a body title's malformed run stays content, the title still taken"
    (let (doc, ds) := elabStr "\\title[junk words {Kept Title}\n\\maketitle"
     !ds.any (·.severity == .error) &&
       (match doc.body with
        | #[.para junk, .center _] => (Ir.plainText junk).endsWith "junk words"
        | _ => false))
  t "a section with no group after its unclosed bracket warns, never fatally"
    (let ds := (elabStr "\\section[never closes\nBody.").2
     !ds.any (·.severity == .error) && ds.any (·.code == "W0312"))

/-- The shared bracket scanner, fed the malformed and the merely leading:
an unclosed `[` is content, never an argument that consumes to the end of
its scan, and a bracket on a later line than its command is content too.
Each case here lost text silently — a frame body, a preamble declaration,
a title — when four copies of the scan disagreed about the guard. -/
def scannerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let blockText (b : Ir.Block) : String :=
    match b with
    | .para xs => Ir.plainText xs
    | _ => ""
  -- an unclosed bracket must not consume the frame body
  let (fDoc, fDs) := elabStr (deck169Body "\\begin{frame}[unclosed\nBody survives.\n\\end{frame}")
  t "unclosed bracket keeps the frame body"
    (match fDoc.body with
     | #[.frame _ _ _ _ body] => body.any fun b => (blockText b).endsWith "Body survives."
     | _ => false)
  t "unclosed bracket in a frame warns" (fDs.any (·.code == "W0310"))
  -- a bracket opening the frame's content is content, not an option
  t "frame content starting with a bracket survives"
    (match (elabStr (deck169Body "\\begin{frame}\n[1] Reference survives.\n\\end{frame}")).1.body with
     | #[.frame _ _ _ _ #[.para xs]] => Ir.plainText xs == "[1] Reference survives."
     | _ => false)
  -- options on the begin line are still arguments, bracket runs included
  t "frame options on the begin line are consumed, never content"
    (match (elabStr (deck169Body "\\begin{frame}[plain][t]{T}\nbody\n\\end{frame}")).1.body with
     | #[.frame title _ _ _ #[.para xs]] =>
       Ir.plainText title == "T" && Ir.plainText xs == "body"
     | _ => false)
  -- unknown environment: unclosed bracket keeps the body, later-line bracket is content
  let (uDoc, uDs) := elabStr "\\begin{mywrap}[unclosed\nkept body\n\\end{mywrap}"
  t "unclosed bracket keeps an unknown environment's body"
    (uDoc.body.any fun b => (blockText b).endsWith "kept body")
  t "unclosed bracket in an unknown environment warns" (uDs.any (·.code == "W0310"))
  t "unknown environment content starting with a bracket survives"
    (match (elabStr "\\begin{mywrap}\n[1] first line\nkept\n\\end{mywrap}").1.body with
     | #[.para xs] => Ir.plainText xs == "[1] first line kept"
     | _ => false)
  -- \title: the title survives its own malformed optional argument
  let titleSrc := "\\title[short never closes {The Real Title}\n\\begin{document}x\\end{document}"
  let (tDoc, tDs) := elabStr titleSrc
  t "title survives an unclosed optional argument"
    (tDoc.info.title == some "The Real Title")
  t "an unclosed title bracket is a warning, not E0313"
    (!tDs.any (·.severity == .error) && tDs.any (·.code == "W0310"))
  -- unknown preamble command: the next line's declaration must survive
  let preSrc := "\\unknowncmd[opts that never close\n\\palette{ accent = #ff0000 }\n" ++
    "\\begin{document}\\textcolor{accent}{x}\\end{document}"
  let (pDoc, pDs) := elabStr preSrc
  t "unclosed bracket does not eat the next preamble declaration"
    (pDoc.palette.find? "accent" |>.isSome)
  t "the swallowed palette warning is gone"
    (!pDs.any (·.code == "W0304") && !pDs.any (·.severity == .error))
  -- ...and a declaration SHARING the malformed command's line survives too
  let preSame := "\\unknowncmd[never closes \\palette{ accent = #00ff00 }\n" ++
    "\\begin{document}\\textcolor{accent}{x}\\end{document}"
  let (psDoc, psDs) := elabStr preSame
  t "unclosed bracket does not eat a declaration on its own line"
    (psDoc.palette.find? "accent" |>.isSome)
  t "no misdirecting palette warning for the shared line"
    (!psDs.any (·.code == "W0304") && !psDs.any (·.severity == .error))
  t "unclosed bracket does not eat the document on its own line"
    (match (elabStr "\\unknowncmd[junk \\begin{document}Body survives.\\end{document}").1.body with
     | #[.para xs] => Ir.plainText xs == "Body survives."
     | _ => false)
  -- reserved inline command: the sentence after the bracket survives
  t "unclosed bracket after a reserved command keeps the text"
    (match (elabStr "\\figure[unclosed and text continues").1.body with
     | #[.para xs] => (Ir.plainText xs).endsWith "and text continues"
     | _ => false)
  -- a reserved command's bracket on a later line is content
  t "bracket on the line after a reserved command is content"
    (match (elabStr "\\figure\n[1] a caption line").1.body with
     | #[.para xs] => Ir.plainText xs == "[1] a caption line"
     | _ => false)
  optArgChecks ref
  envBoundaryChecks ref

def utf8Checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- utf8: valid inputs
  t "utf8 empty" (validate (bytes []) == none)
  t "utf8 ascii" (validate "hello, world".toUTF8 == none)
  t "utf8 multibyte" (validate "naïve — αβγ — 🎉".toUTF8 == none)

  -- utf8: each error class, with offset
  t "utf8 bare continuation" (errKindAt (bytes [0x68, 0x80]) == some (1, .invalidStart 0x80))
  t "utf8 overlong 2-byte" (errKindAt (bytes [0xC0, 0x80]) == some (0, .overlong))
  t "utf8 overlong 3-byte" (errKindAt (bytes [0xE0, 0x9F, 0x80]) == some (0, .overlong))
  t "utf8 overlong 4-byte" (errKindAt (bytes [0xF0, 0x8F, 0x80, 0x80]) == some (0, .overlong))
  t "utf8 surrogate" (errKindAt (bytes [0xED, 0xA0, 0x80]) == some (0, .surrogate))
  t "utf8 out of range" (errKindAt (bytes [0xF4, 0x90, 0x80, 0x80]) == some (0, .outOfRange))
  t "utf8 truncated" (errKindAt (bytes [0x61, 0xC3]) == some (1, .truncated))
  t "utf8 bad continuation" (errKindAt (bytes [0xC3, 0x28]) == some (0, .invalidContinuation 0x28))

  -- utf8: error position tracks lines and columns
  let afterNewlines := bytes ("ab\ncd\n".toUTF8.toList ++ [0xFF])
  t "utf8 position" ((validate afterNewlines).map (fun e => (e.pos.line, e.pos.col)) == some (3, 1))

  -- utf8: agreement with core decoder on every vector above
  for (name, v) in [
      ("empty", bytes []), ("ascii", "hello".toUTF8), ("multi", "🎉é".toUTF8),
      ("cont", bytes [0x80]), ("overlong", bytes [0xC0, 0x80]),
      ("surrogate", bytes [0xED, 0xA0, 0x80]),
      ("range", bytes [0xF4, 0x90, 0x80, 0x80]), ("trunc", bytes [0xC3])] do
    t s!"utf8 agrees with core ({name})"
      ((validate v == none) == (String.fromUTF8? v).isSome)
  utf8FuzzChecks ref

def argsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- args
  t "args empty is help" (parse [] == .ok { cmd := .help })
  t "args build" (parse ["build", "a.tex"] == .ok { cmd := .build "a.tex" })
  t "args verbosity accumulates" (parse ["-v", "-vv", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", verbosity := 3 })
  t "args verbosity clamps" ((parse ["-vvvvv", "build", "a.tex"]).map (·.verbosity) == .ok 3)
  t "args porcelain quiet" (parse ["--porcelain", "-q", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", quiet := true, porcelain := true })
  t "args color eq" ((parse ["--color=never", "build", "a.tex"]).map (·.color) == .ok .never)
  t "args color sep" ((parse ["--color", "always", "version"]).map (·.color) == .ok .always)
  t "args color bad" ((parse ["--color=sometimes"]).isOk == false)
  t "args q v conflict" ((parse ["-q", "-v", "build", "a.tex"]).isOk == false)
  t "args unknown flag" ((parse ["--frobnicate"]).isOk == false)
  t "args build missing file" ((parse ["build"]).isOk == false)
  t "args trailing junk" ((parse ["build", "a.tex", "b.tex"]).isOk == false)
  t "args help flag wins" ((parse ["--help", "build", "a.tex"]).map (·.cmd) == .ok .help)
  -- Flags belong after the command too: a command takes the next positional,
  -- not the next token, or every flag written where people write it is eaten
  -- as the filename.
  t "args flag after command" (parse ["build", "--color", "never", "a.tex"] ==
    .ok { cmd := .build "a.tex", color := .never })
  t "args emit default is pdf"
    ((parse ["build", "a.tex"]).map (·.effectiveEmit #[]) == .ok #[.pdf])
  t "args css default is own" (cssFor none == .own)
  t "args math boundary"
    ((parse ["build", "--math-boundary", "katex", "a.tex"]).map (·.mathBoundary) ==
      .ok (some "katex"))
  -- The removed artifact-shaping flags fail as usage, and the message names
  -- the declaration that replaces each: a human under time pressure gets
  -- the spelling to paste, not just a refusal.
  let removed (argv : List String) (declKey : String) : Bool :=
    match parse argv with
    | .error m => (m.splitOn "\\output{").length ≥ 2 && (m.splitOn declKey).length ≥ 2
    | .ok _ => false
  t "args --css is usage error naming the declaration"
    (removed ["build", "--css", "bulma", "a.tex"] "css =")
  t "args --css= is usage error naming the declaration"
    (removed ["a.tex", "--css=bulma"] "css =")
  t "args --emit is usage error naming the declaration"
    (removed ["build", "--emit", "pdf,html", "a.tex"] "formats =")
  t "args --emit= is usage error naming the declaration"
    (removed ["a.tex", "--emit=html"] "formats =")
  -- args: the file is the command; the output name chooses the backend
  t "args file is the command" (parse ["a.tex"] == .ok { cmd := .build "a.tex" })
  t "args md reserved for markdown" (parse ["notes.md"] == .ok { cmd := .build "notes.md" })
  t "args flags after the file" (parse ["a.tex", "--color", "never"] ==
    .ok { cmd := .build "a.tex", color := .never })
  t "args non-document positional" ((parse ["nonsense.txt"]).isOk == false)
  t "args output flag" ((parse ["a.tex", "-o", "out.html"]).map (·.output) ==
    .ok (some "out.html"))
  t "args output infers html" ((parse ["a.tex", "-o", "out.html"]).map
    (·.effectiveEmit #[]) == .ok #[.html])
  t "args output infers pdf" ((parse ["a.tex", "-o", "b/x.pdf"]).map
    (·.effectiveEmit #[]) == .ok #[.pdf])
  t "args document formats apply" ((parse ["a.tex"]).map (·.effectiveEmit #["html"]) ==
    .ok #[.html])
  t "args output name beats document formats" ((parse ["a.tex", "-o", "out.pdf"]).map
    (·.effectiveEmit #["html"]) == .ok #[.pdf])
  t "args document css applies" (cssFor (some "bulma") == .bulma)
  t "args unknown document css falls back to own" (cssFor (some "tailwind") == .own)
  t "args output dir keeps stem" (outPath (some "out/") false "doc.tex" .pdf == "out/doc.pdf")
  t "args output other backend beside source"
    (outPath (some "out.html") false "doc.tex" .pdf == "doc.pdf")
  t "args watch" ((parse ["a.tex", "--watch"]).map (·.watch) == .ok true)

def lexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- lex
  t "lex words and space" (toks "ab cd" == [.word "ab", .space, .word "cd"])
  t "lex par" (toks "a\n\nb" == [.word "a", .par, .word "b"])
  t "lex newline is space" (toks "a\nb" == [.word "a", .space, .word "b"])
  t "lex comment joins lines" (toks "a%c\nb" == [.word "a", .word "b"])
  -- TeX: `%` discards the rest of its line, end-of-line included, and the
  -- next line opens in state N — its indentation is skipped and a blank
  -- line there is `\par`. The comment hides its own end-of-line, never the
  -- blank line after it (`Lex.blank_line_par_agree`).
  t "lex blank line after a comment is a par"
    (toks "a\n  % c\n\n  b" == [.word "a", .space, .par, .word "b"])
  t "lex blank line after an end-of-line comment is a par"
    (toks "a% c\n\nb" == [.word "a", .par, .word "b"])
  t "lex indented line after a comment adds no space"
    (toks "a% c\n  b" == [.word "a", .word "b"])
  t "lex comment line between lines is one space"
    (toks "a\n% c\nb" == [.word "a", .space, .word "b"])
  t "lex ctrl word swallows space" (toks "\\emph  x" == [.ctrl "emph", .word "x"])
  t "lex ctrl word keeps blank line" (toks "\\par\n\nx" == [.ctrl "par", .par, .word "x"])
  t "lex ctrl symbol" (toks "\\%x" == [.ctrl "%", .word "x"])
  t "lex specials" (toks "{a}$m$[o]" ==
    [.lbrace, .word "a", .rbrace, .math, .word "m", .math, .sym '[', .word "o", .sym ']'])
  t "lex unicode word" (toks "naïve" == [.word "naïve"])
  t "lex position" (((Lex.lex "t" "a\nbé c").1.map fun tk => (tk.pos.line, tk.pos.col)).toList ==
    [(1, 1), (1, 2), (2, 1), (2, 3), (2, 4)])

def nfcChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- UAX #15 NFC at input (Nfc.lean): composed output, canonical
  -- reordering, singleton mapping, idempotence, ASCII passthrough.
  t "nfc composes NFD pair" (Nfc.normalize "e\u0301" == "é")
  t "nfc composes iteratively" (Nfc.normalize "e\u0302\u0301" == "\u1EBF")
  t "nfc reorders by combining class"
    (Nfc.normalize "e\u0301\u0327" == "\u0229\u0301")
  t "nfc maps singleton" (Nfc.normalize "\u212B" == "Å")
  t "nfc keeps ascii" (Nfc.normalize "hello" == "hello")
  t "nfc keeps composed" (Nfc.normalize "Bélair" == "Bélair")
  t "nfc idempotent" (Nfc.normalize (Nfc.normalize "e\u0301\u0327 ơ\u0323")
    == Nfc.normalize "e\u0301\u0327 ơ\u0323")
  t "nfc hangul composes" (Nfc.normalize "\u1100\u1161\u11A8" == "\uAC01")
  -- The word boundary reads these, not the ASCII-only Char.isAlpha /
  -- Char.toLower: é is a letter of a hyphenatable word, and É folds to é
  -- for pattern matching (the fr/de patterns spell letters lowercase).
  t "isLetter covers Latin beyond ASCII"
    (Nfc.isLetter 'é' && Nfc.isLetter 'ß' && Nfc.isLetter 'Ω' &&
      !Nfc.isLetter '×' && !Nfc.isLetter '÷' && !Nfc.isLetter '1' &&
      Nfc.isLetter 'a' && !Nfc.isLetter '-')
  t "toLower folds beyond ASCII"
    (Nfc.toLower 'É' == 'é' && Nfc.toLower 'A' == 'a' && Nfc.toLower 'ß' == 'ß')
  -- The lexer feeds normalized text to everything downstream.
  t "lex normalizes to NFC" (toks "Be\u0301lair" == [.word "Bélair"])

def accentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- TeX accent commands compose to NFC in text elaboration, the same
  -- table .bib values read (Bib.accentTable via Elab.accentCompose):
  -- B\'elair renders "Bélair", not "Belair" + W0301.
  let para? (p : Ir.Doc × Array Diag) : Option (Array Ir.Inline) :=
    match p.1.body with
    | #[.para xs] => some xs
    | _ => none
  let (d1, ds1) := elabStr "B\\'elair"
  t "accent on adjacent word composes" (ds1.isEmpty &&
    para? (d1, ds1) == some #[.text "Bélair"])
  let (d2, ds2) := elabStr "sch\\\"{o}n and \\c{c}a and gro\\ss e"
  t "accent groups, cedilla, and char commands compose" (ds2.isEmpty &&
    para? (d2, ds2) == some #[.text "schön and ça and große"])
  let (d3, ds3) := elabStr "ma\\~nana"
  t "tilde accent composes before the tilde escape" (ds3.isEmpty &&
    para? (d3, ds3) == some #[.text "mañana"])
  let (d4, ds4) := elabStr "a\\~{}b"
  t "empty-group tilde stays the literal escape" (ds4.isEmpty &&
    para? (d4, ds4) == some #[.text "a~b"])
  -- A pair the table does not know keeps its base and warns by name, as
  -- before: nothing new is dropped.
  let (_, ds5) := elabStr "\\'q"
  t "unknown accent pair still warns" (ds5.map (·.code) == #["W0301"])

def localeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Language is data (Locale.lean): babel's package options declare the
  -- main language (last language option = main, babel's rule), and every
  -- generated word — captions, the References heading, quotes — reads the
  -- locale record.
  let (dfr, dsfr) := elabStr
    "\\documentclass{article}\n\\usepackage[english,french]{babel}\n\\begin{document}\nx\n\\end{document}"
  t "babel options declare the main language" (dfr.info.language == some "fr")
  t "the locale resolves from the tag" (dfr.info.locale.tag == "fr")
  t "a shipped language fires nothing" (!dsfr.any (·.code == "W0368"))
  let (den, _) := elabStr
    "\\documentclass{article}\n\\usepackage[french,english]{babel}\n\\begin{document}\nx\n\\end{document}"
  t "the last language option is the main one" (den.info.language == some "en")
  let (_, dsxx) := elabStr
    "\\documentclass{article}\n\\usepackage[klingon]{babel}\n\\begin{document}\nx\n\\end{document}"
  t "a language with no record is named, English stands in"
    (dsxx.any (·.code == "W0368"))
  -- \enquote reads the active locale's delimiters (csquotes under babel).
  let (dq, _) := elabStr
    "\\documentclass{article}\n\\usepackage[french]{babel}\n\\begin{document}\n\\enquote{x}\n\\end{document}"
  t "enquote takes the locale's quotes"
    (dq.body == #[.para #[.text "«x»"]])
  -- The References heading is \refname, locale data.
  let (dref, _) := elabStr
    "\\documentclass{article}\n\\usepackage[french]{babel}\n\\begin{document}\nx\n\n\\bibliography{refs}\n\\end{document}"
  t "the references heading is worded in the main language"
    (dref.body.any fun b => match b with
      | .section 1 true none xs => xs == #[.text "Références"]
      | _ => false)
  -- The abstract heading, in both text backends.
  let (dab, _) := elabStr
    "\\documentclass{article}\n\\usepackage[french]{babel}\n\\begin{document}\n\\begin{abstract}\ny\n\\end{abstract}\nx\n\\end{document}"
  t "the markdown abstract heading follows the locale"
    (((MarkdownDoc.emit dab).splitOn "## Résumé").length == 2)
  t "the html abstract heading follows the locale"
    (((HtmlDoc.emit {} dab).1.splitOn ">Résumé<").length == 2)
  -- Bibliography months come from the locale (BibTeX's jan..dec macros).
  let bib := "@article{k, author={A B}, title={T}, journal={J}, year={2020}, month=jan}"
  let (dcite, _) := elabStr
    "\\documentclass{article}\n\\usepackage[french]{babel}\n\\begin{document}\n\\cite{k}\n\n\\bibliography{refs}\n\\end{document}"
  let (applied, _) := Bib.apply #[("refs", bib)] dcite
  let bibText := applied.body.foldl (init := "") fun acc b => match b with
    | .bibliography _ _ items =>
      items.foldl (init := acc) fun acc i => acc ++ Ir.plainText i.content
    | _ => acc
  t "bibliography months are worded in the main language"
    ((bibText.splitOn "janvier").length == 2)
  -- The language switches: \foreignlanguage tags a run, \selectlanguage
  -- tags the paragraphs after it (from-here-forward flow order), and the
  -- otherlanguage environment tags its body. The attribute is Style.lang
  -- — pure markup, langWrap_text — never a new Inline.
  let (df, dsf) := elabStr "aa \\foreignlanguage{french}{du texte} bb"
  t "foreignlanguage tags its run" (!dsf.any (·.severity != .note) &&
    df.body == #[.para #[.text "aa ",
      .styled (.lang "fr") #[.text "du texte"], .text " bb"]])
  let (dsl, _) := elabStr
    "\\documentclass{article}\n\\begin{document}\nplain\n\n\\selectlanguage{french}\nen français\n\\end{document}"
  t "selectlanguage tags the paragraphs after it"
    (dsl.body == #[.para #[.text "plain"],
      .para #[.styled (.lang "fr") #[.text "en français"]]])
  let (dol, _) := elabStr
    "\\documentclass{article}\n\\begin{document}\nx \\begin{otherlanguage}{german}Wort\\end{otherlanguage} y\n\\end{document}"
  t "otherlanguage tags its body"
    (dol.body == #[.para #[.text "x ",
      .styled (.lang "de") #[.text "Wort"], .text " y"]])
  -- A switch back to the main language clears the attribute.
  let (dback, _) := elabStr
    "\\documentclass{article}\n\\begin{document}\n\\selectlanguage{french}\nfr\n\n\\selectlanguage{english}\nen\n\\end{document}"
  t "switching back to main clears the attribute"
    (dback.body == #[.para #[.styled (.lang "fr") #[.text "fr"]],
      .para #[.text "en"]])
  -- \babelfont[lang] parses — the option stands before the slot — and
  -- the per-language binding is dropped by name, never an error cascade.
  let (dbf, dsbf) := elabStr
    "\\documentclass{article}\n\\babelfont[french]{rm}{Example Serif}\n\\begin{document}\nx\n\\end{document}"
  t "babelfont language binding drops named, no cascade"
    ((dsbf.map (·.code)).contains "W0369" &&
      !dsbf.any (fun d => d.code == "E0320" || d.code == "E0313") &&
      dbf.fonts.body.isNone)
  let (dbf2, dsbf2) := elabStr
    "\\documentclass{article}\n\\babelfont{rm}{Example Serif}\n\\begin{document}\nx\n\\end{document}"
  t "unoptioned babelfont still names the main font"
    (!dsbf2.any (·.code == "W0369") && dbf2.fonts.body == some "Example Serif")

def parseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- parse
  let praw (s : String) : Array Parse.Raw × Array Diag :=
    let (tk, _) := Lex.lex "t" s
    Parse.parse "t" tk
  t "parse group nesting" (((praw "{a{b}}").1.map fun r =>
    match r with
    | .group body _ => s!"group/{body.size}"
    | _ => "?") == #["group/2"])
  t "parse unclosed group" (((praw "{a").2.map (·.code)) == #["E0201"])
  t "parse stray rbrace" (((praw "a}b").2.map (·.code)) == #["E0202"])
  t "parse env" (((praw "\\begin{itemize}\\item a\\end{itemize}").1.map fun r =>
    match r with
    | .env n body _ => s!"env {n}/{body.size}"
    | _ => "?") == #["env itemize/2"])
  t "parse env mismatch" (((praw "\\begin{a}x\\end{b}").2.map (·.code)) == #["E0205"])
  -- The group boundary wins: an environment opened inside `{...}` and still
  -- open at the `}` closes there, named — the `}` is never dropped, so the
  -- env cannot swallow what follows the group (a `\def` body's unbalanced
  -- `\begin{tabular}` once ate the rest of a venue's `.sty`, taking its
  -- `\renewenvironment{abstract}` and the W0303 that refuses it).
  t "parse env unclosed in group closes at the group's end"
    ((((praw "{\\begin{tabular}a}b").1.map fun r =>
      match r with
      | .group body _ => s!"group/{body.size}"
      | .word w _ => w
      | _ => "?") == #["group/1", "b"]) &&
      ((praw "{\\begin{tabular}a}b").2.map (·.code)) == #["E0201"])
  t "parse display math" (((praw "\\[x\\]").1.map fun r =>
    match r with
    | .math true _ _ => "display"
    | _ => "?") == #["display"])

def elabDocChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- elab: clean documents
  let (doc1, d1) := elabStr "hello $x$ world"
  t "elab snippet clean" (d1.isEmpty && doc1.body ==
    #[.para #[.text "hello ",
      .formula false "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil),
      .text " world"]])
  let (doc2, d2) := elabStr "\\textbf{a} {\\itshape b c} d"
  t "elab styles" (d2.isEmpty && doc2.body ==
    #[.para #[.styled .bold #[.text "a"], .text " ", .styled .italic #[.text "b c"], .text " d"]])
  let (doc3, d3) := elabStr "a\n\nb"
  t "elab paragraphs split" (d3.isEmpty && doc3.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  let (doc4, d4) := elabStr "\\section*{Work}\ntext"
  t "elab section star" (d4.isEmpty && doc4.body ==
    #[.section 1 true none #[.text "Work"], .para #[.text "text"]])
  let (doc5, d5) := elabStr "\\begin{itemize}\\item a\\item b\\end{itemize}"
  t "elab itemize" (d5.isEmpty && doc5.body ==
    #[.list false #[#[.para #[.text "a"]], #[.para #[.text "b"]]]])
  let (doc6, d6) := elabStr "\\documentclass[x=1]{article}\n\\begin{document}\nhi\n\\end{document}"
  t "elab documentclass" (d6.isEmpty && doc6.docClass == .article && doc6.classOptions == "x=1")
  -- The assumed class is named on the .tex surface, exactly once, and only
  -- when no \documentclass stands: a declared class (even an unknown one —
  -- E0309 owns that) and the markdown surface stay silent.
  let dcl (f s : String) : Array Diag := (Elab.run f s).2
  t "a classless .tex notes the assumed article page model"
    (((dcl "doc.tex" "x").filter (·.code == "N0017")).size == 1)
  t "a declared class is never noted"
    ((dcl "doc.tex" "\\documentclass{slides}\n\\begin{document}\nx\n\\end{document}").all
      (·.code != "N0017"))
  t "an unknown class is E0309's, not the classless note's"
    ((dcl "doc.tex" "\\documentclass{poster}\n\\begin{document}\nx\n\\end{document}").all
      (·.code != "N0017"))
  t "a classless .md is the surface's grammar, never noted"
    ((dcl "doc.md" "x").all (·.code != "N0017"))
  -- A backend conditional in content is a class or kernel decision made by
  -- hand: noted where it stands, one note per conditional, and a document
  -- without one is silent — the goal state for every reference document.
  t "a backend conditional is noted where it stands"
    (((elabStr "\\begin{ifbackend}{pdf}\nx\n\\end{ifbackend}").2.filter
      (·.code == "N0019")).size == 1)
  t "a document without a conditional is never noted"
    ((elabStr "x\n\n\\begin{nav}\\href{#a}{A}\\end{nav}").2.all (·.code != "N0019"))
  -- The theme install names inert slides furniture: the class gates whether
  -- furniture draws, the theme supplies its values, and a bundle whose
  -- chrome and furniture styles land under article would otherwise be
  -- silently inert. One code one meaning: the document's own \chrome under
  -- article stays W0318 alone.
  t "a theme's slides furniture under article is named at the install"
    ((elabStr (dvDoc "\\theme{moloch}\n" "x")).2.any fun d =>
      d.code == "W0355" && (d.message.splitOn "chrome").length > 1 &&
        (d.message.splitOn "frametitle").length > 1)
  t "the same theme under slides installs drawing furniture, silently"
    ((elabStr (dvDeck "\\theme{moloch}\n" "\\begin{frame}{T}\nx\n\\end{frame}")).2.all
      (·.code != "W0355"))
  t "the theme install is never the document's own chrome door"
    ((elabStr (dvDoc "\\theme{moloch}\n" "x")).2.all (·.code != "W0318"))
  -- The genre classes: records over the flow model. Each implies its
  -- contract as assertions the shipped pages are judged against, and a
  -- document declaring an assertion of the same form takes control.
  let clsDoc (cls extra body : String) : Ir.Doc :=
    (elabStr s!"\\documentclass\{{cls}}\n{extra}\\begin\{document}\n{body}\n\\end\{document}").1
  let resumeDoc := clsDoc "resume" "" "x"
  t "resume class enters the IR" (resumeDoc.docClass == .resume)
  t "resume implies its contract: one page, ink in area, the x-height floor"
    (resumeDoc.asserts.any (·.kind == .pages .eq 1) &&
     resumeDoc.asserts.any (·.kind == .textInArea) &&
     resumeDoc.asserts.any (·.kind == .minXHeight Ir.cardXHeightFloor))
  t "every implied assertion says which contract fired"
    (resumeDoc.asserts.all (·.help.isSome))
  t "a declared pages assertion takes control of the implied one"
    (let d := clsDoc "resume" "\\assert{ pages <= 2 }\n" "x"
     (d.asserts.filter fun a => match a.kind with
       | .pages _ _ => true | _ => false).size == 1 &&
     d.asserts.any (·.kind == .pages .le 2))
  let webDoc := clsDoc "webpage" "" "x"
  t "webpage class enters the IR" (webDoc.docClass == .webpage)
  t "webpage carries its build intent: html and the markdown twin"
    (webDoc.output.formats == #["html", "md"] && webDoc.output.md == some "llms.txt")
  t "webpage implies no shipped-page contract" (webDoc.asserts.isEmpty)
  t "a declared formats list replaces the class's whole"
    ((clsDoc "webpage" "\\output{ formats = pdf }\n" "x").output.formats == #["pdf"])
  t "a declared twin name wins over the class default"
    ((clsDoc "webpage" "\\output{ md = \"notes.txt\" }\n" "x").output.md == some "notes.txt")
  -- Heading numbering is the class record's default: article numbers
  -- (classes.dtx counters), a résumé is scanned and a web page follows
  -- the web's unnumbered convention; \section* opts out either way.
  let secNum (doc : Ir.Doc) : Option String :=
    (doc.body.findSome? fun b => match b with
      | .section _ _ n _ => some n | _ => none).getD none
  t "article numbers a section" (secNum (clsDoc "article" "" "\\section{A}\nx") == some "1")
  t "resume sections stand unnumbered" (secNum (clsDoc "resume" "" "\\section{A}\nx") == none)
  t "webpage sections stand unnumbered" (secNum (clsDoc "webpage" "" "\\section{A}\nx") == none)
  let (doc9, d9) := elabStr
    "\\output{ formats = pdf, html, css = bulma }\n\\begin{document}x\\end{document}"
  t "elab output declaration" (d9.isEmpty && doc9.output.formats == #["pdf", "html"] &&
    doc9.output.css == some "bulma")
  t "elab output bad format" (errCodes
    "\\output{ formats = ps }\n\\begin{document}x\\end{document}" == ["E0321"])
  t "elab output unknown key" (errCodes
    "\\output{ paper = a4 }\n\\begin{document}x\\end{document}" == ["E0322"])

  -- elab: define and call
  let defRole := "\\documentclass{article}\n" ++
    "\\define \\role(who: text, team?: text) {\\textbf{\\who}\\ifgiven{\\team}{ (\\team)}}\n" ++
    "\\begin{document}\n"
  let (doc7, d7) := elabStr (defRole ++ "\\role{Ada}[Compute]\n\\end{document}")
  t "elab define call optional given" (d7.isEmpty && doc7.body ==
    #[.para #[.role "role" #[.styled .bold #[.text "Ada"], .text " (Compute)"]]])
  let (doc8, d8) := elabStr (defRole ++ "\\role{Ada}\n\\end{document}")
  t "elab define call optional omitted" (d8.isEmpty && doc8.body ==
    #[.para #[.role "role" #[.styled .bold #[.text "Ada"]]]])
  t "elab define text param rejects math" (errCodes (defRole ++ "\\role{$x$}\n\\end{document}") ==
    ["E0305"])
  t "elab self reference is unknown" (warnCodes
    ("\\define \\x() {\\x}\n\\begin{document}\\x\\end{document}") == ["W0301"])
  t "elab forward reference is unknown" (warnCodes
    ("\\define \\a() {\\b}\n\\define \\b() {y}\n\\begin{document}\\a\\end{document}") == ["W0301"])
  t "elab later definition sees earlier" (errCodes
    ("\\define \\b() {y}\n\\define \\a() {\\b}\n\\begin{document}\\a\\end{document}") == [])

  -- elab: diagnostics
  -- The non-blocking contract: an unknown command is a warning, its
  -- arguments are content, and content is never dropped for want of a command.
  t "elab unknown command warns" (warnCodes "\\frobnicate" == ["W0301"])
  t "elab unknown command keeps its arguments"
    ((elabStr "a \\frobnicate{kept}{too} b").1.body ==
      #[.para #[.text "a kept too b"]])
  t "elab unknown command warns once per name"
    ((warnCodes "\\zip{a} \\zip{b} \\zap{c}").length == 2)
  -- The warn-once keys are namespaced: an environment and a command sharing
  -- one name are two different unknown constructs, and neither may silence
  -- the other's warning.
  t "an environment and a command of one name both warn"
    ((warnCodes "\\begin{gizmo}body\\end{gizmo}\n\\gizmo{arg}").toArray ==
      #["W0302", "W0301"])
  -- A reserved command whose skipped arguments carry content loses that
  -- content -- but the construct is one a milestone owns, so the loss is
  -- `pending`: reported, and the rest of the document still renders. A
  -- document that wants the strict reading asks for it (`--werror`) rather
  -- than having every planned gap refuse to emit a page.
  t "elab reserved command dropping planned content warns" (warnCodes ("\\documentclass{article}\\figure{x}" ++
    "\\begin{document}y\\end{document}") == ["W0307"])
  t "elab reserved command dropping planned content still renders"
    ((elabStr ("\\documentclass{article}\\figure{x}" ++
      "\\begin{document}y\\end{document}")).1.body == #[.para #[.text "y"]])
  t "elab reserved layout-only command warns" (warnCodes ("\\documentclass{article}\\fontfallback{x}" ++
    "\\begin{document}y\\end{document}") == ["W0329"])
  -- Unknown environments keep their body: the wrapper's decoration is
  -- unknowable, the content inside it is not. Arguments on the \begin line
  -- go with the wrapper; a group on a later line is content.
  t "elab unknown environment keeps its body"
    ((elabStr "\\begin{wrap}{arg}\nkept\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab unknown environment warns once per name"
    ((warnCodes "\\begin{w}a\\end{w}\\begin{w}b\\end{w}") == ["W0302"])
  t "elab unknown environment keeps a group on a later line"
    ((elabStr "\\begin{wrap}\n{kept}\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab reserved environment content dropped is one pending warning"
    (warnCodes "\\begin{external}x\\end{external}" == ["W0307"] &&
     (elabStr "\\begin{external}x\\end{external}").1.body == #[])
  -- The tikz subset narrowed W0307: a picture is elaborated, and what it
  -- cannot render is named per construct instead of dropped whole. With
  -- the boundary open (the default) a picture outside the subset routes
  -- whole to the boundary (N0023); under the declared refusal the losses
  -- are named where they stand and an all-refused picture adds the
  -- placeholder's W0362 — and no door warning: the declaration is the
  -- acceptance, and W0379 is the driver's, for a request no available
  -- tool can fulfil.
  t "elab tikzpicture routes to the boundary by default"
    (warnCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == [] &&
     noteCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["N0023"] &&
     errCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == [])
  t "elab tikzpicture under the refusal keeps the named losses, no W0379"
    (warnCodes (dvDoc "\\pictures{ tool = none }\n"
        "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}") == ["W0362"] &&
     errCodes (dvDoc "\\pictures{ tool = none }\n"
        "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}") == ["E0333"])
  -- The boundary is named, never silent — for the option bracket too: a
  -- picture option outside the subset is W0334, an unusable value inside
  -- it E0333, exactly as the statement walk already has it.
  t "elab picture option outside the subset is named under the refusal"
    (warnCodes (dvDoc "\\pictures{ tool = none }\n"
      "\\begin{tikzpicture}[banana]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")
      == ["W0334"])
  t "elab picture scale that cannot hold is named under the refusal"
    (errCodes (dvDoc "\\pictures{ tool = none }\n"
      "\\begin{tikzpicture}[scale=0]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")
      == ["E0333"])
  -- Named option bundles (`name/.style={...}`) expand where used, so a
  -- loss inside a bundle is named by its real spelling, never the
  -- bundle's; a bundle of subset options loses nothing.
  t "elab picture style bundle of subset options absorbs silently"
    ((elabStr ("\\begin{document}\\begin{tikzpicture}[lbl/.style={font=\\small, text=black}]\n" ++
      "\\node[lbl] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  t "elab picture style bundle names its outside options, not itself"
    (((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}[b/.style={ellipse}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'ellipse'") &&
     !((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}[b/.style={ellipse}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'b'"))
  t "elab picture style bundle referencing an earlier bundle expands"
    ((elabStr ("\\begin{document}\\begin{tikzpicture}[a/.style={font=\\small}, b/.style={a}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  -- **A style reaches its picture wherever `\tikzset` declared it** — the
  -- native half of `Compat.boundaryDecls_covers`, stated over the same walk
  -- (`Compat.tikzsetKeys_covers`). Before it, the style name was a key
  -- outside the subset and the node shipped without the outline its
  -- declaration asked for.
  t "elab tikzset style from the preamble reaches the picture"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  t "elab tikzset style written beside its picture reaches it"
    ((elabStr ("\\begin{document}\n\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  -- The style's keys are what draws: a plain node ships its label alone, a
  -- styled one ships the outline its declaration asked for as well.
  t "elab tikzset style draws the outline its keys declare"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false) &&
     (elabStr ("\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 1
        | _ => false))
  -- A later `\tikzset` may name an earlier one; expansion is at the
  -- definition, so the use site reads one level.
  t "elab tikzset style may name a bundle an earlier line defined"
    ((elabStr ("\\tikzset{a/.style={circle, draw, minimum size=8mm}}\n\\tikzset{b/.style={a}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  -- A picture's own definition shadows the document's of that name: pgf
  -- scopes keys, and the picture's bracket is inside the `\tikzset`.
  t "elab picture style bundle shadows a tikzset bundle of the same name"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[ball/.style={font=\\small}]\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 1
        | _ => false))
  -- **The hostile input: a style that names itself.** Expansion happens at
  -- the definition, where the name is not yet bound, so the reference stays
  -- a literal key and the option loop names it — no fixed point is chased
  -- and no fuel bounds anything. A cycle of two behaves the same way.
  t "elab tikzset self-referential style is named, not chased"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{loop/.style={loop}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[loop] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  t "elab tikzset cycle of two styles is named, not chased"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{a/.style={b}}\n\\tikzset{b/.style={a}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[a] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  -- A key the subset does not know keeps its own spelling in the
  -- diagnostic, never the bundle's — and a style of nothing but unknown
  -- keys cannot make the picture claim to be drawn silently.
  t "elab tikzset style names its outside keys by their own spelling"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{b/.style={ellipse}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'ellipse'"))
  -- A `\tikzset` entry the native reader does not understand is named at
  -- the line that wrote it, and the tool the document configures does not
  -- change that: the engine drew this picture itself, so the entry is read
  -- by nobody. `every label` is such an entry: the option loops read
  -- `every node` and `every path`, and a key path with no loop behind it is
  -- left unread rather than stored as a bundle nothing will ever look up
  -- (`Picture.readableKey`). This pair used to differ — silent with the
  -- boundary open, named under the refusal — on the premise that the real
  -- TikZ read it at the edge; native drawing killed that premise, and
  -- `pictureKeyGateChecks` holds the artifact half (same bytes either way).
  t "elab tikzset entry outside the native reading is named under the refusal"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{every label/.style={draw}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  t "elab tikzset entry outside the native reading is named with the boundary open too"
    (((elabStr ("\\tikzset{every label/.style={draw}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  -- A `\tikzset` the engine reads is never an unknown command, and its
  -- group never reaches the sentence — under the refusal too, which is
  -- where the definition's own source used to print into the paragraph.
  t "elab tikzset is not an unknown command under the refusal"
    ((elabStr ("\\pictures{ tool = none }\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  -- **A style applied in the picture's own bracket reaches the picture's
  -- contents.** pgf sets those keys in the picture's scope, so every path
  -- and node reads them before its own. Before this, a picture-level style
  -- name was a key outside the subset: W0334, and the contents shipped
  -- bare. The node here declares no options at all, so the outline it
  -- draws can only have come from the picture's bracket.
  t "elab picture-level style reaches a node that declares nothing"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[ball]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty &&
     (elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[ball]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  t "elab picture-level style reaches every node in the picture"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[ball]\n" ++
      "\\node at (0,0) {x};\\node at (2,0) {y};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 4
        | _ => false))
  -- **The inner setting wins** (`Picture.inherit_inner_exact`): a key the
  -- node sets again takes the node's value, and the picture's other keys
  -- still apply. Stated here on a key this subset accumulates rather than
  -- assigns — a `minimum size` takes a maximum within one bracket, so
  -- inheriting by prefix alone would leave the picture's larger value
  -- standing and the node would be drawn 9mm wide, not 4mm.
  t "elab a node's own key beats the picture's, even where keys accumulate"
    ((elabStr ("\\tikzset{big/.style={draw, minimum size=9mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[big]\n" ++
      "\\node[minimum size=4mm] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .frame _ _ w h _ _ => w == Dim.mm 4 && h == Dim.mm 4
            | _ => false
        | _ => false))
  -- A picture-level key that names no declared style is still the picture
  -- loop's own, named where it stands: inheritance carries styles, not
  -- every spelling, so nothing became silently acceptable.
  t "elab picture-level key naming no style is still named"
    (warnCodes (dvDoc "\\pictures{ tool = none }\n"
      "\\begin{tikzpicture}[banana]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")
      == ["W0334"])
  -- **An inherited key nothing read is named, never dropped in silence.**
  -- `\fill`'s bracket is a colour spelling, not a key list, so a picture
  -- of nothing but fills reads no keys at all — and it still draws, so the
  -- refusal path would not have named them either.
  t "elab inherited key no path or node read is named at the picture"
    (warnCodes (dvDoc "\\tikzset{odd/.style={ellipse}}\n"
      "\\begin{tikzpicture}[odd]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")
      == ["W0334"] &&
     ((elabStr (dvDoc "\\tikzset{odd/.style={ellipse}}\n"
      "\\begin{tikzpicture}[odd]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")).2.map
      (·.message)).any (fun m => hasStr m "'ellipse'"))
  -- The hostile input at the picture level too: a self-referential style
  -- applied to the picture expands one level, keeps its own name as a
  -- literal key, and the node's option loop names it. Nothing is chased —
  -- inherited entries are never expanded a second time.
  t "elab picture-level self-referential style is named, not chased"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{loop/.style={loop}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[loop]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  -- **`every node` and `every path` are the third precedence level**, run
  -- inside the node's or path's own scope: they beat what the picture set
  -- and lose to the bracket's own (`Picture.mergeOpts`). Before this they
  -- were unread and named at their line; a document that declared one saw
  -- none of it drawn.
  t "elab every-node style reaches a node that declares nothing"
    ((elabStr ("\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty &&
     (elabStr ("\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  t "elab every-path style reaches a draw that declares nothing"
    ((elabStr ("\\tikzset{every path/.style={thick, draw=blue}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ st _ => st.color == { r := 0, g := 0, b := 255 } &&
                st.width == Ir.Pic.thickWidth
            | _ => false
        | _ => false))
  -- The middle boundary: `every node` beats the picture's own entry
  -- (`Picture.merge_every_exact`), stated on the accumulating key, where a
  -- surviving outer entry would win by maximum rather than lose.
  t "elab every-node style beats the picture's entry"
    ((elabStr ("\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\tikzset{wide/.style={minimum size=14mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[wide]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .circle _ _ r _ _ => r == Dim.mm 4
            | _ => false
        | _ => false))
  -- The inner boundary: the node's own bracket beats `every node`
  -- (`Picture.merge_own_exact`).
  t "elab a node's own key beats an every-node style"
    ((elabStr ("\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[minimum size=5mm] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .circle _ _ r _ _ => r == Dim.mm 5 / 2
            | _ => false
        | _ => false))
  -- All three at once: the node's own value is what draws, and neither
  -- other level leaves a trace of its own.
  t "elab a key set at all three levels takes the innermost"
    ((elabStr ("\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\tikzset{wide/.style={minimum size=14mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[wide]\n" ++
      "\\node[minimum size=5mm] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .circle _ _ r _ _ => r == Dim.mm 5 / 2
            | _ => false
        | _ => false))
  -- The path pair of the same two boundaries, read on the stroke: the
  -- picture sets a colour, `every path` another, the path its own.
  t "elab every-path style beats the picture's entry and loses to the path's"
    ((elabStr ("\\tikzset{every path/.style={draw=green}}\n" ++
      "\\tikzset{wire/.style={draw=blue}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[wire]\n" ++
      "\\draw (0,0) -- (2,0);\\draw[draw=red] (0,1) -- (2,1);" ++
      "\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => (pic.shapes.filterMap fun s => match s with
            | .edge _ st _ => some st.color
            | _ => none) == #[{ r := 0, g := 255, b := 0 }, { r := 255, g := 0, b := 0 }]
        | _ => false))
  -- A picture's own bracket may declare the level too, through the one
  -- definition router a `\tikzset` goes through.
  t "elab every-node style declared on the picture's bracket reaches its nodes"
    ((elabStr ("\\begin{document}" ++
      "\\begin{tikzpicture}[every node/.style={circle, draw, minimum size=8mm}]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  -- The hostile input at this level: an `every node` style naming itself.
  -- Expansion is at the definition, where the name is not yet bound, so
  -- the reference stays a literal key the node's loop names — one W0334,
  -- nothing chased.
  t "elab self-referential every-node style is named, not chased"
    ((((elabStr ("\\pictures{ tool = none }" ++
      "\\tikzset{every node/.style={every node}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"]) &&
     ((elabStr ("\\pictures{ tool = none }" ++
      "\\tikzset{every node/.style={every node}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map
      (·.message)).any (fun m => hasStr m "node option"))
  -- A picture-level key no later level names still reaches the construct
  -- (`Picture.merge_picture_covers`): the outermost level survives both
  -- filters, so the picture's colour draws under an `every path` that sets
  -- something else.
  t "elab a picture-level key survives an every-path style of other keys"
    ((elabStr ("\\tikzset{every path/.style={thick}}\n" ++
      "\\tikzset{wire/.style={draw=blue}}\n" ++
      "\\begin{document}\\begin{tikzpicture}[wire]\n" ++
      "\\draw (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ st _ => st.color == { r := 0, g := 0, b := 255 } &&
                st.width == Ir.Pic.thickWidth
            | _ => false
        | _ => false))
  -- An `every X` that declares no keys at all loses nothing, so the two
  -- places the level cannot reach say nothing either.
  t "elab an empty every-path style claims no loss"
    ((elabStr (dvDoc "\\tikzset{every path/.style={}}\n"
      "\\begin{tikzpicture}\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")).2.isEmpty)
  -- The two places this level cannot reach are named, not dropped in
  -- silence: `\fill`'s bracket is a colour spelling, and an edge label
  -- reads its own bracket alone.
  t "elab every-path keys a fill cannot read are named"
    (warnCodes (dvDoc "\\tikzset{every path/.style={thick}}\n"
      "\\begin{tikzpicture}\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")
      == ["W0334"])
  t "elab every-node keys an edge label cannot read are named"
    (((elabStr (dvDoc "\\tikzset{every node/.style={draw}}\n"
      ("\\begin{tikzpicture}\\draw (0,0) -- node {m} (2,0);" ++
       "\\end{tikzpicture}"))).2.map (·.code)).toList == ["W0334"])
  -- **`/.append style` composes where `/.style` shadows.** Both bodies'
  -- keys are read at the use site: the outline comes from the prior body
  -- and the size from the appended one, which a second `/.style` of that
  -- name would have thrown away.
  t "elab append style keeps the prior body and adds to it"
    ((elabStr ("\\tikzset{ball/.style={circle, draw}}\n" ++
      "\\tikzset{ball/.append style={minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .circle _ _ r _ _ => r == Dim.mm 4
            | _ => false
        | _ => false))
  t "elab a second style definition of a name throws the prior body away"
    ((elabStr ("\\tikzset{ball/.style={circle, draw}}\n" ++
      "\\tikzset{ball/.style={minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 1
        | _ => false))
  -- Where both bodies set a key the loop assigns, the appended value is
  -- read last and stands.
  t "elab an appended key the loop assigns beats the prior body's"
    ((elabStr ("\\tikzset{wire/.style={draw=blue}}\n" ++
      "\\tikzset{wire/.append style={draw=red}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[wire] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ st _ => st.color == { r := 255, g := 0, b := 0 }
            | _ => false
        | _ => false))
  -- Appending to a name nothing defined defines it: the keys the document
  -- asked for still apply.
  t "elab append style to an undefined name defines it"
    ((elabStr ("\\tikzset{ball/.append style={circle, draw, minimum size=8mm}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  -- **The hostile input for append: a style appending to itself.** The
  -- splice is still at the definition and against what is already defined,
  -- so the reference resolves to the body that name already had and the
  -- result is that body twice over — read once, drawing what it always
  -- drew. Nothing is chased and nothing is named.
  t "elab a style appending to itself terminates and draws its own keys"
    ((elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\tikzset{ball/.append style={ball}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty &&
     (elabStr ("\\tikzset{ball/.style={circle, draw, minimum size=8mm}}\n" ++
      "\\tikzset{ball/.append style={ball}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[ball] at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 2
        | _ => false))
  -- Appending to a name that does not exist yet keeps the reference a
  -- literal key, which the option loop names: one W0334, nothing chased.
  t "elab a style appending to an undefined self is named, not chased"
    (((elabStr ("\\pictures{ tool = none }\\tikzset{loop/.append style={loop}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node[loop] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.code)).toList
      == ["W0334"])
  -- **`/.tip` declares a tip name the subset can draw.** The engine has one
  -- arrow head and draws a declared tip with it, exactly as it already does
  -- for `latex` — the shape a document gets when it names its own tip and
  -- uses it on an edge, which was `Unknown arrow tip kind` at the boundary
  -- and a dropped option natively.
  t "elab a declared tip draws the subset's arrow head"
    ((elabStr ("\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.isEmpty &&
     (elabStr ("\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ _ tip => tip.isSome
            | _ => false
        | _ => false))
  t "elab a declared tip in braces draws the same head"
    ((elabStr ("\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-{scm}] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ _ tip => tip.isSome
            | _ => false
        | _ => false))
  -- A tip nothing declared is still named by its own spelling, and the
  -- edge still ships: a picture draws what it can and says what it lost.
  t "elab an undeclared tip is named and the edge still draws"
    (((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.map
      (·.code)).toList == ["W0334"] &&
     ((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.map
      (·.message)).any (fun m => hasStr m "'scm'") &&
     (elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.any fun s => match s with
            | .edge _ _ tip => tip.isNone
            | _ => false
        | _ => false))
  -- `>=<tip>` names which head the `->` shorthand draws: accepted for a
  -- declared tip, named for one nothing declared.
  t "elab a declared tip named by '>=' is accepted"
    ((elabStr ("\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[>=scm, ->] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.isEmpty)
  t "elab an undeclared tip named by '>=' is named"
    ((((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[>=scm, ->] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.map
      (·.code)).toList == ["W0334"]) &&
     ((elabStr ("\\pictures{ tool = none }\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[>=scm, ->] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.map
      (·.message)).any (fun m => hasStr m "'scm'"))
  -- The braced spelling of a tip name is the same name: pgf writes it that
  -- way as soon as the tip carries options.
  t "elab a declared tip named by '>=' in braces is accepted"
    ((elabStr ("\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[>={scm}, ->] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.isEmpty)
  -- A `/.tip` declaration is read, so it is not an unread key at its line;
  -- an `every X` with no loop behind it still is (`readableKey`).
  t "elab a tip declaration is not named as an unread key"
    ((elabStr ("\\pictures{ tool = none }\\tikzset{scm/.tip={Latex[round]}}\n" ++
      "\\begin{document}\\begin{tikzpicture}\n" ++
      "\\draw[-scm] (0,0) -- (2,0);\\end{tikzpicture}\\end{document}")).2.isEmpty)
  -- A `(name)` before `at` names the node for edges; the node draws.
  t "elab picture named node draws without a diagnostic"
    ((elabStr ("\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node (u) at (1,2) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty &&
     (elabStr ("\\begin{document}\\begin{tikzpicture}\n" ++
      "\\node (u) at (1,2) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes.size == 1
        | _ => false))
  -- `transform shape` opts the nodes into the picture's scale (pgf manual
  -- §25.4); without it a node keeps its own size.
  t "elab picture transform shape scales the node's label"
    (((elabStr ("\\begin{document}\\begin{tikzpicture}[scale=0.5, transform shape]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes == #[.label 0 0 #[.text "x"] Ir.Color.black 500 .center]
        | _ => false)))
  t "elab picture scale without transform shape leaves the label size alone"
    (((elabStr ("\\begin{document}\\begin{tikzpicture}[scale=0.5]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes == #[.label 0 0 #[.text "x"] Ir.Color.black 1000 .center]
        | _ => false)))
  t "elab reserved char" (errCodes "a & b" == ["E0311"])
  t "elab redefine structural builtin warns and keeps the built-in"
    (warnCodes "\\define \\pagebreak() {x}\n\\begin{document}y\\end{document}" == ["W0303"])
  -- ...except a text symbol, whose name a document may want for itself.
  let (degDoc, degDs) := elabStr
    "\\define \\degree(a: text) {\\textbf{\\a}}\n\\begin{document}\\degree{PhD}\\end{document}"
  t "elab user definition shadows a symbol"
    (degDs.isEmpty && degDoc.body ==
      #[.para #[.role "degree" #[.styled .bold #[.text "PhD"]]]])
  t "elab trailing content warns" (((elabStr
    "\\begin{document}x\\end{document} y").2.map (·.code)) == #["W0001"])

  -- The synthetic \input wrapper carries provenance, and must not invent
  -- structure the file does not have: an inline fragment stays in its
  -- paragraph; a file with paragraph breaks is block content.
  let ip : Pos := {}
  let inlineInput : Array Parse.Raw :=
    #[.word "A" ip, .space,
      .env (Parse.inputEnv "sub.tex") #[.word "with" ip, .space, .word "words" ip] ip,
      .space, .word "B" ip]
  t "inline input does not split its paragraph"
    ((Elab.runRaws "t" inlineInput).1.body == #[.para #[.text "A with words B"]])
  let blockInput : Array Parse.Raw :=
    #[.word "A" ip, .space,
      .env (Parse.inputEnv "sub.tex") #[.word "one" ip, .par ip, .word "two" ip] ip]
  t "an input file with paragraphs is block content"
    ((Elab.runRaws "t" blockInput).1.body ==
      #[.para #[.text "A"], .para #[.text "one"], .para #[.text "two"]])

  -- verbatim: lexically blind content, kept literally as its own block.
  let verbSrc := "\\begin{verbatim}\ndef f(n):\n    return n\n\nf(2)  # two spaces\n\\end{verbatim}"
  t "elab verbatim is a block, content untouched"
    ((elabStr verbSrc).1.body == #[.verbatim none "\ndef f(n):\n    return n\n\nf(2)  # two spaces\n" {}] &&
     (elabStr verbSrc).2.isEmpty)
  t "verbatim lines trim the delimiters, keep blanks and indentation"
    (Ir.verbatimLines "\nabc\n  in\n\nz\n  " == #["abc", "  in", "", "z"])
  t "verbatim drops every trailing blank line, not one"
    (Ir.verbatimLines "\ncode\n\n\n  " == #["code"])
  t "verbatim inline form holds spaces as no-break spaces"
    (Ir.verbatimInlines "\na  b\n" == #[.text "a\u00a0\u00a0b"])

def declChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- declarations: \page, \pdfmeta, \assert
  let declSrc := "\\documentclass{article}\n" ++
    "\\page{ size = a5, margin = 0.5in }\n" ++
    "\\pdfmeta{ title = \"T\", author = \"A\" }\n" ++
    "\\assert{ pages == 1 }\n" ++
    "\\assert{ fonts.all_embedded }\n" ++
    "\\begin{document}hi\\end{document}"
  let (declDoc, declDs) := elabStr declSrc
  t "decl source clean" declDs.isEmpty
  t "decl page size" (declDoc.page.width == Dim.pt 420 && declDoc.page.height == Dim.pt 595)
  t "decl margin both axes"
    (declDoc.page.vmargin == Dim.inch 1 / 2 && declDoc.page.hmargin == Dim.inch 1 / 2)
  t "decl metadata" (declDoc.info.title == some "T" && declDoc.info.author == some "A")
  t "decl assertions parsed" (declDoc.asserts.size == 2)

  -- dimension parsing is exact
  t "decl dim in" (Decl.parseValue "0.5in" == some (.dim (Dim.inch 1 / 2)))
  t "decl dim pt" (Decl.parseValue "12pt" == some (.dim (Dim.pt 12)))
  t "decl dim cm" (Decl.parseValue "2.54cm" == some (.dim (Dim.inch 1)))
  t "decl dim mm" (Decl.parseValue "25.4mm" == some (.dim (Dim.inch 1)))
  t "decl string" (Decl.parseValue "\"a b\"" == some (.str "a b"))
  t "decl ident" (Decl.parseValue "letter" == some (.ident "letter"))
  t "decl int" (Decl.parseValue "3" == some (.int 3))
  t "decl rejects junk" (Decl.parseValue "12 furlongs" == none)

  -- declaration diagnostics, one code each
  t "decl unknown size" (errCodes ("\\documentclass{article}\n\\page{ size = tabloid }\n" ++
    "\\begin{document}x\\end{document}") == ["E0324"])
  t "decl unknown key" (errCodes ("\\documentclass{article}\n\\page{ bogus = 1pt }\n" ++
    "\\begin{document}x\\end{document}") == ["E0322"])
  t "decl wrong type" (errCodes ("\\documentclass{article}\n\\page{ vmargin = \"x\" }\n" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "decl bad assertion" (errCodes ("\\documentclass{article}\n\\assert{ pages =~ 1 }\n" ++
    "\\begin{document}x\\end{document}") == ["E0325"])
  t "decl needs a block" (errCodes ("\\documentclass{article}\n\\page\n" ++
    "\\begin{document}x\\end{document}") == ["E0304"])

  -- assertions are judged against what shipped
  let shipped : Check.Shipped := { pages := 2, fontsEmbedded := true }
  let mkAssert (k : Ir.AssertKind) : Ir.Assertion := { kind := k, span := none }
  t "assert pages eq holds" ((Check.one shipped (mkAssert (.pages .eq 2))).isNone)
  t "assert pages eq fails" ((Check.one shipped (mkAssert (.pages .eq 1))).isSome)
  t "assert pages le holds" ((Check.one shipped (mkAssert (.pages .le 3))).isNone)
  t "assert pages gt fails" ((Check.one shipped (mkAssert (.pages .gt 5))).isSome)
  t "assert fonts holds" ((Check.one shipped (mkAssert .fontsAllEmbedded)).isNone)
  t "assert fonts fails"
    ((Check.one { shipped with fontsEmbedded := false } (mkAssert .fontsAllEmbedded)).isSome)
  t "assert failure names the actual"
    (((Check.one shipped (mkAssert (.pages .eq 1))).map (·.message)).any
      fun m => (m.splitOn "actual: 2").length == 2)
  t "assert all reports every failure"
    ((Check.all shipped #[mkAssert (.pages .eq 1), mkAssert (.pages .eq 2),
      mkAssert (.pages .lt 1)]).size == 2)

def tokensChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \tokens: font-relative lengths, derived tokens, and \block spacing
  let tokSrc := "\\documentclass{article}\n" ++
    "\\tokens{ rhythm = 2ex plus 0.5ex, sep = 0.75 * rhythm, slab = 18pt }\n" ++
    "\\begin{document}\\block[before = sep]{x}\\end{document}"
  let (tokDoc, tokDs) := elabStr tokSrc
  t "tokens source clean" tokDs.isEmpty
  t "tokens ex is symbolic" (tokDoc.tokens.find? "rhythm" ==
    some { width := { ex := 2000 }, stretch := { ex := 500 } })
  t "tokens derived scales earlier" (tokDoc.tokens.find? "sep" ==
    some { width := { ex := 1500 }, stretch := { ex := 375 } })
  t "tokens absolute" (tokDoc.tokens.find? "slab" ==
    some { width := Dim.Length.ofSp (Dim.pt 18) })
  t "block carries declared spacing" (tokDoc.body.any fun b =>
    match b with
    | .spaced before _ => before.value.width.ex == 1500
    | _ => false)
  -- A bare name is a well-formed value of the wrong type (E0323); text that
  -- parses as nothing at all is E0321. Both rejected, code says which.
  t "tokens reject wrong type" (errCodes ("\\documentclass{article}\\tokens{ a = wat }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "tokens reject junk" (errCodes
    ("\\documentclass{article}\\tokens{ a = 3 furlongs }" ++
     "\\begin{document}x\\end{document}") == ["E0321"])
  t "block unknown key" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block[after = 1pt]{x}\\end{document}") == ["E0322"])
  t "block needs a body" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block\\end{document}") == ["E0304"])

  -- Length resolution against real font metrics
  t "length resolve ex" ((Dim.Length.mk 0 0 1000).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 5)
  t "length resolve em" ((Dim.Length.mk 0 1500 0).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 15)
  t "length resolve mixed"
    ((Dim.Length.mk (Dim.pt 2) 1000 1000).resolve (Dim.pt 10) (Dim.pt 4) == Dim.pt 16)

  -- text symbols keep the space after them, unlike other control words
  t "symbol keeps space" (toks "a \\middot b" ==
    [.word "a", .space, .ctrl "middot", .space, .word "b"])
  t "command still eats space" (toks "a \\textbf b" ==
    [.word "a", .space, .ctrl "textbf", .word "b"])
  let (symDoc, symDs) := elabStr "a \\middot b \\ldots"
  t "symbol elaborates" (symDs.isEmpty && symDoc.body ==
    #[.para #[.text "a · b …"]])

def smartChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- smart punctuation: what the author typed is what they meant
  t "smart en dash" ((elabStr "2021--2024").1.body == #[.para #[.text "2021–2024"]])
  t "smart em dash" ((elabStr "a---b").1.body == #[.para #[.text "a—b"]])
  t "smart ellipsis" ((elabStr "wait...").1.body == #[.para #[.text "wait…"]])
  t "smart quotes directional"
    ((elabStr "say \"hi\" and don't").1.body == #[.para #[.text "say “hi” and don’t"]])
  t "mono keeps punctuation literal"
    ((elabStr "\\texttt{a--b}").1.body ==
      #[.para #[.styled .mono #[.text "a--b"]]])
  -- TeX's quote ligatures: `` '' ` and the Spanish !` ?` pairs are what a
  -- LaTeX author types for curly quotes (TeXbook ch. 2 and Appendix F).
  t "tex double quotes" ((elabStr "``x''").1.body == #[.para #[.text "“x”"]])
  t "tex single quotes" ((elabStr "`x'").1.body == #[.para #[.text "‘x’"]])
  t "tex quotes around an apostrophe"
    ((elabStr "``don't''").1.body == #[.para #[.text "“don’t”"]])
  t "tex double open after a space"
    ((elabStr "a ``b'' c").1.body == #[.para #[.text "a “b” c"]])
  t "spanish open exclamation" ((elabStr "!`ay!").1.body == #[.para #[.text "¡ay!"]])
  t "spanish open question" ((elabStr "?`ay?").1.body == #[.para #[.text "¿ay?"]])
  t "mono keeps backticks literal"
    ((elabStr "\\texttt{``x''}").1.body ==
      #[.para #[.styled .mono #[.text "``x''"]]])
  -- smartPunct is idempotent: every rewritable spelling is consumed on the
  -- first pass, so the curly output is a fixed point. Property test over an
  -- adversarial corpus; the theorem needs a multi-invariant induction over
  -- `go`'s accumulator and is not stated yet.
  let punctSamples := ["``x''", "`x'", "``don't''", "a ``b'' c", "!`ay!", "?`ay?",
    "----", "-----", "....", ".....", "''''", "'''", "```", "!``", "?``", "?`?`",
    "say \"hi\" and don't", "2021--2024", "a---b", "wait...", "-.-.", "([\"'"]
  t "smartPunct idempotent on the ligature corpus"
    (punctSamples.all fun s =>
      Ir.smartPunct (Ir.smartPunct s) == Ir.smartPunct s)

/-- The picture subset's boundary is named, never silent: a construct
outside the subset is W0334 naming it, an unreadable expression, range, or
colour inside it is E0333 — and the supported shapes around either still
elaborate (the nothing-silently-skipped contract, as a test). The wrap
declares `tool = none`: the boundary is open by default, and these checks
witness the subset's own diagnostics, which routing would consume. The
unroll and arithmetic facts are checked through the IR the elaborator
ships. -/
def pictureElabChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String :=
    "\\pictures{ tool = none }\\palette{ grid = #2A6F4E }" ++
    "\\begin{document}\\begin{tikzpicture}" ++
    body ++ "\\end{tikzpicture}\\end{document}"
  let picOf (src : String) : Option Ir.Pic.Picture :=
    (elabStr src).1.body.findSome? fun b => match b with
      | .picture p => some p
      | _ => none
  let cm := Dim.mm 10
  t "a foreach of fills unrolls to exactly its range's count"
    ((picOf (wrap "\\foreach \\x in {1,...,3}{\\fill (\\x,0) rectangle ++(1,1);}")).map
      (·.shapes.size) == some 3)
  t "the pair form binds both variables"
    ((picOf (wrap "\\foreach \\k/\\lbl in {1/aa,2/bb}{\\node at (\\k,0) {\\lbl};}")).map
      (·.shapes) == some #[.label cm 0 #[.text "aa"] Ir.Color.black 1000 .center,
                           .label (2 * cm) 0 #[.text "bb"] Ir.Color.black 1000 .center])
  t "truncatemacro floors to a whole unit"
    ((picOf (wrap "\\pgfmathtruncatemacro{\\k}{7/2}\\fill (0,0) rectangle (\\k,1);")).map
      (·.shapes) == some #[.rect 0 0 (3 * cm) cm Ir.Color.black])
  t "ifthenelse picks its branch by the comparison"
    ((picOf (wrap "\\foreach \\k in {1,2}{\
\\pgfmathsetmacro{\\c}{ifthenelse(\\k<2,\"black\",\"white\")}\
\\node[text=\\c] at (\\k,0) {x};}")).map
      (·.shapes) == some #[.label cm 0 #[.text "x"] Ir.Color.black 1000 .center,
                           .label (2 * cm) 0 #[.text "x"] Ir.Color.white 1000 .center])
  t "max and * evaluate inside a coordinate"
    ((picOf (wrap "\\fill (0,0) rectangle (max(1,2)*2, 1);")).map (·.shapes) ==
      some #[.rect 0 0 (4 * cm) cm Ir.Color.black])
  t "scale= scales every coordinate"
    ((picOf (wrap "[scale=0.5]\\fill (0,0) rectangle (2,2);")).map (·.shapes) ==
      some #[.rect 0 0 cm cm Ir.Color.black])
  t "a relative corner adds to its anchor"
    ((picOf (wrap "\\fill (1,1) rectangle ++(1,1);")).map (·.shapes) ==
      some #[.rect cm cm cm cm Ir.Color.black])
  t "a construct outside the subset is W0334, and the rest still draws"
    (warnCodes (wrap "\\draw (0,0) circle (1);\\fill (0,0) rectangle (1,1);") ==
        ["W0334"] &&
      (picOf (wrap "\\draw (0,0) circle (1);\\fill (0,0) rectangle (1,1);")).map
        (·.shapes.size) == some 1)
  t "a zero-step range is E0333, not a hang"
    (errCodes (wrap "\\foreach \\x in {1,1,...,5}{\\fill (\\x,0) rectangle ++(1,1);}") ==
      ["E0333"])
  t "a range walking away from its bound is E0333"
    (errCodes (wrap "\\foreach \\x in {5,4,...,9}{\\fill (\\x,0) rectangle ++(1,1);}") ==
      ["E0333"])
  t "division by zero is E0333 and loses only its shape"
    (errCodes (wrap "\\fill (1/0,0) rectangle (1,1);\\fill (0,0) rectangle (1,1);") ==
        ["E0333"] &&
      (picOf (wrap "\\fill (1/0,0) rectangle (1,1);\\fill (0,0) rectangle (1,1);")).map
        (·.shapes.size) == some 1)
  t "an unknown colour is E0333 naming the spelling"
    ((elabStr (wrap "\\fill[nosuch!30] (0,0) rectangle (1,1);")).2.any fun d =>
      d.code == "E0333" && hasStr d.message "nosuch!30")
  t "an unknown macro is E0333"
    (errCodes (wrap "\\fill (\\nope,0) rectangle (1,1);") == ["E0333"])
  t "an unsupported node option loses only the option"
    (warnCodes (wrap "\\node[ellipse] at (1,1) {x};") == ["W0334"] &&
      (picOf (wrap "\\node[ellipse] at (1,1) {x};")).map (·.shapes.size) == some 1)
  -- Node outlines: circle/rectangle with draw/fill and a declared minimum
  -- (pgf manual §"Shapes": extent = max(minimum, text + 2·inner sep);
  -- the minimum is the whole answer when it dominates the body, the case
  -- the subset renders).
  t "a drawn circle node ships its outline at half the minimum size"
    ((picOf (wrap "\\node[circle, draw, minimum size=8mm, inner sep=1pt] at (0,0) {x};")).map
      (·.shapes) == some #[
        .circle 0 0 (8000 * Dim.mm 10 / 10000 / 2) (some ({} : Ir.Pic.Stroke)) none,
        .label 0 0 #[.text "x"] Ir.Color.black 1000 .center])
  t "a filled rectangle node ships its frame centred on the anchor"
    ((picOf (wrap "\\node[rectangle, draw=grid, fill=white, thick, dashed, \
minimum width=10mm, minimum height=6mm] at (1,1) {x};")).map (·.shapes) ==
      (let w := 10000 * Dim.mm 10 / 10000
       let h := 6000 * Dim.mm 10 / 10000
       some #[
        .frame (cm - w / 2) (cm - h / 2) w h
          (some { color := { r := 42, g := 111, b := 78 }
                  width := Ir.Pic.thickWidth, dash := .dashed })
          (some Ir.Color.white),
        .label cm cm #[.text "x"] Ir.Color.black 1000 .center]))
  t "a drawn node without a minimum names the loss and keeps its label"
    (warnCodes (wrap "\\node[circle, draw] at (0,0) {x};") == ["W0334"] &&
      (picOf (wrap "\\node[circle, draw] at (0,0) {x};")).map (·.shapes.size) == some 1)
  t "a shape option without draw or fill draws nothing and warns nothing"
    ((elabStr (wrap "\\node[circle, minimum size=8mm] at (0,0) {x};")).2.isEmpty &&
      (picOf (wrap "\\node[circle, minimum size=8mm] at (0,0) {x};")).map
        (·.shapes.size) == some 1)
  t "transform shape scales the node's minimum with the picture"
    ((picOf (wrap "[scale=0.5, transform shape]\\node[circle, draw, \
minimum size=8mm] at (0,0) {x};")).map (·.shapes[0]?) ==
      some (some (.circle 0 0 (8000 * Dim.mm 10 / 10000 / 2 / 2) (some ({} : Ir.Pic.Stroke)) none)))
  t "a math node body elaborates as a formula"
    (((picOf (wrap "\\node at (0,0) {$x$};")).map fun p =>
      p.shapes.any fun s => match s with
        | .label _ _ content _ _ _ => content.any fun inl => match inl with
          | .formula false "x" _ => true
          | _ => false
        | _ => false).getD false)
  -- Edges: `\draw (a) -- (b)` border-anchors named endpoints
  -- (`rectBorder_exact`/`circleBorder_step` are the geometry; this is
  -- the wiring). On-axis anchors are exact, so equality is assertable.
  let rr := 8000 * Dim.mm 10 / 10000 / 2
  let twoCircles := "\\node[circle, draw, minimum size=8mm] (u) at (0,0) {x};" ++
    "\\node[circle, draw, minimum size=8mm] (v) at (2,0) {y};"
  t "an edge between two named circles border-anchors both ends"
    ((picOf (wrap (twoCircles ++ "\\draw (u) -- (v);"))).bind (fun p => p.shapes.back?) ==
      some (.edge #[.line rr 0 (2 * cm - rr) 0] {} none))
  t "an arrow edge shortens its line and ships a tip"
    (((picOf (wrap (twoCircles ++ "\\draw[->, thick] (u) -- (v);"))).map fun p =>
      p.shapes.any fun s => match s with
        | .edge segs st (some _) =>
          st.width == Ir.Pic.thickWidth &&
          (segs[0]?.map fun sg => match sg with
            | .line _ _ x2 _ => decide (x2 < 2 * cm - rr)
            | .cubic _ _ _ _ _ _ _ _ => false).getD false
        | _ => false).getD false)
  t "an edge naming no node is E0333"
    (errCodes (wrap "\\draw (a) -- (0,0);") == ["E0333"])
  t "draw= on an edge sets the stroke colour"
    ((picOf (wrap "\\draw[draw=grid] (0,0) -- (1,0);")).map (fun p =>
      p.shapes.any fun s => match s with
        | .edge _ st _ => st.color == { r := 42, g := 111, b := 78 }
        | _ => false) == some true)
  t "a waypoint coordinate chains segments"
    ((picOf (wrap "\\draw (0,0) -- (1,1) -- (2,0);")).map (fun p =>
      p.shapes.any fun s => match s with
        | .edge segs _ _ => segs.size == 2
        | _ => false) == some true)
  t "a path operation outside the subset loses the edge by name"
    ((elabStr (wrap "\\draw (0,0) circle (1);")).2.any fun d =>
      d.code == "W0334" && hasStr d.message "'circle'")
  -- `to[out=,in=]` curves: control points 0.3915·‖d‖ along the declared
  -- tangents (pgf To-Path library), mid-path labels at the Bézier midpoint.
  t "a to[out,in] edge ships a cubic segment"
    ((picOf (wrap "\\draw (0,0) to[out=90,in=180] (2,2);")).map (fun p =>
      p.shapes.any fun s => match s with
        | .edge segs _ _ => segs.any fun sg => match sg with
          | .cubic _ _ _ _ _ _ _ _ => true
          | .line _ _ _ _ => false
        | _ => false) == some true)
  t "a bare to draws the straight line, silently"
    ((elabStr (wrap "\\draw (0,0) to (1,1);")).2.isEmpty &&
      (picOf (wrap "\\draw (0,0) to (1,1);")).map (fun p =>
        p.shapes.any fun s => match s with
          | .edge segs _ _ => segs == #[.line 0 0 cm cm]
          | _ => false) == some true)
  t "a to with only one tangent names the loss and draws straight"
    (warnCodes (wrap "\\draw (0,0) to[out=90] (1,1);") == ["W0334"] &&
      (picOf (wrap "\\draw (0,0) to[out=90] (1,1);")).map (·.shapes.size) == some 1)
  t "a mid-path node labels the segment at its midpoint"
    ((picOf (wrap "\\draw (0,0) -- node {mid} (2,0);")).map (fun p =>
      p.shapes.any fun s => match s with
        | .label x y content _ _ _ => x == cm && y == 0 && content == #[.text "mid"]
        | _ => false) == some true)
  t "an edge label's placement option anchors the named side on the point"
    ((picOf (wrap "\\draw (0,0) -- node[right] {m} (2,0);")).map (fun p =>
      p.shapes.any fun s => match s with
        | .label _ _ _ _ _ al => al == .west
        | _ => false) == some true)
  t "a chained to path keeps every waypoint segment"
    ((picOf (wrap "\\draw (0,0) to[out=90,in=180] (1,1) to[out=0,in=180] (2,0);")).map
      (fun p => p.shapes.any fun s => match s with
        | .edge segs _ _ => segs.size == 2
        | _ => false) == some true)
  t "one construct looped forty times is one diagnostic, not forty"
    (warnCodes (wrap "\\foreach \\x in {1,...,40}{\\draw (\\x,0) circle (1);}") ==
      ["W0334", "W0362"])
  t "an empty tikzpicture ships no block and no diagnostic"
    ((elabStr (wrap "")).2.isEmpty && (picOf (wrap "")).isNone)

/-- The `.bib` grammar: entries, `@string` macros with `#` concatenation,
`@comment`/`@preamble`, brace nesting, both delimiter styles — and the keep
contract: a malformed entry is recorded and skipped, the rest of the file
parses. Names split into BibTeX's four parts from either comma form; values
render their TeX spellings as plain scalars. -/
def bibChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let p := Bib.parse
  let one := p "@article{doe2024, author = {Alex Doe}, title = {A Study}, year = 2024}"
  t "bib: one entry parses whole"
    (one.entries.map (·.key) == #["doe2024"] && one.errors.isEmpty &&
      (one.entries[0]?.map (·.kind)) == some "article" &&
      (one.entries[0]?.bind (·.field? "year")) == some "2024" &&
      (one.entries[0]?.bind (·.field? "author")) == some "Alex Doe")
  t "bib: field names fold to lowercase, keys keep case"
    (((p "@ARTICLE{DoE, TITLE = {x}}").entries[0]?).map (fun e => (e.key, e.field? "title"))
      == some ("DoE", some "x"))
  t "bib: braces nest and protect"
    ((p "@misc{k, title = {a {b {c}} d}}").entries[0]?.bind (·.field? "title")
      == some "a {b {c}} d")
  t "bib: quoted values, brace-protected quote"
    ((p "@misc{k, title = \"the {\"}x{\"} spelling\"}").entries[0]?.bind (·.field? "title")
      == some "the {\"}x{\"} spelling")
  t "bib: string macros concatenate with #"
    ((p "@string{tj = {Journal of Tests}}\n@article{k, journal = tj # { B}}").entries[0]?.bind
      (·.field? "journal") == some "Journal of Tests B")
  t "bib: month macros are predefined"
    ((p "@misc{k, month = jun}").entries[0]?.bind (·.field? "month") == some "June")
  t "bib: parenthesis delimiters"
    ((p "@article(k, year = 1999)").entries[0]?.bind (·.field? "year") == some "1999")
  t "bib: text between entries is comment"
    ((p "stray words @misc{k, year=1} more strays").entries.size == 1)
  t "bib: @comment and @preamble are consumed"
    (let r := p "@comment{x}\n@preamble{\"\\x\"}\n@misc{k, year=1}"
     r.entries.size == 1 && r.errors.isEmpty)
  let broken := p "@article{bad, title = {open\n@misc{good, year = 2020}}\n@book{also, year=2021}"
  t "bib: a malformed entry is recorded and the rest is kept"
    (!broken.errors.isEmpty && broken.entries.map (·.key) == #["also"])
  t "bib: an error names its line"
    ((p "@misc{k,\n  title = ?}").errors.any fun (pos, _) => pos.line == 2)
  t "bib: unknown macro keeps its name visible"
    ((p "@misc{k, journal = mystery}").entries[0]?.bind (·.field? "journal")
      == some "mystery")
  -- Names: the four-part split from both comma forms and the plain form.
  t "bib: names split on the word and, braces opaque"
    (Bib.splitNames "Doe, Alex and {Sand and Gravel Ltd} and others" ==
      #["Doe, Alex", "{Sand and Gravel Ltd}", "others"])
  t "bib: Last, First"
    (Bib.parseName "Doe, Alex" == { first := "Alex", last := "Doe" })
  t "bib: von parts from the comma form"
    (Bib.parseName "van der Berg, Alex" ==
      { first := "Alex", von := "van der", last := "Berg" })
  t "bib: Last, Jr, First"
    (Bib.parseName "Doe, Jr, Alex" == { first := "Alex", last := "Doe", jr := "Jr" })
  t "bib: First von Last"
    (Bib.parseName "Alex van der Berg" ==
      { first := "Alex", von := "van der", last := "Berg" })
  t "bib: First Middle Last"
    (Bib.parseName "Alex B. Doe" == { first := "Alex B.", last := "Doe" })
  t "bib: a braced token is one caseless token of the last name"
    (Bib.parseName "{Example Corp}" == { last := "{Example Corp}" })
  t "bib: full-name order is First von Last, Jr"
    ((Bib.parseName "Doe, Jr, Alex").full == "Alex Doe, Jr")
  t "bib: and-join two, three, elided"
    (Bib.andJoin ["A"] == "A" && Bib.andJoin ["A", "B"] == "A and B" &&
      Bib.andJoin ["A", "B", "C"] == "A, B, and C" &&
      Bib.andJoin ["A", "others"] == "A et al." &&
      Bib.andJoin ["A", "B", "others"] == "A, B, et al.")
  t "bib: label names for citet"
    (Bib.labelNames "Doe, Alex" == "Doe" &&
      Bib.labelNames "Doe, Alex and Roe, Sam" == "Doe and Roe" &&
      Bib.labelNames "Doe, Alex and Roe, Sam and Poe, Kim" == "Doe et al." &&
      Bib.labelNames "Doe, Alex and others" == "Doe et al.")
  -- Value text: TeX spellings become plain scalars.
  t "bib: accents compose"
    (Bib.text "K{\\\"u}nzel and \\'{e} and {\\`o} and \\c{c}" == "Künzel and é and ò and ç")
  t "bib: escapes, ties, dashes"
    (Bib.text "Smith \\& Jones~Ltd, 3--7 --- yes" == "Smith & Jones Ltd, 3–7 — yes")
  t "bib: braces drop, whitespace folds"
    (Bib.text "a {Grand}  title\n  across lines" == "a Grand title across lines")
  t "bib: unknown command keeps its name"
    (Bib.text "\\mystery{x}" == "mysteryx")
  t "bib: sentence case keeps the first char, protection, and colon starts"
    (Bib.sentenceCase "The Great {DNA} Hunt: A Survey" == "The great {DNA} hunt: A survey")

/-- The four style axes: one field renderer under per-type field orders,
citation rendering per style, name formatting, and the named records. The
expected strings transcribe plainnat.bst's output shapes for each FUNCTION
named in `plainnatSteps`'s docstring. -/
def bibStyleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let entry (kind : String) (fields : List (String × String)) : Bib.Entry :=
    { kind
      key := "k1"
      fields := fields.toArray
      pos := {} }
  let render (e : Bib.Entry) : String :=
    Ir.plainText (Bib.renderEntry {} (Bib.plainnatSteps e) e)
  t "bibstyle: article renders authors, sentence title, journal group"
    (render (entry "article"
      [("author", "Doe, Alex and Roe, Sam"), ("title", "A Grand Study of Things"),
       ("journal", "Journal of Tests"), ("volume", "12"), ("number", "3"),
       ("pages", "45--67"), ("year", "2024")]) ==
      "Alex Doe and Sam Roe. A grand study of things. Journal of Tests, 12(3):45–67, 2024.")
  t "bibstyle: book keeps its title case, emphasized, publisher group"
    (render (entry "book"
      [("author", "Doe, Alex"), ("title", "The Grand Book"),
       ("publisher", "Example Press"), ("edition", "Third"), ("year", "2020")]) ==
      "Alex Doe. The Grand Book. Example Press, third edition, 2020.")
  t "bibstyle: inproceedings takes In booktitle, pages spelled out"
    (render (entry "inproceedings"
      [("author", "Doe, Alex"), ("title", "On Tests"),
       ("booktitle", "Proceedings of Examples"), ("pages", "1--10"),
       ("year", "2021")]) ==
      "Alex Doe. On tests. In Proceedings of Examples, pages 1–10, 2021.")
  t "bibstyle: misc renders howpublished and a linked URL"
    (let e := entry "misc"
      [("author", "Doe, Alex"), ("title", "A Web Thing"),
       ("howpublished", "Online"), ("year", "2022"),
       ("url", "https://example.org/x")]
     let out := Bib.renderEntry {} (Bib.plainnatSteps e) e
     Ir.plainText out ==
       "Alex Doe. A web thing. Online, 2022. URL https://example.org/x." &&
     out.any fun x => match x with
       | .link u _ => u == "https://example.org/x"
       | _ => false)
  t "bibstyle: an absent sentence leaves nothing, no stray period"
    (render (entry "article" [("author", "Doe, Alex"), ("title", "T"),
      ("year", "2024")]) == "Alex Doe. T. 2024.")
  t "bibstyle: an entry with no author falls back to editors"
    (render (entry "book" [("editor", "Roe, Sam"), ("title", "Edited"),
      ("year", "2019")]) == "Sam Roe, editor. Edited. 2019.")
  let e1 : Bib.Entry := entry "article"
    [("author", "Doe, Alex and Roe, Sam"), ("year", "2024")]
  let r1 : Bib.Resolved := { key := "k1", position := 3, entry := e1 }
  let e2 : Bib.Entry :=
    { kind := "misc"
      key := "k2"
      fields := #[("author", "Poe, Kim and others"), ("year", "2020")]
      pos := {} }
  let r2 : Bib.Resolved := { key := "k2", position := 1, entry := e2 }
  let cite (p : Bib.CitePunct) (cmd : Ir.CiteCmd) (ps : Array (Option Bib.Resolved)) :=
    Ir.plainText (Bib.renderCite p { cmd } ps)
  t "bibstyle: numeric citep brackets and joins"
    (cite Bib.latexPunct .paren #[some r1, some r2] == "[3, 1]")
  t "bibstyle: numeric citet names then bracket"
    (cite Bib.latexPunct .textual #[some r1] == "Doe and Roe [3]")
  t "bibstyle: author-year citep, natbib's load values, parenthesizes with semicolons"
    (cite {} .paren #[some r1, some r2] ==
      "(Doe and Roe, 2024; Poe et al., 2020)")
  t "bibstyle: author-year citet puts the year in parens"
    (cite {} .textual #[some r1, some r2] ==
      "Doe and Roe (2024); Poe et al. (2020)")
  t "bibstyle: the nat styles' row brackets author-year in squares, commas between"
    (cite Bib.natPunct .paren #[some r1, some r2] ==
      "[Doe and Roe, 2024, Poe et al., 2020]")
  t "bibstyle: an unresolved key prints ? in place"
    (cite Bib.latexPunct .paren #[some r1, none] == "[3, ?]")
  t "bibstyle: citation pieces link to the entry anchor"
    ((Bib.renderCite Bib.latexPunct { cmd := .paren } #[some r1]).any fun x =>
      match x with
      | .link u _ => u == "#ref-k1"
      | _ => false)
  t "bibstyle: named styles pair the axes; unknown is none"
    (((Bib.Style.named "unsrtnat").map (fun s => (s.punct, s.sort)))
        == some (Bib.natPunct, .citation) &&
      ((Bib.Style.named "plainnat").map (fun s => (s.punct, s.sort)))
        == some (Bib.natPunct, .authorYear) &&
      ((Bib.Style.named "plain").map (fun s => (s.punct, s.sort)))
        == some (Bib.latexPunct, .authorYear) &&
      ((Bib.Style.named "unsrt").map (fun s => (s.punct, s.sort)))
        == some (Bib.latexPunct, .citation) &&
      (Bib.Style.named "mystery").isNone)
  -- abbrvnat/abbrv: plainnat/plain with only the abbreviation axis set
  -- (abbrvnat.bst and abbrv.bst FUNCTION {format.names}: `{f.~}{vv~}{ll}{, jj}`
  -- where the plain pair has `{ff~}` — the one designator that differs).
  t "bibstyle: abbrv styles differ from the plain pair only in the name axis"
    (((Bib.Style.named "abbrvnat").map (fun s => (s.punct, s.sort, s.names)))
        == some (Bib.natPunct, .authorYear, { initials := true }) &&
      ((Bib.Style.named "abbrv").map (fun s => (s.punct, s.sort, s.names)))
        == some (Bib.latexPunct, .authorYear, { initials := true }))
  t "bibstyle: abbrv names are J. Smith, never Smith, J."
    (Bib.abbrvNames.render (Bib.parseName "Smith, Jane") == "J. Smith" &&
      Bib.abbrvNames.renderList "Smith, Jane and Doe, Alex B." ==
        "J. Smith and A. B. Doe")
  t "bibstyle: initials and last-first are name-format axes"
    (({ initials := true } : Bib.NameFormat).render (Bib.parseName "Doe, Alex B.")
        == "A. B. Doe" &&
      ({ lastFirst := true } : Bib.NameFormat).render
        (Bib.parseName "van der Berg, Alex") == "Berg, van der Alex")
  t "bibstyle: et-al truncation is a name-format axis"
    (({ etAlAfter := some 2 } : Bib.NameFormat).renderList
      "Doe, Alex and Roe, Sam and Poe, Kim" == "Alex Doe et al.")

/-- The IR carries citations and the reference list: census text, the
one unresolved-mark site, and the request value the driver fulfils. -/
def bibIrChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "bib-ir: an unresolved citation is worth one mark per key"
    (Ir.plainText #[.cite { cmd := .paren } #["a", "b"]] == "?, ?")
  let item : Ir.BibItem :=
    { key := "k1"
      marker := some "1"
      content := #[.text "Alex Doe. A study. 2024."] }
  t "bib-ir: every entry's text is census content"
    (Ir.blockTextList "" [.bibliography "refs" (some "unsrtnat") #[item]] ==
      "Alex Doe. A study. 2024.")
  t "bib-ir: the bibliography names its source for the driver"
    (Ir.bibRefs { body := #[.center #[.bibliography "refs" none #[]],
      .bibliography "refs" none #[], .bibliography "other" none #[]] } ==
      #["refs", "other"])
  t "bib-ir: anchor naming has one site"
    (Ir.bibAnchor "k1" == "ref-k1" && Bib.anchorOf "k1" == "#ref-k1")

/-- Resolution: first-citation order, numbering as sort position, the
rewrite confined to citations and the reference list, and the three
diagnostics. -/
def bibApplyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@misc{a, author = {Doe, Alex}, title = {First}, year = 2024}\n" ++
    "@misc{b, author = {Roe, Sam}, title = {Second}, year = 2020}\n" ++
    "@misc{c, author = {Poe, Kim}, title = {Third}, year = 2022}"
  let doc (style : Option String) (natbib : Option (Array String) := none) : Ir.Doc :=
    { natbib
      body := #[
        .para #[.text "x ", .cite { cmd := .paren } #["b"], .text " y ", .cite { cmd := .textual } #["a"]],
        .para #[.cite { cmd := .paren } #["c", "b"]],
        .bibliography "refs" style #[]] }
  let run (style : Option String) (natbib : Option (Array String) := none) :=
    Bib.apply #[("refs", bib)] (doc style natbib)
  let (outU, dsU) := run (some "unsrtnat")
  t "apply: no diagnostics on a clean resolution" dsU.isEmpty
  let itemsOf (d : Ir.Doc) : Array Ir.BibItem :=
    d.body.foldl (fun acc b => match b with
      | .bibliography _ _ items => acc ++ items
      | _ => acc) #[]
  let paraText (d : Ir.Doc) (i : Nat) : String :=
    match d.body[i]? with
    | some (Ir.Block.para xs) => Ir.plainText xs
    | _ => ""

  t "apply: unsrtnat lists cited keys in first-citation order, each once"
    ((itemsOf outU).map (·.key) == #["b", "a", "c"])
  t "apply: numeric markers are the 1-based list positions"
    ((itemsOf outU).map (·.marker) == #[some "1", some "2", some "3"])
  t "apply: citation marks carry the entry's list position"
    (paraText outU 0 == "x [1] y Doe [2]" && paraText outU 1 == "[3, 1]")
  t "apply: entries format through the style"
    ((itemsOf outU).map (fun i => Ir.plainText i.content) ==
      #["Sam Roe. Second, 2020.", "Alex Doe. First, 2024.", "Kim Poe. Third, 2022."])
  -- plainnat: the same document, the other record, natbib loaded.
  let (outP, dsP) := run (some "plainnat") (some #[])
  t "apply: plainnat sorts by author then year, marks nothing"
    ((itemsOf outP).map (·.key) == #["a", "c", "b"] &&
      (itemsOf outP).all (·.marker.isNone))
  t "apply: plainnat cites author-year in its own square brackets"
    (paraText outP 0 == "x [Roe, 2020] y Doe [2024]")
  -- abbrvnat: plainnat's ordering with initials in the list; a fourth
  -- record, no new code path (W0353 stays silent for it).
  let (outA, dsA) := run (some "abbrvnat") (some #[])
  t "apply: abbrvnat abbreviates list names and keeps plainnat's order"
    (dsA.isEmpty && (itemsOf outA).map (·.key) == #["a", "c", "b"] &&
      ((itemsOf outA).map fun i => Ir.plainText i.content) ==
        #["A. Doe. First, 2024.", "K. Poe. Third, 2022.", "S. Roe. Second, 2020."])
  t "apply: style independence — each entry's content identical across styles"
    (dsP.isEmpty &&
      (itemsOf outU).all fun i =>
        ((itemsOf outP).find? (·.key == i.key)).map (fun j => Ir.plainText j.content)
          == some (Ir.plainText i.content))
  -- The three diagnostics, each with its contract.
  let (outG, dsG) := Bib.apply #[("refs", bib)]
    { body := #[.para #[.cite { cmd := .paren } #["ghost", "a"]],
        .bibliography "refs" none #[]] }
  t "apply: an unknown key warns W0351 and shows ? beside its neighbours"
    ((dsG.map (·.code)) == #["W0351"] && paraText outG 0 == "[?, 1]")
  let (outB, dsB) := Bib.apply #[("refs", "@misc{broken, year = ?}\n" ++ bib)]
    { body := #[.para #[.cite { cmd := .paren } #["a"]], .bibliography "refs" none #[]] }
  t "apply: a malformed entry warns W0352 at its .bib position, rest kept"
    (dsB.map (·.code) == #["W0352"] &&
      (dsB[0]?.bind (·.span)).map (·.file) == some "refs" &&
      (itemsOf outB).map (·.key) == #["a"])
  let (_, dsM) := run (some "mystery")
  t "apply: an unknown style warns W0353 and falls back to the record"
    (dsM.map (·.code) == #["W0353"])
  -- No marker, no sources: the mark still resolves — to LaTeX's `[?]` — and
  -- no `.cite` node survives; the elaborator named the loss at the site
  -- (W0351, the no-bibliography cause), so `apply` says nothing here.
  let (outN, dsN) := Bib.apply #[] { body := #[.para #[.cite { cmd := .paren } #["a"]]] }
  t "apply: a document with no bibliography marker resolves every mark to [?], silently"
    (dsN == #[] && paraText outN 0 == "[?]" && (Ir.pendingNodes outN).isEmpty)

/-- The synthetic bibliography natbib's rows cite: invented people and
venues, one entry per name shape a citation prints differently — three
authors (`et al.`, and all three starred), one, two, and a lowercase
particle (`\Citet` capitalizes it). -/
def natbibBib : String :=
  "@article{alpha2019, author = {Ann Alpha and Bob Beta and Cy Gamma},\n\
    title = {A study of invented widgets}, journal = {Journal of Examples},\n\
    year = {2019}, volume = {3}, number = {2}, pages = {10--20}}\n\
  @book{delta2021, author = {Dee Delta}, title = {Placeholder Methods},\n\
    publisher = {Example Press}, year = {2021}}\n\
  @inproceedings{eps2020, author = {Eve Epsilon and Finn Zeta},\n\
    title = {On synthetic benchmarks},\n\
    booktitle = {Proceedings of the Example Workshop}, year = {2020}, pages = {1--8}}\n\
  @article{pome2018, author = {Quill de Pome}, title = {Lowercase particles},\n\
    journal = {Example Letters}, year = {2018}}\n"

/-- natbib's command table, one row per construct: the call, and the
lines lualatex set for it with `\bibliographystyle{unsrtnat}` — first
under `\usepackage[numbers]{natbib}`, then under a bare
`\usepackage{natbib}`, where unsrtnat's own row sets author-year in square
brackets. Measured with natbib 8.31b and TeX Live 2026 through
`pdftotext`, every row a paragraph `Lnn <call> end.` of one document over
`natbibBib`, so the numbers are first-citation positions in this order. -/
def natbibRows : List (String × String × String) :=
  [("\\citet{alpha2019}", "Alpha et al. [1]", "Alpha et al. [2019]"),
   ("\\citep{alpha2019}", "[1]", "[Alpha et al., 2019]"),
   ("\\cite{alpha2019}", "[1]", "Alpha et al. [2019]"),
   ("\\citet*{alpha2019}", "Alpha, Beta, and Gamma [1]", "Alpha, Beta, and Gamma [2019]"),
   ("\\citep*{alpha2019}", "[1]", "[Alpha, Beta, and Gamma, 2019]"),
   ("\\citep[p.~5]{alpha2019}", "[1, p. 5]", "[Alpha et al., 2019, p. 5]"),
   ("\\citep[see][]{alpha2019}", "[see 1]", "[see Alpha et al., 2019]"),
   ("\\citep[see][p.~5]{alpha2019}", "[see 1, p. 5]", "[see Alpha et al., 2019, p. 5]"),
   ("\\citet[p.~5]{alpha2019}", "Alpha et al. [1, p. 5]", "Alpha et al. [2019, p. 5]"),
   ("\\citet[see][p.~5]{alpha2019}", "Alpha et al. [see 1, p. 5]",
    "Alpha et al. [see 2019, p. 5]"),
   ("\\citep{alpha2019,delta2021}", "[1, 2]", "[Alpha et al., 2019, Delta, 2021]"),
   ("\\citet{alpha2019,delta2021}", "Alpha et al. [1], Delta [2]",
    "Alpha et al. [2019], Delta [2021]"),
   ("\\citealt{alpha2019}", "Alpha et al. 1", "Alpha et al. 2019"),
   ("\\citealp{alpha2019}", "1", "Alpha et al., 2019"),
   ("\\citealp[p.~5]{alpha2019}", "1, p. 5", "Alpha et al., 2019, p. 5"),
   ("\\citeauthor{alpha2019}", "Alpha et al.", "Alpha et al."),
   ("\\citeauthor*{alpha2019}", "Alpha, Beta, and Gamma", "Alpha, Beta, and Gamma"),
   ("\\citeyear{alpha2019}", "2019", "2019"),
   ("\\citeyearpar{alpha2019}", "[2019]", "[2019]"),
   ("\\Citet{pome2018}", "de Pome [3]", "De Pome [2018]"),
   ("\\Citep{pome2018}", "[3]", "[De Pome, 2018]"),
   ("\\citetext{priv.\\ comm.}", "[priv. comm.]", "[priv. comm.]"),
   ("\\citenum{alpha2019}", "1", "1"),
   ("\\citet{eps2020}", "Epsilon and Zeta [4]", "Epsilon and Zeta [2020]"),
   ("\\citep{eps2020,pome2018}", "[4, 3]", "[Epsilon and Zeta, 2020, de Pome, 2018]"),
   ("\\cite[p.~5]{alpha2019}", "[1, p. 5]", "[Alpha et al., 2019, p. 5]"),
   ("\\citealt*{alpha2019}", "Alpha, Beta, and Gamma 1", "Alpha, Beta, and Gamma 2019"),
   ("\\citeauthor{eps2020}", "Epsilon and Zeta", "Epsilon and Zeta"),
   ("\\Citeauthor{pome2018}", "de Pome", "De Pome")]

/-- The mode natbib runs in, one configuration per row: the preamble, the
style, and the lines lualatex set for `\citep{alpha2019,delta2021}`,
`\citet{alpha2019}` and `\cite{alpha2019}` — `none` where the style writes
no author-year label, since natbib then prints `(author?)` for a name the
engine reads from the `.bib`. No natbib is LaTeX's own `\cite`. -/
def natbibModes : List (String × String × List (Option String)) :=
  [("", "plain", [some "[1, 2]", none, some "[1]"]),
   ("\\usepackage{natbib}", "unsrtnat",
    [some "[Alpha et al., 2019, Delta, 2021]", some "Alpha et al. [2019]",
     some "Alpha et al. [2019]"]),
   ("\\usepackage[numbers]{natbib}", "unsrtnat",
    [some "[1, 2]", some "Alpha et al. [1]", some "[1]"]),
   ("\\usepackage[round]{natbib}", "plainnat",
    [some "(Alpha et al., 2019; Delta, 2021)", some "Alpha et al. (2019)",
     some "Alpha et al. (2019)"]),
   ("\\usepackage[authoryear]{natbib}", "plainnat",
    [some "[Alpha et al., 2019, Delta, 2021]", some "Alpha et al. [2019]",
     some "Alpha et al. [2019]"]),
   ("\\usepackage[numbers,round]{natbib}", "unsrtnat",
    [some "(1, 2)", some "Alpha et al. (1)", some "(1)"]),
   ("\\usepackage[round]{natbib}", "plain", [some "(1; 2)", none, some "(1)"]),
   ("\\usepackage{natbib}", "unsrt", [some "[1, 2]", none, some "[1]"]),
   ("\\usepackage[square,comma]{natbib}", "plainnat",
    [some "[Alpha et al., 2019, Delta, 2021]", some "Alpha et al. [2019]",
     some "Alpha et al. [2019]"]),
   ("\\usepackage[angle]{natbib}", "plainnat",
    [some "<Alpha et al., 2019; Delta, 2021>", some "Alpha et al. <2019>",
     some "Alpha et al. <2019>"]),
   ("\\usepackage[curly]{natbib}", "plainnat",
    [some "{Alpha et al., 2019; Delta, 2021}", some "Alpha et al. {2019}",
     some "Alpha et al. {2019}"]),
   ("\\usepackage[semicolon]{natbib}", "plainnat",
    [some "(Alpha et al., 2019; Delta, 2021)", some "Alpha et al. (2019)",
     some "Alpha et al. (2019)"]),
   ("\\usepackage[comma]{natbib}", "plainnat",
    [some "(Alpha et al., 2019, Delta, 2021)", some "Alpha et al. (2019)",
     some "Alpha et al. (2019)"]),
   ("\\usepackage[colon]{natbib}", "plainnat",
    [some "(Alpha et al., 2019; Delta, 2021)", some "Alpha et al. (2019)",
     some "Alpha et al. (2019)"]),
   ("\\usepackage[nobibstyle]{natbib}", "plainnat",
    [some "(Alpha et al., 2019; Delta, 2021)", some "Alpha et al. (2019)",
     some "Alpha et al. (2019)"]),
   ("\\usepackage[round,bibstyle]{natbib}", "plainnat",
    [some "[Alpha et al., 2019, Delta, 2021]", some "Alpha et al. [2019]",
     some "Alpha et al. [2019]"]),
   ("\\usepackage[square]{natbib}", "plainnat",
    [some "[Alpha et al., 2019; Delta, 2021]", some "Alpha et al. [2019]",
     some "Alpha et al. [2019]"])]

/-- natbib's preamble declarations, one configuration per row: the
preamble after `\usepackage{natbib}`, the style, and the lines lualatex set
for `\citep{alpha2019,delta2021}`, `\citet{alpha2019}` and
`\citep[see][p.~5]{alpha2019}`. A preamble declaration closes natbib's
`\bibstyle` door, so what it leaves unset keeps natbib's load value; natbib
reads each item exactly as written, so the space in `authoryear, square`
makes a word it drops and the brackets stay round. -/
def natbibDecls : List (String × String × List String) :=
  [("\\setcitestyle{authoryear,round,semicolon}", "plainnat",
    ["(Alpha et al., 2019; Delta, 2021)", "Alpha et al. (2019)",
     "(see Alpha et al., 2019, p. 5)"]),
   ("\\setcitestyle{numbers,square}", "unsrtnat",
    ["[1; 2]", "Alpha et al. [1]", "[see 1, p. 5]"]),
   ("\\bibpunct{(}{)}{;}{a}{,}{,}", "plainnat",
    ["(Alpha et al., 2019; Delta, 2021)", "Alpha et al. (2019)",
     "(see Alpha et al., 2019, p. 5)"]),
   ("\\setcitestyle{aysep={},notesep={; },citesep={;}}", "plainnat",
    ["(Alpha et al. 2019; Delta 2021)", "Alpha et al. (2019)",
     "(see Alpha et al. 2019; p. 5)"]),
   ("\\setcitestyle{authoryear, square}", "plainnat",
    ["(Alpha et al., 2019; Delta, 2021)", "Alpha et al. (2019)",
     "(see Alpha et al., 2019, p. 5)"]),
   ("\\bibpunct[: ]{[}{]}{,}{n}{}{,}", "unsrtnat",
    ["[1, 2]", "Alpha et al. [1]", "[see 1: p. 5]"]),
   ("\\setcitestyle{square}", "plainnat",
    ["[Alpha et al., 2019; Delta, 2021]", "Alpha et al. [2019]",
     "[see Alpha et al., 2019, p. 5]"])]

/-- The calls as one document, each in its own paragraph `Lk <call> end.`;
the style is declared in the preamble, where natbib reads it back at
`\begin{document}`. -/
def natbibSrc (pre style : String) (calls : List String) : String := Id.run do
  let mut body := ""
  for call in calls, k in [1:calls.length + 1] do
    body := body ++ s!"L{k} {call} end.\n\n"
  return s!"\\documentclass\{article}\n{pre}\n\\bibliographystyle\{{style}}\n\
    \\begin\{document}\n{body}\\bibliography\{refs}\n\\end\{document}\n"

/-- An HTML page's text as a reader gets it: tags dropped, the entities
the escaper writes read back, a no-break space a space. -/
def htmlVisibleText (page : String) : String := Id.run do
  let mut out := ""
  let mut inTag := false
  for c in page.toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return ((((out.replace "&lt;" "<").replace "&gt;" ">").replace "&nbsp;" " ").replace
    "&amp;" "&").replace "\u00A0" " "

/-- **natbib's commands set the lines lualatex sets**, on the shipped page
and in the HTML: every row of `natbibRows` in one synthetic document per
mode, resolved against `natbibBib` and laid out, each line compared whole
with the one lualatex set; then each configuration of `natbibModes`. An
unresolved key is the one declared divergence: natbib's numbers mode
prints `[? ]`, a space its source line leaves after the bold `?`, where
the engine prints `[?]` with the separators a resolved key would have. -/
def natbibChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let shipped (pre style : String) (calls : List String) : Array String × String × Bool :=
    let (doc, _) := elabStr (natbibSrc pre style calls)
    let (doc, bibDiags) := Bib.apply #[("refs", natbibBib)] doc
    ((bodyLines (layoutOf oneFace doc)).map lineInk, htmlVisibleText (HtmlDoc.emit {} doc).1,
      bibDiags.isEmpty)
  let calls := natbibRows.map (·.1)
  for (mode, pre, pick) in [("numbers", "\\usepackage[numbers]{natbib}",
      fun (r : String × String × String) => r.2.1),
      ("author-year", "\\usepackage{natbib}", fun (r : String × String × String) => r.2.2)] do
    let (lines, html, clean) := shipped pre "unsrtnat" calls
    t s!"natbib {mode}: the rows resolve with no diagnostic" clean
    for row in natbibRows, k in [1:natbibRows.length + 1] do
      let line := s!"L{k} {pick row} end."
      t s!"natbib {mode} page: {row.1} sets '{pick row}'" (lines.contains line)
      t s!"natbib {mode} html: {row.1} reads '{pick row}'" (hasStr html line)
  for (pre, style, wants) in natbibModes do
    let calls := if pre.isEmpty then ["\\cite{alpha2019,delta2021}", "\\cite{alpha2019}",
      "\\cite{alpha2019}"] else ["\\citep{alpha2019,delta2021}", "\\citet{alpha2019}",
      "\\cite{alpha2019}"]
    let (lines, html, _) := shipped pre style calls
    for want in wants, k in [1:4] do
      if let some w := want then
        t s!"natbib mode '{pre}' + {style}: line {k} sets '{w}'"
          (lines.contains s!"L{k} {w} end." && hasStr html s!"L{k} {w} end.")
  for (decl, style, wants) in natbibDecls do
    let (lines, html, _) := shipped ("\\usepackage{natbib}" ++ decl) style
      ["\\citep{alpha2019,delta2021}", "\\citet{alpha2019}", "\\citep[see][p.~5]{alpha2019}"]
    for want in wants, k in [1:4] do
      t s!"natbib {decl} + {style}: line {k} sets '{want}'"
        (lines.contains s!"L{k} {want} end." && hasStr html s!"L{k} {want} end.")
  -- The item natbib drops is named where it stands, under its command's key;
  -- in the body, where the engine does not read it, the declaration is named.
  let dropped := (elabStr (natbibSrc "\\usepackage{natbib}\\setcitestyle{authoryear, square}"
    "plainnat" ["x"])).2
  t "natbib: an item natbib does not read is named, keyed to its command"
    (dropped.any fun d => d.code == "W0101" && d.subject == some "ctrl:setcitestyle")
  let body := (elabStr (natbibSrc "\\usepackage{natbib}" "plainnat"
    ["\\setcitestyle{square}"])).1
  t "natbib: a body declaration leaves no ink and no punctuation"
    (body.natbib == some #[] && !hasStr (Ir.plainText (body.body.flatMap fun b =>
      match b with | Ir.Block.para xs => xs | _ => #[])) "square")
  let (miss, _, _) := shipped "\\usepackage[numbers]{natbib}" "unsrtnat" ["\\citep{missing2000}"]
  t "natbib: an unresolved key prints [?], the separators a resolved one has"
    (miss.contains "L1 [?] end.")

/-- The entries natbib's list checks set: invented people and titles, ten
so a numbered list carries labels of two widths (`[9]`, `[10]`), and the
tenth long enough to wrap, so an entry has continuation lines. -/
def natbibListBib : String := Id.run do
  let mut out := ""
  for k in [1:11] do
    let words := String.intercalate " "
      ((List.range (if k == 10 then 30 else 2)).map fun i => s!"widget{i}")
    out := out ++ s!"@misc\{e{k}, author = \{Ann Author}, title = \{Survey of {words}},\n\
      howpublished = \{Example Press}, year = \{{2000 + k}}}\n"
  return out

/-- A shipped line's segments with the x each starts at, from the line's own
origin. -/
def segStarts (l : Layout.LineOut) : Array (Dim.Sp × Layout.Seg) := Id.run do
  let mut x := l.x
  let mut out := #[]
  for s in l.segs do
    out := out.push (x, s)
    x := x + match s with
      | .run _ _ _ w _ _ _ _ _ _ => w
      | .gap w _ => w
      | .rule w _ _ _ => w
      | .image _ w _ => w
  return out

/-- The reference list's shipped lines, one array per entry: the lines after
the References heading that set glyphs (a link's underline ships as a
sibling line of rules), split where the leaf changes. -/
def bibEntryLines (lines : Array Layout.LineOut) : Array (Array Layout.LineOut) := Id.run do
  let start := ((lines.findIdx? (lineText · == "References")).map (· + 1)).getD lines.size
  let mut out : Array (Array Layout.LineOut) := #[]
  let mut cur : Array Layout.LineOut := #[]
  for l in (lines.extract start lines.size).filter hasGlyphRun do
    if !cur.isEmpty && cur.back?.map (·.leaf) != some l.leaf then
      out := out.push cur
      cur := #[]
    cur := cur.push l
  return if cur.isEmpty then out else out.push cur

/-- **The reference list is natbib's list**, on the shipped page and in the
HTML (`\NAT@bibsetup`, `\NAT@bibsetnum`, natbib.sty:627–644): an
author-year entry's first line stands at the margin and its continuation
lines one `\bibhang` in; a numbered entry's label stands right-aligned in a
column as wide as the widest label, `\labelsep` before a text column every
line of the entry shares; `\bibsep` stands between entries, so the baseline
step between two entries is the step inside one plus the gap. A declared
`\setlength{\bibhang}` or `\setlength{\bibsep}` moves exactly that, and
the HTML reads the same values through the same token names. Positions are
read at the measure edge (`x + hang`): character protrusion moves a first
line with its label, as it moves a list item with its bullet. Measured
under lualatex over the same shapes in TeX Gyre Termes at 10 pt: a hang of
9.96 pt, a `[3]` label column of 16.60 pt, entry steps of 19.93 pt against
11.96 pt inside an entry (`pdftotext -bbox`, ink edges). -/
def natbibListChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let build (pre : String) (keys : String) : Ir.Doc × Layout.Out × String :=
    let (doc, _) := elabStr s!"\\documentclass\{article}\n{pre}\n\
      \\bibliographystyle\{unsrtnat}\n\\begin\{document}\nL1 \\citep\{{keys}} end.\n\n\
      \\bibliography\{refs}\n\\end\{document}\n"
    let (doc, _) := Bib.apply #[("refs", natbibListBib)] doc
    (doc, layoutOf oneFace doc, (HtmlDoc.emit {} doc).1)
  let edge (l : Layout.LineOut) : Dim.Sp := l.x + l.hang
  let step (a b : Layout.LineOut) : Dim.Sp := b.y - a.y
  -- author-year: the long entry first, so one entry's own step is read
  let ay (pre : String) := build ("\\usepackage{natbib}" ++ pre) "e10,e1,e2"
  let (doc, out, html) := ay ""
  let geom := Layout.Geom.ofPage doc.page
  let em := geom.fontSize
  let es := bibEntryLines (bodyLines out)
  let rest (e : Array Layout.LineOut) := e.extract 1 e.size
  t s!"natbib list: three author-year entries ship, the first wrapping ({es.map (·.size)})"
    (es.size == 3 && decide ((es[0]?.map (·.size)).getD 0 ≥ 2))
  t "natbib list: an author-year entry's first line stands at the margin"
    (es.all fun e => e[0]?.map edge == some geom.hmargin)
  t "natbib list: its continuation lines hang one em in (\\bibhang)"
    (es.all fun e => (rest e).all fun l => edge l == geom.hmargin + em)
  let within := match es[0]? with
    | some e => if h : 1 < e.size then step e[0] e[1] else 0
    | none => 0
  let between := match es[0]?, es[1]? with
    | some a, some b => match a.back?, b[0]? with
      | some x, some y => step x y
      | _, _ => 0
    | _, _ => 0
  t s!"natbib list: \\bibsep (8pt at 10pt) stands between entries ({between - within})"
    (decide (within > 0) && between - within == Dim.pt 8)
  let (_, out2, html2) := ay "\\setlength{\\bibhang}{2em}\\setlength{\\bibsep}{0pt}"
  let es2 := bibEntryLines (bodyLines out2)
  t "natbib list: a declared \\bibhang moves the continuation lines to it"
    ((es2[0]?.map fun e => (rest e).all fun l => edge l == geom.hmargin + 2 * em).getD false)
  let between2 := match es2[0]?, es2[1]? with
    | some a, some b => match a.back?, b[0]? with
      | some x, some y => step x y
      | _, _ => 0
    | _, _ => 0
  t "natbib list: a declared \\bibsep of zero leaves the entries one line apart"
    (between2 == within)
  t "natbib list html: the author-year entries hang and part by the same token names"
    (hasStr html "<ul class=\"bibliography unmarked\" role=\"list\">" &&
     hasStr html "padding-left: var(--bibhang, 1em); text-indent: calc(-1 * var(--bibhang, 1em))" &&
     hasStr html "row-gap: var(--bibsep, 0.8em)")
  t "natbib list html: a declared \\bibhang and \\bibsep reach the page's custom properties"
    (hasStr html2 "--bibhang: 2em;" && hasStr html2 "--bibsep: 0;")
  -- numbered: ten labels, `[1]` narrower than `[10]`
  let (ndoc, nout, nhtml) :=
    build "\\usepackage[numbers]{natbib}" "e1,e2,e3,e4,e5,e6,e7,e8,e9,e10"
  let ngeom := Layout.Geom.ofPage ndoc.page
  let ns := bibEntryLines (bodyLines nout)
  let label (l : Layout.LineOut) : Option (Dim.Sp × Dim.Sp) :=
    (segStarts l).findSome? fun (x, s) => match s with
      | .run _ _ _ w _ _ _ _ _ .label => some (x, x + w)
      | _ => none
  let labels := ns.filterMap fun e => e[0]?.bind fun l => (label l).map fun (a, b) =>
    (a + l.hang, b + l.hang)
  let widest := labels.foldl (fun m (a, b) => max m (b - a)) 0
  let column := ngeom.hmargin + widest + ngeom.fontSize / 2
  let textStart (l : Layout.LineOut) : Option Dim.Sp :=
    (segStarts l).findSome? fun (x, s) => match s with
      | .run _ _ _ _ glyphs _ _ _ _ a =>
        if glyphs.isEmpty || a == .label then none else some x
      | _ => none
  t s!"natbib list: ten numbered entries ship, each with its label ({labels.size})"
    (ns.size == 10 && labels.size == 10)
  t "natbib list: the labels stand right-aligned in a column the widest label fills"
    (labels.all (·.2 == ngeom.hmargin + widest) &&
     decide ((labels[0]?.map fun (a, b) => b - a).getD widest < widest))
  t "natbib list: every line of a numbered entry starts at one text column, \\labelsep past it"
    (ns.all fun e => e.zipIdx.all fun (l, i) =>
      if i == 0 then (textStart l).map (· + l.hang) == some column else edge l == column)
  t "natbib list html: a numbered entry's label and text are the list grid's two columns"
    (hasStr nhtml "<li id=\"ref-e1\"><span class=\"bib-marker\">[1]</span> <span class=\"bib-entry\">" &&
     hasStr nhtml "grid-template-columns: subgrid;")

/-- BibTeX's own sentence case, row by row: a title as a `.bib` spells it,
and what `"t" change.case$` returned for it under bibtex 0.99d (TeX Live
2026), through a one-function style writing `title "t" change.case$` for
each of these invented values. -/
def sentenceCaseRows : List (String × String) :=
  [("The Shape of $(a, B)$ Pairs in the Folded Lattice",
    "The shape of $(a, b)$ pairs in the folded lattice"),
   ("{QRS}olver: Many-Sided Examples", "{QRS}olver: Many-sided examples"),
   ("{WXYZ}: Wandering Based Invented Estimates",
    "{WXYZ}: Wandering based invented estimates"),
   ("Folded Paper Cranes: Red, Green and Blue",
    "Folded paper cranes: Red, green and blue"),
   ("{A}BC Def Ghi", "{A}bc def ghi"),
   ("Title:No Space After", "Title:no space after"),
   ("Title: {B}raced After Colon", "Title: {B}raced after colon"),
   ("La {\\'E}cole et l{\\'E}t{\\'e}", "La {\\'e}cole et l{\\'e}t{\\'e}"),
   ("{\\'E}cole First", "{\\'E}cole first"),
   ("Study: {\\'E}cole After Colon", "Study: {\\'E}cole after colon"),
   ("A {B}ig {Deal} In {LaTeX}", "A {B}ig {Deal} in {LaTeX}"),
   ("Part One: Part Two: Part Three", "Part one: Part two: Part three"),
   ("Colon at End:", "Colon at end:"),
   ("Q {\\AA}ngstr{\\\"O}m {\\OE}uvre {\\L}ukasz", "Q {\\aa}ngstr{\\\"o}m {\\oe}uvre {\\l}ukasz"),
   ("Ends With {Brace}: And More", "Ends with {Brace}: And more"),
   ("  Leading Spaces Title", "Leading spaces title"),
   ("X {\\bf Bold Word} Y", "X {\\bf bold word} y"),
   ("Hyphen-Word And-More", "Hyphen-word and-more"),
   ("Colon: {\\'E}t{\\'E} {\\\"U}ber", "Colon: {\\'E}t{\\'e} {\\\"u}ber"),
   ("Nested {Outer {Inner} Word}: Next", "Nested {Outer {Inner} Word}: Next"),
   ("{Word}: Then {W}ord", "{Word}: Then {W}ord"),
   ("\\LaTeX{} Macro Title", "\\latex{} macro title"),
   ("Mixed \\emph{Emph Word} Here", "Mixed \\emph{Emph Word} here")]

/-- **A reference-list entry's text is set as the body's**: a title takes
BibTeX's own sentence case, row for row; a `.bib` value's TeX quote and dash
ligatures read as the body's typographic punctuation; a `$…$` span is a
formula, the spaces around it kept, an escaped dollar text; and on the page
and in the HTML the curly quotes ship and the span sets as math — where the
list once printed the dollars, the backticks and the straight quotes. -/
def bibTextChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (v, want) in sentenceCaseRows do
    t s!"bib text: sentence case of '{v}' is bibtex's '{want}'" (Bib.sentenceCase v == want)
  t "bib text: TeX's quote ligatures read as curly quotes"
    (Bib.fieldInlines "Smart ``first, then `second' last'' and `this'" ==
      #[.text "Smart “first, then ‘second’ last” and ‘this’"])
  let spans := Bib.fieldInlines "The shape of $(a, b)$ pairs"
  t "bib text: a $…$ span is a formula between its text, the spaces kept"
    (match spans with
     | #[.text "The shape of ", .formula false "(a, b)" _, .text " pairs"] => true
     | _ => false)
  t "bib text: an escaped dollar and an unclosed one stay text"
    (Bib.fieldInlines "costs \\$5, or $x" == #[.text "costs $5, or $x"])
  let bib := "@article{q1, author = {Ann Author}, title = {On {\\'E}tudes of $(a, B)$ \
    and ``Quoted'' Things}, journal = {Journal of Examples}, year = {2020}}\n"
  let (doc, _) := elabStr "\\documentclass{article}\n\\usepackage{natbib}\n\
    \\bibliographystyle{unsrtnat}\n\\begin{document}\nL1 \\citep{q1} end.\n\n\
    \\bibliography{refs}\n\\end{document}\n"
  let (doc, ds) := Bib.apply #[("refs", bib)] doc
  let fs ← mathSetOf oneFace
  let out := layoutOf fs doc
  let entry := (bibEntryLines (bodyLines out)).foldl (fun s e =>
    e.foldl (fun s l => s ++ lineText l ++ " ") s) ""
  t s!"bib text: the page ships the entry's curly quotes and no dollar ({entry})"
    (hasStr entry "“quoted” things" && !hasStr entry "$" && !hasStr entry "``" &&
      hasStr entry "On études of")
  t "bib text: the span sets in the math face on the page"
    ((bibEntryLines (bodyLines out)).any fun e => e.any fun l => l.segs.any fun s =>
      match s with
      | .run idx _ _ _ glyphs _ _ _ _ _ => fs.math == some idx && !glyphs.isEmpty
      | _ => false)
  let html := (HtmlDoc.emit {} doc).1
  t "bib text: the HTML entry carries the formula as MathML and the curly quotes"
    (hasStr html "<math" && hasStr html "“quoted” things" && ds.isEmpty)

/-- One entry per type plainnat.bst writes, and the branches its functions
take: invented people, titles and venues. -/
def plainnatBib : String :=
  "@article{art1, author = {Doe, Alex and Roe, Sam}, title = {A Grand Study of Things},\n\
    journal = {Journal of Tests}, volume = {12}, number = {3}, pages = {45--67}, year = {2024}}\n\
  @article{art2, author = {Doe, Alex}, title = {T}, year = {2024}}\n\
  @article{art3, author = {Poe, Kim}, title = {No Journal Here}, volume = {7}, pages = {1--9}, year = {2019}}\n\
  @article{art4, author = {Poe, Kim}, title = {Single Page}, journal = {Letters}, pages = {5}, year = {2018}}\n\
  @article{art5, author = {Poe, Kim}, title = {With a URL and a Note}, journal = {Letters},\n\
    year = {2017}, url = {https://example.org/a}, note = {An invented note}}\n\
  @article{art6, author = {Poe, Kim}, title = {Did It Work?}, journal = {Letters}, year = {2016}}\n\
  @book{bk1, author = {Doe, Alex}, title = {The Grand Book}, publisher = {Example Press},\n\
    edition = {Third}, year = {2020}}\n\
  @book{bk2, editor = {Roe, Sam}, title = {Edited}, year = {2019}}\n\
  @book{bk3, editor = {Roe, Sam and Lee, Jo}, title = {Edited Twice}, publisher = {Example Press}, year = {2015}}\n\
  @book{bk4, author = {Doe, Alex}, title = {A Series Book}, volume = {3}, series = {Example Series},\n\
    publisher = {Example Press}, address = {Springfield}, year = {2014}}\n\
  @inproceedings{inp1, author = {Doe, Alex}, title = {On Tests}, booktitle = {Proceedings of Examples},\n\
    pages = {1--10}, year = {2021}}\n\
  @inproceedings{inp2, author = {Doe, Alex}, title = {With Volume}, booktitle = {Advances in Examples},\n\
    volume = {12}, year = {2019}}\n\
  @inproceedings{inp3, author = {Doe, Alex}, title = {No Booktitle}, volume = {21}, number = {44},\n\
    pages = {1--30}, year = {2015}}\n\
  @inproceedings{inp4, author = {Doe, Alex}, title = {With Address}, booktitle = {Proceedings of Examples},\n\
    address = {Springfield}, organization = {Example Society}, publisher = {Example Press}, year = {2013}}\n\
  @inproceedings{inp5, author = {Doe, Alex}, title = {With Editors}, editor = {Roe, Sam},\n\
    booktitle = {Proceedings of Examples}, publisher = {Example Press}, year = {2012}}\n\
  @misc{misc1, author = {Doe, Alex}, title = {A Web Thing}, howpublished = {Online}, year = {2022},\n\
    url = {https://example.org/x}}\n\
  @misc{misc2, author = {Moss, Ann}, title = {Counting Invented Widgets}, year = {2023},\n\
    note = {An internal note, Example Group}}\n\
  @misc{misc3, title = {Only a Title}, year = {2011}}\n\
  @phdthesis{phd1, author = {Lee, Jo}, title = {A Thesis on Examples}, school = {Example University},\n\
    year = {2018}}\n\
  @mastersthesis{ms1, author = {Lee, Jo}, title = {A Masters Thesis}, school = {Example University},\n\
    year = {2010}}\n\
  @techreport{tr1, author = {Ray, Casey}, title = {A Technical Report}, institution = {Example Lab},\n\
    number = {42}, year = {2017}}\n\
  @techreport{tr2, author = {Ray, Casey}, title = {An Unnumbered Report}, institution = {Example Lab},\n\
    year = {2009}}\n\
  @unpublished{unp1, author = {Ray, Casey}, title = {An Unpublished Draft}, note = {Manuscript in preparation},\n\
    year = {2008}}\n\
  @incollection{inc1, author = {Doe, Alex}, title = {A Chapter}, booktitle = {The Collected Examples},\n\
    editor = {Roe, Sam}, publisher = {Example Press}, pages = {10--20}, year = {2007}}\n\
  @manual{man1, author = {Doe, Alex}, title = {The Manual}, organization = {Example Society},\n\
    edition = {Second}, year = {2006}}\n\
  @proceedings{pro1, editor = {Roe, Sam}, title = {Proceedings of the Example Meeting},\n\
    publisher = {Example Press}, address = {Springfield}, year = {2005}}\n\
  @booklet{bkl1, author = {Doe, Alex}, title = {A Booklet}, howpublished = {Distributed by hand}, year = {2004}}\n"

/-- The lines lualatex set for `plainnatBib` under
`\usepackage[numbers]{natbib}` and `\bibliographystyle{unsrtnat}` (TeX Live
2026: bibtex 0.99d, unsrtnat.bst from natbib 8.31b), read through
`pdftotext -layout` in TeX Gyre Termes, one entry to a line. -/
def plainnatLines : List String :=
  ["[1] Alex Doe and Sam Roe. A grand study of things. Journal of Tests, 12(3):45–67, 2024.",
   "[2] Alex Doe. T. 2024.",
   "[3] Kim Poe. No journal here. 7:1–9, 2019.",
   "[4] Kim Poe. Single page. Letters, page 5, 2018.",
   "[5] Kim Poe. With a url and a note. Letters, 2017. URL https://example.org/a. An invented note.",
   "[6] Kim Poe. Did it work? Letters, 2016.",
   "[7] Alex Doe. The Grand Book. Example Press, third edition, 2020.",
   "[8] Sam Roe, editor. Edited. 2019.",
   "[9] Sam Roe and Jo Lee, editors. Edited Twice. Example Press, 2015.",
   "[10] Alex Doe. A Series Book, volume 3 of Example Series. Example Press, Springfield, 2014.",
   "[11] Alex Doe. On tests. In Proceedings of Examples, pages 1–10, 2021.",
   "[12] Alex Doe. With volume. In Advances in Examples, volume 12, 2019.",
   "[13] Alex Doe. No booktitle. volume 21, pages 1–30, 2015.",
   "[14] Alex Doe. With address. In Proceedings of Examples, Springfield, 2013. Example Society, Example Press.",
   "[15] Alex Doe. With editors. In Sam Roe, editor, Proceedings of Examples. Example Press, 2012.",
   "[16] Alex Doe. A web thing. Online, 2022. URL https://example.org/x.",
   "[17] Ann Moss. Counting invented widgets, 2023. An internal note, Example Group.",
   "[18] Only a title, 2011.",
   "[19] Jo Lee. A Thesis on Examples. PhD thesis, Example University, 2018.",
   "[20] Jo Lee. A masters thesis. Master’s thesis, Example University, 2010.",
   "[21] Casey Ray. A technical report. Technical Report 42, Example Lab, 2017.",
   "[22] Casey Ray. An unnumbered report. Technical report, Example Lab, 2009.",
   "[23] Casey Ray. An unpublished draft. Manuscript in preparation, 2008.",
   "[24] Alex Doe. A chapter. In Sam Roe, editor, The Collected Examples, pages 10–20. Example Press, 2007.",
   "[25] Alex Doe. The Manual. Example Society, second edition, 2006.",
   "[26] Sam Roe, editor. Proceedings of the Example Meeting, Springfield, 2005. Example Press.",
   "[27] Alex Doe. A booklet. Distributed by hand, 2004."]

/-- **An entry reads as plainnat.bst writes it**, type by type: every entry of
`plainnatBib` on the shipped page is the line lualatex set for it — the
pieces and their order, the block and sentence boundaries, `add.period$`
(a title's `?` closes its own sentence), the singular `editor`, the
`page`/`pages` word, the edition's case inside a sentence, a series under
its volume, and the branches `inproceedings` and `misc` take on what the
entry holds. -/
def plainnatChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let keys := (plainnatBib.splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.startsWith "@" then ((l.splitOn "{")[1]?).bind (·.splitOn "," |>.head?) else none
  let (doc, _) := elabStr s!"\\documentclass\{article}\n\\usepackage[numbers]\{natbib}\n\
    \\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]\{geometry}\n\
    \\bibliographystyle\{unsrtnat}\n\\begin\{document}\n\
    L1 \\citep\{{String.intercalate "," keys}} end.\n\n\\bibliography\{refs}\n\\end\{document}\n"
  let (doc, ds) := Bib.apply #[("refs", plainnatBib)] doc
  let shipped := (bibEntryLines (bodyLines (layoutOf oneFace doc))).map fun e =>
    String.intercalate " " (e.toList.map lineInk)
  t s!"plainnat: every entry resolves, one per key ({shipped.size} of {keys.length})"
    (shipped.size == keys.length && ds.isEmpty)
  for want in plainnatLines, got in shipped.toList do
    t s!"plainnat: the page sets '{want}' ({got})" (got == want)

/-- Entries whose label names and year coincide, so plainnat.bst's
`forward.pass`/`reverse.pass` give them letters, one more year by the same
names, one other author, and two entries the `\nocite` rows name:
invented people and titles. -/
def natbibLabelBib : String :=
  "@article{gam2019a, author = {Gil Gamma and Hal Eta}, title = {An early invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2019b, author = {Gil Gamma and Hal Eta}, title = {A later invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2020, author = {Gil Gamma and Hal Eta}, title = {A third invented result},\n\
    journal = {Journal of Examples}, year = {2020}}\n\
  @book{iota2018, author = {Ivy Iota}, title = {An Invented Book}, publisher = {Example Press},\n\
    year = {2018}}\n\
  @misc{kap2017, author = {Kai Kappa}, title = {An invented note}, year = {2017}}\n\
  @misc{lam2016, author = {Lu Lambda}, title = {An entry no citation names}, year = {2016}}\n"

/-- The calls the letter rows set, one paragraph each (`natbibSrc`). -/
def natbibLabelCalls : List String :=
  ["\\citet{gam2019a}", "\\citet{gam2019b}", "\\citet{gam2019a,gam2019b}",
   "\\citep{gam2019a,gam2019b}", "\\citep{gam2019a,gam2019b,gam2020}", "\\citeyear{gam2019b}",
   "\\citeyearpar{gam2019a}", "\\citealp{gam2019a,gam2019b}", "\\citealt{gam2019a,gam2019b}",
   "\\citep{iota2018}"]

/-- The author-year lines lualatex set for `natbibLabelCalls` in square
brackets, and the reference list's first three entries. -/
def natbibLabelAy : List String × List String :=
  (["Gamma and Eta [2019a]", "Gamma and Eta [2019b]", "Gamma and Eta [2019a,b]",
    "[Gamma and Eta, 2019a,b]", "[Gamma and Eta, 2019a,b, 2020]", "2019b", "[2019a]",
    "Gamma and Eta, 2019a,b", "Gamma and Eta 2019a,b", "[Iota, 2018]"],
   ["Gil Gamma and Hal Eta. An early invented result. Journal of Examples, 2019a.",
    "Gil Gamma and Hal Eta. A later invented result. Journal of Examples, 2019b.",
    "Gil Gamma and Hal Eta. A third invented result. Journal of Examples, 2020."])

/-- One configuration per row — the preamble, the style, the lines lualatex
set for `natbibLabelCalls`, and the list's first three entries — measured
with TeX Live 2026 (natbib 8.31b, bibtex 0.99e) through `pdftotext`. In
numbers mode natbib defines `\natexlab` to print nothing, so the letters
reach neither the citations nor the list. -/
def natbibLabelModes : List (String × String × List String × List String) :=
  let round (xs : List String) := xs.map fun s => (s.replace "[" "(").replace "]" ")"
  [("\\usepackage{natbib}", "plainnat", natbibLabelAy.1, natbibLabelAy.2),
   ("\\usepackage{natbib}", "unsrtnat", natbibLabelAy.1, natbibLabelAy.2),
   ("\\usepackage{natbib}\\setcitestyle{authoryear,round}", "plainnat",
    round natbibLabelAy.1, natbibLabelAy.2),
   ("\\usepackage{natbib}\\bibpunct{(}{)}{;}{a}{,}{,}", "plainnat",
    round natbibLabelAy.1, natbibLabelAy.2),
   ("\\usepackage[numbers]{natbib}", "unsrtnat",
    ["Gamma and Eta [1]", "Gamma and Eta [2]", "Gamma and Eta [1, 2]", "[1, 2]", "[1, 2, 3]",
     "2019", "[2019]", "1, 2", "Gamma and Eta 1, 2", "[4]"],
    ["[1] Gil Gamma and Hal Eta. An early invented result. Journal of Examples, 2019.",
     "[2] Gil Gamma and Hal Eta. A later invented result. Journal of Examples, 2019.",
     "[3] Gil Gamma and Hal Eta. A third invented result. Journal of Examples, 2020."])]

/-- **Entries that share a label are told apart as plainnat.bst tells them**:
two entries by the same label names in the same year take the letters
plainnat's `forward.pass`/`reverse.pass` give them, in list order; the list
prints each year with its letter (FUNCTION {format.date}), and a citation
prints it too — `\citet{a,b}` sets `2019a,b`, as natbib's loop prints only
the letter for a key whose names and year repeat the last key's. On the
shipped page and in the HTML, in every mode natbib reads; in numbers mode
the letters stay out. -/
def natbibLabelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (pre, style, calls, list) in natbibLabelModes do
    let (doc, _) := elabStr (natbibSrc
      (pre ++ "\n\\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]{geometry}") style
      natbibLabelCalls)
    let (doc, ds) := Bib.apply #[("refs", natbibLabelBib)] doc
    let lines := bodyLines (layoutOf oneFace doc)
    let page := lines.map lineInk
    let entries := (bibEntryLines lines).map fun e => String.intercalate " " (e.toList.map lineInk)
    let html := htmlVisibleText (HtmlDoc.emit {} doc).1
    t s!"natbib letters {pre} + {style}: every key resolves" ds.isEmpty
    for want in calls, k in [1:calls.length + 1] do
      let line := s!"L{k} {want} end."
      t s!"natbib letters {pre} + {style}: page line {k} sets '{want}'" (page.contains line)
      t s!"natbib letters {pre} + {style}: html line {k} reads '{want}'" (hasStr html line)
    for want in list, k in [0:list.length] do
      t s!"natbib letters {pre} + {style}: entry {k + 1} reads '{want}' ({entries[k]?.getD ""})"
        (entries[k]? == some want && hasStr html want)

/-- The `\nocite` rows, one document each: the preamble, the style, the
calls, and the lines lualatex set for them and for the whole reference list
(TeX Live 2026: natbib 8.31b, bibtex 0.99e, through `pdftotext`). -/
def nociteModes : List (String × String × List String × List String × List String) :=
  let calls := ["\\citep{iota2018}", "\\nocite{kap2017}", "\\citep{gam2020}",
    "x\\nocite{kap2017} y"]
  let star := ["\\citep{iota2018}", "\\nocite{*}", "\\citep{gam2020}"]
  let iota := "Ivy Iota. An Invented Book. Example Press, 2018."
  let kap := "Kai Kappa. An invented note, 2017."
  let gam := "Gil Gamma and Hal Eta. A third invented result. Journal of Examples, 2020."
  let lam := "Lu Lambda. An entry no citation names, 2016."
  let early := "Gil Gamma and Hal Eta. An early invented result. Journal of Examples, 2019"
  let later := "Gil Gamma and Hal Eta. A later invented result. Journal of Examples, 2019"
  [("\\usepackage[numbers]{natbib}", "unsrtnat", calls,
    ["L1 [1] end.", "L2 end.", "L3 [3] end.", "L4 x y end."],
    [s!"[1] {iota}", s!"[2] {kap}", s!"[3] {gam}"]),
   ("\\usepackage{natbib}", "plainnat", calls,
    ["L1 [Iota, 2018] end.", "L2 end.", "L3 [Gamma and Eta, 2020] end.", "L4 x y end."],
    [gam, iota, kap]),
   ("\\usepackage[numbers]{natbib}", "unsrtnat", star,
    ["L1 [1] end.", "L2 end.", "L3 [4] end."],
    [s!"[1] {iota}", s!"[2] {early}.", s!"[3] {later}.", s!"[4] {gam}", s!"[5] {kap}",
     s!"[6] {lam}"]),
   ("\\usepackage{natbib}", "plainnat", star,
    ["L1 [Iota, 2018] end.", "L2 end.", "L3 [Gamma and Eta, 2020] end."],
    [s!"{early}a.", s!"{later}b.", gam, iota, kap, lam]),
   ("", "plain", ["\\cite{iota2018}", "\\nocite{kap2017}", "\\cite{gam2020}"],
    ["L1 [2] end.", "L2 end.", "L3 [1] end."],
    [s!"[1] {gam}", s!"[2] {iota}", s!"[3] {kap}"])]

/-- **`\nocite` adds its entries to the list and prints nothing**: a key it
names takes its place in first-citation order, `*` names every entry of the
`.bib` in its order there, and the command sets no ink — a space before it
swallows the spaces after it, as `\@esphack` does. On the page and in the
HTML, with natbib in both modes and without it; a key no entry answers is
named once, and a `\nocite` in a document with no bibliography is silent,
as LaTeX is. -/
def nociteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geometry := "\n\\usepackage[paperwidth=40cm,paperheight=60cm,margin=1cm]{geometry}"
  for (pre, style, calls, lines, list) in nociteModes do
    let (doc, eds) := elabStr (natbibSrc (pre ++ geometry) style calls)
    let (doc, ds) := Bib.apply #[("refs", natbibLabelBib)] doc
    let out := bodyLines (layoutOf oneFace doc)
    let page := out.map lineInk
    let entries := (bibEntryLines out).map fun e => String.intercalate " " (e.toList.map lineInk)
    let html := htmlVisibleText (HtmlDoc.emit {} doc).1
    let tag := s!"nocite {pre} + {style} {calls[1]?.getD ""}"
    t s!"{tag}: no diagnostic" (ds.isEmpty && !eds.any (·.code == "W0301"))
    for want in lines do
      t s!"{tag}: the page sets '{want}'" (page.contains want)
      t s!"{tag}: the html reads '{want}'" (hasStr html want)
    t s!"{tag}: the list is lualatex's ({entries.toList})" (entries.toList == list)
    for want in list do
      t s!"{tag}: the html list reads '{want}'" (hasStr html want)
  let (doc, _) := elabStr (natbibSrc "\\usepackage[numbers]{natbib}" "unsrtnat"
    ["\\nocite{missing2000}"])
  let (doc, ds) := Bib.apply #[("refs", natbibLabelBib)] doc
  t "nocite: a key no entry answers is named once, keyed to it, and prints nothing"
    ((ds.filter (·.code == "W0351")).map (·.subject) == #[some "missing2000"] &&
      ((bodyLines (layoutOf oneFace doc)).map lineInk).contains "L1 end.")
  let (_, eds) := elabStr
    "\\documentclass{article}\n\\begin{document}\nA \\nocite{k} b.\n\\end{document}\n"
  t "nocite: with no bibliography it is silent, as LaTeX is"
    (!eds.any fun d => d.code == "W0351" || d.code == "W0301")

/-- The `\input`-parity cases for the local `.sty` splice: the splice runs
inside the driver's own fixpoint (`Input.expandInputs`), so a
`\usepackage` inside an `\input`'ed preamble file, a `\RequirePackage`
inside a spliced `.sty`, and an `\input` inside a `.sty` all resolve —
each degraded to a misleading W0103 "not supported" while the splice was
one-shot, top-level-only, and ran after `\input` expansion. A `.sty` that
`\RequirePackage`s itself hits the `\input` nesting bound (E0501), never
loops. Fixtures live in tests/corpus/sty-parity, synthetic and invented. -/
def styParityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let run := runStyParity
  -- (a) was: W0103 "package 'venuea' is not supported" — the candidate scan
  -- saw only top-level raws and the \input wrapper hid the \usepackage.
  let (docA, dsA, splicedA) ← run "inputpre"
  t "parity a: a usepackage inside an input'ed preamble file splices — never W0103"
    (dsA.all (·.code != "W0103") && docA.page.hmargin == Dim.pt 108 &&
     splicedA.toList.map (·.1) == ["venuea.sty"])
  t "parity a: N0020 quotes the counts and names the file that asked"
    (dsA.any fun d => d.code == "N0020" &&
      (d.message.splitOn "honoured: 1, named: 0, TeX internals refused: 0").length == 2 &&
      d.span.any (·.file.endsWith "inputpre-preamble.tex"))
  -- (b) was: W0103 at venueb.sty:1 — the diagnostic named the right file,
  -- but venueb2.sty beside the document was never read.
  let (docB, dsB, splicedB) ← run "requirechain"
  t "parity b: a RequirePackage inside a spliced .sty reads the file beside the document"
    (dsB.all (·.code != "W0103") &&
     docB.page.hmargin == Dim.pt 108 && docB.page.vmargin == Dim.pt 108 &&
     splicedB.toList.map (·.1) == ["venueb.sty", "venueb2.sty"] &&
     Compat.styCounts "venueb.sty" dsB == (1, 0, 0) &&
     Compat.styCounts "venueb2.sty" dsB == (1, 0, 0))
  t "parity b: the nested read's N0020 names the .sty that asked, not the document"
    (splicedB.toList.map (·.2.1) == [none, some "venueb.sty"] &&
     dsB.any fun d => d.code == "N0020" && d.span.any (·.file == "venueb.sty"))
  -- (c) was: unexpandable by frontend order — expandInputs ran before the
  -- one-shot splice, so an \input inside a .sty could never expand.
  let (docC, dsC, _) ← run "styinput"
  t "parity c: an input inside a .sty expands on the next pass"
    (dsC.all (fun d => d.code != "W0103" && d.code != "E0502") &&
     docC.page.hmargin == Dim.pt 108)
  let (_, dsD, _) ← run "styloop"
  t "a .sty that RequirePackages itself hits the nesting bound, never loops"
    (dsD.any (·.code == "E0501"))
  -- The spliced-.sty collapse: a TeX internal the engine refuses inside a
  -- venue's style file is correct and unactionable per line, so W0301/W0357
  -- demote to notes there (listed under -v) and N0020's third count carries
  -- them. The boundary is @-names ∪ the TeX82 primitives; a venue macro is
  -- neither and stays a per-line warning; the document's own files always
  -- keep per-line warnings.
  let (_, dsI, _) ← run "internals"
  let refusedI := dsI.filter fun d =>
    d.severity == .note && (d.code == "W0301" || d.code == "W0357")
  t "sty collapse: internals refused inside a spliced .sty are notes, at .sty lines"
    (refusedI.size == 4 && refusedI.all (fun d => d.span.any (·.file == "venuei.sty")) &&
     (refusedI.filter (·.code == "W0357")).size == 1)
  t "sty collapse: a venue macro the engine cannot run stays a per-line warning"
    (dsI.any fun d => d.code == "W0301" && d.severity == .warning &&
      (d.message.splitOn "VenueSetup").length == 2)
  t "sty collapse: N0020 quotes all three counts"
    (dsI.any fun d => d.code == "N0020" &&
      (d.message.splitOn "TeX internals refused: 4").length == 2 &&
      Compat.styCounts "venuei.sty" dsI == (0, 1, 4))
  t "sty collapse: the same internals in the document's own preamble stay warnings"
    (let ds := (Elab.run "doc.tex"
      "\\begingroup\n\\v@final\n\\begin{document}\nx\n\\end{document}").2
     (ds.filter fun d => d.code == "W0301" && d.severity == .warning).size == 2 &&
     ds.all fun d => !(d.code == "W0301" && d.severity == .note))
  t "sty collapse boundary: @-names and TeX82 primitives, nothing else"
    (Compat.texInternal "z@" && Compat.texInternal "@plus" &&
     Compat.texInternal "begingroup" && Compat.texInternal "widowpenalty" &&
     !Compat.texInternal "NewEnviron" && !Compat.texInternal "thanks" &&
     !Compat.texInternal "bf" &&
     Compat.styInternal "venue.sty" "begingroup" &&
     !Compat.styInternal "main.tex" "begingroup")

/-- **`\usetheme{X}` is `\usepackage{beamerthemeX}`** — beamer defines the
whole loading family in terms of the package loader (beamerbasethemes.sty),
so a theme file beside the document is on the input path and the engine
reads it. The defect this closes: `\usetheme` rewrote straight to `\theme`,
matched four shipped bundles, and declared the theme unknown without ever
looking — one unloaded theme then cost the document its whole colour design,
because an unthemed document has no `fg`/`bg` for a `fg!50!bg` mix to reach
and no `frametitlebg` for either backend to paint.

The invariant, stated over the candidate registry (`Compat.themeAsking`) and
proved there (`Compat.themeAsking_candidates`): a declaration the engine can
refuse as unknown-by-name asks the input path first. What the fixtures add is
the end of that sentence — that the read file's colours arrive in the
palette, which is the user-visible payoff and the thing W0304 measures.

**Precedence is composition, not a contest** (PLAN 2026-09-24): the shipped
bundle installs first and the local file overrides it per role, so a role
the file declares is the file's and a role it does not keep the bundle's.
Neither side is silently dropped — the translation note names the bundle,
N0020 names the file. Fixtures in tests/corpus/sty-parity, synthetic. -/
def themeStyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let run := runStyParity
  -- was: W0319 "unknown theme 'venue'; the document is unthemed", the file
  -- beside the document never opened, and every mix over its roles W0304.
  let (docL, dsL, splicedL) ← run "themelocal"
  t "a local beamertheme<name>.sty answers \\usetheme — never W0319"
    (dsL.all (·.code != "W0319") &&
     splicedL.toList.map (·.1) == ["beamerthemevenue.sty"])
  t "the read theme's normal text lands on the fg/bg roles"
    ((docL.palette.find? "fg").isSome && (docL.palette.find? "bg").isSome &&
     docL.palette.find? "frametitlebg" == some { r := 0x3A, g := 0x5A, b := 0x7A })
  -- The W0304 consequence, measured: 39 sites failed in one private deck
  -- because no theme loaded, not because the mix was wrong.
  t "a mix over the read theme's roles resolves — the W0304 consequence"
    (dsL.all (·.code != "W0304"))
  t "N0020 names the theme file and what took"
    (dsL.any fun d => d.code == "N0020" &&
      (d.message.splitOn "beamerthemevenue.sty").length == 2 &&
      Compat.styCounts "beamerthemevenue.sty" dsL == (4, 0, 0))
  -- \usetheme[options]{name} passes its options to the file, as
  -- \usepackage[options]{} does: the option's body runs, and only then.
  let (docO, _, _) ← run "themeopt"
  t "\\usetheme[option]{name} passes the option to the file"
    ((docO.palette.find? "blocktitlebg").isSome &&
     (docL.palette.find? "blocktitlebg").isNone)
  -- Precedence: the shipped bundle is the floor, the local file the override.
  let (docS, dsS, splicedS) ← run "themeshadow"
  t "a file shadowing a shipped bundle overrides the roles it declares"
    (docS.palette.find? "frametitlebg" == some { r := 0x12, g := 0x34, b := 0x56 } &&
     splicedS.toList.map (·.1) == ["beamerthememoloch.sty"])
  t "the shipped bundle still supplies the roles the file leaves alone"
    (docS.palette.find? "alert" == some { r := 0xA5, g := 0x5A, b := 0x13 })
  t "neither side is silent: N0020 names the file and the bundle it overrides"
    (dsS.any fun d => d.code == "N0020" &&
      (d.message.splitOn "beamerthememoloch.sty").length == 2 &&
      (d.message.splitOn "moloch bundle").length == 2)
  -- **A theme's title page is a refused redefinition, not a dropped one.**
  -- The whole point of reading a theme file is that what it declares
  -- arrives; a theme that redefines the title page in beamer's own
  -- vocabulary had that redefinition refused (rightly — its arrangement is
  -- absolute placement the engine does not model) and its *declarative*
  -- appearance refused with it.
  let (_, dsT, splicedT) ← run "themetitleread"
  t "a theme's title-page redefinition is refused, never an error"
    (dsT.all (·.severity != .error) &&
     splicedT.toList.map (·.1) == ["beamerthemeplinth.sty"] &&
     dsT.any fun d => d.code == "W0361" && d.span.any (·.file.endsWith ".sty"))
  t "the refusal names what the theme's declared appearance gave the built-in"
    (dsT.any fun d => d.code == "W0361" &&
      (d.message.splitOn "styled by the redefinition's rules and spacing").length == 2)
  -- Partial absorption: a theme whose every construct the engine refuses is  -- read and yields no role. It is not an *unknown* theme, so W0319 would be
  -- a false statement; what is owed is that the shortfall is measured, and
  -- that the deck is still painted — the slides default bundle is the floor
  -- under a theme the engine could not absorb, so no mix is left half-resolved.
  let (docH, dsH, _) ← run "themehollow"
  t "a theme that yields no role is read, not called unknown"
    (dsH.all (·.code != "W0319") &&
     Compat.styCounts "beamerthemehollow.sty" dsH == (0, 2, 0) &&
     dsH.any fun d => d.code == "N0020" &&
      (d.message.splitOn "honoured: 0").length == 2)
  t "the default bundle floors a theme the engine could not absorb"
    ((docH.palette.find? "fg").isSome && dsH.all (·.code != "W0304"))
  -- The fallback stands: no file, no theme, W0319 and the unthemed path.
  t "an unknown theme with no file beside the document still warns"
    ((Elab.run "d.tex" (deck169 "\\usetheme{nosuchvenue}" "x")).2.any (·.code == "W0319"))
  -- The registry quantification, executed: the floor beside the proof
  -- `Compat.themeAsking_candidates`, which reads the same quantification
  -- through the argument layer (the kernel does not reduce through these
  -- readers, so `decide` cannot).
  -- Every slot of the family, the whole family and nothing else.
  for (cn, pre) in Compat.themeAsking do
    let pos : Pos := ⟨1, 1⟩
    t s!"\\{cn} asks the input path for {pre}<name>.sty"
      (Compat.localStyCandidates
        #[.ctrl cn pos, .group #[.word "venue" pos] pos] == #[pre ++ "venue"])
    t s!"\\{cn} passes its options through and still asks for one file"
      (Compat.localStyCandidates
        #[.ctrl cn pos, .sym '[' pos, .word "wide" pos, .sym ']' pos,
          .group #[.word "venue" pos] pos] == #[pre ++ "venue"])
  t "the family is beamer's five slots, each under its own prefix"
    (Compat.themeAsking.length == 5 &&
     (Compat.themeAsking.map (·.2)).eraseDups.length == 5 &&
     Compat.themeAsking.all fun (_, pre) => pre.startsWith "beamer")
  -- With no file to answer it, every slot is still *named* as a theme slot.
  -- The inner and outer slots used to draw W0301 "unknown command" with
  -- help offering `\define` — advice for a macro, not for a sub-theme — so
  -- the one slot in the family the engine could not read was also the one it
  -- could not describe.
  let dsF := (Elab.run "d.tex" (deck169
    "\\useinnertheme{invented}\\useoutertheme{invented}" "x")).2
  t "a theme slot with no file beside the document is named as configuration"
    (dsF.all (·.code != "W0301") &&
     (dsF.filter (·.code == "W0104")).size ≥ 2 &&
     dsF.all fun d => d.code != "W0104" ||
       ((d.help.getD "").splitOn "\\theme").length == 2)

/-- **A theme's file-name spelling resolves to what its slot spelling
resolves to.** `\usepackage{beamerthemeX}` *is* `\usetheme{X}` — the
identity `Compat.themeAsking` already encodes in the candidate-scan
direction (beamerbasethemes.sty defines the whole family through the
package loader), so the two spellings may not disagree about what a name
means. They did: a theme built on a shipped bundle wrote the bundle's file
name, which reached the CTAN dispatch and drew W0103 "not supported", so
the bundle the engine ships was refused under the one spelling a theme
inheriting it actually uses. Quantified over the registry rather than
per slot, because all five sat one keystroke apart. Fixtures in
tests/corpus/sty-parity, synthetic. -/
def themeSpellingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- was: W0103 "package 'beamerthememoloch' is not supported; skipped",
  -- and with it moloch's whole design — every role, every token, every
  -- style — for a theme whose first line inherits it.
  let (docP, dsP) := Elab.run "d.tex" (deck169 "\\usepackage{beamerthememoloch}" "x")
  t "a shipped bundle under its file name installs the bundle — never W0103"
    (dsP.all (·.code != "W0103") &&
     docP.palette.find? "alert" == some { r := 0xA5, g := 0x5A, b := 0x13 })
  -- The equivalence itself, both directions of one name.
  let (docS, _) := Elab.run "d.tex" (deck169 "\\usetheme{moloch}" "x")
  t "the file-name spelling and the slot spelling resolve to one palette"
    (docP.palette.entries == docS.palette.entries &&
     docP.styles.entries == docS.styles.entries)
  -- The alias rides the package spelling too: metropolis is moloch's
  -- former name, and a deck writing either reaches the shipped bundle.
  let (docM, _) := Elab.run "d.tex" (deck169 "\\usepackage{beamerthememetropolis}" "x")
  t "the metropolis alias resolves under the file-name spelling"
    (docM.palette.find? "alert" == some { r := 0xA5, g := 0x5A, b := 0x13 })
  -- The registry quantification: no member of the family is a CTAN
  -- support question under its file name. The four sub-theme slots have
  -- no bundle concept here, so what they owe is the slot's own named
  -- configuration warning, not a wrong claim about package support.
  for (slot, pre) in Compat.themeAsking do
    let ds := (Elab.run "d.tex" (deck169 s!"\\usepackage\{{pre}invented}" "x")).2
    t s!"{pre}<name> is answered as \\{slot}, not as an unsupported package"
      (ds.all (·.code != "W0103"))
  -- Composition holds under the file-name spelling, exactly as under the
  -- slot: the bundle floors and the local file overrides the roles it
  -- declares. `spliceUse` had no floor, so this spelling took the file
  -- alone and lost the bundle it was written on top of.
  let (docF, _, splicedF) ← runStyParity "themepkgshadow"
  t "a local file under the file-name spelling still floors on the bundle"
    (splicedF.toList.map (·.1) == ["beamerthememoloch.sty"] &&
     docF.palette.find? "frametitlebg" == some { r := 0x12, g := 0x34, b := 0x56 } &&
     docF.palette.find? "alert" == some { r := 0xA5, g := 0x5A, b := 0x13 })

/-- **A construct whose diagnostic names its own translation is translated,
not dropped.** `\setbeamercolor`'s help text named `\palette` and told the
author to perform the translation by hand — thirteen times in one theme of
the private reference corpus, every colour it declares. A help text naming a
mechanical translation is a translation the engine should perform: every fact
needed is in the source.

The element names are beamer's own (beamercolorthemedefault.sty, the default
colour theme's element list; beamercolorthememoloch.sty for the moloch
lineage's own elements), not invented here — and two rows already in the
table spelled them `block alerted title`, which beamer never writes, so they
had never fired. What the engine has no role for stays a **named** loss
carrying that element's name, because a blanket "the engine does not have
this construct" cannot be acted on. Fixtures in tests/corpus/sty-parity,
synthetic and invented. -/
def beamerColorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (docP, dsP, _) ← runStyParity "themepalette"
  let has (role : String) (r g b : UInt8) : Bool :=
    docP.palette.find? role == some { r := r, g := g, b := b }
  -- was: one blanket W0104 for all thirteen, every colour dropped.
  t "the frame title's declared pair reaches the frametitle roles"
    (has "frametitlefg" 0xFF 0xFF 0xFF && has "frametitlebg" 0x20 0x40 0x60)
  -- The two rows that never fired: beamer writes `block title alerted`,
  -- the table spelled it `block alerted title`, so a theme's alerted and
  -- example block titles were dropped by a transposition.
  t "the alerted block title reaches its roles under beamer's own spelling"
    (has "alerttitlefg" 0xFF 0xFF 0xFF && has "alerttitlebg" 0x80 0x30 0x30)
  t "the example block title reaches its roles under beamer's own spelling"
    (has "exampletitlefg" 0xFF 0xFF 0xFF && has "exampletitlebg" 0x30 0x60 0x30)
  t "the plain block title still reaches its roles"
    (has "blocktitlefg" 0xFF 0xFF 0xFF && has "blocktitlebg" 0x2C 0x4A 0x66)
  -- The moloch lineage's own elements, which a theme built on it declares.
  t "the standout frame's declared pair reaches the standout roles"
    (has "standoutfg" 0xFF 0xFF 0xFF && has "standoutbg" 0x10 0x18 0x20)
  t "the progress bar's declared pair reaches the progress roles"
    (has "progressfg" 0xC0 0x80 0x40 && has "progressbg" 0xE0 0xD0 0xC0)
  t "the title separator's declared colour reaches the separator role"
    (has "separator" 0xC0 0x80 0x40)
  t "the footline's declared colour reaches the muted role"
    (has "muted" 0x60 0x60 0x60)
  -- The named loss: an element the engine has no role for names *itself*.
  -- A blanket warning over thirteen distinct elements told the author
  -- nothing about which one it dropped.
  t "an element with no engine role is named, with its own element name"
    (dsP.any fun d => d.code == "W0104" &&
      (d.message.splitOn "sidebar").length == 2)
  t "two elements with no role are two diagnostics, not one blanket"
    (dsP.any fun d => d.code == "W0104" &&
      (d.message.splitOn "palette primary").length == 2)
  -- Composition, the half that is not covered: a key whose side has no
  -- role (`alerted text` has no background here) and beamer's inheritance
  -- (`parent=`) are named rather than silently discarded.
  t "a key whose side has no role is named with the element and the key"
    (dsP.any fun d => d.code == "W0104" &&
      (d.message.splitOn "alerted text").length == 2 &&
      (d.message.splitOn "bg").length ≥ 2)
  t "beamer's colour inheritance is named, never silently dropped"
    (dsP.any fun d => d.code == "W0104" &&
      (d.message.splitOn "parent").length == 2)
  -- Composition, the half that is covered: `fg=` alone leaves `bg`
  -- standing, because `\palette` installs per role.
  let (docC, _) := Elab.run "d.tex" (deck169
    "\\palette{frametitlebg = #010203}\\setbeamercolor{frametitle}{fg=#FFFFFF}" "x")
  t "fg= alone leaves an already-declared bg standing"
    (docC.palette.find? "frametitlebg" == some { r := 0x01, g := 0x02, b := 0x03 } &&
     docC.palette.find? "frametitlefg" == some { r := 0xFF, g := 0xFF, b := 0xFF })
  -- The artifact, not the IR: a declared frame-title ground paints a bar.
  -- Skipped only where no test face is readable; the roles above stand
  -- either way.
  if let some fontData ← findFont then
    if let .ok font := Font.parse fontData then
      let oneFace := oneFaceOf font
      let barFills (pre : String) : Nat :=
        ((layoutOf oneFace (elabStr ("\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
          "\n\\begin{document}\n\\begin{frame}{Head}\nbody text\n\\end{frame}\n" ++
          "\\end{document}")).1).pages.flatMap (·.fills)).size
      t "a theme's declared frame-title ground paints a bar on the page"
        (barFills "\\setbeamercolor{frametitle}{fg=#FFFFFF,bg=#204060}" >
         barFills "\\setbeamercolor{sidebar}{fg=#204060}")

/-- **The font half of the same finding.** `\setbeamerfont`'s W0104 help read
"declare it with `\style{element}{ font = {...} }`" and then dropped the
declaration — four sites in one theme of the private reference corpus,
every font it declares. beamer's font keys are TeX font commands already
(`size=\large`, `series=\bfseries`, `shape=`, `family=`; beamer's "Fonts"
part, beamerbasefont.sty), so the value side needs no vocabulary of its
own: the commands the author wrote become the `font` template, **in the
order they wrote them** — the engine invents no canonical order, so a
`\fontsize{..}{..}\selectfont` value composes the way its author meant.

The claim each check makes is equality with the native spelling the help
text names: the translation of a beamer font declaration *is* the `\style`
declaration, not merely something like it. Element names are beamer's own
(beamerfontthemedefault.sty's element list, plus the moloch lineage's
additions from beamerfontthememoloch.sty). Fixtures in
tests/corpus/sty-parity, synthetic and invented. -/
def beamerFontChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let styleOf (pre : String) (element : String) : Option Ir.ElementStyle :=
    (elabStr (deck169 pre "x")).1.styles.find? element
  -- was: one blanket W0104, every font dropped. The declared value is one
  -- the default bundle does not already carry, so the equality is a real
  -- comparison rather than two copies of the bundle's own frame-title font.
  t "a frame-title font declaration is the \\style declaration it names"
    (styleOf "\\setbeamerfont{frametitle}{size=\\Large,shape=\\itshape}" "frametitle" ==
     styleOf "\\style{frametitle}{ font = {\\Large\\itshape} }" "frametitle" &&
     styleOf "\\setbeamerfont{frametitle}{size=\\Large,shape=\\itshape}" "frametitle" !=
     styleOf "" "frametitle")
  t "the keys translate in the order the author wrote them"
    (styleOf "\\setbeamerfont{frametitle}{series=\\bfseries,size=\\large}" "frametitle" ==
     styleOf "\\style{frametitle}{ font = {\\bfseries\\large} }" "frametitle")
  t "a shape or family key is the same font command in the template"
    (styleOf "\\setbeamerfont{standout}{family=\\sffamily,shape=\\itshape}" "standout" ==
     styleOf "\\style{standout}{ font = {\\sffamily\\itshape} }" "standout")
  -- The furniture whose beamer name and engine element differ.
  t "beamer's section title font styles the section page"
    (styleOf "\\setbeamerfont{section title}{size=\\Large}" "sectionpage" ==
     styleOf "\\style{sectionpage}{ font = {\\Large} }" "sectionpage")
  t "beamer's title font styles the title page"
    (styleOf "\\setbeamerfont{title}{size=\\Large}" "titlepage" ==
     styleOf "\\style{titlepage}{ font = {\\Large} }" "titlepage")
  -- The author line has its own key on the same element, so the two
  -- declarations must compose rather than replace: `\style` edits keys.
  t "beamer's author font is the title page's own author-font key"
    (styleOf "\\setbeamerfont{author}{size=\\small}" "titlepage" ==
     styleOf "\\style{titlepage}{ author-font = {\\small} }" "titlepage")
  let both := "\\setbeamerfont{title}{size=\\Large}\\setbeamerfont{author}{size=\\small}"
  t "a title font and an author font compose on one element"
    (((styleOf both "titlepage").bind (·.font)).isSome &&
     ((styleOf both "titlepage").bind (·.authorFont)).isSome)
  -- The named losses, each naming itself.
  let dsOf (pre : String) : Array Diag := (elabStr (deck169 pre "x")).2
  t "a font element with no engine element is named, with its own name"
    ((dsOf "\\setbeamerfont{framesubtitle}{size=\\small}").any fun d =>
      d.code == "W0104" && (d.message.splitOn "framesubtitle").length == 2)
  -- The document's own font is not an element style: it is `\fonts`, and
  -- the help has to say so rather than offer `\style` for something
  -- `\style` cannot reach.
  t "the document font is refused toward \\fonts, not toward \\style"
    ((dsOf "\\setbeamerfont{normal text}{family=\\sffamily}").any fun d =>
      d.code == "W0104" && (d.message.splitOn "normal text").length == 2 &&
      ((d.help.getD "").splitOn "\\fonts").length == 2)
  t "beamer's font inheritance is named, never silently dropped"
    ((dsOf "\\setbeamerfont{frametitle}{parent=structure}").any fun d =>
      d.code == "W0104" && (d.message.splitOn "parent").length == 2)
  -- A key beamer does not define is named rather than pasted into a font
  -- template, where it would set as prose.
  t "an unknown font key is named, not pasted into the template"
    ((dsOf "\\setbeamerfont{frametitle}{invented=\\bfseries}").any fun d =>
      d.code == "W0104" && (d.message.splitOn "invented").length == 2)
  -- And the whole path through a spliced local theme file.
  let (docF, _, _) ← runStyParity "themepalette"
  t "a local theme file's declared fonts reach the styles through the splice"
    (((docF.styles.find? "frametitle").bind (·.font)).isSome &&
     ((docF.styles.find? "titlepage").bind (·.font)).isSome &&
     ((docF.styles.find? "titlepage").bind (·.authorFont)).isSome &&
     ((docF.styles.find? "sectionpage").bind (·.font)).isSome)

/-- **A construct whose diagnostic names its own translation is translated,
not dropped.** The general invariant behind the two beamer translations, made
executable — and worth more than either, because it is what stops the next
seventeen accumulating.

The sweep reads `Compat.beamerNative`, the help texts a skipped beamer
construct carries, and asks of each: does this help name a native engine
declaration? If it does, the construct owes either a *witness* — an input
whose rewrite records the translation naming that declaration — or a row in
`Compat.translationRefused` saying why the named declaration cannot receive
it. Both directions close: a witness-less help that names a declaration
fails, and a refusal row for a construct whose help names nothing is stale.
The hole this shuts is the one the colour and font arms sat in — a help text
reading "declare the colour with `\palette{...}`" above a warning that
dropped the colour, seventeen times in one file, each site telling the author
to perform by hand a translation every fact for which was in the source. -/
def translationOwedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The declarations a help text names, read through the shared vocabulary.
  let named (help : String) : List String :=
    Compat.nativeDeclarations.filter fun d => (help.splitOn ("\\" ++ d)).length > 1
  -- One input per construct that does translate. A construct whose help
  -- names a declaration and which has no witness here fails below, so this
  -- table cannot quietly fall behind the help texts.
  let witness : List (String × String) :=
    [("setbeamercolor", "\\setbeamercolor{frametitle}{fg=#FFFFFF,bg=#204060}"),
     ("setbeamerfont", "\\setbeamerfont{frametitle}{size=\\Large}"),
     ("setbeamertemplate", "\\setbeamertemplate{frame footer}{Footer note}")]
  -- The vocabulary has to be able to see every help text, or a help naming
  -- a declaration outside it would be skipped instead of judged.
  t "every beamer help text names a declaration the sweep can see"
    (Compat.beamerNative.all fun (_, help) => !(named help).isEmpty)
  for (construct, help) in Compat.beamerNative do
    let decls := named help
    unless decls.isEmpty do
      match Compat.translationRefused.lookup construct with
      | some reason =>
        -- A declared exception states why; an empty or token reason is the
        -- silence the registry exists to prevent.
        t s!"'\\{construct}' declines translation with a stated reason"
          (reason.length ≥ 40 && !(witness.any (·.1 == construct)))
      | none =>
        match witness.lookup construct with
        | none =>
          t s!"'\\{construct}' names a translation, so it translates or says why"
            false
        | some src =>
          -- The translation note (N0100) records what the construct became;
          -- it must name one of the declarations its own help offered.
          let ds := (elabStr (deck169 src "x")).2
          t s!"'\\{construct}' translates to a declaration its help names"
            (ds.any fun d => d.code == "N0100" &&
              decls.any fun nd => (d.message.splitOn ("\\" ++ nd)).length > 1)
  -- The other direction: a refusal row whose construct carries no help
  -- naming a declaration is stale, and would hide a construct that has
  -- since started translating.
  for (construct, _) in Compat.translationRefused do
    t s!"the refusal row for '\\{construct}' is a live row"
      ((Compat.beamerNative.lookup construct).any fun help => !(named help).isEmpty)

/-- **What the deck's first page shows when its theme redefined the title
page.** The claim is the artifact's, so it is measured on the shipped
pages: the title page is still there, and it still carries the metadata the
*document* declared — which is why a theme's arrangement is a refusable
loss and not a dropped one. A theme's title-page template restates, in
absolute placement the engine does not model, a page the engine builds from
`\title`/`\author` and styles through tokens; refusing the arrangement
costs the deck its author's layout, never the author's data.

Split from `themeStyChecks` so the palette half still runs on a host with
no usable font, where a shipped-page claim cannot be made at all. -/
def themeTitleShipChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let (docT, _, _) ← runStyParity "themetitleread"
  let outT := layoutOf oneFace docT
  let censusT := censusOf (coveredColorsOf docT) outT
  t "the title page still ships, with the deck's frame behind it"
    (outT.pages.size == 2)
  t "the shipped title page carries the document's own declared metadata"
    (pageHas censusT 0 "A Placeholder Deck" && pageHas censusT 0 "R. Placeholder")
  -- **A theme's full-bleed title page is its template, read.** The overlay
  -- shape — one picture on the page, a fill over it, nodes pinned to its
  -- points — spells the engine's own title page, so it is read as the
  -- ground and one slot per node (`TitleTemplate.read`) and ships as the
  -- template draws it: judged on the shipped page, colours included.
  let (docO, dsO, _) ← runStyParity "themeoverlay"
  let outO := layoutOf oneFace docO
  let night : Ir.Color := { r := 0x1B, g := 0x23, b := 0x30 }
  let snow : Ir.Color := { r := 0xFA, g := 0xFA, b := 0xF7 }
  let sun : Ir.Color := { r := 0xF2, g := 0xA3, b := 0x3A }
  let runInks (l : Layout.LineOut) : List Ir.Color :=
    l.segs.toList.filterMap fun s => match s with
      | .run _ c .. => some c
      | _ => none
  let titleLines := ((outO.pages[0]?.map (·.lines)).getD #[]).filter (!·.furniture)
  let lineWith (needle : String) : Option Layout.LineOut :=
    titleLines.find? fun l => hasStr (lineText l) needle
  t "an overlay title-page template is read as slots, never refused"
    (dsO.all (·.code != "W0361") && dsO.all (·.code != "W0110") &&
     ((docO.styles.find? "titlepage").map (·.slots.size)) == some 3)
  t "the theme's fonts a read template selects are honoured, not skipped"
    (dsO.all fun d => !(d.code == "W0104" &&
      d.subject.any (·.startsWith "beamer:setbeamerfont:quill")))
  t "the template's fill is the title page's own ground, over the whole page"
    ((outO.pages[0]?.bind (·.fills[0]?)).any fun f =>
      f.color == night && f.x == 0 && f.y == 0)
  t "the title ships in its node's ink, and the pair clears 4.5:1"
    (((lineWith "Placeholder Deck").any fun l =>
        !(runInks l).isEmpty && (runInks l).all (· == snow)) &&
     Contrast.contrastMilli snow night ≥ Contrast.aaText)
  t "the author ships in its node's ink, legible on the ground"
    (((lineWith "R. Placeholder").any fun l =>
        !(runInks l).isEmpty && (runInks l).all (· == sun)) &&
     Contrast.contrastMilli sun night ≥ Contrast.aaText)
  t "a node of literal content ships its content in its own corner"
    ((lineWith "Invented Series").any fun l => l.x > docO.page.width / 2)
  t "the stylesheet translates each slot by its anchor's shares"
    (let css := HtmlDoc.titleSlotCss docO
     (css.splitOn "translate(-0%, -50%)").length == 2 &&
     (css.splitOn "translate(-0%, -100%)").length == 2 &&
     (css.splitOn "translate(-100%, -0%)").length == 2)
  -- Any other shape stays rule (b)'s: refused by name, the built-in standing.
  let (_, dsR) := elabStr (deck169
    "\\setbeamertemplate{title page}{\\centering\\inserttitle\\par\\null}\\title{T}"
    "\\titlepage")
  t "a title-page template of another shape keeps its refusal"
    (dsR.any (·.code == "W0361"))
  -- The withdrawal's premise, falsifiable: a theme font the read template
  -- selects reaches the page. Two builds differing only by that font's
  -- declared size ship different title sizes, so the skip it withdraws was
  -- never the only thing standing between the declaration and the artifact.
  let fontProbe (size : String) : Option Dim.Sp :=
    let pre := "\\setbeamerfont{probe heading}{size=" ++ size ++ "}" ++
      "\\setbeamertemplate{title page}{\\begin{tikzpicture}[remember picture,overlay]" ++
      "\\node[anchor=west, font=\\usebeamerfont{probe heading}] at (current page.west) " ++
      "{\\inserttitle};\\end{tikzpicture}}\\title{Probe}"
    let (doc, _) := elabStr (deck169 pre "\\titlepage")
    ((layoutOf oneFace doc).pages[0]?.bind fun p =>
      (p.lines.filter (!·.furniture))[0]?).map fun l =>
        l.segs.foldl (fun w s => match s with
          | .run _ _ _ wd .. => w + wd
          | _ => w) 0
  t "a theme font a read template selects reaches the shipped title"
    (match fontProbe "\\Large", fontProbe "\\small" with
     | some a, some b => a > b
     | _, _ => false)

mutual

/-- The text the title slide shows in the typed HTML tree: every text node
under the `section` whose class names the title page, in tree order. -/
def titleSlideTextList (inSlide : Bool) (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => titleSlideTextList inSlide (titleSlideTextOne inSlide acc n) rest

def titleSlideTextOne (inSlide : Bool) (acc : String) : Html.Node → String
  | .text s => if inSlide then acc.append s else acc
  | .elem tag attrs kids =>
    let here := inSlide || (tag == "section" &&
      attrs.any fun (k, v) => k == "class" && hasStr v "title-page")
    titleSlideTextList here acc kids.toList
  | .style _ => acc
  | .script _ _ => acc

end

mutual

/-- Every `style` attribute under the title slide's `section`, in tree
order: the inline declarations its runs carry. -/
def titleSlideStylesList (inSlide : Bool) (acc : Array String) :
    List Html.Node → Array String
  | [] => acc
  | n :: rest => titleSlideStylesList inSlide (titleSlideStylesOne inSlide acc n) rest

def titleSlideStylesOne (inSlide : Bool) (acc : Array String) : Html.Node → Array String
  | .elem tag attrs kids =>
    let here := inSlide || (tag == "section" &&
      attrs.any fun (k, v) => k == "class" && hasStr v "title-page")
    let acc := if here then
        attrs.foldl (fun a (k, v) => if k == "style" then a.push v else a) acc
      else acc
    titleSlideStylesList here acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

end

/-- **No datum a template node inserts is dropped.** A node the reader
cannot pin, or cannot wholly read, still ships what it sets: pinned where
its pin reads, in the title page's flow where it does not, and the loss is
one diagnostic with a subject. Each probe is one construct in an invented
overlay template; the page is read off `Layout.Out` (through the census)
and the title slide off the typed HTML tree, never the IR dump. -/
def titleSlotShipChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let overlay (titleNode authorNode : String) : String :=
    "\\definecolor{probeNight}{HTML}{202833}\\definecolor{probeLeaf}{HTML}{9AD1A0}" ++
    "\\setbeamertemplate{title page}{\\begin{tikzpicture}[remember picture,overlay]" ++
    "\\fill[probeNight] (current page.south west) rectangle (current page.north east);" ++
    titleNode ++ authorNode ++ "\\end{tikzpicture}}" ++
    "\\title{Probe Heading}\\author{Pat Example}\\institute{example.org}"
  let pinnedTitle (body : String) : String :=
    "\\node[anchor=west, text=probeLeaf] at ([xshift=2cm]current page.west) {" ++ body ++ "};"
  let pinnedAuthor (body : String) : String :=
    "\\node[anchor=south west, text=probeLeaf] at ([xshift=2cm,yshift=1cm]current page.south west) {" ++
      body ++ "};"
  let ship (pre : String) : Ir.Doc × Array Diag × Array CensusPage × String :=
    let (doc, ds) := elabStr (deck169 pre "\\titlepage")
    let (_, body, _) := HtmlDoc.emitTree {} doc
    (doc, ds, censusOf (coveredColorsOf doc) (layoutOf oneFace doc),
     titleSlideTextList false "" body.toList)
  let slotOf (doc : Ir.Doc) (d : String) : Option Ir.TitleSlot :=
    ((doc.styles.find? "titlepage").getD {}).slots.find? fun sl =>
      sl.datum.map (·.name) == some d
  let key (x : String) : Option String := some ("beamer:setbeamertemplate:title page:" ++ x)
  let shows (c : Array CensusPage) (html needle : String) : Bool :=
    pageHas c 0 needle && hasStr html needle
  -- The control: the reader's own shape, read whole.
  let (docK, dsK, cK, hK) := ship (overlay (pinnedTitle "\\inserttitle")
    (pinnedAuthor "\\insertauthor"))
  t "control: a template read whole ships its title pinned, with no loss named"
    (shows cK hK "Probe Heading" && (slotOf docK "title").any (·.place.isSome) &&
     dsK.all fun d => d.code != "W0110" && d.code != "W0363" && d.code != "W0361")
  -- `{\bfseries\inserttitle}`: a declaration beside the datum is the
  -- node's font, as `font=` is.
  let (docB, dsB, cB, hB) := ship (overlay (pinnedTitle "\\bfseries\\inserttitle")
    (pinnedAuthor "\\insertauthor"))
  t "a font declaration beside the title is read: the title ships pinned, in bold"
    (shows cB hB "Probe Heading" && dsB.all (fun d => d.code != "W0110" && d.code != "W0363") &&
     (slotOf docB "title").any fun sl => sl.place.isSome &&
       sl.font.any fun f => f.any fun i => i == .styled .bold #[])
  -- `{\usebeamercolor[fg]{title}\inserttitle}`: the colour selection is
  -- named and not read; the title ships where it is pinned.
  let (docC, dsC, cC, hC) := ship (overlay
    (pinnedTitle "\\usebeamercolor[fg]{title}\\inserttitle") (pinnedAuthor "\\insertauthor"))
  t "an unread colour selection beside the title: the title ships pinned"
    (shows cC hC "Probe Heading" && (slotOf docC "title").any (·.place.isSome))
  t "the unread colour selection is one named loss with its subject"
    ((dsC.filter fun d => d.code == "W0104" && d.subject == key "\\usebeamercolor").size == 1 &&
     dsC.all fun d => d.code != "W0110" && d.code != "W0363")
  -- `at (0,0)`: a node not pinned to the page sets its datum unpinned.
  let (docU, dsU, cU, hU) := ship (overlay "\\node[anchor=west] at (0,0) {\\inserttitle};"
    (pinnedAuthor "\\insertauthor"))
  t "a title node not pinned to the page still ships the title, in the page's flow"
    (shows cU hU "Probe Heading" && (slotOf docU "title").any (·.place.isNone) &&
     shows cU hU "Pat Example")
  t "the unpinned title node is one named loss with its subject"
    ((dsU.filter (·.code == "W0363")).size == 1 &&
     dsU.any fun d => d.code == "W0363" && d.subject == key "title")
  -- `{\insertauthor\\\insertinstitute}`: two data in one node both ship,
  -- pinned where the node is, each on its own line.
  let (docT, dsT, cT, hT) := ship (overlay (pinnedTitle "\\inserttitle")
    (pinnedAuthor "\\insertauthor\\\\\\insertinstitute"))
  t "a node setting two data ships both, pinned, on the node's two lines"
    (shows cT hT "Pat Example" && shows cT hT "example.org" && shows cT hT "Probe Heading" &&
     (slotOf docT "author").any (fun sl => sl.place.isSome && sl.more == #[(true, .institute)]) &&
     (lineYOf cT 0 "Pat Example").any fun y => (lineYOf cT 0 "example.org").any (y < ·))
  t "a node setting two data in one style is read whole: no loss is named"
    (dsT.all fun d => d.code != "W0363" && d.code != "W0110")
  -- Data the node styles apart are no one slot: each ships unpinned, and
  -- that is one named loss with its subject.
  let (_, dsA, cA, hA) := ship (overlay (pinnedTitle "\\inserttitle")
    (pinnedAuthor "\\insertauthor\\\\\\small\\insertinstitute"))
  t "two data styled apart in one node both ship"
    (shows cA hA "Pat Example" && shows cA hA "example.org")
  t "two data styled apart are one named loss with its subject"
    ((dsA.filter (·.code == "W0363")).size == 1 &&
     dsA.any fun d => d.code == "W0363" && d.subject == key "author+institute")
  -- A datum beside literal text has no slot to stand in: the template is
  -- not read, the built-in title page sets every datum, and that is one
  -- named loss with its subject.
  let (_, dsM, cM, hM) := ship (overlay (pinnedTitle "\\inserttitle")
    (pinnedAuthor "By \\insertauthor"))
  t "a datum beside literal text keeps the built-in title page, which sets every datum"
    (shows cM hM "Pat Example" && shows cM hM "Probe Heading" && shows cM hM "example.org")
  t "a datum beside literal text is one named loss with its subject"
    ((dsM.filter (·.code == "W0363")).size == 1 &&
     dsM.any fun d => d.code == "W0363" && d.subject == key "author")
  -- **A slot ink the title page's ground fails is realized lighter, and
  -- both artifacts ship the realized value** — N0022's claim, read off
  -- each artifact: the PDF run's colour and the ground painted under it
  -- off `Layout.Out`, the HTML token the title slide resolves the run's
  -- `var(--role)` through off the stylesheet the typed tree ships.
  let night : Ir.Color := { r := 0x20, g := 0x28, b := 0x33 }
  let rust : Ir.Color := { r := 0xC8, g := 0x68, b := 0x3A }
  let preR := "\\definecolor{probeNight}{HTML}{202833}\\definecolor{probeRust}{HTML}{C8683A}" ++
    "\\definecolor{probeSnow}{HTML}{F4F4F0}" ++
    "\\setbeamertemplate{title page}{\\begin{tikzpicture}[remember picture,overlay]" ++
    "\\fill[probeNight] (current page.south west) rectangle (current page.north east);" ++
    "\\node[anchor=west, text=probeSnow] at ([xshift=2cm]current page.west) {\\inserttitle};" ++
    "\\node[anchor=south west, text=probeRust] at ([xshift=2cm,yshift=1cm]current page.south west)" ++
    " {\\insertauthor};\\end{tikzpicture}}\\title{Probe Heading}\\author{Pat Example}"
  let (docR, dsR) := elabStr (deck169 preR "\\titlepage")
  let outR := layoutOf oneFace docR
  let authorInk : Option Ir.Color := (outR.pages[0]?.bind fun p =>
    p.lines.find? fun l => hasStr (lineText l) "Pat Example").bind fun l =>
      l.segs.findSome? fun s => match s with
        | .run _ c .. => some c
        | _ => none
  let ground : Option Ir.Color := (outR.pages[0]?.bind (·.fills[0]?)).map (·.color)
  t "the probe's author ink fails its ground as declared, and the loss is noted"
    (Contrast.contrastMilli rust night < Contrast.aaText && dsR.any (·.code == "N0022"))
  t "the PDF ships the realized author ink, legible on the ground painted under it"
    (match authorInk, ground with
     | some c, some g => g == night && c != rust && Contrast.contrastMilli c g ≥ Contrast.aaText
     | _, _ => false)
  let (headR, bodyR, _) := HtmlDoc.emitTree {} docR
  let cssR := treeCssList (treeCssList "" headR.toList) bodyR.toList
  t "the HTML title slide resolves the author's token to the ink the PDF ships"
    ((titleSlideStylesList false #[] bodyR.toList).any (hasStr · "var(--probeRust") &&
     (match authorInk with
      | some c => (cssRulesOf cssR "section.slide.title-page").any
          (hasStr · s!"--probeRust: {HtmlDoc.cssColor c};")
      | none => false))
  -- **Each slot's stylesheet rule pins it where TikZ does**, read off the
  -- stylesheet the typed tree ships for the five-slot fixture. Known
  -- answers spelled from its declarations: `at` names the page point (a
  -- share of the stage per axis: west 0/50, north west 0/0, south east
  -- 100/100 …), `anchor` the box point (the translate), each shift em of
  -- the body. And the title's text edge — the shift plus the inner sep —
  -- agrees with the edge the PDF page sets it at.
  let tgDoc := (← elabFixture "titleground" (← IO.FS.readFile "tests/corpus/titleground.tex")).1
  let (tgHead, tgBody, _) := HtmlDoc.emitTree {} tgDoc
  let tgCss := treeCssList (treeCssList "" tgHead.toList) tgBody.toList
  let em := tgDoc.page.fontSize
  -- One declaration's value: `left: calc(0% + 4.123em)` read as the
  -- percentage and the shift in sp; `padding: 0.333em` as the shift alone.
  let field (decls key : String) : Option String :=
    (decls.splitOn (key ++ ": "))[1]?.map fun rest => ((rest.splitOn ";")[0]?).getD ""
  let emSp (s : String) : Option Dim.Sp :=
    (Decl.parseDecimal ((s.trimAscii.toString.dropEnd 2).toString)).map fun (m, sc) =>
      m * em / (sc : Int)
  let calcOf (v : String) : Option (String × Dim.Sp) :=
    match ((v.drop 5).toString.dropEnd 1).toString.splitOn "% + " with
    | [pct, shift] => (emSp shift).map (pct, ·)
    | _ => none
  let near (a b : Dim.Sp) : Bool := (a - b).natAbs ≤ (em / 1000).natAbs + 1
  let want : List (Nat × String × Dim.Sp × String × Dim.Sp × String) :=
    [(0, "0", Dim.mm 16, "50", Dim.mm 4, "translate(-0%, -50%)"),
     (1, "0", Dim.mm 16, "0", Dim.mm 14, "translate(-0%, -0%)"),
     (2, "0", Dim.mm 16, "100", -Dim.mm 14, "translate(-0%, -100%)"),
     (3, "100", -Dim.mm 16, "100", -Dim.mm 14, "translate(-100%, -100%)"),
     (4, "100", -Dim.mm 16, "0", Dim.mm 14, "translate(-100%, -0%)")]
  for (i, lp, dx, tp, dy, tr) in want do
    let decls := cssRuleOf tgCss s!"section.slide.title-page > .u-titlepage-slot-{i}"
    t s!"slot {i}: its left is the page point's horizontal share plus its x shift"
      (((decls.bind (field · "left")).bind calcOf).any fun (p, s) => p == lp && near s dx)
    t s!"slot {i}: its top is the page point's vertical share plus its y shift"
      (((decls.bind (field · "top")).bind calcOf).any fun (p, s) => p == tp && near s dy)
    t s!"slot {i}: its box is moved by its anchor's shares"
      ((decls.bind (field · "transform")).any (· == tr))
  let tgPdfX := lineXOf (censusOf (coveredColorsOf tgDoc) (layoutOf oneFace tgDoc)) 0
    "A Placeholder Deck"
  let tgRule := cssRuleOf tgCss "section.slide.title-page > .u-titlepage-slot-0"
  t "the title's text edge is one place in both artifacts"
    (match tgPdfX, ((tgRule.bind (field · "left")).bind calcOf),
        ((tgRule.bind (field · "padding")).bind emSp) with
     | some x, some ("0", s), some pad => near (s + pad) x
     | _, _, _ => false)

/-- E0502/E0503 name the file and line of the reference that failed. The
invariant: a missing-file diagnostic points at the file containing the
reference, never at a directory — `--> .:5:1` sent the reader to a
directory's line 5. Fixtures in tests/corpus/input-missing, synthetic. -/
def missingFileSpanChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let run (name : String) : IO (Array Diag) := do
    let path := s!"tests/corpus/input-missing/{name}.tex"
    let src ← IO.FS.readFile path
    let (raws, _) := Parse.parse path (Lex.lex path src).1
    let (_, ds, _) ← Input.expandInputs path raws
    return ds
  let dsM ← run "m"
  t "E0502 renders the including file and line, never its directory"
    (dsM.any fun d => d.code == "E0502" &&
      ((Render.human false d).splitOn
        "--> tests/corpus/input-missing/m.tex:4:1").length == 2)
  let dsN ← run "outer"
  t "a nested input's E0502 names the input file it sits in"
    (dsN.any fun d => d.code == "E0502" &&
      d.span.any fun sp => sp.file.endsWith "inner.tex" && sp.pos == ⟨2, 1⟩)
  -- E0503's half: the marker's span is delivered beside the Doc
  -- (`Elab.ReqSpans`), so the driver's missing-file diagnostic can name
  -- the `\bibliography` line — and the Doc itself stays span-free (the
  -- compat conservation oracle compares Docs across spellings).
  let srcB := dvDoc "" "x \\cite{k}\n\\bibliography{refs}"
  let (_, _, reqsB) := Elab.runRawsSpanned "t" (Parse.parse "t" (Lex.lex "t" srcB).1).1
  t "the bibliography marker records its span for E0503"
    (reqsB.bib.any fun (s, sp) => s == "refs" && sp.file == "t" && sp.pos.col == 1)

/-- The no-bibliography citation judge. The invariant: no '?' ships
silent — a `\cite` in a document that declares no `\bibliography` is
unresolvable, `Bib.apply` never runs, and no file is missing, so the
judge in elabDoc is the only voice left. W0351 fires at the `\cite`, once
per distinct key; a declared bibliography hands the judging to
resolution (its own W0351 per missing key, the m2 shape). -/
def citeNoBibChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ds := dvE (dvDoc "" "Hello \\cite{nokey}.")
  t "a cite with no bibliography fires W0351 at the cite"
    ((ds.filter (·.code == "W0351")).size == 1 &&
     ds.any fun d => d.code == "W0351" && d.span == some ⟨"t", ⟨3, 7⟩⟩)
  t "one diagnostic per distinct key, at its first cite"
    (((dvE (dvDoc "" "\\cite{a} and \\cite{a,b} again \\cite{b}")).filter
      (·.code == "W0351")).size == 2)
  t "a declared bibliography silences the no-bibliography judge"
    ((dvE (dvDoc "" "x \\cite{k}\n\\bibliography{refs}")).all (·.code != "W0351"))
  t "a document with no citations stays silent"
    ((dvE (dvDoc "" "plain text")).all (·.code != "W0351"))

/-- Elaboration terminates — checked under a wall clock, because the
guarantee once lived only as prose and broke silently: the body-`\define`
arm of cffb141 (2026-09-19 01:56) re-exposed a command being expanded to
its own body, and this four-line document looped forever while every
golden stayed green. The bound is generous (the document elaborates in
milliseconds; the failure mode is forever); on a regression the test
fails loudly and exits rather than hanging the suite. The invariant that
forbids the loop is `bindCmd_monotone` in Elab.lean. -/
def terminationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let name := "a \\define inside its own expansion terminates (cffb141 regression)"
  let doc := "\\begin{document}\n\\define \\x {\\block{\\define \\y {z} \\x}}\n\n\\x\n\\end{document}"
  -- The elaboration runs on its own task so the deadline is enforceable;
  -- `lazyPure` defers the pure call into the task, where `asTask (pure e)`
  -- would evaluate `e` on this thread and hang here.
  let task ← IO.asTask (IO.lazyPure fun _ => (Elab.run "t" doc).2.map (·.code))
  let deadline := (← IO.monoMsNow) + 30000
  let mut finished := false
  while !finished && (← IO.monoMsNow) < deadline do
    if (← IO.hasFinished task) then
      finished := true
    else
      IO.sleep 20
  unless finished do
    failures ref name
    IO.eprintln s!"FAIL {name}: still elaborating after 30 s; killing the suite"
    IO.Process.exit 1
  -- Terminated — and with the loop refused honestly: the unbound `\x` in
  -- the expansion is the named W0301, never a silent success.
  match task.get with
  | .ok codes => check ref name (codes.contains "W0301")
  | .error e =>
    failures ref name
    IO.eprintln s!"FAIL {name}: {e}"

/-- A source elaborated the way the driver builds a data document: lex,
parse, expand the data vocabulary (`sources` are the fulfilled file
reads; inline records need none), then elaborate — `Main.resolveData`'s
pipeline with the effects already in hand. -/
def elabData (sources : Array (String × String)) (src : String) :
    Ir.Doc × Array Diag :=
  let (toks, lexDs) := Lex.lex "t" src
  let (raws, parseDs) := Parse.parse "t" toks
  let (raws, dataDs) := Data.expandData "t" sources raws
  Elab.runRaws "t" raws (lexDs ++ parseDs ++ dataDs)

/-- Elaborated equality of a data document against the document with its
data inlined by hand — `expandData_covers` run as an oracle over whole
documents, blocks and inlines both, diagnostics included. -/
def dataCovers (sources : Array (String × String)) (dataSrc handSrc : String) :
    Bool :=
  let (d1, ds1) := elabData sources dataSrc
  let (d2, ds2) := elabStr handSrc
  -- the claim is elaboration equality itself, not a page fact
  Ir.dump d1 #[] == Ir.dump d2 #[] -- ir tier: hand-inlining equality is an elaboration claim
    && ds1.map (·.code) == ds2.map (·.code)

def dataChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bib := "@job{a, role = {Alpha~\\emph{Role} 10\\%}, start = 2020}\n" ++
    "@job{b, role = {Beta Role}, start = 2021, end = 2024, " ++
    "achievements = {\\item One \\item Two}}"
  let srcs := #[("records", bib)]
  let pre := "\\data{ file = \"records\" }\n"
  t "data: \\val splices the field's own TeX — \\emph, ~, \\% are content"
    (dataCovers srcs
      (pre ++ "\\begin{foreach}{j}{job}[; ]\\val{j.role}\\end{foreach}")
      "Alpha~\\emph{Role} 10\\%; Beta Role")
  t "data: \\ifdata branches on presence, else from [...]"
    (dataCovers srcs
      (pre ++ "\\begin{foreach}{j}{job}[ ]\\val{j.start}--\\ifdata{j.end}{\\val{j.end}}[present]\\end{foreach}")
      "2020--present 2021--2024")
  t "data: \\item inside a value is the list the document wraps"
    (dataCovers srcs
      (pre ++ "\\begin{foreach}{j}{job}\\ifdata{j.achievements}{\\begin{itemize}\\val{j.achievements}\\end{itemize}}\\end{foreach}")
      "\\begin{itemize}\\item One \\item Two\\end{itemize}")
  t "data: inline \\data{ @kind{...} } is the same grammar through the other door"
    (dataCovers #[]
      "\\data{ @link{g, url = {example.org}} }\\begin{foreach}{j}{link}\\val{j.url}\\end{foreach}"
      "example.org")
  t "data: an inner foreach variable shadows the outer, innermost first"
    (dataCovers srcs
      (pre ++ "\\data{ @link{g, url = {example.org}} }\n" ++
        "\\begin{foreach}{j}{job}[; ]\\begin{foreach}{j}{link}\\val{j.url}\\end{foreach}\\end{foreach}")
      "example.org; example.org")
  let dataWarns (s : String) : Array Diag :=
    (elabData srcs (pre ++ s)).2.filter (·.severity == .warning)
  t "data: an absent field is W0364 naming the entry's own fields"
    ((dataWarns "\\begin{foreach}{j}{job}\\val{j.end}\\end{foreach}").any fun d =>
      d.code == "W0364" && hasStr d.message "job[1]" &&
        hasStr d.message "role, start")
  t "data: \\ifdata on the same absent field stays silent"
    ((dataWarns "\\begin{foreach}{j}{job}\\ifdata{j.end}{x}\\end{foreach}").isEmpty)
  t "data: an unbound variable is W0364"
    ((dataWarns "\\val{k.role}").any fun d =>
      d.code == "W0364" && hasStr d.message "'k' is not bound")
  t "data: a kind with no records is W0364 naming what the data carries"
    ((dataWarns "\\begin{foreach}{j}{trip}\\val{j.role}\\end{foreach}").any fun d =>
      d.code == "W0364" && hasStr d.message "@job")
  t "data: a forward reference is W0364 — data precedes use"
    (((elabData #[] ("\\begin{foreach}{j}{job}\\val{j.role}\\end{foreach}" ++
        "\\data{ @job{a, role = {X}} }")).2.filter (·.severity == .warning)).any fun d =>
      d.code == "W0364" && hasStr d.message "no data records are declared")
  t "data: a malformed inline entry is W0352 and the rest is kept"
    (let (doc, ds) := elabData #[]
      ("\\data{ @job{bad, role = ?} @job{ok, role = {Kept Role}} }" ++
        "\\begin{foreach}{j}{job}\\val{j.role}\\end{foreach}")
     ds.any (·.code == "W0352") &&
       hasStr (Ir.dump doc #[]) "Kept Role") -- ir tier: what survives is an elaboration fact
  let plain := (Parse.parse "t" (Lex.lex "t" "\\val{j.x} and \\begin{foreach}{j}{job}\\end{foreach}").1).1
  t "data: no \\data, no vocabulary — the document passes through untouched"
    (Data.expandData "t" #[] plain == (plain, #[]))

/-- Footnotes at the surface: `\footnote` is native (never W0301), its
numbering is the gapless counter with `[num]` overriding unstepped, and
the refusals around it are the named codes, each firing exactly where its
loss stands and staying silent elsewhere. -/
def footnoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The invariant whose absence was the defect: a \footnote is a modelled
  -- node, never the W0301 keep-as-text fallback.
  t "footnote elaborates without W0301"
    ((dvE (dvDoc "" "a\\footnote{note body}")).all (·.code != "W0301"))
  t "footnote body lands in a footnote node with number 1"
    ((elabStr (dvDoc "" "a\\footnote{note body}")).1.body ==
      #[.para #[.text "a", .footnote (some 1) #[.text "note body"]]])
  -- Numbering: document-wide, gapless, an override unstepped
  -- (`Ir.footnote_numbers_gapless` is the theorem; this is its wiring).
  t "footnote numbers are 1, 7, 2 under an unstepping override"
    (let doc := (elabStr (dvDoc ""
      "a\\footnote{x} b\\footnote[7]{y} c\\footnote{z}")).1
     (Ir.footnotesOf doc.body).map (·.1) == #[some 1, some 7, some 2])
  t "footnotesOf reads the notes in flow order with their bodies"
    (let doc := (elabStr (dvDoc "" "a\\footnote{x} b\\footnote{y}")).1
     (Ir.footnotesOf doc.body).map (fun n => Ir.plainText n.2) == #["x", "y"])
  -- The note body is document text: the census reads through the wrapper.
  t "the note body survives the text census"
    (let doc := (elabStr (dvDoc "" "a\\footnote{surviving words}")).1
     (Ir.blocksText doc.body).splitOn "surviving words" |>.length == 2)
  t "footnote with no group is E0304"
    ((dvE (dvDoc "" "a\\footnote and on")).any (·.code == "E0304"))
  -- W0371: a paragraph break inside a note is a space, named once.
  t "a paragraph break inside a footnote fires W0371"
    ((dvE (dvDoc "" "a\\footnote{first\n\nsecond}")).any (·.code == "W0371"))
  t "the broken note keeps both halves as one note"
    (let doc := (elabStr (dvDoc "" "a\\footnote{first\n\nsecond}")).1
     (Ir.footnotesOf doc.body).map (fun n => Ir.plainText n.2) == #["first second"])
  t "a one-paragraph footnote stays silent on W0371"
    ((dvE (dvDoc "" "a\\footnote{plain}")).all (·.code != "W0371"))
  -- W0370: the unpaired pair, named as pending, never "unknown".
  t "footnotemark fires W0370, not W0301"
    (let ds := dvE (dvDoc "" "a claim\\footnotemark stands")
     ds.any (·.code == "W0370") && ds.all (·.code != "W0301"))
  t "footnotetext fires W0370 and keeps its text"
    (let (doc, ds) := elabStr (dvDoc "" "a\\footnotetext{kept words}")
     ds.any (·.code == "W0370") &&
       ((Ir.blocksText doc.body).splitOn "kept words").length == 2)
  t "a plain footnote stays silent on W0370"
    ((dvE (dvDoc "" "a\\footnote{x}")).all (·.code != "W0370"))
  -- W0373: \thanks kept inline in the title block, named.
  t "thanks in the title fires W0373 and keeps its text inline"
    (let (doc, ds) := elabStr (dvDoc
      "\\title{A Panel\\thanks{Synthetic Grant 1}}\n" "x\n\\maketitle")
     ds.any (·.code == "W0373") &&
       ((Ir.blocksText doc.body).splitOn "Synthetic Grant 1").length == 2)
  t "a title without thanks stays silent on W0373"
    ((dvE (dvDoc "\\title{A Panel}\n" "x\n\\maketitle")).all (·.code != "W0373"))
  -- W0374: a card face has no note apparatus; the text stays inline.
  t "a footnote on a card fires W0374 and keeps its text inline"
    (let (doc, ds) := elabStr ("\\documentclass{card}\n\\begin{document}\n" ++
      "x\\footnote{an aside}\n\\end{document}")
     ds.any (·.code == "W0374") &&
       (Ir.footnotesOf doc.body).isEmpty &&
       ((Ir.blocksText doc.body).splitOn "an aside").length == 2)
  t "a footnote in an article stays silent on W0374"
    ((dvE (dvDoc "" "x\\footnote{y}")).all (·.code != "W0374"))

/-- The TikZ boundary's elaboration half: a picture outside the rendered
subset becomes a request on the IR (`Ir.pictureRefs`, the `bibRefs` shape)
and an image node the driver fulfils — by default: the boundary tool is
part of the build environment exactly as fonts are, and the driver alone
decides fulfilment. `\pictures{ tool = ... }` pins a tool; `tool = none`
is the declared refusal, keeping the subset's named diagnostics with no
door warning (the declaration is the acceptance; W0379 is the driver's,
for a stated request no available tool can fulfil). The wrapped standalone
carries the preamble's closed list and projects the document's design —
the palette roles the body mentions, the declared font roles
(`Ir.pictureRefs_design_projects`); the request is a pure function of the
document (a pure function's determinism, definitional and so nobody's
theorem; checked here as bytewise agreement across two runs — and
`boundary_request_env_free`: the tool choice never shapes it, checked here
as whole-`Doc` agreement between the pinned and the undeclared
spellings). -/
def boundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pic := "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}"
  let sets := "\\usetikzlibrary{arrows}\n" ++
    "\\tikzset{zz/.style={}}\n\\usepackage{pgfplots}\n"
  let (doc, ds) := elabStr (dvDoc sets pic)
  t "the door is open by default: the default tool rides the IR"
    (doc.pictureTool == some "lualatex")
  t "a refused picture becomes one request with no declaration"
    (doc.pictureSrcs.size == 1 && (Ir.pictureRefs doc).size == 1)
  t "the request's image node stands where the picture stood"
    ((Ir.imageRefs doc).any (·.startsWith Ir.picSrcPrefix))
  t "N0023 names the boundary, once, and nothing warns W0334"
    ((ds.filter (·.code == "N0023")).size == 1 &&
     ds.all (·.code != "W0334") && ds.all (·.code != "W0379"))
  t "the wrapped standalone carries the closed list"
    (match (Ir.pictureRefs doc)[0]? with
     | some (_, w) =>
       hasStr w "\\documentclass{standalone}" && hasStr w "\\usepackage{tikz}" &&
       hasStr w "\\usetikzlibrary{arrows}" && hasStr w "\\tikzset{zz/.style={}}" &&
       hasStr w "\\usepackage{pgfplots}" && hasStr w "\\draw (0,0) circle (1);"
     | none => false)
  t "the picture's identity is the author's bytes, not the request"
    (match doc.pictureSrcs[0]? with
     | some (id, body) => id == Ir.picHash body && !hasStr body "standalone"
     | none => false)
  -- The request is a projection of the document's design
  -- (`Ir.pictureRefs_design_projects`): the palette roles the body
  -- mentions ride with the palette's value, unmentioned roles do not, and
  -- the declared font roles travel — the math face through unicode-math.
  let reqOf (d : Ir.Doc) : String := ((Ir.pictureRefs d)[0]?.map (·.2)).getD ""
  let pal := "\\palette{ ember = #C0431F, quietbg = #F2EEE8 }\n"
  -- The keys and the macro references ride on the `\shade`, the construct
  -- still outside the subset: a `\node` with no `at` draws natively now
  -- (M8b slice 3), and its body's unreadable macro no longer costs the
  -- label either (`Picture.nodeLabel`), so a node always ships a shape and
  -- a fixture about the boundary request has to name something the engine
  -- cannot draw at all.
  let picC := "\\begin{tikzpicture}\\shade[fill=ember!20, text=ember] (0,0) rectangle (1,1);" ++
    "\\end{tikzpicture}"
  let (cdoc, _) := elabStr (dvDoc pal picC)
  t "a palette role the picture mentions is declared in the standalone"
    (hasStr (reqOf cdoc) "\\definecolor{ember}{RGB}{192,67,31}")
  t "a palette role the picture never mentions does not ride"
    (!hasStr (reqOf cdoc) "quietbg" && !hasStr (reqOf cdoc) "\\definecolor{fg}")
  let (cdoc', _) := elabStr (dvDoc "\\palette{ ember = #C0431F, quietbg = #000000 }\n" picC)
  t "an unmentioned palette edit leaves the request untouched"
    (Ir.pictureRefs cdoc == Ir.pictureRefs cdoc' && !(Ir.pictureRefs cdoc).isEmpty)
  let (cdoc'', _) := elabStr (dvDoc "\\palette{ ember = #000000, quietbg = #F2EEE8 }\n" picC)
  t "a mentioned palette edit moves the request"
    (Ir.pictureRefs cdoc != Ir.pictureRefs cdoc'' &&
     (Ir.pictureRefs cdoc).map (·.1) == (Ir.pictureRefs cdoc'').map (·.1))
  let (ldoc, _) := elabStr (dvDoc (pal ++ "\\colorlet{ember2}{ember!50!black}\n")
    ("\\begin{tikzpicture}\\shade[text=ember2] (0,0) rectangle (1,1);" ++
     "\\end{tikzpicture}"))
  t "a colorlet role rides with its resolved value"
    (match ldoc.palette.find? "ember2" with
     | some c => hasStr (reqOf ldoc) (Ir.colorDeclLine ("ember2", c)) &&
         hasStr (reqOf ldoc) "\\definecolor{ember2}{RGB}{"
     | none => false)
  let (kdoc, _) := elabStr (dvDoc "\\palette{ ink = cmyk(0, 0.83, 0.76, 0.07), key = cmyk(0, 1, 1, 0) }\n"
    ("\\begin{tikzpicture}\\shade[text=ink, fill=key] (0,0) rectangle (1,1);" ++
     "\\end{tikzpicture}"))
  t "a cmyk role rides in its declared model"
    ((kdoc.palette.find? "ink" |>.any (·.cmyk.isSome)) &&
      hasStr (reqOf kdoc) "\\definecolor{ink}{cmyk}{0,0.83,0.76,0.07}" &&
      hasStr (reqOf kdoc) "\\definecolor{key}{cmyk}{0,1,1,0}")
  -- The deck's shape, invented text: a theme role reached only through
  -- \alert's rewrite, and a formula in a node — red before this slice
  -- (undefined colour `alert`, Computer Modern letters), green after.
  let (tdoc, tds) := elabStr (dvDoc "\\theme{moloch}\n\\fonts{ math = \"Fira Math\" }\n"
    ("\\begin{tikzpicture}\\shade[\\alert{x} $y$]" ++
     " (0,0) rectangle (1,1);\\end{tikzpicture}"))
  t "a theme role reached through alert's rewrite is declared with the bundle's value"
    (hasStr (reqOf tdoc) "\\textcolor {alert}" &&
     hasStr (reqOf tdoc) "\\definecolor{alert}{RGB}{165,90,19}")
  t "the declared math face rides through unicode-math"
    (hasStr (reqOf tdoc) "\\usepackage{unicode-math}" &&
     hasStr (reqOf tdoc) "\\setmathfont{Fira Math}")
  t "a boundary picture with a formula stays one request with no E0382 of its own"
    ((Ir.pictureRefs tdoc).size == 1 && tds.all (·.code != "E0382"))
  let (fdoc, _) := elabStr (dvDoc
    "\\fonts{ body = \"Source Serif Pro\", sans = \"Open Sans\", mono = \"Source Code Pro\" }\n"
    picC)
  t "the body, sans and mono roles ride as fontspec's three set lines"
    (hasStr (reqOf fdoc) "\\setmainfont{Source Serif Pro}" &&
     hasStr (reqOf fdoc) "\\setsansfont{Open Sans}" &&
     hasStr (reqOf fdoc) "\\setmonofont{Source Code Pro}" &&
     !hasStr (reqOf fdoc) "unicode-math")
  t "a face declared by file name does not travel"
    (!hasStr (reqOf (elabStr (dvDoc "\\fonts{ body = \"SourceSerifPro-Regular.otf\" }\n"
      picC)).1) "\\setmainfont")
  t "the set lines are the boundary's: no W0301 for them"
    (ds.all (·.code != "W0301"))
  -- The document's own macros ride: the closed list was closed over the
  -- commands the engine knows, so a `\newcommand` the picture spells was
  -- undefined at the boundary and the tool drew nothing. The invariant is
  -- `Ir.macroDecls_covers` — a control sequence the body spells that the
  -- document defined is declared in the request — with `Ir.macroDecls_mem`
  -- bounding what rides. Invented macros, invented palette.
  let mac := "\\newcommand{\\tint}[1]{\\textcolor{ember}{#1}}\n" ++
    "\\newcommand{\\badge}[1]{\\tint{[#1]}}\n" ++
    "\\newcommand{\\elsewhere}{only ever in prose}\n"
  let picM := "\\begin{tikzpicture}\\shade[\\badge{ok}] (0,0) rectangle (1,1);" ++
    "\\end{tikzpicture}"
  let (mdoc, mds) := elabStr (dvDoc (pal ++ mac) picM)
  t "a macro the picture spells is defined in the standalone"
    (hasStr (reqOf mdoc) "\\renewcommand{\\badge}[1]")
  t "a definition the standalone reads can never fail on an existing name"
    (hasStr (reqOf mdoc) "\\providecommand{\\badge}{}")
  t "a macro reached only through another macro's body rides too"
    (hasStr (reqOf mdoc) "\\renewcommand{\\tint}[1]")
  t "a macro the picture never reaches stays home"
    (!hasStr (reqOf mdoc) "elsewhere")
  t "a palette role only a carried macro spells is declared"
    (hasStr (reqOf mdoc) "\\definecolor{ember}{RGB}{192,67,31}")
  t "carrying the document's macros costs the picture no diagnostic"
    (mds.all (·.code != "E0382") && (Ir.pictureRefs mdoc).size == 1)
  -- Locality of the cache key, as an oracle (no theorem stands behind it):
  -- editing a macro no picture reaches leaves the request byte-identical,
  -- editing one it reaches moves it — so a warm slot is never served the
  -- wrong drawing, and never discarded for an unrelated edit.
  t "an unreached macro edit leaves the request untouched"
    (reqOf mdoc == reqOf (elabStr (dvDoc (pal ++
      "\\newcommand{\\tint}[1]{\\textcolor{ember}{#1}}\n" ++
      "\\newcommand{\\badge}[1]{\\tint{[#1]}}\n" ++
      "\\newcommand{\\elsewhere}{quite another wording}\n") picM)).1)
  t "a reached macro edit moves the request"
    (reqOf mdoc != reqOf (elabStr (dvDoc (pal ++
      "\\newcommand{\\tint}[1]{\\textcolor{ember}{\\itshape #1}}\n" ++
      "\\newcommand{\\badge}[1]{\\tint{[#1]}}\n" ++
      "\\newcommand{\\elsewhere}{only ever in prose}\n") picM)).1)
  -- The definer family and TeX's own `\def`, each with the arity and the
  -- optional default the document wrote — the default is the one part a
  -- native `UserCmd` cannot spell back, so the declaration is captured as
  -- written rather than reconstructed.
  let (fdoc2, _) := elabStr (dvDoc
    ("\\newcommand{\\plain}{p}\n\\renewcommand{\\plain}{q}\n" ++
     "\\providecommand{\\opt}[2][d]{#1#2}\n\\def\\raw#1{<#1>}\n")
    ("\\begin{tikzpicture}\\shade[\\plain\\opt{a}\\raw{b}]" ++
     " (0,0) rectangle (1,1);\\end{tikzpicture}"))
  t "an optional argument's default travels with its definition"
    (hasStr (reqOf fdoc2) "\\renewcommand{\\opt}[2][d]")
  t "a redefinition in force at the picture rides in the picture as the site's text"
    (hasStr (reqOf fdoc2) "[q\\opt" &&
      !hasStr (reqOf fdoc2) "\\renewcommand{\\plain}{p}" &&
      !hasStr (reqOf fdoc2) "\\newcommand{\\plain}{p}")
  t "TeX's own def rides in its own spelling"
    (hasStr (reqOf fdoc2) "\\def\\raw#1{<#1>}")
  -- Conservation across the definer rewrite, with a picture in play: the
  -- LaTeX spelling and the native one carry the same definition, so a
  -- document that writes `\define` itself is not one whose pictures lose
  -- their macros. An oracle, not a theorem.
  let picD := "\\begin{tikzpicture}\\shade[\\hue{x}] (0,0) rectangle (1,1);" ++
    "\\end{tikzpicture}"
  t "the native define spelling carries the same definition as newcommand"
    (reqOf (elabStr (dvDoc "\\newcommand{\\hue}[1]{\\textbf{#1}}\n" picD)).1 ==
      reqOf (elabStr (dvDoc "\\define \\hue(a1: content) {\\textbf{#1}}\n" picD)).1)
  t "a picture package's load rides too: no W0103 for it"
    (ds.all (·.code != "W0103"))
  -- Determinism by purity: two elaborations of one document state
  -- byte-identical requests, so the cache key means something.
  t "the request is deterministic"
    (doc.pictureSrcs == (elabStr (dvDoc sets pic)).1.pictureSrcs)
  -- Environment-freedom, the executable half (`boundary_request_env_free`
  -- carries the IR statement): pinning the default tool is not an
  -- argument to the artifact — the pinned and the undeclared spellings
  -- elaborate to the identical Doc, request included.
  t "pinning the default tool elaborates to the identical Doc"
    ((elabStr (dvDoc ("\\pictures{ tool = lualatex }\n" ++ sets) pic)).1 ==
      (elabStr (dvDoc ("% pinned by default\n" ++ sets) pic)).1)
  -- TikZ's own spelling pins the same default.
  t "tikzexternalize is the LaTeX-shaped pin"
    ((elabStr (dvDoc "\\usepackage{tikz}\\tikzexternalize\n" pic)).1.pictureTool
      == some "lualatex")
  -- A picture the subset draws whole stays native: the boundary is for
  -- what the subset refuses, never a detour for what the engine owns.
  let native := (elabStr (dvDoc ""
    "\\begin{tikzpicture}\\fill (0,0) rectangle (1,1);\\end{tikzpicture}")).1
  t "an in-subset picture never routes to the boundary"
    (native.pictureSrcs.isEmpty &&
     native.body.any fun b => match b with | .picture _ => true | _ => false)
  -- The declared refusal: the constructs stay refused where they stand,
  -- the placeholder is W0362's, and no W0379 — the declaration accepted
  -- it. The set lines and the picture package's load are then unknown
  -- and unsupported again, named.
  let refuse := "\\pictures{ tool = none }\n"
  let (closedDoc, closedDs) := elabStr (dvDoc (refuse ++ sets) pic)
  t "tool = none refuses: W0334 stays, no request, no W0379"
    (closedDs.any (·.code == "W0334") && closedDs.all (·.code != "W0379") &&
     closedDoc.pictureSrcs.isEmpty && closedDoc.pictureTool.isNone)
  t "tool = none makes the set lines and the picture load named losses again"
    (closedDs.any (·.code == "W0301") && closedDs.any (·.code == "W0103"))
  -- An unpinned tool is refused: the driver executes the named binary, so
  -- the value is drawn from the engine's own list, never the document's.
  -- The misread pin does not close the door: E0321 names the value, and
  -- the default stands — the allowlist is what the driver runs either way.
  let (badDoc, badDs) := elabStr (dvDoc "\\pictures{ tool = rm }\n" pic)
  t "an unpinned tool is refused by name and the default stands"
    (badDs.any (·.code == "E0321") && badDoc.pictureTool == some "lualatex")
  -- A pruned picture asks for nothing: the request follows the tree, as a
  -- pruned bibliography's does.
  t "pictureRefs follows the shipped tree"
    ((Ir.pictureRefs { pictureSrcs := #[("h", "src")] } : Array _).isEmpty)

/-- The boundary picture's measure fit, over `Layout.Out`: an unsized
boundary picture wider than the measure lays out at exactly the measure —
the box is the engine's to measure and place (N0023's claim), the form is
vector, and the document declared no size to honour — with no W0005 for
it. An ordinary image keeps its natural size and LaTeX's honest overfull. -/
def boundaryFitChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (fitDoc, _) := elabStr (dvDoc ""
    "\\begin{tikzpicture}\\draw (0,0) circle (40);\\end{tikzpicture}")
  let fitSrc := ((Ir.imageRefs fitDoc).find? (·.startsWith Ir.picSrcPrefix)).getD ""
  let wideInfo : Image.Plan := { pxW := 2000, pxH := 200 }
  let store : Image.Store := { entries := #[{ src := fitSrc, info := some wideInfo }] }
  let out := layoutOf oneFace fitDoc (imgs := store)
  let geom := Layout.Geom.ofPage fitDoc.page
  let widths := (allLines out).flatMap (·.segs.filterMap fun s => match s with
    | .image _ w _ => some w
    | _ => none)
  t "an unsized boundary picture wider than the measure fits it exactly"
    (widths == #[geom.textWidth])
  t "the fit is silent: no W0005 for the routed box"
    (out.diags.all (·.code != "W0005"))
  let (imgDoc, _) := elabStr (dvDoc ""
    "\\includegraphics[alt={A synthetic band}]{band.png}")
  let imgStore : Image.Store :=
    { entries := #[{ src := "band.png", info := some wideInfo }] }
  let imgOut := layoutOf oneFace imgDoc (imgs := imgStore)
  t "an ordinary wide image keeps its natural size and the overfull is named"
    (((allLines imgOut).flatMap (·.segs.filterMap fun s => match s with
        | .image _ w _ => some w
        | _ => none)) == #[Dim.pt 2000] &&
     imgOut.diags.any (·.code == "W0005"))

/-- **A definition a picture needs reaches that picture's renderer
regardless of where in the document it was written.** The invariant whose
absence shipped three defects at once (PLAN, 2026-09-22 pic-boundary): a
figure kept in its own file carries its `\usetikzlibrary` and `\tikzset`
just above its picture, inside the body, and the collector stopped at
`\begin{document}` — so pgf met a picture whose arrow tips and shapes had
never been defined, the boundary failed, the body-level line fell to W0301
and printed the definition's own source into the paragraph, and the page
shipped an empty box with that source above it. The theorem over the
collector is `Compat.boundaryDecls_covers`; these are the claims about the
document and the page it produces. No `lualatex` is needed for any of
them: the request is the elaborator's, and the ink the native subset's. -/
def pictureDefnReachChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  -- The set lines where a figure file puts them: in the body, above the
  -- picture that reads them.
  let sets := "\\usetikzlibrary{arrows.meta}\n\\tikzset{scmarrow/.tip={Latex[round]}}\n\n"
  -- A picture the subset draws nothing of, so the boundary is its route.
  -- `\shade` is the construct outside it: a `\path` of drawn segments is
  -- native now (M8b slice 3), and a fixture that routes has to name
  -- something the engine genuinely cannot draw.
  let outside := "\\begin{tikzpicture}\\shade (0,0) rectangle (1,1);\\end{tikzpicture}"
  let (bodyDoc, bodyDs) := elabStr (dvDoc "" (sets ++ outside))
  let (preDoc, _) := elabStr (dvDoc sets outside)
  let reqOf (d : Ir.Doc) : String := ((Ir.pictureRefs d)[0]?.map (·.2)).getD ""
  t "a body-level set line reaches the standalone its picture renders in"
    (hasStr (reqOf bodyDoc) "\\usetikzlibrary{arrows.meta}" &&
     hasStr (reqOf bodyDoc) "\\tikzset{scmarrow/.tip={Latex[round]}}")
  t "where a set line stands does not change the request"
    (reqOf bodyDoc == reqOf preDoc && !(reqOf bodyDoc).isEmpty)
  t "a body-level set line is not an unknown command"
    (bodyDs.all (·.code != "W0301"))
  -- Its group addresses pgf, never the sentence: kept as text it printed
  -- the definition's own source into the paragraph.
  let shippedText (d : Ir.Doc) : String :=
    String.intercalate " "
      ((censusOf (coveredColorsOf d) (layoutOf oneFace d)).toList.map (·.text))
  let shipped := shippedText bodyDoc
  t "the definition's source is not ink on the page"
    (!hasStr shipped "scmarrow" && !hasStr shipped "arrows.meta" &&
     !hasStr shipped "Latex")
  -- The declared refusal is still the acceptance: with no boundary, a set
  -- line is an unknown command again, arguments and all.
  let (_, refusedDs) := elabStr (dvDoc "\\pictures{ tool = none }\n" (sets ++ outside))
  t "tool = none makes a body-level set line an unknown command again"
    (refusedDs.any (·.code == "W0301"))
  -- Native first: what the subset draws, it draws, and what it refused is
  -- named beside it. Only a picture it draws nothing of routes.
  let partly := "\\begin{tikzpicture}\\node at (0,0) {Alpha};" ++
    "\\shade (0,0) rectangle (1,1);\\end{tikzpicture}"
  let (partDoc, partDs) := elabStr (dvDoc "" partly)
  t "a picture the subset draws partly stays native, its refusal named"
    (partDoc.pictureSrcs.isEmpty && partDs.any (·.code == "W0334") &&
     partDoc.body.any fun b => match b with | .picture _ => true | _ => false)
  t "the partly-drawn picture ships its ink"
    (hasStr (shippedText partDoc) "Alpha")
  t "a picture the subset draws nothing of still routes to the boundary"
    ((Ir.pictureRefs bodyDoc).size == 1 && bodyDoc.pictureSrcs.size == 1)
  -- A boundary failure is a dropped loss, not a degraded one: `degraded`
  -- promises the reader sees "something stands here", and an empty
  -- unlabelled box is the one thing that does not. Native is tried first,
  -- so a picture only reaches the boundary when the engine drew nothing of
  -- it — no part of it was drawn, so there is nothing to fall back to — and
  -- the run fails rather than shipping a page that reads as intentional.
  let failed := DriverDiag.boundaryFailed "lualatex"
    "! Package pgf Error: Unknown arrow tip kind 'scmarrow'."
  t "a boundary failure is an error the document must declare to accept"
    (failed.code == "E0382" && failed.severity == .error &&
     DiagCode.E0382.loss == .dropped)
  t "the failure carries the tool's own last words"
    (hasStr (failed.help.getD "") "Unknown arrow tip kind")
  -- The converter gap keeps W0378, and keeps it a warning: the PDF is
  -- unaffected and the HTML page shows each picture's alternative.
  t "the HTML converter gap is a different code, and still a warning"
    ((DriverDiag.boundarySvgMissing "not found").code == "W0378" &&
     DiagCode.W0378.loss == .degraded)

/-- The three levels a picture's option entries are read under, read off the
page the engine ships rather than the IR: **picture < every X < the
bracket's own** (`Picture.mergeOpts`, whose boundaries are
`merge_every_exact` and `merge_own_exact`). A node's size and a path's
stroke each take exactly one of the three values declared for it, and the
other two leave no trace — only the artifact can say which survived. The
same page carries the no-boundary fact: the outlines ship as page paths and
no image box stands where either picture is, so the ink is the engine's own
and no external tool was asked to draw it. -/
def pictureEveryLevelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let src :=
    "\\tikzset{every node/.style={circle, draw, minimum size=8mm}}\n" ++
    "\\tikzset{every path/.style={thick, draw=green}}\n" ++
    "\\tikzset{wide/.style={minimum size=14mm}}\n" ++
    "\\tikzset{wire/.style={draw=blue}}\n" ++
    "\\begin{document}\n" ++
    "\\begin{tikzpicture}[wide]\n" ++
    "\\node at (0,0) {A};\n" ++
    "\\node[minimum size=5mm] at (3,0) {C};\n" ++
    "\\end{tikzpicture}\n" ++
    "\\begin{tikzpicture}[wire]\n" ++
    "\\draw (0,0) -- (3,0);\n" ++
    "\\draw[draw=red] (0,0.6) -- (3,0.6);\n" ++
    "\\end{tikzpicture}\n" ++
    "\\end{document}"
  let (doc, ds) := elabStr src
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  t "the every-level document elaborates with nothing refused" ds.isEmpty
  t "both node outlines and both edges ship as page paths"
    ((c[0]?.map (·.paths == 4)).getD false)
  t "no boundary box stands where either picture is"
    ((c[0]?.map (·.images == 0)).getD false)
  -- The node that declared nothing ships `every node`'s 8mm, not the
  -- picture's 14mm; the node that declared its own ships 5mm, not either.
  t "the node that declared nothing ships the every-node size"
    ((c[0]?.bind (·.pathSpans[0]?)).map (· == (Dim.mm 8, Dim.mm 8)) == some true)
  t "the node that declared its own size ships it, over both other levels"
    ((c[0]?.bind (·.pathSpans[1]?)).map (· == (Dim.mm 5, Dim.mm 5)) == some true)
  -- The path pair, read off the shipped strokes: the edge that declared
  -- nothing ships `every path`'s colour over the picture's, and both edges
  -- ship `every path`'s width, which no bracket re-declared. Asserted as
  -- the whole array, so the two edge facts cannot drift onto another path.
  t "the shipped strokes are the two node outlines and the two edges' own"
    ((c[0]?.map (·.pathStrokes ==
      #[(Ir.Color.black, Ir.Pic.thinWidth), (Ir.Color.black, Ir.Pic.thinWidth),
        ({ r := 0, g := 255, b := 0 }, Ir.Pic.thickWidth),
        ({ r := 255, g := 0, b := 0 }, Ir.Pic.thickWidth)])).getD false)
  t "both node bodies ship as ink"
    (pageHas c 0 "A" && pageHas c 0 "C")

/-- The two other definition handlers, read off the shipped page: an
appended body's keys both draw (`Picture.appendStyle` composes where
`/.style` shadows), and an arrow tip the document declared with `/.tip`
ships this subset's own head — a filled triangle path beside the edge's
own, where an undeclared tip ships the edge alone and says so. No image
box on either page: the heads are the engine's ink, not a tool's. -/
def pictureStyleHandlerChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let appended :=
    "\\tikzset{ball/.style={circle, draw}}\n" ++
    "\\tikzset{ball/.append style={minimum size=8mm}}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node[ball] at (0,0) {A};\n\\end{tikzpicture}\n\\end{document}"
  let ca := censusSrc appended
  t "an appended body ships the outline of one half at the size of the other"
    ((ca[0]?.map (·.paths == 1)).getD false &&
     ((ca[0]?.bind (·.pathSpans[0]?)).map (· == (Dim.mm 8, Dim.mm 8)) == some true))
  t "no boundary box stands where the appended-style picture is"
    ((ca[0]?.map (·.images == 0)).getD false)
  let tipSrc (decl : String) : String :=
    decl ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\draw[-scm] (0,0) -- (2,0);\n\\end{tikzpicture}\n\\end{document}"
  let cd := censusSrc (tipSrc "\\tikzset{scm/.tip={Latex[round]}}\n")
  let cu := censusSrc (tipSrc "")
  t "a declared tip ships a head beside its edge"
    ((cd[0]?.map (·.paths == 2)).getD false)
  t "an undeclared tip ships the edge alone"
    ((cu[0]?.map (·.paths == 1)).getD false)
  t "no boundary box stands where the tip pictures are"
    ((cd[0]?.map (·.images == 0)).getD false &&
     (cu[0]?.map (·.images == 0)).getD false)

/-- Native node placement, read off the shipped page (M8b slice 3). Four
facts, each a defect the deck-shaped picture showed:

* A `\node` with no `at` stands at the picture origin — pgf's current
  point at the start of a path — instead of being refused for lack of a
  coordinate. That refusal is what sent a whole picture to the boundary,
  since `pic.shapes.isEmpty` is the only door to it.
* A name written before the option bracket (`\node (n) [keys] {body}`) is
  the same name as one written after it: pgf reads the two orders alike.
* `left=of`/`right=of`/`above=of`/`below=of` place the node at the
  `node distance` from the named one, centre to centre (`Picture.placeRel_exact`).
* The placement is a function of the reference graph, not of declaration
  order: the page is the same whichever of two nodes is written first. The
  rows below read that off two shipped pages; the statement is owed as
  `Obligations.place_order_agree`, which still lacks the independence
  hypothesis its record names. TikZ rejects the forward reference; the
  engine resolves it, and only a reference to a name no node carries — or
  a cycle — is refused, by name.

`\path (a) edge (b)` ships the edge beside them: pgf's `every edge` carries
`draw`, so a `\path` whose operation is `edge` strokes. -/
def pictureNodePlaceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  -- The centre and the half-extents of the k-th shipped path, so a
  -- placement fact reads a point and the borders around it.
  let box (c : Array CensusPage) (k : Nat) :
      Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    (c[0]?.bind (·.pathBoxes[k]?)).map fun (x, y, w, h) =>
      (x + w / 2, y + h / 2, w / 2, h / 2)
  let node (nm body extra : String) : String :=
    "\\node (" ++ nm ++ ") [draw, minimum size=6mm" ++ extra ++ "] {" ++ body ++ "};\n"
  let pic (body : String) : String :=
    "\\tikzset{node distance = 1cm and 1cm}\n\\begin{document}\n" ++
    "\\begin{tikzpicture}\n" ++ body ++ "\\end{tikzpicture}\n\\end{document}"
  let src := pic (node "aa" "Pear" "" ++ node "bb" "Plum" ", right =of aa" ++
    node "cc" "Fig" ", below =of aa" ++ "\\path (aa) edge (bb);\n")
  let (doc, ds) := elabStr src
  let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  t "a picture of placed nodes and a path edge elaborates with nothing refused"
    (ds.all (·.severity == .note))
  t "three node outlines and the path's edge ship as page paths"
    ((c[0]?.map (·.paths == 4)).getD false)
  t "no boundary box stands where the placed-node picture is"
    ((c[0]?.map (·.images == 0)).getD false)
  t "every placed node's body ships as ink"
    (pageHas c 0 "Pear" && pageHas c 0 "Plum" && pageHas c 0 "Fig")
  -- `right =of aa` leaves one node distance between the two *borders*, as
  -- pgf's `positioning` does — so the centres stand that far apart plus a
  -- half-extent from each node. Stated against the extents the page
  -- shipped rather than against a computed total, so the fact is the
  -- invariant and not a restatement of one rounding.
  t "'right =of' leaves one node distance between the borders, at the same height"
    (match box c 0, box c 1 with
     | some (ax, ay, aw, _), some (bx, byy, bw, _) =>
       bx - ax == Dim.mm 10 + aw + bw && byy == ay
     | _, _ => false)
  t "'below =of' leaves one node distance below, at the same x"
    (match box c 0, box c 2 with
     | some (ax, ay, _, ah), some (cx, cy, _, ch) =>
       cy - ay == Dim.mm 10 + ah + ch && cx == ax
     | _, _ => false)
  -- The same two nodes, the referenced one written second: TikZ rejects
  -- this, and the offset the page carries must not know the difference.
  let fwd := censusSrc (pic (node "bb" "Plum" ", right =of aa" ++ node "aa" "Pear" ""))
  let bwd := censusSrc (pic (node "aa" "Pear" "" ++ node "bb" "Plum" ", right =of aa"))
  t "a forward reference resolves: the offset is the same either way round"
    (match box fwd 0, box fwd 1, box bwd 0, box bwd 1 with
     | some (bx, byy, bw, _), some (ax, ay, aw, _),
       some (ax', ay', aw', _), some (bx', byy', bw', _) =>
       bx - ax == bx' - ax' && byy - ay == byy' - ay' &&
         bx - ax == Dim.mm 10 + aw + bw && aw' + bw' == aw + bw
     | _, _, _, _ => false)
  t "no boundary box stands where either order's picture is"
    (((fwd[0]?.map (·.images == 0)).getD false) &&
     ((bwd[0]?.map (·.images == 0)).getD false))
  -- A name no node carries is the one refusal left, and it costs that
  -- node alone: the picture's other node still ships.
  let (_, unknownDs) := elabStr (pic (node "aa" "Pear" "" ++ node "bb" "Plum" ", right =of zz"))
  t "a reference to a name no node carries is refused by that name"
    (unknownDs.any fun d => d.code == "E0333" && hasStr d.message "zz")
  let cu := censusSrc (pic (node "aa" "Pear" "" ++ node "bb" "Plum" ", right =of zz"))
  t "the refused node costs itself, not the picture"
    (pageHas cu 0 "Pear" && ((cu[0]?.map (·.images == 0)).getD false))
  -- An operation's own bracket carries the stroke: on `edge [dashed]` the
  -- dash is what the diagram means by that edge, so it has to reach the
  -- page. Read off the shipped strokes, since only the page can say.
  let dashed := censusSrc (pic (node "aa" "Pear" "" ++ node "bb" "Plum" ", right =of aa" ++
    "\\path (aa) edge [dashed, draw=blue] (bb);\n"))
  t "an edge operation's own bracket reaches the shipped stroke"
    ((dashed[0]?.map (·.pathStrokes.any fun (c, _) =>
      c == { r := 0, g := 0, b := 255 })).getD false)
  -- A `\path` that asks for no drawing paints nothing: pgf's `\path` is
  -- the unpainted one, and only an `edge` or a `draw` key changes that.
  let quiet := censusSrc (pic ("\\path (0,0) -- (2,0);\n"))
  t "a path that asks for no drawing ships no stroke"
    ((quiet[0]?.map (·.paths == 0)).getD false)

/-- **A node body the subset cannot fully read still ships the text it can
read** (`Picture.labelFloor_accounts`). The defect: one unreadable macro in
one body dropped the whole label, so a diagram whose every node wrote a
two-line label shipped an outline with no text in it at all — three
consecutive pages of a real deck — while every warning said so where no
reader looks.

Read off the shipped lines, never an IR dump: the claim is about what a
page carries. The salvage rows pin whole labels rather than absences,
because an absence test passes under a salvage that kept nothing — the
lesson the math floor's own review round recorded.

Four narrowed constructs beside the floor, in the order they cost a reader
most: `\\` opens a real second line (one label shape per line, stacked by
`Picture.nodeLineLead`), a size switch opening a line sets that line's
size, `\textcolor{role}{body}` sets its body in the role, and a phantom is
invisible — no ink, and no loss to name, so the placeholder may not stand
in for it. -/
def pictureNodeFloorChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pic (body : String) : String :=
    "\\palette{ rose = #B03060 }\\begin{document}\n\\begin{tikzpicture}\n" ++
    body ++ "\\end{tikzpicture}\n\\end{document}"
  let run (body : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr (pic body)
    (censusOf (coveredColorsOf doc) (layoutOf oneFace doc), ds)
  -- The label lines a picture shipped, in paint order: text, baseline and
  -- set size, which is everything the stacking and sizing facts read. The
  -- page's own furniture (its number) is not the picture's.
  let labels (c : Array CensusPage) : Array (String × Dim.Sp × Dim.Sp) :=
    (c[0]?.map fun p => p.lines.filterMap fun l =>
      if l.text.isEmpty || l.furniture then none
      else some (l.text, l.y, l.size)).getD #[]
  -- The floor. A body of one unreadable macro around a word keeps the
  -- word: the macro's own name goes, its content stays.
  let (c1, ds1) := run "\\node (a) {\\wobble{Quince}};\n"
  t "an unreadable macro in a node body keeps the body's word"
    ((labels c1).any fun (s, _, _) => s == "Quince")
  t "the unreadable macro is still named at the node"
    (ds1.any fun d => d.code == "W0334" && hasStr d.message "wobble")
  t "the salvaged label ships no markup"
    (!(labels c1).any fun (s, _, _) =>
      hasStr s "\\" || hasStr s "{" || hasStr s "}")
  -- An argument `Ir.floorNamedArgs` says *names* rather than carries never
  -- rides onto the page: a key is not a word the label meant to say. The
  -- one command's own content still does.
  let (c2, _) := run "\\node (a) {\\wobble{Plum}\\ref{some:key}};\n"
  t "a naming argument is dropped where the same command's content is kept"
    ((labels c2).any fun (s, _, _) => s == "Plum")
  t "the named key never reaches the page"
    (!(labels c2).any fun (s, _, _) => hasStr s "some:key")
  -- The empty floor: a body whose every token is unreadable salvages to
  -- nothing, and a blank is not an honest floor either — so the declared
  -- placeholder stands and the case is never silent
  -- (`Picture.labelFloor_accounts`).
  let (c3, ds3) := run "\\node (a) {\\wobble};\n"
  t "a body that salvages to nothing ships the declared placeholder"
    ((labels c3).any fun (s, _, _) => s == Picture.nodeFloorPlaceholder)
  t "the placeholder case is named, not silent"
    (ds3.any fun d => d.code == "W0334")
  -- `\\` is a real second line: two label shapes, the first above the
  -- second by one lead, both centred on the node's own x.
  let (c4, ds4) := run "\\node (a) {Pear\\\\Fig};\n"
  t "a two-line node body elaborates with nothing refused"
    (ds4.all (·.severity == .note))
  t "both of a two-line label's lines ship as ink"
    ((labels c4).any (fun (s, _, _) => s == "Pear") &&
     (labels c4).any fun (s, _, _) => s == "Fig")
  t "the first line stands one lead above the second"
    (match (labels c4).find? (·.1 == "Pear"), (labels c4).find? (·.1 == "Fig") with
     | some (_, y1, _), some (_, y2, s2) => y2 - y1 == Ir.leadingFor s2
     | _, _ => false)
  t "a line break in a node body ships no markup"
    (!(labels c4).any fun (s, _, _) => hasStr s "\\")
  -- A size switch opening a line sets that line's size: a label shape
  -- carries one size, so the switch may open a line and not stand inside
  -- one — where it does, the loss is named rather than half-applied.
  let (c5, ds5) := run "\\node (a) {Pear\\\\\\footnotesize Fig};\n"
  t "a size switch opening a label line is honoured, not refused"
    (ds5.all (·.severity == .note))
  t "the switched line sets smaller than the line above it"
    (match (labels c5).find? (·.1 == "Pear"), (labels c5).find? (·.1 == "Fig") with
     | some (_, _, s1), some (_, _, s2) => s2 < s1
     | _, _ => false)
  -- The gap tracks the size, not a constant: a smaller second line sits
  -- closer than an equal-sized one. Stated as the comparison rather than as
  -- an equality against the leading, because each line is centred on its own
  -- anchor — so the *anchors* are one leading apart and the shipped
  -- baselines differ by the two lines' ink-height correction as well. Equal
  -- sizes are the case where that correction cancels, and the row above pins
  -- it exactly there.
  t "the gap before a smaller line is smaller than before an equal one"
    (match (labels c4).find? (·.1 == "Pear"), (labels c4).find? (·.1 == "Fig"),
           (labels c5).find? (·.1 == "Pear"), (labels c5).find? (·.1 == "Fig") with
     | some (_, a1, _), some (_, a2, _), some (_, b1, _), some (_, b2, _) =>
       b2 - b1 < a2 - a1
     | _, _, _, _ => false)
  let (_, ds6) := run "\\node (a) {Pear \\footnotesize Fig};\n"
  t "a size switch inside a label line is named instead"
    (ds6.any fun d => d.code == "W0334" && hasStr d.message "footnotesize")
  let (_, ds6b) := run "\\node (a) {{\\footnotesize Fig}};\n"
  t "a size switch inside a group is named, never silently lost"
    (ds6b.any fun d => d.code == "W0334" && hasStr d.message "footnotesize")
  -- `\textcolor{role}{body}`: the palette role is already carried to
  -- pictures, so a coloured label draws in its role. Read off the covered
  -- census channel, the only place a shipped colour is visible.
  let (c7, ds7) := run "\\node (a) {\\textcolor{rose}{Sloe}};\n"
  t "a coloured node label elaborates with nothing refused"
    (ds7.all (·.severity == .note))
  t "the coloured label's word still ships"
    ((labels c7).any fun (s, _, _) => s == "Sloe")
  t "a colour role the palette does not carry is named, and the word stays"
    (let (c8, ds8) := run "\\node (a) {\\textcolor{nosuch}{Sloe}};\n"
     ds8.any (fun d => d.code == "W0334" && hasStr d.message "nosuch") &&
       (labels c8).any fun (s, _, _) => s == "Sloe")
  -- A phantom is invisible by definition: its argument is sizing, not
  -- content, so it contributes no ink *and* names no loss — the
  -- placeholder must not stand in for it.
  let (c9, ds9) := run "\\node (a) {\\vphantom{p}Damson};\n"
  t "a phantom costs the label nothing and names nothing"
    (ds9.all (·.severity == .note) &&
      (labels c9).any fun (s, _, _) => s == "Damson")
  t "a phantom's own argument is not ink"
    (!(labels c9).any fun (s, _, _) => hasStr s "p" && s != "Damson")
  let (c10, ds10) := run "\\node (a) {\\vphantom{p}};\n"
  t "a body of nothing but a phantom is honestly empty, not a placeholder"
    (ds10.all (·.severity == .note) &&
      !(labels c10).any fun (s, _, _) => s == Picture.nodeFloorPlaceholder)
  -- The whole point, on the shape the deck carries: every node writes a
  -- two-line label whose second line is a size switch and a coloured
  -- group. Before the floor this picture shipped its edge and no text.
  let deck :=
    "\\node (a) {A\\\\\\footnotesize\\textcolor{rose}{First Words}};\n" ++
    "\\node (b) [right =of a] {B\\\\\\footnotesize\\textcolor{rose}{Other Words}};\n" ++
    "\\path (a) edge (b);\n"
  let (c11, ds11) := run deck
  t "the deck-shaped diagram elaborates with nothing refused"
    (ds11.all (·.severity == .note))
  t "every line of every node's label ships as ink"
    (["A", "First Words", "B", "Other Words"].all fun w =>
      (labels c11).any fun (s, _, _) => s == w)
  t "no boundary box stands where the deck-shaped picture is"
    ((c11[0]?.map (·.images == 0)).getD false)
  t "the diagram's edge ships beside its labels"
    ((c11[0]?.map (·.paths == 1)).getD false)
  -- **A naming argument is a group, never the next token.** An adversarial
  -- review of the first cut found the loose-counter form the math floor's
  -- own second review round had already abandoned: a pending argument any
  -- token satisfied let a starred name's star stand in for it, so
  -- `\hspace*{1pt}` set its length as ink, and let `\color`'s drop land on
  -- the `\textcolor` that followed, so a colour name did. Whole labels, not
  -- absences, because an absence row passes on a salvage that kept nothing.
  let inkOf (body : String) : String :=
    String.intercalate "|" ((labels (run body).1).toList.map (·.1))
  t "a starred name's star does not stand in for its argument"
    (inkOf "\\node (a) {\\hspace*{1pt}delta};\n" == "delta")
  t "every trailing option run goes with the command, not one of them"
    (inkOf "\\node (a) {\\raisebox{2pt}[3pt][4pt]{zeta}};\n" == "zeta")
  t "a length argument never rides onto the page"
    (inkOf "\\node (a) {\\rule{1pt}{2pt}q};\n" == "q")
  t "a colour model run goes with its command"
    (inkOf "\\node (a) {\\textcolor[rgb]{1,0,0}{x}};\n" == "x")
  -- A value argument that would read as a *product* of the expression is
  -- worse than noise: `\cancelto{0}{x}` inked `0x`, which states the
  -- opposite of the source. The floor may be lossy; it may not be false.
  t "a cancel target does not ink as a factor of its expression"
    (inkOf "\\node (a) {\\cancelto{0}{x}};\n" == "x")
  t "a line break's own option run is markup with the break"
    (inkOf "\\node (a) {x\\\\[2ex]y};\n" == "x|y")
  -- **A construct left pending at the end of a body is named.** The same
  -- review found the commit's own headline loss still reachable, and
  -- quieter than before it: a colour with no body, an unterminated option
  -- run and a phantom with no argument each ate the rest of the label in
  -- silence. A mode that has not come to rest is the discriminator.
  let (cp1, dp1) := run "\\node (a) {\\textcolor{rose}};\n"
  t "a colour whose body never came is named and floors to the placeholder"
    (dp1.any (fun d => d.code == "W0334") &&
      (labels cp1).any fun (s, _, _) => s == Picture.nodeFloorPlaceholder)
  let (_, dp2) := run "\\node (a) {\\textcolor{rose}x};\n"
  t "a colour whose body never came keeps the word that followed it"
    (dp2.any (fun d => d.code == "W0334") &&
      inkOf "\\node (a) {\\textcolor{rose}x};\n" == "x")
  let (_, dp3) := run "\\node (a) {\\vphantom};\n"
  t "a phantom with no argument is named, not silently empty"
    (dp3.any fun d => d.code == "W0334")
  t "a phantom with an argument still costs nothing and names nothing"
    (inkOf "\\node (a) {\\vphantom{p}Damson};\n" == "Damson")

mutual

/-- The text runs of one SVG subtree, each with the attributes of every
`<tspan>` around it, innermost first: how the drawing presents each run. -/
def svgRunsOne (env : Array (String × String))
    (acc : Array (String × Array (String × String))) :
    Html.Node → Array (String × Array (String × String))
  | .text s => if s.isEmpty then acc else acc.push (s, env)
  | .elem tag attrs kids =>
    svgRunsList (if tag == "tspan" then attrs ++ env else env) acc kids.toList
  | .style _ => acc
  | .script _ _ => acc

def svgRunsList (env : Array (String × String))
    (acc : Array (String × Array (String × String))) :
    List Html.Node → Array (String × Array (String × String))
  | [] => acc
  | k :: rest => svgRunsList env (svgRunsOne env acc k) rest

end

mutual

/-- Every SVG `<text>` element's runs (`svgRunsOne`), in document order. -/
def svgTextRunsOne (acc : Array (String × Array (String × String))) :
    Html.Node → Array (String × Array (String × String))
  | .elem tag _ kids =>
    if tag == "text" then svgRunsList #[] acc kids.toList
    else svgTextRunsList acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def svgTextRunsList (acc : Array (String × Array (String × String))) :
    List Html.Node → Array (String × Array (String × String))
  | [] => acc
  | k :: rest => svgTextRunsList (svgTextRunsOne acc k) rest

end

def svgTextRuns (body : Array Html.Node) : Array (String × Array (String × String)) :=
  svgTextRunsList #[] body.toList

/-- **One expression on one ground ships one ink, in a paragraph or a
drawing** — review INK-2's finding: a re-weighted mix, and a realized
role, shipped their repaired ink in text runs and their declared one in
picture labels on the same page. Read off `Layout.Out` (the label lines a
picture sets) and off the typed HTML tree (the label's SVG runs against
the paragraph's spans): each expression's label run carries its text
run's ink, in both artifacts; a label standing on a node's own fill is
judged by that fill, so the page's ink does not follow it there.
Invented content. -/
def oneInkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA, soft = #888888 }" ++
    "\\begin{document}\n\\textcolor{fg!60!bg}{Mixtext} and \\textcolor{soft}{Softtext}.\n\n" ++
    "\\begin{tikzpicture}\n" ++
    "\\node (a) at (0,0) {\\textcolor{fg!60!bg}{Mixlabel}};\n" ++
    "\\node (b) at (0,2) {\\textcolor{soft}{Softlabel}};\n" ++
    "\\node[fill=black, minimum width=3cm, minimum height=1cm] (c) at (0,4) " ++
    "{\\textcolor{soft}{Filllabel}};\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let (doc, _) := elabStr src
  let out := layoutOf oneFace doc
  -- The run whose own glyphs spell the word: label lines at one height
  -- would otherwise answer with a neighbour's ink.
  let pdfInk (word : String) : Option Ir.Color := out.pages.findSome? fun p =>
    p.lines.findSome? fun l => l.segs.findSome? fun s => match s with
      | .run _ c _ _ glyphs .. =>
        if hasStr (String.ofList (glyphs.toList.map (·.2))) word then some c else none
      | _ => none
  let mixDeclared : Ir.Color := ({ r := 0x23, g := 0x37, b := 0x3B } : Ir.Color).mix 60
    { r := 0xFA, g := 0xFA, b := 0xFA }
  let softDeclared : Ir.Color := { r := 0x88, g := 0x88, b := 0x88 }
  match pdfInk "Mixtext", pdfInk "Mixlabel" with
  | some text, some label =>
    t "the mix's text run is re-weighted" (text != mixDeclared)
    t "the mix's picture label ships its text run's ink in the PDF" (label == text)
  | _, _ => failures ref "one ink: no mixed text run or label in the PDF"
  match pdfInk "Softtext", pdfInk "Softlabel", pdfInk "Filllabel" with
  | some text, some label, some filled =>
    t "the role's text run is realized" (text != softDeclared)
    t "the role's picture label ships its text run's ink in the PDF" (label == text)
    t "a label on a node's fill is not given the page's ink" (filled == softDeclared)
  | _, _, _ => failures ref "one ink: no soft text run or label in the PDF"
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let spans := elemStylesList #[] body.toList
  let runs := svgTextRuns body
  let spanHas (needle ink : String) : Bool :=
    spans.any fun (txt, st) => hasStr txt needle && hasStr st ink
  let runHas (needle ink : String) : Bool :=
    runs.any fun (txt, attrs) => hasStr txt needle && attrs.any fun (_, v) => hasStr v ink
  match pdfInk "Mixtext", pdfInk "Softtext" with
  | some mix, some soft =>
    t "the HTML paragraph and the HTML label carry the mix's one ink"
      (spanHas "Mixtext" (HtmlDoc.cssColor mix) && runHas "Mixlabel" (HtmlDoc.cssColor mix))
    t "the HTML paragraph and the HTML label carry the role's one ink"
      (spanHas "Softtext" (HtmlDoc.cssColor soft) && runHas "Softlabel" (HtmlDoc.cssColor soft))
  | _, _ => failures ref "one ink: no text runs to compare the HTML against"
  -- Parked, routed to the SVG label emitter (`HtmlDoc.labelNodesOne`): a
  -- role-named label on a node's fill paints `var(--role, declared)`, and
  -- the page's realized `--role` wins there, while the PDF paints the
  -- declared ink the fill's ground keeps. The node ground owes a scope, or
  -- the label the IR's literal. A row failing in both directions: the fix
  -- fails it until the row goes.
  let filledLabelParked := true
  t "parked: an HTML label on a node's fill still reads the page's role ink"
    (runHas "Filllabel" "var(--soft" == filledLabelParked)

/-- **A node's text is inline content, so its styles reach both artifacts.**
The defect: `\textbf{…}` in a node body set in the regular weight where
lualatex sets it bold, and `\emph`, `\textit` and `\textsc` lost their
shapes the same way — the salvage read each text command as an unknown
macro, kept the word, and named the loss where no reader looks. A `\\`
inside a coloured body merged its two lines into one, in silence.

The invariant, measured at the artifact: a node's shipped runs (face,
glyphs, colour, one line per line) are the runs the same source ships as a
paragraph — a picture is not a typographic island. Read off `Layout.Out`
under a set whose four faces are four files, so the face is visible; and
off the typed HTML tree, where the label's `<text>` carries the same
presentation per character. The plain, coloured and math rows held before
the fix and are the instrument's controls. Invented content. -/
def pictureNodeStyleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Index 0 regular, 1 bold, 2 italic, 3 bold italic, in every slot; 4 is
  -- the math face, so a formula sets in it as it does in a document.
  let some fs ← serifFacesSet
    | t "the four shipped Source Serif faces and the math face load" false
  let boldIdx (i : Nat) : Bool := i == 1 || i == 3
  let italIdx (i : Nat) : Bool := i == 2 || i == 3
  let doc (inner : String) : String :=
    "\\palette{ rose = #B03060 }\\begin{document}\n" ++ inner ++ "\n\\end{document}"
  let node (body : String) : String :=
    doc ("\\begin{tikzpicture}\n\\node (a) at (0,0) {" ++ body ++ "};\n\\end{tikzpicture}")
  -- One shipped line as its runs: face, glyphs and colour, in order, with
  -- `none` where an interword space stands — a space is a gap, not a run,
  -- and a row that read only runs would pass a label that lost one.
  let runsOf (l : Layout.LineOut) :
      Array (Option (Nat × Array (Nat × Char) × Ir.Color)) :=
    l.segs.filterMap fun seg => match seg with
      | .run idx color _ _ glyphs _ _ _ _ _ => some (some (idx, glyphs, color))
      | .gap _ true => some none
      | _ => none
  let shipped (src : String) :
      Array (Array (Option (Nat × Array (Nat × Char) × Ir.Color))) :=
    let (d, _) := elabStr src
    ((bodyLines (layoutOf fs d)).filter fun l => (runsOf l).any (·.isSome)).map runsOf
  let diagsOf (src : String) : Array Diag := (elabStr src).2
  -- **The invariant row.** The node's lines are the paragraph's lines.
  let agrees (body : String) : Bool :=
    let n := shipped (node body)
    !n.isEmpty && n == shipped (doc body)
  -- The faces a source's glyphs ship in, one per non-space glyph.
  let facesOf (src : String) : Array Nat :=
    (shipped src).flatMap fun rs => rs.flatMap fun r => match r with
      | some (i, gs, _) => (gs.filter (·.2 != ' ')).map fun _ => i
      | none => #[]
  t "a plain node's runs are the paragraph's (control)" (agrees "Middle")
  t "a bold node's runs are the paragraph's" (agrees "\\textbf{Middle}")
  t "the bold node ships in the bold face, not the regular"
    (let fs' := facesOf (node "\\textbf{Middle}")
     !fs'.isEmpty && fs'.all boldIdx)
  t "an emphasised node's runs are the paragraph's" (agrees "\\emph{Middle}")
  t "the emphasised node ships in the italic face"
    (let fs' := facesOf (node "\\emph{Middle}")
     !fs'.isEmpty && fs'.all italIdx)
  t "an italic node's runs are the paragraph's" (agrees "\\textit{Middle}")
  t "a small-caps node's runs are the paragraph's" (agrees "\\textsc{Middle}")
  t "a bold word inside a node's line keeps its neighbours regular"
    (agrees "Left \\textbf{Middle} Right")
  -- A space just inside a styled group is inside the line, so it stays, as
  -- it does in a paragraph: only a line's own ends are trimmed.
  t "a space inside a styled group's edge stays, as in a paragraph"
    (agrees "Left\\textbf{ Middle}Right" && agrees "Left\\textbf{Middle }Right")
  t "a styled group at a label's ends sets as it does in a paragraph"
    (agrees "\\textbf{ Middle }")
  t "a space inside a coloured group's edge stays, as in a paragraph"
    (agrees "Left\\textcolor{rose}{ Middle}Right")
  t "a nested bold italic node ships in the bold italic face"
    (agrees "\\textbf{\\emph{Middle}}" &&
      (facesOf (node "\\textbf{\\emph{Middle}}")).all (· == 3))
  t "a coloured node's runs are the paragraph's (control)"
    (agrees "\\textcolor{rose}{Middle}")
  t "a coloured bold node, the alert shape, keeps both"
    (agrees "\\textcolor{rose}{\\textbf{Middle}}")
  t "a node's math runs are the paragraph's (control)" (agrees "$x^2$")
  -- A `\\` inside a styled or coloured body is a real break, as in TeX:
  -- two lines, each carrying the body's style.
  t "a line break inside a bold body ships two bold lines"
    (agrees "\\textbf{Pear\\\\Fig}" && (shipped (node "\\textbf{Pear\\\\Fig}")).size == 2)
  t "the spaces around a break inside a body go with the break"
    (agrees "\\textbf{Pear \\\\ Fig}" &&
      (shipped (node "\\textbf{Pear \\\\ Fig}")).size == 2)
  t "a line break inside a coloured body ships two coloured lines"
    (agrees "\\textcolor{rose}{Pear\\\\Fig}" &&
      (shipped (node "\\textcolor{rose}{Pear\\\\Fig}")).size == 2)
  -- Read as a paragraph reads it, so nothing is named.
  t "the styled nodes elaborate with nothing refused"
    (["\\textbf{Middle}", "\\emph{Middle}", "\\textit{Middle}", "\\textsc{Middle}",
      "\\textcolor{rose}{\\textbf{Middle}}", "\\textbf{Pear\\\\Fig}"].all fun b =>
      (diagsOf (node b)).all (·.severity == .note))
  -- **What the subset cannot set is named, never set plain in silence.**
  -- The floor held before the fix too; this row guards it through it.
  let (_, dsEnd) := elabStr (node "\\textbf")
  t "a text style whose argument never came is named (the floor)"
    (dsEnd.any fun d => d.code == DiagCode.W0334.code)
  -- One loss, the size's: the style itself is read, so a second W0334
  -- would be the style refused as it was before the fix.
  let (_, dsSize) := elabStr (node "Pear \\textbf{\\small Fig}")
  t "a size switch inside a styled body is named, and is the only loss"
    ((dsSize.filter fun d => d.code == DiagCode.W0334.code).size == 1)
  t "the styled word beside it still ships bold"
    ((facesOf (node "Pear \\textbf{\\small Fig}")).any boldIdx)
  -- **HTML gets the same runs.** Every character of the label's `<text>`,
  -- with the presentation the SVG gives it — the attributes of every
  -- `<tspan>` around it, innermost first.
  let svgRuns (src : String) : Array (String × Array (String × String)) :=
    let (d, _) := elabStr src
    let (_, body, _) := HtmlDoc.emitTree {} d
    svgTextRuns body
  let attrIn (env : Array (String × String)) (k : String) : Option String :=
    (env.find? (·.1 == k)).map (·.2)
  -- How CSS presents a run (CSS Fonts 4 §2.2, §2.4). The `<text>` element
  -- inherits the page's weight and shape — this page ships no faces, so
  -- CSS's initial `normal`, 400, the regular face's own weight — and every
  -- `<tspan>` around the run applies its `font-weight` and `font-style`,
  -- outermost first: `bolder` and `lighter` against the weight they meet,
  -- a keyword or a number outright, and a class the stylesheet gives a
  -- weight or a shape (`md`, `up`) as its rule. Reading only the innermost
  -- attribute took a nested `bolder` for one bold, and an `italic` inside
  -- an `italic` for the upright the PDF sets.
  let bolder (w : Nat) : Nat := if w < 350 then 400 else if w < 550 then 700 else 900
  let lighter (w : Nat) : Nat := if w < 550 then 100 else if w < 750 then 400 else 700
  let svgFace (env : Array (String × String)) : Nat × Bool :=
    env.reverse.foldl (init := (400, false)) fun (w, it) (k, v) =>
      if k == "font-weight" then
        (if v == "bolder" then bolder w else if v == "lighter" then lighter w
         else if v == "normal" then 400 else if v == "bold" then 700
         else v.toNat?.getD w, it)
      else if k == "font-style" then (w, v == "italic" || v == "oblique")
      else if k == "class" then
        let cs := v.splitOn " "
        (if cs.contains "md" then 400 else w, if cs.contains "up" then false else it)
      else (w, it)
  let svgBold (env : Array (String × String)) : Bool := 600 ≤ (svgFace env).1
  let svgItal (env : Array (String × String)) : Bool := (svgFace env).2
  -- One entry per non-space glyph, from each artifact. The PDF's is the
  -- face the glyph ships in — its own weight and slant, the descriptors
  -- CSS matches the SVG's request against — and whether it is the math
  -- face; the SVG's is what CSS computes for the run (`svgFace`).
  let pdfFaces (src : String) : Array (Char × Nat × Bool × Bool) :=
    (shipped src).flatMap fun rs => rs.flatMap fun r => match r with
      | some (i, gs, _) => (gs.filter (·.2 != ' ')).map fun (_, c) =>
        (c, (fs.get i).weight, (fs.get i).isItalic, fs.math == some i)
      | none => #[]
  let svgFaces (src : String) : Array (Char × Nat × Bool) :=
    (svgRuns src).flatMap fun (s, env) =>
      let (w, it) := svgFace env
      (s.toList.filter (· != ' ')).toArray.map fun c => (c, w, it)
  -- Glyph by glyph: the character and the weight are the PDF's, and so is
  -- the slant, except where the PDF sets the glyph in the math face: math
  -- italic is a character of its own there, so the face's slant says
  -- nothing of the glyph's shape, and the SVG sets every formula as an
  -- italic floor (`HtmlDoc.labelPiece`), the one label math has.
  let facesAgree (src : String) : Bool :=
    let p := pdfFaces src
    let h := svgFaces src
    !p.isEmpty && p.size == h.size &&
      (p.zip h).all fun ((c, w, it, m), (c', w', it')) =>
        c == c' && w == w' && (m || it == it')
  t "the SVG sets the bold node's word bold"
    (let rs := svgRuns (node "\\textbf{Middle}")
     rs.any (fun (s, env) => s == "Middle" && svgBold env))
  t "the SVG sets the emphasised node's word italic"
    ((svgRuns (node "\\emph{Middle}")).any fun (s, env) => s == "Middle" && svgItal env)
  t "the SVG gives a small-caps node the small-caps class"
    ((svgRuns (node "\\textsc{Middle}")).any fun (s, env) =>
      s == "Middle" && attrIn env "class" == some "sc")
  t "the SVG paints a coloured node's word in its palette role"
    ((svgRuns (node "\\textcolor{rose}{Middle}")).any fun (s, env) =>
      s == "Middle" && env.any fun (k, v) => k == "style" && hasStr v "var(--rose")
  t "the SVG keeps a bold word's neighbours regular (guard)"
    ((svgRuns (node "Left \\textbf{Middle} Right")).all fun (s, env) =>
      svgBold env == (s == "Middle"))
  t "a bold node's math runs are the paragraph's (control)" (agrees "\\textbf{$x$}")
  -- Agreement, not presence: the first five held on the base too, where
  -- both artifacts lost the style alike, and the presence rows above are
  -- what failed there. The last four failed at the fix's first cut, whose
  -- nested tspans could only add to what they met: emphasis inside italic
  -- stayed italic where the PDF sets it upright, `\textnormal` inside bold
  -- stayed bold, and math inside bold set bolder.
  for b in ["\\textbf{Middle}", "\\emph{Middle}", "Left \\textbf{Middle} Right",
      "\\textbf{\\emph{Middle}}", "\\textcolor{rose}{\\textbf{Middle}}",
      "\\textit{Plain \\emph{Middle}}", "\\emph{Plain \\emph{Middle}}",
      "\\textbf{Plain \\textnormal{Middle}}", "\\textbf{$x$}"] do
    t s!"per glyph, the SVG's weight and slant are the PDF's: {b}" (facesAgree (node b))
  -- **Math keeps the math face's weight.** The PDF sets a formula in the
  -- math face, which no text weight reaches, so a bold or alerted node's
  -- math is the regular math face. The first cut wrapped the floor in the
  -- enclosing style's `bolder`, and the SVG alone set it bold.
  t "math inside a bold or alerted node keeps the math face's weight in the SVG"
    (["\\textbf{$x$}", "\\textbf{\\textcolor{rose}{$x$}}",
      "\\textcolor{rose}{\\textbf{$x$}}"].all fun b =>
      let p := pdfFaces (node b)
      let h := svgFaces (node b)
      p.any (·.2.2.2) && p.size == h.size &&
        (p.zip h).all fun ((_, w, _, m), (_, w', _)) => !m || w == w')
  -- The page, not the tree: a printer that broke a `<text>` element's
  -- children onto indented lines put a space between `Left` and a bold
  -- `Middle` that the source never had, because SVG text collapses the
  -- indentation to one. The label's rendered text, tags stripped, is the
  -- label's text exactly. Guards: they hold on the base, whose labels carry
  -- no `<tspan>`, and failed on the fix's first cut.
  let stripTags (s : String) : String := Id.run do
    let mut out := ""
    let mut inTag := false
    for c in s.toList do
      if c == '<' then inTag := true
      else if c == '>' then inTag := false
      else if !inTag then out := out.push c
    return out
  let renderedLabel (src : String) (needle : String) : Option String :=
    let (d, _) := elabStr src
    let html := (HtmlDoc.emit {} d).1
    ((html.splitOn "</text>").find? (hasStr · needle)).map fun piece =>
      let afterOpen : List Char :=
        (((piece.splitOn "<text").getLast?.getD "").toList.dropWhile (· != '>')).drop 1
      stripTags (String.ofList afterOpen)
  t "a styled label's rendered SVG text adds no whitespace (guard)"
    (renderedLabel (node "Left\\textbf{Middle}") "Middle" == some "LeftMiddle")
  t "a label's spaces survive the rendering exactly (guard)"
    (renderedLabel (node "Left \\textbf{Middle} Right") "Middle" == some "Left Middle Right")

/-- **A construct outside the subset costs only itself.** Two halves of one
rule, both read off the shipped page.

A `(` where an operation would begin starts a new subpath
(`Picture.subpaths`): a pgf author writes several edges of one diagram in a
single statement — `\path (a) edge (b) (c) edge (d);` — and the evaluator
read one chain, so the `(` that opened the second edge was a construct
outside the subset and the whole statement went with it: four edges of a
real diagram, lost to one token.

And a construct that stays refused pays for itself alone: `baseline` aligns
a picture's baseline with a node's, which needs an inline picture the engine
does not have, so it is named and dropped — and the page must be the page
the same picture ships without it. -/
def pictureSubpathChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pic (body : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ body ++
    "\\end{tikzpicture}\n\\end{document}"
  let run (body : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr (pic body)
    (censusOf (coveredColorsOf doc) (layoutOf oneFace doc), ds)
  let nodes :=
    "\\node (a) {P};\\node (b) [right =of a] {Q};\n" ++
    "\\node (c) [below =of a] {R};\\node (d) [below =of b] {S};\n"
  let (c1, ds1) := run (nodes ++ "\\path (a) edge (b) (c) edge (d);\n")
  t "a two-subpath path elaborates with nothing refused"
    (ds1.all (·.severity == .note))
  t "both subpaths of one path statement ship a stroke"
    ((c1[0]?.map (·.paths == 2)).getD false)
  -- Four in one statement, the shape the deck writes.
  let (c2, ds2) := run (nodes ++
    "\\path (a) edge (b) (c) edge (d) (a) edge (c) (b) edge (d);\n")
  t "four subpaths in one statement ship four strokes"
    (ds2.all (·.severity == .note) && (c2[0]?.map (·.paths == 4)).getD false)
  -- The option bracket belongs to the statement, so it reaches every slice.
  let (c3, _) := run (nodes ++
    "\\path[draw=blue] (a) edge (b) (c) edge (d);\n")
  t "the statement's option bracket rides on every subpath"
    ((c3[0]?.map fun p =>
      p.pathStrokes.size == 2 &&
        p.pathStrokes.all fun (col, _) => col == { r := 0, g := 0, b := 255 }).getD false)
  -- A `--` chain is one path, not two: only a `(` standing where an
  -- operation would begin is a boundary.
  let (c4, ds4) := run "\\draw (0,0) -- (1,0) -- (2,0);\n"
  t "a chained line stays one path"
    (ds4.all (·.severity == .note) && (c4[0]?.map (·.paths == 1)).getD false)
  let (c5, ds5) := run "\\draw (0,0) -- (1,0) (2,0) -- (3,0);\n"
  t "two coordinate chains in one draw ship two paths"
    (ds5.all (·.severity == .note) && (c5[0]?.map (·.paths == 2)).getD false)
  -- **A path that ends at a coordinate is a move, not an error.** The split
  -- turns such a tail into its own slice, and a one-anchor slice is what the
  -- evaluator refuses for want of a second endpoint — so before this row a
  -- legal statement became a fatal E0333 and the document wrote nothing. An
  -- adversarial review found it; the rule is that the split may turn a
  -- refusal into neither silence nor an error.
  let (c8, ds8) := run "\\draw (0,0) -- (1,0) (2,0);\n"
  t "a path that ends at a coordinate draws its chain and does not fail"
    (ds8.all (·.severity == .note) && (c8[0]?.map (·.paths == 1)).getD false)
  let (c9, ds9) := run
    "\\node (a) {P};\\node (b) [right =of a] {Q};\\path (a) edge (b) (a);\n"
  t "a trailing move on a node path costs neither the edge nor the labels"
    (ds9.all (·.severity == .note) && (c9[0]?.map (·.paths == 1)).getD false &&
      pageHas c9 0 "P" && pageHas c9 0 "Q")
  -- A nested paren inside a coordinate is not a boundary either.
  let (c6, ds6) := run "\\draw (max(1,2),0) -- (3,0);\n"
  t "a nested paren inside a coordinate is not a subpath boundary"
    (ds6.all (·.severity == .note) && (c6[0]?.map (·.paths == 1)).getD false)
  -- A statement the split leaves malformed still reaches the evaluator,
  -- which names it: the split may not turn a refusal into silence. Under
  -- the declared refusal, so the subset's own diagnostics stand rather than
  -- the boundary's note.
  let (_, ds7) := elabStr ("\\pictures{ tool = none }" ++ pic "\\draw (0,0);\n")
  t "a path with one endpoint is still named, not silently dropped"
    (ds7.any fun d => d.code == "E0333")
  -- The other half of the same rule, for a construct that stays refused:
  -- `baseline` aligns a picture's baseline with a node's, which needs an
  -- inline picture the engine does not have, so it is named and dropped —
  -- and the drop must cost *only* that alignment. Stated as an equality
  -- between the shipped pages of the same picture with and without the
  -- option, since only the page can say the drop moved nothing.
  let bl := "\\node (c) {P};\\node (d) [right =of c] {Q};\\path (c) edge (d);\n"
  let (withOpt, dsb) := run ("[baseline={(c.base)}]\n" ++ bl)
  let (without, _) := run bl
  t "the dropped baseline option is named at the picture"
    (dsb.any fun d => d.code == "W0334" && hasStr d.message "baseline")
  t "dropping the baseline option moves nothing on the page"
    (withOpt.size == without.size &&
      (match withOpt[0]?, without[0]? with
       | some a, some b =>
         a.paths == b.paths && a.pathBoxes == b.pathBoxes &&
           a.lines.map (fun l => (l.text, l.x, l.y, l.size)) ==
             b.lines.map fun l => (l.text, l.x, l.y, l.size)
       | _, _ => false))

/-- **A picture's box contains its ink** (`Ir.Pic.Picture.inkBbox_covers`).

The defect: a label's declared box is its anchor point, so a diagram of
node labels reserved the hull of their *centres*. Two silent losses
followed. The reserved box was narrower than the text by half a label at
each edge, so the leftmost label's glyphs were painted at negative page
x — outside the media box, the run's first characters simply gone from the
artifact, with no clip path and no diagnostic. And the overrun check reads
that same box, so it measured a box that fits while ink left the page.

Read off the shipped lines, never a box the test computes itself: the
claim is about where glyphs landed. `hmargin` is the picture's own left
edge in a frame, so "the leftmost label's ink begins there" states the
containment tightly in both directions — the box neither cuts the ink nor
reserves space the ink does not use.

What this does *not* fix is the separation: `right =of` puts one node
distance between node *centres* because no body's extent is measured at
elaboration, so labels in a row still overlap. The extent a node should
register, and the separation it buys, are stated and proved on the IR
(`Ir.Pic.nodeExtent`, `nodeExtent_covers`, `nodeExtent_separates`, pinned by
`nodeExtentChecks`); what is left is the walk reading that site and the
driver supplying a measurement, which is `nodeExtent_covers`, owed and
staged. The last rows below are the honest floor meanwhile: a diagram whose
ink leaves the text area is named (W0335), and one whose labels collide
inside a correct box is named too (W0336) — the case the box cannot show,
because the box holds both labels and is right to. -/
def pictureInkBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let frame (body : String) : String :=
    "\\documentclass{slides}\\begin{document}\n\\begin{frame}{A Frame}\n" ++
    "\\begin{tikzpicture}\n" ++ body ++ "\\end{tikzpicture}\n\\end{frame}\n\\end{document}"
  -- A row of `right =of` nodes, each label wide enough that half of it
  -- overhangs the anchor it is centred on.
  let row (n : Nat) : String := Id.run do
    let mut s := "\\node (n0) {A Very Wide Label Indeed That Runs On};\n"
    for k in [1:n] do
      s := s ++ "\\node (n" ++ toString k ++ ") [right =of n" ++ toString (k - 1) ++
        "] {Another Very Wide Label Here};\n"
    return s
  -- The picture's label lines and the page geometry they are judged
  -- against: what the shipped artifact carries, and nothing else.
  let shipped (src : String) : Array CensusLine × Dim.Sp × Dim.Sp × Array Diag :=
    let (doc, _) := elabStr src
    let out := layoutOf oneFace doc
    let geom := Layout.Geom.ofPage doc.page
    let c := censusOf (coveredColorsOf doc) out
    let labels := (c[0]?.map fun p => p.lines.filter fun l =>
      !l.furniture && !l.text.isEmpty && l.text != "A Frame").getD #[]
    (labels, geom.hmargin, geom.textWidth, out.diags)
  let (three, hmargin, textW, threeDs) := shipped (frame (row 3))
  t "a three-node row ships one label line per node"
    (three.size == 3)
  -- The headline measurement: `pdftotext -bbox` reported a negative xMin
  -- for the first run of such a row, and the characters left of zero were
  -- simply absent from the page.
  t "no node label is painted left of the page"
    (three.all fun l => 0 ≤ l.x)
  -- Tight in both directions: the reserved box's left edge *is* the ink's
  -- left edge, so the box neither cuts the leftmost label nor reserves
  -- space no glyph uses.
  t "the picture's box begins exactly where its leftmost label's ink begins"
    (three.foldl (fun a l => min a l.x) textW == hmargin)
  t "a row whose ink fits the text area is not named"
    (!threeDs.any fun d => d.code == "W0335")
  -- The honest floor for the half the engine cannot fix: a diagram whose
  -- measured ink leaves the text area says so. Before the box was
  -- measured this was silent — the hull of eight centres is one node
  -- distance apart seven times over, comfortably inside the measure,
  -- while the labels ran past the trim edge.
  let (eight, _, _, eightDs) := shipped (frame (row 8))
  t "an eight-node row still ships every label"
    (eight.size == 8)
  t "no label of the overrunning row is painted left of the page"
    (eight.all fun l => 0 ≤ l.x)
  t "a row whose measured ink leaves the text area is named"
    (eightDs.any fun d => d.code == "W0335")
  -- The placement regression guard: widening the box may not move a node
  -- relative to the node it was placed against. Declared minimums are the
  -- case the separation is exact in, so the border-to-border distance is
  -- the fact to pin.
  let declared :=
    "\\tikzset{node distance = 1cm and 1cm}\n\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node (aa) [draw, minimum size=6mm] {Pear};\n" ++
    "\\node (bb) [draw, minimum size=6mm, right =of aa] {Plum};\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let (dDoc, _) := elabStr declared
  let dc := censusOf (coveredColorsOf dDoc) (layoutOf oneFace dDoc)
  let dbox (k : Nat) : Option (Dim.Sp × Dim.Sp) :=
    (dc[0]?.bind (·.pathBoxes[k]?)).map fun (x, _, w, _) => (x + w / 2, w / 2)
  t "measuring the box leaves a declared border-to-border separation exact"
    (match dbox 0, dbox 1 with
     | some (ax, aw), some (bx, bw) => bx - ax == Dim.mm 10 + aw + bw
     | _, _ => false)
  -- **The collision the box cannot show.** A correct box holds two labels
  -- that overlap each other, so the overrun row above is silent on a
  -- diagram whose text collides inside the measure — which is the state
  -- every unmeasured `right =of` row is in. Named at the face, the one
  -- place the comparison can be made, and measured rather than guessed.
  let layoutDiags (src : String) : Array Diag :=
    let (doc, _) := elabStr src
    (layoutOf oneFace doc).diags
  let tight := layoutDiags (frame (row 3))
  t "a row whose labels overlap is named"
    (tight.any fun d => d.code == "W0336")
  -- The floor: a diagram whose labels clear one another says nothing.
  -- Without this row the fact passes under a check that fires always.
  let clear := layoutDiags (frame
    ("\\node (a) {x};\n\\node (b) [right =of a] {y};\n"))
  t "a row whose labels clear one another is not named"
    (!clear.any fun d => d.code == "W0336")
  t "a picture of one label is not named"
    (!(layoutDiags (frame "\\node (a) {A Very Wide Label Indeed That Runs On};\n")).any
      fun d => d.code == "W0336")
  -- Two labels of one node's own body stack rather than collide: `\\`
  -- opens a real line, and a multi-line label may not read as an overlap.
  t "the two lines of one node's label are not an overlap"
    (!(layoutDiags (frame "\\node (a) {A Wide First Line\\\\A Wide Second Line};\n")).any
      fun d => d.code == "W0336")

/-- **A conditional is a statement with two branches, and one gap costs the
conditional rather than the diagram** (`Picture.relTrichotomy_exact`,
`Picture.condFloor_accounts`, `Picture.unreachedName_accounts`).

Three defects in one construct. A conditional opener was an unknown control
word, recovered by skipping *to the next `;`* — so it swallowed the first
statement of its own first branch, and then every statement of **both**
branches after that was drawn. That is wrong ink, not missing ink. The node
the swallowed statement declared never registered, so every edge naming it
was refused — and refused as `E0333`, a name nothing declared, which is the
document's fault and not the engine's: one unreadable construct read as six
separate errors, five of them naming nodes the author had written.

So: every `\if…` control word opens a conditional (TeX's own convention,
what `\newif` builds on), its branches are collected separately, the
arithmetic tests are computed, and the rest ship the branch that draws with
the assumption named. A name declared inside a branch that did not run is a
`W0334` naming the mechanism, not an `E0333` naming the node.

Read off the shipped paths and lines: which branch ran is visible only as
ink. Invented content throughout. -/
def pictureCondChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let pic (body : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ body ++
    "\\end{tikzpicture}\n\\end{document}"
  let nodes (a b : String) : String :=
    "\\node (nn) [draw, minimum size=8mm] at (0,0) {" ++ a ++ "};\n" ++
    "\\node (mm) [draw, minimum size=8mm] at (3,0) {" ++ b ++ "};\n"
  -- A computable test: one branch runs and the other's ink is nowhere on
  -- the page. Both branches hold two statements, which is exactly what the
  -- old recovery drew from both.
  let both (k : String) : String :=
    "\\pgfmathsetmacro{\\kk}{" ++ k ++ "}\n\\ifnum\\kk=1\n" ++
    nodes "Pear" "Plum" ++ "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n"
  let (_, ds) := elabStr (pic (both "1"))
  t "a picture with a computable conditional elaborates with nothing refused"
    (ds.all (·.severity == .note))
  let yes := censusSrc (pic (both "1"))
  let no := censusSrc (pic (both "2"))
  t "the taken branch ships its ink"
    (pageHas yes 0 "Pear" && pageHas yes 0 "Plum")
  t "the branch not taken ships none of its ink"
    (!pageHas yes 0 "Fig" && !pageHas yes 0 "Quince")
  t "a false test takes the other branch, and only it"
    (pageHas no 0 "Fig" && pageHas no 0 "Quince" &&
      !pageHas no 0 "Pear" && !pageHas no 0 "Plum")
  t "exactly one branch's outlines ship, not both"
    ((yes[0]?.map (·.paths == 2)).getD false &&
     (no[0]?.map (·.paths == 2)).getD false)
  t "no boundary box stands where a conditional picture is"
    ((yes[0]?.map (·.images == 0)).getD false)
  -- `<` and `>` as well as `=`, so the relation table is not one arm wide.
  let lt := censusSrc (pic
    ("\\pgfmathsetmacro{\\kk}{1}\n\\ifnum\\kk<5\n" ++ nodes "Pear" "Plum" ++
     "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n"))
  let gt := censusSrc (pic
    ("\\pgfmathsetmacro{\\kk}{9}\n\\ifnum\\kk>5\n" ++ nodes "Pear" "Plum" ++
     "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n"))
  t "'<' and '>' read as themselves"
    (pageHas lt 0 "Pear" && !pageHas lt 0 "Fig" &&
     pageHas gt 0 "Pear" && !pageHas gt 0 "Fig")
  -- An uncomputable test: the floor ships the branch that draws, the
  -- assumption is named, and nothing from the other branch appears. The
  -- test names a macro this walk has no binding for, which is the state a
  -- document's own macro is in here.
  let opaqueSrc :=
    pic ("\\ifnum\\notamacro=1\n" ++ nodes "Pear" "Plum" ++
         "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n")
  let (_, opaqueDs) := elabStr opaqueSrc
  t "a test the walk cannot compute is named, and says which branch drew"
    (opaqueDs.any fun d => d.code == "W0334" && hasStr d.message "notamacro" &&
      hasStr d.message "draws")
  let guarded := censusSrc opaqueSrc
  t "an unreadable test still ships a branch, and only one"
    (pageHas guarded 0 "Pear" && !pageHas guarded 0 "Fig" &&
      (guarded[0]?.map (·.paths == 2)).getD false)
  -- Any `\if…` control word opens a conditional, not just the arithmetic
  -- ones: TeX's own convention, and what `\newif` mints. A test about TeX's
  -- run-time state the walk cannot read reaches it and is named by its own
  -- spelling; one the document decides (`\ifodd` of a literal) is decided
  -- before the walk reads the picture, and named there.
  let voidSrc := pic
    ("\\ifvoid0\n" ++ nodes "Pear" "Plum" ++ "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n")
  let (_, voidDs) := elabStr voidSrc
  t "an opener the subset cannot compute is named by its own spelling"
    (voidDs.any fun d => d.code == "W0334" && hasStr d.message "ifvoid")
  -- The four mode tests read a mode that is fixed at a picture's
  -- statements: pgf sets the picture in a horizontal box, so `\ifhmode`
  -- and `\ifinner` hold and `\ifmmode` and `\ifvmode` fail (lualatex draws
  -- exactly those branches). A mode test takes no test tokens, so the
  -- branch opens at once: its first statement is the branch's, not the
  -- test's.
  let modeOf (h : String) : Array CensusPage := censusSrc (pic
    ("\\" ++ h ++ "\n" ++ nodes "Pear" "Plum" ++ "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n"))
  let thenDrawn (c : Array CensusPage) : Bool :=
    pageHas c 0 "Pear" && pageHas c 0 "Plum" && !pageHas c 0 "Fig" && !pageHas c 0 "Quince"
  let elseDrawn (c : Array CensusPage) : Bool :=
    pageHas c 0 "Fig" && pageHas c 0 "Quince" && !pageHas c 0 "Pear" && !pageHas c 0 "Plum"
  t "a head that takes no test keeps its branch's first statement"
    (thenDrawn (modeOf "ifhmode"))
  t "the mode tests at a picture's statements take the branches TeX takes"
    (thenDrawn (modeOf "ifinner") && elseDrawn (modeOf "ifmmode") && elseDrawn (modeOf "ifvmode"))
  t "a mode test's decision is named"
    ((elabStr (pic ("\\ifmmode\n" ++ nodes "Pear" "Plum" ++ "\\else\n" ++
      nodes "Fig" "Quince" ++ "\\fi\n"))).2.any fun d => d.code == "N0114" && d.subject.isSome)
  let oddSrc := pic
    ("\\ifodd 3\n" ++ nodes "Pear" "Plum" ++ "\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n")
  let odd := censusSrc oddSrc
  t "an opener the document decides ships the branch it takes, named"
    (pageHas odd 0 "Pear" && !pageHas odd 0 "Fig" &&
      (elabStr oddSrc).2.any fun d => d.code == "N0114" && d.subject.isSome)
  -- And the branch that draws, not simply the first: a guard is as often
  -- written with the content in the `\else`.
  let elseOnly := censusSrc (pic
    ("\\ifnum\\notamacro=1\n\\else\n" ++ nodes "Fig" "Quince" ++ "\\fi\n"))
  t "where the first branch is empty the floor ships the other"
    (pageHas elseOnly 0 "Fig" && (elseOnly[0]?.map (·.paths == 2)).getD false)
  -- The cascade, contained: a name declared only in the branch the floor
  -- did *not* take is named by the *mechanism*, at warning strength — not
  -- by the node, as an error, per edge.
  let cascadeSrc := pic
    ("\\node (zz) [draw, minimum size=8mm] at (6,0) {Keep};\n" ++
     "\\ifnum\\notamacro=1\n" ++
     "\\node (shown) [draw, minimum size=8mm] at (0,0) {Pear};\n\\else\n" ++
     "\\node (hidden) [draw, minimum size=8mm] at (3,0) {Fig};\n\\fi\n" ++
     "\\draw (hidden) -- (zz);\n")
  let (_, cascadeDs) := elabStr cascadeSrc
  t "a name declared in a branch that did not run is refused at warning strength"
    (cascadeDs.any fun d => d.code == "W0334" && hasStr d.message "hidden")
  t "and not as a name nothing declared"
    (!cascadeDs.any fun d => d.code == "E0333" && hasStr d.message "hidden")
  -- The floor under it: with no gap anywhere, a name nothing declared is
  -- still the document's own error. Without this row the demotion above
  -- would pass under a gate that always fires.
  let (_, plainDs) := elabStr (pic
    ("\\node (zz) [draw, minimum size=8mm] at (6,0) {Keep};\n" ++
     "\\draw (nowhere) -- (zz);\n"))
  t "with no gap in the picture, a name nothing declared stays an error"
    (plainDs.any fun d => d.code == "E0333" && hasStr d.message "nowhere")
  -- An unbalanced conditional may not strand the statements its branch
  -- collected: they are drained at the end of the body.
  let unclosed := censusSrc (pic
    ("\\ifnum\\notamacro=1\n" ++ nodes "Pear" "Plum"))
  t "a conditional never closed still ships what its branch read"
    (pageHas unclosed 0 "Pear" && (unclosed[0]?.map (·.paths == 2)).getD false)

/-- **A node's options are its brackets', wherever the brackets stand**
(`Picture.prologue_swap_agree`, `Picture.prologue_brackets_covers`). pgf
reads `[keys]`, `(name)` and `at (coord)` in any order and any number of
times up to the `{text}`; the walk read one bracket, only before `at`. So
`\node[keys] (n) [keys] {text}` — two brackets, which real TikZ compiles
without complaint — reached the body arm with a `[` where a `{` was
expected and was refused for *needing a body it had written*, and the node
never registered its name, so every edge touching it went too.

Read off the shipped path spans and boxes: which keys a node honoured is
visible only as the outline it drew and where it drew it. Invented content
throughout. -/
def pictureNodePrologueChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let pic (body : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ body ++
    "\\end{tikzpicture}\n\\end{document}"
  -- Two brackets on one node: the width comes from the first, the height
  -- and the outline from the second, so a span of both is the proof that
  -- neither was dropped.
  let twoBrackets := "\\node[minimum width=15mm] (nn) [minimum height=6mm, draw] {Quince};\n"
  let (_, ds) := elabStr (pic twoBrackets)
  t "a node carrying two option brackets elaborates with nothing refused"
    (ds.all (·.severity == .note))
  let two := censusSrc (pic twoBrackets)
  -- Stated as an agreement rather than against an absolute length: one
  -- bracket carrying both keys and two brackets carrying one each must
  -- ship the same outline, which is the whole claim and bakes in no
  -- rounding of the engine's own dimension reading.
  let oneBracket := censusSrc (pic
    "\\node[minimum width=15mm, minimum height=6mm, draw] (nn) {Quince};\n")
  t "both of a node's option brackets reach its outline"
    ((two[0]?.map (·.pathSpans)) == (oneBracket[0]?.map (·.pathSpans)) &&
      (two[0]?.map (·.paths == 1)).getD false)
  t "no boundary box stands where the two-bracket picture is"
    ((two[0]?.map (·.images == 0)).getD false)
  -- The three prologue parts in every order that puts the name and the
  -- bracket either side of `at`: the page must not know which was written.
  let orders : List String :=
    [ "\\node[draw, minimum size=8mm] (nn) at (2,0) {Quince};\n"
    , "\\node (nn) [draw, minimum size=8mm] at (2,0) {Quince};\n"
    , "\\node (nn) at (2,0) [draw, minimum size=8mm] {Quince};\n"
    , "\\node[draw] at (2,0) (nn) [minimum size=8mm] {Quince};\n"
    , "\\node at (2,0) [draw, minimum size=8mm] (nn) {Quince};\n" ]
  let boxesOf (body : String) : Option (Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)) :=
    (censusSrc (pic body))[0]?.map (·.pathBoxes)
  let first := boxesOf (orders.headD "")
  t "a node's outline ships whatever order its prologue was written in"
    ((first.map (·.size == 1)).getD false &&
      orders.all fun o => boxesOf o == first)
  -- The name registers from any position, which is what an edge reads.
  let edged := censusSrc (pic
    ("\\node[draw, minimum size=8mm] at (0,0) (aa) [thick] {Pear};\n" ++
     "\\node (bb) at (3,0) [draw, minimum size=8mm] {Plum};\n" ++
     "\\draw (aa) -- (bb);\n"))
  t "a node names itself from any prologue position, so an edge to it draws"
    ((edged[0]?.map (·.paths == 3)).getD false)
  -- A bracket that never closes is still the node's loss, named. A second
  -- drawn node stands beside it so the picture ships shapes: with none the
  -- whole picture routes to the boundary and the engine's own refusal is
  -- not what the reader gets.
  let standby := "\\node (zz) [draw, minimum size=8mm] at (4,0) {Plum};\n"
  let (_, openDs) := elabStr (pic ("\\node (nn) [draw {Quince};\n" ++ standby))
  t "an option bracket that misses its ']' is refused"
    (openDs.any fun d => d.code == "E0333")
  -- And a node with no body at all stays refused: pgf rejects that too
  -- ("a node must have a (possibly empty) label text"), so the engine's
  -- error is the input's, not a gap in the subset.
  let (_, noBody) := elabStr (pic ("\\node (nn) [draw, minimum size=8mm] ;\n" ++ standby))
  t "a node with no body at all is still refused"
    (noBody.any fun d => d.code == "E0333")
  -- Empty braces *are* a body, and ink nothing: pgf's "possibly empty"
  -- label. Stated against the same node carrying a word, so the outline is
  -- the constant and the text the difference.
  let empty := censusSrc (pic "\\node (nn) [draw, minimum size=8mm] {};\n")
  let worded := censusSrc (pic "\\node (nn) [draw, minimum size=8mm] {Quince};\n")
  t "empty braces are a body: the outline ships and inks no text"
    ((empty[0]?.map (·.pathSpans)) == (worded[0]?.map (·.pathSpans)) &&
      pageHas worded 0 "Quince" && !pageHas empty 0 "Quince")

/-- **A named anchor on a node resolves, and lands on that node's own
border** (`Picture.anchorPoint_between`, `Picture.anchorPoint_corners_exact`).
The defect: `(n.west)` and its siblings — pgf's core positioning
vocabulary, the `rectangle` shape's own `\anchor` declarations — were read
as a node name nothing had declared, so *every* edge written against an
anchor was refused by a name that was never a name. One diagram's three
edge sets went with them.

Read off the shipped path boxes, never an IR dump: an anchor is entirely a
claim about where a segment starts, and only the page can say. The edges
below run between two nodes whose extents the page also carries, so each
row is the anchor's arithmetic against the borders that shipped rather than
against a baked-in number.

An anchor is a *point*, not a border to shorten toward: pgf uses the named
anchor exactly, which is why an anchored edge reaches further than the same
edge written `(a) -- (b)`. Invented content throughout. -/
def pictureAnchorChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let pic (body : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ body ++
    "\\end{tikzpicture}\n\\end{document}"
  -- Two drawn nodes and one edge between anchors of them. The nodes ship
  -- first, so the edge is the third path.
  let two (endA endB : String) : String :=
    "\\node (aa) [draw, minimum size=8mm] at (0,0) {Pear};\n" ++
    "\\node (bb) [draw, minimum size=8mm] at (4,0) {Plum};\n" ++
    "\\draw (" ++ endA ++ ") -- (" ++ endB ++ ");\n"
  let box (c : Array CensusPage) (k : Nat) :
      Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    c[0]?.bind (·.pathBoxes[k]?)
  let (_, ds) := elabStr (pic (two "aa.east" "bb.west"))
  t "an edge between two named anchors elaborates with nothing refused"
    (ds.all (·.severity == .note))
  let side := censusSrc (pic (two "aa.east" "bb.west"))
  t "two node outlines and the anchored edge ship as page paths"
    ((side[0]?.map (·.paths == 3)).getD false)
  t "no boundary box stands where the anchored picture is"
    ((side[0]?.map (·.images == 0)).getD false)
  -- `east` is exactly the right border, `west` exactly the left: the edge
  -- starts where the first box ends and stops where the second begins.
  t "'east' and 'west' put the edge exactly between the two borders"
    (match box side 0, box side 1, box side 2 with
     | some (ax, ay, aw, ah), some (bx, _, _, _), some (ex, ey, ew, eh) =>
       ex == ax + aw && ex + ew == bx && eh == 0 && ey == ay + ah / 2
     | _, _, _ => false)
  -- A corner is exactly its two sides, on the page: `south east` stands at
  -- the east border and the south one at once.
  let corner := censusSrc (pic (two "aa.south east" "bb.north west"))
  t "a corner anchor stands at both of its sides"
    (match box corner 0, box corner 1, box corner 2 with
     | some (ax, ay, aw, _), some (bx, byy, _, bh), some (ex, ey, ew, eh) =>
       ex == ax + aw && ey == ay && ex + ew == bx && ey + eh == byy + bh
     | _, _, _ => false)
  -- pgf declares the corner spelled with a space; an endpoint's tokens are
  -- space-filtered before the name is joined, so both spellings are one
  -- string by the time they are looked up. The page must not know which
  -- was written.
  let tight := censusSrc (pic (two "aa.southeast" "bb.northwest"))
  t "the space-free spelling of a corner is the same anchor"
    ((corner[0]?.map (·.paths == 3)).getD false &&
     (corner[0]?.map (·.pathBoxes)) == (tight[0]?.map (·.pathBoxes)))
  -- An anchor is used exactly, with no shortening toward the far endpoint:
  -- the same edge written by bare name anchors on the border *facing* the
  -- other node, which for `west` on the left node is the near side.
  let bare := censusSrc (pic (two "aa" "bb"))
  t "an anchored endpoint is the declared point, not a border shortened toward the other"
    (match box side 2, box bare 2 with
     | some (_, _, ew, _), some (_, _, bw, _) => ew == bw
     | _, _ => false)
  -- `base` is the label's own baseline, which stands inside the node's own
  -- border wherever the face puts it (`anchorPoint_between`, projected onto
  -- the page). How far below the centre it falls is the *measurement*, and
  -- this walk's metric is a parameter — under one that answers nothing the
  -- baseline is the centre, which is why the row pins containment and not
  -- an offset.
  let base := censusSrc (pic (two "aa.base" "bb.base"))
  t "a 'base'-anchored edge ships"
    ((base[0]?.map (·.paths == 3)).getD false)
  t "'base' stands inside the node's own border"
    (match box base 0, box base 2 with
     | some (_, ay, _, ah), some (_, ey, _, _) => ay ≤ ey && ey ≤ ay + ah
     | _, _ => false)
  -- An anchor this subset has no measurement for is named, and costs its
  -- own edge: `mid` is half an ex above the baseline and an ex is the
  -- face's, which the picture walk cannot ask for.
  let (_, midDs) := elabStr (pic (two "aa.mid" "bb.mid"))
  t "an anchor outside the subset is named by its own spelling"
    (midDs.any fun d => d.code == "W0334" && hasStr d.message "mid")
  -- A name no node carries is still refused, and by the *node's* name
  -- rather than by the anchored spelling: the two refusals are different
  -- facts and the message says which.
  let (_, gone) := elabStr (pic (two "aa.east" "zz.west"))
  t "an anchor on a name no node carries is refused by that name"
    (gone.any fun d => d.code == "E0333" && hasStr d.message "zz" &&
      !hasStr d.message "zz.west")

/-- A node's label sets in the face the body sets in: a picture is not its
own typographic island (`Picture.labelFace_agree`). The defect this pins is
not a slot the engine chose wrongly — it is a picture that drew nothing
natively and went to the boundary, where the external tool's own default
roman drew the node text while the document was set in another family. The
fact is stated as an equality between the two shipped faces rather than
against a slot number, so it still says what it means if the body moves. -/
def pictureLabelFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (n : String) : IO (Option Font.Font) := do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    return (Font.parse (← IO.FS.readBinFile p)).toOption
  let some roman ← load "SourceSerifPro-Regular.otf" | return ()
  let some sans ← load "FiraSans-Regular.otf" | return ()
  let fs := twoSlotOf roman sans
  let src :=
    "\\begin{document}\nA plain body reading.\n\n" ++
    "\\begin{tikzpicture}\n\\node (aa) {Quince};\n\\end{tikzpicture}\n\\end{document}"
  let (doc, ds) := elabStr src
  let c := censusOf (coveredColorsOf doc) (layoutOf fs doc)
  t "the label-face document elaborates with nothing refused"
    (ds.all (·.severity == .note))
  t "no boundary box stands where the label-face picture is"
    ((c[0]?.map (·.images == 0)).getD false)
  let facesOf (needle : String) : Array Nat :=
    (c[0]?.map fun p =>
      (p.lines.filter fun l => hasStr l.text needle).flatMap (·.runFonts)).getD #[]
  let bodyFaces := facesOf "plain body"
  let labelFaces := facesOf "Quince"
  t "the body and the node label both ship ink"
    (!bodyFaces.isEmpty && !labelFaces.isEmpty)
  t "the node label sets in the face the body sets in"
    (labelFaces.all fun f => bodyFaces.contains f)

/-- **`auto` puts an edge's label beside the path, not on it.** pgf's
automatic placement (TikZ manual §17.8, the `auto` and `swap`/`'` keys):
the in-path node stands on the left of the path's own direction, `swap`
takes the other side, and `auto=left`/`auto=right` name it outright. The
engine dropped the key, so the label kept the `center` alignment a label
with no placement takes, sat on the segment's midpoint, and the line was
stroked straight through it — "GR is on the line instead of right above".

`auto` is read at every level pgf reads it at (the document's `\tikzset`,
the picture's bracket, `every path`, the statement's own), because that is
where a deck declares it once; a label's own `above`/`below`/`left`/`right`
still wins, as every inner setting does.

Read off `Layout.Out`: whether a label clears its line is a fact about
where the shipped ink stands, and only the page can say it.
`Picture.autoAlign_mem` is the invariant. Invented content. -/
def pictureAutoLabelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  -- One edge with an in-path label at its middle. The edge is the only
  -- path, and the label's is the only text line.
  let pic (pre pathOpts labelOpts endPt : String) : String :=
    pre ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\draw[" ++ pathOpts ++ "] (0, 0) -- node[" ++ labelOpts ++ "] {Kappa} " ++
    endPt ++ ";\n\\end{tikzpicture}\n\\end{document}"
  -- Where the label's baseline stands *relative to the shipped edge*. The
  -- picture's own box grows toward whichever side the label took, so the
  -- page positions of both move together and only their difference is a
  -- fact about the placement.
  let offset (pre pathOpts labelOpts endPt : String) : Option Dim.Sp :=
    let (doc, _) := elabStr (pic pre pathOpts labelOpts endPt)
    let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
    match (c[0]?.bind (·.pathBoxes[0]?)),
          (c[0]?.bind fun p => (p.lines.find? fun l => hasStr l.text "Kappa")) with
    | some (_, ey, _, _), some l => some (l.y - ey)
    | _, _ => none
  let horiz (pre pathOpts labelOpts : String) : Option Dim.Sp :=
    offset pre pathOpts labelOpts "(4, 0)"
  -- The references: `above` and `below` are placements the engine already
  -- shipped and the suite already trusts, so `auto` is pinned against them
  -- rather than against a sign convention this row would have to assume.
  let above := horiz "" "" "above"
  let below := horiz "" "" "below"
  let onLine := horiz "" "" ""
  let (_, ds) := elabStr (pic "" "auto" "" "(4, 0)")
  t "an 'auto' edge label elaborates with nothing refused"
    (ds.all (·.severity == .note))
  t "'auto' is no longer named as a dropped key"
    (!ds.any fun d => d.code == DiagCode.W0334.code && hasStr d.message "auto")
  -- The three references are three different places, so an equality against
  -- one of them says something.
  t "on the line, above it and below it are three different placements"
    (above.isSome && above != below && above != onLine && below != onLine)
  -- The defect: with no `auto` the label is centred on the segment's
  -- midpoint and the stroke runs through it.
  t "a label with no placement and no 'auto' is centred on the line"
    (horiz "" "" "" == onLine)
  t "'auto' on a left-to-right edge places the label as 'above' does"
    (horiz "" "auto" "" == above)
  t "'swap' takes the other side, as 'below' does"
    (horiz "" "auto, swap" "" == below)
  t "the ' shorthand is 'swap'"
    (horiz "" "auto, '" "" == below)
  t "'auto=right' is 'auto, swap'"
    (horiz "" "auto=right" "" == below)
  t "'auto=left' is plain 'auto'"
    (horiz "" "auto=left" "" == above)
  t "'auto=false' leaves the label on the line"
    (horiz "" "auto=false" "" == onLine)
  -- Declared once for the document, as a deck declares it: the outermost
  -- bracket reaches a path that carries none of its own.
  t "'auto' declared for the document reaches an edge that declares none"
    (horiz "\\tikzset{auto}\n" "" "" == above)
  t "'auto' declared by 'every path' reaches it too"
    (horiz "\\tikzset{every path/.style={auto}}\n" "" "" == above)
  t "'auto' declared for the picture reaches its edges"
    (offset "" "" "" "(4, 0)" != above &&
     (let src := "\\begin{document}\n\\begin{tikzpicture}[auto]\n" ++
        "\\draw (0, 0) -- node {Kappa} (4, 0);\n" ++
        "\\end{tikzpicture}\n\\end{document}"
      let (doc, _) := elabStr src
      let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
      (match (c[0]?.bind (·.pathBoxes[0]?)),
             (c[0]?.bind fun p => (p.lines.find? fun l => hasStr l.text "Kappa")) with
       | some (_, ey, _, _), some l => some (l.y - ey)
       | _, _ => none) == above))
  -- The label's own placement still wins over the computed side, as every
  -- inner setting does.
  t "a label's own placement beats the side 'auto' computed"
    (horiz "" "auto" "below" == below)
  -- A vertical edge takes the other axis: the left of an upward path is
  -- toward smaller x, so the label stands left of the line — which is what
  -- the `left` placement does, and it is the reference again.
  let vertX (pathOpts labelOpts : String) : Option Dim.Sp :=
    let src := "\\begin{document}\n\\begin{tikzpicture}\n" ++
      "\\draw[" ++ pathOpts ++ "] (2, 0) -- node[" ++ labelOpts ++
      "] {Kappa} (2, 4);\n\\end{tikzpicture}\n\\end{document}"
    let (doc, _) := elabStr src
    let c := censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
    match (c[0]?.bind (·.pathBoxes[0]?)),
          (c[0]?.bind fun p => (p.lines.find? fun l => hasStr l.text "Kappa")) with
    | some (ex, _, _, _), some l => some (l.x - ex)
    | _, _ => none
  t "an upward edge's 'left' and 'right' are two different placements"
    ((vertX "" "left").isSome && vertX "" "left" != vertX "" "right")
  t "'auto' on an upward edge places the label as 'left' does"
    (vertX "auto" "" == vertX "" "left")
  t "'swap' on an upward edge places it as 'right' does"
    (vertX "auto, swap" "" == vertX "" "right")

/-- **An anchor stands on the node's border, one inner sep clear of the
letters.** pgf's node border is its text *plus* `inner sep`, default
`0.3333em` (TikZ manual §17.2.2, the `inner sep`/`inner xsep`/`inner ysep`
keys), and §17.5.2's anchors sit on that border. The engine resolved every
anchor on the label's ink instead, so an edge drawn to a node's `west`
started inside its first letter and every anchor sat one sep inside where
pgf puts it — the user's report was exactly "the anchor points are a little
too close to the text".

The claim is stated as a *difference* rather than against a computed
absolute: two builds differing only in the declared sep must put their
anchors exactly that much apart. That makes the row immune to what the
suite's metric answers (it answers nothing, so the ink is zero and the
extent is the sep alone) while still pinning the arithmetic, and it is the
one shape that cannot pass under a reader that ignores the key.
`Picture.borderHalf_between` is the invariant behind it. Invented
content. -/
def pictureInnerSepChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pic (opts : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node[" ++ opts ++ "] (aa) at (0, 0) {Pear};\n" ++
    "\\node[" ++ opts ++ "] (bb) at (4, 0) {Plum};\n" ++
    "\\draw (aa.east) -- (bb.west);\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let edgeBox (opts : String) : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    let (doc, _) := elabStr (pic opts)
    ((censusOf (coveredColorsOf doc) (layoutOf oneFace doc))[0]?).bind (·.pathBoxes[0]?)
  let dflt := edgeBox "text=black"
  let zero := edgeBox "inner sep=0pt"
  let twomm := edgeBox "inner sep=2mm"
  let (_, ds) := elabStr (pic "inner sep=2mm")
  t "an 'inner sep' node elaborates with nothing refused"
    (ds.all (·.severity == .note))
  -- The anchors move, so the edge between them is shorter by two seps: one
  -- at each end. A reader that dropped the key would give three equal
  -- widths, which is what the defect did.
  t "a declared 'inner sep' shortens an anchored edge by one sep at each end"
    (match zero, twomm with
     | some (_, _, wz, _), some (_, _, w2, _) => wz - w2 == 2 * Dim.mm 2
     | _, _ => false)
  t "the default 'inner sep' is pgf's 0.3333em"
    (match zero, dflt with
     | some (_, _, wz, _), some (_, _, wd, _) =>
       wz - wd == 2 * Picture.innerSep Ir.baseFontSize
     | _, _ => false)
  -- With no sep and a metric that measures nothing the two anchors are the
  -- two centres, so the edge spans the declared separation -- to within the
  -- scaled point a milli coordinate rounds to, which is not the claim.
  t "a zero 'inner sep' puts the anchor back on the letters"
    (match zero with
     | some (_, _, wz, _) => Dim.mm 40 - wz <= 1 && wz <= Dim.mm 40
     | none => false)
  -- Per-axis: `inner xsep` moves the side anchors and leaves the top and
  -- bottom where they were, which is what makes it two keys and not one.
  let vert (opts : String) : Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
    let src := "\\begin{document}\n\\begin{tikzpicture}\n" ++
      "\\node[" ++ opts ++ "] (aa) at (0, 0) {Pear};\n" ++
      "\\node[" ++ opts ++ "] (bb) at (0, -4) {Plum};\n" ++
      "\\draw (aa.south) -- (bb.north);\n" ++
      "\\end{tikzpicture}\n\\end{document}"
    let (doc, _) := elabStr src
    ((censusOf (coveredColorsOf doc) (layoutOf oneFace doc))[0]?).bind (·.pathBoxes[0]?)
  t "'inner xsep' alone leaves the vertical anchors where they stood"
    (match vert "inner sep=0pt", vert "inner sep=0pt, inner xsep=2mm" with
     | some (_, _, _, h0), some (_, _, _, hx) => h0 == hx
     | _, _ => false)
  t "'inner ysep' alone moves the vertical anchors"
    (match vert "inner sep=0pt", vert "inner sep=0pt, inner ysep=2mm" with
     | some (_, _, _, h0), some (_, _, _, hy) => h0 - hy == 2 * Dim.mm 2
     | _, _ => false)

/-- **A document's own macros reach its pictures before the walk reads
them.** Expansion precedes execution, as in TeX
(`Picture.expandMacros`): the stream the statement reader and the label
salvage see has already had the document's definitions taken out of it, so
a node body that is nothing but a macro sets the macro's words, and a
one-argument wrapper around `\textcolor` sets its argument in the role it
names.

The defect this closes made three pages of a real deck carry the declared
placeholder where a node's label belonged. The boundary standalone already
carried the document's reachable definitions — that is the macro-closure
work — and the native walk did not, so a picture the engine drew itself met
an undefined control word, salvaged nothing, and shipped the placeholder
`labelFloor` pays a named loss with. The floor was doing its job; it was
being asked the wrong question.

Read off `Layout.Out` — the placeholder's absence and the label's words are
census facts, and the colour a macro-supplied `\textcolor` sets is only
visible on the shipped run. Invented content. -/
def pictureMacroReachChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let pre := "\\palette{ accent = #1188CC }\n" ++
    "\\def\\alphaword{Alpha}\n" ++
    "\\newcommand{\\muted}[1]{\\textcolor{accent}{#1}}\n" ++
    "\\newcommand{\\pairword}[2]{#1 and #2}\n" ++
    "\\def\\innerword{Epsilon}\n" ++
    "\\newcommand{\\chained}{\\innerword}\n"
  let src := pre ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node (aa) at (0, 0) {\\alphaword};\n" ++
    "\\node (bb) at (4, 0) {\\muted{Beta}};\n" ++
    "\\node (cc) at (0, -2) {\\pairword{Gamma}{Delta}};\n" ++
    "\\node (dd) at (4, -2) {\\chained};\n" ++
    "\\draw (aa) -- (bb);\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let (doc, ds) := elabStr src
  let out := layoutOf oneFace doc
  let c := censusOf (coveredColorsOf doc) out
  -- The label ships the macro's words, and never the placeholder a named
  -- loss would have paid with.
  t "a node body of one zero-argument macro ships that macro's words"
    (pageOccurs c 0 "Alpha" == 1)
  t "a one-argument macro ships its argument"
    (pageOccurs c 0 "Beta" == 1)
  t "a two-argument macro ships both arguments in order"
    (pageOccurs c 0 "Gamma and Delta" == 1)
  -- A macro whose body spells another is expanded through: the table is
  -- transitively closed and one pass per entry exhausts the chain.
  t "a macro whose body spells another reaches the page through it"
    (pageOccurs c 0 "Epsilon" == 1 && !pageHas c 0 "innerword")
  t "no node ships the declared placeholder"
    (!pageHas c 0 Picture.nodeFloorPlaceholder)
  t "no macro in a node body is named as unknown"
    (!ds.any fun d => d.code == DiagCode.W0334.code &&
      hasStr d.message "unknown macro")
  t "the macro-reach document elaborates with nothing refused"
    (ds.all (·.severity == .note))
  t "no boundary box stands where the macro picture is"
    ((c[0]?.map (·.images == 0)).getD false)
  -- The colour half: a `\textcolor` the document's macro supplied paints
  -- its argument, which only the shipped run can say.
  let runColors : Array Ir.Color :=
    (out.pages[0]?.map fun p =>
      p.lines.flatMap fun l => l.segs.filterMap fun s =>
        match s with
        | .run _ col _ _ glyphs _ _ _ _ _ =>
          if glyphs.any (·.2 == 'B') then some col else none
        | _ => none).getD #[]
  t "a macro-supplied '\\textcolor' paints the run it wraps"
    (runColors.any (· == { r := 0x11, g := 0x88, b := 0xCC }))
  -- The two names the walk owns are not the document's to take: expanding a
  -- redefined `\node` would delete the statement in silence.
  let (_, ownDs) := elabStr ("\\def\\node{Xyz}\n\\begin{document}\n" ++
    "\\begin{tikzpicture}\n\\node (aa) at (0, 0) {Zeta};\n" ++
    "\\end{tikzpicture}\n\\end{document}")
  let ownC := censusOf (coveredColorsOf (elabStr ("\\def\\node{Xyz}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node (aa) at (0, 0) {Zeta};\n\\end{tikzpicture}\n" ++
    "\\end{document}")).1) (layoutOf oneFace (elabStr ("\\def\\node{Xyz}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node (aa) at (0, 0) {Zeta};\n\\end{tikzpicture}\n\\end{document}")).1)
  t "a macro of a name the walk owns leaves the statement standing"
    (pageOccurs ownC 0 "Zeta" == 1 && !pageHas ownC 0 "Xyz" &&
     ownDs.all (·.severity == .note))
  -- A `\foreach` variable is the picture's, whatever the document called
  -- it: expanding the document's `\xx` would replace the loop's own value.
  let loopC := censusOf (coveredColorsOf (elabStr ("\\def\\xx{9}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\foreach \\xx in {1, 2}{\\node at (\\xx, 0) {Eta\\xx};}\n" ++
    "\\end{tikzpicture}\n\\end{document}")).1)
    (layoutOf oneFace (elabStr ("\\def\\xx{9}\n\\begin{document}\n" ++
      "\\begin{tikzpicture}\n" ++
      "\\foreach \\xx in {1, 2}{\\node at (\\xx, 0) {Eta\\xx};}\n" ++
      "\\end{tikzpicture}\n\\end{document}")).1)
  t "a loop variable is the picture's, not the document's macro of that name"
    (pageHas loopC 0 "Eta1" && pageHas loopC 0 "Eta2" && !pageHas loopC 0 "Eta9")

/-- **A key name the document writes is the key name the walk reads.** The
invariant over the declared-and-used names of one picture: every name a
`/.style` or `/.append style` declares resolves at the bracket that uses
it, so nothing is keyed under one spelling and looked up under another.

The defect this closes is a name cut at its first hyphen. `-` is an
ordinary pgf key-name character (manual §87.2, the key path grammar: `/`
separates a path, `.` introduces a handler, `,` an entry and `=` a value —
every other character is the name's), and the reader admitted a run of
identifiers only. A declaration under `edge-muted` was therefore stored
under nothing and named as a dropped key `edge`, while the bracket that
used it found no bundle and dropped every option in it. One hyphen cost a
declaration, its every use, and the truth of the diagnostic at once.

Read off `Layout.Out`: the strokes and spans a hyphenated bundle sets are
only visible on the page, and the dash is read off the shipped stroke
rather than the census, which carries no dash. Invented content. -/
def pictureHyphenKeyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let body := "rectangle, draw, minimum width=9mm, minimum height=6mm"
  let sets := "\\tikzset{edge-muted/.style={draw=green},\n" ++
    "  node-box/.style={" ++ body ++ "},\n" ++
    "  edge-muted/.append style={dashed}}\n"
  let pic (nodeOpts edgeOpts : String) : String :=
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node[" ++ nodeOpts ++ "] (aa) at (0, 0) {One};\n" ++
    "\\node[" ++ nodeOpts ++ "] (bb) at (4, 0) {Two};\n" ++
    "\\draw[" ++ edgeOpts ++ "] (aa) -- (bb);\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let (doc, ds) := elabStr (sets ++ pic "node-box" "edge-muted")
  let out := layoutOf oneFace doc
  let c := censusOf (coveredColorsOf doc) out
  -- The control: the same keys written out at the use site, with no bundle
  -- in play. Every page claim below is an equality against it, so nothing
  -- here restates an arithmetic the reader would have to trust.
  let (inlineDoc, _) := elabStr (pic body "draw=green, dashed")
  let inlineOut := layoutOf oneFace inlineDoc
  let inlineC := censusOf (coveredColorsOf inlineDoc) inlineOut
  let keyNames : List String :=
    ((ds.filter fun d => d.code == DiagCode.W0334.code &&
      hasStr d.message "picture key").map fun d =>
        (d.message.splitOn "'").getD 1 "").toList
  -- The diagnostic half: a name the reader honours is never named as
  -- dropped, and it is the *truncation* that made the old message false.
  t "a hyphenated style definition is not named as a dropped key"
    (keyNames == [])
  t "no name is reported cut at its hyphen"
    (!keyNames.contains "edge" && !keyNames.contains "node")
  t "the hyphenated-key document elaborates with nothing refused"
    (ds.all (·.severity == .note))
  -- The page half: the two nodes' outlines and the edge, so the bundle
  -- reached both shapes rather than only parsing.
  t "the two hyphenated-bundle nodes and the edge ship as page paths"
    ((c[0]?.map (·.paths == 3)).getD false)
  t "no boundary box stands where the hyphenated-key picture is"
    ((c[0]?.map (·.images == 0)).getD false)
  -- **A hyphenated bundle is its own body.** Applying the name and writing
  -- the keys out ship the same geometry and the same paint.
  t "a hyphenated bundle ships the geometry its body declares"
    ((c[0]?.map (·.pathSpans)) == (inlineC[0]?.map (·.pathSpans)) &&
     (c[0]?.map (·.pathBoxes)) == (inlineC[0]?.map (·.pathBoxes)))
  t "a hyphenated bundle ships the paint its body declares"
    ((c[0]?.map (·.pathStrokes)) == (inlineC[0]?.map (·.pathStrokes)))
  t "a hyphenated bundle sets a node extent at all"
    ((c[0]?.bind (·.pathSpans[0]?)).map (fun (w, h) => w > 0 && h > 0) == some true)
  t "a hyphenated bundle sets the stroke colour it declares"
    ((c[0]?.bind (·.pathStrokes[2]?)).map (·.1 == { r := 0, g := 255, b := 0 })
      == some true)
  -- `/.append style` on the same hyphenated name composes onto it: the
  -- edge is green *and* dashed, which is two handlers reading one name.
  t "'/.append style' on a hyphenated name composes onto it"
    ((out.pages[0]?.bind fun p => (p.paths[2]?).bind (·.stroke)).map
      (·.dash == .dashed) == some true)
  -- **Every bracket, not most of them.** An `edge`/`to` operation carries
  -- its own bracket and read it raw, so a bundle applied there reached no
  -- reader at all — the last place the use side of `styleName_agree` was
  -- not honoured, and on a real deck it was the one that cost a dashed
  -- edge its dash.
  let opSrc := sets ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node[node-box] (aa) at (0, 0) {One};\n" ++
    "\\node[node-box] (bb) at (4, 0) {Two};\n" ++
    "\\path (aa) edge[edge-muted] (bb);\n" ++
    "\\end{tikzpicture}\n\\end{document}"
  let (opDoc, opDs) := elabStr opSrc
  let opOut := layoutOf oneFace opDoc
  t "an edge operation's own bracket expands a hyphenated bundle"
    ((opOut.pages[0]?.bind fun p => (p.paths[2]?).bind (·.stroke)).map
      (fun s => s.dash == .dashed && s.color == { r := 0, g := 255, b := 0 })
      == some true)
  t "a bundle on an edge operation is not named as a dropped option"
    (!opDs.any fun d => d.code == DiagCode.W0334.code && hasStr d.message "edge-muted")
  -- **A dropped key is named by its whole name.** The diagnostic reported
  -- the entry's first token, so a two-word key the subset has no loop for
  -- was named `every` — a key no document is called.
  let namesOf (s : String) : List String :=
    ((elabStr (s ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++
      "\\draw (0, 0) -- (3, 0);\n\\end{tikzpicture}\n\\end{document}")).2.filter
        fun d => d.code == DiagCode.W0334.code &&
          hasStr d.message "picture key").toList.map fun d =>
        (d.message.splitOn "'").getD 1 ""
  t "a two-word key with no loop is named by both its words"
    (namesOf "\\tikzset{every label/.style={draw}}\n" == ["every label"])
  t "a hyphenated key outside the subset is named whole"
    (namesOf "\\tikzset{over-lay}\n" == ["over-lay"])

/-- **Whatever drew a picture, the keys that drawing did not read are
named.** The gate on the key diagnostic is the engine's own drawing, never
the boundary tool the document nominally configures: a `\tikzset` key the
subset does not read is dropped by every picture the engine drew itself,
and the real TikZ only ever sees a picture that went *whole* to the
boundary. The decisive shape is the pair of builds below — one source, one
extra `\pictures{ tool = none }` line, byte-identical PDFs — because it
separates the two things the old gate confused: the drawing does not depend
on the tool, only the honesty does. Invented content and design. -/
def pictureKeyGateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  -- Two keys the subset does not read, beside an arrow-tip default it now
  -- honours (`Picture.readsOpt`, the outermost bracket) and one style
  -- definition it reads. The tip is in the source deliberately: it is the
  -- shape whose silent loss left a diagram's edges headless, and the row
  -- below pins that it is no longer counted as dropped.
  let keys := "\\tikzset{>=latex, overlay, sloped}\n" ++
    "\\tikzset{box/.style={rectangle, draw, minimum width=9mm, minimum height=6mm}}\n"
  -- A picture the subset draws itself: both nodes carry their own extent, so
  -- shapes land and nothing routes to the boundary.
  let native := "\\begin{tikzpicture}\n\\node[box] (a) at (0, 0) {A};\n" ++
    "\\node[box] (b) at (3, 0) {B};\n\\draw[->] (a) -- (b);\n\\end{tikzpicture}\n"
  -- A picture the subset draws nothing of, so it goes whole to the boundary.
  let wholePic := "\\begin{tikzpicture}\n\\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}\n"
  let body := "A paragraph stands first.\n\n" ++ native ++ "\nText resumes after it.\n"
  let openSrc := dvDoc keys body
  let refusedSrc := dvDoc ("\\pictures{ tool = none }\n" ++ keys) body
  let keyNames (ds : Array Diag) : List String :=
    ((ds.filter fun d => d.code == DiagCode.W0334.code &&
      hasStr d.message "picture key").map fun d =>
        (d.message.splitOn "'").getD 1 "").toList
  let (openDoc, openDs) := elabStr openSrc
  let (refusedDoc, refusedDs) := elabStr refusedSrc
  -- The honesty half: the default build names exactly what the refusal does.
  t "the engine's own drawing names every key it did not read"
    (keyNames openDs == ["overlay", "sloped"])
  t "the declared refusal names the same keys, no more"
    (keyNames refusedDs == keyNames openDs)
  -- The artifact half, and the whole point: the drawing does not depend on
  -- the tool. Same bytes, so nothing but the naming moved.
  let pdfOf (doc : Ir.Doc) : ByteArray :=
    let geom := Layout.Geom.ofPage doc.page
    Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info
  t "the two builds ship byte-identical PDFs"
    (pdfOf openDoc == pdfOf refusedDoc)
  -- The boundary is the one reader that makes the claim false, and only for
  -- a picture that went there whole.
  t "a document whose every picture went to the boundary claims no loss"
    (keyNames (elabStr (dvDoc keys ("Prose.\n\n" ++ wholePic))).2 == [])
  t "a key with no picture to lose it is not named"
    (keyNames (elabStr (dvDoc keys "Prose alone, with no diagram at all.\n")).2 == [])
  -- The mixed document is the case the old gate got wrong on real input: one
  -- picture at the boundary does not buy silence for the twelve the engine
  -- drew itself.
  t "one boundary picture beside an engine-drawn one still names the keys"
    (keyNames (elabStr (dvDoc keys ("Prose.\n\n" ++ wholePic ++ "\nMore prose.\n\n" ++
      native))).2 == ["overlay", "sloped"])
  -- The tip default among them is honoured, not named: the set is smaller
  -- and truer, which is the only shrink this diagnostic may take.
  t "the arrow-tip default is honoured rather than named as dropped"
    (!(keyNames openDs).contains ">")
  -- A style definition is read, so it is never among them.
  t "a style definition the subset reads is not named as dropped"
    (!(keyNames openDs).contains "box")

/-- **A key the document sets for every picture is set on every picture**,
read off the shipped page (`Picture.mergeOpts`'s outermost level, whose
facts are `merge_global_covers` and `merge_picture_exact`). A `\tikzset`
entry that is not a style definition but is one the subset reads at a
statement — an arrow-tip default is the shape that motivated it — used to
be dropped whole, so a deck declaring its tip once in the preamble shipped
every edge headless. It is now the outermost bracket: the picture's own and
the statement's own both win over it, and a statement reads it only where
its own shape does, since neither outer bracket was written at that site.
Invented content and design. -/
def pictureGlobalKeyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let censusSrc (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let box := "\\tikzset{box/.style={rectangle, draw, minimum width=9mm, " ++
    "minimum height=6mm}}\n"
  -- The defect, at its smallest: the tip is declared once for the document
  -- and the edge carries no bracket of its own.
  let pair := "\\node[box] (a) at (0, 0) {A};\n\\node[box] (b) at (3, 0) {B};\n"
  let globalTip := censusSrc (box ++ "\\tikzset{->}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ pair ++
    "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")
  t "a tip declared once for the document ships a head on an edge that carries none"
    ((globalTip[0]?.map (·.paths == 4)).getD false)
  -- The head is the engine's own ink: a filled triangle beside the edge, no
  -- boundary box and no external tool.
  t "the head is a triangle the engine drew itself"
    ((globalTip[0]?.map (·.images == 0)).getD false &&
     ((globalTip[0]?.bind (·.pathSpans[3]?)).map fun (w, h) =>
        w < Dim.mm 4 && h < Dim.mm 4 && w > 0 && h > 0) == some true)
  -- The `arrows.meta` spelling of the same tip is the same head, declared
  -- once for the document: the shape the defect was reported on.
  let metaTip := censusSrc (box ++ "\\tikzset{-Latex}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ pair ++
    "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")
  t "the arrows.meta spelling of the tip ships the same head"
    ((metaTip[0]?.map (·.paths == 4)).getD false)
  -- A tip kind this subset cannot draw stays a named loss: the head is
  -- missing, and a substitution would be a head of the wrong shape.
  let otherTip := elabStr (box ++ "\\tikzset{-Stealth}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ pair ++
    "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")
  t "a tip kind the subset cannot draw is still named as dropped"
    (otherTip.2.any fun d => d.code == DiagCode.W0334.code &&
      hasStr d.message "picture key")
  -- Precedence, document < picture < own. `every X` is declared for the
  -- document too, so it stands in its own source below rather than here.
  let ladder := censusSrc (box ++ "\\tikzset{draw=blue}\n" ++
    "\\tikzset{wire/.style={draw=green}}\n" ++
    "\\begin{document}\n" ++
    "\\begin{tikzpicture}\n\\draw (0, 0) -- (3, 0);\n\\end{tikzpicture}\n" ++
    "\\begin{tikzpicture}[wire]\n\\draw (0, 0) -- (3, 0);\n\\end{tikzpicture}\n" ++
    "\\begin{tikzpicture}\n\\draw[draw=red] (0, 0) -- (3, 0);\n" ++
    "\\end{tikzpicture}\n\\end{document}")
  t "an edge declaring nothing anywhere ships the document's colour"
    ((ladder[0]?.bind (·.pathStrokes[0]?)).map (·.1 == { r := 0, g := 0, b := 255 })
      == some true)
  t "the picture's own bracket beats the document's"
    ((ladder[0]?.bind (·.pathStrokes[1]?)).map (·.1 == { r := 0, g := 255, b := 0 })
      == some true)
  t "the statement's own bracket beats every outer level"
    ((ladder[0]?.bind (·.pathStrokes[2]?)).map (·.1 == { r := 255, g := 0, b := 0 })
      == some true)
  -- `every path` is the level between: it beats the document's and the
  -- picture's, and loses to the statement's own.
  let everyMid := censusSrc (box ++ "\\tikzset{draw=blue}\n" ++
    "\\tikzset{wire/.style={draw=green}}\n" ++
    "\\tikzset{every path/.style={draw=orange}}\n" ++
    "\\begin{document}\n" ++
    "\\begin{tikzpicture}[wire]\n\\draw (0, 0) -- (3, 0);\n" ++
    "\\draw[draw=red] (0, 0.6) -- (3, 0.6);\n\\end{tikzpicture}\n\\end{document}")
  t "every path beats both the picture's bracket and the document's"
    ((everyMid[0]?.bind (·.pathStrokes[0]?)).map
      (·.1 == { r := 255, g := 128, b := 0 }) == some true)
  t "the statement's own bracket still beats every path"
    ((everyMid[0]?.bind (·.pathStrokes[1]?)).map (·.1 == { r := 255, g := 0, b := 0 })
      == some true)
  -- The accumulating family is the trap: `minimum size` takes a maximum
  -- within one bracket, so a surviving document-level 8mm would beat the
  -- node's own 4mm and draw the opposite of what the node says.
  let sized := censusSrc ("\\tikzset{minimum size=8mm}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++
    "\\node[draw] (a) at (0, 0) {A};\n" ++
    "\\node[draw, minimum size=4mm] (b) at (4, 0) {B};\n" ++
    "\\end{tikzpicture}\n\\end{document}")
  t "a document-level size reaches the node that declared none"
    ((sized[0]?.bind (·.pathSpans[0]?)).map (· == (Dim.mm 8, Dim.mm 8)) == some true)
  t "the node's own size is not beaten by the document's larger one"
    ((sized[0]?.bind (·.pathSpans[1]?)).map (· == (Dim.mm 4, Dim.mm 4)) == some true)
  -- A document-level entry is read where its own shape reads it and nowhere
  -- else: neither outer bracket was written at this node, so a path-only
  -- key is no loss here. Claiming one is how honouring the tip would have
  -- traded a silent loss for a false one.
  let (_, tipDs) := elabStr (box ++ "\\tikzset{->}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}\n" ++ pair ++
    "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")
  t "a document-level tip is no loss at a node"
    (tipDs.isEmpty)
  -- The W0334 set is smaller and truer, not smaller: a key the subset reads
  -- stops firing and a key outside it keeps firing, from one line.
  let mixedKeys (s : String) : List String :=
    ((elabStr (box ++ s ++ "\\begin{document}\n\\begin{tikzpicture}\n" ++ pair ++
      "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")).2.filter fun d =>
        d.code == DiagCode.W0334.code && hasStr d.message "picture key").toList.map
      fun d => (d.message.splitOn "'").getD 1 ""
  t "a document key the subset reads is no longer named as dropped"
    (mixedKeys "\\tikzset{->, overlay}\n" == ["overlay"])
  t "a document key outside the subset is still named from the same line"
    (mixedKeys "\\tikzset{overlay}\n" == ["overlay"])
  -- A picture-level applied style carrying a key of the other shape is the
  -- same claim one level in, and it was firing before this.
  let (_, inheritDs) := elabStr (box ++ "\\tikzset{head/.style={->}}\n" ++
    "\\begin{document}\n\\begin{tikzpicture}[head]\n" ++ pair ++
    "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")
  t "a picture-level tip is no loss at a node either"
    (inheritDs.isEmpty)
  t "a picture-level tip still ships the head"
    (((censusSrc (box ++ "\\tikzset{head/.style={->}}\n" ++
      "\\begin{document}\n\\begin{tikzpicture}[head]\n" ++ pair ++
      "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}"))[0]?.map
        (·.paths == 4)).getD false)
  -- The floor the shape filter must not cost: an inherited entry no shape
  -- reads is still named, because nobody read it.
  t "an inherited key no shape reads is still named"
    ((elabStr (box ++ "\\tikzset{ghost/.style={overlay}}\n" ++
      "\\begin{document}\n\\begin{tikzpicture}[ghost]\n" ++ pair ++
      "\\draw (a) -- (b);\n\\end{tikzpicture}\n\\end{document}")).2.any fun d =>
        d.code == DiagCode.W0334.code && hasStr d.message "overlay")

/-- The poster-chrome compat arms: `\setbeamercolor` maps the elements the
engine has roles for onto the palette (and only those — an element with no
role keeps the configuration warning), `\footercontent` is the running
foot's own furniture slot (the gemini lineage's footer declaration), and
`\usecolortheme{n}` reads `beamercolorthemen.sty` beside the document —
beamer's own file rule — through the same splice `\usepackage` takes, its
lines then honoured by the same passes a document goes through. Own
function: `main`'s elaboration budget. -/
def posterChromeCompatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (s : String) := "\\documentclass{poster}" ++ s ++
    "\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  let (doc, ds) := elabStr (pre "\\setbeamercolor{headline}{fg=#F5F6FA,bg=#40739E}")
  t "setbeamercolor headline maps to the frametitle pair"
    (doc.palette.find? "frametitlebg" == some { r := 0x40, g := 0x73, b := 0x9E } &&
     doc.palette.find? "frametitlefg" == some { r := 0xF5, g := 0xF6, b := 0xFA } &&
     ds.all (·.severity == .note))
  t "setbeamercolor of an element with no role keeps the configuration warning"
    (warnCodes (pre "\\setbeamercolor{palette primary}{fg=#101010}") == ["W0104"])
  let (fDoc, fDs) := elabStr (pre "\\footercontent{An Invented Venue 2099}")
  t "footercontent is the running foot's slot"
    (fDs.all (·.severity == .note) &&
     (fDoc.foot.map Ir.plainText) == some "An Invented Venue 2099")
  let parseRaws (file s : String) : Array Parse.Raw :=
    (Parse.parse file (Lex.lex file s).1).1
  let docRaws := parseRaws "t" (pre "\\theme{gemini}\\usecolortheme{invented}")
  let ctSty := "\\definecolor{inkco}{HTML}{101010}\n\\setbeamercolor{headline}{bg=inkco}\n"
  let (raws2, spliced) := Compat.applyLocalSty docRaws
    #[("beamercolorthemeinvented", parseRaws "beamercolorthemeinvented.sty" ctSty)]
  let (doc2, ds2) := Elab.runRaws "t" raws2
  t "usecolortheme reads the colour theme beside the document"
    (spliced.toList.map (·.1) == ["beamercolorthemeinvented.sty"] &&
     doc2.palette.find? "frametitlebg" == some { r := 0x10, g := 0x10, b := 0x10 } &&
     ds2.all (·.code != "W0104"))
  t "usecolortheme names a candidate for the driver's read"
    ((Compat.localStyCandidates docRaws).contains "beamercolorthemeinvented")
  t "usecolortheme with no file beside the document keeps its warning"
    (warnCodes (pre "\\usecolortheme{nothere}") == ["W0104"])
  -- The headline band's declarations: the title family becomes furniture
  -- on a headline class; the corner slots ride only with the band.
  let full := pre ("\\title{An Invented Poster}\\author{Alex Doe}" ++
    "\\institute{Nowhere U}\\logoright{\\includegraphics[totalheight=2cm]{lg.png}}")
  let (hDoc, hDs) := elabStr full
  t "a poster reads the title family as its headline band"
    (hDs.all (·.severity == .note) &&
     (hDoc.headline.map fun hl => Ir.plainText hl.title) == some "An Invented Poster" &&
     (hDoc.headline.map fun hl => Ir.plainText hl.institute) == some "Nowhere U" &&
     hDoc.logoRight.isSome)
  t "a corner logo under a class with no band is dropped by name"
    (warnCodes ("\\documentclass{article}\\logoright{x}" ++
      "\\begin{document}y\\end{document}") == ["W0317"])
  t "a corner logo without a declared title is dropped by name"
    ((elabStr (pre "\\logoright{x}")).2.any (·.code == "W0309") &&
     (elabStr (pre "\\logoright{x}")).1.logoRight.isNone)
  t "no title, no band"
    ((elabStr (pre "")).1.headline.isNone)


/-- The boundary cache's decision, the driver's half stated as values
(`LeanTex.Cli.PicCache`): one attempt per request and tool version,
whichever way the tool answered. Before this block a *failing* render was
the one verdict the cache did not keep, so every unrenderable picture paid
a fresh tool process on every build — the drawn ones warmed, the refused
ones never did, and a document with six of them stayed seconds slow
forever. The three facts that close it: a held verdict is never re-run, a
replay reports the tool's own words under the same code, and an attempt the
tool never finished is not a verdict at all. No tool runs here: the policy
is pure, which is why it can be checked at all. -/
def picCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The decision table, exhaustively. `run` is the cold case and only the
  -- cold case (`PicCache.step_cold_exact`).
  t "nothing held: the tool runs"
    (PicCache.step false none == .run)
  t "a drawn PDF serves"
    (PicCache.step true none == .serve)
  t "a remembered refusal replays instead of running"
    (PicCache.step false (some "! Package pgf Error") == .replay "! Package pgf Error")
  t "a drawn PDF outranks a stale refusal in the same slot"
    (PicCache.step true (some "! Package pgf Error") == .serve)
  -- The replay is the fresh diagnostic, not a degraded stand-in: same
  -- code, same message, same help carrying the tool's own last words.
  let says := "! Package pgf Error: No shape named `x' is known."
  let fresh := DriverDiag.boundaryFailed "lualatex" says
  let replayed := match PicCache.step false (some says) with
    | .replay s => some (DriverDiag.boundaryFailed "lualatex" s)
    | _ => none
  t "a replayed refusal is the fresh diagnostic, word for word"
    (replayed.map (·.code) == some fresh.code &&
     replayed.map (·.message) == some fresh.message &&
     replayed.bind (·.help) == fresh.help)
  t "the replayed help still carries the tool's own words"
    (fresh.code == "E0382" && (fresh.help.any fun h => hasStr h says))
  -- What the tool answered, read off the process ending and what it left
  -- behind. An exit the tool chose *and left a log for* is a verdict;
  -- nothing else is.
  t "a clean exit that drew is the drawing"
    (PicCache.outcome (.exited 0) true .absent == .drawn)
  t "a clean exit that drew nothing is the tool's own no"
    (PicCache.outcome (.exited 0) false .absent == .refused "no PDF was produced")
  t "a failing exit carries the log's last words"
    (PicCache.outcome (.exited 1) false (.says says) == .refused says)
  t "a failing exit whose log says nothing usable names the code"
    (PicCache.outcome (.exited 1) false (.says "") == .refused "exit code 1")
  t "a failing exit that left no log at all is no answer about the request"
    (PicCache.outcome (.exited 127) false .absent == .inconclusive "exit code 127")
  t "a budget overrun is no answer about the request"
    (PicCache.outcome (.overran 120) false .absent ==
      .inconclusive "no result within 120 s; killed")
  t "a spawn that raised is no answer about the request"
    (PicCache.outcome (.unstarted "no such file") false .absent ==
      .inconclusive "no such file")
  -- What the cache keeps: the tool's refusal, and nothing the machine did
  -- (`PicCache.remembers_verdict_exact`, `PicCache.unlogged_retried_exact`).
  t "a refusal is remembered, in the tool's words"
    (PicCache.remembers (PicCache.outcome (.exited 1) false (.says says)) == some says)
  t "a drawing is not remembered as a refusal"
    (PicCache.remembers (PicCache.outcome (.exited 0) true .absent) == none)
  t "an overrun is not remembered, so the next build retries it"
    (PicCache.remembers (PicCache.outcome (.overran 120) false .absent) == none)
  t "a failed spawn is not remembered, so the next build retries it"
    (PicCache.remembers (PicCache.outcome (.unstarted "boom") false .absent) == none)
  t "a missing tool is not remembered, so installing it is enough"
    (PicCache.remembers (PicCache.outcome (.exited 127) false .absent) == none)
  -- The slot: the request's content hash and the tool's version, so an
  -- edited picture reads a different slot and is retried, and a tool
  -- upgrade retries every one.
  let k := Ir.picHash "\\draw (0,0) -- (1,1);"
  let k' := Ir.picHash "\\draw (0,0) -- (1,2);"
  let v := Ir.picHash "lualatex 1.0"
  let v' := Ir.picHash "lualatex 1.1"
  t "the drawn PDF and the remembered refusal share one slot"
    (PicCache.pdfName k v == PicCache.stem k v ++ ".pdf" &&
     PicCache.failName k v == PicCache.stem k v ++ ".fail" &&
     PicCache.pdfName k v != PicCache.failName k v)
  t "an edited picture names a different slot"
    (k != k' && PicCache.failName k v != PicCache.failName k' v)
  t "an upgraded tool names a different slot"
    (v != v' && PicCache.failName k v != PicCache.failName k v')
  t "the remembered refusal is not mistaken for a drawing"
    (!(PicCache.failName k v).endsWith ".pdf")
  -- Who the tool is, read off the probe's ending. Only a clean exit names
  -- a version (`PicCache.probed_present_exact`): a machine with nothing
  -- installed still reaches `exec`, comes back nonzero, and hands back
  -- whatever the forked child inherited on its stdout — so reading the
  -- output without the exit code read the parent's own text back as a tool
  -- identity, and a picture no tool had looked at was reported as one the
  -- tool drew nothing for.
  let banner := "This is InventedTeX, Version 1.0"
  t "a clean exit that named itself is the tool"
    (PicCache.probed (.exited 0) banner == .present banner)
  t "a clean exit that named nothing is no tool"
    (PicCache.probed (.exited 0) "" == .absent "no version line")
  t "a nonzero exit is no tool, whatever it wrote"
    (PicCache.probed (.exited 127) banner == .absent "'--version' exited 127" &&
     PicCache.probed (.exited 255) banner == .absent "'--version' exited 255")
  t "a probe that raised is no tool"
    (PicCache.probed (.unstarted "no such file") "" == .absent "no such file")
  t "a probe that never came back is no tool"
    (PicCache.probed (.overran 5) "" == .absent "no version within 5 s; killed")
  -- The two endings route to two different losses, and the absent one is
  -- the degraded one: a placeholder ships and the run stands. A picture the
  -- tool ran on and refused keeps the dropped loss, undiminished.
  let unavailable := DriverDiag.boundaryToolUnavailable "lualatex"
  t "a tool that is not there is a degraded loss, not a dropped one"
    (unavailable.code == "W0379" && DiagCode.W0379.loss == .degraded &&
     unavailable.severity == .warning)
  t "a picture the tool refused is still a dropped loss"
    ((DriverDiag.boundaryFailed "lualatex" says).code == "E0382" &&
     DiagCode.E0382.loss == .dropped && unavailable.code != "E0382")
  -- The version memo: asked once per tool binary, not once per build. The
  -- version string is still the slot's key
  -- (`PicCache.versionStep_remembered_exact`), and a witness that moved
  -- sends the run back to the tool (`versionStep_changed_exact`).
  let stampA := "/opt/invented/bin/tool\t7634408\t1777998731\t0"
  let stampB := "/opt/invented/bin/tool\t7634512\t1778998731\t0"
  t "a witness that still matches answers without asking"
    (PicCache.versionStep (some (stampA, banner)) stampA == .remembered banner)
  t "a witness that moved asks again"
    (PicCache.versionStep (some (stampA, banner)) stampB == .probe)
  t "no memo at all asks"
    (PicCache.versionStep none stampA == .probe)
  t "a witness no stat could take matches nothing"
    (PicCache.versionStep (some ("", banner)) "" == .probe)
  t "a memo with no version asks"
    (PicCache.versionStep (some (stampA, "")) stampA == .probe)
  t "the memo round-trips its two lines"
    (PicCache.readVersionMemo (PicCache.versionMemo stampA banner) ==
      some (stampA, banner))
  t "a memo that is not those two lines asks"
    (PicCache.readVersionMemo "" == none &&
     PicCache.readVersionMemo stampA == none)
  t "the memo lives beside the slots it names"
    (PicCache.versionName v == "tool-" ++ v ++ ".ver" &&
     !(PicCache.versionName v).endsWith ".pdf" &&
     !(PicCache.versionName v).endsWith ".fail")

/-- **A build whose pictures all replay starts no tool process.** The
invariant this block holds, at the seam where the tool is asked who it is:
the version string is part of every slot's name, so learning it was worth a
full tool startup on every build — 70 ms of a 144 ms warm run measured on
six cached pictures, the largest single cost left in it. The answer is now
remembered against a stat-only witness of the binary, and `identify` takes
the probe as an argument precisely so "it was not called" is a claim a test
can make with no tool installed. The property the memo must not spend is
the other half: a witness that moved is asked again, and the version it
comes back with names fresh slots. -/
def toolProbeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let spawns ← IO.mkRef 0
  let answering (answer : PicCache.Tool) : IO PicCache.Tool := do
    spawns.modify (· + 1)
    return answer
  let dir ← IO.FS.createTempDir
  let memo := dir / "tool.ver"
  let stampA := "/opt/invented/bin/tool\t7634408\t1777998731\t0"
  let stampB := "/opt/invented/bin/tool\t9001234\t1788000000\t0"
  let one := "This is InventedTeX, Version 1.0"
  let two := "This is InventedTeX, Version 2.0"
  let cold ← ToolProbe.identify memo stampA (answering (.present one))
  t "the first build asks the tool who it is"
    (cold == .present one && (← spawns.get) == 1)
  let warm ← ToolProbe.identify memo stampA (answering (.present one))
  t "a build whose tool has not moved asks nothing"
    (warm == .present one && (← spawns.get) == 1)
  let warm2 ← ToolProbe.identify memo stampA (answering (.present two))
  t "and keeps answering from the memo, not from the tool"
    (warm2 == .present one && (← spawns.get) == 1)
  let upgraded ← ToolProbe.identify memo stampB (answering (.present two))
  t "a tool whose witness moved is asked again"
    (upgraded == .present two && (← spawns.get) == 2)
  let after ← ToolProbe.identify memo stampB (answering (.present one))
  t "the new version is what the next build remembers"
    (after == .present two && (← spawns.get) == 2)
  -- A tool that cannot say who it is records nothing: nothing would ever
  -- match an empty witness, and installing the tool must take effect at
  -- once rather than after a cache wipe.
  let missing := dir / "absent.ver"
  let gone ← ToolProbe.identify missing "" (answering (.absent "'--version' exited 127"))
  t "a tool that is not there is not remembered as one that is"
    (gone == .absent "'--version' exited 127" && !(← missing.pathExists))
  let gone2 ← ToolProbe.identify missing "" (answering (.absent "'--version' exited 127"))
  t "so the next build asks again, and installing it is enough"
    (gone2 == .absent "'--version' exited 127" && (← spawns.get) == 4)
  IO.FS.removeDirAll dir




/-- The keyed-lookup layer: the index beside a keyed store answers exactly
what the scan answers, and the store a document grows costs its size, not
its square.

Both halves are here because either alone would let the engine lie: the
timing without the identity would admit a faster wrong answer, and the
identity without the timing is what let the square stand. The cost is
asserted on the float merge alone — there the lookup is the whole
measurement, so the number means what it says; the end-to-end resolution
below is checked for its answers, not its clock, because at any size where
its scan would show the elaboration around it dominates. Compiled, the
merge over 50,000 labels ran 5.5 s scanned and 23 ms keyed. -/
def keyedLookupChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The one equation the whole layer rests on, at the cases that matter:
  -- a hit, a miss, an empty store, and a duplicate key — first wins, which
  -- is what makes the index and `find?` the same question.
  let store : Array (String × Nat) := #[("a", 1), ("b", 2), ("a", 3)]
  t "the index answers a present key as the scan does"
    ((Ir.keyIndex store)["a"]? == store.find? (·.1 == "a"))
  t "the index answers an absent key as the scan does"
    ((Ir.keyIndex store)["zz"]? == store.find? (·.1 == "zz"))
  t "a duplicate key reads first-wins through the index, as through the scan"
    ((Ir.keyIndex store)["a"]? == some ("a", 1))
  t "the index is empty for an empty store"
    ((Ir.keyIndex (#[] : Array (String × Nat)))["a"]? == none)
  -- Resolution's identity end to end: many labels, many references, every
  -- one showing its own number. A reference that lost its binding reads
  -- '??', so the numbers are the check.
  let refDoc (n : Nat) : String :=
    "\\documentclass{article}\\begin{document}" ++
    String.join ((List.range n).map fun i =>
      s!"\\section\{S {i}}\\label\{sec:{i}}") ++
    String.join ((List.range n).map fun i => s!"see \\ref\{sec:{i}} ") ++
    "\\end{document}"
  let refTexts (n : Nat) : Array String :=
    Ir.foldBlocks (fun out _ => out) (fun out x => match x with
      | .ref _ _ shown _ => out.push shown
      | _ => out) #[] (elabStr (refDoc n)).1.body
  t "every reference resolves to its own number"
    (refTexts 6 == #["1", "2", "3", "4", "5", "6"])
  let many := refTexts 3000
  t "three thousand references against three thousand labels all resolve"
    (many.size == 3000 && !many.contains "??" && many[2999]? == some "3000")
  -- The cost witness, where the lookup is the whole measurement: 50,000
  -- labels against 50,000 float rows. Scanned this is 2.5 x 10^9
  -- comparisons; keyed it is 50,000 lookups.
  let n := 50000
  let labels : Ir.RefTable := ((List.range n).map fun i => (s!"k{i}", none)).toArray
  let rows : Ir.RefTable := ((List.range n).map fun i =>
    (s!"k{i}", some ({ num := toString i, kind := some .figure } : Ir.RefBinding))).toArray
  let t0 ← IO.monoMsNow
  let merged := Ir.withFloatRows labels rows
  -- Consumed before the clock is read again: a pure `let` floats to its
  -- first use, so a timing with nothing between the two reads measures
  -- nothing (the FontDb.families precedent).
  t "the merge carries every row's number onto its key"
    (merged.size == n && merged[7]? == some ("k7", some { num := "7", kind := some .figure })
      && merged[n - 1]? == some (s!"k{n - 1}", some { num := toString (n - 1), kind := some .figure }))
  let mergeMs := (← IO.monoMsNow) - t0
  t s!"the float merge is linear in the table ({mergeMs} ms for {n} labels x {n} rows)"
    (mergeMs < 800)
  -- The duplicate-label test reads the key set now; the table stays flow
  -- ordered for the backends. A second `\label` of one key is still
  -- refused, exactly once, and distinct keys still draw nothing.
  let dup := (elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section{A}\\label{k}\\section{B}\\label{k}\\end{document}")).2
  t "a redeclared label key is still refused once"
    ((dup.filter (·.code == "W0350")).size == 1)
  let manyLabels := (elabStr ("\\documentclass{article}\\begin{document}" ++
    String.join ((List.range 2000).map fun i => s!"\\section\{S {i}}\\label\{k{i}}") ++
    "\\end{document}")).2
  t "two thousand distinct label keys draw no duplicate warning"
    ((manyLabels.filter (·.code == "W0350")).isEmpty)




/-- A beamer `<...>` specification standing on `\begin{frame}` is a
parameter, never content — the same claim `recoveryChecks` makes for an
unknown command's `[...]` run, one construct further in: beamer writes the
spec *before* the option run (beamer manual §8.1), so a reader that only
knows `[opts]{title}` loses the title too, and the whole run — spec,
options, title — lands as a paragraph. Judged over `Layout.Out`'s glyphs,
never the IR dump: the defect that prompted this shipped a frame with no
title bar at all while the suite was green.

The mode half is a page count, not a glyph: `<presentation:0>` declares
zero slides in presentation mode, so the frame is the author saying *not
in this artifact*. Stated as a commutation — the deck ships exactly what
the same deck with the frame deleted ships — because "ships no page" is
only meaningful against the deck that never held it. -/
def frameSpecChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageText (src : String) : String := pageTextOf oneFace src
  let allText (src : String) : String := allTextOf oneFace src
  let pages (src : String) : Nat :=
    let (d, _) := elabStr src
    (layoutOf oneFace d).pages.size
  let has := hasStr
  -- The line shape, not just the glyphs: a title that leaked into the body
  -- carries the same characters as a title that was read, and only its size
  -- and position say which happened.
  let shape (src : String) : String :=
    let (d, _) := elabStr src
    String.join ((allLines (layoutOf oneFace d)).toList.map
      (fun l => s!"{l.size}:{l.y}:{lineText l}|"))
  -- An overlay spec the deck does keep a page for: the spec and the option
  -- run are parameters, the title group is the title.
  let ov := deck169Body
    "\\begin{frame}<2->[noframenumbering]{Alpha Heading}\nBody sentence.\n\\end{frame}"
  let bare := deck169Body
    "\\begin{frame}[noframenumbering]{Alpha Heading}\nBody sentence.\n\\end{frame}"
  t "a frame's overlay specification ships no character"
    (!has (allText ov) "<" && !has (allText ov) ">" &&
     !has (allText ov) "[" && !has (allText ov) "]" &&
     !has (allText ov) "noframenumbering")
  t "the title survives a specification standing before the option run"
    (shape ov == shape bare && has (allText bare) "Alpha Heading")
  t "the frame body still ships"
    (has (pageText ov) "Body sentence.")
  -- The mode half: zero slides in presentation mode is no page at all.
  let kept := deck169Body "\\begin{frame}{Beta Heading}\nKept sentence.\n\\end{frame}"
  let plus := deck169Body
    ("\\begin{frame}{Beta Heading}\nKept sentence.\n\\end{frame}\n" ++
     "\\begin{frame}<presentation:0>[noframenumbering]{Gamma Heading}\n" ++
     "Absent sentence.\n\\end{frame}")
  t "a frame with no presentation slides ships no page"
    (pages plus == pages kept)
  t "and none of its content reaches the artifact"
    (!has (allText plus) "Gamma Heading" && !has (allText plus) "Absent sentence.")
  t "while the frame beside it is untouched"
    (has (allText plus) "Beta Heading" && has (allText plus) "Kept sentence.")
  -- A silenced frame spends nothing. Its body is never descended into, so a
  -- once-per-document loss is named at the frame that actually ships it —
  -- reported inside the dropped frame, the one visible loss went unnamed.
  let shared := "\\makebox[2cm]{A label}\n"
  let twin := deck169Body
    ("\\begin{frame}<presentation:0>{Hidden Heading}\n" ++ shared ++ "\\end{frame}\n" ++
     "\\begin{frame}{Shown Heading}\n" ++ shared ++ "\\end{frame}")
  let hiddenLine : Nat := 4
  let boxLosses := (dvE twin).filter (·.code == "W0104")
  t "a silenced frame spends no diagnostic of its own"
    (boxLosses.size == 1 && boxLosses.all fun d =>
      match d.span with
      | some s => s.pos.line > hiddenLine
      | none => false)
  -- The predicate itself, row by row. A false positive here deletes a page of
  -- someone's talk, so the rows are beamer's own answers, read from its
  -- decoder: the last entry naming this artifact decides, a comma separates
  -- intervals inside one entry, and only a bare zero silences.
  for (spec, silent) in
      [("<presentation:0>", true), ("<beamer:0>", true), ("<all:0>", true),
       ("<0>", true), ("<presentation:00>", true),
       ("<presentation:0|article:1>", true), ("<beamer:1-|all:0>", true),
       ("<handout:0>", false), ("<article:0>", false), ("<trans:0>", false),
       ("<second:0>", false),
       ("<beamer:0,2>", false), ("<presentation:0-3>", false),
       ("<beamer:1,3>", false), ("<2->", false), ("<+->", false),
       ("<all:0|beamer:1->", false)] do
    t s!"mode spec {spec} {if silent then "silences" else "shows"}"
      (Compat.modeSilencesPresentation spec == silent)
  -- And the class it is read against: beamer's article mode keeps exactly the
  -- frames the presentation omits, so the same spec must not delete content
  -- outside a deck.
  let art := dvDoc "" ("\\begin{frame}<presentation:0>{Delta Heading}\n" ++
    "Article sentence.\n\\end{frame}")
  t "a mode spec deletes no page outside a presentation class"
    (has (allText art) "Article sentence.")

/-- A declared width is not prose. `\parbox[pos]{width}{text}` is a LaTeX
kernel primitive (latex.ltx, `\@iiiparbox`) whose *first* brace group is a
dimension, so the unknown-command recovery — keep every `{...}` as
text — set the width as visible ink beside the label. `\metroset{key=value}`
is the same class one table over: a theme option setter whose argument is a
key list, kept as a paragraph because the command was unknown.

Both are judged on the shipped glyphs. The dimension case is the one that
motivated the rule: a reader saw `.25` standing in front of a label, and
every test in the suite passed. -/
def boxArgChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageText (src : String) : String := pageTextOf oneFace src
  let allText (src : String) : String := allTextOf oneFace src
  let has := hasStr
  let pb := deck169Frame "\\parbox[t]{.25\\textwidth}{Label one}"
  t "a parbox's width argument is not ink"
    (!has (allText pb) ".25" && !has (allText pb) "textwidth")
  t "a parbox's content is"
    (has (pageText pb) "Label one")
  t "and parbox is not an unknown command"
    (!(warnCodes pb).contains "W0301")
  -- The option run is beamer's `[t]` baseline choice: a parameter the box
  -- model has nowhere to put, noted where the environment notes its own. The
  -- geometry itself is no longer a loss — `\parbox{w}{t}` and `{minipage}{w}`
  -- are the same box (latex.ltx, `\@iiiparbox`), so the width is carried.
  t "the box it declares is honoured, its baseline option noted"
    (!(warnCodes pb).contains "W0104" && (elabStr pb).2.any (·.code == "N0102"))
  -- The full kernel signature: [pos][height][inner-pos]{width}{text}.
  let pb3 := deck169Frame "\\parbox[t][2cm][c]{.25\\textwidth}{Label two}"
  t "a parbox's three option runs all go with it"
    (has (pageText pb3) "Label two" &&
     !has (allText pb3) "2cm" && !has (allText pb3) ".25")
  -- The other two boxes in the arm, which had no test of their own.
  let mb := deck169Frame "\\mbox{Label three}"
  t "an mbox keeps its content and declares no box"
    (has (pageText mb) "Label three" && !(warnCodes mb).contains "W0104" &&
     !(warnCodes mb).contains "W0301")
  let mk := deck169Frame "\\makebox[2cm]{Label four}"
  t "a makebox's width is not ink, and its drop is named"
    (has (pageText mk) "Label four" && !has (allText mk) "2cm" &&
     (warnCodes mk).contains "W0104")
  -- Table and arm must not drift: a name in `boxShape` the arm forgot would
  -- keep its width as prose, the defect this table closed.
  for (name, _, _) in Compat.boxShape do
    t s!"boxShape row '{name}' is a known command"
      (!(warnCodes (deck169Frame s!"\\{name}\{Label five}")).contains "W0301")
  let ms := deck169Frame "\\metroset{block=fill}Body sentence."
  t "a theme option setter's key list is not ink"
    (!has (allText ms) "block=fill" && !has (allText ms) "block")
  t "the setter is named as configuration, not as unknown"
    ((warnCodes ms).contains "W0104" && !(warnCodes ms).contains "W0301")
  t "and the content beside it survives"
    (has (pageText ms) "Body sentence.")


/-- The phantom family on the page. A phantom sets a box of its argument's
size and no ink (plain.tex ll. 1024-1031), so no page may ship the
argument — the defect these rows close shipped `\vphantom{y}`'s letter as a
visible glyph beside the word it was propping, which is why every row here
reads the shipped lines rather than the IR.

The axes divide the family, and `Elab.phantomAxes` is the table that says
which member reserves which — `\vphantom` height and depth, `\hphantom`
width, `\phantom` all three, none of them ink. Getting a column wrong is a
subtler defect than the one here: an `\hphantom` propping a height, or a
`\vphantom` claiming a width, is wrong in a direction no page shows plainly,
so both are read off the diagnostics below rather than trusted.

A line already holds its height and depth from its fonts' declared metrics
at each run's size (`Layout.line_box_glyph_free`: emptying every run's glyphs
changes no component of the line box), so a prop whose argument *borrows*
that face is in force before it is asked for — the hand-written alignment fix
is inert rather than lost, and the note says so. An argument in another face
or size is a triple the line may not carry, and that prop really does go
unreserved: named, never dropped quietly. The width axis has no carrier at
all and is a named loss (W0104) exactly as `\makebox`'s declared width is. -/
def phantomChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageText (src : String) : String := pageTextOf oneFace src
  let allText (src : String) : String := allTextOf oneFace src
  let has := hasStr
  -- The reported defect, on the shape it was reported in: a pair of words
  -- aligned by hand shipped the phantom's letters beside the word.
  let v := "Inventory Value\\vphantom{qy} counted"
  t "a vphantom's argument is not ink" (!has (allText v) "qy")
  t "the words around it are, still one run"
    (has (pageText v) "Value counted")
  t "and vphantom is not an unknown command"
    (!(warnCodes v).contains "W0301")
  t "the height and depth it props are already the line's, so nothing is named"
    ((dvE v).all (·.severity == .note))
  -- The other two axes. Content around them survives; the width does not,
  -- and says so.
  let h := "A\\hphantom{qy}B"
  t "an hphantom's argument is not ink" (!has (allText h) "qy")
  t "the text around it survives" (has (pageText h) "A" && has (pageText h) "B")
  t "a width the engine has no carrier for is a named loss, not a silent one"
    ((warnCodes h).contains "W0104" && !(warnCodes h).contains "W0301")
  let p := "A\\phantom{qy}B"
  t "a phantom's argument is not ink" (!has (allText p) "qy")
  t "and its width is named the same way"
    ((warnCodes p).contains "W0104" && !(warnCodes p).contains "W0301")
  -- Table and arm must not drift: a family member the dispatch forgot would
  -- keep its argument as prose, which is the defect itself. One list
  -- (`Picture.phantomCtrl`), read here and by the label salvage.
  for n in Picture.phantomCtrl do
    let src := s!"A\\{n}\{qy}B"
    t s!"phantomCtrl row '{n}' is a known command"
      (!(warnCodes src).contains "W0301")
    t s!"phantomCtrl row '{n}' ships no argument as ink"
      (!has (allText src) "qy")
    t s!"phantomCtrl row '{n}' keeps the text around it"
      (has (pageText src) "A" && has (pageText src) "B")
    -- The axis table is the arm's only authority on which axes a member
    -- reserves, so the two must agree exactly. A width claimed and not
    -- named, or a height named for a member that props none, is a page
    -- lying about its spacing — quietly, in the second case.
    let axes := (Elab.phantomAxes.lookup n).getD ⟨false, false⟩
    t s!"phantomCtrl row '{n}' names a width exactly when its axis reserves one"
      ((warnCodes src).contains "W0104" == axes.width)
    t s!"phantomCtrl row '{n}' speaks of height and depth only if it props them"
      (((dvE src).any fun d =>
        d.code == "N0100" && hasStr d.message "height and depth") == axes.extent)
  -- `\hphantom` props nothing vertically (its height and depth are zero by
  -- definition), so the inertness note is not its to carry. The subtler
  -- defect the axis table exists to prevent, read off the diagnostics.
  t "an hphantom claims no height it does not reserve"
    ((dvE h).all fun d => !(d.code == "N0100" && hasStr d.message "height and depth"))
  -- The hypothesis under the silence, checked rather than assumed: an
  -- argument in another face or size is a (font, size, raise) triple the
  -- line may not carry, so the prop really does go unreserved — and is
  -- named, not dropped quietly.
  let big := "A\\vphantom{\\Large y}B"
  t "an argument in another size is a named loss, never a silent one"
    ((warnCodes big).contains "W0104" && !has (allText big) "y")
  t "and an argument that only borrows the running face is not named"
    ((dvE "A\\vphantom{\\'e}B").all (·.severity == .note))
  -- A phantom's argument is sizing, so nothing inside it is content: a
  -- label, a reference or a citation in there names nothing and resolves
  -- nothing. The group is never elaborated at all.
  let inner := "A\\vphantom{\\label{ghost}qy}B"
  t "a phantom's group is not elaborated: nothing in it is ink"
    (!has (allText inner) "qy")
  t "and nothing in it is a reference target"
    ((dvE "A\\vphantom{\\label{ghost}}B\\ref{ghost}").any fun d => d.code == "W0349")
  -- TeX takes one token, so a bare word gives its first character and keeps
  -- the rest — `\vphantom value` props a `v` and still ships "alue".
  -- Consuming the whole word would drop content in silence, which is the one
  -- recovery no phantom may choose.
  let bare := "G\\vphantom value H"
  t "a bare word gives the phantom one character, not the word"
    (has (pageText bare) "alue")
  t "and the character it gave is not ink"
    (!has (allText bare) "value")
  t "a phantom with no argument at all is named, never silently empty"
    ((dvE "A\\vphantom\n\n\\par").any fun d => d.code == "E0304")
