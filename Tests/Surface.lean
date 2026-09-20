import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

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
    ((page.splitOn "class=\"abstract\"").length == 2 &&
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
    "\\renewenvironment{abstract}{\\vskip 0.075in\\centerline{\\large\\bf Abstract}" ++
    "\\vspace{0.5ex}\\begin{quote}}{\\par\\end{quote}\\vskip 1ex}" ++
    "\\begin{document}\\begin{abstract}Words.\\end{abstract}\\end{document}")
  t "a refused abstract redefinition says the built-in stands styled"
    (vDs.any fun d => d.code == "W0303" &&
      (d.message.splitOn "styling the built-in").length > 1)
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
  -- A \dimexpr value is TeX arithmetic the mapping cannot carry: a named
  -- drop, never a synthesized unreadable \page value (E0321).
  let dimexprDs := (elabStr
    (pre "\\usepackage[footskip=\\dimexpr 0.25in + \\ht\\strutbox\\relax]{geometry}")).2
  t "compat geometry drops a dimexpr value named, not as an error"
    ((dimexprDs.any fun d => d.code == "W0101" && hasStr d.message "footskip") &&
      dimexprDs.all (·.severity != .error))
  -- Dropped geometry keys change the page: a config loss, a warning, never
  -- a note buried behind -v.
  t "compat geometry names what it dropped as a warning"
    ((elabStr (pre "\\usepackage[voffset=1in]{geometry}")).2.any fun d =>
      d.code == "W0101" && d.severity == .warning && d.message.endsWith "voffset")
  t "compat known package is a note, unknown a warning"
    ((elabStr (pre "\\usepackage{hyperref}")).2.all (·.severity == .note) &&
     warnCodes (pre "\\usepackage{pgfplots}") == ["W0103"])
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
    (warnCodes (pre ("\\captionsetup[table]{skip=\\abovecaptionskip}\n" ++
      "\\captionsetup[subtable]{skip=\\abovecaptionskip}")) == ["W0354"] &&
     ((elabStr (pre "\\captionsetup[table]{labelfont=bf}")).2.map (·.message)).any
      (fun m => (m.splitOn "'labelfont'").length == 2))
  t "compat captionsetup skip declares the caption gap"
    ((elabStr (pre "\\captionsetup[table]{skip=10pt}")).1.tokens.find? "captionsep"
        == some { width := { sp := Dim.pt 10 } } &&
     (elabStr (pre "\\captionsetup[table]{skip=10pt}")).2.all (·.severity == .note))
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
  -- \setbeamercovered{transparent} asks for what the engine always does
  -- (dim-not-hide): agreement, not missing configuration — no warning.
  -- A percentage declares the covered colour; anything else (invisible,
  -- dynamic) keeps the warning naming the divergence.
  let themedPre (decls : String) : String :=
    "\\documentclass{beamer}\n\\usetheme{moloch}\n" ++ decls ++
    "\n\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  t "compat setbeamercovered transparent agrees, warning nothing"
    (warnCodes (themedPre "\\setbeamercovered{transparent}") == [])
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
  -- too. Any other `\if…` head (open-ended family, undecidable here)
  -- invalidates the extent and the skip-whole warning stays.
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
  t "compat a foreign conditional inside keeps the skip-whole warning"
    (let ds := (elabStr "\\ifdefined\\a\\ifx\\b\\c\\fi\\fi x").2
     ds.any (·.code == "W0104") && ds.all (·.code != "N0114"))
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
    "\\providecommand{\\maketitle}{}" ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  t "an empty maketitle redefinition renders nothing and is refused"
    (warnCodes emptied == ["W0361"] &&
     Ir.headingLevels (elabStr emptied).1.body == #[0])
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
  let inTitleBlock (doc : Ir.Doc) (p : Ir.Block → Bool) : Bool :=
    doc.body.any fun b => p b ||
      (match b with | .center xs => xs.any p | _ => false)
  t "the refused body's author tabular styles the built-in author line"
    (inTitleBlock aDoc fun b => match b with
      | .para #[.strut h, .styled .bold _] => h == Ir.titleAuthorStrut
      | _ => false)
  t "the trailing vskip becomes the engine's rhythm gap after the block"
    (inTitleBlock aDoc fun b => match b with
      | .spaced g #[] => g == Ir.titleBlockAfter
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
      | .spaced g #[] => g.width == Dim.Length.ofSp (Dim.pt 30)
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
  t "a negative afterskip is a run-in heading: named, skipped, built-in stands"
    (warnCodes ("\\documentclass{article}\\renewcommand{\\paragraph}{" ++
      "\\@startsection{paragraph}{4}{\\z@}{1.5ex}{-1em}{\\normalsize\\bf}}" ++
      "\\begin{document}\\paragraph{P}\nx\\end{document}") == ["W0104"])
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
    ((elabStr ("\\documentclass{article}\\palette{m = #888888}\\begin{document}" ++
      "a {\\color{m}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0x88, g := 0x88, b := 0x88 } (some "m") #[.text "b"], .text " c"]])
  -- `\color`'s argument is a palette *expression*: the `!`-mix grammar lives
  -- once, in `Palette.resolve`, and the bare-name arm routes through it.
  -- Before, `\color{m!50!black}` minted '\m!50!black' as a control word and
  -- the mix warned W0301 with its content losing the colour (run-verified
  -- wrong output). A computed mix carries no CSS var name, as `\textcolor`
  -- already holds.
  t "compat color mix routes through the palette resolver"
    ((elabStr ("\\documentclass{article}\\palette{m = #888888}\\begin{document}" ++
      "a {\\color{m!50!black}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0x44, g := 0x44, b := 0x44 } none #[.text "b"],
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
  t "compat inert commands vanish"
    ((elabStr "a\\noindent\\relax b").2.isEmpty)
  -- The silent list is only for constructs that change nothing the engine
  -- models; one that does (justification, hyphenation language, furniture)
  -- must name its loss instead of vanishing.
  t "compat raggedright names its loss instead of vanishing"
    ((elabStr "a\\raggedright b").2.any (·.code == "W0104"))
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
    ((elabStr (pre "\\setbeamercolor{normal text}{fg=black}")).2.any fun d =>
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
  t "alignment declarations name their loss instead of W0301"
    (let ds := (elabStr "{\\flushleft a} {\\raggedleft b} {\\flushright c}").2
     ds.all (fun d => d.code != "W0301") && ds.any (fun d => d.code == "W0104"))
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
  t "compat koma section spacing"
    (((koma.1.styles.find? "section").bind (·.before)).map (·.width) == some { sp := Dim.pt 6 })
  t "compat koma section rule" (((koma.1.styles.find? "section").bind (·.rule)).map (·.2) == some (some "ink"))
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

/-- The package-claim index: every package in `Compat.nativePackages` ships
`tests/compat-index/<pkg>.txt`, its user-facing command surface as
reviewable data — one line per command, `<place> <annotation> <call>`,
place `pre` | `body`, annotation `impl` | `refuse:<code>`. An `impl` call
elaborates without W0301/W0302; a `refuse:` call fires exactly its named
code, so a refusal that silently stops warning fails too. Adding a package
to the list without its index file fails: the claim and its evidence
arrive together. -/
def compatIndexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let dir : System.FilePath := "tests/compat-index"
  for pkg in Compat.nativePackages do
    let path := dir / (pkg ++ ".txt")
    let found ← path.pathExists
    check ref s!"compat index: '{pkg}' is claimed native but has no index file" found
    unless found do continue
    let content ← IO.FS.readFile path
    for line in content.splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      let place := ((line.splitOn " ").headD "")
      let rest := (line.drop place.length).toString.trimAscii.toString
      let ann := ((rest.splitOn " ").headD "")
      let call := (rest.drop ann.length).toString.trimAscii.toString
      let src := if place == "pre" then
          s!"\\documentclass\{article}\n\\usepackage\{{pkg}}\n{call}\n\\begin\{document}\nx\n\\end\{document}"
        else
          s!"\\documentclass\{article}\n\\usepackage\{{pkg}}\n\\begin\{document}\n{call}\n\\end\{document}"
      let codes := (elabStr src).2.map (·.code)
      if place != "pre" && place != "body" then
        failures ref s!"compat index {pkg}: unreadable place in: {line}"
      else if ann == "impl" then
        check ref s!"compat index {pkg}: '{call}' is marked impl but warns unknown"
          (!codes.contains "W0301" && !codes.contains "W0302")
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
    ("linespread", wrap "\\linespread{1.05}" "x", wrap "\\page{ leading = 1.05 }" "x"),
    ("setstretch", wrap "\\setstretch{1.3}" "x", wrap "\\page{ leading = 1.3 }" "x"),
    ("onehalfspacing", wrap "\\onehalfspacing" "x", wrap "\\page{ leading = 1.25 }" "x"),
    ("definecolor", wrap "\\definecolor{c}{HTML}{112233}" "x",
      wrap "\\palette{ c = #112233 }" "x"),
    ("colorlet", wrap "\\definecolor{c}{HTML}{112233}\\colorlet{d}{c}" "x",
      wrap "\\palette{ c = #112233 }\\palette{ d = c }" "x"),
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
      wrap "\\style{itemize}{ indent = 2em }" "x")]
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
environment follows the same rule as the `@input:` wrapper — an inline body
stays in its sentence, block content breaks it. -/
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
     | #[.verbatim none s] => s.trimAscii.toString == "literal line one"
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
     | #[.frame _ _ _ body] => body.any fun b => (blockText b).endsWith "Body survives."
     | _ => false)
  t "unclosed bracket in a frame warns" (fDs.any (·.code == "W0310"))
  -- a bracket opening the frame's content is content, not an option
  t "frame content starting with a bracket survives"
    (match (elabStr (deck169Body "\\begin{frame}\n[1] Reference survives.\n\\end{frame}")).1.body with
     | #[.frame _ _ _ #[.para xs]] => Ir.plainText xs == "[1] Reference survives."
     | _ => false)
  -- options on the begin line are still arguments, bracket runs included
  t "frame options on the begin line are consumed, never content"
    (match (elabStr (deck169Body "\\begin{frame}[plain][t]{T}\nbody\n\\end{frame}")).1.body with
     | #[.frame title _ _ #[.para xs]] =>
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
  -- cannot render is named per construct instead of dropped whole; an
  -- all-refused picture adds the placeholder's W0362.
  t "elab tikzpicture no longer earns the blanket W0307"
    (warnCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["W0362"] &&
     errCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["E0333"])
  -- The boundary is named, never silent — for the option bracket too: a
  -- picture option outside the subset is W0334, an unusable value inside
  -- it E0333, exactly as the statement walk already has it.
  t "elab picture option outside the subset is named"
    (warnCodes
      "\\begin{tikzpicture}[banana]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}"
      == ["W0334"])
  t "elab picture scale that cannot hold is named"
    (errCodes
      "\\begin{tikzpicture}[scale=0]\\fill (0,0) rectangle (1,1);\\end{tikzpicture}"
      == ["E0333"])
  -- Named option bundles (`name/.style={...}`) expand where used, so a
  -- loss inside a bundle is named by its real spelling, never the
  -- bundle's; a bundle of subset options loses nothing.
  t "elab picture style bundle of subset options absorbs silently"
    ((elabStr ("\\begin{document}\\begin{tikzpicture}[lbl/.style={font=\\small, text=black}]\n" ++
      "\\node[lbl] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
  t "elab picture style bundle names its outside options, not itself"
    (((elabStr ("\\begin{document}\\begin{tikzpicture}[b/.style={ellipse}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'ellipse'") &&
     !((elabStr ("\\begin{document}\\begin{tikzpicture}[b/.style={ellipse}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'b'"))
  t "elab picture style bundle referencing an earlier bundle expands"
    ((elabStr ("\\begin{document}\\begin{tikzpicture}[a/.style={font=\\small}, b/.style={a}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.isEmpty)
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
    ((elabStr verbSrc).1.body == #[.verbatim none "\ndef f(n):\n    return n\n\nf(2)  # two spaces\n"] &&
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
    | .spaced before _ => before.width.ex == 1500
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

/-- The picture subset's boundary is named, never silent: a construct
outside the subset is W0334 naming it, an unreadable expression, range, or
colour inside it is E0333 — and the supported shapes around either still
elaborate (the nothing-silently-skipped contract, as a test). The unroll
and arithmetic facts are checked through the IR the elaborator ships. -/
def pictureElabChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String :=
    "\\palette{ grid = #2A6F4E }\\begin{document}\\begin{tikzpicture}" ++
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
named in `standardOrder`'s docstring. -/
def bibStyleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let entry (kind : String) (fields : List (String × String)) : Bib.Entry :=
    { kind
      key := "k1"
      fields := fields.toArray
      pos := {} }
  let render (e : Bib.Entry) : String :=
    Ir.plainText (Bib.renderEntry {} (Bib.standardOrder e.kind) e)
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
      "Alex Doe. The Grand Book. Example Press, Third edition, 2020.")
  t "bibstyle: inproceedings takes In booktitle, pages spelled out"
    (render (entry "inproceedings"
      [("author", "Doe, Alex"), ("title", "On Tests"),
       ("booktitle", "Proceedings of Examples"), ("pages", "1--10"),
       ("year", "2021")]) ==
      "Alex Doe. On tests. In Proceedings of Examples, pages 1–10, 2021.")
  t "bibstyle: misc renders howpublished and a linked URL"
    (let out := Bib.renderEntry {} (Bib.standardOrder "misc") (entry "misc"
      [("author", "Doe, Alex"), ("title", "A Web Thing"),
       ("howpublished", "Online"), ("year", "2022"),
       ("url", "https://example.org/x")])
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
      ("year", "2019")]) == "Sam Roe, editors. Edited. 2019.")
  let e1 : Bib.Entry := entry "article"
    [("author", "Doe, Alex and Roe, Sam"), ("year", "2024")]
  let r1 : Bib.Resolved := { key := "k1", position := 3, entry := e1 }
  let e2 : Bib.Entry :=
    { kind := "misc"
      key := "k2"
      fields := #[("author", "Poe, Kim and others"), ("year", "2020")]
      pos := {} }
  let r2 : Bib.Resolved := { key := "k2", position := 1, entry := e2 }
  let cite (s : Bib.CiteStyle) (tx : Bool) (ps : Array (Option Bib.Resolved)) :=
    Ir.plainText (Bib.renderCite s tx ps)
  t "bibstyle: numeric citep brackets and joins"
    (cite .numeric false #[some r1, some r2] == "[3, 1]")
  t "bibstyle: numeric citet names then bracket"
    (cite .numeric true #[some r1] == "Doe and Roe [3]")
  t "bibstyle: author-year citep parenthesizes with semicolons"
    (cite .authorYear false #[some r1, some r2] ==
      "(Doe and Roe, 2024; Poe et al., 2020)")
  t "bibstyle: author-year citet puts the year in parens"
    (cite .authorYear true #[some r1, some r2] ==
      "Doe and Roe (2024); Poe et al. (2020)")
  t "bibstyle: an unresolved key prints ? in place"
    (cite .numeric false #[some r1, none] == "[3, ?]")
  t "bibstyle: citation pieces link to the entry anchor"
    ((Bib.renderCite .numeric false #[some r1]).any fun x => match x with
      | .link u _ => u == "#ref-k1"
      | _ => false)
  t "bibstyle: named styles pair the axes; unknown is none"
    (((Bib.Style.named "unsrtnat").map (fun s => (s.cite, s.sort)))
        == some (.numeric, .citation) &&
      ((Bib.Style.named "plainnat").map (fun s => (s.cite, s.sort)))
        == some (.authorYear, .authorYear) &&
      ((Bib.Style.named "plain").map (fun s => (s.cite, s.sort)))
        == some (.numeric, .authorYear) &&
      (Bib.Style.named "mystery").isNone)
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
    (Ir.plainText #[.cite false #["a", "b"]] == "?, ?")
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
  let doc (style : Option String) : Ir.Doc :=
    { body := #[
        .para #[.text "x ", .cite false #["b"], .text " y ", .cite true #["a"]],
        .para #[.cite false #["c", "b"]],
        .bibliography "refs" style #[]] }
  let run (style : Option String) := Bib.apply #[("refs", bib)] (doc style)
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
      #["Sam Roe. Second. 2020.", "Alex Doe. First. 2024.", "Kim Poe. Third. 2022."])
  -- plainnat: the same document, the other record.
  let (outP, dsP) := run (some "plainnat")
  t "apply: plainnat sorts by author then year, marks nothing"
    ((itemsOf outP).map (·.key) == #["a", "c", "b"] &&
      (itemsOf outP).all (·.marker.isNone))
  t "apply: plainnat cites author-year"
    (paraText outP 0 == "x (Roe, 2020) y Doe (2024)")
  t "apply: style independence — each entry's content identical across styles"
    (dsP.isEmpty &&
      (itemsOf outU).all fun i =>
        ((itemsOf outP).find? (·.key == i.key)).map (fun j => Ir.plainText j.content)
          == some (Ir.plainText i.content))
  -- The three diagnostics, each with its contract.
  let (outG, dsG) := Bib.apply #[("refs", bib)]
    { body := #[.para #[.cite false #["ghost", "a"]],
        .bibliography "refs" none #[]] }
  t "apply: an unknown key warns W0351 and shows ? beside its neighbours"
    ((dsG.map (·.code)) == #["W0351"] && paraText outG 0 == "[?, 1]")
  let (outB, dsB) := Bib.apply #[("refs", "@misc{broken, year = ?}\n" ++ bib)]
    { body := #[.para #[.cite false #["a"]], .bibliography "refs" none #[]] }
  t "apply: a malformed entry warns W0352 at its .bib position, rest kept"
    (dsB.map (·.code) == #["W0352"] &&
      (dsB[0]?.bind (·.span)).map (·.file) == some "refs" &&
      (itemsOf outB).map (·.key) == #["a"])
  let (_, dsM) := run (some "mystery")
  t "apply: an unknown style warns W0353 and falls back to the record"
    (dsM.map (·.code) == #["W0353"])
  t "apply: a document with no bibliography marker is untouched"
    (Bib.apply #[("refs", bib)] { body := #[.para #[.cite false #["a"]]] } ==
      ({ body := #[.para #[.cite false #["a"]]] }, #[]))

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
  let run (name : String) :
      IO (Ir.Doc × Array Diag × Array (String × Option String × Pos)) := do
    let path := s!"tests/corpus/sty-parity/{name}.tex"
    let src ← IO.FS.readFile path
    let (raws, _) := Parse.parse path (Lex.lex path src).1
    let (raws, inputDs, spliced) ← Input.expandInputs path raws
    let (doc, ds) := Elab.runRaws path raws
    -- N0020 built after elaboration, exactly as Main.frontend builds it.
    let ds := ds ++ spliced.map fun (sty, srcF, pos) =>
      Compat.styRead (srcF.getD path) sty pos ds
    return (doc, inputDs ++ ds, spliced)
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
