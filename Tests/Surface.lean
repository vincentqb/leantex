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
  t "HTML sets the abstract as a classed section with a heading"
    ((page.splitOn "class=\"abstract\"").length == 2 &&
     (page.splitOn "<h2>").length == 2 &&
     (page.splitOn "Abstract").length == 2)
  let md := MarkdownDoc.emit doc
  t "the markdown twin carries the heading and the body"
    ((md.splitOn "## Abstract").length == 2 &&
     (md.splitOn "Invented summary text.").length == 2)

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
  let (doc, _) := elabStr ("\\documentclass{article}\\begin{document}\\section{Introduction}\nBody.\n\\end{document}")
  t "a number never moves the section anchor"
    ((((HtmlDoc.emit {} doc).1).splitOn "<section id=\"introduction\">").length == 2)

/-- LaTeX idioms translate to native declarations. Own function, same reason. -/
def compatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- LaTeX idioms translate to native declarations, each with a note that
  -- shows the shorter spelling. The document compiles as written.
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  let (geoDoc, geoDs) := elabStr (pre "\\usepackage[letterpaper,vmargin=0.5in,hmargin=0.75in,headsep=1in]{geometry}")
  t "compat geometry becomes page" (geoDs.all (·.severity != .error) &&
    geoDoc.page.vmargin == Dim.inch 1 / 2 && geoDoc.page.hmargin == Dim.inch 3 / 4)
  -- Dropped geometry keys change the page: a config loss, a warning, never
  -- a note buried behind -v.
  t "compat geometry names what it dropped as a warning"
    ((elabStr (pre "\\usepackage[headsep=1in]{geometry}")).2.any fun d =>
      d.code == "W0101" && d.severity == .warning && d.message.endsWith "headsep")
  t "compat known package is a note, unknown a warning"
    ((elabStr (pre "\\usepackage{hyperref}")).2.all (·.severity == .note) &&
     warnCodes (pre "\\usepackage{pgfplots}") == ["W0103"])
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
     ((elabStr (pre "\\captionsetup[table]{skip=10pt}")).2.map (·.message)).any
      (fun m => (m.splitOn "'skip'").length == 2))
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
    "\\documentclass{beamer}\n" ++ decls ++
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
    ((elabStr "\\documentclass{scrartcl}\\begin{document}x\\end{document}").1.docClass == "article")
  t "compat linespread is leading"
    ((elabStr (pre "\\linespread{1.04}")).1.page.leading == 1040)
  t "compat heads become one running head"
    ((elabStr (pre "\\ihead{L}\\ohead{\\thepage}")).1.head.map (·.any (· == .pageNumber)) == some true)
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
  t "a reserved built-in cannot be redefined"
    ((warnCodes ("\\documentclass{article}\\define \\textbf(x: content) {\\emph{\\x}}" ++
      "\\begin{document}\\textbf{a}\\end{document}")) == ["W0303"])
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
  t "compat text symbols" ((elabStr "a\\textbar b\\textperiodcentered c").1.body ==
    #[.para #[.text "a|b·c"]])
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
  let beamerPre := pre ("\\usetheme{moloch}\\usefonttheme{professionalfonts}" ++
    "\\setbeamercovered{transparent}\\addtobeamertemplate{block begin}{}{\\smallskip}" ++
    "\\setbeameroption{hide notes}")
  t "compat beamer config skipped without errors" (errCodes beamerPre == [])
  -- \setbeamercovered{transparent}, \usefonttheme{professionalfonts}, and
  -- \setbeameroption{hide notes} no longer count: each agrees with what
  -- the engine already does and warns nothing. \addtobeamertemplate is
  -- the one construct left asking for templating that is not here.
  t "compat beamer config warns once per construct"
    ((warnCodes beamerPre).length == 1 && (warnCodes beamerPre).all (· == "W0104"))
  t "compat usetheme selects the bundle instead of warning"
    ((elabStr beamerPre).1.palette.find? "frametitlebg" |>.isSome)
  t "compat beamer warnings name the native spelling"
    ((elabStr (pre "\\setbeamercolor{normal text}{fg=black}")).2.any fun d =>
      d.code == "W0104" && ((d.help.getD "").splitOn "\\palette").length == 2)
  t "compat ifdefined resolves instead of skipping; untaken branch is silent"
    (warnCodes (pre "\\ifdefined\\x\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") == [])
  t "compat undecidable tex conditional skipped whole, contents included"
    (warnCodes (pre "\\ifx\\x\\y\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") ==
      ["W0104"])
  t "compat def skipped through its body"
    (errCodes (pre "\\makeatletter\\def\\verbatim@font{\\footnotesize\\ttfamily}\\makeatother") == [])
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
  t "elab documentclass" (d6.isEmpty && doc6.docClass == "article" && doc6.classOptions == "x=1")
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
  -- cannot render is named per construct instead of dropped whole.
  t "elab tikzpicture no longer earns the blanket W0307"
    (warnCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["W0334"])
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
    (((elabStr ("\\begin{document}\\begin{tikzpicture}[b/.style={circle}]\n" ++
      "\\node[b] at (0,0) {x};\\end{tikzpicture}\\end{document}")).2.map (·.message)).any
      (fun m => hasStr m "'circle'") &&
     !((elabStr ("\\begin{document}\\begin{tikzpicture}[b/.style={circle}]\n" ++
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
        | .picture pic => pic.shapes == #[.label 0 0 "x" Ir.Color.black 500]
        | _ => false)))
  t "elab picture scale without transform shape leaves the label size alone"
    (((elabStr ("\\begin{document}\\begin{tikzpicture}[scale=0.5]\n" ++
      "\\node at (0,0) {x};\\end{tikzpicture}\\end{document}")).1.body.any
      (fun b => match b with
        | .picture pic => pic.shapes == #[.label 0 0 "x" Ir.Color.black 1000]
        | _ => false)))
  t "elab reserved char" (errCodes "a & b" == ["E0311"])
  t "elab redefine builtin warns and keeps the built-in"
    (warnCodes "\\define \\textbf() {x}\n\\begin{document}y\\end{document}" == ["W0303"])
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
      (·.shapes) == some #[.label cm 0 "aa" Ir.Color.black 1000,
                           .label (2 * cm) 0 "bb" Ir.Color.black 1000])
  t "truncatemacro floors to a whole unit"
    ((picOf (wrap "\\pgfmathtruncatemacro{\\k}{7/2}\\fill (0,0) rectangle (\\k,1);")).map
      (·.shapes) == some #[.rect 0 0 (3 * cm) cm Ir.Color.black])
  t "ifthenelse picks its branch by the comparison"
    ((picOf (wrap "\\foreach \\k in {1,2}{\
\\pgfmathsetmacro{\\c}{ifthenelse(\\k<2,\"black\",\"white\")}\
\\node[text=\\c] at (\\k,0) {x};}")).map
      (·.shapes) == some #[.label cm 0 "x" Ir.Color.black 1000,
                           .label (2 * cm) 0 "x" Ir.Color.white 1000])
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
    (warnCodes (wrap "\\node[draw] at (1,1) {x};") == ["W0334"] &&
      (picOf (wrap "\\node[draw] at (1,1) {x};")).map (·.shapes.size) == some 1)
  t "one construct looped forty times is one diagnostic, not forty"
    (warnCodes (wrap "\\foreach \\x in {1,...,40}{\\draw (\\x,0) circle (1);}") ==
      ["W0334"])
  t "an empty tikzpicture ships no block and no diagnostic"
    ((elabStr (wrap "")).2.isEmpty && (picOf (wrap "")).isNone)

