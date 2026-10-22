module

public import Tests.ParamCensus
public import LeanTex.Cli.FaceUse
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.FontDiscovery

public section

open LeanTex.Core LeanTex.Cli

/-! A setting the document declares that nothing it sets uses is named once where it stands
(W0449), judged from what the build reads; a package's, a class's or a theme's never is. -/

namespace Tests.UnusedSettings

/-- The unused-setting losses of a source, elaborated. -/
def unused (src : String) : Array Diag := (elabStr src).2.filter (·.kind == .W0449)

def article (pre body : String) : String :=
  s!"\\documentclass\{article}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

def deck (pre body : String) : String :=
  s!"\\documentclass\{beamer}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

/-- A probe colour no default spells. -/
def probeColor : String := "\\definecolor{probeink}{HTML}{8A2BE2}"

/-- Each declaration a document can leave unread, in a document that reads none of it, with the
subject its loss is keyed by. -/
def unreadCases : List (String × String × String) :=
  [("an xcolor colour", article probeColor "Words.", "unused:color:probeink"),
   ("a colour mixed from another", article "\\colorlet{probeink}{red!40}" "Words.",
     "unused:color:probeink"),
   ("a palette colour", article "\\palette{ probeink = #8A2BE2 }" "Words.",
     "unused:color:probeink"),
   ("a list style", article "\\style{itemize}{ gap = 4pt }" "Words.", "unused:style:itemize"),
   ("a heading style", article "\\style{section}{ before = 30pt }" "Words.",
     "unused:style:section"),
   ("a list level", article "\\usepackage{enumitem}\\setlist[enumerate,2]{leftmargin=4em}"
     "\\begin{enumerate}\\item Alpha\\end{enumerate}", "unused:style:enumerate2"),
   ("link colours", article "\\usepackage{hyperref}\\hypersetup{colorlinks, linkcolor=red}"
     "Words.", "unused:style:link,url,cite"),
   ("a beamer block font", deck "\\setbeamerfont{block title}{size=\\tiny}"
     "\\begin{frame}{Title}Words.\\end{frame}", "unused:style:block"),
   ("a beamer item template", deck "\\setbeamertemplate{itemize item}{\\textbullet}"
     "\\begin{frame}{Title}Words.\\end{frame}", "unused:style:itemize"),
   ("listing defaults", article "\\usepackage{listings}\\lstset{numbers=left}" "Words.",
     "unused:listing:lstset"),
   ("minted defaults", article "\\usepackage{minted}\\setminted{linenos}" "Words.",
     "unused:listing:setminted"),
   ("a lexer's minted defaults", article "\\usepackage{minted}\\setminted[python]{linenos}"
     "\\begin{minted}{bash}\necho probe\n\\end{minted}", "unused:listing:setminted:python"),
   ("inline-code defaults", article "\\usepackage{minted}\\setmintedinline{fontsize=\\small}"
     "\\begin{minted}{python}\nx = 1\n\\end{minted}", "unused:listing:setmintedinline"),
   ("a colour only an uncalled definition names",
     article (probeColor ++ "\\newcommand{\\probebox}[1]{\\colorbox{probeink}{#1}}") "Words.",
     "unused:color:probeink"),
   ("a colour only an honoured listing caption's words name", article
     ("\\usepackage{listings}" ++ probeColor)
     "\\begin{lstlisting}[caption={A probeink example}]\nx = 1\n\\end{lstlisting}", "unused:color:probeink"),
   ("a colour only a picture style no picture reads names",
     article ("\\usepackage{tikz}" ++ probeColor ++ "\\tikzset{probe/.style={fill=probeink}}") "Words.",
     "unused:color:probeink"),
   ("a colour only a word of a refused command's prose spells", article probeColor
     "Words \\probeunknowncmd{under the open probeink sky} more.", "unused:color:probeink"),
   ("minted defaults only an unused minted environment's definition reads", article
     "\\usepackage{minted}\\setminted{linenos}\\newminted{python}{}" "Words.",
     "unused:listing:setminted")]

/-- Each declaration with content that reads it. -/
def readCases : List (String × String) :=
  [("a colour painting text", article probeColor "\\textcolor{probeink}{Words.}"),
   ("a colour in a mix", article probeColor "\\textcolor{probeink!50!white}{Words.}"),
   ("a colour as a declaration", article probeColor "{\\color{probeink} Words.}"),
   ("a colour grounding a box", article probeColor "\\colorbox{probeink}{Words.}"),
   ("a colour its own command sets", article probeColor "\\probeink{Words.}"),
   ("a colour another declares from", article (probeColor ++ "\\colorlet{probedeep}{probeink!60!black}")
     "\\textcolor{probedeep}{Words.}"),
   ("a colour a picture paints", article ("\\usepackage{tikz}" ++ probeColor)
     "\\begin{tikzpicture}\\fill[probeink] (0,0) rectangle (1,1);\\end{tikzpicture}"),
   ("a colour a beamer element takes", deck (probeColor ++ "\\setbeamercolor{frametitle}{fg=probeink}")
     "\\begin{frame}{Title}Words.\\end{frame}"),
   ("a list style", article "\\style{itemize}{ gap = 4pt }"
     "\\begin{itemize}\\item Alpha\\end{itemize}"),
   ("a second-level list style", article "\\style{itemize2}{ gap = 4pt }"
     "\\begin{itemize}\\item Alpha\\begin{itemize}\\item Beta\\end{itemize}\\end{itemize}"),
   ("a numbered list style an algorithm's lines read", article
     "\\usepackage{algpseudocode}\\style{enumerate}{ gap = 4pt }"
     "\\begin{algorithmic}[1]\\State alpha\\end{algorithmic}"),
   ("a heading style", article "\\style{section}{ before = 30pt }" "\\section{Opening}Words."),
   ("a heading style a frame title reads on the web page", deck "\\style{section}{ before = 30pt }"
     "\\begin{frame}{Title}Words.\\end{frame}"),
   ("an abstract's heading style", article "\\style{section}{ before = 30pt }"
     "\\begin{abstract}Words.\\end{abstract}"),
   ("link colours", article "\\usepackage{hyperref}\\hypersetup{colorlinks}"
     "\\href{https://example.org}{A place}."),
   ("a beamer block font", deck "\\setbeamerfont{block title}{size=\\tiny}"
     "\\begin{frame}{Title}\\begin{alertblock}{Alert}Words.\\end{alertblock}\\end{frame}"),
   ("listing defaults", article "\\usepackage{listings}\\lstset{numbers=left}"
     "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"),
   ("a lexer's minted defaults", article "\\usepackage{minted}\\setminted[python]{linenos}"
     "\\begin{minted}{python}\nx = 1\n\\end{minted}"),
   ("inline-code defaults", article "\\usepackage{minted}\\setmintedinline{fontsize=\\small}"
     "Inline \\mintinline{python}{x = 1} code."),
   ("a colour a diagram's arrow takes", article ("\\usepackage{tikz-cd}" ++ probeColor)
     "\\begin{tikzcd} A \\arrow[r, probeink] & B \\end{tikzcd}"),
   ("a colour a displayed diagram takes", article ("\\usepackage{tikz-cd}" ++ probeColor)
     "\\[\\begin{tikzcd} A \\arrow[r, probeink] & B \\end{tikzcd}\\]"),
   ("a colour the pictures' preamble names", article ("\\usepackage{pgfplots}" ++ probeColor ++
     "\\pgfplotsset{every axis plot/.append style={color=probeink}}")
     "\\begin{tikzpicture}\\begin{axis}\\addplot coordinates {(0,0) (1,1)};\\end{axis}\\end{tikzpicture}"),
   ("a title page style an author alone reads", article
     "\\author{Probe Author}\\date{1 January 2020}\\style{titlepage}{ author-font = {\\Huge} }"
     "\\maketitle Words."),
   ("a beamer author font a title page reads", deck
     "\\author{Probe Author}\\setbeamerfont{author}{size=\\tiny}" "\\begin{frame}\\titlepage\\end{frame}"),
   ("a beamer block colour a box reads", deck
     "\\usepackage{tcolorbox}\\setbeamercolor{block title}{bg=red,fg=white}"
     "\\begin{frame}{Title}\\begin{tcolorbox}[title=Probe box]Words.\\end{tcolorbox}\\end{frame}"),
   ("a colour declared inside a paragraph, which it ends", article ""
     ("Words.\n" ++ probeColor ++ "\nMore words.")),
   ("listing defaults an inline listing reads", article "\\usepackage{listings}\\lstset{numbers=left}"
     "Inline \\lstinline|x = 1| code."),
   ("a list macro's definition", article
     "\\makeatletter\\def\\@listii{\\leftmargin 8em \\topsep 30pt}\\makeatother"
     "\\begin{quote}Outer.\\begin{quote}Inner.\\end{quote}\\end{quote}"),
   ("a colour whose name holds a dot", article "\\definecolor{probe.ink}{HTML}{8A2BE2}"
     "\\textcolor{probe.ink!50!white}{Words.}"),
   ("minted defaults an environment minted's definer makes reads", article
     "\\usepackage{minted}\\setminted{linenos}\\newminted{python}{}"
     "\\begin{pythoncode}\nx = 1\n\\end{pythoncode}"),
   ("a lexer's minted defaults a named minted environment reads", article
     "\\usepackage{minted}\\setminted[python]{linenos}\\newminted[probecode]{python}{}"
     "\\begin{probecode}\nx = 1\n\\end{probecode}"),
   ("minted defaults a command minted's definer makes reads", article
     "\\usepackage{minted}\\setminted{linenos}\\newmint{python}{}" "\\python|x = 1|"),
   ("inline-code defaults an inline command minted's definer makes reads", article
     "\\usepackage{minted}\\setmintedinline{fontsize=\\small}\\newmintinline{python}{}"
     "Inline \\pythoninline|x = 1| code.")]

/-- Each colour named only by a construct the engine refuses or cannot resolve, with that refusal's
code: the refusal is the one accounting, and the colour is the document's in use. -/
def refusedCases : List (String × DiagCode × String) :=
  [("an unknown command", .W0301, article probeColor "\\probebox{probeink}{Words.}"),
   ("an unknown preamble command", .W0301,
     article (probeColor ++ "\\titleformat{\\section}{\\color{probeink}}{\\thesection}{1em}{}")
       "\\section{Opening}Words."),
   ("a refused listing key", .W0110, article
     ("\\usepackage{listings}" ++ probeColor ++ "\\lstset{keywordstyle=\\color{probeink}}")
     "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"),
   ("a refused box key", .W0104, article ("\\usepackage{tcolorbox}" ++ probeColor)
     "\\begin{tcolorbox}[colback=probeink]Words.\\end{tcolorbox}"),
   ("an unknown environment's options", .W0302, article probeColor
     "\\begin{probeframe}[color=probeink]Words.\\end{probeframe}"),
   ("a refused caption key", .W0104, article
     ("\\usepackage{caption}" ++ probeColor ++ "\\captionsetup{labelfont={color=probeink}}")
     "\\begin{figure}Words.\\caption{A caption.}\\end{figure}"),
   ("a refused list option", .W0104, article ("\\usepackage{enumitem}" ++ probeColor)
     "\\begin{enumerate}[font=\\color{probeink}]\\item Alpha\\end{enumerate}"),
   ("text standing before the document", .E0313, article
     ("\\usepackage{tikz}" ++ probeColor ++ "\\tikzstyle{probe}=[fill=probeink]")
     "\\begin{tikzpicture}\\fill[probe] (0,0) rectangle (1,1);\\end{tikzpicture}"),
   ("a refused column modifier", .W0104, article ("\\usepackage{colortbl}" ++ probeColor)
     "\\begin{tabular}{>{\\columncolor{probeink}}c}x\\end{tabular}"),
   ("a formula refused whole", .W0012, article probeColor "A formula $\\mathcolor{probeink}{x^2}$."),
   ("a link colour read before the colour is declared", .E0326, article
     ("\\usepackage{hyperref}\\hypersetup{colorlinks, urlcolor=probeink}" ++ probeColor)
     "\\href{https://example.org}{A place}."),
   ("a refused hyperref key", .W0104, article
     ("\\usepackage{hyperref}" ++ probeColor ++ "\\hypersetup{probecolor=probeink}") "Words."),
   ("a refused hyperref package option", .W0104, article
     (probeColor ++ "\\usepackage[probecolor=probeink]{hyperref}") "Words."),
   ("a dropped beamer template", .E0111, deck
     (probeColor ++ "\\setbeamertemplate{probe element}{\\color{probeink}Probe}")
     "\\begin{frame}{Title}Words.\\end{frame}"),
   ("a style value refused as malformed", .E0321, article
     (probeColor ++ "\\style{section}{ rule-position = probeink }") "\\section{Opening}Words."),
   ("a title slot off the title page", .E0321, article
     (probeColor ++ "\\style{section}{ slot = { content = {\\color{probeink} Probe} } }")
     "\\section{Opening}Words."),
   ("a style key the element never reads", .W0104, article
     (probeColor ++ "\\style{section}{ align = probeink }") "\\section{Opening}Words."),
   ("a refused listing key setting a font after the colour", .W0110, article
     ("\\usepackage{listings}" ++ probeColor ++ "\\lstset{keywordstyle=\\color{probeink}\\bfseries}")
     "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"),
   ("a refused listing key setting a font before the colour", .W0110, article
     ("\\usepackage{listings}" ++ probeColor ++ "\\lstset{keywordstyle=\\bfseries\\color{probeink}}")
     "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"),
   ("a refused caption key setting a font after the colour", .W0104, article
     ("\\usepackage{caption}" ++ probeColor ++ "\\captionsetup{probefont={\\color{probeink}\\bfseries}}")
     "\\begin{figure}Words.\\caption{A caption.}\\end{figure}"),
   ("an unknown command's page colour", .W0301, article probeColor
     "Words \\probeunknowncmd{\\pagecolor{probeink}} more."),
   ("an unknown command's dropped options", .W0301, article probeColor
     "Words \\probeunknowncmd[color=probeink]{more}."),
   ("an unsupported package's options", .W0103, article
     (probeColor ++ "\\usepackage[linkcolor=probeink]{probenopackage}") "Words."),
   ("a beamer sub-theme package's options", .W0104, deck
     (probeColor ++ "\\usepackage[accent=probeink]{beamercolorthemeprobe}")
     "\\begin{frame}{Title}Words.\\end{frame}")]

/-- Each kind of declaration nothing reads is named once at its site, keyed by what it declares;
one something reads is not. -/
def firesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (what, src, subject) in unreadCases do
    let ds := unused src
    t s!"unused settings: {what} nothing reads is named once, keyed by it ({ds.map (·.subject)})"
      (ds.size == 1 && ds.all fun d => d.kind == .W0449 && d.subject == some subject)
    t s!"unused settings: {what} is named where it stands, as a warning with help"
      (ds.all fun d => d.span.any (·.pos.line == 2) && d.severity == .warning && d.help.isSome)
  for (what, src) in readCases do
    t s!"unused settings: {what} read by the document is not named ({(unused src).map (·.subject)})"
      (unused src).isEmpty
  for (what, code, src) in refusedCases do
    let ds := (elabStr src).2
    t s!"unused settings: a colour {what} names is that refusal's, never named unused ({ds.map (·.kind.code)})"
      (ds.any (·.kind == code) && !ds.any (·.kind == .W0449))
  let palette := unused (article "\\palette{ probeone = #8A2BE2, probetwo = #2BE28A }"
    "\\textcolor{probetwo}{Words.}")
  t "unused settings: the help names the entry of a declaration that declares several"
    (palette.size == 1 && palette.all fun d => d.help.any (·.startsWith "delete the declaration of 'probeone'"))
  let twice := unused (article (probeColor ++ "\n" ++ probeColor) "Words.")
  t "unused settings: a colour declared twice and never read is one loss at both sites"
    (((Diag.foldRepeats twice).filter (·.severity == .warning)).size == 1)
  let later := unused (article "\\usepackage{listings}"
    "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}\n\\lstset{numbers=left}\nWords.")
  t "unused settings: listing defaults after the last listing are named"
    (later.map (·.subject) == #[some "unused:listing:lstset"])
  let both := unused (article "\\definecolor{probeone}{HTML}{8A2BE2}\\definecolor{probetwo}{HTML}{2BE28A}"
    "\\textcolor{probetwo}{Words.}")
  t "unused settings: of two colours, the one nothing paints is the one named"
    (both.map (·.subject) == #[some "unused:color:probeone"])

/-- A declaration in a package, class or theme file is the file's, and one in a file the document
inputs is the document's; one a loading command lowers, or a definition's replacement text makes,
is not the document's either. -/
def scopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let declared := "\n" ++ probeColor ++ "\n\\style{itemize}{ gap = 4pt }\n\\usepackage{listings}" ++
    "\\lstset{numbers=left}\n\\fonts{ mono = \"Probe Mono\" }\n"
  let spliced (cls child : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let raws := parse "root.tex" s!"\\documentclass\{{cls}}\n" ++
      #[Parse.Raw.env (Parse.inputEnv child) (parse child declared) {}] ++
      parse "root.tex" "\\begin{document}\nWords.\n\\end{document}"
    Elab.runRawsSpanned "root.tex" raws
  for (what, cls, child) in [("a package", "article", "probe.sty"),
      ("a class", "article", "probe.cls"), ("a local theme", "beamer", "beamerthemeprobe.sty")] do
    let (_, ds, spans) := spliced cls child
    t s!"unused settings: {what}'s unread declarations are its own, never named"
      (!ds.any (·.kind == .W0449) && spans.faces.isEmpty)
  let nested (cls pkg inner : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let raws := parse "root.tex" s!"\\documentclass\{{cls}}\n" ++
      #[Parse.Raw.env (Parse.inputEnv pkg)
        #[Parse.Raw.env (Parse.inputEnv inner) (parse inner declared) {}] {}] ++
      parse "root.tex" "\\begin{document}\nWords.\n\\end{document}"
    Elab.runRawsSpanned "root.tex" raws
  for (what, cls, pkg, inner) in [("a package", "article", "probe.sty", "probecolors.tex"),
      ("a package", "article", "probe.sty", "probe.cfg"),
      ("a local theme", "beamer", "beamerthemeprobe.sty", "probetheme.tex")] do
    let (_, ds, spans) := nested cls pkg inner
    t s!"unused settings: a file {what} inputs is the package's, its declarations never named ({inner}: {(ds.filter (·.kind == .W0449)).map (·.subject)})"
      (!ds.any (·.kind == .W0449) && spans.faces.isEmpty)
  let (_, ds, spans) := spliced "article" "part.tex"
  t s!"unused settings: an input file's unread declarations are the document's, named in it ({ds.filter (·.kind == .W0449) |>.map (·.subject)})"
    ((ds.filter (·.kind == .W0449)).size == 3 &&
      ds.all fun d => d.kind != .W0449 || d.span.any (·.file == "part.tex"))
  t "unused settings: an input file's face is judged with the face set"
    (spans.faces.map (·.1) == #["mono"] && spans.faces.all (·.2.file == "part.tex"))
  let loaders := [("a link-colour package option", article "\\usepackage[colorlinks]{hyperref}" "Words."),
    ("a font package", article "\\usepackage{courier}" "Words."),
    ("a shipped theme", deck "\\usetheme{moloch}" "\\begin{frame}Words.\\end{frame}")]
  for (what, src) in loaders do
    let (doc, ds, spans) := Elab.runRawsSpanned "t" (parse "t" src)
    t s!"unused settings: {what} declares nothing of the document's own"
      (!ds.any (·.kind == .W0449) && spans.faces.isEmpty && doc.body.size ≥ 1)
  t "unused settings: a colour a document's macro declares where it is called is the macro's"
    (unused (article ("\\newcommand{\\probesetup}{" ++ probeColor ++ "}") "\\probesetup Words.")).isEmpty
  let shared := parse "root.tex" "\\documentclass{article}\n" ++
    #[Parse.Raw.env (Parse.inputEnv "probe.sty")
      #[Parse.Raw.env (Parse.inputEnv "shared.tex") (parse "shared.tex" declared) {}] {},
      Parse.Raw.env (Parse.inputEnv "shared.tex") (parse "shared.tex" declared) {}] ++
    parse "root.tex" "\\begin{document}\nWords.\n\\end{document}"
  let lengthIn (child : String) : Array Diag :=
    let raws := parse "root.tex" "\\documentclass{article}\n" ++
      #[Parse.Raw.env (Parse.inputEnv child)
        (parse child "\\newlength{\\probelen}\n\\setlength{\\probelen}{3pt}\n") {}] ++
      parse "root.tex" "\\begin{document}\nWords.\n\\end{document}"
    (Elab.runRawsSpanned "root.tex" raws).2.1.filter fun d =>
      d.subject == some "param:setlength:probelen"
  t s!"unused settings: a length a package sets and nothing reads is the package's ({(lengthIn "probe.sty").map (·.message)})"
    (lengthIn "probe.sty").isEmpty
  t s!"unused settings: one the document's own input sets is named ({(lengthIn "part.tex").size})"
    ((lengthIn "part.tex").size == 1)
  let (_, ds, spans) := Elab.runRawsSpanned "root.tex" shared
  t s!"unused settings: a file the document inputs is its own though a package inputs it too ({(ds.filter (·.kind == .W0449)).map (·.subject)})"
    ((ds.filter (·.kind == .W0449)).size == 3 && spans.faces.size == 1)
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "probepkg.sty")
      "\\ProvidesPackage{probepkg}\n\\newcommand{\\probeload}{\\input{probeshared}}\n"
    IO.FS.writeFile (dir / "probeshared.tex") (probeColor ++ "\n")
    let named (body : String) : IO (Array Diag) := do
      let root := (dir / "root.tex").toString
      let src := article body "Words."
      let (executed, _, _) ← Input.expandInputs root (Parse.parse root (Lex.lex root src).1).1
      let (_, ds, _) := Elab.runPrepared root (Elab.prepareExecuted root executed)
      return ds.filter (·.kind == .W0449)
    let viaPackage ← named "\\usepackage{probepkg}\n\\probeload"
    t s!"unused settings: a file a package's macro inputs where the document calls it is the package's ({viaPackage.map (·.subject)})"
      viaPackage.isEmpty
    let direct ← named "\\input{probeshared}"
    t s!"unused settings: the same file the document inputs itself is its own ({direct.map (·.subject)})"
      (direct.map (·.subject) == #[some "unused:color:probeink"])

/-- A rendered built-in's redefinition the engine refuses whole is named once, by the refusal; a
definition whose text execution skips in part, which nothing refuses, keeps that loss. -/
def redefinitionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let skipped (ds : Array Diag) : Bool :=
    ds.any fun d => d.kind == .W0104 && d.subject.any (·.startsWith "cond:body:")
  for (what, decl) in [("a redefined bold command",
        "\\renewcommand{\\textbf}[1]{\\ifx\\relax#1\\relax\\else{\\bfseries #1}\\fi}"),
      ("an xparse redefinition of italics",
        "\\NewDocumentCommand{\\textit}{m}{\\ifx\\relax#1\\relax\\else\\underline{#1}\\fi}")] do
    let (_, ds) := elabStr (article decl "Some \\textbf{bold} and \\textit{slanted} words.")
    t s!"unused settings: {what} the gate refuses is its one accounting ({ds.map (·.kind.code)})"
      (ds.any (·.kind == .W0303) && !skipped ds)
  let hooked := "\\DeclareRobustCommand{\\viahook}[1]{\\ifx\\relax#1\\relax H\\else I\\fi}\n" ++
    "\\DeclareRobustCommand{\\viacs}[1]{\\ifx\\relax#1\\relax W\\else X\\fi}\n" ++
    "\\AtBeginDocument{Hello \\viahook{h}}"
  let (_, viaHook) := elabStr (article hooked "Some \\csname viacs\\endcsname{q} words.")
  let skippedOf (ds : Array Diag) (n : String) : Bool := ds.any fun d =>
    d.kind == .W0104 && d.subject.any fun k => k.startsWith "cond:body:" && k.endsWith n
  t s!"unused settings: a definition called only from a hook or through csname keeps its skipped text's loss ({viaHook.map (·.subject)})"
    (skippedOf viaHook "viahook" && skippedOf viaHook "viacs")
  let (_, moded) := elabStr (article
    "\\renewcommand{\\textbf}[1]{\\ifmmode\\mathbf{#1}\\else{\\bfseries #1}\\fi}"
    "Some \\textbf{bold} words.")
  t s!"unused settings: a bold redefinition reading \\ifmmode wins, skipping nothing ({moded.map (·.kind.code)})"
    (!moded.any (·.kind == .W0303) && !skipped moded)
  let cond := "\\NewDocumentCommand{\\zzcond}{m}{\\ifx\\relax#1\\relax\\else\\underline{#1}\\fi}"
  let (_, unused) := elabStr (article cond "Some words.")
  let (_, used) := elabStr (article cond "Some \\zzcond{called} words.")
  t s!"unused settings: a definition no call runs reports no skipped text, one a call runs does ({unused.map (·.kind.code)})"
    (!skipped unused && skipped used)
  let (_, ds) := elabStr (article ("\\renewcommand{\\textbf}[1]{\\ifx\\relax#1\\relax\\else{\\bfseries #1}\\fi}\n" ++
    "\\renewcommand{\\textbf}[1]{\\underline{#1}\\ifx\\relax#1 x\\fi}") "Some \\textbf{bold} words.")
  let skippedAt (line : Nat) := ds.any fun d => d.kind == .W0104 && d.severity == .warning &&
    d.subject.any (·.startsWith "cond:body:") && d.span.any (·.pos.line == line)
  t s!"unused settings: a redefinition that wins keeps its skipped text's loss beside a refused one's refusal ({ds.map (·.kind.code)})"
    (ds.any (·.kind == .W0303) && !skippedAt 2 && skippedAt 3)
  let (_, ds) := elabStr (article ("\\renewcommand{\\textbf}[1]{\\underline{#1}\\ifx\\relax#1 x\\fi}\n" ++
    "\\renewcommand{\\textbf}[1]{\\ifx\\relax#1\\relax\\else{\\bfseries #1}\\fi}") "Some \\textbf{bold} words.")
  t s!"unused settings: a refusal after an earlier definition names that definition as the one standing, which keeps its loss ({ds.map (·.message)})"
    (ds.any (fun d => d.kind == .W0303 && hasStr (d.detail.getD "") ":2 stands") && ds.any fun d =>
      d.kind == .W0104 && d.subject.any (·.startsWith "cond:body:") && d.span.any (·.pos.line == 2))
  let (_, ds) := elabStr (article
    "\\def\\probesetup{\\renewcommand{\\textbf}[1]{\\ifx\\relax##1\\relax\\else{\\bfseries ##1}\\fi}}\n\\probesetup"
    "Some \\textbf{bold} words.")
  t s!"unused settings: a redefinition a macro makes, refused where it is called, is the refusal's alone ({ds.map (·.kind.code)})"
    (ds.any (·.kind == .W0303) && !skipped ds)
  let (_, ds) := elabStr (article
    "\\NewDocumentCommand{\\probecond}{m}{\\ifx\\relax#1\\relax\\else\\underline{#1}\\fi}"
    "Some \\probecond{probe} words.")
  t s!"unused settings: a definition nothing refuses keeps the loss of its skipped text ({ds.map (·.kind.code)})"
    (skipped ds && !ds.any (·.kind == .W0303))

/-- `\allow{W0449}` accepts the loss as a note; a site another warning names keeps that one
accounting; a translated declaration's note stands beside the loss as its own fact. -/
def accountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (allowing, allowed) := elabStr (article (probeColor ++ "\\allow{W0449}") "Words.")
  let accepted := (allowed.filter (·.kind == .W0449)).map (Diag.accept allowing.allow false · |>.1)
  t "unused settings: \\allow{W0449} accepts the loss as a note"
    (accepted.size == 1 && accepted.all (·.severity == .note))
  let (_, ds) := elabStr (article "\\usepackage{enumitem}\\setlist{labelsep=1em}" "Words.")
  t "unused settings: a declaration already named unread keeps that one accounting"
    (ds.any (·.kind == .W0104) && !ds.any (·.kind == .W0449))
  let (_, ds) := elabStr (article probeColor "Words.")
  t "unused settings: the translation's note and the loss stand at one site"
    (ds.any (·.kind == .N0100) && ds.any (·.kind == .W0449) &&
      (ds.filter fun d => d.kind == .N0100 || d.kind == .W0449).all fun d =>
        d.span.any (·.pos.line == 2))

/-- A markdown document's metadata keys only a citation reads are named where the document cites
nothing, each at its field; a citation, a `nocite` or an included file's role reads them. -/
def metadataChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let front := "---\nbibliography: refs.bib\nbiblio-style: plainnat\nreference-section-title: Works\n---\n\n"
  let named (src : String) : Array (Option String) :=
    ((elabMd src).2.filter (·.kind == .W0449)).map (·.subject)
  let uncited := (elabMd (front ++ "# A note\n\nPlain words, citing nothing.\n")).2.filter
    (·.kind == .W0449)
  t s!"unused metadata: a document citing nothing names each citation key it declares ({uncited.map (·.subject)})"
    (uncited.map (·.subject) == #[some "unused:meta:bibliography", some "unused:meta:biblio-style",
      some "unused:meta:reference-section-title"])
  t "unused metadata: each is named at its own field"
    (uncited.map (·.span.map (·.pos.line)) == #[some 2, some 3, some 4])
  t "unused metadata: a citation reads them"
    (named (front ++ "A claim [@roe2020].\n")).isEmpty
  t "unused metadata: a citation no bibliography key holds reads them"
    (named (front ++ "Words [@{roe2020,doe2019}].\n")).isEmpty
  t "unused metadata: a citation an image's text alternative sets reads them"
    (named (front ++ "![A caption citing [@roe2020].](fig.png)\n")).isEmpty
  let leanPage (doc : String) (refs : Option Code.Refs) : Array (Option String) :=
    ((Code.read .lean "t.lean" ("-- leantex: biblio-style = plain\n" ++ doc)
      (refs := refs)).2.filter (·.kind == .W0449)).map (·.subject)
  let refs : Code.Refs := { path := "refs.bib", keys := ({} : Std.HashSet String).insert "roe2020" }
  let declaring (words : String) : String :=
    s!"/-! {words}\n\nBibliography: [refs.bib](refs.bib) -/\ndef x := 1\n"
  t "unused metadata: a Lean page's citation directive key and bibliography line are named where its \
documentation cites nothing"
    (leanPage (declaring "Plain words.") (some refs) ==
      #[some "unused:directive:biblio-style", some "unused:docstring:bibliography"])
  t "unused metadata: a Lean page's citation reads its directive key and bibliography line"
    (leanPage (declaring "A claim [roe2020].") (some refs)).isEmpty
  t "unused metadata: a Lean page whose bibliography is not read is not judged"
    (leanPage (declaring "A claim [roe2020].") none).isEmpty
  t "unused metadata: a nocite reads them"
    (named ("---\nbibliography: refs.bib\nnocite: '@roe2020'\n---\n\nPlain words.\n")).isEmpty
  t "unused metadata: a document with no metadata names nothing"
    (named "# A note\n\nPlain words.\n").isEmpty
  let (_, included) := Md.readIncluded "part.md" (front ++ "Plain words.\n") false
  t "unused metadata: an included file's keys are the including document's to judge"
    (!included.any (·.kind == .W0449))
  t "unused metadata: a key already named keeps that one accounting"
    ((named ("---\nbibliography: refs.bib\nlink-citations: false\n---\n\nPlain words.\n")) ==
      #[some "unused:meta:bibliography"])

/-- Each tag and class a typed HTML tree holds, a class written `.name`, with the most of it one
path from the root nests. -/
def presentOne (path : List String) (acc : Array (String × Nat)) : Html.Node → Array (String × Nat)
  | .elem tag attrs kids =>
    let classes := ((((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " ").filter
      (!·.isEmpty) |>.map ("." ++ ·)
    let path := tag :: path
    let acc := (tag :: classes).foldl (fun a n =>
      let depth := path.count n + (if classes.contains n then 1 else 0)
      match a.findIdx? (·.1 == n) with
      | some i => a.modify i fun (k, d) => (k, max d depth)
      | none => a.push (n, depth)) acc
    kids.attach.foldl (fun a ⟨k, _⟩ => presentOne path a k) acc
  | .text _ | .style _ | .script _ _ => acc
termination_by n => sizeOf n
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹_ ∈ kids›
  simp_wf
  omega

/-- The tags and classes a selector's compounds name, pseudo-classes and their arguments aside. -/
def selectorNames (sel : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  let mut pseudo := false
  for c in sel.toList ++ [' '] do
    if c == '(' then
      depth := depth + 1
    else if c == ')' then
      depth := depth - 1
    else if depth > 0 then
      pure ()
    else if c.isAlphanum || c == '-' || c == '_' then
      cur := cur.push c
    else
      if !cur.isEmpty && !pseudo then out := out.push cur
      cur := if c == '.' then "." else ""
      pseudo := c == ':' || (pseudo && c == ':')
      if c == '.' then pseudo := false
  return out.filter (· != ".")

/-- Whether some selector of a rule's prelude names only what the page holds, a tag a descendant
chain repeats nested as often on the page. -/
def liveSelector (present : Array (String × Nat)) (prelude : String) : Bool :=
  (prelude.splitOn ",").any fun sel =>
    let names := selectorNames sel.trimAscii.toString
    names.all fun n => ["html", "body", "root"].contains n ||
      present.any fun (k, d) => k == n && d ≥ names.count n

/-- Style text without the font faces and the rules no element of the page answers. -/
def liveRules (present : Array (String × Nat)) (css : String) : String := Id.run do
  let mut out := ""
  let mut prelude := ""
  let mut leaf := ""
  let mut keep := false
  let mut depth := 0
  for c in css.toList do
    if depth > 0 then
      leaf := leaf.push c
      if c == '{' then depth := depth + 1
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then
          if keep then out := out ++ leaf
          leaf := ""
    else if c == '{' then
      let sel := prelude.trimAscii.toString
      if sel.startsWith "@media" || sel.startsWith "@supports" || sel.startsWith "@layer" then
        out := out ++ prelude ++ "{"
      else
        keep := !sel.startsWith "@font-face" &&
          (sel.startsWith "@" || liveSelector present sel)
        leaf := prelude ++ "{"
        depth := 1
      prelude := ""
    else if c == '}' || c == ';' then
      out := (out ++ prelude).push c
      prelude := ""
    else prelude := prelude.push c
  return out ++ prelude

/-- A source's artifacts as a reader meets them: the PDF's bytes, the web page's body and head
without what nothing on it reads, the markdown twin, and the diagnostics. -/
structure Seen where
  pdf : ByteArray
  page : String
  css : String
  md : String
  diags : Array Diag

def seen (fonts : Font.FontSet) (src : String) : Seen :=
  let (doc, ds) := bibBuild src #[("refs", ParamCensus.refsBib), ("refs.bib", ParamCensus.refsBib)]
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  let present := tree.foldl (presentOne []) #[]
  let styles := String.join (head.toList.filterMap fun | .style c => some c | _ => none)
  let live := liveRules present styles
  let page := Html.render (Html.elem "div" (ParamCensus.plainNodes #[] tree.toList)) 0 ++
    Html.render (Html.elem "head" (head.filter fun | .style _ => false | _ => true)) 0
  let markup := Html.render (Html.elem "div" tree) 0
  -- A property only an unread property reads is unread too.
  let css := (List.range 4).foldl (fun css _ =>
    ParamCensus.dropUnreadIn (ParamCensus.readProps (css ++ markup)) css) live
  { pdf := driverPdf fonts (Layout.Geom.ofPage doc.page) doc out, page, css
    md := MarkdownDoc.emit doc, diags := ds ++ out.diags ++ hds }

/-- The documents the two-build judge varies a declaration in. -/
def judgedBodies : List (String × String) :=
  [("plain", "Plain words in a paragraph."),
   ("sections", "\\section{Opening}Words.\\subsection{Second}More words."),
   ("lists", "\\begin{itemize}\\item Alpha\\begin{itemize}\\item Beta\\end{itemize}\\end{itemize}" ++
     "\\begin{enumerate}\\item One\\begin{enumerate}\\item Two\\end{enumerate}\\end{enumerate}"),
   ("an algorithm", "\\begin{algorithmic}[1]\\State alpha\\If{beta}\\State gamma\\EndIf\\end{algorithmic}"),
   ("a note", "Words\\footnote{Note words.} here."),
   ("an abstract and a title", "\\maketitle\\begin{abstract}Abstract words.\\end{abstract}Body."),
   ("links and a citation", "\\section{A}\\label{s:a}See Section~\\ref{s:a}, " ++
     "\\href{https://example.org}{a place} and \\cite{key1}.\\bibliographystyle{plainnat}\\bibliography{refs}"),
   ("listings", "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}\\begin{minted}{python}\ny = 2\n" ++
     "\\end{minted}Inline \\mintinline{bash}{echo z} code."),
   ("colour", "\\textcolor{probeink}{Coloured words.}"),
   ("a diagram", "\\begin{tikzcd} A \\arrow[r, probeink] & B \\end{tikzcd}"),
   ("nested quotes", "\\begin{quote}Outer.\\begin{quote}Inner.\\end{quote}\\end{quote}")]

/-- The declarations the two-build judge varies, one at a time. -/
def judgedDecls : List String :=
  [probeColor, "\\colorlet{probeink}{red!40}", "\\palette{ probeink = #8A2BE2 }",
   "\\style{section}{ before = 30pt }", "\\style{subsection}{ before = 30pt }",
   "\\style{itemize}{ indent = 4em }", "\\style{enumerate}{ indent = 4em }",
   "\\style{itemize2}{ indent = 4em }", "\\style{abstract}{ font = {\\Large} }",
   "\\style{titlepage}{ font = {\\Huge} }", "\\style{cite}{ color = red }",
   "\\setlist[enumerate,2]{leftmargin=4em}", "\\hypersetup{colorlinks, linkcolor=red}",
   "\\lstset{numbers=left}", "\\setminted{linenos}", "\\setminted[python]{linenos}",
   "\\setmintedinline{fontsize=\\small}", "\\style{titlepage}{ author-font = {\\Huge} }",
   "\\makeatletter\\def\\@listii{\\leftmargin 8em \\topsep 30pt}\\makeatother",
   "\\lstset{keywordstyle=\\color{red}}", "\\style{block}{ font = {\\Large} }"]

/-- The two-build judge: wherever W0449 names a declaration, the document without it ships the same
PDF bytes, web page and markdown twin. -/
def oracleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let pre := "\\title{Probe title}\\author{Probe author}\\usepackage{listings}\\usepackage{minted}" ++
    "\\usepackage{algpseudocode}\\usepackage{hyperref}\\usepackage{natbib}\\usepackage{enumitem}" ++
    "\\usepackage{tikz-cd}"
  let tasks := judgedBodies.map fun (what, body) =>
    let base := Task.spawn fun _ => seen fonts (article pre body)
    (what, judgedDecls.map fun decl => (decl, base.bind fun b => Task.spawn fun _ =>
      let w := seen fonts (article (pre ++ "\n" ++ decl) body)
      let named := w.diags.any fun (d : Diag) => d.kind == DiagCode.W0449 &&
        d.span.any fun (sp : Span) => sp.pos.line == 3
      let same := w.pdf == b.pdf && w.page == b.page && w.css == b.css && w.md == b.md
      (named, same)))
  let mut faults : Array String := #[]
  let mut named := 0
  for (what, row) in tasks do
    for (decl, task) in row do
      let (n, same) := task.get
      if n then named := named + 1
      if n && !same then faults := faults.push s!"{decl} in {what}"
  check ref s!"unused settings, two builds: a declaration named unused changes no artifact ({faults})"
    faults.isEmpty
  check ref s!"unused settings, two builds: the judge names declarations ({named})" (named ≥ 40)
  -- A declaration some of whose entries something reads names the rest, which the help deletes.
  let linked (keys : String) := seen fonts (article ("\\usepackage{hyperref}\\hypersetup{" ++ keys ++ "}")
    "Plain words.")
  let whole := linked "colorlinks, linkcolor=red, pdftitle={Probe Title}"
  let kept := linked "pdftitle={Probe Title}"
  let helps := (whole.diags.filter (·.kind == .W0449)).filterMap (·.help)
  check ref s!"unused settings, two builds: deleting what the help names of a declaration read in part changes no artifact ({helps})"
    (helps == #["delete what it declares for them, or \\allow{W0449} keeps it"] &&
      whole.pdf == kept.pdf && whole.page == kept.page && whole.css == kept.css && whole.md == kept.md)

/-- A declared face is judged over the settled face set: one no text is set in is named, one a run
or a fallback glyph reads is not. -/
def faceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FontAssembly.FaceScan := { faces := scanned, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let judge (cls fonts body : String) : IO (Option (Array Diag × ByteArray)) := do
    let src := s!"\\documentclass\{{cls}}\n\\fonts\{ {fonts} }\n\\begin\{document}\n{body}\n" ++
      "\\end{document}\n"
    let (doc, _, spans) := Elab.runRawsSpanned "t" (Parse.parse "t" (Lex.lex "t" src).1).1
    match ← FontAssembly.buildFontSet doc scan cache .settled with
    | .ok (fs, doc, _, _) =>
      let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
      return some (FaceUse.diags spans.faces fs doc,
        driverPdf fs (Layout.Geom.ofPage doc.page) doc out)
    | .error _ => return none
  let keys (r : Option (Array Diag × ByteArray)) : Array String :=
    ((r.map (·.1)).getD #[]).filterMap (·.subject)
  let serif := "body = \"Source Serif Pro\""
  let monoOnly ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "Plain words."
  let without ← judge "article" serif "Plain words."
  t s!"unused faces: a typewriter face no code sets in is named ({keys monoOnly})"
    (keys monoOnly == #["unused:face:mono"])
  t "unused faces: the document without it ships the same PDF bytes"
    ((monoOnly.map (·.2)) == (without.map (·.2)) && monoOnly.isSome)
  let code ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "A \\texttt{code} run."
  t s!"unused faces: a typewriter face code sets in is not named ({keys code})" (keys code).isEmpty
  let bib := "@article{probe2020, author = {Roe, Pat}, title = {An Invented Article}, " ++
    "journal = {Journal of Placeholders}, year = {2020}, url = {https://example.org/roe}}\n"
  let cited := s!"\\documentclass\{article}\n\\fonts\{ {serif}, mono = \"Source Code Pro\" }\n" ++
    "\\usepackage{natbib}\\usepackage{url}\n\\begin{document}\nA claim \\citep{probe2020}.\n" ++
    "\\bibliographystyle{plainnat}\n\\bibliography{refs}\n\\end{document}\n"
  let (citedDoc, _, _) := bibBuildParts cited #[("refs", bib), ("refs.bib", bib)]
  match ← FontAssembly.buildFontSet citedDoc scan cache .settled with
  | .ok (fs, doc, _, _) =>
    t "unused faces: a typewriter face a reference list's address sets in is not named"
      (FaceUse.diags #[("mono", ⟨"t", {}⟩)] fs doc).isEmpty
  | .error _ => t "unused faces: the citing document's face set settles" false
  let fallback ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "A rule \u2500 drawn."
  t s!"unused faces: a face a glyph the text face lacks falls back to is not named ({keys fallback})"
    (keys fallback).isEmpty
  let math ← judge "article" (serif ++ ", math = \"Fira Math\"") "Plain words."
  t s!"unused faces: a math face no formula sets in is named ({keys math})"
    (keys math == #["unused:face:math"])
  let refused ← judge "article" (serif ++ ", math = \"Open Sans\"") "Plain words."
  t s!"unused faces: a math face the build refuses for its missing MATH table is that refusal's ({keys refused})"
    (refused.isSome && (keys refused).isEmpty)
  let formula ← judge "article" (serif ++ ", math = \"Fira Math\"") "A formula $x^2$."
  t s!"unused faces: a math face a formula sets in is not named ({keys formula})"
    (keys formula).isEmpty
  let sans ← judge "article" (serif ++ ", sans = \"Open Sans\"") "Plain words."
  t s!"unused faces: a sans face no text sets in is named ({keys sans})"
    (keys sans == #["unused:face:sans"])
  let headed ← judge "article" (serif ++ ", sans = \"Open Sans\"") "\\section{Opening}Words."
  t s!"unused faces: a sans face the web page's headings set in is not named ({keys headed})"
    (keys headed).isEmpty
  let entry ← judge "article" (serif ++ ",\n  mono = \"Source Code Pro\"") "Plain words."
  t s!"unused faces: a face is named at its entry ({((entry.map (·.1)).getD #[]).map (·.span.map (·.pos.line))})"
    (((entry.map (·.1)).getD #[]).map (·.span.map (·.pos.line)) == #[some 3])
  let missingSrc := s!"\\documentclass\{article}\n\\fonts\{ {serif}, mono = \"Probe Missing Mono\" }\n" ++
    "\\begin{document}\nPlain words.\n\\end{document}\n"
  let (missingDoc, _, missingSpans) := Elab.runRawsSpanned "t"
    (Parse.parse "t" (Lex.lex "t" missingSrc).1).1
  match ← FontAssembly.buildFontSet missingDoc scan cache .settled (sites := missingSpans.faces) with
  | .ok (fs, doc, ds, _) =>
    t s!"unused faces: a family no installed face answers is named by its loss alone ({(FaceUse.diags missingSpans.faces fs doc).map (·.subject)})"
      (ds.any (·.kind == .W0390) && (FaceUse.diags missingSpans.faces fs doc).isEmpty)
    t s!"unused faces: a family no installed face answers is named at the entry naming it ({(ds.filter (·.kind == .W0390)).map (·.span.map (·.pos.line))})"
      ((ds.filter (·.kind == .W0390)).map (·.span.map (·.pos.line)) == #[some 2])
  | .error _ => t "unused faces: a document missing one family still settles its face set" false
  let deckFaces := serif ++ ", sans = \"Open Sans\", mono = \"Source Code Pro\""
  let deckBody := "\\begin{frame}{Title}Words.\\end{frame}"
  let slides ← judge "slides" deckFaces deckBody
  t s!"unused faces: a deck's body face its sans text never reads is named ({keys slides})"
    (keys slides == #["unused:face:body", "unused:face:mono"])
  let companion ← judge "slides" deckFaces "\\begin{frame}{Title}A formula $x^2$.\\end{frame}"
  t s!"unused faces: a deck's body face whose companion sets its math is not named ({keys companion})"
    (!(keys companion).contains "unused:face:body")

end Tests.UnusedSettings
