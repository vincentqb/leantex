module

public import Tests.ParamCensus

public section

open LeanTex.Core LeanTex.Cli

/-! The declaration settings census: the colours, listing defaults, list styles, boxes, beamer
settings and counters a document declares are each read, or named where they are set. -/

namespace Tests.ParamCensus

/-- A colour no default spells, so a declaration that is read changes what ships. -/
def probeColor : String := "#8A2BE2"

/-- An article body that paints with code, quotes and boxed text beside the article's own. -/
def paintedBody : String :=
  "\\begin{lstlisting}[language=Python]\nclass Probe(object):\n    def size(self, x):\n" ++
    "        return len(x) + 1  # note\n" ++
    "\\end{lstlisting}\n\\begin{quote}Quoted words.\\end{quote}\\fbox{Boxed words}\n"

/-- A deck that sets a title page, sections, blocks of each kind, covered and alerted text. -/
def paintedDeck (opts pre : String) : String :=
  s!"\\documentclass{opts}\{beamer}\n\\title\{Probe title}\\subtitle\{Probe subtitle}" ++
    s!"\\author\{Probe author}\\institute\{Probe place}\\date\{Probe date}\n{pre}\n" ++
    "\\begin{document}\n\\begin{frame}\\titlepage\\end{frame}\n\\section{Opening}\n" ++
    "\\begin{frame}{Frame title}\\framesubtitle{Frame subtitle}Words \\alert{alerted}\\pause more words" ++
    "\\begin{itemize}\\item one\\item two\\end{itemize}\\begin{block}{Block title}Block words." ++
    "\\end{block}\\begin{alertblock}{Alert title}Alert words.\\end{alertblock}" ++
    "\\begin{exampleblock}{Example title}Example words.\\end{exampleblock}\\end{frame}\n" ++
    "\\begin{frame}[fragile]{Code}\\begin{lstlisting}[language=Python]\nclass Probe(object):\n" ++
    "    def size(self, x):\n        return len(x)  # note\n\\end{lstlisting}\\end{frame}\n" ++
    "\\begin{frame}[standout]Standout words.\\end{frame}\n\\end{document}\n"

/-- Every `\palette` role key and an author colour nothing paints with, in an article, a deck and a
themed deck. -/
def paletteRow : Row :=
  let decl (o : Option String) : String :=
    (o.map fun k => s!"\\palette\{ {k} = {probeColor} }").getD ""
  { reader := "\\palette"
    settings := Ir.Role.keyed.toList.map (·.1)
    keyOf := id
    anyDoc := true
    docs := [fun o => article "" (decl o) paintedBody, fun o => paintedDeck "" (decl o),
      fun o => paintedDeck "" ("\\usetheme{moloch}" ++ decl o),
      fun o => paintedDeck "" (s!"\\palette\{ titlepagebg = #F5F0E6 }" ++ decl o)] }

/-- A deck whose one fragile frame holds `code`, `pre` in its preamble; its uncaptioned listing numbers
nothing a label could name. -/
def codeDeck (pre code : String) : String :=
  s!"\\documentclass\{beamer}\n{pre}\n\\begin\{document}\n\\begin\{frame}[fragile]\{Code}\n{code}\n" ++
    "\\end{frame}\n\\end{document}\n"

/-- The listing reader's keys, each standing in a listing default. -/
def listingSettings : List String :=
  ["caption=Probe caption", "label=lst:probe", "numbers=left", "linenos", "language=Python",
    "style=friendly", "fontsize=\\small", "tabsize=4", "bgcolor=red", "breaklines",
    "basicstyle=\\ttfamily\\small", "firstline=2", invented]

/-- A standing listing default, read by the code that follows it and named where none does. -/
def listingRows : List Row :=
  let code := "\ndef probe(x):\n\treturn x + 1  # a long comment that runs on past the measure " ++
    "of the listing's own line\n"
  let pre := "\\usepackage{listings}\\usepackage{minted}"
  [{ reader := "\\lstset"
     settings := listingSettings
     tries := fun s i => i == 0 || !s.startsWith "label="
     docs := [fun o => article "" (pre ++ (o.map (s!"\\lstset\{{·}}")).getD "")
         s!"\\begin\{lstlisting}{code}\\end\{lstlisting}See listing~\\ref\{lst:probe}.",
       fun o => codeDeck (pre ++ (o.map (s!"\\lstset\{{·}}")).getD "")
         s!"\\begin\{lstlisting}{code}\\end\{lstlisting}See listing~\\ref\{lst:probe}."] },
   { reader := "\\setminted"
     settings := listingSettings
     tries := fun s i => i == 0 || !s.startsWith "label="
     docs := [fun o => article "" (pre ++ (o.map (s!"\\setminted\{{·}}")).getD "")
         s!"\\begin\{minted}\{python}{code}\\end\{minted}See listing~\\ref\{lst:probe}.",
       fun o => codeDeck (pre ++ (o.map (s!"\\setminted\{{·}}")).getD "")
         s!"\\begin\{minted}\{python}{code}\\end\{minted}See listing~\\ref\{lst:probe}."] },
   { reader := "\\setmintedinline"
     settings := Compat.mintedDisplayKeys.map (· ++ "=2") ++ listingSettings
     inert := fun s => Compat.mintedDisplayKeys.contains (KeyVal.entry s).1
     docs := [fun o => article "" (pre ++ (o.map (s!"\\setmintedinline\{{·}}")).getD "")
         "Inline \\mintinline{python}{probe(x)\treturn} code."] }]

/-- Lists of every kind, itemize and enumerate nested three levels deep. -/
def setlistLists : String :=
  let nested (env : String) : String :=
    s!"\\begin\{{env}}\\item Alpha\\begin\{{env}}\\item Beta\\begin\{{env}}\\item Gamma" ++
      s!"\\end\{{env}}\\end\{{env}}\\end\{{env}}"
  nested "itemize" ++ nested "enumerate" ++
    "\\begin{description}\\item[Term] Alpha\\item[Other] Beta\\end{description}"

/-- enumitem's keys, the length and spacing keys and label the reader translates and keys it names,
set for a kind, a kind's deeper level, a level of every kind, and every list, each before another
preamble line, in nested lists of every kind. -/
def setlistRow : Row :=
  let doc (scope : String) (o : Option String) : String :=
    article "" ("\\usepackage{enumitem}" ++ (o.map (s!"\\setlist{scope}\{{·}}")).getD "" ++
      "\n\\newcommand{\\probeword}{x}") setlistLists
  { reader := "\\setlist"
    settings := ((Compat.setlistLengthKeys.map (·.1)) ++ Ir.listSetKeys).map (· ++ "=3em") ++
      ["label=x", "label=(\\alph*)",
      "nosep", "noitemsep", "align=left", "font=\\bfseries", "labelsep=1em", "parsep=0pt",
      "start=3", invented]
    docs := [doc "[itemize]", doc "[enumerate,2]", doc "[2]", doc ""] }

/-- A `\setlist` scope's parts, each beside a part another element styles (a kind beside itemize, a
level beside the second) under a style key and a spacing key: a part no element styles must be
named, though the scope's other part changes the page. -/
def setlistScopeRow : Row :=
  let doc (base key : String) (o : Option String) : String :=
    article "" ("\\usepackage{enumitem}" ++ s!"\\setlist[{base}{(o.map ("," ++ ·)).getD ""}]\{{key}}")
      setlistLists
  { reader := "\\setlist scope"
    settings := ["enumerate", "description", "censusprobekind", "3", "1", "5"]
    keyOf := id
    tries := fun s i => if s.toNat?.isSome then i % 2 == 1 else i % 2 == 0
    docs := [doc "itemize" "label=x", doc "2" "label=x", doc "itemize" "topsep=3em",
      doc "2" "topsep=3em"] }

/-- tcolorbox's keys, each reader held apart: a box's own options, `\\tcbset` standing before a
box, and a defined box's options; the keys the reader reads and keys it refuses. -/
def tcolorboxRows : List Row :=
  let sample (k : String) : String :=
    if k == "title" then "title=Probe title"
    else if k.startsWith "font" then k ++ "=\\bfseries"
    else if k.endsWith "skip" then k ++ "=24pt"
    else if k == "boxed title style" then k ++ "={colframe=blue}"
    else k ++ "=red!50"
  let keys := (Tcolorbox.readKeys.map sample) ++ ["width=5cm", "arc=2mm", "boxrule=2pt",
    "sharp corners", "breakable", invented]
  let pre := "\\usepackage{tcolorbox}"
  let box := "\\begin{tcolorbox}Boxed words.\\end{tcolorbox}"
  let titled := "\\begin{tcolorbox}[title=Box title]Boxed words.\\end{tcolorbox}"
  [{ reader := "\\begin{tcolorbox}"
     settings := keys
     tries := fun s i => i == 1 || !hasStr (KeyVal.entry s).1 "title"
     docs := [fun o => article "" pre
         s!"\\begin\{tcolorbox}{bracketed o}Boxed words.\\end\{tcolorbox}",
       fun o => article "" pre
         s!"\\begin\{tcolorbox}[title=Box title{(o.map ("," ++ ·)).getD ""}]Boxed words.\\end\{tcolorbox}"] },
   { reader := "\\tcbset"
     settings := keys
     neighbour := some (invented ++ "=1")
     tries := fun s i => i == 1 || !hasStr (KeyVal.entry s).1 "title"
     docs := [fun o => article "" (pre ++ (o.map (s!"\\tcbset\{{·}}")).getD "") box,
       fun o => article "" (pre ++ (o.map (s!"\\tcbset\{{·}}")).getD "") titled] },
   { reader := "\\newtcolorbox"
     settings := keys
     tries := fun s i => i == 1 || !hasStr (KeyVal.entry s).1 "title"
     docs := [fun o => article "" (pre ++
         s!"\\newtcolorbox\{probebox}\{{o.getD ""}}") "\\begin{probebox}Boxed words.\\end{probebox}",
       fun o => article "" (pre ++
         s!"\\newtcolorbox\{probebox}\{title=Box title{(o.map ("," ++ ·)).getD ""}}")
         "\\begin{probebox}Boxed words.\\end{probebox}"] }]

/-- An element's name before its options or body. -/
def elementOf (s : String) : String :=
  String.ofList (s.toList.takeWhile fun c => c != '{' && c != '[' && c != '|')

/-- An element and its setting, written `element|setting`. -/
def elementSplit (s : String) : String × String :=
  match s.splitOn "|" with
  | [e, v] => (e, v)
  | _ => (s, "")

/-- Whether `\\setbeamerfont`'s document of that index draws the element: the abstract's title only
in the abstract's deck, which draws nothing else. -/
def fontDrawnIn (element : String) (i : Nat) : Bool :=
  if element == "abstract title" then i == 3 else i != 3 || element == "censusprobeelement"

/-- A `\\setbeamerfont` setting written `element|fields`, followed by another preamble line. -/
def fontOf (o : Option String) : String :=
  (o.map fun s =>
    let (e, v) := elementSplit s
    s!"\\setbeamerfont\{{e}}\{{v}}\n\\newcommand\{\\probeword}\{x}").getD ""

/-- beamer's template, size, font and colour settings, in a deck that shows their elements. -/
def beamerRows : List Row :=
  [{ reader := "\\setbeamertemplate"
     settings := Compat.emptyTemplates.map (· ++ "{}") ++
       Compat.defaultTemplates.map (· ++ "[default]") ++ ["itemize items[circle]",
       "itemize item[square]", "footline[frame number]",
       "frametitle{\\insertframetitle}", "blocks[rounded]", "section in toc[sections numbered]",
       "censusprobetemplate{}"]
     keyOf := elementOf
     inert := fun s => (s.endsWith "{}" && Compat.emptyTemplates.contains (elementOf s)) ||
       (s.endsWith "[default]" && Compat.defaultTemplates.contains (elementOf s))
     docs := [fun o => paintedDeck "" ((o.map fun s =>
       let e := elementOf s
       s!"\\setbeamertemplate\{{e}}{(s.drop e.length).toString}\n\\newcommand\{\\probeword}\{x}").getD ""),
       fun o => paintedDeck "" ("\\usetheme{moloch}" ++ (o.map fun s =>
       let e := elementOf s
       s!"\\setbeamertemplate\{{e}}{(s.drop e.length).toString}").getD "")] },
   { reader := "\\setbeamersize"
     settings := ["text margin left=2cm", "text margin right=2cm", "sidebar width left=2cm",
       "description width=2cm", "mini frame size=2pt", invented]
     neighbour := some (invented ++ "=1")
     docs := [fun o => paintedDeck "" ((o.map (s!"\\setbeamersize\{{·}}")).getD "")] },
   { reader := "\\setbeamerfont"
     settings := Compat.beamerFontElements.map (fun (e, _) => e ++ "|size=\\tiny") ++
       ["frametitle|series=\\bfseries", "frametitle|shape=\\itshape", "normal text|family=\\rmfamily",
        "footline|size=\\tiny", "item|size=\\small", "censusprobeelement|size=\\tiny"]
     keyOf := fun s => (elementSplit s).1
     inert := fun s => let (e, v) := elementSplit s
       e == "frametitle" && Elab.restatesPlainTitle
         (String.join ((KeyVal.items v).toList.map fun kv => (KeyVal.entry kv).2.getD ""))
     tries := fun s i => fontDrawnIn (elementSplit s).1 i
     docs := [fun o => paintedDeck "" (fontOf o), fun o => paintedDeck "" ("\\usetheme{moloch}" ++ fontOf o),
       fun o => paintedDeck "" (fontOf o ++ "\\setbeamercolor{frametitle}{bg=blue,fg=white}"),
       fun o => s!"\\documentclass\{beamer}\n{fontOf o}\n\\begin\{document}\n\\begin\{frame}" ++
         "\\begin{abstract}Abstract words.\\end{abstract}\\end{frame}\n\\end{document}\n"] },
   { reader := "\\setbeamercolor"
     settings := (BeamerColor.roles.flatMap fun (e, fg, bg) =>
       (if fg.isSome then [e ++ "|fg=red"] else []) ++ (if bg.isSome then [e ++ "|bg=blue"] else [])) ++
       ["censusprobeelement|fg=red"]
     keyOf := fun s => (elementSplit s).1
     docs := [fun o => paintedDeck "" ((o.map fun s =>
       let (e, v) := elementSplit s
       s!"\\setbeamercolor\{{e}}\{{v}}").getD ""),
       fun o => paintedDeck "" ("\\usetheme{moloch}" ++ (o.map fun s =>
       let (e, v) := elementSplit s
       s!"\\setbeamercolor\{{e}}\{{v}}").getD "")] }]

/-- The counters a document advances or allocates, before what they number. -/
def counterDeclRows : List Row :=
  let numbered := "\\tableofcontents\\section{Late words}\\subsection{Later}" ++
    "\\paragraph{Late run} Words\\footnote{Late note.}.\\begin{equation}x\\end{equation}" ++
    "\\begin{enumerate}\\item One\\end{enumerate}"
  [{ reader := "\\addtocounter"
     settings := ["secnumdepth", "tocdepth", "page", "section", "subsection", "equation", "figure",
       "table", "footnote", "enumi", "censusprobecounter"]
     keyOf := id
     anyDoc := true
     docs := [fun o => article "" "\\newcounter{censusprobecounter}"
       ((o.map (s!"\\addtocounter\{{·}}\{2}")).getD "" ++ numbered),
       fun o => article "" "" ("\\section{Early words}" ++
         (o.map (s!"\\addtocounter\{{·}}\{2}")).getD "" ++ "\\subsection{Early part}")] },
   { reader := "\\newcounter"
     settings := ["censusprobenew"]
     keyOf := id
     docs := [fun o => article "" ((o.map (s!"\\newcounter\{{·}}")).getD "") numbered] }]

/-- A value each `\style` key reads, other than the element's default. -/
def styleSample (element key : String) : String :=
  if key == "font" || key == "author-font" then "\\bfseries"
  else if key == "marker" then "{x}"
  else if key == "body-size" then "footnotesize"
  else if ["rule", "separator", "hover", "focus", "color"].contains key then probeColor
  else if key == "rule-position" then "baseline"
  else if key == "align" then
    if element == "logo" then "center" else if element == "titlepage" then "left" else "right"
  else if key == "motion" then "400ms"
  else if key == "slot" then "{ set = date, anchor = south, at = south }"
  else if key == "tilde" then "low"
  else "17pt"

/-- A document showing every element a `\style` may name: an article's headings at every level, its
title, abstract, nested lists of every kind, links, addresses and citations, and a deck's frame titles,
section page, standout frame, title page, navigation, logo and blocks. -/
def styledArticle (pre : String) : String :=
  s!"\\documentclass\{article}\n\\title\{Probe title}\\author\{Probe author}\n{pre}\n" ++
    "\\begin{document}\n\\maketitle\n\\begin{abstract}Abstract words.\\end{abstract}\n" ++
    "\\part{Part words}\\section{Section words}\\label{s:a}\\subsection{Subsection words}" ++
    "\\subsubsection{Subsubsection words}\\paragraph{Paragraph words} Run-in words." ++
    "\\subparagraph{Subparagraph words} More words.\n" ++ setlistLists ++
    "\\begin{itemize}\\item One\\begin{itemize}\\item Two\\begin{itemize}\\item Three\\begin{itemize}" ++
    "\\item Four\\end{itemize}\\end{itemize}\\end{itemize}\\end{itemize}" ++
    "\\begin{enumerate}\\item One\\begin{enumerate}\\item Two\\begin{enumerate}\\item Three" ++
    "\\begin{enumerate}\\item Four\\end{enumerate}\\end{enumerate}\\end{enumerate}\\end{enumerate}" ++
    "\\begin{description}\\item[One] Words\\begin{description}\\item[Two] Words" ++
    "\\begin{description}\\item[Three] Words\\begin{description}\\item[Four] Words" ++
    "\\end{description}\\end{description}\\end{description}\\end{description}\n" ++
    "See Section~\\ref{s:a}, \\href{https://example.org}{a place}, \\url{https://example.org/~a} and " ++
    "\\cite{key1}.\n" ++ bibtexList ++ "\n\\end{document}\n"

/-- `\style`'s keys on every element a document styles, each in a document that shows the element:
the flow elements in an article, a deck's furniture in a themed deck, a logo under beamer's own
theme, a title bar's spacing beside its bars and a rule's placement and weight beside the rule. -/
def styleRow : Row :=
  let deckElements := ["frametitle", "sectionpage", "standout", "nav", "block", "alertblock",
    "exampleblock"]
  let barred := "\\style{titlepage}{ rule-above = 1pt, rule-below = 1pt }"
  let barKeys := ["rule-above-skip", "rule-above-gap", "rule-below-gap", "rule-below-skip"]
  let ruled := ["rule-position", "rule-thickness"]
  let decl (o : Option String) : String :=
    (o.map fun s => let (e, kv) := elementSplit s; s!"\\style\{{e}}\{ {kv} }").getD ""
  let shown (e pre : String) (o : Option String) : String :=
    if e == "probeentry" then
      styledArticle ("\\define \\probeentry(word: content) {\\word}" ++ pre ++ decl o)
        |>.replace "\\cite{key1}." "\\cite{key1}.\n\n\\probeentry{Entry words} and more words."
    else if e == "logo" then paintedDeck "" ("\\theme{default}\\logo{Logo words}" ++ pre ++ decl o)
    else if deckElements.contains e then paintedDeck "" ("\\usetheme{moloch}" ++ pre ++ decl o)
    else styledArticle (pre ++ decl o)
  let elements := Ir.styleableElements ++ ["probeentry"]
  { reader := "\\style"
    -- moloch's title stands flush left and an article's centred, so each tries the other side.
    settings := (elements.flatMap fun e => Ir.styleKeys.map fun k => s!"{e}|{k} = {styleSample e k}") ++
      ["titlepage|align = right"]
    keyOf := fun s => (KeyVal.entry (elementSplit s).2).1
    tries := fun s i =>
      let (e, kv) := elementSplit s
      let k := (KeyVal.entry kv).1
      if ruled.contains k then i == 6 + (elements.idxOf e)
      else if e == "titlepage" && barKeys.contains k then i == 2 || i == 3
      else if s == "titlepage|align = left" then i == 0
      else if s == "titlepage|align = right" then i == 1
      else if e == "titlepage" then i == 0 || i == 1
      else if e == "logo" then i == 4
      else if e == "probeentry" then i == 5
      else (i == 1) == deckElements.contains e && i ≤ 1
    docs := [fun o => styledArticle (decl o),
      fun o => paintedDeck "" ("\\usetheme{moloch}" ++ decl o),
      fun o => styledArticle (barred ++ decl o),
      fun o => paintedDeck "" ("\\usetheme{moloch}" ++ barred ++ decl o),
      shown "logo" "", shown "probeentry" ""] ++
      elements.map fun e => shown e s!"\\style\{{e}}\{ rule = {probeColor} }" }

/-- An article setting every element an engine token spaces: a running head, lists at every depth,
a trivlist's items, floats with captions above and below, a booktabs table, displays, footnotes, a framed box, skips, an
algorithm and a natbib reference list. -/
def tokenedArticle (pre : String) : String :=
  s!"\\documentclass\{article}\n\\usepackage\{natbib}\\usepackage\{booktabs}\\usepackage\{algpseudocode}" ++
    s!"\\usepackage\{subcaption}\\runninghead\{Head words}\n{pre}\n\\begin\{document}\n" ++
    "Words before.\\footnote{Note words.} A \\fbox{boxed} word.\n" ++ setlistLists ++
    "\\begin{itemize}\\item One\\begin{itemize}\\item Two\\begin{itemize}\\item Three\\begin{itemize}" ++
    "\\item Four\\end{itemize}\\end{itemize}\\end{itemize}\\end{itemize}\n" ++
    "\\begin{trivlist}\\item Trivlist one.\\item Trivlist two.\\end{trivlist}\n" ++
    "\\begin{figure}[ht]\\centering\\rule{2cm}{1cm}\\caption{Figure words}\\end{figure}\n" ++
    "\\begin{figure}[ht]\\centering\\begin{subfigure}{0.4\\textwidth}\\rule{1cm}{1cm}" ++
    "\\caption{Sub words}\\end{subfigure}\\caption{Outer words}\\end{figure}\n" ++
    "\\begin{table}[ht]\\centering\\caption{Table words}\\begin{tabular}{ll}\\toprule A & B\\\\ " ++
    "\\midrule C & D\\\\ \\cmidrule(lr){1-2} E & F\\\\ \\bottomrule\\end{tabular}\\end{table}\n" ++
    "\\begin{tabular}{|l|l|}\\hline A & B\\\\ \\hline\\hline C & D\\\\ \\hline\\end{tabular}\n\n" ++
    "A long line of text before a display that runs across the measure, and on.\n" ++
    "\\begin{equation}a^2 + b^2 = c^2\\end{equation}\nshort\n\\begin{equation}x\\end{equation}\n" ++
    "Before skips.\\smallskip After small.\\medskip After medium.\\bigskip After big.\n" ++
    "\\begin{algorithm}\\caption{Steps}\\begin{algorithmic}[1]\\State alpha\\If{beta}\\State gamma" ++
    "\\EndIf\\end{algorithmic}\\end{algorithm}\n" ++
    "Citing \\citep{key1,key2}.\n" ++ bibtexList ++ "\n\\end{document}\n"

/-- `\tokens`' names: each engine token, set in an article or a deck setting what it spaces, and an
invented name nothing reads. -/
def tokensRow : Row :=
  let decl (o : Option String) : String := (o.map (s!"\\tokens\{ {·} }")).getD ""
  { reader := "\\tokens"
    settings := Ir.engineTokenNames.map (· ++ " = 31pt") ++ [invented ++ " = 31pt"]
    anyDoc := true
    docs := [fun o => tokenedArticle (decl o),
      fun o => paintedDeck "" ("\\usetheme{moloch}" ++ decl o)] }

/-- Every declaration census row. -/
def declRows : List Row :=
  [paletteRow] ++ listingRows ++ [setlistRow, setlistScopeRow] ++ tcolorboxRows ++ beamerRows ++
    counterDeclRows ++ [styleRow, tokensRow]

/-- A `\style` key and a `\tokens` name nothing reads are named where the document declares them,
its own file or one it inputs, and never in a package, class or theme file, a file one inputs, or a
definition's replacement text. -/
def declaredScopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let declared := "\n\\style{section}{ separator = #8A2BE2 }\n\\tokens{ idleprobe = 2pt }\n"
  let subjects := [some "style:section:separator", some "param:\\tokens:idleprobe"]
  let named (ds : Array Diag) : List (Option String) :=
    subjects.filter fun sub => ds.any fun d => d.code == "W0104" && d.subject == sub
  let built (raws : Array Parse.Raw) : Array Diag := (Elab.runRawsSpanned "root.tex" raws).2.1
  let tail := parse "root.tex" "\\begin{document}\n\\section{Words}Words.\n\\end{document}"
  let head := parse "root.tex" "\\documentclass{article}\n"
  let own := built (head ++ parse "root.tex" declared ++ tail)
  t s!"declared scope: the document's own unread key and token are named ({named own})"
    (named own == subjects)
  let spliced (child : String) : Array Diag :=
    built (head ++ #[Parse.Raw.env (Parse.inputEnv child) (parse child declared) {}] ++ tail)
  t "declared scope: a file the document inputs names its unread key and token"
    (named (spliced "part.tex") == subjects)
  for child in ["probe.sty", "probe.cls", "beamerthemeprobe.sty"] do
    t s!"declared scope: {child}'s unread key and token are its own, never named"
      (named (spliced child)).isEmpty
  let nested := built (head ++ #[Parse.Raw.env (Parse.inputEnv "probe.sty")
    #[Parse.Raw.env (Parse.inputEnv "probecolors.tex") (parse "probecolors.tex" declared) {}] {}] ++ tail)
  t "declared scope: a file a package inputs is the package's" (named nested).isEmpty
  for definer in ["\\newcommand{\\probesetup}", "\\def\\probesetup",
      "\\NewDocumentCommand{\\probesetup}{}"] do
    let defined := built (head ++ parse "root.tex" (definer ++ "{" ++ declared ++ "}\\probesetup\n") ++ tail)
    t s!"declared scope: a definition's replacement text is the definition's ({definer}: {named defined})"
      (named defined).isEmpty
    let after := built (head ++ parse "root.tex" (definer ++ "{x}\n" ++ declared) ++ tail)
    t s!"declared scope: a declaration after a definition is the document's ({definer}: {named after})"
      (named after == subjects)
    let blank := built (head ++ parse "root.tex" (definer ++ "{\n\n" ++ declared ++ "}\n") ++ tail)
    t s!"declared scope: a definition's body holding a blank line is still its own ({definer})"
      (named blank).isEmpty

/-- The declaration census: every setting of every row is read or named, and none read is named
unread. -/
def declCensusChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let judged := declRows.map fun row => (row, rowJudged fonts row)
  for (row, js) in judged do
    let faults := rowFaults row js
    check ref s!"settings census {row.reader}: every setting is read or named\
{String.join (faults.map ("\n  " ++ ·))}" faults.isEmpty

end Tests.ParamCensus
