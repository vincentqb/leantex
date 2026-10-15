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
     docs := [fun o => article "" (pre ++ (o.map (s!"\\lstset\{{·}}")).getD "")
         s!"\\begin\{lstlisting}{code}\\end\{lstlisting}See listing~\\ref\{lst:probe}."] },
   { reader := "\\setminted"
     settings := listingSettings
     docs := [fun o => article "" (pre ++ (o.map (s!"\\setminted\{{·}}")).getD "")
         s!"\\begin\{minted}\{python}{code}\\end\{minted}See listing~\\ref\{lst:probe}."] },
   { reader := "\\setmintedinline"
     settings := Compat.mintedDisplayKeys.map (· ++ "=2") ++ listingSettings
     inert := fun s => Compat.mintedDisplayKeys.contains (KeyVal.entry s).1
     docs := [fun o => article "" (pre ++ (o.map (s!"\\setmintedinline\{{·}}")).getD "")
         "Inline \\mintinline{python}{probe(x)\treturn} code."] }]

/-- enumitem's keys, the length keys and label the reader's table translates and keys it names,
set for a kind, a kind's deeper level, a level of every kind, and every list, each before another
preamble line, in nested lists of every kind. -/
def setlistRow : Row :=
  let nested (env : String) : String :=
    s!"\\begin\{{env}}\\item Alpha\\begin\{{env}}\\item Beta\\begin\{{env}}\\item Gamma" ++
      s!"\\end\{{env}}\\end\{{env}}\\end\{{env}}"
  let lists := nested "itemize" ++ nested "enumerate" ++
    "\\begin{description}\\item[Term] Alpha\\item[Other] Beta\\end{description}"
  let doc (scope : String) (o : Option String) : String :=
    article "" ("\\usepackage{enumitem}" ++ (o.map (s!"\\setlist{scope}\{{·}}")).getD "" ++
      "\n\\newcommand{\\probeword}{x}") lists
  { reader := "\\setlist"
    settings := (Compat.setlistLengthKeys.map (·.1 ++ "=3em")) ++ ["label=x", "label=(\\alph*)",
      "nosep", "noitemsep", "align=left", "font=\\bfseries", "labelsep=1em", "parsep=0pt",
      "start=3", invented]
    docs := [doc "[itemize]", doc "[enumerate,2]", doc "[2]", doc ""] }

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

/-- A `\\setbeamerfont` setting written `element|fields`, followed by another preamble line. -/
def fontOf (o : Option String) : String :=
  (o.map fun s =>
    let (e, v) := elementSplit s
    s!"\\setbeamerfont\{{e}}\{{v}}\n\\newcommand\{\\probeword}\{x}").getD ""

/-- beamer's template, size, font and colour settings, in a deck that shows their elements. -/
def beamerRows : List Row :=
  [{ reader := "\\setbeamertemplate"
     settings := ["navigation symbols{}", "itemize items[circle]", "itemize item[square]",
       "enumerate items[default]", "footline[frame number]", "headline{}",
       "frametitle{\\insertframetitle}", "background{}", "blocks[rounded]",
       "section in toc[sections numbered]", "censusprobetemplate{}"]
     keyOf := elementOf
     inert := fun s => s.endsWith "{}" && Compat.emptyTemplates.contains (elementOf s)
     docs := [fun o => paintedDeck "" ((o.map fun s =>
       let e := elementOf s
       s!"\\setbeamertemplate\{{e}}{(s.drop e.length).toString}\n\\newcommand\{\\probeword}\{x}").getD ""),
       fun o => paintedDeck "" ("\\usetheme{moloch}" ++ (o.map fun s =>
       let e := elementOf s
       s!"\\setbeamertemplate\{{e}}{(s.drop e.length).toString}").getD "")] },
   { reader := "\\setbeamersize"
     settings := ["text margin left=2cm", "text margin right=2cm", "sidebar width left=2cm",
       "description width=2cm", "mini frame size=2pt", invented]
     docs := [fun o => paintedDeck "" ((o.map (s!"\\setbeamersize\{{·}}")).getD "")] },
   { reader := "\\setbeamerfont"
     settings := Compat.beamerFontElements.map (fun (e, _) => e ++ "|size=\\tiny") ++
       ["frametitle|series=\\bfseries", "frametitle|shape=\\itshape", "normal text|family=\\rmfamily",
        "footline|size=\\tiny", "item|size=\\small", "censusprobeelement|size=\\tiny"]
     keyOf := fun s => (elementSplit s).1
     anyDoc := true
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

/-- Every declaration census row. -/
def declRows : List Row :=
  [paletteRow] ++ listingRows ++ [setlistRow] ++ tcolorboxRows ++ beamerRows ++ counterDeclRows

/-- The declaration census: every setting of every row is read or named, and none read is named
unread. -/
def declCensusChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let judged := declRows.map fun row => (row, rowJudged fonts row)
  for (row, js) in judged do
    let faults := rowFaults row js
    check ref s!"settings census {row.reader}: every setting is read or named\
{String.join (faults.map ("\n  " ++ ·))}" faults.isEmpty

end Tests.ParamCensus
