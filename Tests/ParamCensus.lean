module

public import Tests.Artifact
public import LeanTex.Core.KeyVal

public section

open LeanTex.Core LeanTex.Cli

/-! The settings census: every setting a reader accepts ships a different artifact, or a fresh
diagnostic names it, and no setting that changes an artifact is named unread. -/

namespace Tests.ParamCensus

/-- One source's artifacts, PDF bytes, HTML document and markdown twin, and its diagnostics. -/
structure Shipped where
  pdf : Array UInt8
  html : String
  /-- The HTML body without its custom-property declarations. -/
  body : String
  md : String
  diags : Array Diag

/-- A style attribute without its custom-property declarations, which render nothing themselves. -/
def plainAttr (a : String × String) : Option (String × String) :=
  if a.1 != "style" then some a else
    let kept := ((a.2.splitOn ";").map (·.trimAscii.toString)).filter fun d =>
      !d.isEmpty && !d.startsWith "--"
    if kept.isEmpty then none else some ("style", String.intercalate "; " kept)

mutual
/-- A typed HTML node with its custom-property declarations removed. -/
def plainNode : Html.Node → Html.Node
  | .elem tag attrs kids => .elem tag (attrs.filterMap plainAttr) (plainNodes #[] kids.toList)
  | n => n

def plainNodes (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => plainNodes (acc.push (plainNode n)) rest
end

/-- The custom properties a page reads, each spelled `--name` after a `var(`. -/
def readProps (page : String) : List String :=
  ((page.splitOn "var(--").drop 1).map fun rest =>
    "--" ++ String.ofList (rest.toList.takeWhile fun c => c.isAlphanum || c == '-' || c == '_')

/-- CSS characters without the declarations of custom properties outside `reads`, `start` saying a
declaration may begin here and `dropped` that one was just dropped, its semicolon with it. -/
def dropUnreadChars (reads : List String) : Bool → Bool → List Char → List Char
  | _, _, [] => []
  | start, dropped, c :: rest =>
    if dropped && c == ';' then dropUnreadChars reads true false rest
    else if c == '{' || c == ';' || c == '}' then c :: dropUnreadChars reads true false rest
    else if start && c.isWhitespace then c :: dropUnreadChars reads true false rest
    else if start && c == '-' && rest.head? == some '-' &&
        !reads.contains ("-" ++ String.ofList (rest.takeWhile fun d => d.isAlphanum || d == '-' || d == '_')) then
      dropUnreadChars reads true true (rest.dropWhile fun d => d != ';' && d != '}')
    else c :: dropUnreadChars reads false false rest
termination_by _ _ l => l.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have := (List.dropWhile_sublist (l := rest) (p := fun d => d != ';' && d != '}')).length_le
      omega

/-- CSS text without its declarations of custom properties no `var()` of the page reads, and without
the white space a dropped declaration leaves, for comparison. -/
def dropUnreadIn (reads : List String) (css : String) : String :=
  String.ofList ((dropUnreadChars reads true false css.toList).filter (!·.isWhitespace))

mutual
/-- A typed HTML node without the custom-property declarations nothing on its page reads. -/
def dropUnreadNode (reads : List String) : Html.Node → Html.Node
  | .elem tag attrs kids =>
    .elem tag (attrs.filterMap fun (k, v) =>
        if k != "style" then some (k, v) else
          let kept := dropUnreadIn reads v
          if kept.isEmpty then none else some (k, kept))
      (dropUnreadNodes reads #[] kids.toList)
  | .style css => .style (dropUnreadIn reads css)
  | n => n

def dropUnreadNodes (reads : List String) (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => dropUnreadNodes reads (acc.push (dropUnreadNode reads n)) rest
end

/-- The one bibliography the census documents cite. -/
def refsBib : String :=
  "@book{key1, author = {Alpha Writer}, title = {Probe Title}, publisher = {Pub}, year = 2001}\n" ++
  "@book{key2, author = {Bravo Writer and Charlie Writer and Delta Writer}, title = {Second " ++
  "Title}, publisher = {Pub}, year = 2002}\n" ++
  "@book{key3, author = {Echo Writer}, title = {Third Title}, publisher = {Pub}, year = 2003}\n"

/-- A source's artifacts, its page's HTML emitted once and read without the custom properties no
`var()` reads, which render nothing. -/
def shipped (fonts : Font.FontSet) (src : String) : Shipped :=
  let (doc, ds) := bibBuild src #[("refs", refsBib), ("refs.bib", refsBib)]
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  let lang := doc.info.language.getD "en"
  let reads := readProps (Html.document lang head tree)
  let html := Html.document lang (dropUnreadNodes reads #[] head.toList)
    (dropUnreadNodes reads #[] tree.toList)
  { pdf := (driverPdf fonts (Layout.Geom.ofPage doc.page) doc out).data, html
    body := Html.render (Html.elem "div" (plainNodes #[] tree.toList)) 0
    md := MarkdownDoc.emit doc, diags := ds ++ out.diags ++ hds }

/-- Whether `key` stands in `msg` as a whole token, not inside a longer name. -/
def spells (msg key : String) : Bool := Id.run do
  let m := msg.toList.toArray
  let k := key.toList
  if k.isEmpty then return false
  let word (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'
  for i in [0:m.size] do
    if (m.extract i (i + k.length)).toList == k then
      let before := if i == 0 then ' ' else m.getD (i - 1) ' '
      let after := m.getD (i + k.length) ' '
      if !(word before && word (k.headD ' ')) && !(word after && word (k.getLastD ' ')) then
        return true
  return false

/-- The codes that say a setting is not read. -/
def unreadCodes : List String := ["W0101", "W0103", "W0104", "W0110", "W0354", "W0356", "W0367"]

/-- Whether a diagnostic names a setting: its subject is keyed by it, or, past a translation note
that only echoes the source, its message spells it. -/
def names (key : String) (d : Diag) : Bool :=
  d.subject.any (·.endsWith (":" ++ key)) || (d.code != "N0100" && spells d.message key)

/-- One reader's vocabulary: each setting as the document writes it, the documents it is tried in
(`none` without it), and the name its diagnostics carry. -/
structure Row where
  reader : String
  settings : List String
  docs : List (Option String → String)
  keyOf : String → String := fun s => (KeyVal.entry s).1

/-- A setting's verdict in one document: whether the artifacts changed, whether a fresh diagnostic
names it, and whether one names it unread although the PDF or the HTML body changed. -/
def judge (fonts : Font.FontSet) (base : Shipped) (src key : String) : Bool × Bool × Bool :=
  let w := shipped fonts src
  let changed := w.pdf != base.pdf || w.html != base.html || w.md != base.md
  let fresh := w.diags.filter fun d =>
    !base.diags.any fun b => b.code == d.code && b.message == d.message && b.subject == d.subject
  let shows := w.pdf != base.pdf || w.body != base.body
  let naming := fresh.filter (names key)
  -- A setting noted as changing nothing that changes an artifact is read, so its note is false.
  let inert := !naming.isEmpty && naming.all fun d => d.code == "N0100" && hasStr d.message "→ nothing:"
  (changed, !naming.isEmpty,
    (shows && naming.any fun d => unreadCodes.contains d.code) || (inert && shows))

/-- Each setting of a row with its verdict in each document, every build spawned at once. -/
def rowJudged (fonts : Font.FontSet) (row : Row) : List (String × List (Task (Bool × Bool × Bool))) :=
  let bases := row.docs.map fun d => (d, Task.spawn fun _ => shipped fonts (d none))
  row.settings.map fun s =>
    let key := row.keyOf s
    (s, bases.map fun (d, b) => b.bind fun base => Task.spawn fun _ => judge fonts base (d (some s)) key)

/-- The settings of a row read by nothing and named by nothing, and those named unread although
they change an artifact. -/
def rowFaults (row : Row) (judged : List (String × List (Task (Bool × Bool × Bool)))) :
    List String :=
  judged.filterMap fun (s, tasks) =>
    let verdicts := tasks.map Task.get
    if verdicts.any (·.2.2) then
      some s!"{row.reader} '{s}': named unread or as changing nothing, yet it changes an artifact"
    else if verdicts.any fun (c, n, _) => c || n then none
    else some s!"{row.reader} '{s}': read by nothing and named by nothing"

/-- An option no reader declares, which every reader must name. -/
def invented : String := "censusprobeoption"

def articleBody : String :=
  "\\begin{titlepage}Title page words.\\end{titlepage}\n" ++
  "\\section{Opening words}\\label{s:a}\n" ++
  "Plain words with a footnote\\footnote{Note words.} and a link \\href{https://example.org}{to a " ++
  "place} and \\url{https://example.org/a-path-with-hyphens}. See Section~\\ref{s:a}, " ++
  "Equation~\\eqref{e:a}, \\cite{key1} and \\citep{key1}.\n" ++
  "\\begin{itemize}\\item Alpha item\\item Beta item\\begin{enumerate}\\item Inner one\\item Inner " ++
  "two\\end{enumerate}\\end{itemize}\n" ++
  "\\begin{equation}\\label{e:a} a^2 + b^2 = c^2 \\end{equation}\n" ++
  "\\[ \\sum_{i=1}^{n} i = \\int_0^1 f(x)\\,dx \\]\n" ++
  "\\begin{figure}[ht]\\centering\\rule{2cm}{1cm}\\caption{Figure caption words}\\label{f:a}" ++
  "\\end{figure}\n" ++
  "\\begin{table}[ht]\\centering\\caption{Table caption words}\\begin{tabular}{ll}\\hline A & B\\\\ " ++
  "\\hline C & D\\\\ \\hline\\end{tabular}\\end{table}\n" ++
  "Text with ``quoted words'' and dashes -- and --- here, and more words to fill a paragraph " ++
  "that wraps across the measure at least once, twice or more, with a long word such as " ++
  "extraordinarily, a hyphenated well-known term, and a comma, a stop.\n\n" ++
  "\\subsection{Second words}\\paragraph{Run in} Paragraph words, citing \\cite{key2}.\n"

/-- The bibliography an article prints: bibtex's by default. -/
def bibtexList : String := "\\bibliographystyle{plainnat}\\bibliography{refs}"

def article (opts pre body : String) (list : String := bibtexList) : String :=
  s!"\\documentclass{opts}\{article}\n\\title\{Probe title}\\author\{Probe author}\n{pre}\n" ++
    s!"\\begin\{document}\n\\maketitle\n{articleBody}{body}\n{list}\n\\end\{document}\n"

/-- An article whose settings need no body to read them. -/
def plain (opts pre : String) : String :=
  s!"\\documentclass{opts}\{article}\n{pre}\n\\begin\{document}\nProbe words.\n\\end\{document}\n"

def frameBody : String :=
  "\\begin{frame}{Frame title}Words\\pause more words\\begin{itemize}\\item<2-> one\\item two" ++
  "\\end{itemize}\\begin{block}{Block title}Block words.\\end{block}" ++
  "\\IfPackageLoadedTF{amsthm}{Theorems.}{No theorems.}\\end{frame}\n"

def deck (opts pre : String) : String :=
  s!"\\documentclass{opts}\{beamer}\n{pre}\n\\begin\{document}\n{frameBody}\\end\{document}\n"

def bracketed (o : Option String) : String := (o.map fun s => s!"[{s}]").getD ""

/-- The body that exercises a native package's settings, beside the article's own. -/
def packageBody : String → String
  | "algorithm2e" => "\\begin{algorithm}\\caption{Probe steps}\\KwIn{alpha}\\eIf{beta}{gamma\\;}" ++
    "{delta\\;}\\end{algorithm}"
  | "algpseudocode" => "\\begin{algorithmic}[1]\\State alpha\\If{beta}\\State gamma\\EndIf" ++
    "\\end{algorithmic}"
  | "listings" => "\\begin{lstlisting}\ndef probe(x):\n    return x + 1\n\\end{lstlisting}"
  | "minted" => "\\begin{minted}{python}\ndef probe(x):\n    return x + 1\n\\end{minted}"
  | "xcolor" | "color" => "\\textcolor{blue}{Coloured words} and \\colorbox{yellow}{boxed}."
  | "cleveref" => "\\cref{s:a} and \\Cref{f:a}."
  | "cancel" => "$\\cancel{x} + \\bcancel{y}$"
  | "lineno" => "\\linenumbers Numbered words."
  | "appendix" => "\\appendix\\section{Extra}More words."
  | "amsthm" => "\\newtheorem{theorem}{Theorem}\\begin{theorem}Words.\\end{theorem}"
  | "tikz" => "\\begin{tikzpicture}\\draw (0,0) -- (1,1);\\end{tikzpicture}"
  | _ => ""

/-- geometry's documented keys (its manual's §5) beside those its reader's tables name, each with a
sample value. -/
def geometryDocumented : List String :=
  ["paper=a5paper", "papername=a5paper", "totalwidth=12cm", "totalheight=18cm", "lmargin=3cm",
   "rmargin=3cm", "tmargin=3cm", "bmargin=3cm", "inner=3cm", "outer=3cm", "hscale=0.6",
   "vscale=0.6", "lines=30", "includehead", "includefoot", "includeheadfoot", "includemp",
   "includeall", "ignorehead", "ignorefoot", "ignoreheadfoot", "ignoremp", "ignoreall",
   "heightrounded", "hmarginratio=1:2", "vmarginratio=1:2", "marginratio=1:2", "hcentering",
   "vcentering", "centering", "twoside", "asymmetric", "bindingoffset=1cm", "hdivide={2cm,*,3cm}",
   "vdivide={2cm,*,3cm}", "head=20pt", "foot=40pt", "footnotesep=20pt", "marginparwidth=3cm",
   "marginparsep=1cm", "nomarginpar", "columnsep=1cm", "hoffset=1cm", "voffset=1cm",
   "offset=1cm", "layout=a5paper", "layoutwidth=10cm", "layoutheight=12cm", "landscape",
   "portrait", "reversemp", "showframe", "showcrop", "mag=1200", "truedimen", "reset", "pass",
   "total={12cm,18cm}", "body={12cm,18cm}", "text={12cm,18cm}", "scale=0.6", "ratio=1:2",
   "letterpaper", "executivepaper", "b5paper", "screen"]

/-- A value a biblatex option reads, chosen to show in the census's bibliography. -/
def biblatexSample (k : String) : String :=
  if k == "style" || k == "bibstyle" || k == "citestyle" then "authoryear"
  else if k == "sorting" then "ydnt" else if k.startsWith "max" then "1"
  else if k.startsWith "min" then "1" else if k == "language" || k == "sortlocale" then "french"
  else if k == "backend" then "biber" else if k == "bibencoding" || k == "texencoding" then "utf8"
  else if k == "autolang" then "other" else if k == "uniquename" || k == "uniquelist" then "false"
  else if k == "dashed" || k == "isbn" || k == "url" || k == "doi" || k == "eprint" then "false"
  else "true"

/-- The settings a census reads for a package beyond its native and inert tables. -/
def packageSettings : String → List String
  | "geometry" =>
    Compat.geometryPageKeys.map (· ++ "=3cm") ++
      ["left=3cm,right=3cm", "top=3cm,bottom=3cm", "left=3cm", "a4paper", "a5paper",
       "legalpaper", "paperwidth=10cm,paperheight=12cm", "headheight=20pt", "verbose"] ++
      Compat.geometryNoFurniture ++ Compat.driverOptions ++ geometryDocumented
  | "hyperref" => hyperrefSettings
  | "crop" => Compat.cropModes.map (·.1) ++ Compat.cropInert.map (·.1)
  | "lineno" => Compat.linenoInert ++ Compat.linenoNatives.map (·.1)
  | "babel" => ["english", "french", "main=french", "german,english"]
  | "parskip" => ["skip=10pt", "indent"]
  | "beamerposter" => ["size=a1", "orientation=portrait", "scale=1.4"]
  | "caption" | "subcaption" => ["skip=20pt", "position=top", "font=small"]
  | "natbib" => Bib.natbibOptions.map (·.1) ++ ["super"]
  | "biblatex" => ["style=authoryear", "maxnames=1", "giveninits=true", "sorting=ydnt"] ++
    Compat.biblatexInert.map fun k => s!"{k}={biblatexSample k}"
  | "carlito" => ["sfdefault"]
  | "ulem" => ["normalbf"]
  | _ => []
where
  hyperrefSettings : List String :=
    Compat.hyperrefLinkKeys.map (fun k => if k.endsWith "color" || k == "allcolors" then
        k ++ "=blue" else k) ++
      ["colorlinks=false", "pdftitle={Probe title words}", "pdfauthor={Probe writer}",
       "pdfsubject={Probe subject}", "pdfkeywords={probe, census}", "pdfstartview=FitH",
       "pdfpagemode=UseNone", "pdflang=fr"] ++
      Compat.hyperrefInert.map (·.1)

/-- The settings of a package beyond the invented option. -/
def packageVocabulary (p : String) : List String :=
  let own := packageSettings p
  ((Compat.packageOptionNatives.lookup p).getD []).map (·.1) ++
    ((Compat.packageOptionsInert.lookup p).getD []).map (·.1) ++ own

/-- A native package's documents: in the article, and for the frame packages in a deck. -/
def packageDocs (p : String) : List (Option String → String) :=
  let pre (o : Option String) : String := s!"\\usepackage{bracketed o}\{{p}}"
  let along (first : String) (o : Option String) : String := first ++ (o.map ("," ++ ·)).getD ""
  if p == "beamerposter" then [fun o => deck "" (pre o)]
  else if p == "hyperref" then
    [fun o => article "" (pre o) "", fun o => article "" (pre (some (along "colorlinks" o))) ""]
  else if p == "geometry" then
    [fun o => article "" (pre o) "", fun o => article "" (pre o ++ "\\runninghead{Head words}") ""]
  else if p == "ulem" then [fun o => plain "" s!"\\usepackage[{along "normalem" o}]\{ulem}"]
  else if p == "biblatex" then
    [fun o => article "" (pre o ++ "\\addbibresource{refs.bib}") "" (list := "\\printbibliography")]
  else if p == "crop" then [fun o => plain "" (pre o ++ "\\page{ bleed = 5mm }")]
  else if p == "natbib" then
    let many := "\\citep{key1,key2,key3} and \\citep{key3,key1}."
    [fun o => article "" (pre o) many, fun o => article "" (pre (some (along "numbers" o))) many,
     fun o => article "" (pre (some (along "round" o))) many]
  else if p == "lineno" then
    [fun o => article "" (pre o ++ "\\page{ linenumbers = on }") ""]
  else if (packageVocabulary p).isEmpty then [fun o => plain "" (pre o)]
  else [fun o => article "" (pre o) (packageBody p)]

/-- Every native package's options: its native and inert tables, the settings its own reader takes,
and an invented option, which only `inputenc`'s decoder names, as the driver reads the file. -/
def packageRows : List Row :=
  Compat.nativePackages.map fun p =>
    { reader := s!"\\usepackage\{{p}}"
      settings := packageVocabulary p ++ (if p == "inputenc" then [] else [invented])
      docs := packageDocs p }

/-- `\hypersetup` reads the package's keys. -/
def hypersetupRow : Row :=
  { reader := "\\hypersetup"
    settings := packageSettings.hyperrefSettings ++ [invented]
    docs := [fun o => article "" ("\\usepackage{hyperref}" ++ (o.map (s!"\\hypersetup\{{·}}")).getD "") "",
      fun o => article "" ("\\usepackage[colorlinks]{hyperref}" ++
        (o.map (s!"\\hypersetup\{{·}}")).getD "") ""] }

/-- The class options: each model's reads, the inert and refused ones, and others, in an article,
a deck and a card. -/
def classRow : Row :=
  { reader := "\\documentclass"
    settings := ["8pt", "10pt", "11pt", "12pt", "fontsize=12pt", "paper=a5", "b5paper",
      "twocolumn", "draft", "titlepage", "leqno", "fleqn", "openright", "openbib", "parskip=half",
      "aspectratio=169", "handout", "compress"] ++ Elab.classPaperOptions ++
      Elab.classOptionFlags.flatMap (·.2) ++ Elab.classOptionsInert.flatMap (·.2.map (·.1)) ++
      [invented]
    docs := [fun o => article (bracketed o) "" "", fun o => deck (bracketed o) "",
      fun o => s!"\\documentclass{bracketed o}\{card}\n\\begin\{document}\nCard words.\n" ++
        "\\end{document}\n"] }

/-- The kernel's length parameters, set in the preamble and in the body. -/
def lengthRow : Row :=
  let sample (n : String) : String :=
    if n == "textwidth" then "10cm" else if n.endsWith "rulewidth" || n == "fboxrule" then "2pt"
    else "17pt"
  let setting (o : String) : String :=
    if o == "footins" then "\\setlength{\\skip\\footins}{61pt}" else
    (if o == "censusprobelength" then "\\newlength{\\censusprobelength}" else "") ++
      s!"\\setlength\{\\{o}}\{{sample o}}"
  let pre := "\\usepackage{booktabs}\\usepackage{paracol}\\runninghead{Head words}"
  let body := "\\begin{tabular}{|l|l|}\\hline A & B\\\\ \\hline\\hline C & D\\\\ \\hline\\end{tabular} " ++
    "\\begin{tabular}{ll}\\toprule A & B\\\\ \\midrule C & D\\\\ \\cmidrule(lr){1-2} E & F\\\\ " ++
    "\\bottomrule\\end{tabular} \\fbox{Boxed} " ++
    "$\\begin{array}{cc}a & b\\end{array}$\\begin{align}x &= y\\\\ z &= w\\end{align}" ++
    "\\begin{picture}(10,10)\\put(0,0){\\line(1,1){5}}\\end{picture}" ++
    "\\begin{paracol}{2}Left column words.\\switchcolumn Right column words.\\end{paracol}"
  { reader := "\\setlength"
    settings := Compat.paramSites.map (·.1) ++
      ["emergencystretch", "columnseprule", "marginparwidth", "linewidth", "censusprobelength"]
    keyOf := id
    docs := [fun o => article "" (pre ++ (o.map setting).getD "") body,
      fun o => article "" pre ((o.map setting).getD "" ++ body)] }

/-- The counters a document sets, before what they number. -/
def counterRow : Row :=
  { reader := "\\setcounter"
    settings := ["secnumdepth", "tocdepth", "page", "section", "equation", "figure", "table",
      "footnote", "censusprobecounter"]
    keyOf := id
    docs := [fun o => article "" "\\newcounter{censusprobecounter}"
      ((o.map (s!"\\setcounter\{{·}}\{5}")).getD "" ++ "\\tableofcontents\\section{Late words}" ++
        "\\subsection{Later}\\paragraph{Late run} Words\\footnote{Late note.}." ++
        "\\begin{equation}x\\end{equation}\\thecensusprobecounter")] }

/-- A list's own options, which no list reads. -/
def listRow : Row :=
  let list (env : String) (o : Option String) : String :=
    article "\\usepackage{enumitem}" "" s!"\\begin\{{env}}{bracketed o}\\item Alpha\\item Beta\\end\{{env}}"
  { reader := "list options"
    settings := ["label=(\\alph*)", "leftmargin=3em", "itemsep=0pt", "noitemsep", "start=3",
      "resume", invented]
    docs := [list "enumerate", list "itemize", list "description"] }

/-- beamer's covered-content setting. -/
def coveredRow : Row :=
  { reader := "\\setbeamercovered"
    settings := ["transparent", "transparent=30", "invisible", "dynamic", "highly dynamic", invented]
    keyOf := id
    docs := [fun o => deck "" ((o.map (s!"\\setbeamercovered\{{·}}")).getD "")] }

/-- A theme's options, moloch's own and another theme's. -/
def themeRows : List Row :=
  [{ reader := "\\usetheme{moloch}"
     settings := ["block=fill", "block=transparent", "progressbar=frametitle", "numbering=fraction",
       invented]
     docs := [fun o => deck "" s!"\\usetheme{bracketed o}\{moloch}",
       fun o => deck "" s!"\\usepackage{bracketed o}\{beamerthememoloch}"] },
   { reader := "\\usetheme{Madrid}"
     settings := ["secheader", invented]
     docs := [fun o => deck "" s!"\\usetheme{bracketed o}\{Madrid}"] }]

/-- Every census row. -/
def rows : List Row :=
  packageRows ++ [hypersetupRow, classRow, lengthRow, counterRow, listRow, coveredRow] ++ themeRows

/-- Whether a source's diagnostics hold a warning or an error naming a setting. -/
def warnsOf (src key : String) : Bool :=
  (elabStr src).2.any fun d => (d.code.startsWith "W" || d.code.startsWith "E") && names key d

/-- The paragraph gap a page sets between its first two lines, baseline to baseline. -/
def firstGap (fonts : Font.FontSet) (src : String) : Option Dim.Sp :=
  match (pageLines fonts src)[0]? with
  | some ls => match ls[0]?, ls[1]? with
    | some (a, _), some (b, _) => some (b - a)
    | _, _ => none
  | none => none

/-- Settings read as their package or class reads them: values `\setlength` reads, standard
settings silent, a setting the engine does not honour named, and no note claiming what is not so. -/
def paramTruthChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let parskip (v : String) : String :=
    s!"\\documentclass\{article}\n\\usepackage[skip={v}]\{parskip}\n\\begin\{document}\n" ++
      "Alpha words.\n\nBravo words.\n\\end{document}\n"
  t "parskip: a skip is read as \\setlength reads it, and an unreadable one ships its page"
    (["10pt plus1pt", ".5\\baselineskip plus 2pt", "\\medskipamount", "\\baselineskip"].all
        (fun v => (elabStr (parskip v)).2.all fun d => !d.code.startsWith "E") &&
      firstGap fonts (parskip "10pt plus1pt") == some (Dim.pt 22) &&
      firstGap fonts (parskip "\\medskipamount") == some (Dim.pt 18))
  let hyper (o : String) : String := plain "" s!"\\usepackage[{o}]\{hyperref}"
  t "hyperref: the outline it asks for is named, and the none it asks for is not"
    (warnsOf (hyper "bookmarks") "bookmarks" && warnsOf (hyper "bookmarks=true") "bookmarks" &&
      !warnsOf (hyper "bookmarks=false") "bookmarks")
  t "hyperref: its drivers, log switches and default page anchors are silent"
    (["pdftex", "dvips", "xetex", "luatex", "dvipdfmx", "hypertex", "verbose", "debug",
      "pageanchor=true"].all fun o => !warnsOf (hyper o) (KeyVal.entry o).1)
  let foot (o : String) : String :=
    s!"\\documentclass\{article}\n\\usepackage{o}\{geometry}\n\\begin\{document}\nAlpha words.\n" ++
      "\\end{document}\n"
  let folioY (src : String) : Option Dim.Sp :=
    ((pageLines fonts src)[0]?.bind fun ls => ls.find? (·.2.trimAscii.toString == "1")).map (·.1)
  t "geometry: nofoot and noheadfoot set the foot at no skip, nohead leaves it"
    (folioY (foot "[nofoot]") != folioY (foot "") && folioY (foot "[noheadfoot]") == folioY (foot "[nofoot]") &&
      folioY (foot "[nohead]") == folioY (foot ""))
  let micro (cls pkg : String) : Array UInt8 :=
    let src := s!"\\documentclass{cls}\{article}\n\\usepackage[{pkg}]\{microtype}\n\\begin\{document}\n" ++
      "Words, words and words; a line of words, ending in punctuation, of words.\n\\end{document}\n"
    let (doc, _) := elabStr src
    (driverPdf fonts (Layout.Geom.ofPage doc.page) doc (layoutOf fonts doc)).data
  t "microtype: disable=ifdraft reads a draft given before it, the class's included"
    (micro "[draft]" "disable=ifdraft" == micro "" "disable" &&
      micro "" "draft,disable=ifdraft" == micro "" "disable" &&
      micro "" "disable=ifdraft,draft" == micro "" "" &&
      micro "" "activate=false" == micro "" "disable")
  let cls (opts body : String) : String :=
    s!"\\documentclass[{opts}]\{article}\n\\usepackage\{amsmath}\n\\begin\{document}\n{body}\n\\end\{document}\n"
  t "classes: the options a class already answers are silent, an unread one named"
    (["reqno", "twoside=false", "openany", "final"].all (fun o => !warnsOf (cls o "Words.") o) &&
      !warnsOf (deck "[final]" "") "final" && warnsOf (cls "leqno" "Words.") "leqno")
  let pkg (p o : String) : String := plain "" s!"\\usepackage[{o}]\{{p}}"
  t "packages: settings the engine already answers are silent, and an unread one still named"
    (["TU", "T5", "X2", "OT2", "T3", "OML"].all (fun e => !warnsOf (pkg "fontenc" e) e) &&
      !warnsOf (pkg "csquotes" "autostyle=true") "autostyle" &&
      !warnsOf (pkg "csquotes" "german=quotes") "german" &&
      warnsOf (pkg "csquotes" "german=guillemets") "german" &&
      !warnsOf (pkg "babel" "english,shorthands=off") "shorthands" &&
      !warnsOf (pkg "parskip" "indent=0pt") "indent" &&
      !warnsOf (pkg "microtype" "activate={true,nocompatibility}") "activate" &&
      warnsOf (pkg "fontenc" invented) invented)
  let len (pre body : String) : String := plain "" pre |>.replace "Probe words." body
  t "lengths: a length nothing reads is named, one the document uses is not"
    (warnsOf (len "\\newlength{\\gapprobe}\\setlength{\\gapprobe}{2pt}" "Words.") "gapprobe" &&
      !warnsOf (len "\\newlength{\\gapprobe}\\setlength{\\gapprobe}{2pt}" "Words\\hspace{\\gapprobe}.") "gapprobe" &&
      warnsOf (len "\\setlength{\\emergencystretch}{3em}" "Words.") "emergencystretch")

/-- A bare class option a page model's readers read changes that model's document: a flag listed read
that changes nothing is a drop the other models' documents cannot hide. -/
def classFlagChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let docOf : Ir.PageModel → Option (Option String → String)
    | .flow => classRow.docs[0]?
    | .frame => classRow.docs[1]?
    | .face => classRow.docs[2]?
  for (model, flags) in Elab.classOptionFlags do
    if let some doc := docOf model then
      let base := shipped fonts (doc none)
      let silent := flags.filter fun f =>
        let w := shipped fonts (doc (some f))
        w.pdf == base.pdf && w.html == base.html && w.md == base.md
      check ref s!"settings census \\documentclass flags a page model reads change its document \
{silent}" silent.isEmpty

/-- The census: every setting of every row is read or named, and none read is named unread. -/
def paramCensusChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let judged := rows.map fun row => (row, rowJudged fonts row)
  for (row, js) in judged do
    let faults := rowFaults row js
    check ref s!"settings census {row.reader}: every setting is read or named\
{String.join (faults.map ("\n  " ++ ·))}" faults.isEmpty
  classFlagChecks ref fonts

end Tests.ParamCensus
