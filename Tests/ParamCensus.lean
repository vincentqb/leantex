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
  /-- The head's style sheets without the custom-property declarations no `var()` reads. -/
  css : String
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

/-- A bibliography whose entries exercise biblatex's options: shared and prefixed names, long name
lists, editors, translators, identifiers, a language, and circa and uncertain dates. -/
def richBib : String :=
  "@book{rich1, author = {Anna von Probe and Bert Second and Carla Third and Dora Fourth}, " ++
  "title = {Many Hands}, publisher = {Pub}, location = {Town and City and Village}, year = 2001, " ++
  "isbn = {978-0-00-000000-2}, url = {https://example.org/rich1}, doi = {10.1000/rich1}, " ++
  "langid = {french}}\n" ++
  "@book{rich2, author = {Anna von Probe and Bert Second and Carla Third and Dora Fourth}, " ++
  "title = {Second Hands}, publisher = {Pub}, date = {2002~}, editor = {Erin Editor}, " ++
  "translator = {Finn Translator}, eprint = {1234.5678}, eprinttype = {arxiv}}\n" ++
  "@article{rich3, author = {Bea Probe}, title = {Alone}, journaltitle = {Journal}, " ++
  "date = {2003?}, editor = {Erin Editor}, language = {english}}\n" ++
  "@book{rich4, editor = {Erin Editor}, title = {Edited Words}, publisher = {Pub}, year = 2004}\n" ++
  "@book{rich5, author = {Anna von Probe and Zara Zed and Cara Third}, title = {Aardvark Words}, " ++
  "publisher = {Pub}, year = 2009}\n" ++
  "@book{rich6, translator = {Finn Translator}, title = {Translated Words}, publisher = {Pub}, " ++
  "year = 2010}\n" ++
  "@book{rich7, author = {Ola Öberg}, title = {Northern Words}, publisher = {Pub}, year = 2011}\n" ++
  "@book{rich8, author = {Zack Zorn}, title = {Last Words}, publisher = {Pub}, year = 2012}\n"

/-- A source's artifacts, its page's HTML emitted once and read without the custom properties no
`var()` reads, which render nothing. -/
def shipped (fonts : Font.FontSet) (src : String) : Shipped :=
  let (doc, ds) := bibBuild src #[("refs", refsBib), ("refs.bib", refsBib), ("rich", richBib)]
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  let lang := doc.info.language.getD "en"
  let reads := readProps (Html.document lang head tree)
  let html := Html.document lang (dropUnreadNodes reads #[] head.toList)
    (dropUnreadNodes reads #[] tree.toList)
  { pdf := (driverPdf fonts (Layout.Geom.ofPage doc.page) doc out).data, html
    body := Html.render (Html.elem "div" (plainNodes #[] tree.toList)) 0
    css := String.join ((dropUnreadNodes reads #[] head.toList).toList.filterMap fun
      | .style c => some c
      | _ => none)
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

/-- Whether a diagnostic mentions a setting: its subject is keyed by it, or, past a translation note
that only echoes the source, its message spells it. -/
def names (key : String) (d : Diag) : Bool :=
  d.subject.any (·.endsWith (":" ++ key)) || (d.code != "N0100" && spells d.message key)

/-- Whether a subject is keyed by a setting: the setting's name is one of its colon-separated parts
past the first. -/
def keyedBy (key subject : String) : Bool :=
  subject.endsWith (":" ++ key) || hasStr subject (":" ++ key ++ ":")

/-- Whether a diagnostic is a warning or an error keyed by a setting. -/
def warnsKeyed (key : String) (d : Diag) : Bool :=
  d.severity != .note && d.subject.any (keyedBy key)

/-- The codes that say a setting is not read. -/
def unreadCodes : List String :=
  ["W0101", "W0103", "W0104", "W0110", "W0340", "W0354", "W0367"]

/-- Whether a keyed warning says the setting is applied in part, which a change bears out. -/
def inPart (d : Diag) : Bool := d.subject.any (·.startsWith "partial:")

/-- Whether a diagnostic is the note an inert row gives a setting, keyed by it. -/
def notesInert (key : String) (d : Diag) : Bool :=
  d.code == "N0100" && hasStr d.message "→ nothing:" && d.subject.any (keyedBy key)

/-- One reader's vocabulary: each setting as the document writes it, the documents it is tried in
(`none` without it), the name its diagnostics carry, and whether a setting is an inert row of the
reader's own table, whose premise its note stands on. -/
structure Row where
  reader : String
  settings : List String
  docs : List (Option String → String)
  keyOf : String → String := fun s => (KeyVal.entry s).1
  inert : String → Bool := fun _ => false
  /-- Whether a setting is tried in the document of that index: a document holding nothing it acts
  on, or already asking for it, tries nothing. -/
  tries : String → Nat → Bool := fun _ _ => true
  /-- Whether the documents are alternative grounds, a setting read where its element stands: one
  a document without that element leaves unread is a document's own unused setting. -/
  anyDoc : Bool := false
  /-- A key written before each setting in its declaration, whose own name must not stand for it. -/
  neighbour : Option String := none

/-- A setting's verdict in one document: whether the artifacts changed, whether a warning or an
error keyed by it or its inert row's note names it, and whether one names it unread although the
PDF or the page changed. -/
def judge (fonts : Font.FontSet) (base : Shipped) (src key : String) (inert : Bool) :
    Bool × Bool × Bool :=
  let w := shipped fonts src
  let fresh := w.diags.filter fun d =>
    !base.diags.any fun b => b.code == d.code && b.message == d.message && b.subject == d.subject
  let changed := w.pdf != base.pdf || w.html != base.html || w.md != base.md
  let shows := w.pdf != base.pdf || w.body != base.body || w.css != base.css
  let warned := fresh.filter (warnsKeyed key)
  let noted := if inert then fresh.filter (notesInert key) else #[]
  let unread := warned.any (fun d => unreadCodes.contains d.code && !inPart d) ||
    (warned.isEmpty && !noted.isEmpty)
  (changed, !warned.isEmpty || !noted.isEmpty, shows && unread)

/-- Each setting of a row with its verdict in each document, every build spawned at once. -/
def rowJudged (fonts : Font.FontSet) (row : Row) : List (String × List (Task (Bool × Bool × Bool))) :=
  let bases := row.docs.zipIdx.map fun (d, i) => (d, i, Task.spawn fun _ => shipped fonts (d none))
  row.settings.map fun s =>
    let key := row.keyOf s
    let inert := row.inert s
    let written := (row.neighbour.map (· ++ ", " ++ s)).getD s
    (s, (bases.filter fun (_, i, _) => row.tries s i).map fun (d, _, b) => b.bind fun base =>
      Task.spawn fun _ => judge fonts base (d (some written)) key inert)

/-- The settings of a row some document reads by nothing and names by nothing, and those named
unread although they change an artifact. -/
def rowFaults (row : Row) (judged : List (String × List (Task (Bool × Bool × Bool)))) :
    List String :=
  judged.filterMap fun (s, tasks) =>
    let verdicts := tasks.map Task.get
    if verdicts.any (·.2.2) then
      some s!"{row.reader} '{s}': named unread or as changing nothing, yet it changes an artifact"
    else if (if row.anyDoc then verdicts.any else verdicts.all) fun (c, n, _) => c || n then none
    else
      let silent := (verdicts.zipIdx.filter fun ((c, n, _), _) => !c && !n).map (·.2)
      some s!"{row.reader} '{s}': read by nothing and named by nothing in documents {silent}"

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

def article (opts pre body : String) (list : String := bibtexList) (lead : String := "")
    (cls : String := "article") : String :=
  s!"\\documentclass{opts}\{{cls}}\n\\title\{Probe title}\\author\{Probe author}\n{pre}\n" ++
    s!"\\begin\{document}\n\\maketitle\n{lead}{articleBody}{body}\n{list}\n\\end\{document}\n"

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
  | "url" | "xurl" => "See \\url{https://example.org/~probe} here."
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
  else if k == "sorting" then "ydnt" else if k == "maxsortnames" then "4" else if k.startsWith "max" then "1"
  else if k.startsWith "min" then "2" else if k == "sortlocale" then "sv_SE"
  else if k == "language" then "french"
  else if k == "backend" then "biber" else if k == "bibencoding" || k == "texencoding" then "utf8"
  else if k == "autolang" || k == "babel" then "other" else if k == "uniquename" || k == "uniquelist" then "false"
  else if k == "dashed" || k == "isbn" || k == "url" || k == "doi" || k == "eprint" then "false"
  else if ["useauthor", "useeditor", "abbreviate", "clearlang"].contains k then "false"
  else "true"

/-- The settings a census reads for a package beyond its native and inert tables. -/
def packageSettings : String → List String
  | "geometry" =>
    Compat.geometryPageKeys.map (·.name ++ "=3cm") ++
      ["left=3cm,right=3cm", "top=3cm,bottom=3cm", "left=3cm", "top=3cm", "tmargin=3cm,bmargin=2cm",
       "vmargin={3cm,2cm}", "textheight=20cm,vmarginratio=1:1", "vcentering,textheight=20cm",
       "centering,textheight=20cm", "a4paper", "a5paper",
       "legalpaper", "paperwidth=10cm,paperheight=12cm", "headheight=20pt", "verbose"] ++
      Compat.geometryNoFurniture ++ Compat.driverOptions ++ geometryDocumented
  | "hyperref" => hyperrefSettings
  | "crop" => Compat.cropModes.map (·.1) ++ Compat.cropInert.map (·.1)
  | "lineno" => Compat.linenoInert ++ Compat.linenoNatives.map (·.1)
  | "babel" => ["english", "french", "main=french", "german,english"]
  | "parskip" => ["skip=10pt", "indent"]
  | "beamerposter" => ["size=a1", "orientation=portrait", "scale=1.4"]
  | "caption" | "subcaption" => ["skip=20pt", "position=top", "font=small"]
  | "natbib" => CiteDecl.Opt.names.map (·.1) ++ ["super"]
  | "biblatex" => (["style=authoryear", "maxnames=1", "giveninits=true", "sorting=ydnt"] ++
    (Compat.biblatexRead ++ Compat.biblatexInert).map fun k => s!"{k}={biblatexSample k}").eraseDups
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
    let cited := "\\cite{rich1}, \\cite{rich2}, \\cite{rich3}, \\cite{rich4}, \\cite{rich5}, " ++
      "\\cite{rich6}, \\cite{rich7}, \\cite{rich8} and \\textcite{rich1}."
    let doc (lead : String) (o : Option String) : String :=
      let given := if lead.isEmpty then o else some (along lead o)
      article "" (pre given ++ "\\addbibresource{refs.bib}\\addbibresource{rich.bib}") cited
        (list := "\\printbibliography")
    [doc "", doc "style=authoryear", doc "style=authoryear,maxnames=2,maxitems=2",
      doc "maxsortnames=2"]
  else if p == "crop" then
    [fun o => plain "" (pre o ++ "\\page{ bleed = 5mm }"),
     fun o => plain "" ("\\page{ marks = cut }" ++ pre o ++ "\\page{ bleed = 5mm }")]
  else if p == "microtype" then
    [fun o => article "" (pre o) (packageBody p),
     fun o => article "" ("\\page{ protrusion = off, expansion = off }" ++ pre o) (packageBody p)]
  else if p == "setspace" then [fun o => article "" ("\\page{ leading = 2 }" ++ pre o) (packageBody p)]
  else if p == "natbib" then
    let many := "\\citep{key1,key2,key3} and \\citep{key3,key1}."
    [fun o => article "" (pre o) many, fun o => article "" (pre (some (along "numbers" o))) many,
     fun o => article "" (pre (some (along "round" o))) many]
  else if p == "lineno" then
    [fun o => article "" (pre o ++ "\\page{ linenumbers = on }") ""]
  else if (packageVocabulary p).isEmpty then [fun o => plain "" (pre o)]
  else [fun o => article "" (pre o) (packageBody p)]

/-- Whether a package's setting is a row of an inert table its reader reads. -/
def packageInert (p s : String) : Bool :=
  let key := (KeyVal.entry s).1
  ((Compat.packageOptionsInert.lookup p).getD []).any (·.1 == s) ||
    (p == "hyperref" && Compat.hyperrefInert.any (·.1 == s)) ||
    (p == "crop" && Compat.cropInert.any (·.1 == s)) ||
    (p == "lineno" && Compat.linenoInert.contains s) ||
    (p == "biblatex" && Compat.biblatexInert.contains key) ||
    (p == "geometry" && (Compat.driverOptions.contains key || key == "verbose" || key == "headheight" ||
      key == "letterpaper"))

/-- hyperref's colour settings act only where links are coloured, the colouring itself only where
they are not yet. -/
def hyperrefTries (s : String) (i : Nat) : Bool :=
  let k := (KeyVal.entry s).1
  if k == "colorlinks" && s != "colorlinks=false" then i == 0
  else if k.endsWith "color" || k == "allcolors" || k == "hidelinks" || s == "colorlinks=false" then
    i == 1
  else true

/-- natbib's documents: author-year, numbers and round brackets, each with the choices it already
makes, which its own setting asks for again. -/
def natbibAsked : List (List String) :=
  [["authoryear", "round", "semicolon", "colon"], ["numbers", "square", "comma"],
   ["round", "authoryear", "semicolon", "colon"]]

/-- Whether a package's setting is tried in a document: one a document already asks for, a head
key in a document without a running head, or numbers' compression in an author-year document, is
not. -/
def packageTries (p s : String) (i : Nat) : Bool :=
  let k := (KeyVal.entry s).1
  if p == "hyperref" then hyperrefTries s i
  else if p == "geometry" then i == 1 || !(k.startsWith "head" || k == "nohead")
  else if p == "microtype" then
    match (Compat.packageOptionNatives.lookup p).bind (·.lookup s) with
    | some native => if hasStr native.render "= on" then i == 1 else i == 0
    | none => true
  else if p == "crop" then if s == "off" then i == 1 else i == 0
  else if p == "biblatex" then
    -- A citation's names and a list's dashes and uniqueness show in author-year citations, a minimum
    -- below a maximum that truncates, a sorting minimum where names sort before titles.
    if k == "minsortnames" then i == 3
    else if k.startsWith "min" then i == 2
    else if ["maxcitenames", "dashed", "uniquename", "uniquelist"].contains k then i == 1
    else i == 0
  else if p == "natbib" then
    !((natbibAsked[i]?).getD []).contains k && (i == 1 || !(k == "compress" || k == "sort&compress")) &&
      !(k == "bibstyle" && i == 0) && !(k == "nobibstyle" && i != 0)
  else true

/-- Every native package's options: its native and inert tables, the settings its own reader takes,
and an invented option, which only `inputenc`'s decoder names, as the driver reads the file. -/
def packageRows : List Row :=
  Compat.nativePackages.map fun p =>
    { reader := s!"\\usepackage\{{p}}"
      settings := packageVocabulary p ++ (if p == "inputenc" then [] else [invented])
      docs := packageDocs p
      inert := packageInert p
      keyOf := fun s => let k := (KeyVal.entry s).1
        if p == "biblatex" && k == "babel" then "autolang" else k
      tries := packageTries p }


/-- `\hypersetup` reads the package's keys. -/
def hypersetupRow : Row :=
  { reader := "\\hypersetup"
    settings := packageSettings.hyperrefSettings ++ [invented]
    inert := fun s => Compat.hyperrefInert.any (·.1 == s)
    tries := hyperrefTries
    docs := [fun o => article "" ("\\usepackage{hyperref}" ++ (o.map (s!"\\hypersetup\{{·}}")).getD "") "",
      fun o => article "" ("\\usepackage[colorlinks]{hyperref}" ++
        (o.map (s!"\\hypersetup\{{·}}")).getD "") ""] }

/-- A class's document holding an abstract, whose form the title-page options set. -/
def abstracted (cls : String) (o : Option String) : String :=
  s!"\\documentclass{bracketed o}\{{cls}}\n\\begin\{document}\n\\begin\{abstract}Abstract words.\\end\{abstract}\n" ++
    "Body words.\n\\end{document}\n"

/-- The class options an article, a deck, a card and the two abstracts' classes already take, or
give nothing to act on: a one-page abstract has no facing page, nor a heading to number. -/
def classSkipped : List (List String) :=
  [["10pt", "letterpaper", "notitlepage"], ["11pt"], ["10pt"],
   ["10pt", "letterpaper", "notitlepage", "twoside", "chapters"],
   ["10pt", "letterpaper", "titlepage", "twoside", "chapters"]]

/-- What each of `classDocsBeyond`'s classes already takes, as their sources declare their
defaults; a title-page class's `notitlepage` only clears the title page's named loss. -/
def classSkippedBeyond : List (List String) :=
  [["10pt", "letterpaper", "oneside", "titlepage", "notitlepage", "openany", "onecolumn", "final",
    "chapters"],
   ["10pt", "letterpaper", "twoside", "titlepage", "notitlepage", "openright", "onecolumn", "final",
    "chapters"],
   ["10pt", "letterpaper", "twoside", "openright", "onecolumn", "final", "chapters"],
   ["11pt", "a4paper", "oneside", "notitlepage", "titlepage=false", "onecolumn", "final"],
   ["11pt", "a4paper", "oneside", "titlepage", "titlepage=true", "notitlepage", "openany",
    "onecolumn", "final", "chapters"],
   ["11pt", "a4paper", "twoside", "titlepage", "titlepage=true", "notitlepage", "twoside=true",
    "openright", "onecolumn", "final", "chapters"]]

/-- The article-like classes whose options the census tries in an article's body. -/
def classDocsBeyond : List String := ["report", "book", "memoir", "scrartcl", "scrreprt", "scrbook"]

/-- KOMA-Script's class options and memoir's, each with a value its manual documents. -/
def classOptionsBeyond : List String :=
  ["parskip=full", "DIV=12", "BCOR=8mm", "headings=small", "titlepage=true", "twoside=true",
   "open=right", "toc=bibliography", "numbers=noenddot", "captions=tableheading", "abstract=true",
   "headinclude", "footinclude=true", "headsepline", "cleardoublepage=empty", "version=3.20",
   "article", "extrafontsizes", "9pt", "14pt", "17pt", "ms", "showtrims", "oldfontcommands"]

/-- The class options: each model's reads, the inert and refused ones, and others, in an article,
a deck, a card and the abstracts of an article and a report. -/
def classRow : Row :=
  { reader := "\\documentclass"
    settings := ["8pt", "10pt", "11pt", "12pt", "fontsize=12pt", "paper=a5", "b5paper",
      "twocolumn", "draft", "leqno", "fleqn", "openright", "openbib", "parskip=half",
      "aspectratio=169", "handout", "compress"] ++ Elab.classPaperOptions ++
      Elab.classOptionFlags.flatMap (·.2) ++ Elab.classOptionsInert.flatMap (·.2.map (·.1)) ++
      Elab.abstractFormOptions ++ classOptionsBeyond ++ [invented]
    inert := fun s => Elab.classOptionsInert.any (·.2.any (·.1 == s)) ||
      Elab.abstractFormOptions.contains s
    tries := fun s i =>
      let skipped := ((classSkipped ++ classSkippedBeyond)[i]?).getD []
      !skipped.contains s && !(s == "twoside=true" && skipped.contains "twoside")
    docs := [fun o => article (bracketed o) "" "", fun o => deck (bracketed o) "",
      fun o => s!"\\documentclass{bracketed o}\{card}\n\\begin\{document}\nCard words.\n" ++
        "\\end{document}\n", abstracted "article", abstracted "report"] ++
      classDocsBeyond.map fun c o => article (bracketed o) "" "" (cls := c) }

/-- `\KOMAoptions`' keys in a KOMA-Script document: the separation rules it draws none of, noted,
and keys it names. -/
def komaOptionsRow : Row :=
  let drawn := ["headsepline=false", "footsepline=false"]
  { reader := "\\KOMAoptions"
    settings := ["fontsize=12pt", "parskip=half", "DIV=12", "headings=small", "twoside=true",
      "headsepline", "footsepline=true"] ++ drawn ++ [invented ++ "=1"]
    inert := drawn.contains
    docs := [fun o => article "" ((o.map (s!"\\KOMAoptions\{{·}}")).getD "") "" (cls := "scrartcl")] }

/-- The kernel's length parameters, set in the preamble and in the body. -/
def lengthRow : Row :=
  let sample (n : String) : String :=
    if n == "textwidth" then "10cm" else if n.endsWith "rulewidth" || n == "fboxrule" then "2pt"
    else "17pt"
  let setting (o : String) : String :=
    if o == "footins" then "\\setlength{\\skip\\footins}{61pt}" else
    (if o == "censusprobelength" then "\\newlength{\\censusprobelength}" else "") ++
      s!"\\setlength\{\\{o}}\{{sample o}}"
  let pre := "\\usepackage{natbib}\\usepackage{booktabs}\\usepackage{paracol}\\runninghead{Head words}"
  let body := "\\begin{tabular}{|l|l|}\\hline A & B\\\\ \\hline\\hline C & D\\\\ \\hline\\end{tabular} " ++
    "\\begin{tabular}{ll}\\toprule A & B\\\\ \\midrule C & D\\\\ \\cmidrule(lr){1-2} E & F\\\\ " ++
    "\\bottomrule\\end{tabular} \\fbox{Boxed} " ++
    "$\\begin{array}{cc}a & b\\end{array}$\\begin{align}x &= y\\\\ z &= w\\end{align}" ++
    "\\begin{picture}(10,10)\\put(0,0){\\line(1,1){5}}\\end{picture}" ++
    "\\begin{paracol}{2}Left column words.\\switchcolumn Right column words.\\end{paracol}" ++
    "Before skips.\\smallskip After small.\\medskip After medium.\\bigskip After big."
  { reader := "\\setlength"
    inert := fun n => n == "textwidth" || match Compat.paramSites.lookup n with
      | some (.sizeReset _) | some .listReset => true
      | _ => false
    settings := Compat.paramSites.map (·.1) ++
      ["emergencystretch", "columnseprule", "marginparwidth", "linewidth", "censusprobelength",
       "bibsep", "bibhang", "belowcaptionskip", "topskip", "smallskipamount", "medskipamount",
       "bigskipamount"]
    keyOf := id
    docs := [fun o => article "" (pre ++ (o.map setting).getD "") body,
      fun o => article "" pre body (lead := (o.map setting).getD "")] }

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

/-- A list's own options: the spacing its list reads, and the keys it names. -/
def listRow : Row :=
  let list (env : String) (o : Option String) : String :=
    article "\\usepackage{enumitem}" "" s!"\\begin\{{env}}{bracketed o}\\item Alpha\\item Beta\\end\{{env}}"
  { reader := "list options"
    settings := ["label=(\\alph*)", "leftmargin=3em", "itemsep=0pt", "parsep=0pt", "noitemsep",
      "nosep", "start=3", "resume", invented]
    docs := [list "enumerate", list "itemize", list "description"] }

/-- beamer's covered-content setting, tried bare and over a share already in force. -/
def coveredRow : Row :=
  let covered (o : Option String) : String := (o.map (s!"\\setbeamercovered\{{·}}")).getD ""
  { reader := "\\setbeamercovered"
    settings := ["transparent", "transparent=30", "invisible", "dynamic", "highly dynamic", invented]
    keyOf := id
    tries := fun s i => !(s == "invisible" && i == 0)
    docs := [fun o => deck "" (covered o),
      fun o => deck "" ("\\setbeamercovered{transparent=40}\n" ++ covered o)] }

/-- A theme's options, moloch's own and another shipped theme's; an unknown theme's are its loss. -/
def themeRows : List Row :=
  [{ reader := "\\usetheme{moloch}"
     settings := ["block=fill", "block=transparent", "progressbar=frametitle", "numbering=fraction",
       invented]
     docs := [fun o => deck "" s!"\\usetheme{bracketed o}\{moloch}",
       fun o => deck "" s!"\\usepackage{bracketed o}\{beamerthememoloch}"] },
   { reader := "\\usetheme{gemini}"
     settings := ["secheader", invented]
     docs := [fun o => deck "" s!"\\usetheme{bracketed o}\{gemini}"] }]

/-- Every census row. -/
def rows : List Row :=
  packageRows ++ [hypersetupRow, classRow, komaOptionsRow, lengthRow, counterRow, listRow,
    coveredRow] ++ themeRows

/-- Whether a source's diagnostics hold a warning or an error naming a setting. -/
def warnsOf (src key : String) : Bool :=
  (elabStr src).2.any fun d => (d.code.startsWith "W" || d.code.startsWith "E") && names key d

/-- The paragraph gap a page sets between its first two lines, baseline to baseline. -/
def firstGap (fonts : Font.FontSet) (src : String) : Option Dim.Length :=
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
  let titled := "\\usepackage{hyperref}\\hypersetup{pdftitle={Probe}, " ++ invented ++ "=1}"
  t "hyperref: a key after a metadata key is read as one before it"
    (warnsOf (plain "" titled) invented)
  t "hyperref: the outline keys it is given are honoured, none named as lost"
    (["bookmarks", "bookmarks=true", "bookmarks=false", "bookmarksopen", "bookmarksopen=false",
      "bookmarksnumbered", "bookmarksnumbered=false", "pdfpagemode=UseOutlines",
      "pdfpagemode=UseNone"].all fun o => !warnsOf (hyper o) (KeyVal.entry o).1)
  t "hyperref: its drivers, log switches and default page anchors are silent"
    (["pdftex", "dvips", "xetex", "luatex", "dvipdfmx", "hypertex", "verbose", "debug",
      "pageanchor=true"].all fun o => !warnsOf (hyper o) (KeyVal.entry o).1)
  let foot (o : String) : String :=
    s!"\\documentclass\{article}\n\\usepackage{o}\{geometry}\n\\begin\{document}\nAlpha words.\n" ++
      "\\end{document}\n"
  let folioY (src : String) : Option Dim.Length :=
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
    (["TU", "T5", "X2"].all (fun e => !warnsOf (pkg "fontenc" e) e) &&
      !warnsOf (pkg "fontenc" "LGR,T1") "LGR" && !warnsOf (pkg "fontenc" "OT2,T2A") "OT2" &&
      Compat.glyphEncodings.all (fun e => warnsOf (pkg "fontenc" e) e) &&
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

/-- The diagnostics of a source that name a setting. -/
def namingOf (src key : String) : Array Diag := (elabStr src).2.filter (names key)

/-- The first baseline on a source's first page. -/
def firstY (fonts : Font.FontSet) (src : String) : Option Dim.Length :=
  ((pageLines fonts src)[0]?.bind (·[0]?)).map (·.1)

/-- Standard settings are silent where LuaLaTeX ships the same page with and without them or the
engine already does what they ask, one loss is named once, and a message names what was written. -/
def paramSilenceChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let pkg (p o : String) : String := plain "" s!"\\usepackage[{o}]\{{p}}"
  let standard : List (String × String) :=
    [("csquotes", "english=american"), ("hyperref", "pdfencoding=auto"),
     ("hyperref", "pdfencoding=unicode"), ("hyperref", "hyperfootnotes=false"),
     ("hyperref", "pdfpagelabels=false"), ("hyperref", "pdfpagemode=UseNone"),
     ("microtype", "tracking=false"), ("microtype", "kerning=false"), ("microtype", "spacing=false"),
     ("amsmath", "nointlimits"), ("amsmath", "centertags"), ("cleveref", "english"),
     ("siunitx", "output-decimal-marker={.}"), ("minted", "outputdir=build"), ("xurl", "hyphens"),
     ("fontspec", "no-math")]
  let loud := standard.filter fun (p, o) => warnsOf (pkg p o) (KeyVal.entry o).1
  t s!"silence: standard package settings name nothing unread {loud}" loud.isEmpty
  let cls (c o pre : String) : String :=
    s!"\\documentclass[{o}]\{{c}}\n{pre}\n\\begin\{document}\nProbe words.\n\\end\{document}\n"
  let classes : List (String × String × String) :=
    [("scrartcl", "version=last", ""), ("scrartcl", "titlepage=false", ""),
     ("scrartcl", "footinclude=false", ""), ("scrreprt", "open=any", ""),
     ("scrreprt", "headings=openany", ""), ("scrreprt", "openany", ""), ("report", "openany", ""),
     ("article", "usenames", "\\usepackage{xcolor}"),
     ("article", "english", "\\usepackage{babel}"), ("beamer", "unicode", ""),
     ("beamer", "presentation", "")]
  let loudClass := classes.filter fun (c, o, pre) => warnsOf (cls c o pre) (KeyVal.entry o).1
  t s!"silence: standard class options, and those a package takes, name nothing unread {loudClass}"
    loudClass.isEmpty
  t "global options: a class's language option reaches babel, and one no package takes is named"
    ((elabStr (cls "article" "french" "\\usepackage{babel}")).1.info.language == some "fr" &&
      warnsOf (cls "article" "english" "") "english")
  let thesis := "\\documentclass[12pt,a4paper,version=last,titlepage=false,footinclude=false," ++
    "open=any,headings=openany,english]{scrreprt}\n\\usepackage{babel}\n\\usepackage[T1]{fontenc}\n" ++
    "\\usepackage[english=american]{csquotes}\n\\usepackage[nointlimits,centertags]{amsmath}\n" ++
    "\\usepackage[tracking=false,kerning=false,spacing=false]{microtype}\n" ++
    "\\usepackage[usenames]{xcolor}\n\\usepackage[output-decimal-marker={.}]{siunitx}\n" ++
    "\\usepackage[pdfencoding=auto,hyperfootnotes=false,pdfpagelabels=false,pdfpagemode=UseNone]" ++
    "{hyperref}\n\\usepackage[english]{cleveref}\n\\begin{document}\n\\section{Opening}\\label{s:o}\n" ++
    "Words \\enquote{quoted} and \\cref{s:o}.\n\\end{document}\n"
  let thesisLoud := (elabStr thesis).2.filter fun d => d.code.startsWith "W" || d.code.startsWith "E"
  t s!"silence: a KOMA thesis preamble of standard settings warns of nothing \
{thesisLoud.map (·.message)}" thesisLoud.isEmpty
  let babelTwice := "\\documentclass{article}\n\\usepackage[spanish,english]{babel}\n" ++
    "\\begin{document}\nWords. \\selectlanguage{spanish} Palabras.\n\\end{document}\n"
  t "one accounting: a language without a locale is named once, where the body selects it"
    (((elabStr babelTwice).2.filter (·.code == "W0368")).size == 1 &&
      !warnsOf (plain "" "\\usepackage[spanish,english]{babel}") "spanish")
  let skips := ["\\setlength{\\leftskip}{0pt plus 1fill}", "\\setlength{\\rightskip}{0pt plus 1fill}",
    "\\setlength{\\parfillskip}{0pt plus 1fil}"]
  let twice := skips.filter fun a => (namingOf (plain "" a) ((a.drop 12).takeWhile (· != '}')).toString).size != 1
  t s!"one accounting: an unreadable length literal is named once {twice}" twice.isEmpty
  let foo1 := "\\documentclass{article}\n\\usepackage[skip=foo]{parskip}\n\\begin{document}\n" ++
    "Alpha words.\n\nBravo words.\n\\end{document}\n"
  let foo2 := plain "" "\\setlength{\\parskip}{foo}"
  t "an unreadable length value keeps the length, is named, and the page ships"
    ([foo1, foo2].all fun src =>
      (elabStr src).2.all (!·.code.startsWith "E") && warnsOf src "parskip")
  let operand (n src : String) : Bool :=
    let ds := (elabStr src).2
    ds.all (!·.code.startsWith "E") && !ds.any (fun d => d.code == "W0104" && names n d) &&
      (ds.filter fun d => d.code == "W0107" && !d.demoted).map (·.subject) ==
        #[some ("length:" ++ n)]
  let word := plain "" "\\setlength{\\zzprobe}{y}"
  t "an unreadable length value is one degraded operand, keyed by its length, never a setting \
nothing reads"
    (operand "parskip" foo1 && operand "parskip" foo2 && operand "zzprobe" word &&
      operand "parskip" (plain "" "\\addtolength{\\parskip}{y}"))
  t "a word as a length value keeps the translation the door made"
    ((elabStr word).2.any (·.code == "N0100") && (elabStr foo2).2.any (·.code == "N0100"))
  t "the abstract's title-page options and report's own are read, never named"
    ([abstracted "report" none, abstracted "report" (some "notitlepage"),
        abstracted "article" (some "titlepage"), abstracted "book" none].all fun src =>
      !(elabStr src).2.any (·.subject.any (·.startsWith "param:documentclass:")))
  let geo (pre : String) : String :=
    s!"\\documentclass\{article}\n\\usepackage[margin=1in]\{geometry}\n{pre}\n\\begin\{document}\n" ++
      "Alpha words.\n\\end{document}\n"
  t "textheight: the top margin stands under a declared text height, which names nothing"
    (firstY fonts (geo "\\setlength{\\textheight}{500pt}") == firstY fonts (geo "") &&
      !warnsOf (geo "\\setlength{\\textheight}{500pt}") "textheight")
  let body := plain "" "" |>.replace "Probe words." "Words. \\setlength{\\textheight}{500pt} More."
  let geoKeys (o : String) : String := plain "" s!"\\usepackage[{o}]\{geometry}"
  let pageNamed (src : String) : Bool := (elabStr src).2.any fun d =>
    (d.code == "W0340" || d.code == "W0343") && hasStr d.message "\\page"
  t "messages name what the author wrote, and geometry's later key wins"
    (!pageNamed body && !pageNamed (geoKeys "nofoot,footskip=1cm") &&
      !pageNamed (geoKeys "footskip=1cm,nofoot") && !pageNamed (geoKeys "nohead,headsep=1cm"))
  let overlay := deck "" "" |>.replace "\\begin{itemize}\\item<2-> one"
    "\\begin{itemize}[<+->]\\item one"
  t "a list's default overlay specification is named as one, its help no \\setlist"
    ((elabStr overlay).2.any fun d => d.code == "W0104" && hasStr d.message "overlay" &&
      !(d.help.any (hasStr · "setlist")))
  t "an unknown class or theme accounts for its options"
    (!((elabStr (cls "nosuchclass" "draft,twocolumn" "")).2.any
        (·.subject.any (·.startsWith "param:documentclass:"))) &&
      !warnsOf (deck "" "\\usetheme[secheader]{Madrid}") "secheader")

/-- A declared text height places the text block as lualatex does: under the top margin as the
kernel's `\\textheight`, beside geometry's top or bottom margin, or split 2:3 where geometry has
nothing else; a top and a bottom place it apart, and margins win over a height. -/
def textHeightChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := String.join ((List.range 160).map fun i =>
    s!"Paragraph {i} of invented words that run across the measure and on to a second line. ")
  let doc (pre : String) : String :=
    s!"\\documentclass\{article}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"
  -- The first page's body lines, its folio aside.
  let firstPage (src : String) : Array (Dim.Length × String) :=
    (((pageLines fonts src)[0]?).getD #[]).filter fun (_, l) => l.trimAscii.toString.toNat?.isNone
  let top (src : String) : Dim.Length := ((firstPage src)[0]?.map (·.1)).getD 0
  let last (src : String) : Dim.Length := ((firstPage src).back?.map (·.1)).getD 0
  let lead := Dim.pt 12
  let geo (o : String) : String := doc s!"\\usepackage[{o}]\{geometry}"
  let margin := geo "margin=1in"
  let kernel := doc "\\usepackage[margin=1in]{geometry}\n\\setlength{\\textheight}{500pt}"
  t "text height: the kernel's \\textheight keeps the top margin and ends the block 500pt below it"
    (top kernel == top margin && last kernel ≤ Dim.inch 1 + Dim.pt 500 &&
      last kernel + 2 * lead > Dim.inch 1 + Dim.pt 500 && last kernel < last margin)
  let ofTop (src : String) : Dim.Length := top src - top margin + Dim.inch 1
  t "text height: geometry's text height alone splits the leftover 2:3"
    (ofTop (geo "textheight=500pt") == (Dim.bp 792 - Dim.pt 500) * 2 / 5)
  t "text height: geometry's text height beside a bottom margin stands on it"
    (ofTop (geo "textheight=500pt,bottom=1in") == Dim.bp 792 - Dim.pt 500 - Dim.inch 1)
  t "text height: geometry's top and bottom place the block apart, tmargin and vmargin alike"
    (last (geo "top=1in,bottom=2in") ≤ Dim.bp 792 - 2 * Dim.inch 1 &&
      last (geo "top=1in,bottom=2in") + 2 * lead > Dim.bp 792 - 2 * Dim.inch 1 &&
      firstPage (geo "tmargin=1in,bmargin=2in") == firstPage (geo "top=1in,bottom=2in") &&
      firstPage (geo "vmargin={1in,2in}") == firstPage (geo "top=1in,bottom=2in") &&
      top (geo "top=1in,bottom=2in") == top margin)
  t "text height: margins win over a text height, as geometry gives them"
    (firstPage (geo "margin=1in,textheight=500pt") == firstPage margin)
  t "text height: a placed block names nothing"
    (["top=1in,bottom=2in", "textheight=500pt", "textheight=500pt,bottom=1in"].all fun o =>
      (elabStr (geo o)).2.all (·.severity == .note))

/-- A body `\\parskip` spaces the paragraphs that start after it, to the end of its group, on the page
as the preamble's value does and on the web page as the same screen gap. -/
def bodyParskipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    s!"\\documentclass\{article}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"
  let gaps (src : String) : Array Dim.Length :=
    let ys := ((((pageLines fonts src)[0]?).getD #[]).filter fun (_, l) =>
      l.trimAscii.toString.toNat?.isNone).map (·.1)
    (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a
  let paras := "Alpha.\n\nBravo.\n\nCharlie."
  let under (v : String) : Array Dim.Length := gaps (doc s!"\\setlength\{\\parskip}\{{v}}" paras)
  let body := "Alpha.\n\nBravo.\\setlength{\\parskip}{20pt}\n\nCharlie.\n\nDelta.\n\n" ++
    "{\\setlength{\\parskip}{40pt}Echo.\n\nFoxtrot.\\par}\n\nGolf."
  let g := gaps (doc "" body)
  t s!"body parskip: the paragraphs after it take its gap, a group's to the group's end ({reprStr g})"
    (g.size == 6 && g[0]? == (gaps (doc "" paras))[0]? && g[1]? == (under "20pt")[0]? &&
      g[2]? == (under "20pt")[0]? && g[3]? == (under "40pt")[0]? && g[4]? == (under "40pt")[0]? &&
      g[5]? == (under "20pt")[0]?)
  t "body parskip: a group's value alone ends with the group, the page's gap after it"
    (let g := gaps (doc "" "Alpha.\n\n{\\setlength{\\parskip}{40pt}Bravo.\\par}\n\nCharlie.")
     g[0]? == (under "40pt")[0]? && g[1]? == (gaps (doc "" paras))[0]?)
  t "body parskip: unnamed"
    ((elabStr (doc "" body)).2.all fun d => !(d.subject.any (·.endsWith "parskip")) || d.severity == .note)
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  let root := html (doc "\\setlength{\\parskip}{20pt}" paras)
  let value := String.ofList ((((root.splitOn "--parskip: ")[1]?).getD "").toList.takeWhile (· != ';'))
  let shown := html (doc "" body)
  t s!"body parskip: the web page's paragraphs after it carry the page's screen gap ({value})"
    (!value.isEmpty && hasStr shown s!"<p style=\"--parskip: {value}\">Charlie" &&
      hasStr shown "<p>Bravo" && hasStr shown s!"<p style=\"--parskip: {value}\">Golf")
  -- What the body's value spaces is what the preamble's spaces: headings, lists, quotes, centred
  -- and theorem text, each with the list and box gaps the classes set inside them.
  let rest := "\n\n\\section{Heading}\nCharlie.\n\nDelta.\n\\begin{itemize}\n\\item India.\n\n" ++
    "Juliet.\n\\end{itemize}\nEcho.\n\\begin{quote}\nKilo.\n\nLima.\n\\end{quote}\n" ++
    "\\begin{center}\nMike.\n\nNovember.\n\\end{center}\n\\begin{minipage}{5cm}\nOscar.\n\n" ++
    "Papa.\n\\end{minipage}\n\nGolf."
  let viaBody := gaps (doc "" ("Alpha.\\setlength{\\parskip}{20pt}\n\nBravo." ++ rest))
  let viaPreamble := gaps (doc "\\setlength{\\parskip}{20pt}" ("Alpha.\n\nBravo." ++ rest))
  t s!"body parskip: every block after it spaced as by the preamble's ({reprStr viaBody})"
    (viaBody.size > 10 && viaBody == viaPreamble)
  let inner := "Alpha.\n\n\\begin{center}\nBravo.\\setlength{\\parskip}{20pt}\n\nCharlie.\n" ++
    "\\end{center}\n\n\\begin{flushleft}\nDelta.\\setlength{\\parskip}{20pt}\n\nEcho.\n" ++
    "\\end{flushleft}"
  let gi := gaps (doc "" inner)
  t s!"body parskip: one set inside a centred or ragged scope spaces its paragraphs after it ({reprStr gi})"
    (gi[1]? == (under "20pt")[0]? && gi[3]? == (under "20pt")[0]?)
  let own := doc "" "Alpha.\n\n{\\setlength{\\parskip}{30pt}Bravo.}\n\nCharlie."
  t "body parskip: one set inside a paragraph's own group is named, the page's gap standing"
    (gaps own == gaps (doc "" paras) &&
      (elabStr own).2.any fun d => d.code == "W0104" && d.subject.any (·.endsWith "parskip"))
  let deck (body : String) : String :=
    s!"\\documentclass\{beamer}\n\\begin\{document}\n{body}\n\\end\{document}\n"
  let frames := "\\begin{frame}\nAlpha.\\setlength{\\parskip}{20pt}\n\nBravo.\n\\end{frame}\n" ++
    "\\begin{frame}\nCharlie.\n\nDelta.\n\\end{frame}"
  let plain := "\\begin{frame}\nAlpha.\n\nBravo.\n\\end{frame}\n" ++
    "\\begin{frame}\nCharlie.\n\nDelta.\n\\end{frame}"
  let ys (src : String) (k : Nat) : Array Dim.Length :=
    (((pageLines fonts src)[k]?).getD #[]).map (·.1)
  t "body parskip: a frame's value ends with the frame"
    (ys (deck frames) 1 == ys (deck plain) 1 && ys (deck frames) 0 != ys (deck plain) 0)
  let deckRoot := html (s!"\\documentclass\{beamer}\n\\setlength\{\\parskip}\{20pt}\n" ++
    "\\begin{document}\n\\begin{frame}\nAlpha.\n\nBravo.\n\\end{frame}\n\\end{document}\n")
  let deckValue := String.ofList ((((deckRoot.splitOn "--parskip: ")[1]?).getD "").toList.takeWhile (· != ';'))
  t s!"body parskip: a frame's paragraphs carry the deck's screen gap ({deckValue})"
    (!deckValue.isEmpty && hasStr (html (deck frames)) s!"--parskip: {deckValue}")
  -- A group's close leaves a length no token declared at its opening undeclared again.
  let table := "\\begin{tabular}{ll}x&y\\\\\\end{tabular}"
  t "length scope: a table after a group setting its column gap takes the page's"
    (let after := doc "" s!"\{\\setlength\{\\tabcolsep}\{20pt}{table}\\par}\n\n{table}"
     let alone := doc "" s!"{table}\n\n{table}"
     let last (src : String) := ((shippedLines fonts src).filter fun (_, _, _, l) =>
       l.trimAscii.toString.toNat?.isNone).back?.map fun (x, _, _, l) => (x, l)
     last after == last alone && (last after).isSome)

/-- The text block a declaration places, judged on the page the class settles: geometry's keys
solved together across its calls and in their order, the kernel's `\textheight` under the top, and a
key the set leaves without effect named. -/
def textBlockChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (cls pre : String) : String :=
    s!"\\documentclass{cls}\n{pre}\n\\begin\{document}\nx\n\\end\{document}\n"
  let art (pre : String) : String := doc "{article}" pre
  let page (src : String) : Ir.PageSpec := (elabStr src).1.page
  let held (src : String) (top bottom : Dim.Length) : Bool :=
    (page src).vmargin == top && (page src).bottomMargin == bottom
  let tall (src : String) : Dim.Length := let p := page src; p.height - p.vmargin - p.bottomMargin
  let named (src key : String) : Bool :=
    (elabStr src).2.any fun d => d.code == "W0104" && d.subject.any (·.endsWith s!":{key}")
  let quiet (src : String) : Bool := (elabStr src).2.all (·.severity == .note)
  let geo (o : String) : String := art s!"\\usepackage[{o}]\{geometry}"
  let a4 := doc "[a4paper]{article}" "\\setlength{\\textheight}{500pt}"
  t "text block: the kernel's height stands on the page the class option settles"
    ((page a4).height == (page (doc "[a4paper]{article}" "")).height &&
      (page a4).height != (page (art "")).height && tall a4 == Dim.pt 500 &&
      (page a4).vmargin == (page (art "")).vmargin)
  t "text block: geometry's lone height splits the class's page"
    (geometrySplit (page (doc "[a4paper]{article}" "\\usepackage[textheight=500pt]{geometry}"))
      (Dim.pt 500))
  t "text block: a later margin replaces the sides before it, as geometry reads its keys in order"
    (held (geo "top=1in,bottom=2in,margin=0.5in") (Dim.inch 1 / 2) (Dim.inch 1 / 2) &&
      held (geo "margin=0.5in,top=1in,bottom=2in") (Dim.inch 1) (Dim.inch 2) &&
      held (geo "margin=1in,top=2in") (Dim.inch 2) (Dim.inch 1) &&
      quiet (geo "top=1in,bottom=2in,margin=0.5in"))
  let calls (first later : String) : String :=
    art s!"\\usepackage[{first}]\{geometry}\n{later}"
  t "text block: a later geometry call's height beside both margins is named, the margins standing"
    (held (calls "margin=1in" "\\geometry{textheight=500pt}") (Dim.inch 1) (Dim.inch 1) &&
      named (calls "margin=1in" "\\geometry{textheight=500pt}") "textheight")
  t "text block: a later geometry call's ratio splits the height declared before it"
    (let p := page (calls "textheight=500pt" "\\geometry{vmarginratio=1:1}")
     p.vmargin == (p.height - Dim.pt 500) / 2 && p.bottomMargin == p.vmargin)
  t "text block: a later geometry call's top places the height declared before it"
    ((page (calls "textheight=500pt" "\\geometry{top=1in}")).vmargin == Dim.inch 1 &&
      tall (calls "textheight=500pt" "\\geometry{top=1in}") == Dim.pt 500 &&
      quiet (calls "textheight=500pt" "\\geometry{top=1in}"))
  t "text block: every geometry call solves its layout again, replacing the kernel's height"
    (held (calls "margin=1in" "\\setlength{\\textheight}{500pt}\n\\geometry{hmargin=2in}")
        (Dim.inch 1) (Dim.inch 1) &&
      tall (art "\\setlength{\\textheight}{500pt}\n\\usepackage[hmargin=1in]{geometry}") ==
        Dim.bp 792 * 7 / 10)
  t "text block: the kernel's height stands under the top a ratio or a scale placed"
    (let kernel := "\\setlength{\\textheight}{500pt}"
     let even := page (calls "vmarginratio=1:1" kernel)
     let twoToOne := page (calls "vmarginratio=2:1" kernel)
     let half := page (calls "vscale=0.5" kernel)
     let dflt := page (art ("\\usepackage{geometry}\n" ++ kernel))
     let free := even.height - even.height * (700 : Int) / 1000
     even.vmargin == free * (1 : Int) / (2 : Int) &&
       tall (calls "vmarginratio=1:1" kernel) == Dim.pt 500 &&
       twoToOne.vmargin == free * (2 : Int) / (3 : Int) &&
       half.vmargin == (half.height - half.height * (500 : Int) / 1000) * (2 : Int) / (5 : Int) &&
       dflt.vmargin == (page (art "\\usepackage{geometry}")).vmargin &&
       tall (art ("\\usepackage{geometry}\n" ++ kernel)) == Dim.pt 500)
  t "text block: a later declared height replaces the kernel's, a bottom beside a top and it is named"
    (tall (art "\\setlength{\\textheight}{500pt}\n\\page{ textheight = 600pt }") == Dim.pt 600 &&
      tall (art "\\page{ textheight = 300pt, textheight-under = 400pt }") == Dim.pt 400 &&
      tall (art "\\page{ tmargin = 1in, bmargin = 3in, textheight-under = 400pt }") == Dim.pt 400 &&
      named (art "\\page{ tmargin = 1in, bmargin = 3in, textheight-under = 400pt }") "bmargin")
  t "text block: a kernel height leaving no text block is named as a text height"
    ((elabStr (art "\\usepackage{geometry}\n\\setlength{\\textheight}{30in}")).2.any fun d =>
      d.code == "W0104" && hasStr d.message "declared text height leaves the page no text block")
  t "text block: a key an earlier call spelled is not named again, nor geometry's own default"
    (quiet (calls "textheight=500pt,vmarginratio=1:1" "\\geometry{top=1in}") &&
      quiet (calls "textheight=500pt" "\\geometry{vmarginratio=1:1}") &&
      !(elabStr (geo "textheight=0.8\\paperheight")).2.any (fun d =>
        d.subject.any (·.endsWith ":vmarginratio")) &&
      (elabStr (geo "centering,margin=1in")).2.all (fun d => d.code != "W0104") &&
      (elabStr (geo "centering,margin=1in")).2.any (fun d =>
        d.code == "N0100" && d.subject == some "param:geometry:centering"))
  t "text block: geometry reads its horizontal margins in order too"
    ((page (geo "left=2in,right=2in,margin=1in")).hmargin == Dim.inch 1 &&
      (page (geo "margin=1in,left=2in,right=2in")).hmargin == Dim.inch 2)
  t "text block: a frame class sets its text height again, so a preamble one is named"
    (let src := doc "{beamer}" "\\setlength{\\textheight}{100pt}"
     (page src).bmargin == none && (elabStr src).2.any fun d => d.code == "W0104")
  t "text block: newgeometry starts from no vertical key"
    (geometrySplit (page (calls "margin=1in" "\\newgeometry{textheight=500pt}")) (Dim.pt 500))
  t "text block: geometry after the kernel's height places the block from its own keys"
    (held (art "\\setlength{\\textheight}{500pt}\n\\usepackage[margin=1in]{geometry}")
      (Dim.inch 1) (Dim.inch 1))
  t "text block: geometry's height beside a top stands under it, its width centres the block"
    ((page (geo "textheight=500pt,top=1in")).vmargin == Dim.inch 1 &&
      tall (geo "textheight=500pt,top=1in") == Dim.pt 500 &&
      geometrySplit (page (geo "height=500pt")) (Dim.pt 500) &&
      (page (geo "width=400pt")).hmargin == ((page (geo "width=400pt")).width - Dim.pt 400) / 2)
  t "text block: vcentering and centering split a lone height evenly"
    (["vcentering,textheight=500pt", "centering,textheight=500pt"].all fun o =>
      let p := page (geo o)
      p.vmargin == (p.height - Dim.pt 500) / 2 && p.bottomMargin == p.vmargin)
  let native (keys : String) : String := art s!"\\page\{ {keys} }"
  t "text block: the native height stands under a declared margin's top, which it names partial"
    ((page (native "margin = 1in, textheight = 500pt")).vmargin == Dim.inch 1 &&
      tall (native "margin = 1in, textheight = 500pt") == Dim.pt 500 &&
      (elabStr (native "margin = 1in, textheight = 500pt")).2.any fun d =>
        d.code == "W0110" && d.subject == some "partial:\\page:margin")
  t "text block: a bottom another block leaves without effect is named there"
    (named (art "\\page{ tmargin = 1in, textheight = 500pt }\\page{ bmargin = 2in }") "bmargin" &&
      tall (art "\\page{ tmargin = 1in, textheight = 500pt }\\page{ bmargin = 2in }") == Dim.pt 500 &&
      (elabStr (art "\\page{ textheight = 500pt }\\page{ margin = 1in }")).2.any fun d =>
        d.code == "W0110" && d.subject == some "partial:\\page:margin")
  t "text block: a negative margin is refused, and margins leaving no block are named"
    ((elabStr (native "tmargin = -10pt")).2.any (fun d => d.code == "E0323") &&
      named (native "tmargin = 500pt, bmargin = 500pt") "vmargin" &&
      held (native "tmargin = 500pt, bmargin = 500pt") (page (art "")).vmargin (page (art "")).vmargin)
  t "text block: a placed page places to itself"
    (["\\page{ tmargin = 1in, bmargin = 2in }", "\\usepackage[textheight=500pt]{geometry}",
      "\\setlength{\\textheight}{500pt}"].all fun pre => (page (art pre)).placed == page (art pre))
  t "text block: the native top and bottom margins stand apart"
    (held (native "tmargin = 1in, bmargin = 2in") (Dim.inch 1) (Dim.inch 2) &&
      quiet (native "tmargin = 1in, bmargin = 2in"))
  t "text block: a bottom margin beside a top and a height is named, the height standing"
    (named (native "tmargin = 1in, bmargin = 2in, textheight = 500pt") "bmargin" &&
      tall (native "tmargin = 1in, bmargin = 2in, textheight = 500pt") == Dim.pt 500)
  t "text block: a ratio with no lone height to split is named"
    (named (native "vmarginratio = 1:1") "vmarginratio" &&
      named (native "vmarginratio = 1:1, tmargin = 1in, textheight = 500pt") "vmarginratio" &&
      (let p := page (native "textheight = 500pt, vmarginratio = 1:1")
       p.vmargin == (p.height - Dim.pt 500) / 2 && p.bottomMargin == p.vmargin))
  t "text block: a malformed ratio says what the key takes"
    ((elabStr (native "vmarginratio = half")).2.any fun d => hasStr d.message "a ratio such as 2:3")
  t "text block: a height past the page is named and the margins stand"
    (named (native "tmargin = 1in, textheight = 900pt") "textheight" &&
      held (native "tmargin = 1in, textheight = 900pt") (page (native "")).vmargin
        (page (native "")).bottomMargin)
  let img := "\\includegraphics[height=0.5\\textheight, alt={An invented box}]{a.png}"
  let store : Image.Store := { entries := #[{ src := "a.png"
                                              info := some { pxW := 144
                                                             pxH := 72 } }] }
  let html (pre : String) : String :=
    (HtmlDoc.emit { imgs := store } (elabStr (deck169 pre
      s!"\\begin\{frame}\{Pics}\n{img}\n\\end\{frame}")).1).1
  -- Half of a 90 mm stage less 80pt of margins is 34.379% of it.
  t "text block: the deck page reads a textheight fraction of the placed block"
    (hasStr (html "\\page{ tmargin = 20pt, bmargin = 60pt }") "height: 34.379dvh" &&
      !hasStr (html "\\page{ vmargin = 20pt }") "height: 34.379dvh")

/-- Every token name an engine site reads by literal stands in the engine's vocabulary, and the
lengths natbib, caption and the kernel set that the engine reads are not named unread. -/
def engineTokenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut missing : Array String := #[]
  for e in ← System.FilePath.readDir "LeanTex/Core" do
    if e.path.extension != some "lean" then continue
    let src ← IO.FS.readFile e.path
    for pre in ["tokens.find? \"", "tokens.findSourced? \"", "tokenLen \"", ".tokens \"",
        ".tokens kind \""] do
      for piece in (src.splitOn pre).drop 1 do
        let n := String.ofList (piece.toList.takeWhile (· != '"'))
        unless Ir.engineTokenNames.contains n || missing.contains n do missing := missing.push n
  check ref s!"engine tokens: each name an engine site reads stands in the vocabulary {missing}"
    missing.isEmpty
  let src := "\\documentclass{article}\n\\usepackage{natbib}\n\\setlength{\\bibsep}{0pt}\n" ++
    "\\setlength{\\belowcaptionskip}{6pt}\n\\setlength{\\topskip}{30pt}\n\\setlength{\\bibhang}{2em}\n" ++
    "\\begin{document}\nWords.\n\\end{document}\n"
  let named := ["bibsep", "belowcaptionskip", "topskip", "bibhang"].filter (warnsOf src ·)
  check ref s!"engine tokens: lengths the engine reads are not named unread {named}" named.isEmpty

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
