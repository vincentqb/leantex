module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim

/-! The kernel and package constructs a venue's style file and paper lean on. -/

/-- Every body line's text, place and size. -/
private def venueLines (out : Layout.Out) : Array (String × Length × Length × Length) :=
  (bodyLines out).map fun l => (lineText l, l.x, l.y, l.size)

/-- classes.dtx's old font commands set as their declarations do, one axis over the normal font. -/
def oldFontCmdChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let set (body : String) : Layout.Out := layoutOf fonts (elabStr (dvDoc "" body)).1
  let html (body : String) : String := docHtmlOf (elabStr (dvDoc "" body)).1
  let old := "{\\bf Bold} {\\it Ital} {\\tt Mono} {\\sc Caps} {\\sl Slant} {\\rm Roman}"
  let new := "{\\normalfont\\bfseries Bold} {\\normalfont\\itshape Ital} " ++
    "{\\normalfont\\ttfamily Mono} {\\normalfont\\scshape Caps} {\\normalfont\\slshape Slant} " ++
    "{\\normalfont\\rmfamily Roman}"
  t "an old font command sets its text as the normal font with its one axis"
    (venueLines (set old) == venueLines (set new) && html old == html new)
  t "an old font command is no undefined command"
    ((elabStr (dvDoc "" old)).2.all (·.code != "W0301"))

/-- A family default naming an NFSS family selects the face its psnfss package selects. -/
def familyDefaultChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fontsOf (pre : String) : Ir.FontSpec := (elabStr (dvDoc pre "x")).1.fonts
  let named := fontsOf "\\renewcommand{\\rmdefault}{ptm}\n\\renewcommand{\\sfdefault}{phv}\n"
  let times := fontsOf "\\usepackage{times}\n"
  t "\\rmdefault and \\sfdefault naming ptm and phv set the faces times sets for those slots"
    (named.body == some "TeX Gyre Termes" && named.sans == some "TeX Gyre Heros" &&
      named.body == times.body && named.sans == times.sans)
  t "a family default the table does not name declares no face"
    (let odd := fontsOf "\\renewcommand{\\rmdefault}{zzz}\n"
     odd.body == (fontsOf "").body && odd.sans == (fontsOf "").sans)

/-- A `\csname … \endcsname` the engine does not resolve sets none of its name's letters. -/
def csnameInkChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let text (pre body : String) : String :=
    String.join ((bodyLines (layoutOf fonts (elabStr (dvDoc pre body)).1)).toList.map (lineText ·))
  t "an unresolved control name's letters are not ink"
    (text "" "\\csname zzunknown\\endcsname Body words." == "Body words.")
  let patch := "\\newcommand*\\patchX[1]{\\expandafter\\let\\csname old#1\\expandafter" ++
    "\\endcsname\\csname #1\\endcsname}\n"
  t "a package-style environment patch run at the body's start sets nothing"
    (text patch "\\patchX{equation}Body words." == "Body words.")
  t "the text after a \\csname with no \\endcsname still sets"
    (hasStr (text "" "Before \\csname zz") "Before")

/-- fancyvrb's `Verbatim`, and an environment `\DefineVerbatimEnvironment` derives from it, set
their body as minted's code block in the `text` lexer with the options declared. -/
def fancyVerbatimChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let set (pre body : String) : Layout.Out := layoutOf fonts (elabStr (dvDoc pre body)).1
  let code := "theorem a_b (w : W) : f w ≤ f w := by\n  rfl\n"
  let minted := set "" ("\\begin{minted}[fontsize=\\footnotesize, breaklines=true]{text}\n" ++
    code ++ "\\end{minted}")
  let derived := set
    "\\DefineVerbatimEnvironment{X}{Verbatim}{fontsize=\\footnotesize, breaklines=true}\n"
    ("\\begin{X}\n" ++ code ++ "\\end{X}")
  t "a derived fancyvrb environment sets the minted block its options declare"
    (venueLines derived == venueLines minted)
  t "its lines and underscores are kept"
    ((venueLines derived).toList.map (·.1) |>.contains "theorem a_b (w : W) : f w ≤ f w := by")
  let plain := set "" ("\\begin{Verbatim}[fontsize=\\footnotesize]\n" ++ code ++ "\\end{Verbatim}")
  let plainMinted := set "" ("\\begin{minted}[fontsize=\\footnotesize]{text}\n" ++ code ++
    "\\end{minted}")
  t "fancyvrb's own Verbatim reads its written options"
    (venueLines plain == venueLines plainMinted)
  t "the definition is read, not an undefined command"
    ((elabStr (dvDoc "\\DefineVerbatimEnvironment{X}{Verbatim}{}\n" "x")).2.all
      (·.code != "W0301"))

/-- An environment opening with a macro that sets a heading sets it as a heading, and an
environment `\let` to one discarding its body discards it too. -/
def venueEnvChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let set (pre body : String) := venueLines (layoutOf fonts (elabStr (dvDoc pre body)).1)
  let heading := "\\newcommand{\\acksection}{\\section*{Thanks}}\n"
  t "a heading an environment's opening reaches through a macro is a heading"
    (set (heading ++ "\\newenvironment{ack}{\\acksection}{}\n") "Start.\n\\begin{ack}Body.\\end{ack}" ==
      set "" "Start.\n\n\\section*{Thanks}\nBody.")
  t "an environ environment reaching a heading through a macro sets it as a heading"
    (set (heading ++ "\\usepackage{environ}\n\\NewEnviron{ack}{\\acksection\\BODY}\n")
        "Start.\n\\begin{ack}Body.\\end{ack}" ==
      set "" "Start.\n\n\\section*{Thanks}\nBody.")
  let hidden := heading ++ "\\usepackage{environ}\n\\NewEnviron{ack}{\\acksection\\BODY}\n" ++
    "\\NewEnviron{hide}{}\n\\let\\ack\\hide\n\\let\\endack\\endhide\n"
  t "an environment let to one discarding its body discards it"
    (set hidden "Start.\n\n\\begin{ack}Secret words.\\end{ack}\n\nEnd." == set "" "Start.\n\nEnd." &&
      (elabStr (dvDoc hidden "x")).2.all (·.code != "W0301"))

/-- A weight a refused title's body declares at a tabular cell's start sets the author's first line
only, as the cell's row is all it reaches. -/
def authorCellFontChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let titleBody (cell : String) : String :=
    "\\makeatletter\n\\renewcommand{\\maketitle}{\\par\\begingroup" ++
    "\\long\\def\\@makefntext##1{##1}\\@maketitle\\endgroup}\n" ++
    "\\renewcommand{\\@maketitle}{\\vbox{\\hsize\\textwidth\\centering " ++
    "{\\LARGE\\bf \\@title\\par}" ++ cell ++ "}}\n\\makeatother\n" ++
    "\\title{Invented Title}\n\\author{Ada Example \\\\ Example University}\n"
  let html (pre : String) : String := docHtmlOf (elabStr (dvDoc pre "\\maketitle\nBody.")).1
  let inCell := html (titleBody "\\begin{tabular}[t]{c}\\bf \\@author\\end{tabular}")
  t "a cell's weight sets the author's name and not the lines below it"
    (hasStr inCell "<strong>Ada Example" && !hasStr inCell "Example University</strong>")
  let outside := html (titleBody "{\\bf \\begin{tabular}[t]{c}\\@author\\end{tabular}}")
  t "a weight declared around the tabular sets every author line"
    (hasStr outside "Example University</strong>")

/-- A counter macro opening an environment keeps it in its sentence, a defined
`\csname` name is its command, a brace-held `]` stays in fancyvrb's options, a definition the
reader does not set as code is named, and a `\let` stored in a definition hides nothing. -/
def venueEdgeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let lines (pre body : String) := bodyLines (layoutOf fonts (elabStr (dvDoc pre body)).1)
  let text (pre body : String) := String.join ((lines pre body).toList.map (lineText ·))
  let tag := "\\newcounter{note}\n\\newcommand{\\bump}{\\stepcounter{note}}\n" ++
    "\\newenvironment{tag}{\\bump[\\thenote:}{]}\n"
  t "an environment opening with a counter macro stays in its sentence"
    ((lines tag "Words before \\begin{tag}tagged\\end{tag} words after.").size == 1)
  t "a \\csname naming a defined command sets that command"
    (text "\\newcommand{\\foo}{Hello}\n" "\\csname foo\\endcsname{} world." == "Hello world.")
  let (_, braced) := elabStr (dvDoc ""
    "\\begin{Verbatim}[label={[a]b}, fontsize=\\footnotesize]\na_b\n\\end{Verbatim}")
  t "a brace-held bracket stays inside fancyvrb's options"
    (braced.all (·.code != "E0304") && hasStr (text ""
      "\\begin{Verbatim}[label={[a]b}]\na_b\n\\end{Verbatim}") "a_b")
  let (_, other) := elabStr (dvDoc "\\DefineVerbatimEnvironment{Y}{BVerbatim}{}\n" "x")
  t "a definition on a base the reader does not set is named, not noted as read"
    (other.any (·.code == "W0458") && !other.any fun d => d.code == "N0100" &&
      hasStr d.message "DefineVerbatimEnvironment")
  let stored := "\\usepackage{environ}\n\\NewEnviron{ack}{\\BODY}\n\\NewEnviron{hide}{}\n" ++
    "\\newcommand{\\later}{\\let\\ack\\hide}\n"
  t "a \\let stored in a definition hides nothing until it runs"
    (hasStr (text stored "\\begin{ack}Shown words.\\end{ack}") "Shown words.")

/-- A verbatim environment defined in an included file is named there, never noted as read. -/
def fancyIncludedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (_, ds, _) ← runStyParity "fancy-input"
  t "a definition in an included file is named where it stands"
    ((ds.filter fun d => d.code == "W0458" && d.span.any (·.file.endsWith "fancy-part.tex")).size == 1 &&
      !ds.any fun d => d.code == "N0100" && hasStr d.message "DefineVerbatimEnvironment")

/-- A document's artifacts: the page's lines, its HTML, its markdown twin and its PDF's bytes. -/
private def venueArtifacts (fonts : Font.FontSet) (doc : Ir.Doc) : String × String × String × ByteArray :=
  let out := layoutOf fonts doc
  let page := String.intercalate "\n" ((bodyLines out).toList.map (lineText ·))
  let pdf := pdfText (Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info)
  (page, (HtmlDoc.emit {} doc).1, MarkdownDoc.emit doc, pdf)

/-- A style's `\@maketitle` sets, under its conditionals, the block it chooses where the author
would stand: in submission mode its anonymous block in every artifact, the real author nowhere. -/
def anonymousTitleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (anon, _, _) ← runStyParity "venue-anon"
  let (page, html, md, pdf) := venueArtifacts fonts anon
  t "a submission's page sets the style's anonymous block" (hasStr page "Unnamed Writer(s)" &&
    hasStr page "Withheld Institution")
  t "the anonymous cell's declarations reach its first row, as a tabular cell's do"
    (hasStr html "Unnamed Writer(s) </strong>" && !hasStr html "Institution </strong>")
  t "a submission names its author in no artifact"
    (!hasStr page "Ada Example" && !hasStr html "Ada Example" && !hasStr md "Ada Example" &&
      !bytesContain pdf "Ada Example" && !hasStr page "example.org" && !hasStr html "example.org")
  let (final, _, _) ← runStyParity "venue-final"
  let (fpage, fhtml, _, _) := venueArtifacts fonts final
  t "a final copy sets the author the document declares"
    (hasStr fpage "Ada Example" && hasStr fhtml "Ada Example" && !hasStr fpage "Unnamed Writer")

/-- A size command redefined as `\fontsize{size}{skip}\selectfont` sets that size and skip, the
last redefinition of a name winning and the refusal of an earlier one withdrawn. -/
def sizeRedefinitionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let words := "Widgets turn and gears mesh while the invented machine hums along its track, " ++
    "each part in its place and every bolt fastened as the drawing asks of it, over and over."
  let set (pre body : String) := (bodyLines (layoutOf fonts (elabStr (dvDoc pre body)).1)).map
    fun l => (lineText l, l.x, l.y)
  let redefined := "\\renewcommand{\\tiny}{\\fontsize{6pt}{7pt}\\selectfont}\n"
  t "a size command redefined by \\fontsize sets the size and skip it declares"
    (set redefined ("{\\tiny " ++ words ++ "\\par}") ==
      set "" ("{\\fontsize{6pt}{7pt}\\selectfont " ++ words ++ "\\par}"))
  let twice := "\\makeatletter\\renewcommand{\\tiny}{\\@setfontsize\\tiny\\@vipt\\@viipt}" ++
    "\\makeatother\n" ++ redefined
  t "a later redefinition withdraws the refusal of an earlier one"
    ((elabStr (dvDoc twice "x")).2.all (·.code != "W0361"))

/-- A style's author separators set the names they part side by side, each a box of its natural
width, the slack spread evenly around them, and a separator breaking the line starts a row below. -/
def authorSeparatorChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds, _) ← runStyParity "venue-authors"
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let at? (w : String) := lines.find? fun l => hasStr (lineText l) w
  match at? "Ada Example", at? "Bob Placeholder", at? "Cy Sample", at? "Example University" with
  | some a, some b, some c, some u =>
    t "names a separator parts stand side by side on one baseline" (a.y == b.y && a.x < b.x)
    t "a name's lines stand under its first" (a.y < u.y)
    t "a separator breaking the line starts a row below" (b.y < c.y && a.y < c.y)
    let geom := Layout.Geom.ofPage doc.page
    let mid := geom.hmargin + geom.textWidth / 2
    let row := lines.filter fun l => a.y ≤ l.y && l.y < c.y
    let widest (keep : Layout.LineOut → Bool) : Option Layout.LineOut :=
      (row.filter keep).foldl (fun m l => match m with
        | some w => if w.setWidth < l.setWidth then some l else m
        | none => some l) none
    match widest (·.x < mid), widest (mid < ·.x) with
    | some wa, some wb =>
      let left := wa.x - geom.hmargin
      let between := wb.x - (wa.x + wa.setWidth)
      let right := geom.hmargin + geom.textWidth - (wb.x + wb.setWidth)
      -- Each box is its widest line and a `\tabcolsep` on each side, its slack even around them.
      let d := between - left - Dim.pt 6
      let e := left - right
      t "a row's slack stands evenly before, between and after its boxes"
        (Dim.pt 0 ≤ Dim.pt 1 + d && d ≤ Dim.pt 1 && Dim.pt 0 ≤ Dim.pt 1 + e && e ≤ Dim.pt 1)
    | _, _ => t "each name's widest line is set" false
  | _, _, _, _ => t "every name of the authors is set" false
  t "a separator the style defines is no undefined command"
    (ds.all fun d => !(d.code == "W0301" && (hasStr d.message "And" || hasStr d.message "AND")))
  let many := String.intercalate " \\And " ((List.range 6).map fun k =>
    s!"Invented Name{k} Placeholder \\\\ Example Laboratory of Long Names")
  let wide := elabStr ("\\documentclass{article}\n\\makeatletter\n" ++
    "\\renewcommand{\\maketitle}{\\par\\begingroup\\long\\def\\@makefntext##1{##1}\\@maketitle" ++
    "\\endgroup}\n\\renewcommand{\\@maketitle}{\\vbox{\\centering {\\LARGE\\bf \\@title\\par}" ++
    "\\def\\And{\\end{tabular}\\hfil\\linebreak[0]\\hfil\\begin{tabular}[t]{c}\\ignorespaces}" ++
    "\\begin{tabular}[t]{c}\\@author\\end{tabular}}}\n\\makeatother\n\\title{Invented Title}\n" ++
    "\\author{" ++ many ++ "}\n\\begin{document}\n\\maketitle\nBody.\n\\end{document}")
  let wideOut := layoutOf fonts wide.1
  let ys := ((List.range 6).filterMap fun k =>
    ((bodyLines wideOut).find? fun l => hasStr (lineText l) s!"Invented Name{k} ").map (·.y)).eraseDups
  t "a row of names too wide for the measure wraps onto lines of its own, none overfull"
    (ys.length > 1 && ((List.range 6).all fun k =>
      (bodyLines wideOut).any fun l => hasStr (lineText l) s!"Invented Name{k} ") &&
      wideOut.diags.all (·.code != "W0005"))
  t "the web page sets a row of names as boxes wrapping and spaced evenly"
    (hasStr (docHtmlOf doc) "flex-wrap: wrap" && hasStr (docHtmlOf doc) "space-evenly")

/-- A style's title notice, its bottom float on the title's page, stands below that page's text and
footnotes as furniture, and follows the title on the web page. -/
def titleNoticeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, _, _) ← runStyParity "venue-anon"
  let out := layoutOf fonts doc
  let notice := "Under review at an invented venue. Do not distribute."
  match out.pages[0]? with
  | some page =>
    let noticeLines := page.lines.filter fun l => lineText l == notice
    let bodyYs := page.lines.filter (!·.furniture) |>.map (·.y)
    t "the title's page sets the style's notice once, as furniture"
      (noticeLines.size == 1 && noticeLines.all (·.furniture))
    t "the notice stands below the page's text"
      (noticeLines.all fun l => bodyYs.all (· < l.y))
  | none => t "the title's page is set" false
  t "no later page sets the notice"
    ((out.pages.extract 1 out.pages.size).all fun p => p.lines.all (lineText · != notice))
  t "the web page sets the notice after the title" (hasStr (docHtmlOf doc) notice)
  let (final, _, _) ← runStyParity "venue-final"
  t "a final copy sets the notice its options choose"
    ((layoutOf fonts final).pages[0]?.any fun p => p.lines.any (lineText · == "Invented Venue 2026."))

/-- TeX's italic correction `\/` is a control symbol: no undefined command, and the space after it
stays text. -/
def italicCorrectionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\newcommand{\\ord}{40th}\n" "Some \\ord\\/ Conference and {\\itshape shelf\\/} next."
  let (doc, ds) := elabStr src
  t "the space after an italic correction stays text"
    (String.join ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·)) ==
      "Some 40th Conference and shelf next.")
  t "an italic correction is no undefined command" (ds.all (·.code != "W0301"))

/-- The skip a refused title body declares after its bottom bar moves the author by its length, the
author's paragraph opening with the `\\parskip` in force. -/
def titleBarSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (skip : String) : String :=
    "\\makeatletter\n\\renewcommand{\\maketitle}{\\par\\begingroup" ++
    "\\long\\def\\@makefntext##1{##1}\\@maketitle\\endgroup}\n" ++
    "\\renewcommand{\\@maketitle}{\\vbox{\\centering {\\LARGE\\bf \\@title\\par}" ++
    "\\vskip 0.25in\\hrule height 1\\p@\\vskip " ++ skip ++
    "\\begin{tabular}[t]{c}\\@author\\end{tabular}}}\n\\makeatother\n" ++
    "\\title{Invented Title}\n\\author{Ada Example}\n"
  let authorY (skip : String) : Option Length :=
    ((bodyLines (layoutOf fonts (elabStr (dvDoc (doc skip) "\\maketitle\nBody.")).1)).find?
      (lineText · == "Ada Example")).map (·.y)
  match authorY "0.1in", authorY "0.6in" with
  | some near, some far =>
    t "a declared skip after the bar moves the author by its length"
      (Dim.inch 1 / 2 - Dim.pt 1 / 10 ≤ far - near && far - near ≤ Dim.inch 1 / 2 + Dim.pt 1 / 10)
  | _, _ => t "the author is set" false
  -- lualatex sets this author's baseline 15.56 pt under the bar: the skip, no parskip, a row strut.
  let c := censusOfSrc fonts (dvDoc (doc "0.1in") "\\maketitle\nBody.")
  match (pageRuleSegs c 0).back?, lineYOf c 0 "Ada Example" with
  | some (bar, _), some y =>
    t "the author stands from the bar as lualatex sets it"
      (Dim.pt 1556 / 100 - Dim.pt 3 / 2 ≤ y - bar && y - bar ≤ Dim.pt 1556 / 100 + Dim.pt 3 / 2)
  | _, _ => t "the bar and the author are set" false

/-- A redefined abstract's skip between a heading set as a bare line and the quotation it opens
moves its body by its length. -/
def abstractGapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre (skip : String) : String :=
    "\\renewenvironment{abstract}{\\centerline{\\large\\bf Abstract}\\vspace{" ++ skip ++
    "}\\begin{quote}}{\\par\\end{quote}}\n"
  let bodyY (skip : String) : Option Length :=
    ((bodyLines (layoutOf fonts (elabStr (dvDoc (pre skip)
      "\\begin{abstract}Invented words.\\end{abstract}")).1)).find?
      (lineText · == "Invented words.")).map (·.y)
  match bodyY "2pt", bodyY "12pt" with
  | some near, some far =>
    t "a declared skip under the heading moves the abstract's body by its length"
      (Dim.pt 10 - Dim.pt 1 / 10 ≤ far - near && far - near ≤ Dim.pt 10 + Dim.pt 1 / 10)
  | _, _ => t "the abstract's body is set" false
  -- lualatex: 33.88 pt from the heading's baseline to the body's, the skip and the quote's opening.
  let c := censusOfSrc fonts (dvDoc (pre "12pt") "\\begin{abstract}Invented words.\\end{abstract}")
  match lineYOf c 0 "Abstract", lineYOf c 0 "Invented words." with
  | some h, some y =>
    t "the abstract's body stands from its heading as lualatex sets it"
      (Dim.pt 3388 / 100 - Dim.pt 3 / 2 ≤ y - h && y - h ≤ Dim.pt 3388 / 100 + Dim.pt 3 / 2)
  | _, _ => t "the heading and the body are set" false

/-- The venue style checks, over one face. -/
def venueStyleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  oldFontCmdChecks ref fonts
  familyDefaultChecks ref
  csnameInkChecks ref fonts
  fancyVerbatimChecks ref fonts
  venueEnvChecks ref fonts
  authorCellFontChecks ref
  venueEdgeChecks ref fonts
  fancyIncludedChecks ref
  anonymousTitleChecks ref fonts
  sizeRedefinitionChecks ref fonts
  authorSeparatorChecks ref fonts
  titleNoticeChecks ref fonts
  italicCorrectionChecks ref fonts
  titleBarSkipChecks ref fonts
  abstractGapChecks ref fonts
