module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The shipped pages of a document as one comparable value. -/
def pagesOf (fonts : Font.FontSet) (src : String) : String :=
  reprStr (layoutOf fonts (elabStr src).1).pages

/-- A body each parameter's site reads. -/
def settingsBodies : List (String × String) :=
  [("paras", "Alpha words here.\n\nBravo words here.\n\nCharlie words here."),
   ("figure", "Alpha words.\n\n\\begin{figure}[h]\\centering\nBravo box.\n" ++
      "\\caption{Charlie caption.}\\end{figure}\n\nDelta words."),
   ("center", "Alpha words.\n\n\\begin{center}\nBravo words.\n\\end{center}\n\nCharlie words."),
   ("note", "Alpha words.\\footnote{Bravo note.}\n\n" ++
      String.join (List.replicate 70 "Filler words for a full page.\n\n")),
   ("table", "Alpha words.\n\n\\begin{tabular}{ll}\\toprule\nAlpha & Bravo\\\\\n\\midrule\n" ++
      "Charlie & Delta\\\\\n\\cmidrule(lr){1-2}\nEcho & Foxtrot\\\\\n" ++
      "\\bottomrule\n\\end{tabular}\n\nBravo words."),
    ("columns", "\\begin{paracol}{2}Alpha words.\\switchcolumn Bravo words.\\end{paracol}"),
    ("rules", "\\begin{tabular}{ll}\\toprule\\toprule\nAlpha & Bravo\\\\\n" ++
      "\\bottomrule\n\\end{tabular}"),
   ("parlist", "Alpha words.\n\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n\n" ++
      "Charlie words."),
   ("list1", "Alpha words.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n" ++
      "\\begin{enumerate}\n\\item Charlie item.\n\\end{enumerate}"),
   ("list2", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\end{itemize}\n\\end{itemize}"),
   ("list3", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}"),
   ("list4", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{itemize}\n\\item Delta\n" ++
      "\\end{itemize}\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}"),
   ("list5", "\\begin{itemize}\n\\item Alpha\n\\begin{enumerate}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{description}\n\\item Delta\n" ++
      "\\begin{quote}\nEcho\n\\end{quote}\n\\end{description}\n\\end{itemize}\n" ++
      "\\end{enumerate}\n\\end{itemize}"),
   ("list6", "\\begin{itemize}\n\\item Alpha\n\\begin{enumerate}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{description}\n\\item Delta\n" ++
      "\\begin{quote}\nEcho\n\\begin{quote}\nFoxtrot\n\\end{quote}\n\\end{quote}\n" ++
      "\\end{description}\n\\end{itemize}\n\\end{enumerate}\n\\end{itemize}"),
   ("display", "Alpha words before.\n\\[ x = y \\]\nBravo words after."),
   ("displaylong", "Alpha words before this display reach past it.\n\\[ x = y \\]\n" ++
      "Bravo words after.")]

/-- One probe per carried `Compat.paramSites` row: the LaTeX spelling, the native spelling of the
same value, and the body that reads it. -/
def paramProbes : List (String × String × String × String) :=
  [("parskip", "\\setlength{\\parskip}{19pt}", "\\page{ parskip = 19pt }", "paras"),
   ("textwidth", "\\setlength{\\textwidth}{4in}", "\\page{ textwidth = 4in }", "paras"),
   ("headsep", "\\runninghead{Alpha head}\\setlength{\\headsep}{40pt}",
     "\\runninghead{Alpha head}\\page{ headsep = 40pt }", "paras"),
   ("footskip", "\\setlength{\\footskip}{50pt}", "\\page{ footskip = 50pt }", "paras"),
   ("floatsep", "\\setlength{\\floatsep}{30pt}", "\\tokens{ floatsep = 30pt }", "figure"),
   ("abovecaptionskip", "\\setlength{\\abovecaptionskip}{23pt}",
     "\\tokens{ captionsep = 23pt }", "figure"),
   ("topsep", "\\setlength{\\topsep}{17pt}", "\\tokens{ topsep = 17pt }", "center"),
   ("partopsep", "\\setlength{\\partopsep}{9pt}", "\\tokens{ partopsep = 9pt }", "parlist"),
   ("footins", "\\setlength{\\skip\\footins}{61pt}", "\\tokens{ footins = 61pt }", "note"),
    ("tabcolsep", "\\setlength{\\tabcolsep}{13pt}", "\\tokens{ tabcolsep = 13pt }", "table"),
    ("columnsep", "\\setlength{\\columnsep}{19pt}", "\\tokens{ columnsep = 19pt }", "columns"),
   ("heavyrulewidth", "\\setlength{\\heavyrulewidth}{3pt}",
     "\\tokens{ heavyrulewidth = 3pt }", "table"),
   ("lightrulewidth", "\\setlength{\\lightrulewidth}{2pt}",
     "\\tokens{ lightrulewidth = 2pt }", "table"),
   ("cmidrulewidth", "\\setlength{\\cmidrulewidth}{2pt}",
     "\\tokens{ cmidrulewidth = 2pt }", "table"),
   ("cmidrulekern", "\\setlength{\\cmidrulekern}{9pt}",
     "\\tokens{ cmidrulekern = 9pt }", "table"),
   ("aboverulesep", "\\setlength{\\aboverulesep}{7pt}", "\\tokens{ aboverulesep = 7pt }", "table"),
   ("belowrulesep", "\\setlength{\\belowrulesep}{7pt}", "\\tokens{ belowrulesep = 7pt }", "table"),
   ("abovetopsep", "\\setlength{\\abovetopsep}{9pt}", "\\tokens{ abovetopsep = 9pt }", "table"),
   ("belowbottomsep", "\\setlength{\\belowbottomsep}{9pt}",
     "\\tokens{ belowbottomsep = 9pt }", "table"),
   ("doublerulesep", "\\setlength{\\doublerulesep}{8pt}",
     "\\tokens{ doublerulesep = 8pt }", "rules"),
   ("leftmargini", "\\setlength{\\leftmargini}{61pt}", "\\tokens{ leftmargini = 61pt }", "list1"),
   ("leftmarginii", "\\setlength{\\leftmarginii}{47pt}", "\\tokens{ leftmarginii = 47pt }", "list2"),
   ("leftmarginiii", "\\setlength{\\leftmarginiii}{43pt}", "\\tokens{ leftmarginiii = 43pt }",
     "list3"),
   ("leftmarginiv", "\\setlength{\\leftmarginiv}{41pt}", "\\tokens{ leftmarginiv = 41pt }", "list4"),
   ("leftmarginv", "\\setlength{\\leftmarginv}{37pt}", "\\tokens{ leftmarginv = 37pt }", "list5"),
   ("leftmarginvi", "\\setlength{\\leftmarginvi}{31pt}", "\\tokens{ leftmarginvi = 31pt }",
     "list6")]

/-- Does a row's site carry the value onto the page: a page key, a token, or a list level the engine
nests to? -/
def carried : Compat.ParamSite → Bool
  | .page _ | .token _ => true
  | .listIndent _ => true
  | .sizeReset _ | .listReset | .unmodelled _ => false

/-- A LaTeX length setting lands where LaTeX's own code puts it, for every `Compat.paramSites` row,
on the shipped page. -/
def paramSiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\usepackage{booktabs}\n" ++ pre ++
      "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let bodyOf (k : String) : String := (settingsBodies.lookup k).getD ""
  for (n, site) in Compat.paramSites do
    if carried site then
      t s!"paramSites: the carried row '{n}' has a probe"
        (paramProbes.any (·.1 == n))
  for (n, _) in paramProbes do
    t s!"paramSites: the probe '{n}' names a carried row"
      (((Compat.paramSites.lookup n).map carried).getD false)
  for (n, latex, native, bodyKey) in paramProbes do
    let body := bodyOf bodyKey
    let set := pagesOf oneFace (doc latex body)
    t s!"'{n}': the LaTeX setting sets the page its native spelling sets"
      (set == pagesOf oneFace (doc native body))
    t s!"'{n}': the setting moves the page" (set != pagesOf oneFace (doc "" body))
  -- What LaTeX sets again before anything reads it sets nothing here either.
  let reset := [("abovedisplayskip", "displaylong"), ("belowdisplayskip", "displaylong"),
    ("abovedisplayshortskip", "display"), ("belowdisplayshortskip", "display"),
    ("baselineskip", "paras"), ("itemsep", "list1"), ("parsep", "list1"),
    ("leftmargin", "list1"), ("itemindent", "list1")]
  for (n, bodyKey) in reset do
    let src := doc s!"\\setlength\{\\{n}}\{31pt}" (bodyOf bodyKey)
    t s!"'{n}' in the preamble sets the page the document sets without it"
      (pagesOf oneFace src == pagesOf oneFace (doc "" (bodyOf bodyKey)))
    t s!"'{n}' in the preamble says what LaTeX does with it"
      ((dvE src).any fun d => d.code == "N0100" &&
        d.subject == some s!"ctrl:nothing:setlength:{n}")
  -- In the body a display skip stands until the next size change: its token.
  -- A line ending short of the formula spends the short skips, a longer one the others.
  for (n, bodyKey) in [("abovedisplayskip", "displaylong"), ("belowdisplayskip", "displaylong"),
      ("abovedisplayshortskip", "display"), ("belowdisplayshortskip", "display")] do
    let body := bodyOf bodyKey
    let set := pagesOf oneFace (doc "" (s!"\\setlength\{\\{n}}\{31pt}\n\n" ++ body))
    t s!"a body '\\{n}' sets the page its token sets"
      (set == pagesOf oneFace (doc "" (s!"\\tokens\{ {n} = 31pt }\n\n" ++ body)))
    t s!"a body '\\{n}' moves the display it reaches" (set != pagesOf oneFace (doc "" body))
  for (n, site) in Compat.paramSites do
    if let .unmodelled _ := site then
      let ds := dvE (doc s!"\\setlength\{\\{n}}\{7pt}" "Alpha words.")
      t s!"'{n}' is named where it is set"
        ((ds.filter fun d => d.code == "W0104" &&
          d.subject == some s!"ctrl:setlength:{n}").size == 1)
  let every := String.intercalate "\n\n" (settingsBodies.map (·.2))
  for (n, site) in Compat.paramSites do
    if let .unmodelled _ := site then
      t s!"'{n}' named as unread sets nothing on the page"
        (pagesOf oneFace (doc s!"\\setlength\{\\{n}}\{7pt}" every) ==
          pagesOf oneFace (doc "" every))
  -- A zero indent is what the engine does: honoured, said so, never named.
  let flush := dvE (doc "\\setlength{\\parindent}{0pt}" "Alpha words.")
  t "a zero '\\parindent' is honoured, not named"
    (!flush.any (·.code == "W0104") &&
      flush.any (·.subject == some "ctrl:nothing:setlength:parindent"))


/-- A parameter set in a loaded style file ships the page its document spelling ships; only the
diagnostic's severity moves. -/
def paramDemoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let sub (file src : String) : Array Parse.Raw := (Parse.parse file (Lex.lex file src).1).1
  let setting := "\\setlength{\\footnotesep}{7pt}\n"
  let head := sub "main.tex" "\\documentclass{article}\n"
  let tail := sub "main.tex" "\\begin{document}\nAlpha words.\\footnote{Bravo note.}\n\\end{document}"
  let (dSty, dsSty) := Elab.runRaws "main.tex"
    (head ++ #[Parse.Raw.env (Parse.inputEnv "venue.sty") (sub "venue.sty" setting)
      { line := 2, col := 1 }] ++ tail)
  let (dOwn, dsOwn) := Elab.runRaws "main.tex" (head ++ sub "main.tex" setting ++ tail)
  let named (ds : Array Diag) := ds.filter (·.subject == some "ctrl:setlength:footnotesep")
  t "a style file's parameter ships the page the document's does"
    (reprStr (layoutOf oneFace dSty).pages == reprStr (layoutOf oneFace dOwn).pages)
  t "a style file's parameter is a note, the document's a warning"
    ((named dsSty).map (·.severity) == #[.note] && (named dsOwn).map (·.severity) == #[.warning])


/-- A redefined `\normalsize` sets the document's display skips, and a size command in the preamble
sets nothing. -/
def sizeCommandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let body := "Alpha words before the display, long enough to fill a line of text here.\n" ++
    "\\[ x = y \\]\nBravo words after the display."
  let redef (skips : String) : String :=
    "\\makeatletter\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt\n" ++
      skips ++ "}\\makeatother"
  let skips := "\\abovedisplayskip 3\\p@ \\@plus 2\\p@ \\@minus 1\\p@\n" ++
    "\\abovedisplayshortskip \\z@ \\@plus 3\\p@\n\\belowdisplayskip \\abovedisplayskip\n"
  let native := "\\page{ fontsize = 10pt, leading = 0.913 }" ++
    "\\tokens{ abovedisplayskip = 3pt plus 2pt minus 1pt, belowdisplayskip = abovedisplayskip }"
  let set := pagesOf oneFace (doc (redef skips) body)
  t "a redefined \\normalsize ships as its native size and skips do"
    (set == pagesOf oneFace (doc native body))
  t "a redefined \\normalsize's display skips move the page"
    (set != pagesOf oneFace (doc (redef "") body))
  for name in ["normalsize", "small"] do
    let src := doc s!"\\{name}" body
    t s!"a preamble '\\{name}' sets the page the document sets without it"
      (pagesOf oneFace src == pagesOf oneFace (doc "" body))
    t s!"a preamble '\\{name}' says what LaTeX does with it, and is not unknown"
      ((dvE src).any (·.subject == some s!"ctrl:nothing:size:{name}") &&
        !(dvE src).any (·.code == "W0301"))
  -- A copy of a class skip is unknown here: named once, the skip keeping its value.
  let copy := doc (redef "\\belowdisplayskip\\abovedisplayskip\n") body
  let cds := dvE copy
  t "a redefined \\normalsize copying a skip it does not set builds"
    (!cds.any (·.severity == .error))
  t "a \\normalsize copying a skip it does not set names the copy once"
    ((cds.filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:belowdisplayskip"])
  t "a \\normalsize copying a skip it does not set ships the page without it"
    (pagesOf oneFace copy == pagesOf oneFace (doc (redef "") body))


/-- A counter set in the preamble holds where the body starts, and `secnumdepth` decides which
headings number. -/
def counterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let heads := "\\section{Alpha}\nOne.\n\n\\subsection{Bravo}\nTwo."
  let shallow := pagesOf oneFace (doc "\\setcounter{secnumdepth}{1}" heads)
  t "secnumdepth 1 sets a subsection the page a starred one sets"
    (shallow == pagesOf oneFace (doc "" "\\section{Alpha}\nOne.\n\n\\subsection*{Bravo}\nTwo."))
  t "secnumdepth moves the page" (shallow != pagesOf oneFace (doc "" heads))
  let deeper := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{1}"
    (heads ++ "\n\n\\setcounter{secnumdepth}{2}\n\\subsection{Charlie}\nThree."))
  t "a heading above secnumdepth steps nothing: the next numbered one is 1.1"
    (pageHas deeper 0 "1.1" && !pageHas deeper 0 "1.2")
  let note := "Alpha words.\\footnote{Bravo note.}"
  t "a preamble footnote counter numbers the next note after it"
    (pagesOf oneFace (doc "\\setcounter{footnote}{4}" note) ==
      pagesOf oneFace (doc "" "Alpha words.\\footnote[5]{Bravo note.}"))
  let eq := censusOfSrc oneFace (doc "\\addtocounter{equation}{6}"
    "Alpha.\n\\begin{equation}\nx = y\n\\end{equation}")
  t "a preamble equation counter numbers the next equation after it" (pageHas eq 0 "(7)")
  -- A counter set in the body is left where it stands, so numbers only what follows it.
  t "a body counter numbers from where it stands, a preamble one from the body's start"
    (!pageHas (censusOfSrc oneFace (doc "" "\\section{Alpha}\nOne.\n\n\\setcounter{section}{4}\n\
\\section{Bravo}\nTwo.")) 0 "6" &&
      pageHas (censusOfSrc oneFace (doc "\\setcounter{section}{4}" "\\section{Alpha}\nOne.\n\n\
\\section{Bravo}\nTwo.")) 0 "6")
  t "a preamble counter command is not unknown"
    (!(dvE (doc "\\setcounter{secnumdepth}{1}\\stepcounter{footnote}" heads)).any
      (·.code == "W0301"))
  t "an unkept preamble counter is named as in the body"
    ((dvE (doc "\\setcounter{tocdepth}{2}" heads)).any fun d =>
      d.code == "W0104" && d.subject == some "ctrl:setcounter:tocdepth")
  -- Kernel constant registers read as their integers (plain.tex); any other register is named once.
  let zero := doc "\\makeatletter\\setcounter{secnumdepth}{\\z@}\\makeatother" heads
  t "a counter set to '\\z@' builds and reads zero"
    (!(dvE zero).any (·.severity == .error) &&
      pagesOf oneFace zero == pagesOf oneFace (doc "\\setcounter{secnumdepth}{0}" heads))
  t "a counter set to '\\z@' moves the page" (pagesOf oneFace zero != pagesOf oneFace (doc "" heads))
  let reg := doc "\\makeatletter\\setcounter{secnumdepth}{\\@tempcnta}\\makeatother" heads
  t "a counter set to an unreadable register builds, named once"
    (!(dvE reg).any (·.severity == .error) &&
      ((dvE reg).filter (·.code == "W0104")).map (·.subject) ==
        #[some "ctrl:setcounter:secnumdepth:value"])
  t "a counter set to a register it cannot read keeps its value"
    (pagesOf oneFace reg == pagesOf oneFace (doc "" heads))
  -- `secnumdepth` past three numbers the run-in levels (`\paragraph` four, `\subparagraph` five), each after its parent.
  let runIn := "\\section{Alpha}\\subsection{Bravo}\\subsubsection{Charlie}\n" ++
    "\\paragraph{Delta} Echo words.\n\n\\subparagraph{Foxtrot} Golf words."
  let four := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{4}" runIn)
  t "secnumdepth 4 numbers a paragraph after its parent" (pageHas four 0 "1.1.1.1")
  t "secnumdepth 4 leaves a subparagraph unnumbered" (!pageHas four 0 "1.1.1.1.1")
  let five := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{5}" runIn)
  t "secnumdepth 5 numbers a subparagraph after its parent" (pageHas five 0 "1.1.1.1.1")
  t "the class's secnumdepth numbers no paragraph"
    (!pageHas (censusOfSrc oneFace (doc "" runIn)) 0 "1.1.1.1")


/-- A list level's parameters are its class macro's, run where a list of that depth opens. -/
def listLevelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\makeatletter\n" ++ pre ++
      "\n\\makeatother\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let body := "Alpha words.\n\n\\begin{itemize}\n\\item One.\n\\item Two.\n" ++
    "\\begin{itemize}\n\\item Three.\n\\item Four.\n\\end{itemize}\n\\item Five.\n" ++
    "\\end{itemize}\n\nBravo words."
  let keep := "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xiipt}\n"
  let params := "\\setlength{\\topsep}{9pt plus 1pt minus 2pt}\n" ++
    "\\setlength{\\itemsep}{3pt plus 1pt}\n\\setlength{\\parsep}{2pt plus 1pt}\n" ++
    "\\setlength{\\leftmargin}{40pt}\n\\setlength{\\leftmargini}{\\leftmargin}\n"
  let listi := "\\def\\@listi{\\leftmargin\\leftmargini}\n"
  let outer := "\\tokens{ leftmargini = 40pt }\\style{itemize}{ before = 9pt plus 1pt minus 2pt, " ++
    "gap = 5pt plus 2pt }\\style{enumerate}{ before = 9pt plus 1pt minus 2pt, gap = 5pt plus 2pt }"
  let kept := pagesOf oneFace (doc (keep ++ params ++ listi) body)
  t "a kept \\@listi sets the outermost lists the page their native styles set"
    (kept == pagesOf oneFace (doc ("\\page{ fontsize = 10pt, leading = 1 }" ++ outer) body))
  t "a kept \\@listi moves the page" (kept != pagesOf oneFace (doc (keep ++ params) body))
  t "a class's \\normalsize resets \\@listi: the redefinition sets nothing"
    (pagesOf oneFace (doc (params ++ listi) body) == pagesOf oneFace (doc params body))
  let listii := "\\setlength{\\leftmarginii}{30pt}\n\\def\\@listii{\\leftmargin\\leftmarginii\n" ++
    "\\labelwidth\\leftmarginii \\advance\\labelwidth-\\labelsep\n" ++
    "\\topsep 4\\p@ \\@plus 1\\p@ \\parsep 1.5\\p@ \\itemsep \\parsep}\n"
  let inner := "\\tokens{ leftmarginii = 30pt }" ++
    "\\style{itemize2}{ before = 4pt plus 1pt, gap = 3pt }" ++
    "\\style{enumerate2}{ before = 4pt plus 1pt, gap = 3pt }"
  let second := pagesOf oneFace (doc listii body)
  t "a redefined \\@listii sets the second level the page its native style sets"
    (second == pagesOf oneFace (doc inner body))
  t "a redefined \\@listii moves the page"
    (second != pagesOf oneFace (doc "\\setlength{\\leftmarginii}{30pt}" body))
  let ds := dvE (doc listii body)
  t "a list level's arithmetic is read with it; unread settings are named once"
    (!ds.any (·.subject == some "ctrl:advance") &&
      (ds.filter (·.subject == some "ctrl:setlength:labelwidth")).size == 1)
  -- A body assignment between two lists reaches the second only where the level's macro leaves it be.
  let between (set : String) : String :=
    "Alpha words.\n\\begin{itemize}\n\\item One.\n\\item Two.\n\\end{itemize}\n" ++ set ++
      "\nBravo words.\n\\begin{itemize}\n\\item Three.\n\\item Four.\n\\end{itemize}\nCharlie."
  for (set, names) in [("\\setlength{\\topsep}{9pt}", #["topsep"]),
      ("\\setlength{\\itemsep}{0pt}\\setlength{\\parsep}{0pt}", #["itemsep", "parsep"])] do
    let kds := dvE (doc (keep ++ listi) (between set))
    t s!"a kept \\@listi and a body '{set}' build" (!kds.any (·.severity == .error))
    t s!"a kept \\@listi and a body '{set}' name the lists they cannot reach, once each"
      ((kds.filter (·.code == "W0104")).map (·.subject) ==
        names.map fun n => some s!"ctrl:setlength:{n}")
    t s!"the naming gate's premise: no list here reads a body '{set}' under a kept \\@listi"
      (pagesOf oneFace (doc (keep ++ listi) (between set)) ==
        pagesOf oneFace (doc (keep ++ listi) (between "")))
  let cls := doc listi (between "\\setlength{\\itemsep}{0pt}")
  t "under the class's \\@listi a body \\itemsep reaches no list, and says so"
    (!(dvE cls).any (·.code == "W0104") &&
      (dvE cls).any (·.subject == some "ctrl:nothing:setlength:itemsep") &&
      pagesOf oneFace cls == pagesOf oneFace (doc listi (between "")))



/-- Every LaTeX-valid length setting builds: one the door reads holds its value, one it cannot read
is named once and changes nothing. -/
def unreadableLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\usepackage{calc}\n" ++ pre ++ "\n\\begin{document}\n" ++
      body ++ "\n\\end{document}"
  let body := "Alpha words here.\n\nBravo words here.\n\\begin{itemize}\n" ++
    "\\item Charlie item.\n\\item Delta item.\n\\end{itemize}\nEcho words.\n" ++
    "\\begin{tabular}{ll}\nFoxtrot & Golf\n\\end{tabular}"
  let bare := pagesOf oneFace (doc "" body)
  let fine (ds : Array Diag) : Bool :=
    !ds.any fun d => d.severity == .error || d.code == "W0104" || d.code == "W0107" ||
      d.code == "W0301"
  let read : List (String × String) :=
    [("\\newlength{\\probegap}\\setlength{\\probegap}{7pt}\\setlength{\\parskip}{-\\probegap}",
       "\\setlength{\\parskip}{-7pt}"),
     ("\\setlength{\\parskip}{\\medskipamount}",
       "\\setlength{\\parskip}{6pt plus 2pt minus 2pt}"),
     ("\\setlength{\\medskipamount}{20pt}\\setlength{\\parskip}{\\medskipamount}",
       "\\setlength{\\medskipamount}{20pt}\\setlength{\\parskip}{20pt}"),
     ("\\setlength{\\bigskipamount}{3pt}\\setlength{\\parskip}{2\\bigskipamount}",
       "\\setlength{\\bigskipamount}{3pt}\\setlength{\\parskip}{6pt}"),
     ("\\setlength{\\leftmargini}{\\dimexpr 1em+2pt\\relax}",
       "\\setlength{\\leftmargini}{1em + 2pt}"),
     ("\\parskip 6pt plus 1pt", "\\setlength{\\parskip}{6pt plus 1pt}"),
     ("\\parskip=5pt", "\\setlength{\\parskip}{5pt}"),
     ("\\setlength{\\parskip}{7pt}\\setlength{\\topsep}{\\parskip}",
       "\\setlength{\\parskip}{7pt}\\setlength{\\topsep}{7pt}"),
     ("\\makeatletter\\setlength{\\parskip}{\\z@}\\makeatother", "\\setlength{\\parskip}{0pt}"),
     ("\\makeatletter\\newlength{\\@probegap}\\setlength{\\@probegap}{7pt}" ++
        "\\setlength{\\parskip}{\\@probegap}\\makeatother", "\\setlength{\\parskip}{7pt}")]
  for (spelled, literal) in read do
    let src := doc spelled body
    let set := pagesOf oneFace src
    t s!"'{spelled}' sets the page '{literal}' sets"
      (set == pagesOf oneFace (doc literal body))
    t s!"'{spelled}' moves the page" (set != bare)
    t s!"'{spelled}' builds, and names no loss" (fine (dvE src))
  let unread : List (String × String) :=
    [("parskip", "\\setlength{\\parskip}{0pt plus 1fil}"),
     ("parskip", "\\setlength{\\parskip}{0.5\\baselineskip}"),
     ("parskip", "\\setlength{\\parskip}{\\stretch{1}}"),
     ("labelwidth", "\\setlength{\\labelwidth}{0.5\\leftmargini}"),
     ("arraycolsep", "\\setlength{\\arraycolsep}{0.5\\tabcolsep}"),
     ("probegap", "\\newlength{\\probegap}\\setlength{\\probegap}{\\widthof{Alpha}}"),
     ("parskip", "\\addtolength{\\parskip}{2pt}"),
     ("tabcolsep", "\\tabcolsep=\\baselineskip")]
  for (n, pre) in unread do
    let src := doc pre body
    let ds := dvE src
    t s!"'{pre}' builds" (!ds.any (·.severity == .error))
    t s!"'{pre}' is named once, on its parameter"
      ((ds.filter fun d => d.code == "W0107").map (·.subject) ==
        #[some s!"length:{n}"])
    t s!"'{pre}' ships the page the document ships without it" (pagesOf oneFace src == bare)
  -- A definition's body runs where the command is used, so nothing in it is judged where it is defined.
  for pre in ["\\newcommand{\\probesize}{\\setlength{\\belowdisplayskip}{\\abovedisplayskip}}",
      "\\newcommand{\\probesize}{\\belowdisplayskip\\abovedisplayskip}",
      "\\newcommand{\\probesize}{\\addtolength{\\parskip}{2pt}}"] do
    let src := doc pre body
    t s!"'{pre}' names nothing where it is defined" (fine (dvE src))
    t s!"'{pre}' ships the page the document ships without it" (pagesOf oneFace src == bare)
  let listBody (lead : String) : String :=
    "Alpha words.\n\\begin{itemize}" ++ lead ++ "\\item One.\\item Two.\\end{itemize}\nBravo words."
  let idiom := doc "" (listBody "\\setlength{\\itemsep}{0pt}")
  let ids := dvE idiom
  t "a length set before a list's first item builds" (!ids.any (·.severity == .error))
  t "a length before a list's first item is named once, spacing that list only"
    ((ids.filter (·.code == "W0104")).map (·.subject) == #[some "ctrl:setlength:itemsep"])
  t "a length set before a list's first item keeps the list's level spacing"
    (pagesOf oneFace idiom == pagesOf oneFace (doc "" (listBody "")))
  let enumBody (lead : String) : String :=
    "\\begin{enumerate}" ++ lead ++ "\\item Four.\\item Five.\\end{enumerate}"
  let start := dvE (doc "" (enumBody "\\setcounter{enumi}{3}"))
  t "a counter set before a list's first item builds, named once"
    (!start.any (·.severity == .error) &&
      (start.filter (·.code == "W0104")).map (·.subject) == #[some "ctrl:setcounter:enumi"])
  let heads (set : String) : String :=
    "\\section{Alpha}\nOne.\n\\subsection{Bravo}\nTwo.\n\\subsection{Charlie}\nThree.\n" ++
      set ++ "\n\\section{Delta}\nFour."
  let valued := doc "" (heads "\\setcounter{section}{\\value{subsection}}")
  t "a counter set to another's value reads it where it stands"
    (pagesOf oneFace valued == pagesOf oneFace (doc "" (heads "\\setcounter{section}{2}")))
  t "a counter set to another's value builds" (!(dvE valued).any (·.severity == .error))


/-- An assignment is the value later arithmetic reads only where TeX makes it: not in a definition's
body, not past its group. -/
def registerScopeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let doc (pre set : String) : String :=
    "\\documentclass{article}\n\\newlength{\\probegap}\\setlength{\\probegap}{10pt}\n" ++ pre ++
      "\n\\begin{document}\n" ++ set ++ "\nAlpha words.\n\n\\vspace{\\probegap}\n\n" ++
      "Bravo words.\n\\end{document}"
  let eleven := pagesOf oneFace (doc "" "\\setlength{\\probegap}{11pt}")
  let rows : List (String × String × String) :=
    [("an unused definition's arithmetic",
       "\\newcommand{\\probebump}{\\addtolength{\\probegap}{30pt}}",
       "\\addtolength{\\probegap}{1pt}"),
     ("an unused definition's assignment",
       "\\newcommand{\\probeset}{\\setlength{\\probegap}{50pt}}",
       "\\addtolength{\\probegap}{1pt}"),
     ("a group's assignment", "",
       "{\\setlength{\\probegap}{30pt}}\\addtolength{\\probegap}{1pt}"),
     ("an environment's assignment", "",
       "\\begin{minipage}{5cm}\\setlength{\\probegap}{30pt}\\end{minipage}" ++
         "\\addtolength{\\probegap}{1pt}")]
  for (what, pre, set) in rows do
    t s!"{what} is not the value arithmetic after it reads"
      (pagesOf oneFace (doc pre set) ==
        pagesOf oneFace (doc pre ((set.splitOn "\\addtolength").headD "" ++
          "\\setlength{\\probegap}{11pt}")))
  t "the scope rows measure the value: 11pt is not the 10pt the document starts from"
    (eleven != pagesOf oneFace (doc "" ""))


/-- A parameter a command reads as its operand is not assigned. -/
def operandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre : String) : String :=
    "\\documentclass{article}\n\\setlength{\\parskip}{12pt}\n" ++ pre ++
      "\n\\begin{document}\n" ++ ((settingsBodies.lookup "paras").getD "") ++ "\n\\end{document}"
  let plain := pagesOf oneFace (doc "")
  for pre in ["\\ifdim\\parskip=0pt\\relax\\fi",
      "\\makeatletter\\ifdim\\parskip=\\z@\\relax\\fi\\makeatother",
      "\\ifdim 2\\parskip=0pt\\relax\\fi"] do
    t s!"'{pre}' reads the parameter and assigns nothing" (pagesOf oneFace (doc pre) == plain)
  t "the operand rows measure the parameter: 12pt is not the 0pt they compare with"
    (plain != pagesOf oneFace (doc "\\setlength{\\parskip}{0pt}"))



/-- A list parameter set in a list's body is that list's, as `\list` reads it. -/
def listBodyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre lead : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nAlpha words.\n" ++
      "\\begin{itemize}" ++ lead ++ "\\item One.\\item Two.\\end{itemize}\nBravo words.\n" ++
      "\\end{document}"
  let bare := pagesOf oneFace (doc "" "")
  let fails (ds : Array Diag) : Bool := ds.any (·.severity == .error)
  for n in Compat.listSpent do
    let src := doc "" s!"\\setlength\{\\{n}}\{7pt}"
    let ds := dvE src
    t s!"'\\{n}' in a list's body builds, said in a note alone"
      (!fails ds && !ds.any (·.code == "W0104") &&
        ds.any (·.subject == some s!"ctrl:nothing:setlength:{n}"))
    t s!"'\\{n}' in a list's body ships the page the list ships without it"
      (pagesOf oneFace src == bare)
  for n in Compat.listPerItem do
    let src := doc "" s!"\\setlength\{\\{n}}\{7pt}"
    let ds := dvE src
    t s!"'\\{n}' in a list's body builds, named once"
      (!fails ds && (ds.filter (·.code == "W0104")).map (·.subject) ==
        #[some s!"ctrl:setlength:{n}"])
    t s!"the naming gate's premise: no list here reads '\\{n}' set in its body"
      (pagesOf oneFace src == bare)
  let tight := doc "\\providecommand{\\tightlist}{\\setlength{\\itemsep}{0pt}\\setlength{\\parskip}{0pt}}"
    "\\tightlist"
  let tds := dvE tight
  t "pandoc's \\tightlist in a list builds" (!fails tds)
  t "pandoc's \\tightlist names its two settings once each"
    ((tds.filter (·.code == "W0104")).map (·.subject) ==
      #[some "ctrl:setlength:itemsep", some "ctrl:setlength:parskip"])



/-- The lengths LaTeX's kernel and standard classes declare for a document to set, each decided in
`Compat.paramSites`, read by the door, handled by its own arm, or owed. -/
def kernelLengthNames : List String :=
  ["paperwidth", "paperheight", "textwidth", "textheight", "oddsidemargin", "evensidemargin",
   "topmargin", "headheight", "headsep", "footskip", "marginparwidth", "marginparsep",
   "marginparpush", "columnsep", "columnseprule", "columnwidth", "linewidth", "topskip",
   "footnotesep", "footins", "floatsep", "textfloatsep", "intextsep", "dblfloatsep",
   "dbltextfloatsep", "abovecaptionskip", "belowcaptionskip", "parindent", "parskip",
   "baselineskip", "lineskip", "lineskiplimit", "parfillskip", "leftmargin", "leftmargini",
   "leftmarginii", "leftmarginiii", "leftmarginiv", "leftmarginv", "leftmarginvi",
   "rightmargin", "labelwidth", "labelsep", "itemindent", "listparindent", "itemsep", "parsep",
   "topsep", "partopsep", "abovedisplayskip", "belowdisplayskip", "abovedisplayshortskip",
   "belowdisplayshortskip", "jot", "mathindent", "arraycolsep", "tabcolsep", "arrayrulewidth",
   "doublerulesep", "fboxsep", "fboxrule", "unitlength", "smallskipamount", "medskipamount",
   "bigskipamount"]

/-- The kernel lengths no row decides yet, held in both directions. -/
def openKernelLengths : List String :=
  ["paperwidth", "paperheight", "oddsidemargin", "evensidemargin", "topmargin",
   "headheight", "marginparwidth", "marginparsep", "marginparpush", "columnseprule",
   "columnwidth", "linewidth", "topskip", "textfloatsep", "intextsep", "dblfloatsep",
   "dbltextfloatsep", "lineskip", "lineskiplimit", "parfillskip", "mathindent"]

/-- A kernel length is decided where it is set, and read where it is a value. -/
def kernelLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let decided (n : String) : Bool :=
    (Compat.paramSites.lookup n).isSome || (Compat.kernelSkip n).isSome ||
      n == "belowcaptionskip"
  t "every kernel length is decided, or owed by name"
    (kernelLengthNames.filter (!decided ·) == openKernelLengths)
  let doc (cls pre body : String) : String :=
    "\\documentclass{" ++ cls ++ "}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let list := "Alpha words.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}"
  let fails (ds : Array Diag) : Bool := ds.any (·.severity == .error)
  let line := doc "article" "\\setlength{\\leftmargini}{0.1\\linewidth}" list
  t "a measure the page settles later builds, named once on its value"
    (!fails (dvE line) && ((dvE line).filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:leftmargini"])
  t "a measure the page settles later ships the page without the setting"
    (pagesOf oneFace line == pagesOf oneFace (doc "article" "" list))
  let par := doc "article" "\\setlength{\\parindent}{0.05\\textwidth}" list
  t "a paragraph indent of the unsettled measure builds, named once"
    (!fails (dvE par) && ((dvE par).filter (·.code == "W0107")).size == 1)
  let margin := "\\usepackage[margin=2cm]{geometry}"
  let geo := doc "article" (margin ++ "\\setlength{\\leftmargini}{0.1\\linewidth}") list
  t "a flow page's '\\linewidth' is the class's, not the engine's: named once on its value"
    (!fails (dvE geo) && ((dvE geo).filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:leftmargini"])
  let frame (pre : String) : String :=
    doc "beamer" pre ("\\begin{frame}{Alpha}\n" ++ list ++ "\n\\end{frame}")
  let fixed := frame "\\setlength{\\leftmargini}{0.1\\linewidth}"
  t "a class that fixes its text block reads '\\linewidth' as its '\\textwidth'"
    (!fails (dvE fixed) && !(dvE fixed).any (·.code == "W0107") &&
      pagesOf oneFace fixed == pagesOf oneFace (frame "\\setlength{\\leftmargini}{0.1\\textwidth}"))
  t "a class that fixes its text block: '\\linewidth' moves the page"
    (pagesOf oneFace fixed != pagesOf oneFace (frame ""))
  t "the gate's premise: only a declared flow page offers 'textwidth'"
    (fails (dvE (doc "article" "\\tokens{ probe = 0.1 * textwidth }" list)) &&
      !fails (dvE (doc "article" "\\page{ hmargin = 2cm }\\tokens{ probe = 0.1 * textwidth }" list)))
  let body := doc "article" "" ("\\newlength{\\probew}\\setlength{\\probew}{0.1\\linewidth}\n" ++ list)
  t "a body '\\linewidth', its scope's width, builds, named once on its value"
    (!fails (dvE body) && ((dvE body).filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:probew"])
  let head (pre : String) : String :=
    doc "article" ("\\runninghead{Alpha head}" ++ pre) "Alpha words.\n\nBravo words."
  t "'\\headsep' moves a running head's page"
    (pagesOf oneFace (head "\\setlength{\\headsep}{40pt}") != pagesOf oneFace (head ""))
  let skip (pre body : String) : String := doc "article" pre ("Alpha words.\n\n" ++ body ++ "\nBravo words.")
  let medium := pagesOf oneFace (skip "\\setlength{\\medskipamount}{20pt}" "\\medskip")
  t "'\\medskip' skips the amount the document set"
    (medium == pagesOf oneFace (skip "" "\\block[before = 20pt]{}"))
  t "'\\medskip' of a set amount moves the page" (medium != pagesOf oneFace (skip "" "\\medskip"))
  let late := doc "article" "" ("\\setlength{\\textwidth}{4in}\n" ++ list)
  t "a body '\\textwidth' moves no line and says so in a note"
    (pagesOf oneFace late == pagesOf oneFace (doc "article" "" list) &&
      !(dvE late).any (fun d => d.code == "W0340" || d.code == "W0104") &&
      (dvE late).any (·.subject == some "ctrl:nothing:setlength:textwidth"))
