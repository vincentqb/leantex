import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The shipped pages of a document, as one comparable value: two documents
set the same artifact exactly when these agree. -/
def pagesOf (fonts : Font.FontSet) (src : String) : String :=
  reprStr (layoutOf fonts (elabStr src).1).pages

/-- A body each parameter's site reads, invented text throughout. -/
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
   ("display", "Alpha words before.\n\\[ x = y \\]\nBravo words after.")]

/-- One probe per `Compat.paramSites` row an engine site carries: the
LaTeX spelling, the native spelling of the same value, and the body that
reads it. -/
def paramProbes : List (String × String × String × String) :=
  [("parskip", "\\setlength{\\parskip}{19pt}", "\\page{ parskip = 19pt }", "paras"),
   ("abovecaptionskip", "\\setlength{\\abovecaptionskip}{23pt}",
     "\\tokens{ captionsep = 23pt }", "figure"),
   ("topsep", "\\setlength{\\topsep}{17pt}", "\\tokens{ topsep = 17pt }", "center"),
   ("partopsep", "\\setlength{\\partopsep}{9pt}", "\\tokens{ partopsep = 9pt }", "parlist"),
   ("footins", "\\setlength{\\skip\\footins}{61pt}", "\\tokens{ footins = 61pt }", "note"),
   ("tabcolsep", "\\setlength{\\tabcolsep}{13pt}", "\\tokens{ tabcolsep = 13pt }", "table"),
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
   ("leftmargini", "\\setlength{\\leftmargini}{61pt}",
     "\\style{itemize}{ indent = 61pt }\\style{enumerate}{ indent = 61pt }", "list1"),
   ("leftmarginii", "\\setlength{\\leftmarginii}{47pt}",
     "\\style{itemize2}{ indent = 47pt }\\style{enumerate2}{ indent = 47pt }", "list2"),
   ("leftmarginiii", "\\setlength{\\leftmarginiii}{43pt}",
     "\\style{itemize3}{ indent = 43pt }\\style{enumerate3}{ indent = 43pt }", "list3"),
   ("leftmarginiv", "\\setlength{\\leftmarginiv}{41pt}",
     "\\style{itemize4}{ indent = 41pt }\\style{enumerate4}{ indent = 41pt }", "list4")]

/-- Does a row's site carry the value onto the page? The rows every probe
must cover: a page key, a token, a list level the engine nests to. -/
def carried : Compat.ParamSite → Bool
  | .page _ | .token _ => true
  | .listIndent l => l ≤ 4
  | .sizeReset _ | .listReset | .unmodelled _ => false

/-- **A LaTeX length setting lands where LaTeX's own code puts it.**
`Compat.paramSites` gives each kernel and booktabs length its site, and
every claim is checked on the shipped page (`Layout.Out`), quantified over
the table:

- a row that claims an engine site is carried: the setting sets exactly the
  page its native spelling sets, and a different page from the same
  document without it — so a row naming a token nobody reads fails here,
  the shape that left `\leftmargini` and `\skip\footins` declared and
  unread;
- a row LaTeX itself overrides before anything reads it — `\normalsize` at
  `\begin{document}`, `\@listi` at every list — sets the page the document
  sets without it, and says so in a note;
- a row no engine site reads is named where it stands (W0104, keyed by the
  parameter) and sets nothing.

The table and the probes close in both directions: a carried row without
a probe fails, and so does a probe naming no carried row. -/
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
  let reset := [("abovedisplayskip", "display"), ("belowdisplayskip", "display"),
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
  let disp := "Alpha words before.\n\\[ x = y \\]\nBravo words after."
  t "a body '\\abovedisplayskip' sets the page its token sets"
    (pagesOf oneFace (doc "" ("\\setlength{\\abovedisplayskip}{31pt}\n\n" ++ disp)) ==
      pagesOf oneFace (doc "" ("\\tokens{ abovedisplayskip = 31pt }\n\n" ++ disp)))
  -- Every row no site reads is named where it stands, once per parameter.
  for (n, site) in Compat.paramSites do
    if let .unmodelled _ := site then
      let ds := dvE (doc s!"\\setlength\{\\{n}}\{7pt}" "Alpha words.")
      t s!"'{n}' is named where it is set"
        ((ds.filter fun d => d.code == "W0104" &&
          d.subject == some s!"ctrl:setlength:{n}").size == 1)
  -- And sets nothing, which is what the warning says: over a body every
  -- probe reads, the page is the document's without it. A row the engine
  -- does read fails here, the shape that named `\partopsep` "not honoured"
  -- while `Ir.partopsepFor` spent it.
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


/-- **A parameter set in a style file the document loads is the style's
business**, the premise `Compat.setLength` demotes on: the page is the one
the same setting ships from the document's own file, and only the
diagnostic's severity moves — a warning where the author wrote it, a note
where a venue's file did, which N0020 names once. Two builds differing by
the gate's own condition, so a demotion hiding a difference fails here. -/
def paramDemoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let sub (file src : String) : Array Parse.Raw := (Parse.parse file (Lex.lex file src).1).1
  let setting := "\\setlength{\\footnotesep}{7pt}\n"
  let head := sub "main.tex" "\\documentclass{article}\n"
  let tail := sub "main.tex" "\\begin{document}\nAlpha words.\\footnote{Bravo note.}\n\\end{document}"
  let (dSty, dsSty) := Elab.runRaws "main.tex"
    (head ++ #[Parse.Raw.env (Parse.inputEnv "venue.sty") (sub "venue.sty" setting) ⟨2, 1⟩] ++ tail)
  let (dOwn, dsOwn) := Elab.runRaws "main.tex" (head ++ sub "main.tex" setting ++ tail)
  let named (ds : Array Diag) := ds.filter (·.subject == some "ctrl:setlength:footnotesep")
  t "a parameter set in a style file ships the page it ships from the document"
    (reprStr (layoutOf oneFace dSty).pages == reprStr (layoutOf oneFace dOwn).pages)
  t "a parameter set in a style file is a note there and a warning in the document"
    ((named dsSty).map (·.severity) == #[.note] && (named dsOwn).map (·.severity) == #[.warning])


/-- **A redefined `\normalsize` sets the document's display skips, and a
size command in the preamble sets nothing.** `\begin{document}` runs
`\normalsize` (measured under lualatex), so the display skips a venue's
redefinition assigns are the body's — the page is the one their native
tokens set, and not the one the same redefinition without them sets — and a
`\normalsize` or `\small` standing at the preamble's top level is gone by
the first line, as LaTeX's is, said in a note instead of an unknown-command
warning. Asserted on the shipped page. -/
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
  t "a redefined \\normalsize sets the page its native size and display skips set"
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
  -- A skip copied from one the class set is read through the length door:
  -- the class's value is unknown here, so the copy is named once and the
  -- skip keeps its value — which is the copy, since the class's two are one.
  let copy := doc (redef "\\belowdisplayskip\\abovedisplayskip\n") body
  let cds := dvE copy
  t "a redefined \\normalsize copying a skip it does not set builds"
    (!cds.any (·.severity == .error))
  t "a redefined \\normalsize copying a skip it does not set names the copy once"
    ((cds.filter (·.code == "W0104")).map (·.subject) ==
      #[some "ctrl:setlength:belowdisplayskip:value"])
  t "a redefined \\normalsize copying a skip it does not set ships the page without the copy"
    (pagesOf oneFace copy == pagesOf oneFace (doc (redef "") body))


/-- **A counter set in the preamble holds where the body starts, and
`secnumdepth` decides which headings number.** LaTeX's counter commands are
preamble-legal (ltcounts.dtx), so they move to the body's start and the one
counter arm reads them in flow order. A heading deeper than `secnumdepth`
neither numbers nor steps (ltsect.dtx `\@sect`, measured under lualatex: a
subsection hidden at depth 1 leaves the next numbered one `1.1`), and the
footnote and equation counters start where they were set. Asserted on the
shipped page, against the document spelled with the number by hand. -/
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
  t "a preamble counter command is not unknown"
    (!(dvE (doc "\\setcounter{secnumdepth}{1}\\stepcounter{footnote}" heads)).any
      (·.code == "W0301"))
  t "a preamble counter the engine does not keep is named as it is in the body"
    ((dvE (doc "\\setcounter{tocdepth}{2}" heads)).any fun d =>
      d.code == "W0104" && d.subject == some "ctrl:setcounter:tocdepth")
  -- A value held in a register: the kernel's constants read as the
  -- integers they are (plain.tex), any other register is named once and
  -- the counter keeps its value — never an error.
  let zero := doc "\\makeatletter\\setcounter{secnumdepth}{\\z@}\\makeatother" heads
  t "a counter set to '\\z@' builds and reads zero"
    (!(dvE zero).any (·.severity == .error) &&
      pagesOf oneFace zero == pagesOf oneFace (doc "\\setcounter{secnumdepth}{0}" heads))
  t "a counter set to '\\z@' moves the page" (pagesOf oneFace zero != pagesOf oneFace (doc "" heads))
  let reg := doc "\\makeatletter\\setcounter{secnumdepth}{\\@tempcnta}\\makeatother" heads
  t "a counter set to a register it cannot read builds, named once on its value"
    (!(dvE reg).any (·.severity == .error) &&
      ((dvE reg).filter (·.code == "W0104")).map (·.subject) ==
        #[some "ctrl:setcounter:secnumdepth:value"])
  t "a counter set to a register it cannot read keeps its value"
    (pagesOf oneFace reg == pagesOf oneFace (doc "" heads))
  -- `secnumdepth` past three numbers the run-in levels (classes.dtx:
  -- `\paragraph` is level four, `\subparagraph` five), each after its parent.
  let runIn := "\\section{Alpha}\\subsection{Bravo}\\subsubsection{Charlie}\n" ++
    "\\paragraph{Delta} Echo words.\n\n\\subparagraph{Foxtrot} Golf words."
  let four := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{4}" runIn)
  t "secnumdepth 4 numbers a paragraph after its parent" (pageHas four 0 "1.1.1.1")
  t "secnumdepth 4 leaves a subparagraph unnumbered" (!pageHas four 0 "1.1.1.1.1")
  let five := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{5}" runIn)
  t "secnumdepth 5 numbers a subparagraph after its parent" (pageHas five 0 "1.1.1.1.1")
  t "the class's secnumdepth numbers no paragraph"
    (!pageHas (censusOfSrc oneFace (doc "" runIn)) 0 "1.1.1.1")


/-- **A list level's parameters are its class macro's, run where a list of
that depth opens.** `\list` calls `\@listi` … `\@listvi` for its depth
(ltlists.dtx), so a redefinition assigning `\leftmargin`, `\topsep`,
`\itemsep` and `\parsep` sets that level's indent, opening space and gap
between items, over the values the enclosing level left. The outermost is
the one trap, measured under lualatex: a class's `\normalsize` does
`\let\@listi\@listI` and `\begin{document}` runs it, so a preamble
`\@listi` stands only under a redefined `\normalsize` that omits the reset
— as a venue style's does — and otherwise sets exactly the page the
document sets without it. Asserted on the shipped page against the native
styles spelled with the values. -/
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
  let outer := "\\style{itemize}{ indent = 40pt, before = 9pt plus 1pt minus 2pt, " ++
    "gap = 5pt plus 2pt }\\style{enumerate}{ indent = 40pt, before = 9pt plus 1pt minus 2pt, " ++
    "gap = 5pt plus 2pt }"
  let kept := pagesOf oneFace (doc (keep ++ params ++ listi) body)
  t "a kept \\@listi sets the outermost lists the page their native styles set"
    (kept == pagesOf oneFace (doc ("\\page{ fontsize = 10pt, leading = 1 }" ++ outer) body))
  t "a kept \\@listi moves the page" (kept != pagesOf oneFace (doc (keep ++ params) body))
  t "a class's \\normalsize resets \\@listi: the redefinition sets nothing"
    (pagesOf oneFace (doc (params ++ listi) body) == pagesOf oneFace (doc params body))
  let listii := "\\setlength{\\leftmarginii}{30pt}\n\\def\\@listii{\\leftmargin\\leftmarginii\n" ++
    "\\labelwidth\\leftmarginii \\advance\\labelwidth-\\labelsep\n" ++
    "\\topsep 4\\p@ \\@plus 1\\p@ \\parsep 1.5\\p@ \\itemsep \\parsep}\n"
  let inner := "\\style{itemize2}{ indent = 30pt, before = 4pt plus 1pt, gap = 3pt }" ++
    "\\style{enumerate2}{ indent = 30pt, before = 4pt plus 1pt, gap = 3pt }"
  let second := pagesOf oneFace (doc listii body)
  t "a redefined \\@listii sets the second level the page its native style sets"
    (second == pagesOf oneFace (doc inner body))
  t "a redefined \\@listii moves the page"
    (second != pagesOf oneFace (doc "\\setlength{\\leftmarginii}{30pt}" body))
  let ds := dvE (doc listii body)
  t "a list level's arithmetic is read with it, and what it sets unread is named once"
    (!ds.any (·.subject == some "ctrl:advance") &&
      (ds.filter (·.subject == some "ctrl:setlength:labelwidth")).size == 1)
  -- A body assignment between two lists reaches the second in LaTeX
  -- exactly when the level's macro leaves the parameter be: the preamble's
  -- styles are judged on the preamble alone, and a reach the engine's
  -- per-level lists cannot follow is named.
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



/-- **Every LaTeX-valid length setting builds: one the door reads is the
value it holds, and one it cannot read is named once and changes nothing.**
The door evaluates a value where it stands, as TeX copies a register's value
(a kernel parameter the document set, `\medskipamount`, `-\x`,
`\dimexpr … \relax`, TeX's own `\parskip 6pt`), and the page is the one the
literal spelling sets. A value it cannot evaluate — a kernel parameter's
class value, infinite glue, a command that measures text — is W0104 once,
keyed on the parameter, and the page is the one the document ships without
the setting: never an error, never stray text. The list idiom, a setting
before a list's first `\item`, builds the same way. Asserted on the shipped
page and the structured diagnostics. -/
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
    !ds.any fun d => d.severity == .error || d.code == "W0104" || d.code == "W0301"
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
      ((ds.filter fun d => d.code == "W0104").map (·.subject) ==
        #[some s!"ctrl:setlength:{n}:value"])
    t s!"'{pre}' ships the page the document ships without it" (pagesOf oneFace src == bare)
  -- A definition's body runs where the command is used: nothing in it is
  -- judged where it is defined, whatever it copies.
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
  t "a length set before a list's first item is named once, as spacing only that list"
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


/-- **An assignment is the value later arithmetic reads only where TeX makes
it: not in a definition's body, which runs where the command is used, and not
past the group or environment it stands in** (TeXbook ch. 24: assignments
are local to their group). Measured as the gap a `\vspace` of the length
sets on the shipped page, against the document that sets the value LaTeX
computes (lualatex: 11pt in every row). -/
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


/-- **A parameter a command reads as its operand is not assigned.** TeX's
own `⟨variable⟩[=]⟨value⟩` opens a statement, and a register standing
where a command reads a dimension — after `\ifdim`, after a factor —
is that command's operand (TeXbook ch. 20 and 24), so the page is the one
the document ships without the construct. The shape `\ifdim\parskip=0pt`
once set the paragraph gap to zero under a note claiming the assignment. -/
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
