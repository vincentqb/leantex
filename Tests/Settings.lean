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
