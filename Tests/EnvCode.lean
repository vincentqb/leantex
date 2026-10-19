module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.EnvCode

/-- A source and its control ship the same pages, web page head and text, and raise the same
warnings; a macro's role marks its own expansion, not what it sets. -/
private def sameShip (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label src control : String) : IO Unit := do
  let t := check ref
  let said (ds : Array Diag) : List (String × String) :=
    (ds.filter (·.severity != .note)).toList.map fun d => (d.code, d.message)
  let ships (src : String) : Array Diag × String × String × String :=
    let (doc, ds) := elabStr src
    let out := layoutOf fonts doc
    let (head, tree, hds) := HtmlDoc.emitTree {} doc
    (ds ++ out.diags ++ hds, reprStr out.pages, Html.document "en" head #[],
      shownTextList "" tree.toList)
  let (ds, pages, head, text) := ships src
  let (cds, cpages, chead, ctext) := ships control
  t s!"{label}: the control's warnings ({said ds} against {said cds})" (said ds == said cds)
  t s!"{label}: the control's pages" (pages == cpages)
  t s!"{label}: the control's web page head" (head == chead)
  t s!"{label}: the control's text ({text})" (text == ctext)

/-- A macro whose body gives a setting its argument, used in an environment's code, sets there what
the setting written in that code sets, for every setting a definition body leaves to its uses; a
value from the environment's own arguments is named once, its text nowhere. -/
def templateCodeUseChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let colour := "\\usepackage{xcolor}\n"
  let babel := "\\usepackage[french,english]{babel}\n"
  let inline := "Alpha \\begin{probe}Bravo \\enquote{charlie} words\\end{probe} Delta."
  let block := "Alpha.\n\n\\begin{probe}\nBravo words.\n\nCharlie words.\n\\end{probe}\n\nDelta words."
  let painted (ink : String) : String :=
    "Alpha.\n\n\\begin{probe}\n\\textcolor{" ++ ink ++ "}{Bravo} words.\n\\end{probe}\n\nDelta words."
  let deck (pre : String) : String :=
    "\\documentclass{beamer}\n" ++ pre ++
      "\\begin{document}\n\\begin{frame}{Alpha}\n\\begin{probe}Words.\\end{probe}\n\\end{frame}\n\\end{document}"
  -- (setting, preamble, the macro's definition, its use, the setting written out, a body)
  let cases : List (String × String × String × String × String × String) := [
    ("color", colour, "\\newcommand\\use[1]{\\color{#1}}", "\\use{teal}", "\\color{teal}", inline),
    ("color", colour, "\\newcommand\\use[2][HTML]{\\color[#1]{#2}}", "\\use{8B0000}",
      "\\color[HTML]{8B0000}", block),
    ("definecolor", colour, "\\newcommand\\use[2]{\\definecolor{#1}{HTML}{#2}}",
      "\\use{probeink}{8B0000}\\color{probeink}", "\\definecolor{probeink}{HTML}{8B0000}\\color{probeink}",
      block),
    ("colorlet", colour, "\\newcommand\\use[2]{\\colorlet{#1}{#2}}", "\\use{probelet}{blue!50!black}",
      "\\colorlet{probelet}{blue!50!black}", painted "probelet"),
    ("definespotcolor", colour, "\\newcommand\\use[2]{\\definespotcolor{#1}{#2}{0,0.8,1,0.4}}",
      "\\use{probespot}{Probe Ink}", "\\definespotcolor{probespot}{Probe Ink}{0,0.8,1,0.4}",
      painted "probespot"),
    ("linespread", "", "\\newcommand\\use[1]{\\linespread{#1}}", "\\use{1.6}", "\\linespread{1.6}",
      block),
    ("setstretch", "\\usepackage{setspace}\n", "\\newcommand\\use[1]{\\setstretch{#1}}", "\\use{1.6}",
      "\\setstretch{1.6}", block),
    ("fontseries", "", "\\newcommand\\use[1]{\\fontseries{#1}}", "\\use{b}\\selectfont",
      "\\fontseries{b}\\selectfont", inline),
    ("selectlanguage", babel, "\\newcommand\\use[1]{\\selectlanguage{#1}}", "\\use{french}",
      "\\selectlanguage{french}", inline),
    ("foreignlanguage", babel, "\\newcommand\\use[2]{\\foreignlanguage{#1}{#2}}", "\\use{french}{mot}",
      "\\foreignlanguage{french}{mot}", block),
    ("setmathfont", "\\usepackage{unicode-math}\n", "\\newcommand\\use[1]{\\setmathfont{#1}}",
      "\\use{Probe Math}", "\\setmathfont{Probe Math}", block),
    ("newcounter", "", "\\newcommand\\use[1]{\\newcounter{#1}}", "\\use{probecount}",
      "\\newcounter{probecount}", block),
    ("newfontface", "\\usepackage{fontspec}\n", "\\newcommand\\use[1]{\\newfontface\\probeface{#1}}",
      "\\use{Probe Serif}", "\\newfontface\\probeface{Probe Serif}", block),
    ("setfontface", "\\usepackage{fontspec}\n", "\\newcommand\\use[1]{\\setfontface\\probeface{#1}}",
      "\\use{Probe Serif}", "\\setfontface\\probeface{Probe Serif}", block),
    ("renewfontface", "\\usepackage{fontspec}\n\\newfontface\\probeface{Probe Sans}\n",
      "\\newcommand\\use[1]{\\renewfontface\\probeface{#1}}", "\\use{Probe Serif}",
      "\\renewfontface\\probeface{Probe Serif}", block),
    ("providefontface", "\\usepackage{fontspec}\n",
      "\\newcommand\\use[1]{\\providefontface\\probeface{#1}}", "\\use{Probe Serif}",
      "\\providefontface\\probeface{Probe Serif}", block),
    ("setlength", "", "\\newcommand\\use[1]{\\setlength{\\parindent}{#1}}", "\\use{3em}",
      "\\setlength{\\parindent}{3em}", block),
    ("addtolength", "", "\\newcommand\\use[1]{\\addtolength{\\parindent}{#1}}", "\\use{1em}",
      "\\addtolength{\\parindent}{1em}", block),
    ("hypersetup", "\\usepackage{hyperref}\n", "\\newcommand\\use[1]{\\hypersetup{pdftitle={#1}}}",
      "\\use{Probe Title}", "\\hypersetup{pdftitle={Probe Title}}", block),
    ("pagestyle", "", "\\newcommand\\use[1]{\\pagestyle{#1}}", "\\use{empty}", "\\pagestyle{empty}",
      block),
    ("otherlanguage", babel,
      "\\newcommand\\use[2]{\\begin{otherlanguage}{#1}#2\\end{otherlanguage}}", "\\use{french}{mot}",
      "\\begin{otherlanguage}{french}mot\\end{otherlanguage}", block),
    ("otherlanguage*", babel,
      "\\newcommand\\use[2]{\\begin{otherlanguage*}{#1}#2\\end{otherlanguage*}}", "\\use{french}{mot}",
      "\\begin{otherlanguage*}{french}mot\\end{otherlanguage*}", block)]
  for (setting, pre, define, use, written, body) in cases do
    sameShip ref fonts s!"template code: '{setting}' through a macro in an environment's code"
      (dvDoc (pre ++ define ++ "\n\\newenvironment{probe}{" ++ use ++ "}{}\n") body)
      (dvDoc (pre ++ "\\newenvironment{probe}{" ++ written ++ "}{}\n") body)
  t "template code: every setting a definition body leaves to its uses has its case"
    (Compat.paramSettings.all fun s => s == "setbeamertemplate" || cases.any (·.1 == s))
  sameShip ref fonts "template code: a beamer template through a macro in an environment's code"
    (deck "\\newcommand\\use[1]{\\setbeamertemplate{navigation symbols}{#1}}\n\\newenvironment{probe}{\\use{}}{}\n")
    (deck "\\newenvironment{probe}{\\setbeamertemplate{navigation symbols}{}}{}\n")
  sameShip ref fonts "template code: a macro reaching the setting through another"
    (dvDoc (babel ++ "\\newcommand\\sel[1]{\\selectlanguage{#1}}\n\\newcommand\\fr{\\sel{french}}\n" ++
      "\\newenvironment{probe}{\\fr}{}\n") inline)
    (dvDoc (babel ++ "\\newenvironment{probe}{\\selectlanguage{french}}{}\n") inline)
  sameShip ref fonts "template code: the begin and end code each set their own value"
    (dvDoc (babel ++ "\\newcommand\\sel[1]{\\selectlanguage{#1}}\n" ++
      "\\newenvironment{probe}{\\sel{french}}{\\sel{english}}\n") inline)
    (dvDoc (babel ++ "\\newenvironment{probe}{\\selectlanguage{french}}{\\selectlanguage{english}}\n")
      inline)
  let src := dvDoc (colour ++ "\\newcommand\\use[1]{\\color{#1}}\n\\newenvironment{probe}[1]{\\use{#1}}{}\n")
    "Alpha \\begin{probe}{teal}Bravo words\\end{probe} Delta."
  let (ds, _, _, shown) := sourceArtifacts fonts src
  let page := pageTextOf fonts src
  t "template code: a value from the environment's arguments is named once, where the macro is used"
    ((ds.filter (·.subject == some "envcode:color")).size == 1 &&
      (ds.filter (·.subject == some "envcode:color")).all fun d => d.span.map (·.pos.line) == some 4)
  t "template code: a value from the environment's arguments reaches neither page"
    (hasStr page "Bravo" && !hasStr page "teal" && hasStr shown "Bravo" && !hasStr shown "teal")

/-- An inline environment's content and end code stand under the declarations its begin code makes,
to the environment's end, as the group LaTeX's environment opens holds them. -/
def inlineEnvScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let cases : List (String × String × String × String × String) := [
    ("an ink", "\\usepackage{xcolor}\n", "\\color{teal}", "", "\\color{teal}"),
    ("a language", "\\usepackage[french,english]{babel}\n", "\\selectlanguage{french}", "",
      "\\selectlanguage{french}"),
    ("a size", "", "\\large", "", "\\large "),
    ("a shape after text, over the end code", "", "Note: \\itshape", " end", "Note: \\itshape "),
    ("two declarations", "\\usepackage{xcolor}\n", "\\color{teal}\\bfseries", "",
      "\\color{teal}\\bfseries ")]
  for (what, pre, begin, finish, written) in cases do
    sameShip ref fonts s!"inline environment: {what} its begin code declares"
      (dvDoc (pre ++ "\\newenvironment{probe}{" ++ begin ++ "}{" ++ finish ++ "}\n")
        "Alpha \\begin{probe}Bravo charlie words\\end{probe} Delta.")
      (dvDoc pre ("Alpha {" ++ written ++ "Bravo charlie words" ++ finish ++ "} Delta."))
  sameShip ref fonts "inline environment: a typewriter family its begin code declares reads literally"
    (dvDoc "\\newenvironment{probe}{\\ttfamily}{}\n" "Alpha \\begin{probe}\"x\" 'y' a--b\\end{probe} Delta.")
    (dvDoc "" "Alpha {\\ttfamily \"x\" 'y' a--b} Delta.")

/-- An environment whose halves open and close one environment, its arguments read where its
halves set them, ships what the environment written in place ships; so do an environment's commands,
`\trivlist` for `\begin{trivlist}`, and a command no close follows stays a command. -/
def wrapEnvChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\nLead words.\n" ++ body ++
      "\nTail words.\n\\end{document}\n"
  sameShip ref fonts "wrapper: a list"
    (doc "\\newenvironment{kilo}{\\begin{itemize}}{\\end{itemize}}\n"
      "\\begin{kilo}\\item One.\\item Two.\\end{kilo}")
    (doc "" "\\begin{itemize}\\item One.\\item Two.\\end{itemize}")
  sameShip ref fonts "wrapper: a trivlist opening its item"
    (doc "\\newenvironment{lima}{\\begin{trivlist}\\item}{\\end{trivlist}}\n"
      "\\begin{lima}Inside words.\\end{lima}")
    (doc "" "\\begin{trivlist}\\item Inside words.\\end{trivlist}")
  sameShip ref fonts "wrapper: an environment's commands as its halves"
    (doc "\\newenvironment{mike}{\\center\\small}{\\endcenter}\n"
      "\\begin{mike}Centred words.\\end{mike}")
    (doc "" "\\begin{center}\\small Centred words.\\end{center}")
  sameShip ref fonts "wrapper: an argument read in its halves"
    (doc "\\newenvironment{oscar}[1]{\\begin{center}#1}{\\end{center}}\n"
      "\\begin{oscar}{Papa} words.\\end{oscar}")
    (doc "" "\\begin{center}Papa words.\\end{center}")
  sameShip ref fonts "commands: a trivlist's command form"
    (doc "" "\\trivlist\\item Command words.\\endtrivlist")
    (doc "" "\\begin{trivlist}\\item Command words.\\end{trivlist}")
  let (_, ds) := elabStr (doc "\\let\\keep\\center\n\\let\\endkeep\\endcenter\n" "")
  t "commands: an environment's command no close follows stays a command, no error"
    (ds.all (·.severity != .error))
  for pre in ["\\let\\center\\relax\n\\let\\endcenter\\relax\n",
      "\\renewcommand\\itemize{\\list{--}{}}\n\\renewcommand\\enditemize{\\endlist}\n",
      "\\let\\oldcenter=\\center\n\\let\\oldendcenter=\\endcenter\n",
      "\\renewcommand*\\itemize{\\relax}\n\\renewcommand*\\enditemize{\\relax}\n"] do
    let (_, ds) := elabStr (doc pre "")
    t s!"commands: a definition naming an environment's commands opens none: {pre}"
      (ds.all (·.severity != .error))
  let (_, cds) := elabStr (doc "" "\\begin{center}\\center Bravo words.\\end{center}")
  t "commands: an environment's command inside it leaves its end to its begin"
    (cds.all (·.severity != .error))
  sameShip ref fonts "wrapper: an inner wrapper expands as defined where the outer is used"
    (doc ("\\newenvironment{kilo}{\\begin{itemize}}{\\end{itemize}}\n" ++
      "\\newenvironment{lima}{\\begin{kilo}}{\\end{kilo}}\n" ++
      "\\renewenvironment{kilo}{\\begin{center}}{\\end{center}}\n") "\\begin{lima}Centred words.\\end{lima}")
    (doc "" "\\begin{center}Centred words.\\end{center}")
  sameShip ref fonts "wrapper: a wrapper's environment a wrapper itself"
    (doc ("\\newenvironment{kilo}{\\begin{itemize}}{\\end{itemize}}\n" ++
      "\\newenvironment{lima}{\\begin{kilo}}{\\end{kilo}}\n") "\\begin{lima}\\item One.\\end{lima}")
    (doc "" "\\begin{itemize}\\item One.\\end{itemize}")

/-- A style command over a list sets the list under its declaration, and a footnote's list sets
each item on a line of its own after its mark. -/
def blockArgChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (body : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"
  -- Departure: LaTeX's `\textbf` leaves vertical mode first, an empty line above the list.
  sameShip ref fonts "block argument: a bold list"
    (doc "Lead words.\n\n\\textbf{\\begin{itemize}\n\\item Kilo words.\n\\end{itemize}}\nTail words.")
    (doc "Lead words.\n\n{\\bfseries\\begin{itemize}\n\\item Kilo words.\n\\end{itemize}}\nTail words.")
  let (fd, fds) := elabStr (doc ("Lead words.\\footnote{Mike words.\n\\begin{itemize}\n" ++
    "\\item Kilo words.\n\\item Lima words.\n\\end{itemize}\nOscar words.}\nTail words."))
  let notes := (bodyLines (layoutOf fonts fd)).filter (·.note) |>.map (letters ∘ lineText)
  t s!"block argument: a footnote's list ships, each item on a line after its mark: {notes}"
    (fds.all (·.severity != .error) && notes.any (hasStr · "•Kilowords.") &&
      notes.any (hasStr · "•Limawords.") && notes.any (hasStr · "Oscarwords."))
  t "block argument: a footnote's list names its lines as the loss"
    (fds.any (·.code == "W0371"))
  let (od, _) := elabStr (doc ("Lead words.\\footnote{Mike words.\n\\begin{enumerate}[label=(\\alph*)]\n" ++
    "\\item Kilo words.\n\\end{enumerate}}\nTail words."))
  let optNotes := (bodyLines (layoutOf fonts od)).filter (·.note) |>.map (letters ∘ lineText)
  t s!"block argument: a footnote list's options set no ink: {optNotes}"
    (optNotes.any (hasStr · "Kilowords.") && !optNotes.any (hasStr · "label"))

end Tests.EnvCode
