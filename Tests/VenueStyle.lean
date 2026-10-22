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
    (other.any (·.code == "W0302") && !other.any fun d => d.code == "N0100" &&
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
    ((ds.filter fun d => d.code == "W0302" && d.span.any (·.file.endsWith "fancy-part.tex")).size == 1 &&
      !ds.any fun d => d.code == "N0100" && hasStr d.message "DefineVerbatimEnvironment")

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
