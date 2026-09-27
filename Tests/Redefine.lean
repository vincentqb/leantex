import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # A redefined built-in takes effect

A document or its venue style redefines a built-in environment the engine
keeps (its structure is the engine's: the abstract's region, a float's
number). The redefinition's declarations still take effect, where LaTeX
puts them, and the claims here are read off the shipped page and the HTML
tree. Every source is synthetic. -/

/-- The page lines of a source as comparable values. -/
private def shippedLines (fonts : Font.FontSet) (src : String) :
    Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (censusOfSrc fonts src).flatMap fun p => p.lines.map fun l => (l.x, l.y, l.size, l.text)

/-- **A redefined abstract's body sets at the size its begin body leaves in
force.** article.cls declares `\small` over the whole environment; a venue's
`\renewenvironment{abstract}` that declares no size at its top level leaves
the body at `\normalsize`, and a size inside a group (the heading's
`\centerline{\large ...}`) scopes to that group, as TeX scopes it. The
engine kept the built-in's `\small` for every redefinition, so a venue's
normal-size abstract shipped a step small. -/
def abstractRedefChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "\\begin{document}\\begin{abstract}Placeholder summary words.\\end{abstract}\n\n" ++
    "Plain body words after.\\end{document}"
  let venue (begin : String) : String :=
    "\\documentclass{article}\\renewenvironment{abstract}{" ++ begin ++
      "}{\\par\\end{quote}\\vskip 2ex}" ++ body
  let heading := "\\vskip 0.1in\\centerline{\\large\\bf Abstract}\\vspace{1ex}"
  let sizes (src : String) : Option Dim.Sp × Option Dim.Sp :=
    let c := censusOfSrc fonts src
    (lineSizeOf c 0 "Placeholder summary", lineSizeOf c 0 "Plain body words")
  let (redef, text) := sizes (venue (heading ++ "\\begin{quote}"))
  t "a redefinition declaring no body size sets the body at the text's size"
    (redef.isSome && redef == text)
  let (plain, text) := sizes ("\\documentclass{article}" ++ body)
  t "the built-in abstract keeps article's small body"
    (match plain, text with
     | some p, some b => p < b
     | _, _ => false)
  let (topSmall, _) := sizes (venue ("\\small" ++ heading ++ "\\begin{quote}"))
  t "a size switched at the begin body's top level holds over the body"
    (topSmall == plain)
  let (grouped, text) := sizes (venue ("{\\small x}" ++ heading ++ "\\begin{quote}"))
  t "a size switched inside a group scopes to the group"
    (grouped == text)
  let (inQuote, _) := sizes (venue (heading ++ "\\begin{quote}\\small"))
  t "a size switched inside the environment the begin body leaves open holds over the body"
    (inQuote == plain)
  -- Metamorphic: the venue's redefinition and the same appearance spelled
  -- natively ship the same page, line for line.
  let native := "\\documentclass{article}" ++
    "\\style{abstract}{ font = {\\large\\bf}, body-size = normalsize }" ++ body
  t "the redefinition ships the page its native spelling ships"
    (shippedLines fonts (venue (heading ++ "\\begin{quote}")) == shippedLines fonts native)
  -- Both artifacts read the one resolving site: the HTML region carries
  -- the size the page sets.
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  t "the HTML region of a redefined abstract sets its body at the normal size"
    (hasStr (html (venue (heading ++ "\\begin{quote}"))) "class=\"abstract size-normalsize\"")
  t "the HTML region of the built-in abstract sets its body small, as the page does"
    (hasStr (html ("\\documentclass{article}" ++ body)) "class=\"abstract size-small\"")
  let (bad, badDs) := elabStr ("\\documentclass{article}\\style{abstract}{ body-size = big }" ++ body)
  t "an unknown body size is named and leaves the built-in's"
    (Ir.abstractBodySize bad.styles == "small" && badDs.any (·.code == "E0323"))


/-- The baseline distance on page 0 from the first line holding `a` to the
first holding `b`. -/
private def gapBetween (c : Array CensusPage) (a b : String) : Option Dim.Sp :=
  match lineYOf c 0 a, lineYOf c 0 b with
  | some ya, some yb => some (yb - ya)
  | _, _ => none

/-- **A caption setting scoped to a float type reaches that type alone.**
The caption package's `\captionsetup[table]{skip=...}` sets the table
caption's gap and leaves figures at theirs (caption manual §4); the engine
read the scope and dropped it, so a table-only gap moved every figure's
caption too. A venue's table redefinition around the kernel's float core
(`\@float{table}` … `\end@float`) swapping the two caption skips is the
same scoped declaration, and `skip=\abovecaptionskip` sets the gap to
itself. Read off the shipped page: the caption's baseline to its object's. -/
def captionScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "Opening words.\n\n\\begin{table}\\caption{Table words.}" ++
    "\\begin{tabular}{ll}Alpha & Beta\\\\\\end{tabular}\\end{table}\n\n" ++
    "\\begin{figure}Figure body words.\\caption{Figure words.}\\end{figure}\n\nClosing words."
  let gaps (pre : String) : Option Dim.Sp × Option Dim.Sp :=
    let c := censusOfSrc fonts (dvDoc pre body)
    (gapBetween c "Table words" "Alpha", gapBetween c "Figure body" "Figure words")
  let (tDef, fDef) := gaps ""
  let (tScoped, fScoped) := gaps "\\captionsetup[table]{skip=3pt}\n"
  let (tNative, _) := gaps "\\tokens{ captionsep = 3pt }\n"
  t "a table-scoped skip sets the table caption's gap"
    (tScoped.isSome && tScoped == tNative && tScoped != tDef)
  t "a table-scoped skip leaves the figure caption's gap alone"
    (fScoped.isSome && fScoped == fDef)
  let (tFig, fFig) := gaps "\\captionsetup[figure]{skip=3pt}\n"
  t "a figure-scoped skip sets the figure caption's gap and leaves the table's"
    (tFig == tDef && fFig.isSome && fFig != fDef)
  t "a scoped skip ships the page its native kind token ships"
    (shippedLines fonts (dvDoc "\\captionsetup[table]{skip=3pt}\n" body) ==
      shippedLines fonts (dvDoc "\\tokens{ tablecaptionsep = 3pt }\n" body))
  let venue := "\\setlength{\\abovecaptionskip}{8pt}\\setlength{\\belowcaptionskip}{0pt}\n" ++
    "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{0pt}" ++
    "\\setlength{\\belowcaptionskip}{8pt}\\@float{table}}{\\end@float}\n"
  t "a table redefined around the kernel's float core ships its scoped caption gaps"
    (shippedLines fonts (dvDoc venue body) ==
      shippedLines fonts (dvDoc "\\tokens{ captionsep = 8pt, tablecaptionsep = 0pt }\n" body))
  t "a table redefined around the kernel's float core is no refusal"
    (!((dvE (dvDoc venue body)).any (·.code == "W0303")))
  let selfRef := "\\captionsetup[table]{skip=\\abovecaptionskip}\n"
  t "a skip set to the caption skip itself changes nothing and is honoured"
    (shippedLines fonts (dvDoc selfRef body) == shippedLines fonts (dvDoc "" body) &&
     !((dvE (dvDoc selfRef body)).any (·.code == "W0354")))
  let reg := "\\newlength{\\placeholdergap}\\setlength{\\placeholdergap}{3pt}\n" ++
    "\\captionsetup[table]{skip=\\placeholdergap}\n"
  t "a skip naming a declared length reads its value"
    ((gaps reg).1 == tScoped)
  let (tOther, fOther) := gaps "\\captionsetup[lstlisting]{skip=3pt}\n"
  t "a scope the engine has no float for reaches no float, and is named"
    (tOther == tDef && fOther == fDef &&
      (dvE (dvDoc "\\captionsetup[lstlisting]{skip=3pt}\n" body)).any (·.code == "W0354"))
  let html := (HtmlDoc.emit {} (elabStr (dvDoc "\\captionsetup[table]{skip=3pt}\n" body)).1).1
  t "the HTML table caption reads the table's own gap before the document's"
    (hasStr html "--tablecaptionsep: 3pt" &&
      hasStr html "figure.table-float { --ltx-capsep: var(--tablecaptionsep, var(--captionsep,")


/-- **environ's `\NewEnviron` defines the environment it names.** Its code
places the collected body at `\BODY` (environ.sty's `\env@new`); with
`\BODY` once at the code's top level that is the kernel's
`\newenvironment` with the body standing there, and a `[final code]`
joins the end. The package was refused on load and the definer went
unknown, so a venue's environment was never defined and its uses set as
an unknown wrapper. Read off the shipped page, against the kernel
spelling. -/
def environChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let use := "\\begin{placeholder}Middle words\\end{placeholder}"
  let doc (pre body : String) : String := dvDoc ("\\usepackage{environ}\n" ++ pre) body
  -- The parts in reading order, whatever the space between them (that is
  -- the kernel spelling's own business, which the pairs below hold equal).
  let inOrder (s : String) (parts : List String) : Bool :=
    (parts.foldl (fun (acc : Option String) p => acc.bind fun rest =>
      match rest.splitOn p with
      | _ :: after :: more => some (String.intercalate p (after :: more))
      | _ => none) (some s)).isSome
  let defined := doc "\\NewEnviron{placeholder}{Lead words \\BODY}[ Tail words]\n" use
  let kernel := doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" use
  t "a NewEnviron environment ships what its kernel spelling ships"
    (shippedLines fonts defined == shippedLines fonts kernel &&
      inOrder (pageTextOf fonts defined) ["Lead words", "Middle words", "Tail words"])
  t "the package, the definer and the use raise nothing unknown"
    (!((dvE defined).any fun d => ["W0103", "W0301", "W0302"].contains d.code))
  let arg := doc "\\NewEnviron{placeholder}[1]{#1: \\BODY}\n"
    "\\begin{placeholder}{Name}Middle words\\end{placeholder}"
  let argKernel := doc "\\newenvironment{placeholder}[1]{#1: }{}\n"
    "\\begin{placeholder}{Name}Middle words\\end{placeholder}"
  t "a NewEnviron argument reaches its code as the kernel spelling's does"
    (shippedLines fonts arg == shippedLines fonts argKernel)
  let renew := doc "\\RenewEnviron{placeholder}{\\BODY Tail words}\n" use
  t "RenewEnviron is the same definer"
    (shippedLines fonts renew ==
      shippedLines fonts (doc "\\renewenvironment{placeholder}{}{ Tail words}\n" use) &&
     inOrder (pageTextOf fonts renew) ["Middle words", "Tail words"])
  let boxed := doc "\\NewEnviron{placeholder}{\\fbox{\\BODY}}\n" use
  t "a body placed inside a group is refused where it stands, and nothing of it leaks"
    ((dvE boxed).any (·.code == "W0104") &&
      !hasStr (pageTextOf fonts boxed) "BODY" && hasStr (pageTextOf fonts boxed) "Middle words")
