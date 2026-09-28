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
  -- The refusal tells the truth about what it read (review SP-2): a
  -- definition whose heading no reading carries — a run-in heading, none
  -- at all — has only its body size read, and the built-in's heading
  -- word, standing in place of a written one, is named with it.
  let refusal (begin : String) : Option String × Option Ir.ElementStyle :=
    let (d, ds) := elabStr (venue begin)
    ((ds.find? (·.code == "W0303")).map (·.message), d.styles.find? "abstract")
  let (runin, runinStyle) := refusal "\\noindent\\textbf{Summary.}\\ "
  t "a run-in heading is not read as the built-in's, and the refusal says only its size is"
    (match runin, runinStyle with
     | some m, some st =>
       hasStr m "only its body size is read" && !hasStr m "style it" &&
         hasStr m "'Abstract', not 'Summary.'" && st.font.isNone && st.align.isNone
     | _, _ => false)
  let (empty, _) := refusal ""
  t "an empty definition's refusal names no heading it does not write"
    (match empty with
     | some m => hasStr m "only its body size is read" && !hasStr m "not '"
     | none => false)
  let (renamed, _) := refusal "\\small\\begin{center}\\textbf{Overview}\\end{center}\\begin{quote}"
  t "a centred heading of another word styles the built-in, and the word it replaces is named"
    (match renamed with
     | some m => hasStr m "style it" && hasStr m "'Abstract', not 'Overview'"
     | none => false)
  let (same, _) := refusal (heading ++ "\\begin{quote}")
  t "a heading writing the built-in's own word names no replacement"
    (match same with
     | some m => hasStr m "style it" && !hasStr m "not '"
     | none => false)


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
  -- A venue's table redefinition swaps the two skips. Which of them faces
  -- the table is the caption's side and the position it is placed for:
  -- the kernel's `\@makecaption` sets `\abovecaptionskip` above a caption
  -- and `\belowcaptionskip` below it, so under the kernel the swapped
  -- 8pt stands between a caption above and its table; the caption
  -- package's `tableposition=top` sets `\abovecaptionskip` there instead
  -- and puts the 8pt above the caption. Two builds, each against the
  -- native spelling of what LaTeX places; measured on the same shape with
  -- 9pt (caption top to first row, bp): lualatex 20.50 and 11.96, the
  -- engine 21.00 and 12.00.
  let swap := "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{0pt}" ++
    "\\setlength{\\belowcaptionskip}{8pt}\\@float{table}}{\\end@float}\n"
  let venue := "\\setlength{\\abovecaptionskip}{8pt}\\setlength{\\belowcaptionskip}{0pt}\n" ++ swap
  let packaged := "\\usepackage[tableposition=top]{caption}\n" ++ venue
  t "under the kernel, the swapped skip below a caption above its table faces the table"
    (shippedLines fonts (dvDoc venue body) ==
      shippedLines fonts (dvDoc "\\tokens{ captionsep = 8pt, tablecaptionsep = 8pt }\n" body))
  t "under caption's tableposition=top, the skip above the caption faces the table"
    (shippedLines fonts (dvDoc packaged body) ==
      shippedLines fonts (dvDoc ("\\tokens{ captionsep = 8pt, tablecaptionsep = 0pt, " ++
        "tablebelowcaptionskip = 8pt }\n") body))
  let capTop (c : Array CensusPage) : Option Dim.Sp := lineYOf c 0 "Table words"
  let (kernelGap, _) := gaps venue
  let (pkgGap, _) := gaps packaged
  t "the two placements part the caption from its table by the swapped 8pt"
    (match kernelGap, pkgGap with
     | some k, some p => k - p == Dim.pt 8
     | _, _ => false)
  t "the caption package sets the swapped 8pt above the caption, the kernel sets none"
    (match capTop (censusOfSrc fonts (dvDoc packaged body)),
        capTop (censusOfSrc fonts (dvDoc venue body)) with
     | some p, some k => p - k == Dim.pt 8
     | _, _ => false)
  let belowBody := "Opening words.\n\n\\begin{table}\\begin{tabular}{ll}Alpha & Beta\\\\" ++
    "\\end{tabular}\\caption{Table words.}\\end{table}\n\nClosing words."
  t "under the kernel, a caption below its table faces it with the skip above the caption"
    (shippedLines fonts (dvDoc venue belowBody) ==
      shippedLines fonts (dvDoc ("\\tokens{ captionsep = 8pt, tablecaptionsep = 0pt, " ++
        "tablebelowcaptionskip = 8pt }\n") belowBody))
  t "the caption package's default position faces the object with the skip above the caption"
    (shippedLines fonts (dvDoc ("\\usepackage{caption}\n" ++ venue) body) ==
      shippedLines fonts (dvDoc packaged body) &&
     shippedLines fonts (dvDoc packaged body) != shippedLines fonts (dvDoc venue body))
  t "a declared bottom position places a caption above as the kernel does"
    (shippedLines fonts (dvDoc ("\\usepackage{caption}\\captionsetup[table]{position=bottom}\n" ++
        venue) body) == shippedLines fonts (dvDoc venue body) &&
     shippedLines fonts (dvDoc venue body) != shippedLines fonts (dvDoc packaged body))
  t "a table redefined around the kernel's float core is no refusal"
    (!((dvE (dvDoc venue body)).any (·.code == "W0303")))
  -- The idiom's values are read at the door every `\setlength` reads
  -- through (review LP-1): a kernel skip amount or a `\dimexpr` is its
  -- value, a copy of the other caption skip is what this code assigned it,
  -- and a value the door cannot read is one keyed W0104 with the skip left
  -- as it was. Handed to the declaration unread, each failed the build.
  let redef (v : String) : String :=
    "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{" ++ v ++
      "}\\@float{table}}{\\end@float}\n"
  let builds (pre : String) : Bool :=
    !((dvE (dvDoc pre body)).any (·.severity == .error))
  let reads (v lit : String) : Bool :=
    builds (redef v) && !((dvE (dvDoc (redef v) body)).any (·.code == "W0104")) &&
      shippedLines fonts (dvDoc (redef v) body) == shippedLines fonts (dvDoc (redef lit) body)
  let named (pre : String) : Bool :=
    builds pre &&
      ((dvE (dvDoc pre body)).filter (·.code == "W0104")).map (·.subject) ==
        #[some "ctrl:setlength:abovecaptionskip:value"]
  t "a kernel skip amount in the float-core idiom reads as its value"
    (reads "\\smallskipamount" "3pt plus 1pt minus 1pt")
  t "a dimexpr in the float-core idiom reads as its value"
    (reads "\\dimexpr 2pt+1pt\\relax" "3pt")
  t "a declared length in the float-core idiom reads as its value"
    (builds ("\\newlength{\\placeholdergap}\\setlength{\\placeholdergap}{5pt}\n" ++ redef "\\placeholdergap") &&
      shippedLines fonts (dvDoc ("\\newlength{\\placeholdergap}\\setlength{\\placeholdergap}{5pt}\n" ++
        redef "\\placeholdergap") body) == shippedLines fonts (dvDoc (redef "5pt") body))
  t "a value the door cannot read is named once and the skip keeps its value"
    (reads "0.5\\baselineskip" "6pt" ||
      (named (redef "0.5\\baselineskip") &&
        shippedLines fonts (dvDoc (redef "0.5\\baselineskip") body) ==
          shippedLines fonts (dvDoc "\\renewenvironment{table}{\\@float{table}}{\\end@float}\n" body)))
  let copyAfter := "\\renewenvironment{table}{\\setlength{\\belowcaptionskip}{8pt}" ++
    "\\setlength{\\abovecaptionskip}{\\belowcaptionskip}\\@float{table}}{\\end@float}\n"
  let copyAfterLit := "\\renewenvironment{table}{\\setlength{\\belowcaptionskip}{8pt}" ++
    "\\setlength{\\abovecaptionskip}{8pt}\\@float{table}}{\\end@float}\n"
  t "a copy of the skip this code assigned before reads what it assigned"
    (builds copyAfter && shippedLines fonts (dvDoc copyAfter body) ==
      shippedLines fonts (dvDoc copyAfterLit body))
  let copyBefore := "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{\\belowcaptionskip}" ++
    "\\setlength{\\belowcaptionskip}{8pt}\\@float{table}}{\\end@float}\n"
  t "a copy of a caption skip this code never assigned is named, not handed on"
    (named copyBefore && shippedLines fonts (dvDoc copyBefore body) ==
      shippedLines fonts (dvDoc ("\\renewenvironment{table}{\\setlength{\\belowcaptionskip}{8pt}" ++
        "\\@float{table}}{\\end@float}\n") body))
  let html (pre : String) : String := (HtmlDoc.emit {} (elabStr (dvDoc pre body)).1).1
  t "the HTML table caption above its table reads the skip its placement faces there"
    (hasStr (html venue) "--ltx-capsep-top: var(--tablebelowcaptionskip, var(--belowcaptionskip, 0px))" &&
      hasStr (html packaged) "--ltx-capsep-top: var(--tablecaptionsep, var(--captionsep,")
  -- The object's own peer margin (`* + table.booktabs`, the paragraph
  -- gap) collapsed with the caption's skip facing it, so no skip below
  -- the paragraph gap reached the rendered page (Chromium, the swap under
  -- tableposition=top: 11.59px where the page's plan sets 0).
  t "the HTML object after a caption above takes no peer margin of its own"
    (hasStr (html packaged) ":where(figure.float > figcaption:first-child + *) { margin-top: 0; }")
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
  -- subcaption's own scope for every sub-caption is `[sub]` (caption
  -- manual, subcaption §2), `[subfigure]` and `[subtable]` its two types
  -- (review LP-3): named unhonoured, it moved the page off both.
  let subBody := "\\begin{figure}\\begin{subfigure}{0.4\\textwidth}Sub body words." ++
    "\\caption{Sub words.}\\end{subfigure}\\caption{Figure words.}\\end{figure}"
  let subPage (scope : String) : Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
    shippedLines fonts (dvDoc ("\\usepackage{subcaption}\n\\captionsetup[" ++ scope ++
      "]{skip=2pt}\n") subBody)
  t "a sub scope sets every sub-caption as the subfigure scope does"
    (subPage "sub" == subPage "subfigure" &&
      subPage "sub" != shippedLines fonts (dvDoc "\\usepackage{subcaption}\n" subBody) &&
      !((dvE (dvDoc "\\usepackage{subcaption}\n\\captionsetup[sub]{skip=2pt}\n" subBody)).any
        (·.code == "W0354")))


/-- **Owed: the kernel's order for the document's own caption skips.** A
document without the caption package that sets `\abovecaptionskip` and
`\belowcaptionskip` in its preamble has them placed as the kernel's
`\@makecaption` places them: above and below the caption, so a caption
above its table sits on `\belowcaptionskip`. A float-core redefinition
declares that order for its kind (`captionScopeChecks`); a preamble
`\setlength` does not yet — `Compat`'s `\setlength` arms read
`\abovecaptionskip` as the object-binding `captionsep` and drop
`\belowcaptionskip` with a note — so the caption keeps
`\abovecaptionskip` on its table side. Measured against lualatex on a
synthetic probe, caption top to first row in bp: 11.53 there, 21.00
here. Read in both directions: the row holds while the declaration ships
the object-binding page, and turns red when the kernel's order lands. -/
def globalCaptionSkipsOwed : Bool := true

/-- The parked row's judge: the page under the declared skips against the
page of their object-binding reading. -/
def globalCaptionSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body := "Opening words.\n\n\\begin{table}\\caption{Table words.}" ++
    "\\begin{tabular}{ll}Alpha & Beta\\\\\\end{tabular}\\end{table}\n\nClosing words."
  let declared := shippedLines fonts (dvDoc
    "\\setlength{\\abovecaptionskip}{8pt}\\setlength{\\belowcaptionskip}{0pt}\n" body)
  let objectBound := shippedLines fonts (dvDoc "\\tokens{ captionsep = 8pt }\n" body)
  check ref "a document's own caption skips are owed the kernel's order (parked, read both ways)"
    ((declared == objectBound) == globalCaptionSkipsOwed)


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
  -- The words as the page sets them, spaces included: each line below is
  -- lualatex's own for its source, so a glued seam cannot pass.
  let sets (src line : String) : Bool := hasStr (pageTextOf fonts src) line
  let defined := doc "\\NewEnviron{placeholder}{Lead words \\BODY}[ Tail words]\n" use
  let kernel := doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" use
  t "a NewEnviron environment ships what its kernel spelling ships"
    (shippedLines fonts defined == shippedLines fonts kernel &&
      sets defined "Lead words Middle words Tail words")
  t "the package, the definer and the use raise nothing unknown"
    (!((dvE defined).any fun d => ["W0103", "W0301", "W0302"].contains d.code))
  let arg := doc "\\NewEnviron{placeholder}[1]{#1: \\BODY}\n"
    "\\begin{placeholder}{Name}Middle words\\end{placeholder}"
  let argKernel := doc "\\newenvironment{placeholder}[1]{#1: }{}\n"
    "\\begin{placeholder}{Name}Middle words\\end{placeholder}"
  t "a NewEnviron argument reaches its code as the kernel spelling's does"
    (shippedLines fonts arg == shippedLines fonts argKernel && sets arg "Name: Middle words")
  -- TeX ends a control word at the space after it, so `\BODY Tail` puts
  -- no space before the tail, where `{ Tail words}` does.
  let renew := doc "\\RenewEnviron{placeholder}{\\BODY Tail words}\n" use
  t "RenewEnviron is the same definer"
    (shippedLines fonts renew ==
      shippedLines fonts (doc "\\renewenvironment{placeholder}{}{Tail words}\n" use) &&
     sets renew "Middle wordsTail words")
  let spaced := "\\begin{placeholder} Middle words \\end{placeholder}\n\n" ++
    "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
  t "a body bringing its own spaces to the halves' spaced edges sets two at each seam, as TeX does"
    (sets (doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" spaced)
        "Lead words  Middle words  Tail words" &&
     sets (doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" spaced)
        "Inline Lead words  Middle words  Tail words after.")
  let boxed := doc "\\NewEnviron{placeholder}{\\fbox{\\BODY}}\n" use
  t "a body placed inside a group is refused where it stands, and nothing of it leaks"
    ((dvE boxed).any (fun d => d.code == "W0104" && hasStr d.message "inside a group") &&
      !hasStr (pageTextOf fonts boxed) "BODY" && hasStr (pageTextOf fonts boxed) "Middle words")
  -- environ collects the body into `\BODY` and runs the code; a code that
  -- never places it sets its own words and nothing of the body (review SP-3).
  let hidden := doc "\\NewEnviron{placeholder}{}\n" use
  t "a code with no BODY discards the body, and says nothing of it"
    (!hasStr (pageTextOf fonts hidden) "Middle words" &&
      !((dvE hidden).any fun d => ["W0104", "W0301", "W0302"].contains d.code))
  t "a code with no BODY still sets its own words"
    (sets (doc "\\NewEnviron{placeholder}{Lead words}\n" use) "Lead words" &&
      !hasStr (pageTextOf fonts (doc "\\NewEnviron{placeholder}{Lead words}\n" use)) "Middle")
  let hiddenArg := doc "\\NewEnviron{placeholder}[1]{#1}\n"
    "\\begin{placeholder}{Name}Middle words\\end{placeholder}"
  t "a discarding environment's arguments still reach its code"
    (sets hiddenArg "Name" && !hasStr (pageTextOf fonts hiddenArg) "Middle words")
  t "a redefinition placing BODY places the body again"
    (sets (doc "\\NewEnviron{placeholder}{}\n\\RenewEnviron{placeholder}{\\BODY}\n" use)
      "Middle words")
  -- environ runs the code where the body ends and the final code at the
  -- end, whether or not the code places the body (review LP-2): refused,
  -- the body LaTeX hides shipped instead.
  let finalOnly := doc "\\NewEnviron{placeholder}{Lead words}[ Tail words]\n"
    "Alpha words.\n\n\\begin{placeholder}Hidden words\\end{placeholder}\n\nBravo words."
  t "a final code beside a code with no BODY ends the environment, the body hidden"
    (sets finalOnly "Lead words Tail words" && !hasStr (pageTextOf fonts finalOnly) "Hidden" &&
      !((dvE finalOnly).any fun d => ["W0104", "W0301", "W0302"].contains d.code))
  -- environ's `\BODY` is the body with its edge spaces trimmed, and its
  -- default final code `\ignorespacesafterend` skips the spaces after
  -- `\end{…}` (environ.sty `\env@save`, `\environfinalcode`); each line
  -- below is lualatex's for the source (review LP-2).
  let trimmed := "Before \\begin{placeholder} Middle words \\end{placeholder} after.\n\n" ++
    "\\begin{placeholder}\nOther words\n\\end{placeholder}"
  t "environ trims the body's edge spaces and skips the spaces after the end"
    (sets (doc "\\NewEnviron{placeholder}{(\\BODY)}\n" trimmed) "Before (Middle words)after." &&
      sets (doc "\\NewEnviron{placeholder}{(\\BODY)}\n" trimmed) "(Other words)")
  t "a given final code replaces the skip after the end"
    (sets (doc "\\NewEnviron{placeholder}{(\\BODY}[)]\n" trimmed) "Before (Middle words) after.")
  -- A document's own `\BODY` macro in a kernel definition is that macro:
  -- only environ's definer places the collected body there (review LP-1).
  -- Split at it, the kernel's begin code left its end group unconsumed in
  -- the preamble, which failed the build (E0313).
  let ownBody := "\\newcommand{\\BODY}{Inner words}\n" ++
    "\\newenvironment{placeholder}{Lead \\BODY{} }{ Tail words}\n"
  for src in [dvDoc ownBody use, doc ownBody use] do
    t "a document's own BODY macro in a kernel definition is the macro"
      (!((dvE src).any (·.severity == .error)) &&
        sets src "Lead Inner words Middle words Tail words")


/-- **Owed: a redefined abstract's vertical skips.** A venue's
`\renewenvironment{abstract}` declares its own skips — a `\vskip` above
the heading, a `\vspace` between the heading and the `quote` its body sets
in, a `\vskip` below — and LaTeX adds each, the `\vspace` surviving the
quote's `\addvspace` (latex.ltx `\@vspace` appends `\vskip\z@`). The
engine places the abstract by its own rhythm (Layout's `.abstract` arm),
so two redefinitions differing in one declared skip ship one page. This
row is that fact parked, read in both directions: it holds `true` while
the pages agree, and the engine honouring the skip turns the check red
until the row flips — the W0303 clause naming the skips retiring with it.
Measured against lualatex on a synthetic probe, baselines in bp: heading
to body 24.16 there, 18.40 here; last body line to the next paragraph
26.40 there, 18.00 here. -/
def abstractSkipsOwed : Bool := true

/-- The parked row's judge: the page under two declared heading gaps. -/
def abstractSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let venue (gap : String) : String :=
    "\\documentclass{article}\\renewenvironment{abstract}{\\centerline{\\large\\bf Abstract}" ++
      "\\vspace{" ++ gap ++ "}\\begin{quote}}{\\par\\end{quote}}" ++
      "\\begin{document}\\begin{abstract}Placeholder summary words.\\end{abstract}\n\n" ++
      "Plain body words after.\\end{document}"
  let ignored := shippedLines fonts (venue "1ex") == shippedLines fonts (venue "4ex")
  check ref "a redefined abstract's declared skips are owed (parked, read both ways)"
    (ignored == abstractSkipsOwed)
  check ref "the refusal names the skips it leaves to the engine exactly while they are owed"
    (((dvE (venue "1ex")).any fun d =>
      d.code == "W0303" && hasStr d.message "vertical skips") == abstractSkipsOwed)


/-- **A seam sets the spaces TeX sets there** (review LP-4). TeX drops a
space only by its own rules: its input reader makes one token of a run of
blanks and skips the blanks after a control word or a control space
(TeXbook ch. 8). Two space tokens from two sources — a macro body's tail and
the text after its use, an environment half's edge and its body's — set two
interword glues, and the engine's seam collapse set one, a whole space
narrower than lualatex (`A\gap\gap B`: 95.19 bp there, 93.05 here). Each
source ships the line its spaces spelled out as control spaces ship, read off
the shipped line's width. -/
def seamChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let width (pre body : String) : Option Dim.Sp :=
    ((censusOfSrc fonts (dvDoc pre body))[0]?.bind (·.lines.find? (!·.furniture))).map (·.width)
  let same (pre body spelled : String) : Bool :=
    (width pre body).isSome && width pre body == width "" spelled
  t "two control spaces a macro brings set two spaces"
    (same "\\newcommand{\\gap}{\\ }\n" "Alpha\\gap\\gap Bravo words." "Alpha\\ \\ Bravo words." &&
      width "" "Alpha\\ \\ Bravo words." != width "" "Alpha Bravo words.")
  t "a macro body's closing control space and the one after its use set two"
    (same "\\newcommand{\\probeword}{word\\ }\n" "Lead \\probeword\\ next words."
      "Lead word\\ \\ next words.")
  t "a group's closing space and the space after the group set two"
    (same "" "Lead {word } next words." "Lead word\\ \\ next words.")
  t "an environment half's spaced edge and its body's set two at each seam"
    (same "\\newenvironment{placeholder}{Lead words }{ Tail words}\n"
      "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
      "Inline Lead words\\ \\ Middle words\\ \\ Tail words after.")
  t "the blanks after a control space are skipped, as TeX's reader skips them"
    (same "" "Alpha\\  Bravo words." "Alpha\\ Bravo words.")
  -- TeX's own commands at an environment's seams: `\ignorespaces` closing
  -- the begin code skips the body's leading spaces, `\ignorespacesafterend`
  -- in the end code the spaces after `\end{…}` — spent, never an unknown
  -- command whose name reaches the page.
  let lead := "\\newenvironment{placeholder}{Lead words \\ignorespaces}{ Tail words}\n"
  let after := "\\newenvironment{placeholder}{Lead words }{ Tail words\\ignorespacesafterend}\n"
  let use := "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
  t "ignorespaces closing a begin code skips the body's leading spaces"
    (same lead use "Inline Lead words Middle words\\ \\ Tail words after." &&
      !((dvE (dvDoc lead use)).any (·.code == "W0301")))
  t "ignorespacesafterend skips the spaces after the environment's end"
    (same after use "Inline Lead words\\ \\ Middle words\\ \\ Tail wordsafter." &&
      !((dvE (dvDoc after use)).any (·.code == "W0301")))
