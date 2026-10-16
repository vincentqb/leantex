module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! A redefined built-in environment takes effect, read off the shipped page and the HTML tree. -/

/-- Whether a redefined abstract's declared vertical skips are still unhonoured, read both ways by
`abstractSkipChecks`. -/
def abstractSkipsOwed : Bool := true

/-- A redefined abstract's body sets at the size its begin body leaves in force. -/
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
  t "a redefinition with no body size sets the body at text size"
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
  t "a size inside the begin body's open environment holds over the body"
    (inQuote == plain)
  -- The pages agree only while the venue's skips are dropped (`abstractSkipsOwed`).
  let native := "\\documentclass{article}" ++
    "\\style{abstract}{ font = {\\large\\bf}, body-size = normalsize }" ++ body
  t "the redefinition ships its native page exactly while its skips are owed"
    ((shippedLines fonts (venue (heading ++ "\\begin{quote}")) == shippedLines fonts native) ==
      abstractSkipsOwed)
  let html (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  t "a redefined abstract's HTML region sets its body at normal size"
    (hasStr (html (venue (heading ++ "\\begin{quote}"))) "class=\"abstract size-normalsize quoted\"")
  t "the built-in abstract's HTML body is small, as on the page"
    (hasStr (html ("\\documentclass{article}" ++ body)) "class=\"abstract size-small quoted\"")
  let (bad, badDs) := elabStr ("\\documentclass{article}\\style{abstract}{ body-size = big }" ++ body)
  t "an unknown body size is named and leaves the built-in's"
    (Ir.abstractBodySize bad.styles == "small" && badDs.any (·.code == "E0323"))
  let refusal (begin : String) : Option String × Option Ir.ElementStyle :=
    let (d, ds) := elabStr (venue begin)
    ((ds.find? (·.code == "W0303")).map (·.message), d.styles.find? "abstract")
  let (runin, runinStyle) := refusal "\\noindent\\textbf{Summary.}\\ "
  t "a run-in heading is not read; the refusal names only the size read"
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
  t "another centred heading word styles the built-in, the replaced word named"
    (match renamed with
     | some m => hasStr m "style it" && hasStr m "'Abstract', not 'Overview'"
     | none => false)
  let (same, _) := refusal (heading ++ "\\begin{quote}")
  t "a heading writing the built-in's own word names no replacement"
    (match same with
     | some m => hasStr m "style it" && !hasStr m "not '"
     | none => false)
  let (inkless, _) := refusal ("\\vskip 2ex plus 1ex\\centerline{\\large\\bf Abstract}" ++
    "\\addcontentsline{toc}{section}{Abstract}\\begin{quote}")
  t "skip glue and inkless commands' arguments are not heading words"
    (match inkless with
     | some m => hasStr m "style it" && !hasStr m "not '"
     | none => false)
  let (italic, _) := refusal (heading ++ "\\itshape")
  t "a read heading's refusal names the built-in's kept margins and body font"
    (match italic with
     | some m => hasStr m "style it" && hasStr m "margins, body font"
     | none => false)


/-- The baseline distance on page 0 from the first line holding `a` to the first holding `b`. -/
private def gapBetween (c : Array CensusPage) (a b : String) : Option Dim.Sp :=
  match lineYOf c 0 a, lineYOf c 0 b with
  | some ya, some yb => some (yb - ya)
  | _, _ => none

/-- A caption setting scoped to a float type reaches that type alone. -/
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
  t "a figure-scoped skip sets the figure caption gap, not the table's"
    (tFig == tDef && fFig.isSome && fFig != fDef)
  t "a scoped skip ships the page its native kind token ships"
    (shippedLines fonts (dvDoc "\\captionsetup[table]{skip=3pt}\n" body) ==
      shippedLines fonts (dvDoc "\\tokens{ tablecaptionsep = 3pt }\n" body))
  -- `\@makecaption` sets `\abovecaptionskip` above a caption and `\belowcaptionskip` below it.
  let swap := "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{0pt}" ++
    "\\setlength{\\belowcaptionskip}{8pt}\\@float{table}}{\\end@float}\n"
  let venue := "\\setlength{\\abovecaptionskip}{8pt}\\setlength{\\belowcaptionskip}{0pt}\n" ++ swap
  let packaged := "\\usepackage[tableposition=top]{caption}\n" ++ venue
  t "kernel: a caption above its table faces it with the swapped skip below"
    (shippedLines fonts (dvDoc venue body) ==
      shippedLines fonts (dvDoc "\\tokens{ captionsep = 8pt, tablecaptionsep = 8pt }\n" body))
  t "tableposition=top: the skip above the caption faces the table"
    (shippedLines fonts (dvDoc packaged body) ==
      shippedLines fonts (dvDoc ("\\tokens{ captionsep = 8pt, tablecaptionsep = 0pt, " ++
        "tablebelowcaptionskip = 8pt }\n") body))
  let capTop (c : Array CensusPage) : Option Dim.Sp := lineYOf c 0 "Table words"
  let (kernelGap, _) := gaps venue
  let (pkgGap, _) := gaps packaged
  t "the kernel's caption-table gap exceeds the package's by the swapped 8pt"
    (match kernelGap, pkgGap with
     | some k, some p => k - p == Dim.pt 8
     | _, _ => false)
  t "caption puts the swapped 8pt above the caption; the kernel puts none"
    (match capTop (censusOfSrc fonts (dvDoc packaged body)),
        capTop (censusOfSrc fonts (dvDoc venue body)) with
     | some p, some k => p - k == Dim.pt 8
     | _, _ => false)
  let belowBody := "Opening words.\n\n\\begin{table}\\begin{tabular}{ll}Alpha & Beta\\\\" ++
    "\\end{tabular}\\caption{Table words.}\\end{table}\n\nClosing words."
  t "kernel: a caption below its table faces it with the skip above"
    (shippedLines fonts (dvDoc venue belowBody) ==
      shippedLines fonts (dvDoc ("\\tokens{ captionsep = 8pt, tablecaptionsep = 0pt, " ++
        "tablebelowcaptionskip = 8pt }\n") belowBody))
  t "caption's default position faces the object with the skip above"
    (shippedLines fonts (dvDoc ("\\usepackage{caption}\n" ++ venue) body) ==
      shippedLines fonts (dvDoc packaged body) &&
     shippedLines fonts (dvDoc packaged body) != shippedLines fonts (dvDoc venue body))
  t "a declared bottom position places a caption above as the kernel does"
    (shippedLines fonts (dvDoc ("\\usepackage{caption}\\captionsetup[table]{position=bottom}\n" ++
        venue) body) == shippedLines fonts (dvDoc venue body) &&
     shippedLines fonts (dvDoc venue body) != shippedLines fonts (dvDoc packaged body))
  t "a table redefined around the kernel's float core is no refusal"
    (!((dvE (dvDoc venue body)).any (·.code == "W0303")))
  let redef (v : String) : String :=
    "\\renewenvironment{table}{\\setlength{\\abovecaptionskip}{" ++ v ++
      "}\\@float{table}}{\\end@float}\n"
  let builds (pre : String) : Bool :=
    !((dvE (dvDoc pre body)).any (·.severity == .error))
  let reads (v lit : String) : Bool :=
    builds (redef v) && !((dvE (dvDoc (redef v) body)).any (·.code == "W0107")) &&
      shippedLines fonts (dvDoc (redef v) body) == shippedLines fonts (dvDoc (redef lit) body)
  let named (pre : String) : Bool :=
    builds pre &&
      ((dvE (dvDoc pre body)).filter (·.code == "W0107")).map (·.subject) ==
        #[some "length:abovecaptionskip"]
  t "a kernel skip amount in the float-core idiom reads as its value"
    (reads "\\smallskipamount" "3pt plus 1pt minus 1pt")
  t "a dimexpr in the float-core idiom reads as its value"
    (reads "\\dimexpr 2pt+1pt\\relax" "3pt")
  t "a declared length in the float-core idiom reads as its value"
    (builds ("\\newlength{\\placeholdergap}\\setlength{\\placeholdergap}{5pt}\n" ++ redef "\\placeholdergap") &&
      shippedLines fonts (dvDoc ("\\newlength{\\placeholdergap}\\setlength{\\placeholdergap}{5pt}\n" ++
        redef "\\placeholdergap") body) == shippedLines fonts (dvDoc (redef "5pt") body))
  t "an unreadable value is named once and the skip keeps its value"
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
  t "a copy of a never-assigned caption skip is named, not handed on"
    (named copyBefore && shippedLines fonts (dvDoc copyBefore body) ==
      shippedLines fonts (dvDoc ("\\renewenvironment{table}{\\setlength{\\belowcaptionskip}{8pt}" ++
        "\\@float{table}}{\\end@float}\n") body))
  let html (pre : String) : String := (HtmlDoc.emit {} (elabStr (dvDoc pre body)).1).1
  t "the HTML caption above its table reads the skip its placement faces"
    (hasStr (html venue) "--ltx-capsep-top: var(--tablebelowcaptionskip, var(--belowcaptionskip, 0px))" &&
      hasStr (html packaged) "--ltx-capsep-top: var(--tablecaptionsep, var(--captionsep,")
  t "the HTML object after a caption above has no peer margin"
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
  t "the HTML table caption prefers the table's gap to the document's"
    (hasStr html "--tablecaptionsep: 3pt" &&
      hasStr html "figure.table-float { --ltx-capsep: var(--tablecaptionsep, var(--captionsep,")
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


/-- Whether the document's own caption skips still follow their object-binding reading rather than
the kernel's order, read both ways by `globalCaptionSkipChecks`. -/
def globalCaptionSkipsOwed : Bool := true

/-- The judge of `globalCaptionSkipsOwed`: the page under the declared skips against their
object-binding reading. -/
def globalCaptionSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body := "Opening words.\n\n\\begin{table}\\caption{Table words.}" ++
    "\\begin{tabular}{ll}Alpha & Beta\\\\\\end{tabular}\\end{table}\n\nClosing words."
  let declared := shippedLines fonts (dvDoc
    "\\setlength{\\abovecaptionskip}{8pt}\\setlength{\\belowcaptionskip}{0pt}\n" body)
  let objectBound := shippedLines fonts (dvDoc "\\tokens{ captionsep = 8pt }\n" body)
  check ref "a document's caption skips are owed the kernel's order (parked)"
    ((declared == objectBound) == globalCaptionSkipsOwed)

/-- An environment definer in the body ships what `{}` in its place ships, an absent optional
argument takes its definition's default, and a definition ends with its group, as lualatex sets
each. -/
def environScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String := dvDoc ("\\usepackage{environ}\n" ++ pre) body
  let sets (src line : String) : Bool := hasStr (pageTextOf fonts src) line
  let shipped (src : String) : Array (Dim.Sp × Dim.Sp × Dim.Sp × String) × String :=
    let (_, _, _, html) := sourceArtifacts fonts src
    (shippedLines fonts src, html)
  let para (definer : String → String) : String :=
    s!"Alpha words.\n{definer "placeholder"}\nBravo words.\n\n" ++
      s!"Charlie \\textbf\{delta {definer "placeholderb"} echo} foxtrot."
  -- A definer testing for a trailing optional argument reads past the spaces after it.
  let eaten := "Alpha words.\n{}Bravo words.\n\nCharlie \\textbf{delta {}echo} foxtrot."
  let definers : List ((String → String) × Bool) := [
    (fun n => s!"\\NewEnviron\{{n}}[2][Lead]\{#1 \\BODY\{} #2}", true),
    (fun n => s!"\\RenewEnviron\{{n}}\{Other}[ Tail]", false),
    (fun n => s!"\\newenvironment\{{n}}[1][Lead]\{(#1}\{)}", false),
    (fun n => s!"\\renewenvironment*\{{n}}\{(}\{)}", false),
    (fun n => s!"\\defineenv\{{n}}(a1: content) \{(} \{)}", false),
    (fun n => s!"\\newtheorem\{{n}}\{Probe}", true),
    (fun n => s!"\\newtheorem\{{n}}\{Probe}[section]", false),
    (fun n => s!"\\newtheorem*\{{n}}\{Probe}", false)]
  for (definer, eats) in definers do
    let src := doc "\\usepackage{amsthm}\n" (para definer)
    let ds := dvE src
    t s!"a body definition ships the page without it: {definer "placeholder"}"
      (shipped src == shipped (doc "\\usepackage{amsthm}\n" (if eats then eaten
        else para fun _ => "{}")))
    t s!"a body definition is one warning, no error: {definer "placeholder"}"
      ((ds.filter (·.severity != .note)).all (·.code == "W0104") &&
        ds.any (fun d => d.code == "W0104" && !d.demoted) && ds.all (·.severity != .error))
  let inline := doc "" "Charlie \\textbf{delta \\newcommand{\\probecmd}{Probe words} echo} foxtrot."
  t "a definition inside inline content sets nothing of itself"
    (shipped inline == shipped (doc "" "Charlie \\textbf{delta {} echo} foxtrot.") &&
      (dvE inline).any (·.code == "E0312"))
  let defaults := doc ("\\NewEnviron{probeenv}[2][Edflt]{[#1/#2/\\BODY]}\n" ++
      "\\newenvironment{probeold}[2][Odflt]{(#1/#2)}{}\n" ++
      "\\NewEnviron{probehide}[1][Hdflt]{(#1)}\n" ++
      "\\newenvironment{proberedef}[2][Rdflt]{(#1/#2)}{}\n" ++
      "\\renewenvironment{proberedef}[2]{(#1/#2)}{}\n")
    ("A \\begin{probeenv}{q}Inner\\end{probeenv} B\n\n" ++
      "C \\begin{probeenv}[p]{q}Inner\\end{probeenv} D\n\n" ++
      "E \\begin{probeold}{q}Inner\\end{probeold} F\n\n" ++
      "G \\begin{probeold}[p]{q}Inner\\end{probeold} H\n\n" ++
      "I \\begin{probehide}Hidden\\end{probehide} J\n\n" ++
      "K \\begin{probehide}[g]Hidden\\end{probehide} L\n\n" ++
      "M \\begin{proberedef}{q}{r}Inner\\end{proberedef} N\n\n" ++
      "O \\begin{probeold}\n[s]{q}Inner\\end{probeold} P")
  t "an absent optional argument takes its definition's default"
    (sets defaults "A [Edflt/q/Inner]B" && sets defaults "E (Odflt/q)Inner F" &&
      sets defaults "I (Hdflt)J")
  t "a given optional argument stands in place of the default"
    (sets defaults "C [p/q/Inner]D" && sets defaults "G (p/q)Inner H" && sets defaults "K (g)L")
  t "a redefinition without a default leaves none" (sets defaults "M (q/r)Inner N")
  t "an optional argument on the line after the begin is the argument"
    (sets defaults "O (s/q)Inner P")
  let grouped := doc ("\\allow{E0313}\n\\NewEnviron{placeholder}{[\\BODY]}\n" ++
      "{\\RenewEnviron{placeholder}{}}\n" ++
      "\\newenvironment{probeold}[1]{(#1)}{}\n{\\renewenvironment{probeold}[1][Gdflt]{(#1)}{}}\n")
    ("Alpha \\begin{placeholder}Inner words\\end{placeholder} omega.\n\n" ++
      "Beta \\begin{probeold}{q}Inner\\end{probeold} gamma.")
  t "an environment definition inside a group ends with the group"
    (sets grouped "Alpha [Inner words]omega." && sets grouped "Beta (q)Inner gamma." &&
      (dvE grouped).all fun d => d.severity != .error || d.code == "E0313")
  let primitive := doc ("\\NewEnviron{placeholder}{[\\BODY]}\n\\bgroup\\relax\\egroup\n" ++
      "{\\RenewEnviron{placeholder}{}}\n")
    "Alpha \\begin{placeholder}Inner words\\end{placeholder} omega."
  t "a group after a grouping primitive is a group, which ends a definition"
    (sets primitive "Alpha [Inner words]omega.")
  let skippedArgs : List (String × String) := [
    ("\\usepackage{etoolbox}\n\\newtoggle{probesol}\n\\togglefalse{probesol}\n",
      "\\iftoggle{probesol}{\\NewEnviron{probehide}{\\textbf{S:} \\BODY}}" ++
        "{\\NewEnviron{probehide}{}}"),
    ("\\usepackage{ifthen}\n\\newboolean{probesol}\n\\setboolean{probesol}{false}\n",
      "\\ifthenelse{\\boolean{probesol}}{\\NewEnviron{probehide}{\\textbf{S:} \\BODY}}" ++
        "{\\NewEnviron{probehide}{}}"),
    ("", "\\IfFileExists{environ.sty}{\\NewEnviron{probehide}{}}{}"),
    ("\\makeatletter\n", "\\@ifundefined{probehide}{\\NewEnviron{probehide}{}}{}\n\\makeatother"),
    ("\\usepackage{etoolbox}\n", "\\ifdef{\\NewEnviron}{\\NewEnviron{probehide}{}}{}")]
  for (pre, call) in skippedArgs do
    let text := pageTextOf fonts (doc (pre ++ call ++ "\n")
      "Question words.\n\\begin{probehide}Hidden words\\end{probehide}\nAfter words.")
    t s!"a skipped command's argument braces end no definition: {call}"
      (hasStr text "Question words." && hasStr text "After words." && !hasStr text "Hidden")
  let gap (pre : String) : String :=
    dvDoc pre ("Alpha words in the first paragraph.\n\\bigskip\n\n" ++
      "Bravo words in the second paragraph.")
  for pre in ["\\newenvironment{probed}[1][\\setlength{\\bigskipamount}{4cm}]{#1 }{}\n",
      "\\usepackage{environ}\n" ++
        "\\NewEnviron{probed}[1][\\setlength{\\bigskipamount}{4cm}]{[#1/\\BODY]}\n",
      "\\newenvironment{probed}[1][\\setlength{\\parindent}{3cm}]{#1 }{}\n"] do
    t s!"an unused default sets nothing and says nothing where its definition stands: {pre}"
      (shippedLines fonts (gap pre) == shippedLines fonts (gap "") &&
        (dvE (gap pre)).all (·.severity == .note))
  let builtins := doc ("\\usepackage{amsthm}\n\\renewenvironment{quote}[1][Qdflt]{(#1:}{)}\n" ++
      "\\renewenvironment{center}[1][Cdflt]{<#1:}{>}\n" ++
      "\\renewenvironment{proof}[1][\\proofname]{\\par\\noindent\\textbf{#1.} }{\\qed\\par}\n")
    ("A \\begin{quote}x\\end{quote} B\n\nC \\begin{center}y\\end{center} D\n\n" ++
      "\\begin{proof}Proof words.\\end{proof}")
  let builtinText := pageTextOf fonts builtins
  t "a built-in's ignored definition gives none of its default to the built-in"
    (!hasStr builtinText "Qdflt" && !hasStr builtinText "Cdflt" && hasStr builtinText "AxB" &&
      hasStr builtinText "Proof.Proof words." &&
      (dvE builtins).all (·.code != "W0301"))
  let walked := dvDoc ("\\usepackage{csquotes}\n\\usepackage{environ}\n" ++
      "\\newenvironment{probequote}[1][\\enquote{Qd}]{(#1:}{)}\n" ++
      "\\NewEnviron{probebar}[1][Bx\\textbar y]{[#1/\\BODY]}\n" ++
      "\\newenvironment{probememo}[1][\\today]{(#1:}{)}\n")
    ("E \\begin{probequote}x\\end{probequote} F I \\begin{probebar}x\\end{probebar}J " ++
      "M \\begin{probememo}x\\end{probememo} N")
  t "a default is rewritten where its definition stands, as a given argument is"
    (sets walked "E (“Qd”:x) F" && sets walked "I [Bx|y/x]J" &&
      (dvE walked).any (·.code == "W0104") && (dvE walked).all (·.code != "W0301"))
  let late := dvDoc ("\\newenvironment{probeold}[1][Adflt]{(#1:}{)}\n" ++
      "\\newcommand{\\probeuse}{\\begin{probeold}x\\end{probeold}}\n" ++
      "\\renewenvironment{probeold}[1][Bdflt]{(#1:}{)}\n" ++
      "\\newenvironment{probelate}[1]{<#1:}{>}\n" ++
      "\\newcommand{\\probeusel}{\\begin{probelate}{q}x\\end{probelate}}\n" ++
      "\\renewenvironment{probelate}[1][Ldflt]{<#1:}{>}\n")
    "A \\probeuse{} B\n\nE \\probeusel{} F"
  t "a use through a macro takes the default of the definition in force at its use"
    (sets late "A (Bdflt:x) B" && sets late "E <Ldflt:qx> F")
  let hooked := dvDoc ("\\usepackage{etoolbox}\n" ++
      "\\AtBeginDocument{\\newenvironment{probeold}[1][Hd]{(#1:}{)}" ++
      "\\newtheorem{probethm}{Probe}}\n" ++
      "\\AtEndPreamble{\\newenvironment{probeend}[1][Ed]{<#1:}{>}}\n")
    ("A \\begin{probeold}x\\end{probeold} B \\begin{probeend}y\\end{probeend} C\n\n" ++
      "\\begin{probethm}Theorem words.\\end{probethm}")
  t "a definition a hook makes stands as the preamble's, its default with it"
    (sets hooked "A (Hd:x) B <Ed:y> C" && sets hooked "Probe 1Theorem words." &&
      (dvE hooked).all fun d => d.code != "W0104" && d.code != "W0302")
  let reached := doc ("\\newcommand{\\mkthm}{\\newtheorem{probethm}{Probe}}\n" ++
      "\\newcommand{\\mkenv}{\\newenvironment{probeenv}{(}{)}}\n")
    ("Alpha \\mkthm{} bravo.\n\nCharlie \\mkenv{} delta.\n\n" ++
      "Echo words.\n\\theoremstyle{definition}\\newtheorem{probedef}{Probe}[section]\n" ++
      "Foxtrot words.")
  let reachedText := pageTextOf fonts reached
  t "a body definition a macro or a theorem style leads to sets no text of itself"
    (hasStr reachedText "Alpha  bravo." && hasStr reachedText "Charlie  delta." &&
      hasStr reachedText "Foxtrot words." && !hasStr reachedText "robe" &&
      !hasStr reachedText "definition")
  let kept := doc ("\\usepackage{amsthm}\n\\newenvironment{probenote}[1]{\\textbf{#1:} }{}\n" ++
      "\\newtheorem{probethm}{Probe}\n")
    ("\\begin{probenote}{Pre}first use\\end{probenote}\n\n" ++
      "\\newenvironment{probenote}[1]{\\textit{#1!} }{}\n\\newtheorem{probethm}{Other}\n" ++
      "\\newenvironment{itemize}{(}{)}\n\\newenvironment{quote}{(}{)}\n\n" ++
      "\\begin{probenote}{Again}second use\\end{probenote}\n\n" ++
      "\\begin{probethm}Theorem words.\\end{probethm}\n\n" ++
      "\\begin{itemize}\\item Item words.\\end{itemize}\n\n\\begin{quote}Quoted words.\\end{quote}")
  let keptText := pageTextOf fonts kept
  t "a body definition of a defined environment leaves its definition, as LaTeX does"
    (hasStr keptText "Again:" && hasStr keptText "second use" && hasStr keptText "Probe 1" &&
      !hasStr keptText "Other" && !hasStr keptText "(" && !hasStr keptText "!" &&
      (dvE kept).all fun d => d.severity != .error && d.code != "W0302")
  let native := dvDoc ""
    ("Alpha words.\n\\defineenv{probex}(a1: content) {(\\a1} {)}\nBravo words.\n\n" ++
      "India \\begin{probex}{q}x\\end{probex} juliet.")
  t "a native body definition's use with an argument ships it plainly"
    (hasStr (pageTextOf fonts native) "India q x juliet." &&
      (dvE native).all (·.severity != .error))
  let unapplied := doc ""
    ("Alpha words.\n\n\\newenvironment{probenote}[1]{\\textbf{#1:} }{}\n" ++
      "\\NewEnviron{probehide}{}\n" ++
      "\\newtheorem{probethm}{Probe}\n\n\\begin{probenote}{Note}words here\\end{probenote}\n\n" ++
      "\\begin{probehide}Hidden words\\end{probehide}\n\n" ++
      "\\begin{probethm}Theorem words\\end{probethm}")
  let unappliedText := pageTextOf fonts unapplied
  let unappliedDs := dvE unapplied
  let unknownAt (n : String) : Bool :=
    unappliedDs.any fun d => d.code == "W0302" && d.subject == some ("env:" ++ n) && !d.demoted
  t "an unapplied body definition's uses set their arguments and body plainly, or nothing"
    (hasStr unappliedText "Note words here" && hasStr unappliedText "Theorem words" &&
      !hasStr unappliedText "Hidden" && unappliedDs.all (·.severity != .error))
  t "an unapplied body definition's plain use is a degraded unknown environment"
    (unknownAt "probenote" && unknownAt "probethm" && !unknownAt "probehide" &&
      DiagCode.W0302.loss == .degraded)

/-- environ's `\NewEnviron` defines the environment it names, as the kernel spelling with the body
at `\BODY`. -/
def environChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let use := "\\begin{placeholder}Middle words\\end{placeholder}"
  let doc (pre body : String) : String := dvDoc ("\\usepackage{environ}\n" ++ pre) body
  -- Each expected line is lualatex's own, spaces included, so a glued seam fails.
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
  -- TeX ends a control word at the space after it: `\BODY Tail` puts no space before the tail.
  let renew := doc "\\RenewEnviron{placeholder}{\\BODY Tail words}\n" use
  t "RenewEnviron is the same definer"
    (shippedLines fonts renew ==
      shippedLines fonts (doc "\\renewenvironment{placeholder}{}{Tail words}\n" use) &&
     sets renew "Middle wordsTail words")
  let spaced := "\\begin{placeholder} Middle words \\end{placeholder}\n\n" ++
    "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
  t "a spaced body at spaced halves sets two spaces at each seam"
    (sets (doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" spaced)
        "Lead words  Middle words  Tail words" &&
     sets (doc "\\newenvironment{placeholder}{Lead words }{ Tail words}\n" spaced)
        "Inline Lead words  Middle words  Tail words after.")
  let boxed := doc "\\NewEnviron{placeholder}{\\fbox{\\BODY}}\n" use
  t "a body placed inside a group is refused in place, nothing leaking"
    ((dvE boxed).any (fun d => d.code == "W0104" && hasStr d.message "inside a group") &&
      !hasStr (pageTextOf fonts boxed) "BODY" && hasStr (pageTextOf fonts boxed) "Middle words")
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
  let redefined := doc
    "\\NewEnviron{placeholder}[1]{[#1]}\n\\RenewEnviron{placeholder}[2]{[#1|#2]}\n"
    "Before \\begin{placeholder}{alpha}{beta}Hidden words\\end{placeholder} after."
  t "a discarding redefinition reads the arguments its own signature takes"
    (sets redefined "Before [alpha|beta]after." && !hasStr (pageTextOf fonts redefined) "Hidden")
  let unrun (redef : String) : String := doc
    s!"\\NewEnviron\{placeholder}[1]\{[#1]}\n\\newcommand\{\\unused}\{{redef}}\n"
    "Before \\begin{placeholder}{alpha}{beta}Hidden words\\end{placeholder} after."
  t "a redefinition in a definition never run leaves the environment as it stands"
    (sets (unrun "\\RenewEnviron{placeholder}[2]{[x|y]}") "Before [alpha]after." &&
      sets (unrun "\\renewenvironment{placeholder}{(}{)}") "Before [alpha]after.")
  let run := doc ("\\newenvironment{placeholder}{}{}\n" ++
    "\\newcommand{\\hide}{\\RenewEnviron{placeholder}{}}\\hide\n") use
  t "a redefinition in a definition that is run takes effect where it runs"
    (!hasStr (pageTextOf fonts run) "Middle words" &&
      !((dvE run).any fun d => ["W0104", "W0301", "W0302"].contains d.code))
  let finalOnly := doc "\\NewEnviron{placeholder}{Lead words}[ Tail words]\n"
    "Alpha words.\n\n\\begin{placeholder}Hidden words\\end{placeholder}\n\nBravo words."
  t "a final code with a BODY-less code ends the environment, body hidden"
    (sets finalOnly "Lead words Tail words" && !hasStr (pageTextOf fonts finalOnly) "Hidden" &&
      !((dvE finalOnly).any fun d => ["W0104", "W0301", "W0302"].contains d.code))
  let trimmed := "Before \\begin{placeholder} Middle words \\end{placeholder} after.\n\n" ++
    "\\begin{placeholder}\nOther words\n\\end{placeholder}"
  t "environ trims the body's edge spaces and those after the end"
    (sets (doc "\\NewEnviron{placeholder}{(\\BODY)}\n" trimmed) "Before (Middle words)after." &&
      sets (doc "\\NewEnviron{placeholder}{(\\BODY)}\n" trimmed) "(Other words)")
  t "a given final code replaces the skip after the end"
    (sets (doc "\\NewEnviron{placeholder}{(\\BODY}[)]\n" trimmed) "Before (Middle words) after.")
  let ownBody := "\\newcommand{\\BODY}{Inner words}\n" ++
    "\\newenvironment{placeholder}{Lead \\BODY{} }{ Tail words}\n"
  for src in [dvDoc ownBody use, doc ownBody use] do
    t "a document's own BODY macro in a kernel definition is the macro"
      (!((dvE src).any (·.severity == .error)) &&
        sets src "Lead Inner words Middle words Tail words")


/-- algorithm2e's `\SetKw` family: a later definition of a keyword wins, as the package's does. -/
def algKeywordChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String := dvDoc ("\\usepackage[ruled]{algorithm2e}\n" ++ pre)
    s!"\\begin\{algorithm}\n{body}\\end\{algorithm}"
  let sets (src line : String) : Bool := hasStr (pageTextOf fonts src) line
  t "a preamble keyword defined twice sets its later word"
    (sets (doc "\\SetKw{Probe}{first}\n\\SetKw{Probe}{second}\n" "\\Probe alpha\\;\n")
      "second alpha;")
  t "a keyword redefined partway sets each line under the definition in force there"
    (sets (doc "" ("\\SetKw{Probe}{first}\n\\Probe alpha\\;\n\\SetKw{Probe}{second}\n" ++
      "\\Probe beta\\;\n")) "first alpha;second beta;")
  t "an algorithm's own keywords replace the package's and its earlier ones"
    (sets (doc "" ("\\SetKw{KwTo}{until}\n\\SetKw{Probe}{first}\n\\SetKw{Probe}{second}\n" ++
      "\\Probe alpha \\KwTo beta\\;\n")) "second alpha until beta;")

/-- The judge of `abstractSkipsOwed`: the page under two declared heading gaps. -/
def abstractSkipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let venue (gap : String) : String :=
    "\\documentclass{article}\\renewenvironment{abstract}{\\centerline{\\large\\bf Abstract}" ++
      "\\vspace{" ++ gap ++ "}\\begin{quote}}{\\par\\end{quote}}" ++
      "\\begin{document}\\begin{abstract}Placeholder summary words.\\end{abstract}\n\n" ++
      "Plain body words after.\\end{document}"
  let ignored := shippedLines fonts (venue "1ex") == shippedLines fonts (venue "4ex")
  check ref "a redefined abstract's declared skips are owed (parked)"
    (ignored == abstractSkipsOwed)
  check ref "the refusal names the engine-placed skips exactly while owed"
    (((dvE (venue "1ex")).any fun d =>
      d.code == "W0303" && hasStr d.message "vertical skips") == abstractSkipsOwed)


/-- A seam sets the spaces TeX sets there: two space tokens from two sources set two interword
glues. -/
def seamChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let width (pre body : String) : Option Dim.Sp :=
    ((censusOfSrc fonts (dvDoc pre body))[0]?.bind (·.lines.find? (!·.furniture))).map (·.width)
  let same (pre body spelled : String) : Bool :=
    (width pre body).isSome && width pre body == width "" spelled
  t "two control spaces a macro brings set two spaces"
    (same "\\newcommand{\\gap}{\\ }\n" "Alpha\\gap\\gap Bravo words." "Alpha\\ \\ Bravo words." &&
      width "" "Alpha\\ \\ Bravo words." != width "" "Alpha Bravo words.")
  t "a body's closing control space and the one after its use set two"
    (same "\\newcommand{\\probeword}{word\\ }\n" "Lead \\probeword\\ next words."
      "Lead word\\ \\ next words.")
  t "a group's closing space and the space after the group set two"
    (same "" "Lead {word } next words." "Lead word\\ \\ next words.")
  t "an environment half's spaced edge and its body's set two at each seam"
    (same "\\newenvironment{placeholder}{Lead words }{ Tail words}\n"
      "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
      "Inline Lead words\\ \\ Middle words\\ \\ Tail words after.")
  t "the blanks after a control space are skipped"
    (same "" "Alpha\\  Bravo words." "Alpha\\ Bravo words.")
  let lead := "\\newenvironment{placeholder}{Lead words \\ignorespaces}{ Tail words}\n"
  let after := "\\newenvironment{placeholder}{Lead words }{ Tail words\\ignorespacesafterend}\n"
  let use := "Inline \\begin{placeholder} Middle words \\end{placeholder} after."
  t "ignorespaces closing a begin code skips the body's leading spaces"
    (same lead use "Inline Lead words Middle words\\ \\ Tail words after." &&
      !((dvE (dvDoc lead use)).any (·.code == "W0301")))
  t "ignorespacesafterend skips the spaces after the environment's end"
    (same after use "Inline Lead words\\ \\ Middle words\\ \\ Tail wordsafter." &&
      !((dvE (dvDoc after use)).any (·.code == "W0301")))

/-- A built-in the engine ignores every definition of, defined through each definer from a style
file: one refusal at the definition's site accounts for it, its lossy text raises nothing and the
built-in's page stands. -/
def ignoredDefinitionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let definitions : List (String × String) :=
    [("NewDocumentCommand", "\\NewDocumentCommand{\\varul}{m}{\\ifmmode\\underline{#1}\\else#1\\fi}"),
     ("RenewDocumentCommand", "\\RenewDocumentCommand{\\underline}{m}{\\raisebox{1pt}[0pt][0pt]{#1}}"),
     ("newcommand", "\\newcommand{\\sout}[1]{\\setlength{\\fboxsep}{2pt}#1}"),
     ("renewcommand", "\\renewcommand{\\ul}[1]{\\newcommand{\\zzinner}{#1}\\zzinner}"),
     ("DeclareRobustCommand", "\\DeclareRobustCommand{\\uline}[1]{\\ifmmode#1\\fi}"),
     ("def", "\\def\\varul#1{\\raisebox{1pt}[0pt][0pt]{#1}}"),
     ("renewenvironment", "\\renewenvironment{itemize}{\\ifmmode x\\fi}{\\setlength{\\fboxsep}{2pt}}"),
     ("newenvironment", "\\newenvironment{verbatim}{\\raisebox{1pt}[0pt][0pt]{x}}{}")]
  let body := "Alpha \\varul{bravo} \\sout{charlie} \\ul{delta} \\uline{echo} \\underline{golf}.\n" ++
    "\\begin{itemize}\\item Foxtrot words.\\end{itemize}"
  let source (pre : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"
  let pagesOfDoc (doc : Ir.Doc) : String := reprStr (layoutOf fonts doc).pages
  let base := pagesOfDoc (elabStr (source "")).1
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    for (definer, line) in definitions do
      IO.FS.writeFile (dir / "zzbuiltin.sty") (line ++ "\n")
      let (toks, ld) := Lex.lex file (source "\\usepackage{zzbuiltin}")
      let (raws, pd) := Parse.parse file toks
      let (executed, ids, _) ← LeanTex.Cli.Input.expandInputs file raws
      let (doc, ds) := Elab.runExecuted file executed (ld ++ pd ++ ids)
      let mine := ds.filter (·.span.any (·.file.endsWith "zzbuiltin.sty"))
      t s!"ignored definitions: a '\\{definer}' of a built-in is its one refusal, at its site"
        (mine.size == 1 && mine.all fun d => d.code == "W0303" && d.span.any (·.pos.line == 1))
      t s!"ignored definitions: a '\\{definer}' of a built-in leaves the built-in's page"
        (pagesOfDoc doc == base)
      let (_, inline) := elabStr (source line)
      t s!"ignored definitions: a '\\{definer}' of a built-in in the preamble is its one refusal"
        ((inline.filter (·.span.any (·.pos.line == 2))).map (·.code) == #["W0303"])
