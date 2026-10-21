module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim LeanTex.Cli

/-! A document's local class is read as a local style is, on the class it loads. -/

/-- Every body line's text, place and size. -/
private def linePlaces (out : Layout.Out) : Array (String × Length × Length × Length) :=
  (bodyLines out).map fun l => (lineText l, l.x, l.y, l.size)

/-- The invented paper the class fixtures share, under a class line and preamble of its own. -/
private def inventedPaper (classLine preamble body : String) : String :=
  classLine ++ "\n" ++ preamble ++ "\\title{An Invented Result}\n\\author{Ada Example}\n" ++
    "\\begin{document}\n\\maketitle\n\\section{Opening}\n" ++ body ++ "\n\\end{document}\n"

/-- The diagnostics with code `code` sited in `file`. -/
private def sitedIn (ds : Array Diag) (code file : String) : Array Diag :=
  ds.filter fun d => d.code == code && d.span.any (·.file == file)

/-- A local class schedules its options, loads its base as the class line, and sets every line
where that class line sets it; a class it cannot load stands on the article model, named once. -/
def localClassChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let places (src : String) : Array (String × Length × Length × Length) :=
    linePlaces (layoutOf fonts (elabStr src).1)
  let letterDefs := "\\newcommand{\\journalname}{Invented Letters}\n" ++
    "\\newcommand{\\keywords}[1]{\\par\\noindent\\textbf{Keywords:} #1}\n"
  let (letters, lettersDs, lettersRead) ← runStyParity "cls-letters"
  let lettersText := String.join ((bodyLines (layoutOf fonts letters)).toList.map (lineText ·))
  t "a local class is read, not refused as an unknown class"
    (!lettersDs.any (·.code == "E0309") && lettersRead.any (·.1 == "inventedletters.cls"))
  t "a declared class option runs its handler, and the class's commands set their text"
    (hasStr lettersText "Invented Letters" && hasStr lettersText "Review copy" &&
      hasStr lettersText "Keywords:" && !hasStr lettersText "Final copy")
  t "the options the class passes on reach the class it loads, each by its own name"
    (linePlaces (layoutOf fonts letters) == places (inventedPaper
      "\\documentclass[12pt,twocolumn]{article}" letterDefs
      "Widgets turn. \\journalname. Review copy.\n\\keywords{widgets, gadgets}"))
  t "the read class is noted once at its class line"
    ((lettersDs.filter fun d => d.code == "N0020" &&
      (d.message.splitOn "inventedletters.cls").length > 1).size == 1)
  let (plain, plainDs, _) ← runStyParity "cls-plain"
  t "a class loading its base without options leaves the document's options to no class"
    (linePlaces (layoutOf fonts plain) ==
      places (inventedPaper "\\documentclass{article}" "" "Widgets turn."))
  t "each option a class neither handles nor passes on is named once, at the class"
    ((sitedIn plainDs "W0110" "inventedplain.cls").size == 2)
  let (with_, withDs, _) ← runStyParity "cls-with"
  t "a class loading its base with its options sets the page that class line sets"
    (linePlaces (layoutOf fonts with_) ==
      places (inventedPaper "\\documentclass[12pt,twocolumn]{article}" "" "Widgets turn."))
  t "options a class passes on whole are no class's unused options"
    ((sitedIn withDs "W0110" "inventedwith.cls").isEmpty)
  let (nest, nestDs, nestRead) ← runStyParity "cls-nest"
  t "a local class may load another local class, which loads its own base"
    (nestRead.map (·.1) == #["inventednest.cls", "inventedletters.cls"] &&
      !nestDs.any (·.code == "E0309") && !nestDs.any (·.code == "W0110"))
  t "the nested class's options reach the base, and its redefinitions stand"
    (linePlaces (layoutOf fonts nest) == places (inventedPaper "\\documentclass[12pt]{article}"
      "\\newcommand{\\journalname}{Invented Nested Letters}\n" "Widgets turn. \\journalname."))
  let (scratch, scratchDs, _) ← runStyParity "cls-scratch"
  t "a class loading no class stands on the article model, named once"
    (linePlaces (layoutOf fonts scratch) == places (inventedPaper "\\documentclass{article}"
      "\\newcommand{\\journalname}{Invented Scratch}\n" "Widgets turn. \\journalname.") &&
      (scratchDs.filter fun d => d.code == "N0100" &&
        (d.message.splitOn "inventedscratch").length > 1).size == 1)
  let (base, baseDs, _) ← runStyParity "cls-base"
  t "a base class with no file and no model is the class file's refusal, the class's commands kept"
    ((sitedIn baseDs "E0309" "inventedbase.cls").size == 1 &&
      baseDs.all (fun d => d.code != "E0309" || d.span.any (·.file == "inventedbase.cls")) &&
      hasStr (String.join ((bodyLines (layoutOf fonts base)).toList.map (lineText ·)))
        "Invented Base")
  t "a class the engine models reads no file of its name"
    (Compat.modeledClass "article" && Compat.modeledClass "report" &&
      Compat.modeledClass "beamer" && !Compat.modeledClass "inventedletters")

/-- Every body line's text, in page order. -/
private def bodyTexts (out : Layout.Out) : Array String := (bodyLines out).map (lineText ·)

/-- The index of the first line holding `s`. -/
private def lineAt (lines : Array String) (s : String) : Option Nat :=
  lines.findIdx? fun l => hasStr l s

/-- A journal class sets its gathered top matter under its title: every author, address and
key-word line, and the abstract written before `\maketitle`; `\and` keeps authors apart, and an
engine test answers as lualatex does. -/
def journalClassChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let paper (cls top : String) : String :=
    s!"\\documentclass\{{cls}}\n\\title\{An Invented Result}\n" ++ top ++
      "\\begin{document}\n\\begin{abstract}\nInvented summary words.\n\\end{abstract}\n" ++
      "\\maketitle\n\\section{Opening}\nWidgets turn.\n\\end{document}\n"
  let ams := paper "amsart" ("\\author{Ada Example}\n\\address{Example Institute}\n" ++
    "\\email{ada@example.org}\n\\author{Bea Sample}\n\\address{Sample University}\n" ++
    "\\subjclass[2020]{Primary 05C10}\n\\keywords{widgets, gadgets}\n")
  let (amsDoc, amsDs) := elabStr ams
  let amsLines := bodyTexts (layoutOf fonts amsDoc)
  t "an AMS paper names no unknown class and no unknown top-matter command"
    (!amsDs.any (·.code == "E0309") && !amsDs.any (·.code == "W0301"))
  t "every author is set, joined as amsart joins them"
    ((lineAt amsLines "Ada Example and Bea Sample").isSome)
  t "every address and e-mail address is set"
    ((lineAt amsLines "Example Institute").isSome && (lineAt amsLines "Sample University").isSome &&
      (lineAt amsLines "ada@example.org").isSome)
  t "the abstract written before the title is set under it, the key-word lines after it"
    (match lineAt amsLines "An Invented Result", lineAt amsLines "Invented summary words",
        lineAt amsLines "Key words and phrases.", lineAt amsLines "Opening" with
      | some ti, some ab, some kw, some op => ti < ab && ab < kw && kw < op
      | _, _, _, _ => false)
  t "the subject classification line names its scheme's year"
    ((lineAt amsLines "2020 Mathematics Subject Classification.").isSome)
  let acm := paper "acmart" ("\\author{Ada Example}\n" ++
    "\\affiliation{\\institution{Example Institute}\\city{Springfield}\\country{Utopia}}\n" ++
    "\\author{Bea Sample}\n\\affiliation{\\institution{Sample University}" ++
    "\\streetaddress{1 Main St}\\country{Utopia}}\n\\keywords{widgets}\n")
  let (acmDoc, acmDs) := elabStr acm
  let acmLines := bodyTexts (layoutOf fonts acmDoc)
  t "an ACM paper names no unknown class, command or environment"
    (!acmDs.any (·.code == "E0309") && !acmDs.any (·.code == "W0301"))
  t "an ACM affiliation sets its institution, then its place, and no street address"
    ((lineAt acmLines "Springfield, Utopia").isSome &&
      (lineAt acmLines "Sample University").isSome && (lineAt acmLines "1 Main St").isNone)
  t "an ACM key-word line follows the abstract"
    (match lineAt acmLines "Invented summary words", lineAt acmLines "Keywords:" with
      | some ab, some kw => ab < kw
      | _, _ => false)
  let (thmDoc, thmDs) := elabStr ("\\documentclass{acmart}\n\\begin{document}\n" ++
    "\\section{Opening}\n\\begin{theorem}Widgets turn.\\end{theorem}\n" ++
    "\\begin{definition}A widget turns.\\end{definition}\n\\end{document}\n")
  let thmLines := bodyTexts (layoutOf fonts thmDoc)
  t "acmart's theorem environments are declared, numbered within the section"
    (!thmDs.any (·.code == "W0302") && (lineAt thmLines "Theorem 1.1.").isSome &&
      (lineAt thmLines "Definition 1.2.").isSome)
  let gaps (src : String) : Dim.Length :=
    let lines := bodyLines (layoutOf fonts (elabStr src).1)
    match lines.find? fun l => hasStr (lineText l) "Ada" with
    | some l => l.segs.foldl (init := 0) fun w seg => match seg with
        | .gap g _ => w + g
        | _ => w
    | none => 0
  let authors (a : String) : String :=
    s!"\\documentclass\{article}\n\\title\{T}\n\\author\{{a}}\n" ++
      "\\begin{document}\n\\maketitle\nx\n\\end{document}\n"
  t "\\and sets authors apart by at least LaTeX's 1em and both column paddings"
    (gaps (authors "Ada Example \\and Bea Sample") ≥
      gaps (authors "Ada Example Bea Sample") + Dim.pt 22 - Dim.pt 4)
  let engine (test : String) : String :=
    pageTextOf fonts (dvDoc "" s!"\\{test} Yes\\else No\\fi")
  t "an engine test answers as lualatex answers it"
    (engine "ifluatex" == "Yes" && engine "ifLuaTeX" == "Yes" && engine "ifpdf" == "Yes" &&
      engine "ifPDFTeX" == "No" && engine "ifxetex" == "No" && engine "ifXeTeX" == "No")
