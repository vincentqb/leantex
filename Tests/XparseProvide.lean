module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- `\ProvideDocumentCommand` binds only an undefined command; an existing meaning survives and the
unused body neither runs nor inks. -/
def xparseProvideChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let article (pre body : String) :=
    "\\documentclass{article}\\usepackage{xparse}" ++ pre ++
      "\\begin{document}" ++ body ++ "\\end{document}"
  let samePage (label source control ink : String) : IO Unit := do
    let (doc, ds) := elabStr source
    let (expected, expectedDs) := elabStr control
    let (head, tree, _) := HtmlDoc.emitTree {} doc
    let (expectedHead, expectedTree, _) := HtmlDoc.emitTree {} expected
    let page := layoutOf fonts doc
    let expectedPage := layoutOf fonts expected
    t s!"xparse provide {label}: recognised without a warning"
      (ds.all (·.severity == .note))
    t s!"xparse provide {label}: control is recognised without a warning"
      (expectedDs.all (·.severity == .note))
    t s!"xparse provide {label}: typed HTML preserves the command's meaning"
      (Html.document "en" head tree == Html.document "en" expectedHead expectedTree)
    t s!"xparse provide {label}: shipped layout preserves the command's meaning"
      (reprStr page.pages == reprStr expectedPage.pages)
    t s!"xparse provide {label}: the HTML witness reaches the reader"
      (hasStr (shownTextList "" tree.toList) ink)
    t s!"xparse provide {label}: the layout witness reaches the reader"
      ((bodyLines page).any fun line => hasStr (lineText line) ink)

  let fresh : Array (String × String × String × String × String) := #[
    ("zero arguments", "", "Chosen", "\\providedprobe", "Chosen"),
    ("mandatory argument", "m", "Chosen #1", "\\providedprobe{token}", "Chosen token"),
    ("optional argument", "m o", "\\textbf{#1}\\IfValueT{#2}{ (#2)}",
      "\\providedprobe{One}[Two] \\providedprobe{Three}", "One (Two) Three"),
    ("parameter order", "m m", "#2 then #1",
      "\\providedprobe{First}{Second}", "Second then First")]
  for (label, spec, body, call, ink) in fresh do
    let decl (definer : String) :=
      "\\" ++ definer ++ "{\\providedprobe}{" ++ spec ++ "}{" ++ body ++ "}"
    let source := article (decl "ProvideDocumentCommand") call
    samePage label source (article (decl "NewDocumentCommand") call) ink
    t s!"xparse provide {label}: the declaration is accounted by its own name"
      ((elabStr source).2.any fun d =>
        d.code == "N0100" && hasStr d.message "\\ProvideDocumentCommand")

  let definitions : Array (String × String) := #[
    ("xparse definition", "\\NewDocumentCommand{\\providedprobe}{m}{Existing #1}"),
    ("LaTeX definition", "\\newcommand{\\providedprobe}[1]{Existing #1}"),
    ("TeX definition", "\\def\\providedprobe#1{Existing #1}"),
    ("declared definition", "\\DeclareDocumentCommand{\\providedprobe}{m}{Existing #1}"),
    ("renewed definition", "\\NewDocumentCommand{\\providedprobe}{m}{First #1}" ++
      "\\RenewDocumentCommand{\\providedprobe}{m}{Existing #1}"),
    ("earlier provision", "\\ProvideDocumentCommand{\\providedprobe}{m}{Existing #1}")]
  let unused := "\\ProvideDocumentCommand{\\providedprobe}{D<>{UnusedDefault} +m}" ++
    "{\\unusedcommand{UnusedBody}\\newcommand{\\unusedbinding}{UnusedDefinition}}"
  for (label, pre) in definitions do
    let source := article (pre ++ unused) "\\providedprobe{token} Tail"
    samePage label source (article pre "\\providedprobe{token} Tail") "Existing token Tail"
    t s!"xparse provide {label}: keeping the existing definition is accounted"
      ((elabStr source).2.any fun d =>
        d.code == "N0100" &&
        d.subject == some "ctrl:nothing:ProvideDocumentCommand:providedprobe")

  samePage "body-side fresh definition"
    (article "" "Lead \\ProvideDocumentCommand{\\providedprobe}{m}{Chosen #1}\
      \\providedprobe{token} Tail")
    (article "" "Lead \\NewDocumentCommand{\\providedprobe}{m}{Chosen #1}\
      \\providedprobe{token} Tail") "Chosen token Tail"
  samePage "body-side existing definition"
    (article "\\newcommand{\\providedprobe}[1]{Existing #1}"
      ("Lead " ++ unused ++ "\\providedprobe{token} Tail"))
    (article "\\newcommand{\\providedprobe}[1]{Existing #1}"
      "Lead \\providedprobe{token} Tail") "Existing token Tail"

  let conditionalBody := "\\iftrue Unused\\fi"
  samePage "builtin unused conditional"
    (article ("\\ProvideDocumentCommand{\\textbf}{m}{" ++ conditionalBody ++ "}")
      "\\textbf{Kept token} Tail")
    (article "" "\\textbf{Kept token} Tail") "Kept token Tail"
  for (label, pre) in definitions do
    samePage (label ++ " unused conditional")
      (article (pre ++ "\\ProvideDocumentCommand{\\providedprobe}{m}{" ++
          conditionalBody ++ "}") "\\providedprobe{token} Tail")
      (article pre "\\providedprobe{token} Tail") "Existing token Tail"
    let call := "\\providedprobe{token} \\ifdefined\\unusedbinding Leaked\\else Kept\\fi{} Tail"
    samePage (label ++ " does not bind an unused nested definition")
      (article (pre ++ unused) call) (article pre call) "Existing token Kept Tail"

  let builtins : Array (String × String × String × String × String) := #[
    ("bold", "textbf", "", "\\textbf{Kept token} Tail", "Kept token Tail"),
    ("heading", "section", "", "\\section{Kept heading}Tail", "Kept heading"),
    ("paragraph", "par", "", "Before\\par After Tail", "After Tail"),
    ("title", "maketitle", "\\title{Kept title}\\date{}",
      "\\maketitle Tail", "Kept title")]
  for (label, cmd, pre, call, ink) in builtins do
    for body in #["", "\\unusedcommand{UnusedBody}"] do
      let provided := "\\ProvideDocumentCommand{\\" ++ cmd ++ "}{m}{" ++ body ++ "}"
      samePage (label ++ if body.isEmpty then " empty body" else " unused body")
        (article (pre ++ provided) call) (article pre call) ink

  let sectionBody := "\\@startsection{section}{1}{0pt}{5pt}{7pt}{\\itshape}"
  let call := "\\section{Kept heading}Body Tail"
  for definer in #["ProvideDocumentCommand", "providecommand"] do
    let spec := if definer == "ProvideDocumentCommand" then "{}" else ""
    let pre := "\\makeatletter\\" ++ definer ++ "{\\section}" ++ spec ++
      "{" ++ sectionBody ++ "}\\makeatother"
    samePage (definer ++ " ignores a heading idiom")
      (article pre call) (article "" call) "Kept heading"

end Tests
