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
