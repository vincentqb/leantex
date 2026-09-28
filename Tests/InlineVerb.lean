import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- `\verb`: the text between two copies of its delimiter, on one line, is
code read raw — a control word inside it is text, never run — set in the
mono face within its paragraph, its spaces held (`\verb*` shows them as
U+2423); a delimiter with no second copy on its line is E0102, as LaTeX's
"\verb ended by end of line". -/
def inlineVerbChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body (s : String) := s!"\\documentclass\{article}\n\\begin\{document}\n{s}\n\\end\{document}"
  let code (s : String) : Ir.Inline := .styled .mono #[.text (s.map fun c => if c == ' ' then '\u00a0' else c)]
  let (d1, ds1) := elabStr (body "a \\verb|\\small x+y| b")
  t "\\verb keeps a control word as code, inline"
    (ds1.isEmpty && d1.body == #[.para #[.text "a ", code "\\small x+y", .text " b"]])
  let (d2, ds2) := elabStr (body "\\verb!a|b! and \\verb +{x}+.")
  t "\\verb takes any delimiter, after spaces"
    (ds2.isEmpty && d2.body == #[.para #[code "a|b", .text " and ", code "{x}", .text "."]])
  let (d3, ds3) := elabStr (body "\\verb*|a b| c")
  t "\\verb* shows its spaces"
    (ds3.isEmpty && d3.body == #[.para #[code "a␣b", .text " c"]])
  let (d4, _) := elabStr (body "\\verb|x| opens the paragraph")
  t "a paragraph opening with \\verb is one paragraph"
    (d4.body == #[.para #[code "x", .text " opens the paragraph"]])
  t "a \\verb with no closing delimiter on its line is E0102"
    ((elabStr (body "\\verb|abc\nnext")).2.map (·.code) == #["E0102"])
  match ← serifFacesSet with
  | none => failures ref "inline verb: the shipped serif faces did not load"
  | some fonts =>
    let shipped := pageTextOf fonts (body "see \\verb|\\section{A}| here")
    t "the page ships the code, not what it would run"
      (hasStr shipped "\\section{A}")
