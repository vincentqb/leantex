import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # A refusal never raises an error and never adds ink

A construct the engine refuses by name is named once and leaves the page as
the document without it would. Each block holds one refusal path to that
rule, over the shipped pages; the probes are synthetic. -/

/-- The split-group definition: an environment opened in the begin body and
closed in the end body, LaTeX's most common `\newenvironment` idiom. -/
def splitGroupDef (definer name : String) : String :=
  s!"\\{definer}\{{name}}\{\\begin\{center}\\small}\{\\end\{center}}\n"

/-- **A refused environment definition raises no error and ships no ink.**
Every built-in environment name, redefined with the split-group idiom,
builds: its only diagnostic at the definition is W0303, and the page is the
page of the document that never wrote the definition. The defect: the parse
judged the definition's two bodies as document text, so the idiom failed
the build (E0201, E0205) beside the W0303 that ignored it. Quantified over
`Elab.builtinEnvNames`, so a built-in the engine gains is a row. -/
def refusedEnvChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "Body words stand here."
  let plain := pageTextOf fonts (dvDoc "" body)
  for n in Elab.builtinEnvNames do
    let src := dvDoc (splitGroupDef "renewenvironment" n) body
    let ds := dvE src
    t s!"a split-group redefinition of '\{{n}}' raises no error"
      (ds.all (·.severity != .error))
    t s!"the redefinition of '\{{n}}' is named by W0303 alone"
      (ds.all fun d => d.severity == .note || d.code == "W0303")
    t s!"and the page is the page without it ('\{{n}}')"
      (pageTextOf fonts src == plain)

/-- **Parked: an accepted split-group definition is not paired yet.** The
engine elaborates an environment's two halves apart, each under its own
argument scope, so an environment one half opens and the other closes cannot
stand around the content: the definition keeps the parse's E0201 and E0205.
A row fails once pairing lands, and leaves with the fix. -/
def splitPairingOwed : List String := ["center"]

def splitPairingOwedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for n in splitPairingOwed do
    let src := dvDoc (s!"\\newenvironment\{probewrap}\{\\begin\{{n}}}\{\\end\{{n}}}\n")
      "\\begin{probewrap}Wrapped words.\\end{probewrap}"
    t s!"parked: a split '\{{n}}' in an accepted definition still raises E0201"
      ((dvE src).any (·.code == "E0201"))
