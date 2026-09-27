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


mutual

/-- The text of every `<strong>` element of an emitted tree. -/
def strongTextsOne (acc : Array String) : Html.Node → Array String
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := if t == "strong" then acc.push (nodeTextOne "" (.elem t attrs kids)) else acc
    strongTextsList acc kids.toList

def strongTextsList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | k :: rest => strongTextsList (strongTextsOne acc k) rest

end

/-- **A group primitive scopes what a brace pair scopes.** A weight change
between `\begingroup` and `\endgroup` (or `\bgroup` and `\egroup`) reaches
the words inside and stops at the closer, read off the typed HTML tree.
The defect: both words were unknown commands, dropped as text, so the
change leaked to the paragraph's end and a reader saw words bold that
LaTeX sets upright. Quantified over `Compat.groupPrimitives`. -/
def groupPrimitiveChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (o, c) in Compat.groupPrimitives do
    let (doc, ds) := elabStr
      (dvDoc "" s!"Before words. \\{o}\\bfseries Inside words.\\{c} After words.")
    let (_, body, _) := HtmlDoc.emitTree {} doc
    let strong := strongTextsList #[] body.toList
    t s!"'\\{o}' scopes a weight change over its own words"
      (strong.any (hasStr · "Inside words."))
    t s!"and the change stops at '\\{c}'" (strong.all fun s => !hasStr s "After words.")
    t s!"a matched '\\{o}' is no unknown command" (ds.all (·.code != "W0301"))
