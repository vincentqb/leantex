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


/-- **A refused delimited definition's use ships what its braced spelling
ships.** TeX reads a delimited parameter up to its delimiter and consumes
the delimiter as the call's syntax; the engine refuses the definition
(W0357), and its use is then an unknown command whose arguments are kept as
text. Each row pairs a delimited use with the braced call it reads as, and
the pages must agree. The defect: the delimiter was left in the stream, so
the page showed punctuation nobody typed. -/
def delimitedUseChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\def\\probescan#1;{\\textbf{#1}}\n\\def\\probepair#1,#2\\relax{#2}\n" ++
    "\\def\\probewrap(#1){\\emph{#1}}\n"
  let rows := [
    ("Scanned: \\probescan Scanned words; tail words.",
     "Scanned: \\probescan{Scanned words} tail words."),
    ("Paired: \\probepair Left words,Right words\\relax\\ tail.",
     "Paired: \\probepair{Left words}{Right words}\\ tail."),
    ("Wrapped: \\probewrap(Inner words) tail.",
     "Wrapped: \\probewrap{Inner words} tail.")]
  for (delimited, braced) in rows do
    let page := pageTextOf fonts (dvDoc pre delimited)
    t s!"a delimited use ships its braced call's page: {delimited}"
      (page == pageTextOf fonts (dvDoc pre braced))
  t "the definitions stay refused by name"
    ((dvE (dvDoc pre "Body.")).any (·.code == "W0357"))


/-- The laid-out lines of a source, baseline and text: what a claim that two
spellings set one page reads. -/
def pageLines (fonts : Font.FontSet) (src : String) : Array (Array (Dim.Sp × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.text))

/-- **Register arithmetic on a length the document set is evaluated, not
skipped.** TeX's `\advance`, `\multiply`, `\divide` and LaTeX's
`\addtolength` change the value a later layout reads; skipping them left
the earlier value standing, silently, and a paragraph skip advanced by 20pt
set 19.9 bp short per paragraph. Each row pairs the arithmetic with the
literal value it computes, and the pages must agree; a length the rewrite
never set is still named and skipped (W0104). -/
def registerArithChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let paras := "First words.\n\nSecond words.\n\nThird words."
  let gap := "First words.\n\n\\vspace{\\probegap}\nSecond words."
  let tok := "\\newlength{\\probegap}\n\\newlength{\\probeb}\n\\setlength{\\probeb}{4pt}\n" ++
    "\\setlength{\\probegap}{6pt}\n"
  let rows := [
    (dvDoc "\\setlength{\\parskip}{2pt}\n\\advance\\parskip by 20pt\n" paras,
     dvDoc "\\setlength{\\parskip}{22pt}\n" paras),
    (dvDoc "\\setlength{\\parskip}{2pt}\n\\addtolength{\\parskip}{20pt}\n" paras,
     dvDoc "\\setlength{\\parskip}{22pt}\n" paras),
    (dvDoc (tok ++ "\\advance\\probegap by 6pt\n") gap,
     dvDoc (tok ++ "\\setlength{\\probegap}{12pt}\n") gap),
    (dvDoc (tok ++ "\\multiply\\probegap by 3\n") gap,
     dvDoc (tok ++ "\\setlength{\\probegap}{18pt}\n") gap),
    (dvDoc (tok ++ "\\advance\\probegap by -\\probeb\n") gap,
     dvDoc (tok ++ "\\setlength{\\probegap}{2pt}\n") gap)]
  for (arith, literal) in rows do
    let line := ((arith.splitOn "\n").filter fun l =>
      hasStr l "advance" || hasStr l "multiply" || hasStr l "addtolength").headD ""
    t s!"register arithmetic sets the page its value sets: {line}"
      (pageLines fonts arith == pageLines fonts literal)
  t "a length the rewrite never set is still named and skipped"
    ((dvE (dvDoc "\\advance\\probeunset by 2pt\n" "Body.")).any (·.code == "W0104"))
