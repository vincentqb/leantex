import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # A refusal never raises an error and never adds ink

A construct the engine refuses by name is named once and leaves the page as
the document without it would. Each block holds one refusal path to that
rule, over the shipped pages; the probes are synthetic. -/

/-- The shapes a definition's two bodies can split: an environment, a
display, and inline math in both spellings — each opened in the begin body
and closed in the end body. -/
def splitShapes : List (String × String) :=
  [("\\begin{center}\\small", "\\end{center}"), ("\\[", "\\]"), ("$", "$"), ("\\(", "\\)")]

/-- The split-group definition: a construct opened in the begin body and
closed in the end body, LaTeX's most common `\newenvironment` idiom. -/
def splitGroupDef (definer name : String) (shape : String × String) : String :=
  s!"\\{definer}\{{name}}\{{shape.1}}\{{shape.2}}\n"

/-- **A refused environment definition raises no error and ships no ink.**
Every built-in environment name, redefined with the split-group idiom in
each of its shapes, builds: its only diagnostic at the definition is W0303,
and the page is the page of the document that never wrote the definition.
The defect: the parse judged the definition's two bodies as document text,
so the idiom failed the build (E0201, E0205, E0202) beside the W0303 that
ignored it. Quantified over `Elab.builtinEnvNames` and `splitShapes`, so a
built-in the engine gains is a row. -/
def refusedEnvChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "Body words stand here."
  let plain := pageTextOf fonts (dvDoc "" body)
  for n in Elab.builtinEnvNames do
    for shape in splitShapes do
      let src := dvDoc (splitGroupDef "renewenvironment" n shape) body
      let ds := dvE src
      t s!"a split-group redefinition of '\{{n}}' raises no error ({shape.1})"
        (ds.all (·.severity != .error))
      t s!"the redefinition of '\{{n}}' is named by W0303 alone ({shape.1})"
        (ds.all fun d => d.severity == .note || d.code == "W0303")
      t s!"and the page is the page without it ('\{{n}}', {shape.1})"
        (pageTextOf fonts src == plain)
  for shape in splitShapes do
    for head in ["[1]", "[1][Default words for the argument]"] do
      let src := dvDoc s!"\\renewenvironment\{abstract}{head}\{{shape.1}}\{{shape.2}}\n" body
      t s!"a split redefinition with the option runs {head} is W0303 alone ({shape.1})"
        ((dvE src).all fun d => d.severity == .note || d.code == "W0303")

/-- **Parked: an accepted split-group definition is not paired yet.** The
engine elaborates an environment's two halves apart, each under its own
argument scope, so a construct one half opens and the other closes cannot
stand around the content: the definition keeps the parse's E0201. A row
fails once pairing lands for its shape, and leaves with the fix. -/
def splitPairingOwed : List (String × String) :=
  [("\\begin{center}", "\\end{center}"), ("\\[", "\\]"), ("$", "$"), ("\\(", "\\)")]

def splitPairingOwedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (o, c) in splitPairingOwed do
    let src := dvDoc (s!"\\newenvironment\{probewrap}\{{o}}\{{c}}\n")
      "\\begin{probewrap}Wrapped words.\\end{probewrap}"
    t s!"parked: a split '{o}' in an accepted definition still raises E0201"
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

/-- The laid-out lines of a source, baseline and text: what a claim that two
spellings set one page reads. -/
def pageLines (fonts : Font.FontSet) (src : String) : Array (Array (Dim.Sp × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.text))

/-- A bare use of an environment the engine gives a meaning, with the
arguments and body it needs to build. -/
def blockUse (n : String) : String :=
  let body := match n with
    | "itemize" | "enumerate" => "\\item One item"
    | "minipage" => "{4cm}Mini words."
    | "ifbackend" => "{pdf}Backend words."
    | "tabular" => "{ll}Left & Right\\\\"
    | "tabular*" => "{8cm}{ll}Left & Right\\\\"
    | "align" | "align*" => "x &= y"
    | "gather" | "gather*" | "equation" | "equation*" | "displaymath" => "x = y"
    | "block" | "alertblock" | "exampleblock" => "{Block title}Block words."
    | _ => "Block words."
  s!"\\begin\{{n}}{body}\\end\{{n}}"

/-- The spellings of a scope group: the brace pair, and each group
primitive pair. -/
def groupSpellings : List (String × String) :=
  ("{", "}") :: Compat.groupPrimitives.map fun (o, c) => (s!"\\{o} ", s!"\\{c} ")

/-- **A block inside a group stays a block.** A scope group — a brace pair,
`\begingroup … \endgroup`, `\bgroup … \egroup` — scopes declarations and
nothing else (TeXbook ch. 5), so a block environment, a heading or a
display inside one ships the page, the HTML and the diagnostics of the
document without the group; with a size declaration inside, the text is
unchanged. Quantified over the engine's block environments
(`Elab.builtinEnvNames` read by `Elab.bodyIsBlock`) and the group spellings.
The defect: the group was inline content, so a list or table inside one
failed the build, a quote lost its block and an equation its number. -/
def groupedBlockChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let envs := Elab.builtinEnvNames.filter fun n => Elab.bodyIsBlock #[.env n #[] {}]
  let uses := envs.map (fun n => (n, blockUse n)) ++
    [("section", "\\section{Grouped head}"), ("display", "\\[ x = y \\]"),
     ("verbatim", "\\begin{verbatim}code words\\end{verbatim}")]
  let doc (b : String) := dvDoc "" ("Lead words.\n\n" ++ b ++ "\nAfter words.")
  let mut bareFails : List String := []
  for (n, use) in uses do
    let bare := doc use
    let dsB := dvE bare
    if dsB.any (·.severity == .error) then
      bareFails := bareFails ++ [n]
      continue
    let htmlB := (HtmlDoc.emit {} (elabStr bare).1).1
    for (o, c) in groupSpellings do
      let grouped := doc (o ++ use ++ c)
      let dsG := dvE grouped
      t s!"'{o}' around '{n}' builds" (dsG.all (·.severity != .error))
      t s!"'{o}' around '{n}' raises nothing the bare use does not"
        (dsG.all fun d => dsB.any (·.code == d.code))
      t s!"'{o}' around '{n}' ships the bare use's page"
        (pageLines fonts grouped == pageLines fonts bare)
      t s!"'{o}' around '{n}' ships the bare use's HTML"
        ((HtmlDoc.emit {} (elabStr grouped).1).1 == htmlB)
      let sized := doc (o ++ "\\small " ++ use ++ c)
      let dsS := dvE sized
      t s!"'{o}\\small' around '{n}' builds" (dsS.all (·.severity != .error))
      t s!"'{o}\\small' around '{n}' raises nothing the bare use does not"
        (dsS.all fun d => dsB.any (·.code == d.code))
      t s!"'{o}\\small' around '{n}' ships the bare use's text"
        (pageTextOf fonts sized == pageTextOf fonts bare)
      t s!"and the size stops at the group's edge ('{o}', '{n}')"
        (lineSizeOf (censusOfSrc fonts sized) 0 "After words." ==
          lineSizeOf (censusOfSrc fonts bare) 0 "After words.")
  t s!"every bare use builds, so no row is judged vacuously: {bareFails}" bareFails.isEmpty
  for (o, c) in groupSpellings do
    let wrap (b : String) := dvDoc s!"\\newcommand\{\\probeblock}[1]\{{b}}\n"
      "Lead words.\n\n\\probeblock{Cell words}\n\nAfter words."
    let tab := "\\begin{tabular}{l}#1\\end{tabular}"
    let grouped := wrap (o ++ "\\small " ++ tab ++ c)
    t s!"a macro body holding '{o}' around a table builds"
      ((dvE grouped).all (·.severity != .error))
    t s!"and ships the unwrapped body's text ('{o}')"
      (pageTextOf fonts grouped == pageTextOf fonts (wrap tab))

/-- **No document spells an environment name the engine makes.** A
definer body's halves (`Parse.splitOpen`, `Parse.splitClose`) and an
`\input` file's wrapper (`Parse.inputEnv`) each hold a character no word
token holds (`Lex.special`, `Lex.isWs`), and a document's environment name
is one word, so the names the engine once used are ordinary unknown
environments. The defect: `\begin{@open:center}` was read as a split half
and failed the build (E0201), and `\begin{@input:x.sty}` passed for a
spliced file. -/
def reservedEnvNameChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for n in [Parse.splitOpen "center", Parse.splitClose "center", Parse.inputEnv "probe.sty"] do
    t s!"the engine's environment name '{n}' holds a character no word holds"
      (n.any fun c => Lex.special c || Lex.isWs c)
  let use (n : String) :=
    dvDoc "" s!"Lead words.\n\n\\begin\{{n}}Marker words.\\end\{{n}}\nBody words."
  let codes (src : String) := (dvE src).toList.map (·.code)
  let unknown := use "probeunknown"
  for n in ["@open:center", "@close:center", "@input:probe.sty"] do
    t s!"'\{{n}}' is an unknown environment like any other" (codes (use n) == codes unknown)
    t s!"and ships its page ('{n}')" (pageLines fonts (use n) == pageLines fonts unknown)


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

/-- **A use reads the signature in force where it stands.** A later
definition of the same name — undelimited, through any definer, or
delimited anew — replaces a delimited one, so a use after it ships the page
of the document holding only the later definition: the delimiter the use no
longer takes is the author's ink. The defect: every use read the first
delimited definition in the tree, and a period the author typed vanished. -/
def delimitedSigChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let first := "\\def\\probedot#1.{[#1]}\n"
  let use := "Lead \\probedot inner words. tail words."
  for later in ["\\def\\probedot{B}", "\\gdef\\probedot{B}", "\\renewcommand{\\probedot}{B}",
      "\\renewcommand\\probedot{B}", "\\def\\probedot#1;{(#1)}"] do
    t s!"a use after '{later}' reads it, not the first definition"
      (pageTextOf fonts (dvDoc (first ++ later ++ "\n") use) ==
        pageTextOf fonts (dvDoc (later ++ "\n") use))


/-- Register arithmetic on a length the document set is evaluated, not
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


/-- **A composed length assignment is one the length grammar reads, or it
is named.** Register arithmetic composes the value a length holds with its
operand; per unit, `\addtolength` and `\advance` build, and the length then
holds exactly the sum `Decl.parseLength` reads from the two parts. A sum
the grammar cannot read — glue, whose stretch has no place in an
expression — builds too, and is named (W0104), the value left as set. The
defect: the em and ex sums and every glue sum were handed to the grammar
unread and failed the build (E0321). -/
def composedLengthChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body := "First words.\n\n\\vspace{\\probegap}\nSecond words."
  let tok (v : String) := s!"\\newlength\{\\probegap}\n\\setlength\{\\probegap}\{{v}}\n"
  let held (src : String) := (elabStr src).1.tokens.find? "probegap"
  for u in ["pt", "bp", "sp", "mm", "cm", "in", "pc", "em", "ex"] do
    let sum : Option Dim.SymGlue := do
      let a ← Decl.parseLength "10pt"
      let b ← Decl.parseLength ("1" ++ u)
      return { width := a.add b }
    for arith in [s!"\\addtolength\{\\probegap}\{1{u}}", s!"\\advance\\probegap by 1{u}"] do
      let src := dvDoc (tok "10pt" ++ arith ++ "\n") body
      t s!"'{arith}' builds" ((dvE src).all (·.severity != .error))
      t s!"and the length holds the sum of its parts ('{arith}')"
        (sum.isSome && held src == sum)
  for arith in ["\\addtolength{\\probegap}{2pt}", "\\advance\\probegap by 2pt"] do
    let src := dvDoc (tok "10pt plus 2pt" ++ arith ++ "\n") body
    let ds := dvE src
    t s!"'{arith}' on glue builds" (ds.all (·.severity != .error))
    t s!"and is named where the grammar cannot read the sum ('{arith}')"
      (ds.any (·.code == "W0104"))
