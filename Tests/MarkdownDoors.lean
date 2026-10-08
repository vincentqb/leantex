import Tests.Support

open LeanTex.Core LeanTex.Cli
open LeanTex.Core.Parse (Raw)

/-! # Two doors, one meaning

A markdown file reaches the one elaborator through two doors: alone, as a
document of its own, and included in a tex host by `\markdownInput`. The
block-level statement is a theorem (`Elab.markdownInput_blocks_exact`).
The document-level statement — the neutral host's whole document is the
file's own — is pending under the name markdownInput_document_exact: it
passes through the compatibility layer's input state, and owes a
comparable projection of that state (the neutral preamble's equals the
empty one up to its N0100) and the compatibility walk's transparency on
the markdown vocabulary's raws. These checks hold the document level
meanwhile, over a synthetic family that reaches every markdown block and
inline node to depth two:

* D1 — the neutral host's document is the standalone document, whole.
* D2 — capture: a host's redefinition of a vocabulary control reaches the
  included file as it reaches the same raws spliced at the call, and which
  controls are captured today is a table here.
* D3 — the capture bound: redefining a name outside the vocabulary leaves
  the included blocks those of the neutral host.
* D4 — one accounting: every standalone diagnostic appears in the included
  run with its code, subject and span; every other one has a host span.
* D5 — the artifacts: the typed HTML tree and the shipped-page census agree
  across the doors.

Every family carries a planted divergence that must fail. -/

namespace Tests.MarkdownDoors

/-! ## The synthetic family -/

/-- Inline leaves, as markdown spells them. -/
def inlineLeaves : List String :=
  ["plain words", "`co de`", "line one\nline two", "line one\\\nline two",
    "<a id=\"k1\"></a>after"]

/-- Inline containers around a body. -/
def inlineWraps : List (String → String) :=
  [fun x => "*" ++ x ++ "*", fun x => "**" ++ x ++ "**",
    fun x => "[" ++ x ++ "](http://example.org/p)", fun x => "![" ++ x ++ "](pic.png)"]

/-- Every inline arm, alone and to depth two: each leaf, each container of
each leaf, each container of each container of a plain leaf. -/
def inlineFamily : List String :=
  inlineLeaves ++ (inlineWraps.flatMap fun w => inlineLeaves.map w) ++
    (inlineWraps.flatMap fun w => inlineWraps.map fun v => w (v "deep"))

/-- Block leaves, each over a paragraph of plain words. -/
def blockLeaves : List String :=
  ["Plain paragraph.", "# Heading one", "## Heading two", "### Heading three",
    "#### Heading four", "##### Heading five", "###### Heading six",
    "```\ncode line\n```", "```python\nx = 1\n```", "```{r}\ny\n```", "***",
    "Setext heading\n=============="]

/-- Prefix every line of a block, as a container's continuation does. -/
def prefixLines (first rest : String) (block : String) : String :=
  match block.splitOn "\n" with
  | [] => first
  | l :: ls => String.intercalate "\n" ((first ++ l) :: ls.map fun x =>
      if x.isEmpty then rest.trimAsciiEnd.toString else rest ++ x)

/-- Block containers around a block. -/
def blockWraps : List (String → String) :=
  [prefixLines "> " "> ", prefixLines "- " "  ", prefixLines "1. " "   ",
    prefixLines "3. " "   ",
    fun b => prefixLines "- " "  " b ++ "\n\n" ++ prefixLines "- " "  " "loose second",
    fun b => "<details>\n<summary>Summary words</summary>\n\n" ++ b ++ "\n\n</details>"]

/-- Every block arm, alone and to depth two, plus the empty file. -/
def blockFamily : List String :=
  [""] ++ blockLeaves ++ (blockWraps.flatMap fun w => blockLeaves.map w) ++
    (blockWraps.flatMap fun w => blockWraps.map fun v => w (v "Inner words."))

/-- The whole family: block shapes, and inline shapes inside a paragraph. -/
def family : List String :=
  blockFamily ++ inlineFamily.map (fun x => "Before " ++ x ++ " after.")

/-! ## The doors under test -/

def mdName : String := "frag.md"
def hostFile : String := "host.tex"

def standalone (src : String) : Ir.Doc × Array Diag := standaloneDoc mdName src

def included (src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile (neutralHost mdName) [(mdName, mdName, src)]

/-- A planted door that reads markdown through the tex door: the
comparison must see it. -/
def plantedTexDoor (src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile (neutralHost mdName)
  let reader : Compat.InputReader (StateM (Array Diag)) := fun request context => do
    if request.command != "markdownInput" then return (none, context)
    let (sub, rds) := Surface.fragment .tex mdName src request.pos
    modify (· ++ rds)
    let (answer, context) := Elab.resumeInput nullReader context request.file sub
    return (some answer, context)
  let (executed, readDs) := (Elab.executeInputs reader hostFile raws).run #[]
  Elab.runExecuted hostFile executed (ds ++ readDs)

/-- A planted door that names the fragment by another file: the accounting
must see it. -/
def plantedRenamedDoor (src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile (neutralHost mdName) [(mdName, "other.md", src)]

/-- The diagnostic identity the accounting compares. -/
def ident (d : Diag) : String × Option String × Option Span := (d.code, d.subject, d.span)

/-- D4's judge: every standalone diagnostic appears among the included
ones, and every included one that does not is the host's own. -/
def accounted (alone inc : Array Diag) : Bool :=
  alone.all (fun d => inc.any (ident · == ident d)) &&
    inc.all fun d => alone.any (ident · == ident d) ||
      d.span.any (·.file == hostFile)

/-! ## D2 — capture, as data -/

mutual

/-- The host's raws with each `\markdownInput{name}` call replaced by
`wrap` at the call's position, at any depth: the fragment's raws standing
where the call stood. -/
def spliceList (name : String) (wrap : Pos → Array Raw) (out : Array Raw) :
    List Raw → Array Raw
  | [] => out
  | .ctrl "markdownInput" p :: .group #[.word w q] g :: rest =>
    if w == name then spliceList name wrap (out ++ wrap p) rest
    else spliceList name wrap ((out.push (.ctrl "markdownInput" p)).push (.group #[.word w q] g)) rest
  | r :: rest => spliceList name wrap (out.push (spliceOne name wrap r)) rest

def spliceOne (name : String) (wrap : Pos → Array Raw) : Raw → Raw
  | .env n body p => .env n (spliceList name wrap #[] body.toList) p
  | .group body p => .group (spliceList name wrap #[] body.toList) p
  | r => r

end

/-- The host with the fragment's raws spliced at the call, executed with no
reader: the hinge, at document level. -/
def splicedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let fds := (Surface.read .md mdName src).2
  let raws := spliceList mdName (fun p => (Surface.fragment .md mdName src p).1) #[] raws.toList
  Elab.runExecuted hostFile (Elab.executeInputs nullReader hostFile raws) (ds ++ fds)

/-- An article host with one preamble line. -/
def hostWith (pre : String) : String :=
  "\\documentclass{article}\\usepackage{markdown}" ++ pre ++
    "\\begin{document}\\markdownInput{" ++ mdName ++ "}\\end{document}"

/-- A slides host whose frame body is the include. -/
def frameHost : String :=
  "\\documentclass{slides}\\usepackage{markdown}\\begin{document}\\begin{frame}{Frame title}" ++
    "\\markdownInput{" ++ mdName ++ "}\\end{frame}\\end{document}"

/-- A fragment that spells every ordinary control of the vocabulary. -/
def captureFragment : String :=
  "Words *em* **bold** `mono` [link](http://example.org/l) ![alt](pic.png) " ++
    "<a id=\"k2\"></a>tail\\\nnext line\n\n- item one\n- item two\n"

/-- Today's capture rule: which vocabulary controls a host's redefinition
reaches inside included markdown, as it reaches the same call written in
the host. Every ordinary control is captured but `\item`, whose
redefinition reaches no list item, included or written in the host. A
change to the rule is a decision, made here. -/
def captureRule : List (String × Bool) :=
  [("emph", true), ("textbf", true), ("texttt", true), ("href", true),
    ("includegraphics", true), ("item", false), ("hypertarget", true), ("\\", true)]

def markdownDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The vocabulary judge, as a test's assertion and as a judge that can say no.
  for src in family do
    t s!"doors: the desugaring of {repr src} lies in the vocabulary"
      (Md.vocabulary.admitsList (Surface.read .md mdName src).1.toList)
  t "doors: the vocabulary judge refuses math and an unlisted control"
    (!Md.vocabulary.admits (.math false #[] {}) && !Md.vocabulary.admits (.ctrl "section" {}))
  -- D1 and D4 over the family.
  let mut plantedTex := 0
  let mut plantedRenamed := 0
  for src in family do
    let (aDoc, aDs) := standalone src
    let (iDoc, iDs) := included src
    t s!"doors D1: the neutral host's document is the standalone one for {repr src}"
      (iDoc == aDoc)
    t s!"doors D4: one accounting for {repr src}" (accounted aDs iDs)
    if (plantedTexDoor src).1 != aDoc then plantedTex := plantedTex + 1
    if !accounted aDs (plantedRenamedDoor src).2 then plantedRenamed := plantedRenamed + 1
  t s!"doors D1: a door reading markdown as tex is seen ({plantedTex} of {family.length})"
    (plantedTex * 2 > family.length)
  t s!"doors D4: a door that renames the file is seen ({plantedRenamed} of {family.length})"
    (plantedRenamed > 0)
  -- D2: the hinge for every captured control, a frame host, and the rule as data.
  let (neutralDoc, _) := includedDoc hostFile (hostWith "") [(mdName, mdName, captureFragment)]
  for (n, captured) in captureRule do
    let host := hostWith ("\\renewcommand{\\" ++ n ++ "}{Zed}")
    let (iDoc, _) := includedDoc hostFile host [(mdName, mdName, captureFragment)]
    t s!"doors D2: a host redefining \\{n} includes as it splices"
      (iDoc == (splicedDoc host captureFragment).1)
    t s!"doors D2: the capture rule for \\{n} is {captured}"
      ((iDoc.body != neutralDoc.body) == captured)
  let (frameDoc, _) := includedDoc hostFile frameHost [(mdName, mdName, captureFragment)]
  t "doors D2: a frame host includes as it splices"
    (frameDoc == (splicedDoc frameHost captureFragment).1)
  t "doors D2: a splice at the wrong place is seen"
    (frameDoc != (splicedDoc (frameHost.replace "{Frame title}" "{Frame title}Lead words")
      captureFragment).1)
  -- D3: names outside the vocabulary do not reach the included blocks.
  for pre in ["\\renewcommand{\\section}{Zed}", "\\renewcommand{\\textit}{Zed}",
      "\\newcommand{\\foo}{Zed}"] do
    let (doc, _) := includedDoc hostFile (hostWith pre) [(mdName, mdName, captureFragment)]
    t s!"doors D3: {pre} leaves the included blocks alone" (doc.body == neutralDoc.body)
  let (emphDoc, _) := includedDoc hostFile (hostWith "\\renewcommand{\\emph}{Zed}")
    [(mdName, mdName, captureFragment)]
  t "doors D3: a redefinition inside the vocabulary is seen" (emphDoc.body != neutralDoc.body)
  -- D5: the artifacts, from the IR both doors produced.
  let some bytes ← findFont | failures ref "doors D5: missing fixture font"
  let .ok font := Font.parse bytes | failures ref "doors D5: invalid fixture font"
  let fonts := oneFaceOf font
  for src in [captureFragment, "# Heading\n\n> quoted words\n\n```python\nx = 1\n```\n"] do
    let (aDoc, _) := standalone src
    let (iDoc, _) := included src
    let (_, aTree, _) := HtmlDoc.emitTree {} aDoc
    let (_, iTree, _) := HtmlDoc.emitTree {} iDoc
    t s!"doors D5: one HTML tree for {repr src}"
      (mdFlatten "" aTree.toList == mdFlatten "" iTree.toList)
    t s!"doors D5: one shipped-page census for {repr src}"
      (censusText (censusOf #[] (layoutOf fonts aDoc)) ==
        censusText (censusOf #[] (layoutOf fonts iDoc)))

/-- The neutral host through the driver's own reader, against the pure
door: the pure reader is held to the one the driver runs. -/
def markdownDoorDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let host := (dir / hostFile).toString
    let frag := (dir / mdName).toString
    for src in [captureFragment, "# Heading\n\nWords *em*.\n", ""] do
      IO.FS.writeFile frag src
      let (driverDoc, driverDs) ← elabInputSrc host (neutralHost mdName)
      let (pureDoc, pureDs) := includedDoc host (neutralHost mdName) [(mdName, frag, src)]
      t s!"doors: the driver's reader is the pure door for {repr src}"
        (driverDoc == pureDoc && driverDs.map ident == pureDs.map ident)

end Tests.MarkdownDoors
