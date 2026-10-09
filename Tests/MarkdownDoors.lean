import Tests.Support

open LeanTex.Core LeanTex.Cli
open LeanTex.Core.Parse (Raw)

/-! # Two doors, one meaning

A markdown file reaches the one elaborator through two doors: alone, as a
document of its own, and included in a tex host by `\markdownInput`. A
document's surface may declare defaults of its own — how its content sets,
never what is set — so the doors are compared one surface at a time. The
block-level statement is a theorem under one context, so one surface
(`Elab.markdownInput_blocks_exact`). The document-level statement — the
neutral host's whole document is the file alone as a document of the host's
surface — is pending under the name markdownInput_document_exact: it passes
through the compatibility layer's input state, and owes a comparable
projection of that state (the neutral preamble's equals the empty one up to
its N0100) and the compatibility walk's transparency on the markdown
vocabulary's raws. These checks hold the document level meanwhile, over a
synthetic family that reaches every markdown block and inline node to depth
two:

* D1 — under the host's surface: the neutral host's document is the file
  alone as a document named as the host (`aloneDoc`), whole.
* D1′ — under the markdown surface: the markdown door's document is its own
  include, the file alone as a document of its own name, whole and with the
  same diagnostics. Between D1 and D1′ the raws are one array and only the
  document's name differs — the name that selects a surface — and across
  that difference the content census agrees (`Ir.blocksText`), whatever
  defaults a surface declares.
* D2 — capture: a host's redefinition of a vocabulary control reaches the
  included file as it reaches the same raws spliced at the call, and which
  controls are captured today is a table here.
* D3 — the capture bound: redefining a name outside the vocabulary leaves
  the included blocks those of the neutral host.
* D4 — one accounting, under the host's surface: every diagnostic of the
  file alone appears in the included run with its code, subject and span;
  every other one has a host span.
* D5 — the artifacts, under the host's surface: the typed HTML tree and the
  shipped-page census agree.
* D6 — named as the file, an include is nothing: where the included file
  and the including document share a name, a document body or a frame's
  content that is the include is the same document with the file's raws in
  the call's place. This is `Elab.elabBlockScope_input_exact`'s accumulator
  at a frame, composed with the rest of the frame arm, end to end.

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

/-- The file alone under the host's surface: the document D1 holds the
neutral host's to. -/
def aloneInHost (src : String) : Ir.Doc × Array Diag := aloneDoc hostFile mdName src

/-- The file alone as its own include, under its own surface: the document
D1′ holds the markdown door's to. -/
def aloneInSelf (src : String) : Ir.Doc × Array Diag := aloneDoc mdName mdName src

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

/-- D4's judge: the file's own diagnostics — those whose span lies in the
file — are the same in both runs, both ways, by code, subject and span; and
whatever else either run says is its document's own, with no span or one in
the host. A bare document says it assumed the article page model; the
neutral host says its `\usepackage{markdown}` sets nothing. -/
def accounted (alone inc : Array Diag) : Bool :=
  let own (d : Diag) := d.span.any (·.file == mdName)
  let documents (d : Diag) := d.span.all (·.file == hostFile)
  alone.all (fun d => if own d then inc.any (ident · == ident d) else documents d) &&
    inc.all fun d => if own d then alone.any (ident · == ident d) else documents d

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

/-- D6's right side: the host with the file's raws — read under the host's
own name, no wrapper written — standing where each call stood, executed
with no reader. -/
def unwrappedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (sub, fds) := Surface.read .md hostFile src
  let raws := spliceList mdName (fun _ => sub) #[] raws.toList
  Elab.runExecuted hostFile (Elab.executeInputs nullReader hostFile raws) (ds ++ fds)

/-- D6's left side: the host including the file under the host's own name,
so the wrapper names the file already in force. -/
def selfNamedDoc (host src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile host [(mdName, hostFile, src)]

/-- A planted wrapper that means more than a name — a quotation —
standing where the include stood: D6 must see it. -/
def quotedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (sub, fds) := Surface.read .md hostFile src
  let raws := spliceList mdName (fun p => #[.env "quote" sub p]) #[] raws.toList
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
  -- D1, D1′ and D4 over the family.
  let mut plantedTex := 0
  let mut plantedRenamed := 0
  for src in family do
    let (aDoc, aDs) := standalone src
    let (iDoc, iDs) := included src
    let (hDoc, hDs) := aloneInHost src
    let (sDoc, sDs) := aloneInSelf src
    t s!"doors D1: the neutral host's document is the file alone under its surface for {repr src}"
      (iDoc == hDoc)
    t s!"doors D1′: the markdown door's document is its own include for {repr src}"
      (aDoc == sDoc && aDs.map ident == sDs.map ident)
    t s!"doors D1: the content census agrees across the surfaces for {repr src}"
      (Ir.blocksText aDoc.body == Ir.blocksText hDoc.body)
    t s!"doors D4: one accounting for {repr src}" (accounted hDs iDs)
    if (plantedTexDoor src).1 != hDoc then plantedTex := plantedTex + 1
    if !accounted hDs (plantedRenamedDoor src).2 then plantedRenamed := plantedRenamed + 1
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
    let (hDoc, _) := aloneInHost src
    let (iDoc, _) := included src
    let (_, hTree, _) := HtmlDoc.emitTree {} hDoc
    let (_, iTree, _) := HtmlDoc.emitTree {} iDoc
    t s!"doors D5: one HTML tree for {repr src}"
      (mdFlatten "" hTree.toList == mdFlatten "" iTree.toList)
    t s!"doors D5: one shipped-page census for {repr src}"
      (censusText (censusOf #[] (layoutOf fonts hDoc)) ==
        censusText (censusOf #[] (layoutOf fonts iDoc)))
  -- D6: named as the file, an include is nothing, at a body and at a frame.
  let mut quotedSeen := 0
  for src in family do
    for (site, host) in [("body", neutralHost mdName), ("frame", frameHost)] do
      t s!"doors D6: named as the file, a {site} that is the include is its raws for {repr src}"
        ((selfNamedDoc host src).1 == (unwrappedDoc host src).1)
    if (selfNamedDoc frameHost src).1 != (quotedDoc frameHost src).1 then
      quotedSeen := quotedSeen + 1
  t s!"doors D6: a wrapper that means more than a name is seen ({quotedSeen} of {family.length})"
    (quotedSeen * 2 > family.length)
  t "doors D6: raws standing at the wrong place in a frame are seen"
    ((selfNamedDoc frameHost captureFragment).1 !=
      (unwrappedDoc (frameHost.replace "{Frame title}" "{Frame title}Lead words")
        captureFragment).1)

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
