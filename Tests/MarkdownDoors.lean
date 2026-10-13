module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli
open LeanTex.Core.Parse (Raw)

/-! Two doors, one meaning: a markdown file elaborates the same alone and included by
`\markdownInput` (D1 and D1′ the document, D2 capture, D3 its bound, D4 diagnostics, D5 artifacts,
D6 a self-named include). -/

namespace Tests.MarkdownDoors

def inlineLeaves : List String :=
  ["plain words", "`co de`", "line one\nline two", "line one\\\nline two",
    "<a id=\"k1\"></a>after"]

def inlineWraps : List (String → String) :=
  [fun x => "*" ++ x ++ "*", fun x => "**" ++ x ++ "**",
    fun x => "[" ++ x ++ "](http://example.org/p)", fun x => "![" ++ x ++ "](pic.png)"]

/-- Every inline arm, alone and to depth two. -/
def inlineFamily : List String :=
  inlineLeaves ++ (inlineWraps.flatMap fun w => inlineLeaves.map w) ++
    (inlineWraps.flatMap fun w => inlineWraps.map fun v => w (v "deep"))

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

def blockWraps : List (String → String) :=
  [prefixLines "> " "> ", prefixLines "- " "  ", prefixLines "1. " "   ",
    prefixLines "3. " "   ",
    fun b => prefixLines "- " "  " b ++ "\n\n" ++ prefixLines "- " "  " "loose second",
    fun b => "<details>\n<summary>Summary words</summary>\n\n" ++ b ++ "\n\n</details>"]

/-- Every block arm, alone and to depth two, plus the empty file. -/
def blockFamily : List String :=
  [""] ++ blockLeaves ++ (blockWraps.flatMap fun w => blockLeaves.map w) ++
    (blockWraps.flatMap fun w => blockWraps.map fun v => w (v "Inner words."))

/-- Block shapes, and inline shapes inside a paragraph. -/
def family : List String :=
  blockFamily ++ inlineFamily.map (fun x => "Before " ++ x ++ " after.")

def mdName : String := "frag.md"
def hostFile : String := "host.tex"

def standalone (src : String) : Ir.Doc × Array Diag := standaloneDoc mdName src

def included (src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile (neutralHost mdName) [(mdName, mdName, src)]

/-- The file alone under the host's surface (D1). -/
def aloneInHost (src : String) : Ir.Doc × Array Diag := aloneDoc hostFile mdName src

/-- The file alone as its own include, under its own surface (D1′). -/
def aloneInSelf (src : String) : Ir.Doc × Array Diag := aloneDoc mdName mdName src

/-- A planted door reading markdown through the tex door, which the comparison must catch. -/
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

/-- A planted door naming the fragment by another file, which the accounting must catch. -/
def plantedRenamedDoor (src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile (neutralHost mdName) [(mdName, "other.md", src)]

/-- The diagnostic identity the accounting compares. -/
def ident (d : Diag) : String × Option String × Option Span := (d.code, d.subject, d.span)

/-- D4's judge: the file's own diagnostics agree in both runs by code, subject and span, and every
other one is its document's own. -/
def accounted (alone inc : Array Diag) : Bool :=
  let own (d : Diag) := d.span.any (·.file == mdName)
  let documents (d : Diag) := d.span.all (·.file == hostFile)
  alone.all (fun d => if own d then inc.any (ident · == ident d) else documents d) &&
    inc.all fun d => if own d then alone.any (ident · == ident d) else documents d

mutual

/-- The host's raws with each `\markdownInput{name}` call replaced by `wrap` at its position, at any
depth. -/
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

/-- The host with the fragment's raws spliced at the call, executed with no reader. -/
def splicedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let fds := (Surface.read .markdown mdName src).2
  let raws := spliceList mdName (fun p => (Surface.fragment .markdown mdName src p).1) #[]
    raws.toList
  Elab.runExecuted hostFile (Elab.executeInputs nullReader hostFile raws) (ds ++ fds)

/-- D6's right side: the host with the file's raws, read under the host's own name, standing at each
call. -/
def unwrappedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (sub, fds) := Surface.read .markdown hostFile src
  let raws := spliceList mdName (fun _ => sub) #[] raws.toList
  Elab.runExecuted hostFile (Elab.executeInputs nullReader hostFile raws) (ds ++ fds)

/-- D6's left side: the host including the file under the host's own name. -/
def selfNamedDoc (host src : String) : Ir.Doc × Array Diag :=
  includedDoc hostFile host [(mdName, hostFile, src)]

/-- A planted quotation wrapper standing where the include stood, which D6 must catch. -/
def quotedDoc (host src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (sub, fds) := Surface.read .markdown hostFile src
  let raws := spliceList mdName (fun p => #[.env "quote" sub p]) #[] raws.toList
  Elab.runExecuted hostFile (Elab.executeInputs nullReader hostFile raws) (ds ++ fds)

def hostWith (pre : String) : String :=
  "\\documentclass{article}\\usepackage{markdown}" ++ pre ++
    "\\begin{document}\\markdownInput{" ++ mdName ++ "}\\end{document}"

/-- A slides host whose frame body is the include. -/
def frameHost : String :=
  "\\documentclass{slides}\\usepackage{markdown}\\begin{document}\\begin{frame}{Frame title}" ++
    "\\markdownInput{" ++ mdName ++ "}\\end{frame}\\end{document}"

/-- The frame host with each command on a line of its own. -/
def spacedFrameHost : String :=
  "\\documentclass{slides}\n\\usepackage{markdown}\n\n\\begin{document}\n\n" ++
    "\\begin{frame}{Frame title}\n\\markdownInput{" ++ mdName ++ "}\n\\end{frame}\n\n" ++
    "\\end{document}\n"

/-- Is an accumulator in the include theorems' domain: one include wrapper with blank source either
side (`Elab.sourceBlank`)? -/
def includeStands (raws : Array Raw) : Bool :=
  let isWrapper (r : Raw) : Bool := match r with
    | .env n _ _ => (Parse.inputEnvFile? n).isSome
    | _ => false
  match raws.findIdx? isWrapper with
  | some i => (raws.extract 0 i).all Elab.sourceBlank &&
      (raws.extract (i + 1) raws.size).all Elab.sourceBlank
  | none => false

/-- The raws the document body runs through the real pipeline, the accumulator
`Elab.runDocBody_input_exact` reads. -/
def planRaws (host src : String) : Array Raw :=
  let (raws, _) := Surface.read .tex hostFile host
  let (executed, _) := (Elab.executeInputs (mdFileReader [(mdName, mdName, src)]) hostFile
    raws).run #[]
  (Elab.preparedBody hostFile (Elab.prepareExecuted hostFile executed)).1.raws

/-- The same for a corpus fixture, its includes read as the driver reads them. -/
def fixturePlanRaws (n : String) : IO (Array Raw) := do
  let file := s!"{n}.tex"
  let (raws, _) := Surface.read .tex file (← fixtureText s!"testdata/corpus/{n}.tex")
  let (executed, _, _) ← Input.expandInputs file raws (dir := "testdata/corpus")
  return (Elab.preparedBody file (Elab.prepareExecuted file executed)).1.raws

/-- Each frame's content as the frame arm hands it to its content scope. -/
def frameContents (raws : Array Raw) : Array (Array Raw) :=
  raws.filterMap fun r => match r with
    | .env "frame" body _ =>
      if body[0]? matches some (Raw.group ..) then some (body.extract 1 body.size) else none
    | _ => none

/-- A fragment spelling every ordinary control of the vocabulary. -/
def captureFragment : String :=
  "Words *em* **bold** `mono` [link](http://example.org/l) ![alt](pic.png) " ++
    "<a id=\"k2\"></a>tail\\\nnext line\n\n- item one\n- item two\n"

/-- Which vocabulary controls a host's redefinition reaches inside included markdown: all but
`\item`. -/
def captureRule : List (String × Bool) :=
  [("emph", true), ("textbf", true), ("texttt", true), ("href", true),
    ("includegraphics", true), ("item", false), ("hypertarget", true), ("\\", true)]

def markdownDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for src in family do
    t s!"doors: the desugaring of {repr src} lies in the vocabulary"
      (Md.vocabulary.admitsList (Surface.read .markdown mdName src).1.toList)
  t "doors: the vocabulary judge refuses math and an unlisted control"
    (!Md.vocabulary.admits (.math false #[] {}) && !Md.vocabulary.admits (.ctrl "section" {}))
  let mut plantedTex := 0
  let mut plantedRenamed := 0
  for src in family do
    let (aDoc, aDs) := standalone src
    let (iDoc, iDs) := included src
    let (hDoc, hDs) := aloneInHost src
    let (sDoc, sDs) := aloneInSelf src
    t s!"doors D1: the neutral host's document is the file alone, for {repr src}"
      (iDoc == hDoc)
    t s!"doors D1′: the markdown door's document is its own include for {repr src}"
      (aDoc == sDoc && aDs.map ident == sDs.map ident)
    t s!"doors D1: the content census agrees across the surfaces for {repr src}"
      (Ir.blocksText aDoc.body == Ir.blocksText hDoc.body)
    t s!"doors D4: one accounting for {repr src}" (accounted hDs iDs)
    let (wDoc, wDs) := includedDoc hostFile (spacedNeutralHost mdName) [(mdName, mdName, src)]
    t s!"doors D1: the neutral host on lines of its own is the file alone for {repr src}"
      (wDoc == hDoc)
    t s!"doors D4: one accounting on lines of its own for {repr src}" (accounted hDs wDs)
    if (plantedTexDoor src).1 != hDoc then plantedTex := plantedTex + 1
    if !accounted hDs (plantedRenamedDoor src).2 then plantedRenamed := plantedRenamed + 1
  t s!"doors D1: a door reading markdown as tex is seen ({plantedTex} of {family.length})"
    (plantedTex * 2 > family.length)
  t s!"doors D4: a door that renames the file is seen ({plantedRenamed} of {family.length})"
    (plantedRenamed > 0)
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
  for pre in ["\\renewcommand{\\section}{Zed}", "\\renewcommand{\\textit}{Zed}",
      "\\newcommand{\\foo}{Zed}"] do
    let (doc, _) := includedDoc hostFile (hostWith pre) [(mdName, mdName, captureFragment)]
    t s!"doors D3: {pre} leaves the included blocks alone" (doc.body == neutralDoc.body)
  let (emphDoc, _) := includedDoc hostFile (hostWith "\\renewcommand{\\emph}{Zed}")
    [(mdName, mdName, captureFragment)]
  t "doors D3: a redefinition inside the vocabulary is seen" (emphDoc.body != neutralDoc.body)
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
  let mut quotedSeen := 0
  let mut quotedSpaced := 0
  for src in family do
    for (site, host) in [("body", neutralHost mdName), ("frame", frameHost),
        ("body on lines of its own", spacedNeutralHost mdName),
        ("frame on lines of its own", spacedFrameHost)] do
      t s!"doors D6: named as the file, a {site} that is the include is its raws for {repr src}"
        ((selfNamedDoc host src).1 == (unwrappedDoc host src).1)
    t s!"doors D6: a frame with its call on its own line is the tight frame, for {repr src}"
      ((selfNamedDoc spacedFrameHost src).1 == (selfNamedDoc frameHost src).1)
    if (selfNamedDoc frameHost src).1 != (quotedDoc frameHost src).1 then
      quotedSeen := quotedSeen + 1
    if (selfNamedDoc spacedFrameHost src).1 != (quotedDoc spacedFrameHost src).1 then
      quotedSpaced := quotedSpaced + 1
  t s!"doors D6: a wrapper that means more than a name is seen ({quotedSeen} of {family.length})"
    (quotedSeen * 2 > family.length)
  t s!"doors D6: so it is on lines of its own ({quotedSpaced} of {family.length})"
    (quotedSpaced * 2 > family.length)
  t "doors D6: raws standing at the wrong place in a frame are seen"
    ((selfNamedDoc frameHost captureFragment).1 !=
      (unwrappedDoc (frameHost.replace "{Frame title}" "{Frame title}Lead words")
        captureFragment).1)
  for (site, host) in [("tight", neutralHost mdName),
      ("on lines of its own", spacedNeutralHost mdName)] do
    t s!"doors D6: a body whose call stands {site} is in the include theorems' domain"
      (includeStands (planRaws host captureFragment))
  for (site, host) in [("tight", frameHost), ("on lines of its own", spacedFrameHost)] do
    let contents := frameContents (planRaws host captureFragment)
    t s!"doors D6: a frame whose call stands {site} has its content in the domain"
      (contents.size == 1 && contents.all includeStands)
  let deck := frameContents (← fixturePlanRaws "md-include-deck")
  t "doors D6: the corpus deck's included frame has its content in the domain"
    (deck.size == 1 && deck.all includeStands)
  t "doors D6: the domain judge refuses an include beside text (the corpus article)"
    (!includeStands (← fixturePlanRaws "md-include"))

/-- The neutral host through the driver's own reader agrees with the pure door. -/
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
