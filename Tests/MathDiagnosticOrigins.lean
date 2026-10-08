module

public import Tests.Support
public import LeanTex.Cli.FontAssembly

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

namespace Tests

/-- Where a note must point: the written token that opened its formula, or
the written call whose replacement holds it, with the trigger the lexer
recorded there; or no position at all, for a formula no file holds the
opener of. -/
private inductive MathOrigin where
  | at (line col : Nat) (trigger : Option String)
  | unlocated

private def MathOrigin.trigger : MathOrigin → Option String
  | .at _ _ trigger => trigger
  | .unlocated => none

private def MathOrigin.claim : MathOrigin → String
  | .at .. => "names the actual formula position"
  | .unlocated => "names no position"

private structure MathOriginFixture where
  name : String
  preamble : String := ""
  body : String
  face : Option MathOrigin
  alphabets : Array (String × MathOrigin) := #[]
  declared : Bool := false

/-- A picture whose one label calls `\request` at line 7, column 23. -/
private def pictureCall : String :=
  "\\begin{tikzpicture}\n\\node at (0,0) {Label \\request};\n\\end{tikzpicture}"

/-- A style whose node contents set a formula, its opener at column 43. -/
private def styleLine : String :=
  "\\tikzset{lab/.style={draw, node contents={$\\mathcal{A}$}}}"

private def mathOriginFixtures : Array MathOriginFixture := #[
  { name := "later-alphabet"
    body := "First \\(x\\).\n\nLater \\(\\mathcal{A}\\)."
    face := some (.at 4 7 (some "\\("))
    alphabets := #[("cal", .at 6 7 (some "\\("))] },
  { name := "wrappers"
    body := "\\begin{ifbackend}{html,pdf}\n\\begin{center}\n\
      \\textbf{Later \\(\\mathcal{A}\\)}\n\\end{center}\n\\end{ifbackend}"
    face := some (.at 6 15 (some "\\("))
    alphabets := #[("cal", .at 6 15 (some "\\("))] },
  { name := "caption"
    body := "\\begin{figure}\nBody.\n\\caption{Caption \\(\\mathcal{A}\\)}\n\\end{figure}"
    face := some (.at 6 18 (some "\\("))
    alphabets := #[("cal", .at 6 18 (some "\\("))] },
  { name := "running-head"
    preamble := "\\runninghead{Header \\(\\mathcal{A}\\)}\n"
    body := "Body."
    face := some (.at 3 21 (some "\\("))
    alphabets := #[("cal", .at 3 21 (some "\\("))] },
  { name := "running-foot"
    preamble := "\\runningfoot{Footer \\(\\mathcal{A}\\)}\n"
    body := "Body."
    face := some (.at 3 21 (some "\\("))
    alphabets := #[("cal", .at 3 21 (some "\\("))] },
  { name := "title"
    preamble := "\\title{Title \\(\\mathcal{A}\\)}\n"
    body := "\\maketitle"
    face := some (.at 3 14 (some "\\("))
    alphabets := #[("cal", .at 3 14 (some "\\("))] },
  { name := "macro-call"
    preamble := "\\newcommand{\\request}{\\(\\mathcal{A}\\)}\n"
    body := "Plain.\n\n\\request"
    face := some (.at 7 1 (some "\\request"))
    alphabets := #[("cal", .at 7 1 (some "\\request"))] },
  { name := "footnote"
    body := "Body\\footnote{Note \\(\\mathcal{A}\\)}."
    face := some (.at 4 20 (some "\\("))
    alphabets := #[("cal", .at 4 20 (some "\\("))] },
  { name := "empty-formula"
    body := "\\(\\)\n\nActual \\(x\\)."
    face := some (.at 6 8 (some "\\(")) },
  { name := "equation"
    body := "\\begin{equation}\n\\mathcal{A}\n\\end{equation}"
    face := some (.at 4 1 (some "\\begin"))
    alphabets := #[("cal", .at 4 1 (some "\\begin"))] },
  { name := "distinct-alphabets"
    body := "First \\(\\symbf{A}\\).\n\nLater \\(\\mathcal{A}\\).\n\n\
      Last \\(\\symsf{5}\\).\n\nAgain \\(\\mathcal{B}\\)."
    face := some (.at 4 7 (some "\\("))
    alphabets := #[("cal", .at 6 7 (some "\\(")), ("sf", .at 8 6 (some "\\("))] },
  { name := "unpainted-note"
    body := "\\note{Hidden \\(x\\)}\n\nActual \\(\\mathcal{A}\\)."
    face := some (.at 6 8 (some "\\("))
    alphabets := #[("cal", .at 6 8 (some "\\("))] },
  { name := "declared-face"
    body := "First \\(x\\).\n\nLater \\(\\mathcal{A}\\)."
    face := none
    alphabets := #[("cal", .at 6 7 (some "\\("))]
    declared := true },
  { name := "no-formulas", body := "Ordinary text.", face := none },
  -- Dollar formulas retain the authored opener, just as control delimiters do.
  { name := "dollar-source"
    body := "First $x$.\n\nLater $\\mathcal{A}$."
    face := some (.at 4 7 (some "$"))
    alphabets := #[("cal", .at 6 7 (some "$"))] },
  -- A picture label's formula is located at its opener, as a paragraph's is.
  { name := "picture-label"
    preamble := "\\pictures{tool=none}\n"
    body := "\\begin{tikzpicture}\n\\node at (0,0) {Label $\\mathcal{A}$};\n\
      \\end{tikzpicture}"
    face := some (.at 6 23 (some "$"))
    alphabets := #[("cal", .at 6 23 (some "$"))] },
  -- A macro the compatibility pass expands in a label is located at its
  -- written call, as in a paragraph.
  { name := "picture-label-call"
    preamble := "\\pictures{tool=none}\n\\newcommand{\\request}{$\\mathcal{A}$}\n"
    body := pictureCall
    face := some (.at 7 23 (some "\\request"))
    alphabets := #[("cal", .at 7 23 (some "\\request"))] },
  -- A definition the picture walk expands itself is re-read from its text,
  -- whose coordinates index that text, not a file: its formula's notes name
  -- no position, never one in the picture's file.
  { name := "picture-label-xparse"
    preamble := "\\pictures{tool=none}\n\\NewDocumentCommand{\\request}{}{$\\mathcal{A}$}\n"
    body := pictureCall
    face := some .unlocated
    alphabets := #[("cal", .unlocated)] },
  { name := "picture-label-robust"
    preamble := "\\pictures{tool=none}\n\\DeclareRobustCommand{\\request}{$\\mathcal{A}$}\n"
    body := pictureCall
    face := some .unlocated
    alphabets := #[("cal", .unlocated)] },
  -- Beside a written formula, the written one keeps its opener and the
  -- expanded one borrows no site from it.
  { name := "picture-label-xparse-beside"
    preamble := "\\pictures{tool=none}\n\\NewDocumentCommand{\\request}{}{$\\mathcal{A}$}\n"
    body := "\\begin{tikzpicture}\n\\node at (0,0) {$x$};\n\
      \\node at (2,0) {Label \\request};\n\\end{tikzpicture}"
    face := some (.at 7 17 (some "$"))
    alphabets := #[("cal", .unlocated)] },
  -- A document style's formula is located where the style wrote it.
  { name := "picture-style"
    preamble := "\\pictures{tool=none}\n" ++ styleLine ++ "\n"
    body := "\\begin{tikzpicture}\n\\node[lab] at (0,0);\n\\end{tikzpicture}"
    face := some (.at 4 43 (some "$"))
    alphabets := #[("cal", .at 4 43 (some "$"))] }]

private def mathOriginSource (family : String) (f : MathOriginFixture) : String :=
  "\\documentclass{article}\n\\fonts{body=\"" ++ family ++ "\"" ++
    (if f.declared then ",math=\"Fira Math\"" else "") ++ "}\n" ++
    f.preamble ++ "\\begin{document}\n" ++ f.body ++ "\n\\end{document}"

private def mathOriginParse (file text : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file text).1).1

/-- `root` with an included file's raws spliced in: before its document, or
at the end of the document's body. -/
private def spliceInput (root : Array Parse.Raw) (file : String)
    (child : Array Parse.Raw) (inBody : Bool) : Array Parse.Raw :=
  let input : Parse.Raw := .env (Parse.inputEnv file) child {}
  if inBody then root.map fun r => match r with
    | .env "document" body p => .env "document" (body.push input) p
    | r => r
  else
    let k := (root.findIdx? fun r => r matches .env "document" _ _).getD root.size
    root.extract 0 k ++ #[input] ++ root.extract k root.size

/-- The written-token index the frontend takes before expansion: what the
driver reads a note's trigger off (`SourceTriggers.attribute`), so a
relocated replacement token reports the spelling of the call it stands at. -/
private def writtenTokens (file : String) (raws : Array Parse.Raw) : Compat.SourceTriggers :=
  (Elab.prepare file raws).sourceTriggers

private def mathOriginAt (file : String) : MathOrigin → Diag → Bool
  | .at line col _, d => d.span.any fun s =>
    s.file == file && s.pos.line == line && s.pos.col == col
  | .unlocated, d => d.span.isNone

/-- Font resolution must retain the actual requesting formula's source.
N0016 selects a nonempty, painted math request, while each N0018 selects the
first formula missing that alphabet, independently of earlier supported
formulas and other alphabet losses. These are authored reader-to-assembly
checks with a hermetic font scan, each note read as the driver reports it
(`writtenTokens`); no message parsing or invented IR spans supply the
expected origins. A picture label's formula is located where its opener was
written — the picture's own body, or the file that wrote the style setting
it — and nowhere when the walk read it out of a definition's text. -/
def mathDiagnosticOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let faces ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FaceScan := { faces, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  -- Both N0016 producers participate: a designed companion and the first
  -- available MATH face. These fixtures declare text families, so an ambient
  -- LEANTEX_FONT cannot redirect them.
  for family in ["Open Sans", "Fira Sans"] do
    for f in mathOriginFixtures do
      let file := "synthetic/math-origin-" ++ f.name ++ ".tex"
      let raws := mathOriginParse file (mathOriginSource family f)
      let (doc, eds, _) := Elab.runRawsSpanned file raws
      let t := fun why ok => check ref ("math origins " ++ family ++ "/" ++ f.name ++
        ": " ++ why) ok
      t "authored fixture reaches typed math without recovery"
        (!eds.any fun d => d.severity == .error || d.kind == .W0012)
      let .ok (fs, resolved, assembled, _) ← buildFontSet doc scan cache .settled |
        t "font assembly succeeds" false
        continue
      let diags := assembled.map (writtenTokens file raws).attribute
      let faceNotes := diags.filter (·.kind == .N0016)
      t "automatic face is named exactly when undeclared math needs it"
        (faceNotes.size == if f.face.isSome then 1 else 0)
      if let some origin := f.face then
        t ("N0016 " ++ origin.claim)
          (faceNotes.any (mathOriginAt file origin))
        t "N0016 retains the original lexical trigger"
          (faceNotes.any fun d => d.trigger == origin.trigger)
      let alphaNotes := diags.filter (·.kind == .N0018)
      t "alphabet notes retain first-use order and deduplication"
        (alphaNotes.map (·.subject) ==
          f.alphabets.map (fun (name, _) => some ("math-alpha:" ++ name)))
      for (name, origin) in f.alphabets do
        let notes := alphaNotes.filter (·.subject == some ("math-alpha:" ++ name))
        t (name ++ " N0018 " ++ origin.claim)
          (notes.any (mathOriginAt file origin))
        t (name ++ " N0018 retains the original lexical trigger")
          (notes.any fun d => d.trigger == origin.trigger)
      let mathFamily := fs.mathFont?.map (fun (_, font, _) => font.family) |>.getD "math face"
      let plain := Ir.eraseLocations doc
      let (plainResolved, plainDiags) := Ir.resolveMathAlphas fs.mathAlphabets mathFamily plain
      t "provenance does not change the resolved document"
        (Ir.eraseLocations resolved == Ir.eraseLocations plainResolved)
      t "unlocated IR never receives a fabricated origin"
        (plainDiags.all fun d => d.span.isNone && d.trigger.isNone)
      t "a second resolution remains silent"
        ((Ir.resolveMathAlphas fs.mathAlphabets mathFamily resolved).2.isEmpty)
  -- An included formula retains the included file, not the root's location.
  let file := "synthetic/included-math.tex"
  let child := mathOriginParse file "First \\(x\\).\n\nLater \\(\\mathcal{A}\\)."
  let root := mathOriginParse "synthetic/root.tex" "\\fonts{body=\"Open Sans\"}"
  let raws := root.push (.env (Parse.inputEnv file) child {})
  let (doc, _, _) := Elab.runRawsSpanned "synthetic/root.tex" raws
  let .ok (_, _, diags, _) ← buildFontSet doc scan cache .settled |
    check ref "math origins include: font assembly succeeds" false
    return
  for (kind, line) in [(DiagCode.N0016, 1), (.N0018, 3)] do
    check ref s!"math origins include: {repr kind} keeps the child origin and trigger"
      (diags.any fun d => d.kind == kind &&
        mathOriginAt file (.at line 7 (some "\\(")) d && d.trigger == some "\\(")
  -- A document style's formula is located in the file that wrote the style,
  -- wherever the picture applying it stands: the style an included file
  -- wrote, and the root's style applied in a picture an included file holds.
  let picture := "\\begin{tikzpicture}\n\\node[lab] at (0,0);\n\\end{tikzpicture}"
  for (name, rootFile, preamble, body, childFile, child, inBody, owner, line) in [
      ("included style", "synthetic/style-root.tex", "", picture,
        "synthetic/picture-styles.tex", styleLine, false, "synthetic/picture-styles.tex", 1),
      ("included picture", "synthetic/figure-root.tex", styleLine ++ "\n", "",
        "synthetic/picture-figure.tex", picture, true, "synthetic/figure-root.tex", 4)] do
    let root := mathOriginParse rootFile (mathOriginSource "Open Sans"
      { name, preamble := "\\pictures{tool=none}\n" ++ preamble, body, face := none })
    let raws := spliceInput root childFile (mathOriginParse childFile child) inBody
    let (doc, eds, _) := Elab.runRawsSpanned rootFile raws
    check ref s!"math origins {name}: the style reaches the label without recovery"
      (!eds.any fun d => d.severity == .error || d.kind == .W0012 || d.kind == .W0340)
    let .ok (_, _, assembled, _) ← buildFontSet doc scan cache .settled |
      check ref s!"math origins {name}: font assembly succeeds" false
      continue
    let diags := assembled.map (writtenTokens rootFile raws).attribute
    for kind in [DiagCode.N0016, .N0018] do
      check ref s!"math origins {name}: {repr kind} names the style's own file and opener"
        (diags.any fun d => d.kind == kind &&
          mathOriginAt owner (.at line 43 (some "$")) d && d.trigger == some "$")
  -- A provisional request can precede source elaboration. Such a request
  -- must remain unlocated, rather than borrowing an unrelated text span.
  let (preamble, _, _) := Elab.runRawsSpanned "synthetic/provisional.tex"
    (mathOriginParse "synthetic/provisional.tex" "\\fonts{body=\"Open Sans\"}\nText.")
  let .ok (_, _, provisional, _) ← buildFontSet preamble scan cache (.provisional true) |
    check ref "math origins provisional: font assembly succeeds" false
    return
  let notes := provisional.filter (·.kind == .N0016)
  check ref "math origins provisional: absent source is never invented"
    (notes.size == 1 && notes.all fun d => d.span.isNone && d.trigger.isNone)

end Tests
