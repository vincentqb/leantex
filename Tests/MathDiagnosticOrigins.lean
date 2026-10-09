import Tests.Support
import LeanTex.Cli.FontAssembly

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

namespace Tests

private structure MathOrigin where
  line : Nat
  col : Nat
  trigger : Option String := some "\\("

private structure MathOriginFixture where
  name : String
  preamble : String := ""
  body : String
  face : Option MathOrigin
  alphabets : Array (String × MathOrigin) := #[]
  declared : Bool := false

private def mathOriginFixtures : Array MathOriginFixture := #[
  { name := "later-alphabet"
    body := "First \\(x\\).\n\nLater \\(\\mathcal{A}\\)."
    face := some ⟨4, 7, some "\\("⟩
    alphabets := #[("cal", ⟨6, 7, some "\\("⟩)] },
  { name := "wrappers"
    body := "\\begin{ifbackend}{html,pdf}\n\\begin{center}\n\
      \\textbf{Later \\(\\mathcal{A}\\)}\n\\end{center}\n\\end{ifbackend}"
    face := some ⟨6, 15, some "\\("⟩
    alphabets := #[("cal", ⟨6, 15, some "\\("⟩)] },
  { name := "caption"
    body := "\\begin{figure}\nBody.\n\\caption{Caption \\(\\mathcal{A}\\)}\n\\end{figure}"
    face := some ⟨6, 18, some "\\("⟩
    alphabets := #[("cal", ⟨6, 18, some "\\("⟩)] },
  { name := "running-head"
    preamble := "\\runninghead{Header \\(\\mathcal{A}\\)}\n"
    body := "Body."
    face := some ⟨3, 21, some "\\("⟩
    alphabets := #[("cal", ⟨3, 21, some "\\("⟩)] },
  { name := "running-foot"
    preamble := "\\runningfoot{Footer \\(\\mathcal{A}\\)}\n"
    body := "Body."
    face := some ⟨3, 21, some "\\("⟩
    alphabets := #[("cal", ⟨3, 21, some "\\("⟩)] },
  { name := "title"
    preamble := "\\title{Title \\(\\mathcal{A}\\)}\n"
    body := "\\maketitle"
    face := some ⟨3, 14, some "\\("⟩
    alphabets := #[("cal", ⟨3, 14, some "\\("⟩)] },
  { name := "macro-call"
    preamble := "\\newcommand{\\request}{\\(\\mathcal{A}\\)}\n"
    body := "Plain.\n\n\\request"
    face := some ⟨7, 1, some "\\request"⟩
    alphabets := #[("cal", ⟨7, 1, some "\\request"⟩)] },
  { name := "footnote"
    body := "Body\\footnote{Note \\(\\mathcal{A}\\)}."
    face := some ⟨4, 20, some "\\("⟩
    alphabets := #[("cal", ⟨4, 20, some "\\("⟩)] },
  { name := "empty-formula"
    body := "\\(\\)\n\nActual \\(x\\)."
    face := some ⟨6, 8, some "\\("⟩ },
  { name := "equation"
    body := "\\begin{equation}\n\\mathcal{A}\n\\end{equation}"
    face := some ⟨4, 1, some "\\begin"⟩
    alphabets := #[("cal", ⟨4, 1, some "\\begin"⟩)] },
  { name := "distinct-alphabets"
    body := "First \\(\\symbf{A}\\).\n\nLater \\(\\mathcal{A}\\).\n\n\
      Last \\(\\symsf{5}\\).\n\nAgain \\(\\mathcal{B}\\)."
    face := some ⟨4, 7, some "\\("⟩
    alphabets := #[("cal", ⟨6, 7, some "\\("⟩), ("sf", ⟨8, 6, some "\\("⟩)] },
  { name := "unpainted-note"
    body := "\\note{Hidden \\(x\\)}\n\nActual \\(\\mathcal{A}\\)."
    face := some ⟨6, 8, some "\\("⟩
    alphabets := #[("cal", ⟨6, 8, some "\\("⟩)] },
  { name := "declared-face"
    body := "First \\(x\\).\n\nLater \\(\\mathcal{A}\\)."
    face := none
    alphabets := #[("cal", ⟨6, 7, some "\\("⟩)]
    declared := true },
  { name := "no-formulas", body := "Ordinary text.", face := none },
  -- Dollar formulas retain the authored opener, just as control delimiters do.
  { name := "dollar-source"
    body := "First $x$.\n\nLater $\\mathcal{A}$."
    face := some ⟨4, 7, some "$"⟩
    alphabets := #[("cal", ⟨6, 7, some "$"⟩)] },
  -- A picture label's formula is located at its opener, as a paragraph's is.
  { name := "picture-label"
    preamble := "\\pictures{tool=none}\n"
    body := "\\begin{tikzpicture}\n\\node at (0,0) {Label $\\mathcal{A}$};\n\
      \\end{tikzpicture}"
    face := some ⟨6, 23, some "$"⟩
    alphabets := #[("cal", ⟨6, 23, some "$"⟩)] }]

private def mathOriginSource (family : String) (f : MathOriginFixture) : String :=
  "\\documentclass{article}\n\\fonts{body=\"" ++ family ++ "\"" ++
    (if f.declared then ",math=\"Fira Math\"" else "") ++ "}\n" ++
    f.preamble ++ "\\begin{document}\n" ++ f.body ++ "\n\\end{document}"

private def mathOriginParse (file text : String) : Array Parse.Raw :=
  (Parse.parse file (Lex.lex file text).1).1

private def mathOriginAt (file : String) (expected : MathOrigin) (d : Diag) : Bool :=
  d.span.any fun s =>
    s.file == file && s.pos.line == expected.line && s.pos.col == expected.col

/-- Font resolution must retain the actual requesting formula's source.
N0016 selects a nonempty, painted math request, while each N0018 selects the
first formula missing that alphabet, independently of earlier supported
formulas and other alphabet losses. These are authored reader-to-assembly
checks with a hermetic font scan; no message parsing or invented IR spans
supply the expected origins. -/
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
      let source := mathOriginSource family f
      let (doc, eds, _) := Elab.runRawsSpanned file (mathOriginParse file source)
      let t := fun why ok => check ref ("math origins " ++ family ++ "/" ++ f.name ++
        ": " ++ why) ok
      t "authored fixture reaches typed math without recovery"
        (!eds.any fun d => d.severity == .error || d.kind == .W0012)
      let .ok (fs, resolved, diags, _) ← buildFontSet doc scan cache .settled |
        t "font assembly succeeds" false
        continue
      let faceNotes := diags.filter (·.kind == .N0016)
      t "automatic face is named exactly when undeclared math needs it"
        (faceNotes.size == if f.face.isSome then 1 else 0)
      if let some origin := f.face then
        t "N0016 names the actual formula position"
          (faceNotes.any (mathOriginAt file origin))
        t "N0016 retains the original lexical trigger"
          (faceNotes.any fun d => d.trigger == origin.trigger)
      let alphaNotes := diags.filter (·.kind == .N0018)
      t "alphabet notes retain first-use order and deduplication"
        (alphaNotes.map (·.subject) ==
          f.alphabets.map (fun (name, _) => some ("math-alpha:" ++ name)))
      for (name, origin) in f.alphabets do
        let notes := alphaNotes.filter (·.subject == some ("math-alpha:" ++ name))
        t (name ++ " N0018 names its failing formula position")
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
        mathOriginAt file ⟨line, 7, some "\\("⟩ d && d.trigger == some "\\(")
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
