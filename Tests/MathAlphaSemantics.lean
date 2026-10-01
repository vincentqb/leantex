import Tests.FontMath

open LeanTex.Core

namespace Tests

/-- A synthetic formula and the scalars its two artifacts must carry.
PDF paint order puts the superscript before the subscript; MathML's typed
tree orders them the other way. Every expectation is independent of the
alphabet resolver and was measured with unicode-math's default TeX style. -/
structure MathAlphaSemanticCase where
  name : String
  formula : String
  expected : String
  htmlExpected : Option String := none

/-- Greek's ordinary capitals/lowercase, final sigma and the six variant
slots, plus the capital theta symbol and ∂/∇. Latin and digits
distinguish default `symbf` from `symbfit`: default bold is upright except
for lowercase Greek and ∂. These are observed Unicode scalars, not
calls to the production mapping. -/
def mathAlphaSemanticCases : Array MathAlphaSemanticCase := Id.run do
  let upper := "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"
  let lower := "αβγδεζηθικλμνξοπρςστυφχψω"
  let variants := "ϵϑϰϕϱϖ"
  let itUpper := "𝛢𝛣𝛤𝛥𝛦𝛧𝛨𝛩𝛪𝛫𝛬𝛭𝛮𝛯𝛰𝛱𝛲𝛴𝛵𝛶𝛷𝛸𝛹𝛺"
  let itLower := "𝛼𝛽𝛾𝛿𝜀𝜁𝜂𝜃𝜄𝜅𝜆𝜇𝜈𝜉𝜊𝜋𝜌𝜍𝜎𝜏𝜐𝜑𝜒𝜓𝜔"
  let itVariants := "𝜖𝜗𝜘𝜙𝜚𝜛"
  let bfUpper := "𝚨𝚩𝚪𝚫𝚬𝚭𝚮𝚯𝚰𝚱𝚲𝚳𝚴𝚵𝚶𝚷𝚸𝚺𝚻𝚼𝚽𝚾𝚿𝛀"
  let bfLower := "𝛂𝛃𝛄𝛅𝛆𝛇𝛈𝛉𝛊𝛋𝛌𝛍𝛎𝛏𝛐𝛑𝛒𝛓𝛔𝛕𝛖𝛗𝛘𝛙𝛚"
  let bfVariants := "𝛜𝛝𝛞𝛟𝛠𝛡"
  let biUpper := "𝜜𝜝𝜞𝜟𝜠𝜡𝜢𝜣𝜤𝜥𝜦𝜧𝜨𝜩𝜪𝜫𝜬𝜮𝜯𝜰𝜱𝜲𝜳𝜴"
  let biLower := "𝜶𝜷𝜸𝜹𝜺𝜻𝜼𝜽𝜾𝜿𝝀𝝁𝝂𝝃𝝄𝝅𝝆𝝇𝝈𝝉𝝊𝝋𝝌𝝍𝝎"
  let biVariants := "𝝐𝝑𝝒𝝓𝝔𝝕"
  let sources := #[
    ("upper", upper), ("lower", lower), ("variants", variants),
    ("latin", "ABChxyz"), ("digits", "0123456789"),
    ("misc", "\\partial\\nabla ϴ")]
  let alphabets : Array (String × Array String) := #[
    ("symup", #[upper, lower, variants, "ABChxyz", "0123456789", "∂∇ϴ"]),
    ("symrm", #[upper, lower, variants, "ABChxyz", "0123456789", "∂∇ϴ"]),
    ("symit", #[itUpper, itLower, itVariants, "𝐴𝐵𝐶ℎ𝑥𝑦𝑧", "0123456789", "𝜕𝛻𝛳"]),
    ("symbf", #[bfUpper, biLower, biVariants, "𝐀𝐁𝐂𝐡𝐱𝐲𝐳", "𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗", "𝝏𝛁𝚹"]),
    ("symbfup", #[bfUpper, bfLower, bfVariants, "𝐀𝐁𝐂𝐡𝐱𝐲𝐳", "𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗", "𝛛𝛁𝚹"]),
    ("symbfit", #[biUpper, biLower, biVariants, "𝑨𝑩𝑪𝒉𝒙𝒚𝒛", "0123456789", "𝝏𝜵𝜭"])]
  let mut rows := #[]
  for (command, expected) in alphabets do
    for i in [:sources.size] do
      let (kind, source) := sources[i]!
      rows := rows.push {
        name := command ++ "-" ++ kind
        formula := "\\" ++ command ++ "{" ++ source ++ "}"
        expected := expected[i]! }
    -- Control spellings cover all existing named lowercase Greek, with
    -- epsilon/phi's TeX slot convention and varkappa from the generated table.
    let controls :=
      "\\alpha\\beta\\gamma\\delta\\varepsilon\\zeta\\eta\\theta\\iota\\kappa" ++
      "\\lambda\\mu\\nu\\xi ο\\pi\\rho\\varsigma\\sigma\\tau\\upsilon\\varphi" ++
      "\\chi\\psi\\omega\\epsilon\\vartheta\\varkappa\\phi\\varrho\\varpi"
    rows := rows.push {
      name := command ++ "-controls"
      formula := "\\" ++ command ++ "{" ++ controls ++ "}"
      expected := expected[1]! ++ expected[2]! }
  rows := rows ++ #[
    ⟨"symbf-symup", "\\symbf{AΓγ\\symup{AΓγϑ}γ}", "𝐀𝚪𝜸AΓγϑ𝜸", none⟩,
    ⟨"symbfup-symup", "\\symbfup{AΓγ\\symup{AΓγϑ}γ}", "𝐀𝚪𝛄AΓγϑ𝛄", none⟩,
    ⟨"symbf-symit", "\\symbf{AΓγ\\symit{AΓγϑ}γ}", "𝐀𝚪𝜸𝐴𝛤𝛾𝜗𝜸", none⟩,
    ⟨"symbfup-symit", "\\symbfup{AΓγ\\symit{AΓγϑ}γ}", "𝐀𝚪𝛄𝐴𝛤𝛾𝜗𝛄", none⟩,
    ⟨"symup-symbf", "\\symup{AΓγ\\symbf{AΓγϑ}γ}", "AΓγ𝐀𝚪𝜸𝝑γ", none⟩,
    ⟨"symup-symbfup", "\\symup{AΓγ\\symbfup{AΓγϑ}γ}", "AΓγ𝐀𝚪𝛄𝛝γ", none⟩,
    ⟨"symup-symbfit", "\\symup{AΓγ\\symbfit{AΓγϑ}γ}", "AΓγ𝑨𝜞𝜸𝝑γ", none⟩,
    ⟨"symbfit-symrm", "\\symbfit{AΓγ\\symrm{AΓγϑ}γ}", "𝑨𝜞𝜸AΓγϑ𝜸", none⟩,
    ⟨"symbfup-symbfit", "\\symbfup{AΓγ\\symbfit{AΓγϑ}γ}", "𝐀𝚪𝛄𝑨𝜞𝜸𝝑𝛄", none⟩,
    ⟨"symup-scripts", "\\symup{Γ_α^{β}\\frac{γ}{δ}}", "Γβαγδ", some "Γαβγδ"⟩,
    ⟨"symrm-scripts", "\\symrm{Γ_α^{β}\\frac{γ}{δ}}", "Γβαγδ", some "Γαβγδ"⟩,
    ⟨"symbf-scripts", "\\symbf{Γ_α^{β}\\frac{γ}{δ}}", "𝚪𝜷𝜶𝜸𝜹", some "𝚪𝜶𝜷𝜸𝜹"⟩,
    ⟨"symbfup-scripts", "\\symbfup{Γ_α^{β}\\frac{γ}{δ}}", "𝚪𝛃𝛂𝛄𝛅", some "𝚪𝛂𝛃𝛄𝛅"⟩]
  return rows

mutual

/-- Inspect the typed MathML leaves, including each `mathvariant`: a
correct plain Greek scalar without `normal` would be re-italicized by the
browser. This reads artifacts, never the math IR or its alphabet table. -/
private def mathAlphaLeaves (acc : Array Html.Node) : Html.Node → Array Html.Node
  | n@(.elem tag _ kids) =>
    if tag == "mi" || tag == "mn" then acc.push n
    else mathAlphaLeavesList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def mathAlphaLeavesList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: ns => mathAlphaLeavesList (mathAlphaLeaves acc n) ns

end

/-- A forced symbol alphabet has no text-family CSS, and each identifier's
literal scalar is protected from MathML's automatic italic transformation. -/
private def mathAlphaLeafNormal : Html.Node → Bool
  | .elem tag attrs _ =>
    !(attrs.any (·.1 == "style")) &&
      (tag != "mi" || (attrs.find? (·.1 == "mathvariant")).map (·.2) == some "normal")
  | .text _ | .style _ | .script _ _ => false

/-- Exercise the actual document-sourced command, including both sides of
a nested upright/default-bold boundary. Reuse the independently observed
inventory, not the production alphabet map. -/
def mathAlphaLegacyAliasCases : Array MathAlphaSemanticCase :=
  ((mathAlphaSemanticCases.filter fun row => row.name.startsWith "symbf-").map fun row =>
    { row with
      name := row.name.replace "symbf-" "mathbf-"
      formula := row.formula.replace "\\symbf{" "\\mathbf{" }) ++ #[
    ⟨"mathbf-symbfup", "\\mathbf{Γγ\\symbfup{Γγ\\partial}γ}",
      "𝚪𝜸𝚪𝛄𝛛𝜸", none⟩,
    ⟨"symbfup-mathbf", "\\symbfup{Γγ\\mathbf{Γγ\\partial}γ}",
      "𝚪𝛄𝚪𝜸𝝏𝛄", none⟩,
    ⟨"mathbf-symbf", "\\mathbf{Γγ\\symbf{Γγ\\partial}γ}",
      "𝚪𝜸𝚪𝜸𝝏𝜸", none⟩,
    ⟨"symbf-mathbf", "\\symbf{Γγ\\mathbf{Γγ\\partial}γ}",
      "𝚪𝜸𝚪𝜸𝝏𝜸", none⟩]

private structure MathAlphaArtifact where
  glyphs : Array (Nat × Nat × Char)
  pdf : Array (String × String × Int × Option Bool)
  leaves : Array Html.Node

private def mathAlphaArtifact (ref : IO.Ref (List String)) (fs : Font.FontSet)
    (preamble formula : String) : IO MathAlphaArtifact := do
  let (raw, ds) := elabStr ("\\documentclass{article}\n" ++ preamble ++
    "\n\\pagestyle{empty}\\begin{document}$" ++ formula ++ "$\\end{document}")
  let coverage := { fs.mathAlphabets with sources := raw.fonts.mathSources }
  let (doc, ads) := Ir.resolveMathAlphas coverage "Fira Math" raw
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom fs none doc
  let (_, body, hds) := HtmlDoc.emitTree { fonts := some fs } doc
  check ref (formula ++ " has no recovery or missing alphabet")
    (!(ds ++ ads ++ out.diags ++ hds).any fun d =>
      d.severity == .error || d.code == "W0012" || d.code == "W0009" || d.code == "N0018")
  let glyphs := (bodyLines out).flatMap fun line => line.segs.flatMap fun
    | .run f _ _ _ gs _ _ _ _ _ _ => gs.map fun g => (f, g.1, g.2.1)
    | _ => #[]
  let pdf ← match pdfFaceRuns (Pdf.write geom fs out.pages doc.info {} out.outline) with
    | .ok runs => pure runs
    | .error e => do
      failures ref (formula ++ " PDF cannot be read: " ++ e)
      pure #[]
  return { glyphs, pdf, leaves := mathAlphaLeavesList #[] body.toList }

/-- `mathbf=sym` must make the legacy and forced commands agree at all
three artifact observations, while explicit/default text policy keeps the
body's bold face for Latin letters and digits. Policy tests must use the
legacy command itself: changing policy around forced commands alone cannot
detect an alias divergence. -/
private def mathAlphaLegacyAliasChecks (ref : IO.Ref (List String))
    (fs : Font.FontSet) : IO Unit := do
  for row in mathAlphaLegacyAliasCases do
    let legacy ← mathAlphaArtifact ref fs
      "\\usepackage[mathbf=sym]{unicode-math}" row.formula
    let forced ← mathAlphaArtifact ref fs
      "\\usepackage[mathbf=sym]{unicode-math}"
      (row.formula.replace "\\mathbf{" "\\symbf{")
    let wanted := row.expected.toList.toArray.map fun c =>
      (4, ((fs.get 4).gid c).getD 0, c)
    check ref (row.name ++ " aliases the forced Layout scalars and real glyph IDs")
      (wanted.all (fun (_, gid, _) => gid != 0) &&
        legacy.glyphs == wanted && legacy.glyphs == forced.glyphs)
    check ref (row.name ++ " aliases the forced PDF scalars")
      (legacy.pdf == forced.pdf && legacy.pdf.size == 1 &&
        (legacy.pdf[0]?.map fun (_, text, _, _) => text) == some row.expected)
    let text (a : MathAlphaArtifact) :=
      a.leaves.foldl (fun s n => s ++ nodeTextOne "" n) ""
    check ref (row.name ++ " aliases the literal typed MathML scalars")
      (text legacy == row.htmlExpected.getD row.expected && text legacy == text forced &&
        !legacy.leaves.isEmpty && legacy.leaves.all mathAlphaLeafNormal &&
        forced.leaves.all mathAlphaLeafNormal)

  for preamble in ["", "\\usepackage[mathbf=text]{unicode-math}"] do
    for (formula, expected, face, css) in [
        ("\\mathbf{Ax012}", "Ax012", 1,
          "font-family: var(--font-body); font-weight: 700"),
        ("\\symbf{\\mathbf{x}}", "x", 1,
          "font-family: var(--font-body); font-weight: 700"),
        ("\\mathbf{\\mathit{x5}}", "x5", 2,
          "font-family: var(--font-body); font-style: italic"),
        ("\\mathit{\\mathbf{x5}}", "x5", 1,
          "font-family: var(--font-body); font-weight: 700")] do
      let a ← mathAlphaArtifact ref fs preamble formula
      let wanted := expected.toList.toArray.map fun c =>
        (face, ((fs.get face).gid c).getD 0, c)
      check ref (formula ++ " preserves default/explicit text Layout faces and glyph IDs")
        (wanted.all (fun (_, gid, _) => gid != 0) && a.glyphs == wanted)
      check ref (formula ++ " preserves default/explicit text PDF scalars")
        (a.pdf.size == 1 &&
          (a.pdf[0]?.map fun (_, text, _, _) => text) == some expected)
      check ref (formula ++ " preserves default/explicit text MathML faces")
        (mathTextLeavesList #[] a.leaves.toList ==
          expected.toList.toArray.map fun c => (String.singleton c, css))

/-- The real elaboration-to-artifact path: an alias must select the
observed Greek range, the selected Fira face must paint those glyph IDs,
the written PDF must decode to those scalars, and typed MathML must agree.
Both default text policy and explicitly symbol-sourced legacy policy leave
the forced `sym…` aliases invariant. -/
def mathAlphaSemanticsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fs ← serifFacesSet |
    failures ref "math alphabet semantics: shipped fonts must load"
  mathAlphaLegacyAliasChecks ref fs
  for preamble in ["", "\\usepackage[mathrm=sym,mathit=sym,mathbf=sym]{unicode-math}"] do
    for row in mathAlphaSemanticCases do
      let label := "math alphabet " ++ row.name ++
        (if preamble.isEmpty then " default" else " symbol-policy")
      let (raw, ds) := elabStr ("\\documentclass{article}\n" ++ preamble ++
        "\n\\pagestyle{empty}\\begin{document}$" ++ row.formula ++ "$\\end{document}")
      let coverage := { fs.mathAlphabets with sources := raw.fonts.mathSources }
      let (doc, ads) := Ir.resolveMathAlphas coverage "Fira Math" raw
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs none doc
      let (_, body, hds) := HtmlDoc.emitTree { fonts := some fs } doc
      check ref (label ++ " has no recovery or missing alphabet")
        (!(ds ++ ads ++ out.diags ++ hds).any fun d =>
          d.severity == .error || d.code == "W0012" || d.code == "W0009" || d.code == "N0018")
      let glyphs := (bodyLines out).flatMap fun line => line.segs.flatMap fun
        | .run f _ _ _ gs _ _ _ _ _ _ => gs.map fun g => (f, g.1, g.2.1)
        | _ => #[]
      let wanted := row.expected.toList.toArray.map fun c =>
        (4, ((fs.get 4).gid c).getD 0, c)
      check ref (label ++ " paints the observed Layout scalars and glyph IDs")
        (wanted.all (fun (_, gid, _) => gid != 0) && glyphs == wanted)
      let pdf := Pdf.write geom fs out.pages doc.info {} out.outline
      match pdfFaceRuns pdf with
      | .error e => failures ref (label ++ " PDF cannot be read: " ++ e)
      | .ok runs =>
        check ref (label ++ " writes the observed PDF scalars")
          (runs.size == 1 && (runs[0]?.map fun (_, text, _, _) => text) == some row.expected)
      let leaves := mathAlphaLeavesList #[] body.toList
      let htmlText := leaves.foldl (fun s n => s ++ nodeTextOne "" n) ""
      check ref (label ++ " writes the observed typed MathML scalars")
        (htmlText == row.htmlExpected.getD row.expected)
      check ref (label ++ " keeps symbol scalars literal in MathML")
        (!leaves.isEmpty && leaves.all mathAlphaLeafNormal)

  -- Removing one canonical Greek range changes only the alias that uses
  -- it. In particular, upright bold coverage cannot pay for default bold
  -- lowercase Greek; the existing N0018 loss must name that selection.
  for missing in [none, some Math.MathAlphabet.bfit, some Math.MathAlphabet.bf] do
    let coverage : Math.MathAlphabetCoverage := { fs.mathAlphabets with
      covered := fs.mathAlphabets.covered.filter fun (a, r) =>
        missing != some a || r != .greekLower }
    for (command, canonical, subject, full) in [
        ("symbf", Math.MathAlphabet.bfit, "math-alpha:bf-default", "𝚪𝜸𝝏𝛁"),
        ("mathbf", Math.MathAlphabet.bfit, "math-alpha:bf-default", "𝚪𝜸𝝏𝛁"),
        ("symbfup", Math.MathAlphabet.bf, "math-alpha:bf", "𝚪𝛄𝛛𝛁")] do
      let label := command ++ " with missing " ++
        (missing.map Math.MathAlphabet.name).getD "none"
      let expected := if missing == some canonical then "𝚪𝛾𝜕𝛁" else full
      let (raw, ds) := elabStr ("\\documentclass{article}\\pagestyle{empty}" ++
        (if command == "mathbf" then "\\usepackage[mathbf=sym]{unicode-math}" else "") ++
        "\\begin{document}$\\" ++ command ++ "{Γγ\\partial\\nabla}$\\end{document}")
      let coverage := { coverage with sources := raw.fonts.mathSources }
      let (doc, ads) := Ir.resolveMathAlphas coverage "Fira Math" raw
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs none doc
      let (_, body, hds) := HtmlDoc.emitTree { fonts := some fs } doc
      let glyphs := (bodyLines out).flatMap fun line => line.segs.flatMap fun
        | .run _ _ _ _ gs _ _ _ _ _ _ => gs.map (·.2.1)
        | _ => #[]
      let htmlText := (mathAlphaLeavesList #[] body.toList).foldl
        (fun s n => s ++ nodeTextOne "" n) ""
      check ref (label ++ " changes precisely the selected Greek range in both artifacts")
        (glyphs == expected.toList.toArray && htmlText == expected)
      match pdfFaceRuns (Pdf.write geom fs out.pages doc.info {} out.outline) with
      | .error e => failures ref (label ++ " PDF cannot be read: " ++ e)
      | .ok runs =>
        check ref (label ++ " writes the selected Greek range to PDF")
          (runs.size == 1 && (runs[0]?.map fun (_, text, _, _) => text) == some expected)
      check ref (label ++ " accounts for a missing range once under its own alphabet")
        ((ads.filter (·.code == "N0018")).map (·.subject) ==
          (if missing == some canonical then #[some subject] else #[]) &&
          !(ds ++ ads ++ out.diags ++ hds).any fun d =>
            d.severity == .error || d.code == "W0012" || d.code == "W0009")

end Tests
