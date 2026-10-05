import Tests.Support

open LeanTex.Core

namespace Tests

/-- A formula's plaintext reading must retain operation and operand
boundaries. These invented expressions previously collapsed into strings
of digits on pages without a math font. The same reading belongs to SVG
labels and the document's accessible structure. -/
def formulaFloorChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let fonts := { fonts with math := none }
  let cases : List (String × String) :=
    [("\\frac{1}{2}", "(1)/(2)"),
     ("\\frac{\\frac{1}{2}}{3}", "((1)/(2))/(3)"),
     ("{12}_3^4", "(12)_(3)^(4)"),
     ("\\sqrt{12}", "sqrt(12)"),
     ("\\sqrt[3]{12}", "root(3)(12)"),
     ("\\binom{1}{2}", "(stack(1;2))"),
     ("\\cancelto{0}{12}", "cancelto(12;0)"),
     ("\\begin{matrix}1&2\\\\3&4\\end{matrix}", "[[1,2],[3,4]]"),
     ("\\left(12\\right)", "(12)"),
     ("\\hat{12}", "hat(12)")]
  for (source, expected) in cases do
    let sourceDoc := metricDoc ("$" ++ source ++ "$")
    let (doc, _) := elabStr sourceDoc
    let actual := pageTextOf fonts sourceDoc
    check ref s!"formula floor PDF: expected {expected}, got {actual}" (actual == expected)
    check ref s!"formula floor structure: {expected}" ((Struct.ofDoc doc).text == expected)
    let labelDoc := metricDoc ("\\begin{tikzpicture}\\node at (0,0) {$" ++ source ++
      "$};\\end{tikzpicture}")
    let (_, _, _, labelText) := sourceArtifacts fonts labelDoc
    check ref s!"formula floor SVG: expected {expected}, got {labelText}" (labelText == expected)
  -- Invisible delimiters and layout parameters are valid nonprinting
  -- syntax. Raw-source punctuation is not a sound content premise.
  for source in ["\\big.", "\\left.\\right.", "\\quad", "{}",
      "\\genfrac{}{}{0pt}{}{}{}"] do
    let raws := (Parse.parse "formula.tex" (Lex.lex "formula.tex" source).1).1
    check ref s!"nonprinting formula parses: {source}" (MathParse.parseMath false raws).isOk
    let sourceDoc := metricDoc ("$" ++ source ++ "$")
    let actual := pageTextOf fonts sourceDoc
    check ref s!"nonprinting formula stays empty: {source}, got {actual}" (actual == "")
    check ref s!"nonprinting formula structure: {source}"
      ((Struct.ofDoc (elabStr sourceDoc).1).text == "")

end Tests
