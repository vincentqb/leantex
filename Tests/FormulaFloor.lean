import Tests.Support

open LeanTex.Core

namespace Tests

private def formulaTrees (doc : Ir.Doc) : Array String :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (elemNodesList (· == "math") #[] body.toList).filterMap fun node =>
    match node with
    | .elem _ attrs _ =>
      if (HtmlDoc.attrOf? attrs "data-tex").isSome then some (Html.render node 0)
      else none
    | _ => none

/-- A formula's plaintext reading must retain operation and operand
boundaries. These invented expressions previously collapsed into strings
of digits on PDF pages without a math font. Accessible structure keeps that
reading too. HTML diagram labels retain the complete mathematical tree used
in prose instead of painting the fallback notation. -/
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
    let labelText := pageTextOf fonts labelDoc
    check ref s!"formula floor diagram PDF: expected {expected}, got {labelText}"
      (labelText == expected)
    let proseMath := formulaTrees doc
    let labelMath := formulaTrees (elabStr labelDoc).1
    check ref s!"formula diagram HTML retains the complete prose math tree: {source}"
      (proseMath.size == 1 && labelMath == proseMath)
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
