import Tests.CancelMetric

open LeanTex.Core

namespace CancelContext

/-- The driver supplies one font environment to both backends. These
fixtures compare typed artifact attributes, never an elaboration dump. -/
private def contextTree (fonts : Font.FontSet) (doc : Ir.Doc) : Array Html.Node :=
  let geom := Layout.Geom.ofPage doc.page
  let cfg : HtmlDoc.Config := {
    fonts := some fonts
    cancelMetric := fun measures ss st spec body value =>
      Layout.cancelMetric geom fonts ss st spec body value (some measures)
    mathEm := fun measures ss st => Layout.mathEm geom fonts ss st (some measures)
    mathTextEm := fun measures ss st => Layout.mathTextEm geom fonts ss st (some measures) }
  let doc := (Ir.resolveMathAlphas fonts.mathAlphabets "math face" doc).1
  (HtmlDoc.emitTree cfg doc).2.1

/-- Attachment coordinates and physical fraction-rule widths read from
actual HTML elements. Outside font declarations may differ while these
rendered lengths must agree. -/
private def contextGeometry (nodes : Array Html.Node) :=
  elemAttrsList (fun tag => ["svg", "polygon", "mpadded", "mfrac"].contains tag)
    #[] nodes.toList

/-- A local affine size and its evaluated point size ship identical native
ink and identical MathML geometry. The fixed 8pt fraction rule prevents a
wrong em from cancelling out as an otherwise uniform rescaling. -/
private def localContextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let wrappers : Array (String × (String → String)) := #[
    ("minipage", fun s => "\\begin{minipage}{100pt}" ++ s ++ "\\end{minipage}"),
    ("nested minipage", fun s => "\\begin{minipage}{200pt}\\begin{minipage}{0.5\\linewidth}" ++ s ++
      "\\end{minipage}\\end{minipage}"),
    ("table cell", fun s => "\\begin{tabular}{p{100pt}}" ++ s ++ "\\end{tabular}")]
  for (name, wrap) in wrappers do
    for measure in ["linewidth", "columnwidth", "textwidth"] do
      let content := "$u\\cancelto{0g}{\\genfrac{}{}{8pt}{}{x}{x}}v$"
      let source := wrap ("{\\fontsize{0.1\\" ++ measure ++ " + 2pt}{14pt}\\selectfont " ++
        content ++ "}")
      let fixed := wrap ("{\\fontsize{12pt}{14pt}\\selectfont " ++ content ++ "}")
      let (doc, ds) := elabStr (dvDoc "\\usepackage[makeroom]{cancel}" source)
      let (expected, eds) := elabStr (dvDoc "\\usepackage[makeroom]{cancel}" fixed)
      let out := layoutOf fonts doc
      let expectedOut := layoutOf fonts expected
      check ref s!"cancel local context {name}/{measure}: supported source"
        (!(ds ++ eds ++ out.diags ++ expectedOut.diags).any fun d =>
          d.code == "W0012" || d.code == "W0301")
      check ref s!"cancel local context {name}/{measure}: native ink matches 12pt"
        (!(shippedBodyGlyphs out).isEmpty && shippedBodyGlyphs out == shippedBodyGlyphs expectedOut &&
          (bodyLines out).map ShippedInk.polygonsAt ==
            (bodyLines expectedOut).map ShippedInk.polygonsAt)
      let actual := contextGeometry (contextTree fonts doc)
      let wanted := contextGeometry (contextTree fonts expected)
      check ref s!"cancel local context {name}/{measure}: HTML geometry matches native 12pt"
        (!actual.isEmpty && actual == wanted)

/-- Widthless columns divide the remaining measure, and neither a column
nor its siblings change the following paragraph's context. Compare the
shipped ink and typed attachment tree with explicitly evaluated sizes. -/
private def columnContextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let template (size : String) := (elabStr (dvDoc "\\usepackage[makeroom]{cancel}"
    ("{\\fontsize{" ++ size ++ "}{48pt}\\selectfont " ++
      "$u\\cancelto{0g}{\\genfrac{}{}{8pt}{}{x}{x}}v$}"))).1
  let relative := template "0.1\\linewidth + 2pt"
  let widths := #[Ir.BoxWidth.abs (Dim.pt 100), .share, .share]
  let sizes := #["12pt", "17pt", "17pt"]
  let columns := widths.map fun width => (width, relative.body)
  let fixed := widths.zip sizes |>.map fun (width, size) => (width, (template size).body)
  let doc := { relative with
    page := { relative.page with width := Dim.pt 420, hmargin := Dim.pt 10 }
    body := #[.columns columns] ++ relative.body }
  let expected := { doc with body := #[.columns fixed] ++ (template "42pt").body }
  let out := layoutOf fonts doc
  let expectedOut := layoutOf fonts expected
  check ref "cancel local context columns: native shared widths and scope restoration"
    (!(shippedBodyGlyphs out).isEmpty && shippedBodyGlyphs out == shippedBodyGlyphs expectedOut &&
      (bodyLines out).map ShippedInk.polygonsAt ==
        (bodyLines expectedOut).map ShippedInk.polygonsAt)
  let actual := contextGeometry (contextTree fonts doc)
  let wanted := contextGeometry (contextTree fonts expected)
  check ref "cancel local context columns: HTML shared widths and scope restoration"
    (!actual.isEmpty && actual == wanted)

/-- A text-sourced math leaf uses the text em; its neighbouring math glyph
uses the x-height-matched math em. The leaf's emitted font-size must state
that ratio even inside either script style. -/
private def mixedContextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (name, before, after) in [("text", "$", "$"),
      ("script", "$z^{", "}$"), ("scriptscript", "$z^{z^{", "}}$")] do
    let (doc, _) := elabStr (dvDoc "\\usepackage{cancel}"
      ("\\begin{minipage}{100pt}{\\fontsize{12pt}{14pt}\\selectfont " ++ before ++
        "u\\mathsf{M}" ++ after ++ "}\\end{minipage}"))
    let glyphs := shippedBodyGlyphs (layoutOf fonts doc)
    let textEm := (glyphs.find? (·.scalar == 'M')).map (·.size)
    let mathEm := (glyphs.find? (·.scalar == '𝑢')).map (·.size)
    let leaves := elemNodesList (· == "mi") #[] (contextTree fonts doc).toList
    let leaf := leaves.find? fun node => MathMl.nodeChars #[] node == #['M']
    check ref s!"cancel mixed context {name}: native text and math sizes differ"
      (textEm.isSome && mathEm.isSome && textEm != mathEm)
    check ref s!"cancel mixed context {name}: HTML states the native text/math ratio"
      ((do
        let t ← textEm
        let m ← mathEm
        let node ← leaf
        let css ← (attrValuesOf (· == "mi") "style" node)[0]?
        return hasStr css s!"font-size: {MathMl.measuredEm t m}").getD false)

/-- Focused artifact guards for local measurement and mixed text/math ems. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let some fonts ← serifFacesSet |
    check ref "cancel context fixture faces load" false
  localContextChecks ref fonts
  columnContextChecks ref fonts
  mixedContextChecks ref fonts

end CancelContext
