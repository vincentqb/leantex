import Tests.CancelAlignment

open LeanTex.Core

namespace CancelMetric

/-- Independent source snippets share the driver's alphabet resolution;
no round trip through dumped IR supplies the expected artifact. -/
def formula (fonts : Font.FontSet) (source : String) : Option Math.MList :=
  let doc := (elabStr (dvDoc "\\usepackage{cancel}" ("$" ++ source ++ "$"))).1
  firstFormula (Ir.resolveMathAlphas fonts.mathAlphabets "math face" doc).1

/-- Compare the measured mark and target with the shipped page, modulo
only the common translation that page placement and reserved room add.
The target hull is decoded independently from the emitted glyphs. -/
def agrees (fonts : Font.FontSet) (out : Layout.Out) (em : Int)
    (input : Math.CancelIn) (spec : Math.CancelSpec) (target : String) : Bool :=
  (do
    let #[line] := bodyLines out | throw "expected one body line"
    let shipped := ShippedInk.polygonsAt line
    let geom := Math.cancelGeom .to spec.room input
    let some actual := (shipped[0]?).bind (·[0]?) | throw "missing shipped mark"
    let some expected := (geom.polys[0]?).bind (·[0]?) | throw "missing measured mark"
    let dx := actual.1 - expected.1
    let dy := actual.2 - expected.2
    let all := shippedBodyGlyphs out
    let #[anchor] := all.filter (·.scalar == '𝑢') | throw "missing style witness"
    let glyphs := all.filter fun g => target.toList.contains g.scalar
    unless String.ofList (glyphs.toList.map (·.scalar)) == target do
      throw "target census differs"
    let ink ← ShippedInk.targetInk fonts glyphs
    return em > 0 && anchor.size == em &&
      shipped == geom.polys.map (fun ps => ps.map fun (x, y) => (x + dx, y + dy)) &&
      ink.left == dx + geom.valueX + input.vleft &&
      ink.right == dx + geom.valueX + input.vright &&
      ink.bottom == dy + geom.valueY + input.vbot &&
      ink.top == dy + geom.valueY + input.vtop : Except String Bool).toOption.getD false

/-- Source neighbours witness the reserved interval. Operand ink is read
from the shipped outlines independently; signed spacing must not make it
disappear from the measured envelope or cross the following source glyph. -/
def bodyRoomAgrees (fonts : Font.FontSet) (out : Layout.Out)
    (metric : Math.CancelMetric) (spec : Math.CancelSpec) : Bool :=
  (do
    let #[line] := bodyLines out | throw "expected one body line"
    let polys := ShippedInk.polygonsAt line
    let geom := Math.cancelGeom .to spec.room metric.input
    let some actual := (polys[0]?).bind (·[0]?) | throw "missing shipped mark"
    let some expected := (geom.polys[0]?).bind (·[0]?) | throw "missing measured mark"
    let dx := actual.1 - expected.1
    let all := shippedBodyGlyphs out
    let body ← ShippedInk.targetInk fonts (all.filter (·.scalar == '𝑥'))
    let (left, right) ← CancelAlignment.constructEndpoints out
    return body.left == dx + geom.shift + metric.bodyLeft &&
      body.right == dx + geom.shift + metric.bodyRight &&
      (!spec.room || body.inRoom left right) : Except String Bool).toOption.getD false

/-- Ambient declarations reach the existing native resolver. The stale
callback with an empty style history is a negative control: it must be
rejected on the same shipped page when the active size changes. -/
def contextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let fixed (n : Int) : Dim.Affine Dim.Measure :=
    .lit { width := .ofSp (Dim.pt n) }
  let contexts : Array (String × String × Array Ir.Style × Bool) := #[
    ("large", "\\Large ", #[.size "Large"], true),
    ("absolute", "\\fontsize{24pt}{29pt}\\selectfont ",
      #[.fontSize (fixed 24) (fixed 29)], true),
    ("relative-after-large", "\\Large\\fontsize{1.2em}{1.4em}\\selectfont ",
      #[.size "Large", .fontSize (.lit { width := { em := 1200 } })
        (.lit { width := { em := 1400 } })], true),
    ("italic", "\\itshape ", #[.italic], false),
    ("bold-large", "\\bfseries\\Large ", #[.bold, .size "Large"], true)]
  let spec : Math.CancelSpec := { room := true }
  for (name, sourcePrefix, history, differentSize) in contexts do
    for (st, before, after) in [
        (Math.MathStyle.text false, "$", "$"),
        (.script false, "$z^{", "}$")] do
      for operand in ["x", "\\genfrac{}{}{8pt}{}{x}{x}"] do
        let (doc, ds) := elabStr (dvDoc "\\usepackage[makeroom]{cancel}"
          (sourcePrefix ++ before ++ "u\\cancelto{0\\!g}{" ++ operand ++ "}v" ++ after))
        let geom := Layout.Geom.ofPage doc.page
        let out := layoutOf fonts doc geom
        check ref s!"cancel metric context: {name}/{operand} source is supported"
          (!(ds ++ out.diags).any fun d => d.code == "W0012" || d.code == "W0301")
        let some body := formula fonts operand |
          check ref s!"cancel metric context: {name} missing operand" false
        let some value := formula fonts "0\\!g" |
          check ref s!"cancel metric context: {name} missing target" false
        let metric := Layout.cancelMetric geom fonts history st spec body value
        check ref s!"cancel metric context: {name}/{operand} agrees with shipped attachment"
          (metric.any fun m => agrees fonts out m.em m.input spec "0𝑔")
        if differentSize then
          let stale := Layout.cancelMetric geom fonts #[] st spec body value
          check ref s!"cancel metric context: {name}/{operand} rejects a stale default size"
            (!(stale.any fun m => agrees fonts out m.em m.input spec "0𝑔"))

/-- Negative spacing separates an operand's logical advance from its ink.
The callback exposes both, and native reservation contains that ink. -/
def signedRoomChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for operand in ["\\!x", "x\\!\\!\\!\\!", "\\!\\!x\\!\\!\\!\\!"] do
    for room in [false, true] do
      let spec : Math.CancelSpec := { room }
      let opts := if room then "makeroom" else "overlap"
      let (doc, _) := elabStr (dvDoc ("\\usepackage[" ++ opts ++ "]{cancel}")
        ("$u\\cancelto{0\\!g}{" ++ operand ++ "}v$"))
      let geom := Layout.Geom.ofPage doc.page
      let out := layoutOf fonts doc geom
      let measured := do
        let body ← formula fonts operand
        let value ← formula fonts "0\\!g"
        Layout.cancelMetric geom fonts #[] (.text false) spec body value
      check ref s!"cancel metric signed source: {operand}/{opts} preserves target and marks"
        (measured.any fun m => agrees fonts out m.em m.input spec "0𝑔")
      check ref s!"cancel metric signed room: {operand}/{opts} carries operand ink beyond advance"
        (measured.any fun m => bodyRoomAgrees fonts out m spec)

end CancelMetric

open CancelMetric in
/-- A backend callback must measure the same operand, target, style and
font as the native assembly. Shipped polygons, glyph ink and the current
math em witness that agreement across aspect ratios and package options. -/
def CancelMetric.checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  check ref "cancel metric refuses an absent math face"
    ((Layout.cancelMetric {} oneFace #[] (.text false) {} .nil .nil).isNone)
  let styles : Array (String × Math.MathStyle × String × String) := #[
    ("text", .text false, "$", "$"),
    ("display", .display false, "\\[", "\\]"),
    ("script", .script false, "$z^{", "}$"),
    ("scriptscript", .scriptscript false, "$z^{z^{", "}}$")]
  for points in [9, 17] do
    for (name, st, before, after) in styles do
      for operand in ["x", "x+x+x+x+x+x", "\\frac{x}{\\frac{x}{x}}"] do
        for options in ["overlap", "makeroom,thicklines", "makeroom,samesize"] do
          let spec := (Math.CancelSpec.ofOptions (options.splitOn ",")).1
          let (doc, _) := elabStr (dvDoc ("\\usepackage[" ++ options ++ "]{cancel}")
            (before ++ "u\\cancelto{0g}{" ++ operand ++ "}v" ++ after))
          let geom := { Layout.Geom.ofPage doc.page with fontSize := Dim.pt points }
          let out := layoutOf fonts doc geom
          let measured := do
            let body ← formula fonts operand
            let value ← formula fonts "0g"
            Layout.cancelMetric geom fonts #[] st spec body value
          check ref s!"cancel metric shares shipped geometry: {points}/{name}/{operand}/{options}"
            (measured.any fun metric => agrees fonts out metric.em metric.input spec "0𝑔")

  contextChecks ref fonts
  signedRoomChecks ref fonts
