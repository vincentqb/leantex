import Tests.Support

open LeanTex.Core

namespace Tests

private def tableSource (env cell : String) : String :=
  let args := if env == "tabular" then "{lc}"
    else if env == "tabular*" then "{200pt}{lc}" else "{200pt}{lX}"
  dvDoc "\\usepackage{tabularx,booktabs}\n\\newcommand{\\Head}{\\multicolumn{2}{c}{Heading}}\n"
    ("\\begin{" ++ env ++ "}" ++ args ++ "\\toprule\n" ++ cell ++
      "\\\\\n\\bottomrule\\end{" ++ env ++ "}")

/-- Direct and macro spellings of a spanning cell have the same table
context, HTML span, and shipped geometry in every supported table environment. -/
def tableContextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let spans (doc : Ir.Doc) := doc.body.flatMap fun b =>
    attrValuesOf (fun tag => tag == "td" || tag == "th") "colspan" (HtmlDoc.blockNode {} b)
  for env in Compat.tableEnvs do
    let (direct, dd) := elabStr (tableSource env "\\multicolumn{2}{c}{Heading}")
    let (indirect, md) := elabStr (tableSource env "\\Head")
    let dout := layoutOf fonts direct
    let mout := layoutOf fonts indirect
    let dc := censusOf #[] dout
    let mc := censusOf #[] mout
    t s!"table context {env}: no misplaced span or error"
      ((dd ++ md ++ dout.diags ++ mout.diags).all fun d =>
        d.code != "W0337" && d.severity != .error)
    t s!"table context {env}: both HTML cells span two columns"
      (spans direct == #["2"] && spans indirect == #["2"])
    t s!"table context {env}: each head ships once at the same position"
      (pageOccurs dc 0 "Heading" == 1 && pageOccurs mc 0 "Heading" == 1 &&
        lineXOf dc 0 "Heading" == lineXOf mc 0 "Heading" &&
        shippedBodyGlyphs dout == shippedBodyGlyphs mout)

end Tests
