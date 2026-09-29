import Tests.Lengths

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

mutual

private def cqiOwnersOne (owner : String) (out : Array String) : Html.Node → Array String
  | .text _ | .style _ | .script _ _ => out
  | .elem tag attrs kids =>
    let owns := attrs.any fun (k, v) => k == "style" && hasStr v "container-type: inline-size"
    let owner := if owns then
        (attrs.find? (·.1 == "class")).map (·.2) |>.getD tag
      else owner
    let reads := attrs.any fun (_, v) => hasStr v "cqi"
    let out := if reads then out.push owner else out
    cqiOwnersList owner out kids.toList

private def cqiOwnersList (owner : String) (out : Array String) : List Html.Node → Array String
  | [] => out
  | n :: rest => cqiOwnersList owner (cqiOwnersOne owner out n) rest

end

/-- `\fontsize{size}{leading}\selectfont` carries both dimensions through
one affine style and resolves them where the styled text is set. -/
def fontSizeAffineChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let sizes (body : String) := metricRunSizes (metricOut oneFace body)
  t "fontsize accepts LaTeX's unitless point spelling"
    (sizes "{\\fontsize{12}{14.4}\\selectfont Alpha}" == #[Dim.pt 12] &&
      !(warnCodes (metricDoc "{\\fontsize{12}{14.4}\\selectfont Alpha}")).contains "W0301")
  t "fontsize follows the engine's declaration-at-site NFSS convention"
    (sizes "{\\fontsize{12}{14.4}Alpha}" == #[Dim.pt 12])
  let localBody :=
    "\\begin{minipage}{100pt}{\\fontsize{0.1\\linewidth + 2pt}{14pt}\\selectfont Alpha}\\end{minipage}"
  t "fontsize resolves linewidth at the minipage where the run is set"
    (sizes localBody == #[Dim.pt 12])
  let lines := bodyLines (metricOut oneFace
    "{\\fontsize{12pt}{18pt}\\selectfont Alpha\\\\Bravo}")
  t "fontsize leading sets the baseline distance"
    (lines.size == 2 && lines[1]!.y - lines[0]!.y == Dim.pt 18)
  let zeroLines := bodyLines (metricOut oneFace
    "{\\fontsize{12pt}{0pt}\\selectfont Alpha\\\\Bravo}")
  t "fontsize preserves an explicit zero baseline distance"
    (zeroLines.size == 2 && zeroLines[1]!.y - zeroLines[0]!.y == 0)
  let table := metricOut oneFace
    "{\\fontsize{12pt}{18pt}\\selectfont\\begin{tabular}{l}Alpha\\\\Bravo\\end{tabular}}"
  t "a fontsize declaration before a block scopes every glyph in the block"
    (!(metricRunSizes table).isEmpty && (metricRunSizes table).all (· == Dim.pt 12))
  let html := (HtmlDoc.emit {} (elabStr (metricDoc
    "{\\fontsize{12pt}{18pt}\\selectfont Alpha}")).1).1
  t "HTML projects fontsize and leading from the typed style"
    (hasStr html "font-size:12pt" && hasStr html "line-height:18pt")
  let localDoc := (elabStr (metricDoc localBody)).1
  let (_, localTree, _) := HtmlDoc.emitTree {} localDoc
  let localHtml := (HtmlDoc.emit {} localDoc).1
  t "HTML resolves a local fontsize against its nearest box container"
    (hasStr localHtml "font-size:calc(10cqi + 2pt)" &&
      cqiOwnersList "" #[] localTree.toList == #["column"])
  let topDoc := (elabStr (metricDoc
    "{\\fontsize{0.1\\linewidth + 2pt}{14pt}\\selectfont Alpha}")).1
  let (_, topTree, _) := HtmlDoc.emitTree {} topDoc
  t "top-level HTML cqi lengths resolve against the document measure"
    (cqiOwnersList "" #[] topTree.toList == #["main"])
  let cellBody :=
    "\\begin{tabular}{p{100pt}}{\\fontsize{0.1\\linewidth + 2pt}{14pt}\\selectfont Alpha}\\end{tabular}"
  let cellDoc := (elabStr (metricDoc cellBody)).1
  let (_, cellTree, _) := HtmlDoc.emitTree {} cellDoc
  let cellHtml := (HtmlDoc.emit {} cellDoc).1
  t "fontsize resolves against a table cell in both artifacts"
    (sizes cellBody == #[Dim.pt 12] &&
      cqiOwnersList "" #[] cellTree.toList == #["cell-measure"] &&
      hasStr cellHtml "<div class=\"cell-measure\" style=\"container-type: inline-size\">")
  let plainCellHtml := (HtmlDoc.emit {} (elabStr (metricDoc
    "\\begin{tabular}{p{100pt}}Alpha\\end{tabular}")).1).1
  t "a table cell with no context unit gets no query container"
    (!hasStr plainCellHtml "cell-measure")
  let nonlinear := dvE (metricDoc
    "{\\fontsize{\\linewidth * \\columnwidth}{14pt}\\selectfont Alpha}")
  t "nonlinear fontsize arithmetic is refused by name"
    (nonlinear.any fun d => d.code == "E0331" && hasStr d.message "length times a length")
  let register := dvE (metricDoc
    "{\\fontsize{\\wd\\strutbox}{14pt}\\selectfont Alpha}")
  t "register fontsize arithmetic is refused by name"
    (register.any fun d => d.code == "E0331" && hasStr d.message "register")
