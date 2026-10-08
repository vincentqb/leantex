import Tests.Support

open LeanTex.Core LeanTex.Core.Dim

namespace Tests

/-- The cells of every row of an emitted tree, in row order: each cell's
tag and `style` attribute, the covered `\multicolumn` cells having no
element of their own. -/
private def rowCellStyles (nodes : Array Html.Node) : Array (Array (Option String)) :=
  (elemNodesList (· == "tr") #[] nodes.toList).map fun tr => match tr with
    | .elem _ _ kids => kids.filterMap fun k => match k with
      | .elem tag attrs _ =>
        if tag == "td" || tag == "th" then some ((attrs.find? (·.1 == "style")).map (·.2))
        else none
      | _ => none
    | _ => #[]

/-- The scopes a table can stand in, as the source spells them and as the
page and the stylesheet read them: none, `flushleft`, `center`,
`flushright`, and the declarations `\centering` and `\raggedleft`. -/
private def tableScopes : List (String × String × String) :=
  [("no scope", "", ""),
   ("flushleft", "\\begin{flushleft}", "\\end{flushleft}"),
   ("center", "\\begin{center}", "\\end{center}"),
   ("flushright", "\\begin{flushright}", "\\end{flushright}"),
   ("centering", "{\\centering ", "\\par}"),
   ("raggedleft", "{\\raggedleft ", "\\par}")]

/-- A `lcr` table whose rows differ in width in every column, plus a `p`
column whose cells are one short line each. Every word is invented. -/
private def sideTable : String :=
  "\\begin{tabular}{lcrp{0.2\\linewidth}}\n" ++
  "LeftLongCell & MiddleLongCell & RightLongCell & ParLongCell \\\\\n" ++
  "Lf & Md & Rt & Pa \\\\\n" ++
  "\\end{tabular}"

/-- **A cell sets by its column spec, whatever scope its table stands in**
(`Ir.cellSpec`; `Pdf.table_cell_side_agree`). On the page an `l` cell's
lines start at its column's left edge, an `r` cell's end at its right edge,
a `c` cell's centres coincide and a `p` cell starts flush left, under every
scope and in both a flow and a frame; in the typed tree every cell — `left`
included — states its spec's `text-align`. The defect it names: a text
column under `\centering` centred in the HTML, where a cell that stated
nothing inherited its scope's `text-align`, while the page set it flush
left; and under `\raggedleft` the page set an `l` column's cells flush
right, the scope's side leaking into each cell's paragraph. -/
def tableSideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wants : Array String := #["text-align: left", "text-align: center",
    "text-align: right", "text-align: left"]
  for (scope, opening, closing) in tableScopes do
    for (kind, wrap) in [("article", fun (body : String) => dvDoc "" body),
        ("frame", fun body => deck169Frame body)] do
      -- A lead line first: a group opening a frame body is beamer's title
      -- argument, as `\begin{frame}{...}` reads it.
      let src := wrap ("Lead line.\n\n" ++ opening ++ sideTable ++ closing)
      let (doc, ds) := elabStr src
      t s!"table side {kind} {scope}: the source elaborates without loss"
        (ds.all fun d => d.severity != .error && d.code != "W0301" && d.code != "W0302")
      let (_, body, _) := HtmlDoc.emitTree {} doc
      let rows := rowCellStyles body
      t s!"table side {kind} {scope}: every HTML cell states its column's side"
        (rows.size == 2 && rows.all fun cells =>
          cells.size == wants.size && (cells.zip wants).all fun (got, want) => got == some want)
      let c := censusOf #[] (layoutOf oneFace doc)
      let x (s : String) := lineXOf c 0 s
      let r (s : String) := lineRightOf c 0 s
      t s!"table side {kind} {scope}: the l column's cells start at one left edge"
        ((x "LeftLongCell").isSome && x "LeftLongCell" == x "Lf")
      t s!"table side {kind} {scope}: the r column's cells end at one right edge"
        ((r "RightLongCell").isSome && r "RightLongCell" == r "Rt")
      t s!"table side {kind} {scope}: the c column's cells share one centre"
        (match x "MiddleLongCell", r "MiddleLongCell", x "Md", r "Md" with
         | some a, some b, some p, some q => (a + b - (p + q)).natAbs ≤ 2
         | _, _, _, _ => false)
      t s!"table side {kind} {scope}: the p column's cells start flush left"
        ((x "ParLongCell").isSome && x "ParLongCell" == x "Pa")

/-- **A table's rows stand the print leading apart in both artifacts**
(`HtmlDoc.printLeadingMilli`, `HtmlDoc.printLeading_exact`). On the page,
consecutive one-line rows' baselines are `Ir.leadingFor` of the table's size
apart, as LaTeX's `\@arstrutbox` is one `\baselineskip`; in the stylesheet
the formal table declares the same ratio as its `line-height`, under the
default spread and a declared `\linespread` alike. The defect it names: the
HTML rows inherited the screen's prose lead (`bodyLeadingMilli`, 1.45), so
a deck's table stood a fifth taller on its stage than on its page and its
last rows fell below the stage while the PDF page held it. -/
def tableLeadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let rows := "\\begin{tabular}{l}\nRowOne \\\\\nRowTwo \\\\\nRowThree \\\\\n\\end{tabular}"
  for (name, pre, factor) in [("default spread", "", "1.2"),
      ("declared spread", "\\linespread{1.25}\n", "1.5")] do
    for (kind, src) in [("article", dvDoc pre rows), ("frame", deck169 pre
        ("\\begin{frame}\n" ++ rows ++ "\n\\end{frame}"))] do
      let (doc, _) := elabStr src
      let (page, _) := HtmlDoc.emit {} doc
      t s!"table leading {kind} {name}: the formal table declares the print leading"
        (hasStr ((cssRuleOf page "table.booktabs").getD "") s!"line-height: {factor};")
      let geom := Layout.Geom.ofPage doc.page
      let c := censusOf #[] (layoutOf oneFace doc)
      let pitch := Ir.leadingFor geom.fontSize geom.leading
      t s!"table leading {kind} {name}: the page's rows stand the leading apart"
        (match lineYOf c 0 "RowOne", lineYOf c 0 "RowTwo", lineYOf c 0 "RowThree" with
         | some a, some b, some d => b - a == pitch && d - b == pitch
         | _, _, _ => false)

end Tests
