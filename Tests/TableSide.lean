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
`flushright`, and the declarations `\centering`, `\raggedright` and
`\raggedleft`. -/
private def tableScopes : List (String × String × String) :=
  [("no scope", "", ""),
   ("flushleft", "\\begin{flushleft}", "\\end{flushleft}"),
   ("center", "\\begin{center}", "\\end{center}"),
   ("flushright", "\\begin{flushright}", "\\end{flushright}"),
   ("centering", "{\\centering ", "\\par}"),
   ("raggedright", "{\\raggedright ", "\\par}"),
   ("raggedleft", "{\\raggedleft ", "\\par}")]

/-- A `lcr` table whose rows differ in width in every column, plus a `p`
column whose cells are one short line each. Every word is invented. -/
private def sideTable : String :=
  "\\begin{tabular}{lcrp{0.2\\linewidth}}\n" ++
  "LeftLongCell & MiddleLongCell & RightLongCell & ParLongCell \\\\\n" ++
  "Lf & Md & Rt & Pa \\\\\n" ++
  "\\end{tabular}"

/-- A `p` cell whose paragraph wraps over several lines. Every word is
invented. -/
private def wrapTable : String :=
  "\\begin{tabular}{p{5cm}}\nSeveral invented words make a box long enough to " ++
  "wrap across a few lines so the edges show whether it justifies. \\\\\n\\end{tabular}"

/-- Where the wrapping paragraph's lines but its last end on the first page:
the right edge of each line's last glyph run, the lead line left out. -/
private def wrapEnds (out : Layout.Out) : Array Dim.Sp :=
  let lines := ((out.pages[0]?.map (·.lines)).getD #[]).filter fun l =>
    !l.furniture && hasGlyphRun l && !hasStr (lineText l) "Lead"
  lines.pop.filterMap fun l => (lineRuns l).back?.map fun (_, _, x, w) => x + w

/-- **A cell sets by its column spec, whatever scope its table stands in**
(`Ir.cellSpec`; `Pdf.table_cell_side_agree`). On the page an `l` cell's
lines start at its column's left edge, an `r` cell's end at its right edge,
a `c` cell's centres coincide and a `p` cell starts flush left, under every
scope and in both a flow and a frame; in the typed tree every cell — `left`
included — states its spec's `text-align`. And a `p` cell justifies whatever
scope its table stands in: its wrapped lines all end at the cell's right
edge, as lualatex sets them under `\raggedright` (`\@arrayparboxrestore`
zeroes `\rightskip`). The defects it names: a text column under
`\centering` centred in the HTML, where a cell that stated nothing inherited
its scope's `text-align`, while the page set it flush left; under
`\raggedleft` the page set an `l` column's cells flush right, the scope's
side leaking into each cell's paragraph; and under `\raggedright` a wrapped
`p` cell set ragged, the scope's justification leaking the same way. -/
def tableSideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wants : Array String := #["text-align: left", "text-align: center",
    "text-align: right", "text-align: left"]
  for (scope, opening, closing) in tableScopes do
    for (kind, src) in [("article", dvDoc "\\page{ protrusion = off }\n"
        ("Lead line.\n\n" ++ opening ++ wrapTable ++ closing)),
        ("frame", deck169 "\\theme{default}\n\\page{ protrusion = off }"
          ("\\begin{frame}\nLead line.\n\n" ++ opening ++ wrapTable ++ closing ++
            "\n\\end{frame}"))] do
      let ends := wrapEnds (layoutOf oneFace (elabStr src).1)
      t s!"table side {kind} {scope}: a p cell's wrapped lines end at its right edge"
        (match ends[0]? with
         | some e => 3 ≤ ends.size &&
           ends.foldl max e - ends.foldl min e ≤ Dim.pt 1 / 10
         | none => false)
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

/-- A formal table's lengths as lualatex sets them, by class: `\the` of each
in a synthetic preamble after `\usepackage{booktabs}`, before any face is
declared (TeX Live 2026), in sp. A 10pt deck measures booktabs' em and ex in
lmsans10 (4.44pt x-height), a 10pt article in lmroman10 (4.31pt), a 12pt
one in lmroman12 (5.172pt); `\tabcolsep` and `\doublerulesep` are the
class's own 6pt and 2pt. -/
private def tableLengthsLualatex : List (String × String × List (String × String)) :=
  let weights10 := [("heavyrulewidth", "0.80002"), ("lightrulewidth", "0.50003"),
    ("cmidrulewidth", "0.29999"), ("cmidrulekern", "5.0")]
  let fixed := [("tabcolsep", "6.0"), ("doublerulesep", "2.0"), ("abovetopsep", "0.0"),
    ("belowbottomsep", "0.0")]
  [("deck", "\\documentclass[10pt,aspectratio=169]{beamer}\n",
     [("belowrulesep", "2.88597"), ("aboverulesep", "1.77597")] ++ weights10 ++ fixed),
   ("article", "\\documentclass{article}\n",
     [("belowrulesep", "2.80147"), ("aboverulesep", "1.72397")] ++ weights10 ++ fixed),
   ("article 12pt", "\\documentclass[12pt]{article}\n",
     [("belowrulesep", "3.36176"), ("aboverulesep", "2.06876"), ("heavyrulewidth", "0.96002"),
      ("lightrulewidth", "0.60004"), ("cmidrulewidth", "0.35999"), ("cmidrulekern", "6.0")] ++
       fixed)]

/-- A printed `\the` value in points as TeX reads it back: the nearest
65536th. -/
private def spOfPt (printed : String) : Int :=
  match Decl.parseDecimal printed with
  | some (m, sc) => (m * 65536 * 2 + (sc : Int)) / (2 * (sc : Int))
  | none => 0

/-- A small formal table under every kind of rule. Every word is invented. -/
private def ruledTable : String :=
  "\\begin{tabular}{lr}\n\\toprule\nHeadWord & Count \\\\\n\\midrule\n" ++
  "FirstRow & 12 \\\\\n\\cmidrule(lr){1-2}\nSecondRow & 34 \\\\\n\\bottomrule\n\\end{tabular}"

/-- A rule's fallback in an emitted stylesheet: the value `var(--name, …)`
falls back to, as the formal table's rules spell it. -/
private def fallbackOf (css name : String) : Option String :=
  match (css.splitOn s!"var(--{name}, ").drop 1 with
  | rest :: _ => some ((rest.splitOn ")").headD "").trimAscii.toString
  | [] => none

/-- A decimal value with its unit, in thousandths of the unit. -/
private def milliOf (value unit : String) : Option Int := do
  unless value.endsWith unit do none
  let (m, sc) ← Decl.parseDecimal (value.dropEnd unit.length).toString
  return m * 1000 / (sc : Int)

/-- **A table's lengths are lualatex's, in both artifacts.** booktabs fixes
its rule weights and seps once, as it loads, in the preamble's font — Latin
Modern at the class size, never the table's own face or size — and the page
sets an undeclared table by exactly those values (`Layout.tableLength`,
within TeX's rounding of `.65`, `.08` and their peers to a 65536th): a table
declaring them through `\setlength` ships the very page of the one declaring
nothing. The stylesheet states the same values (`Pdf.table_length_agree`):
an article's fallbacks in points, a deck's as their share of the stage, the
unit its type is set in, and a declared table length in the spelling of its
default. The defects it names: the page resolved booktabs' `.65ex` in the
document's body face, so a deck set in a face with a tall x-height opened its
rules 0.5pt wider than lualatex, and the deck's stage spelled `\tabcolsep` in
paper points, under half its share of the PDF page. -/
def tableLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (kind, cls, lengths) in tableLengthsLualatex do
    let body := "Lead line.\n\n" ++ ruledTable
    let wrap (pre : String) := if kind == "deck" then
        cls ++ pre ++ "\\begin{document}\n\\begin{frame}\n" ++ body ++
          "\n\\end{frame}\n\\end{document}"
      else cls ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"
    let (doc, _) := elabStr (wrap "")
    for (name, printed) in lengths do
      let got := Layout.tableLength none doc.preambleFace name
      let want := spOfPt printed
      t s!"table length {kind} {name}: the page's default is lualatex's ({got} against {want} sp)"
        ((got - want).natAbs ≤ 4)
    let declared := String.join (lengths.map fun (name, printed) =>
      s!"\\setlength\{\\{name}}\{{printed}pt}\n")
    let (declDoc, _) := elabStr (wrap declared)
    let c := censusOf #[] (layoutOf oneFace doc)
    let d := censusOf #[] (layoutOf oneFace declDoc)
    let near (a b : Option Dim.Sp) : Bool := match a, b with
      | some x, some y => (x - y).natAbs ≤ 8
      | _, _ => false
    t s!"table length {kind}: a table declaring lualatex's lengths ships the undeclared page"
      ((pageRuleSegs c 0).size == 4 && (pageRuleSegs c 0).size == (pageRuleSegs d 0).size &&
        ((pageRuleSegs c 0).zip (pageRuleSegs d 0)).all (fun (a, b) =>
          (a.1 - b.1).natAbs ≤ 8 && (a.2 - b.2).natAbs ≤ 8) &&
        ["HeadWord", "FirstRow", "SecondRow"].all fun w =>
          near (lineYOf c 0 w) (lineYOf d 0 w) && near (lineXOf c 0 w) (lineXOf d 0 w))
    let (page, _) := HtmlDoc.emit {} doc
    for name in ["belowrulesep", "aboverulesep", "heavyrulewidth", "tabcolsep"] do
      let want := Layout.tableLength none doc.preambleFace name
      let fb := fallbackOf page name
      t s!"table length {kind} {name}: the stylesheet's fallback states the page's length ({fb})"
        (match fb with
         | some v =>
           if kind == "deck" then
             (milliOf v "vh").any fun m =>
               m * doc.page.height ≤ want * 100000 && want * 100000 < (m + 1) * doc.page.height
           else (milliOf v "pt").any fun m => (m * 65536 - want * 1000).natAbs ≤ 32768
         | none => false)
  -- A deck that declares a table length its default already holds ships the
  -- stylesheet it shipped without the declaration's spelling changing.
  let deckSrc (pre : String) :=
    "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++ pre ++
      "\\begin{document}\n\\begin{frame}\n" ++ ruledTable ++ "\n\\end{frame}\n\\end{document}"
  let (plain, _) := HtmlDoc.emit {} (elabStr (deckSrc "")).1
  let (declared, _) := HtmlDoc.emit {} (elabStr (deckSrc "\\setlength{\\tabcolsep}{6pt}\n")).1
  t "table length deck: a declared tabcolsep is spelled as its default"
    ((fallbackOf plain "tabcolsep").any fun v => hasStr declared s!"--tabcolsep: {v};")

end Tests
