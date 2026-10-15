module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim

namespace Tests

/-- Each row's cells in an emitted tree, by first class and side class (`HtmlDoc.cellClasses`);
covered `\multicolumn` cells have no element. -/
private def rowCellSides (nodes : Array Html.Node) : Array (Array (Option String)) :=
  (elemNodesList (· == "tr") #[] nodes.toList).map fun tr => match tr with
    | .elem _ _ kids => kids.filterMap fun k => match k with
      | .elem tag attrs _ =>
        if tag == "td" || tag == "th" then
          some ((attrs.find? (·.1 == "class")).map fun (_, v) => (v.splitOn " ").headD "")
        else none
      | _ => none
    | _ => #[]

/-- The scopes a table can stand in, as source, page and stylesheet read them. -/
private def tableScopes : List (String × String × String) :=
  [("no scope", "", ""),
   ("flushleft", "\\begin{flushleft}", "\\end{flushleft}"),
   ("center", "\\begin{center}", "\\end{center}"),
   ("flushright", "\\begin{flushright}", "\\end{flushright}"),
   ("centering", "{\\centering ", "\\par}"),
   ("raggedright", "{\\raggedright ", "\\par}"),
   ("raggedleft", "{\\raggedleft ", "\\par}")]

/-- An `lcr` table whose rows differ in width in every column, plus a `p` column of one short line
per cell. -/
private def sideTable : String :=
  "\\begin{tabular}{lcrp{0.2\\linewidth}}\n" ++
  "LeftLongCell & MiddleLongCell & RightLongCell & ParLongCell \\\\\n" ++
  "Lf & Md & Rt & Pa \\\\\n" ++
  "\\end{tabular}"

/-- A `p` cell whose paragraph wraps over several lines. -/
private def wrapTable : String :=
  "\\begin{tabular}{p{5cm}}\nSeveral invented words make a box long enough to " ++
  "wrap across a few lines so the edges show whether it justifies. \\\\\n\\end{tabular}"

/-- The wrapping paragraph's lines on the first page, lead line excluded: each left edge and last
run's right edge. -/
private def wrapLines (out : Layout.Out) : Array (Dim.Sp × Dim.Sp) :=
  let lines := ((out.pages[0]?.map (·.lines)).getD #[]).filter fun l =>
    !l.furniture && hasGlyphRun l && !hasStr (lineText l) "Lead"
  lines.filterMap fun l => (lineRuns l).back?.map fun (_, _, x, w) => (l.x, x + w)

/-- Where the wrapping paragraph's lines but its last end on the first page. -/
private def wrapEnds (out : Layout.Out) : Array Dim.Sp :=
  (wrapLines out).pop.map (·.2)

/-- How far a set of edges spreads: its largest less its smallest. -/
private def edgeSpread (xs : Array Dim.Sp) : Dim.Sp :=
  match xs[0]? with
  | some x => xs.foldl max x - xs.foldl min x
  | none => 0

/-- A cell sets by its column spec, whatever scope its table stands in (`Ir.cellSpec`;
`Pdf.table_cell_side_agree`). -/
def tableSideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wants : Array String := #["bt-left", "bt-center", "bt-right", "bt-left"]
  for (scope, opening, closing) in tableScopes do
    for (kind, src) in [("article", dvDoc "\\page{ protrusion = off }\n"
        ("Lead line.\n\n" ++ opening ++ wrapTable ++ closing)),
        ("frame", deck169 "\\theme{default}\n\\page{ protrusion = off }"
          ("\\begin{frame}\nLead line.\n\n" ++ opening ++ wrapTable ++ closing ++
            "\n\\end{frame}"))] do
      let ends := wrapEnds (layoutOf oneFace (elabStr src).1)
      t s!"table side {kind} {scope}: a p cell's wrapped lines end at its right edge"
        (3 ≤ ends.size && edgeSpread ends ≤ Dim.pt 1 / 10)
    for (kind, wrap) in [("article", fun (body : String) => dvDoc "" body),
        ("frame", fun body => deck169Frame body)] do
      -- A lead line first: a group opening a frame body is beamer's title argument.
      let src := wrap ("Lead line.\n\n" ++ opening ++ sideTable ++ closing)
      let (doc, ds) := elabStr src
      t s!"table side {kind} {scope}: the source elaborates without loss"
        (ds.all fun d => d.severity != .error && d.code != "W0301" && d.code != "W0302")
      let (page, _) := HtmlDoc.emit {} doc
      let (_, body, _) := HtmlDoc.emitTree {} doc
      let rows := rowCellSides body
      t s!"table side {kind} {scope}: every HTML cell states its column's side"
        (rows.size == 2 && rows.all fun cells =>
          cells.size == wants.size && (cells.zip wants).all fun (got, want) => got == some want)
      t s!"table side {kind} {scope}: each side class's rule declares its side"
        ([("bt-left", "left"), ("bt-center", "center"), ("bt-right", "right")].all fun (cls, side) =>
          (screenRuleOf page s!"table.booktabs td.{cls}, table.booktabs th.{cls}").any
            (hasStr · s!"text-align: {side};"))
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

/-- A 4 cm paragraph column under a modifier, with one wrapping cell. -/
private def raggedTable (modifier : String) : String :=
  "\\begin{tabular}{" ++ modifier ++ "p{4cm}}\nSeveral invented words make a cell long " ++
  "enough to wrap across a few lines so the edges show whether it justifies. \\\\\n\\end{tabular}"

/-- A paragraph column sets as its modifier declares (`Ir.ColSpec.ragged`, `Layout.cellParagraph`),
and a natural column ignores it. -/
def tableRaggedChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let width := Dim.mm 40
  for (kind, wrap) in [("article", fun (body : String) =>
        dvDoc "\\usepackage{array}\n\\page{ protrusion = off }\n" body),
      ("frame", fun body =>
        deck169 "\\usepackage{array}\n\\theme{default}\n\\page{ protrusion = off }"
          ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}"))] do
    for (name, modifier, side) in [("raggedright", ">{\\raggedright\\arraybackslash}", "bt-left"),
        ("raggedleft", ">{\\raggedleft\\arraybackslash}", "bt-right"),
        ("centering", ">{\\centering\\arraybackslash}", "bt-center")] do
      let (doc, ds) := elabStr (wrap ("Lead line.\n\n" ++ raggedTable modifier))
      t s!"table ragged {kind} {name}: the modifier is read without loss"
        (ds.all fun d => d.severity != .error && d.code != "W0104" && d.code != "W0301")
      let lines := wrapLines (layoutOf oneFace doc)
      let lefts := lines.map (·.1)
      let rights := lines.map (·.2)
      let lo := lefts.foldl min (lefts[0]?.getD 0)
      let hi := rights.foldl max (rights[0]?.getD 0)
      t s!"table ragged {kind} {name}: the cell wraps over several lines within its column"
        (3 ≤ lines.size && hi - lo ≤ width)
      let ok := match name with
        | "raggedright" => edgeSpread lefts == 0 && edgeSpread rights.pop > Dim.pt 1
        | "raggedleft" => edgeSpread rights == 0 && edgeSpread lefts.pop > Dim.pt 1
        | _ => edgeSpread (lines.map fun (a, b) => a + b) ≤ 4 && edgeSpread lefts > Dim.pt 1
      t s!"table ragged {kind} {name}: the lines set ragged on the declared side" ok
      let (_, body, _) := HtmlDoc.emitTree {} doc
      t s!"table ragged {kind} {name}: the HTML cell states the declared side"
        (rowCellSides body == #[#[some side]])
    let natural := "\\begin{tabular}{>{\\raggedleft}l>{\\centering}ll<{\\raggedleft}}\n" ++
      "Abundance & Carousel & Elephant \\\\\nBit & Dot & Fig \\\\\n\\end{tabular}"
    let (doc, _) := elabStr (wrap ("Lead line.\n\n" ++ natural))
    let c := censusOf #[] (layoutOf oneFace doc)
    t s!"table ragged {kind}: a natural column's cells keep its letter's side under a modifier"
      ([("Abundance", "Bit"), ("Carousel", "Dot"), ("Elephant", "Fig")].all fun (a, b) =>
        (lineXOf c 0 a).isSome && lineXOf c 0 a == lineXOf c 0 b)
    let (_, body, _) := HtmlDoc.emitTree {} doc
    t s!"table ragged {kind}: a natural column's HTML cells state its letter's side"
      (rowCellSides body == #[#[some "bt-left", some "bt-left", some "bt-left"],
        #[some "bt-left", some "bt-left", some "bt-left"]])

/-- A table's rows stand the print leading apart in both artifacts (`HtmlDoc.printLeadingMilli`,
`HtmlDoc.printLeading_exact`). -/
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
        (hasStr ((screenRuleOf page "table.booktabs").getD "") s!"line-height: {factor};")
      let geom := Layout.Geom.ofPage doc.page
      let c := censusOf #[] (layoutOf oneFace doc)
      let pitch := Ir.leadingFor geom.fontSize geom.leading
      t s!"table leading {kind} {name}: the page's rows stand the leading apart"
        (match lineYOf c 0 "RowOne", lineYOf c 0 "RowTwo", lineYOf c 0 "RowThree" with
         | some a, some b, some d => b - a == pitch && d - b == pitch
         | _, _, _ => false)

/-- A formal table's lengths in sp as lualatex sets them after `\usepackage{booktabs}`, by class. -/
private def tableLengthsLualatex : List (String × String × List (String × String)) :=
  let weights10 := [("heavyrulewidth", "0.80002"), ("lightrulewidth", "0.50003"),
    ("cmidrulewidth", "0.29999"), ("cmidrulekern", "5.0")]
  let weights11 := [("heavyrulewidth", "0.876"), ("lightrulewidth", "0.54753"),
    ("cmidrulewidth", "0.32848"), ("cmidrulekern", "5.47499")]
  let fixed := [("tabcolsep", "6.0"), ("doublerulesep", "2.0"), ("abovetopsep", "0.0"),
    ("belowbottomsep", "0.0")]
  [("deck", "\\documentclass[10pt,aspectratio=169]{beamer}\n",
     [("belowrulesep", "2.88597"), ("aboverulesep", "1.77597")] ++ weights10 ++ fixed),
   ("deck 11pt", "\\documentclass[aspectratio=169]{beamer}\n",
     [("belowrulesep", "3.16014"), ("aboverulesep", "1.94469")] ++ weights11 ++ fixed),
   ("article", "\\documentclass{article}\n",
     [("belowrulesep", "2.80147"), ("aboverulesep", "1.72397")] ++ weights10 ++ fixed),
   ("article 11pt", "\\documentclass[11pt]{article}\n",
     [("belowrulesep", "3.06761"), ("aboverulesep", "1.88774")] ++ weights11 ++ fixed),
   ("article 12pt", "\\documentclass[12pt]{article}\n",
     [("belowrulesep", "3.36176"), ("aboverulesep", "2.06876"), ("heavyrulewidth", "0.96002"),
      ("lightrulewidth", "0.60004"), ("cmidrulewidth", "0.35999"), ("cmidrulekern", "6.0")] ++
       fixed)]

/-- A printed `\the` value in points read back as TeX reads it: the nearest 65536th. -/
private def spOfPt (printed : String) : Int :=
  match Decl.parseDecimal printed with
  | some (m, sc) => (m * 65536 * 2 + (sc : Int)) / (2 * (sc : Int))
  | none => 0

/-- A small formal table under every kind of rule. -/
private def ruledTable : String :=
  "\\begin{tabular}{lr}\n\\toprule\nHeadWord & Count \\\\\n\\midrule\n" ++
  "FirstRow & 12 \\\\\n\\cmidrule(lr){1-2}\nSecondRow & 34 \\\\\n\\bottomrule\n\\end{tabular}"

/-- A table's source in a class's synthetic document after a lead line: in a frame for a deck, in
the body otherwise. -/
private def ruledSource (kind cls pre : String) (table : String := ruledTable) : String :=
  let body := "Lead line.\n\n" ++ table
  if kind.startsWith "deck" then
    cls ++ pre ++ "\\begin{document}\n\\begin{frame}\n" ++ body ++ "\n\\end{frame}\n\\end{document}"
  else cls ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- The value an emitted stylesheet's `var(--name, …)` falls back to. -/
private def fallbackOf (css name : String) : Option String :=
  match (css.splitOn s!"var(--{name}, ").drop 1 with
  | rest :: _ => some ((rest.splitOn ")").headD "").trimAscii.toString
  | [] => none

/-- A decimal value with its unit, in thousandths of the unit. -/
private def milliOf (value unit : String) : Option Int := do
  unless value.endsWith unit do none
  let (m, sc) ← Decl.parseDecimal (value.dropEnd unit.length).toString
  return m * 1000 / (sc : Int)

/-- Whether a stylesheet length spells `want` as its share of the document's basis: stage height on
a deck, class size elsewhere. -/
private def statesShare (doc : Ir.Doc) (v : String) (want : Dim.Sp) : Bool :=
  match HtmlDoc.lengthBasisOf doc with
  | .stage h => (milliOf v "vh").any fun m =>
    m * h ≤ want * 100000 && want * 100000 < (m + 1) * h
  | .classSize s => (milliOf v "rem").any fun m => 2 * (want * 1000 - m * s).natAbs ≤ s

/-- A table's lengths are lualatex's in both artifacts (`Layout.tableLength`,
`Pdf.table_length_agree`), preamble em and ex lengths fixed in the preamble's font. -/
def tableLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (kind, cls, lengths) in tableLengthsLualatex do
    let (doc, _) := elabStr (ruledSource kind cls "")
    for (name, printed) in lengths do
      let got := Layout.tableLength none doc.preambleFace name
      let want := spOfPt printed
      t s!"table length {kind} {name}: the page's default is lualatex's ({got} against {want} sp)"
        ((got - want).natAbs ≤ 4)
    let declared := String.join (lengths.map fun (name, printed) =>
      s!"\\setlength\{\\{name}}\{{printed}pt}\n")
    let (declDoc, _) := elabStr (ruledSource kind cls declared)
    let c := censusOf #[] (layoutOf oneFace doc)
    let d := censusOf #[] (layoutOf oneFace declDoc)
    -- Each length is within TeX's rounding and a position sums a dozen, so 32 sp bounds it.
    let near (a b : Option Dim.Sp) : Bool := match a, b with
      | some x, some y => (x - y).natAbs ≤ 32
      | _, _ => false
    t s!"table length {kind}: a table declaring lualatex's lengths ships the undeclared page"
      ((pageRuleSegs c 0).size == 4 && (pageRuleSegs c 0).size == (pageRuleSegs d 0).size &&
        ((pageRuleSegs c 0).zip (pageRuleSegs d 0)).all (fun (a, b) =>
          (a.1 - b.1).natAbs ≤ 32 && (a.2 - b.2).natAbs ≤ 8) &&
        ["HeadWord", "FirstRow", "SecondRow"].all fun w =>
          near (lineYOf c 0 w) (lineYOf d 0 w) && near (lineXOf c 0 w) (lineXOf d 0 w))
    let (page, _) := HtmlDoc.emit {} doc
    for name in ["belowrulesep", "aboverulesep", "heavyrulewidth", "tabcolsep"] do
      let want := Layout.tableLength none doc.preambleFace name
      let fb := fallbackOf page name
      t s!"table length {kind} {name}: the stylesheet's fallback states the page's length as its share ({fb})"
        (fb.any (statesShare doc · want))
  -- lualatex prints 4.31pt for 1ex and 5.0pt for .5em in a 10pt article, in a `\small` table too.
  let article := "\\documentclass{article}\n\\usepackage{booktabs}\n"
  let small := "{\\small\n" ++ ruledTable ++ "\n\\par}"
  let (rel, _) := elabStr (ruledSource "article" article
    "\\setlength{\\belowrulesep}{1ex}\n\\setlength{\\aboverulesep}{0.5em}\n" small)
  let (abs, _) := elabStr (ruledSource "article" article
    "\\setlength{\\belowrulesep}{4.31pt}\n\\setlength{\\aboverulesep}{5pt}\n" small)
  t "table length: a preamble's 1ex and .5em are fixed as lualatex fixes them"
    ((rel.tokens.find? "belowrulesep").map (·.width) == some (Dim.Length.ofSp (spOfPt "4.31")) &&
      (rel.tokens.find? "aboverulesep").map (·.width) == some (Dim.Length.ofSp (spOfPt "5.0")))
  let cr := censusOf #[] (layoutOf oneFace rel)
  let ca := censusOf #[] (layoutOf oneFace abs)
  t "table length: a small table under a preamble's 1ex ships the page of its 4.31pt"
    ((pageRuleSegs cr 0).size == 4 && pageRuleSegs cr 0 == pageRuleSegs ca 0 &&
      ["HeadWord", "FirstRow", "SecondRow"].all fun w => lineYOf cr 0 w == lineYOf ca 0 w)
  let deckSrc (pre inner : String) :=
    "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++ pre ++
      "\\begin{document}\n\\begin{frame}\n" ++ inner ++ ruledTable ++
      "\n\\end{frame}\n\\end{document}"
  let (plain, _) := HtmlDoc.emit {} (elabStr (deckSrc "" "")).1
  let (declared, _) := HtmlDoc.emit {} (elabStr (deckSrc "\\setlength{\\tabcolsep}{6pt}\n" "")).1
  let (inFrame, _) := HtmlDoc.emit {} (elabStr (deckSrc "" "\\setlength{\\tabcolsep}{6pt}\n")).1
  t "table length deck: a declared tabcolsep is spelled as its default"
    ((fallbackOf plain "tabcolsep").any fun v => hasStr declared s!"--tabcolsep: {v};")
  t "table length deck: a frame's declared tabcolsep is spelled as its default"
    ((fallbackOf plain "tabcolsep").any fun v => hasStr inFrame s!"--tabcolsep: {v}")

/-- The two rule-to-baseline distances of `ruledTable` as lualatex's `\showbox` prints them, by
class. -/
private def tableStrutLualatex : List (String × String × String × String) :=
  [("deck", "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usepackage{booktabs}\n",
     "11.28593", "5.37601"),
   ("article", "\\documentclass{article}\n\\usepackage{booktabs}\n", "11.20143", "5.32401")]

/-- A table's rows stand on LaTeX's row strut (`Layout.strutBox`, `Layout.tableStrut`). -/
def tableStrutChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (kind, cls, under, over) in tableStrutLualatex do
    let (doc, _) := elabStr (ruledSource kind cls "")
    let c := censusOf #[] (layoutOf oneFace doc)
    let rules := pageRuleSegs c 0
    let rows := ["HeadWord", "FirstRow", "SecondRow"].filterMap (lineYOf c 0 ·)
    let near (got want : Dim.Sp) : Bool := (got - want).natAbs ≤ 8
    t s!"table strut {kind}: the page ships four rules and three rows"
      (rules.size == 4 && rows.length == 3)
    -- rule k stands above row k, and row k above rule k + 1; a rule's segment is its band's bottom and thickness
    let pairs : List (Dim.Sp × Option Dim.Sp × Option Dim.Sp) :=
      (rows.zip (List.range 3)).map fun (y, k) =>
        (y, (rules[k]?).map (fun (r : Dim.Sp × Dim.Sp) => r.1),
          (rules[k + 1]?).map fun (r : Dim.Sp × Dim.Sp) => r.1 - r.2)
    t s!"table strut {kind}: each row stands lualatex's distance below the rule above it"
      (pairs.all fun (y, above, _) => above.any fun ry => near (y - ry) (spOfPt under))
    t s!"table strut {kind}: each rule stands lualatex's distance below the row above it"
      (pairs.all fun (y, _, below) => below.any fun top => near (top - y) (spOfPt over))

/-- A face declared before booktabs loads is a named loss (W0398), and the warning's premise holds
two builds apart. -/
def tableFaceOrderChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let booktabsDiags (cls pre post : String) : Array Diag :=
    let src := cls ++ "\\usepackage{fontspec}\n" ++ pre ++ "\\usepackage{booktabs}\n" ++ post ++
      "\\begin{document}\nx\n\\end{document}"
    (elabStr src).2.filter fun d => d.code == "W0398" || hasStr d.message "booktabs"
  let article := "\\documentclass{article}\n"
  let deck := "\\documentclass[10pt,aspectratio=169]{beamer}\n"
  let main := "\\setmainfont{Invented Serif}\n"
  let sans := "\\setsansfont{Invented Sans}\n"
  let fires (ds : Array Diag) : Bool :=
    ds.size == 1 && ds.all fun d => d.code == "W0398" && d.subject == some "package:booktabs"
  t "table face order: booktabs after an article's main face fires W0398 once"
    (fires (booktabsDiags article main ""))
  t "table face order: booktabs after a deck's sans face fires W0398 once"
    (fires (booktabsDiags deck sans ""))
  t "table face order: booktabs before the face fires nothing"
    (!(booktabsDiags article "" main).any (·.code == "W0398"))
  t "table face order: booktabs after a deck's main face alone fires nothing"
    (!(booktabsDiags deck main "").any (·.code == "W0398"))
  let order (before after : String) :=
    article ++ "\\usepackage{fontspec}\n" ++ before ++ "\\usepackage{booktabs}\n" ++ after ++
      "\\begin{document}\nLead line.\n\n" ++ ruledTable ++ "\n\\end{document}"
  let pdfOf (doc : Ir.Doc) : ByteArray :=
    let geom := Layout.Geom.ofPage doc.page
    Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info
  let (early, earlyDs) := elabStr (order main "")
  let (late, lateDs) := elabStr (order "" main)
  t "table face order: the face before the load and after it ship byte-identical pages"
    (pdfOf early == pdfOf late && earlyDs.any (·.code == "W0398") &&
      !lateDs.any (·.code == "W0398"))

end Tests
