module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! A GFM pipe table is the booktabs table, on both artifacts. -/

namespace Tests.MarkdownTables

/-- One shipped table cell: its tag, its text, and the side its class states. -/
structure Cell where
  tag : String
  text : String
  align : Option String
  deriving BEq, Repr

/-- The `text-align` a cell's side class sets (`HtmlDoc.cellSideRule`). -/
def alignOf (attrs : Array (String × String)) : Option String :=
  (attrs.find? (·.1 == "class")).bind fun (_, v) =>
    (v.splitOn " ").findSome? fun c =>
      [Ir.HAlign.left, .center, .right].findSome? fun h =>
        if c == HtmlDoc.cellSideClass h then some h.align else none

def groupRows (kids : Array Html.Node) : Array (Array Cell) :=
  kids.filterMap fun r => match r with
    | .elem "tr" _ cells => some (cells.filterMap fun c => match c with
      | .elem tag attrs ks =>
        if tag == "th" || tag == "td" then
          some { tag, text := nodeTextList "" ks.toList, align := alignOf attrs }
        else none
      | _ => none)
    | _ => none

/-- Every table a markdown page ships: its head rows and its body rows. -/
def tablesOf (src : String) : Array (Array (Array Cell) × Array (Array Cell)) :=
  let (_, body, _) := HtmlDoc.emitTree {} (elabMd src).1
  (elemNodesList (· == "table") #[] body.toList).map fun t => match t with
    | .elem _ _ kids =>
      let group (g : String) : Array (Array Cell) :=
        kids.foldl (fun acc k => match k with
          | .elem tag _ rs =>
            if tag == g then
              let rows := groupRows rs
              acc ++ rows
            else acc
          | _ => acc) #[]
      (group "thead", group "tbody")
    | _ => (#[], #[])

def texts (rows : Array (Array Cell)) : List (List String) :=
  rows.toList.map fun r => r.toList.map (·.text)

def head (src : String) : List (List String) :=
  ((tablesOf src)[0]?.map (texts ·.1)).getD []

def bodyRows (src : String) : List (List String) :=
  ((tablesOf src)[0]?.map (texts ·.2)).getD []

/-- A markdown table too wide for its measure narrows its columns as a browser's automatic layout
does, and its cells wrap. -/
def wrapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let note := "Rewrites every gadget it is handed and writes each one back in the order of \
its label, then counts them"
  let wide := s!"| Key | Count of rewritten gadgets | Note |\n|---|--:|---|\n\
| `sort_all` | 12 | {note} |\n| `quiet` | 3 | quiet |\n"
  let (doc, _) := elabMd wide
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let left := doc.page.hmargin
  let measure := doc.page.width - 2 * doc.page.hmargin
  t "a too-wide markdown table keeps every glyph inside its measure"
    (!lines.isEmpty && (lines.flatMap lineRuns).all fun (_, _, x, w) =>
      left - Dim.pt 1 ≤ x && x + w ≤ left + measure + Dim.pt 1)
  let ruleWidths := lines.flatMap fun l => l.segs.filterMap fun s => match s with
    | .rule w _ _ _ => some w
    | _ => none
  t s!"and its rules span the measure, the columns filling it ({ruleWidths})"
    (ruleWidths.size == 3 && ruleWidths.all fun w => measure - 8 ≤ w && w ≤ measure)
  let painted := String.intercalate "\n" (lines.map lineText).toList
  t "every word of its narrowed cells reaches the page, unhyphenated"
    ((note.splitOn " ").all (hasStr painted ·) && !hasStr painted "-\n")
  let lineOf (needle : String) : Option Layout.LineOut :=
    lines.find? fun l => (lineRuns l).any fun (_, s, _, _) => s == needle
  let noteX := (lineOf "Rewrites").map (·.x)
  let noteLines := lines.filter fun l => some l.x == noteX
  t s!"a long cell wraps onto lines of its own column ({noteLines.size})"
    (noteLines.size ≥ 4)
  let some face := fonts.fonts[0]?
    | t "the table face loads" false
  let space : Dim.Sp := Dim.pt 10 * face.spaceAdvance / face.unitsPerEm
  t "a wrapping cell is ragged: its word spaces keep their natural width"
    (noteLines.all fun l => l.segs.all fun s => match s with
      | .gap w _ => w ≤ space + Dim.pt 1 / 2
      | _ => true)
  t "a single-word column keeps words whole, at the measure's edge"
    ((lineOf "sort_all").any (·.x == left) && (lineOf "Key").any (·.x == left))
  let countRight := (lineOf "12").map fun l => l.x + l.setWidth
  let countLines := lines.filter fun l => (lineRuns l).any fun (_, s, _, _) =>
    ["Count", "rewritten", "gadgets", "12", "3"].contains s
  t s!"a right-aligned wrapping head hangs from the column's right edge ({countLines.size})"
    (countLines.size ≥ 4 && countLines.all fun l => some (l.x + l.setWidth) == countRight)
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let cells := elemNodesList (fun tag => tag == "td" || tag == "th") #[] body.toList
  let attrsOf (n : Html.Node) : Array (String × String) := match n with
    | .elem _ attrs _ => attrs
    | _ => #[]
  let nowrap (n : Html.Node) : Bool := (attrsOf n).any fun (k, v) =>
    k == "class" && hasStr v "bt-nowrap"
  let (_, texBody, _) := HtmlDoc.emitTree {} (elabStr (dvDoc ""
    "\\begin{tabular}{ll}\nKey & Note \\\\\n\\end{tabular}")).1
  t "markdown HTML cells may wrap; a tex table's natural cells may not"
    (!cells.isEmpty && !cells.any nowrap
      && (elemNodesList (· == "td") #[] texBody.toList).all nowrap)
  let nums (k : Nat) : String := String.intercalate " | "
    ((List.range 9).map fun j => s!"{k}.{1000 + 37 * j + k}{j}")
  let figures := "| label | a | b | c | d | e | f | g | h | i |\n\
|---|---|---|---|---|---|---|---|---|---|\n" ++
    s!"| sorter[a=500,b=0.01] | {nums 1} |\n| sorter[a=50,b=0.01] | {nums 2} |\n"
  let (raws, readDiags) := Md.read "t.md" figures
  let (located, _, _) := Elab.runRawsSpanned "t.md" raws readDiags
  let fout := layoutOf fonts located
  let flines := bodyLines fout
  let rowYs := (flines.filterMap fun l => if (lineText l).startsWith "1." then some l.y else none)
  let cellsAt (y : Dim.Sp) : Array Layout.LineOut :=
    (flines.filter (·.y == y)).qsort (·.x < ·.x)
  t s!"a table too wide by its words alone keeps them whole, no cell overlapping ({rowYs.size})"
    (!rowYs.isEmpty && (rowYs.eraseReps).all fun y =>
      let cs := cellsAt y
      cs.size == 10 && (cs.zip (cs.extract 1 cs.size)).all fun (a, b) => a.x + a.setWidth < b.x)
  let over := fout.diags.filter (·.kind == .W0338)
  t s!"and it fits at a smaller step, so nothing names it ({over.size})"
    (over.isEmpty && (flines.all fun l => l.size < located.page.fontSize))
  let rowOut := layoutOf fonts (elabStr (dvDoc ""
    "\\begin{tabular}{lll}\n\\toprule\nshort & {\\LARGE Tall} & low \\\\\n\\bottomrule\n\\end{tabular}")).1
  let baselineOf (needle : String) : Option Dim.Sp := (bodyLines rowOut).findSome? fun l =>
    if hasStr (lineText l) needle then some l.y else none
  t "a row's cells share one baseline despite a taller first line"
    ((baselineOf "Tall").isSome && baselineOf "short" == baselineOf "Tall"
      && baselineOf "low" == baselineOf "Tall")

/-- The shipped lines that share a baseline, each sorted left to right. -/
def rowsOfLines (lines : Array Layout.LineOut) : Array (Array Layout.LineOut) :=
  let ys := (lines.map (·.y)).toList.eraseDups.toArray
  ys.map fun y => (lines.filter (·.y == y)).qsort (·.x < ·.x)

/-- Do any two of a baseline's lines overlap on the page? -/
def rowOverlaps (row : Array Layout.LineOut) : Bool :=
  (row.zip (row.extract 1 row.size)).any fun (a, b) => b.x < a.x + a.setWidth

/-- A narrowed cell sets its words inside its column, with plain TeX's ragged right skip
(`Layout.narrowedSkip`). -/
def narrowCellChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let why := "The ordering pass reads every widget it is handed and writes each \
one back in the order of its name, then tallies them"
  let src := "| Gadget family name | Handler method | Kind | Why |\n|---|---|---|---|\n\
| Ordering pass | `_reorder_every_widget_name_` | LE | " ++ why ++ " |\n\
| Folding with limits | `_fold_names_before_tallying_widgets_` | EQ in pass | For limited \
pairs that do not reach every shelf, the folded names must equal the tallied ones |\n"
  let (doc, _) := elabMd src
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let right := doc.page.width - doc.page.hmargin
  t s!"no two cells' lines overlap on a baseline ({(rowsOfLines lines).size} baselines)"
    (!lines.isEmpty && !(rowsOfLines lines).any rowOverlaps)
  t "no cell line passes the table's right edge"
    (lines.all fun l => l.x + l.setWidth ≤ right + Dim.pt 1)
  t "and no line is overfull"
    (!(out.diags.any (·.kind == .W0005)))
  t "every word of the narrowed cells reaches the page"
    (let painted := String.intercalate "\n" (lines.map lineText).toList
     (why.splitOn " ").all (hasStr painted ·) && hasStr painted "_reorder_every_widget_name_")
  let words := ["network", "protocol", "handler", "registry"]
  let single := "| Words | Prose |\n|---|---|\n| " ++ " ".intercalate words ++ " | " ++
    " ".intercalate (List.replicate 12 why) ++ " |\n"
  let sout := layoutOf fonts (elabMd single).1
  let slines := bodyLines sout
  let yOf (w : String) : Option Dim.Sp :=
    (slines.find? fun l => (lineRuns l).any (·.2.1 == w)).map (·.y)
  let ys := words.filterMap yOf
  t s!"a narrowed cell sets one word a line when only one fits ({ys})"
    (ys.length == 4 && ys.eraseDups.length == 4)
  t "and overlaps no neighbour"
    (!(rowsOfLines slines).any rowOverlaps && !(sout.diags.any (·.kind == .W0005)))
  let texDoc := (elabStr (dvDoc "\\usepackage{array}\n"
    ("\\begin{tabular}{>{\\raggedright\\arraybackslash}p{2.1cm}l}\n" ++
      " ".intercalate words ++ " & next \\\\\n\\end{tabular}"))).1
  let texOut := layoutOf fonts texDoc (pats := Hyphen.forTag texDoc.info.locale.tag)
  let tlines := bodyLines texOut
  t s!"a tex ragged p column wraps inside its column, over no neighbour ({tlines.size} lines)"
    (tlines.size ≥ 4 && !(rowsOfLines tlines).any rowOverlaps
      && !(texOut.diags.any (·.kind == .W0005)))

/-- A markdown table too wide for its words sets at the largest smaller step at which they fit
(`Layout.tableFit`), else centred over both margins. -/
def fitStepChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let row (k : Nat) : String := " | ".intercalate
    ((List.range 9).map fun j => s!"{k}{j}.{4000 + 61 * j + k}")
  let src (label : String) := "| label | p | q | r | s | t | u | v | w | z |\n\
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|\n" ++
    s!"| {label} | {row 1} |\n| {label}x | {row 2} |\n"
  let fitsIn (doc : Ir.Doc) (avail : Dim.Sp) := Layout.tableFit (Layout.Geom.ofPage doc.page)
    fonts {} (Layout.tableLength none doc.preambleFace "tabcolsep") avail
  let fitsAt (doc : Ir.Doc) := fitsIn doc (Layout.Geom.ofPage doc.page).textWidth
  let tableOf (doc : Ir.Doc) := doc.body.findSome? fun b => match b with
    | .table cols padL padR rows _ spans => some (cols, padL, padR, rows, spans)
    | _ => none
  let tableOf? (doc : Ir.Doc) := Ir.foldBlocks (fun found b => found.orElse fun _ => match b with
      | .table cols padL padR rows _ spans => some (cols, padL, padR, rows, spans)
      | _ => none) (fun found _ => found) none doc.body
  let decide (doc : Ir.Doc) : Option Layout.TableFit := (tableOf doc).map
    fun (cols, padL, padR, rows, spans) => fitsAt doc cols padL padR rows spans
  let sizes (out : Layout.Out) : List Dim.Sp :=
    (((bodyLines out).filter fun l => (lineText l).any Char.isDigit).toList.map (·.size)).eraseDups
  let (mid, _) := elabMd (src "sorter")
  let mout := layoutOf fonts mid
  let mfit := decide mid
  t s!"a table whose words pass the measure at its body size steps down ({repr mfit})"
    (mfit.any fun f => f.step.isSome && f.overhang == 0)
  let stepped := (mfit.bind (·.step)).map fun s =>
    Ir.scaleStepIn mid.page.scale mid.page.fontSize s
  t s!"and its cells set at that step on the page ({sizes mout})"
    (stepped.isSome && sizes mout == stepped.toList)
  let left := mid.page.hmargin
  let right := mid.page.width - mid.page.hmargin
  t "every glyph of the stepped table stays inside the measure"
    ((bodyLines mout).all fun l => left - Dim.pt 1 ≤ l.x && l.x + l.setWidth ≤ right + Dim.pt 1)
  let wide := src "sorter[alpha=500,beta=0.01,gamma=7,delta=2]"
  let (big, _) := elabMd wide
  let bout := layoutOf fonts big
  let bfit := decide big
  t s!"a table too wide at its floor sets at the floor and overhangs ({repr bfit})"
    (bfit.any fun f => f.step == Layout.tableSteps.getLast? && f.overhang > 0)
  let blines := bodyLines bout
  let xs := blines.map (·.x)
  let ends := blines.map fun l => l.x + l.setWidth
  let lo := xs.foldl min (xs[0]?.getD 0)
  let hi := ends.foldl max (ends[0]?.getD 0)
  t s!"its overhang is centred across both margins ({left - lo} left, {hi - right} right)"
    (lo < left && right < hi && (left - lo - (hi - right)).natAbs ≤ (Dim.pt 1).natAbs)
  t "and every glyph stays on the paper"
    (0 ≤ lo && hi ≤ big.page.width)
  t "the page names the overhang at the table's first cell"
    ((bout.diags.filter (·.kind == .W0338)).size == 1)
  let cfgOf (doc : Ir.Doc) : HtmlDoc.Config := { tableFit := fun avail cols padL padR rows spans =>
    let f := fitsIn doc avail cols padL padR rows spans
    (f.step, f.overhang > 0) }
  let tableAttrs (doc : Ir.Doc) : Array (String × String) :=
    let (_, body, _) := HtmlDoc.emitTree (cfgOf doc) doc
    match ((elemNodesList (· == "table") #[] body.toList)[0]? : Option Html.Node) with
    | some (.elem _ attrs _) => attrs
    | _ => #[]
  let styleOf (doc : Ir.Doc) := (HtmlDoc.attrOf? (tableAttrs doc) "style").getD ""
  let classOf (doc : Ir.Doc) := (HtmlDoc.attrOf? (tableAttrs doc) "class").getD ""
  let emMilli (style : String) : Option Nat :=
    (style.splitOn ";").findSome? fun decl => match decl.splitOn ":" with
      | [k, v] =>
        if k.trimAscii.toString != "font-size" then none
        else
          let v := (v.trimAscii.toString.dropEnd "em".length).toString
          match v.splitOn "." with
          | [w, f] => some (w.toNat! * 1000 + ((f ++ "00").take 3).toString.toNat!)
          | [w] => some (w.toNat! * 1000)
          | _ => none
      | _ => none
  let stepMilli (doc : Ir.Doc) (fit : Option Layout.TableFit) : Option Nat :=
    (fit.bind (·.step)).bind fun s => doc.page.scale.lookup s
  t s!"the HTML table states the page's step as its font size ({styleOf mid})"
    ((stepMilli mid mfit).isSome && emMilli (styleOf mid) == stepMilli mid mfit
      && !hasStr (classOf mid) "bt-overhang")
  t s!"and centres the floor's overhang on paper ({classOf big})"
    ((stepMilli big bfit).isSome && emMilli (styleOf big) == stepMilli big bfit
      && hasStr (classOf big) "bt-overhang")
  let figures (k : Nat) : String := " | ".intercalate
    ((List.range 12).map fun j => s!"{1000000 + 91 * j + k}.{100000 + j}")
  let paperWide := "| " ++ " | ".intercalate ((List.range 12).map (s!"c{·}")) ++ " |\n|" ++
    String.join (List.replicate 12 "--:|") ++ "\n" ++
    String.join ((List.range 3).map fun k => "| " ++ figures k ++ " |\n")
  let (pdoc, _) := elabMd paperWide
  let pout := layoutOf fonts pdoc
  let plines := (bodyLines pout).filter hasGlyphRun
  t s!"a table past the paper at the floor takes the last step, on the paper ({repr (decide pdoc)})"
    ((decide pdoc).any (·.step == some Layout.tableLastStep) && !plines.isEmpty
      && plines.all fun l => 0 ≤ l.x && l.x + l.setWidth ≤ pdoc.page.width)
  let listed := "- An item holding a table:\n\n" ++
    "\n".intercalate ((paperWide.splitOn "\n").filter (!·.isEmpty) |>.map ("  " ++ ·)) ++ "\n"
  let (ldoc, _) := elabMd listed
  let lout := layoutOf fonts ldoc
  let llines := (bodyLines lout).filter fun l => hasGlyphRun l && !hasStr (lineText l) "item"
  let lover := lout.diags.filter (·.kind == .W0338)
  t s!"a table overhanging its list item stays on the paper, named ({lover.map (·.message)})"
    (!llines.isEmpty && llines.all (fun l => 0 ≤ l.x && l.x + l.setWidth ≤ ldoc.page.width)
      && lover.size == 1 && lover.all fun d => hasStr d.message "overhangs the margins")
  let longWords := ["internationalization", "extraordinarily", "characteristically",
    "incomprehensibility", "counterproductively", "interchangeability"]
  for k in [0:6] do
    let cells := (List.range 4).map fun j => " ".intercalate
      ((List.range (2 + (k + j) % 3)).map fun m => longWords[(k + j + m) % longWords.length]!)
    let table := "- Item:\n\n  | " ++ " | ".intercalate ((List.range 4).map (s!"h{·}")) ++
      " |\n  |---|---|---|---|\n  | " ++ " | ".intercalate cells ++ " |\n"
    let (kdoc, _) := elabMd table
    let kout := layoutOf fonts kdoc
    let lm := Ir.leftMarginAt kdoc.docClass.record.lists kdoc.tokens kdoc.preambleFace 1
    let kfit := (tableOf? kdoc).map fun (cols, padL, padR, rows, spans) =>
      fitsIn kdoc ((Layout.Geom.ofPage kdoc.page).textWidth - lm) cols padL padR rows spans
    let kright := kdoc.page.width - kdoc.page.hmargin
    t s!"a listed table judged to fit its measure sets inside it ({k}: {repr kfit})"
      (kfit.any (fun f => (0 : Dim.Sp) < f.overhang) ||
        ((bodyLines kout).filter hasGlyphRun).all fun l => l.x + l.setWidth ≤ kright)
  let flagCell := "| Flag | Effect |\n|---|---|\n\
| `--rewrite-every-gadget-label-before-counting-them-and-writing-each-one-back` | \
the sorter reads every gadget it is handed |\n"
  let (fdoc, _) := elabMd flagCell
  let fout := layoutOf fonts fdoc
  let ffit := decide fdoc
  let fsize := ((ffit.bind (·.step)).map fun s => Ir.scaleStepIn fdoc.page.scale fdoc.page.fontSize s
    ).getD fdoc.page.fontSize
  t s!"hyphenated code sets at the decided size, inside the measure ({repr ffit})"
    (ffit.any (·.overhang == 0) && ((bodyLines fout).filter hasGlyphRun).all fun l =>
      l.size == fsize && left - Dim.pt 1 ≤ l.x && l.x + l.setWidth ≤ right + Dim.pt 1)
  for (label, wrap, inset) in [
      ("a quotation", fun (l : String) => "> " ++ l, 2),
      ("a list item", fun (l : String) => (if l.startsWith "| label" then "- " else "  ") ++ l, 1)] do
    let nested := "\n".intercalate (((src "sorter").splitOn "\n").filter (!·.isEmpty) |>.map wrap) ++ "\n"
    let (ndoc, _) := elabMd nested
    let nout := layoutOf fonts ndoc
    let lm := Ir.leftMarginAt ndoc.docClass.record.lists ndoc.tokens ndoc.preambleFace 1
    let avail := (Layout.Geom.ofPage ndoc.page).textWidth - inset * lm
    let nfit := (tableOf? ndoc).map fun (cols, padL, padR, rows, spans) =>
      fitsIn ndoc avail cols padL padR rows spans
    let nsize := ((nfit.bind (·.step)).map fun s =>
      Ir.scaleStepIn ndoc.page.scale ndoc.page.fontSize s).getD ndoc.page.fontSize
    t s!"a table in {label} decides against that measure and sets at its step ({repr nfit}; {sizes nout})"
      (nfit.isSome && sizes nout == [nsize])
    t s!"and the HTML states the same step for it ({styleOf ndoc})"
      (emMilli (styleOf ndoc) == stepMilli ndoc nfit)
  let (small, _) := elabMd "| a | b |\n|---|--:|\n| alpha | 12 |\n"
  t "a table that fits keeps its body size and no overhang"
    (decide small == some {} && !hasStr (styleOf small) "font-size"
      && !hasStr (classOf small) "bt-overhang")
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "fragment.md") (src "sorter")
    let (host, _) ← elabInputSrc (dir / "host.tex").toString
      (dvDoc "\\usepackage{markdown}\n" "Hostwords.\n\n\\markdownInput{fragment.md}\n")
    let hlines := (bodyLines (layoutOf fonts host)).filter fun l =>
      hasGlyphRun l && !hasStr (lineText l) "Hostwords"
    let hl := host.page.hmargin
    let hr := host.page.width - host.page.hmargin
    let hlo := (hlines.map (·.x)).foldl min hr
    let hhi := (hlines.map fun l => l.x + l.setWidth).foldl max hl
    t s!"an included table steps down in its host and centres its overhang ({repr (decide host)}; {hl - hlo} left, {hhi - hr} right)"
      ((decide host).any (·.step.isSome) && !hlines.isEmpty
        && (hl - hlo - (hhi - hr)).natAbs ≤ (Dim.pt 1).natAbs)

def markdownTableChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let basic := "| Name | Count |\n|------|------:|\n| alpha | 12 |\n| beta | 7 |\n"
  t "a pipe table ships as one table: its header row under the head, its data rows under the body"
    ((tablesOf basic).size == 1 && head basic == [["Name", "Count"]]
      && bodyRows basic == [["alpha", "12"], ["beta", "7"]])
  t "a header cell is a th and a data cell a td"
    ((tablesOf basic).all fun (h, b) =>
      h.all (·.all (·.tag == "th")) && b.all (·.all (·.tag == "td")))
  t "no pipe and no paragraph survive from a table's rows"
    (!hasStr (mdTreeOf basic) "|" && !hasStr (mdTreeOf basic) "<p>")
  let report := "| Orchard | rows | 🌳 `pruned` | ☀️ sunny | 🍂 `shed` / fallen |\n\
|---|---:|---:|---:|---:|\n| north | 12 | 9 | 3 | 0 |\n| south | 7 | 7 | 0 | 0 |\n"
  let reportTree := mdTreeOf report
  let (_, reportBody, _) := HtmlDoc.emitTree {} (elabMd report).1
  let codesInHead := (elemNodesList (· == "th") #[] reportBody.toList).foldl
    (fun n th => n + (elemNodesList (· == "code") #[] [th]).size) 0
  t "a head with inline code and emoji keeps both in its cells"
    (head report == [["Orchard", "rows", "🌳 pruned", "☀️ sunny", "🍂 shed / fallen"]]
      && codesInHead == 2
      && bodyRows report == [["north", "12", "9", "3", "0"], ["south", "7", "7", "0", "0"]])
  t "the delimiter row is structure, never text: no dash ships"
    (!hasStr reportTree "—" && !hasStr reportTree "–" && !hasStr reportTree "---")
  t "a right-aligned delimiter right-aligns its column, head included"
    ((tablesOf report).all fun (h, b) => (h ++ b).all fun r =>
      r.toList.map (·.align) ==
        [some "left", some "right", some "right", some "right", some "right"])
  let aligned := "| a | b | c | d |\n| :-- | :-: | --: | --- |\n| e | f | g | h |\n"
  t "each delimiter cell's colons give its column's alignment"
    ((tablesOf aligned).all fun (h, b) => (h ++ b).all fun r =>
      r.toList.map (·.align) == [some "left", some "center", some "right", some "left"])
  let escaped := "| a \\| b | `c \\| d` |\n| --- | --- |\n| x & y | p \\\\ q |\n"
  t "an escaped pipe is cell text, in plain text and in a code span"
    (head escaped == [["a | b", "c | d"]] && hasStr (mdTreeOf escaped) "<code>c | d</code>")
  t "a cell's ampersand and backslash cannot split a column or a row"
    (bodyRows escaped == [["x & y", "p \\ q"]])
  t "a header the delimiter row does not match is a paragraph"
    ((tablesOf "| a | b |\n| --- |\n| c |\n").isEmpty
      && hasStr (mdTreeOf "| a | b |\n| --- |\n| c |\n") "<p>")
  t "a short row is padded, a long one loses its excess"
    (bodyRows "| a | b |\n| - | - |\n| c |\n| d | e | f |\n" == [["c", ""], ["d", "e"]])
  t "leading and trailing pipes are optional, row by row"
    (head "a | b\n- | -\n" == [] && head "a | b\n-|-\n| c | d |\n" == [["a", "b"]]
      && bodyRows "a | b\n-|-\n| c | d |\n" == [["c", "d"]])
  t "a line without a pipe continues the table as a one-cell row"
    (bodyRows "| a | b |\n| - | - |\n| c | d |\nplain\n" == [["c", "d"], ["plain", ""]])
  t "a blank line ends the table, and what follows is a paragraph"
    (bodyRows "| a |\n| - |\n| c |\n\nafter\n" == [["c"]]
      && hasStr (mdTreeOf "| a |\n| - |\n| c |\n\nafter\n") "</table><p>after</p>")
  for (start, tag) in [("> quoted", "<blockquote>"), ("# heading", "<h1"),
      ("- item", "<ul>"), ("```\ncode\n```", "<pre"), ("***", "")] do
    let src := "| a |\n| - |\n| c |\n" ++ start ++ "\n"
    t s!"another block's start ends the table: {start.replace "\n" "⏎"}"
      (bodyRows src == [["c"]] && hasStr (mdTreeOf src) ("</table>" ++ tag))
  t "the paragraph lines above the header stay a paragraph"
    (hasStr (mdTreeOf "lead line\n| a | b |\n|---|---|\n| c | d |\n") "<p>lead line</p><table"
      && head "lead line\n| a | b |\n|---|---|\n| c | d |\n" == [["a", "b"]])
  t "a table in a quote or a list item stays in its container"
    (hasStr (mdTreeOf "> | a |\n> | - |\n> | c |\n\nafter\n") "<blockquote><table"
      && hasStr (mdTreeOf "- | a |\n  | - |\n  | c |\n\nafter\n") "<li><table"
      && bodyRows "> | a |\n> | - |\n> | c |\nafter\n" == [["c"]])
  t "a dash underline is a setext heading, a colon one a one-column table"
    (hasStr (mdTreeOf "abc\n---\n") "<h2" && (tablesOf "abc\n---\n").isEmpty
      && head "abc\n:--\n" == [["abc"]])
  t "a paragraph whose header failed to match never becomes a table"
    ((tablesOf "a | b | c\n-|-\n-|-\n").isEmpty)
  t "a delimiter row indented as code is paragraph text"
    ((tablesOf "| a |\n    | - |\n").isEmpty)
  t "a table raises no diagnostic of its own"
    ((dvMd report).isEmpty && (dvMd aligned).isEmpty && (dvMd escaped).isEmpty)
  let some fonts ← serifFacesSet
    | t "the markdown table faces load" false
      return
  let (doc, _) := elabMd basic
  let out := layoutOf fonts doc
  let census := censusOf (coveredColorsOf doc) out
  let painted := String.intercalate "\n" ((bodyLines out).map lineText).toList
  t "every cell of the table reaches the shipped page"
    (["Name", "Count", "alpha", "12", "beta", "7"].all (hasStr painted ·))
  let rules := pageRuleSegs census 0
  t s!"the table draws booktabs' three rules: heavy, light, heavy ({rules.size})"
    (rules.size == 3 && match rules[0]?, rules[1]?, rules[2]? with
      | some (_, top), some (_, mid), some (_, bot) => top == bot && mid < top
      | _, _, _ => false)
  let runRight (needle : String) : Option Dim.Sp :=
    (bodyLines out).findSome? fun l =>
      (lineRuns l).findSome? fun (_, s, x, w) => if s == needle then some (x + w) else none
  let runLeft (needle : String) : Option Dim.Sp :=
    (bodyLines out).findSome? fun l =>
      (lineRuns l).findSome? fun (_, s, x, _) => if s == needle then some x else none
  t "a right-aligned column ends its cells at one edge on the page"
    (runRight "12" == runRight "7" && runRight "12" == runRight "Count"
      && runLeft "12" != runLeft "7")
  t "a left-aligned column starts its cells at one edge on the page"
    (runLeft "alpha" == runLeft "beta" && runLeft "alpha" == runLeft "Name")
  t "the table has no outer pad: its first column starts at the text's left edge"
    (runLeft "Name" == some doc.page.hmargin)
  wrapChecks ref fonts
  narrowCellChecks ref fonts
  fitStepChecks ref fonts

end Tests.MarkdownTables
