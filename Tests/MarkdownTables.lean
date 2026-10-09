module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-! **A GFM pipe table is the booktabs table, on both artifacts.**

The markdown reader once had no table: a header row, a delimiter row and two
data rows shipped as one run-on paragraph, the delimiter's hyphens turned
into dashes. The invariant is over what ships — the typed HTML tree's
`<table>` and the laid-out page's rules — never over the md AST: the cells,
in order, under one head row; each column's alignment from its delimiter
cell; the GFM row rules (escaped pipes, missing and excess cells, where a
table ends); and booktabs' three rules with no vertical one. Every word here
is invented. -/

namespace Tests.MarkdownTables

/-- One shipped table cell: its tag, its text, and the side its class
states (`HtmlDoc.cellSideClass`), if any. -/
structure Cell where
  tag : String
  text : String
  align : Option String
  deriving BEq, Repr

/-- The side a cell's side class states: the `text-align` its rule sets
(`HtmlDoc.cellSideRule`). -/
def alignOf (attrs : Array (String × String)) : Option String :=
  (attrs.find? (·.1 == "class")).bind fun (_, v) =>
    (v.splitOn " ").findSome? fun c =>
      [Ir.HAlign.left, .center, .right].findSome? fun h =>
        if c == HtmlDoc.cellSideClass h then some h.align else none

/-- A row group's rows, each its cells. -/
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

/-- The cells' texts, row by row. -/
def texts (rows : Array (Array Cell)) : List (List String) :=
  rows.toList.map fun r => r.toList.map (·.text)

def head (src : String) : List (List String) :=
  ((tablesOf src)[0]?.map (texts ·.1)).getD []

def bodyRows (src : String) : List (List String) :=
  ((tablesOf src)[0]?.map (texts ·.2)).getD []

/-- **A markdown table too wide for its measure fits it, as a web table
does.** At its natural width a column of prose ran past the page edge and
lost its words. A markdown table is a web table: too wide for the measure,
its columns narrow as a browser's automatic table layout narrows them —
each keeps its widest word, and what the measure leaves beyond them is
shared in proportion to how much wider each column's widest line is — and
the cells of a narrowed column wrap, ragged on the side their alignment
names, with no hyphen; its HTML cells are left free to wrap the same way. A
table whose words alone pass the measure keeps every word whole, no cell
over another, and sets a step smaller (`fitStepChecks`). And every cell of
a row stands on the row's baseline by its first line, whatever that line's
height. -/
def wrapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let note := "Rewrites every gadget it is handed and writes each one back in the order of \
its label, then counts them"
  let wide := s!"| Key | Count of rewritten gadgets | Note |\n|---|--:|---|\n\
| `--sort` | 12 | {note} |\n| `-q` | 3 | quiet |\n"
  let (doc, _) := elabMd wide
  let out := layoutOf fonts doc
  let lines := bodyLines out
  let left := doc.page.hmargin
  let measure := doc.page.width - 2 * doc.page.hmargin
  t "a markdown table too wide for its measure keeps every glyph inside it"
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
  -- One word per cell needs no narrowing: the first column keeps its words
  -- whole, code included.
  t "a column of single words keeps them whole and stands at the measure's edge"
    ((lineOf "--sort").any (·.x == left) && (lineOf "Key").any (·.x == left))
  let countRight := (lineOf "12").map fun l => l.x + l.setWidth
  let countLines := lines.filter fun l => (lineRuns l).any fun (_, s, _, _) =>
    ["Count", "rewritten", "gadgets", "12", "3"].contains s
  t s!"a right-aligned column hangs every line of its wrapping head from its right edge ({countLines.size})"
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
  t "a markdown table's HTML cells may wrap, as its page's do; a tex table's natural cells may not"
    (!cells.isEmpty && !cells.any nowrap
      && (elemNodesList (· == "td") #[] texBody.toList).all nowrap)
  -- Words alone too wide for the measure: whole, side by side, and named.
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
  t s!"a table whose words alone pass the measure keeps each word whole, no cell over another ({rowYs.size})"
    (!rowYs.isEmpty && (rowYs.eraseReps).all fun y =>
      let cs := cellsAt y
      cs.size == 10 && (cs.zip (cs.extract 1 cs.size)).all fun (a, b) => a.x + a.setWidth < b.x)
  let over := fout.diags.filter (·.kind == .W0338)
  t s!"and it fits at a smaller step, so nothing names it ({over.size})"
    (over.isEmpty && (flines.all fun l => l.size < located.page.fontSize))
  -- One row, one baseline: a taller first line moves every cell's down.
  let rowOut := layoutOf fonts (elabStr (dvDoc ""
    "\\begin{tabular}{lll}\n\\toprule\nshort & {\\LARGE Tall} & low \\\\\n\\bottomrule\n\\end{tabular}")).1
  let baselineOf (needle : String) : Option Dim.Sp := (bodyLines rowOut).findSome? fun l =>
    if hasStr (lineText l) needle then some l.y else none
  t "the cells of a row stand on one baseline though one cell's first line is taller"
    ((baselineOf "Tall").isSome && baselineOf "short" == baselineOf "Tall"
      && baselineOf "low" == baselineOf "Tall")

/-- The shipped lines that share a baseline, each sorted left to right. -/
def rowsOfLines (lines : Array Layout.LineOut) : Array (Array Layout.LineOut) :=
  let ys := (lines.map (·.y)).toList.eraseDups.toArray
  ys.map fun y => (lines.filter (·.y == y)).qsort (·.x < ·.x)

/-- Do any two of a baseline's lines overlap: one cell's line running over
the next cell's on the page? -/
def rowOverlaps (row : Array Layout.LineOut) : Bool :=
  (row.zip (row.extract 1 row.size)).any fun (a, b) => b.x < a.x + a.setWidth

/-- **A narrowed cell sets its words inside its column.** A ragged line's
stretch lives in its word spaces, so a line that holds one word, or one run
of code broken where the url package breaks it, held none: the breaker
priced every such line as infinitely bad and packed the cell's words onto
one overfull line instead, across the next column's text. A narrowed cell's
every line now carries plain TeX's ragged right skip (`Layout.narrowedSkip`):
no two lines on one baseline overlap, none passes the table's right edge,
and no line is overfull. Every word is invented. -/
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
  -- Words that each fit their column, two of which do not: one per line,
  -- the neighbouring column of prose taking the room.
  let words := ["network", "protocol", "handler", "registry"]
  let single := "| Words | Prose |\n|---|---|\n| " ++ " ".intercalate words ++ " | " ++
    " ".intercalate (List.replicate 12 why) ++ " |\n"
  let sout := layoutOf fonts (elabMd single).1
  let slines := bodyLines sout
  let yOf (w : String) : Option Dim.Sp :=
    (slines.find? fun l => (lineRuns l).any (·.2.1 == w)).map (·.y)
  let ys := words.filterMap yOf
  t s!"a narrowed cell whose words fit its column one at a time sets one a line ({ys})"
    (ys.length == 4 && ys.eraseDups.length == 4)
  t "and overlaps no neighbour"
    (!(rowsOfLines slines).any rowOverlaps && !(sout.diags.any (·.kind == .W0005)))
  -- A tex `>{\raggedright}p` column keeps LaTeX's setting, hyphenation
  -- included, never the narrowed cell's: set without its hyphens, its words
  -- once packed onto one line over the next column.
  let texDoc := (elabStr (dvDoc "\\usepackage{array}\n"
    ("\\begin{tabular}{>{\\raggedright\\arraybackslash}p{2.1cm}l}\n" ++
      " ".intercalate words ++ " & next \\\\\n\\end{tabular}"))).1
  let texOut := layoutOf fonts texDoc (pats := Hyphen.forTag texDoc.info.locale.tag)
  let tlines := bodyLines texOut
  t s!"a tex ragged p column wraps inside its column, over no neighbour ({tlines.size} lines)"
    (tlines.size ≥ 4 && !(rowsOfLines tlines).any rowOverlaps
      && !(texOut.diags.any (·.kind == .W0005)))

/-- **A markdown table too wide for its words stays on the page.** A table
whose widest unbreakable runs alone pass the measure kept its body size and
ran its last columns off the paper. It now sets at the largest of LaTeX's
smaller steps at which its words fit (`Layout.tableFit`), and a table too
wide even at the floor stands centred on the measure, overhanging both
margins equally — on paper while it is no wider than the two together. The
HTML states the same step as the table's font size and centres the same
overhang on paper. A table that fits keeps its size. -/
def fitStepChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let row (k : Nat) : String := " | ".intercalate
    ((List.range 9).map fun j => s!"{k}{j}.{4000 + 61 * j + k}")
  let src (label : String) := "| label | p | q | r | s | t | u | v | w | z |\n\
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|\n" ++
    s!"| {label} | {row 1} |\n| {label}x | {row 2} |\n"
  let fitsAt (doc : Ir.Doc) := Layout.tableFit (Layout.Geom.ofPage doc.page) fonts {}
    (Layout.tableLength none doc.preambleFace "tabcolsep")
  let tableOf (doc : Ir.Doc) := doc.body.findSome? fun b => match b with
    | .table cols padL padR rows _ spans => some (cols, padL, padR, rows, spans)
    | _ => none
  let decide (doc : Ir.Doc) : Option Layout.TableFit := (tableOf doc).map
    fun (cols, padL, padR, rows, spans) => fitsAt doc cols padL padR rows spans
  let sizes (out : Layout.Out) : List Dim.Sp :=
    (((bodyLines out).filter fun l => (lineText l).any Char.isDigit).toList.map (·.size)).eraseDups
  -- Fits at a smaller step.
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
  -- Too wide even at the floor: centred, on paper, named.
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
  -- The HTML states the same decision.
  let cfgOf (doc : Ir.Doc) : HtmlDoc.Config := { tableFit := fun cols padL padR rows spans =>
    let f := fitsAt doc cols padL padR rows spans
    (f.step, f.overhang > 0) }
  let tableAttrs (doc : Ir.Doc) : Array (String × String) :=
    let (_, body, _) := HtmlDoc.emitTree (cfgOf doc) doc
    match ((elemNodesList (· == "table") #[] body.toList)[0]? : Option Html.Node) with
    | some (.elem _ attrs _) => attrs
    | _ => #[]
  let styleOf (doc : Ir.Doc) := (HtmlDoc.attrOf? (tableAttrs doc) "style").getD ""
  let classOf (doc : Ir.Doc) := (HtmlDoc.attrOf? (tableAttrs doc) "class").getD ""
  -- The font size a style declares, in thousandths of an em.
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
  -- A table that fits keeps its size, on both artifacts.
  let (small, _) := elabMd "| a | b |\n|---|--:|\n| alpha | 12 |\n"
  t "a table that fits keeps its body size and no overhang"
    (decide small == some {} && !hasStr (styleOf small) "font-size"
      && !hasStr (classOf small) "bt-overhang")
  -- The fit is the table's own: included in a tex document, the same
  -- fragment's table narrows its columns too.
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
    t s!"an included fragment's table steps down in its host and centres what overhangs \
({repr (decide host)}; {hl - hlo} left, {hhi - hr} right)"
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
  -- The reported shape: inline code and emoji in the head, every number
  -- column right-aligned, the delimiter row's hyphens never text.
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
  t "a right-aligned delimiter cell right-aligns its whole column, head included"
    ((tablesOf report).all fun (h, b) => (h ++ b).all fun r =>
      r.toList.map (·.align) ==
        [some "left", some "right", some "right", some "right", some "right"])
  let aligned := "| a | b | c | d |\n| :-- | :-: | --: | --- |\n| e | f | g | h |\n"
  t "each delimiter cell's colons give its column's alignment"
    ((tablesOf aligned).all fun (h, b) => (h ++ b).all fun r =>
      r.toList.map (·.align) == [some "left", some "center", some "right", some "left"])
  -- Rows split before inlines are read: an escaped pipe is a pipe, even in
  -- a code span; a cell's `&` and backslash are its text, never a column
  -- or a row of the table it desugars to.
  let escaped := "| a \\| b | `c \\| d` |\n| --- | --- |\n| x & y | p \\\\ q |\n"
  t "an escaped pipe is cell text, in plain text and in a code span"
    (head escaped == [["a | b", "c | d"]] && hasStr (mdTreeOf escaped) "<code>c | d</code>")
  t "a cell's ampersand and backslash cannot split a column or a row"
    (bodyRows escaped == [["x & y", "p \\ q"]])
  t "a header whose cells the delimiter row does not match is a paragraph"
    ((tablesOf "| a | b |\n| --- |\n| c |\n").isEmpty
      && hasStr (mdTreeOf "| a | b |\n| --- |\n| c |\n") "<p>")
  t "a short row is padded with empty cells and a long one loses its excess"
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
  t "a table inside a quote and inside a list item stays inside its container"
    (hasStr (mdTreeOf "> | a |\n> | - |\n> | c |\n\nafter\n") "<blockquote><table"
      && hasStr (mdTreeOf "- | a |\n  | - |\n  | c |\n\nafter\n") "<li><table"
      && bodyRows "> | a |\n> | - |\n> | c |\nafter\n" == [["c"]])
  t "a dash underline is a setext heading, a colon one a one-column table"
    (hasStr (mdTreeOf "abc\n---\n") "<h2" && (tablesOf "abc\n---\n").isEmpty
      && head "abc\n:--\n" == [["abc"]])
  t "a paragraph whose header once failed to match never becomes a table"
    ((tablesOf "a | b | c\n-|-\n-|-\n").isEmpty)
  t "a delimiter row indented as code is paragraph text"
    ((tablesOf "| a |\n    | - |\n").isEmpty)
  t "a table raises no diagnostic of its own"
    ((dvMd report).isEmpty && (dvMd aligned).isEmpty && (dvMd escaped).isEmpty)
  -- The paged artifact: the same cells, booktabs' three rules and no other.
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
  t s!"the shipped table draws booktabs' three rules, heavy, light and heavy ({rules.size})"
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
