import Tests.Support

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

/-- One shipped table cell: its tag, its text, and the `text-align` its
style declares, if any. -/
structure Cell where
  tag : String
  text : String
  align : Option String
  deriving BEq, Repr

/-- The `text-align` a style attribute declares. -/
def alignOf (attrs : Array (String × String)) : Option String :=
  (attrs.find? (·.1 == "style")).bind fun (_, v) =>
    (v.splitOn ";").findSome? fun decl =>
      match decl.splitOn ":" with
      | [k, a] => if k.trimAscii.toString == "text-align" then some a.trimAscii.toString else none
      | _ => none

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
over another, and is named at its first cell. And every cell of a row
stands on the row's baseline by its first line, whatever that line's
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
  t s!"and it is named at its first cell, with a remedy markdown can write ({over.size})"
    (over.size == 1 && over.all fun d => d.span.map (·.pos.line) == some 1
      && (d.help.any fun h => hasStr h "split the table"))
  -- One row, one baseline: a taller first line moves every cell's down.
  let rowOut := layoutOf fonts (elabStr (dvDoc ""
    "\\begin{tabular}{lll}\n\\toprule\nshort & {\\LARGE Tall} & low \\\\\n\\bottomrule\n\\end{tabular}")).1
  let baselineOf (needle : String) : Option Dim.Sp := (bodyLines rowOut).findSome? fun l =>
    if hasStr (lineText l) needle then some l.y else none
  t "the cells of a row stand on one baseline though one cell's first line is taller"
    ((baselineOf "Tall").isSome && baselineOf "short" == baselineOf "Tall"
      && baselineOf "low" == baselineOf "Tall")

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
      r.toList.map (·.align) == [none, some "right", some "right", some "right", some "right"])
  let aligned := "| a | b | c | d |\n| :-- | :-: | --: | --- |\n| e | f | g | h |\n"
  t "each delimiter cell's colons give its column's alignment"
    ((tablesOf aligned).all fun (h, b) => (h ++ b).all fun r =>
      r.toList.map (·.align) == [none, some "center", some "right", none])
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

end Tests.MarkdownTables
