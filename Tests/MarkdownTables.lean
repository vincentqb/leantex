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

end Tests.MarkdownTables
