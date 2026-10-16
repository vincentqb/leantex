module

public import LeanTex.Cli.FontDiscovery
public import Tests.Support
public import Tests.CorpusStore

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The margin number column of a page census: furniture lines standing left of the measure, where
the centred page number never stands. -/
def marginNumbers (geom : Layout.Geom) (c : Array CensusPage) :
    Array (Array CensusLine) :=
  c.map fun p => p.lines.filter fun l =>
    l.furniture && l.x + l.width ≤ geom.hmargin

/-- The shipped-page rule for `\page{ linenumbers = on }`: every counted body line carries one
margin number at its baseline, numbered consecutively from 1. -/
def linenoCensus (geom : Layout.Geom) (c : Array CensusPage) :
    List (String × Bool) :=
  let margin := marginNumbers geom c
  let counted := c.map fun p => p.lines.filter (·.counted)
  [("the article spans two pages", c.size ≥ 2),
   ("every counted body line carries exactly one margin number at its \
baseline, consecutively from 1 across pages",
     Id.run do
       let mut k := 0
       let mut ok := true
       for (cl, ml) in counted.zip margin do
         ok := ok && ml.size == cl.size
         for l in cl do
           k := k + 1
           ok := ok && (ml.filter fun m =>
             m.y == l.y && m.text.trimAscii.toString == toString k).size == 1
       return ok && k > 0),
   ("the heading line is counted",
     ((c[0]?.bind fun p => p.lines.find? fun l =>
       hasStr l.text "Numbered galley").map (·.counted)).getD false),
   ("the display formula's line is counted — numbered like every line \
here, where lineno's default is not (the recorded divergence)",
     ((c[0]?.bind fun p => p.lines.find? fun l =>
       hasStr l.text "=").map (·.counted)).getD false),
   ("the float's body and caption are box content, not counted",
     c.toList.all fun p => p.lines.all fun l =>
       !(hasStr l.text "floated caption" && l.counted) &&
       !(hasStr l.text "float body" && l.counted)),
   ("the footnote is an insertion, not counted",
     c.toList.all fun p => p.lines.all fun l =>
       !(hasStr l.text "insertion" && l.counted)),
   ("the numbers set at the footnotesize step, right-aligned with the \
undeclared column hanging from half the margin",
     (margin.toList.all fun ml => ml.toList.all fun m =>
       m.size == Ir.scaleStepIn Ir.sizeScale geom.fontSize "footnotesize" &&
       m.x + m.width == geom.hmargin / 2) &&
     margin.toList.any (!·.isEmpty))]

/-- The modulo half: the count advances on every counted line and only its multiples print, each at
its line's baseline. -/
def linenoModuloCensus (geom : Layout.Geom) (c : Array CensusPage) :
    List (String × Bool) :=
  let margin := (marginNumbers geom c).foldl (· ++ ·) #[]
  let countedLines := c.foldl (fun a p => a ++ p.lines.filter (·.counted)) #[]
  [("one page", c.size == 1),
   ("the count crosses the second modulus", countedLines.size ≥ 10),
   ("only multiples of five print, in order — the count still advances \
on every counted line",
     margin.map (·.text.trimAscii.toString) ==
       (Array.range (countedLines.size / 5)).map fun i => toString ((i + 1) * 5)),
   ("each printed number stands at a counted line's own baseline",
     margin.all fun m => countedLines.any fun l => l.y == m.y)]

/-- A conditional fixture's census: one page, every kept branch ships and no hidden branch does. -/
def condBranchRow (kept hidden : List String) :
    Layout.Geom → Array CensusPage → List (String × Bool) := fun _ c =>
  [("one page", c.size == 1)] ++
  kept.map (fun k => (s!"the branch TeX keeps ships: {k}", hasStr (censusText c) k)) ++
  hidden.map (fun h => (s!"the branch TeX skips does not: {h}", !hasStr (censusText c) h))

/-- The size of the first line on page 0 holding `needle`, or 0. -/
def mdSizeOf (c : Array CensusPage) (needle : String) : Dim.Sp :=
  (lineSizeOf c 0 needle).getD 0

/-- The pages' text as prose, every run of spaces one space. -/
def censusProse (c : Array CensusPage) : String :=
  " ".intercalate (((censusText c).splitOn " ").filter (!·.isEmpty))

/-- The pages' ink with every space dropped. -/
def censusInk (c : Array CensusPage) : String :=
  String.ofList ((censusText c).toList.filter (· != ' '))

/-- Three rules in line order bracket a table as booktabs does: a heavy rule above the header, a
lighter one below it, and one as heavy as the first under the last row. -/
def booktabsBrackets (c : Array CensusPage) (rules : List (Dim.Sp × Dim.Sp))
    (header firstRow lastRow : String) : Bool :=
  match rules, lineYOf c 0 header, lineYOf c 0 firstRow, lineYOf c 0 lastRow with
  | [(top, heavy), (mid, light), (bottom, heavy')], some h, some f, some l =>
    decide (light < heavy) && heavy == heavy' && decide (top < h) && decide (h < mid) &&
      decide (mid < f) && decide (l < bottom)
  | _, _, _, _ => false

/-- The markdown fixtures' census rows, read off `Layout.Out`. -/
def censusMdRows :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("md-cite", fun _ c => [
    ("one page", c.size == 1),
    ("each citation ships in plainnat's author-year marks, its notes inside them",
      ["A first claim [Roe, 2020]", "by name: Doe and Hale [2024]",
        "[see Poe, 2022, pp. 101-110; Roe, 2020]", "Roe [2020] wrote",
        "Doe and Hale [2024, p. 46]", "[Doe and Hale, 2024, chap. 2]", "key [?] shows"].all
        (hasStr (censusProse c) ·)),
    ("what is not a citation ships as written",
      ["someone@example.org", "@roe2020 and an escaped @roe2020"].all (hasStr (censusProse c) ·)),
    ("the list ships under its declared title, sorted, the nocite entry among them",
      ((lineYOf c 0 "Works cited").bind fun h => (lineYOf c 0 "Alex B. Doe").bind fun d =>
        (lineYOf c 0 "Kim Poe").bind fun p => (lineYOf c 0 "Sam Roe").bind fun r =>
          (lineYOf c 0 "Rin Vale").map fun v => decide (h < d ∧ d < p ∧ p < r ∧ r < v)).getD false),
    ("no metadata reaches the page",
      !["bibliography", "md-cite.bib", "plainnat", "underscore"].any (hasStr (censusText c) ·))]),
  ("md-code", fun geom c => [
    ("one page", c.size == 1),
    ("the code span ships inside its sentence",
      hasStr (censusText c) "Inline code such as count_birds(day) sits in a sentence"),
    ("a doubled-backtick span keeps the backtick it holds", hasStr (censusText c) "a`b"),
    ("the fenced block's long line wraps inside the measure, every character shipped, \
its comment included",
      hasStr (censusInk c) "andentry.verified)#onelongline" &&
        ["returnsum(", "longline"].all fun n =>
          (lineRightOf c 0 n).any fun r => decide (r ≤ geom.pageW - geom.hmargin)),
    ("the long lines with an arrow, a comparison, a path and a formula ship every character",
      hasStr (censusInk c) "->dict:" && hasStr (censusInk c) ")==expected" &&
        hasStr (censusInk c) "season/report.txt\"" && hasStr (censusInk c) "String->String:=funpath=>" &&
        hasStr (censusInk c) "(1:Nat)≤2:=bydecide"),
    ("a tilde fence keeps its indented line", hasStr (censusText c) "indentedlineinsidethefence"),
    -- A note's class paints a code ground: the fenced blocks stand on it.
    ("the fenced code stands on its code ground", (c[0]?.map fun p => decide (p.fills ≥ 1)).getD false),
    ("prose resumes after the code", hasStr (censusText c) "A paragraph after the code.")]),
  ("md-emphasis", fun _ c => [
    ("one page", c.size == 1),
    ("an intraword underscore is not emphasis", hasStr (censusText c) "snake_case_name"),
    ("escaped markers ship as themselves",
      hasStr (censusText c) "*not emphasis*" && hasStr (censusText c) "# not a heading"),
    ("a backslash and two trailing spaces each end a line",
      match lineYOf c 0 "A backslash at the end of a line", lineYOf c 0 "forces a hard break",
          lineYOf c 0 "as do two trailing spaces" with
      | some a, some b, some d => decide (a < b) && decide (b < d)
      | _, _, _ => false),
    ("named and numeric references decode", hasStr (censusText c) "& © © © and a lone & sign")]),
  ("md-headings", fun _ c => [
    ("one page", c.size == 1),
    ("every rank's heading ships",
      ["Harbour Notes", "The quay", "Moorings", "Winter moorings", "The inner basin",
        "The breakwater"].all (hasStr (censusText c) ·)),
    ("the underlined title and ranks two and three step down in size, all above the body",
      decide (mdSizeOf c "Harbour Notes" > mdSizeOf c "The quay") &&
      decide (mdSizeOf c "The quay" > mdSizeOf c "Moorings") &&
      decide (mdSizeOf c "Moorings" > mdSizeOf c "Twelve rings")),
    ("a hyphen-underlined heading sets at the second rank, as its number-sign twin",
      mdSizeOf c "Setext heading, second rank" == mdSizeOf c "The quay")]),
  ("md-images", fun _ c => [
    ("one page", c.size == 1),
    ("every image ships, the linked one and the one in a list item included",
      (c[0]?.map (·.images)).getD 0 == 4),
    ("the sentence around an inline image ships", hasStr (censusText c) "An image inside a sentence"),
    ("the list item holding an image keeps its marker",
      hasStr (censusText c) "• A list item with an image:")]),
  ("md-links", fun _ c => [
    ("one page", c.size == 1),
    ("an inline link's text ships", hasStr (censusProse c) "An inline link to the example site"),
    ("links inside emphasis and strong text ship",
      hasStr (censusText c) "see the index" && hasStr (censusText c) "strong text with a link"),
    ("link underlines ship as rules", (c[0]?.map fun p => decide (p.rules ≥ 1)).getD false)]),
  ("md-lists", fun geom c => [
    ("one page", c.size == 1),
    ("each nesting level ships its own marker",
      hasStr (censusText c) "• Waterproof notebook" && hasStr (censusText c) "– Two sharpened" &&
      hasStr (censusText c) "* The pocket with a zip"),
    ("a nested item stands right of its parent",
      match lineXOf c 0 "Pencils, not pens", lineXOf c 0 "Two sharpened",
          lineXOf c 0 "The pocket with a zip" with
      | some a, some b, some d => decide (a < b) && decide (b < d)
      | _, _, _ => false),
    ("an ordered list numbers its items", hasStr (censusText c) "2. Leave a note of the route."),
    ("a list item's second paragraph ships inside the item",
      (lineXOf c 0 "A second paragraph in the same item").any fun x => decide (x > geom.hmargin)),
    ("code inside an item ships", hasStr (censusText c) "check--tide--routenorth")]),
  ("md-quotes", fun geom c => [
    ("one page", c.size == 1),
    ("a quotation stands right of the text area's edge",
      (lineXOf c 0 "The lamp is lit at dusk").any fun x => decide (x > geom.hmargin)),
    ("a nested quotation stands right of the one holding it",
      match lineXOf c 0 "Outer quotation.", lineXOf c 0 "An inner quotation" with
      | some a, some b => decide (a < b)
      | _, _ => false),
    ("a list inside a quotation keeps its markers", hasStr (censusText c) "• lamp oil"),
    ("a heading and code inside a quotation ship",
      hasStr (censusText c) "A heading inside a quotation" &&
      hasStr (censusText c) "codeinsideaquotation")]),
  ("md-readme", fun _ c => [
    ("one page", c.size == 1),
    ("the install command ships", hasStr (censusText c) "makeinstallPREFIX=$HOME/.local"),
    ("an ordered step holds its code and its nested list",
      hasStr (censusText c) "tidegaugereadharbour.log" &&
      hasStr (censusText c) "• by date, --day 2091-03-14;"),
    ("a quotation inside a step ships",
      hasStr (censusText c) "High water 06:10 (4.1 m), low water 12:25."),
    ("the option table's cells ship",
      ["--units", "metres or feet", "print the numbers and no words"].all (hasStr (censusText c) ·)),
    ("the option table ships as a booktabs table, its delimiter row read and not set",
      booktabsBrackets c ((pageRuleSegs c 0).toList.take 3) "Default" "the day to report"
        "print the numbers and no words" && !hasStr (censusText c) "| |"),
    ("the task items' text ships", hasStr (censusText c) "read the log format"),
    ("each disclosure ships its summary on a line above its whole body, closed or open",
      [("The log reads as empty", "Check that each line",
          "Check that each line carries a timestamp and a height, a tab between them."),
        ("Reading in other units", "Heights print in metres",
          "Heights print in metres unless --units feet is given.")].all fun (summary, first, body) =>
        hasStr (censusProse c) body &&
        match lineYOf c 0 summary, lineYOf c 0 first with
        | some a, some b => decide (a < b)
        | _, _ => false)]),
  ("md-rules", fun _ c => [
    ("one page", c.size == 1),
    ("every section the rules divide ships",
      ["The first section ends", "The second section ends", "The third, with underscores.",
        "A closing paragraph after the last rule."].all (hasStr (censusText c) ·))]),
  ("md-table", fun _ c => [
    ("one page", c.size == 1),
    ("every cell's text ships",
      ["Monday", "06:10", "12:25", "Wednesday", "13:50", "4.6"].all (hasStr (censusText c) ·)),
    ("an escaped pipe's row ships its meaning", hasStr (censusText c) "a literal pipe"),
    ("prose after a table ships", hasStr (censusText c) "A paragraph after the table"),
    ("each pipe table ships as a booktabs table, its delimiter row read and not set",
      (pageRuleSegs c 0).size == 6 && !hasStr (censusText c) "| |" &&
        booktabsBrackets c ((pageRuleSegs c 0).toList.take 3) "High water" "Monday" "Wednesday" &&
        booktabsBrackets c (((pageRuleSegs c 0).toList.drop 3).take 3) "Meaning" "a literal pipe"
          "about"),
    ("each column aligns as its delimiter row says: right columns end with their header, \
the centred one centres on it, the left one starts with it",
      lineXOf c 0 "Monday" == lineXOf c 0 "Day" &&
      lineRightOf c 0 "06:10" == lineRightOf c 0 "High water" &&
      lineRightOf c 0 "4.1" == lineRightOf c 0 "Range (m)" &&
      (match lineXOf c 0 "12:25", lineRightOf c 0 "12:25", lineXOf c 0 "Low water",
          lineRightOf c 0 "Low water" with
        | some a, some b, some d, some e => a + b == d + e
        | _, _, _, _ => false))])]

/-- A loss a markdown golden ships with no diagnostic naming it, judged over every markdown golden
both ways; `owner` names the change that reads the construct. -/
structure SilentLoss where
  what : String
  owner : String
  fixtures : List String
  shows : Ir.Doc → Layout.Out → Array CensusPage → Array Diag → Bool

/-- The link targets of every link that wraps an image, document order. -/
def imageLinkTargets (doc : Ir.Doc) : Array String :=
  Ir.foldDoc (fun acc i => match i with
    | .link url body => if body.any (fun b => b matches .image ..) then acc.push url else acc
    | _ => acc) #[] doc

/-- Every link target the pages carry: a linked run's or a link rectangle's. -/
def pageLinkTargets (out : Layout.Out) : Array String :=
  out.pages.foldl (fun acc p =>
    p.lines.foldl (fun acc l => l.segs.foldl (fun acc s => match s with
      | .run _ _ (some url) .. => acc.push url
      | _ => acc) acc) (acc ++ p.links.map (·.target))) #[]

/-- The silent losses the markdown goldens ship. -/
def silentLosses : List SilentLoss := [
  { what := "a task list item ships its checkbox as bracket text"
    owner := "list items that carry a task state, set as a box in both artifacts"
    fixtures := ["md-readme"]
    shows := fun _ _ c _ => hasStr (censusText c) "[ ] " || hasStr (censusText c) "[x] " },
  { what := "a reference link ships its brackets, and its definition ships as a paragraph"
    owner := "link reference definitions, resolved by the markdown reader"
    fixtures := ["md-links"]
    shows := fun _ _ c _ => hasStr (censusText c) "][" && hasStr (censusText c) "]: https://" },
  { what := "an image a link wraps ships without its link: no linked run or link rectangle carries its target"
    owner := "a link annotation over a linked image"
    fixtures := ["md-images"]
    shows := fun doc out _ _ =>
      (imageLinkTargets doc).any fun t => !(pageLinkTargets out).contains t }]

/-- Each silent loss's judge over every markdown golden, both ways. -/
def silentLossChecks (ref : IO.Ref (List String))
    (seen : Array (String × Ir.Doc × Layout.Out × Array CensusPage × Array Diag)) : IO Unit := do
  for row in silentLosses do
    check ref s!"silent loss '{row.what}': names its owner and a golden" (!row.owner.isEmpty && !row.fixtures.isEmpty)
    for n in row.fixtures do
      check ref s!"silent loss '{row.what}': {n} is a markdown golden" (mdGoldenNames.contains n)
    for (n, doc, out, c, ds) in seen do
      let fires := row.shows doc out c ds
      if row.fixtures.contains n then
        check ref s!"silent loss '{row.what}': {n} still ships it — if it no longer does, \
take {n} out of the row, or the row out, and leave the guard that keeps it read" fires
      else
        check ref s!"silent loss '{row.what}': {n} ships it unrecorded — list {n} under the row" (!fires)

/-- Census assertions, one row per golden fixture: what each fixture's shipped pages show, judged
from `Layout.Out`. -/
def censusRows0 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("affine-lengths", fun _ c => [
    ("one page", c.size == 1),
    ("every unequal measure ships its labelled content",
      ["Top measure", "Minipage measure", "Column measure", "Paragraph cell",
        "Target-width cell"].all (hasStr (censusText c) ·)),
    ("every affine rule reaches the shipped page",
      (c[0]?.map (·.rules)).getD 0 == 5)]),
  ("md-include", fun _ c => [
    ("one page", c.size == 1),
    ("the included heading, emphasis, list items and code reach the shipped page",
      ["Included placeholder notes", "invented paragraph with bold words", "First included item",
        "Second included item", "defplaceholder(n):", "returnn+1"].all (pageHas c 0 ·)),
    ("the included file stands between its neighbours",
      ((lineYOf c 0 "standing before").bind fun a =>
        (lineYOf c 0 "Included placeholder notes").bind fun h =>
          (lineYOf c 0 "standing after").map fun b => decide (a < h ∧ h < b)).getD false)]),
  ("md-cite-include", fun _ c => [
    ("one page", c.size == 1),
    ("the article's and its markdown file's citations ship in one numbering",
      ["citing [1] before", "cite [2] and Doe and Hale [3, p. 42]", "citing Vale [4] after"].all
        (hasStr (censusProse c) ·)),
    ("one reference list ships all four entries, once each",
      ["[1] Sam Roe", "[2] Kim Poe", "[3] Alex B. Doe", "[4] Rin Vale"].all
        (fun s => pageOccurs c 0 s == 1) && pageOccurs c 0 "References" == 1)]),
  ("md-include-deck", fun _ c => [
    ("a title page and one frame page", c.size == 2),
    ("the frame's included list and quotation reach its page below the title",
      ["First slide point from markdown", "Second slide point with inline code",
        "A quoted placeholder line."].all (pageHas c 1 ·) &&
      ((lineYOf c 1 "Included placeholder frame").bind fun t =>
        (lineYOf c 1 "First slide point").map fun i => decide (t < i)).getD false)]),
  ("listings", fun geom c => [
    ("one page", c.size == 1),
    -- A no-break space ships as a glyphless box, so a code line's census text reads glued.
    ("the caption ships numbered with the locale's listing word, above the code",
      hasStr (censusText c) "Listing 1: An invented probe." &&
      ((lineYOf c 0 "An invented probe").bind fun cy =>
        (lineYOf c 0 "defprobe(n):").map fun ly => decide (cy < ly)).getD false),
    ("the declared line numbers ship as furniture beside their lines",
      pageHas c 0 "1defprobe(n):" && pageHas c 0 "2returnn+1"),
    ("the minted body ships its code and never its language argument",
      pageHas c 0 "print(\"synthetic\")" && !hasStr (censusText c) "python"),
    ("the reference resolves to the listing's number",
      hasStr (censusText c) "adds one"),
    ("the quantity ships its unit symbols",
      hasStr (censusText c) "345.6" && hasStr (censusText c) "kg"),
    ("the code inherits the surrounding size when none is declared",
      lineSizeOf c 0 "defprobe(n):" == some geom.fontSize)]),
  ("footnotes", fun geom c => [
    ("the article spans two pages", c.size ≥ 2),
    ("the first note ships at the foot of page one",
      pageHas c 0 "first" && pageHas c 0 "foot of page one" &&
      ((lineYOf c 0 "invented survey").bind fun sy =>
        (lineYOf c 0 "foot of page one").map fun ny => decide (sy < ny)).getD false),
    ("the note ink stands above bodyBottom, in the text block",
      ((lineYOf c 0 "foot of page one").map fun ny =>
        decide (ny ≤ geom.pageH - geom.vmargin)).getD false),
    ("the mark's digit ships raised beside its word",
      pageHas c 0 "here1"),
    ("the boundary note shares its mark's page, wherever the break fell",
      (List.range c.size).any fun i =>
        pageHas c i "boundary claim" && pageHas c i "boundary note"),
    ("no page carries a note whose mark is elsewhere",
      (List.range c.size).all fun i =>
        (!pageHas c i "boundary note" || pageHas c i "boundary claim") &&
        (!pageHas c i "foot of page one" || pageHas c i "invented survey")),
    ("the override mark ships as 12, unstepped",
      hasStr (censusText c) "number12" && hasStr (censusText c) "chosen note"),
    ("the footnote rule ships at its declared weight above the notes",
      ((lineYOf c 0 "foot of page one").map fun ny =>
        (pageRuleSegs c 0).any fun rt =>
          decide (rt.1 < ny) && rt.2 == geom.fontSize * 4 / 100).getD false),
    ("the notes set at footnotesize",
      lineSizeOf c 0 "foot of page one" ==
        some (geom.fontSize * ((Ir.sizeScale.lookup "footnotesize").getD 1000) / 1000))]),
  ("eqnum", fun geom c => [
    ("one page", c.size == 1),
    ("the first equation ships its number", hasStr (censusText c) "(1)"),
    ("the opted-out display frees its number for the next",
      hasStr (censusText c) "(2)" && !hasStr (censusText c) "(3)"),
    ("the number is right-aligned on the measure",
      -- to the sp integer division owes the fil pair, as pad_center does
      (lineRightOf c 0 "(1)").any fun r =>
        decide (r ≤ geom.hmargin + geom.textWidth ∧
          geom.hmargin + geom.textWidth - r ≤ 2)),
    ("eqref resolves to the parenthesised number",
      hasStr (censusText c) "Equation(1)")]),
  ("crossref", fun _ c => [
    ("one page", c.size == 1),
    ("a resolved reference ships its number on the page",
      hasStr (censusText c) "Section1 opened"),
    ("eqref ships its parenthesised number", hasStr (censusText c) "(2)"),
    ("an unresolved reference ships LaTeX's ??",
      hasStr (censusText c) "see??"),
    ("an appendix reference letters itself",
      hasStr (censusText c) "AppendixA letters"),
    ("the heading line carries its number beside its title",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Alpha").map
        fun l => hasStr l.text "1").getD false),
    ("float references ship the numbers their captions carry",
      hasStr (censusText c) "Figure1 and Table1 are referenced"),
    ("the captions ship those same numbers as their prefixes",
      hasStr (censusText c) "Figure 1: An invented crossref panel."
        && hasStr (censusText c) "Table 1: An invented data strip.")]),
  ("abstract", fun geom c => [
    ("one page", c.size == 1),
    ("the class furniture heading ships", hasStr (censusText c) "Abstract"),
    ("the abstract body ships", hasStr (censusText c) "Entirely synthetic findings"),
    ("the abstract body is set off the margin",
      (lineXOf c 0 "Entirely synthetic findings").any fun x => decide (x > geom.hmargin)),
    ("the following body returns to the margin",
      lineXOf c 0 "Body text follows the abstract" == some geom.hmargin),
    ("the abstract heading ships in the styled section's font",
      lineSizeOf c 0 "Abstract" == some (geom.fontSize * 1200 / 1000) &&
      lineSizeOf c 0 "Abstract" == lineSizeOf c 0 "Introduction"),
    ("the abstract heading centres in the measure",
      ((lineXOf c 0 "Abstract").map fun x =>
        decide (x > geom.hmargin)).getD false)]),
  ("algorithm", fun _ c => [
    ("the caption ships numbered with the locale word",
      hasStr (censusText c) "Algorithm 1: Exchange sort of an invented list."),
    ("the second algorithm takes the next number",
      hasStr (censusText c) "Algorithm 2: The same exchange sort, algorithmicx spelling."),
    ("the io lines ship their generated labels",
      hasStr (censusText c) "Input:" && hasStr (censusText c) "Output:"),
    ("a declared io keyword ships its line under its own word",
      hasStr (censusText c) "Bound: every weight between one and nine"),
    ("the generated keywords ship around the declared content",
      hasStr (censusText c) "for" && hasStr (censusText c) "do"
        && hasStr (censusText c) "end"),
    ("the declared statement ships", hasStr (censusText c) "swap"),
    ("the comment ships between its fences",
      hasStr (censusText c) "/* one pass floats the heaviest weight to the end */"),
    ("the else branch ships its keyword and body",
      hasStr (censusText c) "else" && hasStr (censusText c) "keep the pair as it stands"),
    ("the reference resolves to the float's number",
      hasStr (censusText c) "Algorithm1 is restated"),
    ("the line numbers keep one left column whatever the depth",
      ((lineXOf c 0 "swap").bind fun sx =>
        (lineXOf c 0 "keep the pair").bind fun kx =>
        (lineXOf c 0 "Input:").map fun ix =>
          decide (sx = kx ∧ kx = ix)).getD false)]),
  ("paragraphs", fun _ c => [
    ("one page", c.size == 1),
    ("the opening sentence ships", hasStr (censusText c) "Typesetting is the arrangement of type"),
    ("it wraps to at least four lines", (c[0]?.map fun p => decide (p.lines.size ≥ 4)).getD false),
    ("the plain page number ships, the page's last-laid line",
      ((c[0]?.bind fun p => p.lines.back?).map (·.text.trimAscii.toString)) == some "1")]),
  ("layout", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "The first section"),
    ("a list marker ships beside its item", hasStr (censusText c) "• One concise point")]),
  ("bibliography", fun _ c => [
    ("the numeric citation marks ship in first-citation order",
      hasStr (censusText c) "[1]") ,
    ("a textual citation ships its author names before the mark",
      hasStr (censusText c) "Doe and van der Berg [2]"),
    ("a grouped citation keeps one bracket", hasStr (censusText c) "[3, 1]"),
    ("the unknown key ships its ? mark", hasStr (censusText c) "[?]"),
    ("the References heading ships", hasStr (censusText c) "References"),
    ("the last entry ships with its position's marker",
      hasStr (censusText c) "[7] Casey Ray"),
    ("the accent composes on the shipped page", hasStr (censusText c) "Künzel"),
    ("the corporate author ships unsplit",
      hasStr (censusText c) "Example Press Editorial Group"),
    ("the elided list ships as et al", hasStr (censusText c) "Ariel Fox"),
    ("the howpublished group ships with its year", hasStr (censusText c) "Online, 2020")]),
  ("declared", fun _ c => [
    ("one page, as the fixture asserts", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared geometry")])]

def censusRows1 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("redefine", fun _ c => [
    ("one page", c.size == 1),
    ("the refused redefinition leaves the built-in title shipping",
      hasStr (censusText c) "Fallback Title Probe"),
    ("the author ships under it", hasStr (censusText c) "An Invented Author"),
    ("the refused body's internals never ship as text",
      !hasStr (censusText c) "venuetitlebox"),
    ("the runnable redefinition ships its own body",
      hasStr (censusText c) "The runnable body wins.")]),
  ("blocks", fun geom c => [
    ("one page", c.size == 1),
    ("each block ships its title",
      hasStr (censusText c) "A Plain Statement" &&
      hasStr (censusText c) "A Loud Statement" &&
      hasStr (censusText c) "A Worked Instance"),
    ("each body ships under its title",
      ((lineYOf c 0 "A Plain Statement").bind fun ty =>
        (lineYOf c 0 "The body of the plain block").map fun by_ =>
          decide (ty < by_)).getD false &&
      hasStr (censusText c) "The alert body stands under its own title." &&
      hasStr (censusText c) "The example body stands under its own title."),
    ("the untitled block ships its body under its empty title band",
      hasStr (censusText c) "An untitled block keeps its body under an empty title band."),
    -- Only `blocktitlebg` is declared, so only plain blocks draw a bar, the untitled one included.
    ("the declared title bar ships on both plain blocks",
      (c[0]?.map (·.fills)).getD 0 == 2),
    ("a filled title stands on the measure, its paint reaching beyond it",
      lineXOf c 0 "A Plain Statement" == some geom.hmargin),
    ("unfilled titles stand on the measure",
      lineXOf c 0 "A Loud Statement" == some geom.hmargin &&
      lineXOf c 0 "A Worked Instance" == some geom.hmargin)]),
  ("poster", fun geom c => [
    ("one face ships as one page", c.size == 1),
    ("the board is the record's A0 landscape trim",
      geom.pageW == Dim.mm 1189 && geom.pageH == Dim.mm 841),
    ("the margins are the record's 1cm safe zone",
      geom.hmargin == Dim.mm 10 && geom.vmargin == Dim.mm 10),
    ("the body sets at beamerposter's 24.88pt normalsize",
      lineSizeOf c 0 "Body text in the first column" == some (Dim.pt 2488 / 100)),
    ("the poster title ships", hasStr (censusText c) "An Invented Poster Probe"),
    ("both panels ship their titles and bodies",
      hasStr (censusText c) "First Invented Panel" &&
      hasStr (censusText c) "Second Invented Panel" &&
      hasStr (censusText c) "entirely synthetic" &&
      hasStr (censusText c) "likewise synthetic"),
    ("the columns stand side by side",
      ((lineXOf c 0 "Body text in the first column").bind fun x1 =>
        (lineXOf c 0 "Body text in the second column").map fun x2 =>
          decide (x1 < x2)).getD false),
    ("no page number ships on a poster",
      ((c[0]?.bind fun p => p.lines.back?).map
        (·.text.trimAscii.toString != "1")).getD false)]),
  ("poster-headline", fun geom c => [
    ("one face ships as one page", c.size == 1),
    ("the band ships the title family",
      hasStr (censusText c) "An Invented Band Title" &&
      hasStr (censusText c) "Alex Placeholder" &&
      hasStr (censusText c) "Sam Example" &&
      hasStr (censusText c) "An Invented Institute"),
    ("the band bar paints from the page top, full width, above the ground",
      ((c[0]?.map (·.fillRects)).getD #[]).any fun r =>
        r.1 == 0 && r.2.1 == 0 && r.2.2.1 == geom.pageW && r.2.2.2 < geom.pageH),
    ("the title matter centres on the declared alignment",
      ((c[0]?.bind fun p => p.lines.find? fun l =>
        hasStr l.text "An Invented Band Title").map fun l =>
          decide ((2 * l.x + l.width - geom.pageW).natAbs ≤ 1)).getD false),
    ("the body columns start below the band",
      (((c[0]?.bind fun p => p.lines.find? fun l =>
          hasStr l.text "An Invented Band Title").map (·.y)).bind fun ty =>
        ((c[0]?.bind fun p => p.lines.find? fun l =>
          hasStr l.text "First Invented Panel").map (·.y)).map fun by_ =>
            decide (ty < by_)).getD false),
    ("the themed alert panel ships its title on a bar",
      hasStr (censusText c) "Second Invented Panel" &&
      (c[0]?.map (·.fills)).getD 0 ≥ 3),
    ("the footercontent line ships as foot furniture",
      ((c[0]?.bind fun p => p.lines.find? fun l =>
        hasStr l.text "An Invented Workshop 2099").map (·.furniture)).getD false),
    ("the corner logo stands as furniture on the band's right",
      (c[0]?.map fun p => p.lines.any fun l =>
        l.furniture && l.text.trimAscii.toString.isEmpty &&
          l.x > geom.pageW / 2).getD false)]),
  ("titleground", fun geom c => [
    ("two pages", c.size == 2),
    ("the title page ships its matter",
      pageHas c 0 "A Placeholder Deck" && pageHas c 0 "P. Placeholder" &&
        pageHas c 0 "example.org"),
    ("the title page's ground covers the page and is painted first",
      (c[0]?.bind fun p => p.fillRects[0]?).map
        (fun r => decide (r.1 == (0 : Dim.Sp) ∧ r.2.1 == (0 : Dim.Sp) ∧
          r.2.2.1 == geom.pageW ∧ r.2.2.2 == geom.pageH)) == some true),
    ("the frame after it ships its own page",
      pageHas c 1 "On the document" &&
        pageHas c 1 "on the ground every other page carries"),
    ("the title starts inside its pinned node separations",
      lineXOf c 0 "A Placeholder Deck" ==
        some (Dim.mm 16 + Ir.pgfInnerSep geom.fontSize + Ir.pgfOuterSep)),
    ("the title sets at its slot's declared size",
      lineSizeOf c 0 "A Placeholder Deck" == some (Dim.pt 18)),
    ("the author's slot is pinned above the page foot, not under the title",
      ((lineYOf c 0 "P. Placeholder").map fun y =>
        decide (y ≤ geom.pageH - Dim.mm 14 ∧ y ≥ geom.pageH - Dim.mm 14 - Dim.pt 14)).getD false),
    ("the institute stands in the foot's other corner, right of the middle",
      ((lineXOf c 0 "example.org").map fun x => decide (x > geom.pageW / 2)).getD false &&
        ((lineYOf c 0 "example.org").map fun y =>
          decide (y ≤ geom.pageH - Dim.mm 14 ∧ y ≥ geom.pageH - Dim.mm 14 - Dim.pt 14)).getD false),
    ("a title page with slots ships no lineage separator",
      (c[0]?.map (·.rules)) == some 0)]),
  ("titlebars", fun geom c =>
    let bars := pageRuleSegs c 0
    let titleY := (lineYOf c 0 "Bars Probe Title").getD 0
    [("one page", c.size == 1),
     ("the styled built-in ships the title", hasStr (censusText c) "Bars Probe Title"),
     ("the author ships under it", hasStr (censusText c) "An Invented Author"),
     ("the body text ships after the title block",
       hasStr (censusText c) "Body text follows the styled built-in title."),
     -- 3 pt and 2 pt match no engine default, so these bars can only come from the fixture.
     ("two bars ship at the body's declared weights",
       bars.map (·.2) == #[Dim.pt 3, Dim.pt 2]),
     ("the top bar stands above the title line, the bottom below",
       (bars.map fun s => decide (s.1 < titleY)) == #[true, false]),
     -- The gaps are the engine's rhythm; the fixture's own `\vskip`s are deliberately unread.
     ("the top bar stands three quanta above the title's cap line",
       (bars[0]?.map fun s => decide (3 * Ir.rhythmQuantum geom.fontSize ≤ titleY - s.1 ∧
         titleY - s.1 ≤ 3 * Ir.rhythmQuantum geom.fontSize + geom.fontSize * 1440 / 1000)).getD false),
     ("the bottom bar stands exactly three quanta below the title's baseline",
       (bars[1]?.map fun s => decide (s.1 - titleY ==
         3 * Ir.rhythmQuantum geom.fontSize + Dim.pt 2)).getD false),
     ("the title is centred in the measure",
       ((lineXOf c 0 "Bars Probe Title").map fun x =>
         decide (x > geom.hmargin)).getD false),
     -- `\Large` is the body's; the engine's default is LARGE, so a default-styled title fails.
     ("the title sets at the body's declared \\Large, not the LARGE default",
       lineSizeOf c 0 "Bars Probe Title" ==
         some (geom.fontSize * 1440 / 1000)),
     -- The author line's 2u strut: 24pt plus one quantum under the bottom bar.
     ("the author line carries its 2u strut under the bottom bar",
       ((pageRuleSegs c 0)[1]?.map fun s =>
         let d := (lineYOf c 0 "An Invented Author").getD 0 - s.1
         decide (Dim.pt 24 + Ir.rhythmQuantum geom.fontSize ≤ d ∧
           d ≤ Dim.pt 24 + Ir.rhythmQuantum geom.fontSize + 2 * geom.fontSize)).getD false),
     -- The rhythm gap after the block, 2u at the body size, plus the interline.
     ("the 2u gap after the title block stands before the body text",
       let d := (lineYOf c 0 "Body text follows").getD 0 -
         (lineYOf c 0 "An Invented Author").getD 0
       decide (Dim.pt 36 ≤ d ∧ d ≤ Dim.pt 36 + 3 * geom.fontSize))]),
  ("fonts", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Faces"),
    ("the body claim ships", hasStr (censusText c) "Body text is set in the serif family")]),
  ("palette", fun _ c => [
    ("one page", c.size == 1),
    ("the coloured heading ships", hasStr (censusText c) "A coloured heading")]),
  ("tokens", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared spacing")]),
  ("fill", fun _ c => [
    ("one page", c.size == 1),
    ("hfill sets both edges on one line",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Left edge").map
        fun l => hasStr l.text "right edge").getD false)]),
  ("links", fun _ c => [
    ("one page", c.size == 1),
    ("the running foot resolves page number and count", hasStr (censusText c) "page 1 of 1"),
    ("link underlines ship as rules", (c[0]?.map fun p => decide (p.rules ≥ 1)).getD false)])]

def censusRows2 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("resume", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Alex Doe"),
    ("the contact line ships", hasStr (censusText c) "alex@example.org")]),
  ("resume-data", fun _ c => [
    ("one page", c.size == 1),
    ("the first record's employer ships", hasStr (censusText c) "Example Corp"),
    ("the record without an end ships the else branch",
      hasStr (censusText c) "1996–present"),
    ("a bounded record ships both years", hasStr (censusText c) "1989–1996"),
    ("a highlights item ships with a marker",
      hasStr (censusText c) "• Measured the bulbs"),
    ("the tie inside a value holds its words on one line",
      (c[0]?.map fun p => p.lines.any fun l =>
        hasStr l.text "potting" && hasStr l.text "shed,").getD false),
    ("the records ship in file order",
      ((censusText c).splitOn "Example Corp").length > 1 &&
        hasStr (((censusText c).splitOn "Example Corp").getLast? |>.getD "")
          "Widgets Ltd")]),
  ("talk", fun _ c => [
    ("a page per overlay step plus one per remaining frame", c.size == 6),
    ("the first step page hides the pending lines, as beamer does by default",
      !pageHas c 0 "Metrics are queryable" && !pageCovered c 0 "Metrics are queryable"),
    ("the next step page shows them", pageHas c 1 "Metrics are queryable"),
    ("the final step page has nothing covered", pageAllRevealed c 2)]),
  ("deck", fun _ c => [
    ("a page per frame and step, the section opening none under a theme with no section page",
      c.size == 7),
    ("the step page covers its pending item at the deck's declared transparent share",
      pageCovered c 1 "Frames are page boundaries" && pageAllRevealed c 2),
    ("the title frame ships the title", pageHas c 0 "A Certified Deck"),
    ("the standout frame fills its background", (c[6]?.map (·.fills == 1)).getD false),
    ("the standout content ships", pageHas c 6 "Questions?"),
    ("the alignment's reasons ship whole beside their steps",
      pageHas c 5 "the first odd number" && pageHas c 5 "two odd numbers")]),
  ("tables-deck", fun _ c => [
    ("the title page, then a page per step of the table frame: no continuation page",
      c.size == 3 && pageHas c 0 "An Invented Table Deck"),
    ("the table frame's first page ships its head, first and last row",
      pageHas c 1 "Count" && pageHas c 1 "A placeholder row with a longer label" &&
        pageHas c 1 "Last row"),
    ("the text column's cells start at one left edge under the centred scope",
      (lineXOf c 1 "Short label").isSome &&
        lineXOf c 1 "Short label" == lineXOf c 1 "A placeholder row with a longer label"),
    ("the count column's cells end at one right edge",
      (lineRightOf c 1 "1,204").isSome && lineRightOf c 1 "1,204" == lineRightOf c 1 "2,274"),
    ("the later columns are hidden on the first step and shown on the second",
      !pageHas c 1 "15.97" && !pageCovered c 1 "15.97" && pageHas c 2 "15.97" && pageAllRevealed c 2)]),
  ("deck1610", fun geom c => [
    ("one page, the frame", c.size == 1),
    -- aspectratio=1610 is beamer's 160×100 mm row (user guide §8.1).
    ("the pages ship on the declared 16:10 stage",
      geom.pageW == Dim.mm 160 && geom.pageH == Dim.mm 100),
    ("the frame title ships", pageHas c 0 "One declared key"),
    ("the frame body ships", pageHas c 0 "160 by 100 millimetres")]),
  ("themed", fun geom c => [
    ("pages", c.size == 8),
    ("the section page carries its progress-bar fills", (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the frame-title bar fills", (c[2]?.map fun p => decide (p.fills ≥ 1)).getD false),
    -- moloch's frametitle bar: a full-width fill, `2·pad + strut` tall at `\large`.
    ("the frame-title bar is moloch's box: 2·pad + strut at the title step",
      let titleSize := Ir.scaleStepIn Ir.sizeScale geom.fontSize "large"
      let pad := Ir.frameTitlePadding.width.resolve titleSize 0
      let strut := Ir.frameTitleStrut titleSize
      let h := Layout.frameBarHeight pad (pad + strut) 0
      (c[2]?.map fun p => p.fillRects.any fun (x, y, w, fh) =>
        x == 0 && y == 0 && w == geom.pageW && fh == h).getD false),
    ("the frame title's baseline stands one pad and one strut below the page top",
      let titleSize := Ir.scaleStepIn Ir.sizeScale geom.fontSize "large"
      lineYOf c 2 "A theme is data" ==
        some (Ir.frameTitlePadding.width.resolve titleSize 0 + Ir.frameTitleStrut titleSize)),
    ("the pending step hides the alert and example beats",
      !pageHas c 3 "alert beat" && !pageHas c 3 "teal example beat"),
    ("the second step shows them", pageHas c 4 "alert beat" && pageHas c 4 "teal example beat"),
    ("the second step reveals them", pageAllRevealed c 4),
    -- The continuation page repeats the title line and the bar fill (page ground + bar ≥ 2 fills).
    ("the tall frame spills onto a continuation page",
      pageHas c 5 "Overflow beat one" && pageHas c 6 "eighteen"),
    ("every page of the frame carries its title",
      pageHas c 5 "A frame that continues" && pageHas c 6 "A frame that continues"),
    ("the continuation page repeats the title bar",
      (c[6]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the continuation body sets below the repeated title, never over it",
      ((lineYOf c 6 "A frame that continues").bind fun ty =>
        (lineYOf c 6 "eighteen").map fun by' => decide (by' > ty)).getD false),
    ("the standout frame fills its background", (c[7]?.map fun p => decide (p.fills ≥ 1)).getD false)]),
  ("daylight", fun _ c => [
    ("pages", c.size == 5),
    ("every page paints the warm paper", c.all fun p => decide (p.fills ≥ 1)),
    ("the frame page carries no title bar", (c[2]?.map (·.fills == 1)).getD false),
    ("the frame title ships as a plain heading", pageHas c 2 "A default bundle"),
    ("the section page draws its progress track",
      (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("each block paints its title band and its body",
      (c[3]?.map fun p => decide (p.fills ≥ 7)).getD false && pageHas c 3 "An alerted card"),
    ("the standout page fills its azure room", (c[4]?.map fun p => decide (p.fills ≥ 1)).getD false),
    ("the accent beats ship", pageHas c 2 "azure emphasis" && pageHas c 2 "green example")]),
  ("latex-idioms", fun _ c => [
    ("one page", c.size == 1),
    ("the opening title ships", hasStr (censusText c) "Spring Bulletin"),
    ("the section rules draw", c.any fun p => decide (p.rules ≥ 1)),
    ("thispagestyle empty keeps the opening page bare of the running head and its number",
      (c[0]?.map fun p => p.lines.all fun l =>
        l.text.trimAscii.toString != "1" && !hasStr l.text "Harbour Rowing Club").getD false),
    ("the hand-aligned pair ships both its words",
      hasStr (censusText c) "Novice" && hasStr (censusText c) "Trophy"),
    ("and the phantom's argument reaches no page",
      !hasStr (censusText c) "gj")]),
  ("headroom", fun geom c => [
    ("one page", c.size == 1),
    ("the head ships with its page number", hasStr (censusText c) "Invented Field Notes"),
    ("the body ships under it", hasStr (censusText c) "reserves a band below the margin"),
    ("the head keeps its own line: no body text beside it",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Invented Field Notes").map
        fun l => !hasStr l.text "tight margin").getD false),
    ("body lines sit at the margin, not in the band",
      lineXOf c 0 "The running head above this page" == some geom.hmargin)]),
  ("wrapper", fun _ c => [
    ("both wrapper halves ship around the body",
      hasStr (censusText c) "First: body one (end First)"),
    ("the renewed environment ships its new half", hasStr (censusText c) "Aside. body two")]),
  ("centering", fun geom c => [
    ("the lead line sits at the margin",
      lineXOf c 0 "Left-aligned lead." == some geom.hmargin),
    ("the centred line sits past the margin",
      (lineXOf c 0 "One centred line.").any fun x => decide (x > geom.hmargin)),
    ("the standout line is centred",
      (lineXOf c 1 "Questions?").any fun x => decide (x > geom.hmargin))])]

def censusRows3 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("columns", fun geom c => [
    ("three frames, three pages", c.size == 3),
    ("the narrow column sets right of the wide one",
      (lineXOf c 0 "A narrow aside.").any fun x => decide (x > geom.hmargin)),
    ("both equal shares ship", pageHas c 1 "left half" && pageHas c 1 "right half"),
    ("the three command-form columns stand side by side",
      ((lineXOf c 2 "First third").bind fun x1 =>
        (lineXOf c 2 "Second third").bind fun x2 =>
          (lineXOf c 2 "Third third").map fun x3 =>
            decide (x1 < x2 && x2 < x3)).getD false),
    ("the three command-form columns share their top line",
      ((lineYOf c 2 "First third").bind fun y1 =>
        (lineYOf c 2 "Second third").bind fun y2 =>
          (lineYOf c 2 "Third third").map fun y3 =>
            decide (y1 == y2 && y2 == y3)).getD false)]),
  ("overlays-blocks", fun _ c => [
    ("a page per step across all frames", c.size == 12),
    ("a list revealed whole is hidden whole",
      !pageHas c 0 "Placeholder point one." && !pageHas c 0 "Placeholder point two."),
    ("the step revealing it ships its markers with it", pageHas c 1 "• Placeholder point one."),
    ("alt inks its first beat alone on the first step",
      pageOccurs c 9 "The first beat." == 1 && !pageHas c 9 "The second beat."),
    ("alt replaces it with the second beat on the later step",
      pageOccurs c 10 "The second beat." == 1 && !pageHas c 10 "The first beat."),
    ("an alternative is inked at full colour, never covered",
      !pageCovered c 9 "The first beat." && !pageCovered c 10 "The second beat."),
    ("a pause inside a column hides below it", !pageHas c 7 "Below the pause." && pageHas c 8 "Below the pause.")]),
  ("chrome", fun geom c => [
    ("pages", c.size == 5),
    -- The title page is `[plain,noframenumbering]`, so the first content frame is 1.
    ("the title page carries no footer",
      !pageHas c 0 "Footers" &&
        ((c[0]?.map fun p => p.lines.all (·.text != "1")).getD false)),
    ("numbering starts at the first countable frame",
      pageHas c 2 "Footers" && lineRightOf c 2 "1" == some (geom.pageW - Ir.footline.right)),
    ("a framefoot note takes the left slot", pageHas c 3 "source: example.org/data"),
    ("the default footer returns when the wrapper ends",
      pageHas c 4 "Footers" && lineRightOf c 4 "3" == some (geom.pageW - Ir.footline.right))]),
  ("footer-left", fun geom c => [
    ("pages", c.size == 4),
    ("the sectionless frame still numbers at the right edge",
      lineRightOf c 1 "1" == some (geom.pageW - Ir.footline.right)),
    ("the number is a line of its own, whole and unmoved",
      ((c[1]?.bind fun p => p.lines.find? fun l => hasStr l.text "1").map
        fun l => l.text == "1").getD false),
    ("the section title takes the left slot flush left",
      lineXOf c 3 "Placement" == some Ir.footline.left),
    ("the sectioned frame numbers at the same right edge",
      lineRightOf c 3 "2" == some (geom.pageW - Ir.footline.right))]),
  ("footer-mixed", fun _ c => [
    ("pages", c.size == 5),
    ("the step pages advance the physical number",
      pageHas c 2 "p. 3" && pageHas c 3 "p. 4"),
    ("and hold the frame number across the step",
      (lineRightOf c 2 "p. 3").isSome && pageHas c 2 "1" && pageHas c 3 "1"),
    ("the plain frame carries the next of both",
      pageHas c 4 "p. 5" && pageHas c 4 "2")]),
  ("footer-collide", fun geom c => [
    ("pages", c.size == 2),
    ("the number still ends at its right inset",
      lineRightOf c 1 "1" == some (geom.pageW - Ir.footline.right)),
    ("the overlong note still ships flush left",
      lineXOf c 1 "0123456789" == some Ir.footline.left)]),
  ("lists", fun _ c => [
    ("one page", c.size == 1),
    ("four itemize levels ship their four marks",
      ["• Outer point one", "– Second level", "* Third level", "· Fourth level"].all
        fun m => hasStr (censusText c) m),
    ("enumerate marks per level", ["1. First", "(a) Nested resets to one",
      "i. Third level", "A. Fourth level"].all fun m => hasStr (censusText c) m),
    ("the enclosing counter resumes", hasStr (censusText c) "3. Third")]),
  ("lists-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the base override ships", hasStr (censusText c) "– The base override"),
    ("the level override ships", hasStr (censusText c) "• The level override")]),
  ("marker-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the declared en-dash marker ships beside each item",
      pageHas c 0 "– First invented point" && pageHas c 0 "– Second invented point")]),
  ("marker-content", fun _ c => [
    ("one page", c.size == 1),
    ("the items ship", pageHas c 0 "An item marked by a picture"),
    ("no default text marker substitutes for the image",
      !pageHas c 0 "• An item" && !pageHas c 0 "– An item")]),
  ("lists-deck", fun _ c => [
    ("pages", c.size == 4),
    ("nesting shows through the theme", pageHas c 2 "– Nested under the stepped item"),
    ("ordered marks on a slide", pageHas c 3 "1. First placeholder")])]

def censusRows4 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("valign", fun _ c => [
    ("five frames, the overflow spilling once", c.size == 6),
    ("each declared frame ships its body",
      pageHas c 0 "A short body sits midway" && pageHas c 1 "This body hugs its title"
        && pageHas c 2 "This body sits on the bottom margin"),
    ("the spill page carries the overflow", pageHas c 5 "resolved to enumerate")]),
  ("images", fun _ c => [
    ("one page", c.size == 1),
    ("the sentence around the inline image ships",
      hasStr (censusText c) "sits in the line"),
    ("the figure caption ships with its number", hasStr (censusText c) "Figure 1: Three rectangles, fitted")]),
  ("svg-figures", fun _ c => [
    ("one page", c.size == 1),
    ("the prose around the figures ships",
      hasStr (censusText c) "A chart drawn by the engine" &&
        hasStr (censusText c) "A moving figure, described" &&
        hasStr (censusText c) "Captions in translucent and reused groups" &&
        hasStr (censusText c) "A field of values drawn as an embedded raster"),
    ("all five figures ship as boxes on the page", (c.map (·.images)).foldl (· + ·) 0 == 5),
    ("all five are the engine's own drawings", (c.map (·.figures)).foldl (· + ·) 0 == 5),
    ("the chart's labels ship as the figure's text",
      c.any fun p => hasStr p.figureText "invented quantity" && hasStr p.figureText "measured value"),
    ("the moving figure's label ships", c.any fun p => hasStr p.figureText "invented signal"),
    ("captions in a translucent text, a translucent group and a reused group all ship",
      c.any fun p => hasStr p.figureText "A faded caption" &&
        hasStr p.figureText "Beside a faded square" && hasStr p.figureText "A reused caption"),
    ("the shaded squares' label ships", c.any fun p => hasStr p.figureText "Shaded"),
    ("the raster figure's labels ship", c.any fun p => hasStr p.figureText "invented field")]),
  ("figures", fun _ c => [
    ("one page", c.size == 1),
    ("the prose around the embedded PDF ships",
      hasStr (censusText c) "Before the figure"),
    ("the inline sentence ships around its embedded page",
      hasStr (censusText c) "And extensionless")]),
  ("webpage", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Doe"),
    ("the section headings ship",
      hasStr (censusText c) "Work" && hasStr (censusText c) "Training")]),
  ("webnav", fun _ c => [
    ("one page", c.size == 1),
    ("the shared content ships", hasStr (censusText c) "appears on every surface"),
    ("the print-only conditional ships on the page",
      hasStr (censusText c) "This sentence is set only on the printed page."),
    ("the unwrapped menu nav ships no body ink",
      !hasStr (censusText c) "Back to top")]),
  ("nav-directory", fun _ c => [
    ("one page", c.size == 1),
    ("the title, its author line and the paragraph ship",
      hasStr (censusText c) "An Invented Directory" && hasStr (censusText c) "Alex Doe" &&
        hasStr (censusText c) "An invented page"),
    ("the three-hundred-entry menu ships no body ink: it is the outline",
      !hasStr (censusText c) "Entry")]),
  ("icons", fun _ c => [
    ("one page", c.size == 1),
    ("the contact words ship", hasStr (censusText c) "Email"),
    ("the icon glyphs ship as ink",
      hasStr (censusText c) "\uF09B" && hasStr (censusText c) "\uF0E0" &&
      hasStr (censusText c) "\uF08C" && hasStr (censusText c) "\uF19D" &&
      hasStr (censusText c) "\uF062")]),
  ("diagram", fun geom c => [
    ("one page", c.size == 1),
    ("the 4×4 grid ships its sixteen fills, as the picture's own marks",
      (c[0]?.map fun p => p.paths == 16 && p.fills == 0).getD false),
    ("every diagonal label ships",
      ["aa", "bb", "cc", "dd"].all fun l => hasStr (censusText c) l),
    ("the labels step up the diagonal",
      (((lineXOf c 0 "aa").bind fun xa => (lineXOf c 0 "dd").map fun xd =>
        decide (xa < xd)).getD false)),
    ("the centred picture stands past the margin",
      ((lineXOf c 0 "aa").map fun x => decide (x > geom.hmargin)).getD false),
    ("the prose around the diagram ships",
      hasStr (censusText c) "Before the diagram" &&
        hasStr (censusText c) "After the diagram")]),
  ("diagram-overflow", fun _ c => [
    ("one page", c.size == 1),
    ("the band ships as a fill, the picture's own mark",
      (c[0]?.map fun p => p.paths == 1 && p.fills == 0).getD false),
    ("its label ships", hasStr (censusText c) "wide band")]),
  ("diagram-boundary", fun _ c => [
    ("one page", c.size == 1),
    ("the boundary request ships as one image box where the picture stood",
      (c[0]?.map (·.images == 1)).getD false),
    ("the prose around the requested picture ships",
      hasStr (censusText c) "routes to the" &&
        hasStr (censusText c) "Text follows the requested picture")]),
  ("diagram-refused", fun _ c => [    ("one page", c.size == 1),
    ("the placeholder outline ships as four fills, the picture's own marks",
      (c[0]?.map fun p => p.paths == 4 && p.fills == 0).getD false),
    ("the diagnostic code ships inside the box", hasStr (censusText c) "W0362"),
    ("the prose around the placeholder ships",
      hasStr (censusText c) "constructs outside the rendered subset" &&
        hasStr (censusText c) "Text resumes after the placeholder")]),
  ("diagram-shapes", fun _ c => [
    ("one page", c.size == 1),
    -- three outlines + four edges + one arrow-tip triangle
    ("the node outlines, edges, and tip ship as page paths",
      (c[0]?.map (·.paths == 8)).getD false),
    ("the text node body ships", hasStr (censusText c) "tile"),
    ("the curve's mid-path label ships", hasStr (censusText c) "bend"),
    ("the alphabet edge label ships upright",
      hasStr (censusText c) "rd" && !hasStr (censusText c) "𝑟𝑑"),
    ("every node ships a glyph line",
      (c[0]?.map fun p => decide (p.lines.size ≥ 3)).getD false)])]

def censusRows5 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("diagram-tikzset", fun _ c => [
    ("one page", c.size == 1),
    -- Two circles, one rectangle and one edge, then the second picture's two inheriting edges.
    ("the styled node outlines and the edges ship as page paths",
      (c[0]?.map (·.paths == 6)).getD false),
    ("no boundary box stands where the picture is",
      (c[0]?.map (·.images == 0)).getD false),
    ("the edge that declared nothing inherits the picture's colour and width",
      ((c[0]?.bind (·.pathStrokes[4]?)).map fun (col, w) =>
        col == { r := 0, g := 0, b := 255 } && w == Ir.Pic.thickWidth).getD false),
    ("the edge that re-declared the colour keeps its own, and the picture's width",
      ((c[0]?.bind (·.pathStrokes[5]?)).map fun (col, w) =>
        col == { r := 255, g := 0, b := 0 } && w == Ir.Pic.thickWidth).getD false),
    ("every styled node's body ships",
      hasStr (censusText c) "P" && hasStr (censusText c) "Q" &&
        hasStr (censusText c) "out"),
    ("the prose around the diagram ships",
      hasStr (censusText c) "Before the diagram" &&
        hasStr (censusText c) "After the diagram")]),
  -- Four tree edges with their tips make eight marks; the draw=none edge ships none.
  ("diagram-tree", fun _ c => [
    ("one page", c.size == 1),
    ("no boundary box stands where the pictures are",
      (c[0]?.map (·.images == 0)).getD false),
    ("every edge, tip, dot and curve ships as a page path",
      (c[0]?.map (·.paths == 18)).getD false),
    ("every node label ships",
      ["sum", "left", "right", "mid", "span"].all fun l => hasStr (censusText c) l),
    ("the tree grows up: its children stand above the root",
      (((lineYOf c 0 "sum").bind fun ys => (lineYOf c 0 "left").map fun yl =>
        decide (yl < ys)).getD false)),
    ("growing up turns the siblings: the first child stands right of the second",
      (((lineXOf c 0 "left").bind fun xl => (lineXOf c 0 "right").map fun xr =>
        decide (xr < xl)).getD false)),
    ("the declared size sets the label after it smaller than the one before",
      (((lineSizeOf c 0 "span").bind fun a => (lineSizeOf c 0 "mid").map fun b =>
        decide (a < b)).getD false)),
    ("the picture's font= sets its tree's labels below the body size",
      (((lineSizeOf c 0 "sum").bind fun a => (lineSizeOf c 0 "mid").map fun b =>
        decide (a < b)).getD false))]),
  -- The rounded box, turned polyline, continued arc, stopped arrow and tip, and faded fill.
  ("diagram-scope", fun _ c => [
    ("one page", c.size == 1),
    ("no boundary box stands where the picture is",
      (c[0]?.map (·.images == 0)).getD false),
    ("every path, tip and fill ships as a page path",
      (c[0]?.map (·.paths == 6)).getD false),
    ("the scope's colour and width stroke its path, and end with it",
      (c[0]?.map fun p => p.pathStrokes.any (· == ({ r := 42, g := 111, b := 78 }, Ir.Pic.thickWidth)) &&
        p.pathStrokes.any (·.2 == Ir.Pic.thinWidth)).getD false),
    ("the labels ship, the turned one beside its path",
      hasStr (censusText c) "box" && hasStr (censusText c) "turned")]),
  -- Seven arrows, each a shaft and a tip, and the description label's ground.
  ("diagram-cd", fun _ c => [
    ("one page", c.size == 1),
    ("no boundary box stands where the diagrams are",
      (c[0]?.map (·.images == 0)).getD false),
    ("every arrow's shaft and tip ships as a page path, and the description's ground",
      (c[0]?.map fun p => p.paths == 15 && p.pathStrokes.size == 14).getD false),
    ("every cell and label ships as mathematics",
      ["𝑃", "𝑄", "𝑅", "𝑆", "𝑢", "𝑣", "𝑤", "𝑥", "𝐾", "𝐿", "𝑀", "𝑚"].all
        fun l => hasStr (censusText c) l),
    ("a label is set a script size below its cells",
      (((lineSizeOf c 0 "𝑢").bind fun a => (lineSizeOf c 0 "𝑃").map fun b =>
        decide (a < b)).getD false)),
    ("a row stands below the row before it",
      (((lineYOf c 0 "𝑃").bind fun yp => (lineYOf c 0 "𝑅").map fun yr =>
        decide (yp < yr)).getD false)),
    ("the coloured diagonal strokes its shaft and tip in its colour",
      (c[0]?.map fun p => (p.pathStrokes.filter (·.1 == { r := 255, g := 0, b := 0 })).size == 2).getD false),
    ("the prose around the square ships",
      hasStr (censusText c) "Before the square" && hasStr (censusText c) "After the square")]),
  -- Each mark is one page path; the pin's edge is in help lines and the fitted frame dashed.
  ("diagram-longtail", fun _ c => [
    ("one page", c.size == 1),
    ("no boundary box stands where the pictures are",
      (c[0]?.map (·.images == 0)).getD false),
    ("every shading, fill, outline, arrow, edge, frame and brace ships as a page path",
      (c[0]?.map fun p => p.paths == 11 && p.pathStrokes.size == 8).getD false),
    ("the pin's edge ships in help lines, gray at 0.2 pt",
      (c[0]?.map fun p => p.pathStrokes.any (· == ({ r := 128, g := 128, b := 128 }, Dim.pt 2 / 10))).getD false),
    ("the fitted frame ships dashed",
      (c[0]?.map fun p => p.pathRuns.any (·.2)).getD false),
    ("every node's text, its label's and its pin's ships",
      ["oval", "kite", "node", "top", "pin"].all fun l => hasStr (censusText c) l)]),
  ("diagram-strokes", fun _ c => [
    ("one page", c.size == 1),
    ("the three strokes ship as the picture's own marks, no page fill among them",
      (c[0]?.map fun p => p.paths == 3 && p.fills == 0).getD false),
    ("the chain ships as one path of two segments, joined at its corner",
      ((c[0]?.bind (·.pathRuns[0]?)).map fun (runs, dashed) => runs == #[2] && !dashed).getD false),
    ("the zero line width ships as the hairline, width zero",
      ((c[0]?.bind (·.pathStrokes[1]?)).map fun (_, w) => w == 0).getD false),
    ("the dashed chain ships as one dashed path of two segments",
      ((c[0]?.bind (·.pathRuns[2]?)).map fun (runs, dashed) => runs == #[2] && dashed).getD false),
    ("the prose around the strokes ships",
      hasStr (censusText c) "Before the strokes" &&
        hasStr (censusText c) "After the strokes")]),
  ("tables", fun geom c => [
    ("one page", c.size == 1),
    ("the header row ships", hasStr (censusText c) "Construct"
      && hasStr (censusText c) "Meaning"),
    ("every body cell ships", hasStr (censusText c) "invented row"
      && hasStr (censusText c) "alpha" && hasStr (censusText c) "beta"),
    ("both table captions ship, each with its number in front",
      hasStr (censusText c) "Table 1: A booktabs table with declared spacing."
        && hasStr (censusText c) "Table 2: The caption above: the table convention."),
    ("the figure caption ships, numbered on its own counter",
      hasStr (censusText c) "Figure 1: A figure’s caption, bound below what it captions."),
    -- top + mid + bottom, then top + cmid + bottom: six drawn rules.
    ("the booktabs rules draw", ((c[0]?.map (·.rules)).getD 0) == 6),
    ("cells sit in their declared columns: the second column right of the first",
      ((lineXOf c 0 "Construct").bind fun a =>
        (lineXOf c 0 "Meaning").map fun b => decide (a < b)).getD false),
    ("the floated table centres: its first cell sits past the margin",
      (lineXOf c 0 "invented row").any fun x => decide (x > geom.hmargin)),
    ("the spanned head ships once, right of the first column",
      pageOccurs c 0 "a spanned head" == 1 &&
      ((lineXOf c 0 "a spanned head").bind fun h =>
        (lineXOf c 0 "left").map fun l => decide (h > l)).getD false)]),
  ("tables-ragged", fun _ c => [
    ("one page", c.size == 1),
    ("every declared cell ships, the ragged row's included",
      hasStr (censusText c) "alpha" && hasStr (censusText c) "gamma"
        && hasStr (censusText c) "delta" && hasStr (censusText c) "epsilon"),
    ("the rules draw", ((c[0]?.map (·.rules)).getD 0) == 2)]),
  ("subfigures", fun _ c => [
    ("one page", c.size == 1),
    ("both panels ship their diagram labels",
      hasStr (censusText c) "left box" && hasStr (censusText c) "right box"),
    ("the lettered subcaptions ship",
      hasStr (censusText c) "(a) The first invented panel."
        && hasStr (censusText c) "(b) The second invented panel."),
    ("the parent caption ships its figure number",
      hasStr (censusText c) "Figure 1: Two invented panels side by side."),
    ("the second figure keeps the document-order counter",
      hasStr (censusText c) "Figure 2: The plain figure, numbered second."),
    ("the panels stand side by side: the right label right of the left",
      ((lineXOf c 0 "left box").bind fun xl => (lineXOf c 0 "right box").map
        fun xr => decide (xl < xr)).getD false)]),
  ("box-sides", fun geom c =>
    let near (a b : Dim.Sp) : Bool := decide ((a - b).natAbs ≤ (Dim.pt 1).natAbs)
    let right := geom.hmargin + geom.textWidth
    [("one page", c.size == 1),
     ("the document title stands centred in the measure",
       ((lineXOf c 0 "An Invented Box Study").bind fun x =>
         (lineRightOf c 0 "An Invented Box Study").map fun r =>
           near (x - geom.hmargin) (right - r)).getD false),
     ("the tabular title stands centred in the measure",
       ((lineXOf c 0 "An Invented Tabular Title").bind fun x =>
         (lineRightOf c 0 "An Invented Tabular Title").map fun r =>
           near (x - geom.hmargin) (right - r)).getD false),
     ("the lone minipage stands centred, a quarter of the measure each side",
       ((lineXOf c 0 "An invented lone minipage").map
         (near · (geom.hmargin + geom.textWidth / 4))).getD false),
     ("the parbox stands centred, three tenths of the measure each side",
       ((lineXOf c 0 "An invented parbox").map
         (near · (geom.hmargin + geom.textWidth * 3 / 10))).getD false),
     ("the right-set table ends a tabcolsep before the measure's right edge",
       ((lineRightOf c 0 "second row").map (near · (right - Dim.pt 6))).getD false)]),
  ("float-center", fun _ c => [
    ("one page", c.size == 1),
    ("the figure caption ships with its number",
      hasStr (censusText c) "Figure 1: An invented centred panel."),
    ("the grouped body ships as float content",
      hasStr (censusText c) "An invented stand-in for a centred panel body."),
    ("the table caption ships with its number after its tabular",
      hasStr (censusText c) "Table 1: An invented centred strip."),
    ("the tabular content ships",
      hasStr (censusText c) "alpha" && hasStr (censusText c) "delta"),
    ("the references resolve to the numbers the captions carry",
      hasStr (censusText c) "Figure1 and Table1 are referenced")]),
  ("math", fun _ c => [
    ("one page", c.size == 1),
    ("prose around the display ships",
      hasStr (censusText c) "The paragraph continues after the display"),
    ("the display-size sum ships as a glyph", hasStr (censusText c) "∑"),
    ("an align row ships aligned glyphs", hasStr (censusText c) "=(𝑥−1)(𝑥+1)"),
    ("every fraction bar, overbar, and overline ships as a rule",
      ((c[0]?.map (·.rules)).getD 0) == 10),
    ("the accent marks ship as glyphs",
      hasStr (censusText c) "\u0302" && hasStr (censusText c) "\u20D7"),
    ("the out-of-scope construct degrades to its text content, never its markup",
      hasStr (censusText c) "?=" && !hasStr (censusText c) "overset"),
    ("\\mathbb takes its Letterlike scalars", hasStr (censusText c) "ℝ"
      && hasStr (censusText c) "ℂ"),
    ("the bold alphabet ships, boldsymbol keeps the variable italic",
      hasStr (censusText c) "v" && !hasStr (censusText c) "𝐯"
        && hasStr (censusText c) "𝛽"),
    ("\\mathrm sets upright", hasStr (censusText c) "Err"),
    ("a document macro's expansion ships",
      hasStr (censusText c) "w" && !hasStr (censusText c) "𝐰"),
    ("a word stands as a script's argument", hasStr (censusText c) "null")]),
  ("math-text", fun _ c => [
    ("one page", c.size == 1),
    ("\\textbf and \\textit ship the alphabets \\mathbf and \\mathit mean",
      !hasStr (censusText c) "𝐮" && !hasStr (censusText c) "𝑣"
        && hasStr (censusText c) "u"),
    ("a coloured letter ships its glyph", hasStr (censusText c) "𝑤"),
    ("\\text sets its words upright",
      hasStr (censusText c) "gain" && hasStr (censusText c) "loss"),
    ("a brace group inside \\text is grouping alone",
      hasStr (censusText c) "abc"),
    ("a symbol inside \\text ships its scalar",
      hasStr (censusText c) "first…last"),
    ("the coloured styled alignment ships its operator and its word",
      hasStr (censusText c) "∑" && hasStr (censusText c) "bound above"),
    ("an alignment's reasons ship whole",
      hasStr (censusText c) "by the placeholder rule that swaps two terms" &&
        hasStr (censusText c) "by an invented lemma"),
    ("a condition ships its words", hasStr (censusText c) "otherwise"),
    ("the unmodelled construct ships its content", hasStr (censusText c) "?="),
    ("no page of this fixture ships a control sequence",
      !hasStr (censusText c) "overset" && !hasStr (censusText c) "textcolor"
        && !hasStr (censusText c) "textbf")]),
  ("math-alpha", fun _ c =>
    let has (n : Nat) := hasStr (censusText c) (String.ofList [Char.ofNat n])
    [
    ("one page", c.size == 1),
    ("the styled letters ship their plain base glyphs",
      hasStr (censusText c) "B" && hasStr (censusText c) "C"
        && hasStr (censusText c) "D" && hasStr (censusText c) "E"),
    ("a styled scalar never ships a Mathematical Alphanumeric codepoint",
      !has 0x1D401 && !has 0x1D436 && !has 0x1D5A3 && !has 0x1D674),
    ("a styled digit ships its digit", hasStr (censusText c) "7"),
    ("a nested styled scalar ships its letter in a script",
      hasStr (censusText c) "k"),
    ("the unstyled variables ship as italic Alphanumeric scalars",
      has 0x1D465 && has 0x1D466),
    ("no page of this fixture ships a control sequence",
      !hasStr (censusText c) "mathsf" && !hasStr (censusText c) "mathbf"
        && !hasStr (censusText c) "mathrm")]),
  ("math-cancel", fun _ c => [
    ("one page", c.size == 1),
    ("the document title ships", hasStr (censusText c) "Annotated Formulas"),
    ("the four commands ship their strikes and arrowheads",
      ((c[0]?.map (·.polys.size)).getD 0) == 8),
    ("both annotation values and the neighbouring superscripts ship",
      ["0", "7", "𝑥", "𝑦", "𝑧", "𝑤", "2"].all (hasStr (censusText c) ·)),
    ("the fraction still ships its bar", ((c[0]?.map (·.rules)).getD 0) > 0),
    ("no cancellation command reaches the page as markup",
      !hasStr (censusText c) "cancel" && !hasStr (censusText c) "textcolor")]),
  ("math-companion", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display sum ships as a glyph", hasStr (censusText c) "∑"),
    ("the fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1),
    ("prose after the display ships",
      hasStr (censusText c) "The paragraph continues after the display")])]

def censusRows6 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("math-first", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1)]),
  ("greek-literal", fun _ c => [
    ("one page", c.size == 1),
    ("lowercase literals ship the Mathematical Italic scalars",
      ["𝜆", "𝜃", "𝜑", "𝜀", "𝛼", "𝛽", "𝛾", "𝜔"].all (hasStr (censusText c))),
    ("the symbol slots ship their own scalars",
      hasStr (censusText c) "𝜖" && hasStr (censusText c) "𝜙"),
    ("capitals ship upright", hasStr (censusText c) "Ω" && hasStr (censusText c) "Φ"),
    ("no Greek letter ships as body-face source text",
      ["λ", "θ", "φ", "ε", "ϵ", "ϕ", "α", "β", "γ", "ω"].all fun g =>
        !hasStr (censusText c) g),
    ("the function name stays upright", hasStr (censusText c) "cos")]),
  ("quotes", fun geom c => [
    ("one page", c.size == 1),
    ("the quotation's text ships", hasStr (censusText c) "A short invented epigraph"),
    ("the quotation's second paragraph ships",
      hasStr (censusText c) "The second paragraph of the same quotation"),
    ("prose sits at the margin",
      lineXOf c 0 "A paragraph before the quotation" == some geom.hmargin),
    ("the quotation indents from the margin by \\leftmargini (classes.dtx: 2.5em)",
      lineXOf c 0 "A short invented epigraph"
        == some (geom.hmargin + geom.fontSize * 5 / 2))]),
  ("quote-deck", fun geom c => [
    ("one frame, one page", c.size == 1),
    ("the quotation ships on the slide",
      pageHas c 0 "Typesetting is invisible until it fails"),
    ("the slide's quotation indents from the margin by beamer's \\leftmargini (2em of 10.95pt)",
      (lineXOf c 0 "Typesetting is invisible").any fun x =>
        decide (x == geom.hmargin + 2 * (Dim.pt 1095 / 100)))]),
  ("outline", fun _ c => [
    ("one page", c.size == 1),
    ("the level-0 title ships as the title furniture",
      hasStr (censusText c) "An Invented Field Guide"),
    ("the author line ships under it", hasStr (censusText c) "Alex Doe"),
    ("every rung of the heading ladder ships",
      ["Habitats", "Wetlands", "Reed Beds", "Migration"].all
        fun h => hasStr (censusText c) h)]),
  ("outline-gap", fun _ c => [
    ("one page", c.size == 1),
    ("the diagnosed document still ships every heading",
      hasStr (censusText c) "Field Notes" &&
        hasStr (censusText c) "A Detail Too Deep")]),
  ("overlays", fun _ c => [
    ("one handout page per step", c.size == 10),
    ("a pending step, a set and an item covered again ship only where they show",
      pageHas c 7 "Early" && pageHas c 7 "Every other" && !pageHas c 7 "Later" &&
      pageHas c 8 "Early" && !pageHas c 8 "Every other" && pageHas c 8 "Later" &&
      !pageHas c 9 "Early" && pageHas c 9 "Every other" && pageHas c 9 "Later"),
    ("step one hides the later beats", !pageHas c 0 "Second beat." && !pageHas c 0 "Third beat."),
    ("each later step shows its beat", pageHas c 1 "Second beat." && pageHas c 2 "Third beat."),
    ("the last step reveals everything", pageAllRevealed c 2),
    ("pause hides what follows it", !pageHas c 3 "After the pause." && pageHas c 4 "After the pause."),
    ("visible ships none of its argument off its step",
      !pageHas c 5 "a phrase kept in place" && !pageCovered c 5 "a phrase kept in place"),
    ("its line stands where its step sets it, as wide, the phrase inked there",
      let line (i : Nat) := (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text "and after it").map
        fun l => (l.x, l.y, l.width)
      (line 5).isSome && line 5 == line 6 && pageHas c 6 "a phrase kept in place" &&
        pageAllRevealed c 6)]),
  ("overprint", fun _ c => [
    ("a page per step across the three frames: three, two, one", c.size == 6),
    ("the opening step inks its one reading and neither of the others",
      pageOccurs c 0 "The lone opening reading." == 1 &&
        !pageHas c 0 "A listed point on the middle step." &&
        !pageHas c 0 "The closing reading opens a paragraph."),
    ("an item holding a list steps whole, markers and all, alone on its step",
      pageHas c 1 "• A listed point on the middle step." &&
        pageHas c 1 "• A second listed point beside it." &&
        !pageHas c 1 "The lone opening reading."),
    ("an item holding two paragraphs ships both, on two baselines",
      pageHas c 2 "The closing reading opens a paragraph." &&
        pageHas c 2 "And ends on a second paragraph." &&
        ((lineYOf c 2 "opens a paragraph").bind fun y1 =>
          (lineYOf c 2 "second paragraph").map fun y2 => decide (y1 < y2)).getD false),
    ("content before the first item stands on every step of its frame",
      pageOccurs c 3 "Standing above every reading." == 1 &&
        pageOccurs c 4 "Standing above every reading." == 1),
    ("each later reading ships on its own step page only",
      pageOccurs c 3 "Shown on the opening step only." == 1 &&
        !pageHas c 3 "Shown on the later step only." &&
        pageOccurs c 4 "Shown on the later step only." == 1 &&
        !pageHas c 4 "Shown on the opening step only."),
    ("a reading is inked at full colour: an alternative is replaced, never dimmed",
      (List.range 6).all fun i => pageAllRevealed c i),
    ("the reading the rewrite refuses to number ships once, not several",
      pageOccurs c 5 "A reading kept as written." == 1),
    ("the readings are steps of one frame, not frames of their own: the \
frame number holds across each frame's step pages",
      (List.range 6).map (fun i =>
        (c[i]?.bind fun p => (p.lines.find? (·.furniture)).map (·.text)).getD "")
        == ["1", "1", "1", "2", "2", "3"])]),
  ("notes", fun _ c => [
    ("one page", c.size == 1),
    ("the note never ships on the handout", !hasStr (censusText c) "Say hello"),
    ("the paragraph flows on unbroken", hasStr (censusText c) "never breaks the flow")]),
  ("furniture", fun _ c => [
    ("pages", c.size == 6),
    ("the title ships", pageHas c 0 "Frame Furniture"),
    ("the centred line ships", hasStr (censusText c) "This line is centred."),
    ("the step page hides its pending beats", !pageHas c 3 "Second beat." && pageHas c 4 "Second beat."),
    ("the narrow column ships", hasStr (censusText c) "The narrow column.")]),
  ("trio-page", fun _ c => [
    ("one page", c.size == 1),
    ("the studio name ships", hasStr (censusText c) "Cardamom Press"),
    ("the shared section style draws its rules", (c[0]?.map (·.rules == 2)).getD false)])]

def censusRows7 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("palette-seeds", fun _ c => [
    ("pages", c.size == 2),
    ("the seeded frame title ships", pageHas c 0 "Seeded"),
    ("each block's title ships", pageHas c 0 "A Plain Statement" &&
      pageHas c 0 "A Loud Statement" && pageHas c 0 "A Worked Instance"),
    ("three blocks paint a band and a body each, under the title bar",
      (c[0]?.map fun p => decide (7 ≤ p.fills)).getD false),
    ("the listing ships", pageHas c 1 "synthetic")]),
  ("trio-deck", fun _ c => [
    ("a page per frame, the section opening none under a theme with no section page",
      c.size == 3),
    ("the title ships", pageHas c 0 "Cardamom Press"),
    ("the section's frame follows the first", pageHas c 2 "Editions of 64")]),
  ("trio-card", fun geom c => [
    ("two faces, two pages", c.size == 2),
    ("the front ships the name", pageHas c 0 "Pat Placeholder"),
    ("the back ships the contact", pageHas c 1 "press@example.org"),
    ("each face ships exactly the eight cut marks and no other fill",
      c.all fun p => p.fills == 8),
    ("every mark stands in the bleed strip: outside the trim, inside the medium",
      c.all fun p => p.fillRects.all fun r =>
        decide (-geom.bleed ≤ r.1 ∧ r.1 + r.2.2.1 ≤ geom.pageW + geom.bleed ∧
          -geom.bleed ≤ r.2.1 ∧ r.2.1 + r.2.2.2 ≤ geom.pageH + geom.bleed) &&
        decide (r.1 + r.2.2.1 ≤ 0 ∨ geom.pageW ≤ r.1 ∨
          r.2.1 + r.2.2.2 ≤ 0 ∨ geom.pageH ≤ r.2.1)),
    ("no mark ink within the declared gap of a trim corner",
      c.all fun p => p.fillRects.all fun r =>
        ([(0, 0), (geom.pageW, 0), (0, geom.pageH), (geom.pageW, geom.pageH)] :
            List (Dim.Sp × Dim.Sp)).all fun cc =>
          decide ¬(r.1 < cc.1 + geom.markGap ∧ cc.1 - geom.markGap < r.1 + r.2.2.1 ∧
            r.2.1 < cc.2 + geom.markGap ∧ cc.2 - geom.markGap < r.2.1 + r.2.2.2)),
    ("the marks are duplex-symmetric: the horizontal flip maps each onto a mark",
      c.all fun p => p.fillRects.all fun r =>
        p.fillRects.contains (geom.pageW - r.1 - r.2.2.1, r.2.1, r.2.2.1, r.2.2.2))]),
  ("lineno", linenoCensus),
  ("lineno-modulo", linenoModuloCensus),
  ("cond-newif", condBranchRow ["Setter branch ships.", "Initial branch ships."]
    ["Setter branch hidden.", "Initial branch hidden."]),
  ("cond-ifdefined", condBranchRow ["Defined branch ships.", "Absent branch ships."]
    ["Defined branch hidden.", "Absent branch hidden."]),
  ("cond-ifx", condBranchRow ["Equal branch ships.", "Unequal branch ships."]
    ["Equal branch hidden.", "Unequal branch hidden."]),
  ("cond-ifnum", condBranchRow ["Holding branch ships.", "Failing branch ships."]
    ["Holding branch hidden.", "Failing branch hidden."]),
  ("cond-loaded", condBranchRow ["Loaded branch ships.", "Unloaded branch ships."]
    ["Loaded branch hidden.", "Unloaded branch hidden."]),
  ("alert-mark", fun _ c => [
    ("pages", c.size == 1),
    ("the alerted words ship", pageHas c 0 "marked"),
    ("the alert's mark ships in the accent, under the short alert and each line of the long one",
      (c[0]?.map fun p =>
        let ys := (p.decorations.filter fun d => match d.1 with
          | .highlight col _ => col == Ir.Color.ofHtml 0xFA 0xCC 0x15
          | .underline | .lineThrough => false).map (·.2.1)
        decide (3 ≤ (ys.toList.eraseDups).length)).getD false)]),
  ("deck-sections", fun _ c => [
    ("a page per frame and one for the text outside every frame, none for a section",
      c.size == 6),
    ("each page holds its own frame's or the outside text's words, in order",
      [(0, "Sections Without Pages"), (1, "kettle fills"), (2, "spout of"), (3, "Cups follow"),
        (4, "stands on a page"), (5, "dries the cups")].all fun (i, w) => pageHas c i w),
    ("a reference to a section and a subsection shows beamer's number",
      pageHas c 1 "2 pours" && pageHas c 2 "1 sets" && pageHas c 3 "1 said"),
    ("the footline names the section in force on every frame",
      pageHas c 1 "Kettles" && pageHas c 2 "Kettles" && pageHas c 3 "Cups" &&
        pageHas c 5 "Washing up"),
    ("the text outside every frame shares its page with no frame",
      !pageHas c 4 "Serving" && !pageHas c 4 "Drying")]),
  ("deck-hooks", fun _ c => [
    ("a page per frame and one per section the document's hook opens, none for a starred one",
      c.size == 7),
    ("each page holds its frame's words or its section's title, in order",
      [(0, "Sections Behind Hooks"), (1, "Wheels"), (2, "holds its spokes"), (3, "runs true"),
        (4, "Chains"), (5, "Chains follow"), (6, "spare tube")].all fun (i, w) => pageHas c i w),
    ("a section's page shows its title alone, and a starred section inks nothing",
      !pageHas c 1 "Spokes" && !pageHas c 4 "Links" && !pageHas c 6 "Spare parts"),
    ("a reference to a section shows beamer's number", pageHas c 2 "2 drives" && pageHas c 5 "1 said")])]

/-- Whether `a` ships above `b` on page 0. -/
def shipsAbove (c : Array CensusPage) (a b : String) : Bool :=
  match lineYOf c 0 a, lineYOf c 0 b with
  | some ya, some yb => decide (ya < yb)
  | _, _ => false

/-- Whether `b` ships on the line right after `a`'s on page 0. -/
def shipsNext (c : Array CensusPage) (a b : String) : Bool :=
  match c[0]? with
  | some p =>
    match p.lines.findIdx? (hasStr ·.text a) with
    | some i => (p.lines[i + 1]?.map (hasStr ·.text b)).getD false
    | none => false
  | none => false

/-- The code fixtures' census rows: prose where its comment stands or above the code it
documents, the code every character, no comment delimiter of the prose and no directive. -/
def censusCodeRows :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("code-lean", fun _ c => [
    ("one page", c.size == 1),
    ("the module doc's heading ships first, as the title", shipsAbove c "Tide tables" "Every name"),
    ("the first module doc stands above the block comment before it",
      shipsAbove c "What the page shows" "Aninventedmodule"),
    ("a docstring stands right above its declaration's code",
      shipsNext c "The heights, in centimetres" "defabove(mark:Nat)"),
    ("the code keeps its line comment, its string's markers and its nested block comment",
      hasStr (censusInk c) "--alinecommentstaysinthecode" &&
        hasStr (censusInk c) "\"a/--notadoc-/b\"" && hasStr (censusInk c) "/-nested-/"),
    ("an indented field docstring stays in the code",
      hasStr (censusInk c) "/--Afield'sdocstringisindentedandstaysinthecode.-/"),
    ("no prose ships its comment delimiters, and the directive ships nowhere",
      !hasStr (censusInk c) "/-!" && !hasStr (censusInk c) "/--Theheights" &&
        !hasStr (censusInk c) "leantex:")]),
  ("code-python", fun _ c => [
    ("one page", c.size == 1),
    ("the file's name ships first, as its title", shipsAbove c "code-python.py" "Kettle timings."),
    ("the module docstring stands above the line before it", shipsAbove c "Kettle timings." "#!/usr"),
    ("a docstring stands above its def, and the def's body follows its header",
      shipsNext c "Return the minutes" "defminutes(litres:float)->float:" &&
        shipsNext c "defminutes(litres:float)" "return2.5*litres+0.5"),
    ("a decorated def's prose stands above its decorator, and a raw docstring keeps its backslash",
      shipsNext c "Round up; a raw docstring keeps \\d" "@functools.lru_cache(maxsize=None)"),
    ("a method's docstring stands above its header, which keeps its indentation",
      shipsNext c "Describe the kettle" "deflabel(self)->str:"),
    ("the code keeps its comment and its f-string, and no docstring quote ships",
      hasStr (censusInk c) "#acommentstaysinthecode" &&
        hasStr (censusInk c) "f\"{self.capacity}litres\"" && !hasStr (censusInk c) "\"\"\"")]),
  ("code-bash", fun _ c => [
    ("one page", c.size == 1),
    ("the file's name ships first, as its title", shipsAbove c "code-bash.sh" "Rinse the cache"),
    ("the leading comment block stands above the line before it", shipsAbove c "Rinse the cache" "#!/usr"),
    ("the code after the block joins the line before it in one listing",
      shipsNext c "#!/usr/bin/envbash" "set-eu"),
    ("the block ships without its comment markers, the code with its own",
      !hasStr (censusText c) "# Rinse" && hasStr (censusInk c) "#atrailingcommentstaysinthecode")]),
  ("lean-cite", fun _ c => [
    ("one page", c.size == 1),
    ("a bracketed key ships as alpha's label, as doc-gen4 shows its tag, collapsed or not",
      hasStr (censusText c) "does, [Ash01], and" && hasStr (censusText c) "form, [BC02];"),
    ("a key the bibliography lacks ships as written, as does a bracketed key in code",
      hasStr (censusText c) "[unknown1999]" && hasStr (censusInk c) "[ash2001]"),
    ("Pandoc's spelling cites, and an @name the bibliography lacks ships as written",
      hasStr (censusText c) "[Roe20, p. 3]" && hasStr (censusInk c) "BirchandCole[BC02]" &&
        hasStr (censusText c) "@List.map"),
    ("the list ships last, under its heading", shipsAbove c "References" "Ada Ash. Alpha Notes")]),
  ("lean-cite-include", fun _ c => [
    ("one page", c.size == 1),
    ("the article's and its Lean file's citations ship in one numbering, in the article's style",
      ["citing [1] before", "does, [2], and", "form, [3];", "Birch and Cole [3]",
        "Doe and Hale [5] after"].all (hasStr (censusProse c) ·)),
    ("the included documentation ships as prose under its heading, its code as a listing",
      shipsAbove c "Citing from Lean documentation" "A module doc cites" &&
        hasStr (censusInk c) "defsucc'(n:Nat):Nat:=n+1" && !hasStr (censusProse c) "/-!"),
    ("one reference list ships all five entries, once each, a key both files hold the article's",
      ["[1] Rin Vale", "[2] Ada Ash", "[3] Bo Birch", "[4] Sam Roe", "[5] Alex B. Doe"].all
        (fun s => pageOccurs c 0 s == 1) && pageOccurs c 0 "References" == 1 &&
        hasStr (censusProse c) "Notes on placeholder text")])]

/-- The census rows in parts of at most `censusPartRows`, since a list literal's elaboration grows
faster than its rows. -/
def censusParts :
    List (List (String × (Layout.Geom → Array CensusPage → List (String × Bool)))) :=
  [censusRows0, censusRows1, censusRows2, censusRows3, censusRows4, censusRows5,
    censusRows6, censusRows7, censusMdRows, censusCodeRows]

def censusPartRows : Nat := 16

def censusTable :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) :=
  censusParts.flatten

/-- The outline tier of the census: a fixture whose layout ships a PDF outline owes a row asserting
it. -/
def censusOutlineTable :
    List (String × (Array Layout.OutlineEntry → List (String × Bool))) := [
  ("webnav", fun o => [
    ("one entry per menu link, in order",
      o.map (·.title) == #["First Light", "Gathered Notes", "Back to top"]),
    ("the section targets resolve to the page their headings land on",
      (o.filter (·.title != "Back to top")).all (·.page == some 0)),
    ("the #top target lands at the document's top, as no anchor claims it",
      (o.find? (·.title == "Back to top")).map
        (fun e => e.page == some 0 && e.fragment == some "top") == some true)]),
  ("nav-directory", fun o => [
    ("one entry per menu link, in order",
      o.map (·.title) == (Array.range 300).map fun i => s!"Entry {i + 1}"),
    ("every entry rides its own address, with no page",
      o.zipIdx.all fun (e, i) =>
        e.page.isNone && e.url == some s!"https://example.org/entries/{i + 1}")])]

/-- The phrase a corpus file writes in its own header to declare itself out of the golden set. -/
def corpusExcludeMarker : String := "excluded from the golden set"

/-- Whether a corpus file's opening lines, read as one run of prose, declare it out of the golden
set. -/
def declaresExcluded (text : String) : Bool :=
  let header := ((text.splitOn "\n").take 16).map fun line =>
    let l := line.trimAscii.toString
    if l.startsWith "%" then (l.drop 1).toString.trimAscii.toString else l
  hasStr (" ".intercalate header) corpusExcludeMarker

/-- The top-level files under `testdata/corpus` a surface reads: the entries a golden run could
draw from. -/
def corpusDocs : IO (Array String) := do
  let dir : System.FilePath := "testdata/corpus"
  let mut out := #[]
  for entry in (← dir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless (Ir.Surface.ofInput? entry).isSome do continue
    unless (← (dir / entry).isDir) do
      out := out.push entry
  return out

/-- `goldenNames` against the corpus directory, both ways: every fixture is golden or declares its
exclusion, and an excluded `.tex` still refuses to elaborate. -/
def corpusCoverageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let dir : System.FilePath := "testdata/corpus"
  for entry in ← corpusDocs do
    let some stem := (System.FilePath.mk entry).fileStem | continue
    let listed := goldenNames.contains stem
    let text ← IO.FS.readFile (dir / entry)
    let excluded := declaresExcluded text
    check ref s!"corpus {entry}: in the directory but not in the golden set, \
and its header does not say why not"
      (listed || excluded)
    check ref s!"corpus {entry}: declares itself out of the golden set yet is listed in it"
      (!(listed && excluded))
    if excluded && !listed && entry.endsWith ".tex" then
      let (_, diags) ← elabFixture stem text
      check ref s!"corpus {entry}: excuses itself from the golden set but now \
elaborates without complaint — promote it"
        (diags.any fun d =>
          d.severity == .error || d.code == "W0301" || d.code == "W0302")
  for n in goldenNames do
    check ref s!"golden {n}: in the golden set but no {goldenFile n}"
      (← System.FilePath.pathExists (goldenFile n))
  for n in mdGoldenNames do
    check ref s!"golden {n}: both {n}.md and {n}.tex exist, and the golden set reads only the .md"
      (!(← (dir / s!"{n}.tex").pathExists))

/-- No page of any golden fixture ships a LaTeX markup character as ink. -/
def inkMarkupChecks (ref : IO.Ref (List String)) (n : String)
    (c : Array CensusPage) : IO Unit := do
  let allowed := inkMarkupAllowed n
  let text := censusText c
  for ch in inkMarkupWatch do
    unless allowed.contains ch do
      check ref s!"census {n}: ships the markup character '{ch}' as ink"
        (!text.any (· == ch))

/-- Every golden fixture has a `censusTable` row whose facts hold on the pages the engine ships. -/
def censusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let mathSet ← mathSetOf oneFace
  for (part, i) in censusParts.zipIdx do
    check ref s!"census part {i} holds {part.length} rows, at most {censusPartRows}"
      (part.length ≤ censusPartRows)
  for n in goldenNames do
    check ref s!"census covers {n}" (censusTable.any (·.1 == n))
  for (n, _) in censusTable do
    check ref s!"census row {n} names a golden fixture" (goldenNames.contains n)
  -- A fixture reaching math without a declared face resolves it as the driver does.
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let mut seen := #[]
  for (n, facts) in censusTable do
    let (doc, diags) ← goldenDoc n
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    -- The census reads what the driver ships: images beside the fixture, figures in its faces.
    let store ← corpusStore doc (some fs)
    let out := (fittedOf fs doc geom (some pats) store).out
    let c := censusOf (coveredColorsOf doc) out store
    if mdGoldenNames.contains n then seen := seen.push (n, doc, out, c, diags)
    inkMarkupChecks ref n c
    for (label, ok) in facts geom c do
      check ref s!"census {n}: {label}" ok
    if !out.outline.isEmpty then
      check ref s!"census {n}: a shipped outline has its outline row"
        ((censusOutlineTable.lookup n).isSome)
    for (label, ok) in ((censusOutlineTable.lookup n).map (· out.outline)).getD [] do
      check ref s!"census {n} outline: {label}" ok
  silentLossChecks ref seen

/-- A resolved reference to a key inside a captioned float shows the number the numbered node
carries, over every golden fixture. -/
def floatRefAgreementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let labelsIn (body : Array Ir.Block) (caption : Array Ir.Inline) : Array String :=
    let fi := fun (out : Array String) (x : Ir.Inline) => match x with
      | .label k => out.push k
      | _ => out
    Ir.foldBlocks (fun out _ => out) fi (Ir.foldInlines fi #[] caption) body
  let floatsIn (body : Array Ir.Block) :
      Array (Ir.FloatKind × Option Nat × Array Ir.Block × Array Ir.Inline) :=
    Ir.foldBlocks (fun out b => match b with
      | .float kind num _ fbody fcaption => out.push (kind, num, fbody, fcaption)
      | _ => out) (fun out _ => out) #[] body
  for n in goldenNames do
    let (doc, _) ← goldenDoc n
    let refs := Ir.foldBlocks (fun out _ => out)
      (fun out x => match x with
        | .ref key form text _ => out.push (key, form, text)
        | _ => out) #[] doc.body
    for (kind, num, body, caption) in floatsIn doc.body do
      if kind != Ir.FloatKind.sub then
        if let some nnum := num then
          let nested := (floatsIn body).flatMap fun (_, _, nb, nc) => labelsIn nb nc
          let direct := (labelsIn body caption).filter (!nested.contains ·)
          for key in direct do
            for (k, form, text) in refs do
              if k == key then
                let expect := if form == Ir.RefForm.paren then s!"({nnum})"
                  else toString nnum
                check ref
                  s!"float ref agreement {n}: '{key}' resolves to the number its float carries"
                  (text == expect)
