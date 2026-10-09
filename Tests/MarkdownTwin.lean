module

public import Tests.Support

public section

open LeanTex.Core

/-! # The twin reads back

Each row is a spelling class the markdown twin once got wrong: a document
whose twin, read back through the markdown door, lost or changed what the
IR held. The assertion is over the twin's text and the IR it reads back to
— the twin is the artifact, and the door is how a reader meets it. The
`mdtwin` tier counts the same round trip over the CommonMark examples and
the corpus; these rows name the classes one by one. -/

namespace Tests.MarkdownTwin

/-- A document's twin, and what the twin reads back as. -/
def roundTrip (d : Ir.Doc) : String × Ir.Doc × Array Diag :=
  let tw := MarkdownDoc.emit d
  let (back, ds) := elabMd tw
  (tw, back, ds)

/-- The same from a tex body in the plain article. -/
def texRoundTrip (body : String) : String × Ir.Doc × Array Diag :=
  roundTrip (elabStr (dvDoc "" body)).1

/-- One paragraph of plain text, as the IR holds it. -/
def textDoc (s : String) : Ir.Doc := { body := #[.para #[.text s]] }

/-- Does the body read back as one paragraph whose text is `s`? -/
def oneParagraph (d : Ir.Doc) (s : String) : Bool :=
  match d.body.toList with
  | [.para xs] => Ir.plainText xs == s
  | _ => false

def hasError (ds : Array Diag) : Bool := ds.any (·.severity == .error)

/-- Inline spellings: escapes, code spans, links, runs. -/
def twinInlineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- A code span's content is not unescaped: `snake\_case` read back with
  -- its backslash.
  let (tw, back, _) := texRoundTrip "\\texttt{snake\\_case} sets"
  t s!"twin: a code span holds its text exactly ({repr tw})"
    (hasStr tw "`snake_case`" && oneParagraph back "snake_case sets")
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .mono #[.text "a `tick` and ``two``"]]] }
  t s!"twin: a code span outlasts the backtick runs inside it ({repr tw})"
    (oneParagraph back "a `tick` and ``two``")
  -- Raw HTML and character references are text in the IR, so text in the twin.
  for s in ["Literal <b>bold</b> stays text", "An &amp; entity stays text",
      "Both <br> and &lt;", "a&#10;b"] do
    let (tw, back, ds) := roundTrip (textDoc s)
    t s!"twin: {repr s} reads back as its text ({repr tw})"
      (oneParagraph back s && !hasError ds)
  -- A line ending inside text has one spelling, a numeric reference.
  let (tw, back, _) := roundTrip (textDoc "first\nsecond")
  t s!"twin: a line ending in text reads back as one ({repr tw})"
    (oneParagraph back "first\nsecond")
  -- A link whose text is its plain destination is an autolink; a
  -- destination reads back exactly.
  let (tw, back, _) := texRoundTrip "\\href{http://example.org/x}{http://example.org/x}"
  t s!"twin: a bare link is an autolink ({repr tw})"
    (hasStr tw "<http://example.org/x>" &&
      back.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .link url _ => url == "http://example.org/x"
          | _ => false
        | _ => false)
  -- A code-set link keeps its destination and its face, whichever of the
  -- two the IR holds outside: a code span holds no link, so the code goes
  -- inside it.
  for (src, url, text) in [("\\url{http://example.org/u}", "http://example.org/u",
        "http://example.org/u"),
      ("\\texttt{see \\href{http://example.org/m}{name}}", "http://example.org/m", "name")] do
    let (tw, back, _) := texRoundTrip src
    t s!"twin: {repr src} keeps its destination and its code face ({repr tw})"
      (hasStr tw ("[`" ++ text ++ "`](" ++ url ++ ")") &&
        back.body.any fun b => match b with
          | .para xs => xs.any fun x => match x with
            | .link u body => u == url && hasStr (MarkdownDoc.inlineText body) ("`" ++ text ++ "`")
            | _ => false
          | _ => false)
  for url in ["http://example.org/a(b)c", "http://example.org/a b", "pic\\name.png"] do
    let (tw, back, _) := roundTrip { body := #[.para #[.link url #[.text "words"]]] }
    t s!"twin: the destination {repr url} reads back exactly ({repr tw})"
      (back.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .link u _ => u == url
          | _ => false
        | _ => false)
  -- Adjacent runs of one style are one run.
  let (tw, back, _) := texRoundTrip "\\textbf{a}\\textbf{b} after"
  t s!"twin: adjacent bold runs are one run ({repr tw})"
    (hasStr tw "**ab**" && oneParagraph back "ab after")
  -- A run's own spaces stand outside its delimiters.
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .bold #[.text "Alex Doe "],
    .text "next"]] }
  t s!"twin: a run's trailing space stands outside it ({repr tw})"
    (hasStr tw "**Alex Doe** next" && oneParagraph back "Alex Doe next")
  -- A heading's trailing hash is its text, not its closing sequence.
  let (tw, back, _) := roundTrip { body := #[.section 1 true none #[.text "Issue #"]] }
  t s!"twin: a heading keeps its trailing hash ({repr tw})"
    (back.body.any fun b => match b with
      | .section _ _ _ xs => Ir.plainText xs == "Issue #"
      | _ => false)

/-- Block spellings: line starts, fences, containers, lists. -/
def twinBlockChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- A paragraph that opens like a block, at its start or after a hard break.
  -- Backtick runs and doubled dashes are left out: the reader sets them as
  -- quotes and dashes whatever their escapes, a dialect decision pending,
  -- so no spelling of them reads back as written.
  for s in ["1. Not a list", "# Not a heading", "+ Not a bullet", "- Not a bullet",
      "> Not a quote", "3) Not a list", "~~~ not a fence", "***", "===", "* * *",
      "- - -", "12. twelve", "  indented words"] do
    let (tw, back, _) := roundTrip (textDoc s)
    t s!"twin: a paragraph {repr s} stays a paragraph ({repr tw})"
      (oneParagraph back s.trimAsciiStart.toString)
    let (tw, back, _) := roundTrip { body := #[.para #[.text "Before", .linebreak default, .text s]] }
    t s!"twin: a line {repr s} after a hard break stays in its paragraph ({repr tw})"
      (match back.body.toList with
        | [.para _] => true
        | _ => false)
  -- A hard break before a line of `=` is no setext underline.
  let (tw, back, _) := texRoundTrip "A \\\\\n====="
  t s!"twin: a hard break before ===== makes no heading ({repr tw})"
    (!back.body.any (· matches .section ..))
  -- A listing holding a fence keeps it as content.
  let listing := "x\n```\ny"
  let (tw, back, _) := texRoundTrip ("\\begin{verbatim}\n" ++ listing ++ "\n\\end{verbatim}")
  t s!"twin: a listing holding ``` keeps it ({repr tw})"
    (back.body.any fun b => match b with
      | .verbatim _ s _ => (Ir.verbatimLines s).toList == ["x", "```", "y"]
      | _ => false)
  -- A listing's blank lines are its content, two in a row as one, at the
  -- top level and under a container.
  let spaced := "def a():\n    pass\n\n\ndef b():\n    pass"
  for (where_, wrap) in [("at the top level", fun (b : Ir.Block) => #[b]),
      ("in a quotation", fun b => #[.quote #[b]]),
      ("in a list item", fun b => #[.list false #[#[.para #[.text "item"], b]]])] do
    let (tw, back, _) := roundTrip { body := wrap (.verbatim none spaced {}) }
    let found := (back.body.map fun b => match b with
      | .verbatim _ s _ => #[s]
      | .quote body => body.filterMap fun b => match b with
        | .verbatim _ s _ => some s
        | _ => none
      | .list _ items => items.flatMap fun it => it.filterMap fun b => match b with
        | .verbatim _ s _ => some s
        | _ => none
      | _ => #[]).flatten
    t s!"twin: a listing's two blank lines in a row survive {where_} ({repr tw})"
      (found.any fun s => (Ir.verbatimLines s).toList == (Ir.verbatimLines spaced).toList)
  -- A code block inside a quotation and inside a list item stays inside.
  let (tw, back, _) := texRoundTrip
    "\\begin{quote}\n\\begin{verbatim}\ncode in quote\n\\end{verbatim}\n\\end{quote}"
  t s!"twin: a code block in a quotation stays in it ({repr tw})"
    (back.body.any fun b => match b with
      | .quote body => body.any (· matches .verbatim ..)
      | _ => false)
  let (tw, back, ds) := texRoundTrip
    "\\begin{itemize}\\item a\n\\begin{verbatim}\ncode in item\n\\end{verbatim}\n\\end{itemize}"
  t s!"twin: a code block in a list item stays in it ({repr tw})"
    (!hasError ds && back.body.any fun b => match b with
      | .list _ items => items.any (·.any (· matches .verbatim ..))
      | _ => false)
  -- A nested list under an ordered item stays under it.
  let (tw, back, _) := texRoundTrip
    "\\begin{enumerate}\\item a\n\\begin{itemize}\\item b\\end{itemize}\\end{enumerate}"
  t s!"twin: a bullet list nested in an ordered item stays nested ({repr tw})"
    (match back.body.toList with
      | [.list true items] => items.size == 1 && items.any fun it =>
          it.any fun b => (b matches .list false _) || (match b with
            | .role _ body => body.any (· matches .list false _)
            | _ => false)
      | _ => false)
  -- Two paragraphs of one item are two paragraphs.
  let (tw, back, _) := roundTrip { body := #[.list false #[#[.para #[.text "one"],
    .para #[.text "two"]]]] }
  t s!"twin: an item's two paragraphs stay two ({repr tw})"
    (match back.body.toList with
      | [.list false items] => items.any fun it => (it.filter (· matches .para _)).size == 2
      | _ => false)
  -- Two lists side by side stay two lists.
  let (tw, back, _) := roundTrip { body := #[.list false #[#[.para #[.text "a"]]],
    .list false #[#[.para #[.text "b"]]]] }
  t s!"twin: two adjacent lists stay two ({repr tw})"
    ((back.body.filter (· matches .list ..)).size == 2)
  -- Two lists side by side inside an item stay two, and neither they nor a
  -- list closing an item make the list holding them loose.
  let inner (x : String) : Ir.Block := .list false #[#[.para #[.text x]]]
  for (what, doc) in [("two lists in one item",
        ({ body := #[.list false #[#[.para #[.text "first"], inner "a", inner "b"]]] } : Ir.Doc)),
      ("a list closing an item", { body := #[.list false #[#[.para #[.text "first"], inner "a"],
        #[.para #[.text "second"]]]] })] do
    let (tw, back, ds) := roundTrip doc
    t s!"twin: {what} reads back as written and tight ({repr tw})"
      (back.body == doc.body && !ds.any (·.subject == some "md:loose-list"))
  -- A wrapper the twin writes as its body — a resolved step, a role — is
  -- opened inside an item, so the item's paragraph and the list nested under
  -- it stay tight; and a first block that writes nothing leaves the marker to
  -- the next one, which would otherwise stand after an empty item.
  for (what, doc, want) in [
      ("a stepped item's paragraph and its nested list",
        ({ body := #[.list false #[#[.onSteps { first := 2, last := none } #[.para #[.text "first"],
          .role "in-paragraph" #[inner "a"]]]]] } : Ir.Doc),
        #[Ir.Block.list false #[#[.para #[.text "first"], inner "a"]]]),
      ("an item opening with a note",
        { body := #[.list false #[#[.note #[.para #[.text "aside"]], .para #[.text "x"]]]] },
        #[Ir.Block.list false #[#[.para #[.text "x"]]]])] do
    let (tw, back, ds) := roundTrip doc
    t s!"twin: {what} reads back tight, its blocks at the item's level ({repr tw})"
      (back.body == want && !ds.any (·.subject == some "md:loose-list") &&
        MarkdownDoc.emit back == tw)
  -- An empty quotation is still there.
  let (tw, back, _) := roundTrip { body := #[.quote #[]] }
  t s!"twin: an empty quotation reads back ({repr tw})"
    (back.body.any (· matches .quote _))
  -- The corpus list fixture's twin reads back with no refusal.
  let path := "testdata/corpus/lists.tex"
  let (doc, _) ← elabInputSrc path (← IO.FS.readFile path)
  let (tw, _, ds) := roundTrip doc
  t s!"twin: the list fixture's twin reads back unrefused ({(ds.filter (·.severity == .error)).map (·.subject)})"
    (!hasError ds && !tw.isEmpty)

/-- The reader half of `MarkdownDoc.escapeLineStart_contract`: what the
model says opens no block, the markdown door reads as one paragraph of the
line's own text. -/
def twinLineStartChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Backtick fences and doubled dashes are the writer's alone to hold
  -- (the theorem): the reader sets them as quotes and dashes whatever their
  -- escapes, a dialect decision pending, so they cannot be read back.
  let openers := ["#", "##", "######", "-", "+", "*", ">", "~~~", "===", "***",
    "* * *", "- - -", "1.", "1)", "123.", "9)", "=", "_ _ _"]
  let follow := ["", " word", "\tword", "  two words"]
  let lead := ["", " ", "   "]
  let mut n := 0
  for o in openers do
    for f in follow do
      for l in lead do
        let line := l ++ o ++ f
        let written := MarkdownDoc.escapeLineStart line
        let (back, _) := elabMd (written ++ "\n")
        -- the reader collapses a run of spaces, as it does in any paragraph
        let squeeze (s : String) : String :=
          " ".intercalate (((s.replace "\t" " ").splitOn " ").filter (!·.isEmpty))
        unless (match back.body.toList with
             | [.para xs] => squeeze (Ir.plainText xs) == squeeze line
             | _ => false) do
          t s!"twin: the line {repr line}, written {repr written}, reads back as itself" false
        n := n + 1
  t s!"twin: {n} generated lines checked" (n == openers.length * follow.length * lead.length)

/-- The tables of a document, every row of each, in document order. -/
def tableRows (d : Ir.Doc) : Array (Array (Array Ir.Inline)) :=
  Ir.foldBlocks (fun acc b => match b with
    | .table _ _ _ rows _ _ => acc ++ rows
    | _ => acc) (fun acc _ => acc) #[] d.body

/-- A pipe table's rows as the twin writes them: its lines that open with a
pipe, the delimiter row left out. -/
def twinRows (tw : String) : List String :=
  match (tw.splitOn "\n").filter (·.startsWith "|") with
  | first :: _ :: rest => first :: rest
  | rows => rows

/-- Table cells: the row GFM reads (`MarkdownDoc.gfmRow`) holds one cell per
cell the IR holds, each reading back through the markdown door as the
cell's own text — a pipe in code, in text, in a destination or in a formula
opens no cell, and a hard break stays on the row's line. -/
def twinTableChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\begin{tabular}{lll}\n\\texttt{a|b} & c|d & \\texttt{x || y}\\\\\n" ++
    "\\texttt{p\\textbackslash{}|q} & \\href{http://example.org/a|b}{e} & $|x|$\\\\\n" ++
    "\\texttt{|lead} & r & \\texttt{end|}\n\\end{tabular}"
  -- the hard break a wrapping cell can hold, set in the IR: the tabular's
  -- `\\\\` ends its row
  let broken : Array Ir.Inline := #[.text "r", .linebreak default, .text "s"]
  let doc := { (elabStr (dvDoc "" src)).1 with
    body := (elabStr (dvDoc "" src)).1.body.map fun b => match b with
      | .table cols pl pr rows rules spans =>
        .table cols pl pr (rows.modify 2 (·.set! 1 broken)) rules spans
      | b => b }
  let tw := MarkdownDoc.emit doc
  let rows := tableRows doc
  let lines := twinRows tw
  t s!"twin: a table's rows are its lines ({lines.length} of {rows.size}; {repr tw})"
    (lines.length == rows.size && rows.size == 3)
  for (line, row) in lines.zip rows.toList do
    let cells := MarkdownDoc.gfmRow line
    t s!"twin: the row {repr line} reads as {row.size} cells ({repr cells})"
      (cells.length == row.size)
    for (cell, ir) in cells.zip row.toList do
      -- a formula's source is the twin's spelling, which the door reads
      -- as text: its pipes are held by the cell count above
      unless ir.any (· matches .math .. | .formula ..) do
        let (back, _) := elabMd (cell ++ "\n")
        let want := (Ir.plainText ir).replace "\n" " "
        t s!"twin: the cell {repr cell} reads back as {repr want}"
          (match back.body.toList with
            | [.para xs] => Ir.plainText xs == want
            | [] => want.isEmpty
            | _ => false)
  t s!"twin: a cell's destination keeps its pipe ({repr tw})"
    (hasStr tw "[e](http://example.org/a\\|b)")

/-- Headings: a hard break in a title has no spelling on a heading's line,
so it is written as a space, and the heading reads back as one heading. -/
def twinHeadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (src, title) in [("\\section{Alder\\\\ Birch}", "1 Alder Birch"),
      ("\\section*{Cedar\\\\ Dogwood}", "Cedar Dogwood")] do
    let (tw, back, _) := texRoundTrip src
    t s!"twin: a heading with a hard break stays one heading ({repr tw})"
      (match back.body.toList with
        | [.section _ _ _ xs] => Ir.plainText xs == title
        | _ => false)
  let (doc, _) := elabStr (dvDeck "" "\\begin{frame}{Elm\\\\ Fir}\nGrove\n\\end{frame}")
  let tw := MarkdownDoc.emit doc
  let (back, _) := elabMd tw
  t s!"twin: a frame title with a hard break stays one heading ({repr tw})"
    (hasStr tw "## Elm Fir\n" && back.body.any fun b => match b with
      | .section _ _ _ xs => Ir.plainText xs == "Elm Fir"
      | _ => false)

def markdownTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  twinInlineChecks ref
  twinBlockChecks ref
  twinLineStartChecks ref
  twinTableChecks ref
  twinHeadingChecks ref

end Tests.MarkdownTwin
