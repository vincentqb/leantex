module

public import Tests.Support

public section

open LeanTex.Core

/-! The markdown twin reads back, through the markdown door, to the IR it was written from. -/

namespace Tests.MarkdownTwin

/-- A document's twin, and what the twin reads back as. -/
def roundTrip (d : Ir.Doc) : String × Ir.Doc × Array Diag :=
  let tw := MarkdownDoc.emit d
  let (back, ds) := elabMd tw
  (tw, back, ds)

/-- The same from a tex body in the plain article. -/
def texRoundTrip (body : String) : String × Ir.Doc × Array Diag :=
  roundTrip (elabStr (dvDoc "" body)).1

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
  let (tw, back, _) := texRoundTrip "\\texttt{snake\\_case} sets"
  t s!"twin: a code span holds its text exactly ({repr tw})"
    (hasStr tw "`snake_case`" && oneParagraph back "snake_case sets")
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .mono #[.text "a `tick` and ``two``"]]] }
  t s!"twin: a code span outlasts the backtick runs inside it ({repr tw})"
    (oneParagraph back "a `tick` and ``two``")
  for s in ["Literal <b>bold</b> stays text", "An &amp; entity stays text",
      "Both <br> and &lt;", "a&#10;b"] do
    let (tw, back, ds) := roundTrip (textDoc s)
    t s!"twin: {repr s} reads back as its text ({repr tw})"
      (oneParagraph back s && !hasError ds)
  let (tw, back, _) := roundTrip (textDoc "first\nsecond")
  t s!"twin: a line ending in text reads back as one ({repr tw})"
    (oneParagraph back "first\nsecond")
  let (tw, back, _) := texRoundTrip "\\href{http://example.org/x}{http://example.org/x}"
  t s!"twin: a bare link is an autolink ({repr tw})"
    (hasStr tw "<http://example.org/x>" &&
      back.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .link url _ => url == "http://example.org/x"
          | _ => false
        | _ => false)
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
  let (tw, back, _) := texRoundTrip "\\textbf{a}\\textbf{b} after"
  t s!"twin: adjacent bold runs are one run ({repr tw})"
    (hasStr tw "**ab**" && oneParagraph back "ab after")
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .bold #[.text "Alex Doe "],
    .text "next"]] }
  t s!"twin: a run's trailing space stands outside it ({repr tw})"
    (hasStr tw "**Alex Doe** next" && oneParagraph back "Alex Doe next")
  let (tw, back, _) := roundTrip { body := #[.section 1 true none #[.text "Issue #"]] }
  t s!"twin: a heading keeps its trailing hash ({repr tw})"
    (back.body.any fun b => match b with
      | .section _ _ _ xs => Ir.plainText xs == "Issue #"
      | _ => false)

/-- Block spellings: line starts, fences, containers, lists. -/
def twinBlockChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Backtick runs and doubled dashes are left out: the reader sets them as quotes and dashes.
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
  let (tw, back, _) := texRoundTrip "A \\\\\n====="
  t s!"twin: a hard break before ===== makes no heading ({repr tw})"
    (!back.body.any (· matches .section ..))
  let listing := "x\n```\ny"
  let (tw, back, _) := texRoundTrip ("\\begin{verbatim}\n" ++ listing ++ "\n\\end{verbatim}")
  t s!"twin: a listing holding ``` keeps it ({repr tw})"
    (back.body.any fun b => match b with
      | .verbatim _ s _ => (Ir.verbatimLines s).toList == ["x", "```", "y"]
      | _ => false)
  let spaced := "def a():\n    pass\n\n\ndef b():\n    pass"
  for (where_, wrap) in [("at the top level", fun (b : Ir.Block) => #[b]),
      ("in a quotation", fun b => #[.quote ⟨.quote, {}⟩ #[b]]),
      ("in a list item", fun b => #[.list false {} #[#[.para #[.text "item"], b]]])] do
    let (tw, back, _) := roundTrip { body := wrap (.verbatim none spaced {}) }
    let found := (back.body.map fun b => match b with
      | .verbatim _ s _ => #[s]
      | .quote _ body => body.filterMap fun b => match b with
        | .verbatim _ s _ => some s
        | _ => none
      | .list _ _ items => items.flatMap fun it => it.filterMap fun b => match b with
        | .verbatim _ s _ => some s
        | _ => none
      | _ => #[]).flatten
    t s!"twin: a listing's two blank lines in a row survive {where_} ({repr tw})"
      (found.any fun s => (Ir.verbatimLines s).toList == (Ir.verbatimLines spaced).toList)
  let (tw, back, _) := texRoundTrip
    "\\begin{quote}\n\\begin{verbatim}\ncode in quote\n\\end{verbatim}\n\\end{quote}"
  t s!"twin: a code block in a quotation stays in it ({repr tw})"
    (back.body.any fun b => match b with
      | .quote _ body => body.any (· matches .verbatim ..)
      | _ => false)
  let (tw, back, ds) := texRoundTrip
    "\\begin{itemize}\\item a\n\\begin{verbatim}\ncode in item\n\\end{verbatim}\n\\end{itemize}"
  t s!"twin: a code block in a list item stays in it ({repr tw})"
    (!hasError ds && back.body.any fun b => match b with
      | .list _ _ items => items.any (·.any (· matches .verbatim ..))
      | _ => false)
  let (tw, back, _) := texRoundTrip
    "\\begin{enumerate}\\item a\n\\begin{itemize}\\item b\\end{itemize}\\end{enumerate}"
  t s!"twin: a bullet list nested in an ordered item stays nested ({repr tw})"
    (match back.body.toList with
      | [.list true _ items] => items.size == 1 && items.any fun it =>
          it.any fun b => (b matches .list false _ _) || (match b with
            | .role _ body => body.any (· matches .list false _ _)
            | _ => false)
      | _ => false)
  let (tw, back, _) := roundTrip { body := #[.list false {} #[#[.para #[.text "one"],
    .para #[.text "two"]]]] }
  t s!"twin: an item's two paragraphs stay two ({repr tw})"
    (match back.body.toList with
      | [.list false _ items] => items.any fun it => (it.filter (· matches .para _)).size == 2
      | _ => false)
  let (tw, back, _) := roundTrip { body := #[.list false {} #[#[.para #[.text "a"]]],
    .list false {} #[#[.para #[.text "b"]]]] }
  t s!"twin: two adjacent lists stay two ({repr tw})"
    ((back.body.filter (· matches .list ..)).size == 2)
  let inner (x : String) : Ir.Block := .list false {} #[#[.para #[.text x]]]
  for (what, doc) in [("two lists in one item",
        ({ body := #[.list false {} #[#[.para #[.text "first"], inner "a", inner "b"]]] } : Ir.Doc)),
      ("a list closing an item", { body := #[.list false {} #[#[.para #[.text "first"], inner "a"],
        #[.para #[.text "second"]]]] })] do
    let (tw, back, ds) := roundTrip doc
    t s!"twin: {what} reads back as written and tight ({repr tw})"
      (back.body == doc.body && !ds.any (·.subject == some "md:loose-list"))
  for (what, doc, want) in [
      ("a stepped item's paragraph and its nested list",
        ({ body := #[.list false {} #[#[.onSteps { first := 2, last := none } #[.para #[.text "first"],
          .role "in-paragraph" #[inner "a"]]]]] } : Ir.Doc),
        #[Ir.Block.list false {} #[#[.para #[.text "first"], inner "a"]]]),
      ("an item opening with a note",
        { body := #[.list false {} #[#[.note #[.para #[.text "aside"]], .para #[.text "x"]]]] },
        #[Ir.Block.list false {} #[#[.para #[.text "x"]]]])] do
    let (tw, back, ds) := roundTrip doc
    t s!"twin: {what} reads back tight, its blocks at the item's level ({repr tw})"
      (back.body == want && !ds.any (·.subject == some "md:loose-list") &&
        MarkdownDoc.emit back == tw)
  let (tw, back, _) := roundTrip { body := #[.quote ⟨.quote, {}⟩ #[]] }
  t s!"twin: an empty quotation reads back ({repr tw})"
    (back.body.any (· matches .quote ..))
  let path := "testdata/corpus/lists.tex"
  let (doc, _) ← elabInputSrc path (← fixtureText path)
  let (tw, _, ds) := roundTrip doc
  t s!"twin: the list fixture's twin reads back unrefused ({(ds.filter (·.severity == .error)).map (·.subject)})"
    (!hasError ds && !tw.isEmpty)

/-- The reader half of `MarkdownDoc.escapeLineStart_contract`: what the model says opens no block
reads back as one paragraph. -/
def twinLineStartChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Backtick fences and doubled dashes are the writer's alone to hold; the reader cannot read them back.
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
    | .table _ _ _ rows _ _ => acc ++ rows.map (·.map Ir.cellLine)
    | _ => acc) (fun acc _ => acc) #[] d.body

/-- A pipe table's rows as the twin writes them, delimiter row left out. -/
def twinRows (tw : String) : List String :=
  match (tw.splitOn "\n").filter (·.startsWith "|") with
  | first :: _ :: rest => first :: rest
  | rows => rows

/-- Table cells: each GFM row (`MarkdownDoc.gfmRow`) holds one cell per IR cell, each reading back
as its own text. -/
def twinTableChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := "\\begin{tabular}{lll}\n\\texttt{a|b} & c|d & \\texttt{x || y}\\\\\n" ++
    "\\texttt{p\\textbackslash{}|q} & \\href{http://example.org/a|b}{e} & $|x|$\\\\\n" ++
    "\\texttt{|lead} & r & \\texttt{end|}\n\\end{tabular}"
  -- the hard break a wrapping cell holds is set in the IR: a tabular's `\\\\` ends its row
  let broken : Array Ir.Inline := #[.text "r", .linebreak default, .text "s"]
  let doc := { (elabStr (dvDoc "" src)).1 with
    body := (elabStr (dvDoc "" src)).1.body.map fun b => match b with
      | .table cols pl pr rows rules spans =>
        .table cols pl pr (rows.modify 2 (·.set! 1 (Ir.cellOf broken))) rules spans
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
      -- a formula's source is the twin's spelling, read back as text; the cell count holds its pipes
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

/-- Headings: a break on a heading's line is written `<br>`, and the heading reads back as one
heading holding it. -/
def twinHeadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (src, title) in [("\\section{Alder\\\\ Birch}", "1 Alder Birch"),
      ("\\section*{Cedar\\\\ Dogwood}", "Cedar Dogwood")] do
    let (tw, back, _) := texRoundTrip src
    t s!"twin: a heading with a hard break stays one heading, its break kept ({repr tw})"
      (match back.body.toList with
        | [.section _ _ _ xs] => Ir.plainText xs == title && xs.any (· matches .linebreak _)
        | _ => false)
  let (doc, _) := elabStr (dvDeck "" "\\begin{frame}{Elm\\\\ Fir}\nGrove\n\\end{frame}")
  let tw := MarkdownDoc.emit doc
  let (back, _) := elabMd tw
  t s!"twin: a frame title with a hard break stays one heading, its break kept ({repr tw})"
    (hasStr tw "## Elm<br>Fir\n" && back.body.any fun b => match b with
      | .section _ _ _ xs => Ir.plainText xs == "Elm Fir" && xs.any (· matches .linebreak _)
      | _ => false)

/-- The llms.txt head: title and summary are written as text, read back as their own characters, and
break no line. -/
def twinHeadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (ttl, summ) in [("Tips <and> & *stars* for C_x #", "- a bullet, # a hash, <b> and * stars"),
      ("1. Numbered <title>", "> quoted &amp; text"), ("Two\nlines", "Also\ntwo")] do
    let info : Ir.Meta := { title := some ttl, subject := some summ }
    let doc : Ir.Doc := { body := #[.para #[.text "Body."]], info }
    let (tw, back, ds) := roundTrip doc
    t s!"twin: the metadata title {repr ttl} and summary {repr summ} read back ({repr tw})"
      (!hasError ds && match back.body.toList with
        | [.section _ _ _ xs, .quote _ qs, .para _] =>
          Ir.plainText xs == ttl && (match qs.toList with
            | [.para ys] => Ir.plainText ys == summ
            | _ => false)
        | _ => false)

/-- A tex body's document as the driver elaborates one, source locations kept. -/
def driverDoc (body : String) : Ir.Doc :=
  let src := dvDoc "" body
  (Elab.runPrepared "t.tex" (Elab.prepare "t.tex" (Surface.read .tex "t.tex" src).1)).1

/-- The twin the driver ships, from a document with source locations, is the twin written with them
erased. -/
def twinDriverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for body in ["\\href{http://example.org/x}{http://example.org/x} and \\url{http://example.org/u}",
      "\\textbf{a}\\textbf{b} after \\emph{c} \\texttt{d|e}",
      "\\begin{itemize}\\item one\n\\item two \\textbf{bold}\\end{itemize}",
      "\\section{Head \\# }\nText.\\footnote{A note.}"] do
    let shipped := MarkdownDoc.emit (driverDoc body)
    let measured := MarkdownDoc.emit (elabStr (dvDoc "" body)).1
    t s!"twin: the driver's twin of {repr body} is the measured one ({repr shipped} vs {repr measured})"
      (shipped == measured)
  t "twin: the driver's twin writes a bare link as an autolink"
    (hasStr (MarkdownDoc.emit (driverDoc "\\href{http://example.org/x}{http://example.org/x}"))
      "<http://example.org/x>")

/-- Edge spellings: trailing heading `#`, padded block titles, footnote hard breaks, runs ending in
a tab or break, and reference markers. -/
def twinEdgeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (tw, back, _) := roundTrip { body := #[.section 1 true none #[.text "Issue # "]] }
  t s!"twin: a heading's hash before trailing space is its text ({repr tw})"
    (back.body.any fun b => match b with
      | .section _ _ _ xs => Ir.plainText xs == "Issue #"
      | _ => false)
  let (tw, back, _) := roundTrip { body := #[.titled .block #[.text " Edge title "]
    #[.para #[.text "Inside."]]] }
  t s!"twin: a titled block's title with spaces at its ends is bold ({repr tw})"
    (hasStr tw "**Edge title**" && back.body.any fun b => match b with
      | .para xs => xs.any fun x => match x with
        | .styled .bold ys => Ir.plainText ys == "Edge title"
        | _ => false
      | _ => false)
  let doc : Ir.Doc := { body := #[.para #[.text "Text", .footnote (some 1)
    #[.text "Note", .linebreak default, .text "# not a heading"]]] }
  let tw := MarkdownDoc.emit doc
  t s!"twin: a footnote's lines stay its own ({repr tw})"
    (hasStr tw "[^1]: Note\\\n    \\# not a heading")
  -- A run's delimiters stand clear of white space and a hard break, beside which they neither open nor close.
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .bold #[.text "Alder\t"],
    .text "Birch"]] }
  t s!"twin: a run's closing tab stands outside it ({repr tw})"
    (hasStr tw "**Alder**\tBirch" && back.body.any fun b => match b with
      | .para xs => xs.any fun x => match x with
        | .styled .bold ys => Ir.plainText ys == "Alder"
        | _ => false
      | _ => false)
  let (tw, back, _) := roundTrip { body := #[.para #[.styled .bold #[.text "Cedar",
    .linebreak default], .text "Dogwood"]] }
  t s!"twin: a run's closing hard break stands outside it ({repr tw})"
    (hasStr tw "**Cedar**\\\nDogwood" && back.body.any fun b => match b with
      | .para xs => xs.any fun x => match x with
        | .styled .bold ys => Ir.plainText ys == "Cedar"
        | _ => false
      | _ => false)
  -- A list the twin declares reads back from its bibliography; one it cannot, as its entries.
  let markers (d : Ir.Doc) : Array (String × Option String) := Ir.foldBlocks (fun out b =>
    match b with
    | .bibliography _ _ items => out ++ items.map fun it => (it.key, it.marker)
    | _ => out) (fun out _ => out) #[] d.body
  let (d, _) ← elabFixture "bibliography" (← fixtureText "testdata/corpus/bibliography.tex")
  let tw := MarkdownDoc.emit d
  let (back, _) := mdBibBuild tw (← corpusBibs d)
  t s!"twin: a declared reference list's markers read back from its bibliography ({repr tw})"
    (hasStr tw "::: {#refs}" && !(markers d).isEmpty && markers back == markers d)
  let (own, _) := bibBuild (dvDoc "" "See \\cite{a}.\n\n\\begin{thebibliography}{9}\n\\bibitem{a} \
Ada Ash. Alpha Notes.\n\\end{thebibliography}") #[]
  let tw := MarkdownDoc.emit own
  let (back, _) := elabMd tw
  t s!"twin: a reference list it cannot declare reads back as its entries, each anchored ({repr tw})"
    (hasStr tw "<a name=\"ref-a\"></a>\\[1\\] Ada Ash" && hasStr tw "(#ref-a)" &&
      MarkdownDoc.emit back == tw)

/-- A disclosure's twin is the element its reader reads back, in a document, a quotation and a list
item. -/
def twinDisclosureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let inner := "\n<summary>Q&amp;A &lt;now></summary>\n\nAlder.\n\n- Birch\n\n\
<details>\n<summary>Inner</summary>\n\nCedar.\n\n</details>\n\n</details>\n"
  for (opener, label) in [("<details>", "closed"), ("<details open>", "open")] do
    let (doc, ds0) := elabMd (opener ++ inner)
    let (tw, back, ds) := roundTrip doc
    t s!"twin: a {label} disclosure reads back to itself ({repr tw})"
      (ds0.isEmpty && back.body == doc.body && ds.isEmpty && MarkdownDoc.emit back == tw)
    t s!"twin: a {label} disclosure keeps its tag and its summary's references ({repr tw})"
      (tw.startsWith (opener ++ "\n<summary>Q&amp;A &lt;now></summary>\n"))
  let (brDoc, _) := elabMd "<details>\n<summary>Alder&#10;Birch&#13;Cedar&#12;Delta</summary>\n\nEcho.\n\n</details>\n"
  let (brTw, brBack, _) := roundTrip brDoc
  t s!"twin: a summary's referenced white space reads as a space and back ({repr brTw})"
    (brBack.body == brDoc.body && hasStr brTw "<summary>Alder Birch Cedar Delta</summary>")
  for (src, loose) in [("> <details>\n> <summary>Elm</summary>\n>\n> Fir.\n> </details>\n", false),
      ("- <details>\n  <summary>Elm</summary>\n\n  Fir.\n  </details>\n- Gorse\n", true),
      ("- <details>\n  <summary>Elm</summary>\n\n  - Alder\n  </details>\n- Gorse\n", true),
      ("- <details>\n  <summary>Elm</summary>\n\n  1. Alder\n  </details>\n- Gorse\n", true),
      ("- <details>\n  <summary>Elm</summary>\n\n  > Alder\n  </details>\n- Gorse\n", true),
      ("- > <details>\n  > <summary>Elm</summary>\n  >\n  > Fir.\n  > </details>\n- Gorse\n", false)] do
    let (doc, ds0) := elabMd src
    let (tw, back, ds) := roundTrip doc
    let named (xs : Array Diag) : Bool :=
      if loose then xs.size == 1 && xs.all (·.subject == some "md:loose-list") else xs.isEmpty
    t s!"twin: a contained disclosure reads back to itself, a loosened list named ({repr tw}: {ds0.map (·.subject)} then {ds.map (·.subject)})"
      (named ds0 && back.body == doc.body && named ds)

/-- A laid-out paragraph is one paragraph of hard-broken lines, each after the first opening on its
indent, and reads back as that paragraph: its lines' text kept, a long line's wrap no longer at its
indent the loss. -/
def twinLinesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc : Ir.Doc := { body := #[.lines #[{ depth := 0, content := #[.text "If"] },
    { depth := 1, content := #[.text "for every n, n is 0,"] },
    { depth := 2, content := #[.text "deeper"] }, { depth := 0, content := #[.text "then False."] }]] }
  let (tw, back, ds) := roundTrip doc
  let step := "\u2003\u2002"
  t s!"twin: a laid-out paragraph is one paragraph, each line after a hard break and its indent ({repr tw})"
    (hasStr tw ("If\\\n" ++ step ++ "for every n, n is 0,\\\n" ++ step ++ step ++ "deeper\\\n" ++
      "then False.\n"))
  t s!"twin: a laid-out paragraph reads back as one paragraph of its lines, indents kept as text ({repr back.body})"
    ((match back.body.toList with
      | [.para xs] => Ir.plainText xs ==
        "If " ++ step ++ "for every n, n is 0, " ++ step ++ step ++ "deeper then False."
      | _ => false) && !hasError ds && MarkdownDoc.emit back == tw)

/-- The markdown door reads the twin's escaped text as itself, up to what `Text.norm` reads alike,
and markup as markup, as `MarkdownDoc.escape_read_id`'s model does. -/
def twinEscapeReadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let special := "\\`*_[]<>&@|!#$%^~{}()-+.:;=?/\"' \t\n".toList
  let edges := ["see...@kqzv", "a.@kqzv", "-@kqzv", "x -@kqzv", "a@kqzv", "@{kqzv}", "[@kqzv]",
    "@kqzv@wxyb", "(@kqzv)", "a\n@kqzv", "@*"]
  let samples := (special.map ([·]) ++ special.flatMap fun a => special.map fun b => [a, b]).map
    String.ofList ++ edges
  -- smart punctuation respells these, and the door folds white space runs
  let typographic (s : String) := s.any fun c => "'\"-.`".toList.contains c
  let spaced (s : String) := hasStr s "  " || s.any (· == '\t') || hasStr s " \n" ||
    hasStr s "\n "
  for (front, ats) in [("", false), (worksMeta, true)] do
    let texts := samples.map fun s => "Kqzv " ++ s ++ "x Kqzv"
    let escaped := texts.map fun s => MarkdownDoc.escapeChars true ats s.toList
    let src := front ++ "\n\n".intercalate (escaped.map String.ofList) ++ "\n"
    let paras := (elabMd src).1.body.toList.filterMap fun b => match b with
      | .para xs => some xs
      | _ => none
    let cites (xs : Array Ir.Inline) := Ir.foldInlines (fun n x => match x with
      | .cite .. | .cited .. => n + 1
      | _ => n) 0 xs
    let bad := ((texts.zip escaped).zip paras).filter fun ((s, e), xs) =>
      let got := Ir.plainText xs
      let same := if spaced s then Text.norm got.toList == Text.norm s.toList
        else if typographic s then Text.canon got.toList == Text.canon s.toList
        else got == s
      cites xs > 0 || !same || MarkdownDoc.readText true ats none e != some s.toList
    t s!"twin: escaped text reads back as itself (cites {ats}; {bad.length} of {texts.length} not, \
{paras.length} paragraphs: {(bad.take 6).map (·.1.1)})"
      (paras.length == texts.length && bad.isEmpty)
  for raw in ["*Kqzv*", "_Kqzv_", "`Kqzv`", "<https://example.org>", "&amp;", "[Kqzv](#x)"] do
    let xs := match (elabMd (raw ++ "\n")).1.body.toList with
      | [.para xs] => xs
      | _ => #[]
    t s!"twin: unescaped markup {raw} reads as none under the model and as markup at the door"
      (MarkdownDoc.readText true false none raw.toList == none && Ir.plainText xs != raw)

def markdownTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  twinDisclosureChecks ref
  twinLinesChecks ref
  twinInlineChecks ref
  twinBlockChecks ref
  twinLineStartChecks ref
  twinTableChecks ref
  twinHeadingChecks ref
  twinHeadChecks ref
  twinDriverChecks ref
  twinEdgeChecks ref
  twinEscapeReadChecks ref

end Tests.MarkdownTwin
