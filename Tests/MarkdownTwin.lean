import Tests.Support

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
  -- A bare link is an autolink; a destination reads back exactly.
  let (tw, back, _) := texRoundTrip "\\url{http://example.org/x}"
  t s!"twin: a bare link is an autolink ({repr tw})"
    (hasStr tw "<http://example.org/x>" &&
      back.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .link url _ => url == "http://example.org/x"
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

def markdownTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  twinInlineChecks ref
  twinBlockChecks ref
  twinLineStartChecks ref

end Tests.MarkdownTwin
