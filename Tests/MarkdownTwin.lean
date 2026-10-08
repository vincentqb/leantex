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

def markdownTwinChecks (ref : IO.Ref (List String)) : IO Unit := do
  twinInlineChecks ref

end Tests.MarkdownTwin
