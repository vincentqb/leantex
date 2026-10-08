/-
Does the markdown twin read back? Committed as numbers. Run from the
repository root:

  lake env lean --run scripts/mdtwin.lean              regenerate the baseline
  lake env lean --run scripts/mdtwin.lean --check      gate against the committed one
  lake env lean --run scripts/mdtwin.lean --selftest   break each measurement once

The twin (`MarkdownDoc.emit`) writes markdown from the IR, and the markdown
door reads markdown into the same IR. The round trip is the twin's
correctness claim, and it is an internal one: measured here, never assumed.
Three measurements, each a level with its own blind spot:

* `cm.<section>.reread-exact` — of the CommonMark examples the reader
  accepts (no error), how many re-read from their own twin to the same IR
  body. Per section, so one section's fall cannot hide behind another's
  rise.
* `corpus.reread-clean` — of the tex corpus, run as the driver runs it,
  how many twins re-read with no error.
* `corpus.twin-stable` — how many twins are a fixed point of the round
  trip: emitting the re-read document writes the same bytes.

`twin-stable` is blind to IR distinctions markdown cannot spell (italic and
emphasis both write `*x*`), which `reread-exact` sees; the selftest holds
that pair in both directions.

Hermetic: committed inputs only, elaboration in-process, no fonts, no
tool, no network.
-/
import Tests.Support
import scripts.Board

open LeanTex.Core Scoreboard

/-- The CommonMark spec this tier reads its examples from, the commonmark
tier's own committed copy. -/
def specPath : String := "testdata/commonmark/spec-0.31.2.txt"

/-- One spec example's markdown and its section. -/
structure Case where
  section_ : String
  md : String

/-- The examples of the spec, in order: a fence of 32 backticks and
`example` opens one, a lone `.` ends its markdown, and the section is the
last `## ` heading outside an example. A `→` stands for a tab. -/
def readCases (text : String) : Array Case := Id.run do
  let fence := String.ofList (List.replicate 32 '`')
  let mut out : Array Case := #[]
  let mut sec := "Introduction"
  let mut inside := false
  let mut afterDot := false
  let mut md := ""
  for raw in text.splitOn "\n" do
    let line := if raw.endsWith "\r" then (raw.toList.dropLast |> String.ofList) else raw
    if inside then
      if line == fence then
        out := out.push { section_ := sec, md := md }
        inside := false
        afterDot := false
        md := ""
      else if line == "." && !afterDot then afterDot := true
      else if !afterDot then
        md := md ++ String.ofList (line.toList.map fun c => if c == '\u2192' then '\t' else c) ++ "\n"
    else if line.startsWith fence && (line.splitOn "example").length > 1 then
      inside := true
    else if line.startsWith "## " then
      sec := (line.toList.drop 3 |> String.ofList)
  return out

/-- A document read back from its twin, through the markdown door. -/
def reread (emit : Ir.Doc → String) (d : Ir.Doc) : Ir.Doc × Array Diag :=
  elabMd (emit d)

def hasError (ds : Array Diag) : Bool := ds.any (·.severity == .error)

/-- The CommonMark rows: per section, the accepted examples whose twin
re-reads to the same body. -/
def cmRows (emit : Ir.Doc → String) (cases : Array Case) : Array Row × Nat × Nat := Id.run do
  let mut sections : Array (String × Nat) := #[]
  let mut accepted := 0
  let mut exact := 0
  for c in cases do
    let (d, ds) := elabMd c.md
    let i := match sections.findIdx? (·.1 == c.section_) with
      | some i => i
      | none => sections.size
    if i == sections.size then sections := sections.push (c.section_, 0)
    if hasError ds then continue
    accepted := accepted + 1
    if (reread emit d).1.body == d.body then
      exact := exact + 1
      sections := sections.modify i fun (s, k) => (s, k + 1)
  let rows := sections.map fun (s, k) => { item := s!"cm.{s}.reread-exact", value := (k : Int) }
  return (rows, accepted, exact)

/-- The corpus rows, over documents already elaborated. -/
def corpusRows (emit : Ir.Doc → String) (docs : Array Ir.Doc) : Array Row × Nat × Nat := Id.run do
  let mut clean := 0
  let mut stable := 0
  for d in docs do
    let (back, ds) := reread emit d
    unless hasError ds do clean := clean + 1
    if emit back == emit d then stable := stable + 1
  return (#[{ item := "corpus.reread-clean", value := (clean : Int) },
    { item := "corpus.twin-stable", value := (stable : Int) }], clean, stable)

/-- Every tex fixture of the corpus, run as the driver runs it: its includes
fulfilled at their use, then elaboration. -/
def corpusDocs : IO (Array (String × Ir.Doc)) := do
  let mut paths : Array String := #[]
  for f in ← System.FilePath.readDir "testdata/corpus" do
    if f.fileName.endsWith ".tex" then paths := paths.push f.path.toString
  let mut out := #[]
  for p in paths.qsort (· < ·) do
    let (d, _) ← elabInputSrc p (← IO.FS.readFile p)
    out := out.push (p, d)
  return out

def measureWith (emit : Ir.Doc → String) : IO (Array String × Array Row) := do
  let cases := readCases (← IO.FS.readFile specPath)
  let (cm, accepted, exact) := cmRows emit cases
  let docs ← corpusDocs
  let (corpus, clean, stable) := corpusRows emit (docs.map (·.2))
  return (#[s!"# source: {cases.size} CommonMark 0.31.2 examples, {accepted} accepted by the \
reader, {exact} of them re-read from their twin to the same IR body",
    s!"# source: {docs.size} tex corpus fixtures, {clean} twins re-read with no error, \
{stable} a fixed point of the round trip"], cm ++ corpus)

/-- A twin that writes `*` unescaped: the round trip it fails is the one a
lost escape loses. -/
def droppedEscapes (d : Ir.Doc) : String := (MarkdownDoc.emit d).replace "\\*" "*"

def mdtwinSelftest : IO UInt32 := tierSelftest "mdtwin" fun no => do
  -- The blind-spot pair: italic and emphasis write one spelling, so the
  -- byte level sees one twin where the IR level sees two documents.
  let italic : Ir.Doc := { body := #[.para #[.styled .italic #[.text "x"]]] }
  let emph : Ir.Doc := { body := #[.para #[.styled .emph #[.text "x"]]] }
  no "blind spot: twin-stable reads italic and emphasis as one twin"
    (MarkdownDoc.emit italic == MarkdownDoc.emit emph)
  no "blind spot: reread-exact tells italic from emphasis"
    (italic.body != emph.body)
  -- A writer that drops escapes is seen: its literal asterisks read back as
  -- emphasis.
  let cases : Array Case := #[{ section_ := "S", md := "\\*a\\* b\n" },
    { section_ := "S", md := "plain\n" }]
  let (_, _, exact) := cmRows MarkdownDoc.emit cases
  let (_, _, planted) := cmRows droppedEscapes cases
  no s!"planted: a writer that drops escapes lowers reread-exact ({exact} → {planted})"
    (planted < exact)
  -- An error in the re-read is what reread-clean counts.
  let (_, clean, _) := corpusRows (fun _ => "<div>raw html</div>\n") #[italic]
  no "planted: a twin the reader refuses is not clean" (clean == 0)
  -- The reader of the spec: an example, its section, its tab.
  let fence := String.ofList (List.replicate 32 '`')
  let parsed := readCases ("## Tabs\n\n" ++ fence ++ " example\n\u2192foo\n.\n<p>x</p>\n" ++
    fence ++ "\n## Next\n")
  no "spec reader: one example in its section, its tab restored"
    (parsed.size == 1 && parsed.all fun c => c.section_ == "Tabs" && c.md == "\tfoo\n")

def main (args : List String) : IO UInt32 :=
  tierMain "mdtwin" .raw (measureWith MarkdownDoc.emit) mdtwinSelftest args
