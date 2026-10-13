/-
The mdtwin tier: whether the markdown twin reads back, per CommonMark section (`reread-exact`)
and over the corpus (`reread-clean`, `twin-stable`); hermetic.
Usage: lake build TestsModules ScriptsModules && lake env lean --run scripts/mdtwin.lean [--check | --selftest]
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

/-- The examples of the spec, in order: a fence of 32 backticks and `example` opens one, a
lone `.` ends its markdown, the section is the last `## ` heading outside an example, and
a `→` stands for a tab. -/
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

/-- Every corpus document as the driver elaborates it (`corpusTwinDocs`). -/
def corpusDocs : IO (Array (String × Ir.Doc)) := corpusTwinDocs

def measureWith (emit : Ir.Doc → String) : IO (Array String × Array Row) := do
  let cases := readCases (← IO.FS.readFile specPath)
  let (cm, accepted, exact) := cmRows emit cases
  let docs ← corpusDocs
  let (corpus, clean, stable) := corpusRows emit (docs.map (·.2))
  return (#[s!"# source: {cases.size} CommonMark 0.31.2 examples, {accepted} accepted by the \
reader, {exact} of them re-read from their twin to the same IR body",
    s!"# source: {docs.size} corpus documents, {clean} twins re-read with no error, \
{stable} a fixed point of the round trip"], cm ++ corpus)

/-- A twin that writes `*` unescaped: the round trip it fails is the one a
lost escape loses. -/
def droppedEscapes (d : Ir.Doc) : String := (MarkdownDoc.emit d).replace "\\*" "*"

def mdtwinSelftest : IO UInt32 := tierSelftest "mdtwin" fun no => do
  -- The blind-spot pair: italic re-reads as emphasis, a byte fixed point the IR level sees.
  let italic : Ir.Doc := { body := #[.para #[.styled .italic #[.text "x"]]] }
  let emph : Ir.Doc := { body := #[.para #[.styled .emph #[.text "x"]]] }
  let back := (reread MarkdownDoc.emit italic).1
  no "blind spot: italic and emphasis write one twin"
    (MarkdownDoc.emit italic == MarkdownDoc.emit emph)
  no "blind spot: twin-stable is blind to it, the re-read italic writing the same twin"
    (MarkdownDoc.emit back == MarkdownDoc.emit italic)
  no "blind spot: reread-exact sees it, the re-read italic being another body"
    (back.body != italic.body)
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
