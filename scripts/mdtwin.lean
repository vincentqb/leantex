/-
The mdtwin tier: whether the markdown twin reads back per CommonMark section, over the corpus and,
for citations, with their bibliography (`cite.reread-ink`); hermetic.
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

/-- A document read back from its twin, built with the `.bib` texts its bibliography named, as the
document was. -/
def rereadWith (emit : Ir.Doc → String) (d : Ir.Doc) (found : Array (String × String)) :
    Ir.Doc × Array Diag :=
  if found.isEmpty then reread emit d else mdBibBuild (emit d) found

/-- The corpus rows, over documents already elaborated, each with its `.bib` texts. -/
def corpusRows (emit : Ir.Doc → String) (docs : Array (Ir.Doc × Array (String × String))) :
    Array Row × Nat × Nat := Id.run do
  let mut clean := 0
  let mut stable := 0
  for (d, found) in docs do
    let (back, ds) := rereadWith emit d found
    unless hasError ds do clean := clean + 1
    if emit back == emit d then stable := stable + 1
  return (#[{ item := "corpus.reread-clean", value := (clean : Int) },
    { item := "corpus.twin-stable", value := (stable : Int) }], clean, stable)

/-- The citation rows: Pandoc's citations, under a declared bibliography, whose twin re-reads to the
same IR body. -/
def citeRows (emit : Ir.Doc → String) (cases : List String) : Array Row × Nat := Id.run do
  let mut exact := 0
  for md in cases do
    let (d, _) := elabMd (worksMeta ++ md ++ "\n")
    if (reread emit d).1.body == d.body then exact := exact + 1
  return (#[{ item := "cite.reread-exact", value := (exact : Int) }], exact)

/-- A cited document's twin built again with the `.bib` texts its bibliography named. -/
def rebuiltWith (emit : Ir.Doc → String) (d : Ir.Doc) (found : Array (String × String)) : Ir.Doc :=
  (rereadWith emit d found).1

/-- The citation-ink rows: the cited documents, each with its `.bib` texts, whose twin, built again
with their bibliography, sets the same text, where its blocks break aside. -/
def citeInkRows (emit : Ir.Doc → String) (docs : Array (Ir.Doc × Array (String × String))) :
    Array Row × Nat × Nat := Id.run do
  let mut same : Nat := 0
  for (d, found) in docs do
    let back := rebuiltWith emit d found
    if inkFlat back.body == inkFlat d.body then same := same + 1
  return (#[{ item := "cite.reread-ink", value := (same : Int) }], docs.size, same)

/-- The corpus documents, each with the `.bib` texts beside the corpus its bibliography names. -/
def withBibs (docs : Array Ir.Doc) : IO (Array (Ir.Doc × Array (String × String))) :=
  docs.mapM fun d => return (d, ← corpusBibs d)

/-- Every corpus document as the driver elaborates it (`corpusTwinDocs`). -/
def corpusDocs : IO (Array (String × Ir.Doc)) := corpusTwinDocs

def measureWith (emit : Ir.Doc → String) : IO (Array String × Array Row) := do
  let cases := readCases (← IO.FS.readFile specPath)
  let (cm, accepted, exact) := cmRows emit cases
  let docs ← corpusDocs
  let found ← withBibs (docs.map (·.2))
  let (corpus, clean, stable) := corpusRows emit found
  let citeCases := mdCiteTwinCases.map (·.1)
  let (cite, citeExact) := citeRows emit citeCases
  let (ink, cited, inked) := citeInkRows emit (found.filter fun (d, _) => !(Ir.bibRefs d).isEmpty)
  return (#[s!"# source: {cases.size} CommonMark 0.31.2 examples, {accepted} accepted by the \
reader, {exact} of them re-read from their twin to the same IR body",
    s!"# source: {docs.size} corpus documents, {clean} twins re-read with no error, \
{stable} a fixed point of the round trip",
    s!"# source: {citeCases.length} Pandoc citations, {citeExact} re-read from their twin to the \
same IR body",
    s!"# source: {cited} cited corpus documents, {inked} of them setting the same text from their \
twin built again with their bibliography"], cm ++ corpus ++ cite ++ ink)

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
  -- A writer that escapes every at sign is seen: its citations read back as text.
  let citeCases := mdCiteTwinCases.map (·.1)
  let (_, spelled) := citeRows MarkdownDoc.emit citeCases
  let (_, escaped) := citeRows (fun d => (MarkdownDoc.emit d).replace "@" "\\@") citeCases
  no s!"planted: a writer that escapes at signs lowers cite.reread-exact ({spelled} → {escaped})"
    (escaped < spelled)
  -- The blind-spot pair: a twin setting a citation as its ink reads back to the same text, which
  -- cite.reread-ink cannot tell from the twin spelling it, while the re-read body is another.
  let bibs := #[("works.bib", worksBib)]
  let (cited, _) := mdBibBuild (worksMeta ++ "Text [@a].\n") bibs
  let spelledBack := rebuiltWith MarkdownDoc.emit cited bibs
  let inkedBack := rebuiltWith MarkdownDoc.emit { cited with citeSetup := none } bibs
  no "blind spot: cite.reread-ink is blind to a twin setting its citations as their ink"
    (inkText inkedBack.body == inkText spelledBack.body && inkText spelledBack.body == inkText cited.body)
  no "blind spot: the re-read body sees it, the inked twin reading back no citation"
    (inkedBack.body != spelledBack.body && spelledBack.body == cited.body)
  -- The blind-spot pair: one paragraph and its text in two set one ink, which cite.reread-ink
  -- cannot tell apart, while the bodies differ.
  let whole : Array Ir.Block := #[.para #[.text "ab"]]
  let split : Array Ir.Block := #[.para #[.text "a"], .para #[.text "b"]]
  no "blind spot: cite.reread-ink is blind to where a body's blocks break"
    (inkFlat whole == inkFlat split)
  no "blind spot: the re-read body sees it, the blocks being others" (whole != split)
  -- A twin that drops its metadata block is seen: its citations read back as their source.
  let dropMeta (d : Ir.Doc) : String :=
    ((MarkdownDoc.emit d).splitOn "\n---\nbibliography:").headD ""
  let (_, citedN, inked) := citeInkRows MarkdownDoc.emit #[(cited, bibs)]
  let (_, _, dropped) := citeInkRows dropMeta #[(cited, bibs)]
  no s!"planted: a twin without its metadata lowers cite.reread-ink ({inked} → {dropped})"
    (citedN == 1 && dropped < inked)
  -- An error in the re-read is what reread-clean counts.
  let (_, clean, _) := corpusRows (fun _ => "<div>raw html</div>\n") #[(italic, #[])]
  no "planted: a twin the reader refuses is not clean" (clean == 0)
  -- The reader of the spec: an example, its section, its tab.
  let fence := String.ofList (List.replicate 32 '`')
  let parsed := readCases ("## Tabs\n\n" ++ fence ++ " example\n\u2192foo\n.\n<p>x</p>\n" ++
    fence ++ "\n## Next\n")
  no "spec reader: one example in its section, its tab restored"
    (parsed.size == 1 && parsed.all fun c => c.section_ == "Tabs" && c.md == "\tfoo\n")

def main (args : List String) : IO UInt32 :=
  tierMain "mdtwin" .raw (measureWith MarkdownDoc.emit) mdtwinSelftest args
