/-
The PDF reader and validator oracle. Run from the repository root:

  lake build TestsModules leantex && lake env lean --run scripts/pdf-oracles.lean

The engine's own reader judges every written file inside `lake test`
(Tests/PdfConformance.lean: the reference walk, the mutants, determinism).
This script is the external half: it builds every corpus fixture that
declares a PDF output (or declares none) with the shipped binary, then asks
the readers on this host — Poppler (`pdfinfo`, `pdffonts`, `pdftotext`),
Ghostscript, pypdf — and the validator (veraPDF, PDF/A-4 and PDF/UA-2 on
the four reference fixtures) what they make of the bytes, and writes what
they said as data: `tests/oracles/reader-matrix.txt`, whose `[feature]`
cells are (feature, reader) verdicts and whose `[profile]` cells are the
validator's measured failures per fixture. This script is the file's only
writer; `lake test` reads it like a golden and never asks what is
installed. A tool not on PATH writes `untested`, never `pass`.

Exit is non-zero when any cell in a `target:` column is not `pass`. The
run record (tool versions, per-fixture verdicts, the matrix diff, the
validator's raw summaries) lands under
/tmp/leantex-agents/modern-output/pdf-oracles-<date>.md.
-/
import Tests.PdfConformance

open LeanTex.Core

def die (msg : String) : IO Unit := do
  IO.eprintln s!"pdf-oracles: FAIL {msg}"
  IO.Process.exit 1

def runTool (cmd : String) (args : Array String) : IO (Option IO.Process.Output) := do
  try
    pure (some (← IO.Process.output { cmd, args }))
  catch _ => pure none

/-- The version a tool prints, or `none` when it is not on PATH. -/
def versionOf (cmd : String) (args : Array String) (pick : String → Option String) :
    IO (Option String) := do
  match ← runTool cmd args with
  | none => pure none
  | some out =>
    if out.exitCode != 0 then pure none else pure (pick (out.stdout ++ out.stderr))

def firstWordAfter (text key : String) : Option String :=
  ((text.splitOn key).drop 1).head?.bind fun rest =>
    ((rest.trimAscii.toString.splitOn "\n").head?.bind fun l => (l.splitOn " ").head?)

/-- The readers exercised: every column the matrix carries, in order. -/
def readerColumns : Array String :=
  #["poppler", "ghostscript", "pypdf", "verapdf", "pdfium", "pdfjs", "qpdf", "arlington"]

/-- The columns this run exercises and the gate demands `pass` on. -/
def targetColumns : Array String := #["poppler", "ghostscript", "pypdf"]

/-- The fixtures the `[profile]` section is keyed by: synthetic, four
shapes (deck, one-page résumé, two-face card, image page). -/
def profileFixtures : List String := ["deck", "resume", "trio-card", "images"]

/-- One fixture's verdicts from the host readers: a reason per failed
check, empty when every check passed. -/
structure Fixture where
  name : String
  pages : Nat
  features : List String
  poppler : Array String := #[]
  ghostscript : Array String := #[]
  pypdf : Array String := #[]
  tagged : String := ""
  deriving Repr

/-- A font set from the faces this host and the corpus directory carry:
the body (or sans) family the document names, at the four standard
weights, else the default family; the math face the driver would pick
(declared, or the body's companion, or the first MATH-table face); the
scan's per-glyph fallback — enough for the shipped text the containment
check reads. The driver's declared per-variant faces are not reproduced
here: they move line breaks, never the characters shipped. -/
def fontSetFor (faces : Array FontDb.Face) (doc : Ir.Doc) : IO (Option Font.FontSet) := do
  let spec := doc.fonts
  let named := spec.body.orElse fun _ => spec.sans.orElse fun _ => spec.mono
  let some family := named.orElse fun _ => FontDb.defaultFamily faces | return none
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Nat × Bool) × Nat) := #[]
  let famOf (slot : Nat) : String := match slot with
    | 1 => spec.sans.getD family
    | 2 => spec.mono.getD family
    | _ => family
  for slot in [0:3] do
    for (w, i) in [(400, false), (700, false), (400, true), (700, true)] do
      if let some (face, _) := FontDb.resolveWeight faces (famOf slot) none w i then
        match paths.findIdx? (· == face.path) with
        | some k => index := index.push ((slot, w, i), k)
        | none =>
          if let .ok f := Font.parse (← IO.FS.readBinFile face.path) then
            index := index.push ((slot, w, i), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  if fonts.isEmpty then return none
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  for c in Layout.docScalars doc do
    match (Array.range fonts.size).find? (fun k => ((fonts[k]!).gid c).isSome) with
    | some k => fallback := fallback.push (c, k)
    | none => uncovered := uncovered.push c
  for (c, path) in ← FontDb.fallbackPicksPreferring (·.startsWith "tests/corpus") faces uncovered do
    match paths.findIdx? (· == path) with
    | some k => fallback := fallback.push (c, k)
    | none =>
      if let .ok f := Font.parse (← IO.FS.readBinFile path) then
        fallback := fallback.push (c, fonts.size)
        fonts := fonts.push f
        paths := paths.push path
  let mut mathIdx : Option Nat := none
  let mathPick : Option FontDb.Face ← match spec.math with
    | some fam => pure ((FontDb.resolveVariant faces fam none {}).map (·.1))
    | none =>
      if (Layout.docMathScalars doc).isEmpty then pure none
      else pure ((← FontDb.pickMathFace faces (spec.body.getD "")).map (·.1))
  if let some face := mathPick then
    match paths.findIdx? (· == face.path) with
    | some k => if (fonts[k]!).math.isSome then mathIdx := some k
    | none =>
      if let .ok f := Font.parse (← IO.FS.readBinFile face.path) then
        if f.math.isSome then
          mathIdx := some fonts.size
          fonts := fonts.push f
          paths := paths.push face.path
  return some { fonts, index, fallback, math := mathIdx }

/-- The ink a text carries, as a character multiset: what containment
compares. Whitespace is layout, the hyphen is line breaking's (a word
hyphenated at a line end gains one), so neither counts. -/
def inkOf (s : String) : Std.HashMap Char Nat :=
  s.toList.foldl (fun m c =>
    if c.isWhitespace || c == '-' || c == '\u00ad' then m
    else m.insert c (m.getD c 0 + 1)) {}

/-- The characters of `need` (with multiplicity) that `have` lacks. -/
def missingInk (need have_ : Std.HashMap Char Nat) : Array Char :=
  need.fold (fun acc c k =>
    let short := k - have_.getD c 0
    acc ++ Array.replicate short c) #[]

/-- The failed rule ids in a veraPDF XML report, `clause-testNumber`,
sorted, once each; and the report's own summary line. -/
def veraFailures (xml : String) : Array String × String := Id.run do
  let mut ids : Array String := #[]
  let mut summary := ""
  for l in xml.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith "<details " then summary := t
    if t.startsWith "<rule " && hasStr t "status=\"failed\"" then
      let attr (k : String) : String :=
        (((t.splitOn (k ++ "=\"")).drop 1).head?.bind fun r => (r.splitOn "\"").head?).getD "?"
      let id := s!"{attr "clause"}-{attr "testNumber"}"
      unless ids.contains id do ids := ids.push id
  return (ids.qsort (· < ·), summary)

def main : IO Unit := do
  let bin := ".lake/build/bin/leantex"
  unless ← System.FilePath.pathExists bin do
    let b ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
    if b.exitCode != 0 then die s!"lake build leantex: {b.stderr}"
  let date := ((← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }).stdout).trimAscii.toString
  -- Tool versions; a missing tool is `none`, and its column stays untested.
  let popplerV ← versionOf "pdfinfo" #["-v"] (firstWordAfter · "pdfinfo version ")
  let gsV ← versionOf "gs" #["--version"] fun s => (s.trimAscii.toString.splitOn "\n").head?
  let pypdfV ← versionOf "python3" #["-c", "import pypdf; print(pypdf.__version__)"]
    fun s => (s.trimAscii.toString.splitOn "\n").head?
  let veraPath := "/home/linuxbrew/.linuxbrew/bin/verapdf"
  let veraV ← versionOf veraPath #["--version"] (firstWordAfter · "veraPDF ")
  let toolsLine (vera : Option String) : String := String.intercalate "  " [
    s!"poppler {popplerV.getD "absent"}", s!"ghostscript {gsV.getD "absent"}",
    s!"pypdf {pypdfV.getD "absent"}", s!"verapdf {vera.getD "absent"}"]
  IO.println s!"pdf-oracles: {toolsLine veraV}"
  let dir ← IO.FS.createTempDir
  let faces ← FontDb.scanRoots (["tests/corpus/fonts"] ++ (← FontDb.systemRoots []))
  let pats := Hyphen.english.get
  -- The fixtures: every corpus document that declares a PDF output or
  -- declares none, built by the shipped binary.
  let mut names : Array String := #[]
  for f in ← System.FilePath.readDir "tests/corpus" do
    if f.fileName.endsWith ".tex" then
      names := names.push ((f.fileName.dropEnd 4).toString)
  names := names.qsort (· < ·)
  let mut fixtures : Array Fixture := #[]
  let mut notBuilt : Array String := #[]
  let mut record : Array String := #[]
  for n in names do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let formats := doc.output.formats
    unless formats.isEmpty || formats.contains "pdf" do continue
    let pdfPath := dir / s!"{n}.pdf"
    let built ← IO.Process.output { cmd := bin, args :=
      #[s!"tests/corpus/{n}.tex", "-o", pdfPath.toString, "--porcelain", "-q"] }
    if built.exitCode != 0 then
      notBuilt := notBuilt.push s!"{n} (exit {built.exitCode})"
      continue
    let pages := (((built.stdout.splitOn "\"pages\":").drop 1).head?.bind fun r =>
      ((r.splitOn ",").head?.bind (·.toNat?))).getD 0
    let pdf ← IO.FS.readBinFile pdfPath
    let features ← match PdfRead.objects pdf with
      | .ok es => pure (featuresOfEntries es.val)
      | .error e => die s!"{n}: the engine's reader refuses the built file: {e}"; pure []
    let mut fx : Fixture := { name := n, pages, features }
    -- Poppler: pdfinfo, pdffonts, pdftotext.
    if popplerV.isSome then
      let info ← IO.Process.output { cmd := "pdfinfo", args := #[pdfPath.toString] }
      let field (k : String) : String :=
        ((((info.stdout.splitOn (k ++ ":")).drop 1).head?.bind fun r =>
          (r.splitOn "\n").head?).getD "").trimAscii.toString
      unless field "PDF version" == "2.0" do
        fx := { fx with poppler := fx.poppler.push s!"pdfinfo-version:{field "PDF version"}" }
      unless field "Pages" == toString pages do
        fx := { fx with poppler := fx.poppler.push s!"pdfinfo-pages:{field "Pages"}/{pages}" }
      fx := { fx with tagged := field "Tagged" }
      let fonts ← IO.Process.output { cmd := "pdffonts", args := #[pdfPath.toString] }
      let rows := ((fonts.stdout.splitOn "\n").drop 2).filter (!·.trimAscii.toString.isEmpty)
      let cols (l : String) : Array String :=
        ((l.splitOn " ").filter (!·.isEmpty)).toArray
      let embAll := rows.all fun l => let c := cols l; c[c.size - 5]? == some "yes"
      let uniAll := rows.all fun l => let c := cols l; c[c.size - 3]? == some "yes"
      unless embAll do fx := { fx with poppler := fx.poppler.push "pdffonts-emb" }
      unless uniAll do fx := { fx with poppler := fx.poppler.push "pdffonts-uni" }
      -- pdffonts' `emb` column and the engine's census agree: pdf-objects'
      -- oracle, reasserted here.
      match PdfCensus.census pdf with
      | .ok c =>
        unless c.fontsEmbedded == embAll do
          fx := { fx with poppler := fx.poppler.push "pdffonts-census-disagree" }
      | .error e => fx := { fx with poppler := fx.poppler.push s!"census:{e}" }
      let text ← IO.Process.output { cmd := "pdftotext", args := #["-layout", pdfPath.toString, "-"] }
      match ← fontSetFor faces doc with
      | none => fx := { fx with poppler := fx.poppler.push "pdftotext-nofont" }
      | some fs =>
        let store ← corpusStore doc
        let out := layoutOf fs doc (Layout.Geom.ofPage doc.page) (some pats) store
        -- Body lines only: furniture (line numbers, running feet) follows
        -- this font set's line breaks, which the driver's may not share.
        let shipped := String.intercalate " " ((bodyLines out).toList.map (lineText ·))
        let missing := missingInk (inkOf shipped) (inkOf text.stdout)
        unless missing.isEmpty do
          let sample := String.ofList (missing.toList.take 12)
          fx := { fx with poppler := fx.poppler.push s!"pdftotext-missing:{missing.size}:{sample}" }
    -- Ghostscript: a full interpretation with errors fatal, no device.
    if gsV.isSome then
      let gs ← IO.Process.output { cmd := "gs", args :=
        #["-q", "-dNOPAUSE", "-dBATCH", "-dPDFSTOPONERROR", "-sDEVICE=nullpage", pdfPath.toString] }
      unless gs.exitCode == 0 && gs.stderr.isEmpty && gs.stdout.isEmpty do
        let why := (gs.stderr ++ gs.stdout).trimAscii.toString.take 60
        fx := { fx with ghostscript := fx.ghostscript.push s!"gs-exit{gs.exitCode}:{why}" }
    -- pypdf, strict: every page's text and the metadata read.
    if pypdfV.isSome then
      let py ← IO.Process.output { cmd := "python3", args := #["-c",
        "import sys\nfrom pypdf import PdfReader\nr = PdfReader(sys.argv[1], strict=True)\n\
for p in r.pages:\n    p.extract_text()\nr.metadata\nprint(len(r.pages))", pdfPath.toString] }
      unless py.exitCode == 0 && py.stdout.trimAscii.toString == toString pages do
        let why := ((py.stderr.trimAscii.toString.splitOn "\n").getLast?.getD "").take 60
        fx := { fx with pypdf := fx.pypdf.push s!"pypdf-exit{py.exitCode}:{why}" }
    fixtures := fixtures.push fx
    let verdict (xs : Array String) : String := if xs.isEmpty then "pass" else String.intercalate " " xs.toList
    record := record.push s!"| {n} | {pages} | {fx.tagged} | {verdict fx.poppler} | {verdict fx.ghostscript} | {verdict fx.pypdf} | {String.intercalate " " fx.features} |"
    IO.println s!"  {n}: {pages} pages; poppler {verdict fx.poppler}; gs {verdict fx.ghostscript}; pypdf {verdict fx.pypdf}"
  if fixtures.size < 40 then die s!"only {fixtures.size} fixtures built"
  -- veraPDF over the four reference fixtures, both profiles: measured
  -- failures, recorded as cells and in the run record.
  let mut profiles : Array (String × String × String) := #[]
  let mut veraRaw : Array String := #[]
  let mut veraCore : Option String := none
  for n in profileFixtures do
    unless fixtures.any (·.name == n) do die s!"profile fixture {n} was not built"
    for (profile, flavour) in [("pdf/a-4", "4"), ("pdf/ua-2", "ua2")] do
      let cell ← if veraV.isNone then pure "untested" else do
        let v ← IO.Process.output { cmd := veraPath, args := #["-df", flavour, (dir / s!"{n}.pdf").toString] }
        let (ids, summary) := veraFailures v.stdout
        veraCore := veraCore.orElse fun _ =>
          firstWordAfter v.stdout "<releaseDetails id=\"core\" version=\"" |>.map fun w =>
            ((w.splitOn "\"").headD w)
        veraRaw := veraRaw.push s!"- {profile} {n}: {summary}"
        pure (if ids.isEmpty then (if hasStr v.stdout "isCompliant=\"true\"" then "pass" else "fail:unparsed")
          else s!"fail:{String.intercalate "," ids.toList}")
      profiles := profiles.push (profile, n, cell)
      IO.println s!"  {profile} {n}: {cell}"
  -- The feature cells: a reader passes a feature when it passed every
  -- fixture that reaches it; a feature no built fixture reaches is untested.
  let cellFor (reader : String) (feature : String) : String :=
    let reaching := fixtures.filter (·.features.contains feature)
    if reaching.isEmpty then "untested" else
    let verdictOf (fx : Fixture) : Array String := match reader with
      | "poppler" => if popplerV.isNone then #["untested"] else fx.poppler
      | "ghostscript" => if gsV.isNone then #["untested"] else fx.ghostscript
      | "pypdf" => if pypdfV.isNone then #["untested"] else fx.pypdf
      | _ => #["untested"]
    let fails := reaching.filterMap fun fx =>
      let v := verdictOf fx
      if v.isEmpty then none else some (fx.name, v)
    if fails.any (·.2 == #["untested"]) then "untested"
    else if fails.isEmpty then "pass"
    else "fail:" ++ String.intercalate "," (fails.toList.map fun (n, v) =>
      s!"{n}={String.intercalate "+" ((v.map fun s => (s.splitOn ":").headD s).toList)}")
  -- The CLI's version and the validation core's, as veraPDF reports both.
  let tools := toolsLine (veraV.map fun v => match veraCore with
    | some c => if c == v then v else s!"{v}/{c}"
    | none => v)
  let pad (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - min w s.length) ' ')
  let mut lines : Array String := #[
    "# generated by scripts/pdf-oracles.lean — do not hand-edit",
    s!"target: {String.intercalate " " targetColumns.toList}",
    s!"tools: {tools}",
    s!"date: {date}",
    "",
    "[feature]",
    pad "# feature" 20 ++ String.intercalate "  " (readerColumns.toList.map (pad · 12))]
  for f in writerFeatures do
    lines := lines.push (pad f 20 ++ String.intercalate "  " (readerColumns.toList.map fun r => pad (cellFor r f) 12))
  lines := lines.push ""
  lines := lines.push "[profile]"
  lines := lines.push (pad "# profile" 10 ++ pad "fixture" 11 ++ "verdict")
  for (p, n, cell) in profiles do
    lines := lines.push (pad p 10 ++ pad n 11 ++ cell)
  let text := String.intercalate "\n" lines.toList ++ "\n"
  let matrixPath := "tests/oracles/reader-matrix.txt"
  let previous ← try IO.FS.readFile matrixPath catch _ => pure ""
  IO.FS.createDirAll "tests/oracles"
  IO.FS.writeFile matrixPath text
  -- The file reads back through the gate's own parser, and the gate judges it.
  let gaps ← match readMatrix text with
    | .error e => die s!"the written matrix does not parse: {e}"; pure #[]
    | .ok m => pure (featureGate m writerFeatures)
  -- The run record.
  let diff := if previous == text then "unchanged" else if previous.isEmpty then "new file" else Id.run do
    let a := (previous.splitOn "\n").toArray
    let b := (text.splitOn "\n").toArray
    let mut out : Array String := #[]
    for i in [0:max a.size b.size] do
      let la := a[i]?.getD ""
      let lb := b[i]?.getD ""
      if la != lb then out := out.push s!"  - {la}\n  + {lb}"
    return String.intercalate "\n" out.toList
  let recordDir := "/tmp/leantex-agents/modern-output"
  IO.FS.createDirAll recordDir
  let recordPath := s!"{recordDir}/pdf-oracles-{date}.md"
  IO.FS.writeFile recordPath (String.intercalate "\n" ([
    s!"# pdf-oracles run — {date}", "",
    s!"tools: {tools}", "",
    s!"veraPDF --version: {(((← runTool veraPath #["--version"]).map (·.stdout)).getD "absent").trimAscii}",
    "", s!"fixtures built: {fixtures.size}; not built: {if notBuilt.isEmpty then "none" else String.intercalate ", " notBuilt.toList}",
    "", "| fixture | pages | Tagged | poppler | ghostscript | pypdf | features |",
    "|---|---:|---|---|---|---|---|"] ++ record.toList ++ [
    "", "## veraPDF raw summaries", ""] ++ veraRaw.toList ++ [
    "", "## profile cells", ""] ++ (profiles.toList.map fun (p, n, c) => s!"- {p} {n}: {c}") ++ [
    "", "## matrix diff against the checked-in file", "", diff,
    "", s!"## gate over target columns: {if gaps.isEmpty then "pass" else String.intercalate "; " gaps.toList}", ""]))
  IO.println s!"pdf-oracles: wrote {matrixPath} and {recordPath}"
  IO.FS.removeDirAll dir
  unless gaps.isEmpty do die s!"target cells not pass: {gaps}"
  IO.println "pdf-oracles: all target cells pass"
