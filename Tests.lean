import Tests.Support
import Tests.Surface
import Tests.Layout
import Tests.Census
import Tests.Backends
import Tests.Diag
import Tests.Themes
import Tests.FontMath

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The backend blocks, dispatched together so each stays a leaf the
module split can place; main runs this right after compatChecks, which
used to carry these calls as its tail. -/
def backendSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  styleChecks ref
  htmlLayoutChecks ref
  htmlRhythmChecks ref
  classHookChecks ref
  runinChecks ref
  abstractChecks ref
  headingNumberChecks ref
  anchorChecks ref
  markdownChecks ref
  mdPreambleChecks ref
  backendChecks ref
  landmarkChecks ref
  pinChecks ref
  mdNameChecks ref
  interactionChecks ref
  motionSiteChecks ref

/-- The layout, census, theme, and chrome blocks all read the same shipped
face; dispatched together so each stays a leaf the module split can place.
fontSuiteChecks used to carry these calls in its parse-success arm — it
still owns reporting a missing or unparsable font, so failure here only
skips. -/
def layoutSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let pats := Hyphen.load
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let oneFace := oneFaceOf font
  let geom : Layout.Geom := {}
  pdfFaceChecks ref geom oneFace font
  webMetaChecks ref geom oneFace

  lineChecks ref geom oneFace
  listChecks ref oneFace font
  filChecks ref oneFace
  underlineChecks ref geom oneFace font
  linkSignalChecks ref geom oneFace
  inkGeometryChecks ref
  spacingChecks ref geom oneFace font
  slideChecks ref oneFace
  tableChecks ref oneFace
  recoveryChecks ref oneFace
  roleLayoutChecks ref geom oneFace
  navLayoutChecks ref geom oneFace
  vdistChecks ref geom oneFace
  headBandChecks ref oneFace
  cardChecks ref oneFace pats
  censusChecks ref oneFace pats
  scopeChecks ref oneFace
  bandChecks ref oneFace
  agreeChecks ref oneFace pats
  pictureLayoutChecks ref oneFace
  quoteChecks ref oneFace
  refChecks ref oneFace
  titleChecks ref
  outlineChecks ref
  columnsChecks ref oneFace
  overlayChecks ref oneFace
  overlayBlockChecks ref oneFace
  noteChecks ref oneFace
  themeFurnitureChecks ref oneFace
  themeReconcileChecks ref oneFace
  chromeDeclChecks ref
  layerDiagChecks ref
  footerBandChecks ref oneFace
  chromeFooterChecks ref oneFace
  numberingChecks ref oneFace
  composeChecks ref oneFace
  frameFootChecks ref oneFace
  scannerChecks ref
  rhythmChecks ref oneFace
  measureChecks ref oneFace
  imageChecks ref oneFace

/-- The `.bib` grammar: entries, `@string` macros with `#` concatenation,
`@comment`/`@preamble`, brace nesting, both delimiter styles — and the keep
contract: a malformed entry is recorded and skipped, the rest of the file
parses. Names split into BibTeX's four parts from either comma form; values
render their TeX spellings as plain scalars. -/
def bibChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let p := Bib.parse
  let one := p "@article{doe2024, author = {Alex Doe}, title = {A Study}, year = 2024}"
  t "bib: one entry parses whole"
    (one.entries.map (·.key) == #["doe2024"] && one.errors.isEmpty &&
      (one.entries[0]?.map (·.kind)) == some "article" &&
      (one.entries[0]?.bind (·.field? "year")) == some "2024" &&
      (one.entries[0]?.bind (·.field? "author")) == some "Alex Doe")
  t "bib: field names fold to lowercase, keys keep case"
    (((p "@ARTICLE{DoE, TITLE = {x}}").entries[0]?).map (fun e => (e.key, e.field? "title"))
      == some ("DoE", some "x"))
  t "bib: braces nest and protect"
    ((p "@misc{k, title = {a {b {c}} d}}").entries[0]?.bind (·.field? "title")
      == some "a {b {c}} d")
  t "bib: quoted values, brace-protected quote"
    ((p "@misc{k, title = \"the {\"}x{\"} spelling\"}").entries[0]?.bind (·.field? "title")
      == some "the {\"}x{\"} spelling")
  t "bib: string macros concatenate with #"
    ((p "@string{tj = {Journal of Tests}}\n@article{k, journal = tj # { B}}").entries[0]?.bind
      (·.field? "journal") == some "Journal of Tests B")
  t "bib: month macros are predefined"
    ((p "@misc{k, month = jun}").entries[0]?.bind (·.field? "month") == some "June")
  t "bib: parenthesis delimiters"
    ((p "@article(k, year = 1999)").entries[0]?.bind (·.field? "year") == some "1999")
  t "bib: text between entries is comment"
    ((p "stray words @misc{k, year=1} more strays").entries.size == 1)
  t "bib: @comment and @preamble are consumed"
    (let r := p "@comment{x}\n@preamble{\"\\x\"}\n@misc{k, year=1}"
     r.entries.size == 1 && r.errors.isEmpty)
  let broken := p "@article{bad, title = {open\n@misc{good, year = 2020}}\n@book{also, year=2021}"
  t "bib: a malformed entry is recorded and the rest is kept"
    (!broken.errors.isEmpty && broken.entries.map (·.key) == #["also"])
  t "bib: an error names its line"
    ((p "@misc{k,\n  title = ?}").errors.any fun (pos, _) => pos.line == 2)
  t "bib: unknown macro keeps its name visible"
    ((p "@misc{k, journal = mystery}").entries[0]?.bind (·.field? "journal")
      == some "mystery")
  -- Names: the four-part split from both comma forms and the plain form.
  t "bib: names split on the word and, braces opaque"
    (Bib.splitNames "Doe, Alex and {Sand and Gravel Ltd} and others" ==
      #["Doe, Alex", "{Sand and Gravel Ltd}", "others"])
  t "bib: Last, First"
    (Bib.parseName "Doe, Alex" == { first := "Alex", last := "Doe" })
  t "bib: von parts from the comma form"
    (Bib.parseName "van der Berg, Alex" ==
      { first := "Alex", von := "van der", last := "Berg" })
  t "bib: Last, Jr, First"
    (Bib.parseName "Doe, Jr, Alex" == { first := "Alex", last := "Doe", jr := "Jr" })
  t "bib: First von Last"
    (Bib.parseName "Alex van der Berg" ==
      { first := "Alex", von := "van der", last := "Berg" })
  t "bib: First Middle Last"
    (Bib.parseName "Alex B. Doe" == { first := "Alex B.", last := "Doe" })
  t "bib: a braced token is one caseless token of the last name"
    (Bib.parseName "{Example Corp}" == { last := "{Example Corp}" })
  t "bib: full-name order is First von Last, Jr"
    ((Bib.parseName "Doe, Jr, Alex").full == "Alex Doe, Jr")
  t "bib: and-join two, three, elided"
    (Bib.andJoin ["A"] == "A" && Bib.andJoin ["A", "B"] == "A and B" &&
      Bib.andJoin ["A", "B", "C"] == "A, B, and C" &&
      Bib.andJoin ["A", "others"] == "A et al." &&
      Bib.andJoin ["A", "B", "others"] == "A, B, et al.")
  t "bib: label names for citet"
    (Bib.labelNames "Doe, Alex" == "Doe" &&
      Bib.labelNames "Doe, Alex and Roe, Sam" == "Doe and Roe" &&
      Bib.labelNames "Doe, Alex and Roe, Sam and Poe, Kim" == "Doe et al." &&
      Bib.labelNames "Doe, Alex and others" == "Doe et al.")
  -- Value text: TeX spellings become plain scalars.
  t "bib: accents compose"
    (Bib.text "K{\\\"u}nzel and \\'{e} and {\\`o} and \\c{c}" == "Künzel and é and ò and ç")
  t "bib: escapes, ties, dashes"
    (Bib.text "Smith \\& Jones~Ltd, 3--7 --- yes" == "Smith & Jones Ltd, 3–7 — yes")
  t "bib: braces drop, whitespace folds"
    (Bib.text "a {Grand}  title\n  across lines" == "a Grand title across lines")
  t "bib: unknown command keeps its name"
    (Bib.text "\\mystery{x}" == "mysteryx")
  t "bib: sentence case keeps the first char, protection, and colon starts"
    (Bib.sentenceCase "The Great {DNA} Hunt: A Survey" == "The great {DNA} hunt: A survey")

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)
  let t := check ref

  utf8Checks ref
  argsChecks ref
  renderChecks ref
  lexChecks ref
  parseChecks ref
  elabDocChecks ref

  -- goldens
  runGoldens update (failures ref)

  -- dim
  t "sp pt string" ((Dim.pt 10).toPtString == "10" && (Dim.pt 3 / 2).toPtString == "1.5")
  dimChecks ref
  -- The two spellings of one length must agree: the engine's pt is the big
  -- point everywhere, so a default deck stage and \page{ width = 160mm }
  -- name the same number of sp.
  t "dim mm agrees with inch" (Dim.mm 254 == Dim.inch 10)

  kpChecks ref
  hyphenChecks ref
  walkChecks ref
  diagChecks ref
  pictureElabChecks ref
  diagVoiceChecks ref update
  allowChecks ref
  werrorChecks ref
  declChecks ref
  tokensChecks ref
  compatChecks ref
  compatIndexChecks ref
  compatConservationChecks ref
  classOptionChecks ref
  backendSuiteChecks ref
  unitChecks ref
  exprChecks ref
  wrapperChecks ref
  centeringChecks ref
  fontDiagChecks ref
  declaredFaceChecks ref
  fallbackChecks ref
  smallCapsGsubChecks ref
  iconChecks ref
  smartChecks ref
  linkHtmlChecks ref
  paletteChecks ref
  mixChecks ref
  contrastChecks ref
  themeChecks ref
  designChecks ref
  roleChecks ref
  roleInvocationChecks ref
  roleShadowChecks ref
  fontsDeclChecks ref
  fontSuiteChecks ref
  layoutSuiteChecks ref
  mathChecks ref
  bibChecks ref

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1

