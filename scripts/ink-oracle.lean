/-
The ink oracle: the external half of the artifact tier. Run from the
repository root:

  lake build TestsModules && lake env lean --run scripts/ink-oracle.lean
  lake env lean --run scripts/ink-oracle.lean --selftest

`lake test` judges the produced bytes with the engine's own reader
(Tests/Artifact.lean: the page box, the text area, the bands, the markup
watch, consecutive pages, the glyph names). That keeps the suite hermetic —
it asks nothing of what this host has installed — and it buys the one
weakness an in-tree reader always has: a reader built from the same
understanding as the writer can be wrong in the same direction twice. Every
defect this tier exists for was in fact found by an outside tool.

So this script is the corroboration, and it is deliberately not in
`lake test`: it asks Poppler (`pdftotext -bbox`) what it sees, and holds
that against what `readArtifact` saw on the same bytes. Two agreements are
checked per page — the ink extent (the tightest box containing every word)
and the text — and one verdict: whether Poppler's own numbers put any word
outside the page box, which must match the engine reader's `pageBox`
judgement fixture for fixture.

A tool not on PATH reports `untested` and exits 0: an absent Poppler is a
fact about the machine, never a pass and never a failure. A disagreement
exits 1.

Nothing is written to the repository. The comparison is extent-and-text
rather than word-for-word on purpose: Poppler groups glyphs into words by
its own spacing rules while the engine reads the writer's runs, so the two
segment differently and only their union is comparable.
-/
import Tests.Artifact

open LeanTex.Core LeanTex.Cli

/-- One `<word …>` of `pdftotext -bbox` output. Poppler's origin is the
top-left corner with y growing down, so a bound is converted against the
page height it reports. -/
structure PopWord where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  text : String
  deriving Repr, Inhabited

/-- The value of `attr="…"` in a tag, as text. -/
def attrOf (line attr : String) : Option String := do
  let after ← (line.splitOn (attr ++ "=\""))[1]?
  (after.splitOn "\"")[0]?

/-- A decimal number as a `Float`, sign and fraction only — the shape
`pdftotext -bbox` writes (`149.723000`). Written out rather than borrowed
so the oracle's own reading has no dependency to be wrong about. -/
def parseFloat (s : String) : Option Float := do
  let (neg, body) := match s.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | cs => (false, cs)
  let parts := (String.ofList body).splitOn "."
  let ip ← (parts[0]?).bind String.toNat?
  let frac : Float ← match parts[1]? with
    | none => pure 0.0
    | some f =>
      if f.isEmpty then pure 0.0
      else do
        let d ← f.toNat?
        pure ((Float.ofNat d) / (Float.ofNat (10 ^ f.length)))
  let v := (Float.ofNat ip) + frac
  return if neg then -v else v

def floatAttr (line attr : String) : Option Float :=
  (attrOf line attr).bind parseFloat

/-- The text between `>` and `</word>`, with the three XML entities the
tool emits decoded. -/
def wordText (line : String) : String :=
  let afterTag := String.intercalate ">" ((line.splitOn ">").drop 1)
  let body := ((afterTag.splitOn "</word>")[0]?).getD ""
  ((body.replace "&amp;" "&").replace "&lt;" "<").replace "&gt;" ">"

/-- One page of `pdftotext -bbox`: its declared height and its words. -/
structure PopPage where
  height : Float
  words : Array PopWord
  deriving Repr, Inhabited

def parseBbox (xml : String) : Array PopPage := Id.run do
  let mut out : Array PopPage := #[]
  let mut cur : Option PopPage := none
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<page " then
      if let some p := cur then out := out.push p
      cur := some { height := (floatAttr line "height").getD 0, words := #[] }
    else if line.startsWith "<word " then
      match cur, floatAttr line "xMin", floatAttr line "yMin",
        floatAttr line "xMax", floatAttr line "yMax" with
      | some p, some x0, some y0, some x1, some y1 =>
        let w : PopWord := { x0 := x0, y0 := y0, x1 := x1, y1 := y1, text := wordText line }
        cur := some { p with words := p.words.push w }
      | _, _, _, _, _ => pure ()
  if let some p := cur then out := out.push p
  return out

/-- The tightest box containing every word, in PDF user space (y up). -/
def popExtent (p : PopPage) : Option (Float × Float × Float × Float) := Id.run do
  let some w0 := p.words[0]? | return none
  let mut x0 := w0.x0
  let mut x1 := w0.x1
  let mut yl := p.height - w0.y1
  let mut yh := p.height - w0.y0
  for w in p.words do
    x0 := min x0 w.x0
    x1 := max x1 w.x1
    yl := min yl (p.height - w.y1)
    yh := max yh (p.height - w.y0)
  return some (x0, yl, x1, yh)

/-- The same extent off the engine reader's runs, in the same space. -/
def artExtent (p : ArtPage) : Option (Float × Float × Float × Float) := Id.run do
  let some r0 := p.runs[0]? | return none
  let f (v : Dim.Sp) : Float := (Float.ofInt v) / 65536.0
  let mut x0 := f r0.x
  let mut x1 := f r0.x1
  let mut yl := f r0.bottom
  let mut yh := f r0.top
  for r in p.runs do
    x0 := min x0 (f r.x)
    x1 := max x1 (f r.x1)
    yl := min yl (f r.bottom)
    yh := max yh (f r.top)
  return some (x0, yl, x1, yh)

/-- How far the two readings of one page's ink extent may differ. Two
points: Poppler measures a word's painted glyph outlines while the engine
reads the writer's advance box and the descriptor's declared ascent and
descent, so the two bound the same ink differently by design — the point of
the comparison is that neither is off by a *placement*, which is what every
defect this tier exists for was. -/
def extentTolerance : Float := 2.0

/-- Letters and digits only, lowercased and sorted: the comparison the two
readings can both satisfy. Poppler joins a hyphenated break, inserts spaces
by its own rules, and returns words in *its* reading order (columns, table
cells and floats reordered), while the engine reads the writer's runs in
painting order. So the content is comparable and the order is not, and this
sorts to say only the comparable thing. -/
def inkLetters (s : String) : String :=
  String.ofList ((s.toList.filter fun c => c.isAlphanum).map Char.toLower).mergeSort

structure Verdict where
  fixture : String
  pages : Nat
  extentGaps : Array String
  textGap : Option String
  offPageDisagreement : Option String
  deriving Inhabited

def Verdict.ok (v : Verdict) : Bool :=
  v.extentGaps.isEmpty && v.textGap.isNone && v.offPageDisagreement.isNone

def haveTool (name : String) : IO Bool := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  return out.exitCode == 0

/-- The self-test: the parser on hand-written output, and the extent
arithmetic, so the oracle's own reading is checked with no tool present. -/
def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  let xml := "<doc>\n  <page width=\"612.000000\" height=\"792.000000\">\n\
    <word xMin=\"10.500000\" yMin=\"72.000000\" xMax=\"40.250000\" yMax=\"85.000000\">Ab&amp;c</word>\n\
    <word xMin=\"5.000000\" yMin=\"100.000000\" xMax=\"20.000000\" yMax=\"110.000000\">d-e</word>\n\
  </page>\n</doc>"
  let ps := parseBbox xml
  unless ps.size == 1 do bad := bad.push s!"one page expected, got {ps.size}"
  if let some p := ps[0]? then
    unless p.words.size == 2 do bad := bad.push s!"two words expected, got {p.words.size}"
    unless p.height == 792.0 do bad := bad.push "page height"
    unless (p.words[0]?.map (·.text)) == some "Ab&c" do
      bad := bad.push s!"entity decode: {(p.words[0]?.map (·.text))}"
    match popExtent p with
    | some (x0, yl, x1, yh) =>
      unless x0 == 5.0 && x1 == 40.25 do bad := bad.push s!"x extent {x0}..{x1}"
      -- y flips: the lower bound is 792 - 110, the upper 792 - 72.
      unless yl == 682.0 && yh == 720.0 do bad := bad.push s!"y extent {yl}..{yh}"
    | none => bad := bad.push "no extent"
  unless inkLetters "Ab&c d-e" == "abcde" do bad := bad.push "inkLetters"
  unless inkLetters "ba" == inkLetters "ab" do bad := bad.push "inkLetters order-insensitive"
  unless (parseBbox "<doc></doc>").isEmpty do bad := bad.push "empty doc"
  if bad.isEmpty then
    IO.println "ink-oracle --selftest: all passed"
    return 0
  for b in bad do IO.eprintln s!"FAIL {b}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  unless ← haveTool "pdftotext" do
    IO.println "ink-oracle: pdftotext not on PATH — untested (never a pass)"
    return 0
  let pats := Hyphen.english.get
  let some fontData ← findFont | throw (IO.userError "ink-oracle: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "ink-oracle: corpus font unparsable")
  let oneFace := oneFaceOf font
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
  let dir ← IO.FS.createTempDir
  let mut verdicts : Array Verdict := #[]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, diags) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let store ← corpusStore doc
    let out := layoutOf fs doc geom (some pats) store
    let pdf := driverPdf fs geom doc out store
    let pdfPath := dir / s!"{n}.pdf"
    IO.FS.writeBinFile pdfPath pdf
    let read := readArtifact pdf
    if let .error e := read then
      IO.eprintln s!"ink-oracle {n}: the engine reader refused its own bytes: {e}"
      return 1
    let pages := read.toOption.getD #[]
    let args : Array String := #["-bbox", pdfPath.toString, "-"]
    let r ← IO.Process.output { cmd := "pdftotext", args := args }
    if r.exitCode != 0 then
      IO.eprintln s!"ink-oracle {n}: pdftotext exited {r.exitCode}"
      return 1
    let pops := parseBbox r.stdout
    let mut gaps : Array String := #[]
    if pops.size != pages.size then
      gaps := gaps.push s!"page count: poppler {pops.size}, engine {pages.size}"
    for i in [0:min pops.size pages.size] do
      match popExtent pops[i]!, artExtent pages[i]! with
      | some (px0, py0, px1, py1), some (ax0, ay0, ax1, ay1) =>
        let off := fun (a b : Float) => (a - b).abs
        let worst := max (off px0 ax0) (max (off py0 ay0) (max (off px1 ax1) (off py1 ay1)))
        if extentTolerance < worst then
          gaps := gaps.push s!"p{i + 1} extent off by {worst}: poppler [{px0} {py0} {px1} {py1}] engine [{ax0} {ay0} {ax1} {ay1}]"
      | _, _ => pure ()
    -- The text both readings can compare: letters and digits, in order.
    let popText := inkLetters (String.join (pops.toList.flatMap fun p =>
      p.words.toList.map (·.text)))
    let artText := inkLetters (String.join (pages.toList.flatMap fun p =>
      p.runs.toList.map (·.text)))
    let textGap : Option String :=
      if popText == artText then none
      else some s!"letters differ: poppler {popText.length}, engine {artText.length}"
    -- The page-box verdict, from Poppler's own numbers, against the
    -- engine reader's. `accounted` is read the way the suite reads it.
    let accounted := artAccounted (diags ++ out.diags)
    let popOff := pops.toList.any fun p =>
      p.words.toList.any fun w => w.x0 < -0.01 || w.y0 < -0.01
    let reading : ArtReading :=
      { pages := pages, area := artBodyArea geom, accounted := accounted }
    let engineOff := !(artOffences reading .pageBox).isEmpty
    let offGap : Option String :=
      if popOff == engineOff || accounted then none
      else some s!"off-page: poppler {popOff}, engine {engineOff}"
    verdicts := verdicts.push { fixture := n, pages := pages.size, extentGaps := gaps,
                                textGap := textGap, offPageDisagreement := offGap }
  let bad := verdicts.filter fun v => !v.ok
  IO.println s!"ink-oracle: {verdicts.size} fixtures, \
{verdicts.foldl (fun a v => a + v.pages) 0} pages, {bad.size} disagreeing"
  for v in bad do
    IO.eprintln s!"DISAGREE {v.fixture}"
    for g in v.extentGaps do IO.eprintln s!"    {g}"
    if let some g := v.textGap then IO.eprintln s!"    {g}"
    if let some g := v.offPageDisagreement then IO.eprintln s!"    {g}"
  return if bad.isEmpty then 0 else 1
