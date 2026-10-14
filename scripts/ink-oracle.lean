/-
The ink oracle: Poppler's ink extent, text and off-page verdict per corpus page against
`readArtifact`'s; without Poppler it reports `untested` and exits 0, a disagreement exits 1.
Usage: lake build ScriptsModules && lake env lean --run scripts/ink-oracle.lean [--selftest]
-/
import LeanTex.Cli.FontDiscovery
import Tests.Artifact
import scripts.ToolDump

open LeanTex.Core LeanTex.Cli

/-- One `<word …>` of `pdftotext -bbox` output, its bounds converted from Poppler's
top-left origin against the page height. -/
structure PopWord where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  text : String
  deriving Repr, Inhabited

def floatAttr (line attr : String) : Option Float :=
  (attrOf line attr).bind parseFloat

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

/-- How far the two readings of a page's ink extent may differ: Poppler bounds painted
outlines and the engine advance boxes and declared ascent and descent, so only a placement
error exceeds two points. -/
def extentTolerance : Float := 2.0

/-- Letters and digits only, lowercased and sorted, since Poppler's word order and spacing
differ from the writer's painting order. -/
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

/-- The self-test: the parser on hand-written output and the extent arithmetic, needing no
tool. -/
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
  let numbers : List (String × Float) := [("0.0197563", 0.0197563), ("1.2e-05", 0.000012),
    ("1.2e+05", 120000.0), ("-12.5", -12.5), ("+3", 3.0), ("72.000000", 72.0), ("1.", 1.0),
    (".5", 0.5)]
  for (text, v) in numbers do
    unless (parseFloat text).any (fun x => Float.abs (x - v) ≤ 1e-9 * max 1.0 (Float.abs v)) do
      bad := bad.push s!"parseFloat {text}: {parseFloat text}"
  for text in ["", ".", "-", "a.b.c", "1e", "1e2.5", "1_000", "0.1_5", "1e1_0", "e5"] do
    unless parseFloat text == none do bad := bad.push s!"parseFloat refuses {text.quote}"
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
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let dir ← IO.FS.createTempDir
  let mut verdicts : Array Verdict := #[]
  for n in goldenNames do
    let (doc, diags) ← goldenDoc n
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
    let popText := inkLetters (String.join (pops.toList.flatMap fun p =>
      p.words.toList.map (·.text)))
    let artText := inkLetters (String.join (pages.toList.flatMap fun p =>
      p.runs.toList.map (·.text)))
    let textGap : Option String :=
      if popText == artText then none
      else some s!"letters differ: poppler {popText.length}, engine {artText.length}"
    -- The page-box verdict from Poppler's numbers, against the engine reader's.
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
