/-
The parity ladder's shared half: the levels, the declared-divergence registry, the reference
sidecar, and the content-key pins tying a committed reference to its sources.
-/
import Tests.Artifact

open LeanTex.Core

namespace Parity

/-! The levels: P0 build, P1 pages, P2 census, P3 order, P4 lines; P5 placement is
measured apart (`scripts/parity-measure.lean`), and R raster is not built. -/

/-- One level of the ladder, cumulative: a fixture's recorded level counts the levels that
hold from the bottom. -/
inductive Level where
  /-- Both engines produce a document: the reference compiled under `-halt-on-error`, and
  the engine raised no error. -/
  | build
  /-- The two artifacts carry the same number of pages. -/
  | pages
  /-- Page for page, the same *multiset* of inked Unicode scalars. -/
  | census
  /-- Page for page, the same *sequence* of inked Unicode scalars. -/
  | order
  /-- Page for page, the same partition of that sequence into lines, whitespace dropped,
  so blind to a missing interword space, which the placement level sees. -/
  | lines
  deriving Repr, BEq, Inhabited

def Level.all : List Level := [.build, .pages, .census, .order, .lines]

def Level.tag : Level → String
  | .build => "P0"
  | .pages => "P1"
  | .census => "P2"
  | .order => "P3"
  | .lines => "P4"

def Level.what : Level → String
  | .build => "both engines produce a document"
  | .pages => "page count agrees"
  | .census => "per-page glyph census agrees"
  | .order => "per-page reading order agrees"
  | .lines => "per-page line partition agrees"

/-- The level's one-word name, as the vocabulary table spells it. -/
def Level.word : Level → String
  | .build => "build"
  | .pages => "pages"
  | .census => "census"
  | .order => "order"
  | .lines => "lines"

/-- The level of a fixture whose reference does not compile: outside the denominator, and
recorded. -/
def refuses : Int := -1

/-- A level as it reads in the baseline and in a report. -/
def levelName (l : Int) : String :=
  if l < 0 then "refuses"
  else
    match (Level.all.drop (l.toNat)).head? with
    | some r => s!"{l} (next: {r.tag})"
    | none => s!"{l} (top)"

/-! The declared-divergence registry: each deliberate divergence a level could meet, with
the levels it may excuse; nothing the engine emits reads it. -/
inductive Divergence where
  /-- The engine measures in PDF big points and LaTeX in TeX points (0.375 % apart); a
  paired reference declares its geometry in `bp`, so this excuses nothing. -/
  | pointUnit
  /-- The first baseline of a text block sits elsewhere, each engine deriving it from the
  top margin by its own rule: a uniform origin offset. -/
  | firstBaseline
  /-- The engine sets an undeclared article measure from a copy-fitting table, LaTeX from
  the class default; a fixture declaring its geometry never meets this. -/
  | defaultMeasure
  /-- Neither side's glyph runs are words, so the ladder compares scalars, never runs. -/
  | runSegmentation
  /-- The page number stands elsewhere; it carries the same glyph, so it reaches the
  census and order levels only. -/
  | numberPlacement
  /-- Colour and shade, permanently out of scope: the engine's contrast contracts claim
  more than parity with LaTeX. -/
  | colourModel
  deriving Repr, BEq, Inhabited

def Divergence.all : List Divergence :=
  [.pointUnit, .firstBaseline, .defaultMeasure, .runSegmentation,
   .numberPlacement, .colourModel]

def Divergence.name : Divergence → String
  | .pointUnit => "point-unit"
  | .firstBaseline => "first-baseline"
  | .defaultMeasure => "default-measure"
  | .runSegmentation => "run-segmentation"
  | .numberPlacement => "number-placement"
  | .colourModel => "colour-model"

/-- Which levels this divergence may excuse; empty means nothing the ladder checks. -/
def Divergence.excuses : Divergence → List Level
  | .pointUnit => []
  | .firstBaseline => []
  | .defaultMeasure => [.pages, .census, .order, .lines]
  | .runSegmentation => []
  | .numberPlacement => []
  | .colourModel => []

/-- Whether this divergence lies outside the ladder's subject, rather than unmet by its
current levels. -/
def Divergence.outOfScope : Divergence → Bool
  | .colourModel => true
  | _ => false

def Divergence.why : Divergence → String
  | .pointUnit => "pinned away: a paired reference declares its geometry in bp"
  | .firstBaseline => "an origin offset; no level reads absolute position yet"
  | .defaultMeasure => "a different measure rebreaks lines, so it can move the page count, the per-page census, the reading order and the line partition; which of them it reaches is measured per fixture, never assumed"
  | .runSegmentation => "the ladder compares scalars, never runs"
  | .numberPlacement => "same glyph, different place; no level reads absolute position yet"
  | .colourModel => "out of scope permanently: the ladder never reads colour"

def Divergence.ofName? (s : String) : Option Divergence :=
  Divergence.all.find? (·.name == s)

/-- What a fixture declares about its pairing, one registry name per `% diverges:` line; a
stop below the top no declaration excuses is unexplained, and a declaration on a fixture
reaching the top is stale. -/
def declaredDivergences (src : String) : Except String (List Divergence) := do
  let mut out : List Divergence := []
  for line in src.splitOn "\n" do
    let l := line.trimAscii.toString
    unless l.startsWith "% diverges: " do continue
    let n := (l.drop 12).trimAscii.toString
    match Divergence.ofName? n with
    | some d => out := out ++ [d]
    | none => throw s!"'{n}' is not a name in the divergence registry"
  return out

/-! The inked-scalar readings, off what the file paints (`ArtPage.runs`), whitespace
dropped on both sides since how a writer spaces words is its own choice. -/

def inked (s : String) : List Char :=
  s.toList.filter fun c => !c.isWhitespace

/-- A page's lines top to bottom: runs grouped by exact baseline, in descending baseline
then ascending pen order, never painting order; a single-column reading. -/
def runLines (p : ArtPage) : Array (Array (Nat × ArtRun)) := Id.run do
  let mut ys : Array Dim.Length := #[]
  let mut groups : Array (Array (Nat × ArtRun)) := #[]
  let mut n := 0
  for r in p.runs do
    match ys.findIdx? (· == r.y) with
    | some i => groups := groups.set! i (groups[i]!.push (n, r))
    | none =>
      ys := ys.push r.y
      groups := groups.push #[(n, r)]
    n := n + 1
  let order := (Array.range ys.size).qsort fun i j => ys[j]! < ys[i]!
  let mut out : Array (Array (Nat × ArtRun)) := #[]
  for i in order do
    out := out.push (groups[i]!.qsort fun a b =>
      a.2.x < b.2.x || (a.2.x == b.2.x && a.1 < b.1))
  return out

/-- Every line a page inks, in reading order, whitespace dropped, empty lines dropped. -/
def linesOf (p : ArtPage) : Array String := Id.run do
  let mut out : Array String := #[]
  for line in runLines p do
    let s := String.ofList (inked (String.join (line.toList.map (·.2.text))))
    unless s.isEmpty do out := out.push s
  return out

/-- Every scalar a page inks, in reading order (`linesOf` joined); blind to how the
scalars split into lines. -/
def orderKey (p : ArtPage) : String := String.join (linesOf p).toList

/-- Every scalar a page inks, sorted: the multiset, blind to order. -/
def censusKey (p : ArtPage) : String :=
  String.ofList (inked (String.join (p.runs.toList.map (·.text)))).mergeSort

/-- A page's line partition as one comparable string. -/
def lineKey (p : ArtPage) : String :=
  String.intercalate "\n" (linesOf p).toList

/-- Where two strings first differ, for a report that names the page rather
than only failing it. -/
def firstGap (a b : String) : String := Id.run do
  let x := a.toList.toArray
  let y := b.toList.toArray
  let n := min x.size y.size
  for i in [0:n] do
    if x[i]? != y[i]? then
      return s!"offset {i}: engine {repr (x[i]?)}, reference {repr (y[i]?)}"
  if x.size == y.size then return "no difference"
  return s!"the readings agree for {n} scalars, then one runs on: \
engine {x.size}, reference {y.size}"

/-! The reference sidecar: one `<name>.ref.txt` per fixture, `key: value` per line, pinned
by `Flate.contentKey`, which the gate verifies with nothing installed. -/
structure Sidecar where
  fixture : String
  /-- Whether the reference engine compiled the reference source; `false` puts the fixture
  outside the denominator. -/
  compiles : Bool
  pdfKey : String
  pdfSize : Nat
  /-- The content key of `<name>.tex`: the engine's half of the pairing. -/
  srcKey : String
  /-- The content key of `<name>.tex` with its comment lines dropped, so `--repin` can
  accept an edit that cannot move a glyph. -/
  srcBodyKey : String
  /-- The content key of `<name>.ref.tex`: the reference's half. -/
  refSrcKey : String
  engine : String
  /-- The LaTeX format the run loaded, from the log's `LaTeX2e <date>` line. -/
  format : String
  argv : String
  /-- Every in-repo file the run read, `path=key` per item, from `-recorder`'s input
  list. -/
  inputs : String
  pages : Nat
  overfull : Nat
  provenance : String
  deriving Repr, Inhabited

def Sidecar.render (s : Sidecar) : String :=
  String.intercalate "\n"
    [s!"fixture: {s.fixture}",
     s!"compiles: {if s.compiles then "yes" else "no"}",
     s!"pdf-key: {s.pdfKey}",
     s!"pdf-size: {s.pdfSize}",
     s!"src-key: {s.srcKey}",
     s!"src-body-key: {s.srcBodyKey}",
     s!"ref-src-key: {s.refSrcKey}",
     s!"engine: {s.engine}",
     s!"format: {s.format}",
     s!"argv: {s.argv}",
     s!"inputs: {s.inputs}",
     s!"pages: {s.pages}",
     s!"overfull: {s.overfull}",
     s!"provenance: {s.provenance}"] ++ "\n"

private def fieldOf (lines : List String) (key : String) : Option String :=
  (lines.find? (·.startsWith (key ++ ":"))).map fun l =>
    (l.drop (key.length + 1)).trimAscii.toString

def Sidecar.parse (text : String) : Except String Sidecar := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  let need (k : String) : Except String String :=
    match fieldOf lines k with
    | some v => .ok v
    | none => .error s!"the sidecar has no '{k}' line"
  let nat (k : String) : Except String Nat := do
    let v ← need k
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"the sidecar's '{k}' is not a number: {v}"
  return { fixture := ← need "fixture"
           compiles := (← need "compiles") == "yes"
           pdfKey := ← need "pdf-key"
           pdfSize := ← nat "pdf-size"
           srcKey := ← need "src-key"
           srcBodyKey := ← need "src-body-key"
           refSrcKey := ← need "ref-src-key"
           engine := ← need "engine"
           format := ← need "format"
           argv := ← need "argv"
           inputs := ← need "inputs"
           pages := ← nat "pages"
           overfull := ← nat "overfull"
           provenance := ← need "provenance" }

/-! The pins: content keys tying a committed reference to the two sources it was built
from. -/

def srcKeyOf (src : String) : String := Flate.contentKey src.toUTF8

/-- A source with its whole-line comments dropped; a trailing comment on a line of content
still moves the key. -/
def bodyOf (src : String) : String :=
  String.intercalate "\n"
    ((src.splitOn "\n").filter fun l => !(l.trimAscii.toString.startsWith "%"))

/-- Whether the engine's own lexer captures any of this source raw, where a `%` line is
text. -/
def lexesVerbatim (src : String) : Bool :=
  (Lex.lex "parity" src).1.any fun t =>
    match t.tok with
    | .verb _ _ => true
    | _ => false

/-- What `src-body-key` pins: a source the lexer reads any part of raw is pinned whole, so
every edit to it needs a fresh reference. -/
def srcBodyKeyOf (src : String) : String :=
  if lexesVerbatim src then srcKeyOf src else srcKeyOf (bodyOf src)

/-- What `--repin` may do to one sidecar. -/
inductive Repin where
  | unnecessary
  | repinned (side : Sidecar)
  | refused (why : String)
  deriving Inhabited

/-- Re-pin the engine's half of a pairing without the reference engine, only when the
reference source, its bytes and every pinned input are as recorded and the engine's source
moved only in comment lines. -/
def repinDecision (side : Sidecar) (src refSrc : String)
    (refKey : String) (refSize : Nat) (inputsMoved : List String) : Repin :=
  if srcKeyOf src == side.srcKey then .unnecessary
  else if srcBodyKeyOf src != side.srcBodyKey then
    .refused "the document changed, not only its comments — build a new reference"
  else if srcKeyOf refSrc != side.refSrcKey then
    .refused "the reference source changed too — build a new reference"
  else if side.compiles && (refKey != side.pdfKey || refSize != side.pdfSize) then
    .refused "the committed reference is not the one the sidecar records"
  else match inputsMoved with
    | p :: _ => .refused s!"{p} has changed since the reference read it"
    | [] => .repinned { side with srcKey := srcKeyOf src }

/-- The side files the reference engine leaves, which are no reference and no input. -/
def refLitter : List String :=
  [".ref.aux", ".ref.log", ".ref.out", ".ref.toc", ".ref.nav", ".ref.snm", ".ref.fls"]

/-- The `inputs:` field back as `path`, `key` pairs; an item that is not exactly one `=`
is dropped. -/
def inputPins (s : String) : List (String × String) :=
  (s.splitOn " ").filterMap fun item =>
    match item.trimAscii.toString.splitOn "=" with
    | [p, k] => if p.isEmpty || k.isEmpty then none else some (p, k)
    | _ => none

/-- Where the parity corpus lives. -/
def parityDir : String := "testdata/parity"

/-- Every fixture in the parity corpus, found by reading the directory. -/
def parityNames : IO (Array String) := do
  let mut out : Array String := #[]
  for e in ← System.FilePath.readDir parityDir do
    let n := e.fileName
    if n.endsWith ".tex" && !n.endsWith ".ref.tex" then
      out := out.push ((n.take (n.length - 4)).toString)
  return out.qsort (· < ·)

/-- A page's glyph origins by line, each glyph with the offset in its line's character
stream where it starts, its identity across writers. -/
def placedLines (p : ArtPage) : Array (Array (Nat × Dim.Length × Dim.Length × String)) := Id.run do
  let mut out : Array (Array (Nat × Dim.Length × Dim.Length × String)) := #[]
  for line in runLines p do
    let mut glyphs : Array (Nat × Dim.Length × Dim.Length × String) := #[]
    let mut off := 0
    for (_, r) in line do
      for (x, t) in r.glyphs do
        let inkedT := String.ofList (inked t)
        unless inkedT.isEmpty do
          glyphs := glyphs.push (off, x, r.y, inkedT)
          off := off + inkedT.length
    unless glyphs.isEmpty do out := out.push glyphs
  return out

/-- The pairing a placement claim measures over: glyphs matched line for line by stream
offset and spelling; a glyph spelled differently is skipped on both sides and counted. -/
def placePairs (engine reference : ArtPage) :
    Array ((Dim.Length × Dim.Length) × (Dim.Length × Dim.Length)) × Nat := Id.run do
  let el := placedLines engine
  let rl := placedLines reference
  let mut pairs : Array ((Dim.Length × Dim.Length) × (Dim.Length × Dim.Length)) := #[]
  let mut skipped := 0
  for li in [0:min el.size rl.size] do
    let a := el[li]!
    let b := rl[li]!
    let mut i := 0
    let mut j := 0
    for _ in [0:a.size + b.size + 1] do
      if a.size ≤ i || b.size ≤ j then break
      let (ao, ax, ay, atext) := a[i]!
      let (bo, bx, byy, btext) := b[j]!
      if ao == bo && atext == btext then
        pairs := pairs.push ((ax, ay), (bx, byy))
        i := i + 1
        j := j + 1
      else if ao ≤ bo then
        skipped := skipped + 1
        i := i + 1
      else
        skipped := skipped + 1
        j := j + 1
    skipped := skipped + (a.size - i) + (b.size - j)
  return (pairs, skipped)

/-- A sorted list's value at a percentile, for a distribution report. -/
def atPercentile (xs : Array Dim.Length) (pct : Nat) : Dim.Length :=
  if xs.isEmpty then 0
  else
    let s := xs.qsort (· < ·)
    s[min (s.size - 1) (s.size * pct / 100)]!

end Parity
