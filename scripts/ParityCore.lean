/-
The cross-engine parity ladder, shared half: the rung vocabulary, the
declared-divergence registry, the reference sidecar, and the baseline
ratchet. Two scripts read this module and nothing else shares it —
`scripts/parity-regen.lean`, which runs `lualatex`, and
`scripts/parity.lean`, which never does.

The split is the hermeticity rule: fixtures and tests never depend on what
this host has installed, and a parity ladder needs a reference from another
engine. So the reference is a *committed artifact* with a provenance
sidecar, the regenerator is the only thing that invokes the other engine,
and the gate reads bytes already in the tree.

Why the gate reads the reference with the engine's own PDF reader rather
than a tool: `PdfRead` already follows xref streams and object streams
(which is what a modern reference uses), and that reader is independently
corroborated against Poppler on the engine's own output by
`scripts/ink-oracle.lean`. Reading both sides with one reader also means a
disagreement is a disagreement about the documents, never about two
readers.
-/
import Tests.Artifact

open LeanTex.Core

namespace Parity

/-! ## The rungs -/

/-- One rung of the ladder. Cumulative: a fixture's recorded level is the
number of rungs that hold, counted from the bottom, so a rung is only ever
asked about a fixture whose lower rungs hold.

The names say what is compared, not how well it went: `build` compares
nothing, it establishes the denominator. -/
inductive Rung where
  /-- Both engines produce a document: the reference compiled under
  `-halt-on-error`, and the engine raised no error diagnostic. Only then is
  the fixture comparable at all. -/
  | build
  /-- The two artifacts carry the same number of pages. -/
  | pages
  /-- Page for page, the same *multiset* of inked Unicode scalars. -/
  | census
  /-- Page for page, the same *sequence* of inked Unicode scalars. -/
  | order
  /-- Page for page, the same partition of that sequence into lines: the
  same words on the same line, line for line.

  This rung exists because the one below it cannot see line breaking.
  Measured 2026-09-25 on `pagebreak`: the reading-order rung held while the
  two sides broke page 2's first line at different words — the scalar
  sequence is identical either way, so a multiset cannot see it and a
  sequence cannot either. It is the cheap half of what a geometry rung
  would check, and unlike a geometry rung it needs no advance widths, so it
  is not blocked on reading the reference's own `/W`. -/
  | lines
  deriving Repr, BEq, Inhabited

def Rung.all : List Rung := [.build, .pages, .census, .order, .lines]

def Rung.tag : Rung → String
  | .build => "T0"
  | .pages => "T1"
  | .census => "T2"
  | .order => "T3"
  | .lines => "T4"

def Rung.what : Rung → String
  | .build => "both engines produce a document"
  | .pages => "page count agrees"
  | .census => "per-page glyph census agrees"
  | .order => "per-page reading order agrees"
  | .lines => "per-page line partition agrees"

/-- The level a fixture whose reference does not compile records. Such a
fixture is outside the denominator: nothing about the engine is claimed by
it, and it may not be silently dropped either. -/
def refuses : Int := -1

/-- A level as it reads in the baseline and in a report. -/
def levelName (l : Int) : String :=
  if l < 0 then "refuses"
  else
    match (Rung.all.drop (l.toNat)).head? with
    | some r => s!"{l} (next: {r.tag})"
    | none => s!"{l} (top)"

/-! ## The declared-divergence registry

leantex diverges from LaTeX deliberately in ways that are recorded as prose
today. A general oracle that flagged all of them on every run would be
switched off within a week, so each divergence a rung could meet is a
constructor here with a reason and a scope: which rungs it may excuse, and
whether it is on this ladder's subject at all.

The registry lives beside the ladder rather than inside `LeanTex/` because
what it classifies is a *comparison*, not a document: nothing the engine
emits reads it, and a divergence only means something once a second engine
is in the room. If a rung ever needs the engine itself to declare one, that
is the moment it moves into the tree. -/
inductive Divergence where
  /-- A `pt` is not a `pt`: the engine measures in PDF big points (1⁄72 in)
  and LaTeX in TeX points (1⁄72.27 in), so a "10 pt" document is 0.375 %
  larger here. Measured on a paired fixture: the reference set at `10pt`
  reads back as size 9.9626 and leading 11.955, against the engine's 10 and
  12 exactly. Pinned away rather than tolerated — a paired reference
  declares its geometry in `bp` — so it excuses nothing. -/
  | pointUnit
  /-- The first baseline of a text block sits in a different place: the two
  engines derive it from the top margin by their own rules. Measured at
  0.725 pt on a paired fixture with every declared quantity matched and the
  units pinned. Uniform down the page (every later baseline differs by the
  same amount), so it is an origin offset, not drift. -/
  | firstBaseline
  /-- Left to itself, the engine sets an article's measure from a
  copy-fitting table and LaTeX sets it from the class default; the two are
  not the same width. A fixture that declares its geometry never meets
  this. -/
  | defaultMeasure
  /-- Neither side's glyph runs are words. The engine emits a run per
  hyphenation opportunity even where it does not break; the reference emits
  a run per kern pair. Measured on one paired line: 23 runs against 17, for
  identical text. Any rung that reasons about runs as units is reasoning
  about an artefact of two writers, so the ladder compares scalars and
  never runs. -/
  | runSegmentation
  /-- The page number is in a different place. Measured at 3.18 pt
  vertically on a paired fixture. It carries the same glyph, so it reaches
  the census and order rungs and not the geometry ones. -/
  | numberPlacement
  /-- Colour and shade: the covered-shade blend, the alert dimming, the
  WCAG contrast contracts. Permanently out of this ladder's scope — three
  of these are colour-model divergences by construction, and the engine's
  contrast contracts are a *stronger* claim than parity with LaTeX, so a
  rung that demanded agreement here would be demanding that the engine get
  worse. The ladder never reads colour. -/
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

/-- Which rungs this divergence may excuse a disagreement on. Empty means
it cannot excuse anything the ladder currently checks — either because the
pairing pins it away, or because no rung reads the quantity it is about. -/
def Divergence.excuses : Divergence → List Rung
  | .pointUnit => []
  | .firstBaseline => []
  | .defaultMeasure => [.pages, .census, .order, .lines]
  | .runSegmentation => []
  | .numberPlacement => []
  | .colourModel => []

/-- Is this divergence outside the ladder's subject for good, rather than
merely unmet by today's rungs? -/
def Divergence.outOfScope : Divergence → Bool
  | .colourModel => true
  | _ => false

def Divergence.why : Divergence → String
  | .pointUnit => "pinned away: a paired reference declares its geometry in bp"
  | .firstBaseline => "an origin offset; no rung reads absolute position yet"
  | .defaultMeasure => "a different measure rebreaks lines, which moves the page count, the per-page census, the reading order and the line partition all at once"
  | .runSegmentation => "the ladder compares scalars, never runs"
  | .numberPlacement => "same glyph, different place; no rung reads absolute position yet"
  | .colourModel => "out of scope permanently: the ladder never reads colour"

def Divergence.ofName? (s : String) : Option Divergence :=
  Divergence.all.find? (·.name == s)

/-- What a fixture declares about its own pairing, read from its `%
diverges:` lines — one registry name each. A fixture that stops below the
top without declaring a divergence that excuses the rung it stopped on has
an *unexplained* stop, and one that declares a divergence while reaching the
top has a stale declaration. Both are reported; the second is a failure, for
the reason the ratchet's rise is one — a declaration nobody removed when the
engine improved is a declaration that will excuse the next regression.

This is the "arm of a level's definition" shape rather than a suppression
list: a declaration never changes a verdict. It says which rung a stop is
allowed to be at, and it fails when the claim and the measurement part. -/
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

/-! ## The inked-scalar readings

Both readings come off `ArtPage.runs`, which is what the *file* paints —
the pen advanced per glyph, characters from the file's own `/ToUnicode`.
Whitespace is dropped on both sides: the engine separates words by
positioning the next run, the reference sometimes by a space glyph, and a
difference in which of those a writer chose is not a difference in what the
page shows. -/

def inked (s : String) : List Char :=
  s.toList.filter fun c => !c.isWhitespace

/-- Every scalar a page inks, in painting order. -/
def orderKey (p : ArtPage) : String :=
  String.ofList (inked (String.join (p.runs.toList.map (·.text))))

/-- Every scalar a page inks, sorted: the multiset, spelled so two
readings can be compared by one equality. -/
def censusKey (p : ArtPage) : String :=
  String.ofList (inked (String.join (p.runs.toList.map (·.text)))).mergeSort

/-- A page's lines, in painting order: the runs grouped by baseline, each
line's scalars joined. Both writers position each line once and paint down
the page, so first appearance is reading order and the exact `y` is the
grouping key — no tolerance, because the question is which words share a
line, not where the line is.

Whitespace is dropped per line, after grouping, for the reason `inked`
gives: which side spelled a space as a glyph is a writer's choice. -/
def linesOf (p : ArtPage) : Array String := Id.run do
  let mut ys : Array Dim.Sp := #[]
  let mut texts : Array String := #[]
  for r in p.runs do
    match ys.findIdx? (· == r.y) with
    | some i => texts := texts.set! i (texts[i]! ++ r.text)
    | none =>
      ys := ys.push r.y
      texts := texts.push r.text
  let mut out : Array String := #[]
  for t in texts do
    let s := String.ofList (inked t)
    unless s.isEmpty do out := out.push s
  return out

/-- A page's line partition as one comparable string: the lines in reading
order, separated by a scalar no line can contain. -/
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

/-! ## The reference sidecar

One file per fixture, `<name>.ref.txt`, `key: value` per line. Not JSON:
the repository has no JSON reader, and a hand-rolled one would be a
dependency to be wrong about in the one place whose whole job is to be
trustworthy.

The pin is `Flate.contentKey` — the repository's own content address, the
same one the picture cache keys an external tool's answer by. Deliberately
not sha256: the gate must verify the pin with nothing installed, and a
second hash the gate could not check would be decoration. The pin's job is
to catch drift between a source and the reference built from it, which is
what it does. -/
structure Sidecar where
  fixture : String
  /-- Did the reference engine compile the reference source at all? `false`
  puts the fixture outside the denominator, and is recorded rather than
  inferred from a missing file. -/
  compiles : Bool
  pdfKey : String
  pdfSize : Nat
  /-- The content key of `<name>.tex`: the engine's half of the pairing. -/
  srcKey : String
  /-- The content key of `<name>.ref.tex`: the reference's half. -/
  refSrcKey : String
  engine : String
  argv : String
  pages : Nat
  overfull : Nat
  provenance : String
  deriving Repr, Inhabited

def sidecarKeys : List String :=
  ["fixture", "compiles", "pdf-key", "pdf-size", "src-key", "ref-src-key",
   "engine", "argv", "pages", "overfull", "provenance"]

def Sidecar.render (s : Sidecar) : String :=
  String.intercalate "\n"
    [s!"fixture: {s.fixture}",
     s!"compiles: {if s.compiles then "yes" else "no"}",
     s!"pdf-key: {s.pdfKey}",
     s!"pdf-size: {s.pdfSize}",
     s!"src-key: {s.srcKey}",
     s!"ref-src-key: {s.refSrcKey}",
     s!"engine: {s.engine}",
     s!"argv: {s.argv}",
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
           refSrcKey := ← need "ref-src-key"
           engine := ← need "engine"
           argv := ← need "argv"
           pages := ← nat "pages"
           overfull := ← nat "overfull"
           provenance := ← need "provenance" }

/-! ## The scoreboard and its ratchet

One integer per fixture, committed to `tests/scoreboard/parity.tsv` in the
one format every tier of the autonomy loop uses: `#` lines for provenance
(data, never gated), then `item<TAB>integer` rows, sorted and unique, higher
better. A tier regresses when a value drops or a baselined item disappears;
an item is retired only by a `# retired: <item> — <why>` line, which is a
decision somebody wrote down rather than a row somebody deleted.

The oracle is never "must match": it is "must not fall, and a rise must be
recorded". A rise is also a failure — the recorded number is stale — which
is the same shape the artifact tier's offence rows already have: a fix that
removes an offence fails until its row goes too. Without that, a rung that
rose once and fell later would look green the whole way down. -/
structure Row where
  fixture : String
  level : Int
  deriving Repr, Inhabited

/-- Where the scoreboard lives. One directory for every tier of the loop, so
a sibling tier's file sits beside this one and reads the same way. -/
def scoreboardPath : System.FilePath := "tests/scoreboard/parity.tsv"

/-- Rows sorted by name and deduplicated, which is the committed order: a
regeneration that reordered the file would show as a diff that means
nothing. -/
def renderBaseline (rows : List Row) (provenance : List String) : String :=
  let sorted := (rows.toArray.qsort (·.fixture < ·.fixture)).toList
  let uniq := sorted.foldl (fun acc r =>
    if acc.any (·.fixture == r.fixture) then acc else acc ++ [r]) []
  String.join (provenance.map (fun l => s!"# {l}\n"))
    ++ String.join (uniq.map fun r => s!"{r.fixture}\t{r.level}\n")

/-- The fixtures a scoreboard has retired, by the `# retired:` line that is
the only way to retire one. A retired fixture's row may be gone without the
ratchet calling it a fall. -/
def retiredOf (text : String) : List String :=
  (text.splitOn "\n").filterMap fun raw =>
    let l := raw.trimAscii.toString
    if l.startsWith "# retired: " then
      some ((((l.drop 11).toString.splitOn " —").head?.getD "").trimAscii.toString)
    else none

def parseBaseline (text : String) : Except String (List Row) := do
  let mut out : List Row := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "\t").filter (!·.isEmpty) with
    | [n, v] =>
      match v.trimAscii.toString.toInt? with
      | some l =>
        if out.any (·.fixture == n) then
          throw s!"the scoreboard lists {n} twice"
        out := out ++ [{ fixture := n, level := l }]
      | none => throw s!"the scoreboard row for {n} is not a number: {v}"
    | _ => throw s!"a scoreboard row is not '<fixture><TAB><level>': {repr line}"
  return out

/-- The content key of a source, spelled once so the regenerator's pin and
the gate's check cannot come apart. -/
def srcKeyOf (src : String) : String := Flate.contentKey src.toUTF8

/-- Where the parity corpus lives. -/
def parityDir : String := "tests/parity"

/-- Every fixture in the parity corpus, found by reading the directory
rather than by a list in this file: a pair dropped in and never listed
would otherwise be a fixture nothing judges. -/
def parityNames : IO (Array String) := do
  let mut out : Array String := #[]
  for e in ← System.FilePath.readDir parityDir do
    let n := e.fileName
    if n.endsWith ".tex" && !n.endsWith ".ref.tex" then
      out := out.push ((n.take (n.length - 4)).toString)
  return out.qsort (· < ·)

end Parity
