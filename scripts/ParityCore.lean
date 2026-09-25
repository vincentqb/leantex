/-
The cross-engine parity ladder, shared half: the level vocabulary, the
declared-divergence registry, the reference sidecar, and the pins that tie
a committed reference to its sources. Two scripts read this module and
nothing else shares it — `scripts/parity-regen.lean`, which runs `lualatex`,
and `scripts/parity.lean`, which never does. The baseline ratchet is not
here: the tier is held by `Scoreboard.ratchet`, the one ratchet every tier
shares.

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

/-! ## The levels

P0–P5 plus R, one vocabulary: P0 build, P1 pages, P2 census, P3 order,
P4 lines, P5 placement, R raster. P5 and R are not built — placement is
measured and deferred (`scripts/parity-measure.lean`), and raster would be
printed and never gated — so `Level` has the five that are. -/

/-- One level of the ladder. Cumulative: a fixture's recorded level is the
number of levels that hold, counted from the bottom, so a level is only ever
asked about a fixture whose lower levels hold.

The names say what is compared, not how well it went: `build` compares
nothing, it establishes the denominator. -/
inductive Level where
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
  same scalars on the same line, line for line.

  Not the same *words*: whitespace is dropped before the comparison,
  because which side spells a space as a glyph and which positions the next
  run is a writer's choice. So "foo bar" and "foobar" agree here, and a
  missing interword space is a difference the placement level sees, where
  the gap geometry is.

  This level exists because the one below it cannot see line breaking.
  Measured 2026-09-25 on `pagebreak`: the reading-order level held while the
  two sides broke page 2's first line at different words — the scalar
  sequence is identical either way, so a multiset cannot see it and a
  sequence cannot either. It is the cheap half of what a geometry level
  would check, and unlike a geometry level it needs no advance widths. -/
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

/-- The level a fixture whose reference does not compile records. Such a
fixture is outside the denominator: nothing about the engine is claimed by
it, and it may not be silently dropped either. -/
def refuses : Int := -1

/-- A level as it reads in the baseline and in a report. -/
def levelName (l : Int) : String :=
  if l < 0 then "refuses"
  else
    match (Level.all.drop (l.toNat)).head? with
    | some r => s!"{l} (next: {r.tag})"
    | none => s!"{l} (top)"

/-! ## The declared-divergence registry

leantex diverges from LaTeX deliberately in ways that are recorded as prose
today. A general oracle that flagged all of them on every run would be
switched off within a week, so each divergence a level could meet is a
constructor here with a reason and a scope: which levels it may excuse, and
whether it is on this ladder's subject at all.

The registry lives beside the ladder rather than inside `LeanTex/` because
what it classifies is a *comparison*, not a document: nothing the engine
emits reads it, and a divergence only means something once a second engine
is in the room. If a level ever needs the engine itself to declare one, that
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
  identical text. Any level that reasons about runs as units is reasoning
  about an artefact of two writers, so the ladder compares scalars and
  never runs. -/
  | runSegmentation
  /-- The page number is in a different place. Measured at 3.18 pt
  vertically on a paired fixture. It carries the same glyph, so it reaches
  the census and order levels and not the geometry ones. -/
  | numberPlacement
  /-- Colour and shade: the covered-shade blend, the alert dimming, the
  WCAG contrast contracts. Permanently out of this ladder's scope — three
  of these are colour-model divergences by construction, and the engine's
  contrast contracts are a *stronger* claim than parity with LaTeX, so a
  level that demanded agreement here would be demanding that the engine get
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

/-- Which levels this divergence may excuse a disagreement on. Empty means
it cannot excuse anything the ladder currently checks — either because the
pairing pins it away, or because no level reads the quantity it is about. -/
def Divergence.excuses : Divergence → List Level
  | .pointUnit => []
  | .firstBaseline => []
  | .defaultMeasure => [.pages, .census, .order, .lines]
  | .runSegmentation => []
  | .numberPlacement => []
  | .colourModel => []

/-- Is this divergence outside the ladder's subject for good, rather than
merely unmet by today's levels? -/
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

/-- What a fixture declares about its own pairing, read from its `%
diverges:` lines — one registry name each. A fixture that stops below the
top without declaring a divergence that excuses the level it stopped on has
an *unexplained* stop, and one that declares a divergence while reaching the
top has a stale declaration. Both are reported; the second is a failure, for
the reason the ratchet's rise is one — a declaration nobody removed when the
engine improved is a declaration that will excuse the next regression.

This is the "arm of a level's definition" shape rather than a suppression
list: a declaration never changes a verdict. It says which level a stop is
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

/-- A page's lines, top to bottom: the runs grouped by exact baseline, each
group's runs left to right, each line's scalars joined.

The grouping key is the exact `y`, with no tolerance, because the question
is which scalars share a line and not where the line is. The *order* is the
geometry, not the painting: sorted by descending baseline, then ascending
pen. Painting order is what a writer chose — a float or a footnote one
writer paints at its source position and places elsewhere reverses it — so
two pages carrying the same lines stacked in a different vertical order
would read identically off paint order and do not read identically here.

Whitespace is dropped per line, after grouping, for the reason `inked`
gives: which side spelled a space as a glyph is a writer's choice.

This is a single-column reading order. A two-column page's baselines
interleave the columns, so `Level.order` is not asking about such a page
yet; the fixture that first sets two columns needs a column-aware reading
or a declared divergence, and the ladder will say so by disagreeing. -/
def linesOf (p : ArtPage) : Array String := Id.run do
  let mut ys : Array Dim.Sp := #[]
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
  let mut out : Array String := #[]
  for i in order do
    let line := groups[i]!.qsort fun a b =>
      a.2.x < b.2.x || (a.2.x == b.2.x && a.1 < b.1)
    let s := String.ofList (inked (String.join (line.toList.map (·.2.text))))
    unless s.isEmpty do out := out.push s
  return out

/-- Every scalar a page inks, in reading order: the lines top to bottom,
joined. Read off `linesOf` rather than the run array, so the order level and
the line level agree about what "reading order" means and neither reports a
writer's painting sequence as the page's. -/
def orderKey (p : ArtPage) : String := String.join (linesOf p).toList

/-- Every scalar a page inks, sorted: the multiset, spelled so two
readings can be compared by one equality. -/
def censusKey (p : ArtPage) : String :=
  String.ofList (inked (String.join (p.runs.toList.map (·.text)))).mergeSort

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
  /-- The content key of `<name>.tex` with its comment lines dropped: the
  half of the engine's source that can change what the engine typesets.

  Two keys rather than one because the whole-file key catches an edit the
  gate cannot clear by itself. A fixture's `% diverges:` declaration and its
  prose header are comments; correcting one moved `src-key`, the gate then
  reported a stale pairing, and its own advice was to re-run the reference
  engine — so the gate's remedy for its own annotation needed `lualatex`,
  and on a host without it the gate stayed red. With the body keyed
  separately, `--repin` can accept exactly the edits that cannot have moved
  a glyph, and a real edit to the document still needs a new reference. -/
  srcBodyKey : String
  /-- The content key of `<name>.ref.tex`: the reference's half. -/
  refSrcKey : String
  engine : String
  /-- The LaTeX format the run loaded, from the log's own `LaTeX2e <date>`
  line. `engine` names the binary, which is not the same fact: the same
  binary with a newer format lays out differently. -/
  format : String
  argv : String
  /-- Every in-repo file the run read, `path=key` per space-separated item,
  from `-recorder`'s input list. The shipped font is the one that matters:
  nothing pinned it before, so a font update could leave the engine on the
  new face and the reference on the old one with no stale report. -/
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

/-! ## The pins

A committed reference is tied to the two sources it was built from by
content keys, so an edit to either half is a stale pairing and never a
level result. -/

def srcKeyOf (src : String) : String := Flate.contentKey src.toUTF8

/-- A source with its whole-line comments dropped: the part of a fixture that
can change what the engine typesets. A trailing comment on a line of content
moves this key too, which is the conservative direction — such an edit needs
a fresh reference rather than a repin. -/
def bodyOf (src : String) : String :=
  String.intercalate "\n"
    ((src.splitOn "\n").filter fun l => !(l.trimAscii.toString.startsWith "%"))

/-- Does the engine's own lexer capture any of this source raw? Inside a
verbatim or listing body a `%` line is text the engine sets, so dropping it
would let `--repin` clear an edit to the document itself. Asked of the lexer
rather than of a copy of its environment list, so the two cannot drift. -/
def lexesVerbatim (src : String) : Bool :=
  (Lex.lex "parity" src).1.any fun t =>
    match t.tok with
    | .verb _ _ => true
    | _ => false

/-- What `src-body-key` pins. A source the lexer reads any part of raw is
pinned whole, so every edit to it needs a fresh reference. -/
def srcBodyKeyOf (src : String) : String :=
  if lexesVerbatim src then srcKeyOf src else srcKeyOf (bodyOf src)

/-- What `--repin` may do to one sidecar. -/
inductive Repin where
  | unnecessary
  | repinned (side : Sidecar)
  | refused (why : String)
  deriving Inhabited

/-- Re-pin the engine's half of a pairing without the reference engine,
when and only when nothing the reference depends on has moved: the
reference source, the committed bytes and every pinned input are the ones
the sidecar records, and the engine's source differs from its pin only in
comment lines.

The point is that the gate's remedy for its own annotation must be
reachable on a host with no TeX install. The pin exists to catch a broken
correspondence between two hand-written halves; a comment cannot break one,
and the engine's half is recompiled from source on every run, so nothing is
being taken on trust that was not already. Everything else refuses, and the
refusal names which fact moved. -/
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

/-- The side files the reference engine leaves behind. None of them is a
reference, and a committed one would be noise the ladder never reads. Also
what the recorded input list drops: the engine reading its own scratch file
is not an input of the document. -/
def refLitter : List String :=
  [".ref.aux", ".ref.log", ".ref.out", ".ref.toc", ".ref.nav", ".ref.snm", ".ref.fls"]

/-- The `inputs:` field back as `path`, `key` pairs. An item that is not
exactly one `=` is dropped rather than guessed at — a path carrying an `=`
would have to be spelled another way, and no in-repo input does. -/
def inputPins (s : String) : List (String × String) :=
  (s.splitOn " ").filterMap fun item =>
    match item.trimAscii.toString.splitOn "=" with
    | [p, k] => if p.isEmpty || k.isEmpty then none else some (p, k)
    | _ => none

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

/-- A page's glyph origins, one per inked scalar: where the glyph starts and
what it spells. Whitespace is dropped for the reason `inked` gives. The unit
of a placement comparison is the glyph and never the run — the two writers
segment runs differently by construction (`Divergence.runSegmentation`). -/
def placedOf (p : ArtPage) : Array (Dim.Sp × Dim.Sp × String) := Id.run do
  let mut out : Array (Dim.Sp × Dim.Sp × String) := #[]
  for r in p.runs do
    for (x, t) in r.glyphs do
      if t.any (fun c => !c.isWhitespace) then out := out.push (x, r.y, t)
  return out

/-- A page's glyph origins by line: the same grouping `linesOf` uses, each
line's glyphs left to right, each carrying the offset in that line's
character stream where it starts. The offset is the glyph's identity across
writers — a ligature is one glyph spelling two characters on one side and
two glyphs on the other, and nothing but the character stream says which
glyph is which. -/
def placedLines (p : ArtPage) : Array (Array (Nat × Dim.Sp × Dim.Sp × String)) := Id.run do
  let mut ys : Array Dim.Sp := #[]
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
  let mut out : Array (Array (Nat × Dim.Sp × Dim.Sp × String)) := #[]
  for i in order do
    let line := groups[i]!.qsort fun a b =>
      a.2.x < b.2.x || (a.2.x == b.2.x && a.1 < b.1)
    let mut glyphs : Array (Nat × Dim.Sp × Dim.Sp × String) := #[]
    let mut off := 0
    for (_, r) in line do
      for (x, t) in r.glyphs do
        let inkedT := String.ofList (inked t)
        unless inkedT.isEmpty do
          glyphs := glyphs.push (off, x, r.y, inkedT)
          off := off + inkedT.length
    unless glyphs.isEmpty do out := out.push glyphs
  return out

/-- The pairing a placement claim measures over: line for line, each line's
glyphs matched by where they start in that line's character stream and what
they spell. A glyph the other side spells differently — a ligature against
its two characters — is skipped on both sides and counted, never paired with
a neighbour: one mismatch paired through would shift every later glyph on
the line and report hundreds of points of disagreement that are an artefact
of the matching. -/
def placePairs (engine reference : ArtPage) :
    Array ((Dim.Sp × Dim.Sp) × (Dim.Sp × Dim.Sp)) × Nat := Id.run do
  let el := placedLines engine
  let rl := placedLines reference
  let mut pairs : Array ((Dim.Sp × Dim.Sp) × (Dim.Sp × Dim.Sp)) := #[]
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
def atPercentile (xs : Array Dim.Sp) (pct : Nat) : Dim.Sp :=
  if xs.isEmpty then 0
  else
    let s := xs.qsort (· < ·)
    s[min (s.size - 1) (s.size * pct / 100)]!

end Parity
