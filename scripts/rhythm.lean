/-
The vertical rhythm, measured at every declared boundary and held to a
reference. Run from the repository root:

  lake env lean --run scripts/rhythm.lean               regenerate the tier baseline
  lake env lean --run scripts/rhythm.lean --check       gate against tests/scoreboard/rhythm.tsv
  lake env lean --run scripts/rhythm.lean --selftest    break each predicate once
  lake env lean --run scripts/rhythm.lean --table       every boundary: engine, reference, delta
  lake env lean --run scripts/rhythm.lean --lines <f>   a fixture's engine lines, leaves and marks
  lake env lean --run scripts/rhythm.lean --reference [fixture…]   needs lualatex; writes tests/rhythm/<f>.ref
  lake env lean --run scripts/rhythm.lean --verify-reference [fixture…]   needs lualatex; rebuilds
                                                        each reference and holds it to the file
  lake env lean --run scripts/rhythm.lean --html <dir>  needs node and Playwright's Chromium: every
                                                        fixture's page, measured in a browser; a report

A fixture is `tests/rhythm/<name>.tex`. Its header declares what it probes
(`% rhythm:`) and its boundaries, one per line:

  % boundary: <class> <marker> <kind>

`<marker>` names the lower side of the boundary: the first line holding that
word, or, spelled `=<text>`, the line whose whole text is `<text>` (a page
number). `<kind>` says what is measured, always downward on the page and in
bp (1/72 in: the PDF user unit, and this engine's pt):

  span    baseline of the text line above → baseline of the marker's line
  above   baseline of the text line above → top edge of the marks between them
  below   bottom edge of the marks between → baseline of the marker's line
  top     the page's top edge → baseline of the marker's line
  pitch   as span, inside one block: a table's rows, a code block's lines

"Marks" are everything a page paints that is not text: picture paths, fills,
rules, images, polygons. A fixture whose source is not LaTeX names its LaTeX
half with `% reference: <file>`; otherwise the reference engine compiles the
fixture itself, which is the user's case — a LaTeX document built by both engines.

The reference is lualatex's output, measured by `--reference` with the
engine's own PDF reader (`Tests.Artifact.readArtifact`, the reader the parity
ladder uses) and committed as numbers only: `tests/rhythm/<name>.ref`, one
row per boundary with its unit and what it measures from, plus the content
keys of both sources, so a fixture edited without regenerating is a named
fault and never a silent comparison against another document.

The engine side is measured in process from `Layout.Out`, built the way the
driver builds a document (`Scoreboard.Hermetic`'s sequence) over the shipped
faces only: hermetic, no TeX, no host font. A line's block is its structure
leaf (`LineOut.leaf`), and the measurement's premise is checked on every run
rather than assumed: the marker opens its line (on both sides), and the
marker's line opens its block, so the line above belongs to the block
before (on the engine's side, which has structure). A boundary whose premise
fails is measured as absent — the engine set the construct inline, or
merged two blocks — and never compared: its "gap" would be another
quantity, and one that happened to equal the reference would count.

The tier: per fixture and boundary class, `<fixture>/<class>.boundaries`,
the boundaries declared, and two counts of them: `.within`, how many ship
within `toleranceMilliBp` of the reference, and `.near`, how many within
`nearMilliBp`, half the rhythm quantum.
The reference is what LaTeX does, not what the engine must do: a boundary
the engine sets differently on purpose counts as outside, and the ratchet
holds the count from falling, never from rising.

Two comparison levels, each with its blind spots declared. `.within` sees
each declared boundary's gap to within the tolerance, and nothing else —
not a difference under half a bp, not horizontal placement, not a boundary
no fixture declares, not line pitch inside a block. Nor does it see a gap
move while it stays outside the tolerance: a quoted block's boundaries once
went from 1.9 bp short of lualatex's to 4.1 bp past it under an unchanged
count. `.near` sees that move, and is blind inside its own band.
`--selftest` holds the pair each level owes: two gaps under the tolerance
apart read equal under `.within` and unequal to the exact comparison above
it, and two gaps inside the band read equal under `.near` and unequal under
`.within`.
-/
import Tests.Artifact
import scripts.Board

open LeanTex.Core LeanTex.Cli Scoreboard

namespace Rhythm

/-- Where the fixtures and their references live. -/
def rhythmDir : String := "tests/rhythm"

/-- The tolerance a shipped gap is judged within, in thousandths of a bp:
half a bp. One pixel of the 110 dpi review raster is 0.65 bp, so a gap
inside this tolerance cannot be seen there; and the two engines' units
differ by 0.375 % (TeX's pt is 1/72.27 in, this engine's 1/72 in), which is
0.1 bp on a 27 bp gap — inside it. -/
def toleranceMilliBp : Int := 500

/-- The second band, in thousandths of a bp: half the rhythm quantum at the
article base (`Ir.rhythmQuantum` of `Ir.baseFontSize` is 6 bp). The engine
sets its gaps on that grid, so a gap rounded from lualatex's to the grid
stands at most this far from it. A constant, not the function read at run
time, so an engine change cannot move the band; the selftest fails once the
premise does. -/
def nearMilliBp : Int := 3000

/-- sp per bp, and the conversion to thousandths of a bp, rounded half away
from zero so a value reads the same whichever side of zero it is. -/
def spPerBp : Int := 65536

def milliBpOfSp (v : Int) : Int :=
  let n := v * 1000
  if n ≥ 0 then (n + spPerBp / 2) / spPerBp else -((-n + spPerBp / 2) / spPerBp)

/-- A value in thousandths of a bp, spelled `12.345`. -/
def showMilli (m : Int) : String :=
  let a := m.natAbs
  let frac := toString (a % 1000)
  let frac := "".pushn '0' (3 - frac.length) ++ frac
  (if m < 0 then "-" else "") ++ s!"{a / 1000}.{frac}"

/-- `12.345` back to thousandths; at most three decimals. -/
def parseMilli (s : String) : Option Int := do
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let (whole, frac) ← match body.splitOn "." with
    | [w] => pure (w, "")
    | [w, f] => pure (w, f)
    | _ => none
  if whole.isEmpty || frac.length > 3 then none
  let w ← whole.toNat?
  let f ← if frac.isEmpty then pure 0 else (frac ++ "".pushn '0' (3 - frac.length)).toNat?
  let v : Int := (w * 1000 + f : Nat)
  return (if neg then -v else v)

/-! ## What a fixture declares -/

inductive Kind where
  | span
  | above
  | below
  | top
  | pitch
  deriving BEq, Inhabited, Repr

def Kind.all : List Kind := [.span, .above, .below, .top, .pitch]

def Kind.name : Kind → String
  | .span => "span"
  | .above => "above"
  | .below => "below"
  | .top => "top"
  | .pitch => "pitch"

def Kind.ofName? (s : String) : Option Kind := Kind.all.find? (·.name == s)

/-- What a kind measures, from where to where: the words each `.ref` row
carries beside its number. -/
def Kind.measures : Kind → String
  | .span => "baseline of the text line above → baseline of the marker's line"
  | .above => "baseline of the text line above → top edge of the marks between"
  | .below => "bottom edge of the marks between → baseline of the marker's line"
  | .top => "top edge of the page → baseline of the marker's line"
  | .pitch => "baseline of the line above, in the same block → baseline of the marker's line"

structure Spec where
  cls : String
  marker : String
  kind : Kind
  deriving BEq, Inhabited, Repr

structure Fixture where
  name : String
  about : String
  specs : Array Spec
  /-- The LaTeX half, when the fixture's own source is not LaTeX. -/
  refSrc : Option String
  deriving Inhabited

/-- A class name is `[a-z0-9-]+`, so an item reads as one token. -/
def classOk (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isLower || c.isDigit || c == '-'

def headerValue (l key : String) : Option String :=
  let pre := s!"% {key}:"
  if l.startsWith pre then some (l.drop pre.length).toString.trimAscii.toString else none

/-- A fixture's declarations, read off its header. A malformed boundary line
is an error rather than a skipped line: a declaration that measures nothing
would read as coverage. -/
def parseFixture (name src : String) : Except String Fixture := do
  let mut about : Option String := none
  let mut specs : Array Spec := #[]
  let mut refSrc : Option String := none
  for raw in src.splitOn "\n" do
    let l := raw.trimAsciiEnd.toString
    if let some v := headerValue l "rhythm" then about := some v
    if let some v := headerValue l "reference" then refSrc := some v
    if let some v := headerValue l "boundary" then
      match (v.splitOn " ").filter (!·.isEmpty) with
      | [cls, marker, kind] =>
        let some k := Kind.ofName? kind
          | throw s!"{name}: '% boundary: {v}': kind '{kind}' is not one of span, above, below, top, pitch"
        unless classOk cls do throw s!"{name}: '% boundary: {v}': class '{cls}' is not [a-z0-9-]+"
        if marker.isEmpty || marker == "=" then throw s!"{name}: '% boundary: {v}': empty marker"
        let s : Spec := { cls, marker, kind := k }
        if specs.contains s then throw s!"{name}: '% boundary: {v}' is declared twice"
        specs := specs.push s
      | _ => throw s!"{name}: '% boundary: {v}' is not '<class> <marker> <kind>'"
  let some what := about | throw s!"{name}: no '% rhythm:' line saying what the fixture probes"
  if specs.isEmpty then throw s!"{name}: no '% boundary:' line, so nothing is measured"
  return { name, about := what, specs, refSrc }

/-! ## A page as the measurement reads it

Every coordinate is in sp, downward from the page's top edge, on both
sides: the engine's layout coordinates already are, and a PDF's are flipped
against its media box. -/

structure MLine where
  y : Int
  text : String
  /-- The structure leaf the line sets (`LineOut.leaf`); the reference's
  lines carry none, since its PDF is untagged. -/
  leaf : Option Nat := none
  furniture : Bool := false
  deriving BEq, Inhabited, Repr

structure MPage where
  /-- Text lines, top to bottom. A line with no glyph is not here: a rule
  alone, an image alone, is a mark. -/
  lines : Array MLine
  /-- Every non-text mark: its top and bottom edge. -/
  marks : Array (Int × Int)
  deriving Inhabited, Repr

/-- Does `marker` stand in `s` as a word: an occurrence with no letter
immediately before or after it? Digits may touch it, because a section
number is set against its title with no space glyph between them on one
side and with one on the other. -/
def holdsWord (s marker : String) : Bool := Id.run do
  let cs := s.toList.toArray
  let ms := marker.toList.toArray
  if ms.isEmpty || cs.size < ms.size then return false
  for i in [0:cs.size - ms.size + 1] do
    let mut hit := true
    for j in [0:ms.size] do
      if cs[i + j]! != ms[j]! then
        hit := false
        break
    if hit then
      let before := if i == 0 then ' ' else cs[i - 1]!
      let after := cs[i + ms.size]?.getD ' '
      if !before.isAlpha && !after.isAlpha then return true
  return false

def lineMatches (marker : String) (l : MLine) : Bool :=
  if marker.startsWith "=" then
    l.text.trimAscii.toString == (marker.drop 1).toString
  else holdsWord l.text marker

/-- A line's first word: its first maximal run of letters. A section number,
a list's bullet, a footnote's mark and a bracketed label come before it and
are not words. -/
def firstWord (s : String) : Option String :=
  let w := String.ofList ((s.toList.dropWhile (!·.isAlpha)).takeWhile (·.isAlpha))
  if w.isEmpty then none else some w

/-- The first line, in page order, the marker names. -/
def findMarker (pages : Array MPage) (marker : String) : Option (Nat × Nat) := Id.run do
  for i in [0:pages.size] do
    let p := pages[i]!
    for j in [0:p.lines.size] do
      if lineMatches marker p.lines[j]! then return some (i, j)
  return none

/-- The first half of the premise, checked on both sides: a marker opens its
line. One standing inside a line is text the block it was meant to open ran
into — the engine set a construct inline — and the line above it is not the
previous block's. -/
def openFault (pages : Array MPage) (s : Spec) : Option String := do
  if s.marker.startsWith "=" then none
  let (i, j) ← findMarker pages s.marker
  let l := pages[i]!.lines[j]!
  if firstWord l.text == some s.marker then none
  else some s!"the marker '{s.marker}' stands inside a line that opens with \
'{(firstWord l.text).getD ""}', so the block it opens was set inline"

/-- The text line above line `j` of a page: the nearest one standing
strictly higher, skipping furniture unless the marker's own line is
furniture, and skipping a line with no letter unless the marker's own line
has none — a raised footnote mark is its own baseline in a PDF, and it is
not the text line a reader measures a gap from. -/
def lineAbove (p : MPage) (j : Nat) : Option MLine := Id.run do
  let me := p.lines[j]!
  let lettered (l : MLine) : Bool := l.text.any Char.isAlpha
  let mut best : Option MLine := none
  for l in p.lines do
    if l.y < me.y && (me.furniture || !l.furniture) && (lettered l || !lettered me) then
      match best with
      | some b => if b.y < l.y then best := some l
      | none => best := some l
  return best

/-- The marks standing between two baselines: a mark whose vertical extent
overlaps the open band between them. -/
def marksBetween (p : MPage) (hi lo : Int) : Array (Int × Int) :=
  p.marks.filter fun (t, b) => t < lo && b > hi

/-- One boundary's measured gap, in sp, or why it has none. -/
def gapOf (pages : Array MPage) (s : Spec) : Except String Int := do
  let some (i, j) := findMarker pages s.marker
    | throw s!"no line holds the marker '{s.marker}'"
  let p := pages[i]!
  let me := p.lines[j]!
  if s.kind == .top then return me.y
  let some up := lineAbove p j
    | throw s!"the marker '{s.marker}' opens page {i + 1}, so no line above it shares its page"
  match s.kind with
  | .span | .pitch => return me.y - up.y
  | .above | .below =>
    let ms := marksBetween p up.y me.y
    if ms.isEmpty then throw s!"no mark stands between the marker '{s.marker}' and the line above it"
    let top := ms.foldl (fun a m => min a m.1) ms[0]!.1
    let bot := ms.foldl (fun a m => max a m.2) ms[0]!.2
    return (if s.kind == .above then top - up.y else me.y - bot)
  | .top => return me.y

/-- The measurement's premise, on the side that has structure: the marker's
line opens its block, so the line above belongs to the block before. A line
whose leaf is the line above's is a line inside one block, and its "gap" is
a line pitch — a different quantity, which would be compared silently. A
`pitch` declares exactly that quantity, so it asks the opposite: the line
above sets the same leaf. -/
def premiseFault (pages : Array MPage) (s : Spec) : Option String := do
  if s.kind == .top then none
  let (i, j) ← findMarker pages s.marker
  let p := pages[i]!
  let me := p.lines[j]!
  let up ← lineAbove p j
  if s.kind == .pitch then
    if me.leaf.isSome && me.leaf != up.leaf then
      some s!"the marker '{s.marker}' opens a block of its own, so the pitch declared there is a boundary's gap"
    else none
  else if me.leaf.isSome && me.leaf == up.leaf then
    some s!"the marker '{s.marker}' is not the first line of its block (the line above sets the same structure leaf)"
  else none

/-! ## The two artifacts, read -/

/-- The engine's pages. Text is every glyph run the line ships, gaps as
spaces — and a kern too (a glyphless run: `\,`, `\quad`, `~`, a label's
`\labelsep`), which the reference's PDF reads as the space it is, so a
marker a kern precedes or follows stays a word; marks are picture paths,
fills, and the rules, images and polygons a line carries. -/
def ofOut (out : Layout.Out) : Array MPage :=
  out.pages.map fun p => Id.run do
    let mut lines : Array MLine := #[]
    let mut marks : Array (Int × Int) := #[]
    for l in p.lines do
      let mut text := ""
      for s in l.segs do
        match s with
        | .run _ _ _ w glyphs _ _ _ _ _ _ =>
          if glyphs.isEmpty then
            if w > 0 then text := text.push ' '
          else for (_, c, _) in glyphs do text := text.push c
        | .gap _ _ | .decoratedGap _ _ _ => text := text.push ' '
        | .rule _ th raise _ | .decoration _ _ th raise _ =>
          marks := marks.push (l.y - raise - th, l.y - raise)
        | .image _ _ h => marks := marks.push (l.y - h, l.y)
        | .poly pts _ =>
          if let some (_, y) := pts[0]? then
            let bounds := pts.foldl (fun (t, b) (_, y) =>
              (min t (l.y - y), max b (l.y - y))) (l.y - y, l.y - y)
            marks := marks.push bounds
      if !(text.trimAscii.isEmpty) then
        lines := lines.push { y := l.y, text, leaf := l.leaf, furniture := l.furniture }
    for f in p.fills do marks := marks.push (f.y, f.y + f.h)
    for q in p.paths do
      let (t, b) : Int × Int := match q.path with
        | .circle _ cy r => (cy - r.natAbs, cy + r.natAbs)
        | .rect _ y _ h => (y, y + h)
        | .tri _ y1 _ y2 _ y3 => (min y1 (min y2 y3), max y1 (max y2 y3))
        | .segs segs =>
          let ys := segs.flatMap fun s => match s with
            | .line _ y1 _ y2 => #[y1, y2]
            | .cubic _ y1 _ ya _ yb _ y2 => #[y1, ya, yb, y2]
          (ys.foldl min (ys[0]?.getD 0), ys.foldl max (ys[0]?.getD 0))
      marks := marks.push (t, b)
    return { lines := lines.qsort (·.y < ·.y), marks }

/-- A 2×3 affine matrix in fixed point (65536 = 1), PDF's `[a b c d e f]`. -/
structure Ctm where
  a : Int := 65536
  b : Int := 0
  c : Int := 0
  d : Int := 65536
  e : Int := 0
  f : Int := 0
  deriving Inhabited

/-- `m` concatenated onto `t`, as `cm` does (§8.4.4: CTM′ = M × CTM). -/
def Ctm.concat (m t : Ctm) : Ctm :=
  let u := 65536
  { a := (m.a * t.a + m.b * t.c) / u, b := (m.a * t.b + m.b * t.d) / u
    c := (m.c * t.a + m.d * t.c) / u, d := (m.c * t.b + m.d * t.d) / u
    e := (m.e * t.a + m.f * t.c) / u + t.e, f := (m.e * t.b + m.f * t.d) / u + t.f }

def Ctm.apply (t : Ctm) (x y : Int) : Int × Int :=
  ((t.a * x + t.c * y) / 65536 + t.e, (t.b * x + t.d * y) / 65536 + t.f)

/-- Every mark a content stream paints, as its bounding box in PDF user
space, under the transformation in force: a stroked or filled path, and an
image (the unit square its `cm` maps). The shared reader
(`Tests.Artifact.evalContent`) reads a path's operands in the coordinates
they are written in, which is right for this engine's output and wrong for
a TikZ picture, whose paths are written inside the picture's own `cm`: read
that way, a picture stands at the page's origin. Text is not a mark. -/
def ctmMarks (content : ByteArray) : Array (Int × Int × Int × Int) := Id.run do
  let mut out : Array (Int × Int × Int × Int) := #[]
  let mut ctm : Ctm := {}
  let mut saved : Array Ctm := #[]
  let mut nums : Array Int := #[]
  let mut box : Option (Int × Int × Int × Int) := none
  let grow (bx : Option (Int × Int × Int × Int)) (p : Int × Int) : Option (Int × Int × Int × Int) :=
    match bx with
    | none => some (p.1, p.2, p.1, p.2)
    | some (x0, y0, x1, y1) => some (min x0 p.1, min y0 p.2, max x1 p.1, max y1 p.2)
  for t in scanContent content do
    match t with
    | .num v _ => nums := nums.push v
    | .op o =>
      if o == "q" then saved := saved.push ctm
      else if o == "Q" then
        ctm := saved.back?.getD {}
        saved := saved.pop
      else if o == "cm" && nums.size ≥ 6 then
        let n := nums.extract (nums.size - 6) nums.size
        ctm := Ctm.concat { a := n[0]!, b := n[1]!, c := n[2]!, d := n[3]!, e := n[4]!, f := n[5]! } ctm
      else if (o == "m" || o == "l") && nums.size ≥ 2 then
        box := grow box (ctm.apply nums[nums.size - 2]! nums[nums.size - 1]!)
      else if o == "c" && nums.size ≥ 6 then
        for k in [0:3] do
          box := grow box (ctm.apply nums[nums.size - 6 + 2 * k]! nums[nums.size - 5 + 2 * k]!)
      else if (o == "v" || o == "y") && nums.size ≥ 4 then
        for k in [0:2] do
          box := grow box (ctm.apply nums[nums.size - 4 + 2 * k]! nums[nums.size - 3 + 2 * k]!)
      else if o == "re" && nums.size ≥ 4 then
        let (x, y, w, h) := (nums[nums.size - 4]!, nums[nums.size - 3]!, nums[nums.size - 2]!,
          nums[nums.size - 1]!)
        for (px, py) in [(x, y), (x + w, y), (x, y + h), (x + w, y + h)] do
          box := grow box (ctm.apply px py)
      else if ["f", "F", "f*", "B", "B*", "b", "b*", "S", "s"].contains o then
        if let some bx := box then out := out.push bx
        box := none
      else if o == "n" then box := none
      else if o == "Do" then
        let mut ib : Option (Int × Int × Int × Int) := none
        for (px, py) in [((0 : Int), (0 : Int)), (65536, 0), (0, 65536), (65536, 65536)] do
          ib := grow ib (ctm.apply px py)
        if let some bx := ib then out := out.push bx
      nums := #[]
    | _ => pure ()
  return out

/-- A reference page: its runs grouped into lines by baseline, each line's
text in left-to-right order, flipped to run downward from the media box's
top; its marks read under the transformation in force (`ctmMarks`). -/
def ofArt (p : ArtPage) : MPage := Id.run do
  let top := p.media.2.2.2
  let mut ys : Array Int := #[]
  let mut runs : Array (Array ArtRun) := #[]
  for r in p.runs do
    match ys.findIdx? (· == r.y) with
    | some i => runs := runs.modify i (·.push r)
    | none =>
      ys := ys.push r.y
      runs := runs.push #[r]
  let mut lines : Array MLine := #[]
  for i in [0:ys.size] do
    let rs := runs[i]!.qsort (·.x < ·.x)
    let text := String.intercalate " " (rs.toList.map (·.text))
    if !(text.trimAscii.isEmpty) then
      lines := lines.push { y := top - ys[i]!, text }
  let marks := (ctmMarks p.content).map fun (_, y0, _, y1) => (top - y1, top - y0)
  return { lines := lines.qsort (·.y < ·.y), marks }

/-! ## The reference file: numbers only -/

structure RefRow where
  spec : Spec
  milliBp : Int
  deriving BEq, Inhabited, Repr

structure RefFile where
  fixture : String
  srcKey : String
  refSrc : String
  refSrcKey : String
  engine : String
  format : String
  rows : Array RefRow
  deriving BEq, Inhabited, Repr

def refPath (name : String) : String := s!"{rhythmDir}/{name}.ref"

def RefFile.render (r : RefFile) : String := Id.run do
  let mut out := "# the lualatex reference for one rhythm fixture — generated by \
scripts/rhythm.lean --reference; numbers only, never hand-edit\n"
  out := out ++ s!"fixture: {r.fixture}\n"
  out := out ++ s!"src-key: {r.srcKey}\n"
  out := out ++ s!"ref-src: {r.refSrc}\n"
  out := out ++ s!"ref-src-key: {r.refSrcKey}\n"
  out := out ++ s!"engine: {r.engine}\n"
  out := out ++ s!"format: {r.format}\n"
  out := out ++ "unit: bp (1/72 in, the PDF user unit), measured downward on the page\n"
  for row in r.rows do
    out := out ++ s!"{row.spec.cls}\t{row.spec.marker}\t{row.spec.kind.name}\t\
{showMilli row.milliBp} bp\t{row.spec.kind.measures}\n"
  return out

def RefFile.parse (text : String) : Except String RefFile := do
  let mut r : RefFile := default
  let mut seen : Array String := #[]
  for raw in text.splitOn "\n" do
    let l := raw.trimAsciiEnd.toString
    if l.isEmpty || l.startsWith "#" then continue
    let field (k : String) : Option String :=
      if l.startsWith (k ++ ":") then some (l.drop (k.length + 1)).toString.trimAscii.toString
      else none
    if let some v := field "fixture" then r := { r with fixture := v }; seen := seen.push "fixture"
    else if let some v := field "src-key" then r := { r with srcKey := v }; seen := seen.push "src-key"
    else if let some v := field "ref-src-key" then
      r := { r with refSrcKey := v }; seen := seen.push "ref-src-key"
    else if let some v := field "ref-src" then r := { r with refSrc := v }; seen := seen.push "ref-src"
    else if let some v := field "engine" then r := { r with engine := v }; seen := seen.push "engine"
    else if let some v := field "format" then r := { r with format := v }; seen := seen.push "format"
    else if (field "unit").isSome then seen := seen.push "unit"
    else
      match l.splitOn "\t" with
      | [cls, marker, kind, value, _] =>
        let some k := Kind.ofName? kind | throw s!"row '{l}': kind '{kind}' unknown"
        let some v := (if value.endsWith " bp" then parseMilli (value.dropEnd 3).toString else none)
          | throw s!"row '{l}': value '{value}' is not '<n.nnn> bp'"
        r := { r with rows := r.rows.push { spec := { cls, marker, kind := k }, milliBp := v } }
      | _ => throw s!"line '{l}' is neither a field nor a five-column row"
  for k in ["fixture", "src-key", "ref-src", "ref-src-key", "engine", "format", "unit"] do
    unless seen.contains k do throw s!"no '{k}:' line"
  return r

/-! ## Building each side -/

def fontsDir : System.FilePath := "tests/corpus/fonts"

/-- The engine's pages for a fixture, built as the driver builds one —
lex, parse, `\input` and `\data` beside the file, one preparation, the
picture-label metric against the preamble's faces, the bibliography — over
the shipped faces only, then laid out with the document's own patterns. -/
def engineOut (cache : IO.Ref (Array (String × Font.Font))) (faces : Array FontDb.Face)
    (oneFace : Font.FontSet) (file : String) : IO (Layout.Out × Array Diag × Nat) := do
  let src ← IO.FS.readFile file
  let (toks, lexDiags) := Lex.lex file src
  let (raws, parseDiags) := Parse.parse file toks
  let (executed, inputDiags, _) ← Input.expandInputs file raws
  let (raws, dataDiags) ← Input.resolveData file executed.raws
  let prepared := Elab.prepareExecuted file { executed with raws := raws }
  let pre := Elab.preambleDoc file prepared
  let preFs ← Hermetic.fontSetFor cache oneFace faces fontsDir pre
  let metric := Layout.labelMetric (Layout.Geom.ofPage pre.page) preFs
  let (doc, elabDiags, spans) := Elab.runPrepared file prepared
    (lexDiags ++ parseDiags ++ inputDiags ++ dataDiags) metric
  let (doc, bibDiags) ← Input.resolveBibliography file doc spans.bib
  let fs ← Hermetic.fontSetFor cache oneFace faces fontsDir doc
  let (store, imgDiags, _) ← Hermetic.storeFor rhythmDir doc
  let out := Layout.run (Layout.Geom.ofPage doc.page) fs (Hyphen.forTag doc.info.locale.tag) doc store
  let diags := elabDiags ++ bibDiags ++ imgDiags ++ out.diags
  return (out, diags, (Diag.resolveAll doc.allow false diags).errors)

/-- The shipped body face and its one-face set: every fixture's text sets
in it, on both sides (the reference names the same file through fontspec). -/
def oneFaceSet (cache : IO.Ref (Array (String × Font.Font))) : IO Font.FontSet := do
  let some body ← Hermetic.loadFont cache (fontsDir / "OpenSans-Regular.ttf").toString
    | throw (IO.userError s!"{fontsDir}/OpenSans-Regular.ttf does not parse")
  return { fonts := #[body], index := Hermetic.oneFaceIndex }

/-- Every fixture, by name, in name order. -/
def fixtureNames : IO (Array String) := do
  let mut out : Array String := #[]
  for e in ← System.FilePath.readDir rhythmDir do
    let n := e.fileName
    if n.endsWith ".tex" && !n.endsWith ".ref.tex" then out := out.push (n.dropEnd 4).toString
  return out.qsort (· < ·)

def keyOf (src : String) : String := Flate.contentKey src.toUTF8

/-- One measured boundary: the reference's number and the engine's, or why
the engine has none. -/
structure Measured where
  fixture : String
  row : RefRow
  engine : Except String Int
  deriving Inhabited

def Measured.within (m : Measured) (tol : Int := toleranceMilliBp) : Bool :=
  match m.engine with
  | .ok e => (e - m.row.milliBp).natAbs ≤ tol.natAbs
  | .error _ => false

def Measured.near (m : Measured) : Bool := m.within nearMilliBp

/-- A fixture measured, or the fault that stops it being measured: no
reference, a reference of another source, a failed premise. -/
def measureFixture (cache : IO.Ref (Array (String × Font.Font))) (faces : Array FontDb.Face)
    (oneFace : Font.FontSet) (name : String) : IO (Except String (Array Measured)) := do
  let file := s!"{rhythmDir}/{name}.tex"
  let src ← IO.FS.readFile file
  let fx ← match parseFixture name src with
    | .ok f => pure f
    | .error e => return .error e
  let refText ← readFileOr (refPath name)
  if refText.isEmpty then
    return .error s!"{name}: no reference {refPath name}; regenerate: \
lake env lean --run scripts/rhythm.lean --reference {name}"
  let ref ← match RefFile.parse refText with
    | .ok r => pure r
    | .error e => return .error s!"{refPath name}: {e}"
  if ref.srcKey != keyOf src then
    return .error s!"{name}: {file} moved since its reference was measured; regenerate: \
lake env lean --run scripts/rhythm.lean --reference {name}"
  if let some r := fx.refSrc then
    let rs ← readFileOr s!"{rhythmDir}/{r}"
    if ref.refSrc != r || ref.refSrcKey != keyOf rs then
      return .error s!"{name}: its LaTeX half {r} moved since the reference was measured; \
regenerate: lake env lean --run scripts/rhythm.lean --reference {name}"
  let declared := fx.specs
  let recorded := ref.rows.map (·.spec)
  if declared != recorded then
    return .error s!"{name}: the reference's boundaries are not the ones the fixture declares; \
regenerate: lake env lean --run scripts/rhythm.lean --reference {name}"
  let (out, _, _) ← engineOut cache faces oneFace file
  let pages := ofOut out
  -- A boundary whose premise fails on the engine's side is measured as
  -- absent, never compared: its "gap" would be another quantity, and one
  -- that happened to equal the reference would count as a match.
  return .ok (ref.rows.map fun row =>
    let engine := match openFault pages row.spec, premiseFault pages row.spec with
      | some why, _ => .error s!"premise: {why}"
      | none, some why => .error s!"premise: {why}"
      | none, none => (gapOf pages row.spec).map milliBpOfSp
    { fixture := name, row, engine })

/-- Every fixture measured; a fault anywhere is a fault of the run. -/
def measureAll : IO (Except (Array String) (Array Measured)) := do
  let cache ← IO.mkRef #[]
  let faces ← Hermetic.shippedFaces fontsDir
  let oneFace ← oneFaceSet cache
  let mut faults : Array String := #[]
  let mut out : Array Measured := #[]
  for n in ← fixtureNames do
    match ← measureFixture cache faces oneFace n with
    | .ok ms => out := out ++ ms
    | .error e => faults := faults.push e
  return (if faults.isEmpty then .ok out else .error faults)

/-- The tier's rows: per fixture and class, the boundaries declared and how
many of them are within each band. -/
def rowsOf (ms : Array Measured) : Array Row := Id.run do
  let mut keys : Array String := #[]
  let mut within : Array Int := #[]
  let mut near : Array Int := #[]
  let mut total : Array Int := #[]
  for m in ms do
    let k := s!"{m.fixture}/{m.row.spec.cls}"
    let i := match keys.idxOf? k with
      | some i => i
      | none => keys.size
    if i == keys.size then
      keys := keys.push k
      within := within.push 0
      near := near.push 0
      total := total.push 0
    total := total.modify i (· + 1)
    if m.within then within := within.modify i (· + 1)
    if m.near then near := near.modify i (· + 1)
  let mut rows : Array Row := #[]
  for i in [0:keys.size] do
    rows := rows.push { item := s!"{keys[i]!}.within", value := within[i]! }
    rows := rows.push { item := s!"{keys[i]!}.near", value := near[i]! }
    rows := rows.push { item := s!"{keys[i]!}.boundaries", value := total[i]! }
  return rows

def tierMeasure : IO (Array String × Array Row) := do
  match ← measureAll with
  | .error faults =>
    for f in faults do IO.eprintln s!"rhythm: fault: {f}"
    return (#[], #[])
  | .ok ms =>
    let n := (← fixtureNames).size
    let w := (ms.filter (·.within)).size
    let nr := (ms.filter (·.near)).size
    return (#[s!"# source: {n} fixtures under {rhythmDir}, {ms.size} declared boundaries, \
{w} within {showMilli toleranceMilliBp} bp of lualatex's and {nr} within {showMilli nearMilliBp}; \
the engine measured in process from Layout.Out over the shipped faces, the reference committed \
beside each fixture as numbers"],
      rowsOf ms)

/-- Every boundary, printed: the report the ranking is read from. -/
def table : IO UInt32 := do
  match ← measureAll with
  | .error faults =>
    for f in faults do IO.eprintln s!"rhythm: fault: {f}"
    return 2
  | .ok ms =>
    IO.println "fixture\tclass\tmarker\tkind\tengine_bp\treference_bp\tdelta_bp\twithin\tnear"
    for m in ms do
      let (e, d) := match m.engine with
        | .ok e => (showMilli e, showMilli (e - m.row.milliBp))
        | .error why => (s!"none ({why})", "-")
      IO.println s!"{m.fixture}\t{m.row.spec.cls}\t{m.row.spec.marker}\t{m.row.spec.kind.name}\t\
{e}\t{showMilli m.row.milliBp}\t{d}\t{if m.within then "yes" else "no"}\t\
{if m.near then "yes" else "no"}"
    return 0

/-- A fixture's engine pages, printed line by line: what a declaration's
marker has to name, read off the artifact the tier measures. -/
def dumpLines (name : String) : IO UInt32 := do
  let cache ← IO.mkRef #[]
  let faces ← Hermetic.shippedFaces fontsDir
  let oneFace ← oneFaceSet cache
  let (out, diags, errors) ← engineOut cache faces oneFace s!"{rhythmDir}/{name}.tex"
  IO.println s!"{name}: {out.pages.size} pages, {errors} errors"
  for p in ofOut out, i in [0:out.pages.size] do
    IO.println s!"page {i + 1}"
    for l in p.lines do
      IO.println s!"  {showMilli (milliBpOfSp l.y)}\tleaf={l.leaf}\tfurniture={l.furniture}\t{l.text}"
    for (t, b) in p.marks do
      IO.println s!"  mark {showMilli (milliBpOfSp t)} → {showMilli (milliBpOfSp b)}"
  for d in diags do IO.println s!"  diag {d.code} {d.subject} {d.message.take 100}"
  return 0

/-! ## The HTML report (needs node, Playwright and a cached Chromium; never a gate)

Each fixture's page is emitted in process, exactly as `Scoreboard.Hermetic`
emits a corpus page (the document's own stylesheet mode, its images beside
it), and a browser measures it: every text line's baseline, found from the
first glyph's box less its face's descent at its size, and every picture's
and image's box. The same declarations are then read over those lines as
over a PDF page. A browser's layout is a measurement, never a theorem, so
this prints and gates nothing.

The fair comparison is not in lengths. `HtmlDoc.backend_gaps_agree` holds the
two backends to the same *multiple* of their own context's rhythm quantum —
half the print leading on paper, half the screen leading on a screen — so
each gap is also printed in its own context's quanta, the reference's in the
PDF's. The screen leading is read off the page, as the first paragraph's
computed line height: on an article page that is `bodyLeadingMilli` of the
root size, and on a deck it is the stage's scaled one. -/

/-- The measuring probe, run by node with the Playwright module in
`PW_MODULE`: for every page named, every text line's baseline and text, and
every picture's and image's vertical extent, all in CSS px from the
document's top edge. -/
def probeJs : String := r#"
const { chromium } = require(process.env.PW_MODULE);
const path = require('path');
(async () => {
  const dir = process.argv[2];
  const names = process.argv.slice(3);
  const browser = await chromium.launch({ headless: true, args: ['--no-sandbox', '--disable-gpu'] });
  console.log(['version', browser.version()].join('\t'));
  const page = await browser.newPage({ viewport: { width: 1280, height: 960 } });
  for (const n of names) {
    await page.goto('file://' + path.join(dir, n + '.html'));
    await page.evaluate(() => document.fonts.ready);
    const got = await page.evaluate(() => {
      const root = parseFloat(getComputedStyle(document.documentElement).fontSize);
      const descents = new Map();
      const descentOf = (el) => {
        const cs = getComputedStyle(el);
        const key = [cs.fontFamily, cs.fontSize, cs.fontWeight, cs.fontStyle].join('|');
        if (descents.has(key)) return descents.get(key);
        const box = document.createElement('div');
        box.style.cssText = 'position:absolute;left:0;top:0;visibility:hidden;line-height:normal;white-space:nowrap';
        box.style.fontFamily = cs.fontFamily; box.style.fontSize = cs.fontSize;
        box.style.fontWeight = cs.fontWeight; box.style.fontStyle = cs.fontStyle;
        const t = document.createElement('span'); t.textContent = 'x';
        const p = document.createElement('span');
        p.style.cssText = 'display:inline-block;width:0;height:0;vertical-align:baseline';
        box.appendChild(t); box.appendChild(p); document.body.appendChild(box);
        const r = document.createRange(); r.selectNodeContents(t);
        const d = r.getBoundingClientRect().bottom - p.getBoundingClientRect().bottom;
        box.remove(); descents.set(key, d); return d;
      };
      const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, { acceptNode: (t) => {
        const el = t.parentElement;
        if (!el || el.closest('style,script,noscript,svg,[aria-hidden="true"]')) return NodeFilter.FILTER_REJECT;
        return t.nodeValue.trim() ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT; } });
      // Every glyph's baseline, in document order: its box's bottom less its
      // face's descent at its size. Lines are the clusters of one baseline,
      // so a hyphenation point or a formula's atoms never split a line. A
      // deck's stages stand side by side, so a stage's lines are set apart
      // by a stride no page reaches: no line is ever another stage's above.
      const stages = [...document.querySelectorAll('section.slide')];
      const glyphs = [];
      const rg = document.createRange();
      for (let t = walker.nextNode(); t; t = walker.nextNode()) {
        const s = t.nodeValue;
        const st = t.parentElement.closest('section.slide');
        const stride = st ? 100000 * (stages.indexOf(st) + 1) : 0;
        let i = 0;
        for (const ch of s) {
          const w = ch.length;
          rg.setStart(t, i); rg.setEnd(t, i + w);
          i += w;
          const b = rg.getBoundingClientRect();
          if (b.width === 0 && b.height === 0) continue;
          glyphs.push({ ch, base: stride + b.bottom + scrollY - descentOf(t.parentElement) });
        }
      }
      const lines = [];
      for (const g of glyphs) {
        let l = lines.find((x) => Math.abs(x.base - g.base) < 1);
        if (!l) {
          if (/\s/.test(g.ch)) continue;
          l = { base: g.base, text: '' }; lines.push(l);
        }
        l.text += g.ch;
      }
      const p = document.querySelector('main p, section p, p');
      const leading = p ? parseFloat(getComputedStyle(p).lineHeight) : root * 1.45;
      const marks = [...document.querySelectorAll('svg, img')].map((e) => {
        const b = e.getBoundingClientRect(); return [b.top + scrollY, b.bottom + scrollY]; })
        .filter(([t, b]) => b > t);
      return { root, leading, lines: lines.map((l) => [l.base, l.text]), marks };
    });
    console.log(['page', n, got.leading.toFixed(3)].join('\t'));
    for (const [y, t] of got.lines) console.log(['line', n, y.toFixed(3), t.replace(/\s+/g, ' ')].join('\t'));
    for (const [t, b] of got.marks) console.log(['mark', n, t.toFixed(3), b.toFixed(3)].join('\t'));
  }
  await browser.close();
})().catch((e) => { console.error(String(e && e.message || e)); process.exit(4); });
"#

/-- A fixture's HTML page, emitted as a corpus page is (`Hermetic.pageFor`'s
sequence and configuration, with no error gate: a page that errs is still
measured), with the image bytes it names. -/
def engineHtml (cache : IO.Ref (Array (String × Font.Font))) (faces : Array FontDb.Face)
    (oneFace : Font.FontSet) (name : String) : IO (String × Array (String × ByteArray)) := do
  let file := s!"{rhythmDir}/{name}.tex"
  let src ← IO.FS.readFile file
  let (toks, lexDiags) := Lex.lex file src
  let (raws, parseDiags) := Parse.parse file toks
  let (executed, inputDiags, _) ← Input.expandInputs file raws
  let (raws, dataDiags) ← Input.resolveData file executed.raws
  let prepared := Elab.prepareExecuted file { executed with raws := raws }
  let pre := Elab.preambleDoc file prepared
  let preFs ← Hermetic.fontSetFor cache oneFace faces fontsDir pre
  let metric := Layout.labelMetric (Layout.Geom.ofPage pre.page) preFs
  let (doc, _, spans) := Elab.runPrepared file prepared
    (lexDiags ++ parseDiags ++ inputDiags ++ dataDiags) metric
  let (doc, _) ← Input.resolveBibliography file doc spans.bib
  let fs ← Hermetic.fontSetFor cache oneFace faces fontsDir doc
  let (store, _, read) ← Hermetic.storeFor rhythmDir doc
  let css : HtmlDoc.CssMode := match cssFor doc.output.css with
    | .own => .own
    | .bulma => .bulma
    | .none => .none
  let cfg : HtmlDoc.Config :=
    { css, imgs := store
      fonts := if doc.fontPolicy == .embedded then some fs else none
      fontsDir := s!"{name}.fonts", assetsDir := s!"{name}.assets" }
  return ((HtmlDoc.emit cfg doc).1, read)

/-- The PDF's rhythm quantum for a fixture, in thousandths of a bp: half the
leading at the document's body size, the engine's own definition
(`Ir.rhythmQuantum`). -/
def pdfQuantumMilli (name : String) : IO Int := do
  let file := s!"{rhythmDir}/{name}.tex"
  let (doc, _) := Elab.run file (← IO.FS.readFile file)
  return milliBpOfSp (Ir.rhythmQuantum doc.page.fontSize)

/-- A number of thousandths as quanta of `q` thousandths, to two decimals. -/
def inQuanta (v q : Int) : String :=
  if q == 0 then "-" else
  let h := (v * 100 + (if v ≥ 0 then q / 2 else -(q / 2))) / q
  let a := h.natAbs
  let f := toString (a % 100)
  (if h < 0 then "-" else "") ++ s!"{a / 100}.{"".pushn '0' (2 - f.length)}{f}"

/-- The Playwright modules whose Chromium launches on this host, in the
order `html-oracle` tries them: `LEANTEX_PLAYWRIGHT`, then every module
`npx playwright install` left under `~/.npm/_npx`. Nothing is installed. -/
def playwrightModules : IO (Array String) := do
  let mut cands : Array String := #[]
  if let some p ← IO.getEnv "LEANTEX_PLAYWRIGHT" then cands := cands.push p
  if let some home ← IO.getEnv "HOME" then
    let npx : System.FilePath := home / ".npm" / "_npx"
    if ← npx.isDir then
      for e in (← npx.readDir).qsort (·.fileName < ·.fileName) do
        let m := e.path / "node_modules" / "playwright"
        if ← (m / "package.json").pathExists then cands := cands.push m.toString
  let mut ok : Array String := #[]
  for m in cands do
    let launch := "require(process.env.PW_MODULE).chromium.launch({headless:true,args:['--no-sandbox','--disable-gpu']})" ++
      ".then(b=>b.close()).catch(()=>process.exit(1))"
    let r ← IO.Process.output { cmd := "node", args := #["-e", launch], env := #[("PW_MODULE", some m)] }
    if r.exitCode == 0 then ok := ok.push m
  return ok

def htmlReport (outDir : String) : IO UInt32 := do
  let out : System.FilePath := outDir
  IO.FS.createDirAll out
  let cache ← IO.mkRef #[]
  let faces ← Hermetic.shippedFaces fontsDir
  let oneFace ← oneFaceSet cache
  let names ← fixtureNames
  for n in names do
    let (html, read) ← engineHtml cache faces oneFace n
    IO.FS.writeFile (out / s!"{n}.html") html
    for (cand, bytes) in read do
      let p := out / s!"{n}.assets" / cand
      if let some d := p.parent then IO.FS.createDirAll d
      IO.FS.writeBinFile p bytes
  let module ← match (← playwrightModules).toList with
    | m :: _ => pure m
    | [] =>
      IO.eprintln "rhythm: no Playwright module found (LEANTEX_PLAYWRIGHT names one); the HTML is \
written but not measured"
      return 2
  IO.FS.writeFile (out / "probe.cjs") probeJs
  let r ← IO.Process.output
    { cmd := "node", args := #[(out / "probe.cjs").toString, out.toString] ++ names
      env := #[("PW_MODULE", some module)] }
  IO.FS.writeFile (out / "probe.tsv") r.stdout
  if r.exitCode != 0 then
    IO.eprintln s!"rhythm: the probe exited {r.exitCode}: {r.stderr}"
    return 2
  -- The probe's lines back as pages the declarations read: CSS px scaled to
  -- sp at 65536 per px, so every predicate above applies unchanged.
  let pxSp (s : String) : Int := (parseMilli s).getD 0 * spPerBp / 1000
  let mut pages : Array (String × MPage) := #[]
  let mut leadings : Array (String × Int) := #[]
  let mut version := "?"
  for l in r.stdout.splitOn "\n" do
    match l.splitOn "\t" with
    | ["version", v] => version := v
    | ["page", n, lead] =>
      pages := pages.push (n, { lines := #[], marks := #[] })
      leadings := leadings.push (n, pxSp lead)
    | ["line", n, y, t] =>
      pages := pages.map fun (m, p) =>
        if m == n then (m, { p with lines := p.lines.push { y := pxSp y, text := t } }) else (m, p)
    | ["mark", n, t, b] =>
      pages := pages.map fun (m, p) =>
        if m == n then (m, { p with marks := p.marks.push (pxSp t, pxSp b) }) else (m, p)
    | _ => pure ()
  let ms ← match ← measureAll with
    | .ok ms => pure ms
    | .error faults =>
      for f in faults do IO.eprintln s!"rhythm: fault: {f}"
      return 2
  IO.println s!"# chromium {version}; engine PDF measured in process; the HTML emitted in process \
and measured by the browser; lengths bp (PDF) and CSS px (HTML); q = that context's rhythm quantum"
  IO.println "fixture\tclass\tmarker\tkind\tpdf_bp\tpdf_q\tref_bp\tref_q\thtml_px\thtml_q\tpdf-ref_q\thtml-pdf_q"
  for m in ms do
    let qPdf ← pdfQuantumMilli m.fixture
    let lead := ((leadings.find? (·.1 == m.fixture)).map (·.2)).getD 0
    let qHtml := milliBpOfSp (lead / 2)
    let html : Except String Int := match pages.find? (·.1 == m.fixture) with
      | some (_, p) =>
        if m.row.spec.kind == .top then .error "a page's top is not a screen's"
        else match openFault #[p] m.row.spec with
          | some why => .error why
          | none => (gapOf #[p] m.row.spec).map milliBpOfSp
      | none => .error "not measured"
    let showQ (v : Except String Int) (q : Int) : String × String := match v with
      | .ok x => (showMilli x, inQuanta x q)
      | .error _ => ("-", "-")
    let (pb, pq) := showQ m.engine qPdf
    let (rb, rq) := showQ (.ok m.row.milliBp) qPdf
    let (hb, hq) := showQ html qHtml
    let dPR := match m.engine with
      | .ok e => inQuanta (e - m.row.milliBp) qPdf
      | .error _ => "-"
    let dHP := match m.engine, html with
      | .ok e, .ok h => inQuanta (h * qPdf - e * qHtml) (qPdf * qHtml)
      | _, _ => "-"
    IO.println s!"{m.fixture}\t{m.row.spec.cls}\t{m.row.spec.marker}\t{m.row.spec.kind.name}\t\
{pb}\t{pq}\t{rb}\t{rq}\t{hb}\t{hq}\t{dPR}\t{dHP}"
  return 0

/-! ## The private documents (a report; never a gate, never the tree)

A document with no markers is read by pairing: each engine line whose
structure tag opens a new marked-content sequence is a block boundary, and
the reference line whose first twelve letters match it on the same page is
the same boundary there. The gap on each side is the baseline of the line
above it to its own. A boundary is classed by the engine's tags on either
side (`P-P`, `H2-P`, `LI-LI`, …), with whether a picture or an image stands
between.

It reads private inputs, so it is structurally unable to write into the
repository: it writes only into a directory named on the command line, and
refuses one that resolves inside the working tree. What it writes carries no
text of the document: page numbers, tags and lengths. -/

/-- A line's structure: the tag and marked-content id of its first run's
innermost content mark, as the engine's writer wrote it. -/
def lineTag (rs : Array ArtRun) : Option (String × Nat) :=
  rs.findSome? fun r => r.marks.reverse.findSome? fun m => match m with
    | .content t n => some (t, n)
    | .artifact _ => none

structure PLine where
  y : Int
  key : String
  tag : Option (String × Nat)
  deriving Inhabited

/-- A page's lines for pairing: baseline, the first twelve letters of the
text (the pairing key, never written out), and the structure tag. -/
def pairLines (p : ArtPage) : Array PLine := Id.run do
  let top := p.media.2.2.2
  let mut ys : Array Int := #[]
  let mut runs : Array (Array ArtRun) := #[]
  for r in p.runs do
    match ys.findIdx? (· == r.y) with
    | some i => runs := runs.modify i (·.push r)
    | none =>
      ys := ys.push r.y
      runs := runs.push #[r]
  let mut out : Array PLine := #[]
  for i in [0:ys.size] do
    let rs := runs[i]!.qsort (·.x < ·.x)
    let letters := String.ofList ((String.join (rs.toList.map (·.text))).toList.filter Char.isAlpha)
    if letters.length ≥ 3 then
      out := out.push { y := top - ys[i]!, key := String.ofList (letters.toList.take 12), tag := lineTag rs }
  return out.qsort (·.y < ·.y)

/-- Is `dir` inside the working tree? Both sides resolved, so neither a
relative spelling nor a symlink hides the answer. -/
def insideTree (dir : String) : IO Bool := do
  IO.FS.createDirAll dir
  let d ← IO.FS.realPath dir
  let t ← IO.FS.realPath "."
  return d == t || d.toString.startsWith (t.toString ++ "/")

def privateReport (enginePdf refPdf outDir label : String) (probe : Option String := none) :
    IO UInt32 := do
  if ← insideTree outDir then
    IO.eprintln "rhythm: refusing: the private report writes only outside the working tree"
    return 2
  let read (f : String) : IO (Array ArtPage) := do
    match readArtifact (← IO.FS.readBinFile f) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"{f}: {e}")
  let eng ← read enginePdf
  let ref ← read refPdf
  -- The HTML page's lines, when a browser measured it (`probeJs`'s output
  -- over the engine's own page): baselines in CSS px as sp, one document.
  let keyOfText (t : String) : String :=
    String.ofList ((t.toList.filter Char.isAlpha).take 12)
  let mut html : Array (Int × String) := #[]
  let mut lead : Int := 0
  if let some pf := probe then
    for l in (← IO.FS.readFile pf).splitOn "\n" do
      match l.splitOn "\t" with
      | ["line", _, y, t] =>
        if (keyOfText t).length ≥ 3 then
          html := html.push ((parseMilli y).getD 0 * spPerBp / 1000, keyOfText t)
      | ["page", _, v] => lead := (parseMilli v).getD 0 * spPerBp / 1000
      | _ => pure ()
  let mut cursor := 0
  let mut rows : Array String :=
    #["page\tabove\tbelow\tmarks\tengine_bp\treference_bp\tdelta_bp\thtml_px\thtml_lead_px"]
  for pi in [0:eng.size] do
    let el := pairLines eng[pi]!
    let rl := (ref[pi]?.map pairLines).getD #[]
    let emarks := ctmMarks eng[pi]!.content
    let etop := eng[pi]!.media.2.2.2
    for i in [1:el.size] do
      let me := el[i]!
      let up := el[i - 1]!
      let opens := match me.tag, up.tag with
        | some (_, a), some (_, b) => a != b
        | _, _ => true
      if !opens then continue
      let tagName (t : Option (String × Nat)) : String := (t.map (·.1)).getD "none"
      -- A mark stands between only when it lies inside the band: a page's
      -- ground or a title bar overlaps every band and stands between none.
      let between := emarks.any fun (_, y0, _, y1) => etop - y1 ≥ up.y && etop - y0 ≤ me.y
      let egap := me.y - up.y
      let rgap : Option Int := do
        let j ← rl.findIdx? (·.key == me.key)
        if j == 0 then none
        some (rl[j]!.y - rl[j - 1]!.y)
      let (rb, d) := match rgap with
        | some g => (showMilli (milliBpOfSp g), showMilli (milliBpOfSp (egap - g)))
        | none => ("-", "-")
      -- The HTML twin of the same boundary: the next line in document order
      -- with the same key, and the line standing above it on the screen.
      let mut hb := "-"
      match (html.extract cursor html.size).findIdx? (·.2 == me.key) with
      | some k =>
        let j := cursor + k
        cursor := j + 1
        let above := html.filter fun (y, _) => y < html[j]!.1
        if let some (ya, _) := above.foldl (fun (acc : Option (Int × String)) h =>
            match acc with
            | some a => if a.1 < h.1 then some h else some a
            | none => some h) none then
          hb := showMilli (milliBpOfSp (html[j]!.1 - ya))
      | none => pure ()
      rows := rows.push s!"{pi + 1}\t{tagName up.tag}\t{tagName me.tag}\t{if between then "yes" else "no"}\t\
{showMilli (milliBpOfSp egap)}\t{rb}\t{d}\t{hb}\t{showMilli (milliBpOfSp lead)}"
  let path : System.FilePath := outDir / s!"{label}-boundaries.tsv"
  IO.FS.writeFile path ("\n".intercalate rows.toList ++ "\n")
  IO.println s!"rhythm: {rows.size - 1} boundaries over {eng.size} engine pages, {ref.size} reference pages"
  return 0

/-- One page a browser measures with `probeJs`, for a private document's
HTML: its lines go to `<outDir>/probe-<page>.tsv`, and like the report the
probe refuses a directory inside the working tree, because those lines are
the document's text. -/
def probePage (htmlDir page outDir : String) : IO UInt32 := do
  if ← insideTree outDir then
    IO.eprintln "rhythm: refusing: a private page's probe writes only outside the working tree"
    return 2
  let some module := (← playwrightModules)[0]?
    | IO.eprintln "rhythm: no Playwright module launches a Chromium here"; return 2
  let js : System.FilePath := (outDir : System.FilePath) / "probe.cjs"
  IO.FS.writeFile js probeJs
  let r ← IO.Process.output
    { cmd := "node", args := #[js.toString, htmlDir, page], env := #[("PW_MODULE", some module)] }
  IO.FS.writeFile ((outDir : System.FilePath) / s!"probe-{page}.tsv") r.stdout
  if r.exitCode != 0 then
    IO.eprintln s!"rhythm: the probe exited {r.exitCode}"
    return 2
  return 0

/-! ## The reference, measured (needs lualatex; never a gate) -/

def lualatex : String := "lualatex"

/-- The format line of a LaTeX log: `LaTeX2e <…>`. -/
def formatOf (log : String) : String :=
  ((log.splitOn "\n").find? (·.startsWith "LaTeX2e <")).getD "unknown"

/-- Build one fixture's reference in a scratch directory and measure it.
The source is compiled where it stands, so its relative paths (the shipped
faces) resolve as they do for the engine; nothing is written beside it
except the `.ref` the measurement produces. -/
def referenceOf (fx : Fixture) (src : String) : IO (Except String RefFile) := do
  let texName := fx.refSrc.getD s!"{fx.name}.tex"
  let texSrc ← if fx.refSrc.isSome then readFileOr s!"{rhythmDir}/{texName}" else pure src
  if texSrc.isEmpty then return .error s!"{fx.name}: {rhythmDir}/{texName} is absent or empty"
  let work ← IO.FS.createTempDir
  try
    let run : IO IO.Process.Output := IO.Process.output
      { cmd := lualatex
        args := #["-halt-on-error", "-interaction=nonstopmode", "-file-line-error",
                  s!"-output-directory={work}", s!"-jobname={fx.name}", texName]
        cwd := some rhythmDir
        env := #[("SOURCE_DATE_EPOCH", some "0"), ("FORCE_SOURCE_DATE", some "1")] }
    let r1 ← run
    if r1.exitCode != 0 then
      return .error s!"{fx.name}: lualatex refused {texName} (exit {r1.exitCode}); \
its log: {work}/{fx.name}.log\n{r1.stdout.takeEnd 1200}"
    let r2 ← run
    if r2.exitCode != 0 then
      return .error s!"{fx.name}: lualatex's second run failed (exit {r2.exitCode})"
    let pdf ← IO.FS.readBinFile (work / s!"{fx.name}.pdf")
    let pages ← match readArtifact pdf with
      | .ok ps => pure (ps.map ofArt)
      | .error e => return .error s!"{fx.name}: the reference PDF does not read: {e}"
    -- The reference's premise, as it can be checked without structure: every
    -- marker is found, and the markers stand in the order the fixture
    -- declares them — so each line above is the previous block's.
    let mut rows : Array RefRow := #[]
    let mut last : Option (Nat × Int) := none
    for s in fx.specs do
      if let some why := openFault pages s then
        return .error s!"{fx.name}: in the reference, {why}; declare the word that opens the line"
      match gapOf pages s with
      | .error e => return .error s!"{fx.name}: the reference has no gap for '{s.cls} {s.marker} \
{s.kind.name}': {e}"
      | .ok v =>
        rows := rows.push { spec := s, milliBp := milliBpOfSp v }
        if s.kind != .top then
          let some (i, j) := findMarker pages s.marker | pure ()
          let y := pages[i]!.lines[j]!.y
          if let some (li, ly) := last then
            if i < li || (i == li && y < ly) then
              return .error s!"{fx.name}: the reference sets '{s.marker}' above a marker \
declared before it, so the line above it is not the previous boundary's block"
          last := some (i, y)
    let log ← readFileOr (work / s!"{fx.name}.log").toString
    let ver ← IO.Process.output { cmd := lualatex, args := #["--version"] }
    return .ok
      { fixture := fx.name, srcKey := keyOf src, refSrc := texName, refSrcKey := keyOf texSrc
        engine := ((ver.stdout.splitOn "\n").headD "").trimAscii.toString
        format := formatOf log, rows }
  finally
    IO.FS.removeDirAll work

def reference (names : List String) (verify : Bool := false) : IO UInt32 := do
  let all ← fixtureNames
  let names := if names.isEmpty then all.toList else names
  let mut bad := 0
  for n in names do
    let src ← readFileOr s!"{rhythmDir}/{n}.tex"
    match parseFixture n src with
    | .error e =>
      IO.eprintln s!"rhythm: {e}"
      bad := bad + 1
    | .ok fx =>
      match ← referenceOf fx src with
      | .error e =>
        IO.eprintln s!"rhythm: {e}"
        bad := bad + 1
      | .ok r =>
        if verify then
          -- The committed numbers are only as good as their reproducibility:
          -- rebuild each one and hold it to the file, byte for byte.
          let committed ← readFileOr (refPath n)
          if committed == r.render then IO.println s!"rhythm: {refPath n} reproduces"
          else
            IO.eprintln s!"rhythm: {refPath n} does not reproduce on this host; a fresh \
measurement differs from the committed file"
            bad := bad + 1
        else
          IO.FS.writeFile (refPath n) r.render
          IO.println s!"rhythm: wrote {refPath n} ({r.rows.size} boundaries)"
  return (if bad == 0 then 0 else 1)

/-! ## Selftest -/

def selftest : IO UInt32 := tierSelftest "rhythm" fun no => do
  let bp (n : Int) : Int := n * spPerBp
  -- Units: sp to thousandths of a bp, rounded symmetrically, and back.
  no "units: 12 bp is 12.000" (showMilli (milliBpOfSp (bp 12)) == "12.000")
  no "units: -0.5 bp is -0.500" (showMilli (milliBpOfSp (-(spPerBp / 2))) == "-0.500")
  no "units: parse reads three decimals" (parseMilli "17.933" == some 17933)
  no "units: parse reads a negative" (parseMilli "-0.25" == some (-250))
  no "units: parse refuses four decimals" (parseMilli "1.2345").isNone
  -- The format: a round trip, and the empty value's round trip.
  let s1 : Spec := { cls := "par-par", marker := "Birch", kind := .span }
  let full : RefFile :=
    { fixture := "f", srcKey := "K1", refSrc := "f.tex", refSrcKey := "K2", engine := "E"
      format := "LaTeX2e <x>", rows := #[{ spec := s1, milliBp := 17933 },
        { spec := { s1 with kind := .top, marker := "=1" }, milliBp := -5 }] }
  no "format: a full record round-trips" (RefFile.parse full.render == .ok full)
  let empty : RefFile := default
  no "format: the empty record round-trips (every field empty, no rows)"
    (RefFile.parse empty.render == .ok empty)
  no "format: a record missing its unit line is refused"
    (RefFile.parse ((full.render.splitOn "\n").filter (!·.startsWith "unit:") |> "\n".intercalate)
      |>.toOption).isNone
  -- Declarations: a bad kind, a bad class, a repeat, no boundary, no purpose.
  let hdr := "% rhythm: x\n"
  no "fixture: a well-formed declaration parses"
    ((parseFixture "f" (hdr ++ "% boundary: par-par Birch span\n")).toOption.map (·.specs.size) == some 1)
  no "fixture: an unknown kind is refused"
    (parseFixture "f" (hdr ++ "% boundary: par-par Birch sideways\n")).toOption.isNone
  no "fixture: a class outside [a-z0-9-] is refused"
    (parseFixture "f" (hdr ++ "% boundary: Par Birch span\n")).toOption.isNone
  no "fixture: a boundary declared twice is refused"
    (parseFixture "f" (hdr ++ "% boundary: a B span\n% boundary: a B span\n")).toOption.isNone
  no "fixture: a fixture with no boundary is refused" (parseFixture "f" hdr).toOption.isNone
  no "fixture: a fixture that does not say what it probes is refused"
    (parseFixture "f" "% boundary: a B span\n").toOption.isNone
  -- The marker as a word: digits may touch it, letters may not.
  no "word: a section number set against its title still names it" (holdsWord "1Cedar heading" "Cedar")
  no "word: a spaced number names it" (holdsWord "1 Cedar heading" "Cedar")
  no "word: a longer word does not" (!holdsWord "Cedars grow" "Cedar")
  no "word: a word ending in it does not" (!holdsWord "RedCedar" "Cedar")
  no "word: a word at the line's end does" (holdsWord "under Cedar" "Cedar")
  -- The reference's marks are read under the transformation in force: a
  -- path written inside a picture's own `cm` stands where the `cm` puts it.
  let content := "q 1 0 0 1 100 200 cm 0 0 m 10 0 l 10 20 l S Q 5 5 20 10 re f".toUTF8
  no s!"marks: a path inside cm is moved by it: {ctmMarks content}"
    (ctmMarks content == #[(bp 100, bp 200, bp 110, bp 220), (bp 5, bp 5, bp 25, bp 15)])
  let scaled := "q 2 0 0 3 10 10 cm 0 0 m 1 1 l S Q q 50 0 0 40 7 9 cm /Im1 Do Q".toUTF8
  no s!"marks: scale composes, and an image is its unit square mapped: {ctmMarks scaled}"
    (ctmMarks scaled == #[(bp 10, bp 10, bp 12, bp 13), (bp 7, bp 9, bp 57, bp 49)])
  -- Polygon coordinates rise from a line's baseline; page marks run down.
  -- Seed bounds from a vertex so the baseline itself adds no phantom ink.
  let polygonMarks (pts : Array (Int × Int)) : Array (Int × Int) :=
    let line : Layout.LineOut :=
      { x := 0, y := bp 160, size := bp 12
        segs := #[.poly pts Ir.Color.black], setWidth := 0 }
    (ofOut { pages := #[{ lines := #[line] }], diags := #[] }).flatMap (·.marks)
  no "marks: a polygon spanning its baseline has both extents"
    (polygonMarks #[(0, bp 5), (bp 10, bp (-10)), (bp 20, bp 20)] == #[(bp 140, bp 170)])
  no "marks: a polygon wholly above the baseline stops above it"
    (polygonMarks #[(0, bp 5), (bp 10, bp 20), (bp 20, bp 10)] == #[(bp 140, bp 155)])
  no "marks: a polygon wholly below the baseline starts below it"
    (polygonMarks #[(0, bp (-5)), (bp 10, bp (-20)), (bp 20, bp (-10))] == #[(bp 165, bp 180)])
  no "marks: an empty polygon paints nothing" (polygonMarks #[] == #[])
  let polygonPage : MPage :=
    { lines := #[{ y := bp 100, text := "Alder", leaf := some 0 },
                  { y := bp 200, text := "Birch", leaf := some 1 }]
      marks := polygonMarks #[(0, bp 20), (bp 10, bp (-10)), (bp 20, 0)] }
  no "gap: above includes polygon ink"
    (gapOf #[polygonPage] { cls := "c", marker := "Birch", kind := .above } == .ok (bp 40))
  no "gap: below includes polygon ink"
    (gapOf #[polygonPage] { cls := "c", marker := "Birch", kind := .below } == .ok (bp 30))
  -- The premise's first half: a marker opens its line.
  let merged : MPage := { lines := #[{ y := bp 100, text := "Elm ends here. Hazel starts", leaf := some 4 },
    { y := bp 112, text := "• Birch item", leaf := some 5 }], marks := #[] }
  no "open: a marker inside a line is named" (openFault #[merged] { cls := "c", marker := "Hazel", kind := .span }).isSome
  no "open: a bullet before the marker is not a word" (openFault #[merged] { cls := "c", marker := "Birch", kind := .span }).isNone
  no "open: a section number before the marker is not a word" (firstWord "1.1Hazel sub" == some "Hazel")
  -- The measurement over hand-written pages.
  let pg : MPage :=
    { lines := #[{ y := bp 100, text := "Alder one", leaf := some 0 },
                 { y := bp 112, text := "more of Alder", leaf := some 0 },
                 { y := bp 130, text := "Birch two", leaf := some 1 },
                 { y := bp 200, text := "Cedar three", leaf := some 3 },
                 { y := bp 700, text := "1", furniture := true }]
      marks := #[(bp 140, bp 180)] }
  let g (m : String) (k : Kind) := gapOf #[pg] { cls := "c", marker := m, kind := k }
  no "gap: span reads the line above, not the block's first line"
    (g "Birch" .span == .ok (bp 18))
  no "gap: above reads to the top of the marks between" (g "Cedar" .above == .ok (bp 10))
  no "gap: below reads from the bottom of the marks between" (g "Cedar" .below == .ok (bp 20))
  no "gap: top reads from the page's edge" (g "Birch" .top == .ok (bp 130))
  no "gap: a whole-line marker names the furniture line" (g "=1" .top == .ok (bp 700))
  no "gap: furniture is not the line above body text"
    (gapOf #[{ pg with lines := pg.lines.push { y := bp 199, text := "x", furniture := true } }]
      { cls := "c", marker := "Cedar", kind := .span } == .ok (bp 70))
  no "gap: a raised mark with no letter is not the line above"
    (gapOf #[{ pg with lines := pg.lines.push { y := bp 197, text := "1" } }]
      { cls := "c", marker := "Cedar", kind := .span } == .ok (bp 70))
  no "gap: a missing marker has no gap" (g "Yew" .span).toOption.isNone
  no "gap: a marker opening its page has no gap" (g "Alder" .span).toOption.isNone
  no "gap: no mark between has no above" (g "Birch" .above).toOption.isNone
  -- The premise: a marker inside its block is a fault, at its block's head it is not.
  no "premise: a marker opening its block holds"
    (premiseFault #[pg] { cls := "c", marker := "Birch", kind := .span }).isNone
  no "premise: a marker inside its block is named"
    (premiseFault #[pg] { cls := "c", marker := "more", kind := .span }).isSome
  -- The comparison level and its blind spot: under the tolerance apart reads
  -- equal here and unequal to the exact comparison above it; over it, unequal.
  let row : RefRow := { spec := s1, milliBp := 18000 }
  let at04 : Measured := { fixture := "f", row, engine := .ok 18400 }
  let at06 : Measured := { fixture := "f", row, engine := .ok 18600 }
  let at29 : Measured := { fixture := "f", row, engine := .ok 15100 }
  let at31 : Measured := { fixture := "f", row, engine := .ok 21100 }
  let unmeasured : Measured := { at04 with engine := .error "x" }
  no "level: 0.4 bp apart is within the tolerance" at04.within
  no "level: 0.4 bp apart is not exact (the level above sees it)" (!at04.within 0)
  no "level: 0.6 bp apart is outside the tolerance" (!at06.within)
  no "level: an unmeasured engine side is outside" (!unmeasured.within)
  no "band: 0.4 and 2.9 bp apart are both near (it is blind between them)" (at04.near && at29.near)
  no "band: 0.4 and 2.9 bp apart differ under within (the level above sees it)"
    (at04.within && !at29.within)
  no "band: 3.1 bp apart is outside it" (!at31.near)
  no "band: an unmeasured engine side is outside it" (!unmeasured.near)
  no "band: half the rhythm quantum at the article base"
    (nearMilliBp == milliBpOfSp (Ir.rhythmQuantum Ir.baseFontSize) / 2)
  -- The rows: three per fixture and class, in the order first met.
  let rs := rowsOf #[at04, at06, at31, { at04 with row := { row with spec := { s1 with cls := "a-b" } } }]
  no s!"rows: within, near and boundaries: {rs.map (fun r => (r.item, r.value))}"
    (rs.map (fun r => (r.item, r.value)) ==
      #[("f/par-par.within", 1), ("f/par-par.near", 2), ("f/par-par.boundaries", 3),
        ("f/a-b.within", 1), ("f/a-b.near", 1), ("f/a-b.boundaries", 1)])

end Rhythm

def main (args : List String) : IO UInt32 := do
  match args with
  | "--reference" :: names => Rhythm.reference names
  | "--verify-reference" :: names => Rhythm.reference names (verify := true)
  | ["--table"] => Rhythm.table
  | ["--lines", name] => Rhythm.dumpLines name
  | ["--html", dir] => Rhythm.htmlReport dir
  | ["--private", eng, ref, dir, label] => Rhythm.privateReport eng ref dir label
  | ["--private", eng, ref, dir, label, probe] => Rhythm.privateReport eng ref dir label (some probe)
  | ["--probe", htmlDir, page, dir] => Rhythm.probePage htmlDir page dir
  | _ => tierMain "rhythm" (.pairs "within" "boundaries") Rhythm.tierMeasure Rhythm.selftest args
