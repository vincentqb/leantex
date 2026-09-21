import LeanTex.Core.Dim
import LeanTex.Core.Layout

/-!
# PDF content streams as typed operators

A page's content stream is built as an `Array ContentOp` — one constructor
per painting operator the writer emits — and rendered by `render`, a pure
serializer with an equational theory (`content_render_exact` and its
per-constructor twins). The construction (`contentOps`) is the layout
walk that decides pen moves, `TJ` arrays, and graphics-state changes; the
rendering is spelling only. Marked content (`BDC`/`BMC` … `EMC`) is one
constructor, `marked (tag) (body)`, on both the text object's operators
and the page's: an ill-nested pair is unrepresentable, the body's ink is
what it was (`mark_ink_exact`), and `render` opens and closes each
sequence on lines of its own (`render_lines_exact`), so the stream with
those lines removed is the stream of the unwrapped operators.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Layout

/-- One hexadecimal digit of `n`'s low nibble, upper case. -/
def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

/-- `acc` with a glyph id's four hex digits pushed — the digits an
Identity-H CID string spells (ISO 32000-2 §9.7.4.2: two bytes per CID).
Pushing in place is the hot path (every glyph on every page); `gidHex` is
its four-character value, `pushGid_eq` the equation between them. -/
def pushGid (acc : String) (g : Nat) : String :=
  (((acc.push (hexDigit (g / 4096))).push (hexDigit (g / 256))).push (hexDigit (g / 16))).push
    (hexDigit g)

def gidHex (g : Nat) : String := pushGid "" g

theorem pushGid_eq (acc : String) (g : Nat) : pushGid acc g = acc ++ gidHex g := by
  simp only [pushGid, gidHex, String.push_eq_append, String.empty_append, String.append_assoc]

/-- Path construction operators, ISO 32000-2 §8.5.2 (Table 58). -/
inductive PathOp where
  | moveTo (x y : Sp)
  | lineTo (x y : Sp)
  | curveTo (x1 y1 x2 y2 x3 y3 : Sp)
  | close
  | rect (x y w h : Sp)
  deriving Repr, BEq, Inhabited

/-- One element of a `TJ` array (§9.4.3): a glyph string, or a horizontal
adjustment in thousandths of the text space unit. -/
inductive TextItem where
  | glyphs (gids : Array Nat)
  | adjust (d : Int)
  deriving Repr, BEq, Inhabited

/-- Artifact types, ISO 32000-2 §14.8.2.2.2 Table 363: `/Pagination` for
running heads, feet and page numbers, `/Layout` for rules, fills and
bars, `/Page` for cut marks and printer's marks. -/
inductive ArtifactKind where
  | pagination
  | layout
  | page
  deriving Repr, BEq, Inhabited

/-- The tag a marked-content sequence opens with (§14.6.2). An artifact
carries its type when the emission site knows it; a page fill carries
none, because the layout ships backgrounds, bars and cut marks in one
array and the writer will not guess between `/Layout` and `/Page`. -/
inductive MarkTag where
  | artifact (kind : Option ArtifactKind)
  deriving Repr, BEq, Inhabited

/-- The line that opens the sequence: the tag and its property dictionary
before `BDC` (Table 352), or the tag alone before `BMC` when there are no
properties to give (§14.6.1 — `BDC` takes two operands; a bare tag before
it is a syntax error on which a reader drops the rest of the page). Closed
literals: the opener is spelled once per rule and once per fill group on
every page. -/
def MarkTag.opener : MarkTag → String
  | .artifact none => "/Artifact BMC"
  | .artifact (some .pagination) => "/Artifact << /Type /Pagination >> BDC"
  | .artifact (some .layout) => "/Artifact << /Type /Layout >> BDC"
  | .artifact (some .page) => "/Artifact << /Type /Page >> BDC"

/-- Text-object operators (§9.3–9.4): horizontal scale in per-mille,
text matrix, font resource and size, fill colour, and one `TJ` array;
and a marked-content sequence (§14.6: `BDC … EMC` may nest inside
`BT … ET`) — the only spelling of the pair, so an unbalanced one is
unrepresentable. -/
inductive TextOp where
  | scale (permille : Int)
  | move (x y : Sp)
  | font (res : Nat) (size : Sp)
  | color (c : Ir.Color)
  | show (items : Array TextItem)
  | marked (tag : MarkTag) (body : Array TextOp)
  deriving Repr, BEq, Inhabited

/-- One page-level painting operation, in PDF user space. -/
inductive ContentOp where
  /-- A filled rectangle: a page fill or a rule. -/
  | fill (color : Ir.Color) (x y w h : Sp)
  /-- A picture path with its declared paint; the painting operator
  (`B`/`S`/`f`/`n`) is decided by which paints are present. -/
  | path (fill : Option Ir.Color) (stroke : Option Ir.Pic.Stroke) (segs : Array PathOp)
  /-- The page's one text object, `BT … ET`. -/
  | text (ops : Array TextOp)
  /-- An image XObject mapped onto `w × h` at `(x, y)`. -/
  | image (x y w h : Sp) (res : Nat)
  /-- The outlined box standing where an image that did not load would. -/
  | imageMissing (x y w h : Sp)
  /-- A marked-content sequence around page-level operations. -/
  | marked (tag : MarkTag) (body : Array ContentOp)
  deriving Repr, BEq, Inhabited

def PathOp.render : PathOp → String
  | .moveTo x y => s!"{x.toPtString} {y.toPtString} m "
  | .lineTo x y => s!"{x.toPtString} {y.toPtString} l "
  | .curveTo x1 y1 x2 y2 x3 y3 =>
    s!"{x1.toPtString} {y1.toPtString} {x2.toPtString} {y2.toPtString} \
{x3.toPtString} {y3.toPtString} c "
  | .close => "h "
  | .rect x y w h => s!"{x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re "

def TextItem.render : TextItem → String
  | .glyphs gids => (gids.foldl pushGid "<").push '>'
  | .adjust d => toString d

mutual

/-- One text operator, without its line end: the text object and a marked
sequence each put every operator on a line of its own. -/
def TextOp.render : TextOp → String
  | .scale p => s!"{p / 10}.{p % 10} Tz"
  | .move x y => s!"1 0 0 1 {x.toPtString} {y.toPtString} Tm"
  | .font res size => s!"/F{res + 1} {size.toPtString} Tf"
  | .color c => c.pdfFill
  | .show items => (items.foldl (fun acc it => acc ++ it.render) "[") ++ "] TJ"
  | .marked t body => TextOp.renderLines (t.opener ++ "\n") body.toList ++ "EMC"

/-- The operators onto `acc`, each followed by its line end. -/
def TextOp.renderLines (acc : String) : List TextOp → String
  | [] => acc
  | o :: rest => TextOp.renderLines (acc ++ o.render ++ "\n") rest

end

/-- Dash patterns, §8.4.3.6, with pgf's rhythms (pgf manual §15.3.2:
dashed on 3 pt off 3 pt, dotted on the line width off 1 pt). -/
def dashOp (st : Ir.Pic.Stroke) : String :=
  match st.dash with
  | .solid => ""
  | .dashed => "[3 3] 0 d "
  | .dotted => s!"[{st.width.toPtString} 1] 0 d "

/-- The path-painting operator the declared paints select (§8.5.3, Table
60): `B` fills then strokes, `S` strokes, `f` fills, `n` ends the path
without painting. -/
def paintOp : Option Ir.Pic.Stroke → Option Ir.Color → String
  | some _, some _ => "B"
  | some _, none => "S"
  | none, some _ => "f"
  | none, none => "n"

def strokeOp : Option Ir.Pic.Stroke → String
  | some st =>
    let dash := dashOp st
    s!"{st.color.pdfStroke} {st.width.toPtString} w " ++ dash
  | none => ""

def fillOp : Option Ir.Color → String
  | some c => s!"{c.pdfFill} "
  | none => ""

mutual

def ContentOp.render : ContentOp → String
  | .fill c x y w h =>
    s!"q {c.pdfFill} {x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re f Q"
  | .path fl st segs =>
    let fillS := fillOp fl
    let strokeS := strokeOp st
    let head := "q " ++ fillS ++ strokeS
    let body := segs.foldl (fun acc seg => acc ++ seg.render) head
    body ++ paintOp st fl ++ " Q"
  | .text ops => (ops.foldl (fun acc op => acc ++ op.render ++ "\n") "BT\n") ++ "ET"
  | .image x y w h res =>
    s!"q {w.toPtString} 0 0 {h.toPtString} {x.toPtString} {y.toPtString} cm /Im{res + 1} Do Q"
  | .imageMissing x y w h =>
    -- A neutral grey hairline box: the failure is visible where the figure
    -- would stand, and the diagnostic already said why.
    s!"q 0.62 0.62 0.66 RG 0.75 w {x.toPtString} {y.toPtString} {w.toPtString} \
{h.toPtString} re S Q"
  | .marked t body => ContentOp.renderLines (t.opener ++ "\n") body.toList ++ "EMC"

/-- The operations onto `acc`, each followed by its line end. -/
def ContentOp.renderLines (acc : String) : List ContentOp → String
  | [] => acc
  | o :: rest => ContentOp.renderLines (acc ++ o.render ++ "\n") rest

end

/-- One step of `render`: the first operation opens the stream, every
later one follows a newline. -/
def renderStep : Option String → ContentOp → Option String
  | none, op => some op.render
  | some s, op => some (s ++ "\n" ++ op.render)

/-- The stream: operations one per line. -/
def render (ops : Array ContentOp) : String := (ops.foldl renderStep none).getD ""

/-! ## Construction: the layout walk -/

/-- The text object's walk state. `items` is the open `TJ` array — empty
exactly when no array is open. `font` is the layout face index in force
(`-1` before the first `Tf`), `size` and `color` likewise; `tz` the live
expansion in per-mille delta from 100 %; `x` the layout position; `pen`
where the PDF pen is, once a glyph run has set it. Rules and images
gather here and paint after `ET`: path and `Do` operators may not appear
inside a text object. -/
structure TextSt where
  ops : Array TextOp := #[]
  items : Array TextItem := #[]
  font : Int := -1
  size : Sp := -1
  color : Ir.Color := Ir.Color.black
  tz : Int := 0
  x : Sp := 0
  pen : Option (Sp × Sp) := none
  rules : Array (Ir.Color × Sp × Sp × Sp × Sp) := #[]
  images : Array (Sp × Sp × Sp × Sp × Option Nat) := #[]

def TextSt.op (st : TextSt) (o : TextOp) : TextSt := { st with ops := st.ops.push o }

def TextSt.closeTJ (st : TextSt) : TextSt :=
  if st.items.isEmpty then st else { st with ops := st.ops.push (.show st.items), items := #[] }

/-- Bring the pen to a run at `(st.x, runY)`. Inside an open array with
the face unchanged, a small horizontal move is an adjustment in the live
size — thousandths of the font size times the horizontal scale, so under
expansion the number compensates by the inverse factor, and a viewer that
keeps adjustments in sixteen bits (macOS Preview drops the whole array
past ±32767) never sees one that large. Any other move is an absolute
`Tm`, and closes the array. A fresh line has no pen until its first run
sets one. -/
def adjustFor (dx size tz : Int) : Int :=
  let v0 := dx * 1000 / size
  if tz == 0 then v0 else v0 * 1000 / (1000 + tz)

def TextSt.toPen (st : TextSt) (changes : Bool) (runY : Sp) : TextSt :=
  match st.pen with
  | some (hx, hy) =>
    if hx != st.x || hy != runY then
      let v := adjustFor (st.x - hx) st.size st.tz
      if !st.items.isEmpty && !changes && hy == runY && v.natAbs ≤ 32000 then
        { st with items := st.items.push (.adjust (-v)) }
      else
        st.closeTJ.op (.move st.x runY)
    else st
  | none => st.op (.move st.x runY)

def TextSt.setFont (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) : TextSt :=
  if st.font != (idx : Int) || st.size != size then
    { st.op (.font (remap[idx]?.getD 0) size) with font := idx, size := size }
  else st

def TextSt.setColor (st : TextSt) (color : Ir.Color) : TextSt :=
  if st.color != color then { st.op (.color color) with color := color } else st

/-- A `TJ` array cannot switch fonts or colours mid-array, so a run in a
different face or colour closes it and emits `Tf`/`rg` before reopening. -/
def TextSt.setFace (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp)
    (color : Ir.Color) : TextSt :=
  ((st.closeTJ).setFont remap idx size).setColor color

/-- One glyph run: the pen, then the face and colour when they change,
then the glyphs. A kern (a run with no glyphs) only moves the layout
position, like a gap. -/
def stepRun (remap : Array Nat) (lineSize ypdf : Sp) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Sp) (glyphs : Array (Nat × Char)) (segSize raise : Sp) : TextSt :=
  if glyphs.isEmpty then { st with x := st.x + w } else
  let runY := ypdf + raise
  let size := if segSize == 0 then lineSize else segSize
  let changes := st.font != (idx : Int) || st.size != size || st.color != color
  let st := st.toPen changes runY
  let st := if changes then st.setFace remap idx size color else st
  { st with items := st.items.push (.glyphs (glyphs.map (·.1))), x := st.x + w,
            pen := some (st.x + w, runY) }

def stepSeg (remap : Array Nat) (imgMap : Array (Option Nat)) (lineSize ypdf : Sp)
    (st : TextSt) : Seg → TextSt
  | .rule w thickness raise color =>
    { st with rules := st.rules.push (color, st.x, ypdf + raise, w, thickness), x := st.x + w }
  | .image idx w h =>
    { st with images := st.images.push (st.x, ypdf, w, h, idx.bind fun k => imgMap[k]?.getD none),
              x := st.x + w }
  | .gap w => { st with x := st.x + w }
  | .run idx color _ w glyphs segSize _ raise _ =>
    stepRun remap lineSize ypdf st idx color w glyphs segSize raise

/-- One line's operators, walked from a state whose `ops` are empty: the
expansion factor when it changes (`Tz`, §9.3.4, scales shapes and
advances alike — exactly hz-style expansion, and the run widths layout
emitted are already rescaled by the same factor), then the segments from
the line's left edge with no pen, then the array closed. The result's
`ops` are the line's own, for `stepLine` to append or to wrap. The bleed
shifts everything: layout works in trim coordinates and the trim box sits
`bleed` in from the medium's corner. -/
def lineSt (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (st : TextSt)
    (l : LineOut) : TextSt :=
  let ypdf := geom.bleed + geom.pageH - l.y
  let st : TextSt := { st with ops := #[] }
  let st := if l.expand != st.tz then { st.op (.scale (1000 + l.expand)) with tz := l.expand }
    else st
  let st := { st with x := geom.bleed + l.x, pen := none }
  (l.segs.foldl (stepSeg remap imgMap l.size ypdf) st).closeTJ

/-- The tag every furniture line's operators sit under: running heads,
feet and page numbers are pagination artifacts (Table 363). -/
def furnitureTag : MarkTag := .artifact (some .pagination)

/-- One line onto the text object: a furniture line's operators as one
pagination artifact, a flow line's operators as they are. The origin is
known here and lost after — the line is the unit the layout marks. -/
def stepLine (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (st : TextSt)
    (l : LineOut) : TextSt :=
  let s := lineSt geom remap imgMap st l
  { s with ops := if l.furniture then st.ops.push (.marked furnitureTag s.ops) else st.ops ++ s.ops }

/-- The specification twin of `stepLine`: the same line, nothing wrapped —
what the writer emitted before marked content existed. `mark_ink_exact`
is stated against it. -/
def stepLinePlain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (st : TextSt)
    (l : LineOut) : TextSt :=
  let s := lineSt geom remap imgMap st l
  { s with ops := st.ops ++ s.ops }

/-- A picture path in PDF space: the circle as four cubic Bézier arcs (the
standard k = 4(√2−1)/3 ≈ 0.5523 approximation), a rectangle as `re`, an
edge's segments each opening with a move unless it continues the previous
one, a triangle closed. -/
def pathSegs (geom : Geom) : PagePath → Array PathOp
  | .circle cx cy r =>
    let x := geom.bleed + cx
    let y := geom.bleed + geom.pageH - cy
    let k := r * 5523 / 10000
    #[.moveTo (x + r) y,
      .curveTo (x + r) (y + k) (x + k) (y + r) x (y + r),
      .curveTo (x - k) (y + r) (x - r) (y + k) (x - r) y,
      .curveTo (x - r) (y - k) (x - k) (y - r) x (y - r),
      .curveTo (x + k) (y - r) (x + r) (y - k) (x + r) y,
      .close]
  | .rect rx ry rw rh => #[.rect (geom.bleed + rx) (geom.bleed + geom.pageH - ry - rh) rw rh]
  | .segs segs =>
    let pt (x y : Sp) : Sp × Sp := (geom.bleed + x, geom.bleed + geom.pageH - y)
    let step (acc : Option (Sp × Sp) × Array PathOp) (sg : Ir.Pic.PathSeg) :
        Option (Sp × Sp) × Array PathOp :=
      let (prev, out) := acc
      match sg with
      | .line x1 y1 x2 y2 =>
        let a := pt x1 y1
        let b := pt x2 y2
        let out := if prev != some a then out.push (.moveTo a.1 a.2) else out
        (some b, out.push (.lineTo b.1 b.2))
      | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
        let a := pt x1 y1
        let c1 := pt c1x c1y
        let c2 := pt c2x c2y
        let b := pt x2 y2
        let out := if prev != some a then out.push (.moveTo a.1 a.2) else out
        (some b, out.push (.curveTo c1.1 c1.2 c2.1 c2.2 b.1 b.2))
    (segs.foldl step (none, #[])).2
  | .tri x1 y1 x2 y2 x3 y3 =>
    let pt (x y : Sp) : Sp × Sp := (geom.bleed + x, geom.bleed + geom.pageH - y)
    let a := pt x1 y1
    let b := pt x2 y2
    let c := pt x3 y3
    #[.moveTo a.1 a.2, .lineTo b.1 b.2, .lineTo c.1 c.2, .close]

/-- A single operation under an artifact wrapper. -/
def artifact (kind : Option ArtifactKind) (o : ContentOp) : ContentOp :=
  .marked (.artifact kind) #[o]

/-- A block of operations under one artifact wrapper, or nothing when
there are none: a page's fills are one sequence and its rules another —
one opener and one `EMC` per block, where one per operation cost a
rule-heavy document seven per cent of its size and a fifth of its
writing time for no reader's benefit. -/
def artifactBlock (kind : Option ArtifactKind) (ops : Array ContentOp) : Array ContentOp :=
  if ops.isEmpty then #[] else #[.marked (.artifact kind) ops]

/-- An image that loaded is real content and stays bare (the structure
slice tags it); the placeholder box of one that did not is decoration —
a layout artifact, the diagnostic having already said why. -/
def imageOp (x y w h : Sp) : Option Nat → ContentOp
  | some n => .image x y w h n
  | none => artifact (some .layout) (.imageMissing x y w h)

def imageOpPlain (x y w h : Sp) : Option Nat → ContentOp
  | some n => .image x y w h n
  | none => .imageMissing x y w h

/-- One page's operations: fills first, in order (the page background,
then any bars), as one artifact of no stated type — the layout ships
backgrounds, bars and cut marks in one array; then picture paths bare (a
diagram is real content: the structure slice tags it as a figure, and
wrapping it as an artifact would hide it to pass a rule); then the text
object, with each furniture line a pagination artifact; then the images
the text walk gathered, a placeholder a layout artifact; then the rules
it gathered, as one layout artifact. -/
def contentOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := page.paths.map fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)
  let st := page.lines.foldl (stepLine geom remap imgMap) {}
  let images := st.images.map fun (x, y, w, h, res) => imageOp x y w h res
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let body := (artifactBlock none fills ++ paths).push (.text st.ops)
  (body ++ images) ++ artifactBlock (some .layout) rules

/-- The specification twin of `contentOps`: the same operations with no
marked content — the writer before this layer, kept so `mark_ink_exact`
can name the stream it must reproduce. -/
def contentOpsPlain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := page.paths.map fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)
  let st := page.lines.foldl (stepLinePlain geom remap imgMap) {}
  let images := st.images.map fun (x, y, w, h, res) => imageOpPlain x y w h res
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let body := (fills ++ paths).push (.text st.ops)
  (body ++ images) ++ rules

/-! ## The glyph census -/

/-- The glyph runs an item carries: a `TJ` string is one run, an
adjustment none. -/
def TextItem.runs : TextItem → List (Array Nat)
  | .glyphs gids => [gids]
  | .adjust _ => []

mutual

def TextOp.runs : TextOp → List (Array Nat)
  | .scale _ => []
  | .move _ _ => []
  | .font _ _ => []
  | .color _ => []
  | .show items => items.toList.flatMap TextItem.runs
  | .marked _ body => TextOp.runsList body.toList

def TextOp.runsList : List TextOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := TextOp.runsList rest
    o.runs ++ tail

end

mutual

def ContentOp.runs : ContentOp → List (Array Nat)
  | .fill _ _ _ _ _ => []
  | .path _ _ _ => []
  | .text ops => ops.toList.flatMap TextOp.runs
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => ContentOp.runsList body.toList

def ContentOp.runsList : List ContentOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := ContentOp.runsList rest
    o.runs ++ tail

end

/-- Every glyph run a content stream paints, in stream order. -/
def runsOf (ops : Array ContentOp) : List (Array Nat) := ops.toList.flatMap ContentOp.runs

/-! ## Marked content: the line spec and the ink underneath -/

/-- One line of a content stream as the renderer lays it: an operator's
spelling, the opener with its tag (`BDC`, or `BMC` when the tag carries
no properties), or an `EMC`. `lines` is the structural
spec `render` computes (`render_lines_exact`): a fact about which lines
open and close sequences is stated here, and reaches the bytes through
that theorem. -/
inductive Line where
  | op (s : String)
  | open (tag : MarkTag)
  | emc
  deriving Repr, BEq, Inhabited

def Line.render : Line → String
  | .op s => s
  | .open t => t.opener
  | .emc => "EMC"

def Line.isOpen : Line → Bool
  | .open _ => true
  | .op _ => false
  | .emc => false

def Line.isEmc : Line → Bool
  | .emc => true
  | .op _ => false
  | .open _ => false

/-- The marked-content lines dropped: what a strip of `BDC`/`EMC` lines
leaves of a stream. -/
def stripMarks (ls : List Line) : List Line := ls.filter fun l => !l.isOpen && !l.isEmc

mutual

def TextOp.lines : TextOp → List Line
  | .scale p => [.op (TextOp.render (.scale p))]
  | .move x y => [.op (TextOp.render (.move x y))]
  | .font res size => [.op (TextOp.render (.font res size))]
  | .color c => [.op (TextOp.render (.color c))]
  | .show items => [.op (TextOp.render (.show items))]
  | .marked t body => .open t :: (TextOp.linesList body.toList ++ [.emc])

def TextOp.linesList : List TextOp → List Line
  | [] => []
  | o :: rest =>
    let tail := TextOp.linesList rest
    o.lines ++ tail

end

mutual

def ContentOp.lines : ContentOp → List Line
  | .fill c x y w h => [.op (ContentOp.render (.fill c x y w h))]
  | .path fl st segs => [.op (ContentOp.render (.path fl st segs))]
  | .text ops => .op "BT" :: (TextOp.linesList ops.toList ++ [.op "ET"])
  | .image x y w h res => [.op (ContentOp.render (.image x y w h res))]
  | .imageMissing x y w h => [.op (ContentOp.render (.imageMissing x y w h))]
  | .marked t body => .open t :: (ContentOp.linesList body.toList ++ [.emc])

def ContentOp.linesList : List ContentOp → List Line
  | [] => []
  | o :: rest =>
    let tail := ContentOp.linesList rest
    o.lines ++ tail

end

/-- The stream's lines, in order. -/
def lines (ops : Array ContentOp) : List Line := ContentOp.linesList ops.toList

/-- Lines joined by their separators: the stream `render` spells. A spec,
not the writer's path (`render` accumulates); the tails are bound so the
copy each prepend makes is visible where it stands. -/
def joinLines : List Line → String
  | [] => ""
  | l :: rest =>
    let tail := joinTail rest
    l.render ++ tail
where
  joinTail : List Line → String
    | [] => ""
    | l :: rest =>
      let tail := joinTail rest
      "\n" ++ l.render ++ tail

/-- Lines each closed by its line end: the body of a marked sequence, or
of the text object. -/
def termLines : List Line → String
  | [] => ""
  | l :: rest =>
    let tail := termLines rest
    l.render ++ "\n" ++ tail

mutual

/-- The ink under a text operator: a marked sequence flattened to its
body, in order; a leaf as it is. -/
def TextOp.ink : TextOp → List TextOp
  | .scale p => [.scale p]
  | .move x y => [.move x y]
  | .font res size => [.font res size]
  | .color c => [.color c]
  | .show items => [.show items]
  | .marked _ body => TextOp.inkList body.toList

def TextOp.inkList : List TextOp → List TextOp
  | [] => []
  | o :: rest =>
    let tail := TextOp.inkList rest
    o.ink ++ tail

end

def inkText (ops : Array TextOp) : Array TextOp := (TextOp.inkList ops.toList).toArray

mutual

/-- The ink under a page operation: wrappers dropped at every depth, the
text object's own wrappers included. -/
def ContentOp.ink : ContentOp → List ContentOp
  | .fill c x y w h => [.fill c x y w h]
  | .path fl st segs => [.path fl st segs]
  | .text ops => [.text (inkText ops)]
  | .image x y w h res => [.image x y w h res]
  | .imageMissing x y w h => [.imageMissing x y w h]
  | .marked _ body => ContentOp.inkList body.toList

def ContentOp.inkList : List ContentOp → List ContentOp
  | [] => []
  | o :: rest =>
    let tail := ContentOp.inkList rest
    o.ink ++ tail

end

/-- The stream with every marked-content wrapper removed, bodies kept in
order: the operators that paint. -/
def inkOps (ops : Array ContentOp) : Array ContentOp := (ContentOp.inkList ops.toList).toArray

/-- A decoration leaf: a fill or a placeholder box — the operations this
layer never leaves bare (`artifacts_covers`). -/
def ContentOp.decoration : ContentOp → Bool
  | .fill _ _ _ _ _ => true
  | .imageMissing _ _ _ _ => true
  | .path _ _ _ => false
  | .text _ => false
  | .image _ _ _ _ _ => false
  | .marked _ _ => false

/-- The glyph run a segment ships: a run's glyph ids when it has any (a
kern is a run with none, and paints nothing). -/
def segRuns : Seg → List (Array Nat)
  | .run _ _ _ _ glyphs _ _ _ _ => if glyphs.isEmpty then [] else [glyphs.map (·.1)]
  | .gap _ => []
  | .rule _ _ _ _ => []
  | .image _ _ _ => []

/-- The shipped glyph census of a page: every run's glyphs, line by line
in segment order — what `pdftotext` reads back, before spelling. -/
def pageRuns (page : PageOut) : List (Array Nat) :=
  page.lines.toList.flatMap fun l => l.segs.toList.flatMap segRuns

/-! ## The equational theory of `render`

Every renderer above is a left fold that appends; these are the list
equations it computes, so a fact about the bytes is a fact about the
typed array. -/

/-- The general fold-with-append law under an arbitrary accumulator. -/
theorem foldl_append_acc (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ l.foldl (fun s x => s ++ f x) "" := by
  induction l generalizing acc with
  | nil => simp [String.append_empty]
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ f x), ih ("" ++ f x), String.empty_append, String.append_assoc]

theorem foldl_append_eq (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ String.join (l.map f) := by
  show l.foldl (fun s x => s ++ f x) acc = acc ++ (l.map f).foldl (fun r s => r ++ s) ""
  rw [List.foldl_map, foldl_append_acc]

/-- The stream's shape as a list equation: operations joined by newlines.
The specification `render` is proved to compute (`content_render_exact`);
`render` itself accumulates. -/
def renderList : List ContentOp → String
  | [] => ""
  | [o] => o.render
  | o :: rest => o.render ++ ("\n" ++ renderList rest)

theorem renderList_go (l : List ContentOp) (acc : String) :
    l.foldl renderStep (some acc)
      = some (match l with | [] => acc | _ :: _ => acc ++ "\n" ++ renderList l) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons, renderStep, ih]
    cases rest with
    | nil => rfl
    | cons y rest' => simp only [renderList, String.append_assoc]

/-- **The renderer computes its list specification.** The accumulating
`render` and the structural `renderList` agree on every operator array —
the equation the old string builder had no way to state, and the one a
fact about the bytes (`mark_ink_exact`, once marked content lands) reduces
to a fact about the typed array through. -/
theorem content_render_exact (ops : Array ContentOp) :
    render ops = renderList ops.toList := by
  unfold render
  rw [← Array.foldl_toList]
  cases ops.toList with
  | nil => rfl
  | cons o rest =>
    simp only [List.foldl_cons]
    rw [show renderStep none o = some o.render from rfl, renderList_go]
    cases rest with
    | nil => rfl
    | cons y rest' => simp only [renderList, Option.getD_some, String.append_assoc]

theorem text_render_exact (ops : Array TextOp) :
    (ContentOp.text ops).render
      = "BT\n" ++ String.join (ops.toList.map fun o => o.render ++ "\n") ++ "ET" := by
  simp only [ContentOp.render, String.append_assoc]
  rw [← Array.foldl_toList, foldl_append_eq, String.append_assoc]

theorem show_render_exact (items : Array TextItem) :
    (TextOp.show items).render
      = "[" ++ String.join (items.toList.map TextItem.render) ++ "] TJ" := by
  simp only [TextOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]

/-- The glyph string: the ids' hex digits between the angle brackets that
delimit a PDF hexadecimal string (ISO 32000-2 §7.3.4.3). -/
theorem glyphs_render_exact (gids : Array Nat) :
    (TextItem.glyphs gids).render
      = String.singleton '<' ++ String.join (gids.toList.map gidHex) ++ String.singleton '>' := by
  simp only [TextItem.render]
  rw [show pushGid = fun acc g => acc ++ gidHex g from funext fun _ => funext fun _ => pushGid_eq ..,
    ← Array.foldl_toList, foldl_append_eq, String.push_eq_append]
  rfl

theorem path_render_exact (fl : Option Ir.Color) (st : Option Ir.Pic.Stroke) (segs : Array PathOp) :
    (ContentOp.path fl st segs).render
      = "q " ++ fillOp fl ++ strokeOp st ++ String.join (segs.toList.map PathOp.render)
        ++ paintOp st fl ++ " Q" := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]
/-- The runs a walk state holds: those already in ops, then the open array's. -/
def TextSt.runs (st : TextSt) : List (Array Nat) :=
  st.ops.toList.flatMap TextOp.runs ++ st.items.toList.flatMap TextItem.runs

theorem flatMap_nil_fun (l : List α) : l.flatMap (fun (_ : α) => ([] : List β)) = [] :=
  List.flatMap_eq_nil_iff.mpr fun _ _ => rfl

theorem op_runs (st : TextSt) (o : TextOp) (h : o.runs = []) : (st.op o).runs = st.runs := by
  simp [TextSt.op, TextSt.runs, h]

theorem closeTJ_runs (st : TextSt) : st.closeTJ.runs = st.runs := by
  unfold TextSt.closeTJ
  split
  · rfl
  · simp [TextSt.runs, TextOp.runs]

theorem closeTJ_items (st : TextSt) : st.closeTJ.items = #[] := by
  unfold TextSt.closeTJ
  split
  · rename_i h
    exact Array.isEmpty_iff.mp h
  · rfl

theorem toPen_runs (st : TextSt) (c : Bool) (y : Sp) : (st.toPen c y).runs = st.runs := by
  unfold TextSt.toPen
  split
  · split
    · simp only []
      split
      · simp [TextSt.runs, TextItem.runs]
      · rw [op_runs _ _ rfl, closeTJ_runs]
    · rfl
  · rw [op_runs _ _ rfl]

theorem setFont_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) :
    (st.setFont remap idx size).runs = st.runs := by
  unfold TextSt.setFont
  split
  · exact op_runs _ _ rfl
  · rfl

theorem setColor_runs (st : TextSt) (c : Ir.Color) : (st.setColor c).runs = st.runs := by
  unfold TextSt.setColor
  split
  · exact op_runs _ _ rfl
  · rfl

theorem setFace_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) (c : Ir.Color) :
    (st.setFace remap idx size c).runs = st.runs := by
  unfold TextSt.setFace
  rw [setColor_runs, setFont_runs, closeTJ_runs]

theorem stepRun_runs (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char)) (ss raise : Sp) :
    (stepRun remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  unfold stepRun
  split
  · simp [TextSt.runs]
  · simp only []
    generalize hc : (st.font != (idx : Int) || st.size != (if ss == 0 then ls else ss)
      || st.color != c) = changes
    have key : ∀ (s : TextSt) (i : TextItem) (x' : Sp) (p' : Option (Sp × Sp)),
        TextSt.runs { s with items := s.items.push i, x := x', pen := p' } = s.runs ++ i.runs := by
      intro s i x' p'
      simp [TextSt.runs]
    rw [key]
    simp only [TextItem.runs]
    split
    · rw [setFace_runs, toPen_runs]
    · rw [toPen_runs]

theorem stepSeg_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp) (st : TextSt)
    (seg : Seg) : (stepSeg remap imgMap ls y st seg).runs = st.runs ++ segRuns seg := by
  cases seg with
  | rule => simp [stepSeg, TextSt.runs, segRuns]
  | image => simp [stepSeg, TextSt.runs, segRuns]
  | gap => simp [stepSeg, TextSt.runs, segRuns]
  | run => exact stepRun_runs ..

theorem foldl_segs_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (segs : List Seg) (st : TextSt) :
    (segs.foldl (stepSeg remap imgMap ls y) st).runs = st.runs ++ segs.flatMap segRuns := by
  induction segs generalizing st with
  | nil => simp
  | cons s rest ih => simp [ih, stepSeg_runs, List.append_assoc]

theorem TextOp.runsList_eq (l : List TextOp) : TextOp.runsList l = l.flatMap TextOp.runs := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [TextOp.runsList, ih]

theorem ContentOp.runsList_eq (l : List ContentOp) :
    ContentOp.runsList l = l.flatMap ContentOp.runs := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.runsList, ih]

theorem lineSt_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    (lineSt geom remap imgMap st l).runs
      = st.items.toList.flatMap TextItem.runs ++ l.segs.toList.flatMap segRuns := by
  unfold lineSt
  simp only []
  rw [closeTJ_runs, ← Array.foldl_toList, foldl_segs_runs]
  congr 1
  split
  · simp [TextSt.runs, TextSt.op, TextOp.runs]
  · simp [TextSt.runs]

theorem lineSt_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) : (lineSt geom remap imgMap st l).items = #[] := by
  unfold lineSt
  exact closeTJ_items _

theorem stepLine_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap st l).runs = st.runs ++ l.segs.toList.flatMap segRuns := by
  unfold stepLine
  have hs := lineSt_runs geom remap imgMap st l
  have hi := lineSt_items geom remap imgMap st l
  simp only [TextSt.runs] at hs ⊢
  rw [hi] at hs ⊢
  simp only [List.flatMap_nil, List.append_nil] at hs ⊢
  split
  · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
      List.append_assoc]
  · simp [Array.toList_append, List.flatMap_append, hs, List.append_assoc]

theorem stepLine_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) : (stepLine geom remap imgMap st l).items = #[] := by
  unfold stepLine
  exact lineSt_items ..

theorem foldl_lines_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (lines : List LineOut) (st : TextSt) :
    (lines.foldl (stepLine geom remap imgMap) st).runs
      = st.runs ++ lines.flatMap (fun l => l.segs.toList.flatMap segRuns) := by
  induction lines generalizing st with
  | nil => simp
  | cons l rest ih => simp [ih, stepLine_runs, List.append_assoc]

theorem foldl_lines_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (lines : List LineOut) (st : TextSt) (h : st.items = #[]) :
    (lines.foldl (stepLine geom remap imgMap) st).items = #[] := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_items ..)

theorem imageOp_runs (x y w h : Sp) (r : Option Nat) : (imageOp x y w h r).runs = [] := by
  cases r <;> simp [imageOp, artifact, ContentOp.runs, ContentOp.runsList]

theorem artifact_runs (k : Option ArtifactKind) (o : ContentOp) :
    (artifact k o).runs = o.runs := by
  simp [artifact, ContentOp.runs, ContentOp.runsList]

theorem artifactBlock_runs (k : Option ArtifactKind) (ops : Array ContentOp) :
    (artifactBlock k ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h]
  · simp [ContentOp.runs, ContentOp.runsList_eq]

/-- **The PDF paints every glyph run the page shipped, in order.** The glyph
census of the typed content stream is the page's run census: no run
dropped, none invented, none reordered — the `_text` fact for the
PageOut → ContentOp projection (not a `Conserves` instance: the walk
changes type, as `structTree_text` does). -/
theorem contentOps_text (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : runsOf (contentOps geom remap imgMap page) = pageRuns page := by
  unfold runsOf contentOps pageRuns
  have himg : ∀ t : Sp × Sp × Sp × Sp × Option Nat,
      ContentOp.runs (imageOp t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) = [] :=
    fun t => imageOp_runs ..
  simp only [Array.toList_append, Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, artifactBlock_runs, Array.toList_map, List.flatMap_map, himg,
    flatMap_nil_fun]
  simp only [ContentOp.runs, flatMap_nil_fun, List.append_nil, List.nil_append]
  have hr := foldl_lines_runs geom remap imgMap page.lines.toList {}
  have hi := foldl_lines_items geom remap imgMap page.lines.toList {} rfl
  rw [Array.foldl_toList] at hr hi
  simp only [TextSt.runs, hi] at hr
  simpa using hr
theorem hexDigit_inj : ∀ a, a < 16 → ∀ b, b < 16 → hexDigit a = hexDigit b → a = b := by
  decide

theorem hexDigit_mod (a : Nat) : hexDigit a = hexDigit (a % 16) := by
  simp [hexDigit]

theorem hexDigit_eq_mod {a b : Nat} (h : hexDigit a = hexDigit b) : a % 16 = b % 16 := by
  rw [hexDigit_mod a, hexDigit_mod b] at h
  exact hexDigit_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

theorem gidHex_toList (g : Nat) :
    (gidHex g).toList
      = [hexDigit (g / 4096), hexDigit (g / 256), hexDigit (g / 16), hexDigit g] := by
  simp [gidHex, pushGid, String.toList_push]

/-- A glyph id in the Identity-H range is recoverable from its four hex
digits: the spelling is injective below 65536 (above it, the leading
digits wrap — the honest bound). -/
theorem gidHex_inj {g₁ g₂ : Nat} (h₁ : g₁ < 65536) (h₂ : g₂ < 65536)
    (h : gidHex g₁ = gidHex g₂) : g₁ = g₂ := by
  have hl := congrArg String.toList h
  rw [gidHex_toList, gidHex_toList] at hl
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨e1, e2, e3, e4⟩ := hl
  have := hexDigit_eq_mod e1
  have := hexDigit_eq_mod e2
  have := hexDigit_eq_mod e3
  have := hexDigit_eq_mod e4
  omega

theorem join_cons (a : String) (as : List String) :
    String.join (a :: as) = a ++ String.join as := by
  unfold String.join
  simp only [List.foldl_cons]
  have := foldl_append_acc (fun x : String => x) as ("" ++ a)
  simp only [String.empty_append] at this
  exact this

theorem join_gidHex_inj : ∀ (l₁ l₂ : List Nat), (∀ g ∈ l₁, g < 65536) → (∀ g ∈ l₂, g < 65536) →
    String.join (l₁.map gidHex) = String.join (l₂.map gidHex) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by
    have := congrArg String.toList h
    simp [String.toList_append, gidHex_toList] at this
  | x :: _, [], _, _, h => by
    have := congrArg String.toList h
    simp [String.toList_append, gidHex_toList] at this
  | x :: r₁, y :: r₂, h₁, h₂, h => by
    have hl := congrArg String.toList h
    simp only [List.map_cons, join_cons, String.toList_append] at hl
    have hlen : (gidHex x).toList.length = (gidHex y).toList.length := by
      simp [gidHex_toList]
    obtain ⟨hx, hr⟩ := List.append_inj hl hlen
    have hxy := gidHex_inj (h₁ x (by simp)) (h₂ y (by simp)) (String.ext hx)
    have hrest := join_gidHex_inj r₁ r₂ (fun g hg => h₁ g (by simp [hg]))
      (fun g hg => h₂ g (by simp [hg])) (String.ext hr)
    rw [hxy, hrest]

/-- **The glyph string is injective on Identity-H ids.** Two `TJ` glyph
items that spell the same carry the same ids, when every id is below
65536 — the strongest injectivity the stream honestly has: `render`
itself is not injective (`render_not_inj`). -/
theorem glyphs_inj {a b : Array Nat} (ha : ∀ g ∈ a, g < 65536) (hb : ∀ g ∈ b, g < 65536)
    (h : (TextItem.glyphs a).render = (TextItem.glyphs b).render) : a = b := by
  rw [glyphs_render_exact, glyphs_render_exact] at h
  have h := (String.append_left_inj _).mp h
  have h := (String.append_right_inj _).mp h
  exact Array.toList_inj.mp (join_gidHex_inj _ _ (fun g hg => ha g (Array.mem_toList_iff.mp hg))
    (fun g hg => hb g (Array.mem_toList_iff.mp hg)) h)

/-- `render` is not injective: a page fill and a fill-only rectangle path
spell the same operators (as they must — one `re f` is one `re f`), so no
theorem may read an operator array back from its bytes. Every fact about
what the stream carries is stated over the typed array. -/
theorem render_not_inj : ∃ a b : Array ContentOp, a ≠ b ∧ render a = render b :=
  ⟨#[.fill Ir.Color.black 0 0 1 1], #[.path (some Ir.Color.black) none #[.rect 0 0 1 1]],
    fun h => by have := congrArg (·[0]?) h; simp at this, rfl⟩

/-! ## Marked content: the line spec, balance, and the ink underneath -/

theorem joinTail_append_singleton (a : List Line) (x : Line) :
    joinLines.joinTail (a ++ [x]) = joinLines.joinTail a ++ ("\n" ++ x.render) := by
  induction a with
  | nil => simp [joinLines.joinTail]
  | cons l rest ih => simp [joinLines.joinTail, ih, String.append_assoc]

theorem termLines_append (a b : List Line) : termLines (a ++ b) = termLines a ++ termLines b := by
  induction a with
  | nil => simp [termLines]
  | cons l rest ih => simp [termLines, ih, String.append_assoc]

theorem termLines_eq_joinTail (l : List Line) :
    "\n" ++ termLines l = joinLines.joinTail l ++ "\n" := by
  induction l with
  | nil => simp [termLines, joinLines.joinTail]
  | cons x rest ih =>
    simp only [termLines, joinLines.joinTail, String.append_assoc]
    rw [ih]

/-- The shape of a marked sequence and of the text object: an opening
line, a terminated body, a closing line — as joined lines. -/
theorem open_body_close_eq (a : String) (l : List Line) (z : String) :
    a ++ "\n" ++ termLines l ++ z = a ++ (joinLines.joinTail l ++ ("\n" ++ z)) := by
  induction l generalizing a with
  | nil => simp [termLines, joinLines.joinTail, String.append_assoc]
  | cons x rest ih =>
    simp only [termLines, joinLines.joinTail]
    have := ih (a ++ "\n" ++ x.render)
    simp only [String.append_assoc] at this ⊢
    exact this

theorem joinTail_append (a b : List Line) (hb : b ≠ []) :
    joinLines.joinTail (a ++ b) = joinLines.joinTail a ++ ("\n" ++ joinLines b) := by
  induction a with
  | nil =>
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hb
    simp [joinLines.joinTail, joinLines, String.append_assoc]
  | cons x rest ih => simp [joinLines.joinTail, ih, String.append_assoc]

theorem joinLines_append (a b : List Line) (ha : a ≠ []) (hb : b ≠ []) :
    joinLines (a ++ b) = joinLines a ++ ("\n" ++ joinLines b) := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil ha
  simp [joinLines, joinTail_append _ _ hb, String.append_assoc]

/-- A non-empty line list closed by its line end is the joined lines
followed by one. -/
theorem termLines_cons (l : Line) (rest : List Line) :
    termLines (l :: rest) = joinLines (l :: rest) ++ "\n" := by
  simp only [termLines, joinLines, String.append_assoc]
  rw [termLines_eq_joinTail]

theorem TextOp.lines_ne_nil (o : TextOp) : o.lines ≠ [] := by
  cases o <;> simp [TextOp.lines]

theorem ContentOp.lines_ne_nil (o : ContentOp) : o.lines ≠ [] := by
  cases o <;> simp [ContentOp.lines]

theorem TextOp.linesList_append (a b : List TextOp) :
    TextOp.linesList (a ++ b) = TextOp.linesList a ++ TextOp.linesList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [TextOp.linesList, ih]

theorem ContentOp.linesList_append (a b : List ContentOp) :
    ContentOp.linesList (a ++ b) = ContentOp.linesList a ++ ContentOp.linesList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.linesList, ih]

mutual

/-- **Every text operator renders as its lines joined**, a marked
sequence as its opening line, its body's lines, and its `EMC` line. -/
theorem TextOp.render_lines_exact : ∀ o : TextOp, o.render = joinLines o.lines
  | .scale p => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .move x y => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .font res size => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .color c => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .show items => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .marked t body => by
    rw [TextOp.render, TextOp.lines, TextOp.renderLines_exact body.toList, joinLines,
      joinTail_append_singleton]
    simp only [Line.render]
    exact open_body_close_eq ..

theorem TextOp.renderLines_exact : ∀ (l : List TextOp) (acc : String),
    TextOp.renderLines acc l = acc ++ termLines (TextOp.linesList l)
  | [], acc => by simp [TextOp.renderLines, TextOp.linesList, termLines]
  | o :: rest, acc => by
    have hl : termLines o.lines = o.render ++ "\n" := by
      obtain ⟨l, rest', h⟩ := List.exists_cons_of_ne_nil (TextOp.lines_ne_nil o)
      rw [h, termLines_cons, ← h, ← TextOp.render_lines_exact o]
    rw [TextOp.renderLines, TextOp.renderLines_exact rest, TextOp.linesList]
    simp only [termLines_append, hl, String.append_assoc]

end

mutual

/-- **Every page operation renders as its lines joined**: the text object
as `BT`, its operators' lines, `ET`; a marked sequence as its opening
line, its body's lines, and its `EMC` line. -/
theorem ContentOp.render_lines_exact : ∀ o : ContentOp, o.render = joinLines o.lines
  | .fill c x y w h => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .path fl st segs => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .image x y w h res => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .imageMissing x y w h => by
    simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .text ops => by
    rw [ContentOp.render, ContentOp.lines, ← Array.foldl_toList,
      show ops.toList.foldl (fun acc op => acc ++ op.render ++ "\n") "BT\n"
        = TextOp.renderLines "BT\n" ops.toList from ?_,
      TextOp.renderLines_exact, joinLines, joinTail_append_singleton]
    · simp only [Line.render]
      rw [show ("BT\n" : String) = "BT" ++ "\n" from rfl]
      exact open_body_close_eq ..
    · generalize "BT\n" = acc
      induction ops.toList generalizing acc with
      | nil => rfl
      | cons o rest ih => simp only [List.foldl_cons, TextOp.renderLines, ih]
  | .marked t body => by
    rw [ContentOp.render, ContentOp.lines, ContentOp.renderLines_exact body.toList, joinLines,
      joinTail_append_singleton]
    simp only [Line.render]
    exact open_body_close_eq ..

theorem ContentOp.renderLines_exact : ∀ (l : List ContentOp) (acc : String),
    ContentOp.renderLines acc l = acc ++ termLines (ContentOp.linesList l)
  | [], acc => by simp [ContentOp.renderLines, ContentOp.linesList, termLines]
  | o :: rest, acc => by
    have hl : termLines o.lines = o.render ++ "\n" := by
      obtain ⟨l, rest', h⟩ := List.exists_cons_of_ne_nil (ContentOp.lines_ne_nil o)
      rw [h, termLines_cons, ← h, ← ContentOp.render_lines_exact o]
    rw [ContentOp.renderLines, ContentOp.renderLines_exact rest, ContentOp.linesList]
    simp only [termLines_append, hl, String.append_assoc]

end

theorem ContentOp.linesList_ne_nil (o : ContentOp) (rest : List ContentOp) :
    ContentOp.linesList (o :: rest) ≠ [] := by
  simp [ContentOp.linesList, ContentOp.lines_ne_nil]

theorem renderList_eq_joinLines (l : List ContentOp) :
    renderList l = joinLines (ContentOp.linesList l) := by
  induction l with
  | nil => rfl
  | cons o rest ih =>
    cases rest with
    | nil =>
      simp only [renderList, ContentOp.linesList, List.append_nil]
      exact ContentOp.render_lines_exact o
    | cons p rest' =>
      have hl : ContentOp.linesList (o :: p :: rest') = o.lines ++ ContentOp.linesList (p :: rest') :=
        ContentOp.linesList.eq_2 ..
      rw [renderList, ih, ContentOp.render_lines_exact o, hl,
        joinLines_append _ _ (ContentOp.lines_ne_nil o) (ContentOp.linesList_ne_nil p rest')]
      simp

/-- **The stream is its lines joined.** `render`'s bytes are `lines`'
spelling: what opens and closes a marked-content sequence on the page is
decided on the typed line list, and this equation carries it to the
bytes. -/
theorem render_lines_exact (ops : Array ContentOp) : render ops = joinLines (lines ops) := by
  rw [content_render_exact, lines, renderList_eq_joinLines]

mutual

theorem TextOp.lines_balanced :
    ∀ o : TextOp, o.lines.countP Line.isOpen = o.lines.countP Line.isEmc
  | .scale _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .move _ _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .font _ _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .color _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .show _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .marked t body => by
    have := TextOp.linesList_balanced body.toList
    simp [TextOp.lines, Line.isOpen, Line.isEmc, List.countP_append, List.countP_cons, this]

theorem TextOp.linesList_balanced : ∀ l : List TextOp,
    (TextOp.linesList l).countP Line.isOpen = (TextOp.linesList l).countP Line.isEmc
  | [] => rfl
  | o :: rest => by
    have h₁ := TextOp.lines_balanced o
    have h₂ := TextOp.linesList_balanced rest
    simp [TextOp.linesList, List.countP_append, h₁, h₂]

end

mutual

theorem ContentOp.lines_balanced :
    ∀ o : ContentOp, o.lines.countP Line.isOpen = o.lines.countP Line.isEmc
  | .fill _ _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .path _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .image _ _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .imageMissing _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .text ops => by
    have := TextOp.linesList_balanced ops.toList
    simp [ContentOp.lines, Line.isOpen, Line.isEmc, List.countP_append, this]
  | .marked t body => by
    have := ContentOp.linesList_balanced body.toList
    simp [ContentOp.lines, Line.isOpen, Line.isEmc, List.countP_append, List.countP_cons, this]

theorem ContentOp.linesList_balanced : ∀ l : List ContentOp,
    (ContentOp.linesList l).countP Line.isOpen = (ContentOp.linesList l).countP Line.isEmc
  | [] => rfl
  | o :: rest => by
    have h₁ := ContentOp.lines_balanced o
    have h₂ := ContentOp.linesList_balanced rest
    simp [ContentOp.linesList, List.countP_append, h₁, h₂]

end

/-- **Every stream opens as many marked-content sequences as it closes**:
opening (`BDC`/`BMC`) and `EMC` lines pair off, whatever the operator array — the
executable form of "ill-nesting is unrepresentable", since `marked` is
the only constructor that spells either. Reaches the bytes through
`render_lines_exact`. -/
theorem lines_marked_balanced (ops : Array ContentOp) :
    (lines ops).countP Line.isOpen = (lines ops).countP Line.isEmc :=
  ContentOp.linesList_balanced _

theorem stripMarks_cons_open (t : MarkTag) (ls : List Line) :
    stripMarks (.open t :: ls) = stripMarks ls := by
  simp [stripMarks, Line.isOpen]

theorem stripMarks_cons_op (s : String) (ls : List Line) :
    stripMarks (.op s :: ls) = .op s :: stripMarks ls := by
  simp [stripMarks, Line.isOpen, Line.isEmc]

theorem stripMarks_append (a b : List Line) : stripMarks (a ++ b) = stripMarks a ++ stripMarks b :=
  List.filter_append ..

theorem stripMarks_emc : stripMarks [.emc] = [] := by simp [stripMarks, Line.isEmc]

theorem stripMarks_nil : stripMarks [] = [] := rfl

theorem stripMarks_countP_open (ls : List Line) : (stripMarks ls).countP Line.isOpen = 0 := by
  rw [List.countP_eq_zero]
  intro l hl
  simp only [stripMarks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hl
  simp [hl.2.1]

theorem TextOp.inkList_append (a b : List TextOp) :
    TextOp.inkList (a ++ b) = TextOp.inkList a ++ TextOp.inkList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [TextOp.inkList, ih]

theorem ContentOp.inkList_append (a b : List ContentOp) :
    ContentOp.inkList (a ++ b) = ContentOp.inkList a ++ ContentOp.inkList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.inkList, ih]

mutual

/-- The lines of an operator's ink are its lines with the marked-content
lines stripped. -/
theorem TextOp.lines_ink : ∀ o : TextOp, TextOp.linesList o.ink = stripMarks o.lines
  | .scale p => by simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .move x y => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .font res size => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .color c => by simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .show items => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .marked t body => by
    rw [TextOp.ink, TextOp.lines, TextOp.linesList_ink body.toList, stripMarks_cons_open,
      stripMarks_append, stripMarks_emc, List.append_nil]

theorem TextOp.linesList_ink : ∀ l : List TextOp,
    TextOp.linesList (TextOp.inkList l) = stripMarks (TextOp.linesList l)
  | [] => rfl
  | o :: rest => by
    rw [TextOp.inkList, TextOp.linesList, TextOp.linesList_append, TextOp.lines_ink o,
      TextOp.linesList_ink rest, stripMarks_append]

end

mutual

theorem ContentOp.lines_ink : ∀ o : ContentOp, ContentOp.linesList o.ink = stripMarks o.lines
  | .fill c x y w h => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .path fl st segs => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .image x y w h res => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .imageMissing x y w h => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .text ops => by
    rw [ContentOp.ink, ContentOp.linesList, ContentOp.linesList, List.append_nil, ContentOp.lines,
      ContentOp.lines, inkText, List.toList_toArray, TextOp.linesList_ink, stripMarks_cons_op,
      stripMarks_append, stripMarks_cons_op, stripMarks_nil]
  | .marked t body => by
    rw [ContentOp.ink, ContentOp.lines, ContentOp.linesList_ink body.toList, stripMarks_cons_open,
      stripMarks_append, stripMarks_emc, List.append_nil]

theorem ContentOp.linesList_ink : ∀ l : List ContentOp,
    ContentOp.linesList (ContentOp.inkList l) = stripMarks (ContentOp.linesList l)
  | [] => rfl
  | o :: rest => by
    rw [ContentOp.inkList, ContentOp.linesList, ContentOp.linesList_append, ContentOp.lines_ink o,
      ContentOp.linesList_ink rest, stripMarks_append]

end

/-- **The ink's stream is the stream with its marked-content lines
removed.** `inkOps` drops every wrapper; on the bytes that is exactly a
strip of the opening and `EMC` lines (`render_lines_exact`) — the equation
the artifact acceptance's stripped-stream comparison executes. -/
theorem inkOps_lines_exact (ops : Array ContentOp) : lines (inkOps ops) = stripMarks (lines ops) := by
  simp only [lines, inkOps, List.toList_toArray]
  exact ContentOp.linesList_ink _

theorem render_inkOps_exact (ops : Array ContentOp) :
    render (inkOps ops) = joinLines (stripMarks (lines ops)) := by
  rw [render_lines_exact, inkOps_lines_exact]

/-! ### The text walk under `inkText` -/

theorem inkText_append (a b : Array TextOp) : inkText (a ++ b) = inkText a ++ inkText b := by
  simp [inkText, TextOp.inkList_append]

theorem inkText_push (ops : Array TextOp) (o : TextOp) :
    inkText (ops.push o) = inkText ops ++ o.ink.toArray := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList]

theorem inkText_push_marked (ops : Array TextOp) (t : MarkTag) (body : Array TextOp) :
    inkText (ops.push (.marked t body)) = inkText ops ++ inkText body := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList, TextOp.ink]

/-- A state's ops seen through `inkText`: what the text walk decides that
the marking cannot change. -/
def TextSt.plain (st : TextSt) : TextSt := { st with ops := inkText st.ops }

theorem lineSt_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) : lineSt geom remap imgMap st.plain l = lineSt geom remap imgMap st l := by
  simp [lineSt, TextSt.plain]

/-- **Marking a line moves no ink**: the wrapped line and the plain line
agree on everything but the wrapper. -/
theorem stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap st l).plain = (stepLinePlain geom remap imgMap st l).plain := by
  simp only [stepLine, stepLinePlain, TextSt.plain]
  split
  · simp [inkText_push_marked, inkText_append]
  · rfl

theorem stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    {st st' : TextSt} (h : st.plain = st'.plain) (l : LineOut) :
    (stepLinePlain geom remap imgMap st l).plain = (stepLinePlain geom remap imgMap st' l).plain := by
  have hl : lineSt geom remap imgMap st l = lineSt geom remap imgMap st' l := by
    rw [← lineSt_plain geom remap imgMap st, h, lineSt_plain]
  have ho : inkText st.ops = inkText st'.ops := congrArg TextSt.ops h
  simp only [stepLinePlain, TextSt.plain, hl, inkText_append, ho]

theorem foldl_stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (ls : List LineOut) {st st' : TextSt} (h : st.plain = st'.plain) :
    (ls.foldl (stepLinePlain geom remap imgMap) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap) st').plain := by
  induction ls generalizing st st' with
  | nil => exact h
  | cons l rest ih => exact ih (stepLinePlain_resp geom remap imgMap h l)

/-- The marked walk and the plain walk agree under `inkText`, line by line. -/
theorem foldl_stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (ls : List LineOut) (st : TextSt) :
    (ls.foldl (stepLine geom remap imgMap) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap) st).plain := by
  induction ls generalizing st with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl_cons]
    rw [ih, foldl_stepLinePlain_resp geom remap imgMap rest (stepLine_plain geom remap imgMap st l)]

/-! ### The plain walk pushes only leaves -/

theorem op_plainOps (st : TextSt) (o : TextOp) (h : inkText st.ops = st.ops) (hl : o.ink = [o]) :
    inkText (st.op o).ops = (st.op o).ops := by
  simp [TextSt.op, inkText_push, h, hl]

theorem closeTJ_plainOps (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText st.closeTJ.ops = st.closeTJ.ops := by
  unfold TextSt.closeTJ
  split
  · exact h
  · exact op_plainOps st _ h (by simp [TextOp.ink])

theorem toPen_plainOps (st : TextSt) (c : Bool) (y : Sp) (h : inkText st.ops = st.ops) :
    inkText (st.toPen c y).ops = (st.toPen c y).ops := by
  unfold TextSt.toPen
  split
  · split
    · simp only []
      split
      · exact h
      · exact op_plainOps _ _ (closeTJ_plainOps st h) (by simp [TextOp.ink])
    · exact h
  · exact op_plainOps _ _ h (by simp [TextOp.ink])

theorem setFont_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp)
    (h : inkText st.ops = st.ops) :
    inkText (st.setFont remap idx size).ops = (st.setFont remap idx size).ops := by
  unfold TextSt.setFont
  split
  · exact op_plainOps _ _ h (by simp [TextOp.ink])
  · exact h

theorem setColor_plainOps (st : TextSt) (c : Ir.Color) (h : inkText st.ops = st.ops) :
    inkText (st.setColor c).ops = (st.setColor c).ops := by
  unfold TextSt.setColor
  split
  · exact op_plainOps _ _ h (by simp [TextOp.ink])
  · exact h

theorem setFace_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) (c : Ir.Color)
    (h : inkText st.ops = st.ops) :
    inkText (st.setFace remap idx size c).ops = (st.setFace remap idx size c).ops :=
  setColor_plainOps _ _ (setFont_plainOps _ _ _ _ (closeTJ_plainOps _ h))

theorem stepRun_plainOps (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char)) (ss raise : Sp) (h : inkText st.ops = st.ops) :
    inkText (stepRun remap ls y st idx c w glyphs ss raise).ops
      = (stepRun remap ls y st idx c w glyphs ss raise).ops := by
  unfold stepRun
  split
  · exact h
  · simp only []
    generalize (st.font != (idx : Int) || st.size != (if ss == 0 then ls else ss)
      || st.color != c) = changes
    split
    · exact setFace_plainOps _ _ _ _ _ (toPen_plainOps _ _ _ h)
    · exact toPen_plainOps _ _ _ h

theorem stepSeg_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (st : TextSt) (seg : Seg) (h : inkText st.ops = st.ops) :
    inkText (stepSeg remap imgMap ls y st seg).ops = (stepSeg remap imgMap ls y st seg).ops := by
  cases seg with
  | rule => exact h
  | image => exact h
  | gap => exact h
  | run => exact stepRun_plainOps _ _ _ _ _ _ _ _ _ _ h

theorem foldl_segs_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (segs : List Seg) (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText (segs.foldl (stepSeg remap imgMap ls y) st).ops
      = (segs.foldl (stepSeg remap imgMap ls y) st).ops := by
  induction segs generalizing st with
  | nil => exact h
  | cons s rest ih => exact ih _ (stepSeg_plainOps _ _ _ _ _ _ h)

theorem lineSt_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    inkText (lineSt geom remap imgMap st l).ops = (lineSt geom remap imgMap st l).ops := by
  unfold lineSt
  simp only []
  apply closeTJ_plainOps
  rw [← Array.foldl_toList]
  apply foldl_segs_plainOps
  split
  · exact op_plainOps _ _ rfl (by simp [TextOp.ink])
  · rfl

theorem stepLinePlain_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) (h : inkText st.ops = st.ops) :
    inkText (stepLinePlain geom remap imgMap st l).ops = (stepLinePlain geom remap imgMap st l).ops := by
  simp only [stepLinePlain, inkText_append, h, lineSt_plainOps]

theorem foldl_stepLinePlain_plainOps (geom : Geom) (remap : Array Nat)
    (imgMap : Array (Option Nat)) (ls : List LineOut) (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText (ls.foldl (stepLinePlain geom remap imgMap) st).ops
      = (ls.foldl (stepLinePlain geom remap imgMap) st).ops := by
  induction ls generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLinePlain_plainOps _ _ _ _ _ h)

/-! ### The theorems this layer owes -/

theorem artifact_ink (k : Option ArtifactKind) (o : ContentOp) : (artifact k o).ink = o.ink := by
  simp [artifact, ContentOp.ink, ContentOp.inkList]

theorem artifactBlock_ink (k : Option ArtifactKind) (ops : Array ContentOp) :
    ContentOp.inkList (artifactBlock k ops).toList = ContentOp.inkList ops.toList := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h, ContentOp.inkList]
  · simp [ContentOp.inkList, ContentOp.ink]

theorem mem_artifactBlock {k : Option ArtifactKind} {ops : Array ContentOp} {o : ContentOp}
    (h : o ∈ artifactBlock k ops) : o = .marked (.artifact k) ops := by
  unfold artifactBlock at h
  split at h
  · simp at h
  · simpa using h

theorem inkList_map {α : Type} (f g : α → ContentOp) (l : List α) (h : ∀ a, (f a).ink = [g a]) :
    ContentOp.inkList (l.map f) = l.map g := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ContentOp.inkList, h, ih]

theorem imageOp_ink (x y w h : Sp) (r : Option Nat) :
    (imageOp x y w h r).ink = [imageOpPlain x y w h r] := by
  cases r <;> simp [imageOp, imageOpPlain, artifact_ink, ContentOp.ink]

theorem imageOpPlain_ink (x y w h : Sp) (r : Option Nat) :
    (imageOpPlain x y w h r).ink = [imageOpPlain x y w h r] := by
  cases r <;> simp [imageOpPlain, ContentOp.ink]

/-- **Marking moves no ink.** The stream this layer builds, with every
marked-content wrapper removed, is the stream the writer built before the
layer existed (`contentOpsPlain`, the specification twin): same
operators, same order, same operands — so the same bytes
(`render_inkOps_exact`), and the strip of marked-content lines the
acceptance runs is this equation on the file. A fact of the content
stream, not a projection of an IR statement: the IR never sees marked
content. -/
theorem mark_ink_exact (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) :
    inkOps (contentOps geom remap imgMap page) = contentOpsPlain geom remap imgMap page := by
  unfold contentOps contentOpsPlain
  have hp := foldl_stepLine_plain geom remap imgMap page.lines.toList {}
  rw [Array.foldl_toList, Array.foldl_toList] at hp
  have hpo := foldl_stepLinePlain_plainOps geom remap imgMap page.lines.toList {} rfl
  rw [Array.foldl_toList] at hpo
  have hops : inkText (page.lines.foldl (stepLine geom remap imgMap) {}).ops
      = (page.lines.foldl (stepLinePlain geom remap imgMap) {}).ops := by
    rw [← hpo]; exact congrArg TextSt.ops hp
  have himg := congrArg TextSt.images hp
  have hrul := congrArg TextSt.rules hp
  simp only [TextSt.plain] at himg hrul
  simp only [inkOps, Array.toList_append, Array.toList_push, ContentOp.inkList_append,
    artifactBlock_ink, Array.toList_map, ContentOp.inkList, ContentOp.ink, hops, himg, hrul,
    List.append_nil]
  rw [inkList_map _ (fun f => ContentOp.fill f.color (geom.bleed + f.x)
      (geom.bleed + geom.pageH - f.y - f.h) f.w f.h) _ (fun f => by simp [ContentOp.ink]),
    inkList_map _ (fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)) _
      (fun p => by simp [ContentOp.ink]),
    inkList_map _ (fun (t : Sp × Sp × Sp × Sp × Option Nat) =>
      imageOpPlain t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => imageOp_ink ..),
    inkList_map _ (fun (t : Ir.Color × Sp × Sp × Sp × Sp) =>
      ContentOp.fill t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => by simp [ContentOp.ink])]
  apply Array.toList_inj.mp
  simp [Array.toList_append, Array.toList_push, Array.toList_map]

/-- **No decoration is left bare.** Every fill and every placeholder box
`contentOps` ships sits under a marked wrapper; the operations at the top
of the stream are wrappers, picture paths, loaded images, and the text
object. -/
theorem artifacts_covers (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : ∀ o ∈ contentOps geom remap imgMap page, o.decoration = false := by
  intro o ho
  simp only [contentOps, Array.mem_append, Array.mem_push, Array.mem_map] at ho
  rcases ho with (((hf | ⟨p, _, rfl⟩) | rfl) | ⟨t, _, rfl⟩) | hr
  · rw [mem_artifactBlock hf]; rfl
  · rfl
  · rfl
  · cases t.2.2.2.2 <;> rfl
  · rw [mem_artifactBlock hr]; rfl

/-- The pagination artifacts at the top of a text object. -/
def textArtifacts (ops : Array TextOp) : Nat := (TextOp.linesList ops.toList).countP Line.isOpen

theorem lineSt_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) : textArtifacts (lineSt geom remap imgMap st l).ops = 0 := by
  have h := lineSt_plainOps geom remap imgMap st l
  unfold textArtifacts
  rw [← h, inkText, List.toList_toArray, TextOp.linesList_ink, stripMarks_countP_open]

theorem stepLine_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    textArtifacts (stepLine geom remap imgMap st l).ops
      = textArtifacts st.ops + (if l.furniture then 1 else 0) := by
  have h0 := lineSt_textArtifacts geom remap imgMap st l
  unfold textArtifacts at h0 ⊢
  simp only [stepLine]
  split
  · simp [Array.toList_push, TextOp.linesList_append, TextOp.linesList, TextOp.lines,
      List.countP_append, List.countP_cons, Line.isOpen, h0]
  · simp [Array.toList_append, TextOp.linesList_append, List.countP_append, h0]

/-- **Every furniture line is one pagination artifact, and no flow line
is any.** The text object `contentOps` ships carries exactly one wrapper
per line the furniture pass laid — the count is the census the artifact
acceptance reads. -/
theorem furniture_covers (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (lines : Array LineOut) :
    textArtifacts (lines.foldl (stepLine geom remap imgMap) {}).ops
      = (lines.filter (·.furniture)).size := by
  have h : ∀ (ls : List LineOut) (st : TextSt),
      textArtifacts (ls.foldl (stepLine geom remap imgMap) st).ops
        = textArtifacts st.ops + (ls.filter (·.furniture)).length := by
    intro ls
    induction ls with
    | nil => intro st; simp
    | cons l rest ih =>
      intro st
      simp only [List.foldl_cons, ih, stepLine_textArtifacts, List.filter_cons]
      split <;> simp <;> omega
  rw [← Array.foldl_toList, h, ← Array.length_toList, Array.toList_filter]
  simp [textArtifacts, TextOp.linesList]

end LeanTex.Core.Pdf
