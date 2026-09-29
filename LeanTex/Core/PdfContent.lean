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
adjustment in thousandths of the text space unit. `kerned` is a glyph
string whose glyphs each carry the number set before them — `nums`
beside `gids`, 0 for none — one run's string with its pair kerns, spelled
`<…>n<…>` as lualatex spells it, and one run for the glyph census all the
same. -/
inductive TextItem where
  | glyphs (gids : Array Nat)
  | kerned (gids : Array Nat) (nums : Array Int)
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
array and the writer will not guess between `/Layout` and `/Page`. Real
content carries the structure type of the element that lists it, its
marked-content identifier on the page (§14.7.5.1: unique per page), and
the structure leaf it paints — the last is data for the structure walk,
never spelled. -/
inductive MarkTag where
  | artifact (kind : Option ArtifactKind)
  | content (s : String) (mcid : Nat) (leaf : Nat)
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
  | .content s mcid _ => s!"/{s} << /MCID {mcid} >> BDC"

/-- What a line's ink stands for, read off the layout: running furniture;
a structure leaf, under the structure type the structure walk gave the
element holding that leaf; or ink no leaf owns (a rules-only line, the
generated heading of an abstract), which is an artifact of no stated
type. Decided once per line and once per image — the origin is known at
the line and lost after. -/
inductive Origin where
  | furniture
  | unattributed
  | leaf (k : Nat) (tag : String)
  deriving Repr, BEq, Inhabited

/-- A line's origin: `tags` is the structure walk's answer per leaf id
(`PdfStruct.leafTags`), `none` for a leaf no element holds. -/
def Origin.of (tags : Array (Option String)) (l : LineOut) : Origin :=
  if l.furniture then .furniture else
  match l.leaf with
  | some k =>
    match (tags[k]?).join with
    | some s => .leaf k s
    | none => .unattributed
  | none => .unattributed

/-- The tag an origin's operators sit under. The marked-content identifier
is a placeholder here: `numberMarks` assigns them in stream order once the
page's operators are all built. -/
def Origin.mark : Origin → MarkTag
  | .furniture => .artifact (some .pagination)
  | .unattributed => .artifact none
  | .leaf k tag => .content tag 0 k

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
  | .kerned gids nums => Id.run do
    let mut s := "<"
    for h : i in [0:gids.size] do
      let n := nums.getD i 0
      if n != 0 then s := ((s.push '>') ++ toString n).push '<'
      s := pushGid s gids[i]
    return s.push '>'
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

/-- An image the text walk gathered for painting after `ET`: its box, its
XObject resource when it loaded, and the origin of the line it stood in
— a loaded image is real content under its line's leaf, a furniture
line's image (a logo) a pagination artifact. -/
structure ImgOut where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  res : Option Nat
  origin : Origin
  deriving Repr, BEq, Inhabited

/-- A glyph's advance as the file states it: its `hmtx` width in
millionths of the em, rounded to the nearest — what the `/W` array spells,
to three decimals of a thousandth, and so the width a viewer's pen
advances by (`TextSt.widths`). Exact in thousandths for a face on a
1000-unit em; to 5·10⁻⁷ em otherwise, where whole thousandths would drift
the pen up to one per glyph. -/
def widthμOf (upem units : Nat) : Int := ((units * 1000000 + upem / 2) / upem : Nat)

def pdfWidthμ (font : Font.Font) (g : Nat) : Int :=
  widthμOf font.unitsPerEm (font.widths[g]?.getD 0)

/-- The embedded faces' `pdfWidthμ` widths, by layout face index (`keep`,
the faces the file embeds; any other face ships no glyph): the writer's
pen reads one width per glyph shipped, so they are tabled once per
document — by the same `widthμOf` — and read by index with a `0` past a
face's last glyph, as `pdfWidthμ` answers there. -/
def widthTable (fonts : Array Font.Font) (keep : Array Nat) : Array (Array Int) :=
  fonts.mapIdx fun k f => if keep.contains k then f.widths.map (widthμOf f.unitsPerEm) else #[]


/-- The viewer's pen inside the open `TJ` array, as the writer computes it
from what it wrote (§9.4.4): `xm` the x the array's `Tm` spells, in
thousandths of a point (`Sp.toPtMilli`, the value a reader parses back),
`y` the baseline it spells, and `adv` the advance since then in millionths
of the text size — each glyph adds its `/W` width in that unit, each `TJ`
number `n` subtracts `1000 n`. The horizontal scale multiplies both terms
alike, so it enters only where a layout length is converted
(`penTarget`). -/
structure Pen where
  xm : Int
  y : Sp
  adv : Int
  deriving Repr, BEq, Inhabited

/-- The text object's walk state. `items` is the open `TJ` array — empty
exactly when no array is open. `font` is the layout face index in force
(`-1` before the first `Tf`), `size` and `color` likewise; `tz` the live
expansion in per-mille delta from 100 %; `x` the layout position; `pen`
where the viewer's pen is (`Pen`), once a `Tm` has set it; `widths` each
face's `/W` widths in millionths of the em, by layout face index and glyph
id (`widthTable`) — what the file tells the viewer, and so what the pen
advances by. Rules and
images gather here and paint after `ET`: path and `Do` operators may not
appear inside a text object. -/
structure TextSt where
  ops : Array TextOp := #[]
  items : Array TextItem := #[]
  font : Int := -1
  size : Sp := -1
  color : Ir.Color := Ir.Color.black
  tz : Int := 0
  x : Sp := 0
  pen : Option Pen := none
  widths : Array (Array Int) := #[]
  rules : Array (Ir.Color × Sp × Sp × Sp × Sp) := #[]
  images : Array ImgOut := #[]

def TextSt.op (st : TextSt) (o : TextOp) : TextSt := { st with ops := st.ops.push o }

def TextSt.closeTJ (st : TextSt) : TextSt :=
  if st.items.isEmpty then st else { st with ops := st.ops.push (.show st.items), items := #[] }

/-- `num / den` rounded to the nearest integer, half away from zero, the
numerator given as a sign and a magnitude: every product the pen's
conversions round is formed in `Nat`, where a value below 2⁶³ is a machine
word — an `Int` past 2³¹ is a heap number, and these run once per glyph. -/
@[inline] def roundDiv (neg : Bool) (num den : Nat) : Int :=
  if den == 0 then 0 else
    let q : Nat := (2 * num + den) / (2 * den)
    if neg then -(q : Int) else q

/-- A layout x as the pen advance that reaches it, in the pen's unit:
`(x − Tm) / (size · scale)` in millionths, with the `Tm` x and the size as
the file spells them (`xm`, `sm`: thousandths of a point) and the scale
`1000 + tz` per mille, rounded to the nearest millionth — that is,
`(1000·x − 65536·xm) · 1953125 / (128 · sm · (1000 + tz))`, since
10⁹ / 65536 = 1953125 / 128; the difference is split into its positive and
negative parts so it is formed as a magnitude (`roundDiv`). -/
def penTarget (sm tz xm : Int) (x : Sp) : Int :=
  let den : Nat := 128 * sm.toNat * (1000 + tz).toNat
  let pos : Nat := 1000 * x.toNat + 65536 * (-xm).toNat
  let neg : Nat := 65536 * xm.toNat + 1000 * (-x).toNat
  if neg ≤ pos then roundDiv false ((pos - neg) * 1953125) den
  else roundDiv true ((neg - pos) * 1953125) den

/-- A laid-out advance `P` from a run's start as the pen advance it needs,
in millionths of the size the file spells (`sm`): `P · 1953125 / (128 · sm)`,
rounded. The line's expansion cancels out of it — the layout scales the run
by the factor the viewer scales the pen by. -/
@[inline] def runOffset (sm : Int) (P : Sp) : Int :=
  roundDiv (P < 0) (P.natAbs * 1953125) (128 * sm.natAbs)

/-- The `TJ` number that brings a pen standing `d` millionths past its
target (short of it when negative) to within half a thousandth: `d / 1000`
rounded to the nearest integer, half up — zero exactly when the pen is
already that close. -/
@[inline] def nudge (d : Int) : Int := (d + 500) / 1000

/-- **A nudged pen stands within half a thousandth of the em of its
target.** Whatever the distance `d`, the residue `d − 1000 · nudge d` lies
in `[−500, 499]` millionths: the resolution of a `TJ` number, and nothing
more. -/
theorem nudge_between (d : Int) :
    -500 ≤ d - 1000 * nudge d ∧ d - 1000 * nudge d ≤ 499 := by
  unfold nudge
  omega

/-- An absolute move: the open array closed, `Tm` at the layout x and
`runY`, and the pen restarted at the x the `Tm` spells. -/
def TextSt.moveTo (st : TextSt) (runY : Sp) : TextSt :=
  { st.closeTJ.op (.move st.x runY) with
    pen := some { xm := st.x.toPtMilli, y := runY, adv := 0 } }

/-- Bring the pen to a run at `(st.x, runY)`. Inside an open array with
the face unchanged and the baseline the same, the move is the number that
puts the viewer's pen within half a thousandth of the em of the layout's
x (`nudge`, measured from where the file's own arithmetic left it), unless
that number exceeds ±32000 — a viewer that keeps adjustments in sixteen
bits (macOS Preview drops the whole array past ±32767) never sees one that
large. Any other move is an absolute `Tm` (`moveTo`), which closes the
array: a face or size change re-bases the pen, whose unit is the size. A
fresh line has no pen until its first run sets one. -/
def TextSt.toPen (st : TextSt) (changes : Bool) (runY : Sp) : TextSt :=
  match st.pen with
  | some p =>
    let n := nudge (p.adv - penTarget st.size.toPtMilli st.tz p.xm st.x)
    if !st.items.isEmpty && !changes && p.y == runY && n.natAbs ≤ 32000 then
      if n == 0 then st
      else { st with items := st.items.push (.adjust n),
                     pen := some { p with adv := p.adv - 1000 * n } }
    else st.moveTo runY
  | none => st.moveTo runY

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

/-- A run's string being placed: its glyph ids, their numbers beside
them, the pen (`Pen.adv`'s unit) and the laid-out advance `P` reached. One
record of scalars and scalar arrays, updated in place — a nested tuple
would cost the loop three allocations a glyph. -/
structure PlaceSt where
  gids : Array Nat
  nums : Array Int
  adv : Int
  P : Sp

/-- One glyph of a run onto its string: the number that brings the pen
from where the previous glyph's `/W` width left it to `tgt P` — the
glyph's layout position, `P` its laid-out advance from the run's start —
then the glyph and its own width. -/
@[inline] def placeStep (wμ : Nat → Int) (tgt : Sp → Int) (st : PlaceSt) :
    Nat × Char × Sp → PlaceSt
  | (g, _, a) =>
    let n := nudge (st.adv - tgt st.P)
    ⟨st.gids.push g, st.nums.push n, st.adv - 1000 * n + wμ g, st.P + a⟩

/-- `placeStep`'s string as a list: each glyph with the number set before
it, from pen `adv` at laid-out advance `P`. -/
def placeSpec (wμ : Nat → Int) (tgt : Sp → Int) :
    Int → Sp → List (Nat × Char × Sp) → List (Nat × Int)
  | _, _, [] => []
  | adv, P, (g, _, a) :: rest =>
    let n := nudge (adv - tgt P)
    (g, n) :: placeSpec wμ tgt (adv - 1000 * n + wμ g) (P + a) rest

/-- Where a viewer's pen stands as each glyph of a kerned string begins,
from pen `p` — §9.4.4's arithmetic, the number first, then the glyph's
width — whatever chose the numbers. -/
def penStarts (wμ : Nat → Int) : Int → List (Nat × Int) → List Int
  | _, [] => []
  | p, (g, n) :: rest => (p - 1000 * n) :: penStarts wμ (p - 1000 * n + wμ g) rest

/-- Each glyph's laid-out advance from the run's start. -/
def glyphStarts : Sp → List (Nat × Char × Sp) → List Sp
  | _, [] => []
  | P, (_, _, a) :: rest => P :: glyphStarts (P + a) rest

/-- The fold builds `placeSpec`'s string: its glyph ids, and beside them
its numbers. -/
theorem placeStep_fold_exact (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (ga : Array Nat) (na : Array Int) (adv : Int) (P : Sp) :
    (gs.foldl (placeStep wμ tgt) ⟨ga, na, adv, P⟩).gids.toList
        = ga.toList ++ (placeSpec wμ tgt adv P gs).map (·.1)
      ∧ (gs.foldl (placeStep wμ tgt) ⟨ga, na, adv, P⟩).nums.toList
        = na.toList ++ (placeSpec wμ tgt adv P gs).map (·.2) := by
  induction gs generalizing ga na adv P with
  | nil => simp [placeSpec]
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp only [List.foldl_cons, placeStep, placeSpec]
    obtain ⟨h1, h2⟩ := ih (ga.push g) (na.push (nudge (adv - tgt P)))
      (adv - 1000 * nudge (adv - tgt P) + wμ g) (P + a)
    exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩

theorem placeSpec_glyphs_id (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (adv : Int) (P : Sp) : (placeSpec wμ tgt adv P gs).map (·.1) = gs.map (·.1) := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, ih]

/-- Placing a run keeps its glyphs, in order: only numbers are added. -/
theorem place_glyphs_id (wμ : Nat → Int) (tgt : Sp → Int) (glyphs : Array (Nat × Char × Sp))
    (adv : Int) : (glyphs.foldl (placeStep wμ tgt) ⟨#[], #[], adv, 0⟩).gids = glyphs.map (·.1) := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, ← Array.foldl_toList, (placeStep_fold_exact ..).1]
  simpa using placeSpec_glyphs_id wμ tgt glyphs.toList adv 0

/-- The numbers the fold writes are `placeSpec`'s, the ones `place_between`
places by. -/
theorem place_nums_exact (wμ : Nat → Int) (tgt : Sp → Int) (glyphs : Array (Nat × Char × Sp))
    (adv : Int) : (glyphs.foldl (placeStep wμ tgt) ⟨#[], #[], adv, 0⟩).nums.toList
      = (placeSpec wμ tgt adv 0 glyphs.toList).map (·.2) := by
  rw [← Array.foldl_toList, (placeStep_fold_exact ..).2]
  simp

theorem placeSpec_length_exact (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (adv : Int) (P : Sp) : (penStarts wμ adv (placeSpec wμ tgt adv P gs)).length = gs.length := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, penStarts, ih]

theorem glyphStarts_length_exact (P : Sp) (gs : List (Nat × Char × Sp)) :
    (glyphStarts P gs).length = gs.length := by
  induction gs generalizing P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [glyphStarts, ih]

/-- **Every glyph a run paints starts where the layout put it**, to the
resolution of the file: by the viewer's own arithmetic over the numbers
`placeStep` writes and the widths the file declares (`penStarts`), each
glyph's pen stands within `[−500, 499]` millionths of the em — under half
a thousandth — of its target, the layout's position for it (both lists
hold one entry per glyph: `placeSpec_length_exact`,
`glyphStarts_length_exact`). The written advances are the laid-out
advances, pair kerns included; and since each number is chosen from where
the file's arithmetic actually left the pen, the residue never accumulates
along a line. -/
theorem place_between (wμ : Nat → Int) (tgt : Sp → Int) (adv : Int) (P : Sp)
    (gs : List (Nat × Char × Sp)) :
    ∀ d ∈ List.zipWith (· - ·) (penStarts wμ adv (placeSpec wμ tgt adv P gs))
        ((glyphStarts P gs).map tgt), -500 ≤ d ∧ d ≤ 499 := by
  induction gs generalizing adv P with
  | nil => simp [placeSpec, penStarts]
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp only [placeSpec, penStarts, glyphStarts, List.map_cons, List.zipWith_cons_cons,
      List.mem_cons]
    rintro d (rfl | hd)
    · have := nudge_between (adv - tgt P)
      omega
    · exact ih _ _ d hd

/-- A run's string: plain when no glyph needed a number, kerned otherwise. -/
def runItem (gids : Array Nat) (nums : Array Int) : TextItem :=
  if nums.all (· == 0) then .glyphs gids else .kerned gids nums

/-- A placed run onto the open array: its string, the layout x past its
width, and the pen where the file's arithmetic left it. -/
def TextSt.pushRun (st : TextSt) (item : TextItem) (w : Sp) (pen : Pen) : TextSt :=
  { st with items := st.items.push item, x := st.x + w, pen := some pen }

/-- One glyph run: the pen, then the face and colour when they change,
then the glyphs, each placed where the layout put it (`placeStep`): a
glyph's layout position is the run's x plus its laid-out advance from the
run's start — the pair kerns the layout applied included — under the
line's expansion as the layout scaled the run (`w + w·f/1000`). The pen
the file's arithmetic reaches is where every later move is measured from.
A kern (a run with no glyphs) only moves the layout position, like a gap. -/
def stepRun (remap : Array Nat) (lineSize ypdf : Sp) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Sp) (glyphs : Array (Nat × Char × Sp)) (segSize raise : Sp) :
    TextSt :=
  if glyphs.isEmpty then { st with x := st.x + w } else
  let runY := ypdf + raise
  let size := if segSize == 0 then lineSize else segSize
  let changes := st.font != (idx : Int) || st.size != size || st.color != color
  let st := st.toPen changes runY
  let st := if changes then st.setFace remap idx size color else st
  let p := st.pen.getD { xm := st.x.toPtMilli, y := runY, adv := 0 }
  let sm := st.size.toPtMilli
  let t0 := penTarget sm st.tz p.xm st.x
  let wf := st.widths.getD idx #[]
  -- Sized once: grown by doubling, these arrays' freed halves left the page
  -- renderer to fresh allocator pages, and rendering took twice as long.
  let r := glyphs.foldl (placeStep (wf.getD · 0) (fun P => t0 + runOffset sm P))
    ⟨Array.mkEmpty glyphs.size, Array.mkEmpty glyphs.size, p.adv, 0⟩
  st.pushRun (runItem r.gids r.nums) w { p with adv := r.adv }

def stepSeg (remap : Array Nat) (imgMap : Array (Option Nat)) (lineSize ypdf : Sp)
    (og : Origin) (st : TextSt) : Seg → TextSt
  | .rule w thickness raise color =>
    { st with rules := st.rules.push (color, st.x, ypdf + raise, w, thickness), x := st.x + w }
  | .image idx w h =>
    { st with images := st.images.push { x := st.x, y := ypdf, w, h,
                                         res := idx.bind fun k => imgMap[k]?.getD none,
                                         origin := og },
              x := st.x + w }
  | .gap w _ => { st with x := st.x + w }
  | .run idx color _ w glyphs segSize _ _ raise _ _ =>
    stepRun remap lineSize ypdf st idx color w glyphs segSize raise

/-- One line's operators, walked from a state whose `ops` are empty: the
expansion factor when it changes (`Tz`, §9.3.4, scales shapes and
advances alike — exactly hz-style expansion, and the run widths layout
emitted are already rescaled by the same factor), then the segments from
the line's left edge with no pen, then the array closed. The result's
`ops` are the line's own, for `stepLine` to append or to wrap; the images
it gathers carry the line's origin. The bleed shifts everything: layout
works in trim coordinates and the trim box sits `bleed` in from the
medium's corner. -/
def lineSt (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (og : Origin)
    (st : TextSt) (l : LineOut) : TextSt :=
  let ypdf := geom.bleed + geom.pageH - l.y
  let st : TextSt := { st with ops := #[] }
  let st := if l.expand != st.tz then { st.op (.scale (1000 + l.expand)) with tz := l.expand }
    else st
  let st := { st with x := geom.bleed + l.x, pen := none }
  (l.segs.foldl (stepSeg remap imgMap l.size ypdf og) st).closeTJ

/-- The tag every furniture line's operators sit under: running heads,
feet and page numbers are pagination artifacts (Table 363). -/
def furnitureTag : MarkTag := .artifact (some .pagination)

/-- One line onto the text object, under the wrapper its origin names: a
furniture line's operators as one pagination artifact; a line painting a
structure leaf as one marked-content sequence of that leaf's structure
type (identifier assigned later by `numberMarks`); a line no leaf owns as
one artifact of no type. A line whose operators are empty (an image-only
line, whose ink paints after `ET`) adds nothing — a sequence around
nothing would be an identifier with no content. A furniture line is
wrapped whatever it holds: the furniture census counts lines. -/
def stepLine (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let og := Origin.of tags l
  let s := lineSt geom remap imgMap og st l
  match og with
  | .furniture => { s with ops := st.ops.push (.marked furnitureTag s.ops) }
  | .unattributed =>
    { s with ops := if s.ops.isEmpty then st.ops else st.ops.push (.marked (.artifact none) s.ops) }
  | .leaf k tag =>
    { s with ops := if s.ops.isEmpty then st.ops
                    else st.ops.push (.marked (.content tag 0 k) s.ops) }

/-- The specification twin of `stepLine`: the same line, nothing wrapped —
what the writer emitted before marked content existed. `mark_ink_exact`
is stated against it. -/
def stepLinePlain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let s := lineSt geom remap imgMap (Origin.of tags l) st l
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

/-- An image that loaded is real content under its line's origin; the
placeholder box of one that did not is decoration — a layout artifact,
the diagnostic having already said why. -/
def imageOp (i : ImgOut) : ContentOp :=
  match i.res with
  | some n => .marked i.origin.mark #[.image i.x i.y i.w i.h n]
  | none => artifact (some .layout) (.imageMissing i.x i.y i.w i.h)

def imageOpPlain (i : ImgOut) : ContentOp :=
  match i.res with
  | some n => .image i.x i.y i.w i.h n
  | none => .imageMissing i.x i.y i.w i.h

/-- The tag a picture's paths sit under: the structure type the walk gave
the picture's leaf, or — for a path no leaf owns, which the layout never
ships (`placePicture` stamps every path with its picture's leaf) — an
artifact of no type. -/
def groupTag (tags : Array (Option String)) : Option Nat → MarkTag
  | some k =>
    match (tags[k]?).join with
    | some s => .content s 0 k
    | none => .artifact none
  | none => .artifact none

/-- An open group of paths closed onto the stream as one sequence. -/
def flushGroup (tags : Array (Option String)) (out : Array ContentOp) :
    Option (Option Nat × Array ContentOp) → Array ContentOp
  | none => out
  | some (lf, ops) => out.push (.marked (groupTag tags lf) ops)

/-- Picture paths grouped per picture: consecutive paths stamped with the
same leaf are one picture's ink and sit under one sequence (the layout
pushes a picture's paths together, `placePicture`). Structural on the
list; the open group travels as state so the walk needs no lookahead. -/
def pathGroupsList (geom : Geom) (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) : List PathOut → Array ContentOp
  | [] => flushGroup tags out cur
  | p :: rest =>
    let op := ContentOp.path p.fill p.stroke (pathSegs geom p.path)
    match cur with
    | some (lf, ops) =>
      if lf == p.leaf then pathGroupsList geom tags out (some (lf, ops.push op)) rest
      else pathGroupsList geom tags (flushGroup tags out cur) (some (p.leaf, #[op])) rest
    | none => pathGroupsList geom tags out (some (p.leaf, #[op])) rest

def pathGroups (geom : Geom) (tags : Array (Option String)) (paths : Array PathOut) :
    Array ContentOp :=
  pathGroupsList geom tags #[] none paths.toList

mutual

/-- Marked-content identifiers assigned in stream order from `n`: every
`content` tag takes the next number, artifacts take none, and the walk
descends every body — so identifiers are unique per page whatever the
construction nested (`numberMarks_mcids_exact`). The tag's type and leaf
are kept; only the identifier changes. -/
def TextOp.number (n : Nat) : TextOp → TextOp × Nat
  | o@(.scale _) => (o, n)
  | o@(.move _ _) => (o, n)
  | o@(.font _ _) => (o, n)
  | o@(.color _) => (o, n)
  | o@(.show _) => (o, n)
  | .marked (.artifact a) body =>
    let r := TextOp.numberList n #[] body.toList
    (.marked (.artifact a) r.1, r.2)
  | .marked (.content s _ k) body =>
    let r := TextOp.numberList (n + 1) #[] body.toList
    (.marked (.content s n k) r.1, r.2)

def TextOp.numberList (n : Nat) (acc : Array TextOp) : List TextOp → Array TextOp × Nat
  | [] => (acc, n)
  | o :: rest =>
    let r := TextOp.number n o
    TextOp.numberList r.2 (acc.push r.1) rest

end

mutual

def ContentOp.number (n : Nat) : ContentOp → ContentOp × Nat
  | o@(.fill _ _ _ _ _) => (o, n)
  | o@(.path _ _ _) => (o, n)
  | .text ops =>
    let r := TextOp.numberList n #[] ops.toList
    (.text r.1, r.2)
  | o@(.image _ _ _ _ _) => (o, n)
  | o@(.imageMissing _ _ _ _) => (o, n)
  | .marked (.artifact a) body =>
    let r := ContentOp.numberList n #[] body.toList
    (.marked (.artifact a) r.1, r.2)
  | .marked (.content s _ k) body =>
    let r := ContentOp.numberList (n + 1) #[] body.toList
    (.marked (.content s n k) r.1, r.2)

def ContentOp.numberList (n : Nat) (acc : Array ContentOp) :
    List ContentOp → Array ContentOp × Nat
  | [] => (acc, n)
  | o :: rest =>
    let r := ContentOp.number n o
    ContentOp.numberList r.2 (acc.push r.1) rest

end

/-- A page's operators with their marked-content identifiers assigned in
stream order from 0. -/
def numberMarks (ops : Array ContentOp) : Array ContentOp :=
  (ContentOp.numberList 0 #[] ops.toList).1

/-- One page's operations: fills first, in order (the page background,
then any bars), as one artifact of no stated type — the layout ships
backgrounds, bars and cut marks in one array; then picture paths, one
sequence per picture under its figure's type; then the text object, each
line under its origin's wrapper; then the images the text walk gathered,
each under its line's origin, a placeholder a layout artifact; then the
rules it gathered, as one layout artifact. Identifiers in stream order
over the middle — paths, text, images; the two artifact blocks hold fills
only and carry none, and a rule-heavy page would pay their rebuild for
nothing. Every painting operator sits under exactly one wrapper
(`mcids_partition_covers`). -/
def contentOps (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := pathGroups geom tags page.paths
  let st := page.lines.foldl (stepLine geom remap imgMap tags) { widths }
  let images := st.images.map imageOp
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let middle := numberMarks ((paths.push (.text st.ops)) ++ images)
  (artifactBlock none fills ++ middle) ++ artifactBlock (some .layout) rules

/-- The specification twin of `contentOps`: the same operations with no
marked content — the writer before this layer, kept so `mark_ink_exact`
can name the stream it must reproduce. -/
def contentOpsPlain (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := page.paths.map fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)
  let st := page.lines.foldl (stepLinePlain geom remap imgMap tags) { widths }
  let images := st.images.map imageOpPlain
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let body := (fills ++ paths).push (.text st.ops)
  (body ++ images) ++ rules

/-! ## The glyph census -/

/-- The glyph runs an item carries: a `TJ` string is one run, an
adjustment none. -/
def TextItem.runs : TextItem → List (Array Nat)
  | .glyphs gids => [gids]
  | .kerned gids _ => [gids]
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
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then [] else [glyphs.map (·.1)]
  | .gap _ _ => []
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

theorem moveTo_runs (st : TextSt) (y : Sp) : (st.moveTo y).runs = st.runs := by
  have h := op_runs st.closeTJ (.move st.x y) rfl
  rw [closeTJ_runs] at h
  exact h

theorem toPen_runs (st : TextSt) (c : Bool) (y : Sp) : (st.toPen c y).runs = st.runs := by
  unfold TextSt.toPen
  split
  · simp only []
    split
    · split
      · rfl
      · simp [TextSt.runs, TextItem.runs]
    · exact moveTo_runs st y
  · exact moveTo_runs st y

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

theorem runItem_runs (gids : Array Nat) (nums : Array Int) : (runItem gids nums).runs = [gids] := by
  unfold runItem
  split <;> rfl

theorem pushRun_runs (st : TextSt) (i : TextItem) (w : Sp) (p : Pen) :
    (st.pushRun i w p).runs = st.runs ++ i.runs := by
  simp [TextSt.pushRun, TextSt.runs]

theorem stepRun_runs (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char × Sp)) (ss raise : Sp) :
    (stepRun remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  unfold stepRun
  split
  · simp [TextSt.runs]
  · simp only [pushRun_runs, runItem_runs, Array.mkEmpty_eq, place_glyphs_id]
    congr 1
    simp only [apply_ite TextSt.runs, setFace_runs, toPen_runs, ite_self]

theorem stepSeg_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp) (og : Origin)
    (st : TextSt) (seg : Seg) : (stepSeg remap imgMap ls y og st seg).runs = st.runs ++ segRuns seg := by
  cases seg with
  | rule => simp [stepSeg, TextSt.runs, segRuns]
  | image => simp [stepSeg, TextSt.runs, segRuns]
  | gap => simp [stepSeg, TextSt.runs, segRuns]
  | run => exact stepRun_runs ..

theorem foldl_segs_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (segs : List Seg) (st : TextSt) :
    (segs.foldl (stepSeg remap imgMap ls y og) st).runs = st.runs ++ segs.flatMap segRuns := by
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
    (og : Origin) (st : TextSt) (l : LineOut) :
    (lineSt geom remap imgMap og st l).runs
      = st.items.toList.flatMap TextItem.runs ++ l.segs.toList.flatMap segRuns := by
  unfold lineSt
  simp only []
  rw [closeTJ_runs, ← Array.foldl_toList, foldl_segs_runs]
  congr 1
  split
  · simp [TextSt.runs, TextSt.op, TextOp.runs]
  · simp [TextSt.runs]

theorem lineSt_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) : (lineSt geom remap imgMap og st l).items = #[] := by
  unfold lineSt
  exact closeTJ_items _

/-- The runs of a text object's operators after one line: the line's runs
in segment order appended, whatever wrapper the origin chose — a wrapper
ships its body's runs, and an empty line ships none. -/
theorem stepLine_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).runs = st.runs ++ l.segs.toList.flatMap segRuns := by
  unfold stepLine
  have hs := lineSt_runs geom remap imgMap (Origin.of tags l) st l
  have hi := lineSt_items geom remap imgMap (Origin.of tags l) st l
  simp only [TextSt.runs] at hs ⊢
  rw [hi] at hs ⊢
  simp only [List.flatMap_nil, List.append_nil] at hs ⊢
  have hempty : (lineSt geom remap imgMap (Origin.of tags l) st l).ops.isEmpty = true →
      List.flatMap TextItem.runs st.items.toList = []
        ∧ List.flatMap segRuns l.segs.toList = [] := by
    intro he
    rw [← List.append_eq_nil_iff, ← hs, Array.isEmpty_iff.mp he]
    simp
  split
  · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
      List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
        List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
        List.append_assoc]

theorem stepLine_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).items = #[] := by
  simp only [stepLine]
  split <;> exact lineSt_items ..

theorem foldl_lines_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt) :
    (lines.foldl (stepLine geom remap imgMap tags) st).runs
      = st.runs ++ lines.flatMap (fun l => l.segs.toList.flatMap segRuns) := by
  induction lines generalizing st with
  | nil => simp
  | cons l rest ih => simp [ih, stepLine_runs, List.append_assoc]

theorem foldl_lines_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt) (h : st.items = #[]) :
    (lines.foldl (stepLine geom remap imgMap tags) st).items = #[] := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_items ..)

theorem imageOp_runs (i : ImgOut) : (imageOp i).runs = [] := by
  unfold imageOp
  split <;> simp [artifact, ContentOp.runs, ContentOp.runsList]

theorem flushGroup_runs (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) (hc : ∀ g ∈ cur, ∀ o ∈ g.2, o.runs = [])
    (ho : ∀ o ∈ out, o.runs = []) : ∀ o ∈ flushGroup tags out cur, o.runs = [] := by
  intro o h
  cases cur with
  | none => exact ho o h
  | some g =>
    simp only [flushGroup, Array.mem_push] at h
    rcases h with h | rfl
    · exact ho o h
    · simp only [ContentOp.runs, ContentOp.runsList_eq]
      exact List.flatMap_eq_nil_iff.mpr fun o' h' => hc g rfl o' (Array.mem_def.mpr h')

/-- A picture's paths paint no glyph run, however grouped. -/
theorem pathGroupsList_runs (geom : Geom) (tags : Array (Option String)) (paths : List PathOut)
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp))
    (hc : ∀ g ∈ cur, ∀ o ∈ g.2, o.runs = []) (ho : ∀ o ∈ out, o.runs = []) :
    ∀ o ∈ pathGroupsList geom tags out cur paths, o.runs = [] := by
  induction paths generalizing out cur with
  | nil => exact flushGroup_runs tags out cur hc ho
  | cons p rest ih =>
    simp only [pathGroupsList]
    have hop : ∀ o ∈ #[ContentOp.path p.fill p.stroke (pathSegs geom p.path)], o.runs = [] := by
      intro o h
      simp only [Array.mem_singleton] at h
      subst h
      rfl
    split
    · rename_i lf ops
      split
      · apply ih
        · intro g hg o h
          simp only [Option.mem_def, Option.some.injEq] at hg
          subst hg
          simp only [Array.mem_push] at h
          rcases h with h | rfl
          · exact hc _ rfl o h
          · rfl
        · exact ho
      · apply ih
        · intro g hg o h
          simp only [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact hop o h
        · exact flushGroup_runs tags out _ hc ho
    · apply ih
      · intro g hg o h
        simp only [Option.mem_def, Option.some.injEq] at hg
        subst hg
        exact hop o h
      · exact ho

theorem pathGroups_runs (geom : Geom) (tags : Array (Option String)) (paths : Array PathOut) :
    (pathGroups geom tags paths).toList.flatMap ContentOp.runs = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro o h
  exact pathGroupsList_runs geom tags paths.toList #[] none (by simp) (by simp) o
    (Array.mem_def.mpr h)

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

mutual

/-- Numbering the marked-content identifiers touches no glyph run. -/
theorem TextOp.number_runs : ∀ (o : TextOp) (n : Nat), (TextOp.number n o).1.runs = o.runs
  | .scale _, _ => rfl
  | .move _ _, _ => rfl
  | .font _ _, _ => rfl
  | .color _, _ => rfl
  | .show _, _ => rfl
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.runs, TextOp.runsList_eq, h]
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_runs body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.runs, TextOp.runsList_eq, h]

theorem TextOp.numberList_runs : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    (TextOp.numberList n acc l).1.toList.flatMap TextOp.runs
      = acc.toList.flatMap TextOp.runs ++ l.flatMap TextOp.runs
  | [], n, acc => by simp [TextOp.numberList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    simp [TextOp.numberList_runs rest, Array.toList_push, TextOp.number_runs o n]

end

mutual

theorem ContentOp.number_runs : ∀ (o : ContentOp) (n : Nat),
    (ContentOp.number n o).1.runs = o.runs
  | .fill _ _ _ _ _, _ => rfl
  | .path _ _ _, _ => rfl
  | .image _ _ _ _ _, _ => rfl
  | .imageMissing _ _ _ _, _ => rfl
  | .text ops, n => by
    have h := TextOp.numberList_runs ops.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, h]
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, ContentOp.runsList_eq, h]
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_runs body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, ContentOp.runsList_eq, h]

theorem ContentOp.numberList_runs : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    (ContentOp.numberList n acc l).1.toList.flatMap ContentOp.runs
      = acc.toList.flatMap ContentOp.runs ++ l.flatMap ContentOp.runs
  | [], n, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    simp [ContentOp.numberList_runs rest, Array.toList_push, ContentOp.number_runs o n]

end

theorem numberMarks_runs_list (ops : Array ContentOp) :
    (numberMarks ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold numberMarks
  rw [ContentOp.numberList_runs]
  simp

theorem numberMarks_runs (ops : Array ContentOp) : runsOf (numberMarks ops) = runsOf ops :=
  numberMarks_runs_list ops

/-- **The PDF paints every glyph run the page shipped, in order.** The glyph
census of the typed content stream is the page's run census: no run
dropped, none invented, none reordered — the `_text` fact for the
PageOut → ContentOp projection (not a `Conserves` instance: the walk
changes type, as `structTree_text` does). -/
theorem contentOps_text (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    runsOf (contentOps geom remap widths imgMap tags page) = pageRuns page := by
  unfold contentOps
  unfold runsOf pageRuns
  simp only [Array.toList_append, List.flatMap_append, artifactBlock_runs, numberMarks_runs_list]
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_map, List.flatMap_map, imageOp_runs,
    flatMap_nil_fun, pathGroups_runs]
  simp only [ContentOp.runs, flatMap_nil_fun, List.append_nil, List.nil_append]
  have hr := foldl_lines_runs geom remap imgMap tags page.lines.toList { widths }
  have hi := foldl_lines_items geom remap imgMap tags page.lines.toList { widths } rfl
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
    (og : Origin) (st : TextSt) (l : LineOut) :
    lineSt geom remap imgMap og st.plain l = lineSt geom remap imgMap og st l := by
  simp [lineSt, TextSt.plain]

/-- **Marking a line moves no ink**: the wrapped line and the plain line
agree on everything but the wrapper — whichever wrapper the origin chose,
and when the line's operators are empty and nothing is wrapped. -/
theorem stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).plain
      = (stepLinePlain geom remap imgMap tags st l).plain := by
  simp only [stepLine, stepLinePlain, TextSt.plain]
  have hempty : ∀ (a b : Array TextOp), b.isEmpty = true → inkText a = inkText (a ++ b) := by
    intro a b hb
    rw [Array.isEmpty_iff.mp hb, Array.append_empty]
  split
  · simp [inkText_push_marked, inkText_append]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append]

theorem stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) {st st' : TextSt} (h : st.plain = st'.plain) (l : LineOut) :
    (stepLinePlain geom remap imgMap tags st l).plain
      = (stepLinePlain geom remap imgMap tags st' l).plain := by
  have hl : lineSt geom remap imgMap (Origin.of tags l) st l
      = lineSt geom remap imgMap (Origin.of tags l) st' l := by
    rw [← lineSt_plain geom remap imgMap _ st, h, lineSt_plain]
  have ho : inkText st.ops = inkText st'.ops := congrArg TextSt.ops h
  simp only [stepLinePlain, TextSt.plain, hl, inkText_append, ho]

theorem foldl_stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (ls : List LineOut) {st st' : TextSt}
    (h : st.plain = st'.plain) :
    (ls.foldl (stepLinePlain geom remap imgMap tags) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st').plain := by
  induction ls generalizing st st' with
  | nil => exact h
  | cons l rest ih => exact ih (stepLinePlain_resp geom remap imgMap tags h l)

/-- The marked walk and the plain walk agree under `inkText`, line by line. -/
theorem foldl_stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (ls : List LineOut) (st : TextSt) :
    (ls.foldl (stepLine geom remap imgMap tags) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st).plain := by
  induction ls generalizing st with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl_cons]
    rw [ih, foldl_stepLinePlain_resp geom remap imgMap tags rest
      (stepLine_plain geom remap imgMap tags st l)]

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

theorem moveTo_plainOps (st : TextSt) (y : Sp) (h : inkText st.ops = st.ops) :
    inkText (st.moveTo y).ops = (st.moveTo y).ops :=
  op_plainOps _ _ (closeTJ_plainOps st h) (by simp [TextOp.ink])

theorem toPen_plainOps (st : TextSt) (c : Bool) (y : Sp) (h : inkText st.ops = st.ops) :
    inkText (st.toPen c y).ops = (st.toPen c y).ops := by
  unfold TextSt.toPen
  split
  · simp only []
    split
    · split
      · exact h
      · exact h
    · exact moveTo_plainOps st y h
  · exact moveTo_plainOps st y h

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
    (w : Sp) (glyphs : Array (Nat × Char × Sp)) (ss raise : Sp) (h : inkText st.ops = st.ops) :
    inkText (stepRun remap ls y st idx c w glyphs ss raise).ops
      = (stepRun remap ls y st idx c w glyphs ss raise).ops := by
  unfold stepRun
  split
  · exact h
  · simp only [TextSt.pushRun]
    split <;> split
    all_goals first
      | exact setFace_plainOps _ _ _ _ _ (toPen_plainOps _ _ _ h)
      | exact toPen_plainOps _ _ _ h

theorem stepSeg_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (st : TextSt) (seg : Seg) (h : inkText st.ops = st.ops) :
    inkText (stepSeg remap imgMap ls y og st seg).ops = (stepSeg remap imgMap ls y og st seg).ops := by
  cases seg with
  | rule => exact h
  | image => exact h
  | gap => exact h
  | run => exact stepRun_plainOps _ _ _ _ _ _ _ _ _ _ h

theorem foldl_segs_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (segs : List Seg) (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText (segs.foldl (stepSeg remap imgMap ls y og) st).ops
      = (segs.foldl (stepSeg remap imgMap ls y og) st).ops := by
  induction segs generalizing st with
  | nil => exact h
  | cons s rest ih => exact ih _ (stepSeg_plainOps _ _ _ _ _ _ _ h)

theorem lineSt_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    inkText (lineSt geom remap imgMap og st l).ops = (lineSt geom remap imgMap og st l).ops := by
  unfold lineSt
  simp only []
  apply closeTJ_plainOps
  rw [← Array.foldl_toList]
  apply foldl_segs_plainOps
  split
  · exact op_plainOps _ _ rfl (by simp [TextOp.ink])
  · rfl

theorem stepLinePlain_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) (h : inkText st.ops = st.ops) :
    inkText (stepLinePlain geom remap imgMap tags st l).ops
      = (stepLinePlain geom remap imgMap tags st l).ops := by
  simp only [stepLinePlain, inkText_append, h, lineSt_plainOps]

theorem foldl_stepLinePlain_plainOps (geom : Geom) (remap : Array Nat)
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ls : List LineOut) (st : TextSt)
    (h : inkText st.ops = st.ops) :
    inkText (ls.foldl (stepLinePlain geom remap imgMap tags) st).ops
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st).ops := by
  induction ls generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLinePlain_plainOps _ _ _ _ _ _ h)

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

theorem imageOp_ink (i : ImgOut) : (imageOp i).ink = [imageOpPlain i] := by
  unfold imageOp imageOpPlain
  split <;> simp [artifact_ink, ContentOp.ink, ContentOp.inkList]

/-- The ink an open path group holds. -/
def groupInk : Option (Option Nat × Array ContentOp) → List ContentOp
  | none => []
  | some (_, ops) => ContentOp.inkList ops.toList

theorem flushGroup_ink (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) :
    ContentOp.inkList (flushGroup tags out cur).toList
      = ContentOp.inkList out.toList ++ (groupInk cur) := by
  cases cur with
  | none => simp [flushGroup, groupInk]
  | some g =>
    obtain ⟨lf, ops⟩ := g
    simp [flushGroup, groupInk, Array.toList_push, ContentOp.inkList_append, ContentOp.inkList,
      ContentOp.ink]

/-- Grouping a page's paths per picture moves no path: the ink under the
groups is the paths, in order. -/
theorem pathGroupsList_ink (geom : Geom) (tags : Array (Option String)) (paths : List PathOut)
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)) :
    ContentOp.inkList (pathGroupsList geom tags out cur paths).toList
      = ContentOp.inkList out.toList ++ (groupInk cur)
        ++ paths.map (fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)) := by
  induction paths generalizing out cur with
  | nil => simp [pathGroupsList, flushGroup_ink]
  | cons p rest ih =>
    simp only [pathGroupsList]
    split
    · split
      · rw [ih]
        simp [groupInk, Array.toList_push, ContentOp.inkList_append, ContentOp.inkList,
          ContentOp.ink, List.append_assoc]
      · rw [ih, flushGroup_ink]
        simp [groupInk, ContentOp.inkList, ContentOp.ink, List.append_assoc]
    · rw [ih]
      simp [groupInk, ContentOp.inkList, ContentOp.ink, List.append_assoc]

theorem pathGroups_ink (geom : Geom) (tags : Array (Option String)) (paths : Array PathOut) :
    ContentOp.inkList (pathGroups geom tags paths).toList
      = paths.toList.map (fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)) := by
  unfold pathGroups
  rw [pathGroupsList_ink]
  simp [groupInk, ContentOp.inkList]

mutual

/-- Numbering the identifiers touches no ink. -/
theorem TextOp.number_ink : ∀ (o : TextOp) (n : Nat), (TextOp.number n o).1.ink = o.ink
  | .scale _, _ => rfl
  | .move _ _, _ => rfl
  | .font _ _, _ => rfl
  | .color _, _ => rfl
  | .show _, _ => rfl
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_ink body.toList n #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [TextOp.number, TextOp.ink, h]
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_ink body.toList (n + 1) #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [TextOp.number, TextOp.ink, h]

theorem TextOp.numberList_ink : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    TextOp.inkList (TextOp.numberList n acc l).1.toList
      = TextOp.inkList acc.toList ++ (TextOp.inkList l)
  | [], n, acc => by simp [TextOp.numberList, TextOp.inkList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    rw [TextOp.numberList_ink rest, Array.toList_push, TextOp.inkList_append, TextOp.inkList,
      TextOp.inkList, TextOp.number_ink o n]
    simp [TextOp.inkList]

end

mutual

theorem ContentOp.number_ink : ∀ (o : ContentOp) (n : Nat), (ContentOp.number n o).1.ink = o.ink
  | .fill _ _ _ _ _, _ => rfl
  | .path _ _ _, _ => rfl
  | .image _ _ _ _ _, _ => rfl
  | .imageMissing _ _ _ _, _ => rfl
  | .text ops, n => by
    have h := TextOp.numberList_ink ops.toList n #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, inkText, h]
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_ink body.toList n #[]
    simp only [ContentOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, h]
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_ink body.toList (n + 1) #[]
    simp only [ContentOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, h]

theorem ContentOp.numberList_ink : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    ContentOp.inkList (ContentOp.numberList n acc l).1.toList
      = ContentOp.inkList acc.toList ++ (ContentOp.inkList l)
  | [], n, acc => by simp [ContentOp.numberList, ContentOp.inkList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    rw [ContentOp.numberList_ink rest, Array.toList_push, ContentOp.inkList_append,
      ContentOp.inkList, ContentOp.inkList, ContentOp.number_ink o n]
    simp [ContentOp.inkList]

end

theorem numberMarks_ink_list (ops : Array ContentOp) :
    ContentOp.inkList (numberMarks ops).toList = ContentOp.inkList ops.toList := by
  unfold numberMarks
  rw [ContentOp.numberList_ink]
  simp [ContentOp.inkList]

theorem numberMarks_ink (ops : Array ContentOp) : inkOps (numberMarks ops) = inkOps ops := by
  unfold inkOps
  rw [numberMarks_ink_list]

/-- **Marking moves no ink.** The stream this layer builds, with every
marked-content wrapper removed, is the stream the writer built before the
layer existed (`contentOpsPlain`, the specification twin): same
operators, same order, same operands — so the same bytes
(`render_inkOps_exact`), and the strip of marked-content lines the
acceptance runs is this equation on the file. Both wrapper kinds are
covered: artifacts and structure content alike hide nothing, and the
identifier numbering rewrites tags only. A fact of the content stream,
not a projection of an IR statement: the IR never sees marked content. -/
theorem mark_ink_exact (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    inkOps (contentOps geom remap widths imgMap tags page)
      = contentOpsPlain geom remap widths imgMap tags page := by
  unfold contentOps contentOpsPlain
  simp only [inkOps, Array.toList_append, ContentOp.inkList_append, numberMarks_ink_list]
  have hp := foldl_stepLine_plain geom remap imgMap tags page.lines.toList { widths }
  rw [Array.foldl_toList, Array.foldl_toList] at hp
  have hpo := foldl_stepLinePlain_plainOps geom remap imgMap tags page.lines.toList { widths } rfl
  rw [Array.foldl_toList] at hpo
  have hops : inkText (page.lines.foldl (stepLine geom remap imgMap tags) { widths }).ops
      = (page.lines.foldl (stepLinePlain geom remap imgMap tags) { widths }).ops := by
    rw [← hpo]; exact congrArg TextSt.ops hp
  have himg := congrArg TextSt.images hp
  have hrul := congrArg TextSt.rules hp
  simp only [TextSt.plain] at himg hrul
  simp only [Array.toList_push, ContentOp.inkList_append,
    artifactBlock_ink, pathGroups_ink, Array.toList_map, ContentOp.inkList, ContentOp.ink, hops,
    himg, hrul, List.append_nil]
  rw [inkList_map _ (fun f => ContentOp.fill f.color (geom.bleed + f.x)
      (geom.bleed + geom.pageH - f.y - f.h) f.w f.h) _ (fun f => by simp [ContentOp.ink]),
    inkList_map _ imageOpPlain _ imageOp_ink,
    inkList_map _ (fun (t : Ir.Color × Sp × Sp × Sp × Sp) =>
      ContentOp.fill t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => by simp [ContentOp.ink])]
  apply Array.toList_inj.mp
  simp [Array.toList_append, Array.toList_push, Array.toList_map]

/-! ### Every painting operator sits under a wrapper -/

def TextOp.isMarked : TextOp → Bool
  | .marked _ _ => true
  | .scale _ => false
  | .move _ _ => false
  | .font _ _ => false
  | .color _ => false
  | .show _ => false

/-- A page-level operation the layer leaves nothing bare under: a wrapper,
or the text object with every operator of its own wrapped. -/
def ContentOp.wrapped : ContentOp → Bool
  | .marked _ _ => true
  | .text ops => ops.all TextOp.isMarked
  | .fill _ _ _ _ _ => false
  | .path _ _ _ => false
  | .image _ _ _ _ _ => false
  | .imageMissing _ _ _ _ => false

theorem TextOp.number_marked (o : TextOp) (n : Nat) : (TextOp.number n o).1.isMarked = o.isMarked := by
  cases o with
  | marked t body => cases t <;> simp [TextOp.number, TextOp.isMarked]
  | _ => rfl

theorem TextOp.numberList_marked (l : List TextOp) (n : Nat) (acc : Array TextOp)
    (ha : ∀ o ∈ acc, o.isMarked = true) (hl : ∀ o ∈ l, o.isMarked = true) :
    ∀ o ∈ (TextOp.numberList n acc l).1, o.isMarked = true := by
  induction l generalizing n acc with
  | nil => simpa [TextOp.numberList] using ha
  | cons o rest ih =>
    rw [TextOp.numberList]
    refine ih _ _ ?_ (fun o h => hl o (List.mem_cons_of_mem _ h))
    intro o' h
    simp only [Array.mem_push] at h
    rcases h with h | rfl
    · exact ha o' h
    · rw [TextOp.number_marked]
      exact hl o (List.mem_cons_self ..)

theorem ContentOp.number_wrapped (o : ContentOp) (n : Nat) (h : o.wrapped = true) :
    (ContentOp.number n o).1.wrapped = true := by
  cases o with
  | text ops =>
    simp only [ContentOp.number, ContentOp.wrapped, Array.all_eq_true_iff_forall_mem] at h ⊢
    exact TextOp.numberList_marked ops.toList n #[] (by simp) (fun o h' => h o (Array.mem_def.mpr h'))
  | marked t body => cases t <;> simp [ContentOp.number, ContentOp.wrapped]
  | fill => exact absurd h (by simp [ContentOp.wrapped])
  | path => exact absurd h (by simp [ContentOp.wrapped])
  | image => exact absurd h (by simp [ContentOp.wrapped])
  | imageMissing => exact absurd h (by simp [ContentOp.wrapped])

theorem ContentOp.numberList_wrapped (l : List ContentOp) (n : Nat) (acc : Array ContentOp)
    (ha : ∀ o ∈ acc, o.wrapped = true) (hl : ∀ o ∈ l, o.wrapped = true) :
    ∀ o ∈ (ContentOp.numberList n acc l).1, o.wrapped = true := by
  induction l generalizing n acc with
  | nil => simpa [ContentOp.numberList] using ha
  | cons o rest ih =>
    rw [ContentOp.numberList]
    refine ih _ _ ?_ (fun o h => hl o (List.mem_cons_of_mem _ h))
    intro o' h
    simp only [Array.mem_push] at h
    rcases h with h | rfl
    · exact ha o' h
    · exact ContentOp.number_wrapped o n (hl o (List.mem_cons_self ..))

/-- Every operator the line walk puts on the text object is under a
wrapper: a line's operators are wrapped or, when empty, absent. -/
theorem stepLine_marked (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut)
    (h : ∀ o ∈ st.ops, o.isMarked = true) :
    ∀ o ∈ (stepLine geom remap imgMap tags st l).ops, o.isMarked = true := by
  have push : ∀ t body o, o ∈ st.ops.push (.marked t body) → o.isMarked = true := by
    intro t body o ho
    simp only [Array.mem_push] at ho
    rcases ho with ho | rfl
    · exact h o ho
    · rfl
  intro o
  simp only [stepLine]
  split
  · exact push _ _ o
  · split
    · exact h o
    · exact push _ _ o
  · split
    · exact h o
    · exact push _ _ o

theorem foldl_lines_marked (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt)
    (h : ∀ o ∈ st.ops, o.isMarked = true) :
    ∀ o ∈ (lines.foldl (stepLine geom remap imgMap tags) st).ops, o.isMarked = true := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_marked geom remap imgMap tags st l h)

theorem flushGroup_wrapped (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) (ho : ∀ o ∈ out, o.wrapped = true) :
    ∀ o ∈ flushGroup tags out cur, o.wrapped = true := by
  intro o h
  cases cur with
  | none => exact ho o h
  | some g =>
    simp only [flushGroup, Array.mem_push] at h
    rcases h with h | rfl
    · exact ho o h
    · rfl

theorem pathGroupsList_wrapped (geom : Geom) (tags : Array (Option String)) (paths : List PathOut)
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp))
    (ho : ∀ o ∈ out, o.wrapped = true) :
    ∀ o ∈ pathGroupsList geom tags out cur paths, o.wrapped = true := by
  induction paths generalizing out cur with
  | nil => exact flushGroup_wrapped tags out cur ho
  | cons p rest ih =>
    simp only [pathGroupsList]
    split
    · split
      · exact ih _ _ ho
      · exact ih _ _ (flushGroup_wrapped tags out _ ho)
    · exact ih _ _ ho

theorem imageOp_wrapped (i : ImgOut) : (imageOp i).wrapped = true := by
  unfold imageOp
  split <;> rfl

/-- **Every painting operator sits under exactly one wrapper.** At the top
of the stream every operation is a marked-content sequence or the text
object, and every operator of the text object is a marked-content
sequence: no fill, path, glyph run or image is bare — real content under
its structure type, everything else an artifact. The identifier half of
the statement is `numberMarks_mcids_exact`. -/
theorem wrapped_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags page, o.wrapped = true := by
  unfold contentOps numberMarks
  intro o ho
  simp only [Array.mem_append] at ho
  rcases ho with (hf | hm) | hr
  · rw [mem_artifactBlock hf]; rfl
  · refine ContentOp.numberList_wrapped _ _ _ (by simp) ?_ o hm
    intro o ho
    simp only [Array.mem_toList_iff, Array.mem_append, Array.mem_push, Array.mem_map] at ho
    rcases ho with (hp | rfl) | ⟨i, _, rfl⟩
    · exact pathGroupsList_wrapped geom tags _ #[] none (by simp) o hp
    · simp only [ContentOp.wrapped, Array.all_eq_true_iff_forall_mem]
      have := foldl_lines_marked geom remap imgMap tags page.lines.toList { widths } (by simp)
      rw [Array.foldl_toList] at this
      exact this
    · exact imageOp_wrapped i
  · rw [mem_artifactBlock hr]; rfl

/-- **No decoration is left bare** — the corollary `wrapped_covers`
projects: every fill and every placeholder box sits under a wrapper. -/
theorem artifacts_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags page, o.decoration = false := by
  intro o ho
  have h := wrapped_covers geom remap widths imgMap tags page o ho
  cases o <;> simp_all [ContentOp.wrapped, ContentOp.decoration]

/-! ### Identifiers in stream order -/

/-- A content opener's identifier and leaf; nothing for an artifact or an
operator. -/
def Line.contentOpen : Line → Option (Nat × Nat)
  | .open (.content _ m k) => some (m, k)
  | .open (.artifact _) => none
  | .op _ => none
  | .emc => none

def Line.isPaginationOpen : Line → Bool
  | .open (.artifact (some .pagination)) => true
  | .open (.artifact (some .layout)) => false
  | .open (.artifact (some .page)) => false
  | .open (.artifact none) => false
  | .open (.content _ _ _) => false
  | .op _ => false
  | .emc => false

/-- The `(identifier, leaf)` pairs a stream's content openers carry, in
stream order. -/
def contentOpens (ls : List Line) : List (Nat × Nat) := ls.filterMap Line.contentOpen

mutual

/-- The content openers under a text operator, without rendering them:
`TextOp.lines` spells every operator on the way to the same list
(`marksList_eq_contentOpens`), which on a rule-heavy page is a full render
paid a second time. -/
def TextOp.marks (acc : Array (Nat × Nat)) : TextOp → Array (Nat × Nat)
  | .scale _ => acc
  | .move _ _ => acc
  | .font _ _ => acc
  | .color _ => acc
  | .show _ => acc
  | .marked (.artifact _) body => TextOp.marksList acc body.toList
  | .marked (.content _ m k) body => TextOp.marksList (acc.push (m, k)) body.toList

def TextOp.marksList (acc : Array (Nat × Nat)) : List TextOp → Array (Nat × Nat)
  | [] => acc
  | o :: rest => TextOp.marksList (TextOp.marks acc o) rest

end

mutual

def ContentOp.marks (acc : Array (Nat × Nat)) : ContentOp → Array (Nat × Nat)
  | .fill _ _ _ _ _ => acc
  | .path _ _ _ => acc
  | .text ops => TextOp.marksList acc ops.toList
  | .image _ _ _ _ _ => acc
  | .imageMissing _ _ _ _ => acc
  | .marked (.artifact _) body => ContentOp.marksList acc body.toList
  | .marked (.content _ m k) body => ContentOp.marksList (acc.push (m, k)) body.toList

def ContentOp.marksList (acc : Array (Nat × Nat)) : List ContentOp → Array (Nat × Nat)
  | [] => acc
  | o :: rest => ContentOp.marksList (ContentOp.marks acc o) rest

end

/-- The marked content of one page: its identifiers and the leaves they
paint, read off the typed stream — what the structure walk keys on. -/
def pageMarks (ops : Array ContentOp) : Array (Nat × Nat) := ContentOp.marksList #[] ops.toList

theorem contentOpens_append (a b : List Line) :
    contentOpens (a ++ b) = contentOpens a ++ contentOpens b := by
  simp [contentOpens, List.filterMap_append]

theorem contentOpens_op (s : String) : contentOpens [.op s] = [] := rfl
theorem contentOpens_emc : contentOpens [.emc] = [] := rfl
theorem contentOpens_nil : contentOpens [] = [] := rfl

/-- Two adjacent ranges are one, however the second's start is spelled. -/
theorem range'_append_of (s m s' n : Nat) (h : s' = s + m) :
    List.range' s m ++ List.range' s' n = List.range' s (m + n) := by
  subst h
  have := @List.range'_append s m n 1
  simpa only [Nat.one_mul] using this

theorem TextOp.linesList_push (acc : Array TextOp) (o : TextOp) :
    TextOp.linesList (acc.push o).toList = TextOp.linesList acc.toList ++ o.lines := by
  rw [Array.toList_push, TextOp.linesList_append]
  simp [TextOp.linesList]

theorem ContentOp.linesList_push (acc : Array ContentOp) (o : ContentOp) :
    ContentOp.linesList (acc.push o).toList = ContentOp.linesList acc.toList ++ o.lines := by
  rw [Array.toList_push, ContentOp.linesList_append]
  simp [ContentOp.linesList]

theorem range'_cons_of (n m : Nat) (h : n + 1 ≤ m) :
    n :: List.range' (n + 1) (m - (n + 1)) = List.range' n (m - n) := by
  rw [show m - n = (m - (n + 1)) + 1 by omega]
  rfl

mutual

/-- The identifiers the numbering hands out are the run from `n` of the
count it returns, in stream order. -/
theorem TextOp.number_mcids : ∀ (o : TextOp) (n : Nat),
    (contentOpens (TextOp.number n o).1.lines).map Prod.fst
      = List.range' n ((TextOp.number n o).2 - n)
    ∧ n ≤ (TextOp.number n o).2
  | .scale _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .move _ _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .font _ _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .color _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .show _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_mcids body.toList n #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [TextOp.number, TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_mcids body.toList (n + 1) #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [TextOp.number, TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append, List.filterMap_nil, List.append_nil, List.map_cons]
    rw [← contentOpens, h.1, range'_cons_of _ _ h.2]
    exact ⟨rfl, by omega⟩

theorem TextOp.numberList_mcids : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    (contentOpens (TextOp.linesList (TextOp.numberList n acc l).1.toList)).map Prod.fst
      = (contentOpens (TextOp.linesList acc.toList)).map Prod.fst
        ++ List.range' n ((TextOp.numberList n acc l).2 - n)
    ∧ n ≤ (TextOp.numberList n acc l).2
  | [], n, acc => by simp [TextOp.numberList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    have ho := TextOp.number_mcids o n
    have ih := TextOp.numberList_mcids rest (TextOp.number n o).2 (acc.push (TextOp.number n o).1)
    rw [ih.1, TextOp.linesList_push, contentOpens_append, List.map_append, ho.1, List.append_assoc,
      range'_append_of _ _ _ _ (Nat.add_sub_cancel' ho.2).symm]
    refine ⟨?_, by omega⟩
    congr 2
    omega

end

mutual

theorem ContentOp.number_mcids : ∀ (o : ContentOp) (n : Nat),
    (contentOpens (ContentOp.number n o).1.lines).map Prod.fst
      = List.range' n ((ContentOp.number n o).2 - n)
    ∧ n ≤ (ContentOp.number n o).2
  | .fill _ _ _ _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .path _ _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .image _ _ _ _ _, _ => by
    simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .imageMissing _ _ _ _, _ => by
    simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .text ops, n => by
    have h := TextOp.numberList_mcids ops.toList n #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_mcids body.toList n #[]
    simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_mcids body.toList (n + 1) #[]
    simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil, List.map_cons]
    rw [← contentOpens, h.1, range'_cons_of _ _ h.2]
    exact ⟨rfl, by omega⟩

theorem ContentOp.numberList_mcids : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    (contentOpens (ContentOp.linesList (ContentOp.numberList n acc l).1.toList)).map Prod.fst
      = (contentOpens (ContentOp.linesList acc.toList)).map Prod.fst
        ++ List.range' n ((ContentOp.numberList n acc l).2 - n)
    ∧ n ≤ (ContentOp.numberList n acc l).2
  | [], n, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    have ho := ContentOp.number_mcids o n
    have ih := ContentOp.numberList_mcids rest (ContentOp.number n o).2
      (acc.push (ContentOp.number n o).1)
    rw [ih.1, ContentOp.linesList_push, contentOpens_append, List.map_append, ho.1,
      List.append_assoc, range'_append_of _ _ _ _ (Nat.add_sub_cancel' ho.2).symm]
    refine ⟨?_, by omega⟩
    congr 2
    omega

end

mutual

theorem TextOp.marks_eq_contentOpens : ∀ (o : TextOp) (acc : Array (Nat × Nat)),
    TextOp.marks acc o = acc ++ (contentOpens o.lines).toArray
  | .scale _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .move _ _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .font _ _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .color _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .show _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .marked (.artifact a) body, acc => by
    rw [TextOp.marks, TextOp.marksList_eq_contentOpens body.toList]
    simp [TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append]
  | .marked (.content s m k) body, acc => by
    rw [TextOp.marks, TextOp.marksList_eq_contentOpens body.toList]
    simp [TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append]

theorem TextOp.marksList_eq_contentOpens : ∀ (l : List TextOp) (acc : Array (Nat × Nat)),
    TextOp.marksList acc l = acc ++ (contentOpens (TextOp.linesList l)).toArray
  | [], acc => by simp [TextOp.marksList, TextOp.linesList, contentOpens]
  | o :: rest, acc => by
    rw [TextOp.marksList, TextOp.marksList_eq_contentOpens rest, TextOp.marks_eq_contentOpens o,
      TextOp.linesList, contentOpens_append]
    simp

end

mutual

theorem ContentOp.marks_eq_contentOpens : ∀ (o : ContentOp) (acc : Array (Nat × Nat)),
    ContentOp.marks acc o = acc ++ (contentOpens o.lines).toArray
  | .fill _ _ _ _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .path _ _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .image _ _ _ _ _, acc => by
    simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .imageMissing _ _ _ _, acc => by
    simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .text ops, acc => by
    rw [ContentOp.marks, TextOp.marksList_eq_contentOpens ops.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]
  | .marked (.artifact a) body, acc => by
    rw [ContentOp.marks, ContentOp.marksList_eq_contentOpens body.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]
  | .marked (.content s m k) body, acc => by
    rw [ContentOp.marks, ContentOp.marksList_eq_contentOpens body.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]

theorem ContentOp.marksList_eq_contentOpens : ∀ (l : List ContentOp) (acc : Array (Nat × Nat)),
    ContentOp.marksList acc l = acc ++ (contentOpens (ContentOp.linesList l)).toArray
  | [], acc => by simp [ContentOp.marksList, ContentOp.linesList, contentOpens]
  | o :: rest, acc => by
    rw [ContentOp.marksList, ContentOp.marksList_eq_contentOpens rest,
      ContentOp.marks_eq_contentOpens o, ContentOp.linesList, contentOpens_append]
    simp

end

/-- The page's marks are the content openers of its lines, in order. -/
theorem pageMarks_eq_contentOpens (ops : Array ContentOp) :
    pageMarks ops = (contentOpens (lines ops)).toArray := by
  unfold pageMarks lines
  rw [ContentOp.marksList_eq_contentOpens]
  simp

/-- **`numberMarks_mcids_exact`**: a numbered stream's marked-content
identifiers, in stream order, are exactly `0, 1, …, n−1` — unique per page
(§14.7.5.1), with no gap, however the construction nested them. -/
theorem numberMarks_mcids_exact (ops : Array ContentOp) :
    (pageMarks (numberMarks ops)).toList.map Prod.fst = List.range (pageMarks (numberMarks ops)).size := by
  have h := ContentOp.numberList_mcids ops.toList 0 #[]
  simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
    List.nil_append, Nat.sub_zero] at h
  rw [pageMarks_eq_contentOpens]
  unfold numberMarks lines
  have hl := congrArg List.length h.1
  rw [List.length_map, List.length_range'] at hl
  rw [List.toList_toArray, List.size_toArray, hl, h.1, List.range_eq_range']

/-- A block of fills opens no content sequence. -/
theorem fillBlock_contentOpens (k : Option ArtifactKind) (fills : Array ContentOp)
    (hf : ∀ o ∈ fills, ∃ c x y w h, o = ContentOp.fill c x y w h) :
    contentOpens (ContentOp.linesList (artifactBlock k fills).toList) = [] := by
  have hl : ∀ (l : List ContentOp), (∀ o ∈ l, ∃ c x y w h, o = ContentOp.fill c x y w h) →
      contentOpens (ContentOp.linesList l) = [] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons o rest ih =>
      intro h
      obtain ⟨c, x, y, w, hh, rfl⟩ := h o (List.mem_cons_self ..)
      rw [ContentOp.linesList]
      simp only [ContentOp.lines, contentOpens_append, contentOpens_op, List.nil_append]
      exact ih (fun o ho => h o (List.mem_cons_of_mem _ ho))
  unfold artifactBlock
  split
  · rfl
  · simp only [ContentOp.linesList, ContentOp.lines,
      List.append_nil, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append,
      List.filterMap_nil]
    rw [← contentOpens, hl fills.toList (fun o ho => hf o (Array.mem_toList_iff.mp ho))]

/-- **`mcids_partition_covers`** (the `_covers` statement): every painting
operator of a page is under exactly one wrapper (`wrapped_covers`), and the
identifiers its content wrappers carry are `0 … n−1` in stream order —
the two fill blocks around the numbered middle carry none. -/
theorem mcids_partition_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    (∀ o ∈ contentOps geom remap widths imgMap tags page, o.wrapped = true)
    ∧ (pageMarks (contentOps geom remap widths imgMap tags page)).toList.map Prod.fst
        = List.range (pageMarks (contentOps geom remap widths imgMap tags page)).size := by
  refine ⟨wrapped_covers geom remap widths imgMap tags page, ?_⟩
  unfold contentOps
  have hA := fillBlock_contentOpens none (page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h)
    (fun o ho => by
      simp only [Array.mem_map] at ho
      obtain ⟨f, _, rfl⟩ := ho
      exact ⟨_, _, _, _, _, rfl⟩)
  have hC := fillBlock_contentOpens (some .layout)
    ((page.lines.foldl (stepLine geom remap imgMap tags) { widths }).rules.map
      fun (c, x, y, w, h) => ContentOp.fill c x y w h)
    (fun o ho => by
      simp only [Array.mem_map] at ho
      obtain ⟨t, _, rfl⟩ := ho
      exact ⟨_, _, _, _, _, rfl⟩)
  have hmid : ∀ (a m c : Array ContentOp),
      contentOpens (ContentOp.linesList a.toList) = [] →
      contentOpens (ContentOp.linesList c.toList) = [] →
      pageMarks ((a ++ m) ++ c) = pageMarks m := by
    intro a m c ha hc
    rw [pageMarks_eq_contentOpens, pageMarks_eq_contentOpens]
    unfold lines
    rw [Array.toList_append, Array.toList_append, ContentOp.linesList_append,
      ContentOp.linesList_append, contentOpens_append, contentOpens_append, ha, hc]
    simp
  rw [hmid _ _ _ hA hC]
  exact numberMarks_mcids_exact _

/-! ### Furniture -/

/-- The pagination artifacts at the top of a text object. -/
def textArtifacts (ops : Array TextOp) : Nat :=
  (TextOp.linesList ops.toList).countP Line.isPaginationOpen

theorem stripMarks_countP_pagination (ls : List Line) :
    (stripMarks ls).countP Line.isPaginationOpen = 0 := by
  rw [List.countP_eq_zero]
  intro l hl
  simp only [stripMarks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hl
  cases l with
  | op s => simp [Line.isPaginationOpen]
  | emc => simp [Line.isPaginationOpen]
  | «open» t => simp [Line.isOpen] at hl

theorem lineSt_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    textArtifacts (lineSt geom remap imgMap og st l).ops = 0 := by
  have h := lineSt_plainOps geom remap imgMap og st l
  unfold textArtifacts
  rw [← h, inkText, List.toList_toArray, TextOp.linesList_ink, stripMarks_countP_pagination]

/-- A line is furniture exactly when its origin says so. -/
theorem Origin.of_furniture_iff (tags : Array (Option String)) (l : LineOut) :
    Origin.of tags l = .furniture ↔ l.furniture = true := by
  unfold Origin.of
  split
  · simp [*]
  · rename_i hf
    simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.false_eq_true, iff_false]
    split
    · split <;> simp
    · simp

theorem stepLine_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    textArtifacts (stepLine geom remap imgMap tags st l).ops
      = textArtifacts st.ops + (if l.furniture then 1 else 0) := by
  unfold textArtifacts
  have hpush : ∀ og t, (TextOp.linesList (st.ops.push (.marked t
      (lineSt geom remap imgMap og st l).ops)).toList).countP Line.isPaginationOpen
      = (TextOp.linesList st.ops.toList).countP Line.isPaginationOpen
        + (if (Line.open t).isPaginationOpen then 1 else 0) := by
    intro og t
    have h0 := lineSt_textArtifacts geom remap imgMap og st l
    unfold textArtifacts at h0
    rw [TextOp.linesList_push, List.countP_append, TextOp.lines, List.countP_cons,
      List.countP_append, h0]
    simp [Line.isPaginationOpen]
  simp only [stepLine]
  generalize hog : Origin.of tags l = og
  cases og with
  | furniture =>
    have hf := (Origin.of_furniture_iff tags l).mp hog
    dsimp only
    rw [hpush]
    simp [hf, furnitureTag, Line.isPaginationOpen]
  | unattributed =>
    have hf : l.furniture = false := by
      cases hfl : l.furniture with
      | false => rfl
      | true =>
        have := (Origin.of_furniture_iff tags l).mpr hfl
        rw [hog] at this
        cases this
    dsimp only
    split
    · simp [hf]
    · rw [hpush]
      simp [hf, Line.isPaginationOpen]
  | leaf k tag =>
    have hf : l.furniture = false := by
      cases hfl : l.furniture with
      | false => rfl
      | true =>
        have := (Origin.of_furniture_iff tags l).mpr hfl
        rw [hog] at this
        cases this
    dsimp only
    split
    · simp [hf]
    · rw [hpush]
      simp [hf, Line.isPaginationOpen]

/-- **Every furniture line is one pagination artifact, and no flow line
is any.** The text object `contentOps` ships carries exactly one
pagination wrapper per line the furniture pass laid — the count is the
census the artifact acceptance reads. -/
theorem furniture_covers (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : Array LineOut) :
    textArtifacts (lines.foldl (stepLine geom remap imgMap tags) {}).ops
      = (lines.filter (·.furniture)).size := by
  have h : ∀ (ls : List LineOut) (st : TextSt),
      textArtifacts (ls.foldl (stepLine geom remap imgMap tags) st).ops
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
