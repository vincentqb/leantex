module

public import LeanTex.Core.Dim
public import LeanTex.Core.Color

/-!
# One vector model for pictures, SVG images and PDF figures

A figure is a painter's-algorithm tree of draws, groups, symbol uses,
outline stamps, rasters, engine-set labels and ink-free words, in one frame
of `Sp` coordinates with y growing upward. The meaning is the fragment PDF
(ISO 32000-2 §8, §11) and SVG 2 (§13, CSS Masking 1, Compositing 1) share:
nodes paint in array order; a group's kids live in its child frame, painting
is restricted to the intersection of its clips, and a group alpha below 1000
composites the kids as one isolated group; a stroke is centred on its path,
its width and dash live in the node's frame, and width 0 is the thinnest
visible line (PDF's meaning, and TikZ's `line width=0pt`). Cap, join and
miter limit are always explicit, because the two formats start from
different defaults: PDF's miter limit is 10 and SVG's is 4.

Matrices are exact rationals and compose exactly; no point is ever
transformed by a matrix (`Affine.apply` exists for the algebra and for box
images). A page placement is an integer isometry (`Iso`), applied to
coordinates exactly. The algebra's proofs live in `GfxAffine`, off the
import chain to the elaborator.
-/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

/-- A point in a figure frame: `Sp` at 2⁻¹⁶ of the frame unit, y up. -/
public abbrev Pt := Sp × Sp

/-- A box: min corner, then max corner. `Ir.Pic.Box` is this type. -/
public abbrev Box := Pt × Pt

/-- The join of two boxes: the smallest box holding both. -/
@[expose] public def Box.join (a b : Box) : Box :=
  ((min a.1.1 b.1.1, min a.1.2 b.1.2), (max a.2.1 b.2.1, max a.2.2 b.2.2))

/-- `a` is inside `b`, componentwise. -/
@[expose] public def Box.le (a b : Box) : Prop :=
  b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

public instance (a b : Box) : Decidable (Box.le a b) := by
  unfold Box.le
  infer_instance

-- The Box proofs state their arithmetic over bare `Int` binders because
-- `omega` does not see through the `Sp` abbreviation.

public theorem Box.le_refl (a : Box) : Box.le a a := by
  have h : ∀ x : Int, x ≤ x := fun _ => Int.le_refl _
  exact ⟨h _, h _, h _, h _⟩

public theorem Box.le_join_left (a b : Box) : Box.le a (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ x := by intro x y; omega
  have hmax : ∀ x y : Int, x ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_join_right (a b : Box) : Box.le b (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ y := by intro x y; omega
  have hmax : ∀ x y : Int, y ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_trans {a b c : Box} (h1 : Box.le a b) (h2 : Box.le b c) : Box.le a c := by
  have h : ∀ x y z : Int, x ≤ y → y ≤ z → x ≤ z := fun _ _ _ => Int.le_trans
  exact ⟨h _ _ _ h2.1 h1.1, h _ _ _ h2.2.1 h1.2.1,
         h _ _ _ h1.2.2.1 h2.2.2.1, h _ _ _ h1.2.2.2 h2.2.2.2⟩

/-- Joining with a box inside both sides' join stays inside it. -/
public theorem Box.join_le {a b c : Box} (ha : Box.le a c) (hb : Box.le b c) :
    Box.le (Box.join a b) c := by
  have hmin : ∀ x y z : Int, z ≤ x → z ≤ y → z ≤ min x y := by intro x y z; omega
  have hmax : ∀ x y z : Int, x ≤ z → y ≤ z → max x y ≤ z := by intro x y z; omega
  exact ⟨hmin _ _ _ ha.1 hb.1, hmin _ _ _ ha.2.1 hb.2.1,
    hmax _ _ _ ha.2.2.1 hb.2.2.1, hmax _ _ _ ha.2.2.2 hb.2.2.2⟩

/-- The hull fold over a list of boxes, `List` companion first. Polymorphic
in what it reads a box from, so one walk and one set of containment lemmas
serve every hull. -/
public def boxFoldList {α : Type} (f : α → Box) (acc : Box) : List α → Box
  | [] => acc
  | s :: rest => boxFoldList f (Box.join acc (f s)) rest

/-- The smallest box holding every box in an array. Empty is the empty box
at the origin. -/
@[expose] public def Box.hull (bs : Array Box) : Box :=
  match bs.toList with
  | [] => ((0, 0), (0, 0))
  | b :: rest => boxFoldList id b rest

public theorem boxFoldList_le {α : Type} (f : α → Box) (acc : Box) (xs : List α) :
    Box.le acc (boxFoldList f acc xs) := by
  induction xs generalizing acc with
  | nil => exact Box.le_refl acc
  | cons s rest ih =>
    exact Box.le_trans (Box.le_join_left acc (f s)) (ih (Box.join acc (f s)))

public theorem boxFoldList_mem {α : Type} (f : α → Box) (acc : Box) (xs : List α) (s : α)
    (h : s ∈ xs) : Box.le (f s) (boxFoldList f acc xs) := by
  induction xs generalizing acc with
  | nil => cases h
  | cons t rest ih =>
    cases h with
    | head =>
      exact Box.le_trans (Box.le_join_right acc (f s)) (boxFoldList_le _ _ rest)
    | tail _ hmem => exact ih (Box.join acc (f t)) hmem

/-- **The hull covers what it folds**: every box of the array lies inside
the hull. -/
public theorem Box.hull_covers (bs : Array Box) (b : Box) (h : b ∈ bs) :
    Box.le b (Box.hull bs) := by
  have h' : b ∈ bs.toList := by simpa using h
  unfold Box.hull
  split
  · next heq => rw [heq] at h'; cases h'
  · next t rest heq =>
    rw [heq] at h'
    cases h' with
    | head => exact boxFoldList_le _ _ rest
    | tail _ hmem => exact boxFoldList_mem _ _ rest b hmem

/-- An optional box joined with another: what a hull of possibly-absent
geometry folds. -/
@[expose] public def Box.joinOpt : Option Box → Option Box → Option Box
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Box.join a b)

/-- A box grown by `d` on every side. -/
@[expose] public def Box.dilate (b : Box) (d : Sp) : Box :=
  ((b.1.1 - d, b.1.2 - d), (b.2.1 + d, b.2.2 + d))

/-- The box of one point. -/
@[expose] public def Box.point (p : Pt) : Box := (p, p)

/-- `a` inside `b` where either may be absent: nothing is inside anything,
and something is never inside nothing. -/
@[expose] public def Box.leOpt : Option Box → Option Box → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => Box.le a b

/-! ## Transforms -/

/-- An affine map, `(x, y) ↦ (a·x + c·y + e, b·x + d·y + f)`: the entry
order of ISO 32000-2 §8.3.3 and SVG's `matrix()`. Exact rationals; the
translation is in the frame's `Sp`. -/
public structure Affine where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The identity map. -/
@[expose] public def Affine.unit : Affine := ⟨1, 0, 0, 1, 0, 0⟩

/-- `m` after `n`: the map `p ↦ m (n p)`. A PDF `cm` inside a frame `n`
leaves the frame `n.compose cm`; SVG's nested `transform` composes the same
way. -/
@[expose] public def Affine.compose (m n : Affine) : Affine :=
  { a := m.a * n.a + m.c * n.b, b := m.b * n.a + m.d * n.b
    c := m.a * n.c + m.c * n.d, d := m.b * n.c + m.d * n.d
    e := m.a * n.e + m.c * n.f + m.e, f := m.b * n.e + m.d * n.f + m.f }

/-- The map applied to a rational point. -/
@[expose] public def Affine.apply (m : Affine) (p : Rat × Rat) : Rat × Rat :=
  (m.a * p.1 + m.c * p.2 + m.e, m.b * p.1 + m.d * p.2 + m.f)

/-- A translation by whole `Sp`. -/
@[expose] public def Affine.translate (dx dy : Sp) : Affine := ⟨1, 0, 0, 1, dx, dy⟩

/-- A scaling about the origin. -/
@[expose] public def Affine.scale (sx sy : Rat) : Affine := ⟨sx, 0, 0, sy, 0, 0⟩

/-- The six operands both artifacts spell a matrix with — PDF's `cm` and
`/Matrix`, SVG's `matrix()`: the linear entries as they stand, the
translation from `Sp` to points, each through the one nine-decimal printer
(`Dim.ratString`). -/
public def Affine.operands (m : Affine) : String :=
  s!"{ratDecimal m.a} {ratDecimal m.b} {ratDecimal m.c} {ratDecimal m.d} \
{ratString m.e.num ((m.e.den : Int) * spPerPt)} {ratString m.f.num ((m.f.den : Int) * spPerPt)}"

/-- An integer isometry: `(x, y) ↦ (x + dx, dy − y)` when it flips, else
`(x + dx, y + dy)`. A page placement is one, so it is applied to coordinates
exactly and never spelled as a matrix. -/
public structure Iso where
  flipY : Bool
  dx : Sp
  dy : Sp
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Iso.apply (t : Iso) (p : Pt) : Pt :=
  (p.1 + t.dx, if t.flipY then t.dy - p.2 else p.2 + t.dy)

/-- The inverse isometry. -/
@[expose] public def Iso.inv (t : Iso) : Iso :=
  if t.flipY then { flipY := true, dx := -t.dx, dy := t.dy }
  else { flipY := false, dx := -t.dx, dy := -t.dy }

/-- `s` after `t`. -/
@[expose] public def Iso.compose (s t : Iso) : Iso :=
  { flipY := s.flipY != t.flipY, dx := t.dx + s.dx
    dy := if s.flipY then s.dy - t.dy else t.dy + s.dy }

/-- The isometry as an exact matrix. -/
@[expose] public def Iso.toAffine (t : Iso) : Affine :=
  ⟨1, 0, 0, if t.flipY then -1 else 1, t.dx, t.dy⟩

/-- The inverse undoes the isometry on every point. -/
public theorem Iso.inv_apply_id (t : Iso) (p : Pt) : t.inv.apply (t.apply p) = p := by
  obtain ⟨fl, dx, dy⟩ := t
  obtain ⟨x, y⟩ := p
  have hx : ∀ a b : Int, a + b + -b = a := by intro a b; omega
  have hy : ∀ a b : Int, b - (b - a) = a := by intro a b; omega
  cases fl
  · simp only [Iso.inv, Iso.apply, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;>
      exact ⟨hx x dx, hx y dy⟩
  · simp only [Iso.inv, Iso.apply, ↓reduceIte, Prod.mk.injEq] <;> exact ⟨hx x dx, hy y dy⟩

/-- The isometry undoes its inverse. -/
public theorem Iso.apply_inv_id (t : Iso) (p : Pt) : t.apply (t.inv.apply p) = p := by
  obtain ⟨fl, dx, dy⟩ := t
  obtain ⟨x, y⟩ := p
  have hx : ∀ a b : Int, a + -b + b = a := by intro a b; omega
  have hy : ∀ a b : Int, b - (b - a) = a := by intro a b; omega
  cases fl
  · simp only [Iso.inv, Iso.apply, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;>
      exact ⟨hx x dx, hx y dy⟩
  · simp only [Iso.inv, Iso.apply, ↓reduceIte, Prod.mk.injEq] <;> exact ⟨hx x dx, hy y dy⟩

/-- An axis-aligned rectangle (min corner, extents) carried by the isometry:
the image's min corner, extents unchanged. -/
@[expose] public def Iso.rect (t : Iso) (x y w h : Sp) : Sp × Sp × Sp × Sp :=
  (x + t.dx, if t.flipY then t.dy - (y + h) else y + t.dy, w, h)

/-- A box carried by the isometry: its image's min and max corners. -/
@[expose] public def Iso.box (t : Iso) (b : Box) : Box :=
  if t.flipY then ((b.1.1 + t.dx, t.dy - b.2.2), (b.2.1 + t.dx, t.dy - b.1.2))
  else ((b.1.1 + t.dx, b.1.2 + t.dy), (b.2.1 + t.dx, b.2.2 + t.dy))

/-! ## Geometry -/

/-- One segment, from the current point: a line, or a cubic Bézier with
its two control points. -/
public inductive Seg where
  | line (p : Pt)
  | cubic (c1 c2 p : Pt)
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Seg.endPt : Seg → Pt
  | .line p => p
  | .cubic _ _ p => p

/-- A subpath: a start point, its segments, and whether it closes. -/
public structure Subpath where
  start : Pt
  segs : Array Seg
  closed : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Where a subpath's pen stands after its last segment. -/
@[expose] public def Subpath.endPt (s : Subpath) : Pt :=
  (s.segs.back?.map Seg.endPt).getD s.start

/-- A draw's geometry: an axis-aligned rectangle (min corner, extents), an
axis-aligned ellipse (centre, radii), or a path. -/
public inductive Geom where
  | rect (x y w h : Sp)
  | ellipse (cx cy rx ry : Sp)
  | path (subs : Array Subpath)
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Rule where
  | nonzero
  | evenOdd
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Cap where
  | butt
  | round
  | square
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Join where
  | miter
  | round
  | bevel
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Opacity in thousandths. -/
public abbrev Alpha := Fin 1001

@[expose] public def Alpha.opaque : Alpha := ⟨1000, by decide⟩

/-- A gradient stop: its offset in 65536ths, its opaque colour. -/
public structure Stop where
  offset : Fin 65537
  color : Ir.Color
  deriving Repr, Inhabited, DecidableEq

/-- Exact stop equality: the colour's PDF rider included. -/
public instance : BEq Stop where
  beq a b := a.offset == b.offset && a.color.r == b.color.r && a.color.g == b.color.g &&
    a.color.b == b.color.b && a.color.cmyk == b.color.cmyk

/-- A gradient with pad spread, interpolated in sRGB-encoded components
(SVG's default `color-interpolation`, PDF Type 2 functions over DeviceRGB).
`xf` maps the gradient's own frame into the node's. A radial gradient's
start circle lies inside its end circle. -/
public inductive Gradient where
  | linear (p0 p1 : Pt) (stops : Array Stop) (xf : Affine)
  | radial (c0 : Pt) (r0 : Sp) (c1 : Pt) (r1 : Sp) (stops : Array Stop) (xf : Affine)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The map from a gradient's own frame into the frame of what it paints. -/
@[expose] public def Gradient.xf : Gradient → Affine
  | .linear _ _ _ xf => xf
  | .radial _ _ _ _ _ xf => xf

/-- A gradient with its frame map replaced, its points and stops kept. -/
@[expose] public def Gradient.withXf (g : Gradient) (m : Affine) : Gradient :=
  match g with
  | .linear p0 p1 stops _ => .linear p0 p1 stops m
  | .radial c0 r0 c1 r1 stops _ => .radial c0 r0 c1 r1 stops m

@[simp] public theorem Gradient.xf_withXf (g : Gradient) (m : Affine) : (g.withXf m).xf = m := by
  cases g <;> rfl

@[simp] public theorem Gradient.withXf_withXf (g : Gradient) (a b : Affine) :
    (g.withXf a).withXf b = g.withXf b := by
  cases g <;> rfl

public inductive Paint where
  | solid (c : Ir.Color)
  | gradient (g : Gradient)
  deriving Repr, BEq, Inhabited

public structure Fill where
  paint : Paint
  rule : Rule
  alpha : Alpha
  deriving Repr, BEq, Inhabited

/-- How a draw strokes. Every field is stated: PDF starts at miter limit 10
and SVG at 4, so a producer says which it means. -/
public structure Stroke where
  paint : Paint
  width : Sp
  cap : Cap
  join : Join
  miterLimit : Rat
  dash : Array Sp
  phase : Sp
  alpha : Alpha
  deriving Repr, BEq, Inhabited

/-- A paint as seen from a frame that `m` maps into the one it was stated
in: a gradient's own frame composed through `m`, a colour as it is. -/
@[expose] public def Paint.under (m : Affine) : Paint → Paint
  | .solid c => .solid c
  | .gradient g => .gradient (g.withXf (m.compose g.xf))

@[expose] public def Fill.under (m : Affine) (f : Fill) : Fill := { f with paint := f.paint.under m }

@[expose] public def Stroke.under (m : Affine) (s : Stroke) : Stroke :=
  { s with paint := s.paint.under m }

public structure Clip where
  geom : Geom
  rule : Rule
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The faces an SVG run asks for, in CSS order; generic families lower
case. -/
public structure FaceReq where
  families : Array String
  weight : Nat
  italic : Bool
  deriving Repr, BEq, Inhabited

public inductive Anchor where
  | start
  | middle
  | «end»
  deriving Repr, BEq, DecidableEq, Inhabited

/-- SVG text, shaped by the engine. `xf` places the run's baseline origin. -/
public structure Run where
  xf : Affine
  size : Sp
  text : String
  face : FaceReq
  anchor : Anchor
  fill : Option Fill
  stroke : Option Stroke
  lang : Option String
  deriving Repr, Inhabited

/-- A run after shaping: a face of the document's `FontSet`, glyph ids with
their pen x, the resolved start already folded into `xf`. -/
public structure Shaped where
  face : Nat
  size : Sp
  xf : Affine
  glyphs : Array (Nat × Sp)
  text : String
  fill : Option Fill
  stroke : Option Stroke
  deriving Repr, Inhabited

/-- A raster's encoded bytes (PNG, or JPEG when `jpeg`), its pixel size,
and whether a reader may smooth its samples when it scales them — SVG's
`image-rendering: auto` and PDF's `/Interpolate true`; otherwise each
sample paints its own square, the two formats' other default, and the
only reading two renderers agree on pixel for pixel. -/
public structure Raster where
  bytes : ByteArray
  jpeg : Bool
  pxW : Nat
  pxH : Nat
  smooth : Bool
  deriving Inhabited

public instance : Repr Raster where
  reprPrec r _ := s!"Raster({r.bytes.size} bytes, {r.pxW}x{r.pxH})"

/-- One node of a figure. `use` paints a symbol under a transform; `stamp`
paints a paint-less outline with the instance's paints (a glyph, a Type 3
procedure, an unpainted SVG definition); `image` maps a raster's unit
square into the parent frame, its (0,0) the image's bottom-left; `label` is
engine-set text; `words` paints nothing and carries recovered text. -/
public inductive Node (L : Type) where
  | draw (g : Geom) (fill : Option Fill) (stroke : Option Stroke)
  | group (xf : Affine) (clips : Array Clip) (alpha : Alpha) (kids : Array (Node L))
  | use (sym : Nat) (xf : Affine)
  | stamp (outline : Nat) (xf : Affine) (fill : Option Fill) (stroke : Option Stroke)
  | image (raster : Nat) (xf : Affine)
  | label (l : L)
  | words (s : String)
  deriving Repr, Inhabited

/-- What an importer met and could not give this meaning, keyed by feature. -/
public inductive Loss where
  | element (n : String)
  | attribute (n : String)
  | property (n : String)
  | value (n : String)
  | operator (n : String)
  | resource (n : String)
  | font (kind : String)
  | budget (what : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A figure. `box` is the extent layout reserves; `clipToBox` says whether
the box clips (an SVG viewport, a PDF BBox — never a TikZ picture, pgf
§15.8). A `use` inside symbol `j` names some `k < j`. An empty `losses`
is what native means. -/
public structure Figure (L : Type) where
  box : Box
  clipToBox : Bool
  nodes : Array (Node L)
  outlines : Array (Array Subpath)
  symbols : Array (Array (Node L))
  rasters : Array Raster
  title : Option String
  losses : Array Loss
  deriving Repr, Inhabited

/-! ## The kit every producer shares -/

namespace Trig

/-- One radian in 2⁻³⁰ units is `2^30`; angles below are in those units. -/
public def unit : Int := 1073741824

/-- π·2³⁰, rounded. -/
public def pi : Int := 3373259426

/-- atan(2⁻ⁱ)·2³⁰, rounded, i = 0…30 (`scripts/trig-oracle.lean` recomputes
them). -/
public def atanTable : Array Int := #[
  843314857, 497837829, 263043837, 133525159, 67021687, 33543516, 16775851,
  8388437, 4194283, 2097149, 1048576, 524288, 262144, 131072, 65536, 32768,
  16384, 8192, 4096, 2048, 1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1]

/-- The CORDIC gain ∏ 1/√(1 + 2⁻²ⁱ) over the table, ·2³⁰, rounded. -/
public def gain : Int := 652032874

/-- `x >> i` with floor rounding. -/
private def shr (x : Int) (i : Nat) : Int := x / (2 ^ i : Nat)

/-- Rotation-mode CORDIC from `(x, y)` through angle `z`, |z| ≤ π/2. -/
private def rotate (x y z : Int) : Int × Int := Id.run do
  let mut x := x
  let mut y := y
  let mut z := z
  for h : i in [0:atanTable.size] do
    let t := atanTable[i]
    if 0 ≤ z then
      let x' := x - shr y i
      y := y + shr x i
      x := x'
      z := z - t
    else
      let x' := x + shr y i
      y := y - shr x i
      x := x'
      z := z + t
  return (x, y)

/-- `(cos θ, sin θ)` at 2⁻³⁰, for any angle in 2⁻³⁰ radians. The angle is
reduced to (−π, π], then a half-turn folds it into the rotation's range;
the four axis directions are exact, so an axis-aligned arc's chord is read
without the rotation's rounding (`scripts/trig-oracle.lean` bounds the
rest). -/
public def cosSin (θ : Int) : Int × Int :=
  let twoPi := 2 * pi
  let r := θ % twoPi
  let r := if r > pi then r - twoPi else r
  let half := pi / 2
  if r = 0 then (unit, 0)
  else if r = half then (0, unit)
  else if r = -half then (0, -unit)
  else if r = pi then (-unit, 0)
  else if r > half then
    let (c, s) := rotate gain 0 (r - pi)
    (-c, -s)
  else if r < -half then
    let (c, s) := rotate gain 0 (r + pi)
    (-c, -s)
  else rotate gain 0 r

/-- Vectoring-mode CORDIC: the angle of `(x, y)` with `x > 0`. -/
private def vector (x y : Int) : Int := Id.run do
  let mut x := x
  let mut y := y
  let mut z : Int := 0
  for h : i in [0:atanTable.size] do
    let t := atanTable[i]
    if y < 0 then
      let x' := x - shr y i
      y := y + shr x i
      x := x'
      z := z - t
    else
      let x' := x + shr y i
      y := y - shr x i
      x := x'
      z := z + t
  return z

/-- A vector scaled by a power of two until its larger coordinate stands in
`[2³⁰, 2³¹)`: its angle is unchanged, and a short vector's floored shifts
would otherwise steer the rotation by the vector's own coarseness
(`scripts/trig-oracle.lean` measured 0.2° at magnitude 2¹⁰). -/
private def lift (x y : Int) : Int × Int :=
  let m := max x.natAbs y.natAbs
  if m == 0 || m ≥ 2 ^ 30 then (x, y) else
  let k := 30 - m.log2
  (x * ((2 ^ k : Nat) : Int), y * ((2 ^ k : Nat) : Int))

/-- `atan2 y x` in 2⁻³⁰ radians, in (−π, π]; `atan2 0 0 = 0`. -/
public def atan2 (y0 x0 : Int) : Int :=
  let v := lift x0 y0
  let x := v.1
  let y := v.2
  if x > 0 then vector x y
  else if x < 0 then
    if 0 ≤ y then vector (-x) (-y) + pi else vector (-x) (-y) - pi
  else if y > 0 then pi / 2
  else if y < 0 then -(pi / 2)
  else 0

/-- `⌊√n⌋`. -/
public def isqrt (n : Nat) : Nat := n.sqrt

/-- `n / d` rounded to the nearest integer, half away from zero (`d > 0`). -/
public def divRound (n d : Int) : Int :=
  if n < 0 then -((-n + d / 2) / d) else (n + d / 2) / d

end Trig

namespace Kit

/-- The quarter-arc control distance, as a fraction of the radius: the
standard 4(√2 − 1)/3 ≈ 0.5523 that pgf and today's PDF circle spell
(`k = r·5523/10000`). -/
public def kappaNum : Int := 5523
public def kappaDen : Int := 10000

/-- An axis-aligned ellipse as four cubic quarter arcs, counter-clockwise
in a y-up frame from angle 0, closed: today's PDF circle, point for point. -/
@[expose] public def ellipse (cx cy rx ry : Sp) : Array Subpath :=
  let kx := rx * kappaNum / kappaDen
  let ky := ry * kappaNum / kappaDen
  #[{ start := (cx + rx, cy)
      segs := #[.cubic (cx + rx, cy + ky) (cx + kx, cy + ry) (cx, cy + ry),
                .cubic (cx - kx, cy + ry) (cx - rx, cy + ky) (cx - rx, cy),
                .cubic (cx - rx, cy - ky) (cx - kx, cy - ry) (cx, cy - ry),
                .cubic (cx + kx, cy - ry) (cx + rx, cy - ky) (cx + rx, cy)]
      closed := true }]

/-- A rectangle's outline, ISO 32000-2 §8.5.2.1's `re`: from its min
corner along the bottom edge, counter-clockwise in a y-up frame. -/
@[expose] public def rectPath (x y w h : Sp) : Subpath :=
  { start := (x, y), segs := #[.line (x + w, y), .line (x + w, y + h), .line (x, y + h)]
    closed := true }

/-- `p · num / den`, rounded to the nearest `Sp`, half away from zero. -/
private def mulRound (p num den : Int) : Int :=
  let n := p * num
  if n < 0 then -((-n + den / 2) / den) else (n + den / 2) / den

/-- A rounded rectangle, SVG 2 §10.2's `rect` with its radii clamped to half
the extents; quarter corners use the ellipse's control distance. -/
public def roundedRect (x y w h rx ry : Sp) : Subpath :=
  let rx := max 0 (min rx (w / 2))
  let ry := max 0 (min ry (h / 2))
  if rx == 0 || ry == 0 then rectPath x y w h else
  let kx := mulRound rx kappaNum kappaDen
  let ky := mulRound ry kappaNum kappaDen
  let r := x + w
  let t := y + h
  { start := (x + rx, y)
    segs := #[.line (r - rx, y),
      .cubic (r - rx + kx, y) (r, y + ry - ky) (r, y + ry),
      .line (r, t - ry),
      .cubic (r, t - ry + ky) (r - rx + kx, t) (r - rx, t),
      .line (x + rx, t),
      .cubic (x + rx - kx, t) (x, t - ry + ky) (x, t - ry),
      .line (x, y + ry),
      .cubic (x, y + ry - ky) (x + rx - kx, y) (x + rx, y)]
    closed := true }

/-- A quadratic Bézier elevated to the cubic that draws it: controls two
thirds of the way from each end to the quadratic's control, rounded to the
grid (within one unit of the exact elevation). -/
public def quadToCubic (p0 q p1 : Pt) : Seg :=
  .cubic (p0.1 + mulRound (q.1 - p0.1) 2 3, p0.2 + mulRound (q.2 - p0.2) 2 3)
    (p1.1 + mulRound (q.1 - p1.1) 2 3, p1.2 + mulRound (q.2 - p1.2) 2 3) p1

/-- A dash array as both formats read it: an odd SVG list is doubled, and a
list with no positive entry or a negative one draws solid. -/
public def normDash (d : Array Sp) : Array Sp :=
  if d.any (· < 0) || !d.any (0 < ·) then #[]
  else if d.size % 2 == 1 then d ++ (d) else d

/-- A point at angle θ (2⁻³⁰ rad) on the axis-aligned ellipse of radii
`(rx, ry)` about `(cx, cy)`, the ellipse turned by `(cφ, sφ)` — centre and
radii at `1/sc` of an `Sp`, the point rounded once, to the `Sp`. -/
private def onEllipse (cx cy sc rx ry cφ sφ θ : Int) : Pt :=
  let (c, s) := Trig.cosSin θ
  let u := rx * c
  let v := ry * s
  let uu := Trig.unit * Trig.unit
  (Trig.divRound (cx * uu + (u * cφ - v * sφ)) (uu * sc),
   Trig.divRound (cy * uu + (u * sφ + v * cφ)) (uu * sc))

/-- The tangent direction at θ, scaled by `k` (2⁻³⁰): what a piece's
control point stands off its end by — radii at `1/sc` of an `Sp`, the
offset rounded once, to the `Sp`. -/
private def tangent (sc rx ry cφ sφ θ k : Int) : Int × Int :=
  let (c, s) := Trig.cosSin θ
  let u := -(rx * s)
  let v := ry * c
  let u3 := Trig.unit * Trig.unit * Trig.unit * sc
  (Trig.divRound ((u * cφ - v * sφ) * k) u3, Trig.divRound ((u * sφ + v * cφ) * k) u3)

/-- The control distance of a piece through `δ` (2⁻³⁰ rad): 4/3·tan(δ/4),
at 2⁻³⁰. -/
private def pieceK (δ : Int) : Int :=
  let cs := Trig.cosSin (δ / 4)
  if cs.1 ≤ 0 then 0 else Trig.divRound (4 * cs.2 * Trig.unit) (3 * cs.1)

/-- The pieces of an arc before its last, `n − 1` of them through `δ` each
from `θ0`, and the angle the last starts at. -/
private def arcHead (cx cy sc rx ry cφ sφ θ0 δ k : Int) (n : Nat) : Array Seg × Int := Id.run do
  let mut out : Array Seg := #[]
  let mut θ := θ0
  for _ in [0:n - 1] do
    let p0 := onEllipse cx cy sc rx ry cφ sφ θ
    let p1 := onEllipse cx cy sc rx ry cφ sφ (θ + δ)
    let t0 := tangent sc rx ry cφ sφ θ k
    let t1 := tangent sc rx ry cφ sφ (θ + δ) k
    out := out.push (.cubic (p0.1 + t0.1, p0.2 + t0.2) (p1.1 - t1.1, p1.2 - t1.2) p1)
    θ := θ + δ
  return (out, θ)

/-- An arc's last piece, from `θ` to `θ0 + Δ`, ending on `last`. -/
private def arcLast (cx cy sc rx ry cφ sφ θ0 Δ θ : Int) (last : Pt) : Seg :=
  let p0 := onEllipse cx cy sc rx ry cφ sφ θ
  let kl := pieceK (θ0 + Δ - θ)
  let t0 := tangent sc rx ry cφ sφ θ kl
  let t1 := tangent sc rx ry cφ sφ (θ0 + Δ) kl
  .cubic (p0.1 + t0.1, p0.2 + t0.2) (last.1 - t1.1, last.2 - t1.2) last

/-- `arcCubics` with the centre and radii at `1/sc` of an `Sp`: what the
endpoint conversion hands it, so its centre is not rounded before the
pieces are. -/
private def arcCubicsAt (cx cy sc rx ry φ θ0 Δ : Int) (last : Pt) : Array Seg :=
  let quarter := Trig.pi / 2
  let n : Nat := max 1 ((Δ.natAbs + quarter.natAbs - 1) / quarter.natAbs)
  let δ := Δ / (n : Int)
  let csφ := Trig.cosSin φ
  let head := arcHead cx cy sc rx ry csφ.1 csφ.2 θ0 δ (pieceK δ) n
  head.1.push (arcLast cx cy sc rx ry csφ.1 csφ.2 θ0 Δ head.2 last)

/-- The cubic pieces of an elliptic arc from angle `θ0` through `Δ` (2⁻³⁰
rad), in at most quarter turns, each with the control distance
4/3·tan(δ/4); the ellipse turned by `φ`. The last piece ends exactly on
`last` — the declared endpoint — whatever the trigonometry rounds, so a
path continuing from it never opens a gap (`arcCubics_exact`). -/
public def arcCubics (cx cy rx ry φ θ0 Δ : Int) (last : Pt) : Array Seg :=
  arcCubicsAt cx cy 1 rx ry φ θ0 Δ last

/-- **An arc ends exactly where it was declared to** (`_exact`): its last
piece's end is `last`, whatever the trigonometry rounded on the way, so the
path continuing from it opens no gap. -/
public theorem arcCubics_exact (cx cy rx ry φ θ0 Δ : Int) (last : Pt) :
    (arcCubics cx cy rx ry φ θ0 Δ last).back?.map Seg.endPt = some last := by
  simp only [arcCubics, arcCubicsAt, Array.back?_push, Option.map_some]
  rfl

/-- The resolution the endpoint conversion works at: 2⁻¹⁶ of an `Sp`, so
the half-chord, the centre and the scaled radii are not rounded to the
`Sp` before the centre is — near a half-ellipse the centre moves far for a
small change of the half-chord (`scripts/trig-oracle.lean` measures it). -/
private def arcScale : Int := 65536

/-- An arc in SVG's endpoint parameterization (SVG 2 §9.5, Appendix B.2.4:
`p1` to `p2`, radii, x-axis rotation φ in 2⁻³⁰ rad, the two flags),
converted to the centre form and drawn by `arcCubics`. Radii too small to
reach are scaled up as B.2.5 says, which puts the centre at the chord's
midpoint — set there, not recomputed from rounded radii; a zero radius is a
line; coincident ends draw nothing. -/
public def arcEndpoint (p1 : Pt) (rx ry φ : Int) (large sweep : Bool) (p2 : Pt) : Array Seg :=
  if p1 == p2 then #[] else
  if rx == 0 || ry == 0 then #[.line p2] else
  let u := Trig.unit
  let sc := arcScale
  let (cφ, sφ) := Trig.cosSin φ
  let dx := p1.1 - p2.1
  let dy := p1.2 - p2.2
  let x1 := Trig.divRound ((cφ * dx + sφ * dy) * sc) (2 * u)
  let y1 := Trig.divRound ((cφ * dy - sφ * dx) * sc) (2 * u)
  let rx0 : Int := (rx.natAbs : Int) * sc
  let ry0 : Int := (ry.natAbs : Int) * sc
  let lamNum := x1 * x1 * (ry0 * ry0) + y1 * y1 * (rx0 * rx0)
  let lamDen := rx0 * rx0 * (ry0 * ry0)
  let scaled := lamNum > lamDen
  let (rx, ry) := if scaled then
      let s : Int := Trig.isqrt (lamNum * u * u / lamDen).toNat + 1
      (rx0 * s / u + 1, ry0 * s / u + 1)
    else (rx0, ry0)
  let rx2 := rx * rx
  let ry2 := ry * ry
  let numer := rx2 * ry2 - rx2 * (y1 * y1) - ry2 * (x1 * x1)
  let denom := rx2 * (y1 * y1) + ry2 * (x1 * x1)
  let coef : Int := if scaled || denom == 0 || numer ≤ 0 then 0
    else Trig.isqrt (numer * u * u / denom).toNat
  let coef := if large == sweep then -coef else coef
  let cx1 := Trig.divRound (coef * rx * y1) (ry * u)
  let cy1 := -(Trig.divRound (coef * ry * x1) (rx * u))
  let cx := Trig.divRound (cφ * cx1 - sφ * cy1) u + (p1.1 + p2.1) * sc / 2
  let cy := Trig.divRound (sφ * cx1 + cφ * cy1) u + (p1.2 + p2.2) * sc / 2
  let θ1 := Trig.atan2 ((y1 - cy1) * rx) ((x1 - cx1) * ry)
  let θ2 := Trig.atan2 ((-y1 - cy1) * rx) ((-x1 - cx1) * ry)
  let Δ := θ2 - θ1
  let Δ := if !sweep && Δ > 0 then Δ - 2 * Trig.pi
    else if sweep && Δ < 0 then Δ + 2 * Trig.pi else Δ
  arcCubicsAt cx cy sc rx ry φ θ1 Δ p2

/-- A regular polygon's vertices, the first at angle `θ0` (2⁻³⁰ rad). -/
public def regularPolygon (cx cy r : Sp) (n : Nat) (θ0 : Int) : Subpath :=
  let n := max 3 n
  let vertex (k : Nat) : Pt :=
    let (c, s) := Trig.cosSin (θ0 + 2 * Trig.pi * (k : Int) / (n : Int))
    (cx + Trig.divRound (r * c) Trig.unit, cy + Trig.divRound (r * s) Trig.unit)
  { start := vertex 0, segs := (Array.range (n - 1)).map fun k => .line (vertex (k + 1))
    closed := true }

end Kit

/-! ## Reading a figure: its marks -/

/-- A geometry as both artifacts' readers meet it: an ellipse is the four
arcs both formats paint (`Kit.ellipse`); a rectangle and a path are
themselves. -/
@[expose] public def Geom.normal : Geom → Geom
  | .rect x y w h => .rect x y w h
  | .ellipse cx cy rx ry => .path (Kit.ellipse cx cy rx ry)
  | .path subs => .path subs

/-- A segment's points mapped. -/
@[expose] public def Seg.map (f : Pt → Pt) : Seg → Seg
  | .line p => .line (f p)
  | .cubic c1 c2 p => .cubic (f c1) (f c2) (f p)

@[expose] public def Subpath.map (f : Pt → Pt) (s : Subpath) : Subpath :=
  { s with start := f s.start, segs := s.segs.map (Seg.map f) }

/-- A geometry carried by an isometry: a rectangle's min corner by
`Iso.rect`, an ellipse's centre, a path's every point. -/
@[expose] public def Geom.mapIso (t : Iso) : Geom → Geom
  | .rect x y w h =>
    let (x', y', w', h') := t.rect x y w h
    .rect x' y' w' h'
  | .ellipse cx cy rx ry =>
    let (cx', cy') := t.apply (cx, cy)
    .ellipse cx' cy' rx ry
  | .path subs => .path (subs.map (Subpath.map t.apply))

/-- One ink mark as a reader of either artifact meets it, in the figure's
frame: the frame it paints in (`ctm`, child to figure), its geometry in that
frame (`Geom.normal`), its paints — widths and dashes in that frame, every
gradient's own frame composed through to the figure's (`Paint.under`), the
one frame a reader recovers it in from either artifact: PDF states a
pattern's matrix against its stream's default space (ISO 32000-2 §8.7.2),
SVG a gradient's against the user space of the element it paints (SVG 2
§14.2.2) — the clips in force, each with the frame it was declared in, and
the alphas of the isolated groups around it, outermost first. A shading
paints its gradient, its frame the figure's, over the clips in force.
Labels and words are not ink. -/
public inductive Mark where
  | paint (ctm : Affine) (geom : Geom) (fill : Option Fill) (stroke : Option Stroke)
      (clips : Array (Affine × Clip)) (alphas : Array Alpha)
  | raster (ctm : Affine) (raster : Nat) (clips : Array (Affine × Clip)) (alphas : Array Alpha)
  | shading (g : Gradient) (clips : Array (Affine × Clip)) (alphas : Array Alpha)
  deriving Repr, BEq, Inhabited

/-- The reading context a walk carries: the frame, the clips, the group
alphas. -/
public structure Ctx where
  ctm : Affine
  clips : Array (Affine × Clip)
  alphas : Array Alpha
  deriving Repr, BEq, Inhabited

@[expose] public def Ctx.root : Ctx := { ctm := Affine.unit, clips := #[], alphas := #[] }

/-- Entering a group: its frame composes, its clips join in its child
frame, an alpha below 1000 is one more isolated group. -/
@[expose] public def Ctx.enter (cx : Ctx) (xf : Affine) (clips : Array Clip) (alpha : Alpha) :
    Ctx :=
  let ctm := cx.ctm.compose xf
  { ctm := ctm
    clips := cx.clips ++ clips.map fun c => (ctm, { c with geom := c.geom.normal })
    alphas := if alpha == Alpha.opaque then cx.alphas else cx.alphas.push alpha }

mutual

-- conserves: none — a reading, not a rewrite: what it owes is each
-- artifact's reading of it (`GfxPdf.marks_projects`, `GfxSvg.marks_projects`).
/-- One node's marks onto `acc`, under `cx`, over an expanded tree
(`Figure.expanded`): its uses are already the groups they paint, so the walk
stays structural and a `use` left in it paints nothing. -/
@[expose] public def Node.marksOne {L : Type} (outlines : Array (Array Subpath)) (cx : Ctx)
    (acc : Array Mark) : Node L → Array Mark
  | .draw g fl st =>
    acc.push (.paint cx.ctm g.normal (fl.map (Fill.under cx.ctm)) (st.map (Stroke.under cx.ctm))
      cx.clips cx.alphas)
  | .group xf clips alpha kids => Node.marksList outlines (cx.enter xf clips alpha) acc kids.toList
  | .use _ _ => acc
  | .stamp o xf fl st =>
    let m := cx.ctm.compose xf
    acc.push (.paint m (.path (outlines[o]?.getD #[])) (fl.map (Fill.under m))
      (st.map (Stroke.under m)) cx.clips cx.alphas)
  | .image k xf => acc.push (.raster (cx.ctm.compose xf) k cx.clips cx.alphas)
  | .label _ => acc
  | .words _ => acc

@[expose] public def Node.marksList {L : Type} (outlines : Array (Array Subpath)) (cx : Ctx)
    (acc : Array Mark) : List (Node L) → Array Mark
  | [] => acc
  | n :: rest => Node.marksList outlines cx (Node.marksOne outlines cx acc n) rest

end

mutual

-- conserves: none — expansion keeps what a use paints and says; the marks
-- and words read from it are its census (`Figure.marks`, `Figure.said_text`).
/-- A node with every `use k` whose `k < bound` replaced by its expanded
body under the use's frame, and every other use dropped (`wf` refuses
them). Used to read symbol bodies in order. -/
@[expose] public def Node.expandOne {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (acc : Array (Node L)) : Node L → Array (Node L)
  | .draw g fl st => acc.push (.draw g fl st)
  | .group xf clips alpha kids =>
    acc.push (.group xf clips alpha (Node.expandList done bound #[] kids.toList))
  | .use k xf =>
    if k < bound then
      match done[k]? with
      | some body => acc.push (.group xf #[] Alpha.opaque body)
      | none => acc
    else acc
  | .stamp o xf fl st => acc.push (.stamp o xf fl st)
  | .image k xf => acc.push (.image k xf)
  | .label l => acc.push (.label l)
  | .words s => acc.push (.words s)

@[expose] public def Node.expandList {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (acc : Array (Node L)) : List (Node L) → Array (Node L)
  | [] => acc
  | n :: rest => Node.expandList done bound (Node.expandOne done bound acc n) rest

end

mutual

-- conserves: none — a predicate.
/-- Whether a tree holds no `use`: what an expanded body is. -/
@[expose] public def Node.useFree {L : Type} : Node L → Bool
  | .draw _ _ _ => true
  | .group _ _ _ kids => Node.useFreeList kids.toList
  | .use _ _ => false
  | .stamp _ _ _ _ => true
  | .image _ _ => true
  | .label _ => true
  | .words _ => true

@[expose] public def Node.useFreeList {L : Type} : List (Node L) → Bool
  | [] => true
  | n :: rest => Node.useFree n && Node.useFreeList rest

end

/-- The symbol bodies with their uses expanded, in symbol order: body `j`
reads only bodies `k < j`, so the expansion is a fold and needs no fuel. -/
@[expose] public def Figure.bodies {L : Type} (fig : Figure L) : Array (Array (Node L)) :=
  fig.symbols.foldl (fun done sym => done.push (Node.expandList done done.size #[] sym.toList))
    #[]

/-- The figure's nodes with every use replaced by the group it paints. -/
@[expose] public def Figure.expanded {L : Type} (fig : Figure L) : Array (Node L) :=
  Node.expandList fig.bodies fig.bodies.size #[] fig.nodes.toList

/-- **What a figure paints**, in painter's order: the reading both
artifacts' readers must reproduce (`GfxPdf.marks_projects`,
`GfxSvg.marks_projects`). -/
@[expose] public def Figure.marks {L : Type} (fig : Figure L) : Array Mark :=
  Node.marksList fig.outlines Ctx.root #[] fig.expanded.toList

/-! ## Boxes -/

/-- The least box of whole `Sp` holding an affine image of a box: the
image's extremes are at the corners' images (the map is linear in each axis),
rounded outward (`Affine.boxImage_covers`). -/
@[expose] public def Box.image (m : Affine) (b : Box) : Box :=
  let x0 : Rat := b.1.1
  let y0 : Rat := b.1.2
  let x1 : Rat := b.2.1
  let y1 : Rat := b.2.2
  let fx (x y : Rat) : Rat := m.a * x + m.c * y + m.e
  let fy (x y : Rat) : Rat := m.b * x + m.d * y + m.f
  ((Rat.floor (min (min (fx x0 y0) (fx x1 y0)) (min (fx x0 y1) (fx x1 y1))),
    Rat.floor (min (min (fy x0 y0) (fy x1 y0)) (min (fy x0 y1) (fy x1 y1)))),
   (Rat.ceil (max (max (fx x0 y0) (fx x1 y0)) (max (fx x0 y1) (fx x1 y1))),
    Rat.ceil (max (max (fy x0 y0) (fy x1 y0)) (max (fy x0 y1) (fy x1 y1)))))

/-- The hull of a list of points onto `acc`. -/
@[expose] public def ptsHull (acc : Option Box) : List Pt → Option Box
  | [] => acc
  | p :: rest => ptsHull (Box.joinOpt acc (some (Box.point p))) rest

/-- A segment's points, controls included. -/
@[expose] public def Seg.points : Seg → List Pt
  | .line p => [p]
  | .cubic c1 c2 p => [c1, c2, p]

/-- A subpath's points, controls included. -/
@[expose] public def Subpath.points (s : Subpath) : List Pt :=
  s.start :: s.segs.toList.flatMap Seg.points

/-- A geometry's control hull in its own frame: a cubic lies in the convex
hull of its control points, so this bounds what it draws. `none` for a
path with no points. -/
@[expose] public def Geom.hull : Geom → Option Box
  | .rect x y w h => some ((min x (x + w), min y (y + h)), (max x (x + w), max y (y + h)))
  | .ellipse cx cy rx ry =>
    some ((min (cx - rx) (cx + rx), min (cy - ry) (cy + ry)),
      (max (cx - rx) (cx + rx), max (cy - ry) (cy + ry)))
  | .path subs => ptsHull none (subs.toList.flatMap Subpath.points)

/-- The point at `t` of the cubic Bézier from `p0` through controls `c1`
and `c2` to `p1`, exactly, in Bernstein form: what `Geom.hull` bounds
(`cubicAt_between`). -/
@[expose] public def cubicAt (p0 c1 c2 p1 : Pt) (t : Rat) : Rat × Rat :=
  let s := 1 - t
  let w0 := s * s * s
  let w1 := 3 * s * s * t
  let w2 := 3 * s * t * t
  let w3 := t * t * t
  (w0 * p0.1 + w1 * c1.1 + w2 * c2.1 + w3 * p1.1, w0 * p0.2 + w1 * c1.2 + w2 * c2.2 + w3 * p1.2)

/-- How far a stroke's paint reaches past its path, in the path's frame:
half the width, times the miter limit for miter joins and 3/2 for square
caps. -/
@[expose] public def Stroke.reach (s : Stroke) : Sp :=
  let half := s.width / 2
  let byJoin : Sp := match s.join with
    | .miter => if s.miterLimit ≤ 1 then half else
        Rat.ceil ((half : Rat) * s.miterLimit)
    | .round => half
    | .bevel => half
  let byCap : Sp := match s.cap with
    | .square => half + half / 2 + 1
    | .butt => half
    | .round => half
  max 0 (max half (max byJoin byCap))

/-- A mark's geometry box in the figure frame (no stroke reach). -/
@[expose] public def Mark.geomBox (rasterBox : Box) : Mark → Option Box
  | .paint ctm g _ _ _ _ => g.hull.map (Box.image ctm)
  | .raster ctm _ _ _ => some (Box.image ctm rasterBox)
  | .shading _ _ _ => none

/-- A mark's ink box in the figure frame: its geometry dilated by the
stroke's reach in the mark's frame, then imaged. -/
@[expose] public def Mark.inkBox (rasterBox : Box) : Mark → Option Box
  | .paint ctm g _ st _ _ =>
    g.hull.map fun b => Box.image ctm (Box.dilate b ((st.map Stroke.reach).getD 0))
  | .raster ctm _ _ _ => some (Box.image ctm rasterBox)
  | .shading _ _ _ => none

/-- The unit square a raster's image maps: one frame unit on a side, 2¹⁶
`Sp` — both formats' image space (a PDF image XObject paints the unit
square of its user space, an SVG `image` of width and height 1 in the
viewBox's unit). -/
@[expose] public def rasterUnit : Box := ((0, 0), (65536, 65536))

/-- The hull of a box-valued reading over an array. -/
@[expose] public def hullOf {α : Type} (f : α → Option Box) (xs : Array α) : Option Box :=
  xs.foldl (fun acc x => Box.joinOpt acc (f x)) none

/-- **The geometry box**: the hull of every mark's control points through
its frame — pgf's rule, and the box layout reserves for a picture. -/
@[expose] public def Figure.geomBox {L : Type} (fig : Figure L) : Option Box :=
  hullOf (Mark.geomBox rasterUnit) fig.marks

mutual

-- conserves: none — a census of labels, which `Figure.inkBox` reads.
/-- The labels a node holds onto `acc`, each with the frame it stands in,
over an expanded tree. -/
@[expose] public def Node.labelsOne {L : Type} (ctm : Affine) (acc : Array (Affine × L)) :
    Node L → Array (Affine × L)
  | .draw _ _ _ => acc
  | .group xf _ _ kids => Node.labelsList (ctm.compose xf) acc kids.toList
  | .use _ _ => acc
  | .stamp _ _ _ _ => acc
  | .image _ _ => acc
  | .label l => acc.push (ctm, l)
  | .words _ => acc

@[expose] public def Node.labelsList {L : Type} (ctm : Affine) (acc : Array (Affine × L)) :
    List (Node L) → Array (Affine × L)
  | [] => acc
  | n :: rest => Node.labelsList ctm (Node.labelsOne ctm acc n) rest

end

/-- Every label of a figure with its frame, in painter's order. -/
@[expose] public def Figure.labels {L : Type} (fig : Figure L) : Array (Affine × L) :=
  Node.labelsList Affine.unit #[] fig.expanded.toList

/-- **The ink box**: every mark's geometry dilated by its stroke's reach,
and every label's measured box, through their frames — the box ink claims
and overrun checks read. Quantified over the label measurement, which the
model cannot make. -/
@[expose] public def Figure.inkBox {L : Type} (fig : Figure L) (labelBox : L → Option Box) :
    Option Box :=
  Box.joinOpt (hullOf (Mark.inkBox rasterUnit) fig.marks)
    (hullOf (fun (p : Affine × L) => (labelBox p.2).map (Box.image p.1)) fig.labels)

/-! ## Rewrites -/

/-- A gradient recoloured stop by stop. -/
@[expose] public def Gradient.recolor (f : Ir.Color → Ir.Color) : Gradient → Gradient
  | .linear p0 p1 stops xf => .linear p0 p1 (stops.map fun s => { s with color := f s.color }) xf
  | .radial c0 r0 c1 r1 stops xf =>
    .radial c0 r0 c1 r1 (stops.map fun s => { s with color := f s.color }) xf

@[expose] public def Paint.recolor (f : Ir.Color → Ir.Color) : Paint → Paint
  | .solid c => .solid (f c)
  | .gradient g => .gradient (g.recolor f)

@[expose] public def Fill.recolor (f : Ir.Color → Ir.Color) (fl : Fill) : Fill :=
  { fl with paint := fl.paint.recolor f }

@[expose] public def Stroke.recolor (f : Ir.Color → Ir.Color) (st : Stroke) : Stroke :=
  { st with paint := st.paint.recolor f }

mutual

-- conserves: none — a repaint keeps the figure's words; that census is
-- `Figure.said_text`, stated over the figure.
/-- A node repainted, keeping its geometry and text; labels by `fl`. -/
@[expose] public def Node.recolorOne {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) :
    Node L → Node L
  | .draw g fill st => .draw g (fill.map (Fill.recolor f)) (st.map (Stroke.recolor f))
  | .group xf clips alpha kids => .group xf clips alpha (Node.recolorList f fl #[] kids.toList)
  | .use k xf => .use k xf
  | .stamp o xf fill st => .stamp o xf (fill.map (Fill.recolor f)) (st.map (Stroke.recolor f))
  | .image k xf => .image k xf
  | .label l => .label (fl l)
  | .words s => .words s

@[expose] public def Node.recolorList {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (acc : Array (Node L)) : List (Node L) → Array (Node L)
  | [] => acc
  | n :: rest => Node.recolorList f fl (acc.push (Node.recolorOne f fl n)) rest

end

mutual

-- conserves: none — taking labels out keeps every mark (`dropLabels_marks_id`
-- in `GfxContract`); the words census changes by exactly the labels.
/-- A node with its labels taken out at every depth: what a backend that
sets labels elsewhere paints. -/
@[expose] public def Node.dropLabelsOne {L : Type} (acc : Array (Node Empty)) :
    Node L → Array (Node Empty)
  | .draw g fl st => acc.push (.draw g fl st)
  | .group xf clips alpha kids => acc.push (.group xf clips alpha (Node.dropLabelsList #[] kids.toList))
  | .use k xf => acc.push (.use k xf)
  | .stamp o xf fl st => acc.push (.stamp o xf fl st)
  | .image k xf => acc.push (.image k xf)
  | .label _ => acc
  | .words s => acc.push (.words s)

@[expose] public def Node.dropLabelsList {L : Type} (acc : Array (Node Empty)) :
    List (Node L) → Array (Node Empty)
  | [] => acc
  | n :: rest => Node.dropLabelsList (Node.dropLabelsOne acc n) rest

end

/-- A figure with its labels taken out: a picture's ink, whose labels the
page sets as lines. -/
@[expose] public def Figure.dropLabels {L : Type} (fig : Figure L) : Figure Empty :=
  { box := fig.box, clipToBox := fig.clipToBox, nodes := Node.dropLabelsList #[] fig.nodes.toList
    outlines := fig.outlines, symbols := fig.symbols.map fun s => Node.dropLabelsList #[] s.toList
    rasters := fig.rasters, title := fig.title, losses := fig.losses }

/-- A figure repainted: how a picture dims under an overlay cover. -/
@[expose] public def Figure.recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (fig : Figure L) : Figure L :=
  { fig with nodes := Node.recolorList f fl #[] fig.nodes.toList
             symbols := fig.symbols.map fun s => Node.recolorList f fl #[] s.toList }

/-- A length on the milli-point grid both emitters print through
(`Sp.toPtString`): what a reader of the spelling gets back. -/
@[expose] public def qSp (x : Sp) : Sp :=
  let m := x.toPtMilli
  if m < 0 then -(((-m) * 65536 + 500) / 1000) else (m * 65536 + 500) / 1000

/-- A matrix entry on the nine-decimal grid of `Dim.ratString`. -/
@[expose] public def qRat (r : Rat) : Rat :=
  let n := r.num * 1000000000
  let d := (r.den : Int)
  let v := if n < 0 then -((-n + d / 2) / d) else (n + d / 2) / d
  mkRat v 1000000000

@[expose] public def Affine.quantize (m : Affine) : Affine :=
  ⟨qRat m.a, qRat m.b, qRat m.c, qRat m.d, qRat m.e, qRat m.f⟩

@[expose] public def qPt (p : Pt) : Pt := (qSp p.1, qSp p.2)

@[expose] public def Geom.quantize : Geom → Geom
  | .rect x y w h => .rect (qSp x) (qSp y) (qSp w) (qSp h)
  | .ellipse cx cy rx ry => .ellipse (qSp cx) (qSp cy) (qSp rx) (qSp ry)
  | .path subs => .path (subs.map (Subpath.map qPt))

@[expose] public def Gradient.quantize : Gradient → Gradient
  | .linear p0 p1 stops xf => .linear (qPt p0) (qPt p1) stops xf.quantize
  | .radial c0 r0 c1 r1 stops xf => .radial (qPt c0) (qSp r0) (qPt c1) (qSp r1) stops xf.quantize

@[expose] public def Paint.quantize : Paint → Paint
  | .solid c => .solid c
  | .gradient g => .gradient g.quantize

@[expose] public def Fill.quantize (fl : Fill) : Fill := { fl with paint := fl.paint.quantize }

@[expose] public def Stroke.quantize (st : Stroke) : Stroke :=
  { st with paint := st.paint.quantize, width := qSp st.width, dash := st.dash.map qSp
            phase := qSp st.phase, miterLimit := qRat st.miterLimit }

@[expose] public def Clip.quantize (c : Clip) : Clip := { c with geom := c.geom.quantize }

mutual

-- conserves: none — quantizing moves coordinates and keeps words; that
-- census is `Figure.said_text`, stated over the figure.
/-- A node on the emitters' print grid; labels by `ql`. -/
@[expose] public def Node.quantizeOne {L : Type} (ql : L → L) : Node L → Node L
  | .draw g fill st => .draw g.quantize (fill.map Fill.quantize) (st.map Stroke.quantize)
  | .group xf clips alpha kids =>
    .group xf.quantize (clips.map Clip.quantize) alpha (Node.quantizeList ql #[] kids.toList)
  | .use k xf => .use k xf.quantize
  | .stamp o xf fill st => .stamp o xf.quantize (fill.map Fill.quantize) (st.map Stroke.quantize)
  | .image k xf => .image k xf.quantize
  | .label l => .label (ql l)
  | .words s => .words s

@[expose] public def Node.quantizeList {L : Type} (ql : L → L) (acc : Array (Node L)) :
    List (Node L) → Array (Node L)
  | [] => acc
  | n :: rest => Node.quantizeList ql (acc.push (Node.quantizeOne ql n)) rest

end

/-- A figure on the grid both emitters print to: read-back identities are
stated over quantized figures. -/
@[expose] public def Figure.quantize {L : Type} (ql : L → L) (fig : Figure L) : Figure L :=
  { fig with
    box := (qPt fig.box.1, qPt fig.box.2)
    nodes := Node.quantizeList ql #[] fig.nodes.toList
    outlines := fig.outlines.map fun o => o.map (Subpath.map qPt)
    symbols := fig.symbols.map fun s => Node.quantizeList ql #[] s.toList }

mutual

-- conserves: none — the census `Figure.said` reads; `Figure.said_text` is
-- its statement.
/-- The words a node sets onto `acc`: labels through `text`, `words` as
they are. -/
@[expose] public def Node.wordsOne {L : Type} (text : L → String) (acc : Array String) :
    Node L → Array String
  | .draw _ _ _ => acc
  | .group _ _ _ kids => Node.wordsList text acc kids.toList
  | .use _ _ => acc
  | .stamp _ _ _ _ => acc
  | .image _ _ => acc
  | .label l => acc.push (text l)
  | .words s => acc.push s

@[expose] public def Node.wordsList {L : Type} (text : L → String) (acc : Array String) :
    List (Node L) → Array String
  | [] => acc
  | n :: rest => Node.wordsList text (Node.wordsOne text acc n) rest

end

/-- **What a figure says**: its labels' and words' text — a symbol's read
through each use that paints it (`Figure.expanded`) — blank ones out,
trimmed and joined as a picture's own words are (`Ir.Pic.Picture.said`). -/
@[expose] public def Figure.said {L : Type} (text : L → String) (fig : Figure L) : String :=
  String.intercalate ", " ((Node.wordsList text #[] fig.expanded.toList).toList.filterMap fun s =>
    if s.toList.any (!·.isWhitespace) then some s.trimAscii.toString else none)

/-! ## Well-formedness -/

@[expose] public def Geom.wf : Geom → Bool
  | .rect _ _ w h => 0 ≤ w && 0 ≤ h
  | .ellipse _ _ rx ry => 0 ≤ rx && 0 ≤ ry
  | .path _ => true

@[expose] public def Gradient.wf : Gradient → Bool
  | .linear _ _ stops _ => (stops.zip (stops.drop 1)).all fun (a, b) => a.offset ≤ b.offset
  | .radial _ r0 _ r1 stops _ =>
    0 ≤ r0 && 0 ≤ r1 && (stops.zip (stops.drop 1)).all fun (a, b) => a.offset ≤ b.offset

@[expose] public def Paint.wf : Paint → Bool
  | .solid _ => true
  | .gradient g => g.wf

@[expose] public def Stroke.wf (st : Stroke) : Bool :=
  0 ≤ st.width && 1 ≤ st.miterLimit && st.paint.wf &&
    (st.dash.isEmpty || (st.dash.size % 2 == 0 && st.dash.all (0 ≤ ·) && st.dash.any (0 < ·)))

mutual

-- conserves: none — a predicate.
/-- A node's indices in range — a `use` inside symbol `j` names some
`k < j` (`bound`), an outline and a raster exist — and its extents, widths,
radii and dash arrays sound. -/
@[expose] public def Node.wfOne {L : Type} (nOutlines nRasters bound : Nat) : Node L → Bool
  | .draw g fill st => g.wf && (fill.all (·.paint.wf)) && (st.all Stroke.wf)
  | .group _ clips _ kids =>
    clips.all (·.geom.wf) && Node.wfList nOutlines nRasters bound kids.toList
  | .use k _ => k < bound
  | .stamp o _ fill st => o < nOutlines && (fill.all (·.paint.wf)) && (st.all Stroke.wf)
  | .image k _ => k < nRasters
  | .label _ => true
  | .words _ => true

@[expose] public def Node.wfList {L : Type} (nOutlines nRasters bound : Nat) :
    List (Node L) → Bool
  | [] => true
  | n :: rest => Node.wfOne nOutlines nRasters bound n && Node.wfList nOutlines nRasters bound rest

end

mutual

-- conserves: none — a predicate.
/-- Whether a tree paints no raster. -/
@[expose] public def Node.imageFree {L : Type} : Node L → Bool
  | .draw _ _ _ => true
  | .group _ _ _ kids => Node.imageFreeList kids.toList
  | .use _ _ => true
  | .stamp _ _ _ _ => true
  | .image _ _ => false
  | .label _ => true
  | .words _ => true

@[expose] public def Node.imageFreeList {L : Type} : List (Node L) → Bool
  | [] => true
  | n :: rest => Node.imageFree n && Node.imageFreeList rest

end

/-- A figure that paints no raster, its symbols' bodies included — what a
page's ink is (`ofPictureIn_imageFree_exact`): the PDF writer names a raster only
from the image store, so it refuses an ink that would paint one. -/
@[expose] public def Figure.imageFree {L : Type} (fig : Figure L) : Bool :=
  Node.imageFreeList fig.nodes.toList && fig.symbols.all fun s => Node.imageFreeList s.toList

/-- A well-formed figure: every index in range, the symbol order acyclic,
stops ordered, extents, widths and radii non-negative, dash arrays even
with a positive entry, the box's corners ordered. -/
@[expose] public def Figure.wf {L : Type} (fig : Figure L) : Bool :=
  fig.box.1.1 ≤ fig.box.2.1 && fig.box.1.2 ≤ fig.box.2.2 &&
    Node.wfList fig.outlines.size fig.rasters.size fig.symbols.size fig.nodes.toList &&
    (fig.symbols.zipIdx.all fun (s, j) => Node.wfList fig.outlines.size fig.rasters.size j s.toList)

end LeanTex.Core.Gfx
