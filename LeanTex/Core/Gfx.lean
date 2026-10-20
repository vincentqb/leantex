module

public import LeanTex.Core.Dim
public import LeanTex.Core.Color
public import LeanTex.Core.Trig
import LeanTex.Core.DeriveBEq

/-! The vector model pictures, SVG images and PDF figures share: a painter's-algorithm tree in a
y-up `Length` frame, with exact rational matrices. -/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

/-- A point in a figure frame, y up. -/
public abbrev Pt := Length × Length

/-- A box: min corner, then max corner. -/
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

public theorem Box.le_refl (a : Box) : Box.le a a := by
  have h : ∀ x : Length, x ≤ x := by intro x; length_omega
  exact ⟨h _, h _, h _, h _⟩

public theorem Box.le_join_left (a b : Box) : Box.le a (Box.join a b) := by
  have hmin : ∀ x y : Length, min x y ≤ x := by intro x y; length_omega
  have hmax : ∀ x y : Length, x ≤ max x y := by intro x y; length_omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_join_right (a b : Box) : Box.le b (Box.join a b) := by
  have hmin : ∀ x y : Length, min x y ≤ y := by intro x y; length_omega
  have hmax : ∀ x y : Length, y ≤ max x y := by intro x y; length_omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_trans {a b c : Box} (h1 : Box.le a b) (h2 : Box.le b c) : Box.le a c := by
  have h : ∀ x y z : Length, x ≤ y → y ≤ z → x ≤ z := by intro x y z; length_omega
  exact ⟨h _ _ _ h2.1 h1.1, h _ _ _ h2.2.1 h1.2.1,
         h _ _ _ h1.2.2.1 h2.2.2.1, h _ _ _ h1.2.2.2 h2.2.2.2⟩

public theorem Box.join_le {a b c : Box} (ha : Box.le a c) (hb : Box.le b c) :
    Box.le (Box.join a b) c := by
  have hmin : ∀ x y z : Length, z ≤ x → z ≤ y → z ≤ min x y := by intro x y z; length_omega
  have hmax : ∀ x y z : Length, x ≤ z → y ≤ z → max x y ≤ z := by intro x y z; length_omega
  exact ⟨hmin _ _ _ ha.1 hb.1, hmin _ _ _ ha.2.1 hb.2.1,
    hmax _ _ _ ha.2.2.1 hb.2.2.1, hmax _ _ _ ha.2.2.2 hb.2.2.2⟩

/-- The hull fold over a list of boxes, polymorphic in what it reads a box from. -/
public def boxFoldList {α : Type} (f : α → Box) (acc : Box) : List α → Box
  | [] => acc
  | s :: rest => boxFoldList f (Box.join acc (f s)) rest

/-- The smallest box holding every box in an array; empty is the empty box at the origin. -/
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
@[expose] public def Box.dilate (b : Box) (d : Length) : Box :=
  ((b.1.1 - d, b.1.2 - d), (b.2.1 + d, b.2.2 + d))

@[expose] public def Box.point (p : Pt) : Box := (p, p)

/-- `a` inside `b` where either may be absent: nothing is inside anything,
and something is never inside nothing. -/
@[expose] public def Box.leOpt : Option Box → Option Box → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => Box.le a b

/-- An affine map `(x, y) ↦ (a·x + c·y + e, b·x + d·y + f)` (ISO 32000-2 §8.3.3), exact, its
translation in base units. -/
public structure Affine where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Affine.unit : Affine := ⟨1, 0, 0, 1, 0, 0⟩

/-- `m` after `n`: the map `p ↦ m (n p)`. -/
@[expose] public def Affine.compose (m n : Affine) : Affine :=
  { a := m.a * n.a + m.c * n.b, b := m.b * n.a + m.d * n.b
    c := m.a * n.c + m.c * n.d, d := m.b * n.c + m.d * n.d
    e := m.a * n.e + m.c * n.f + m.e, f := m.b * n.e + m.d * n.f + m.f }

/-- The map applied to a rational point. -/
@[expose] public def Affine.apply (m : Affine) (p : Rat × Rat) : Rat × Rat :=
  (m.a * p.1 + m.c * p.2 + m.e, m.b * p.1 + m.d * p.2 + m.f)

/-- A translation by whole lengths. -/
@[expose] public def Affine.translate (dx dy : Length) : Affine := ⟨1, 0, 0, 1, dx.toRat, dy.toRat⟩

/-- A scaling about the origin. -/
@[expose] public def Affine.scale (sx sy : Rat) : Affine := ⟨sx, 0, 0, sy, 0, 0⟩

/-- The six matrix operands both formats spell, the translation in big points. -/
public def Affine.operands (m : Affine) : String :=
  s!"{ratDecimal m.a} {ratDecimal m.b} {ratDecimal m.c} {ratDecimal m.d} \
{unitsRatBpString m.e} {unitsRatBpString m.f}"

/-- An integer isometry: `(x, y) ↦ (x + dx, dy − y)` when it flips, else `(x + dx, y + dy)`. -/
public structure Iso where
  flipY : Bool
  dx : Length
  dy : Length
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Iso.apply (t : Iso) (p : Pt) : Pt :=
  (p.1 + t.dx, if t.flipY then t.dy - p.2 else p.2 + t.dy)

@[expose] public def Iso.inv (t : Iso) : Iso :=
  if t.flipY then { flipY := true, dx := -t.dx, dy := t.dy }
  else { flipY := false, dx := -t.dx, dy := -t.dy }

/-- `s` after `t`. -/
@[expose] public def Iso.compose (s t : Iso) : Iso :=
  { flipY := s.flipY != t.flipY, dx := t.dx + s.dx
    dy := if s.flipY then s.dy - t.dy else t.dy + s.dy }

/-- The isometry as an exact matrix. -/
@[expose] public def Iso.toAffine (t : Iso) : Affine :=
  ⟨1, 0, 0, if t.flipY then -1 else 1, t.dx.toRat, t.dy.toRat⟩

public theorem Iso.inv_apply_id (t : Iso) (p : Pt) : t.inv.apply (t.apply p) = p := by
  obtain ⟨fl, dx, dy⟩ := t
  obtain ⟨x, y⟩ := p
  have hx : ∀ a b : Length, a + b + -b = a := by intro a b; length_omega
  have hy : ∀ a b : Length, b - (b - a) = a := by intro a b; length_omega
  cases fl
  · simp only [Iso.inv, Iso.apply, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    exact ⟨hx x dx, hx y dy⟩
  · simp only [Iso.inv, Iso.apply, ↓reduceIte, Prod.mk.injEq]; exact ⟨hx x dx, hy y dy⟩

public theorem Iso.apply_inv_id (t : Iso) (p : Pt) : t.apply (t.inv.apply p) = p := by
  obtain ⟨fl, dx, dy⟩ := t
  obtain ⟨x, y⟩ := p
  have hx : ∀ a b : Length, a + -b + b = a := by intro a b; length_omega
  have hy : ∀ a b : Length, b - (b - a) = a := by intro a b; length_omega
  cases fl
  · simp only [Iso.inv, Iso.apply, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    exact ⟨hx x dx, hx y dy⟩
  · simp only [Iso.inv, Iso.apply, ↓reduceIte, Prod.mk.injEq]; exact ⟨hx x dx, hy y dy⟩

/-- An axis-aligned rectangle (min corner, extents) carried by the isometry. -/
@[expose] public def Iso.rect (t : Iso) (x y w h : Length) : Length × Length × Length × Length :=
  (x + t.dx, if t.flipY then t.dy - (y + h) else y + t.dy, w, h)

/-- A box carried by the isometry: its image's min and max corners. -/
@[expose] public def Iso.box (t : Iso) (b : Box) : Box :=
  if t.flipY then ((b.1.1 + t.dx, t.dy - b.2.2), (b.2.1 + t.dx, t.dy - b.1.2))
  else ((b.1.1 + t.dx, b.1.2 + t.dy), (b.2.1 + t.dx, b.2.2 + t.dy))

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
  | rect (x y w h : Length)
  | ellipse (cx cy rx ry : Length)
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

public instance : BEq Stop where
  beq a b := a.offset == b.offset && a.color.r == b.color.r && a.color.g == b.color.g &&
    a.color.b == b.color.b && a.color.cmyk == b.color.cmyk && a.color.ink? == b.color.ink?

/-- A pad-spread gradient interpolated in sRGB-encoded components, `xf` mapping its own frame into
the node's. -/
public inductive Gradient where
  | linear (p0 p1 : Pt) (stops : Array Stop) (xf : Affine)
  | radial (c0 : Pt) (r0 : Length) (c1 : Pt) (r1 : Length) (stops : Array Stop) (xf : Affine)
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

/-- How a draw strokes, every field stated, since PDF's and SVG's defaults differ. -/
public structure Stroke where
  paint : Paint
  width : Length
  cap : Cap
  join : Join
  miterLimit : Rat
  dash : Array Length
  phase : Length
  alpha : Alpha
  deriving Repr, BEq, Inhabited

@[expose] public def Stroke.dashed (s : Stroke) : Bool := !s.dash.isEmpty

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

/-- SVG text the engine shapes: `xf` maps the run's baseline space into its frame, and a run that
`follows` continues the chunk before it (SVG 2 §11.10.2). -/
public structure Run where
  xf : Affine
  follows : Bool
  size : Length
  text : String
  face : FaceReq
  anchor : Anchor
  fill : Option Fill
  stroke : Option Stroke
  lang : Option String
  deriving Repr, Inhabited

/-- A run after shaping: each glyph's face, glyph id, scalar and pen x, with the role, weight and
slant the shaping resolved. -/
public structure Shaped where
  size : Length
  xf : Affine
  glyphs : Array (Nat × Nat × Char × Length)
  text : String
  fill : Option Fill
  stroke : Option Stroke
  lang : Option String
  role : Nat
  weight : Nat
  italic : Bool
  deriving Repr, Inhabited

/-- A raster's encoded bytes (PNG, or JPEG when `jpeg`), its pixel size, and whether a reader may smooth it. -/
public structure Raster where
  bytes : ByteArray
  jpeg : Bool
  pxW : Nat
  pxH : Nat
  smooth : Bool
  deriving Inhabited

public instance : Repr Raster where
  reprPrec r _ := s!"Raster({r.bytes.size} bytes, {r.pxW}x{r.pxH})"

/-- One node of a figure: a draw, group, symbol use, outline stamp, raster, engine-set label, or
ink-free words. -/
public inductive Node (L : Type) where
  | draw (g : Geom) (fill : Option Fill) (stroke : Option Stroke)
  | group (xf : Affine) (clips : Array Clip) (alpha : Alpha) (kids : Array (Node L))
  | use (sym : Nat) (xf : Affine)
  | stamp (outline : Nat) (xf : Affine) (fill : Option Fill) (stroke : Option Stroke)
  | image (raster : Nat) (xf : Affine)
  | label (l : L)
  | words (s : String)
  deriving Repr, Inhabited

deriving_structural_beq Node

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
  /-- A part of a style sheet the reader does not read, by the noun phrase naming it. -/
  | css (what : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A figure: the box layout reserves and whether it clips, its nodes and symbols, and its losses. -/
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

namespace Kit

/-- The quarter-arc control distance as a fraction of the radius, 4(√2 − 1)/3 ≈ 0.5523. -/
public def kappaNum : Int := 5523
public def kappaDen : Int := 10000

/-- An axis-aligned ellipse as four cubic quarter arcs, counter-clockwise from angle 0, closed. -/
@[expose] public def ellipse (cx cy rx ry : Length) : Array Subpath :=
  let kx := rx * kappaNum / kappaDen
  let ky := ry * kappaNum / kappaDen
  #[{ start := (cx + rx, cy)
      segs := #[.cubic (cx + rx, cy + ky) (cx + kx, cy + ry) (cx, cy + ry),
                .cubic (cx - kx, cy + ry) (cx - rx, cy + ky) (cx - rx, cy),
                .cubic (cx - rx, cy - ky) (cx - kx, cy - ry) (cx, cy - ry),
                .cubic (cx + kx, cy - ry) (cx + rx, cy - ky) (cx + rx, cy)]
      closed := true }]

/-- A rectangle's outline as ISO 32000-2 §8.5.2.1's `re` draws it. -/
@[expose] public def rectPath (x y w h : Length) : Subpath :=
  { start := (x, y), segs := #[.line (x + w, y), .line (x + w, y + h), .line (x, y + h)]
    closed := true }

/-- A rounded rectangle (SVG 2 §10.2), its radii clamped to half the extents. -/
public def roundedRect (x y w h rx ry : Length) : Subpath :=
  let rx := max 0 (min rx (w / 2))
  let ry := max 0 (min ry (h / 2))
  if rx == 0 || ry == 0 then rectPath x y w h else
  let kx := Length.scaleRound rx kappaNum kappaDen
  let ky := Length.scaleRound ry kappaNum kappaDen
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

/-- A quadratic Bézier elevated to the cubic that draws it, within one unit of the exact elevation. -/
public def quadToCubic (p0 q p1 : Pt) : Seg :=
  .cubic (p0.1 + Length.scaleRound (q.1 - p0.1) 2 3, p0.2 + Length.scaleRound (q.2 - p0.2) 2 3)
    (p1.1 + Length.scaleRound (q.1 - p1.1) 2 3, p1.2 + Length.scaleRound (q.2 - p1.2) 2 3) p1

/-- A dash array as both formats read it: an odd SVG list is doubled, and a
list with no positive entry or a negative one draws solid. -/
@[expose] public def normDash (d : Array Length) : Array Length :=
  if d.any (· < 0) || !d.any (0 < ·) then #[]
  else if d.size % 2 == 1 then d ++ (d) else d

private def onEllipse (cx cy sc rx ry cφ sφ θ : Int) : Pt :=
  let (c, s) := Trig.cosSin θ
  let u := rx * c
  let v := ry * s
  let uu := Trig.unit * Trig.unit
  (.ofUnits (Trig.divRound (cx * uu + (u * cφ - v * sφ)) (uu * sc)),
   .ofUnits (Trig.divRound (cy * uu + (u * sφ + v * cφ)) (uu * sc)))

private def tangent (sc rx ry cφ sφ θ k : Int) : Pt :=
  let (c, s) := Trig.cosSin θ
  let u := -(rx * s)
  let v := ry * c
  let u3 := Trig.unit * Trig.unit * Trig.unit * sc
  (.ofUnits (Trig.divRound ((u * cφ - v * sφ) * k) u3),
   .ofUnits (Trig.divRound ((u * sφ + v * cφ) * k) u3))

private def pieceK (δ : Int) : Int :=
  let cs := Trig.cosSin (δ / 4)
  if cs.1 ≤ 0 then 0 else Trig.divRound (4 * cs.2 * Trig.unit) (3 * cs.1)

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

private def arcLast (cx cy sc rx ry cφ sφ θ0 Δ θ : Int) (last : Pt) : Seg :=
  let p0 := onEllipse cx cy sc rx ry cφ sφ θ
  let kl := pieceK (θ0 + Δ - θ)
  let t0 := tangent sc rx ry cφ sφ θ kl
  let t1 := tangent sc rx ry cφ sφ (θ0 + Δ) kl
  .cubic (p0.1 + t0.1, p0.2 + t0.2) (last.1 - t1.1, last.2 - t1.2) last

private def arcCubicsAt (cx cy sc rx ry φ θ0 Δ : Int) (last : Pt) : Array Seg :=
  let quarter := Trig.pi / 2
  let n : Nat := max 1 ((Δ.natAbs + quarter.natAbs - 1) / quarter.natAbs)
  let δ := Δ / (n : Int)
  let csφ := Trig.cosSin φ
  let head := arcHead cx cy sc rx ry csφ.1 csφ.2 θ0 δ (pieceK δ) n
  head.1.push (arcLast cx cy sc rx ry csφ.1 csφ.2 θ0 Δ head.2 last)

/-- The cubic pieces of an elliptic arc from `θ0` through `Δ` (2⁻³⁰ rad), the last ending exactly on `last`. -/
public def arcCubics (cx cy rx ry : Length) (φ θ0 Δ : Int) (last : Pt) : Array Seg :=
  arcCubicsAt cx.units cy.units 1 rx.units ry.units φ θ0 Δ last

public theorem arcCubics_exact (cx cy rx ry : Length) (φ θ0 Δ : Int) (last : Pt) :
    (arcCubics cx cy rx ry φ θ0 Δ last).back?.map Seg.endPt = some last := by
  simp only [arcCubics, arcCubicsAt, Array.back?_push, Option.map_some]
  rfl

private def arcScale : Int := 65536

/-- An arc in SVG's endpoint parameterization (SVG 2 §9.5, Appendix B.2.4) as cubic pieces. -/
public def arcEndpoint (p1 : Pt) (rx ry : Length) (φ : Int) (large sweep : Bool) (p2 : Pt) :
    Array Seg :=
  if p1 == p2 then #[] else
  if rx == 0 || ry == 0 then #[.line p2] else
  let rx := rx.units
  let ry := ry.units
  let u := Trig.unit
  let sc := arcScale
  let (cφ, sφ) := Trig.cosSin φ
  let dx := (p1.1 - p2.1).units
  let dy := (p1.2 - p2.2).units
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
  let cx := Trig.divRound (cφ * cx1 - sφ * cy1) u + (p1.1 + p2.1).units * sc / 2
  let cy := Trig.divRound (sφ * cx1 + cφ * cy1) u + (p1.2 + p2.2).units * sc / 2
  let θ1 := Trig.atan2 ((y1 - cy1) * rx) ((x1 - cx1) * ry)
  let θ2 := Trig.atan2 ((-y1 - cy1) * rx) ((-x1 - cx1) * ry)
  let Δ := θ2 - θ1
  let Δ := if !sweep && Δ > 0 then Δ - 2 * Trig.pi
    else if sweep && Δ < 0 then Δ + 2 * Trig.pi else Δ
  arcCubicsAt cx cy sc rx ry φ θ1 Δ p2

/-- A regular polygon's vertices, the first at angle `θ0` (2⁻³⁰ rad). -/
public def regularPolygon (cx cy r : Length) (n : Nat) (θ0 : Int) : Subpath :=
  let n := max 3 n
  let vertex (k : Nat) : Pt :=
    let (c, s) := Trig.cosSin (θ0 + 2 * Trig.pi * (k : Int) / (n : Int))
    (cx + r.scaleRound c Trig.unit, cy + r.scaleRound s Trig.unit)
  { start := vertex 0, segs := (Array.range (n - 1)).map fun k => .line (vertex (k + 1))
    closed := true }

end Kit

/-- A geometry as both formats' readers meet it: an ellipse as its four arcs, a degenerate
rectangle as the path `re` traces. -/
@[expose] public def Geom.normal : Geom → Geom
  | .rect x y w h => if 0 < w ∧ 0 < h then .rect x y w h else .path #[Kit.rectPath x y w h]
  | .ellipse cx cy rx ry => .path (Kit.ellipse cx cy rx ry)
  | .path subs => .path subs

/-- A geometry as the path it traces from its start, which a dash pattern runs along. -/
@[expose] public def Geom.traced : Geom → Geom
  | .rect x y w h => .path #[Kit.rectPath x y w h]
  | .ellipse cx cy rx ry => .path (Kit.ellipse cx cy rx ry)
  | .path subs => .path subs

/-- The outline a draw paints: the traced path under a dashed stroke, else the normal outline. -/
@[expose] public def Geom.drawn (g : Geom) (dashed : Bool) : Geom :=
  if dashed then g.traced else g.normal

@[expose] public def Seg.map (f : Pt → Pt) : Seg → Seg
  | .line p => .line (f p)
  | .cubic c1 c2 p => .cubic (f c1) (f c2) (f p)

@[expose] public def Subpath.map (f : Pt → Pt) (s : Subpath) : Subpath :=
  { s with start := f s.start, segs := s.segs.map (Seg.map f) }

@[expose] public def Geom.mapIso (t : Iso) : Geom → Geom
  | .rect x y w h =>
    let (x', y', w', h') := t.rect x y w h
    .rect x' y' w' h'
  | .ellipse cx cy rx ry =>
    let (cx', cy') := t.apply (cx, cy)
    .ellipse cx' cy' rx ry
  | .path subs => .path (subs.map (Subpath.map t.apply))

/-- One ink mark as a reader of either artifact meets it, in the figure's frame: a paint (its frame,
drawn geometry and paints), a raster under its frame, or a shading, each with its clips and group
alphas. -/
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

-- conserves: none — a reading, not a rewrite.
/-- One node's marks onto `acc` under `cx`, over an expanded tree. -/
@[expose] public def Node.marksOne {L : Type} (outlines : Array (Array Subpath)) (cx : Ctx)
    (acc : Array Mark) : Node L → Array Mark
  | .draw g fl st =>
    acc.push (.paint cx.ctm (g.drawn (st.any Stroke.dashed)) (fl.map (Fill.under cx.ctm))
      (st.map (Stroke.under cx.ctm)) cx.clips cx.alphas)
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

-- conserves: none — expansion keeps what a use paints and says.
/-- A node with each `use k` for `k < bound` replaced by its expanded body, and every other use dropped. -/
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

/-- The symbol bodies with their uses expanded, in symbol order. -/
@[expose] public def Figure.bodies {L : Type} (fig : Figure L) : Array (Array (Node L)) :=
  fig.symbols.foldl (fun done sym => done.push (Node.expandList done done.size #[] sym.toList))
    #[]

/-- The figure's nodes with every use replaced by the group it paints. -/
@[expose] public def Figure.expanded {L : Type} (fig : Figure L) : Array (Node L) :=
  Node.expandList fig.bodies fig.bodies.size #[] fig.nodes.toList

/-- What a figure paints, in painter's order. -/
@[expose] public def Figure.marks {L : Type} (fig : Figure L) : Array Mark :=
  Node.marksList fig.outlines Ctx.root #[] fig.expanded.toList

/-- The least whole-`Length` box holding an affine image of a box, rounded outward. -/
@[expose] public def Box.image (m : Affine) (b : Box) : Box :=
  let x0 : Rat := b.1.1.toRat
  let y0 : Rat := b.1.2.toRat
  let x1 : Rat := b.2.1.toRat
  let y1 : Rat := b.2.2.toRat
  let fx (x y : Rat) : Rat := m.a * x + m.c * y + m.e
  let fy (x y : Rat) : Rat := m.b * x + m.d * y + m.f
  ((.ofRatFloor (min (min (fx x0 y0) (fx x1 y0)) (min (fx x0 y1) (fx x1 y1))),
    .ofRatFloor (min (min (fy x0 y0) (fy x1 y0)) (min (fy x0 y1) (fy x1 y1)))),
   (.ofRatCeil (max (max (fx x0 y0) (fx x1 y0)) (max (fx x0 y1) (fx x1 y1))),
    .ofRatCeil (max (max (fy x0 y0) (fy x1 y0)) (max (fy x0 y1) (fy x1 y1)))))

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

/-- A geometry's control hull in its own frame, which bounds what it draws; `none` for a path with no points. -/
@[expose] public def Geom.hull : Geom → Option Box
  | .rect x y w h => some ((min x (x + w), min y (y + h)), (max x (x + w), max y (y + h)))
  | .ellipse cx cy rx ry =>
    some ((min (cx - rx) (cx + rx), min (cy - ry) (cy + ry)),
      (max (cx - rx) (cx + rx), max (cy - ry) (cy + ry)))
  | .path subs => ptsHull none (subs.toList.flatMap Subpath.points)

/-- The exact point at `t` of the cubic Bézier from `p0` through `c1` and `c2` to `p1`. -/
@[expose] public def cubicAt (p0 c1 c2 p1 : Pt) (t : Rat) : Rat × Rat :=
  let s := 1 - t
  let w0 := s * s * s
  let w1 := 3 * s * s * t
  let w2 := 3 * s * t * t
  let w3 := t * t * t
  (w0 * p0.1.toRat + w1 * c1.1.toRat + w2 * c2.1.toRat + w3 * p1.1.toRat,
   w0 * p0.2.toRat + w1 * c1.2.toRat + w2 * c2.2.toRat + w3 * p1.2.toRat)

/-- How far a stroke's paint reaches past its path: half the width, times the miter limit for miter
joins and 3/2 for square caps. -/
@[expose] public def Stroke.reach (s : Stroke) : Length :=
  let half := s.width / 2
  let byJoin : Length := match s.join with
    | .miter => if s.miterLimit ≤ 1 then half else
        .ofRatCeil (half.toRat * s.miterLimit)
    | .round => half
    | .bevel => half
  let byCap : Length := match s.cap with
    | .square => half + half / 2 + Length.quantum
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

/-- The unit square a raster's image maps, one big point on a side in both formats. -/
@[expose] public def rasterUnit : Box := ((0, 0), (bp 1, bp 1))

/-- The hull of a box-valued reading over an array. -/
@[expose] public def hullOf {α : Type} (f : α → Option Box) (xs : Array α) : Option Box :=
  xs.foldl (fun acc x => Box.joinOpt acc (f x)) none

/-- The geometry box: the hull of every mark's control points through its frame, the box layout
reserves for a picture. -/
@[expose] public def Figure.geomBox {L : Type} (fig : Figure L) : Option Box :=
  hullOf (Mark.geomBox rasterUnit) fig.marks

mutual

-- conserves: none — a census of labels, which `Figure.inkBox` reads.
/-- The labels a node holds onto `acc`, each with its frame, over an expanded tree. -/
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

/-- The ink box: every mark's stroke-dilated geometry and every label's measured box, through their frames. -/
@[expose] public def Figure.inkBox {L : Type} (fig : Figure L) (labelBox : L → Option Box) :
    Option Box :=
  Box.joinOpt (hullOf (Mark.inkBox rasterUnit) fig.marks)
    (hullOf (fun (p : Affine × L) => (labelBox p.2).map (Box.image p.1)) fig.labels)

/-- The stops of a gradient. -/
@[expose] public def Gradient.stops : Gradient → Array Stop
  | .linear _ _ stops _ => stops
  | .radial _ _ _ _ stops _ => stops

/-- The one ink a gradient shades: every stop the paper or a tint of that ink, one of them the
ink; `none` for any other gradient. -/
public def Gradient.singleInk? (g : Gradient) : Option Ir.Ink := do
  let i ← g.stops.findSome? fun s => s.color.ink?.map (·.1)
  guard (g.stops.all fun s => s.color.isPaper || (s.color.ink?.map (·.1)) == some i)
  return i

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

private theorem Stroke.recolor_dashed (f : Ir.Color → Ir.Color) (st : Option Stroke) :
    (st.map (Stroke.recolor f)).any Stroke.dashed = st.any Stroke.dashed := by
  cases st <;> rfl

mutual

-- conserves: none — a repaint keeps the figure's words.
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

/-- A paint's gradient, after `acc`. -/
@[expose] public def paintGradients (acc : Array Gradient) : Option Paint → Array Gradient
  | some (.gradient g) => acc.push g
  | some (.solid _) | none => acc

mutual

-- conserves: none — answers the gradients a node paints, a read the PDF and judges share.
/-- The gradients a node paints at every depth, in paint order. -/
@[expose] public def Node.gradientsOne {L : Type} (acc : Array Gradient) : Node L → Array Gradient
  | .draw _ fill st => paintGradients (paintGradients acc (fill.map (·.paint))) (st.map (·.paint))
  | .group _ _ _ kids => Node.gradientsList acc kids.toList
  | .stamp _ _ fill st => paintGradients (paintGradients acc (fill.map (·.paint))) (st.map (·.paint))
  | .use _ _ | .image _ _ | .label _ | .words _ => acc

@[expose] public def Node.gradientsList {L : Type} (acc : Array Gradient) :
    List (Node L) → Array Gradient
  | [] => acc
  | n :: rest => Node.gradientsList (Node.gradientsOne acc n) rest

end

mutual

-- conserves: none — taking labels out keeps every mark.
/-- A node with its labels taken out at every depth. -/
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

public theorem Node.recolorList_map {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (acc : Array (Node L)) (xs : List (Node L)) :
    Node.recolorList f fl acc xs = acc ++ (xs.map (Node.recolorOne f fl)).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.recolorList]
  | cons x rest ih => simp [Node.recolorList, ih]

private theorem hullOf_map_eq {α β : Type} (r : α → Option Box) (q : β → Option Box)
    (xs : Array α) (ys : Array β) (h : xs.map r = ys.map q) : hullOf r xs = hullOf q ys := by
  unfold hullOf
  rw [← Array.foldl_map (f := r) (g := Box.joinOpt), ← Array.foldl_map (f := q) (g := Box.joinOpt),
    h]

mutual

private theorem marksOne_recolor_geom {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (outlines : Array (Array Subpath)) (cx : Ctx) (acc acc' : Array Mark)
    (h : acc'.map (Mark.geomBox rasterUnit) = acc.map (Mark.geomBox rasterUnit)) :
    ∀ n : Node L,
      (Node.marksOne outlines cx acc' (Node.recolorOne f fl n)).map (Mark.geomBox rasterUnit) =
        (Node.marksOne outlines cx acc n).map (Mark.geomBox rasterUnit)
  | .draw g fill st => by
    simp only [Node.recolorOne, Node.marksOne, Array.map_push, h, Mark.geomBox,
      Stroke.recolor_dashed]
  | .group xf clips alpha kids => by
    simp only [Node.recolorOne, Node.marksOne, Node.recolorList_map, Array.toList_append,
      List.nil_append]
    exact marksList_recolor_geom f fl outlines _ acc acc' h kids.toList
  | .use k xf => by simp only [Node.recolorOne, Node.marksOne, h]
  | .stamp o xf fill st => by
    simp only [Node.recolorOne, Node.marksOne, Array.map_push, h, Mark.geomBox]
  | .image k xf => by simp only [Node.recolorOne, Node.marksOne, Array.map_push, h, Mark.geomBox]
  | .label l => by simp only [Node.recolorOne, Node.marksOne, h]
  | .words w => by simp only [Node.recolorOne, Node.marksOne, h]

private theorem marksList_recolor_geom {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (outlines : Array (Array Subpath)) (cx : Ctx) (acc acc' : Array Mark)
    (h : acc'.map (Mark.geomBox rasterUnit) = acc.map (Mark.geomBox rasterUnit)) :
    ∀ xs : List (Node L),
      (Node.marksList outlines cx acc' (xs.map (Node.recolorOne f fl))).map
          (Mark.geomBox rasterUnit) =
        (Node.marksList outlines cx acc xs).map (Mark.geomBox rasterUnit)
  | [] => by simpa [Node.marksList] using h
  | n :: rest => by
    simp only [List.map_cons, Node.marksList]
    exact marksList_recolor_geom f fl outlines cx _ _
      (marksOne_recolor_geom f fl outlines cx acc acc' h n) rest

end

public theorem Node.recolor_geomBox_id {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (n : Node L) :
    hullOf (Mark.geomBox rasterUnit) (Node.marksOne #[] Ctx.root #[] (Node.recolorOne f fl n)) =
      hullOf (Mark.geomBox rasterUnit) (Node.marksOne #[] Ctx.root #[] n) :=
  hullOf_map_eq _ _ _ _ (marksOne_recolor_geom f fl #[] Ctx.root #[] #[] rfl n)

/-- A figure with its labels taken out, for a page that sets them as lines. -/
@[expose] public def Figure.dropLabels {L : Type} (fig : Figure L) : Figure Empty :=
  { box := fig.box, clipToBox := fig.clipToBox, nodes := Node.dropLabelsList #[] fig.nodes.toList
    outlines := fig.outlines, symbols := fig.symbols.map fun s => Node.dropLabelsList #[] s.toList
    rasters := fig.rasters, title := fig.title, losses := fig.losses }

@[expose] public def Figure.recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (fig : Figure L) : Figure L :=
  { fig with nodes := Node.recolorList f fl #[] fig.nodes.toList
             symbols := fig.symbols.map fun s => Node.recolorList f fl #[] s.toList }

/-- A length on the milli-point grid both emitters print to. -/
@[expose] public def qLen (x : Length) : Length := .ofBpMilli x.toBpMilli

/-- A matrix entry on the nine-decimal grid of `Dim.ratString`. -/
@[expose] public def qRat (r : Rat) : Rat :=
  let n := r.num * 1000000000
  let d := (r.den : Int)
  let v := if n < 0 then -((-n + d / 2) / d) else (n + d / 2) / d
  mkRat v 1000000000

@[expose] public def Affine.quantize (m : Affine) : Affine :=
  ⟨qRat m.a, qRat m.b, qRat m.c, qRat m.d, qRat m.e, qRat m.f⟩

@[expose] public def qPt (p : Pt) : Pt := (qLen p.1, qLen p.2)

@[expose] public def Geom.quantize : Geom → Geom
  | .rect x y w h => .rect (qLen x) (qLen y) (qLen w) (qLen h)
  | .ellipse cx cy rx ry => .ellipse (qLen cx) (qLen cy) (qLen rx) (qLen ry)
  | .path subs => .path (subs.map (Subpath.map qPt))

@[expose] public def Gradient.quantize : Gradient → Gradient
  | .linear p0 p1 stops xf => .linear (qPt p0) (qPt p1) stops xf.quantize
  | .radial c0 r0 c1 r1 stops xf => .radial (qPt c0) (qLen r0) (qPt c1) (qLen r1) stops xf.quantize

@[expose] public def Paint.quantize : Paint → Paint
  | .solid c => .solid c
  | .gradient g => .gradient g.quantize

@[expose] public def Fill.quantize (fl : Fill) : Fill := { fl with paint := fl.paint.quantize }

@[expose] public def Stroke.quantize (st : Stroke) : Stroke :=
  { st with paint := st.paint.quantize, width := qLen st.width, dash := st.dash.map qLen
            phase := qLen st.phase, miterLimit := qRat st.miterLimit }

@[expose] public def Clip.quantize (c : Clip) : Clip := { c with geom := c.geom.quantize }

mutual

-- conserves: none — quantizing moves coordinates and keeps words.
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

/-- A figure on the grid both emitters print to. -/
@[expose] public def Figure.quantize {L : Type} (ql : L → L) (fig : Figure L) : Figure L :=
  { fig with
    box := (qPt fig.box.1, qPt fig.box.2)
    nodes := Node.quantizeList ql #[] fig.nodes.toList
    outlines := fig.outlines.map fun o => o.map (Subpath.map qPt)
    symbols := fig.symbols.map fun s => Node.quantizeList ql #[] s.toList }

mutual

-- conserves: none — the census `Figure.said` reads.
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

/-- What a figure says: its labels' and words' text, symbols read through their uses, blanks out, joined. -/
@[expose] public def Figure.said {L : Type} (text : L → String) (fig : Figure L) : String :=
  String.intercalate ", " ((Node.wordsList text #[] fig.expanded.toList).toList.filterMap fun s =>
    if s.toList.any (!·.isWhitespace) then some s.trimAscii.toString else none)

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
/-- A node's indices in range and its extents, widths, radii and dash arrays sound. -/
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

/-- A figure that paints no raster, its symbols included. -/
@[expose] public def Figure.imageFree {L : Type} (fig : Figure L) : Bool :=
  Node.imageFreeList fig.nodes.toList && fig.symbols.all fun s => Node.imageFreeList s.toList

/-- A well-formed figure: every index in range, the symbol order acyclic,
stops ordered, extents, widths and radii non-negative, dash arrays even
with a positive entry, the box's corners ordered. -/
@[expose] public def Figure.wf {L : Type} (fig : Figure L) : Bool :=
  fig.box.1.1 ≤ fig.box.2.1 && fig.box.1.2 ≤ fig.box.2.2 &&
    Node.wfList fig.outlines.size fig.rasters.size fig.symbols.size fig.nodes.toList &&
    (fig.symbols.zipIdx.all fun (s, j) => Node.wfList fig.outlines.size fig.rasters.size j s.toList)

mutual

-- conserves: none — a predicate.
@[expose] public def Node.labelFree {L : Type} : Node L → Bool
  | .draw _ _ _ => true
  | .group _ _ _ kids => Node.labelFreeList kids.toList
  | .use _ _ => true
  | .stamp _ _ _ _ => true
  | .image _ _ => true
  | .label _ => false
  | .words _ => true

@[expose] public def Node.labelFreeList {L : Type} : List (Node L) → Bool
  | [] => true
  | n :: rest => Node.labelFree n && Node.labelFreeList rest

end

mutual

-- conserves: none — a relabelling that keeps every mark.
/-- A node with each label read through `f`, at every depth; its ink stays. -/
@[expose] public def Node.mapLabelsOne {L L' : Type} (f : L → L') : Node L → Node L'
  | .draw g fl st => .draw g fl st
  | .group xf clips alpha kids => .group xf clips alpha (Node.mapLabelsList f #[] kids.toList)
  | .use k xf => .use k xf
  | .stamp o xf fl st => .stamp o xf fl st
  | .image k xf => .image k xf
  | .label l => .label (f l)
  | .words s => .words s

@[expose] public def Node.mapLabelsList {L L' : Type} (f : L → L') (acc : Array (Node L')) :
    List (Node L) → Array (Node L')
  | [] => acc
  | n :: rest => Node.mapLabelsList f (acc.push (Node.mapLabelsOne f n)) rest

end

/-- A node a figure's top level may hold where its labels stand there: a
label, or ink holding none. -/
@[expose] public def Node.topOk {L : Type} : Node L → Bool
  | .label _ => true
  | .draw _ _ _ => true
  | .group _ _ _ kids => Node.labelFreeList kids.toList
  | .use _ _ => true
  | .stamp _ _ _ _ => true
  | .image _ _ => true
  | .words _ => true

/-- A figure whose labels stand at its top level: every node a label or label-free ink, every
symbol label-free. -/
@[expose] public def Figure.labelsTop {L : Type} (fig : Figure L) : Bool :=
  fig.nodes.all Node.topOk && fig.symbols.all fun s => s.all Node.labelFree

/-- One step of what a figure paints, in painter's order: an ink mark, or a
label the engine sets. -/
public inductive Step (L : Type) where
  | mark (m : Mark)
  | label (l : L)
  deriving Repr, BEq, Inhabited

@[expose] public def Step.mapLabel {L L' : Type} (f : L → L') : Step L → Step L'
  | .mark m => .mark m
  | .label l => .label (f l)

/-- A step with its label replaced by what `f` sets for it — none, one or
several labels of another type; a mark stays. -/
@[expose] public def Step.labelsBy {L α : Type} (f : L → Array α) : Step L → Array (Step α)
  | .mark m => #[.mark m]
  | .label l => (f l).map .label

/-- One top-level node's steps: a label itself, any other node the marks it paints. -/
@[expose] public def Figure.nodeSteps {L : Type} (fig : Figure L) (n : Node L) : Array (Step L) :=
  match n with
  | .label l => #[.label l]
  | .draw .. | .group .. | .use .. | .stamp .. | .image .. | .words _ =>
    (Node.marksList fig.outlines Ctx.root #[]
      (Node.expandOne fig.bodies fig.bodies.size #[] n).toList).map .mark

/-- What a figure paints, its top-level labels among its ink, in painter's order. -/
@[expose] public def Figure.steps {L : Type} (fig : Figure L) : Array (Step L) :=
  fig.nodes.foldl (fun acc n => acc ++ fig.nodeSteps n) #[]

end LeanTex.Core.Gfx
