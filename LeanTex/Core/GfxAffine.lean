module

public import LeanTex.Core.Gfx

/-!
# The figure frame's algebra

The proofs `Gfx` keeps off the import chain to the elaborator: exact
rational transforms compose associatively with a unit, application commutes
with composition, an integer isometry inverts exactly on points, rectangles
and geometry, and an affine image of a box covers the image of every point
inside it; the print grid both emitters spell is a fixed point; the ink box
covers every mark and label and the geometry box; a cubic stays inside its
control hull.
-/

namespace LeanTex.Core.Gfx

open LeanTex.Core.Dim

/-- Applying a composite is applying its parts in turn. -/
public theorem Affine.apply_compose_exact (m n : Affine) (p : Rat × Rat) :
    (m.compose n).apply p = m.apply (n.apply p) := by
  cases m; cases n; cases p
  simp only [Affine.compose, Affine.apply, Prod.mk.injEq]
  constructor <;> grind

/-- Composition is associative, exactly: frames nest without rounding. -/
public theorem Affine.compose_assoc_exact (m n o : Affine) :
    (m.compose n).compose o = m.compose (n.compose o) := by
  cases m; cases n; cases o
  simp only [Affine.compose, Affine.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The identity is a unit on both sides. -/
public theorem Affine.compose_unit_id (m : Affine) :
    m.compose Affine.unit = m ∧ Affine.unit.compose m = m := by
  cases m
  simp only [Affine.compose, Affine.unit, Affine.mk.injEq]
  grind

/-- An isometry's matrix applies as the isometry does. -/
public theorem Iso.toAffine_apply_exact (t : Iso) (p : Pt) :
    t.toAffine.apply ((p.1 : Rat), (p.2 : Rat)) =
      (((t.apply p).1 : Rat), ((t.apply p).2 : Rat)) := by
  obtain ⟨fl, dx, dy⟩ := t
  obtain ⟨x, y⟩ := p
  cases fl <;> simp only [Iso.toAffine, Affine.apply, Iso.apply, Prod.mk.injEq,
    Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> constructor <;> grind

/-- Composition of isometries is application in turn. -/
public theorem Iso.compose_apply_exact (s t : Iso) (p : Pt) :
    (s.compose t).apply p = s.apply (t.apply p) := by
  obtain ⟨fs, sx, sy⟩ := s
  obtain ⟨ft, tx, ty⟩ := t
  obtain ⟨x, y⟩ := p
  have hx : ∀ a b c : Int, a + (b + c) = a + b + c := by intro a b c; omega
  have ff : ∀ a b c : Int, a + (b + c) = a + b + c := by intro a b c; omega
  have ft' : ∀ a b c : Int, b + c - a = b - a + c := by intro a b c; omega
  have tf : ∀ a b c : Int, c - b - a = c - (a + b) := by intro a b c; omega
  have tt : ∀ a b c : Int, a + (c - b) = c - (b - a) := by intro a b c; omega
  cases fs <;> cases ft
  · simp only [Iso.compose, Iso.apply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] <;>
      exact Prod.ext (hx x tx sx) (ff y ty sy)
  · simp only [Iso.compose, Iso.apply, Bool.false_bne, ↓reduceIte, Bool.false_eq_true] <;>
      exact Prod.ext (hx x tx sx) (ft' y ty sy)
  · simp only [Iso.compose, Iso.apply, Bool.bne_false, ↓reduceIte, Bool.false_eq_true] <;>
      exact Prod.ext (hx x tx sx) (tf y ty sy)
  · simp only [Iso.compose, Iso.apply, bne_self_eq_false, ↓reduceIte, Bool.false_eq_true] <;>
      exact Prod.ext (hx x tx sx) (tt y ty sy)

/-- An isometry's inverse matrix cancels its matrix, exactly. -/
public theorem Iso.inv_compose_unit_id (t : Iso) :
    t.inv.toAffine.compose t.toAffine = Affine.unit := by
  obtain ⟨fl, dx, dy⟩ := t
  cases fl <;> simp only [Iso.inv, Iso.toAffine, Affine.compose, Affine.unit,
    Bool.false_eq_true, ↓reduceIte, Affine.mk.injEq] <;> push_cast <;> grind

/-- The rectangle carried by the inverse is the rectangle carried back. -/
public theorem Iso.rect_inv_id (t : Iso) (x y w h : Sp) :
    let r := t.rect x y w h
    t.inv.rect r.1 r.2.1 r.2.2.1 r.2.2.2 = (x, y, w, h) := by
  obtain ⟨fl, dx, dy⟩ := t
  have hx : ∀ a b : Int, a + b + -b = a := by intro a b; omega
  have hy : ∀ a b c : Int, b - (b - (a + c) + c) = a := by intro a b c; omega
  cases fl
  · simp only [Iso.inv, Iso.rect, Bool.false_eq_true, ↓reduceIte] <;>
      exact Prod.ext (hx x dx) (Prod.ext (hx y dy) rfl)
  · simp only [Iso.inv, Iso.rect, ↓reduceIte] <;>
      exact Prod.ext (hx x dx) (Prod.ext (hy y dy h) rfl)

/-- Mapping a point list by the inverse undoes mapping it by the isometry. -/
private theorem Seg.map_inv_id (t : Iso) (s : Seg) : (s.map t.apply).map t.inv.apply = s := by
  cases s <;> simp [Seg.map, Iso.inv_apply_id]

private theorem Subpath.map_inv_id (t : Iso) (s : Subpath) :
    (s.map t.apply).map t.inv.apply = s := by
  obtain ⟨st, segs, cl⟩ := s
  simp only [Subpath.map, Iso.inv_apply_id, Array.map_map, Subpath.mk.injEq, true_and, and_true]
  conv => rhs; rw [← Array.map_id segs]
  apply Array.map_congr_left
  intro a _
  exact Seg.map_inv_id t a

/-- **A geometry carried by an isometry comes back exactly** (`_id`): the
reader of either artifact recovers the figure's geometry from the placed
one, whatever the placement flips. -/
public theorem Geom.mapIso_inv_id (t : Iso) (g : Geom) : (g.mapIso t).mapIso t.inv = g := by
  cases g with
  | rect x y w h =>
    have := Iso.rect_inv_id t x y w h
    simp only [Geom.mapIso] at this ⊢
    rw [this]
  | ellipse cx cy rx ry =>
    have := Iso.inv_apply_id t (cx, cy)
    simp only [Geom.mapIso]
    rw [this]
  | path subs =>
    simp only [Geom.mapIso, Array.map_map, Geom.path.injEq]
    conv => rhs; rw [← Array.map_id subs]
    apply Array.map_congr_left
    intro a _
    exact Subpath.map_inv_id t a

/-- A product with a coordinate inside an interval is inside the interval
the endpoints' products span, whatever the factor's sign. -/
private theorem mul_between (a x0 x x1 : Rat) (h0 : x0 ≤ x) (h1 : x ≤ x1) :
    min (a * x0) (a * x1) ≤ a * x ∧ a * x ≤ max (a * x0) (a * x1) := by
  rcases Rat.le_total (a := 0) (b := a) with h | h
  · have := Rat.mul_le_mul_of_nonneg_left h0 h
    have := Rat.mul_le_mul_of_nonneg_left h1 h
    grind
  · have := Rat.mul_le_mul_of_nonneg_left h0 (show 0 ≤ -a by grind)
    have := Rat.mul_le_mul_of_nonneg_left h1 (show 0 ≤ -a by grind)
    grind

/-- An affine coordinate over a box is between its values at the box's
corners: linear in each axis, so its extremes are corners. -/
private theorem affine_between (a c e x0 x1 y0 y1 x y : Rat)
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    min (min (a * x0 + c * y0 + e) (a * x1 + c * y0 + e))
        (min (a * x0 + c * y1 + e) (a * x1 + c * y1 + e)) ≤ a * x + c * y + e ∧
    a * x + c * y + e ≤
      max (max (a * x0 + c * y0 + e) (a * x1 + c * y0 + e))
        (max (a * x0 + c * y1 + e) (a * x1 + c * y1 + e)) := by
  have ha := mul_between a x0 x x1 hx0 hx1
  have hc := mul_between c y0 y y1 hy0 hy1
  grind

/-- **An affine image of a box covers the image of every point inside it**
(`_covers`): the image's x and y lie between the rounded-outward box's
edges. What makes a box carried through a frame a sound bound for the ink
the frame paints. -/
public theorem Affine.boxImage_covers (m : Affine) (b : Box) (x y : Rat)
    (hx0 : (b.1.1 : Rat) ≤ x) (hx1 : x ≤ (b.2.1 : Rat))
    (hy0 : (b.1.2 : Rat) ≤ y) (hy1 : y ≤ (b.2.2 : Rat)) :
    ((Box.image m b).1.1 : Rat) ≤ (m.apply (x, y)).1 ∧ (m.apply (x, y)).1 ≤ ((Box.image m b).2.1 : Rat) ∧
    ((Box.image m b).1.2 : Rat) ≤ (m.apply (x, y)).2 ∧ (m.apply (x, y)).2 ≤ ((Box.image m b).2.2 : Rat) := by
  have hx := affine_between m.a m.c m.e _ _ _ _ x y hx0 hx1 hy0 hy1
  have hy := affine_between m.b m.d m.f _ _ _ _ x y hx0 hx1 hy0 hy1
  simp only [Box.image, Affine.apply]
  exact ⟨Rat.le_trans (Rat.floor_le _) hx.1, Rat.le_trans hx.2 Rat.le_ceil,
    Rat.le_trans (Rat.floor_le _) hy.1, Rat.le_trans hy.2 Rat.le_ceil⟩

private theorem image_monotone_core (m : Affine) (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : Int)
    (h1 : bx0 ≤ ax0) (h2 : by0 ≤ ay0) (h3 : ax1 ≤ bx1) (h4 : ay1 ≤ by1)
    (hx : ax0 ≤ ax1) (hy : ay0 ≤ ay1) :
    Box.le (Box.image m ((ax0, ay0), (ax1, ay1))) (Box.image m ((bx0, by0), (bx1, by1))) := by
  have cast : ∀ {p q : Int}, p ≤ q → (p : Rat) ≤ (q : Rat) := fun h =>
    Rat.intCast_le_intCast.mpr h
  have cv := fun (x y : Int) (hx0 : bx0 ≤ x) (hx1 : x ≤ bx1) (hy0 : by0 ≤ y) (hy1 : y ≤ by1) =>
    Affine.boxImage_covers m ((bx0, by0), (bx1, by1)) x y (cast hx0) (cast hx1) (cast hy0) (cast hy1)
  have c00 := cv ax0 ay0 h1 (by omega) h2 (by omega)
  have c10 := cv ax1 ay0 (by omega) h3 h2 (by omega)
  have c01 := cv ax0 ay1 h1 (by omega) (by omega) h4
  have c11 := cv ax1 ay1 (by omega) h3 (by omega) h4
  simp only [Box.image, Affine.apply] at c00 c10 c01 c11 ⊢
  refine ⟨Rat.le_floor_iff.mpr ?_, Rat.le_floor_iff.mpr ?_, Rat.ceil_le_iff.mpr ?_,
    Rat.ceil_le_iff.mpr ?_⟩ <;> grind

/-- **A box carried through a frame grows with the box** (`_monotone`):
every corner of an ordered smaller box is a point of the larger, so its
image is inside the larger's image, and the outward rounding keeps the
order. -/
public theorem Box.image_monotone (m : Affine) {a b : Box} (h : Box.le a b)
    (hx : a.1.1 ≤ a.2.1) (hy : a.1.2 ≤ a.2.2) :
    Box.le (Box.image m a) (Box.image m b) := by
  obtain ⟨⟨ax0, ay0⟩, ⟨ax1, ay1⟩⟩ := a
  obtain ⟨⟨bx0, by0⟩, ⟨bx1, by1⟩⟩ := b
  exact image_monotone_core m ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 h.1 h.2.1 h.2.2.1 h.2.2.2 hx hy

/-! ## Reading walks: accumulators and expansion -/

public theorem Node.marksList_append {L : Type} (outlines : Array (Array Subpath)) (cx : Ctx)
    (acc : Array Mark) (a b : List (Node L)) :
    Node.marksList outlines cx acc (a ++ b) =
      Node.marksList outlines cx (Node.marksList outlines cx acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons n rest ih => simp [Node.marksList, ih]

mutual

public theorem Node.expandOne_acc {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (acc : Array (Node L)) (n : Node L) :
    Node.expandOne done bound acc n = acc ++ Node.expandOne done bound #[] n := by
  cases n with
  | draw g fl st => simp [Node.expandOne]
  | group xf clips alpha kids => simp [Node.expandOne]
  | use k xf =>
    simp only [Node.expandOne]
    split
    · split <;> simp
    · simp
  | stamp o xf fl st => simp [Node.expandOne]
  | image k xf => simp [Node.expandOne]
  | label l => simp [Node.expandOne]
  | words w => simp [Node.expandOne]

public theorem Node.expandList_acc {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (acc : Array (Node L)) (xs : List (Node L)) :
    Node.expandList done bound acc xs = acc ++ Node.expandList done bound #[] xs := by
  match xs with
  | [] => simp [Node.expandList]
  | n :: rest =>
    simp only [Node.expandList]
    rw [Node.expandList_acc done bound _ rest,
      Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest,
      Node.expandOne_acc done bound acc n, Array.append_assoc]

end
public theorem Node.useFreeList_append {L : Type} (a b : List (Node L)) :
    Node.useFreeList (a ++ b) = (Node.useFreeList a && Node.useFreeList b) := by
  induction a with
  | nil => simp [Node.useFreeList]
  | cons n rest ih => simp [Node.useFreeList, ih, Bool.and_assoc]

mutual

public theorem Node.expandOne_useFree {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (hdone : ∀ b ∈ done, Node.useFreeList b.toList = true) :
    ∀ (n : Node L) (acc : Array (Node L)), Node.useFreeList acc.toList = true →
      Node.useFreeList (Node.expandOne done bound acc n).toList = true
  | .draw g fl st, acc, ha => by
    simp [Node.expandOne, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree]
  | .group xf clips alpha kids, acc, ha => by
    simp only [Node.expandOne, Array.toList_push, Node.useFreeList_append, ha, Node.useFreeList,
      Node.useFree, Bool.true_and, Bool.and_true]
    exact Node.expandList_useFree done bound hdone kids.toList #[] rfl
  | .use k xf, acc, ha => by
    simp only [Node.expandOne]
    split
    · split
      · next body hb =>
        simp only [Array.toList_push, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree,
          Bool.true_and, Bool.and_true]
        exact hdone body (Array.mem_of_getElem? hb)
      · exact ha
    · exact ha
  | .stamp o xf fl st, acc, ha => by
    simp [Node.expandOne, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree]
  | .image k xf, acc, ha => by
    simp [Node.expandOne, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree]
  | .label l, acc, ha => by
    simp [Node.expandOne, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree]
  | .words w, acc, ha => by
    simp [Node.expandOne, Node.useFreeList_append, ha, Node.useFreeList, Node.useFree]

public theorem Node.expandList_useFree {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (hdone : ∀ b ∈ done, Node.useFreeList b.toList = true) :
    ∀ (xs : List (Node L)) (acc : Array (Node L)), Node.useFreeList acc.toList = true →
      Node.useFreeList (Node.expandList done bound acc xs).toList = true
  | [], acc, ha => ha
  | n :: rest, acc, ha => by
    simp only [Node.expandList]
    exact Node.expandList_useFree done bound hdone rest _ (Node.expandOne_useFree done bound hdone n acc ha)

end

/-- **Every expanded symbol body is use-free** (`_covers`): body `j` reads
only bodies before it, each already expanded, so no `use` survives — what
lets a form body be read without a further lookup. -/
public theorem Figure.bodies_useFree_covers {L : Type} (fig : Figure L) :
    ∀ b ∈ fig.bodies, Node.useFreeList b.toList = true := by
  unfold Figure.bodies
  refine Array.foldl_induction (motive := fun _ (done : Array (Array (Node L))) =>
    ∀ b ∈ done, Node.useFreeList b.toList = true) (by simp) ?_
  intro i done ih b hb
  simp only [Array.mem_push] at hb
  rcases hb with hb | rfl
  · exact ih b hb
  · exact Node.expandList_useFree done done.size ih _ #[] rfl



/-! ## The print grid is a fixed point -/

-- The grid arithmetic is stated over bare `Int`: `omega` does not see
-- through `Sp`.
private theorem milli_back (M : Int) :
    (((M * 65536 + 500) / 1000) * 1000 + 32768) / 65536 = M := by
  omega

private theorem toPtMilli_qSp_core (x : Int) : Sp.toPtMilli (qSp x) = Sp.toPtMilli x := by
  have hm : ∀ y : Int, Sp.toPtMilli y =
      if y < 0 then -(((y.natAbs * 1000 + 32768) / 65536 : Nat) : Int)
      else (((y.natAbs * 1000 + 32768) / 65536 : Nat) : Int) := fun _ => rfl
  generalize hM : Sp.toPtMilli x = m
  have hq : qSp x = if m < 0 then -(((-m) * 65536 + 500) / 1000) else (m * 65536 + 500) / 1000 := by
    simp only [qSp, hM]
  rw [hq]
  split
  · rw [hm]
    have := milli_back (-m)
    split <;> omega
  · rw [hm]
    have := milli_back m
    split <;> omega

/-- A length on the print grid stays where it is (`_fixed_point`). -/
public theorem qSp_fixed_point (x : Sp) : qSp (qSp x) = qSp x := by
  have hg : ∀ y : Sp, qSp y = (fun m : Int =>
      if m < 0 then -(((-m) * 65536 + 500) / 1000) else (m * 65536 + 500) / 1000) (Sp.toPtMilli y) :=
    fun _ => rfl
  rw [hg (qSp x), toPtMilli_qSp_core x, ← hg x]

private theorem round_mul (v d : Int) (hd : 0 < d) :
    (if v * d < 0 then -((-(v * d) + d / 2) / d) else (v * d + d / 2) / d) = v := by
  have h2 : (d / 2) / d = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  split
  · rw [← Int.neg_mul, Int.add_comm, Int.add_mul_ediv_right _ _ (by omega), h2]
    omega
  · rw [Int.add_comm, Int.add_mul_ediv_right _ _ (by omega), h2]
    omega

private theorem qRat_mkRat (v : Int) : qRat (mkRat v 1000000000) = mkRat v 1000000000 := by
  have hq := (Rat.mkRat_eq_iff (Rat.den_nz _) (by decide : (1000000000 : Nat) ≠ 0)).mp
    (Rat.mkRat_self (mkRat v 1000000000))
  have hd : (0 : Int) < ((mkRat v 1000000000).den : Int) := by
    have := Rat.den_pos (mkRat v 1000000000)
    omega
  unfold qRat
  simp only
  have hq' : (mkRat v 1000000000).num * 1000000000 = v * ((mkRat v 1000000000).den : Int) := by
    simpa using hq
  rw [hq', round_mul v _ hd]

/-- A matrix entry on the nine-decimal grid stays where it is
(`_fixed_point`). -/
public theorem qRat_fixed_point (r : Rat) : qRat (qRat r) = qRat r := qRat_mkRat _

public theorem qPt_fixed_point (p : Pt) : qPt (qPt p) = qPt p := by
  simp [qPt, qSp_fixed_point]

private theorem Seg.map_qPt (s : Seg) : (s.map qPt).map qPt = s.map qPt := by
  cases s <;> simp [Seg.map, qPt_fixed_point]

private theorem Subpath.map_qPt (s : Subpath) : (s.map qPt).map qPt = s.map qPt := by
  simp only [Subpath.map, qPt_fixed_point, Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro a _
  exact Seg.map_qPt a

private theorem Affine.quantize_fixed_point (m : Affine) : m.quantize.quantize = m.quantize := by
  simp [Affine.quantize, qRat_fixed_point]

private theorem Geom.quantize_fixed_point (g : Geom) : g.quantize.quantize = g.quantize := by
  cases g with
  | rect => simp [Geom.quantize, qSp_fixed_point]
  | ellipse => simp [Geom.quantize, qSp_fixed_point]
  | path subs =>
    simp only [Geom.quantize, Array.map_map, Geom.path.injEq]
    apply Array.map_congr_left
    intro a _
    exact Subpath.map_qPt a

private theorem Paint.quantize_fixed_point (p : Paint) : p.quantize.quantize = p.quantize := by
  cases p with
  | solid => rfl
  | gradient g =>
    cases g <;> simp [Paint.quantize, Gradient.quantize, qPt_fixed_point, qSp_fixed_point,
      Affine.quantize_fixed_point]

private theorem Fill.quantize_fixed_point (f : Fill) : f.quantize.quantize = f.quantize := by
  simp [Fill.quantize, Paint.quantize_fixed_point]

private theorem Stroke.quantize_fixed_point (st : Stroke) : st.quantize.quantize = st.quantize := by
  simp only [Stroke.quantize, Paint.quantize_fixed_point, qSp_fixed_point, qRat_fixed_point,
    Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro a _
  exact qSp_fixed_point a

private theorem Clip.quantize_fixed_point (c : Clip) : c.quantize.quantize = c.quantize := by
  simp [Clip.quantize, Geom.quantize_fixed_point]

public theorem Node.quantizeList_acc {L : Type} (ql : L → L) (acc : Array (Node L))
    (xs : List (Node L)) :
    Node.quantizeList ql acc xs = acc ++ Node.quantizeList ql #[] xs := by
  induction xs generalizing acc with
  | nil => simp [Node.quantizeList]
  | cons n rest ih =>
    simp only [Node.quantizeList]
    rw [ih, ih (#[].push _), Array.push_empty]
    simp

public theorem Node.recolorList_acc {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (acc : Array (Node L)) (xs : List (Node L)) :
    Node.recolorList f fl acc xs = acc ++ Node.recolorList f fl #[] xs := by
  induction xs generalizing acc with
  | nil => simp [Node.recolorList]
  | cons n rest ih =>
    simp only [Node.recolorList]
    rw [ih, ih (#[].push _), Array.push_empty]
    simp

public theorem Node.wordsList_append {L : Type} (text : L → String) (acc : Array String)
    (a b : List (Node L)) :
    Node.wordsList text acc (a ++ b) = Node.wordsList text (Node.wordsList text acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons n rest ih => exact ih _

private theorem Node.quantizeList_append {L : Type} (ql : L → L) (a b : List (Node L)) :
    Node.quantizeList ql #[] (a ++ b) = Node.quantizeList ql #[] a ++ Node.quantizeList ql #[] b := by
  induction a with
  | nil => simp [Node.quantizeList]
  | cons n rest ih =>
    simp only [List.cons_append, Node.quantizeList]
    rw [Node.quantizeList_acc, ih, Node.quantizeList_acc ql (#[].push _) rest, Array.append_assoc]

mutual

private theorem Node.quantizeOne_fixed_point {L : Type} (ql : L → L)
    (hl : ∀ l, ql (ql l) = ql l) :
    ∀ n : Node L, Node.quantizeOne ql (Node.quantizeOne ql n) = Node.quantizeOne ql n
  | .draw g fl st => by
    cases fl <;> cases st <;>
      simp [Node.quantizeOne, Geom.quantize_fixed_point, Fill.quantize_fixed_point,
        Stroke.quantize_fixed_point]
  | .group xf clips alpha kids => by
    simp only [Node.quantizeOne, Affine.quantize_fixed_point, Array.map_map]
    rw [Node.quantizeList_fixed_point ql hl kids.toList]
    congr 1
    apply Array.map_congr_left
    intro a _
    exact Clip.quantize_fixed_point a
  | .use k xf => by simp [Node.quantizeOne, Affine.quantize_fixed_point]
  | .stamp o xf fl st => by
    cases fl <;> cases st <;>
      simp [Node.quantizeOne, Affine.quantize_fixed_point, Fill.quantize_fixed_point,
        Stroke.quantize_fixed_point]
  | .image k xf => by simp [Node.quantizeOne, Affine.quantize_fixed_point]
  | .label l => by simp [Node.quantizeOne, hl]
  | .words w => by simp [Node.quantizeOne]

private theorem Node.quantizeList_fixed_point {L : Type} (ql : L → L)
    (hl : ∀ l, ql (ql l) = ql l) :
    ∀ xs : List (Node L),
      Node.quantizeList ql #[] (Node.quantizeList ql #[] xs).toList = Node.quantizeList ql #[] xs
  | [] => by simp [Node.quantizeList]
  | n :: rest => by
    simp only [Node.quantizeList]
    rw [Node.quantizeList_acc ql (#[].push _) rest, Array.push_empty, Array.toList_append,
      Node.quantizeList_append, Node.quantizeList_fixed_point ql hl rest]
    simp [Node.quantizeList, Node.quantizeOne_fixed_point ql hl n]

end

/-- **The print grid is a fixed point** (`_fixed_point`): quantizing a
quantized figure moves nothing — every length is already on the milli-point
grid `Sp.toPtString` prints, every matrix entry on the nine-decimal grid
`ratString` prints — so a read-back identity stated over quantized figures
holds of the figure a reader parses back. Labels by `ql`, itself idempotent. -/
public theorem Figure.quantize_fixed_point {L : Type} (ql : L → L) (hl : ∀ l, ql (ql l) = ql l)
    (fig : Figure L) : (fig.quantize ql).quantize ql = fig.quantize ql := by
  simp only [Figure.quantize, qPt_fixed_point, Array.map_map]
  rw [Node.quantizeList_fixed_point ql hl]
  congr 1
  · apply Array.map_congr_left
    intro a _
    simp only [Function.comp, Array.map_map]
    apply Array.map_congr_left
    intro s _
    exact Subpath.map_qPt s
  · apply Array.map_congr_left
    intro a _
    exact Node.quantizeList_fixed_point ql hl a.toList

/-! ## The ink box covers the ink -/

private theorem Box.leOpt_refl (a : Option Box) : Box.leOpt a a := by
  cases a with
  | none => trivial
  | some a => exact Box.le_refl a

private theorem Box.leOpt_trans {a b c : Option Box} (h1 : Box.leOpt a b) (h2 : Box.leOpt b c) :
    Box.leOpt a c := by
  cases a <;> cases b <;> cases c <;> simp_all [Box.leOpt]
  exact Box.le_trans h1 h2

private theorem Box.leOpt_joinOpt_left (a b : Option Box) : Box.leOpt a (Box.joinOpt a b) := by
  cases a <;> cases b <;> simp [Box.leOpt, Box.joinOpt, Box.le_refl, Box.le_join_left]

private theorem Box.leOpt_joinOpt_right (a b : Option Box) : Box.leOpt b (Box.joinOpt a b) := by
  cases a <;> cases b <;> simp [Box.leOpt, Box.joinOpt, Box.le_refl, Box.le_join_right]

private theorem Box.joinOpt_mono {a a' b b' : Option Box} (ha : Box.leOpt a a')
    (hb : Box.leOpt b b') : Box.leOpt (Box.joinOpt a b) (Box.joinOpt a' b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all [Box.leOpt, Box.joinOpt]
  · exact Box.le_trans hb (Box.le_join_right _ _)
  · exact Box.le_trans ha (Box.le_join_left _ _)
  · exact Box.join_le (Box.le_trans ha (Box.le_join_left _ _)) (Box.le_trans hb (Box.le_join_right _ _))

private theorem hullOf_list_acc {α : Type} (f : α → Option Box) (acc : Option Box) (xs : List α) :
    Box.leOpt acc (xs.foldl (fun acc x => Box.joinOpt acc (f x)) acc) := by
  induction xs generalizing acc with
  | nil => exact Box.leOpt_refl acc
  | cons x rest ih => exact Box.leOpt_trans (Box.leOpt_joinOpt_left acc (f x)) (ih _)

private theorem hullOf_list_mem {α : Type} (f : α → Option Box) (acc : Option Box) (xs : List α)
    (x : α) (h : x ∈ xs) :
    Box.leOpt (f x) (xs.foldl (fun acc x => Box.joinOpt acc (f x)) acc) := by
  induction xs generalizing acc with
  | nil => cases h
  | cons y rest ih =>
    cases h with
    | head => exact Box.leOpt_trans (Box.leOpt_joinOpt_right acc (f x)) (hullOf_list_acc f _ rest)
    | tail _ hm => exact ih _ hm

private theorem hullOf_list_mono {α : Type} (f g : α → Option Box) (hfg : ∀ x, Box.leOpt (f x) (g x))
    (a b : Option Box) (hab : Box.leOpt a b) (xs : List α) :
    Box.leOpt (xs.foldl (fun acc x => Box.joinOpt acc (f x)) a)
      (xs.foldl (fun acc x => Box.joinOpt acc (g x)) b) := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x rest ih => exact ih _ _ (Box.joinOpt_mono hab (hfg x))

private theorem hullOf_mem {α : Type} (f : α → Option Box) (xs : Array α) (x : α) (h : x ∈ xs) :
    Box.leOpt (f x) (hullOf f xs) := by
  unfold hullOf
  rw [← Array.foldl_toList]
  exact hullOf_list_mem f none xs.toList x (by simpa using h)

private theorem hullOf_mono {α : Type} (f g : α → Option Box) (hfg : ∀ x, Box.leOpt (f x) (g x))
    (xs : Array α) : Box.leOpt (hullOf f xs) (hullOf g xs) := by
  unfold hullOf
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact hullOf_list_mono f g hfg none none trivial xs.toList

private theorem ptsHull_ordered (acc : Option Box)
    (hacc : ∀ b, acc = some b → b.1.1 ≤ b.2.1 ∧ b.1.2 ≤ b.2.2) (ps : List Pt) :
    ∀ b, ptsHull acc ps = some b → b.1.1 ≤ b.2.1 ∧ b.1.2 ≤ b.2.2 := by
  induction ps generalizing acc with
  | nil => exact hacc
  | cons p rest ih =>
    apply ih
    intro b hb
    cases acc with
    | none =>
      simp only [Box.joinOpt, Option.some.injEq] at hb
      subst hb
      simp only [Box.point]
      exact ⟨Int.le_refl _, Int.le_refl _⟩
    | some a =>
      simp only [Box.joinOpt, Option.some.injEq] at hb
      subst hb
      have ha := hacc a rfl
      have hmin : ∀ x y z : Int, x ≤ z → min x y ≤ max z y := by intro x y z; omega
      simp only [Box.join, Box.point]
      exact ⟨hmin _ _ _ ha.1, hmin _ _ _ ha.2⟩

/-- A geometry's hull has its corners in order. -/
private theorem Geom.hull_ordered (g : Geom) :
    ∀ b, g.hull = some b → b.1.1 ≤ b.2.1 ∧ b.1.2 ≤ b.2.2 := by
  have hmm : ∀ x y : Int, min x y ≤ max x y := by intro x y; omega
  intro b hb
  cases g with
  | rect x y w h =>
    simp only [Geom.hull, Option.some.injEq] at hb
    subst hb
    exact ⟨hmm _ _, hmm _ _⟩
  | ellipse cx cy rx ry =>
    simp only [Geom.hull, Option.some.injEq] at hb
    subst hb
    exact ⟨hmm _ _, hmm _ _⟩
  | path subs =>
    exact ptsHull_ordered none (by simp) _ b hb

private theorem dilate_covers (b : Box) (d : Sp) (hd : 0 ≤ d) : Box.le b (Box.dilate b d) := by
  have h1 : ∀ x e : Int, 0 ≤ e → x - e ≤ x := by intro x e; omega
  have h2 : ∀ x e : Int, 0 ≤ e → x ≤ x + e := by intro x e; omega
  exact ⟨h1 _ _ hd, h1 _ _ hd, h2 _ _ hd, h2 _ _ hd⟩

private theorem Stroke.reach_nonneg (s : Stroke) : 0 ≤ s.reach := by
  have h : ∀ a b : Int, 0 ≤ max 0 (max a b) := by intro a b; omega
  exact h _ _

private theorem Mark.geomBox_le_inkBox (mk : Mark) :
    Box.leOpt (Mark.geomBox rasterUnit mk) (Mark.inkBox rasterUnit mk) := by
  cases mk with
  | paint ctm g fl st clips alphas =>
    simp only [Mark.geomBox, Mark.inkBox]
    cases hg : g.hull with
    | none => trivial
    | some b =>
      have ho := Geom.hull_ordered g b hg
      have hr : 0 ≤ (st.map Stroke.reach).getD 0 := by
        cases st with
        | none => exact Int.le_refl 0
        | some s => exact Stroke.reach_nonneg s
      exact Box.image_monotone ctm (dilate_covers b _ hr) ho.1 ho.2
  | raster ctm k w h => exact Box.le_refl _
  | shading g clips alphas => trivial

/-- **The ink box covers every mark's ink and every label's measured box**
(`_covers`): each mark's geometry dilated by its stroke's reach through its
frame, and each label's box through the frame it stands in, lies inside the
figure's ink box — quantified over the label measurement, as
`Ir.Pic.Picture.inkBbox_covers` is, because the model cannot measure a
label. -/
public theorem Figure.inkBox_covers {L : Type} (fig : Figure L) (labelBox : L → Option Box) :
    (∀ mk ∈ fig.marks, Box.leOpt (Mark.inkBox rasterUnit mk) (fig.inkBox labelBox)) ∧
    (∀ p ∈ fig.labels, Box.leOpt ((labelBox p.2).map (Box.image p.1)) (fig.inkBox labelBox)) := by
  refine ⟨fun mk hm => ?_, fun p hp => ?_⟩
  · exact Box.leOpt_trans (hullOf_mem _ _ mk hm) (Box.leOpt_joinOpt_left _ _)
  · exact Box.leOpt_trans (hullOf_mem (fun (p : Affine × L) => (labelBox p.2).map (Box.image p.1))
      _ p hp) (Box.leOpt_joinOpt_right _ _)

/-- **The ink box covers the geometry box** (`_covers`): reach is never
negative and an affine image grows with its box, so the box ink claims holds
the box layout reserves from geometry — whatever the labels measure. -/
public theorem Figure.inkBox_geom_covers {L : Type} (fig : Figure L) (labelBox : L → Option Box) :
    Box.leOpt fig.geomBox (fig.inkBox labelBox) :=
  Box.leOpt_trans (hullOf_mono _ _ Mark.geomBox_le_inkBox fig.marks) (Box.leOpt_joinOpt_left _ _)

/-! ## A cubic stays in its control hull -/

private theorem convex4_between (lo hi a b c d w0 w1 w2 w3 : Rat)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hs : w0 + w1 + w2 + w3 = 1)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) (hc : lo ≤ c ∧ c ≤ hi) (hd : lo ≤ d ∧ d ≤ hi) :
    lo ≤ w0 * a + w1 * b + w2 * c + w3 * d ∧ w0 * a + w1 * b + w2 * c + w3 * d ≤ hi := by
  have a0 := Rat.mul_le_mul_of_nonneg_left ha.1 hw0
  have a1 := Rat.mul_le_mul_of_nonneg_left ha.2 hw0
  have b0 := Rat.mul_le_mul_of_nonneg_left hb.1 hw1
  have b1 := Rat.mul_le_mul_of_nonneg_left hb.2 hw1
  have c0 := Rat.mul_le_mul_of_nonneg_left hc.1 hw2
  have c1 := Rat.mul_le_mul_of_nonneg_left hc.2 hw2
  have d0 := Rat.mul_le_mul_of_nonneg_left hd.1 hw3
  have d1 := Rat.mul_le_mul_of_nonneg_left hd.2 hw3
  have elo : lo = w0 * lo + w1 * lo + w2 * lo + w3 * lo := by
    rw [← Rat.add_mul, ← Rat.add_mul, ← Rat.add_mul, hs, Rat.one_mul]
  have ehi : hi = w0 * hi + w1 * hi + w2 * hi + w3 * hi := by
    rw [← Rat.add_mul, ← Rat.add_mul, ← Rat.add_mul, hs, Rat.one_mul]
  constructor <;> grind

private theorem bernstein (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (1 - t) * (1 - t) * (1 - t) ∧ 0 ≤ 3 * (1 - t) * (1 - t) * t ∧
    0 ≤ 3 * (1 - t) * t * t ∧ 0 ≤ t * t * t ∧
    (1 - t) * (1 - t) * (1 - t) + 3 * (1 - t) * (1 - t) * t + 3 * (1 - t) * t * t + t * t * t = 1 := by
  have hs : 0 ≤ 1 - t := by grind
  have hss := Rat.mul_nonneg hs hs
  have h3 : (0 : Rat) ≤ 3 := by decide
  refine ⟨Rat.mul_nonneg hss hs, Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg h3 hs) hs) h0,
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg h3 hs) h0) h0,
    Rat.mul_nonneg (Rat.mul_nonneg h0 h0) h0, by grind⟩

/-- **A cubic stays inside any box holding its control points**
(`_between`): at every `t` in `[0, 1]` the Bernstein weights are
non-negative and sum to one, so each coordinate of the curve's point is a
convex combination of the four controls' — between the box's edges. The
convex-hull fact `Geom.hull` and `Ir.Pic.PathSeg.box` bound a drawn curve
by. -/
public theorem cubicAt_between (p0 c1 c2 p1 : Pt) (b : Box) (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hp : ∀ p ∈ [p0, c1, c2, p1], Box.le (Box.point p) b) :
    (b.1.1 : Rat) ≤ (cubicAt p0 c1 c2 p1 t).1 ∧ (cubicAt p0 c1 c2 p1 t).1 ≤ (b.2.1 : Rat) ∧
    (b.1.2 : Rat) ≤ (cubicAt p0 c1 c2 p1 t).2 ∧ (cubicAt p0 c1 c2 p1 t).2 ≤ (b.2.2 : Rat) := by
  obtain ⟨w0, w1, w2, w3, hs⟩ := bernstein t h0 h1
  have cast : ∀ {p q : Int}, p ≤ q → (p : Rat) ≤ (q : Rat) := fun h => Rat.intCast_le_intCast.mpr h
  have pt : ∀ p ∈ [p0, c1, c2, p1],
      ((b.1.1 : Rat) ≤ p.1 ∧ (p.1 : Rat) ≤ b.2.1) ∧ ((b.1.2 : Rat) ≤ p.2 ∧ (p.2 : Rat) ≤ b.2.2) := by
    intro p hm
    have h := hp p hm
    simp only [Box.le, Box.point] at h
    exact ⟨⟨cast h.1, cast h.2.2.1⟩, ⟨cast h.2.1, cast h.2.2.2⟩⟩
  have q0 := pt p0 (by simp)
  have q1 := pt c1 (by simp)
  have q2 := pt c2 (by simp)
  have q3 := pt p1 (by simp)
  have hx := convex4_between _ _ _ _ _ _ _ _ _ _ w0 w1 w2 w3 hs q0.1 q1.1 q2.1 q3.1
  have hy := convex4_between _ _ _ _ _ _ _ _ _ _ w0 w1 w2 w3 hs q0.2 q1.2 q2.2 q3.2
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

end LeanTex.Core.Gfx
