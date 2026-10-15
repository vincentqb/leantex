module

/-! A PDF function of one input as the figure importer reads it (ISO 32000-2 §7.10): its value, and
the stops a gradient draws it at. -/

namespace LeanTex.Core.PdfGfx

/-- `t` held to `[d0, d1]`, as a function holds its input to its domain. -/
@[expose] public def clampTo (d0 d1 t : Rat) : Rat := max d0 (min d1 t)

/-- Each component of `c0` carried a fraction `v` of the way to `c1`'s. -/
@[expose] public def blend (c0 c1 : Array Rat) (v : Rat) : Array Rat :=
  (c0.zip c1).map fun (a, b) => a + v * (b - a)

/-- An exponential (§7.10.3): its domain, its two ends and its exponent. -/
public structure Expo where
  d0 : Rat
  d1 : Rat
  c0 : Array Rat
  c1 : Array Rat
  n : Rat

/-- A sampled function of one input (§7.10.2): domain, sample count, bits, outputs, encode and
decode pairs, and its decoded stream. -/
public structure Sampled where
  d0 : Rat
  d1 : Rat
  size : Nat
  bps : Nat
  nout : Nat
  e0 : Rat
  e1 : Rat
  decode : Array Rat
  raw : Option ByteArray

/-- A function alone or within a stitching: an exponential, a sampled function, or one the importer
does not read. -/
public inductive Piece where
  | expo (e : Expo)
  | sampled (s : Sampled)
  | unread

/-- A stitching (§7.10.4): its domain, bounds, encodings and functions. -/
public structure Stitch where
  d0 : Rat
  d1 : Rat
  bounds : Array Rat
  enc : Array Rat
  subs : Array Piece

/-- A function of one input as the importer reads it. -/
public inductive Fn where
  | piece (p : Piece)
  | stitch (s : Stitch)

/-- An exponential at `t`: exact where its exponent is a whole number up to 16, else linear. -/
@[expose] public def Expo.eval (e : Expo) (t : Rat) : Array Rat :=
  let t := clampTo e.d0 e.d1 t
  let tn : Rat := if e.n.den == 1 && 0 ≤ e.n && e.n ≤ 16 then t ^ e.n.num.toNat else t
  blend e.c0 e.c1 tn

/-- A sampled function at `t`, at 8 or 16 bits, linear between the two samples around `t`. -/
public def Sampled.eval (sm : Sampled) (t : Rat) : Option (Array Rat) := do
  let raw ← sm.raw
  guard ((sm.bps == 8 || sm.bps == 16) && sm.size ≥ 1)
  let t := clampTo sm.d0 sm.d1 t
  let e := if sm.d1 == sm.d0 then sm.e0 else sm.e0 + (t - sm.d0) * (sm.e1 - sm.e0) / (sm.d1 - sm.d0)
  let e := max 0 (min ((sm.size : Rat) - 1) e)
  let i0 := e.floor.toNat
  let i1 := min (sm.size - 1) (i0 + 1)
  let frac := e - (i0 : Rat)
  let maxV : Nat := 2 ^ sm.bps - 1
  let sample (i j : Nat) : Rat :=
    let k := i * sm.nout + j
    let v := if sm.bps == 8 then (raw[k]?.getD 0).toNat
      else (raw[2 * k]?.getD 0).toNat * 256 + (raw[2 * k + 1]?.getD 0).toNat
    let x : Rat := mkRat v maxV
    let d0 := sm.decode[2 * j]?.getD 0
    let d1 := sm.decode[2 * j + 1]?.getD 1
    d0 + x * (d1 - d0)
  return (Array.range sm.nout).map fun j => sample i0 j + frac * (sample i1 j - sample i0 j)

/-- A piece at `t`; one the importer does not read is nothing. -/
@[expose] public def Piece.eval : Piece → Rat → Option (Array Rat)
  | .expo e, t => some (e.eval t)
  | .sampled s, t => s.eval t
  | .unread, _ => none

/-- Where a stitching's piece `k` starts (§7.10.4): its domain's start for
the first, the bound before it for the others. -/
@[expose] public def Stitch.lo (s : Stitch) (k : Nat) : Rat :=
  if k == 0 then s.d0 else s.bounds[k - 1]?.getD s.d0

/-- Where a stitching's piece `k` ends: the bound after it, its domain's end
for the last. -/
@[expose] public def Stitch.hi (s : Stitch) (k : Nat) : Rat :=
  if k ≥ s.bounds.size then s.d1 else s.bounds[k]?.getD s.d1

/-- The encoding of piece `k`: where its start and its end carry to. -/
@[expose] public def Stitch.e0 (s : Stitch) (k : Nat) : Rat := s.enc[2 * k]?.getD 0

@[expose] public def Stitch.e1 (s : Stitch) (k : Nat) : Rat := s.enc[2 * k + 1]?.getD 1

/-- An input carried into piece `k` by its encoding. -/
@[expose] public def Stitch.carry (s : Stitch) (k : Nat) (t : Rat) : Rat :=
  if s.hi k == s.lo k then s.e0 k
  else s.e0 k + (t - s.lo k) * (s.e1 k - s.e0 k) / (s.hi k - s.lo k)

/-- The piece of a stitching for `t`; `left` takes, at an inner bound, the piece that ends there. -/
@[expose] public def Stitch.index (s : Stitch) (t : Rat) (left : Bool) : Nat :=
  let t' := clampTo s.d0 s.d1 t
  min (s.bounds.toList.filter fun b => if left && s.d0 < t && t ≤ s.d1 then b < t' else b ≤ t').length
    (s.subs.size - 1)

/-- A function of one input at `t` (§7.10). -/
@[expose] public def Fn.eval : Fn → Rat → Bool → Option (Array Rat)
  | .piece p, t, _ => p.eval t
  | .stitch s, t, left =>
    if s.subs.size = 0 then none else
    let k := s.index t left
    (s.subs[k]?.getD .unread).eval (s.carry k (clampTo s.d0 s.d1 t))

/-- The points of `xs` strictly inside `(s0, s1)`. -/
@[expose] public def inside (s0 s1 : Rat) (xs : Array Rat) : Array Rat :=
  xs.filter fun x => s0 < x && x < s1

/-- An exponential's stops over `[s0, s1]`, exact where its exponent is 1, else 17 points. -/
@[expose] public def Expo.stops (e : Expo) (s0 s1 : Rat) : Array Rat × Bool :=
  if e.n = 1 then (#[s0] ++ inside s0 s1 #[e.d0, e.d1] ++ #[s1], true)
  else ((Array.range 17).map fun (k : Nat) => s0 + (s1 - s0) * mkRat k 16, false)

/-- A sampled function's stops over `[s0, s1]`: its samples and where its
domain holds its input. -/
@[expose] public def Sampled.stops (sm : Sampled) (s0 s1 : Rat) : Array Rat × Bool :=
  let pts := if sm.e1 == sm.e0 || sm.size > 4096 then #[] else
    (Array.range sm.size).map fun (i : Nat) => sm.d0 + ((i : Rat) - sm.e0) * (sm.d1 - sm.d0) / (sm.e1 - sm.e0)
  (#[s0] ++ inside s0 s1 (pts ++ #[sm.d0, sm.d1]) ++ #[s1],
    (sm.bps == 8 || sm.bps == 16) && sm.size ≤ 4096 && sm.e1 != sm.e0)

@[expose] public def Piece.stops : Piece → Rat → Rat → Array Rat × Bool
  | .expo e, s0, s1 => e.stops s0 s1
  | .sampled s, s0, s1 => s.stops s0 s1
  | .unread, s0, s1 => (#[s0, s1], false)

/-- The stops a stitching's piece `k` sets inside `(t0, t1)`, carried back through its encoding, and
whether they are exact. -/
@[expose] public def Stitch.back (s : Stitch) (t0 t1 : Rat) (k : Nat) : Array Rat × Bool :=
  let r := (s.subs[k]?.getD .unread).stops (min (s.e0 k) (s.e1 k)) (max (s.e0 k) (s.e1 k))
  (inside t0 t1 (if s.e1 k == s.e0 k then #[] else
      r.1.map fun u => s.lo k + (u - s.e0 k) * (s.hi k - s.lo k) / (s.e1 k - s.e0 k)),
    r.2)

/-- A stitching laid out as §7.10.4 lays one: one bound fewer than its functions, bounds in order. -/
@[expose] public def Stitch.wellFormed (s : Stitch) : Bool :=
  s.subs.size == s.bounds.size + 1 &&
    decide ((s.d0 :: s.bounds.toList ++ [s.d1]).Pairwise fun a b => a ≤ b)

/-- Where a function's stops stand over `[t0, t1]`, and whether linear interpolation between them is
the function itself (§7.10). -/
@[expose] public def Fn.stops : Fn → Rat → Rat → Array Rat × Bool
  | .piece p, t0, t1 => p.stops t0 t1
  | .stitch s, t0, t1 =>
    let backs := (Array.range s.subs.size).map (s.back t0 t1)
    (#[t0] ++ inside t0 t1 (s.bounds ++ #[s.d0, s.d1]) ++ backs.flatMap (·.1) ++ #[t1],
      s.wellFormed && backs.all (·.2))

/-- Each component of `a` carried a fraction `s` of the way to `b`'s. -/
@[expose] public def lerpArr (a b : Array Rat) (s : Rat) : Array Rat :=
  (a.zip b).map fun (x, y) => x + s * (y - x)

/-- Whether every piece is an exponential. -/
@[expose] public def Fn.expoOnly : Fn → Bool
  | .piece (.expo _) => true
  | .piece _ => false
  | .stitch s => s.subs.all fun | .expo _ => true | _ => false

/-- `g` is the line between its values at `a` and `b`, over `[a, b]`. -/
def AffOn (g : Rat → Rat) (a b : Rat) : Prop :=
  ∀ t, a ≤ t → t ≤ b → g t = g a + (t - a) / (b - a) * (g b - g a)

private theorem lerp_between (x y s : Rat) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    min x y ≤ x + s * (y - x) ∧ x + s * (y - x) ≤ max x y := by
  by_cases hxy : x ≤ y
  · have p1 : 0 ≤ s * (y - x) := Rat.mul_nonneg h0 (by grind)
    have p2 : 0 ≤ (1 - s) * (y - x) := Rat.mul_nonneg (by grind) (by grind)
    grind
  · have p1 : 0 ≤ s * (x - y) := Rat.mul_nonneg h0 (by grind)
    have p2 : 0 ≤ (1 - s) * (x - y) := Rat.mul_nonneg (by grind) (by grind)
    grind

private theorem frac_unit (a b t : Rat) (hab : a < b) (h1 : a ≤ t) (h2 : t ≤ b) :
    0 ≤ (t - a) / (b - a) ∧ (t - a) / (b - a) ≤ 1 := by
  have hba : 0 < b - a := by grind
  have hm : (t - a) / (b - a) * (b - a) = t - a := Rat.div_mul_cancel (by grind)
  constructor
  · apply Classical.byContradiction
    intro hs
    have : (t - a) / (b - a) * (b - a) < 0 := (Rat.mul_neg_iff_of_pos_right hba).mpr (by grind)
    grind
  · apply Classical.byContradiction
    intro hs
    have : 0 < ((t - a) / (b - a) - 1) * (b - a) := Rat.mul_pos (by grind) hba
    grind

private theorem clamp_lerp (d0 d1 x y s : Rat) (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (k0 : ¬ (min x y < d0 ∧ d0 < max x y)) (k1 : ¬ (min x y < d1 ∧ d1 < max x y)) :
    clampTo d0 d1 (x + s * (y - x)) = clampTo d0 d1 x + s * (clampTo d0 d1 y - clampTo d0 d1 x) := by
  have hv := lerp_between x y s h0 h1
  unfold clampTo
  generalize hv' : x + s * (y - x) = v at hv ⊢
  grind

private theorem back_between (lo hi e0 e1 a b d : Rat) (hhl : hi ≠ lo) (he : e1 ≠ e0) (hab : a < b)
    (hd : min (e0 + (a - lo) * (e1 - e0) / (hi - lo)) (e0 + (b - lo) * (e1 - e0) / (hi - lo)) < d ∧
      d < max (e0 + (a - lo) * (e1 - e0) / (hi - lo)) (e0 + (b - lo) * (e1 - e0) / (hi - lo))) :
    a < lo + (d - e0) * (hi - lo) / (e1 - e0) ∧ lo + (d - e0) * (hi - lo) / (e1 - e0) < b := by
  generalize hua : e0 + (a - lo) * (e1 - e0) / (hi - lo) = ua at hd
  generalize hub : e0 + (b - lo) * (e1 - e0) / (hi - lo) = ub at hd
  generalize hq : (hi - lo) / (e1 - e0) = q
  have hε : e1 - e0 ≠ 0 := by grind
  have hq0 : q ≠ 0 := by
    intro h0
    rw [← hq, Rat.div_def] at h0
    have := Rat.mul_inv_cancel _ hε
    grind
  have hts : lo + (d - e0) * (hi - lo) / (e1 - e0) = lo + (d - e0) * q := by
    rw [← hq, Rat.div_def, Rat.div_def]; grind
  have ia : a - (lo + (d - e0) * q) = ua * q - d * q := by
    rw [← hua, ← hq, Rat.div_def, Rat.div_def]
    grind
  have ib : b - (lo + (d - e0) * q) = ub * q - d * q := by
    rw [← hub, ← hq, Rat.div_def, Rat.div_def]
    grind
  rw [hts]
  by_cases hneg : q < 0
  · have hn : 0 < -q := by grind
    by_cases h : ua < ub
    · have x1 := Rat.mul_lt_mul_of_pos_right (show ua < d by grind) hn
      have x2 := Rat.mul_lt_mul_of_pos_right (show d < ub by grind) hn
      grind
    · have x1 := Rat.mul_lt_mul_of_pos_right (show ub < d by grind) hn
      have x2 := Rat.mul_lt_mul_of_pos_right (show d < ua by grind) hn
      grind
  · have hpos : 0 < q := by grind
    by_cases h : ua < ub
    · have x1 := Rat.mul_lt_mul_of_pos_right (show ua < d by grind) hpos
      have x2 := Rat.mul_lt_mul_of_pos_right (show d < ub by grind) hpos
      grind
    · have x1 := Rat.mul_lt_mul_of_pos_right (show ub < d by grind) hpos
      have x2 := Rat.mul_lt_mul_of_pos_right (show d < ua by grind) hpos
      grind

private theorem affOn_id (a b : Rat) (hab : a < b) : AffOn (fun t => t) a b := by
  intro t _ _
  have := Rat.div_mul_cancel (a := t - a) (b := b - a) (by grind)
  grind

private theorem affOn_clamp (d0 d1 a b : Rat) (w : Rat → Rat) (hab : a < b) (hw : AffOn w a b)
    (k0 : ¬ (min (w a) (w b) < d0 ∧ d0 < max (w a) (w b)))
    (k1 : ¬ (min (w a) (w b) < d1 ∧ d1 < max (w a) (w b))) :
    AffOn (fun t => clampTo d0 d1 (w t)) a b := by
  intro t h1 h2
  obtain ⟨hs0, hs1⟩ := frac_unit a b t hab h1 h2
  show clampTo d0 d1 (w t) = clampTo d0 d1 (w a) + _ * (clampTo d0 d1 (w b) - clampTo d0 d1 (w a))
  rw [hw t h1 h2]
  exact clamp_lerp d0 d1 (w a) (w b) _ hs0 hs1 k0 k1

private theorem affOn_carry (s : Stitch) (k : Nat) (a b : Rat) (w : Rat → Rat) (hw : AffOn w a b) :
    AffOn (fun t => s.carry k (w t)) a b := by
  intro t h1 h2
  simp only [Stitch.carry]
  split
  · grind
  · rw [hw t h1 h2]; grind

private theorem lerpArr_blend (c0 c1 : Array Rat) (p q s : Rat) :
    lerpArr (blend c0 c1 p) (blend c0 c1 q) s = blend c0 c1 (p + s * (q - p)) := by
  apply Array.ext
  · simp [lerpArr, blend]
  · intro i h1 h2
    simp [lerpArr, blend]
    grind

private theorem expo_eval_one (e : Expo) (hn : e.n = 1) (t : Rat) :
    e.eval t = blend e.c0 e.c1 (clampTo e.d0 e.d1 t) := by
  simp [Expo.eval, hn]

private theorem expo_stops_exact (e : Expo) (s0 s1 : Rat) (h : (e.stops s0 s1).2 = true) : e.n = 1 := by
  unfold Expo.stops at h
  split at h
  · assumption
  · simp at h

private theorem mem_inside {s0 s1 x : Rat} {xs : Array Rat} :
    x ∈ inside s0 s1 xs ↔ x ∈ xs ∧ s0 < x ∧ x < s1 := by
  simp [inside, Array.mem_filter]

private theorem filter_sorted_index (P : Rat → Bool) (hP : ∀ y z, y ≤ z → P z = true → P y = true) :
    ∀ (l : List Rat), l.Pairwise (· ≤ ·) → ∀ i (h : i < l.length), (P l[i] = true ↔ i < (l.filter P).length)
  | [], _, i, h => absurd h (by simp)
  | y :: ys, hl, i, h => by
    rw [List.pairwise_cons] at hl
    by_cases hy : P y = true
    · rw [List.filter_cons_of_pos hy, List.length_cons]
      cases i with
      | zero => simp [hy]
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [filter_sorted_index P hP ys hl.2 j (by simp at h; omega)]
        omega
    · rw [List.filter_cons_of_neg hy]
      have hall : ∀ z ∈ ys, P z = false := fun z hz => by
        cases hpz : P z
        · rfl
        · exact absurd (hP y z (hl.1 z hz) hpz) hy
      have hnil : ys.filter P = [] := List.filter_eq_nil_iff.mpr (fun z hz => by simp [hall z hz])
      rw [hnil]
      cases i with
      | zero => simp [hy]
      | succ j => simp [hall _ (List.getElem_mem _)]


private theorem clamp_moves (d0 d1 a b : Rat) (hD : d0 ≤ d1)
    (g0 : ¬ (a < d0 ∧ d0 < b)) (g1 : ¬ (a < d1 ∧ d1 < b)) (h : clampTo d0 d1 a ≠ clampTo d0 d1 b) :
    d0 ≤ a ∧ b ≤ d1 := by
  unfold clampTo at h
  grind

private theorem clamp_of_mem (d0 d1 x : Rat) (h0 : d0 ≤ x) (h1 : x ≤ d1) : clampTo d0 d1 x = x := by
  unfold clampTo
  grind

private theorem clamp_le_iff_step (d0 d1 a b x β : Rat) (hβ : d0 ≤ β ∧ β ≤ d1) (hab : a < b)
    (hax : a ≤ x) (hxb : x < b) (g : ¬ (a < β ∧ β < b)) :
    (β ≤ clampTo d0 d1 x ↔ β ≤ clampTo d0 d1 a) := by
  unfold clampTo
  grind

private theorem clamp_le_iff_left (d0 d1 a b β : Rat) (hβ : d0 ≤ β ∧ β ≤ d1) (hab : a < b)
    (g : ¬ (a < β ∧ β < b)) :
    ((if (decide (d0 < b) && decide (b ≤ d1)) = true then decide (β < clampTo d0 d1 b)
      else decide (β ≤ clampTo d0 d1 b)) = decide (β ≤ clampTo d0 d1 a)) := by
  unfold clampTo
  split <;> simp only [decide_eq_decide] <;> grind

private theorem min_max_ne {x y d : Rat} (h : min x y < d ∧ d < max x y) : x ≠ y := by
  intro e
  subst e
  grind

public theorem stitch_exact (f : Fn) (t0 t1 a b t : Rat) (hf : f.expoOnly = true)
    (hex : (f.stops t0 t1).2 = true) (hab : a < b) (h0 : t0 ≤ a) (h1 : b ≤ t1)
    (hgap : ∀ p ∈ (f.stops t0 t1).1, ¬ (a < p ∧ p < b)) (hta : a ≤ t) (htb : t < b) :
    ∃ A B, f.eval a false = some A ∧ f.eval b true = some B ∧
      f.eval t false = some (lerpArr A B ((t - a) / (b - a))) := by
  cases f with
  | piece p =>
    cases p with
    | expo e =>
      have hn : e.n = 1 := expo_stops_exact e t0 t1 hex
      have gap : ∀ d, (d = e.d0 ∨ d = e.d1) → ¬ (a < d ∧ d < b) := by
        intro d hd hdab
        apply hgap d _ hdab
        simp only [Fn.stops, Piece.stops, Expo.stops, hn, ↓reduceIte, Array.mem_append, mem_inside]
        rcases hd with rfl | rfl <;> simp <;> grind
      refine ⟨blend e.c0 e.c1 (clampTo e.d0 e.d1 a), blend e.c0 e.c1 (clampTo e.d0 e.d1 b), ?_, ?_, ?_⟩
      · simp [Fn.eval, Piece.eval, expo_eval_one e hn]
      · simp [Fn.eval, Piece.eval, expo_eval_one e hn]
      · simp only [Fn.eval, Piece.eval, expo_eval_one e hn, lerpArr_blend]
        have := affOn_clamp e.d0 e.d1 a b (fun t => t) hab (affOn_id a b hab)
          (by have := gap e.d0 (Or.inl rfl); grind) (by have := gap e.d1 (Or.inr rfl); grind) t hta
          (Rat.le_of_lt htb)
        simp only at this
        rw [this]
    | sampled _ => simp [Fn.expoOnly] at hf
    | unread => simp [Fn.expoOnly] at hf
  | stitch s =>
    simp only [Fn.stops, Bool.and_eq_true] at hex hgap
    obtain ⟨hwf, hall⟩ := hex
    simp only [Stitch.wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwf
    obtain ⟨hsize, hpw⟩ := hwf
    have hpw' := hpw
    rw [List.pairwise_append, List.pairwise_cons] at hpw'
    obtain ⟨⟨hD0, hB⟩, -, hBD1⟩ := hpw'
    have hD : s.d0 ≤ s.d1 := hBD1 s.d0 (by simp) s.d1 (by simp)
    have hBD : ∀ y ∈ s.bounds.toList, s.d0 ≤ y ∧ y ≤ s.d1 :=
      fun y hy => ⟨hD0 y hy, hBD1 y (by simp [hy]) s.d1 (by simp)⟩
    have mem : ∀ y, y ∈ inside t0 t1 (s.bounds ++ #[s.d0, s.d1]) ∨
        (∃ k, k < s.subs.size ∧ y ∈ (s.back t0 t1 k).1) →
        y ∈ #[t0] ++ inside t0 t1 (s.bounds ++ #[s.d0, s.d1]) ++
          ((Array.range s.subs.size).map (s.back t0 t1)).flatMap (·.1) ++ #[t1] := by
      intro y hy
      simp only [Array.mem_append, Array.mem_flatMap, Array.mem_map, Array.mem_range]
      rcases hy with hy | ⟨k, hk, hy⟩
      · exact Or.inl (Or.inl (Or.inr hy))
      · exact Or.inl (Or.inr ⟨_, ⟨k, hk, rfl⟩, hy⟩)
    have gIn : ∀ y ∈ s.bounds ++ #[s.d0, s.d1], ¬ (a < y ∧ y < b) := fun y hy hyab =>
      hgap y (mem y (Or.inl (mem_inside.mpr ⟨hy, by grind, by grind⟩))) hyab
    have gB : ∀ y ∈ s.bounds.toList, ¬ (a < y ∧ y < b) :=
      fun y hy => gIn y (Array.mem_append.mpr (Or.inl (by simpa using hy)))
    have gD0 : ¬ (a < s.d0 ∧ s.d0 < b) := gIn s.d0 (by simp)
    have gD1 : ¬ (a < s.d1 ∧ s.d1 < b) := gIn s.d1 (by simp)
    have gK : ∀ k, k < s.subs.size → ∀ y ∈ (s.back t0 t1 k).1, ¬ (a < y ∧ y < b) :=
      fun k hk y hy hyab => hgap y (mem y (Or.inr ⟨k, hk, hy⟩)) hyab
    have hallK : ∀ k, k < s.subs.size → (s.back t0 t1 k).2 = true := by
      intro k hk
      rw [Array.all_eq_true] at hall
      have := hall k (by simpa using hk)
      simpa using this
    let K := (s.bounds.toList.filter fun β => decide (β ≤ clampTo s.d0 s.d1 a)).length
    have hKle : K ≤ s.bounds.size := by
      have := List.length_filter_le (fun β => decide (β ≤ clampTo s.d0 s.d1 a)) s.bounds.toList
      simpa using this
    have idx_t : ∀ x, a ≤ x → x < b → s.index x false = K := by
      intro x hax hxb
      simp only [Stitch.index, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have : (s.bounds.toList.filter fun β => decide (β ≤ clampTo s.d0 s.d1 x)) =
          s.bounds.toList.filter fun β => decide (β ≤ clampTo s.d0 s.d1 a) := by
        apply List.filter_congr
        intro β hβ
        simp only [decide_eq_decide]
        exact clamp_le_iff_step s.d0 s.d1 a b x β (hBD β hβ) hab hax hxb (gB β hβ)
      rw [this]
      omega
    have idx_b : s.index b true = K := by
      simp only [Stitch.index, Bool.true_and]
      have : (s.bounds.toList.filter fun β => if (decide (s.d0 < b) && decide (b ≤ s.d1)) = true
            then decide (β < clampTo s.d0 s.d1 b) else decide (β ≤ clampTo s.d0 s.d1 b)) =
          s.bounds.toList.filter fun β => decide (β ≤ clampTo s.d0 s.d1 a) := by
        apply List.filter_congr
        intro β hβ
        exact clamp_le_iff_left s.d0 s.d1 a b β (hBD β hβ) hab (gB β hβ)
      rw [this]
      omega
    have hKlt : K < s.subs.size := by omega
    obtain ⟨E, hE⟩ : ∃ E, s.subs[K]? = some (.expo E) := by
      simp only [Fn.expoOnly, Array.all_eq_true] at hf
      have := hf K hKlt
      revert this
      rw [Array.getElem?_eq_getElem hKlt]
      cases s.subs[K] with
      | expo E => intro _; exact ⟨E, rfl⟩
      | sampled _ => simp
      | unread => simp
    have hEn : E.n = 1 := by
      have := hallK K hKlt
      simp only [Stitch.back, hE, Option.getD_some, Piece.stops] at this
      exact expo_stops_exact E _ _ this
    have hn0 : s.subs.size ≠ 0 := by omega
    have ev : ∀ x left, s.index x left = K →
        Fn.eval (.stitch s) x left = some (blend E.c0 E.c1 (clampTo E.d0 E.d1 (s.carry K (clampTo s.d0 s.d1 x)))) := by
      intro x left hx
      simp [Fn.eval, hn0, hx, hE, Piece.eval, expo_eval_one E hEn]
    have hc : AffOn (clampTo s.d0 s.d1) a b := affOn_clamp s.d0 s.d1 a b (fun t => t) hab
      (affOn_id a b hab) (by grind) (by grind)
    have hu : AffOn (fun x => s.carry K (clampTo s.d0 s.d1 x)) a b :=
      affOn_carry s K a b (clampTo s.d0 s.d1) hc
    have noKink : ∀ d, (d = E.d0 ∨ d = E.d1) →
        ¬ (min (s.carry K (clampTo s.d0 s.d1 a)) (s.carry K (clampTo s.d0 s.d1 b)) < d ∧
          d < max (s.carry K (clampTo s.d0 s.d1 a)) (s.carry K (clampTo s.d0 s.d1 b))) := by
      intro d hd hmid
      have hmove : clampTo s.d0 s.d1 a ≠ clampTo s.d0 s.d1 b := by
        intro heq
        rw [heq] at hmid
        exact min_max_ne hmid rfl
      have hDa := clamp_moves s.d0 s.d1 a b hD gD0 gD1 hmove
      have hca : clampTo s.d0 s.d1 a = a :=
        clamp_of_mem _ _ _ hDa.1 (Rat.le_trans (Rat.le_of_lt hab) hDa.2)
      have hcb : clampTo s.d0 s.d1 b = b :=
        clamp_of_mem _ _ _ (Rat.le_trans hDa.1 (Rat.le_of_lt hab)) hDa.2
      rw [hca, hcb] at hmid
      have hPdown : ∀ y z : Rat, y ≤ z → decide (z ≤ clampTo s.d0 s.d1 a) = true →
          decide (y ≤ clampTo s.d0 s.d1 a) = true := by
        intro y z hyz hz
        simp only [decide_eq_true_eq] at hz ⊢
        exact Rat.le_trans hyz hz
      have hlo : s.lo K ≤ a := by
        unfold Stitch.lo
        split
        · grind
        · rename_i hK0
          have hK0' : K ≠ 0 := by simpa using hK0
          have hK1 : K - 1 < s.bounds.toList.length := by simp; omega
          have hP := (filter_sorted_index _ hPdown s.bounds.toList hB (K - 1) hK1).mpr (by omega)
          simp only [decide_eq_true_eq, hca] at hP
          rw [Array.getElem?_eq_getElem (by simp at hK1; omega), Option.getD_some]
          simpa using hP
      have hhi : b ≤ s.hi K := by
        unfold Stitch.hi
        split
        · grind
        · rename_i hKb
          have hKb' : K < s.bounds.size := by simpa using hKb
          have hK1 : K < s.bounds.toList.length := by simp; omega
          have hP := filter_sorted_index _ hPdown s.bounds.toList hB K hK1
          have hnot : ¬ (s.bounds.toList[K] ≤ clampTo s.d0 s.d1 a) := by
            intro h
            have := hP.mp (by simpa using h)
            omega
          rw [hca] at hnot
          have hg := gB s.bounds.toList[K] (List.getElem_mem _)
          rw [Array.getElem?_eq_getElem (by simp at hK1; omega), Option.getD_some]
          have e : s.bounds[K] = s.bounds.toList[K] := by simp
          grind
      have hne : s.hi K ≠ s.lo K := by grind
      have he : s.e1 K ≠ s.e0 K := by
        intro heq
        simp only [Stitch.carry, beq_iff_eq, hne, ↓reduceIte, heq] at hmid
        grind
      simp only [Stitch.carry, beq_iff_eq, hne, ↓reduceIte] at hmid
      have hbt := back_between (s.lo K) (s.hi K) (s.e0 K) (s.e1 K) a b d hne he hab hmid
      have hin : min (s.e0 K) (s.e1 K) < d ∧ d < max (s.e0 K) (s.e1 K) := by
        have fa := frac_unit (s.lo K) (s.hi K) a (by grind) hlo (by grind)
        have fb := frac_unit (s.lo K) (s.hi K) b (by grind) (by grind) hhi
        have la := lerp_between (s.e0 K) (s.e1 K) _ fa.1 fa.2
        have lb := lerp_between (s.e0 K) (s.e1 K) _ fb.1 fb.2
        have ea : s.e0 K + (a - s.lo K) * (s.e1 K - s.e0 K) / (s.hi K - s.lo K) =
            s.e0 K + (a - s.lo K) / (s.hi K - s.lo K) * (s.e1 K - s.e0 K) := by grind
        have eb : s.e0 K + (b - s.lo K) * (s.e1 K - s.e0 K) / (s.hi K - s.lo K) =
            s.e0 K + (b - s.lo K) / (s.hi K - s.lo K) * (s.e1 K - s.e0 K) := by grind
        grind
      apply gK K hKlt _ _ hbt
      simp only [Stitch.back, hE, Option.getD_some, Piece.stops, Expo.stops, hEn, ↓reduceIte,
        mem_inside, beq_iff_eq, he]
      refine ⟨Array.mem_map.mpr ⟨d, ?_, rfl⟩, by grind, by grind⟩
      simp only [Array.mem_append, mem_inside]
      rcases hd with rfl | rfl <;> simp <;> grind
    have aff := affOn_clamp E.d0 E.d1 a b (fun x => s.carry K (clampTo s.d0 s.d1 x)) hab hu
      (noKink E.d0 (Or.inl rfl)) (noKink E.d1 (Or.inr rfl))
    refine ⟨_, _, ev a false (idx_t a (Rat.le_refl) hab), ev b true idx_b, ?_⟩
    rw [ev t false (idx_t t hta htb), lerpArr_blend]
    have := aff t hta (Rat.le_of_lt htb)
    simp only at this
    rw [this]

end LeanTex.Core.PdfGfx
