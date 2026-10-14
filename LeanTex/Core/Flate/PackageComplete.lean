module

import all LeanTex.Core.Flate.PackageKraft
import all LeanTex.Core.Flate.PackageLengths

namespace LeanTex.Core.Flate.PackageMerge

/-- Weights that never decrease. -/
def Ascending (w : Array Nat) : Prop :=
  ∀ i j, i ≤ j → j < w.size → w[i]?.getD 0 ≤ w[j]?.getD 0

theorem pairWeights_get_exact (w : Array Nat) :
    (pairWeights w).size = w.size / 2 ∧
      ∀ j < w.size / 2, (pairWeights w)[j]?.getD 0 = w[2 * j]?.getD 0 + w[2 * j + 1]?.getD 0 := by
  let P (i : Nat) (out : Array Nat) : Prop :=
    out.size = i ∧ ∀ j < i, out[j]?.getD 0 = w[2 * j]?.getD 0 + w[2 * j + 1]?.getD 0
  unfold pairWeights
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact P (P (w.size / 2)) _ 0 (w.size / 2) _ (Nat.zero_le _)
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ _ (fun _ h => h)
  intro i _ _ out h
  change P (i + 1) (out.push (w[2 * i]?.getD 0 + w[2 * i + 1]?.getD 0))
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  rw [Array.getElem?_push, h.1]
  by_cases hji : j < i
  · rw [ite_eq_right (show j ≠ i by omega)]
    exact h.2 j hji
  · have he : j = i := by omega
    subst he
    simp

theorem pairWeights_ascending (w : Array Nat) (hw : Ascending w) : Ascending (pairWeights w) := by
  obtain ⟨hs, hg⟩ := pairWeights_get_exact w
  intro i j hij hj
  rw [hs] at hj
  rw [hg i (by omega), hg j hj]
  have h1 := hw (2 * i) (2 * j) (by omega) (by omega)
  have h2 := hw (2 * i + 1) (2 * j + 1) (by omega) (by omega)
  omega

/-- What `merge`'s output holds after `a` leaves and `b` packages, over ascending inputs: its
weights ascend and stay below the heads still to come, a package was taken only below the next
leaf, and every leaf a prefix holds weighs at most that prefix's last weight. -/
structure MergeFor (items pairs : Array Nat) (w : Array Nat) (f : Array Bool) (a b : Nat) :
    Prop where
  bounds : a ≤ items.size ∧ b ≤ pairs.size
  sizes : w.size = a + b ∧ f.size = a + b
  leaves : f.toList.count true = a
  front : ∀ i < w.size, (a < items.size → w[i]?.getD 0 ≤ items[a]?.getD 0) ∧
    (b < pairs.size → w[i]?.getD 0 ≤ pairs[b]?.getD 0)
  asc : Ascending w
  greedy : ∀ t ≤ f.size, 0 < (f.toList.take t).count false →
    (f.toList.take t).count true < items.size →
    pairs[(f.toList.take t).count false - 1]?.getD 0 < items[(f.toList.take t).count true]?.getD 0
  bound : ∀ t ≤ f.size, ∀ j < (f.toList.take t).count true,
    items[j]?.getD 0 ≤ w[t - 1]?.getD 0

private theorem take_push_le {α : Type} (f : Array α) (x : α) (t : Nat) (ht : t ≤ f.size) :
    (f.push x).toList.take t = f.toList.take t := by
  rw [Array.toList_push, List.take_append_of_le_length (by simpa using ht)]

private theorem take_push_full {α : Type} (f : Array α) (x : α) :
    (f.push x).toList.take (f.size + 1) = f.toList ++ [x] := by
  rw [Array.toList_push]
  apply List.take_of_length_le
  simp

private theorem push_get_le (w : Array Nat) (x : Nat) (i : Nat) (hi : i < w.size) :
    (w.push x)[i]?.getD 0 = w[i]?.getD 0 := by
  rw [Array.getElem?_push, ite_eq_right (show i ≠ w.size by omega)]

private theorem push_get_last (w : Array Nat) (x : Nat) : (w.push x)[w.size]?.getD 0 = x := by
  rw [Array.getElem?_push, ite_eq_left rfl]
  rfl

private theorem bool_count (xs : List Bool) : xs.count true + xs.count false = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp <;> omega

private theorem false_count (f : Array Bool) (a : Nat) (h : f.toList.count true = a) :
    f.toList.count false = f.size - a := by
  have := bool_count f.toList
  simp only [Array.length_toList] at this
  omega

private theorem take_size_exact {α : Type} (f : Array α) : f.toList.take f.size = f.toList :=
  List.take_of_length_le (by simp)

private theorem mergeFor_push (items pairs : Array Nat) (w : Array Nat) (f : Array Bool) (a b : Nat) (hm : MergeFor items pairs w f a b)
    (x : Nat) (leaf : Bool) (a' b' : Nat)
    (hfront : ∀ i < w.size, w[i]?.getD 0 ≤ x)
    (hnext : (a' < items.size → x ≤ items[a']?.getD 0) ∧ (b' < pairs.size → x ≤ pairs[b']?.getD 0))
    (hheads : ∀ i < w.size, (a' < items.size → w[i]?.getD 0 ≤ items[a']?.getD 0) ∧
      (b' < pairs.size → w[i]?.getD 0 ≤ pairs[b']?.getD 0))
    (hcount : a' = a + (if leaf then 1 else 0) ∧ b' = b + (if leaf then 0 else 1))
    (hbounds : a' ≤ items.size ∧ b' ≤ pairs.size)
    (hgreedy : 0 < b' → a' < items.size → pairs[b' - 1]?.getD 0 < items[a']?.getD 0)
    (hbound : ∀ j < a', items[j]?.getD 0 ≤ x) :
    MergeFor items pairs (w.push x) (f.push leaf) a' b' := by
  have hws := hm.sizes.1
  have hfs := hm.sizes.2
  have hfull : (f.push leaf).toList.take (f.size + 1) = f.toList ++ [leaf] := take_push_full f leaf
  have hb : f.toList.count false = b := by rw [false_count f a hm.leaves]; omega
  have hct : (f.toList ++ [leaf]).count true = a' := by
    rw [List.count_append, hm.leaves, hcount.1]
    cases leaf <;> simp
  have hcf : (f.toList ++ [leaf]).count false = b' := by
    rw [List.count_append, hb, hcount.2]
    cases leaf <;> simp
  have hsum : a' + b' = a + b + 1 := by
    rw [hcount.1, hcount.2]
    cases leaf <;> simp <;> omega
  refine ⟨hbounds, ⟨by simp only [Array.size_push]; omega, by simp only [Array.size_push]; omega⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hct
  · intro i hi'
    simp only [Array.size_push] at hi'
    by_cases hlt : i < w.size
    · rw [push_get_le w x i hlt]
      exact hheads i hlt
    · have he : i = w.size := by omega
      subst he
      rw [push_get_last]
      exact hnext
  · intro i j hij hj
    simp only [Array.size_push] at hj
    by_cases hjw : j < w.size
    · rw [push_get_le w x i (by omega), push_get_le w x j hjw]
      exact hm.asc i j hij hjw
    · have he : j = w.size := by omega
      subst he
      rw [push_get_last]
      by_cases hiw : i < w.size
      · rw [push_get_le w x i hiw]
        exact hfront i hiw
      · have he : i = w.size := by omega
        subst he
        rw [push_get_last]
        exact Nat.le_refl _
  · intro t ht hpos hlt
    simp only [Array.size_push] at ht
    by_cases htf : t ≤ f.size
    · rw [take_push_le f leaf t htf] at hpos hlt ⊢
      exact hm.greedy t htf hpos hlt
    · have he : t = f.size + 1 := by omega
      subst he
      simp only [hfull, hct, hcf] at hpos hlt ⊢
      exact hgreedy hpos hlt
  · intro t ht j hj
    simp only [Array.size_push] at ht
    by_cases htf : t ≤ f.size
    · rw [take_push_le f leaf t htf] at hj
      by_cases ht0 : t = 0
      · subst ht0
        simp at hj
      · rw [push_get_le w x (t - 1) (by omega)]
        exact hm.bound t htf j hj
    · have he : t = f.size + 1 := by omega
      subst he
      simp only [hfull, hct] at hj
      rw [show f.size + 1 - 1 = w.size by omega, push_get_last]
      exact hbound j hj

theorem merge_for (items pairs : Array Nat) (hi : Ascending items) (hp : Ascending pairs) :
    MergeFor items pairs (merge items pairs).1 (merge items pairs).2 items.size pairs.size := by
  let P (i : Nat) (s : Array Nat × Array Bool × Nat × Nat) : Prop :=
    MergeFor items pairs s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ s.2.2.1 + s.2.2.2 = i
  unfold merge
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:items.size + pairs.size]
    (Array.mkEmpty _, Array.mkEmpty _, 0, 0) _ :
      Id (Array Nat × Array Bool × Nat × Nat)) = result
  have hp' : P (items.size + pairs.size) result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P (items.size + pairs.size)) _ 0 _ _ (Nat.zero_le _)
      ?_ _ (fun _ h => h)
    · refine ⟨⟨⟨Nat.zero_le _, Nat.zero_le _⟩, ⟨by simp, by simp⟩, by simp, ?_, ?_, ?_, ?_⟩, rfl⟩
      · intro i hi'
        simp at hi'
      · intro i j _ hj
        simp at hj
      · intro t ht
        simp at ht
        subst ht
        simp
      · intro t ht j hj
        simp at ht
        subst ht
        simp at hj
    intro i _ hi' s hs
    rcases hs with ⟨hm, hab⟩
    have ha := hm.bounds.1
    have hb := hm.bounds.2
    have hws := hm.sizes.1
    by_cases hleaf : s.2.2.1 < items.size ∧
        (pairs.size ≤ s.2.2.2 ∨ items[s.2.2.1]?.getD 0 ≤ pairs[s.2.2.2]?.getD 0)
    · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hleaf]
      change P (i + 1) (s.1.push _, s.2.1.push true, s.2.2.1 + 1, s.2.2.2)
      refine ⟨mergeFor_push items pairs s.1 s.2.1 s.2.2.1 s.2.2.2 hm
        (items[s.2.2.1]?.getD 0) true (s.2.2.1 + 1) s.2.2.2 ?_ ?_ ?_ (by simp) ⟨by omega, hb⟩
        ?_ ?_, show s.2.2.1 + 1 + s.2.2.2 = i + 1 by omega⟩
      · intro k hk
        exact (hm.front k hk).1 hleaf.1
      · refine ⟨fun h => hi _ _ (by omega) h, fun h => ?_⟩
        rcases hleaf.2 with h' | h'
        · omega
        · exact h'
      · intro k hk
        refine ⟨fun h => Nat.le_trans ((hm.front k hk).1 hleaf.1) (hi _ _ (by omega) h),
          fun h => (hm.front k hk).2 h⟩
      · intro hpos hlt
        have hg := hm.greedy s.2.1.size (Nat.le_refl _)
        rw [take_size_exact, hm.leaves] at hg
        have hcf : s.2.1.toList.count false = s.2.2.2 := by
          rw [false_count s.2.1 _ hm.leaves]
          have := hm.sizes.2
          omega
        rw [hcf] at hg
        exact Nat.lt_of_lt_of_le (hg hpos hleaf.1) (hi _ _ (by omega) hlt)
      · intro j hj
        exact hi _ _ (by omega) hleaf.1
    · have hpair : s.2.2.2 < pairs.size := by omega
      have hless : pairs[s.2.2.2]?.getD 0 < items[s.2.2.1]?.getD 0 ∨ items.size ≤ s.2.2.1 := by
        by_cases hlt : s.2.2.1 < items.size
        · left
          have : ¬ items[s.2.2.1]?.getD 0 ≤ pairs[s.2.2.2]?.getD 0 := fun h =>
            hleaf ⟨hlt, Or.inr h⟩
          omega
        · right; omega
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hleaf, ite_false,
        hpair, ite_true]
      change P (i + 1) (s.1.push _, s.2.1.push false, s.2.2.1, s.2.2.2 + 1)
      refine ⟨mergeFor_push items pairs s.1 s.2.1 s.2.2.1 s.2.2.2 hm
        (pairs[s.2.2.2]?.getD 0) false s.2.2.1 (s.2.2.2 + 1) ?_ ?_ ?_ (by simp) ⟨ha, by omega⟩
        ?_ ?_, show s.2.2.1 + (s.2.2.2 + 1) = i + 1 by omega⟩
      · intro k hk
        exact (hm.front k hk).2 hpair
      · refine ⟨fun h => ?_, fun h => hp _ _ (by omega) h⟩
        rcases hless with h' | h'
        · omega
        · omega
      · intro k hk
        exact ⟨fun h => (hm.front k hk).1 h,
          fun h => Nat.le_trans ((hm.front k hk).2 hpair) (hp _ _ (by omega) h)⟩
      · intro _ hlt
        rcases hless with h' | h'
        · simpa using h'
        · omega
      · intro j hj
        have hw0 : 0 < s.1.size := by omega
        have hb' := hm.bound s.2.1.size (Nat.le_refl _) j (by rw [take_size_exact, hm.leaves]; exact hj)
        rw [show s.2.1.size - 1 = s.1.size - 1 by have := hm.sizes.2; omega] at hb'
        exact Nat.le_trans hb' ((hm.front (s.1.size - 1) (by omega)).2 hpair)
  rcases hp' with ⟨hm, hab⟩
  have := hm.bounds
  have ha : result.2.2.1 = items.size := by omega
  have hb : result.2.2.2 = pairs.size := by omega
  rw [ha, hb] at hm
  exact hm

/-- Each package level's weights and provenance flags, the leaves' level first. -/
def level (items : Array Nat) : Nat → Array Nat × Array Bool
  | 0 => (items, Array.replicate items.size true)
  | k + 1 => merge items (pairWeights (level items k).1)

theorem levels_level_exact (items : Array Nat) (limit : Nat) (hl : 0 < limit) :
    ∀ k < limit, (levels items limit)[k]?.getD #[] = (level items k).2 := by
  let P (i : Nat) (s : Array Nat × Array Bool × Array (Array Bool)) : Prop :=
    s.1 = (level items (i - 1)).1 ∧ s.2.1 = (level items (i - 1)).2 ∧ s.2.2.size = i - 1 ∧
      ∀ k < i - 1, s.2.2[k]?.getD #[] = (level items k).2
  unfold levels
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:limit]
    (items, Array.replicate items.size true, (#[] : Array (Array Bool))) _ :
      Id (Array Nat × Array Bool × Array (Array Bool))) = result
  have hp : P limit result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P limit) _ 1 limit _ hl
      ⟨rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ _ (fun _ h => h)
    intro i hi _ s hs
    rcases hs with ⟨h1, h2, h3, h4⟩
    change P (i + 1)
      ((merge items (pairWeights s.1)).1, (merge items (pairWeights s.1)).2, s.2.2.push s.2.1)
    have hk : i = (i - 1) + 1 := by omega
    have hsucc : level items i = merge items (pairWeights (level items (i - 1)).1) := by
      conv => lhs; rw [hk]
      rfl
    refine ⟨by simp only [Nat.add_sub_cancel, hsucc, h1], by simp only [Nat.add_sub_cancel, hsucc, h1],
      by simp only [Array.size_push, h3, Nat.add_sub_cancel]; omega, ?_⟩
    intro k hk'
    simp only [Nat.add_sub_cancel] at hk'
    rw [Array.getElem?_push, h3]
    by_cases he : k = i - 1
    · subst he
      simp [h2]
    · rw [ite_eq_right he]
      exact h4 k (by omega)
  rcases hp with ⟨_, h2, h3, h4⟩
  intro k hk
  rw [Array.getElem?_push, h3]
  by_cases he : k = limit - 1
  · subst he
    simp [h2]
  · rw [ite_eq_right he]
    exact h4 k (by omega)

/-- What every package level holds over ascending leaves: ascending weights beside their flags,
every leaf once, and every leaf a prefix holds at most that prefix's last weight. -/
structure LevelShape (items : Array Nat) (w : Array Nat) (f : Array Bool) : Prop where
  asc : Ascending w
  size_eq : w.size = f.size
  leaves : f.toList.count true = items.size
  bound : ∀ t ≤ f.size, ∀ j < (f.toList.take t).count true, items[j]?.getD 0 ≤ w[t - 1]?.getD 0

private theorem take_replicate_true (n t : Nat) (ht : t ≤ n) :
    ((Array.replicate n true).toList.take t).count true = t := by
  simp [List.take_replicate, Nat.min_eq_left ht]

theorem level_shape (items : Array Nat) (hi : Ascending items) :
    ∀ k, LevelShape items (level items k).1 (level items k).2
  | 0 => by
    refine ⟨hi, by simp [level], by simp [level], ?_⟩
    intro t ht j hj
    simp only [level, Array.size_replicate] at ht hj
    rw [take_replicate_true _ _ ht] at hj
    exact hi j (t - 1) (by omega) (by omega)
  | k + 1 => by
    have hm := merge_for items (pairWeights (level items k).1) hi
      (pairWeights_ascending _ (level_shape items hi k).asc)
    show LevelShape items (merge items (pairWeights (level items k).1)).1
      (merge items (pairWeights (level items k).1)).2
    exact ⟨hm.asc, by rw [hm.sizes.1, hm.sizes.2], hm.leaves, hm.bound⟩

private theorem count_take_le (f : List Bool) (b : Bool) (t : Nat) : (f.take t).count b ≤ f.count b :=
  (List.take_sublist t f).count_le b

private theorem nested_core (items W' W : Array Nat) (F' F : Array Bool) (t : Nat)
    (hs : LevelShape items W' F')
    (hm : MergeFor items (pairWeights W') W F items.size (pairWeights W').size)
    (ht : t ≤ F.size) :
    (F'.toList.take (2 * (F.toList.take t).count false)).count true ≤
      (F.toList.take t).count true := by
  have hpw := pairWeights_get_exact W'
  have hpf : (F.toList.take t).count false ≤ W'.size / 2 := by
    have := count_take_le F.toList false t
    rw [false_count F _ hm.leaves, hm.sizes.2] at this
    have := hpw.1
    omega
  have hg := hm.greedy t ht
  generalize ha : (F.toList.take t).count true = a at hg ⊢
  generalize hp : (F.toList.take t).count false = p at hg hpf ⊢
  by_cases hp0 : p = 0
  · subst hp0
    simp
  by_cases hla : items.size ≤ a
  · have := count_take_le F'.toList true (2 * p)
    rw [hs.leaves] at this
    omega
  have hg' := hg (by omega) (by omega)
  rw [hpw.2 (p - 1) (by omega), show 2 * (p - 1) + 1 = 2 * p - 1 by omega] at hg'
  by_cases hle : (F'.toList.take (2 * p)).count true ≤ a
  · exact hle
  · exfalso
    have hb := hs.bound (2 * p) (by rw [← hs.size_eq]; omega) a (by omega)
    omega

/-- The leaves the next finer level selects for a level's packages are among the leaves that
level selects: package-merge's selections nest. -/
theorem level_nested (items : Array Nat) (hi : Ascending items) (k t : Nat)
    (ht : t ≤ (level items (k + 1)).2.size) :
    ((level items k).2.toList.take (2 * ((level items (k + 1)).2.toList.take t).count false)).count
        true ≤ ((level items (k + 1)).2.toList.take t).count true :=
  nested_core items (level items k).1 (level items (k + 1)).1 (level items k).2
    (level items (k + 1)).2 t (level_shape items hi k)
    (merge_for items (pairWeights (level items k).1) hi
      (pairWeights_ascending _ (level_shape items hi k).asc)) ht

private theorem sum_shift {α : Type} (xs : List α) (f g : α → Nat) (coin : Nat)
    (h : ∀ s ∈ xs, g s + coin = f s) :
    (xs.map g).sum + xs.length * coin = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have hs := h s (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem addBits_mass_exact (sorted lens : Array Nat) (leaves limit i : Nat)
    (hn : sorted.toList.Nodup) (hv : ∀ s ∈ sorted.toList, s < lens.size)
    (hl : leaves ≤ sorted.size) (hi : i < limit)
    (hw : ∀ s ∈ sorted.toList.take leaves, lens[s]?.getD 0 = i) :
    mass limit sorted (addBits sorted lens leaves) + leaves * 2 ^ (limit - 1 - i) =
      mass limit sorted lens := by
  have he := addBits_exact sorted lens leaves hn hv hl
  have hd : ∀ s ∈ sorted.toList.take leaves, ∀ t ∈ sorted.toList.drop leaves, s ≠ t :=
    (List.nodup_append.mp (by simpa only [List.take_append_drop] using hn)).2.2
  have hp := sum_shift (sorted.toList.take leaves)
    (fun s => 2 ^ (limit - lens[s]?.getD 0))
    (fun s => 2 ^ (limit - (addBits sorted lens leaves)[s]?.getD 0))
    (2 ^ (limit - 1 - i)) (by
      intro s hs
      rw [he.2 s, ite_eq_left hs, hw s hs, show limit - (i + 1) = limit - 1 - i by omega,
        show limit - i = (limit - 1 - i) + 1 by omega, Nat.pow_succ]
      omega)
  have ht :
      ((sorted.toList.drop leaves).map fun s =>
        2 ^ (limit - (addBits sorted lens leaves)[s]?.getD 0)) =
      ((sorted.toList.drop leaves).map fun s => 2 ^ (limit - lens[s]?.getD 0)) := by
    apply List.map_congr_left
    intro s hs
    have hno : s ∉ sorted.toList.take leaves := fun hm => hd s hm s hs rfl
    simp only [he.2 s, ite_eq_right hno, Nat.add_zero]
  simp only [List.length_take, Array.length_toList, Nat.min_eq_left hl] at hp
  rw [mass_split limit sorted (addBits sorted lens leaves) leaves,
    mass_split limit sorted lens leaves, ht]
  omega

/-- The backtrace after `i` levels: the credit balances exactly, and every leaf the next level
selects has a code exactly `i` bits long. -/
private structure TraceExact (sorted : Array Nat) (size : Nat) (levels : Array (Array Bool))
    (i : Nat) (lens : Array Nat) (take : Nat) : Prop where
  size_eq : lens.size = size
  enough : i < levels.size → take ≤ capacity sorted.size (levels.size - 1 - i)
  more : take = 0 ∨ i < levels.size
  credit : mass levels.size sorted lens + (sorted.size - 1) * 2 ^ levels.size =
    sorted.size * 2 ^ levels.size + take * 2 ^ (levels.size - 1 - i)
  shape : i < levels.size → ∀ j < (selected (levels[levels.size - 1 - i]?.getD #[]) take).1,
    lens[sorted[j]?.getD 0]?.getD 0 = i

private theorem mass_whole (n L : Nat) (hn : 0 < n) : n * 2 ^ L = (n - 1) * 2 ^ L + 2 ^ L := by
  calc n * 2 ^ L = ((n - 1) + 1) * 2 ^ L := congrArg (· * 2 ^ L) (by omega)
    _ = _ := by rw [Nat.add_mul, Nat.one_mul]

/-- With nested selections, the backtrace's codes fill the code space exactly. -/
theorem backtrace_mass_exact (sorted : Array Nat) (size : Nat) (levels : Array (Array Bool))
    (hn : sorted.toList.Nodup) (hv : ∀ s ∈ sorted.toList, s < size)
    (hpos : 1 < sorted.size) (hl : 0 < levels.size) (hfit : sorted.size ≤ 2 ^ levels.size)
    (hlevels : ∀ k < levels.size, LevelFor sorted.size k (levels[k]?.getD #[]))
    (hnest : ∀ k, k + 1 < levels.size → ∀ t ≤ (levels[k + 1]?.getD #[]).size,
      (selected (levels[k]?.getD #[]) (2 * (selected (levels[k + 1]?.getD #[]) t).2)).1 ≤
        (selected (levels[k + 1]?.getD #[]) t).1) :
    mass levels.size sorted (backtrace sorted size levels) = 2 ^ levels.size := by
  let P (i : Nat) (s : Array Nat × Nat) : Prop := TraceExact sorted size levels i s.1 s.2
  let Q (s : Array Nat × Nat) : Prop := mass levels.size sorted s.1 = 2 ^ levels.size
  have hzero : ∀ s : Nat, (Array.replicate size 0)[s]?.getD 0 = 0 := by
    intro s
    by_cases he : s < size <;> simp [he]
  have hwhole := mass_whole sorted.size levels.size (by omega)
  unfold backtrace
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:levels.size]
    (Array.replicate size 0, 2 * sorted.size - 2) _ : Id (Array Nat × Nat)) = result
  have hq : Q result := by
    rw [← hres]
    apply Progress.forIn_range_exact P Q _ 0 levels.size _ (Nat.zero_le _) ?_ ?_ ?_
    · refine ⟨by simp, ?_, Or.inr hl, ?_, ?_⟩
      · intro _
        simpa using capacity_solution_between sorted.size levels.size hl hfit
      · have hm : mass levels.size sorted (Array.replicate size 0) =
            sorted.size * 2 ^ levels.size := by
          simp [mass, hzero, List.map_const', List.sum_replicate_nat]
        have he : (sorted.size - 1) * 2 ^ levels.size =
            (2 * sorted.size - 2) * 2 ^ (levels.size - 1) := by
          have hsize : levels.size = (levels.size - 1) + 1 := by omega
          have hn' : 2 * sorted.size - 2 = (sorted.size - 1) * 2 := by omega
          conv => lhs; rw [hsize, Nat.pow_succ]
          rw [hn']
          simp only [Nat.mul_assoc, Nat.mul_comm]
        dsimp only
        rw [hm, Nat.sub_zero, ← he, Nat.add_comm]
      · intro _ j _
        exact hzero _
    · intro i _ hi s hs
      have hk : levels.size - 1 - i < levels.size := by omega
      have hf := hlevels _ hk
      have ht : s.2 ≤ (levels[levels.size - 1 - i]?.getD #[]).size := by
        rw [hf.1]
        exact hs.enough hi
      obtain ⟨hcount, hleaves, hpairs⟩ :=
        selected_counts_exact (levels[levels.size - 1 - i]?.getD #[]) s.2 ht
      rw [hf.2.1] at hleaves
      generalize hsel : selected (levels[levels.size - 1 - i]?.getD #[]) s.2 = sel at *
      obtain ⟨a, p⟩ := sel
      dsimp only at hcount hleaves hpairs
      have hv' : ∀ x ∈ sorted.toList, x < s.1.size := by simpa only [hs.size_eq] using hv
      have hadd := addBits_exact sorted s.1 a hn hv' hleaves
      have hshape := hs.shape hi
      rw [hsel] at hshape
      have hw : ∀ x ∈ sorted.toList.take a, s.1[x]?.getD 0 = i := by
        intro x hx
        obtain ⟨j, hj, hx⟩ := List.mem_take_iff_getElem.mp hx
        have hj' : j < sorted.size := by simp only [Array.length_toList] at hj; omega
        have := hshape j (by omega)
        rw [getElem?_pos sorted j hj', Option.getD_some] at this
        rw [← hx]
        simpa using this
      have hmass := addBits_mass_exact sorted s.1 a levels.size i hn hv' hleaves hi hw
      have hlast : i + 1 = levels.size → p = 0 := by
        intro he
        have hk0 : levels.size - 1 - i = 0 := by omega
        have h3 := hf.2.2
        rw [hk0] at h3 hpairs
        simp only [ite_true] at h3
        omega
      have hcredit := selected_credit levels.size i a p hi hlast
      rw [hcount] at hcredit
      have hnew : mass levels.size sorted (addBits sorted s.1 a) +
          (sorted.size - 1) * 2 ^ levels.size =
          sorted.size * 2 ^ levels.size + 2 * p * 2 ^ (levels.size - 1 - (i + 1)) := by
        have := hs.credit
        omega
      simp only [Id.run]
      by_cases hz : 2 * p = 0
      · simp only [beq_iff_eq, hz, ite_true]
        change mass levels.size sorted (addBits sorted s.1 a) = 2 ^ levels.size
        rw [hz, Nat.zero_mul, Nat.add_zero, hwhole] at hnew
        omega
      · simp only [beq_iff_eq, hz, ite_false]
        refine ⟨by rw [hadd.1, hs.size_eq], ?_, ?_, hnew, ?_⟩
        · intro hnext
          have hk0 : levels.size - 1 - i ≠ 0 := by omega
          rw [hf.2.2, ite_eq_right hk0] at hpairs
          rw [show levels.size - 1 - i - 1 = levels.size - 1 - (i + 1) by omega] at hpairs
          omega
        · by_cases he : i + 1 = levels.size
          · exact Or.inl (by simp [hlast he])
          · exact Or.inr (by omega)
        · intro hnext j hj
          have hidx : levels.size - 1 - (i + 1) + 1 = levels.size - 1 - i := by omega
          have hnest' := hnest (levels.size - 1 - (i + 1)) (by omega) s.2 (by rw [hidx]; exact ht)
          rw [hidx, hsel] at hnest'
          have hja : j < a := Nat.lt_of_lt_of_le hj hnest'
          have hj' : j < sorted.size := by omega
          have hmem : sorted[j]?.getD 0 ∈ sorted.toList.take a := by
            rw [getElem?_pos sorted j hj', Option.getD_some]
            exact List.mem_take_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩
          rw [hadd.2, ite_eq_left hmem, hw _ hmem]
    · intro s hs
      have hz : s.2 = 0 := hs.more.resolve_right (by omega)
      have hc := hs.credit
      rw [hz, Nat.zero_mul, Nat.add_zero, hwhole] at hc
      change mass levels.size sorted s.1 = 2 ^ levels.size
      omega
  exact hq

/-- Package-merge over two or more live symbols fills the code space: the Kraft sum of its
lengths is exactly `2 ^ limit`. -/
theorem lengths_mass_exact (freqs : Array Nat) (limit : Nat) (hl : 0 < limit)
    (hfit : freqs.size ≤ 2 ^ limit) (hn : 1 < (live freqs).size) :
    mass limit (live freqs) (lengths freqs limit) = 2 ^ limit := by
  let le : Nat → Nat → Bool := fun a b => freqs[a]?.getD 0 ≤ freqs[b]?.getD 0
  let sorted := ((live freqs).toList.mergeSort le).toArray
  let items := sorted.map fun s => freqs[s]?.getD 0
  have hlen : lengths freqs limit = backtrace sorted freqs.size (levels items limit) := by
    change (if (live freqs).size == 0 then Array.replicate freqs.size 0 else
      if (live freqs).size == 1 then
        (Array.replicate freqs.size 0).set! ((live freqs)[0]?.getD 0) 1 else
        backtrace sorted freqs.size (levels items limit)) = _
    have h0 : ((live freqs).size == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    have h1 : ((live freqs).size == 1) = false := by simp only [beq_eq_false_iff_ne]; omega
    rw [h0, h1]
    rfl
  have hp : sorted.Perm (live freqs) := Array.Perm.of_toList_perm (by
    simpa only [sorted, List.toList_toArray] using List.mergeSort_perm (live freqs).toList le)
  have hnd : sorted.toList.Nodup := hp.symm.toList.nodup (live_nodup freqs)
  have hv : ∀ s ∈ sorted.toList, s < freqs.size := fun s hs =>
    ((live_mem freqs s).mp (hp.toList.mem_iff.mp hs)).1
  have hsize : sorted.size = (live freqs).size := hp.size_eq
  have hss : (live freqs).size ≤ freqs.size := by
    simpa [live] using
      (Array.size_filter_le (xs := Array.range freqs.size) (p := fun s => freqs[s]?.getD 0 > 0))
  have hasc : Ascending items := by
    have hpw := List.pairwise_mergeSort (le := le)
      (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega)
      (live freqs).toList
    intro i j hij hj
    have hj' : j < sorted.size := by simpa [items] using hj
    by_cases he : i = j
    · subst he
      exact Nat.le_refl _
    · have := List.pairwise_iff_getElem.mp hpw i j (by simpa [sorted] using (by omega : i < sorted.size))
        (by simpa [sorted] using hj') (by omega)
      simp only [le, decide_eq_true_eq] at this
      simp only [items, Array.getElem?_map, getElem?_pos sorted i (by omega),
        getElem?_pos sorted j hj', Option.map_some, Option.getD_some]
      simpa [sorted] using this
  have hlev := levels_exact items limit hl
  have hlv := levels_level_exact items limit hl
  have hitems : items.size = sorted.size := by simp [items]
  have hnest : ∀ k, k + 1 < (levels items limit).size →
      ∀ t ≤ ((levels items limit)[k + 1]?.getD #[]).size,
      (selected ((levels items limit)[k]?.getD #[])
          (2 * (selected ((levels items limit)[k + 1]?.getD #[]) t).2)).1 ≤
        (selected ((levels items limit)[k + 1]?.getD #[]) t).1 := by
    intro k hk t ht
    rw [hlev.1] at hk
    have hf1 := hlev.2 (k + 1) hk
    have hf0 := hlev.2 k (by omega)
    rw [hlv (k + 1) hk] at ht hf1 ⊢
    rw [hlv k (by omega)] at hf0 ⊢
    have hs1 := selected_exact _ t ht
    have hpf : (selected (level items (k + 1)).2 t).2 ≤ ((level items (k + 1)).2).toList.count false := by
      rw [hs1.2]
      exact count_take_le _ false t
    rw [hf1.2.2, ite_eq_right (by omega), Nat.add_sub_cancel] at hpf
    have hs0 := selected_exact (level items k).2 (2 * (selected (level items (k + 1)).2 t).2)
      (by rw [hf0.1]; omega)
    rw [hs0.1, hs1.1, hs1.2]
    exact level_nested items hasc k t ht
  have hm := backtrace_mass_exact sorted freqs.size (levels items limit) hnd hv
    (by omega) (by rw [hlev.1]; exact hl) (by rw [hlev.1]; omega)
    (fun k hk => by have := hlev.2 k (by rw [hlev.1] at hk; exact hk); rwa [hitems] at this)
    hnest
  rw [hlev.1] at hm
  rw [hlen]
  have he := (hp.toList.map (fun s => 2 ^ (limit - (backtrace sorted freqs.size
    (levels items limit))[s]?.getD 0))).sum_nat
  simpa only [mass, he] using hm

theorem lengths_empty_exact (freqs : Array Nat) (limit : Nat) (h0 : (live freqs).size = 0) :
    lengths freqs limit = Array.replicate freqs.size 0 := by
  change (if (live freqs).size == 0 then Array.replicate freqs.size 0 else _) = _
  rw [show ((live freqs).size == 0) = true by simp [h0]]
  rfl

theorem lengths_single_exact (freqs : Array Nat) (limit : Nat) (h1 : (live freqs).size = 1) :
    lengths freqs limit = (Array.replicate freqs.size 0).set! ((live freqs)[0]?.getD 0) 1 := by
  change (if (live freqs).size == 0 then Array.replicate freqs.size 0 else
    if (live freqs).size == 1 then
      (Array.replicate freqs.size 0).set! ((live freqs)[0]?.getD 0) 1 else _) = _
  rw [show ((live freqs).size == 0) = false by simp [h1],
    show ((live freqs).size == 1) = true by simp [h1]]
  rfl

theorem live_single_lt (freqs : Array Nat) (h1 : (live freqs).size = 1) :
    (live freqs)[0]?.getD 0 < freqs.size :=
  ((live_mem freqs _).mp (by
    rw [getElem?_pos (live freqs) 0 (by omega), Option.getD_some]
    exact Array.getElem_mem_toList _)).1

end LeanTex.Core.Flate.PackageMerge
