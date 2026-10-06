module

import all LeanTex.Core.Flate.PackageMerge

namespace LeanTex.Core.Flate.PackageMerge

theorem pairWeights_size_exact (weights : Array Nat) :
    (pairWeights weights).size = weights.size / 2 := by
  unfold pairWeights
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact (fun i (out : Array Nat) => out.size = i)
    (fun out => out.size = weights.size / 2) _ 0 (weights.size / 2) _
    (Nat.zero_le _) rfl
  · intro i _ _ out h
    change (out.push _).size = i + 1
    simpa only [Array.size_push] using congrArg (· + 1) h
  · intro out h
    exact h

/-- The actual merge consumes every leaf and package exactly once. It
needs no assumption about weights or their ordering. -/
theorem merge_counts_exact (items pairs : Array Nat) :
    (merge items pairs).1.size = items.size + pairs.size ∧
    (merge items pairs).2.size = items.size + pairs.size ∧
    (merge items pairs).2.toList.count true = items.size ∧
    (merge items pairs).2.toList.count false = pairs.size := by
  let P (i : Nat) (s : Array Nat × Array Bool × Nat × Nat) : Prop :=
    s.2.2.1 ≤ items.size ∧ s.2.2.2 ≤ pairs.size ∧
    s.2.2.1 + s.2.2.2 = i ∧ s.1.size = i ∧ s.2.1.size = i ∧
    s.2.1.toList.count true = s.2.2.1 ∧
    s.2.1.toList.count false = s.2.2.2
  unfold merge
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:items.size + pairs.size]
    (Array.mkEmpty _, Array.mkEmpty _, 0, 0) _ :
      Id (Array Nat × Array Bool × Nat × Nat)) = result
  have hp : P (items.size + pairs.size) result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P (items.size + pairs.size)) _ 0 _ _
      (Nat.zero_le _) (by simp [P]) _ (fun _ h => h)
    intro i _ hi s hs
    rcases hs with ⟨ha, hb, hab, hw, hf, ht, hn⟩
    by_cases hleaf : s.2.2.1 < items.size ∧
        (pairs.size ≤ s.2.2.2 ∨ items[s.2.2.1]?.getD 0 ≤ pairs[s.2.2.2]?.getD 0)
    · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hleaf]
      change P (i + 1) (s.1.push _, s.2.1.push true, s.2.2.1 + 1, s.2.2.2)
      dsimp only [P]
      refine ⟨by omega, hb, by omega, ?_, ?_, ?_, ?_⟩ <;> simp [hw, hf, ht, hn]
    · have hpair : s.2.2.2 < pairs.size := by omega
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hleaf, ite_false,
        hpair, ite_true]
      change P (i + 1) (s.1.push _, s.2.1.push false, s.2.2.1, s.2.2.2 + 1)
      dsimp only [P]
      refine ⟨ha, by omega, by omega, ?_, ?_, ?_, ?_⟩ <;> simp [hw, hf, ht, hn]
  rcases hp with ⟨ha, hb, hab, hw, hf, ht, hn⟩
  exact ⟨hw, hf, by omega, by omega⟩

/-- Number of coins at a denomination; only complete pairs carry up. -/
def capacity (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => n + capacity n k / 2

private def gap (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => (gap n k + 1) / 2

private theorem capacity_gap (n k : Nat) : capacity n k + gap n k = 2 * n := by
  induction k with
  | zero => simp [capacity, gap, Nat.two_mul]
  | succ k ih =>
    simp only [capacity, gap]
    omega

private theorem gap_le_iff (n k d : Nat) : gap n k ≤ d ↔ n ≤ d * 2 ^ k := by
  induction k generalizing d with
  | zero => simp [gap]
  | succ k ih =>
    have h : (gap n k + 1) / 2 ≤ d ↔ gap n k ≤ 2 * d := by omega
    simp only [gap, h, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- The largest package list contains the complete solution prefix
whenever the alphabet fits the declared bit limit. -/
theorem capacity_solution_between (n limit : Nat) (hl : 0 < limit)
    (hn : n ≤ 2 ^ limit) :
    2 * n - 2 ≤ capacity n (limit - 1) := by
  have hg : gap n (limit - 1) ≤ 2 := by
    apply (gap_le_iff n (limit - 1) 2).2
    rw [Nat.mul_comm, ← Nat.pow_succ, show (limit - 1).succ = limit by omega]
    exact hn
  have := capacity_gap n (limit - 1)
  omega

def LevelFor (n k : Nat) (flags : Array Bool) : Prop :=
  flags.size = capacity n k ∧ flags.toList.count true = n ∧
    flags.toList.count false = if k = 0 then 0 else capacity n (k - 1) / 2

private theorem level_push (n i : Nat) (out : Array (Array Bool)) (flags : Array Bool)
    (hs : out.size = i) (ho : ∀ k < i, LevelFor n k (out[k]?.getD #[]))
    (hf : LevelFor n i flags) :
    ∀ k < i + 1, LevelFor n k ((out.push flags)[k]?.getD #[]) := by
  intro k hk
  by_cases he : k = i
  · subst k
    simpa only [Array.getElem?_push, hs, ite_true,
      Option.getD_some] using hf
  · have hki : k < i := by omega
    simpa only [Array.getElem?_push, hs, he, ite_false] using ho k hki

/-- Every recorded level has the exact leaf/package counts produced by
the merge, including the final level appended after the loop. -/
theorem levels_exact (items : Array Nat) (limit : Nat) (hl : 0 < limit) :
    (levels items limit).size = limit ∧
      ∀ k < limit, LevelFor items.size k ((levels items limit)[k]?.getD #[]) := by
  let P (i : Nat) (s : Array Nat × Array Bool × Array (Array Bool)) : Prop :=
    s.1.size = capacity items.size (i - 1) ∧
    LevelFor items.size (i - 1) s.2.1 ∧
    s.2.2.size = i - 1 ∧
    ∀ k < i - 1, LevelFor items.size k (s.2.2[k]?.getD #[])
  unfold levels
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:limit]
    (items, Array.replicate items.size true, (#[] : Array (Array Bool))) _ :
      Id (Array Nat × Array Bool × Array (Array Bool))) = result
  have hp : P limit result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P limit) _ 1 limit _ hl
      (by simp [P, LevelFor, capacity, Array.count_replicate]) _ (fun _ h => h)
    intro i hi _ s hs
    rcases hs with ⟨hw, hf, ho, hall⟩
    change P (i + 1)
      ((merge items (pairWeights s.1)).1, (merge items (pairWeights s.1)).2,
        s.2.2.push s.2.1)
    have hm := merge_counts_exact items (pairWeights s.1)
    have hpair := pairWeights_size_exact s.1
    have hic : capacity items.size i = items.size + capacity items.size (i - 1) / 2 := by
      calc capacity items.size i = capacity items.size ((i - 1) + 1) :=
            congrArg (capacity items.size) (by omega)
        _ = _ := rfl
    dsimp only [P]
    simp only [Nat.add_sub_cancel_right]
    refine ⟨by omega, ?_, by simp [ho]; omega, ?_⟩
    · exact ⟨by omega, hm.2.2.1,
        by simpa only [show i ≠ 0 by omega, ite_false, hpair, hw] using hm.2.2.2⟩
    · have := level_push items.size (i - 1) s.2.2 s.2.1 ho hall hf
      simpa only [Nat.sub_add_cancel hi] using this
  rcases hp with ⟨_, hf, ho, hall⟩
  refine ⟨by simp only [Array.size_push, ho, Nat.sub_add_cancel hl], ?_⟩
  have := level_push items.size (limit - 1) result.2.2 result.2.1 ho hall hf
  simpa only [Nat.sub_add_cancel hl] using this

/-- The two selection counters read exactly the consumed flag prefix. -/
theorem selected_exact (flags : Array Bool) (take : Nat) (ht : take ≤ flags.size) :
    (selected flags take).1 = (flags.toList.take take).count true ∧
    (selected flags take).2 = (flags.toList.take take).count false := by
  let P (i : Nat) (s : Nat × Nat) : Prop :=
    s.1 = (flags.toList.take i).count true ∧
    s.2 = (flags.toList.take i).count false
  unfold selected
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact P (P take) _ 0 take _ (Nat.zero_le _)
    (by simp [P]) _ (fun _ h => h)
  intro i _ hi s hs
  have hf : i < flags.size := by omega
  have hfl : i < flags.toList.length := by simpa using hf
  have he := List.take_succ_eq_append_getElem hfl
  rcases hs with ⟨ha, hb⟩
  cases hv : flags[i] with
  | false =>
    simp only [getElem?_pos flags i hf, Option.getD_some, hv, Bool.false_eq_true, ite_false]
    change P (i + 1) (s.1, s.2 + 1)
    simp [P, he, ha, hb, hv]
  | true =>
    simp only [getElem?_pos flags i hf, Option.getD_some, hv, ite_true]
    change P (i + 1) (s.1 + 1, s.2)
    simp [P, he, ha, hb, hv]

private theorem bool_count (xs : List Bool) :
    xs.count true + xs.count false = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp <;> omega

theorem selected_counts_exact (flags : Array Bool) (take : Nat) (ht : take ≤ flags.size) :
    (selected flags take).1 + (selected flags take).2 = take ∧
    (selected flags take).1 ≤ flags.toList.count true ∧
    (selected flags take).2 ≤ flags.toList.count false := by
  rcases selected_exact flags take ht with ⟨ha, hb⟩
  rw [ha, hb]
  refine ⟨?_, (List.take_sublist take flags.toList).count_le true,
    (List.take_sublist take flags.toList).count_le false⟩
  rw [bool_count, List.length_take, Array.length_toList, Nat.min_eq_left ht]

end LeanTex.Core.Flate.PackageMerge
