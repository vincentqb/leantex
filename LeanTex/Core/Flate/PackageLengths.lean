module

import all LeanTex.Core.Flate.PackageKraft

namespace LeanTex.Core.Flate.PackageMerge

private theorem sum_positive (xs : List Nat) (f : Nat → Nat)
    (h : ∀ s ∈ xs, 0 < f s) : xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have hs := h s (by simp)
    have ht := ih (fun s hs => h s (by simp [hs]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem member_mass (xs : List Nat) (f : Nat → Nat)
    (h : ∀ s ∈ xs, 0 < f s) (s : Nat) (hs : s ∈ xs) :
    f s + (xs.length - 1) ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hs
  | cons t xs ih =>
    have ht := h t (by simp)
    have hp : ∀ s ∈ xs, 0 < f s := fun s hs => h s (by simp [hs])
    rcases List.mem_cons.mp hs with he | hs
    · subst s
      have hb := sum_positive xs f hp
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
    · have hb := ih hp hs
      have hn : 0 < xs.length := List.length_pos_of_mem hs
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- With at least two leaves, a zero-width live symbol alone would spend
the entire Kraft budget; every other leaf still has positive mass. -/
theorem LengthsFor.live_positive (sorted lens : Array Nat) (size limit : Nat)
    (h : LengthsFor sorted size limit lens) (hn : 1 < sorted.size)
    (s : Nat) (hs : s ∈ sorted.toList) : 0 < lens[s]?.getD 0 := by
  have hm := member_mass sorted.toList (fun s => 2 ^ (limit - lens[s]?.getD 0))
    (fun _ _ => Nat.pow_pos Nat.zero_lt_two) s hs
  change 2 ^ (limit - lens[s]?.getD 0) + (sorted.size - 1) ≤
    mass limit sorted lens at hm
  have hk := h.kraft
  by_cases he : 0 < lens[s]?.getD 0
  · exact he
  · have hz : lens[s]?.getD 0 = 0 := by omega
    simp only [hz, Nat.sub_zero] at hm
    omega

private abbrev live (freqs : Array Nat) : Array Nat :=
  (Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0

private theorem live_mem (freqs : Array Nat) (s : Nat) :
    s ∈ (live freqs).toList ↔ s < freqs.size ∧ 0 < freqs[s]?.getD 0 := by
  simp [live, List.mem_range]

private theorem live_nodup (freqs : Array Nat) : (live freqs).toList.Nodup := by
  simp only [live, Array.toList_filter, Array.toList_range]
  exact List.Pairwise.filter _ List.nodup_range

private theorem perm_lengths (syms sorted lens : Array Nat) (size limit : Nat)
    (hp : sorted.Perm syms) (h : LengthsFor sorted size limit lens) :
    LengthsFor syms size limit lens := by
  refine ⟨h.size_eq, h.width_le, ?_, ?_⟩
  · intro s hs
    exact h.unused_zero s (fun hm => hs (hp.toList.mem_iff.mp hm))
  · have he := (hp.toList.map (fun s => 2 ^ (limit - lens[s]?.getD 0))).sum_nat
    simpa only [mass, he] using h.kraft

private theorem singleton_contract (syms : Array Nat) (size limit : Nat)
    (hn : syms.size = 1) (hv : ∀ s ∈ syms.toList, s < size) (hl : 0 < limit) :
    LengthsFor syms size limit
      ((Array.replicate size 0).set! (syms[0]?.getD 0) 1) ∧
    ∀ s, 0 < ((Array.replicate size 0).set! (syms[0]?.getD 0) 1)[s]?.getD 0 ↔
      s ∈ syms.toList := by
  have he : syms.toList = [syms[0]?.getD 0] := by
    apply List.ext_getElem
    · simpa using hn
    · intro i hi hj
      have hi0 : i = 0 := by simp only [hn, Array.length_toList] at hi; omega
      subst i
      simp only [List.getElem_cons_zero, Array.getElem_toList,
        getElem?_pos syms 0 (by omega), Option.getD_some]
  have hv0 := hv (syms[0]?.getD 0) (by simp [he])
  have hg : ∀ s, ((Array.replicate size 0).set! (syms[0]?.getD 0) 1)[s]?.getD 0 =
      if s = syms[0]?.getD 0 then 1 else 0 := by
    intro s
    by_cases hs : s = syms[0]?.getD 0
    · subst s
      simp [hv0]
    · by_cases hb : s < size <;> simp [hs, Ne.symm hs, hb]
  refine ⟨⟨by simp, ?_, ?_, ?_⟩, ?_⟩
  · intro s
    rw [hg s]
    split <;> omega
  · intro s hs
    have hne : s ≠ syms[0]?.getD 0 := by simpa only [he, List.mem_singleton] using hs
    simp only [hg s, ite_eq_right hne]
  · simp only [mass, he, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, hg, ite_true]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  · intro s
    simp only [hg, he, List.mem_singleton]
    split <;> simp_all

/-- Package-merge gives every positive-frequency symbol a bounded,
positive length, leaves every unused symbol at zero, and satisfies Kraft.
The alphabet and bit limit are the actual encoder inputs. -/
theorem lengths_contract (freqs : Array Nat) (limit : Nat) (hl : 0 < limit)
    (hfit : freqs.size ≤ 2 ^ limit) :
    LengthsFor ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0)
      freqs.size limit (lengths freqs limit) ∧
    ∀ s : Nat, 0 < (lengths freqs limit)[s]?.getD 0 ↔ 0 < freqs[s]?.getD 0 := by
  let syms := live freqs
  have hv : ∀ s ∈ syms.toList, s < freqs.size := fun s hs => (live_mem freqs s).mp hs |>.1
  have hmem : ∀ s, s ∈ syms.toList ↔ 0 < freqs[s]?.getD 0 := by
    intro s
    rw [live_mem]
    constructor
    · exact And.right
    · intro hs
      refine ⟨?_, hs⟩
      by_cases he : s < freqs.size
      · exact he
      · simp only [getElem?_neg freqs s he, Option.getD_none] at hs
        omega
  let sorted := syms.qsort fun a b => freqs[a]?.getD 0 < freqs[b]?.getD 0
  let items := sorted.map fun s => freqs[s]?.getD 0
  let out := if syms.size == 0 then Array.replicate freqs.size 0 else
    if syms.size == 1 then (Array.replicate freqs.size 0).set! (syms[0]?.getD 0) 1 else
      backtrace sorted freqs.size (levels items limit)
  change LengthsFor syms freqs.size limit out ∧
    ∀ s : Nat, 0 < out[s]?.getD 0 ↔ 0 < freqs[s]?.getD 0
  dsimp only [out]
  by_cases hzero : syms.size = 0
  · simp only [beq_iff_eq, hzero, ite_true]
    have he : syms = #[] := Array.eq_empty_of_size_eq_zero hzero
    have hg : ∀ s : Nat, (Array.replicate freqs.size 0)[s]?.getD 0 = 0 := by
      intro s
      by_cases hi : s < freqs.size <;> simp [hi]
    refine ⟨⟨by simp, ?_, ?_, ?_⟩, ?_⟩
    · intro s
      simp only [hg, Nat.zero_le]
    · intro s _
      exact hg s
    · simp [mass, he]
    · intro s
      have hf : ¬ 0 < freqs[s]?.getD 0 := by
        intro hs
        have hm := (hmem s).mpr hs
        simp only [he, Array.toList_empty, List.not_mem_nil] at hm
      simp [hg, hf]
  · simp only [beq_iff_eq, hzero, ite_false]
    by_cases hone : syms.size = 1
    · simp only [hone, ite_true]
      have hc := singleton_contract syms freqs.size limit hone hv hl
      exact ⟨hc.1, fun s => (hc.2 s).trans (hmem s)⟩
    · simp only [hone, ite_false]
      have hp : sorted.Perm syms := qsort_perm_exact syms _
      have hn : sorted.toList.Nodup := hp.symm.toList.nodup (live_nodup freqs)
      have hv' : ∀ s ∈ sorted.toList, s < freqs.size := fun s hs =>
        hv s (hp.toList.mem_iff.mp hs)
      have hlevel := levels_exact items limit hl
      have hs : sorted.size ≤ freqs.size :=
        Nat.le_trans (by have := hp.size_eq; omega : sorted.size ≤ syms.size)
          (by simpa [syms, live] using
            (Array.size_filter_le (xs := Array.range freqs.size)
              (p := fun s => freqs[s]?.getD 0 > 0)))
      have htrace := backtrace_contract sorted freqs.size (levels items limit) hn hv'
        (by have := hp.size_eq; omega) (by omega)
        (by rw [hlevel.1]; exact Nat.le_trans hs hfit) (by
          intro k hk
          have h := hlevel.2 k (by omega)
          simpa only [items, Array.size_map] using h)
      rw [hlevel.1] at htrace
      refine ⟨perm_lengths syms sorted _ _ _ hp htrace, ?_⟩
      intro s
      constructor
      · intro h
        apply (hmem s).mp
        by_cases he : s ∈ syms.toList
        · exact he
        · have hu := htrace.unused_zero s (fun hm => he (hp.toList.mem_iff.mp hm))
          omega
      · intro h
        exact htrace.live_positive sorted _ _ _ (by have := hp.size_eq; omega) s
          (hp.toList.mem_iff.mpr ((hmem s).mpr h))

end LeanTex.Core.Flate.PackageMerge
