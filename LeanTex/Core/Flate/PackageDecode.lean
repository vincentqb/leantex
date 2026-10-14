module

import all LeanTex.Core.Flate.PackageLengths
import all LeanTex.Core.Flate.PackageComplete
import all LeanTex.Core.Flate.HuffmanKraft

namespace LeanTex.Core.Flate

private theorem array_values (xs : Array Nat) :
    xs.toList = (List.range xs.size).map fun s => xs[s]?.getD 0 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList,
      getElem?_pos xs i (by simpa using hi), Option.getD_some]

private theorem sum_filter (xs : List Nat) (p : Nat → Bool) (f : Nat → Nat) :
    ((xs.filter p).map f).sum = (xs.map fun s => if p s then f s else 0).sum := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    by_cases hp : p s = true <;> simp [hp, ih]

theorem packageMerge_kraft_exact (freqs : Array Nat) (limit : Nat)
    (hl : 0 < limit) (hfit : freqs.size ≤ 2 ^ limit) :
    Canonical.kraft (PackageMerge.lengths freqs limit).toList limit =
      PackageMerge.mass limit ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0)
        (PackageMerge.lengths freqs limit) := by
  let lens := PackageMerge.lengths freqs limit
  have hc := PackageMerge.lengths_contract freqs limit hl hfit
  have hsize : lens.size = freqs.size := hc.1.size_eq
  have he (s : Nat) :
      Canonical.cost limit (lens[s]?.getD 0) =
        if 0 < freqs[s]?.getD 0 then 2 ^ (limit - lens[s]?.getD 0) else 0 := by
    by_cases hp : 0 < freqs[s]?.getD 0
    · have hn : 0 < lens[s]?.getD 0 ∧ lens[s]?.getD 0 ≤ limit :=
        ⟨(hc.2 s).mpr hp, hc.1.width_le s⟩
      simp only [Canonical.cost, ite_eq_left hn, ite_eq_left hp]
    · have hz : lens[s]?.getD 0 = 0 := by
        have hn : ¬ 0 < lens[s]?.getD 0 := fun h => hp ((hc.2 s).mp h)
        omega
      simp [Canonical.cost, hz, hp]
  change Canonical.kraft lens.toList limit = PackageMerge.mass limit _ lens
  simp only [PackageMerge.mass, Array.toList_filter, Array.toList_range, sum_filter,
    decide_eq_true_eq]
  unfold Canonical.kraft
  rw [array_values, List.map_map]
  simp only [Function.comp_def, he, hsize]

theorem packageMerge_kraft_between (freqs : Array Nat) (limit : Nat)
    (hl : 0 < limit) (hfit : freqs.size ≤ 2 ^ limit) :
    Canonical.kraft (PackageMerge.lengths freqs limit).toList limit ≤ 2 ^ limit := by
  rw [packageMerge_kraft_exact freqs limit hl hfit]
  exact (PackageMerge.lengths_contract freqs limit hl hfit).1.kraft

private theorem kraft_append (xs ys : List Nat) (width : Nat) :
    Canonical.kraft (xs ++ ys) width = Canonical.kraft xs width + Canonical.kraft ys width := by
  simp [Canonical.kraft]

private theorem kraft_zeros (k width : Nat) : Canonical.kraft (List.replicate k 0) width = 0 := by
  simp [Canonical.kraft, Canonical.cost]

private theorem single_split (n s : Nat) (hs : s < n) :
    ((Array.replicate n 0).set! s 1).toList =
      List.replicate s 0 ++ 1 :: List.replicate (n - s - 1) 0 := by
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, Array.toList_replicate,
    List.set_eq_take_append_cons_drop, ite_eq_left (by simpa using hs), List.take_replicate,
    List.drop_replicate, Nat.min_eq_left (by omega), show n - (s + 1) = n - s - 1 by omega]

/-- The encoder's tables are those zlib's inflate admits: two or more live symbols fill the code
space, and one or none, which only a payload table (`sparse`) admits, leave a lone one-bit code
or no code at all. -/
theorem packageMerge_mkHuff?_exact (freqs : Array Nat) (limit : Nat) (sparse : Bool)
    (hl : 0 < limit ∧ limit ≤ 15) (hfit : freqs.size ≤ 2 ^ limit)
    (hs : sparse = true ∨
      1 < ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).size) :
    mkHuff? (PackageMerge.lengths freqs limit) sparse =
      some (mkHuff (PackageMerge.lengths freqs limit)) := by
  have hc := PackageMerge.lengths_contract freqs limit hl.1 hfit
  have hw : ∀ len ∈ (PackageMerge.lengths freqs limit).toList, len ≤ limit := by
    intro len hm
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hm)
    have := hc.1.width_le i
    rw [hi, Option.getD_some] at this
    exact this
  apply (mkHuff?_some_exact _ _ _).mpr
  refine ⟨rfl, ?_⟩
  have hscale := Canonical.kraft_scale_exact _ limit 15 hl.2 hw
  have hpow : 2 ^ limit * 2 ^ (15 - limit) = 2 ^ 15 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hl.2]
  by_cases h2 : 1 < ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).size
  · left
    rw [hscale, packageMerge_kraft_exact freqs limit hl.1 hfit,
      PackageMerge.lengths_mass_exact freqs limit hl.1 hfit h2, hpow]
  · right
    refine ⟨hs.resolve_right h2, ?_⟩
    by_cases h0 : ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).size = 0
    · left
      rw [PackageMerge.lengths_empty_exact freqs limit h0, Array.toList_replicate, kraft_zeros]
    · right
      have h1 : ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).size = 1 := by
        omega
      have hlt := PackageMerge.live_single_lt freqs h1
      rw [PackageMerge.lengths_single_exact freqs limit h1, single_split _ _ hlt]
      refine ⟨?_, ?_⟩
      · rw [kraft_append, kraft_zeros, Canonical.kraft_cons, kraft_zeros]
        simp [Canonical.cost]
      · simp [List.count_replicate]

theorem packageMerge_decode_exact (freqs : Array Nat) (limit : Nat) (r : Br) (s : Nat)
    (hl : 0 < limit ∧ limit ≤ 15) (hfit : freqs.size ≤ 2 ^ limit)
    (hs : 0 < freqs[s]?.getD 0)
    (hf : BitField r.data r.bitPos ((PackageMerge.lengths freqs limit)[s]?.getD 0)
      ((canonCodes (PackageMerge.lengths freqs limit))[s]?.getD 0)) :
    (mkHuff (PackageMerge.lengths freqs limit)).decode r =
      some (s, { r with bitPos :=
        r.bitPos + (PackageMerge.lengths freqs limit)[s]?.getD 0 }) := by
  have hc := PackageMerge.lengths_contract freqs limit hl.1 hfit
  have hi : s < freqs.size := by
    by_cases hi : s < freqs.size
    · exact hi
    · simp only [getElem?_neg freqs s hi, Option.getD_none] at hs
      omega
  apply canonCodes_decode_exact _ r s _
  · intro t _
    exact Nat.le_trans (hc.1.width_le t) hl.2
  · rw [hc.1.size_eq]
    exact hi
  · exact (hc.2 s).mpr hs
  · rfl
  · exact Canonical.kraft_code_space_between _ limit _ hl.2 (hc.1.width_le s)
      (packageMerge_kraft_between freqs limit hl.1 hfit)
  · exact hf

end LeanTex.Core.Flate
