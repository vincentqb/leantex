module

import all LeanTex.Core.Flate.PackageLengths
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

/-- The actual package-merge length vector obeys the canonical decoder's
Kraft budget, including unused and singleton alphabets. -/
theorem packageMerge_kraft_between (freqs : Array Nat) (limit : Nat)
    (hl : 0 < limit) (hfit : freqs.size ≤ 2 ^ limit) :
    Canonical.kraft (PackageMerge.lengths freqs limit).toList limit ≤ 2 ^ limit := by
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
  have hk := hc.1.kraft
  change PackageMerge.mass limit _ lens ≤ 2 ^ limit at hk
  simp only [PackageMerge.mass, Array.toList_filter, Array.toList_range,
    sum_filter, decide_eq_true_eq] at hk
  change Canonical.kraft lens.toList limit ≤ 2 ^ limit
  unfold Canonical.kraft
  rw [array_values, List.map_map]
  simp only [Function.comp_def, he, hsize]
  exact hk

/-- Every live symbol of the production package-merge encoder is decoded
by the table built from those same lengths. All table validity and
code-space facts are derived; the remaining stream premise names the
actual emitted bits. -/
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
