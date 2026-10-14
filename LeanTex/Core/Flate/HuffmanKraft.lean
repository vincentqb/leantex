module

import all LeanTex.Core.Flate.HuffmanProof
import Init.Data.List.Nat.Sum

namespace LeanTex.Core.Flate.Canonical

/-- The slots a code of length `len` occupies at `width`; unused and longer codes occupy none. -/
def cost (width len : Nat) : Nat :=
  if 0 < len ∧ len ≤ width then 2 ^ (width - len) else 0

/-- The integer-scaled Kraft sum at `width`, over the codes no longer than `width`. -/
def kraft (lengths : List Nat) (width : Nat) : Nat :=
  (lengths.map (cost width)).sum

private theorem cost_step (width len : Nat) :
    cost (width + 1) len = 2 * cost width len + if len = width + 1 then 1 else 0 := by
  by_cases hz : len = 0
  · subst len
    simp [cost]
  · by_cases hl : len ≤ width
    · have hp : 0 < len := by omega
      have hn : len ≤ width + 1 := by omega
      have he : len ≠ width + 1 := by omega
      have hs : width + 1 - len = (width - len) + 1 := by omega
      simp only [cost, hp, hl, hn, and_self, ite_true, he, ite_false, Nat.add_zero,
        hs, Nat.pow_succ, Nat.mul_comm]
    · by_cases he : len = width + 1
      · subst len
        simp [cost, hl]
      · have hn : ¬ len ≤ width + 1 := by omega
        simp [cost, hl, hn, he]

private theorem kraft_cons (len : Nat) (lengths : List Nat) (width : Nat) :
    kraft (len :: lengths) width = cost width len + kraft lengths width := by
  simp [kraft]

private theorem kraft_zero (lengths : List Nat) : kraft lengths 0 = 0 := by
  have hz (len : Nat) : cost 0 len = 0 := by
    have hn : ¬ (0 < len ∧ len ≤ 0) := by omega
    simp only [cost, ite_eq_right hn]
  induction lengths with
  | nil => rfl
  | cons len lengths ih => rw [kraft_cons, hz, ih]

theorem kraft_step_exact (lengths : List Nat) (width : Nat) :
    kraft lengths (width + 1) = 2 * kraft lengths width + lengths.count (width + 1) := by
  induction lengths with
  | nil => simp [kraft]
  | cons len lengths ih =>
    rw [kraft_cons, kraft_cons, cost_step, ih]
    simp only [List.count_cons, beq_iff_eq]
    by_cases he : len = width + 1 <;> simp only [he, ite_true, ite_false] <;> omega

theorem start_kraft_exact (lengths : Array Nat) (width : Nat) (hw : width ≤ 15) :
    start (fun k => (huffCounts lengths)[k]?.getD 0) width +
      (huffCounts lengths)[width]?.getD 0 = kraft lengths.toList width := by
  have hc : CountsFor lengths.toList (huffCounts lengths) := huffCounts_loop_exact lengths
  induction width with
  | zero => simp [start, hc.2, kraft_zero]
  | succ width ih =>
    have hp : 0 < width + 1 ∧ width + 1 < 16 := by omega
    rw [start, hc.2 (width + 1), ite_eq_left hp, kraft_step_exact]
    have he := ih (by omega)
    omega

private theorem cost_scale (width limit len : Nat) (hw : width ≤ limit) :
    cost width len * 2 ^ (limit - width) ≤ cost limit len := by
  by_cases hl : 0 < len ∧ len ≤ width
  · have hn : 0 < len ∧ len ≤ limit := ⟨hl.1, by omega⟩
    simp only [cost, hl, hn, and_self, ite_true]
    rw [← Nat.pow_add, show width - len + (limit - width) = limit - len by omega]
    exact Nat.le_refl _
  · simp only [cost, hl, ite_false, Nat.zero_mul, Nat.zero_le]

theorem kraft_scale_between (lengths : List Nat) (width limit : Nat)
    (hw : width ≤ limit) :
    kraft lengths width * 2 ^ (limit - width) ≤ kraft lengths limit := by
  induction lengths with
  | nil => simp [kraft]
  | cons len lengths ih =>
    have hc := cost_scale width limit len hw
    rw [kraft_cons, kraft_cons, Nat.add_mul]
    omega

theorem kraft_code_space_between (lengths : Array Nat) (limit width : Nat)
    (hl : limit ≤ 15) (hw : width ≤ limit)
    (hk : kraft lengths.toList limit ≤ 2 ^ limit) :
    start (fun k => (huffCounts lengths)[k]?.getD 0) width +
      (huffCounts lengths)[width]?.getD 0 ≤ 2 ^ width := by
  rw [start_kraft_exact lengths width (by omega)]
  have hs := kraft_scale_between lengths.toList width limit hw
  have hp : 2 ^ limit = 2 ^ width * 2 ^ (limit - width) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hw]
  have hm : kraft lengths.toList width * 2 ^ (limit - width) ≤
      2 ^ width * 2 ^ (limit - width) := by rw [← hp]; exact Nat.le_trans hs hk
  exact Nat.le_of_mul_le_mul_right hm (Nat.two_pow_pos _)

private theorem cost_scale_exact (width limit len : Nat) (hw : width ≤ limit) (hl : len ≤ width) :
    cost limit len = cost width len * 2 ^ (limit - width) := by
  by_cases hz : len = 0
  · subst len
    simp [cost]
  · have hp : 0 < len ∧ len ≤ width := ⟨by omega, hl⟩
    have hn : 0 < len ∧ len ≤ limit := ⟨by omega, by omega⟩
    simp only [cost, hp, hn, and_self, ite_true]
    rw [← Nat.pow_add, show width - len + (limit - width) = limit - len by omega]

theorem kraft_scale_exact (lengths : List Nat) (width limit : Nat) (hw : width ≤ limit)
    (hl : ∀ len ∈ lengths, len ≤ width) :
    kraft lengths limit = kraft lengths width * 2 ^ (limit - width) := by
  induction lengths with
  | nil => simp [kraft]
  | cons len lengths ih =>
    rw [kraft_cons, kraft_cons, Nat.add_mul, ih (fun l h => hl l (by simp [h])),
      cost_scale_exact width limit len hw (hl len (by simp))]

end LeanTex.Core.Flate.Canonical

namespace LeanTex.Core.Flate

theorem mkHuff?_some_exact (lengths : Array Nat) (h : Huff) :
    mkHuff? lengths = some h ↔
      h = mkHuff lengths ∧ Canonical.kraft lengths.toList 15 ≤ 2 ^ 15 := by
  have hk := Canonical.start_kraft_exact lengths 15 (Nat.le_refl _)
  have hfits : (mkHuff lengths).fits = true ↔ Canonical.kraft lengths.toList 15 ≤ 2 ^ 15 := by
    show decide (Canonical.start (fun k => (huffCounts lengths)[k]?.getD 0) 15 +
      (huffCounts lengths)[15]?.getD 0 ≤ 2 ^ 15) = true ↔ _
    rw [decide_eq_true_iff, hk]
  simp only [mkHuff?]
  by_cases hp : Canonical.kraft lengths.toList 15 ≤ 2 ^ 15
  · rw [ite_eq_left (hfits.mpr hp)]
    exact ⟨fun he => ⟨(Option.some.inj he).symm, hp⟩, fun ⟨he, _⟩ => he ▸ rfl⟩
  · rw [ite_eq_right (fun hf => hp (hfits.mp hf))]
    exact ⟨(fun he => by cases he), fun ⟨_, hk'⟩ => absurd hk' hp⟩

/-- An accepted table decodes each symbol of a nonzero length from its canonical code. -/
theorem mkHuff?_decode_exact (lengths : Array Nat) (h : Huff) (hh : mkHuff? lengths = some h)
    (hb : ∀ s < lengths.size, lengths[s]?.getD 0 ≤ 15) (r : Br) (s width : Nat)
    (hs : s < lengths.size) (hw : 0 < width) (hl : lengths[s]?.getD 0 = width)
    (hf : BitField r.data r.bitPos width ((canonCodes lengths)[s]?.getD 0)) :
    h.decode r = some (s, { r with bitPos := r.bitPos + width }) := by
  obtain ⟨rfl, hk⟩ := (mkHuff?_some_exact lengths h).mp hh
  have hw15 : width ≤ 15 := by have := hb s hs; omega
  exact canonCodes_decode_exact lengths r s width hb hs hw hl
    (Canonical.kraft_code_space_between lengths 15 width (Nat.le_refl _) hw15 hk) hf

end LeanTex.Core.Flate
