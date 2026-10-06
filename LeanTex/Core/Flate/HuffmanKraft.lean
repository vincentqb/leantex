import LeanTex.Core.Flate.HuffmanProof
import Init.Data.List.Nat.Sum

namespace LeanTex.Core.Flate.Canonical

/-- A symbol's occupied slots at a given code width. Unused symbols and
longer codes do not occupy a slot at this width. -/
def cost (width len : Nat) : Nat :=
  if 0 < len ∧ len ≤ width then 2 ^ (width - len) else 0

/-- Integer-scaled Kraft mass, including only codes no longer than the
scale. At the maximum length this is the complete code-space budget. -/
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

/-- Moving to the next width doubles occupied slots and adds the codes
whose declared length is exactly that new width. -/
theorem kraft_step_exact (lengths : List Nat) (width : Nat) :
    kraft lengths (width + 1) = 2 * kraft lengths width + lengths.count (width + 1) := by
  induction lengths with
  | nil => simp [kraft]
  | cons len lengths ih =>
    rw [kraft_cons, kraft_cons, cost_step, ih]
    simp only [List.count_cons, beq_iff_eq]
    by_cases he : len = width + 1 <;> simp only [he, ite_true, ite_false] <;> omega

/-- Canonical intervals count exactly the slots occupied by all widths
through the current one. The bucket counts are those of `mkHuff`. -/
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

/-- A shorter-width code budget embeds into every larger-width budget. -/
theorem kraft_scale_between (lengths : List Nat) (width limit : Nat)
    (hw : width ≤ limit) :
    kraft lengths width * 2 ^ (limit - width) ≤ kraft lengths limit := by
  induction lengths with
  | nil => simp [kraft]
  | cons len lengths ih =>
    have hc := cost_scale width limit len hw
    rw [kraft_cons, kraft_cons, Nat.add_mul]
    omega

/-- Kraft's bound on the actual length vector discharges the canonical
decoder's code-space premise for every used width. -/
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

end LeanTex.Core.Flate.Canonical
