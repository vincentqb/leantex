namespace LeanTex.Core.Flate.Canonical

/-- First canonical code of width `k + 1`, after widths `1` through `k`. -/
def first (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (first count k + count (k + 1)) * 2

/-- Number of symbols with widths `1` through `k`. -/
def index (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => index count k + count (k + 1)

theorem first_later_between (count : Nat → Nat) (k d : Nat) :
    (first count k + count (k + 1)) * 2 ^ (d + 1) ≤ first count (k + 1 + d) := by
  induction d with
  | zero => simp [first]
  | succ d ih =>
    rw [show k + 1 + (d + 1) = (k + 1 + d) + 1 by omega, first]
    calc
      _ = ((first count k + count (k + 1)) * 2 ^ (d + 1)) * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ first count (k + 1 + d) * 2 := Nat.mul_le_mul_right _ ih
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right ..)

/-- No strict prefix of a later canonical code lies in an earlier code interval. -/
theorem first_prefix_between (count : Nat → Nat) (width k code : Nat)
    (hk : 1 ≤ k) (hkw : k < width) (hc : first count (width - 1) ≤ code) :
    first count (k - 1) + count k ≤ code / 2 ^ (width - k) := by
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
  have h := first_later_between count (k - 1) (width - k - 1)
  have h1 : k - 1 + 1 = k := by omega
  have h2 : k + (width - k - 1) = width - 1 := by omega
  have h3 : width - k - 1 + 1 = width - k := by omega
  rw [h1, h2, h3] at h
  exact Nat.le_trans h hc

theorem readBit_prefix_exact (code cut : Nat) :
    code / 2 ^ (cut + 1) * 2 + (code / 2 ^ cut) % 2 = code / 2 ^ cut := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- Reverse exactly `width` low bits, including leading zeroes. -/
def reverseBits (code : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => reverseBits code width * 2 + code / 2 ^ width % 2

theorem reverseBits_between (code width : Nat) :
    reverseBits code width < 2 ^ width := by
  induction width with
  | zero => simp [reverseBits]
  | succ width ih =>
    rw [reverseBits, Nat.pow_succ]
    have := Nat.mod_lt (code / 2 ^ width) (by decide : 0 < 2)
    omega

theorem reverseBits_bit_exact (code width k : Nat) (hk : k < width) :
    (reverseBits code width).testBit k = code.testBit (width - 1 - k) := by
  induction width generalizing k with
  | zero => omega
  | succ width ih =>
    rw [reverseBits, Nat.mul_comm (reverseBits code width) 2]
    have hbit : code / 2 ^ width % 2 < 2 ^ 1 := Nat.mod_lt _ (by decide)
    rw [show 2 = 2 ^ 1 from rfl, Nat.testBit_two_pow_mul_add _ hbit]
    by_cases h0 : k = 0
    · subst k
      simp only [Nat.zero_lt_succ, ite_true, Nat.testBit_zero, Nat.mod_mod,
        Nat.add_sub_cancel_right, Nat.sub_zero]
      exact (Nat.testBit_eq_decide_div_mod_eq).symm
    · have hk1 : ¬ k < 1 := by omega
      simp only [hk1, ite_false]
      rw [ih (k - 1) (by omega)]
      congr 1
      omega

/-- Reversing a bounded code twice recovers the whole code. -/
theorem reverseBits_id (code width : Nat) (hc : code < 2 ^ width) :
    reverseBits (reverseBits code width) width = code := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < width
  · rw [reverseBits_bit_exact _ _ _ hk,
      reverseBits_bit_exact _ _ _ (by omega)]
    congr 1
    omega
  · have hp : 2 ^ width ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (reverseBits_between _ _) hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc hp)]

end LeanTex.Core.Flate.Canonical
