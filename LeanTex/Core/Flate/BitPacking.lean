namespace LeanTex.Core.Flate.BitPacking

theorem or_shift_exact (hi lo n : Nat) (hlo : lo < 2 ^ n) :
    (hi <<< n) ||| lo = hi * 2 ^ n + lo := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm hi, ← Nat.two_pow_add_eq_or_of_lt hlo]

theorem packBits_exact (hi lo n : Nat) (hn : n < 64)
    (hlo : lo < 2 ^ n) (hhi : hi < 2 ^ (64 - n)) :
    ((hi.toUInt64 <<< n.toUInt64) ||| lo.toUInt64).toNat = hi * 2 ^ n + lo := by
  have hpow : 2 ^ (64 - n) * 2 ^ n = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hres : hi * 2 ^ n + lo < 2 ^ 64 := by
    calc
      _ < hi * 2 ^ n + 2 ^ n := Nat.add_lt_add_left hlo _
      _ = (hi + 1) * 2 ^ n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ (64 - n) * 2 ^ n := Nat.mul_le_mul_right _ hhi
      _ = _ := hpow
  have hhi64 : hi < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..))
  have hlo64 : lo < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hn))
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, Nat.toUInt64,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt hhi64, Nat.mod_eq_of_lt hlo64,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn]
  rw [Nat.mod_eq_of_lt (show hi <<< n < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega)]
  exact or_shift_exact hi lo n hlo

theorem shiftOne_exact (n : Nat) (hn : n < 64) :
    ((1 : UInt64) <<< n.toUInt64).toNat = 2 ^ n := by
  have hpow : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  simp only [UInt64.toNat_shiftLeft, Nat.toUInt64, UInt64.toNat_ofNat']
  simp [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hpow]

theorem maskBits_exact (n : Nat) (hn : n < 64) :
    (((1 : UInt64) <<< n.toUInt64) - 1).toNat = 2 ^ n - 1 := by
  rw [UInt64.toNat_sub_of_le]
  · simp [shiftOne_exact n hn]
  · simpa [UInt64.le_iff_toNat_le, shiftOne_exact n hn] using
      Nat.succ_le_of_lt (Nat.two_pow_pos n)

theorem takeBits_exact (v : UInt64) (n : Nat) (hn : n < 64) :
    (v &&& (((1 : UInt64) <<< n.toUInt64) - 1)).toNat = v.toNat % 2 ^ n := by
  simp only [UInt64.toNat_and, maskBits_exact n hn, Nat.and_two_pow_sub_one_eq_mod]

theorem unpackBits_exact (hi lo n : Nat) (hn : n < 64)
    (hlo : lo < 2 ^ n) (hhi : hi < 2 ^ (64 - n)) :
    let packed := (hi.toUInt64 <<< n.toUInt64) ||| lo.toUInt64
    (packed >>> n.toUInt64).toNat = hi ∧
      (packed &&& (((1 : UInt64) <<< n.toUInt64) - 1)).toNat = lo := by
  dsimp only
  constructor
  · simp only [UInt64.toNat_shiftRight, packBits_exact hi lo n hn hlo hhi,
      Nat.toUInt64, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_comm hi, Nat.mul_add_div (Nat.two_pow_pos n),
      Nat.div_eq_of_lt hlo, Nat.add_zero]
  · rw [takeBits_exact _ n hn, packBits_exact hi lo n hn hlo hhi,
      Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlo]

theorem lowBits_succ (v k : Nat) :
    v % 2 ^ k + ((v >>> k) &&& 1) * 2 ^ k = v % 2 ^ (k + 1) := by
  have mask1 (x : Nat) : x &&& 1 = x % 2 := Nat.and_two_pow_sub_one_eq_mod x 1
  rw [Nat.shiftRight_eq_div_pow, mask1, Nat.pow_succ, Nat.mod_mul]
  rw [Nat.mul_comm]

theorem appendBit_exact (v : Nat) (k : Nat) (hk : k < 64) :
    ((v % 2 ^ k).toUInt64 ||| (((v >>> k) &&& 1).toUInt64 <<< k.toUInt64)).toNat =
      v % 2 ^ (k + 1) := by
  have hlo : v % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hbit : (v >>> k) &&& 1 < 2 := by
    rw [show (v >>> k) &&& 1 = (v >>> k) % 2 from
      Nat.and_two_pow_sub_one_eq_mod _ 1]
    exact Nat.mod_lt _ (by decide)
  have hhi : (v >>> k) &&& 1 < 2 ^ (64 - k) := by
    apply Nat.lt_of_lt_of_le hbit
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ 64 - k by omega)
  rw [UInt64.or_comm, packBits_exact _ _ _ hk hlo hhi, Nat.add_comm]
  exact lowBits_succ v k

theorem packField_bits_exact (lo hi n width i : Nat)
    (hlo : lo < 2 ^ n) (hiidx : i < n + width) :
    (lo + hi % 2 ^ width * 2 ^ n).testBit i =
      if i < n then lo.testBit i else hi.testBit (i - n) := by
  rw [Nat.add_comm, ← or_shift_exact _ _ n hlo,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < n
  · have hn : ¬ n ≤ i := by omega
    simp [h, hn]
  · have hn : n ≤ i := by omega
    have hz : lo.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) hn))
    have hw : i - n < width := by omega
    simp [h, hn, hz, hw]

end LeanTex.Core.Flate.BitPacking
