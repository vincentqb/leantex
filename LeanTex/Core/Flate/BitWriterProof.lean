module

import all LeanTex.Core.Flate.BitWriter
import all LeanTex.Core.Flate.PackageDecode

namespace LeanTex.Core.Flate

def Bw.position (w : Bw) : Nat := 8 * w.out.size + w.nbits.toNat

/-- The later writer retains the whole earlier stream, including pending bits. -/
def Bw.Extends (later earlier : Bw) : Prop :=
  earlier.position ≤ later.position ∧
    ∀ i < earlier.position, later.bitValue i = earlier.bitValue i

theorem Bw.Extends.refl (w : Bw) : w.Extends w :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Bw.Extends.trans {a b c : Bw} (hcb : c.Extends b) (hba : b.Extends a) :
    c.Extends a :=
  ⟨Nat.le_trans hba.1 hcb.1, fun i hi =>
    (hcb.2 i (Nat.lt_of_lt_of_le hi hba.1)).trans (hba.2 i hi)⟩

theorem Bw.Field.extend {a b : Bw} {start width value : Nat}
    (hf : a.Field start width value) (he : b.Extends a) :
    b.Field start width value :=
  ⟨Nat.le_trans hf.1 he.1, fun k hk =>
    (he.2 _ (by have := hf.1; dsimp only [Bw.position]; omega)).trans (hf.2 k hk)⟩

/-- Every supported push preserves all previously emitted fields. -/
theorem pushU_extends_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) : (w.pushU v n).Extends w := by
  constructor
  · change _ ≤ 8 * (w.pushU v n).out.size + (w.pushU v n).nbits.toNat
    rw [pushU_position_exact w v n hw hn]
    exact Nat.le_add_right ..
  · intro i hi
    rw [pushU_bits_exact w v n hw hn i (by dsimp only [Bw.position] at hi; omega)]
    exact ite_eq_left hi

private theorem width_toUInt64 (n : Nat) (hn : n ≤ 16) :
    n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

theorem push_valid (w : Bw) (v n : Nat) (hw : w.Valid) (hn : n ≤ 16) :
    (w.push v n).Valid :=
  pushU_valid w _ _ hw (by simpa only [width_toUInt64 n hn] using hn)

theorem push_position_exact (w : Bw) (v n : Nat) (hw : w.Valid) (hn : n ≤ 16) :
    (w.push v n).position = w.position + n := by
  simpa only [Bw.push, Bw.position, width_toUInt64 n hn] using
    pushU_position_exact w v.toUInt64 n.toUInt64 hw
      (by simpa only [width_toUInt64 n hn] using hn)

theorem push_extends_exact (w : Bw) (v n : Nat) (hw : w.Valid) (hn : n ≤ 16) :
    (w.push v n).Extends w :=
  pushU_extends_exact w _ _ hw (by simpa only [width_toUInt64 n hn] using hn)

theorem push_field_exact (w : Bw) (v n : Nat) (hw : w.Valid)
    (hn : n ≤ 16) (hv : v < 2 ^ n) :
    (w.push v n).Field w.position n v := by
  have hv64 : v < 2 ^ 64 := Nat.lt_of_lt_of_le hv
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have hvn : v.toUInt64.toNat = v := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hv64]
  simpa only [Bw.push, Bw.position, width_toUInt64 n hn, hvn] using
    pushU_field_exact w v.toUInt64 n.toUInt64 hw
      (by simpa only [width_toUInt64 n hn] using hn)

/-- Bytes containing the writer's complete stream, possibly followed by more
data. This is a relation over the actual bytes, not a second encoder. -/
def Bw.Realizes (w : Bw) (data : ByteArray) : Prop :=
  w.position ≤ data.size * 8 ∧
    ∀ i < w.position,
      ((data[i / 8]?.getD 0).toNat).testBit (i % 8) = w.bitValue i

theorem Bw.Realizes.field {w : Bw} {data : ByteArray} (hr : w.Realizes data)
    {start width value : Nat} (hf : w.Field start width value) :
    BitField data start width value := by
  refine ⟨Nat.le_trans hf.1 hr.1, ?_⟩
  intro k hk
  have hi : start + k < w.position := by have := hf.1; dsimp only [Bw.position]; omega
  have he := congrArg Bool.toNat ((hr.2 _ hi).trans (hf.2 k hk))
  simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using he

theorem Bw.Realizes.prefix {a b : Bw} {data : ByteArray}
    (hr : b.Realizes data) (he : b.Extends a) : a.Realizes data :=
  ⟨Nat.le_trans he.1 hr.1, fun i hi =>
    (hr.2 i (Nat.lt_of_lt_of_le hi he.1)).trans (he.2 i hi)⟩

theorem Bw.Realizes.push {w : Bw} {data : ByteArray} (hr : w.Realizes data) (b : UInt8) :
    w.Realizes (data.push b) := by
  constructor
  · have := hr.1
    simp only [ByteArray.size_push]
    omega
  · intro i hi
    have hb : i / 8 < data.size := by have := hr.1; omega
    simpa only [getElem?_push, hb, ite_true] using hr.2 i hi

theorem flush_realizes_exact (w : Bw) (hw : w.Valid) : w.Realizes w.flush :=
  ⟨by simpa only [Bw.position, Nat.mul_comm] using flush_position_between w hw,
    fun i hi => flush_bits_exact w hw i hi⟩

/-- Appending a checksum byte cannot change an earlier bit field. -/
theorem BitField.push {data : ByteArray} {start width value : Nat}
    (hf : BitField data start width value) (b : UInt8) :
    BitField (data.push b) start width value := by
  constructor
  · have := hf.1
    simp only [ByteArray.size_push]
    omega
  · intro k hk
    have hb : (start + k) / 8 < data.size := by have := hf.1; omega
    simpa only [getElem?_push, hb, ite_true] using hf.2 k hk

/-- A production Huffman code stays decodable in the final stream after any
later writes, byte draining, padding, and trailing bytes. -/
theorem packageMerge_push_decode_exact (freqs : Array Nat) (limit : Nat) (w : Bw)
    (data : ByteArray) (s : Nat) (hw : w.Valid)
    (hl : 0 < limit ∧ limit ≤ 15) (hfit : freqs.size ≤ 2 ^ limit)
    (hs : 0 < freqs[s]?.getD 0)
    (hr : (w.push ((canonCodes (PackageMerge.lengths freqs limit))[s]?.getD 0)
      ((PackageMerge.lengths freqs limit)[s]?.getD 0)).Realizes data) :
    (mkHuff (PackageMerge.lengths freqs limit)).decode {data, bitPos := w.position} =
      some (s, {data, bitPos :=
        w.position + (PackageMerge.lengths freqs limit)[s]?.getD 0}) := by
  have hc := PackageMerge.lengths_contract freqs limit hl.1 hfit
  have hi : s < freqs.size := by
    by_cases hi : s < freqs.size
    · exact hi
    · simp only [getElem?_neg freqs s hi, Option.getD_none] at hs
      omega
  have hb : ∀ k < (PackageMerge.lengths freqs limit).size,
      (PackageMerge.lengths freqs limit)[k]?.getD 0 ≤ 15 :=
    fun k _ => Nat.le_trans (hc.1.width_le k) hl.2
  apply packageMerge_decode_exact freqs limit _ s hl hfit hs
  apply hr.field
  apply push_field_exact w _ _ hw (by have := hb s (by simpa [hc.1.size_eq] using hi); omega)
  rw [(canonCodes_exact _ hb).2 s (by simpa [hc.1.size_eq] using hi)]
  exact Canonical.reverseBits_between _ _

/-- Realization preserves each completed byte, including the zlib wrapper. -/
theorem Bw.Realizes.byte_exact {w : Bw} {data : ByteArray} (hr : w.Realizes data)
    (i : Nat) (hi : i < w.out.size) : data[i]? = w.out[i]? := by
  have hd : i < data.size := by have := hr.1; dsimp only [Bw.position] at this; omega
  rw [getElem?_pos data i hd, getElem?_pos w.out i hi]
  congr 1
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · have hb : 8 * i + k < 8 * w.out.size := by omega
    have hpos : 8 * i + k < w.position := by dsimp only [Bw.position]; omega
    have hdiv : (8 * i + k) / 8 = i := by omega
    have hmod : (8 * i + k) % 8 = k := by omega
    simpa only [Bw.bitValue, hb, ite_true, hdiv, hmod,
      getElem?_pos data i hd, getElem?_pos w.out i hi, Option.getD_some] using hr.2 _ hpos
  · have hbound : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt8.toNat_lt _) hbound),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt8.toNat_lt _) hbound)]

end LeanTex.Core.Flate
