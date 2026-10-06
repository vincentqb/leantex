module

public import LeanTex.Core.Flate
import all LeanTex.Core.Flate
import LeanTex.Core.Loop

namespace LeanTex.Core.Flate

private def AdlerWords (s : UInt64) : Prop :=
  (s >>> 32).toNat < 65521 ∧ (s &&& 0xFFFFFFFF).toNat < 65521

private theorem packed_words (a b : UInt64) (ha : a.toNat < 65521) (hb : b.toNat < 65521) :
    AdlerWords ((a <<< 32) ||| b) := by
  have hpack : (((a <<< 32) ||| b) : UInt64).toNat = a.toNat * 4294967296 + b.toNat := by
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
    change ((a.toNat <<< 32) % 18446744073709551616 ||| b.toNat) = _
    have hm : a.toNat <<< 32 < 18446744073709551616 := by
      rw [Nat.shiftLeft_eq]
      omega
    rw [Nat.mod_eq_of_lt hm, ← Nat.shiftLeft_add_eq_or_of_lt (show b.toNat < 2^32 by omega)]
    rw [Nat.shiftLeft_eq]
  unfold AdlerWords
  rw [UInt64.toNat_shiftRight, UInt64.toNat_and, hpack]
  change (a.toNat * 4294967296 + b.toNat) >>> 32 < 65521 ∧
    (a.toNat * 4294967296 + b.toNat) &&& (2^32 - 1) < 65521
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem reduced_words (s : UInt64) :
    AdlerWords ((((s >>> 32) % 65521) <<< 32) ||| ((s &&& 0xFFFFFFFF) % 65521)) := by
  apply packed_words
  · exact UInt64.toNat_mod_lt _ (by decide)
  · exact UInt64.toNat_mod_lt _ (by decide)

private theorem adler32_bound (data : ByteArray) : Flate.adler32 data < 256 ^ 4 := by
  unfold Flate.adler32
  apply Loop.bind_of_inv (P := fun p : UInt64 × Nat => AdlerWords p.1)
    (Q := fun n : Nat => n < 256^4)
  · apply Loop.forIn_range_inv (P := fun p : UInt64 × Nat => AdlerWords p.1)
    · change AdlerWords 1
      unfold AdlerWords
      decide
    · intro j hlo hhi p hp
      exact reduced_words _
  · intro p hp
    change ((p.1 >>> 32) * 65536 + (p.1 &&& 0xFFFFFFFF)).toNat < 256^4
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    change ((((p.1 >>> 32).toNat * 65536) % 18446744073709551616 +
      (p.1 &&& 0xFFFFFFFF).toNat) % 18446744073709551616) < 4294967296
    rcases hp with ⟨hh, hl⟩
    omega

private theorem byte_data (b : ByteArray) (i : Nat) : b[i]? = b.data[i]? := rfl

private theorem pushBe32_trailer (b : ByteArray) (v : Nat) (hv : v < 256^4) :
    let raw := Flate.pushBe32 b v
    let n := raw.size
    (raw[n - 4]?.getD 0).toNat * 16777216 + (raw[n - 3]?.getD 0).toNat * 65536 +
      (raw[n - 2]?.getD 0).toNat * 256 + (raw[n - 1]?.getD 0).toNat = v := by
  dsimp only
  simp only [Flate.pushBe32, ByteArray.size_push, byte_data, ByteArray.data_push,
    Array.getElem?_push, Array.size_push, show b.data.size = b.size from rfl]
  simp only [show b.size + 1 + 1 + 1 + 1 - 4 = b.size by omega,
    show b.size + 1 + 1 + 1 + 1 - 3 = b.size + 1 by omega,
    show b.size + 1 + 1 + 1 + 1 - 2 = b.size + 1 + 1 by omega,
    show b.size + 1 + 1 + 1 + 1 - 1 = b.size + 1 + 1 + 1 by omega]
  simp only [show b.size ≠ b.size + 1 by omega,
    show b.size ≠ b.size + 1 + 1 by omega,
    show b.size ≠ b.size + 1 + 1 + 1 by omega,
    show b.size + 1 ≠ b.size + 1 + 1 by omega,
    show b.size + 1 ≠ b.size + 1 + 1 + 1 by omega,
    show b.size + 1 + 1 ≠ b.size + 1 + 1 + 1 by omega,
    ↓reduceIte, Option.getD_some, UInt8.toNat_ofNat', Nat.mod_mod]
  omega

/-- The complete compressor output ends in its Adler-32 checksum. The width
bound is proved over the production loop, without exposing the bit writer. -/
public theorem deflate_checksum_exact (data : ByteArray) :
    let raw := Flate.deflate data
    let n := raw.size
    4 ≤ n ∧
    (raw[n - 4]?.getD 0).toNat * 16777216 + (raw[n - 3]?.getD 0).toNat * 65536 +
      (raw[n - 2]?.getD 0).toNat * 256 + (raw[n - 1]?.getD 0).toNat = Flate.adler32 data := by
  constructor
  · simp only [Flate.deflate, Flate.pushBe32, ByteArray.size_push]
    omega
  · exact pushBe32_trailer _ _ (adler32_bound data)

end LeanTex.Core.Flate
