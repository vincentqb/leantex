module

public import LeanTex.Core.Flate
import all LeanTex.Core.Flate
import LeanTex.Core.Loop

namespace LeanTex.Core.Flate

private theorem adlerFrom_words (data : ByteArray) (i : Nat) (a b : UInt64) :
    a.toNat < 65521 → b.toNat < 65521 →
      (adlerFrom data i a b).1.toNat < 65521 ∧ (adlerFrom data i a b).2.toNat < 65521 := by
  fun_induction adlerFrom data i a b with
  | case1 _ _ _ _ _ ih =>
    intro _ _
    exact ih (UInt64.toNat_mod_lt _ (by decide)) (UInt64.toNat_mod_lt _ (by decide))
  | case2 => intro ha hb; exact ⟨ha, hb⟩

private theorem adler32_bound (data : ByteArray) : Flate.adler32 data < 256 ^ 4 := by
  obtain ⟨ha, hb⟩ := adlerFrom_words data 0 1 0 (by decide) (by decide)
  unfold Flate.adler32
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  change ((((adlerFrom data 0 1 0).2.toNat * 65536) % 18446744073709551616 +
    (adlerFrom data 0 1 0).1.toNat) % 18446744073709551616) < 4294967296
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
