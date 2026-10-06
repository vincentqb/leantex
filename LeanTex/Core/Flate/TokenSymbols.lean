import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate

def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258]

def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4,
    5, 5, 5, 5, 0]

def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
    769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
    11, 11, 12, 12, 13, 13]

/-- Largest length code whose base is ≤ `len` — code 285 alone covers 258
(RFC 1951 §3.2.5's table). -/
def lenSymOf (len : Nat) : Nat := Id.run do
  let mut sym := 0
  for k in [0:lenBase.size] do
    if lenBase[k]?.getD 999 ≤ len then sym := k
  return sym

def distSymOf (d : Nat) : Nat := Id.run do
  let mut sym := 0
  for k in [0:distBase.size] do
    if distBase[k]?.getD 99999 ≤ d then sym := k
  return sym

/-- `len → length code`, indexed directly by the length (3–258). -/
def lenSymTab : Array Nat := (Array.range 259).map lenSymOf

/-- `dist → distance code` for distances ≤ 256. -/
def distSymTab1 : Array Nat := (Array.range 257).map distSymOf

/-- Distances past 256 bucket by `(d-1) >>> 7`: every base past 256 is
≡ 1 (mod 128), so a bucket never straddles two codes. -/
def distSymTab2 : Array Nat := (Array.range 256).map fun k => distSymOf (k * 128 + 1)

/-- One LZ77 token: a literal byte, or bit 31 set with `(len-3) <<< 15`
and `dist-1` packed beside it. -/
def matchToken (len dist : Nat) : UInt32 :=
  (0x80000000 : UInt32) ||| ((len - 3).toUInt32 <<< 15) ||| (dist - 1).toUInt32

/-- Match payload and tag occupy disjoint bits throughout the RFC range. -/
theorem matchToken_toNat (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    (matchToken len dist).toNat = 2147483648 + (len - 3) * 32768 + (dist - 1) := by
  have hlow31 : (len - 3) * 32768 + (dist - 1) < 2 ^ 31 := by omega
  have hl32 : len - 3 < 2 ^ 32 := by omega
  have hd32 : dist - 1 < 2 ^ 32 := by omega
  have hs32 : (len - 3) * 32768 < 2 ^ 32 := by clear hlow31; omega
  have hd15 : dist - 1 < 2 ^ 15 := by omega
  simp only [matchToken, UInt32.toNat_or, UInt32.toNat_shiftLeft, Nat.toUInt32,
    UInt32.toNat_ofNat', UInt32.reduceToNat, Nat.reduceMod,
    Nat.mod_eq_of_lt hl32, Nat.mod_eq_of_lt hd32, Nat.shiftLeft_eq,
    Nat.reducePow, Nat.mod_eq_of_lt hs32]
  rw [Nat.or_assoc]
  have hlo : ((len - 3) * 32768 ||| (dist - 1)) =
      (len - 3) * 32768 + (dist - 1) := by
    simpa only [Nat.shiftLeft_eq, Nat.reducePow] using
      BitPacking.or_shift_exact (len - 3) (dist - 1) 15 hd15
  rw [hlo, Nat.or_comm]
  change _ ||| 2 ^ 31 = _
  rw [Nat.or_two_pow_eq_add_of_lt hlow31]
  simp only [Nat.reducePow, Nat.add_assoc, Nat.add_comm]

/-- The actual scalar token reader recovers both fields without truncation. -/
theorem matchToken_fields_exact (len dist : Nat) (hl : 3 ≤ len ∧ len ≤ 258)
    (hd : 1 ≤ dist ∧ dist ≤ 32768) :
    (((matchToken len dist >>> 15) &&& 255).toNat + 3 = len) ∧
      ((matchToken len dist &&& 32767).toNat + 1 = dist) ∧
      256 ≤ (matchToken len dist).toNat := by
  simp only [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt32.reduceToNat,
    Nat.reduceMod, matchToken_toNat len dist hl hd, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have mask8 (x : Nat) : x &&& 255 = x % 256 :=
    Nat.and_two_pow_sub_one_eq_mod x 8
  have mask15 (x : Nat) : x &&& 32767 = x % 32768 :=
    Nat.and_two_pow_sub_one_eq_mod x 15
  rw [mask8, mask15]
  omega


/-- A match token read back: its length, its distance, and the distance
code that distance selects — the inverse of `matchToken`'s packing, spelled
once for the two loops that read every token (frequencies, then bits). The
bit work stays in `UInt32`: a `Nat` shift is an out-of-line bignum call
with no scalar fast path, which is `Bw`'s own lesson one loop out. -/
def matchOf (t : UInt32) : Nat × Nat × Nat :=
  let distBits := t &&& 32767
  let dist := distBits.toNat + 1
  ((((t >>> 15) &&& 255).toNat + 3, dist,
    if dist ≤ 256 then distSymTab1[dist]?.getD 0
    else distSymTab2[(distBits >>> 7).toNat]?.getD 0))

end LeanTex.Core.Flate
