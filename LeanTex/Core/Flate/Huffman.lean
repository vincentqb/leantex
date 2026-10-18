module

public import LeanTex.Core.Flate.Error
import LeanTex.Core.Flate.BitPacking
import all LeanTex.Core.Flate.Canonical
import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate

public structure Br where
  data : ByteArray
  bitPos : Nat

public def Br.bit (r : Br) : Option (Nat × Br) :=
  match r.data[r.bitPos / 8]? with
  | none => Option.none
  | some b => some ((b.toNat >>> (r.bitPos % 8)) &&& 1, { r with bitPos := r.bitPos + 1 })

/-- Bit `pos % 8` of a byte, counted from its least significant. -/
@[inline] def bitAt (b : UInt8) (pos : Nat) : UInt8 := (b >>> (pos % 8).toUInt8) &&& 1

theorem bitAt_toNat (b : UInt8) (pos : Nat) : (bitAt b pos).toNat = (b.toNat >>> (pos % 8)) &&& 1 := by
  have h8 : pos % 8 < 8 := Nat.mod_lt _ (by decide)
  have hs : (UInt8.ofNat (pos % 8)).toNat = pos % 8 :=
    UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)
  simp only [bitAt, UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.toUInt8, hs, Nat.mod_eq_of_lt h8]
  rfl

theorem bitAt_toUInt64 (b : UInt8) (pos : Nat) :
    (bitAt b pos).toUInt64 = ((b.toNat >>> (pos % 8)) &&& 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, bitAt_toNat, Nat.toUInt64, UInt64.toNat_ofNat']
  have : (b.toNat >>> (pos % 8)) &&& 1 ≤ 1 := Nat.and_le_right
  omega

/-- The bits from `k` on of an `n`-bit field read LSB-first from bit `pos`, OR-ed into `acc`. -/
def bitsGo (data : ByteArray) (n k : Nat) (acc : UInt64) (pos : Nat) : Option (Nat × Nat) :=
  if k < n then
    if h : pos / 8 < data.size then
      bitsGo data n (k + 1) (acc ||| ((bitAt data[pos / 8] pos).toUInt64 <<< k.toUInt64)) (pos + 1)
    else none
  else some (acc.toNat, pos)
termination_by n - k

/-- Reads `n ≤ 16` bits, LSB-first. -/
@[inline] public def Br.bits (r : Br) (n : Nat) : Option (Nat × Br) :=
  (bitsGo r.data n 0 0 r.bitPos).map fun p => (p.1, { r with bitPos := p.2 })

/-- A little-endian bit field in the actual input bytes. -/
def BitField (data : ByteArray) (start width value : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        (value >>> k) &&& 1

public theorem Br.bits_zero_exact (r : Br) : r.bits 0 = some (0, r) := by
  unfold Br.bits bitsGo
  rfl

theorem bitsGo_exact (data : ByteArray) (start n v : Nat) (hn : n < 64)
    (hf : BitField data start n v) :
    ∀ m k, k + m = n →
      bitsGo data n k (v % 2 ^ k).toUInt64 (start + k) = some (v % 2 ^ n, start + n)
  | 0, k, hk => by
    subst hk
    unfold bitsGo
    simp only [Nat.add_zero, Nat.lt_irrefl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq,
      and_true]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt v (Nat.two_pow_pos k))
      (Nat.pow_le_pow_right (by decide) (by omega)))
  | m + 1, k, hk => by
    have hindex : (start + k) / 8 < data.size := by have := hf.1; omega
    have heq := hf.2 k (by omega)
    simp only [getElem?_pos data ((start + k) / 8) hindex, Option.getD_some] at heq
    unfold bitsGo
    simp only [show k < n by omega, ↓reduceIte, hindex, ↓reduceDIte, bitAt_toUInt64, heq]
    have hacc : (v % 2 ^ k).toUInt64 ||| (((v >>> k) &&& 1).toUInt64 <<< k.toUInt64) =
        (v % 2 ^ (k + 1)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [BitPacking.appendBit_exact v k (by omega)]
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
        (Nat.mod_lt v (Nat.two_pow_pos (k + 1)))
        (Nat.pow_le_pow_right (by decide) (show k + 1 ≤ 64 by omega)))).symm
    rw [hacc, show start + k + 1 = start + (k + 1) by omega]
    exact bitsGo_exact data start n v hn hf m (k + 1) (by omega)

theorem bitField_bits_exact (r : Br) (n v : Nat) (hn : n < 64)
    (hv : v < 2 ^ n) (hf : BitField r.data r.bitPos n v) :
    r.bits n = some (v, { r with bitPos := r.bitPos + n }) := by
  have h := bitsGo_exact r.data r.bitPos n v hn hf n 0 (by omega)
  simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, Nat.mod_eq_of_lt hv] at h
  simp only [Br.bits]
  rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, h, Option.map_some]

/-- A canonical Huffman table: code counts per length and symbols in canonical order; a code the
lengths leave unassigned fails at decode. -/
public structure Huff where
  counts : Array Nat
  symbols : Array Nat

/-- The width counts of `lengths`, ignoring zero and widths above fifteen. -/
def CountsFor (lengths : List Nat) (counts : Array Nat) : Prop :=
  counts.size = 16 ∧ ∀ k, counts[k]?.getD 0 =
    if 0 < k ∧ k < 16 then lengths.count k else 0

theorem huffCounts_loop_exact (lengths : Array Nat) :
    CountsFor lengths.toList (Id.run do
      let mut counts := Array.replicate 16 0
      for l in lengths do
        if l > 0 && l < 16 then
          counts := counts.set! l (counts[l]?.getD 0 + 1)
      return counts) := by
  simp only [Id.run, bind, pure]
  apply Progress.forIn_array_exact CountsFor (CountsFor lengths.toList) _ lengths _
  · constructor
    · simp
    · intro k
      by_cases hk : k < 16 <;> simp [hk]
  · intro before l _ _ counts hc
    simp only [Id.run, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hl : 0 < l ∧ l < 16
    · simp only [hl]
      change CountsFor (before ++ [l]) (counts.set! l (counts[l]?.getD 0 + 1))
      refine ⟨by simpa only [Array.size_set!] using hc.1, ?_⟩
      intro k
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases he : l = k
      · subst k
        have hi : l < counts.size := by have := hc.1; omega
        simp only [ite_true, hi, Option.getD_some]
        rw [hc.2 l]
        simp [hl]
      · simp only [he, ite_false, hc.2 k, List.count_append,
          List.count_singleton, beq_iff_eq, Nat.add_zero]
    · simp only [hl, ite_false]
      change CountsFor (before ++ [l]) counts
      refine ⟨hc.1, ?_⟩
      intro k
      rw [hc.2 k, List.count_append, List.count_singleton]
      by_cases hk : 0 < k ∧ k < 16
      · have he : l ≠ k := by rintro rfl; exact hl hk
        simp only [hk, beq_iff_eq, he, ite_false, Nat.add_zero]
      · simp only [hk, ite_false]
  · intro counts hc
    exact hc

def huffCounts (lengths : Array Nat) : Array Nat := Id.run do
  let mut counts : Array Nat := Array.replicate 16 0
  for l in lengths do
    if l > 0 && l < 16 then
      counts := counts.set! l (counts[l]?.getD 0 + 1)
  return counts

def huffSymbols (lengths : Array Nat) : Array Nat := Id.run do
  let mut symbols : Array Nat := #[]
  for len in [1:16] do
    for s in [0:lengths.size] do
      if lengths[s]?.getD 0 == len then
        symbols := symbols.push s
  return symbols

public def mkHuff (lengths : Array Nat) : Huff :=
  { counts := huffCounts lengths, symbols := huffSymbols lengths }

/-- The code space the codes occupy: their integer Kraft sum at fifteen bits, of `2 ^ 15`. -/
public def Huff.used (h : Huff) : Nat :=
  Canonical.start (fun k => h.counts[k]?.getD 0) 15 + h.counts[15]?.getD 0

/-- Whether zlib's inflate admits the codes: they fill the code space, or, for a payload table
(`sparse`), they are one one-bit code or none at all. -/
public def Huff.admits (h : Huff) (sparse : Bool) : Bool :=
  h.used == 2 ^ 15 ||
    sparse && (h.used == 0 || h.used == 2 ^ 14 && h.counts[1]?.getD 0 == 1)

/-- The canonical table of `lengths` where zlib's inflate admits it (`Huff.admits`). -/
public def mkHuff? (lengths : Array Nat) (sparse : Bool) : Option Huff :=
  let h := mkHuff lengths
  if h.admits sparse then some h else none

/-- The canonical decode from code length `len` on: the code so far, the first code and the symbol
index of that length, and the next bit's position. -/
def decodeGo (h : Huff) (data : ByteArray) (len : Nat) (code : UInt64) (first index pos : Nat) :
    Option (Nat × Nat) :=
  if len < 16 then
    if hp : pos / 8 < data.size then
      let code := (code <<< 1) ||| (bitAt data[pos / 8] pos).toUInt64
      let count := h.counts[len]?.getD 0
      if code.toNat < first + count then
        some (h.symbols[index + (code.toNat - first)]?.getD 0, pos + 1)
      else decodeGo h data (len + 1) code ((first + count) * 2) (index + count) (pos + 1)
    else none
  else none
termination_by 16 - len

/-- Decode one symbol, MSB-first, bounded by the 15-bit maximum length. -/
@[inline] public def Huff.decode (h : Huff) (r : Br) : Option (Nat × Br) :=
  (decodeGo h r.data 1 0 0 0 r.bitPos).map fun p => (p.1, { r with bitPos := p.2 })

/-- A codeword's most-significant-first bits in the actual byte stream. -/
def CodeField (data : ByteArray) (start width code : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        code / 2 ^ (width - 1 - k) % 2

theorem BitField.codeField {data : ByteArray} {start width code : Nat}
    (hf : BitField data start width (Canonical.reverseBits code width)) :
    CodeField data start width code := by
  refine ⟨hf.1, ?_⟩
  intro k hk
  rw [hf.2 k hk]
  have hb := congrArg Bool.toNat (Canonical.reverseBits_bit_exact code width k hk)
  simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using hb

/-- A code's prefix one bit longer, appended as the low bit of the shorter prefix. -/
theorem codeStep_exact (code cut : Nat) (hcode : code < 2 ^ 16) :
    ((code / 2 ^ (cut + 1)).toUInt64 <<< 1) ||| (code / 2 ^ cut % 2).toUInt64 =
      (code / 2 ^ cut).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hhi : code / 2 ^ (cut + 1) < 2 ^ (64 - 1) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hpack := BitPacking.packBits_exact (code / 2 ^ (cut + 1)) (code / 2 ^ cut % 2) 1
    (by decide) (Nat.mod_lt _ (by decide)) hhi
  rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, hpack, Nat.pow_one,
    Canonical.readBit_prefix_exact]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))).symm

theorem decodeGo_exact (h : Huff) (data : ByteArray) (start width code : Nat)
    (hw : 1 ≤ width ∧ width ≤ 15) (hcode : code < 2 ^ width)
    (hf : CodeField data start width code)
    (hlo : Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) ≤ code)
    (hhi : code <
      Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) +
        h.counts[width]?.getD 0) :
    ∀ m k, k + m = width → 1 ≤ k →
      decodeGo h data k (code / 2 ^ (width + 1 - k)).toUInt64
          (Canonical.first (fun k => h.counts[k]?.getD 0) (k - 1))
          (Canonical.index (fun k => h.counts[k]?.getD 0) (k - 1)) (start + (k - 1)) =
        some (h.symbols[Canonical.index (fun k => h.counts[k]?.getD 0) (width - 1) +
          (code - Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1))]?.getD 0,
          start + width)
  | m, k, hk, hk1 => by
    have hindex : (start + (k - 1)) / 8 < data.size := by
      have := hf.1
      omega
    have heq := hf.2 (k - 1) (by omega)
    have he1 : width - 1 - (k - 1) = width - k := by omega
    simp only [getElem?_pos data ((start + (k - 1)) / 8) hindex, Option.getD_some, he1] at heq
    unfold decodeGo
    simp only [show k < 16 by omega, ↓reduceIte, hindex, ↓reduceDIte, bitAt_toUInt64, heq]
    have he : width + 1 - k = (width - k) + 1 := by omega
    have hsmall : code < 2 ^ 16 := Nat.lt_of_lt_of_le hcode (Nat.pow_le_pow_right (by decide) (by omega))
    rw [he, codeStep_exact code (width - k) hsmall]
    have hnat : (code / 2 ^ (width - k)).toUInt64.toNat = code / 2 ^ (width - k) := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
    rw [hnat]
    by_cases hlast : k = width
    · subst k
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
      split
      · simp only [Option.some.injEq, Prod.mk.injEq, true_and]
        omega
      · next hne => exact absurd hhi hne
    · have hskip := Canonical.first_prefix_between (fun k => h.counts[k]?.getD 0) width k code hk1
        (by omega) hlo
      split
      · next hlt => exact absurd hlt (Nat.not_lt.mpr hskip)
      · have hk1' : k - 1 + 1 = k := by omega
        have hw1 : width + 1 - (k + 1) = width - k := by omega
        have hfirst : Canonical.first (fun k => h.counts[k]?.getD 0) k =
            (Canonical.first (fun k => h.counts[k]?.getD 0) (k - 1) + h.counts[k]?.getD 0) * 2 := by
          simpa only [hk1'] using
            (show Canonical.first (fun k => h.counts[k]?.getD 0) (k - 1 + 1) =
              (Canonical.first (fun k => h.counts[k]?.getD 0) (k - 1) +
                h.counts[k - 1 + 1]?.getD 0) * 2 from rfl)
        have hidx : Canonical.index (fun k => h.counts[k]?.getD 0) k =
            Canonical.index (fun k => h.counts[k]?.getD 0) (k - 1) + h.counts[k]?.getD 0 := by
          simpa only [hk1'] using
            (show Canonical.index (fun k => h.counts[k]?.getD 0) (k - 1 + 1) =
              Canonical.index (fun k => h.counts[k]?.getD 0) (k - 1) +
                h.counts[k - 1 + 1]?.getD 0 from rfl)
        have hnext := decodeGo_exact h data start width code hw hcode hf hlo hhi (m - 1) (k + 1)
          (by omega) (by omega)
        simp only [Nat.add_sub_cancel, hw1] at hnext
        rw [← hnext, ← hfirst, ← hidx, show start + (k - 1) + 1 = start + k by omega]
termination_by m => m
decreasing_by omega

theorem huff_decode_exact (h : Huff) (r : Br) (width code : Nat)
    (hw : 1 ≤ width ∧ width ≤ 15) (hcode : code < 2 ^ width)
    (hf : CodeField r.data r.bitPos width code)
    (hlo : Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) ≤ code)
    (hhi : code <
      Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) +
        h.counts[width]?.getD 0) :
    h.decode r = some
      (h.symbols[Canonical.index (fun k => h.counts[k]?.getD 0) (width - 1) +
        (code - Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1))]?.getD 0,
        {r with bitPos := r.bitPos + width}) := by
  have hgo := decodeGo_exact h r.data r.bitPos width code hw hcode hf hlo hhi (width - 1) 1
    (by omega) (by omega)
  simp only [Nat.sub_self, Nat.add_zero, Nat.add_sub_cancel] at hgo
  rw [Nat.div_eq_of_lt hcode] at hgo
  simp only [Huff.decode]
  rw [show ((0 : Nat).toUInt64) = 0 from rfl] at hgo
  rw [show Canonical.first (fun k => h.counts[k]?.getD 0) 0 = 0 from rfl,
    show Canonical.index (fun k => h.counts[k]?.getD 0) 0 = 0 from rfl] at hgo
  rw [hgo, Option.map_some]

def codeStarts (blCount : Array Nat) : Array Nat := Id.run do
  let mut nextCode := Array.replicate 16 0
  let mut code := 0
  for b in [1:16] do
    code := (code + blCount[b - 1]?.getD 0) * 2
    nextCode := nextCode.set! b code
  return nextCode

def reverseCode (code width : Nat) : Nat := Id.run do
  let mut rev := 0
  let mut v := code
  for _ in [0:width] do
    rev := rev * 2 + v % 2
    v := v / 2
  return rev

/-- Canonical codes from lengths (RFC 1951 §3.2.2), bit-reversed for the LSB-first writer. -/
public def canonCodes (lengths : Array Nat) : Array Nat := Id.run do
  let mut nextCode := codeStarts (huffCounts lengths)
  let mut codes := Array.replicate lengths.size 0
  for s in [0:lengths.size] do
    let l := lengths[s]?.getD 0
    if l > 0 then
      let c := nextCode[l]?.getD 0
      nextCode := nextCode.set! l (c + 1)
      codes := codes.set! s (reverseCode c l)
  return codes

theorem canonCodes_reverseBits_exact (code width : Nat) :
    reverseCode code width = Canonical.reverseBits code width := by
  let P (k : Nat) (s : Nat × Nat) : Prop :=
    s = (Canonical.reverseBits code k, code / 2 ^ k)
  simp only [reverseCode, Id.run, bind, pure]
  generalize hres : (forIn [0:width] (0, code) _ : Id (Nat × Nat)) = result
  have hloop : P width result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P width) _ 0 width _ (Nat.zero_le _)
      (by simp [P, Canonical.reverseBits]) _ (fun _ h => h)
    intro k _ _ s hs
    dsimp only [P] at hs
    subst s
    change (Canonical.reverseBits code k * 2 + code / 2 ^ k % 2,
      code / 2 ^ k / 2) = _
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    rfl
  dsimp only [P] at hloop
  rw [hloop]

end LeanTex.Core.Flate
