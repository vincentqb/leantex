import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.Canonical
import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate

structure Br where
  data : ByteArray
  bitPos : Nat

def Br.bit (r : Br) : Option (Nat × Br) :=
  match r.data[r.bitPos / 8]? with
  | none => Option.none
  | some b => some ((b.toNat >>> (r.bitPos % 8)) &&& 1, { r with bitPos := r.bitPos + 1 })

/-- Read `n ≤ 16` bits, LSB-first. The accumulator is a `UInt64`: a `Nat`
shift has no scalar fast path in the runtime. -/
def Br.bits (r : Br) (n : Nat) : Option (Nat × Br) := Id.run do
  let mut r := r
  let mut v : UInt64 := 0
  for k in [0:n] do
    match r.bit with
    | none => return none
    | some (b, r') =>
      v := v ||| (b.toUInt64 <<< k.toUInt64)
      r := r'
  return some (v.toNat, r)

/-- A little-endian bit field in the actual input bytes. -/
def BitField (data : ByteArray) (start width value : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        (value >>> k) &&& 1

/-- Reading a present field recovers its entire value and advances exactly its width.
This invariant follows the existing early-return loop and its `UInt64` accumulator. -/
theorem bitField_bits_exact (r : Br) (n v : Nat) (hn : n < 64)
    (hv : v < 2 ^ n) (hf : BitField r.data r.bitPos n v) :
    r.bits n = some (v, { r with bitPos := r.bitPos + n }) := by
  have hb (k : Nat) (hk : k < n) :
      ({r with bitPos := r.bitPos + k} : Br).bit =
        some ((v >>> k) &&& 1, {r with bitPos := r.bitPos + (k + 1)}) := by
    have hindex : (r.bitPos + k) / 8 < r.data.size := by
      have := hf.1
      omega
    have heq := hf.2 k hk
    simp only [getElem?_pos r.data ((r.bitPos + k) / 8) hindex, Option.getD_some] at heq
    simp only [Br.bit, getElem?_pos r.data ((r.bitPos + k) / 8) hindex, heq, Nat.add_assoc]
  let P (k : Nat) (s : Option (Option (Nat × Br)) × Br × UInt64) : Prop :=
    s = (none, {r with bitPos := r.bitPos + k}, (v % 2 ^ k).toUInt64)
  unfold Br.bits
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:n] (none, r, (0 : UInt64)) _ :
    Id (Option (Option (Nat × Br)) × Br × UInt64)) = result
  have hloop : P n result := by
    rw [← hres]
    apply Progress.forIn_range_exact P (P n) _ 0 n _ (Nat.zero_le _)
      (by simp [P, Nat.mod_one]) _ (fun _ h => h)
    intro k _ hk s hs
    dsimp only [P] at hs
    subst s
    rw [hb k hk]
    change (none, {r with bitPos := r.bitPos + (k + 1)},
      (v % 2 ^ k).toUInt64 ||| (((v >>> k) &&& 1).toUInt64 <<< k.toUInt64)) = _
    congr 2
    apply UInt64.toNat_inj.mp
    rw [BitPacking.appendBit_exact v k (by omega)]
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.mod_lt v (Nat.two_pow_pos (k + 1)))
      (Nat.pow_le_pow_right (by decide) (show k + 1 ≤ 64 by omega)))).symm
  dsimp only [P] at hloop
  rw [hloop]
  simp only [Nat.mod_eq_of_lt hv, Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv
    (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hn)))]


/-- A canonical Huffman table: `counts[len]` codes of each length, and the
symbols in canonical order. The construction never fails; an over-subscribed
set of lengths simply fails to decode, which the caller reports. -/
structure Huff where
  counts : Array Nat
  symbols : Array Nat

/-- Exact width buckets: zero and widths above the RFC's 15-bit limit do
not contribute to the table, including its unused zero-width bucket. -/
def CountsFor (lengths : List Nat) (counts : Array Nat) : Prop :=
  counts.size = 16 ∧ ∀ k, counts[k]?.getD 0 =
    if 0 < k ∧ k < 16 then lengths.count k else 0

/-- The shared counting loop in both Huffman table builders counts precisely
the widths it has consumed. -/
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

def mkHuff (lengths : Array Nat) : Huff :=
  { counts := huffCounts lengths, symbols := huffSymbols lengths }

/-- The decoder's actual table contains exactly the declared width counts. -/
theorem mkHuff_counts_exact (lengths : Array Nat) :
    CountsFor lengths.toList (mkHuff lengths).counts := by
  exact huffCounts_loop_exact lengths

/-- Decode one symbol, MSB-first, bounded by the 15-bit maximum length. -/
def Huff.decode (h : Huff) (r : Br) : Option (Nat × Br) := Id.run do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  let mut r := r
  for len in [1:16] do
    match r.bit with
    | none => return none
    | some (b, r') =>
      r := r'
      code := code * 2 + b
      let count := h.counts[len]?.getD 0
      if code < first + count then
        return some (h.symbols[index + (code - first)]?.getD 0, r)
      index := index + count
      first := (first + count) * 2
  return none

/-- A codeword's most-significant-first bits in the actual byte stream. -/
def CodeField (data : ByteArray) (start width code : Nat) : Prop :=
  start + width ≤ data.size * 8 ∧
    ∀ k < width,
      ((data[(start + k) / 8]?.getD 0).toNat >>> ((start + k) % 8)) &&& 1 =
        code / 2 ^ (width - 1 - k) % 2

/-- Reversing the encoder's value turns the writer's little-endian field into
the decoder's most-significant-first codeword. -/
theorem BitField.codeField {data : ByteArray} {start width code : Nat}
    (hf : BitField data start width (Canonical.reverseBits code width)) :
    CodeField data start width code := by
  refine ⟨hf.1, ?_⟩
  intro k hk
  rw [hf.2 k hk]
  have hb := congrArg Bool.toNat (Canonical.reverseBits_bit_exact code width k hk)
  simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using hb

/-- The actual bounded Huffman decoder recognizes every code in its canonical
interval. Earlier lengths cannot consume a prefix of that code. -/
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
  let count := fun (k : Nat) => h.counts[k]?.getD 0
  let answer := some
    (h.symbols[Canonical.index count (width - 1) +
      (code - Canonical.first count (width - 1))]?.getD 0,
      {r with bitPos := r.bitPos + width})
  let P (k : Nat) (s : Option (Option (Nat × Br)) × Nat × Nat × Nat × Br) : Prop :=
    k ≤ width ∧ s = (none, code / 2 ^ (width + 1 - k),
      Canonical.first count (k - 1), Canonical.index count (k - 1),
      {r with bitPos := r.bitPos + (k - 1)})
  let Q (s : Option (Option (Nat × Br)) × Nat × Nat × Nat × Br) : Prop :=
    s.1 = some answer
  have hb (k : Nat) (hk : 1 ≤ k) (hkw : k ≤ width) :
      ({r with bitPos := r.bitPos + (k - 1)} : Br).bit =
        some (code / 2 ^ (width - k) % 2,
          {r with bitPos := r.bitPos + k}) := by
    have hindex : (r.bitPos + (k - 1)) / 8 < r.data.size := by
      have := hf.1
      omega
    have heq := hf.2 (k - 1) (by omega)
    have he1 : width - 1 - (k - 1) = width - k := by omega
    have he2 : r.bitPos + (k - 1) + 1 = r.bitPos + k := by omega
    simp only [getElem?_pos r.data ((r.bitPos + (k - 1)) / 8) hindex,
      Option.getD_some, he1] at heq
    simp only [Br.bit, getElem?_pos r.data ((r.bitPos + (k - 1)) / 8) hindex,
      heq, he2]
  unfold Huff.decode
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [1:16] (none, 0, 0, 0, r) _ :
    Id (Option (Option (Nat × Br)) × Nat × Nat × Nat × Br)) = result
  have hloop : Q result := by
    rw [← hres]
    apply Progress.forIn_range_exact P Q _ 1 16 _ (by decide) ?_ ?_ ?_
    · simp [P, Canonical.first, Canonical.index, Nat.div_eq_of_lt hcode, hw.1]
    · intro k hk _ s hs
      obtain ⟨hkw, hs⟩ := hs
      subst s
      rw [hb k hk hkw]
      dsimp only
      have he : width + 1 - k = (width - k) + 1 := by omega
      rw [he, Canonical.readBit_prefix_exact]
      by_cases hlast : k = width
      · subst k
        simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
        have hhi' : code <
            Canonical.first count (width - 1) + h.counts[width]?.getD 0 := hhi
        simp only [hhi', ite_true, Id.run, Q, answer]
      · have hskip := Canonical.first_prefix_between count width k code hk (by omega) hlo
        have hskip' : ¬ code / 2 ^ (width - k) <
            Canonical.first count (k - 1) + h.counts[k]?.getD 0 := Nat.not_lt.mpr hskip
        simp only [hskip', ite_false]
        change k + 1 ≤ width ∧
          (none, code / 2 ^ (width - k),
            (Canonical.first count (k - 1) + count k) * 2,
            Canonical.index count (k - 1) + count k,
            {r with bitPos := r.bitPos + k}) = _
        refine ⟨by omega, ?_⟩
        have hk1 : k - 1 + 1 = k := by omega
        have hw1 : width + 1 - (k + 1) = width - k := by omega
        have hfirst : Canonical.first count k =
            (Canonical.first count (k - 1) + count k) * 2 := by
          simpa only [hk1] using
            (show Canonical.first count (k - 1 + 1) =
              (Canonical.first count (k - 1) + count (k - 1 + 1)) * 2 from rfl)
        have hindex : Canonical.index count k =
            Canonical.index count (k - 1) + count k := by
          simpa only [hk1] using
            (show Canonical.index count (k - 1 + 1) =
              Canonical.index count (k - 1) + count (k - 1 + 1) from rfl)
        simp only [hw1, Nat.add_sub_cancel_right, hfirst, hindex]
    · intro s hs
      have := hs.1
      omega
  change result.1 = some answer at hloop
  rw [hloop]

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

/-- Canonical codes from lengths — the same assignment `mkHuff` decodes
(RFC 1951 §3.2.2), each code's bits reversed so the LSB-first writer
emits them most-significant first as §3.1.1 requires. -/
def canonCodes (lengths : Array Nat) : Array Nat := Id.run do
  let mut nextCode := codeStarts (huffCounts lengths)
  let mut codes := Array.replicate lengths.size 0
  for s in [0:lengths.size] do
    let l := lengths[s]?.getD 0
    if l > 0 then
      let c := nextCode[l]?.getD 0
      nextCode := nextCode.set! l (c + 1)
      codes := codes.set! s (reverseCode c l)
  return codes

/-- The bit-reversal loop used by `canonCodes` has exactly the declared bit order.
The invariant records both the reversed prefix and the unconsumed code suffix. -/
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
