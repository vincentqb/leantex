module

import all LeanTex.Core.Flate.Huffman

/-! The production bit writer and its pending-bit and field invariants.
Keeping the state and its equations together lets stream proofs retain earlier
fields while subsequent writes drain the same fixed-width accumulator. -/

namespace LeanTex.Core.Flate

/-- A bit writer, LSB-first within each byte (RFC 1951 §3.1.1: "bits of
each byte starting with the least-significant"). Huffman codes arrive
already bit-reversed (`canonCodes`), so one writer serves codes and extra
bits alike. Fewer than eight bits are pending between pushes, so a push
of at most sixteen drains at most two bytes. Fixed-width arithmetic
throughout: `Nat`'s shift is an out-of-line bignum call with no scalar
fast path (measured at ~80 ns; it was three quarters of the compressor). -/
public structure Bw where
  out : ByteArray
  bits : UInt64
  nbits : UInt64

/-- Append `n` bits of `v` (`n ≤ 16`). -/
public def Bw.pushU (w : Bw) (v n : UInt64) : Bw :=
  let bits := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
  let nbits := w.nbits + n
  if nbits ≥ 16 then
    { out := (w.out.push bits.toUInt8).push (bits >>> 8).toUInt8
      bits := bits >>> 16
      nbits := nbits - 16 }
  else if nbits ≥ 8 then
    { out := w.out.push bits.toUInt8
      bits := bits >>> 8
      nbits := nbits - 8 }
  else
    { w with bits, nbits }

public def Bw.push (w : Bw) (v n : Nat) : Bw := w.pushU v.toUInt64 n.toUInt64

public def Bw.flush (w : Bw) : ByteArray :=
  if w.nbits == 0 then w.out else w.out.push w.bits.toUInt8

/-- The writer has fewer than one byte pending and no set bits above it. -/
def Bw.Valid (w : Bw) : Prop :=
  w.nbits.toNat < 8 ∧ w.bits.toNat < 2 ^ w.nbits.toNat

theorem pushU_payload_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)).toNat =
      w.bits.toNat + v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat := by
  have hn64 : n.toNat < 64 := by omega
  have hmask : (v &&& ((1 <<< n) - 1)).toNat = v.toNat % 2 ^ n.toNat := by
    simpa only [Nat.toUInt64, UInt64.ofNat_toNat] using
      BitPacking.takeBits_exact v n.toNat hn64
  have hhi : (v &&& ((1 <<< n) - 1)).toNat < 2 ^ (64 - w.nbits.toNat) := by
    rw [hmask]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by have := hw.1; omega))
  have hp := BitPacking.packBits_exact
    (v &&& ((1 <<< n) - 1)).toNat w.bits.toNat w.nbits.toNat
    (by have := hw.1; omega) hw.2 hhi
  simp only [Nat.toUInt64, UInt64.ofNat_toNat] at hp
  rw [hmask] at hp
  simpa only [UInt64.or_comm, Nat.add_comm] using hp

theorem pushU_payload_between (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)).toNat <
      2 ^ (w.nbits.toNat + n.toNat) := by
  rw [pushU_payload_exact w v n hw hn, Nat.add_comm, Nat.pow_add]
  have hm := Nat.mod_lt v.toNat (Nat.two_pow_pos n.toNat)
  calc
    v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat + w.bits.toNat
      < v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat + 2 ^ w.nbits.toNat :=
        Nat.add_lt_add_left hw.2 _
    _ = (v.toNat % 2 ^ n.toNat + 1) * 2 ^ w.nbits.toNat := by
      rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ n.toNat * 2 ^ w.nbits.toNat := Nat.mul_le_mul_right _ hm
    _ = _ := Nat.mul_comm _ _


/-- Draining the packed payload emits exactly its complete bytes and retains
exactly its high, incomplete byte. No runtime arithmetic wraps. -/
theorem pushU_pending_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    let total := w.nbits.toNat + n.toNat
    let payload := w.bits.toNat + v.toNat % 2 ^ n.toNat * 2 ^ w.nbits.toNat
    (w.pushU v n).nbits.toNat = total % 8 ∧
      (w.pushU v n).bits.toNat = payload / 2 ^ (total / 8 * 8) ∧
      (w.pushU v n).out.size = w.out.size + total / 8 := by
  have hw8 := hw.1
  have hsum : (w.nbits + n).toNat = w.nbits.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hp := pushU_payload_exact w v n hw hn
  dsimp only
  unfold Bw.pushU
  dsimp only
  split
  · rename_i h16
    have ht : 16 ≤ w.nbits.toNat + n.toNat := by
      simpa [UInt64.le_iff_toNat_le, hsum] using h16
    have hd : (w.nbits.toNat + n.toNat) / 8 = 2 := by omega
    simp only [UInt64.toNat_sub_of_le _ _ h16, hsum, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow, hp, ByteArray.size_push, hd, UInt64.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
    constructor
    · omega
    · constructor
      · trivial
      · trivial
  · rename_i h16
    have ht : w.nbits.toNat + n.toNat < 16 := by
      simp [UInt64.le_iff_toNat_le, hsum] at h16
      omega
    split
    · rename_i h8
      have ht8 : 8 ≤ w.nbits.toNat + n.toNat := by
        simpa [UInt64.le_iff_toNat_le, hsum] using h8
      have hd : (w.nbits.toNat + n.toNat) / 8 = 1 := by omega
      simp only [UInt64.toNat_sub_of_le _ _ h8, hsum, UInt64.toNat_shiftRight,
        Nat.shiftRight_eq_div_pow, hp, ByteArray.size_push, hd, UInt64.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
      constructor
      · omega
      · exact ⟨trivial, trivial⟩
    · rename_i h8
      have ht8 : w.nbits.toNat + n.toNat < 8 := by
        simp [UInt64.le_iff_toNat_le, hsum] at h8
        omega
      simp only [hsum, hp, Nat.div_eq_of_lt ht8, Nat.mod_eq_of_lt ht8,
        Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.add_zero, and_self]


/-- The pending-bit invariant is preserved by every supported writer push. -/
theorem pushU_valid (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) : (w.pushU v n).Valid := by
  have hp := pushU_pending_exact w v n hw hn
  have hb := pushU_payload_between w v n hw hn
  rw [pushU_payload_exact w v n hw hn] at hb
  unfold Bw.Valid
  constructor
  · rw [hp.1]
    exact Nat.mod_lt _ (by decide)
  · rw [hp.1, hp.2.1]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [← Nat.pow_add]
    have he : (w.nbits.toNat + n.toNat) % 8 +
        (w.nbits.toNat + n.toNat) / 8 * 8 = w.nbits.toNat + n.toNat := by omega
    rw [he]
    exact hb

/-- A push advances the bit position by exactly its field width. -/
theorem pushU_position_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    8 * (w.pushU v n).out.size + (w.pushU v n).nbits.toNat =
      8 * w.out.size + w.nbits.toNat + n.toNat := by
  have hp := pushU_pending_exact w v n hw hn
  rw [hp.1, hp.2.2]
  omega


theorem getElem?_push (a : ByteArray) (b : UInt8) (i : Nat) :
    (a.push b)[i]? = if i < a.size then a[i]? else if i = a.size then some b else none := by
  by_cases h1 : i < a.size
  · rw [getElem?_pos (a.push b) i (by rw [ByteArray.size_push]; omega), getElem?_pos a i h1]
    simp only [h1, ↓reduceIte, ByteArray.getElem_eq_getElem_data, ByteArray.data_push]
    exact congrArg some (Array.getElem_push_lt h1)
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i = a.size
    · subst h2
      rw [getElem?_pos (a.push b) a.size (by rw [ByteArray.size_push]; omega)]
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, Array.getElem_push]
    · simp only [h2, ↓reduceIte]
      exact getElem?_neg (a.push b) i (by rw [ByteArray.size_push]; omega)

/-- The infinite zero-padded bit view of completed bytes and pending payload. -/
def Bw.bitValue (w : Bw) (i : Nat) : Bool :=
  if i < 8 * w.out.size then
    ((w.out[i / 8]?.getD 0).toNat).testBit (i % 8)
  else w.bits.toNat.testBit (i - 8 * w.out.size)

private theorem drainByte_bits_exact (out : ByteArray) (bits n n' : UInt64) (i : Nat) :
    ({out := out.push bits.toUInt8, bits := bits >>> 8, nbits := n'} : Bw).bitValue i =
      ({out, bits, nbits := n} : Bw).bitValue i := by
  unfold Bw.bitValue
  dsimp only
  rw [ByteArray.size_push]
  by_cases h : i < 8 * out.size
  · have h' : i < 8 * (out.size + 1) := by omega
    have hi : i / 8 < out.size := by omega
    simp only [h, h', ite_true, getElem?_push, hi]
  · by_cases h' : i < 8 * (out.size + 1)
    · have hi : i / 8 = out.size := by omega
      have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
      have he : i - 8 * out.size = i % 8 := by omega
      simp only [h, h', ite_true, ite_false, getElem?_push, hi, Nat.lt_irrefl,
        Option.getD_some, UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, hk,
        decide_true, Bool.true_and, he]
    · have he : 8 + (i - 8 * (out.size + 1)) = i - 8 * out.size := by omega
      simp [h, h', UInt64.toNat_shiftRight, Nat.testBit_shiftRight, he]

private theorem pushU_drain_bits (w : Bw) (v n : UInt64) (i : Nat) :
    (w.pushU v n).bitValue i =
      ({ w with
          bits := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
          nbits := w.nbits + n } : Bw).bitValue i := by
  let p := w.bits ||| ((v &&& ((1 <<< n) - 1)) <<< w.nbits)
  have hr : (p >>> 8) >>> 8 = p >>> 16 := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, ← Nat.shiftRight_add]
  unfold Bw.pushU
  dsimp only
  split
  · change ({ out := (w.out.push p.toUInt8).push (p >>> 8).toUInt8
              bits := p >>> 16
              nbits := _ } : Bw).bitValue i = _
    rw [← hr]
    exact (drainByte_bits_exact (w.out.push p.toUInt8) (p >>> 8) 0 0 i).trans
      (drainByte_bits_exact w.out p 0 0 i)
  · split
    · exact drainByte_bits_exact w.out p 0 0 i
    · rfl

/-- Appending a field preserves every old bit and supplies exactly its new bits. -/
theorem pushU_bits_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) (i : Nat)
    (hi : i < 8 * w.out.size + w.nbits.toNat + n.toNat) :
    (w.pushU v n).bitValue i =
      if i < 8 * w.out.size + w.nbits.toNat then w.bitValue i
      else v.toNat.testBit (i - (8 * w.out.size + w.nbits.toNat)) := by
  rw [pushU_drain_bits]
  by_cases ho : i < 8 * w.out.size
  · have hp : i < 8 * w.out.size + w.nbits.toNat := by omega
    simp only [Bw.bitValue, ho, hp, ite_true]
  · have hp := BitPacking.packField_bits_exact w.bits.toNat v.toNat
      w.nbits.toNat n.toNat (i - 8 * w.out.size) hw.2 (by omega)
    simp only [Bw.bitValue, ho, ite_false, pushU_payload_exact w v n hw hn]
    rw [hp]
    by_cases hh : i < 8 * w.out.size + w.nbits.toNat
    · have hl : i - 8 * w.out.size < w.nbits.toNat := by omega
      simp only [hh, hl, ite_true]
    · have hl : ¬ i - 8 * w.out.size < w.nbits.toNat := by omega
      have he : i - 8 * w.out.size - w.nbits.toNat =
          i - (8 * w.out.size + w.nbits.toNat) := by omega
      simp only [hh, hl, ite_false, he]

theorem flush_position_between (w : Bw) (hw : w.Valid) :
    8 * w.out.size + w.nbits.toNat ≤ 8 * w.flush.size := by
  by_cases hn : w.nbits = 0
  · simp [Bw.flush, hn]
  · simp only [Bw.flush, beq_iff_eq, hn, ite_false, ByteArray.size_push]
    have := hw.1
    omega

theorem flush_bits_exact (w : Bw) (hw : w.Valid) (i : Nat)
    (hi : i < 8 * w.out.size + w.nbits.toNat) :
    ((w.flush[i / 8]?.getD 0).toNat).testBit (i % 8) = w.bitValue i := by
  by_cases hn : w.nbits = 0
  · have ho : i < 8 * w.out.size := by simpa [hn] using hi
    simp only [Bw.flush, hn, beq_self_eq_true, ite_true, Bw.bitValue, ho]
  · by_cases ho : i < 8 * w.out.size
    · have hb : i / 8 < w.out.size := by omega
      simp only [Bw.flush, beq_iff_eq, hn, ite_false, Bw.bitValue, ho, ite_true,
        getElem?_push, hb]
    · have hs := hw.1
      have hb : i / 8 = w.out.size := by omega
      have he : i - 8 * w.out.size = i % 8 := by omega
      have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
      simp only [Bw.flush, beq_iff_eq, hn, ite_false, Bw.bitValue, ho,
        getElem?_push, hb, Nat.lt_irrefl, ite_true, Option.getD_some,
        UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, hk, decide_true,
        Bool.true_and, he]

/-- A field already written, including the writer's pending incomplete byte. -/
def Bw.Field (w : Bw) (start width value : Nat) : Prop :=
  start + width ≤ 8 * w.out.size + w.nbits.toNat ∧
    ∀ k < width, w.bitValue (start + k) = value.testBit k

theorem Bw.Field.pushU (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) {start width value : Nat} (hf : w.Field start width value) :
    (w.pushU v n).Field start width value := by
  constructor
  · rw [pushU_position_exact w v n hw hn]
    have := hf.1
    omega
  · intro k hk
    have hh : start + k < 8 * w.out.size + w.nbits.toNat := by have := hf.1; omega
    rw [pushU_bits_exact w v n hw hn _ (by omega)]
    simpa only [hh, ite_true] using hf.2 k hk

theorem pushU_field_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) :
    (w.pushU v n).Field (8 * w.out.size + w.nbits.toNat) n.toNat v.toNat := by
  constructor
  · rw [pushU_position_exact w v n hw hn]
    exact Nat.le_refl _
  · intro k hk
    have hh : ¬ 8 * w.out.size + w.nbits.toNat + k <
        8 * w.out.size + w.nbits.toNat := by omega
    rw [pushU_bits_exact w v n hw hn _ (by omega)]
    simp only [hh, ite_false, Nat.add_sub_cancel_left]

theorem Bw.Field.flush (w : Bw) (hw : w.Valid) {start width value : Nat}
    (hf : w.Field start width value) : BitField w.flush start width value := by
  constructor
  · simpa only [Nat.mul_comm] using Nat.le_trans hf.1 (flush_position_between w hw)
  · intro k hk
    have hi : start + k < 8 * w.out.size + w.nbits.toNat := by have := hf.1; omega
    have he := congrArg Bool.toNat ((flush_bits_exact w hw _ hi).trans (hf.2 k hk))
    simpa only [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using he

/-- A field pushed through the actual writer is read back by the actual reader. -/
theorem pushU_read_exact (w : Bw) (v n : UInt64) (hw : w.Valid)
    (hn : n.toNat ≤ 16) (hv : v.toNat < 2 ^ n.toNat) :
    ({data := (w.pushU v n).flush, bitPos := 8 * w.out.size + w.nbits.toNat} : Br).bits
        n.toNat =
      some (v.toNat, { data := (w.pushU v n).flush
                       bitPos := 8 * w.out.size + w.nbits.toNat + n.toNat }) := by
  exact bitField_bits_exact _ _ _ (by omega) hv
    (Bw.Field.flush (w.pushU v n) (pushU_valid w v n hw hn)
      (pushU_field_exact w v n hw hn))

/-- A bounded canonical code written by the actual bit writer is decoded by
the actual Huffman decoder, at any valid starting byte alignment. The table
interval identifies the decoded symbol; constructing that interval is separate. -/
theorem push_huff_decode_exact (w : Bw) (h : Huff) (width code : Nat)
    (hw : w.Valid) (hwidth : 1 ≤ width ∧ width ≤ 15) (hcode : code < 2 ^ width)
    (hlo : Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) ≤ code)
    (hhi : code <
      Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1) +
        h.counts[width]?.getD 0) :
    h.decode
      { data := (w.push (Canonical.reverseBits code width) width).flush
        bitPos := 8 * w.out.size + w.nbits.toNat } =
      some
        (h.symbols[Canonical.index (fun k => h.counts[k]?.getD 0) (width - 1) +
          (code - Canonical.first (fun k => h.counts[k]?.getD 0) (width - 1))]?.getD 0,
          { data := (w.push (Canonical.reverseBits code width) width).flush
            bitPos := 8 * w.out.size + w.nbits.toNat + width }) := by
  have hn64 : width < 2 ^ 64 := by omega
  have hn : width.toUInt64.toNat = width := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64]
  have hr64 : Canonical.reverseBits code width < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Canonical.reverseBits_between _ _)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hr : (Canonical.reverseBits code width).toUInt64.toNat =
      Canonical.reverseBits code width := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hr64]
  have hn16 : width.toUInt64.toNat ≤ 16 := by omega
  apply huff_decode_exact _ _ _ _ hwidth hcode _ hlo hhi
  apply BitField.codeField
  simpa only [Bw.push, hn, hr] using
    (Bw.Field.flush
      (w.pushU (Canonical.reverseBits code width).toUInt64 width.toUInt64)
      (pushU_valid w _ _ hw hn16)
      (pushU_field_exact w _ _ hw hn16))


end LeanTex.Core.Flate
