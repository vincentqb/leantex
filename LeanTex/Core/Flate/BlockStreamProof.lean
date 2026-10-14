module

import all LeanTex.Core.Flate.BlockStream
import all LeanTex.Core.Flate.TokenCodecProof
import all LeanTex.Core.Flate.DynamicHeaderProof
import LeanTex.Core.Flate.PackageComplete
import LeanTex.Core.Flate.Frequencies

namespace LeanTex.Core.Flate.BlockStream

theorem lengths_contract (tokens : Array UInt32) :
    (257 ≤ (lengths tokens).1.size ∧ (lengths tokens).1.size ≤ 286) ∧
      (1 ≤ (lengths tokens).2.size ∧ (lengths tokens).2.size ≤ 30) ∧
      (∀ s : Nat, (lengths tokens).1[s]?.getD 0 < 16) ∧
      (∀ s : Nat, (lengths tokens).2[s]?.getD 0 < 16) := by
  have hf := TokenBlock.alphabets_contract tokens
  have hl := PackageMerge.lengths_contract (TokenBlock.alphabets tokens).1 15
    (by decide) (Nat.le_trans hf.1.2 (by decide))
  have hd := PackageMerge.lengths_contract (TokenBlock.alphabets tokens).2 15
    (by decide) (Nat.le_trans hf.2.1.2 (by decide))
  dsimp only [lengths]
  exact ⟨by simpa only [hl.1.size_eq] using hf.1,
    by simpa only [hd.1.size_eq] using hf.2.1,
    fun s => Nat.lt_of_le_of_lt (hl.1.width_le s) (by decide),
    fun s => Nat.lt_of_le_of_lt (hd.1.width_le s) (by decide)⟩

private theorem kraft_constant (m v : Nat) (hv : 0 < v ∧ v ≤ 15) :
    Canonical.kraft (List.replicate m v) 15 = m * 2 ^ (15 - v) := by
  simp [Canonical.kraft, Canonical.cost, hv.1, hv.2, List.sum_replicate_nat]

private theorem fill_not_constant (m v : Nat) (hm : 257 ≤ m ∧ m ≤ 286) (hv : 0 < v ∧ v ≤ 15)
    (h : m * 2 ^ (15 - v) = 2 ^ 15) : False := by
  have hsplit : 2 ^ 15 = 2 ^ v * 2 ^ (15 - v) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hv.2]
  rw [hsplit] at h
  have he : m = 2 ^ v := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
  by_cases h8 : v ≤ 8
  · have : 2 ^ v ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) h8
    omega
  · have : 2 ^ 9 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Literal/length lengths over 257 to 286 symbols with an end of block are never one length
throughout: one length cannot fill that code space, and with the end of block alone symbol zero
has none. -/
private theorem literal_lengths_vary (freqs : Array Nat) (hs : 257 ≤ freqs.size ∧ freqs.size ≤ 286)
    (h256 : 0 < freqs[256]?.getD 0) :
    ∃ j < (PackageMerge.lengths freqs 15).size,
      (PackageMerge.lengths freqs 15)[j]?.getD 0 ≠ (PackageMerge.lengths freqs 15)[256]?.getD 0 := by
  have hfit : freqs.size ≤ 2 ^ 15 := Nat.le_trans hs.2 (by decide)
  have hc := PackageMerge.lengths_contract freqs 15 (by decide) hfit
  generalize hlens : PackageMerge.lengths freqs 15 = lens at hc ⊢
  have hsize : lens.size = freqs.size := hc.1.size_eq
  have hv : 0 < lens[256]?.getD 0 := (hc.2 256).mpr h256
  have hw : lens[256]?.getD 0 ≤ 15 := hc.1.width_le 256
  by_cases h0 : 0 < freqs[0]?.getD 0
  · have hk := packageMerge_kraft_exact freqs 15 (by decide) hfit
    rw [PackageMerge.lengths_mass_exact freqs 15 (by decide) hfit
      (Frequencies.live_two freqs 0 256 (by omega) (by omega) (by decide) h0 h256), hlens] at hk
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ x ∈ lens.toList, x = lens[256]?.getD 0 := by
      intro x hx
      obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hx)
      have hjs : j < lens.size := by
        by_cases h : j < lens.size
        · exact h
        · simp [getElem?_neg lens j h] at hj
      refine Classical.byContradiction fun hne => hno ⟨j, hjs, ?_⟩
      rw [hj, Option.getD_some]
      exact hne
    rw [List.eq_replicate_iff.mpr ⟨rfl, hall⟩, kraft_constant _ _ ⟨hv, hw⟩,
      Array.length_toList] at hk
    exact fill_not_constant _ _ ⟨by omega, by omega⟩ ⟨hv, hw⟩ hk
  · have hz : lens[0]?.getD 0 = 0 := by
      have := hc.2 0
      omega
    exact ⟨0, by omega, by omega⟩

/-- A block's code lengths are never one length throughout (`literal_lengths_vary`). -/
theorem lengths_vary (tokens : Array UInt32) :
    ∃ i j, i < ((lengths tokens).1 ++ (lengths tokens).2).size ∧
      j < ((lengths tokens).1 ++ (lengths tokens).2).size ∧
      ((lengths tokens).1 ++ (lengths tokens).2)[i]?.getD 0 ≠
        ((lengths tokens).1 ++ (lengths tokens).2)[j]?.getD 0 := by
  have hf := TokenBlock.alphabets_contract tokens
  have hfit : (TokenBlock.alphabets tokens).1.size ≤ 2 ^ 15 := Nat.le_trans hf.1.2 (by decide)
  have hsize := (PackageMerge.lengths_contract _ 15 (by decide) hfit).1.size_eq
  have hlit : (lengths tokens).1 = PackageMerge.lengths (TokenBlock.alphabets tokens).1 15 := rfl
  obtain ⟨j, hj, hne⟩ := literal_lengths_vary _ hf.1 hf.2.2.1
  rw [← hlit] at hj hne hsize
  refine ⟨j, 256, by simp only [Array.size_append]; omega,
    by simp only [Array.size_append]; omega, ?_⟩
  rw [Array.getElem?_append_left hj, Array.getElem?_append_left (by omega)]
  exact hne

theorem write_contract {raw : ByteArray} {start finish : Nat} {tokens : Array UInt32}
    (ht : TokensFor raw start tokens finish) (w : Bw) (hw : w.Valid) :
    (write tokens w).Valid ∧ (write tokens w).Extends w := by
  let litLens := (lengths tokens).1
  let distLens := (lengths tokens).2
  let w1 := w.push 1 1
  let w2 := w1.push 2 2
  have hc := lengths_contract tokens
  have h1 : w1.Valid := push_valid w 1 1 hw (by decide)
  have h2 : w2.Valid := push_valid w1 2 2 h1 (by decide)
  have hh := DynamicHeader.write_contract litLens distLens w2 h2 hc.2.2.1 hc.2.2.2
  have hp := TokenBlock.writePayload_contract litLens distLens
    (DynamicHeader.write litLens distLens w2) hh.1
    (fun s => Nat.le_of_lt (hc.2.2.1 s)) (fun s => Nat.le_of_lt (hc.2.2.2 s)) ht
  exact ⟨hp.1, hp.2.trans (hh.2.trans ((push_extends_exact w1 2 2 h1 (by decide)).trans
    (push_extends_exact w 1 1 hw (by decide))))⟩

theorem readStep_write_bounded_exact (raw : ByteArray) (maxOut : Nat)
    (hmax : raw.size ≤ maxOut) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    readStep maxOut (ByteArray.empty, {data, bitPos := w.position}) =
      .ok (.inl raw) := by
  let litLens := (lengths tokens).1
  let distLens := (lengths tokens).2
  let w1 := w.push 1 1
  let w2 := w1.push 2 2
  let wh := DynamicHeader.write litLens distLens w2
  have hc := lengths_contract tokens
  have h1 : w1.Valid := push_valid w 1 1 hw (by decide)
  have h2 : w2.Valid := push_valid w1 2 2 h1 (by decide)
  have hh := DynamicHeader.write_contract litLens distLens w2 h2 hc.2.2.1 hc.2.2.2
  have hp := TokenBlock.writePayload_contract litLens distLens wh hh.1
    (fun s => Nat.le_of_lt (hc.2.2.1 s)) (fun s => Nat.le_of_lt (hc.2.2.2 s)) ht
  have rh : wh.Realizes data := hr.prefix hp.2
  have r2 : w2.Realizes data := rh.prefix hh.2
  have r1 : w1.Realizes data := r2.prefix (push_extends_exact w1 2 2 h1 (by decide))
  have b1 := push_bit_exact w data 1 hw (by decide) r1
  have b2 := push_bits_exact w1 data 2 2 h1 (by decide) (by decide) r2
  have bh := DynamicHeader.read_write_exact litLens distLens w2 data h2
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (lengths_vary tokens) rh
  have bp := TokenBlock.read_write_bounded_exact raw maxOut hmax tokens ht wh data hh.1 hr
  have hf := TokenBlock.alphabets_contract tokens
  have k1 := packageMerge_mkHuff?_exact (TokenBlock.alphabets tokens).1 15 true
    ⟨by decide, by decide⟩ (Nat.le_trans hf.1.2 (by decide)) (Or.inl rfl)
  have k2 := packageMerge_mkHuff?_exact (TokenBlock.alphabets tokens).2 15 true
    ⟨by decide, by decide⟩ (Nat.le_trans hf.2.1.2 (by decide)) (Or.inl rfl)
  have heob : ((PackageMerge.lengths (TokenBlock.alphabets tokens).1 15)[256]?.getD 0 == 0) =
      false := by
    have := (PackageMerge.lengths_contract (TokenBlock.alphabets tokens).1 15 (by decide)
      (Nat.le_trans hf.1.2 (by decide))).2 256
    simp only [beq_eq_false_iff_ne]
    have := this.mpr hf.2.2.1
    omega
  dsimp only [w1, w2, wh, litLens, distLens, lengths] at b2 bh bp
  simp only [readStep, b1, b2, readBody, show (2 == 0) = false by decide,
    show (2 == 1) = false by decide, show (2 == 2) = true by decide,
    Bool.false_eq_true, ↓reduceIte, bh, heob, k1, k2, bp, bind, Except.bind, pure, Except.pure]
  rfl

theorem read_write_bounded_exact (raw : ByteArray) (maxOut : Nat)
    (hmax : raw.size ≤ maxOut) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    read {data, bitPos := w.position} ByteArray.empty maxOut = .ok raw := by
  exact DecodeLoop.run_exact (readStep maxOut)
    (ByteArray.empty, {data, bitPos := w.position}) raw 1 (8 * data.size / 3 + 2)
    (.malformed "deflate: no final block")
    (.done (readStep_write_bounded_exact raw maxOut hmax tokens ht w data hw hr))
    (by omega)

theorem read_write_exact (raw : ByteArray) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    read {data, bitPos := w.position} ByteArray.empty raw.size = .ok raw :=
  read_write_bounded_exact raw raw.size (Nat.le_refl _) tokens ht w data hw hr

end LeanTex.Core.Flate.BlockStream
