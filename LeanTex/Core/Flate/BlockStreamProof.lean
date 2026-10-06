import LeanTex.Core.Flate.BlockStream
import LeanTex.Core.Flate.TokenCodecProof
import LeanTex.Core.Flate.DynamicHeaderProof

namespace LeanTex.Core.Flate.BlockStream

/-- The actual frequency-derived alphabets fit the dynamic header's RFC
counts and all their transmitted lengths fit a four-bit value. -/
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

/-- Writing a complete dynamic block preserves every bit before the block. -/
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

/-- The final dynamic block is read by the actual outer decoder as a complete
stream, after reading its transmitted tables and every payload symbol. -/
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
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 rh
  have bp := TokenBlock.read_write_bounded_exact raw maxOut hmax tokens ht wh data hh.1 hr
  dsimp only [w1, w2, wh, litLens, distLens, lengths] at b2 bh bp
  simp only [readStep, b1, b2, readBody, show (2 == 0) = false by decide,
    show (2 == 1) = false by decide, show (2 == 2) = true by decide,
    Bool.false_eq_true, ↓reduceIte, bh, bp, bind, Except.bind, pure, Except.pure]
  rfl

theorem readStep_write_exact (raw : ByteArray) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    readStep raw.size (ByteArray.empty, {data, bitPos := w.position}) =
      .ok (.inl raw) :=
  readStep_write_bounded_exact raw raw.size (Nat.le_refl _) tokens ht w data hw hr

/-- A complete production dynamic block decodes to its input through the
bounded outer loop. Realization allows subsequent padding and zlib trailer. -/
theorem read_write_bounded_exact (raw : ByteArray) (maxOut : Nat)
    (hmax : raw.size ≤ maxOut) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    read {data, bitPos := w.position} ByteArray.empty maxOut = .ok raw := by
  exact DecodeLoop.run_exact (readStep maxOut)
    (ByteArray.empty, {data, bitPos := w.position}) raw 1 (8 * data.size / 3 + 2)
    "deflate: no final block"
    (.done (readStep_write_bounded_exact raw maxOut hmax tokens ht w data hw hr))
    (by omega)

theorem read_write_exact (raw : ByteArray) (tokens : Array UInt32)
    (ht : TokensFor raw 0 tokens raw.size) (w : Bw) (data : ByteArray) (hw : w.Valid)
    (hr : (write tokens w).Realizes data) :
    read {data, bitPos := w.position} ByteArray.empty raw.size = .ok raw :=
  read_write_bounded_exact raw raw.size (Nat.le_refl _) tokens ht w data hw hr

end LeanTex.Core.Flate.BlockStream
