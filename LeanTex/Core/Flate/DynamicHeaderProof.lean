module

import all LeanTex.Core.Flate.DynamicHeader
import all LeanTex.Core.Flate.FieldStreamProof
import all LeanTex.Core.Flate.CodeLengthsCodecProof
import Init.Data.Array.Extract

namespace LeanTex.Core.Flate.DynamicHeader

/-- The complete RFC permutation, checked over its nineteen positions. -/
theorem inverseOrder_contract :
    ∀ i : Fin 19, inverseOrder[i.val]?.getD 0 < 19 ∧
      order[inverseOrder[i.val]?.getD 0]? = some i.val := by
  decide

theorem fields_contract (lengths : Array Nat) :
    4 ≤ (fields lengths).size ∧ (fields lengths).size ≤ 19 ∧
      ∀ s : Nat, (fields lengths)[s]?.getD 0 = (ordered lengths)[s]?.getD 0 := by
  have h := Frequencies.trim_contract 4 (ordered lengths)
  have hs : (ordered lengths).size = 19 := by simp [ordered, order]
  simpa only [fields, hs, show min 4 19 = 4 by decide] using h

/-- Trimming removes zero fields only; restoring the RFC order recovers every
entry of the original code-length alphabet, including omitted zero entries. -/
theorem restore_fields_exact (lengths : Array Nat) (hs : lengths.size = 19) :
    restore (fields lengths) = lengths := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 19
  · have hin : i < inverseOrder.size := hi
    have hr := inverseOrder_contract ⟨i, hi⟩
    simp only [restore, Array.getElem?_map, getElem?_pos inverseOrder i hin,
      Option.map_some]
    have he : inverseOrder[i] = inverseOrder[i]?.getD 0 := by
      simp only [getElem?_pos inverseOrder i hin, Option.getD_some]
    rw [he, (fields_contract lengths).2.2]
    simp only [ordered, Array.getElem?_map, hr.2, Option.map_some, Option.getD_some]
    simp only [getElem?_pos lengths i (by omega), Option.getD_some]
  · have hr : ¬ i < (restore (fields lengths)).size := by
      simpa only [restore, Array.size_map, show inverseOrder.size = 19 by rfl] using hi
    simp only [getElem?_neg (restore (fields lengths)) i hr, getElem?_neg lengths i (by omega)]

theorem fields_width_exact (lengths : Array Nat) (hl : ∀ s : Nat, lengths[s]?.getD 0 ≤ 7) :
    ∀ v ∈ (fields lengths).toList, v < 2 ^ 3 := by
  intro v hv
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hv)
  have hf := (fields_contract lengths).2.2 i
  rw [hi, Option.getD_some] at hf
  rw [hf, ordered, Array.getElem?_map]
  cases he : order[i]? with
  | none => simp
  | some s =>
    simp only [Option.map_some, Option.getD_some]
    have := hl s
    omega

theorem codeLengths_contract (litLens distLens : Array Nat) :
    (codeLengths litLens distLens).size = 19 ∧
      ∀ s : Nat, (codeLengths litLens distLens)[s]?.getD 0 ≤ 7 := by
  have hf := (CodeLengths.frequencies_contract
    (CodeLengths.encode (litLens ++ distLens))).1
  have hl := PackageMerge.lengths_contract
    (CodeLengths.frequencies (CodeLengths.encode (litLens ++ distLens))) 7
    (by decide) (by omega)
  exact ⟨hl.1.size_eq.trans hf, hl.1.width_le⟩

theorem append_width_exact (litLens distLens : Array Nat)
    (hl : ∀ s : Nat, litLens[s]?.getD 0 < 16)
    (hd : ∀ s : Nat, distLens[s]?.getD 0 < 16) :
    ∀ s < (litLens ++ distLens).size, (litLens ++ distLens)[s]?.getD 0 < 16 := by
  intro s _
  rw [Array.getElem?_append]
  split
  · exact hl s
  · exact hd _

/-- The actual header writer retains all earlier fields. Its RLE alphabet
comes from the length vectors it transmits. -/
theorem write_contract (litLens distLens : Array Nat) (w : Bw) (hw : w.Valid)
    (hl : ∀ s : Nat, litLens[s]?.getD 0 < 16)
    (hd : ∀ s : Nat, distLens[s]?.getD 0 < 16) :
    (write litLens distLens w).Valid ∧ (write litLens distLens w).Extends w := by
  let lengths := codeLengths litLens distLens
  let values := fields lengths
  let w1 := w.push (litLens.size - 257) 5
  let w2 := w1.push (distLens.size - 1) 5
  let w3 := w2.push (values.size - 4) 4
  have h1 : w1.Valid := push_valid w _ 5 hw (by decide)
  have h2 : w2.Valid := push_valid w1 _ 5 h1 (by decide)
  have h3 : w3.Valid := push_valid w2 _ 4 h2 (by decide)
  have hf := FieldStream.write_contract 3 values w3 h3 (by decide)
  have hc := CodeLengths.write_contract lengths (canonCodes lengths)
    (CodeLengths.encode (litLens ++ distLens)) (FieldStream.write 3 values w3)
    hf.1 (fun s => Nat.le_trans ((codeLengths_contract litLens distLens).2 s) (by decide))
    (CodeLengths.encode_contract _ (append_width_exact litLens distLens hl hd)).2
  exact ⟨hc.1, hc.2.trans (hf.2.trans
    ((push_extends_exact w2 _ 4 h2 (by decide)).trans
      ((push_extends_exact w1 _ 5 h1 (by decide)).trans
        (push_extends_exact w _ 5 hw (by decide)))))⟩

/-- A complete dynamic header reads back the exact two arrays used by the
payload encoder. The sizes are the RFC alphabet bounds, and the final byte
array may contain any later payload and trailer preserving these fields. -/
theorem read_write_exact (litLens distLens : Array Nat) (w : Bw) (data : ByteArray)
    (hw : w.Valid) (hls : 257 ≤ litLens.size ∧ litLens.size ≤ 286)
    (hds : 1 ≤ distLens.size ∧ distLens.size ≤ 30)
    (hl : ∀ s : Nat, litLens[s]?.getD 0 < 16)
    (hd : ∀ s : Nat, distLens[s]?.getD 0 < 16)
    (hr : (write litLens distLens w).Realizes data) :
    read {data, bitPos := w.position} =
      .ok (litLens, distLens, {data, bitPos := (write litLens distLens w).position}) := by
  let lengths := codeLengths litLens distLens
  let values := fields lengths
  let w1 := w.push (litLens.size - 257) 5
  let w2 := w1.push (distLens.size - 1) 5
  let w3 := w2.push (values.size - 4) 4
  let w4 := FieldStream.write 3 values w3
  have h1 : w1.Valid := push_valid w _ 5 hw (by decide)
  have h2 : w2.Valid := push_valid w1 _ 5 h1 (by decide)
  have h3 : w3.Valid := push_valid w2 _ 4 h2 (by decide)
  have hf := FieldStream.write_contract 3 values w3 h3 (by decide)
  have hc := CodeLengths.write_contract lengths (canonCodes lengths)
    (CodeLengths.encode (litLens ++ distLens)) w4
    hf.1 (fun s => Nat.le_trans ((codeLengths_contract litLens distLens).2 s) (by decide))
    (CodeLengths.encode_contract _ (append_width_exact litLens distLens hl hd)).2
  have r4 : w4.Realizes data := hr.prefix hc.2
  have r3 : w3.Realizes data := r4.prefix hf.2
  have r2 : w2.Realizes data := r3.prefix (push_extends_exact w2 _ 4 h2 (by decide))
  have r1 : w1.Realizes data := r2.prefix (push_extends_exact w1 _ 5 h1 (by decide))
  have b1 := push_bits_exact w data (litLens.size - 257) 5 hw (by decide) (by omega) r1
  have b2 := push_bits_exact w1 data (distLens.size - 1) 5 h1 (by decide) (by omega) r2
  have hs := fields_contract lengths
  have b3 := push_bits_exact w2 data (values.size - 4) 4 h2 (by decide)
    (by have : values.size ≤ 19 := hs.2.1; omega) r3
  have b4 := FieldStream.read_write_exact 3 values w3 data h3 (by decide)
    (fields_width_exact lengths (codeLengths_contract litLens distLens).2) r4
  have b5 := CodeLengths.read_write_exact (litLens ++ distLens)
    (append_width_exact litLens distLens hl hd) w4 data hf.1 hr
  change CodeLengths.read (mkHuff lengths) (litLens ++ distLens).size
      {data, bitPos := w4.position} =
    .ok (litLens ++ distLens, {data, bitPos := (write litLens distLens w).position}) at b5
  have hrestore : restore values = lengths :=
    restore_fields_exact lengths (codeLengths_contract litLens distLens).1
  have hsize : values.size - 4 + 4 = values.size := by
    have : 4 ≤ values.size := hs.1
    omega
  have hnlit : litLens.size - 257 + 257 = litLens.size := by omega
  have hndist : distLens.size - 1 + 1 = distLens.size := by omega
  simp only [Array.size_append] at b5
  dsimp only [w1, w2, w3, w4, values, lengths] at b2 b3 b4 b5 hrestore hsize
  simp only [read, b1, b2, b3, hsize, hnlit, hndist, b4,
    hrestore, bind, Except.bind, pure, Except.pure]
  rw [b5]
  simp only [Array.extract_append_left, Array.extract_append_right, Array.extract_size]

end LeanTex.Core.Flate.DynamicHeader
