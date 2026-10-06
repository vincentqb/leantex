import LeanTex.Core.Flate.BitStream
import LeanTex.Core.Flate.BitWriterProof

namespace LeanTex.Core.Flate

/-- An emitted field reads back at its actual writer position after arbitrary
later writes. The realization premise is supplied by the final flush. -/
theorem push_bits_exact (w : Bw) (data : ByteArray) (v n : Nat)
    (hw : w.Valid) (hn : n ≤ 16) (hv : v < 2 ^ n)
    (hr : (w.push v n).Realizes data) :
    ({data, bitPos := w.position} : Br).bits n =
      some (v, {data, bitPos := (w.push v n).position}) := by
  rw [push_position_exact w v n hw hn]
  exact bitField_bits_exact _ n v (by omega) hv
    (hr.field (push_field_exact w v n hw hn hv))

/-- A zero-width field is the identity for the reader, including at end of input. -/
theorem Br.bits_zero_id (r : Br) : r.bits 0 = some (0, r) := by
  simp [Br.bits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem pushExtra_contract (w : Bw) (value width : Nat)
    (hw : w.Valid) (hn : width ≤ 16) :
    (w.pushExtra value width).Valid ∧ (w.pushExtra value width).Extends w := by
  unfold Bw.pushExtra
  split
  · exact ⟨push_valid w value width hw hn, push_extends_exact w value width hw hn⟩
  · exact ⟨hw, Bw.Extends.refl w⟩

theorem pushExtra_bits_exact (w : Bw) (data : ByteArray) (value width : Nat)
    (hw : w.Valid) (hn : width ≤ 16) (hv : value < 2 ^ width)
    (hr : (w.pushExtra value width).Realizes data) :
    ({data, bitPos := w.position} : Br).bits width =
      some (value, {data, bitPos := (w.pushExtra value width).position}) := by
  by_cases h : 0 < width
  · simpa only [Bw.pushExtra, h, ite_true] using
      push_bits_exact w data value width hw hn hv (by
        simpa only [Bw.pushExtra, h, ite_true] using hr)
  · have hn : width = 0 := by omega
    have hv : value = 0 := by simp only [hn] at hv; omega
    simp [hn, hv, Bw.pushExtra, Br.bits_zero_id]

namespace BitStream

/-- Array emission preserves every preceding bit and the pending-byte bound. -/
theorem write_contract {α : Type} (emit : Bw → α → Bw) (entries : Array α) (w : Bw)
    (hw : w.Valid)
    (hstep : ∀ entry ∈ entries.toList, ∀ w, w.Valid →
      (emit w entry).Valid ∧ (emit w entry).Extends w) :
    (write emit entries w).Valid ∧ (write emit entries w).Extends w := by
  change (forIn entries w (fun entry s => pure (.yield (emit s entry))) :
    Id Bw).run.Valid ∧
      (forIn entries w (fun entry s => pure (.yield (emit s entry))) :
        Id Bw).run.Extends w
  apply Progress.forIn_array_exact
    (fun _ s => s.Valid ∧ s.Extends w) (fun s => s.Valid ∧ s.Extends w)
    _ entries w ⟨hw, Bw.Extends.refl w⟩ ?_ (fun _ h => h)
  intro before entry after heq s hs
  have hm : entry ∈ entries.toList := by simp [heq]
  have he := hstep entry hm s hs.1
  exact ⟨he.1, he.2.trans hs.2⟩

end BitStream
/-- The one-bit header reader recovers a certified bit field. -/
theorem bitField_bit_exact (r : Br) (v : Nat) (hv : v < 2)
    (hf : BitField r.data r.bitPos 1 v) :
    r.bit = some (v, {r with bitPos := r.bitPos + 1}) := by
  have hi : r.bitPos / 8 < r.data.size := by have := hf.1; omega
  have he := hf.2 0 (by decide)
  simp only [Nat.add_zero, Nat.shiftRight_zero, Nat.and_one_is_mod,
    Nat.mod_eq_of_lt hv, getElem?_pos r.data (r.bitPos / 8) hi, Option.getD_some] at he
  simpa only [Br.bit, getElem?_pos r.data (r.bitPos / 8) hi, Nat.and_one_is_mod] using
    congrArg (fun x => some (x, {r with bitPos := r.bitPos + 1})) he

theorem push_bit_exact (w : Bw) (data : ByteArray) (v : Nat)
    (hw : w.Valid) (hv : v < 2) (hr : (w.push v 1).Realizes data) :
    ({data, bitPos := w.position} : Br).bit =
      some (v, {data, bitPos := (w.push v 1).position}) := by
  rw [push_position_exact w v 1 hw (by decide)]
  exact bitField_bit_exact _ v hv (hr.field (push_field_exact w v 1 hw (by decide) hv))

end LeanTex.Core.Flate
