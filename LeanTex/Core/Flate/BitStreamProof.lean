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
end LeanTex.Core.Flate
