import LeanTex.Core.Flate
import LeanTex.Core.Flate.BitWriterProof

namespace LeanTex.Core.Flate

/-- The four trailer bytes preserve every bit already emitted by the writer. -/
theorem pushBe32_realizes_exact (w : Bw) (data : ByteArray) (v : Nat)
    (h : w.Realizes data) : w.Realizes (pushBe32 data v) := by
  exact (((h.push _).push _).push _).push _

/-- The production compressor's final flush and checksum retain all its fields. -/
theorem zlibFlush_realizes_exact (w : Bw) (raw : ByteArray) (hw : w.Valid) :
    w.Realizes (pushBe32 w.flush (adler32 raw)) :=
  pushBe32_realizes_exact w w.flush _ (flush_realizes_exact w hw)

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

end LeanTex.Core.Flate
