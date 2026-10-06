module

import all LeanTex.Core.Flate
import all LeanTex.Core.Flate.BitStreamProof

namespace LeanTex.Core.Flate

/-- The four trailer bytes preserve every bit already emitted by the writer. -/
theorem pushBe32_realizes_exact (w : Bw) (data : ByteArray) (v : Nat)
    (h : w.Realizes data) : w.Realizes (pushBe32 data v) := by
  exact (((h.push _).push _).push _).push _

/-- The production compressor's final flush and checksum retain all its fields. -/
theorem zlibFlush_realizes_exact (w : Bw) (raw : ByteArray) (hw : w.Valid) :
    w.Realizes (pushBe32 w.flush (adler32 raw)) :=
  pushBe32_realizes_exact w w.flush _ (flush_realizes_exact w hw)

end LeanTex.Core.Flate
