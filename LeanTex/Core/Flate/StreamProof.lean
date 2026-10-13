module

import all LeanTex.Core.Flate
import all LeanTex.Core.Flate.BitStreamProof

namespace LeanTex.Core.Flate

theorem pushBe32_realizes_exact (w : Bw) (data : ByteArray) (v : Nat)
    (h : w.Realizes data) : w.Realizes (pushBe32 data v) := by
  exact (((h.push _).push _).push _).push _

theorem zlibFlush_realizes_exact (w : Bw) (raw : ByteArray) (hw : w.Valid) :
    w.Realizes (pushBe32 w.flush (adler32 raw)) :=
  pushBe32_realizes_exact w w.flush _ (flush_realizes_exact w hw)

end LeanTex.Core.Flate
