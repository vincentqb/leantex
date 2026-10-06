module

public import LeanTex.Core.Flate.CodeLengths
public import LeanTex.Core.Flate.BitWriter
import LeanTex.Core.Flate.BitStream
import LeanTex.Core.Flate.Frequencies

namespace LeanTex.Core.Flate.CodeLengths

/-- Frequencies of the dynamic prelude's RLE alphabet (RFC 1951 §3.2.7). -/
public def frequencies (entries : Array Entry) : Array Nat :=
  Frequencies.count (fun entry => some entry.1) entries (Array.replicate 19 0)

/-- Emit the canonical code and extra bits of one dynamic table entry. -/
def writeEntry (lengths codes : Array Nat) (w : Bw) (entry : Entry) : Bw :=
  let w := w.push (codes[entry.1]?.getD 0) (lengths[entry.1]?.getD 0)
  if entry.2.2 > 0 then w.push entry.2.1 entry.2.2 else w

/-- The actual dynamic-table entry loop, shared with the stream proof. -/
public def write (lengths codes : Array Nat) (entries : Array Entry) (w : Bw) : Bw :=
  BitStream.write (writeEntry lengths codes) entries w

end LeanTex.Core.Flate.CodeLengths
