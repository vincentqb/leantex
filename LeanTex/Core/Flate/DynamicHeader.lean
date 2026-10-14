module

public import LeanTex.Core.Flate.BitWriter
public import LeanTex.Core.Flate.Huffman
import LeanTex.Core.Flate.Alphabet
import LeanTex.Core.Flate.FieldStream
import LeanTex.Core.Flate.CodeLengthsReader
import LeanTex.Core.Flate.CodeLengthsWriter
import LeanTex.Core.Flate.PackageMerge

namespace LeanTex.Core.Flate.DynamicHeader

/-- Transmission order of the code-length alphabet (RFC 1951 §3.2.7). -/
def order : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Wire position of each code-length symbol, in symbol order. -/
def inverseOrder : Array Nat :=
  #[3, 17, 15, 13, 11, 9, 7, 5, 4, 6, 8, 10, 12, 14, 16, 18, 0, 1, 2]

def ordered (lengths : Array Nat) : Array Nat :=
  order.map (fun symbol => lengths[symbol]?.getD 0)

/-- The code-length fields in transmission order, trailing zeros dropped down to the mandatory four. -/
def fields (lengths : Array Nat) : Array Nat :=
  Frequencies.trim 4 (ordered lengths)

/-- Reconstruct the complete code-length alphabet from its transmitted prefix. -/
def restore (values : Array Nat) : Array Nat :=
  inverseOrder.map (fun index => values[index]?.getD 0)

def codeLengths (litLens distLens : Array Nat) : Array Nat :=
  PackageMerge.lengths (CodeLengths.frequencies (CodeLengths.encode (litLens ++ distLens))) 7

/-- Writes the declared alphabet sizes, the three-bit fields and the run-length-encoded lengths. -/
public def write (litLens distLens : Array Nat) (w : Bw) : Bw :=
  let lengths := codeLengths litLens distLens
  let values := fields lengths
  let w := ((w.push (litLens.size - 257) 5).push (distLens.size - 1) 5).push
    (values.size - 4) 4
  let w := FieldStream.write 3 values w
  CodeLengths.write lengths (canonCodes lengths) (CodeLengths.encode (litLens ++ distLens)) w

/-- Reads a dynamic block's literal and distance length arrays, at most 286 and 30 of them, under a
complete code-length code (RFC 1951 §3.2.7), as zlib's inflate reads them. -/
public def read (r : Br) : Except Error (Array Nat × Array Nat × Br) := do
  let some (hlit, r) := r.bits 5 | .error (.malformed "deflate: truncated")
  let some (hdist, r) := r.bits 5 | .error (.malformed "deflate: truncated")
  let some (hclen, r) := r.bits 4 | .error (.malformed "deflate: truncated")
  let nlit := hlit + 257
  let ndist := hdist + 1
  if nlit > 286 || ndist > 30 then
    .error (.malformed "deflate: more literal/length or distance codes than the alphabets hold")
  else
  let (values, r) ← FieldStream.read 3 (hclen + 4) r
  let some table := mkHuff? (restore values) (sparse := false)
    | .error (.malformed "deflate: the code-length code is over-subscribed or incomplete")
  let (lengths, r) ← CodeLengths.read table (nlit + ndist) r
  return (lengths.extract 0 nlit, lengths.extract nlit (nlit + ndist), r)

end LeanTex.Core.Flate.DynamicHeader
