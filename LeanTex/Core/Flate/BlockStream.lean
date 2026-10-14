module

public import LeanTex.Core.Flate.BitWriter
public import LeanTex.Core.Flate.Huffman
import LeanTex.Core.Flate.TokenBlock
import LeanTex.Core.Flate.TokenFrequencies
import LeanTex.Core.Flate.DynamicHeader
import LeanTex.Core.Flate.DecodeLoop
import LeanTex.Core.Flate.PackageMerge

namespace LeanTex.Core.Flate.BlockStream

/-- The fixed litlen table (RFC 1951 §3.2.6). -/
private def fixedLit : Huff :=
  mkHuff (Array.ofFn (n := 288) fun i =>
    if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8)

private def fixedDist : Huff :=
  mkHuff (Array.replicate 30 5)

/-- Stored blocks align to the next byte, then carry LEN, ~LEN, and raw bytes. -/
def readStored (r : Br) (out : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × Br) := do
  let byte := (r.bitPos + 7) / 8
  let some l0 := r.data[byte]? | .error "deflate: truncated stored block"
  let some l1 := r.data[byte + 1]? | .error "deflate: truncated stored block"
  let len := l0.toNat + 256 * l1.toNat
  if byte + 4 + len > r.data.size then .error "deflate: stored block overruns the stream"
  else if out.size + len > maxOut then .error "deflate: output exceeds the declared size"
  else return (out ++ r.data.extract (byte + 4) (byte + 4 + len),
      {r with bitPos := 8 * (byte + 4 + len)})

/-- Read one block body using the tables its type declares. -/
def readBody (btype : Nat) (r : Br) (out : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × Br) := do
  if btype == 0 then readStored r out maxOut
  else if btype == 1 then TokenBlock.read fixedLit fixedDist r out maxOut
  else if btype == 2 then
    let (litLens, distLens, r) ← DynamicHeader.read r
    let some lit := mkHuff? litLens | .error "deflate: over-subscribed literal/length code"
    let some dist := mkHuff? distLens | .error "deflate: over-subscribed distance code"
    TokenBlock.read lit dist r out maxOut
  else .error "deflate: reserved block type"

/-- The final bit distinguishes a complete stream from another block. -/
def readStep (maxOut : Nat) (state : ByteArray × Br) :
    Except String (Sum ByteArray (ByteArray × Br)) := do
  let (out, r) := state
  let some (bfinal, r) := r.bit | .error "deflate: truncated"
  let some (btype, r) := r.bits 2 | .error "deflate: truncated"
  let (out, r) ← readBody btype r out maxOut
  return if bfinal == 1 then .inl out else .inr (out, r)

/-- Reads blocks through the final one, bounded by the three bits every block consumes. -/
public def read (r : Br) (out : ByteArray) (maxOut : Nat) : Except String ByteArray :=
  DecodeLoop.run (8 * r.data.size / 3 + 2) (readStep maxOut) (out, r)
    "deflate: no final block"

/-- Both payload alphabets' code lengths, limited to fifteen bits (RFC 1951 §3.2.7). -/
def lengths (tokens : Array UInt32) : Array Nat × Array Nat :=
  let (litFreq, distFreq) := TokenBlock.alphabets tokens
  (PackageMerge.lengths litFreq 15, PackageMerge.lengths distFreq 15)

/-- Writes a final dynamic block whose header and payload use the same two length arrays. -/
public def write (tokens : Array UInt32) (w : Bw) : Bw :=
  let (litLens, distLens) := lengths tokens
  let w := (w.push 1 1).push 2 2
  let w := DynamicHeader.write litLens distLens w
  TokenBlock.writePayload litLens distLens tokens w

end LeanTex.Core.Flate.BlockStream
