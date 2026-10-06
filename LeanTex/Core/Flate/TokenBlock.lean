module

public import LeanTex.Core.Flate.BitWriter
public import LeanTex.Core.Flate.Huffman
import LeanTex.Core.Flate.TokenSymbols
import LeanTex.Core.Flate.BitStream
import LeanTex.Core.Flate.DecodeLoop

namespace LeanTex.Core.Flate.TokenBlock

/-- Copy from the growing output, so a match may overlap its destination. -/
def copy (out : ByteArray) (len dist : Nat) : ByteArray := Id.run do
  let mut result := out
  for _ in [0:len] do
    result := result.push (result[result.size - dist]?.getD 0)
  return result

/-- One production symbol step. Completion is distinct from continuation:
the bounded driver consumes the actual token count, including end-of-block. -/
def readStep (lit dist : Huff) (maxOut : Nat) (state : ByteArray × Br) :
    Except String (Sum (ByteArray × Br) (ByteArray × Br)) := do
  let (out, r) := state
  let some (sym, r) := lit.decode r | .error "deflate: truncated block"
  if sym == 256 then return .inl (out, r)
  else if sym < 256 then
    if out.size ≥ maxOut then .error "deflate: output exceeds the declared size"
    else return .inr (out.push (UInt8.ofNat sym), r)
  else
    let i := sym - 257
    let some base := lenBase[i]? | .error "deflate: bad length code"
    let some extra := lenExtra[i]? | .error "deflate: bad length code"
    let some (e, r) := r.bits extra | .error "deflate: truncated"
    let len := base + e
    let some (dsym, r) := dist.decode r | .error "deflate: truncated"
    let some dbase := distBase[dsym]? | .error "deflate: bad distance code"
    let some dextra := distExtra[dsym]? | .error "deflate: bad distance code"
    let some (de, r) := r.bits dextra | .error "deflate: truncated"
    let d := dbase + de
    if d == 0 || d > out.size then .error "deflate: distance before the start of output"
    else if out.size + len > maxOut then .error "deflate: output exceeds the declared size"
    else return .inr (copy out len d, r)

/-- The symbol loop remains bounded by the caller's declared output size. -/
public def read (lit dist : Huff) (r : Br) (out : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × Br) :=
  DecodeLoop.run (maxOut + 2) (readStep lit dist maxOut) (out, r)
    "deflate: block did not end"

/-- A match has four consecutive fields: length code, length extra bits,
distance code, and distance extra bits. -/
def writeMatch (litLens litCodes distLens distCodes : Array Nat)
    (w : Bw) (len dist di : Nat) : Bw :=
  let li := lenSymTab[len]?.getD 0
  let w := w.push (litCodes[257 + li]?.getD 0) (litLens[257 + li]?.getD 0)
  let w := w.pushExtra (len - lenBase[li]?.getD 0) (lenExtra[li]?.getD 0)
  let w := w.push (distCodes[di]?.getD 0) (distLens[di]?.getD 0)
  w.pushExtra (dist - distBase[di]?.getD 0) (distExtra[di]?.getD 0)

/-- Emit one packed token with the production canonical codes and RFC extra
fields. The scalar token representation is shared with frequency counting. -/
def writeEntry (litLens litCodes distLens distCodes : Array Nat)
    (w : Bw) (t : UInt32) : Bw :=
  if t < 256 then
    let lit := t.toNat
    w.push (litCodes[lit]?.getD 0) (litLens[lit]?.getD 0)
  else
    let (len, dist, di) := matchOf t
    writeMatch litLens litCodes distLens distCodes w len dist di

def write (litLens litCodes distLens distCodes : Array Nat)
    (tokens : Array UInt32) (w : Bw) : Bw :=
  BitStream.write (writeEntry litLens litCodes distLens distCodes) tokens w

/-- The token payload includes its terminating symbol. -/
public def writePayload (litLens distLens : Array Nat) (tokens : Array UInt32) (w : Bw) : Bw :=
  let litCodes := canonCodes litLens
  let distCodes := canonCodes distLens
  let w := write litLens litCodes distLens distCodes tokens w
  w.push (litCodes[256]?.getD 0) (litLens[256]?.getD 0)

end LeanTex.Core.Flate.TokenBlock
