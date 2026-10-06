import LeanTex.Core.Flate.BitStream
import LeanTex.Core.Flate.Huffman
import LeanTex.Core.Flate.DecodeLoop

namespace LeanTex.Core.Flate.FieldStream

/-- The fixed-width fields at the start of a dynamic header. -/
def write (width : Nat) (values : Array Nat) (w : Bw) : Bw :=
  BitStream.write (fun w value => w.push value width) values w

/-- Accumulate exactly the declared field count before decoding the next stage. -/
def readStep (width count : Nat) (state : Array Nat × Br) :
    Except String (Sum (Array Nat × Br) (Array Nat × Br)) :=
  if state.1.size ≥ count then .ok (.inl state)
  else match state.2.bits width with
  | none => .error "deflate: truncated"
  | some (value, r) => .ok (.inr (state.1.push value, r))

def read (width count : Nat) (r : Br) : Except String (Array Nat × Br) :=
  DecodeLoop.run (count + 1) (readStep width count) (#[], r) "deflate: truncated"

end LeanTex.Core.Flate.FieldStream
