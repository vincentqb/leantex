module

public import LeanTex.Core.Flate
import all LeanTex.Core.Flate
import LeanTex.Core.Hex

namespace LeanTex.Core.Flate

private theorem hex16_utf8ByteSize (x : UInt64) : (hex16 x).utf8ByteSize = 16 := by
  unfold hex16
  exact Hex.digits_utf8ByteSize_exact true 16 x.toNat

public theorem contentKey_size_exact (b : ByteArray) : (contentKey b).toUTF8.size = 32 := by
  simp [contentKey, hex16_utf8ByteSize]

end LeanTex.Core.Flate
