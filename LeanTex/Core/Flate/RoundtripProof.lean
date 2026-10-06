import LeanTex.Core.Flate.BlockStreamProof
import LeanTex.Core.Flate.StreamProof

namespace LeanTex.Core.Flate

theorem zlibWriter_valid : zlibWriter.Valid := by
  simp [zlibWriter, Bw.Valid]

/-- Token conservation and the actual block writer preserve the zlib header
and the pending-byte bound for every input. -/
theorem deflateWriter_contract (raw : ByteArray) :
    (deflateWriter raw).Valid ∧ (deflateWriter raw).Extends zlibWriter :=
  BlockStream.write_contract (tokenize_covers raw) zlibWriter zlibWriter_valid

/-- Flushing and appending the checksum preserve the compressor's entire
written bit stream. -/
theorem deflate_realizes_exact (raw : ByteArray) :
    (deflateWriter raw).Realizes (deflate raw) :=
  zlibFlush_realizes_exact (deflateWriter raw) raw (deflateWriter_contract raw).1

/-- The two bytes read by the public inflater are the actual zlib wrapper
bytes, preserved through compression, byte alignment, and checksum emission. -/
theorem deflate_header_exact (raw : ByteArray) :
    (deflate raw)[0]? = some (0x78 : UInt8) ∧
      (deflate raw)[1]? = some (0x9C : UInt8) := by
  have hp : zlibWriter.Realizes (deflate raw) :=
    (deflate_realizes_exact raw).prefix (deflateWriter_contract raw).2
  exact ⟨hp.byte_exact 0 (by decide), hp.byte_exact 1 (by decide)⟩

/-- The actual zlib compressor and bounded inflater compose to the identity
for every byte array. The proof uses the hash-chain token conservation,
frequency-derived package-merge tables, transmitted dynamic header, bit
writer, match copies, end markers, final byte flush, and zlib wrapper. -/
theorem inflate_deflate_id (raw : ByteArray) :
    inflate (deflate raw) raw.size = .ok raw := by
  have hh := deflate_header_exact raw
  have hr := BlockStream.read_write_exact raw (tokenize raw) (tokenize_covers raw)
    zlibWriter (deflate raw) zlibWriter_valid (deflate_realizes_exact raw)
  change BlockStream.read {data := deflate raw, bitPos := 16} ByteArray.empty raw.size =
    .ok raw at hr
  simpa [inflate, hh.1, hh.2] using hr

/-- A caller may reserve more output space than the source requires. The
decoder still returns exactly the compressed input, with its ordinary output
checks and token-loop budget both justified by the declared capacity. -/
theorem inflate_deflate_bounded_id (raw : ByteArray) (maxOut : Nat)
    (hmax : raw.size ≤ maxOut) :
    inflate (deflate raw) maxOut = .ok raw := by
  have hh := deflate_header_exact raw
  have hr := BlockStream.read_write_bounded_exact raw maxOut hmax (tokenize raw)
    (tokenize_covers raw) zlibWriter (deflate raw) zlibWriter_valid (deflate_realizes_exact raw)
  change BlockStream.read {data := deflate raw, bitPos := 16} ByteArray.empty maxOut =
    .ok raw at hr
  simpa [inflate, hh.1, hh.2] using hr

end LeanTex.Core.Flate
