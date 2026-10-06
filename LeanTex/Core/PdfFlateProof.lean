import LeanTex.Core.PdfRead
import LeanTex.Core.Flate.RoundtripProof
import LeanTex.Core.Flate.ChecksumProof

namespace LeanTex.Core.PdfRead

private theorem decodeStream_flate (dict : Obj) (raw data : ByteArray)
    (hf : dict.get? "Filter" = some (.name "FlateDecode"))
    (hd : dict.get? "DL" = none) (hp : dict.get? "DecodeParms" = none)
    (hinflate : Flate.inflate raw maxDecoded = .ok data)
    (hn : 4 ≤ raw.size)
    (hc : (raw[raw.size - 4]?.getD 0).toNat * 16777216 +
      (raw[raw.size - 3]?.getD 0).toNat * 65536 +
      (raw[raw.size - 2]?.getD 0).toNat * 256 +
      (raw[raw.size - 1]?.getD 0).toNat = Flate.adler32 data) :
    decodeStream dict raw = .ok data := by
  unfold decodeStream
  rw [hf, hd, hp]
  change (Flate.inflate raw maxDecoded >>= fun v =>
    if (raw.size < 4 || (raw[raw.size - 4]?.getD 0).toNat * 16777216 +
        (raw[raw.size - 3]?.getD 0).toNat * 65536 +
        (raw[raw.size - 2]?.getD 0).toNat * 256 +
        (raw[raw.size - 1]?.getD 0).toNat != Flate.adler32 v) then
      .error "malformed PDF: a stream's data does not match its Adler-32 checksum"
    else .ok v) = .ok data
  rw [hinflate]
  simp only [bind, Except.bind]
  simp [show ¬ raw.size < 4 by omega, hc]

theorem decodeStream_deflate_exact (dict : Obj) (data : ByteArray)
    (hsize : data.size ≤ maxDecoded)
    (hf : dict.get? "Filter" = some (.name "FlateDecode"))
    (hd : dict.get? "DL" = none) (hp : dict.get? "DecodeParms" = none) :
    decodeStream dict (Flate.deflate data) = .ok data := by
  have hc := Flate.deflate_checksum_exact data
  exact decodeStream_flate dict _ data hf hd hp
    (Flate.inflate_deflate_bounded_id data maxDecoded hsize) hc.1 hc.2

theorem decodeStream_unfiltered_exact (dict : Obj) (raw : ByteArray)
    (hf : dict.get? "Filter" = none) : decodeStream dict raw = .ok raw := by
  unfold decodeStream
  rw [hf]
  rfl

end LeanTex.Core.PdfRead
