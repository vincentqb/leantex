module

public import LeanTex.Core.Pdf
import LeanTex.Core.Flate.RoundtripProof

namespace LeanTex.Core.Pdf

/-- **A copied page's content survives the writer's compression** (`_id`):
the stream stored for a copied form inflates, under the filter its
dictionary declares, to the content the source page carried — within the
reader's decoding bound, and given that a deflate the driver supplied
inflates back to that content, as the content-hash cache's answer for it
does. -/
public theorem copiedForm_inflate_id (content : ByteArray) (z? : Option ByteArray)
    (h : content.size ≤ PdfRead.maxDecoded)
    (hz : ∀ z, z? = some z → Flate.inflate z PdfRead.maxDecoded = .ok content) :
    (if (copiedFormStream content z?).2 then
        Flate.inflate (copiedFormStream content z?).1 PdfRead.maxDecoded
      else .ok (copiedFormStream content z?).1) = .ok content := by
  cases z? with
  | none =>
    by_cases hd : (Flate.deflate content).size < content.size
    · simp [copiedFormStream, hd, Flate.inflate_deflate_bounded_id content _ h]
    · simp [copiedFormStream, hd]
  | some z =>
    by_cases hd : z.size < content.size
    · simp [copiedFormStream, hd, hz z rfl]
    · simp [copiedFormStream, hd]

end LeanTex.Core.Pdf
