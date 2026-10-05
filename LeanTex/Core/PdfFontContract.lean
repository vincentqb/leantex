import LeanTex.Core.Pdf
import LeanTex.Core.PdfCensus

namespace LeanTex.Core.Pdf

private theorem fontObjects_embedded (t : ObjTable) (k : Nat) (font : Font.Font)
    (baseFont : String) (widths : PdfRead.Obj) (es : Array PdfRead.Entry)
    (e : PdfRead.Entry)
    (hval : e.val = (fontObjects t k font baseFont widths).type0 ∨
      e.val = (fontObjects t k font baseFont widths).cid)
    (hdescriptor : PdfCensus.deref es (.ref (ObjTable.fdId k) 0) =
      (fontObjects t k font baseFont widths).descriptor) :
    PdfCensus.fontEmbedded es e = true := by
  rcases hval with hval | hval
  · unfold PdfCensus.fontEmbedded
    rw [hval]
    rfl
  · unfold PdfCensus.fontEmbedded
    split
    · rfl
    · rfl
    · simp only [hval, (fontObjects_links_exact t k font baseFont widths).2.2.1,
        Option.getD_some, hdescriptor]
      have hfile := (fontObjects_links_exact t k font baseFont widths).2.2.2
      cases hcff : font.isCff <;> simp_all

/-- The read-side font census follows from recovered font dictionaries
and descriptor references. These premises are the reader boundary:
parsing, decompression, and object-stream lookup must recover the writer's
values, and any foreign font needs a separate contract.

The conclusion is the census's rule (a descriptor carries a program
reference), not validation of the font program's bytes. No reader success
or font-program validity is inferred from construction alone. -/
theorem fontObjects_census_contract (t : ObjTable) (font : Nat → Font.Font)
    (baseFont : Nat → String) (widths : Nat → PdfRead.Obj)
    (trailer : PdfRead.Obj) (es : Array PdfRead.Entry)
    (hfonts : ∀ e ∈ PdfCensus.fontEntries es, ∃ k, k < t.nf ∧
      (e.val = (fontObjects t k (font k) (baseFont k) (widths k)).type0 ∨
       e.val = (fontObjects t k (font k) (baseFont k) (widths k)).cid))
    (hdescriptors : ∀ k, k < t.nf →
      PdfCensus.deref es (.ref (ObjTable.fdId k) 0) =
        (fontObjects t k (font k) (baseFont k) (widths k)).descriptor) :
    (PdfCensus.ofEntries trailer es).fontsEmbedded = true := by
  apply (PdfCensus.census_fontsEmbedded_exact trailer es).2
  intro e he
  obtain ⟨k, hk, hval⟩ := hfonts e he
  exact fontObjects_embedded t k (font k) (baseFont k) (widths k) es e hval
    (hdescriptors k hk)

end LeanTex.Core.Pdf
