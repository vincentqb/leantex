module

public import LeanTex.Core.Pdf
public import LeanTex.Core.HtmlDoc
import all LeanTex.Core.Pdf
import LeanTex.Core.Ir
import all LeanTex.Core.HtmlDoc

/-! Agreement of the two backends over their shared IR and font environment. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Font LeanTex.Core.Layout

public theorem pdf_default_contract_exact : ({} : Ir.OutputContract).unmet profile = #[] :=
  Ir.OutputContract.unmet_default_exact profile

public theorem html_fonts_cover_pdf (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) :
    ∀ k ∈ keepFaces fs pages, ∃ ff ∈ HtmlDoc.shipFaces fs, ff.index = k :=
  fun k hk => HtmlDoc.shipFaces_covers fs (keepFaces_lt fs pages h k hk)

public theorem features_agree (features : Ir.Features) :
    (!(HtmlDoc.kernCssFor features).isEmpty) = Layout.kernEnabled features := by
  cases features with
  | mk kern => cases kern <;> simp [HtmlDoc.kernCssFor, Layout.kernEnabled]

public theorem table_cell_side_agree (cols : Array Ir.ColSpec) (spans : Array Ir.ColSpan)
    (i j : Nat) :
    HtmlDoc.cellSideClassOf cols spans i j = HtmlDoc.cellSideClass (Layout.cellSide cols spans i j) ∧
      HtmlDoc.cellSideRule (Layout.cellSide cols spans i j) =
        "table.booktabs td." ++ HtmlDoc.cellSideClassOf cols spans i j ++
          ", table.booktabs th." ++ HtmlDoc.cellSideClassOf cols spans i j ++
          " { text-align: " ++ (Layout.cellSide cols spans i j).align ++ "; }\n" :=
  ⟨rfl, rfl⟩

public theorem table_length_agree (doc : Ir.Doc) (name : String) :
    HtmlDoc.tableLengthFallback doc name =
      HtmlDoc.tableLengthCss (HtmlDoc.lengthBasisOf doc)
        (Dim.Length.ofSp (Layout.tableLength none doc.preambleFace name)) := rfl

public theorem picture_box_agree (geom : Layout.Geom) (fs : FontSet) (pic : Ir.Pic.Picture) :
    Layout.pictureBox geom fs {} (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) pic =
      (Gfx.ofPicture (Layout.labelMetric geom fs) pic).box ∧
    (Gfx.ofPicture (Layout.labelMetric geom fs) pic).box =
      HtmlDoc.pictureBoxOf { labelMetric := Layout.labelMetric geom fs } pic :=
  ⟨(Layout.pictureBox_projects geom fs {} pic).trans (Gfx.ofPicture_box_exact _ pic).symm,
    Gfx.ofPicture_box_exact _ pic⟩

public theorem alt_text_agree (floor : String) (a : Ir.Alt) (t : String)
    (ht : HtmlDoc.nonBlank t = true)
    (h : (altElem #[rootElem] 0 0 a).back?.bind (·.alt) = some t) :
    HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor a) "aria-label" = some t ∧
      HtmlDoc.attrOf? (HtmlDoc.imgAltAttrs a) "alt" = some t := by
  rw [altElem_root_alt_exact] at h
  cases a with
  | described s =>
    simp only [Option.some.injEq] at h
    subst h
    simp [HtmlDoc.pictureAltAttrs, HtmlDoc.imgAltAttrs, HtmlDoc.attrOf?, HtmlDoc.firstNonBlank, ht]
  | undeclared => contradiction
  | decorative => contradiction

public theorem alt_hidden_agree (floor : String) (a : Ir.Alt) :
    (altElem #[rootElem] 0 0 a).size = 1 ↔
      HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor a) "aria-hidden" = some "true" := by
  rw [altElem_size_exact]
  cases a <;> simp [HtmlDoc.pictureAltAttrs, HtmlDoc.attrOf?]

public theorem fontPolicy_projects (doc : Ir.Doc) (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) (hp : doc.fontPolicy == .embedded) :
    ∀ k ∈ keepFaces fs pages,
      ∃ ff ∈ (if doc.fontPolicy == .embedded then HtmlDoc.shipFaces fs else #[]),
        ff.index = k := by
  rw [ite_eq_left hp]
  exact html_fonts_cover_pdf fs pages h

end LeanTex.Core.Pdf
