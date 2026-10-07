module

public import LeanTex.Core.Pdf
public import LeanTex.Core.HtmlDoc
import all LeanTex.Core.Pdf
import all LeanTex.Core.Ir
import all LeanTex.Core.HtmlDoc

/-! Agreement of the two backends over their shared IR and font environment.
These proofs depend on both emitters; the PDF producer itself needs only
its layout, structure, and serialization inputs. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Font LeanTex.Core.Layout

/-- The undeclared contract is met by this writer (`_exact`): a document
that declares no contract key gets no W0701 from its PDF. -/
public theorem pdf_default_contract_exact : ({} : Ir.OutputContract).unmet profile = #[] := by
  decide

/-- **The HTML ships the faces the PDF embeds: one `FontSet`, two
projections.** Every face this writer would embed for these pages
(`keepFaces`) is declared by a `@font-face` in the HTML emission built
from the same set (`HtmlDoc.shipFaces`), with captured font programs
embedded in the HTML font resources. Stated as the superset the HTML can
honestly promise: it never sees layout's used-glyph data, so it declares
every face of the set, and the embedded subset is covered a fortiori. The
convention is AGENTS': the artifact is a function of the document and the
font environment — a viewer without the document's faces installed must
not read it in a stand-in. -/
public theorem html_fonts_cover_pdf (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) :
    ∀ k ∈ keepFaces fs pages, ∃ ff ∈ HtmlDoc.shipFaces fs, ff.index = k :=
  fun k hk => HtmlDoc.shipFaces_covers fs (keepFaces_lt fs pages h k hk)

/-- **Both artifacts' kerning request is one record's two projections**
(`_agree`). `HtmlDoc.kernCssFor` emits the browser request and
`Layout.kernEnabled` gates every pair and space-pair lookup. The live
stylesheet and all three layout call sites pass `Ir.features` itself, so a
caller cannot substitute a detached literal at one backend. Quantifying the
record keeps the statement meaningful when a document-level feature switch
reaches the resolving site. -/
public theorem features_agree (features : Ir.Features) :
    (!(HtmlDoc.kernCssFor features).isEmpty) = Layout.kernEnabled features := by
  cases features with
  | mk kern => cases kern <;> simp [HtmlDoc.kernCssFor, Layout.kernEnabled]

/-- **Both artifacts size a picture by one IR box** (`_agree`). The PDF
reserves and places a picture by `Layout.pictureBox`, and the SVG's
`viewBox` is `HtmlDoc.pictureBoxOf` (`HtmlDoc.pictureViewBox_projects`);
under the measurement the driver hands both — `Layout.labelMetric` over the
one face set, the x-height the layout resolves — the two are the one value
`Ir.Pic.Picture.box`: the declared box exactly (`box_declared_exact`), else
every mark's ink and every node's border (`box_covers`). Before, the SVG
read the hull of label *anchors* while the page read the ink, so one
picture had two sizes. -/
public theorem picture_box_agree (geom : Layout.Geom) (fs : FontSet) (pic : Ir.Pic.Picture) :
    Layout.pictureBox geom fs {} (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) pic =
      HtmlDoc.pictureBoxOf { labelMetric := Layout.labelMetric geom fs } pic := by
  simpa only [HtmlDoc.pictureBoxOf] using Layout.pictureBox_projects geom fs {} pic

/-- **The two artifacts carry one text for a non-text object** (`_agree`):
whatever text a `Figure` carries as `/Alt` (`altElem`, the PDF's projection
of the object's `Ir.Alt`), the HTML names the object by that same text — an
svg's `aria-label`, an img's `alt` — because both project the one value
(for a picture, `Ir.Pic.Picture.alternative`: the author's words, else its
labels'). -/
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

/-- **The two artifacts hide the same objects** (`_agree`): the PDF adds no
element for a non-text object — its ink an artifact — exactly when the HTML
takes its svg out of the accessibility tree. -/
public theorem alt_hidden_agree (floor : String) (a : Ir.Alt) :
    (altElem #[rootElem] 0 0 a).size = 1 ↔
      HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor a) "aria-hidden" = some "true" := by
  rw [altElem_size_exact]
  cases a <;> simp [HtmlDoc.pictureAltAttrs, HtmlDoc.attrOf?]

/-- **Both artifacts' font decisions are projections of one policy value**
(`_projects`). `Doc.fontPolicy` is the one resolving site; the driver's
`shipFonts` is the spelling `doc.fontPolicy == .embedded`, and the HTML's
shipment is `shipFaces` under it and nothing otherwise — the `if` here is
that gate, written out. Under `.embedded` the shipment covers every face
this writer embeds (`html_fonts_cover_pdf` is the body); under `.none` the
document declared that its stylesheet owns the faces, and the PDF still
embeds its own, as `profile.fonts = .embeds` records. -/
public theorem fontPolicy_projects (doc : Ir.Doc) (fs : FontSet) (pages : Array PageOut)
    (h : 0 < fs.fonts.size) (hp : doc.fontPolicy == .embedded) :
    ∀ k ∈ keepFaces fs pages,
      ∃ ff ∈ (if doc.fontPolicy == .embedded then HtmlDoc.shipFaces fs else #[]),
        ff.index = k := by
  rw [ite_eq_left hp]
  exact html_fonts_cover_pdf fs pages h

end LeanTex.Core.Pdf
