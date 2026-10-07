module

public import LeanTex.Core.LayoutCensus
import all LeanTex.Core.LayoutCensus

namespace LeanTex.Core.Layout

open Font Ir

private theorem run_body_census (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) :
    Census.bodyPages (run geom fs pats doc imgs frameSpans).pages =
      Census.bodyPages (ship geom fs pats doc imgs frameSpans).pages := by
  have h := congrArg
    (fun pages : Array (Array LineOut) =>
      pages.toList.flatMap fun lines => lines.toList.flatMap LineOut.glyphChars)
    (lines_counted_projects geom fs pats doc imgs frameSpans)
  simpa only [Census.bodyPages, Array.toList_map, List.flatMap_map] using h

private theorem attributed_leaf_filter (lines : Array LineOut) (k : Nat) :
    ((lines.filter fun l => l.leaf.isSome).filter fun l => l.leaf == some k) =
      lines.filter (fun l => l.leaf == some k) := by
  rw [Array.filter_filter]
  apply congrArg (fun p : LineOut → Bool => lines.filter p)
  funext l
  cases l.leaf <;> simp

private theorem run_leaf_census (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (k : Nat) :
    Census.leafPages (run geom fs pats doc imgs frameSpans).pages k =
      Census.leafPages (ship geom fs pats doc imgs frameSpans).pages k := by
  have h := congrArg
    (fun pages : Array (Array LineOut) =>
      pages.toList.flatMap fun lines =>
        (lines.filter fun l => l.leaf == some k).toList.flatMap LineOut.glyphChars)
    (lines_attributed_projects geom fs pats doc imgs frameSpans)
  simpa only [Census.leafPages, Array.toList_map, List.flatMap_map,
    attributed_leaf_filter] using h

private theorem shipment_glyph_clean (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span))
    (hd : ∀ d ∈ (run geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    ∀ d ∈ (ship geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009" := by
  intro d hm
  obtain ⟨e, he, hc, _⟩ := shipment_diags_covers geom fs pats doc imgs frameSpans d hm
  simpa only [hc] using hd e he

/-- Ordered source-body conservation through the actual public layout run.
The input consists of arbitrary literal paragraphs; paragraph lengths,
font choices, pagination, and running furniture are unrestricted. Automatic
hyphen insertion is disabled, and missing glyphs must be absent from the
run's diagnostics. Nonpainting spaces are omitted on both sides. Counted
body lines exclude generated page numbers and authored running furniture. -/
public theorem run_paras_body_exact (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body)
    (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (run geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    inkCensus (Census.bodyPages (run geom fs pats doc imgs frameSpans).pages) =
      inkCensus (Ir.blocksText doc.body).toList := by
  rw [run_body_census]
  exact ship_paras_body_exact geom fs pats doc imgs frameSpans hplain hh
    (shipment_glyph_clean geom fs pats doc imgs frameSpans hd)

/-- Each paragraph's owned glyphs survive the actual public layout run in
order, with the same multiplicity. Ownership is computed from the source
alone by `paragraphSourceInk`: a paragraph owns all its text inlines at its
opening structural leaf. Other leaf indices have an empty owned census.
The premises concern literal source paragraphs, hyphen insertion, and
observable missing-glyph diagnostics; no collector or placement invariant
is assumed. Furniture and print marks preserve this source census. -/
public theorem run_paras_leaf_exact (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (hplain : PlainParagraphs doc.body)
    (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (run geom fs pats doc imgs frameSpans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") (k : Nat) :
    inkCensus (Census.leafPages (run geom fs pats doc imgs frameSpans).pages k) =
      paragraphSourceInk doc.body k := by
  rw [run_leaf_census]
  exact ship_paras_leaf_exact geom fs pats doc imgs frameSpans hplain hh
    (shipment_glyph_clean geom fs pats doc imgs frameSpans hd) k

end LeanTex.Core.Layout
