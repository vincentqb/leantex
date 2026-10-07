module

import LeanTex.Core.LayoutCensus
import LeanTex.Core.Layout.FramePartition
import LeanTex.Core.Layout.SpacingContract
import LeanTex.Core.Layout.InkOutput
import LeanTex.Core.Layout.TextConservation

namespace Tests.LayoutContractInterface

open LeanTex.Core Layout Font

-- Ordinary consumers can state and apply the contracts without producer bodies.
example : Array PageOut → Nat → List Char := Census.leafPages
example : Array PageOut → List Char := Census.bodyPages

example (sh : Shipped) (k : Nat) :
    Census.leafPages (runPost sh).pages k = Census.leafPages sh.pages k :=
  Census.runPost_leaf_exact sh k

example (sh : Shipped) :
    Census.bodyPages (runPost sh).pages = Census.bodyPages sh.pages :=
  Census.runPost_body_exact sh

example : LawfulBEq FrameOrigin := inferInstance
example : Out → Option FrameOrigin → Array PageOut := FramePartition.pages
example : Out → Nat → Array PageOut := FramePartition.sourcePages

example (out : Out) (owner : Option FrameOrigin) (page : PageOut) :
    page ∈ FramePartition.pages out owner ↔
      page ∈ out.pages ∧ page.frameOrigin = owner :=
  FramePartition.pages_mem out owner page

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span)) :
    let out := run geom fs pats doc imgs spans
    let openings := frameOpenings geom fs pats doc imgs spans
    (FramePartition.pages out none).size +
      ((FramePartition.origins openings).map
        (fun o => (FramePartition.pages out (some o)).size)).sum = out.pages.size :=
  FramePartition.run_count_exact geom fs pats doc imgs spans

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span)) (source : Nat) :
    let out := run geom fs pats doc imgs spans
    let openings := frameOpenings geom fs pats doc imgs spans
    ((FramePartition.steps openings source).map
      (fun o => (FramePartition.pages out (some o)).size)).sum =
        (FramePartition.sourcePages out source).size :=
  FramePartition.run_source_count_exact geom fs pats doc imgs spans source

example (a : Spacing.Pending) (r : Spacing.Context) (g : Dim.Glue)
    (ha : Spacing.Ordinary a) (hg : Spacing.CoversDefault a r g) :
    ((Spacing.flushed a r).foldl Dim.Glue.add {}).width ≤
      ((Spacing.flushed (Spacing.add a g) r).foldl Dim.Glue.add {}).width :=
  Spacing.flushed_width_monotone a r g ha hg

example (geom : Geom) (fs : FontSet) (before after : Ir.Doc)
    (h : Spacing.twoParagraphIncreasing geom fs before after = true) :
    ((Spacing.inkBaselines (run geom fs none before)).getLast?.getD 0 : Int) ≤
      (Spacing.inkBaselines (run geom fs none after)).getLast?.getD 0 :=
  Spacing.twoParagraphIncreasing_contract geom fs before after h

example : LineOut → FontSet → Dim.Sp → Dim.Sp → Prop := LineOut.OutlinesIn
example : Out → FontSet → LabelAudit.Request → Prop := Out.LabelInkCovered
example : Out → LabelAudit.Request → Prop := Out.LabelLossNamed

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span))
    (r : LabelAudit.Request) (hr : r ∈ labelRequests geom fs pats doc imgs spans) :
    (run geom fs pats doc imgs spans).LabelInkCovered fs r ∨
      (run geom fs pats doc imgs spans).LabelLossNamed r :=
  run_ink_covered_or_named geom fs pats doc imgs spans r hr

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span))
    (hp : PlainParagraphs doc.body) (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (run geom fs pats doc imgs spans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") :
    inkCensus (Census.bodyPages (run geom fs pats doc imgs spans).pages) =
      inkCensus (Ir.blocksText doc.body).toList :=
  run_paras_body_exact geom fs pats doc imgs spans hp hh hd

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span))
    (hp : PlainParagraphs doc.body) (hh : geom.hyphenate = false ∨ pats = none)
    (hd : ∀ d ∈ (run geom fs pats doc imgs spans).diags,
      d.code ≠ "E0405" ∧ d.code ≠ "W0009") (k : Nat) :
    inkCensus (Census.leafPages (run geom fs pats doc imgs spans).pages k) =
      paragraphSourceInk doc.body k :=
  run_paras_leaf_exact geom fs pats doc imgs spans hp hh hd k

-- A proof module's implementation imports do not become its clients' API.
example : True := by
  fail_if_success have := Layout.Acc
  fail_if_success have := Layout.collect
  fail_if_success have := Layout.placePara
  fail_if_success have := Layout.Spacing.Program.ops
  fail_if_success have := Layout.Spacing.Program.initial
  fail_if_success have := Census.attributed_leaf_filter_exact
  fail_if_success have := FramePartition.count_partition
  fail_if_success have := Spacing.boundaryWidth
  fail_if_success have := Layout.labelAccounted_covers
  fail_if_success have := Layout.run_body_census
  fail_if_success have := Layout.run_leaf_census
  fail_if_success have := Layout.shipment_glyph_clean
  fail_if_success have := Ir.fillList
  trivial

end Tests.LayoutContractInterface
