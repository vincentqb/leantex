module

import LeanTex.Core.Layout

namespace Tests.LayoutInterface

open LeanTex.Core Layout Font

example : Geom := {}
example : LineOut := { x := 0, y := 0, size := 0, segs := #[], setWidth := 0 }
example : PageOut := {}
example : Out := { pages := #[], diags := #[] }
example : Repr FrameOrigin := inferInstance
example : BEq FrameOrigin := inferInstance
example : DecidableEq FrameOrigin := inferInstance

example (out : Out) : Array PageOut × Array Diag × Array ParagraphBreaks :=
  (out.pages, out.diags, out.paragraphBreaks)

example (line : LineOut) : Array Seg × Option Nat × Bool × List Char :=
  (line.segs, line.leaf, line.counted, line.glyphChars)

example : Geom → FontSet → Option Hyphen.Patterns → Ir.Doc → Image.Store →
    Array (Nat × Span) → Array (Nat × Span) → Out := @run

example : Geom → FontSet → Option Hyphen.Patterns → Ir.Doc → Image.Store →
    Array (Nat × Span) → Array (Nat × Span) → Shipped := @ship

example : Shipped → Out := runPost
example : Ir.Doc → Array Char := docScalars
example : Ir.Doc → Array Char := docMathScalars
example : Ir.Doc → Array (Nat × Nat × Bool) := docWeightKeys
example : Array Item → KpSums := kpSums

-- The conservation domain is determined by source constructors alone.
example (paragraphs : Array (Array String)) :
    PlainParagraphs (paragraphs.map fun xs => .para (xs.map .text)) := by
  intro b hb
  obtain ⟨xs, _, rfl⟩ := Array.mem_map.mp hb
  refine ⟨xs.map .text, rfl, ?_⟩
  intro x hx
  obtain ⟨s, _, rfl⟩ := Array.mem_map.mp hx
  exact ⟨s, rfl⟩

-- These shared projection equations are part of the backend interface.
example (features : Ir.Features) : kernEnabled features = features.kern := rfl

example (geom : Geom) (fs : FontSet) (imgs : Image.Store) (pic : Ir.Pic.Picture) :
    pictureBox geom fs imgs (fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm) pic =
      pic.box (labelMetric geom fs imgs) :=
  pictureBox_projects geom fs imgs pic

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span)) :
    ReflowsNamed (run geom fs pats doc imgs spans).paragraphBreaks
      (run geom fs pats doc imgs spans).diags :=
  reflow_named geom fs pats doc imgs spans

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span))
    (hp : PlainParagraphs doc.body) (page : PageOut)
    (hpage : page ∈ (run geom fs pats doc imgs spans).pages) (line : LineOut)
    (hline : line ∈ page.lines) (hf : line.furniture = false) (hg : line.glyphChars ≠ []) :
    ∃ k, line.leaf = some k ∧ k < (Struct.ofDoc (pdfView doc)).leaves.size :=
  lines_attributed_covers geom fs pats doc imgs spans hp page hpage line hline hf hg

example (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store) (spans : Array (Nat × Span))
    (page : PageOut) (hp : page ∈ (run geom fs pats doc imgs spans).pages) :
    SelectedFrame (frameOpenings geom fs pats doc imgs spans) page.frameStamp :=
  run_frames_footed geom fs pats doc imgs spans page hp

example (geom : Geom) (fs : FontSet) (doc : Ir.Doc) : Spacing.Program :=
  Spacing.program geom fs doc

example (fs : FontSet) (page : Spacing.Page) (paragraph : Spacing.Paragraph)
    (breaks : Array Nat) (skips : Array Dim.Glue) :
    Decidable (Spacing.ParagraphSafe fs page paragraph breaks skips) :=
  inferInstance

example (pending : Spacing.Pending) : Spacing.PendingView := Spacing.pending pending
example (page : Spacing.Page) : Array PageOut := Spacing.shipped page

example : True := by
  fail_if_success have := Layout.Acc
  fail_if_success have := Layout.Rd
  fail_if_success have := Layout.B
  fail_if_success have := Layout.FlattenSt
  fail_if_success have := Layout.LeafCtr
  fail_if_success have := Layout.WordAcc
  fail_if_success have := Layout.ParaJob
  fail_if_success have := Layout.StagedOp
  fail_if_success have := Layout.StepSt
  fail_if_success have := Layout.collect
  fail_if_success have := Layout.placeFrom
  fail_if_success have := Layout.placePara
  fail_if_success have := Layout.Spacing.Program.ops
  fail_if_success have := Layout.Spacing.Program.initial
  fail_if_success have := Layout.Spacing.Pending.mk
  fail_if_success have := Layout.Spacing.Pending.owed
  fail_if_success have := Layout.Spacing.Context.mk
  fail_if_success have := Layout.Spacing.Context.fs
  fail_if_success have := Layout.Spacing.Page.mk
  fail_if_success have := Layout.Spacing.Page.cur
  fail_if_success have := Layout.Spacing.Paragraph.mk
  fail_if_success have := Layout.Spacing.Paragraph.items
  fail_if_success have := Ir.fillList
  trivial

example : True := by
  fail_if_success have := Layout.pushWord_toks
  fail_if_success have := Layout.flatten_attr_covers
  fail_if_success have := Layout.runFloat_whole
  trivial

end Tests.LayoutInterface
