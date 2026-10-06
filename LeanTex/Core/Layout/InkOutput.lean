import LeanTex.Core.Layout.InkContract

namespace LeanTex.Core.Layout

open Dim Font

/-- The successful check supplies actual font-outline answers and bounds
every glyph of every painted run, in that run's own face, size and raise. -/
theorem observeLabel_outlines_covers (fs : FontSet) (line : LineOut)
    (stamp : LabelAudit.Stamp)
    (hk : (observeLabel fs line stamp).known = true)
    (hb : (observeLabel fs line stamp).bounded = true) :
    line.OutlinesIn fs (line.y - stamp.above) (line.y + stamp.below) := by
  have hk' : labelGlyphUnknown fs line.size line.segs = false := by
    simpa only [observeLabel, Bool.not_eq_true'] using hk
  intro idx color link width glyphs sz leading decorations raise ground attr hrun g hg
  obtain ⟨lo, hi, he⟩ := labelGlyphUnknown_complete fs line.size line.segs hk'
    idx color link width glyphs sz leading decorations raise ground attr hrun g hg
  have hr := Array.all_eq_true'.mp hb _ hrun
  have hg' := Array.all_eq_true'.mp hr g hg
  simp only [he] at hg'
  have hbounds := of_decide_eq_true hg'
  refine ⟨lo, hi, he, ?_⟩
  exact ⟨Int.sub_le_sub_left hbounds.1 _, Int.add_le_add_left hbounds.2 _⟩

/-- An audit observation is the reading of a line on an actual page.
Producer results that disappeared before shipping cannot enter this census. -/
theorem labelObservations_mem (fs : FontSet) (pages : Array PageOut)
    (o : LabelAudit.Observation) (ho : o ∈ labelObservations fs pages) :
    ∃ page ∈ pages, ∃ line ∈ page.lines, ∃ stamp,
      line.pictureLabel = some stamp ∧ o = observeLabel fs line stamp := by
  obtain ⟨page, hp, ho⟩ := Array.mem_flatMap.mp ho
  obtain ⟨line, hl, ho⟩ := Array.mem_filterMap.mp ho
  cases hs : line.pictureLabel with
  | none => simp [hs] at ho
  | some stamp =>
    simp only [hs, Option.map_some, Option.some.injEq] at ho
    exact ⟨page, hp, line, hl, stamp, hs, ho.symm⟩

/-- Every stamped line on a final page enters the outline audit. -/
theorem labelObservations_contains (fs : FontSet) (pages : Array PageOut)
    (page : PageOut) (hp : page ∈ pages) (line : LineOut) (hl : line ∈ page.lines)
    (stamp : LabelAudit.Stamp) (hs : line.pictureLabel = some stamp) :
    observeLabel fs line stamp ∈ labelObservations fs pages := by
  apply Array.mem_flatMap.mpr
  refine ⟨page, hp, Array.mem_filterMap.mpr ⟨line, hl, ?_⟩⟩
  simp only [hs, Option.map_some]

/-- Occurrence identity comes from collection's operation and shape
indices; identical text at another site is not a substitute. -/
def LineOut.CarriesLabel (line : LineOut) (r : LabelAudit.Request) : Prop :=
  ∃ stamp, line.pictureLabel = some stamp ∧
    stamp.origin = r.origin ∧ stamp.key = r.key

/-- A selected occurrence either has no painted line and no text, or
ships a complete line whose actual run outlines fit its measured reserve.
The reserve travels with the baseline through vertical placement. -/
def Out.LabelInkCovered (out : Out) (fs : FontSet) (r : LabelAudit.Request) : Prop :=
  (r.blank = true ∧
    ¬ ∃ page ∈ out.pages, ∃ line ∈ page.lines, line.CarriesLabel r) ∨
  ∃ page ∈ out.pages, ∃ line ∈ page.lines, ∃ stamp,
    line.pictureLabel = some stamp ∧ stamp.origin = r.origin ∧ stamp.key = r.key ∧
      stamp.lineCount ≤ 1 ∧
      line.OutlinesIn fs (line.y - stamp.above) (line.y + stamp.below)

/-- A loss names both the selected label's key and its full source.
For a line that shipped, provenance may be the producer's first actual
line; for a missing occurrence it is collection's source. -/
def Out.LabelLossNamed (out : Out) (r : LabelAudit.Request) : Prop :=
  ∃ d ∈ out.diags, d.subject = some r.key ∧
    (d.kind ∈ ([.W0328, .W0394, .E0395, .W0396] : List DiagCode) ∨
      (d.kind.loss == .dropped || d.kind.loss == .pending) = true) ∧
    (d.span = r.source ∨
      ∃ page ∈ out.pages, ∃ line ∈ page.lines, ∃ stamp,
        line.pictureLabel = some stamp ∧ stamp.origin = r.origin ∧
          stamp.key = r.key ∧ d.span = stamp.source)

private theorem labelAccounted_covers (fs : FontSet) (out : Out)
    (r : LabelAudit.Request)
    (h : LabelAudit.accounted r (labelObservations fs out.pages) out.diags) :
    out.LabelInkCovered fs r ∨ out.LabelLossNamed r := by
  rcases h with ⟨hb, hn⟩ | ⟨o, ho, hm, hk, hg, hc⟩ | ⟨d, hd, hs, hk, hp⟩
  · left
    left
    refine ⟨hb, ?_⟩
    rintro ⟨page, hp, line, hl, stamp, hs, hi, hk⟩
    exact hn ⟨observeLabel fs line stamp,
      labelObservations_contains fs out.pages page hp line hl stamp hs, hi, hk⟩
  · left
    right
    obtain ⟨page, hp, line, hl, stamp, hs, rfl⟩ := labelObservations_mem fs out.pages o ho
    exact ⟨page, hp, line, hl, stamp, hs, hm.1, hm.2, hc,
      observeLabel_outlines_covers fs line stamp hk hg⟩
  · right
    refine ⟨d, hd, hs, hk, ?_⟩
    rcases hp with hp | ⟨o, ho, hm, hp⟩
    · exact Or.inl hp
    · right
      obtain ⟨page, hpage, line, hl, stamp, hstamp, rfl⟩ :=
        labelObservations_mem fs out.pages o ho
      exact ⟨page, hpage, line, hl, stamp, hstamp, hm.1, hm.2, hp⟩

/-- The complete public layout guarantee: each occurrence selected before
pagination either ships measured glyph ink inside its reserve or has a
keyed, source-preserving loss in the actual `Out`. The successful branch
reads the final page's runs, not plaintext shaped in a nominal body face.

This replaces the false cap-height alignment-box claim. Alignment remains
glyph-blind; the independently measured reserve supplies containment. -/
theorem run_ink_covered_or_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Ir.Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (r : LabelAudit.Request)
    (hr : r ∈ labelRequests geom fs pats doc imgs frameSpans) :
    (run geom fs pats doc imgs frameSpans).LabelInkCovered fs r ∨
      (run geom fs pats doc imgs frameSpans).LabelLossNamed r :=
  labelAccounted_covers fs _ r (run_label_accounts geom fs pats doc imgs frameSpans r hr)

/-- The complementary output-wide guarantee: every final stamped line has
complete measured glyph containment or its own source-preserving account.
This includes repeated and textually blank occurrences. -/
theorem run_shipped_ink_covered_or_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Ir.Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span))
    (page : PageOut) (hp : page ∈ (run geom fs pats doc imgs frameSpans).pages)
    (line : LineOut) (hl : line ∈ page.lines)
    (stamp : LabelAudit.Stamp) (hs : line.pictureLabel = some stamp) :
    (stamp.lineCount ≤ 1 ∧
      line.OutlinesIn fs (line.y - stamp.above) (line.y + stamp.below)) ∨
    ∃ kind ∈ ([.W0328, .W0394, .W0396] : List DiagCode),
      LabelAudit.named stamp.key stamp.source kind
        (run geom fs pats doc imgs frameSpans).diags := by
  have h := run_label_observed_accounts geom fs pats doc imgs frameSpans
    (observeLabel fs line stamp)
    (labelObservations_contains fs _ page hp line hl stamp hs)
  rcases h with ⟨hk, hb, hc⟩ | hn
  · exact Or.inl ⟨hc, observeLabel_outlines_covers fs line stamp hk hb⟩
  · exact Or.inr hn

/-- A missing outline answer on any actual shipped label always has its
own W0394 account, including full provenance. Truncation or a bounds loss
cannot silence this check. -/
theorem run_missing_outline_named (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Ir.Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span))
    (page : PageOut) (hp : page ∈ (run geom fs pats doc imgs frameSpans).pages)
    (line : LineOut) (hl : line ∈ page.lines)
    (stamp : LabelAudit.Stamp) (hs : line.pictureLabel = some stamp)
    (hu : labelGlyphUnknown fs line.size line.segs = true) :
    LabelAudit.named stamp.key stamp.source .W0394
      (run geom fs pats doc imgs frameSpans).diags := by
  apply run_label_unknown_named geom fs pats doc imgs frameSpans
    (observeLabel fs line stamp)
  · exact labelObservations_contains fs _ page hp line hl stamp hs
  · simp only [observeLabel, hu, Bool.not_true]

end LeanTex.Core.Layout
