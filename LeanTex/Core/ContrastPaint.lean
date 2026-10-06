import LeanTex.Core.ContrastRatio
import LeanTex.Core.Layout

/-!
Contrast observations over placed glyphs. The document realization plan
cannot enumerate all such paint: overlays compute colours, and pictures
and furniture can introduce ink after that walk.

The arithmetic contract is over `Ir.Color`. Its placed-page projection
reads actual `Layout.Out` data, preserves every occurrence and its address,
and makes no inference about covered/decorative status. A recorded ground
is not a proof about overlapping fills or paths. The caller supplies both
the fallback ground and the threshold; failures here are observations,
not a request to emit a diagnostic for intentionally covered text.
-/
namespace LeanTex.Core.Contrast

open Ir Layout

/-- A nonempty glyph run's paint at its zero-based address in the output.
`ground` retains `none`: resolving a fallback must not erase the evidence
that a painter did not record a local ground. -/
structure RunPaint where
  page : Nat
  line : Nat
  segment : Nat
  ink : Color
  ground : Option Color
  deriving Repr, BEq

/-- Read exactly the paint a glyph run carries. Spacing, rules, decoration,
images and polygons are outside this text census. -/
def runPaint? (page line segment : Nat) : Seg → Option RunPaint
  | .run _ ink _ _ glyphs _ _ _ _ ground _ =>
    if glyphs.isEmpty then none else some { page, line, segment, ink, ground }
  | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => none

private theorem runPaint?_address
    (hp : runPaint? page line segment seg = some paint) :
    paint.page = page ∧ paint.line = line ∧ paint.segment = segment := by
  cases seg <;> simp only [runPaint?] at hp <;> try cases hp
  split at hp
  · cases hp
  · cases hp
    exact ⟨rfl, rfl, rfl⟩

/-- The actual ordered census, with duplicates retained. It is read from
placed output, not reconstructed from source or from a palette plan. -/
def shippedPaints (out : Out) : Array RunPaint :=
  out.pages.zipIdx.flatMap fun (page, p) =>
    page.lines.zipIdx.flatMap fun (line, l) =>
      line.segs.zipIdx.filterMap fun (seg, s) => runPaint? p l s seg

/-- Independent address-based specification of one census entry. -/
def PaintOccurs (out : Out) (paint : RunPaint) : Prop :=
  ∃ page line seg,
    out.pages[paint.page]? = some page ∧
    page.lines[paint.line]? = some line ∧
    line.segs[paint.segment]? = some seg ∧
    runPaint? paint.page paint.line paint.segment seg = some paint

/-- Both directions: every census entry has an actual nonempty glyph run
at its reported address, and every such run is present. -/
theorem shippedPaints_exact (out : Out) (paint : RunPaint) :
    paint ∈ shippedPaints out ↔ PaintOccurs out paint := by
  constructor
  · intro h
    rcases Array.mem_flatMap.mp h with ⟨⟨page, p⟩, hp, h⟩
    rcases Array.mem_flatMap.mp h with ⟨⟨line, l⟩, hl, h⟩
    rcases Array.mem_filterMap.mp h with ⟨⟨seg, s⟩, hs, hr⟩
    have ha := runPaint?_address hr
    refine ⟨page, line, seg, ?_, ?_, ?_, ?_⟩
    · rw [ha.1]
      exact Array.mk_mem_zipIdx_iff_getElem?.mp hp
    · rw [ha.2.1]
      exact Array.mk_mem_zipIdx_iff_getElem?.mp hl
    · rw [ha.2.2]
      exact Array.mk_mem_zipIdx_iff_getElem?.mp hs
    · simpa only [ha.1, ha.2.1, ha.2.2] using hr
  · rintro ⟨page, line, seg, hp, hl, hs, hr⟩
    apply Array.mem_flatMap.mpr
    refine ⟨(page, paint.page), Array.mk_mem_zipIdx_iff_getElem?.mpr hp, ?_⟩
    apply Array.mem_flatMap.mpr
    refine ⟨(line, paint.line), Array.mk_mem_zipIdx_iff_getElem?.mpr hl, ?_⟩
    exact Array.mem_filterMap.mpr
      ⟨(seg, paint.segment), Array.mk_mem_zipIdx_iff_getElem?.mpr hs, hr⟩

/-- No assumption about the layout algorithm: a nonempty run in the output
is always in the actual census, including computed overlay/furniture ink. -/
theorem shippedPaints_covers (out : Out)
    (hp : out.pages[p]? = some page) (hl : page.lines[l]? = some line)
    (hs : line.segs[s]? =
      some (.run font ink link width glyphs size leading decorations raise ground attr))
    (hne : glyphs.isEmpty = false) :
    { page := p, line := l, segment := s, ink, ground } ∈ shippedPaints out := by
  apply (shippedPaints_exact ..).mpr
  refine ⟨page, line, _, hp, hl, hs, ?_⟩
  simp [runPaint?, hne]

/-- The observation and its assessment travel together; equal colours at
different addresses must not consume one another's exemption decisions. -/
structure RunAssessment where
  paint : RunPaint
  assessment : PairAssessment
  deriving Repr, BEq

def assessRun (defaultGround : Color) (required : Nat) (paint : RunPaint) :
    RunAssessment :=
  { paint, assessment := assessPair required paint.ink (paint.ground.getD defaultGround) }

/-- Arithmetic for every nonempty placed glyph run. Call with the effective
page ground for the document that produced `out`. This does not resolve a
picture's unrecorded local fill or recover exemption provenance. -/
def shippedAudit (defaultGround : Color) (required : Nat) (out : Out) :
    Array RunAssessment :=
  (shippedPaints out).map (assessRun defaultGround required)

theorem shippedAudit_exact (defaultGround : Color) (required : Nat)
    (out : Out) (a : RunAssessment) :
    a ∈ shippedAudit defaultGround required out ↔
      ∃ paint, PaintOccurs out paint ∧ assessRun defaultGround required paint = a := by
  simp only [shippedAudit, Array.mem_map, shippedPaints_exact]

/-- The audit never silently drops a run. The retained entry includes the
actual colours and the implemented contrast decision. -/
theorem shippedAudit_covers (defaultGround : Color) (required : Nat) (out : Out)
    (hp : out.pages[p]? = some page) (hl : page.lines[l]? = some line)
    (hs : line.segs[s]? =
      some (.run font ink link width glyphs size leading decorations raise ground attr))
    (hne : glyphs.isEmpty = false) :
    assessRun defaultGround required
      { page := p, line := l, segment := s, ink, ground } ∈
        shippedAudit defaultGround required out := by
  exact Array.mem_map.mpr ⟨_, shippedPaints_covers out hp hl hs hne, rfl⟩

/-- Arithmetic below the supplied threshold; this deliberately does not
classify a run as covered, decorative, or eligible for a diagnostic. -/
def shippedFailures (defaultGround : Color) (required : Nat) (out : Out) :
    Array RunAssessment :=
  (shippedAudit defaultGround required out).filter fun a => !a.assessment.passes

/-- A failure is exactly an actual run below the supplied threshold. -/
theorem shippedFailures_exact (defaultGround : Color) (required : Nat)
    (out : Out) (a : RunAssessment) :
    a ∈ shippedFailures defaultGround required out ↔
      ∃ paint, PaintOccurs out paint ∧
        assessRun defaultGround required paint = a ∧
        contrastMilli paint.ink (paint.ground.getD defaultGround) < required := by
  simp only [shippedFailures, Array.mem_filter, shippedAudit_exact]
  constructor
  · rintro ⟨⟨paint, hp, rfl⟩, h⟩
    refine ⟨paint, hp, rfl, Nat.lt_of_not_ge ?_⟩
    intro hle
    have hpass := (assessPair_contract required paint.ink
      (paint.ground.getD defaultGround)).2.mpr hle
    change (!(assessPair required paint.ink (paint.ground.getD defaultGround)).passes) =
      true at h
    simp only [hpass, Bool.not_true, Bool.false_eq_true] at h
  · rintro ⟨paint, hp, rfl, h⟩
    refine ⟨⟨paint, hp, rfl⟩, ?_⟩
    rw [Bool.not_eq_true']
    apply Bool.of_not_eq_true
    intro hpass
    exact Nat.not_lt_of_ge ((assessPair_contract required paint.ink
      (paint.ground.getD defaultGround)).2.mp hpass) h

/-- Empty failure output certifies all recorded pairs at the supplied
threshold, in both directions. No premise assumes the judge's correctness. -/
theorem shippedFailures_clear_contract (defaultGround : Color) (required : Nat)
    (out : Out) :
    shippedFailures defaultGround required out = #[] ↔
      ∀ paint, PaintOccurs out paint →
        required ≤ contrastMilli paint.ink (paint.ground.getD defaultGround) := by
  rw [Array.eq_empty_iff_forall_not_mem]
  constructor
  · intro h paint hp
    apply Nat.le_of_not_gt
    intro hlt
    exact h (assessRun defaultGround required paint)
      ((shippedFailures_exact ..).mpr ⟨paint, hp, rfl, hlt⟩)
  · intro h a ha
    rcases (shippedFailures_exact ..).mp ha with ⟨paint, hp, _, hlt⟩
    exact Nat.not_lt_of_ge (h paint hp) hlt

end LeanTex.Core.Contrast
