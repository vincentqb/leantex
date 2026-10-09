module

public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Layout

/-!
Contrast observations over placed glyphs. The document realization plan
cannot enumerate all such paint: overlays compute colours, and pictures
and furniture can introduce ink after that walk.

The arithmetic contract is over `Ir.Color`. Its placed-page projection
reads actual `Layout.Out` data and preserves every occurrence and address.
The raw audit retains observations under caller-selected thresholds.
The PDF assertion instead reads actual font metrics and a conservative
background decision; unsupported evidence remains explicitly unverified.
A recorded run ground or a colour resembling covered text is no exemption.
-/
namespace LeanTex.Core.Contrast

open Ir Layout

/-- A nonempty glyph run's paint at its zero-based address in the output.
`ground` retains `none`: resolving a fallback must not erase the evidence
that a painter did not record a local ground. -/
public structure RunPaint where
  page : Nat
  line : Nat
  segment : Nat
  ink : Color
  ground : Option Color
  deriving Repr, BEq

/-- Read exactly the paint a glyph run carries. Spacing, rules, decoration,
images and polygons are outside this text census. -/
public def runPaint? (page line segment : Nat) : Seg → Option RunPaint
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
public def shippedPaints (out : Out) : Array RunPaint :=
  out.pages.zipIdx.flatMap fun (page, p) =>
    page.lines.zipIdx.flatMap fun (line, l) =>
      line.segs.zipIdx.filterMap fun (seg, s) => runPaint? p l s seg

/-- Independent address-based specification of one census entry. -/
public def PaintOccurs (out : Out) (paint : RunPaint) : Prop :=
  ∃ page line seg,
    out.pages[paint.page]? = some page ∧
    page.lines[paint.line]? = some line ∧
    line.segs[paint.segment]? = some seg ∧
    runPaint? paint.page paint.line paint.segment seg = some paint

/-- Both directions: every census entry has an actual nonempty glyph run
at its reported address, and every such run is present. -/
public theorem shippedPaints_exact (out : Out) (paint : RunPaint) :
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
public theorem shippedPaints_covers (out : Out)
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
public structure RunAssessment where
  paint : RunPaint
  assessment : PairAssessment
  deriving Repr, BEq

public def assessRun (defaultGround : Color) (required : Nat) (paint : RunPaint) :
    RunAssessment :=
  { paint, assessment := assessPair required paint.ink (paint.ground.getD defaultGround) }

/-- Arithmetic for every nonempty placed glyph run. Call with the effective
page ground for the document that produced `out`. This does not resolve a
picture's unrecorded local fill or recover exemption provenance. -/
public def shippedAudit (defaultGround : Color) (required : Nat) (out : Out) :
    Array RunAssessment :=
  (shippedPaints out).map (assessRun defaultGround required)

public theorem shippedAudit_exact (defaultGround : Color) (required : Nat)
    (out : Out) (a : RunAssessment) :
    a ∈ shippedAudit defaultGround required out ↔
      ∃ paint, PaintOccurs out paint ∧ assessRun defaultGround required paint = a := by
  simp only [shippedAudit, Array.mem_map, shippedPaints_exact]

/-- The audit never silently drops a run. The retained entry includes the
actual colours and the implemented contrast decision. -/
public theorem shippedAudit_covers (defaultGround : Color) (required : Nat) (out : Out)
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
public def shippedFailures (defaultGround : Color) (required : Nat) (out : Out) :
    Array RunAssessment :=
  (shippedAudit defaultGround required out).filter fun a => !a.assessment.passes

/-- A failure is exactly an actual run below the supplied threshold. -/
public theorem shippedFailures_exact (defaultGround : Color) (required : Nat)
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
public theorem shippedFailures_clear_contract (defaultGround : Color) (required : Nat)
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

/-- Paint outside the text census may overlap a glyph. Until a local
occlusion proof is available, such a page cannot borrow a recorded run
ground as evidence of its visible background. -/
private def textOnly : Seg → Bool
  | .run _ _ _ _ _ _ _ decorations _ _ _ =>
    !decorations.underline && decorations.lineThrough.isNone
  | .gap .. => true
  | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => false

/-- A sufficient, deliberately conservative background decision over the
actual PDF paint list. Every rectangle covers the medium, no path paints,
and no later non-text segment can obscure the text. The last rectangle
wins; an unpainted PDF page uses white paper. This certifies the uniform
substrate only, not absence of overlapping text or full WCAG conformance.
PDF painting order is `fills`, picture ink, text, then inline graphics. -/
public def uniformTextGround? (geom : Geom) (page : PageOut) : Option Color :=
  if page.inks.any (fun ink => !ink.fig.marks.isEmpty) ||
      !(page.lines.all fun line => line.segs.all textOnly) ||
      !(page.fills.all fun fill =>
        fill.x ≤ -geom.bleed && fill.y ≤ -geom.bleed &&
        geom.pageW + geom.bleed ≤ fill.x + fill.w &&
        geom.pageH + geom.bleed ≤ fill.y + fill.h) then none
  else some ((page.fills.back?).map (·.color) |>.getD Color.white)

/-- Cache each page's background decision once; assessing many runs must
not rescan every page's paint for each glyph run. -/
public def shippedGrounds (geom : Geom) (out : Out) : Array (Option Color) :=
  out.pages.map (uniformTextGround? geom)

public theorem shippedGrounds_projects (geom : Geom) (out : Out) {p : Nat} {page : PageOut}
    (h : out.pages[p]? = some page) :
    (shippedGrounds geom out)[p]? = some (uniformTextGround? geom page) := by
  simp [shippedGrounds, Array.getElem?_map, h]

/-- Actual point size and OpenType weight, including the PDF writer's
fallback to the body face. An absent font is unresolved, never bold by
assumption. No source colour spelling is used as an exemption. -/
public def runMetrics? (fs : Font.FontSet) (out : Out) (paint : RunPaint) :
    Option (Dim.Sp × Nat) := do
  let page ← out.pages[paint.page]?
  let line ← page.lines[paint.line]?
  let .run idx _ _ _ _ size _ _ _ _ _ ← line.segs[paint.segment]? | none
  let font ← fs.fonts[idx]?.orElse fun _ => fs.fonts[0]?
  return (if size == 0 then line.size else size, font.weight)

public inductive ContrastUnknown where
  | metrics
  | nonpositiveSize
  | ground
  deriving Repr, BEq

/-- An arithmetic verdict or the precise evidence the judge lacks.
Below-threshold paint is retained even when it might be deliberately
covered: declaring an exemption requires provenance, not colour equality. -/
public inductive TextVerdict where
  | measured (ground : Color) (size : Dim.Sp) (weight : Nat) (pair : PairAssessment)
  | unverified (reason : ContrastUnknown)
  deriving Repr, BEq

public def TextVerdict.passes : TextVerdict → Bool
  | .measured _ _ _ pair => pair.passes
  | .unverified _ => false

public structure JudgedPaint where
  paint : RunPaint
  verdict : TextVerdict
  deriving Repr, BEq

public def judgePaint (grounds : Array (Option Color)) (fs : Font.FontSet)
    (out : Out) (paint : RunPaint) : JudgedPaint :=
  { paint, verdict :=
    match runMetrics? fs out paint with
    | none => .unverified .metrics
    | some (size, weight) =>
      if size ≤ 0 then .unverified .nonpositiveSize
      else match grounds[paint.page]?.join with
        | none => .unverified .ground
        | some ground => .measured ground size weight
          (assessPair (textRequired size (weight ≥ 700)) paint.ink ground) }

/-- Independent acceptance condition: actual font metrics, a positive
size, a supported background and the implemented integer contrast bound.
There is no premise assuming that an earlier diagnostic judge was complete. -/
public def TextVerified (grounds : Array (Option Color)) (fs : Font.FontSet)
    (out : Out) (paint : RunPaint) : Prop :=
  ∃ size weight ground,
    runMetrics? fs out paint = some (size, weight) ∧
    0 < size ∧ grounds[paint.page]?.join = some ground ∧
    textRequired size (weight ≥ 700) ≤ contrastMilli paint.ink ground

public theorem judgePaint_exact (grounds : Array (Option Color)) (fs : Font.FontSet)
    (out : Out) (paint : RunPaint) :
    (judgePaint grounds fs out paint).verdict.passes = true ↔
      TextVerified grounds fs out paint := by
  cases hm : runMetrics? fs out paint with
  | none => simp [judgePaint, hm, TextVerdict.passes, TextVerified]
  | some metrics =>
    rcases metrics with ⟨size, weight⟩
    by_cases hs : size ≤ 0
    · simp [judgePaint, hm, hs, TextVerdict.passes, TextVerified, Int.not_lt.mpr hs]
    · cases hg : grounds[paint.page]?.join with
      | none => simp [judgePaint, hm, hs, hg, TextVerdict.passes, TextVerified]
      | some ground =>
        simp [judgePaint, hm, hs, hg, TextVerdict.passes, TextVerified,
          and_assoc, Int.lt_of_not_ge hs,
          (assessPair_contract (textRequired size (weight ≥ 700)) paint.ink ground).2]

/-- One result for every actual nonempty run, with background scans shared.
Unknown grounds and missing metrics remain in the same census as measured
ink. This runs only when a PDF accessibility assertion requests it. -/
public def shippedJudgments (geom : Geom) (fs : Font.FontSet) (out : Out) :
    Array JudgedPaint :=
  let grounds := shippedGrounds geom out
  (shippedPaints out).map (judgePaint grounds fs out)

/-- Completeness over the placed artifact, replacing the false claim that
the source colour plan enumerates all paint. Every occurrence has its own
verdict, including unresolved cases; repeated colours do not merge sites. -/
public theorem contrast_judged_complete (geom : Geom) (fs : Font.FontSet)
    (out : Out) (paint : RunPaint) (h : PaintOccurs out paint) :
    judgePaint (shippedGrounds geom out) fs out paint ∈ shippedJudgments geom fs out := by
  exact Array.mem_map.mpr ⟨paint, (shippedPaints_exact ..).mpr h, rfl⟩

public def shippedContrastIssues (geom : Geom) (fs : Font.FontSet) (out : Out) :
    Array JudgedPaint :=
  (shippedJudgments geom fs out).filter fun j => !j.verdict.passes

public theorem shippedContrastIssues_exact (geom : Geom) (fs : Font.FontSet)
    (out : Out) (j : JudgedPaint) :
    j ∈ shippedContrastIssues geom fs out ↔
      ∃ paint, PaintOccurs out paint ∧
        judgePaint (shippedGrounds geom out) fs out paint = j ∧
        ¬ TextVerified (shippedGrounds geom out) fs out paint := by
  simp only [shippedContrastIssues, Array.mem_filter, shippedJudgments,
    Array.mem_map, shippedPaints_exact]
  constructor
  · rintro ⟨⟨paint, hp, rfl⟩, hj⟩
    exact ⟨paint, hp, rfl, fun hv =>
      by simp [(judgePaint_exact ..).mpr hv] at hj⟩
  · rintro ⟨paint, hp, rfl, hv⟩
    refine ⟨⟨paint, hp, rfl⟩, ?_⟩
    rw [Bool.not_eq_true']
    exact Bool.of_not_eq_true (fun h => hv ((judgePaint_exact ..).mp h))

/-- An empty issue list means every placed glyph run has verified metrics,
a supported background and sufficient integer contrast. An unresolved
case cannot silently pass. This is the implemented PDF text-contrast
contract, not a certification of all WCAG criteria or browser paint. -/
public theorem shippedContrast_clear_contract (geom : Geom) (fs : Font.FontSet)
    (out : Out) :
    shippedContrastIssues geom fs out = #[] ↔
      ∀ paint, PaintOccurs out paint →
        TextVerified (shippedGrounds geom out) fs out paint := by
  rw [Array.eq_empty_iff_forall_not_mem]
  constructor
  · intro h paint hp
    apply Classical.byContradiction
    intro hv
    exact h _ ((shippedContrastIssues_exact ..).mpr ⟨paint, hp, rfl, hv⟩)
  · intro h j hj
    rcases (shippedContrastIssues_exact ..).mp hj with ⟨paint, hp, _, hv⟩
    exact hv (h paint hp)

end LeanTex.Core.Contrast
