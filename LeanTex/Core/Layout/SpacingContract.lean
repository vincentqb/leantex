module

public import LeanTex.Core.Layout
import all LeanTex.Core.Layout

namespace LeanTex.Core.Layout.Spacing

open LeanTex.Core.Dim

/- The old unconditional statement was false in two independent ways:
an element declaration can replace a larger peer default, and a page break
can lower a later line's page-local baseline. The contract below quantifies
over a fixed production boundary. It compares resolved widths, accounts for
the default that the declaration removes, and derives placement from an
explicit fit inequality. No emitted-gap or displacement inequality is assumed. -/

private def selectedDefault (p : PendingView) (peer tex : Glue) : Glue :=
  if p.trivOwed then tex else peer

/-- The resolved default an element declaration must replace. An empty
boundary can owe the peer default. A zero-width tail causes `addvspace` to
append and clear `declaredSkip`, so its old stacked default must be covered.
A nonzero tail keeps that flag and pays the larger tail width instead. -/
public def replacementFloor (a : Pending) (r : Context) : Sp :=
  let p := pending a
  match p.owed.back? with
  | none =>
    if p.wantDefault then
      (peerGap r).width -
        (if p.declaredSkip then (selectedDefault p (peerGap r) (texGap r)).width else 0)
    else 0
  | some last =>
    if last.width == 0 && p.wantDefault && p.declaredSkip then
      (selectedDefault p (peerGap r) (texGap r)).width
    else 0

/-- Input condition in resolved scaled points. Nonnegative width alone does
not cover a positive peer default that the element's convention removes. -/
public def CoversDefault (a : Pending) (r : Context) (g : Glue) : Prop :=
  (0 : Int) ≤ g.width ∧ replacementFloor a r ≤ g.width

private def boundaryWidth (p : PendingView) (peer tex : Glue) : Sp :=
  (p.owed.foldl Glue.add {}).width +
    if p.owed.isEmpty then
      if p.wantDefault then peer.width else 0
    else if p.wantDefault && p.declaredSkip then (selectedDefault p peer tex).width else 0

private theorem flushed_width (a : Pending) (r : Context) (h : Ordinary a) :
    ((flushed a r).foldl Glue.add {}).width =
      boundaryWidth (pending a) (peerGap r) (texGap r) := by
  rw [(flush_emits_exact a r h).2]
  generalize pending a = p
  rcases p with ⟨owed, want, declared, triv⟩
  by_cases he : owed.isEmpty = true
  · have hz : owed = #[] := Array.empty_of_isEmpty he
    subst owed
    cases want <;> simp [boundaryWidth, Glue.add]
  · have hn : owed.isEmpty = false := Bool.eq_false_iff.mpr he
    cases want <;> cases declared <;> cases triv <;>
      simp [boundaryWidth, selectedDefault, hn, Glue.add, Int.add_comm]

private theorem sum_width_from (gs : Array Glue) (g : Glue) :
    (gs.foldl Glue.add g).width = g.width + (gs.foldl Glue.add {}).width := by
  have widths (initial : Glue) :
      (gs.foldl Glue.add initial).width =
        gs.foldl (fun w v => w + v.width) initial.width :=
    (Array.foldl_hom (fun v : Glue => v.width)
      (g₁ := Glue.add) (g₂ := fun w v => w + v.width)
      (xs := gs) (init := initial) (fun _ _ => rfl)).symm
  rw [widths, widths]
  have shifted := Array.foldl_hom (fun w : Sp => g.width + w)
    (g₁ := fun w (v : Glue) => w + v.width)
    (g₂ := fun w (v : Glue) => w + v.width)
    (xs := gs) (init := 0) (fun _ _ => Int.add_assoc ..)
  simpa using shifted

/-- The actual `addvOwed` selection never reduces the sum of pending widths
when the inserted width is nonnegative. Empty, zero-tail append, replacement
and retained-tail arms are all quantified, including signed prior glue. -/
public theorem merge_width_monotone (gs : Array Glue) (g : Glue)
    (hg : (0 : Int) ≤ g.width) :
    (gs.foldl Glue.add {}).width ≤ ((merge gs g).foldl Glue.add {}).width := by
  cases hb : gs.back? with
  | none =>
    have hz := Array.back?_eq_none_iff.mp hb
    subst gs
    rw [merge_exact]
    simp only [Array.back?_empty]
    simpa [Glue.add] using hg
  | some last =>
    obtain ⟨prior, rfl⟩ := Array.back?_eq_some_iff.mp hb
    rw [merge_exact]
    simp only [Array.back?_push]
    by_cases h0 : last.width == 0
    · simp only [h0, ite_true, Array.foldl_push, Glue.add]
      exact Int.le_add_of_nonneg_right hg
    · simp only [h0, Bool.false_eq_true, ite_false]
      by_cases hlt : last.width < g.width
      · simp only [hlt, ite_true, Array.pop_push, Array.foldl_push, Glue.add]
        exact Int.add_le_add_left (Int.le_of_lt hlt) _
      · simp [hlt]

/-- The resolved compensation condition suffices for the emitted boundary,
including the empty-boundary default that `gapGlue` alone does not count. -/
public theorem flushed_width_monotone (a : Pending) (r : Context) (g : Glue)
    (h : Ordinary a) (hc : CoversDefault a r g) :
    ((flushed a r).foldl Glue.add {}).width ≤
      ((flushed (add a g) r).foldl Glue.add {}).width := by
  rw [flushed_width a r h, flushed_width (add a g) r (add_ordinary a g h)]
  rw [add_pending_exact]
  rcases hc with ⟨hg, hc⟩
  unfold replacementFloor at hc
  generalize pending a = p at hc ⊢
  rcases p with ⟨owed, want, declared, triv⟩
  cases hb : owed.back? with
  | none =>
    have hz := Array.back?_eq_none_iff.mp hb
    subst owed
    have hm : merge #[] g = #[g] := by
      rw [merge_exact]
      simp only [Array.back?_empty]
    cases want <;> cases declared <;> cases triv <;>
      simp_all [boundaryWidth, selectedDefault, Glue.add] <;>
      dsimp only [Sp] at * <;> omega
  | some last =>
    obtain ⟨prior, rfl⟩ := Array.back?_eq_some_iff.mp hb
    simp only [Array.back?_push, Option.any_some] at hc ⊢
    rw [merge_exact]
    simp only [Array.back?_push]
    by_cases h0 : last.width == 0
    · cases want <;> cases declared <;> cases triv <;>
        simp_all [boundaryWidth, selectedDefault, Glue.add] <;>
        dsimp only [Sp] at * <;> omega
    · by_cases hlt : last.width < g.width
      · cases want <;> cases declared <;> cases triv <;>
          simp_all [boundaryWidth, selectedDefault, Glue.add] <;>
          dsimp only [Sp] at * <;> omega
      · simp [h0, hlt]

/-- The page's fit test as an input inequality over the current geometry,
the fixed line's measured extent, and the resolved glue about to be consumed.
This does not assert that a line stayed on a page: `place_exact` proves that
the production `fitCommit` takes its checked commit arm from this bound. -/
public def Fits (a : Pending) (r : Context) (b : Page) (size : Sp)
    (segs : Array Seg) : Prop :=
  let i := input r b size segs
  let g := (flushed a r).foldl Glue.add i.skip
  i.origin + g.width + i.inkBelow - i.floor ≤ i.shrink + g.shrink

/-- **Resolved element spacing is monotone on a fixed page.** The actual
collector emits only the witnessed skips; actual skip placement and
`placeLine` preserve the shipped prefix and all prior baselines, and append
one baseline that does not move upward. The premises name ordinary boundary
state, resolved default compensation, ordinary text geometry and both input
fit inequalities. They assume no glue-selection or line-movement result.

This is a contract at the production placement boundary, before page-close
stretch/shrink distribution. It does not compare unconstrained whole-document
runs or infer rendered ink from font metadata. -/
public theorem elementSpace_placement_monotone (a : Pending) (r : Context) (b : Page)
    (x size : Sp) (segs : Array Seg) (width : Sp) (g : Glue)
    (ha : Ordinary a) (hb : Ready b segs) (hg : CoversDefault a r g)
    (hfit : Fits a r b size segs) (hfit' : Fits (add a g) r b size segs) :
    Emits a r (flushed a r) ∧ Emits (add a g) r (flushed (add a g) r) ∧
    shipped (place a r b x size segs width) = shipped b ∧
    shipped (place (add a g) r b x size segs width) = shipped b ∧
    ∃ y y' : Sp,
      baselines (place a r b x size segs width) = (baselines b).push y ∧
      baselines (place (add a g) r b x size segs width) = (baselines b).push y' ∧
      y ≤ y' := by
  have hp := place_exact a r b x size segs width hb hfit
  have hp' := place_exact (add a g) r b x size segs width hb hfit'
  have hw := flushed_width_monotone a r g ha hg
  refine ⟨(flush_emits_exact a r ha).1,
    (flush_emits_exact (add a g) r (add_ordinary a g ha)).1,
    hp.1, hp'.1, _, _, hp.2, hp'.2, ?_⟩
  rw [sum_width_from (flushed a r) (input r b size segs).skip,
    sum_width_from (flushed (add a g) r) (input r b size segs).skip]
  exact Int.add_le_add_left (Int.add_le_add_left hw _) _

/-- Resolved element spacing cannot lower the last ink baseline of the
actual `Layout.run` output under the stated production input conditions.

Both documents reach the same preceding layout and prepared final paragraph;
their intervening operations are the actual collector's ordinary flush,
before and after `add`. The resolved gap covers any displaced
default. Each line meets the real placer's numeric fit test, and the last
page closes naturally at fixed top alignment without fil redistribution.
`AtTail` and `ParagraphSafe` name these input conditions; neither assumes
baseline order or page preservation. Paragraphs may have any line count.

The unqualified claim remains false: replacing a larger default or starting
a new page can move the last local baseline upward. Tests/ElementSpacing
retains both counterexamples and the signed relative-length counterexample.
The final projection reads text ink, excluding notes and furniture, exactly
as the original whole-run obligation did. -/
public theorem elementSpace_monotone (geom : Geom) (fs : Font.FontSet)
    (before after : Ir.Doc) (a : Pending) (r : Context) (b : Page)
    (j : Paragraph) (breaks : Array Nat) (g : Glue)
    (ha : Ordinary a) (hg : CoversDefault a r g)
    (hbefore : AtTail geom fs before b j breaks (flushed a r))
    (hafter : AtTail geom fs after b j breaks (flushed (add a g) r))
    (hfit : ParagraphSafe fs b j breaks (flushed a r))
    (hfit' : ParagraphSafe fs b j breaks (flushed (add a g) r)) :
    ((inkBaselines (Layout.run geom fs none before)).getLast?.getD 0 : Int) ≤
      (inkBaselines (Layout.run geom fs none after)).getLast?.getD 0 := by
  apply run_tail_monotone geom fs before after b j breaks _ _
    hbefore hafter hfit hfit'
  rw [sum_width_from (flushed a r) (queuedGlue b),
    sum_width_from (flushed (add a g) r) (queuedGlue b)]
  exact Int.add_le_add_left (flushed_width_monotone a r g ha hg) _

/-- A certificate discharges the staging and fit premises of the whole-run
contract. The remaining inequality compares resolved input glue, before
placement; the common queued glue cancels. -/
public theorem TailPair.run_monotone {geom : Geom} {fs : Font.FontSet}
    {before after : Ir.Doc} (c : TailPair geom fs before after)
    (hw : (c.beforeSkips.foldl Glue.add {}).width ≤
      (c.afterSkips.foldl Glue.add {}).width) :
    ((inkBaselines (Layout.run geom fs none before)).getLast?.getD 0 : Int) ≤
      (inkBaselines (Layout.run geom fs none after)).getLast?.getD 0 := by
  apply run_tail_monotone geom fs before after c.page c.paragraph c.breaks
    c.beforeSkips c.afterSkips c.before_reaches c.after_reaches
    c.before_safe c.after_safe
  rw [sum_width_from c.beforeSkips (queuedGlue c.page),
    sum_width_from c.afterSkips (queuedGlue c.page)]
  exact Int.add_le_add_left hw _

/-- A sufficient-input check for arbitrary actual documents. The bounded
two-paragraph certificate checks common preparation and numeric fit; this
last check compares only the resolved intervening glue. `false` can mean an
unsupported document shape, changed preparation, failed fit bounds, or decreasing
glue. It is not a completeness claim about all monotone document changes. -/
public def twoParagraphIncreasing (geom : Geom) (fs : Font.FontSet)
    (before after : Ir.Doc) : Bool :=
  match twoParagraphPair? geom fs before after with
  | none => false
  | some c => decide ((c.beforeSkips.foldl Glue.add {}).width ≤
      (c.afterSkips.foldl Glue.add {}).width)

/-- An accepted input check proves the real `Layout.run` comparison for
every supplied font environment and document pair. Callers need neither
private staging identities nor an assumed output-page comparison. -/
public theorem twoParagraphIncreasing_contract (geom : Geom) (fs : Font.FontSet)
    (before after : Ir.Doc) (h : twoParagraphIncreasing geom fs before after = true) :
    ((inkBaselines (Layout.run geom fs none before)).getLast?.getD 0 : Int) ≤
      (inkBaselines (Layout.run geom fs none after)).getLast?.getD 0 := by
  cases hc : twoParagraphPair? geom fs before after with
  | none => simp [twoParagraphIncreasing, hc] at h
  | some c =>
    apply c.run_monotone
    exact of_decide_eq_true (by simpa [twoParagraphIncreasing, hc] using h)

end LeanTex.Core.Layout.Spacing
