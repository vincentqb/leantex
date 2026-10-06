import LeanTex.Core.Layout

namespace LeanTex.Core.Layout

open Font Ir

instance : LawfulBEq FrameOrigin where
  eq_of_beq := by
    intro a b h
    cases a with | mk sa ta =>
      cases b with | mk sb tb =>
        change ((sa == sb) && (ta == tb)) = true at h
        simpa only [FrameOrigin.mk.injEq, Bool.and_eq_true, beq_iff_eq] using h
  rfl := by
    intro a
    cases a with | mk s t =>
      change ((s == s) && (t == t)) = true
      simp

namespace FramePartition

/-- One key per collected source and overlay step. Only keys are
deduplicated: repeated, equal physical pages still contribute separately
to the counts below. This reads collector openings, never displayed
counters or a predicted number of overlay pages. -/
def origins (openings : Array FrameOpening) : List FrameOrigin :=
  (openings.toList.filterMap (·.origin)).eraseDups

/-- All physical pages carrying one opening's source and overlay step.
`none` selects the unowned flow pages. -/
def pages (out : Out) (owner : Option FrameOrigin) : Array PageOut :=
  out.pages.filter (fun p => p.frameOrigin == owner)

/-- Actual physical pages of one source, including every overlay and spill. -/
def sourcePages (out : Out) (source : Nat) : Array PageOut :=
  out.pages.filter (fun p => p.frameOrigin.any (fun o => o.source == source))

/-- The actual collected overlay keys of one source. -/
def steps (openings : Array FrameOpening) (source : Nat) : List FrameOrigin :=
  (origins openings).filter (fun o => o.source == source)

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | x :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem origins_nodup (openings : Array FrameOpening) :
    (origins openings).Nodup :=
  eraseDups_nodup _

theorem origins_mem (openings : Array FrameOpening) (origin : FrameOrigin) :
    origin ∈ origins openings ↔ ∃ f ∈ openings, f.origin = some origin := by
  simp [origins, List.mem_filterMap]

theorem pages_mem (out : Out) (owner : Option FrameOrigin) (p : PageOut) :
    p ∈ pages out owner ↔ p ∈ out.pages ∧ p.frameOrigin = owner := by
  simp [pages]

/-- Distinct source/step keys cannot own the same page. Displayed numbers,
footer presence and equality of page contents play no role. -/
theorem pages_disjoint (out : Out) (a b : Option FrameOrigin) (hne : a ≠ b)
    (p : PageOut) (ha : p ∈ pages out a) : p ∉ pages out b := by
  intro hb
  exact hne ((pages_mem ..).mp ha |>.2 |>.symm.trans ((pages_mem ..).mp hb).2)

private theorem sum_map_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem indicator_sum {α : Type} [DecidableEq α]
    (keys : List α) (hn : keys.Nodup) (key : α) :
    (keys.map (fun k => if key = k then 1 else 0)).sum =
      if key ∈ keys then 1 else 0 := by
  induction keys with
  | nil => simp
  | cons k keys ih =>
    obtain ⟨hk, ht⟩ := List.nodup_cons.mp hn
    by_cases he : key = k
    · subst key
      simp [hk, ih ht]
    · simp [he, ih ht]

/-- Each list position contributes to exactly one listed key. This is a
count of occurrences, so equal page values are not collapsed. -/
private theorem count_partition {α β : Type} [DecidableEq β]
    (xs : List α) (key : α → β) (keys : List β) (hn : keys.Nodup)
    (hc : ∀ x ∈ xs, key x ∈ keys) :
    (keys.map (fun k => xs.countP (fun x => decide (key x = k)))).sum = xs.length := by
  induction xs with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons x xs ih =>
    have hx := hc x (by simp)
    have ht : ∀ y ∈ xs, key y ∈ keys := fun y hy => hc y (by simp [hy])
    simp only [List.countP_cons, List.length_cons]
    rw [sum_map_add]
    have hi := indicator_sum keys hn (key x)
    simp only [hx, ↓reduceIte] at hi
    simp only [decide_eq_true_eq, hi, ih ht]

private theorem pages_size_count (out : Out) (owner : Option FrameOrigin) :
    (pages out owner).size =
      out.pages.toList.countP (fun p => decide (p.frameOrigin = owner)) := by
  unfold pages
  rw [← Array.countP_eq_size_filter, Array.countP_toList]
  congr 1
  funext p
  by_cases he : p.frameOrigin = owner <;> simp [he]

/-- The finite set of partition keys includes the flow bucket, even when
that bucket is empty. -/
def keys (openings : Array FrameOpening) : List (Option FrameOrigin) :=
  none :: (origins openings).map some

theorem keys_nodup (openings : Array FrameOpening) :
    (keys openings).Nodup := by
  simp only [keys, List.nodup_cons, List.mem_map,
    Option.some_ne_none, and_false, exists_false, not_false_eq_true, true_and]
  simpa only [List.Nodup, List.pairwise_map, ne_eq, Option.some.injEq] using
    origins_nodup openings

theorem run_owner_mem (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span))
    (p : PageOut) (hp : p ∈ (run geom fs pats doc imgs frameSpans).pages) :
    p.frameOrigin ∈ keys (frameOpenings geom fs pats doc imgs frameSpans) := by
  cases ho : p.frameOrigin with
  | none => simp [keys]
  | some origin =>
    obtain ⟨f, hf, he, _, _⟩ :=
      frame_pages_footed geom fs pats doc imgs frameSpans p hp origin ho
    have hm := (origins_mem _ origin).mpr ⟨f, hf, he⟩
    simp [keys, hm]

/-- Actual physical page counts, summed over the collector's distinct
source/step keys and the unowned flow bucket, equal the public run's page
count. The coverage premise of the counting algebra is discharged by the
actual collector/placement invariant, including spills and float replay. -/
theorem run_count_exact (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store) (frameSpans : Array (Nat × Span)) :
    let out := run geom fs pats doc imgs frameSpans
    let openings := frameOpenings geom fs pats doc imgs frameSpans
    (pages out none).size +
      ((origins openings).map (fun origin => (pages out (some origin)).size)).sum =
        out.pages.size := by
  have hc := count_partition
    (run geom fs pats doc imgs frameSpans).pages.toList PageOut.frameOrigin
    (keys (frameOpenings geom fs pats doc imgs frameSpans)) (keys_nodup _)
    (fun p hp => run_owner_mem geom fs pats doc imgs frameSpans p
      (Array.mem_toList_iff.mp hp))
  simp only [keys, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_def] at hc
  simpa only [pages_size_count, Array.length_toList] using hc

private theorem source_pages_owner (out : Out) (source : Nat) (origin : FrameOrigin)
    (hs : origin.source = source) :
    pages { out with pages := sourcePages out source } (some origin) =
      pages out (some origin) := by
  simp only [pages, sourcePages, Array.filter_filter]
  congr 1
  funext p
  cases ho : p.frameOrigin with
  | none => simp
  | some o =>
    by_cases he : o = origin
    · simp [he, hs]
    · simp [he]

/-- A source's physical-page count is the sum of its actual overlay
counts. In particular an overflowing overlay contributes every page it
ships, and repeated displayed numbers cannot transfer pages between
source indices. -/
theorem run_source_count_exact (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store)
    (frameSpans : Array (Nat × Span)) (source : Nat) :
    let out := run geom fs pats doc imgs frameSpans
    let openings := frameOpenings geom fs pats doc imgs frameSpans
    ((steps openings source).map (fun origin => (pages out (some origin)).size)).sum =
      (sourcePages out source).size := by
  let out := run geom fs pats doc imgs frameSpans
  let openings := frameOpenings geom fs pats doc imgs frameSpans
  let selected := { out with pages := sourcePages out source }
  have hn : ((steps openings source).map some).Nodup := by
    simpa only [steps, List.Nodup, List.pairwise_map, ne_eq, Option.some.injEq] using
      (origins_nodup openings).filter (fun o => o.source == source)
  have hc : ∀ p ∈ selected.pages.toList,
      p.frameOrigin ∈ (steps openings source).map some := by
    intro p hp
    have hm : p ∈ sourcePages out source := Array.mem_toList_iff.mp hp
    obtain ⟨hp, hs⟩ := Array.mem_filter.mp hm
    cases ho : p.frameOrigin with
    | none => simp [ho] at hs
    | some origin =>
      have hs' : origin.source = source := by simpa [ho] using hs
      obtain ⟨f, hf, he, _, _⟩ :=
        frame_pages_footed geom fs pats doc imgs frameSpans p hp origin ho
      have hm := (origins_mem openings origin).mpr ⟨f, hf, he⟩
      simp [steps, hm, hs']
  have total := count_partition selected.pages.toList PageOut.frameOrigin
    ((steps openings source).map some) hn hc
  have sizes : (steps openings source).map
      (fun origin => (pages selected (some origin)).size) =
      (steps openings source).map (fun origin => (pages out (some origin)).size) := by
    apply List.map_congr_left
    intro origin ho
    have hs : origin.source = source := by
      simpa using (List.mem_filter.mp ho).2
    exact congrArg Array.size (source_pages_owner out source origin hs)
  simp only [List.map_map, Function.comp_def, ← pages_size_count,
    Array.length_toList, sizes] at total
  exact total

end FramePartition

/-- Corrected physical frame partition. Every actual page has exactly one
bucket among the real collector's source/step openings and the flow bucket;
these buckets account for every physical page, with multiplicity. A spill
adds a page to its source/step bucket, and a restarted display counter does
not merge distinct sources. The original overlay-count claim is refuted
by `LayoutContracts.counterexamples`. -/
theorem pages_partition_frames (geom : Geom) (fs : FontSet)
    (pats : Option Hyphen.Patterns) (doc : Doc) (imgs : Image.Store := {})
    (frameSpans : Array (Nat × Span) := #[]) :
    let out := run geom fs pats doc imgs frameSpans
    let openings := frameOpenings geom fs pats doc imgs frameSpans
    (FramePartition.keys openings).Nodup ∧
    (∀ p ∈ out.pages, ∃ owner ∈ FramePartition.keys openings,
      p ∈ FramePartition.pages out owner ∧
      ∀ other, p ∈ FramePartition.pages out other → other = owner) ∧
    (FramePartition.pages out none).size +
      ((FramePartition.origins openings).map
        (fun origin => (FramePartition.pages out (some origin)).size)).sum =
      out.pages.size ∧
    (∀ source, ((FramePartition.steps openings source).map
      (fun origin => (FramePartition.pages out (some origin)).size)).sum =
        (FramePartition.sourcePages out source).size) := by
  refine ⟨FramePartition.keys_nodup _, ?_,
    FramePartition.run_count_exact geom fs pats doc imgs frameSpans,
    FramePartition.run_source_count_exact geom fs pats doc imgs frameSpans⟩
  intro p hp
  refine ⟨p.frameOrigin, FramePartition.run_owner_mem geom fs pats doc imgs frameSpans p hp,
    (FramePartition.pages_mem ..).mpr ⟨hp, rfl⟩, ?_⟩
  intro other ho
  exact ((FramePartition.pages_mem ..).mp ho).2.symm

end LeanTex.Core.Layout
