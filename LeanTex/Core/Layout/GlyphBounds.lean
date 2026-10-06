module

public import LeanTex.Core.Dim
public import LeanTex.Core.Font

namespace LeanTex.Core.Layout.GlyphBounds

open Dim

/-- A layout extent and whether any part lacks outline evidence. Nominal
font metrics remain useful for best-effort placement, but do not certify
containment of an outline the font reader could not measure. -/
public structure Measurement where
  extent : Sp × Sp := (0, 0)
  unresolved : Bool := false
  deriving Repr, BEq, Inhabited

/-- Read the actual face's outline result. The fallback keeps the existing
placement value and carries its missing evidence in the same result.
The equation is exposed for layout's agreement proof, including its
nominal branch; the fallback scaler stays local to that branch. -/
@[expose] public def glyph (font : Font.Font) (size raise : Sp) (gid : Nat) : Measurement :=
  match font.yExtent gid with
  | some (lo, hi) =>
    { extent := (hi * size / (font.unitsPerEm : Int) + raise,
        (-lo) * size / (font.unitsPerEm : Int) - raise) }
  | none =>
    -- Preserve the layout scaler's treatment of a nonpositive size.
    let nominal (units : Nat) : Sp := (units * size.toNat) / font.unitsPerEm
    { extent := (nominal font.capHeight.toNat + raise,
        nominal (-font.descent).toNat - raise)
      unresolved := true }

/-- Known outline coordinates are scaled in their own run's face, size and
raise, with no substitution of the paragraph face or a nominal height. -/
public theorem glyph_known_exact (font : Font.Font) (size raise : Sp)
    (gid : Nat) (lo hi : Int) (h : font.yExtent gid = some (lo, hi)) :
    glyph font size raise gid =
      { extent := (hi * size / (font.unitsPerEm : Int) + raise,
          (-lo) * size / (font.unitsPerEm : Int) - raise) } := by
  simp [glyph, h]

/-- The unresolved flag records exactly the font reader's failure to
provide an outline extent, even when the nominal fallback is nonzero. -/
public theorem glyph_unresolved_exact (font : Font.Font) (size raise : Sp)
    (gid : Nat) :
    (glyph font size raise gid).unresolved = true ↔ font.yExtent gid = none := by
  cases h : font.yExtent gid <;> simp [glyph, h]

/-- Join ink reaches without losing an unresolved constituent. -/
public def Measurement.join (a b : Measurement) : Measurement :=
  { extent := (max a.extent.1 b.extent.1, max a.extent.2 b.extent.2)
    unresolved := a.unresolved || b.unresolved }

private def Dominates (a b : Measurement) : Prop :=
  a.extent.1 ≤ b.extent.1 ∧ a.extent.2 ≤ b.extent.2

private theorem dominates_trans {a b c : Measurement} (hab : Dominates a b)
    (hbc : Dominates b c) : Dominates a c :=
  ⟨Int.le_trans hab.1 hbc.1, Int.le_trans hab.2 hbc.2⟩

private theorem join_left (a b : Measurement) : Dominates a (a.join b) :=
  ⟨Int.le_max_left _ _, Int.le_max_left _ _⟩

private theorem join_right (a b : Measurement) : Dominates b (a.join b) :=
  ⟨Int.le_max_right _ _, Int.le_max_right _ _⟩

/-- An array fold for measured ink and its missing evidence.
Both fields consume the same constituents in the same pass. -/
public def fold {α : Type} (measure : α → Measurement) (xs : Array α)
    (initial : Measurement := {}) : Measurement :=
  xs.foldl (fun acc x => acc.join (measure x)) initial

/-- Each constituent is bounded by the actual array fold. This is a value
invariant indexed by the consumed prefix, so repeated glyphs need no
uniqueness assumption. -/
public theorem fold_covers {α : Type} (measure : α → Measurement)
    (xs : Array α) (initial : Measurement) (x : α) (hx : x ∈ xs) :
    (measure x).extent.1 ≤ (fold measure xs initial).extent.1 ∧
      (measure x).extent.2 ≤ (fold measure xs initial).extent.2 := by
  obtain ⟨j, hj, hget⟩ := Array.mem_iff_getElem.mp hx
  have h : j < xs.size → Dominates (measure x) (fold measure xs initial) := by
    refine Array.foldl_induction
      (motive := fun n acc => j < n → Dominates (measure x) acc) ?_ ?_
    · omega
    · intro i acc ih hnext
      by_cases hprev : j < i.val
      · exact dominates_trans (ih hprev) (join_left _ _)
      · have hij : i.val = j := by omega
        have hxi : xs[i] = x := by
          change xs[i.val] = x
          simpa only [hij] using hget
        change Dominates (measure x) (acc.join (measure xs[i]))
        rw [hxi]
        exact join_right _ _
  exact h hj

/-- Unknown outlines cannot disappear in a later maximum, including when a
different glyph has a larger known extent. Conversely, a complete fold has
not manufactured an unresolved result. -/
public theorem fold_unresolved_exact {α : Type} (measure : α → Measurement)
    (xs : Array α) (initial : Measurement) :
    (fold measure xs initial).unresolved = true ↔
      initial.unresolved = true ∨ ∃ x ∈ xs, (measure x).unresolved = true := by
  simp only [fold, ← Array.foldl_toList, ← Array.mem_toList_iff]
  induction xs.toList generalizing initial with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Measurement.join, Bool.or_eq_true, List.mem_cons,
      exists_eq_or_imp, or_assoc]

end LeanTex.Core.Layout.GlyphBounds
