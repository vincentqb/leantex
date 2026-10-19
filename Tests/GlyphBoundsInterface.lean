module

import LeanTex.Core.Layout.GlyphBounds

/-! The producer's paired measurement and its contracts reach an ordinary import; the fold-induction
machinery stays private. -/

open LeanTex.Core
open LeanTex.Core.Layout.GlyphBounds
open Dim

namespace Tests.GlyphBoundsInterface

example : Repr Measurement := inferInstance
example : BEq Measurement := inferInstance
example : Inhabited Measurement := inferInstance
example (top below : Length) (unknown : Bool) : Measurement :=
  { extent := (top, below), unresolved := unknown }
example : Measurement → Measurement → Measurement := Measurement.join

example (font : Font) (size raise : Length) (gid : Nat) (lo hi : Int)
    (known : font.yExtent gid = some (lo, hi)) :
    glyph font size raise gid =
      { extent := (hi * size / (font.unitsPerEm : Int) + raise,
          (-lo) * size / (font.unitsPerEm : Int) - raise) } :=
  glyph_known_exact font size raise gid lo hi known

example (font : Font) (size raise : Length) (gid : Nat) :
    (glyph font size raise gid).unresolved = true ↔ font.yExtent gid = none :=
  glyph_unresolved_exact font size raise gid

-- Layout's agreement proof unfolds both branches, the nominal fallback included.
example (font : Font) (size raise : Length) (gid : Nat) :
    (glyph font size raise gid).extent =
      match font.yExtent gid with
      | some (lo, hi) =>
        (hi * size / (font.unitsPerEm : Int) + raise,
          (-lo) * size / (font.unitsPerEm : Int) - raise)
      | none =>
        (font.capHeight.toNat * max 0 size / font.unitsPerEm + raise,
          (-font.descent).toNat * max 0 size / font.unitsPerEm - raise) := by
  unfold glyph
  cases font.yExtent gid <;> rfl

example {α : Type} (measure : α → Measurement) (xs : Array α)
    (initial : Measurement) (x : α) (hx : x ∈ xs) :
    (measure x).extent.1 ≤ (fold measure xs initial).extent.1 ∧
      (measure x).extent.2 ≤ (fold measure xs initial).extent.2 :=
  fold_covers measure xs initial x hx

example {α : Type} (measure : α → Measurement) (xs : Array α)
    (initial : Measurement) :
    (fold measure xs initial).unresolved = true ↔
      initial.unresolved = true ∨ ∃ x ∈ xs, (measure x).unresolved = true :=
  fold_unresolved_exact measure xs initial

example : True := by
  fail_if_success have := LeanTex.Core.Layout.GlyphBounds.Dominates
  fail_if_success have := LeanTex.Core.Layout.GlyphBounds.dominates_trans
  fail_if_success have := LeanTex.Core.Layout.GlyphBounds.join_left
  fail_if_success have := LeanTex.Core.Layout.GlyphBounds.join_right
  trivial

end Tests.GlyphBoundsInterface
