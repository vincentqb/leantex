module

import LeanTex.Core.Layout.GlyphBounds

/-! The producer's paired measurement and its contracts are available from
an ordinary import. The glyph equation remains usable by layout's
agreement proof; its fold-induction machinery is private. -/

open LeanTex.Core
open LeanTex.Core.Layout.GlyphBounds
open Dim

namespace Tests.GlyphBoundsInterface

example : Repr Measurement := inferInstance
example : BEq Measurement := inferInstance
example : Inhabited Measurement := inferInstance
example (top below : Sp) (unknown : Bool) : Measurement :=
  { extent := (top, below), unresolved := unknown }
example : Measurement → Measurement → Measurement := Measurement.join

example (font : Font.Font) (size raise : Sp) (gid : Nat) (lo hi : Int)
    (known : font.yExtent gid = some (lo, hi)) :
    glyph font size raise gid =
      { extent := (hi * size / (font.unitsPerEm : Int) + raise,
          (-lo) * size / (font.unitsPerEm : Int) - raise) } :=
  glyph_known_exact font size raise gid lo hi known

example (font : Font.Font) (size raise : Sp) (gid : Nat) :
    (glyph font size raise gid).unresolved = true ↔ font.yExtent gid = none :=
  glyph_unresolved_exact font size raise gid

-- The real agreement proof unfolds both branches, including the nominal
-- fallback, whose local scaler needs no exported helper.
example (font : Font.Font) (size raise : Sp) (gid : Nat) :
    (glyph font size raise gid).extent =
      match font.yExtent gid with
      | some (lo, hi) =>
        (hi * size / (font.unitsPerEm : Int) + raise,
          (-lo) * size / (font.unitsPerEm : Int) - raise)
      | none =>
        ((font.capHeight.toNat * size.toNat) / font.unitsPerEm + raise,
          ((-font.descent).toNat * size.toNat) / font.unitsPerEm - raise) := by
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
