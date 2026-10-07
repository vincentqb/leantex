module

public import LeanTex.Core.Ir
import LeanTex.Core.Oklab

/-!
The WCAG arithmetic shared by painting defaults and the document contrast
judge. Keeping it below layout lets a pure painter read the very same
thresholds the judge checks, without importing the judge's document walk.

Sources: WCAG 2.2, relative luminance, contrast ratio, SC 1.4.3 and SC 1.4.11:
https://www.w3.org/TR/WCAG22/#dfn-relative-luminance
https://www.w3.org/TR/WCAG22/#dfn-contrast-ratio
-/
namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir
open LeanTex.Core.Oklab (channelLinear)

/-- WCAG relative luminance in units of 10⁻⁷ (0 = black, 10⁷ = white):
0.2126·R + 0.7152·G + 0.0722·B over the linearised channels.
`Oklab.channelLinear` is the one tabulation of the sRGB transfer function.
The division truncates below 10⁻⁷. -/
public def luminance (c : Color) : Nat :=
  (2126 * (channelLinear.getD c.r.toNat 0)
    + 7152 * (channelLinear.getD c.g.toNat 0)
    + 722 * (channelLinear.getD c.b.toNat 0)) / 10000

/-- WCAG contrast ratio ×1000, truncated: (L₁ + 0.05)/(L₂ + 0.05) with the
lighter luminance on top. Channel rounding and truncation differ from the
real-valued ratio by less than 0.007. -/
public def contrastMilli (a b : Color) : Nat :=
  let la := luminance a
  let lb := luminance b
  ((max la lb + 500000) * 1000) / (min la lb + 500000)

/-- An arithmetic assessment, before a caller's exemption policy. Ratios
and thresholds use the units of `contrastMilli`. -/
public structure PairAssessment where
  ratio : Nat
  required : Nat
  deriving Repr, BEq

public def PairAssessment.passes (a : PairAssessment) : Bool :=
  decide (a.required ≤ a.ratio)

/-- The integer comparison shared by the document use judge and the
placed-run audit. This asserts the implemented arithmetic, not equality
to an unrounded real-valued WCAG computation. -/
public def assessPair (required : Nat) (ink ground : Color) : PairAssessment :=
  { ratio := contrastMilli ink ground, required }

public theorem assessPair_contract (required : Nat) (ink ground : Color) :
    (assessPair required ink ground).ratio = contrastMilli ink ground ∧
    ((assessPair required ink ground).passes = true ↔
      required ≤ contrastMilli ink ground) := by
  exact ⟨rfl, decide_eq_true_iff⟩

/-- SC 1.4.3 (AA), normal text: 4.5:1. -/
public def aaText : Nat := 4500
/-- SC 1.4.3 (AA), large-scale text (≥ 18pt, or ≥ 14pt bold): 3:1. -/
public def aaLargeText : Nat := 3000
/-- SC 1.4.11 (AA), non-text UI information: 3:1. -/
public def aaNonText : Nat := 3000

/-- WCAG 2.2's large-scale text boundary, in the same point units as layout.
The document planner and placed-glyph judge share this decision. -/
public def largeText (size : Dim.Sp) (bold : Bool) : Bool :=
  size ≥ Dim.pt 18 || (bold && size ≥ Dim.pt 14)

public def textRequired (size : Dim.Sp) (bold : Bool) : Nat :=
  if largeText size bold then aaLargeText else aaText

end LeanTex.Core.Contrast
