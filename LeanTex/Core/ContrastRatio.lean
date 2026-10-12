module

public import LeanTex.Core.Color
public import LeanTex.Core.Dim
public import LeanTex.Core.DesignRole
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

/-- The same ratio from two luminances already in hand (10⁻⁷ units): what a
search reads before it quantizes a candidate. -/
public def ratioOf (la lb : Nat) : Nat :=
  ((max la lb + 500000) * 1000) / (min la lb + 500000)

public theorem contrastMilli_ratioOf_exact (a b : Color) :
    contrastMilli a b = ratioOf (luminance a) (luminance b) := by
  unfold contrastMilli ratioOf
  rfl

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

/-- The ratio a role's need owes, in `contrastMilli`'s units: text 4.5:1
and large-scale text 3:1 (SC 1.4.3), non-text information and a state
change 3:1 (SC 1.4.11); a ground or decoration owes nothing. -/
@[expose] public def required : Ir.Need → Nat
  | .text => aaText
  | .largeText => aaLargeText
  | .nonText => aaNonText
  | .state => aaNonText
  | .decorative => 0

/-- Every need's ratio is at most the text one: a pair that clears 4.5:1
clears whatever its need asks. -/
public theorem required_le_aaText (n : Ir.Need) : required n ≤ aaText := by
  cases n <;> decide

/-- SC 1.4.6 (AAA), normal text: 7:1. -/
public def aaaText : Nat := 7000
/-- SC 1.4.6 (AAA), large-scale text: 4.5:1. -/
public def aaaLargeText : Nat := 4500
/-- Non-text information where the reader asks more contrast: 4.5:1, an
engine choice — WCAG 2.2 sets no enhanced level for SC 1.4.11, and this
holds an edge to the enhanced large-text ratio beside it. -/
public def moreNonText : Nat := 4500

/-- The ratio a need owes in a scheme: `required`'s in print and the plain
screens, and where the reader asks more contrast (`Scheme.more`) SC 1.4.6's
7:1 for text and 4.5:1 for large-scale text, with non-text information and
a state change at `moreNonText`. -/
@[expose] public def requiredIn (s : Ir.Scheme) (n : Ir.Need) : Nat :=
  if s.more then
    match n with
    | .text => aaaText
    | .largeText => aaaLargeText
    | .nonText => moreNonText
    | .state => moreNonText
    | .decorative => 0
  else required n

/-- A scheme that asks no more contrast owes what `required` owes. -/
public theorem requiredIn_plain (s : Ir.Scheme) (h : s.more = false) (n : Ir.Need) :
    requiredIn s n = required n := by
  simp [requiredIn, h]

/-- **A more scheme never owes less** (`_monotone`): each need's ratio there
is at least its plain one. -/
public theorem requiredIn_monotone (s : Ir.Scheme) (n : Ir.Need) : required n ≤ requiredIn s n := by
  unfold requiredIn
  cases s.more <;> cases n <;> decide

/-- A pair that clears the normal-text requirement also clears the
large-scale text requirement. Consumers need this ordering, not the
implementation of either threshold. -/
public theorem aaLargeText_le_aaText : aaLargeText ≤ aaText := by
  decide

/-- WCAG 2.2's large-scale text boundary, in the same point units as layout.
The document planner and placed-glyph judge share this decision. -/
public def largeText (size : Dim.Sp) (bold : Bool) : Bool :=
  size ≥ Dim.pt 18 || (bold && size ≥ Dim.pt 14)

public def textRequired (size : Dim.Sp) (bold : Bool) : Nat :=
  if largeText size bold then aaLargeText else aaText

end LeanTex.Core.Contrast
