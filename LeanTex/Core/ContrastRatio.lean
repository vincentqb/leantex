module

public import LeanTex.Core.Color
public import LeanTex.Core.Dim
public import LeanTex.Core.DesignRole
import LeanTex.Core.Oklab

/-! The WCAG 2.2 [WCAG22] contrast arithmetic (relative luminance, contrast ratio, SC 1.4.3, SC 1.4.11)
shared by painting defaults and the document contrast judge. -/
namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir
open LeanTex.Core.Oklab (channelLinear)

/-- WCAG relative luminance in units of 10⁻⁷: 0.2126·R + 0.7152·G + 0.0722·B over the linearised
channels. -/
public def luminance (c : Color) : Nat :=
  (2126 * (channelLinear.getD c.r.toNat 0)
    + 7152 * (channelLinear.getD c.g.toNat 0)
    + 722 * (channelLinear.getD c.b.toNat 0)) / 10000

/-- WCAG contrast ratio ×1000, (L₁ + 0.05)/(L₂ + 0.05) with the lighter on top, truncated. -/
public def contrastMilli (a b : Color) : Nat :=
  let la := luminance a
  let lb := luminance b
  ((max la lb + 500000) * 1000) / (min la lb + 500000)

/-- An arithmetic assessment before a caller's exemption policy, in `contrastMilli`'s units. -/
public structure PairAssessment where
  ratio : Nat
  required : Nat
  deriving Repr, BEq

public def PairAssessment.passes (a : PairAssessment) : Bool :=
  decide (a.required ≤ a.ratio)

/-- The integer contrast comparison the use judge and the placed-run audit share. -/
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

/-- Whether a covered form keeps the covered-state contract on its ground: quieter there than the
active colour, and `floor`, 3:1 unless asked more, from it (SC 1.4.11). -/
@[expose] public def coverHolds (ground active covered : Color) (floor : Nat := aaNonText) : Bool :=
  decide (contrastMilli covered ground < contrastMilli active ground) &&
    decide (floor ≤ contrastMilli active covered)

/-- The ratio a role's need owes, in `contrastMilli`'s units. -/
@[expose] public def required : Ir.Need → Nat
  | .text => aaText
  | .largeText => aaLargeText
  | .nonText => aaNonText
  | .state => aaNonText
  | .decorative => 0

/-- **A medium's text floor is what the judge asks of its text**: the
ratio text owes at the medium's size (`Need.atStage`). -/
public theorem depth_text_exact (d : GroundDepth) :
    d.text = required (Need.text.atStage d.stage) := by
  cases d with
  | mk _ _ _ _ stage => cases stage <;> rfl

/-- SC 1.4.6 (AAA), normal text: 7:1. -/
public def aaaText : Nat := 7000
/-- SC 1.4.6 (AAA), large-scale text: 4.5:1. -/
public def aaaLargeText : Nat := 4500
/-- Non-text information where the reader asks more contrast: 4.5:1, an engine choice. -/
public def moreNonText : Nat := 4500

/-- The ratio a need owes in a scheme: `required`'s, or SC 1.4.6's where the reader asks more. -/
@[expose] public def requiredIn (s : Ir.Scheme) (n : Ir.Need) : Nat :=
  if s.more then
    match n with
    | .text => aaaText
    | .largeText => aaaLargeText
    | .nonText => moreNonText
    | .state => moreNonText
    | .decorative => 0
  else required n

public theorem requiredIn_monotone (s : Ir.Scheme) (n : Ir.Need) : required n ≤ requiredIn s n := by
  unfold requiredIn
  cases s.more <;> cases n <;> decide

public theorem aaLargeText_le_aaText : aaLargeText ≤ aaText := by
  decide

/-- WCAG 2.2's large-scale text boundary (≥ 18pt, or ≥ 14pt bold), in CSS's points. -/
public def largeText (size : Dim.Length) (bold : Bool) : Bool :=
  size ≥ Dim.bp 18 || (bold && size ≥ Dim.bp 14)

public def textRequired (size : Dim.Length) (bold : Bool) : Nat :=
  if largeText size bold then aaLargeText else aaText

end LeanTex.Core.Contrast
