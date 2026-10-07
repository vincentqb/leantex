module

import LeanTex.Core.Oklab
import LeanTex.Core.ContrastRatio
import LeanTex.Core.Listing

/-! Ordinary callers read the colour model and its contracts. Internal
search state and inverse coordinates at a different scale stay private. -/

open LeanTex.Core
open Ir

namespace Tests.ColourInterface

example : Color → Oklab.Lab := Oklab.labOf
example : Oklab.Lab → Color := Oklab.toColorOfLab
example : Nat → Color → Color → Color := Oklab.cover
example : Design → Cover := Design.cover
example : Color → Color → Nat := Contrast.contrastMilli
example : Palette → Option Color → ListingStyle → Bool :=
  fun pal ground style => Listing.contract pal ground (style := style)

example (n : Nat) (h : n ≤ 10^18) :
    (Oklab.icbrt n)^3 ≤ n ∧ n < (Oklab.icbrt n + 1)^3 :=
  Oklab.icbrt_spec n h

example (f : Nat) (c s : Oklab.Lab) :
    (Oklab.labMix f c s).L = 100 * s.L + (f : Int) * (c.L - s.L) :=
  Oklab.labMix_L f c s

example (pal : Palette) (ground covered : Option Color)
    (t : ListingHighlight.Token) (style : ListingStyle) :
    plainTextOne (Listing.tokenInline pal ground covered t style) = t.text :=
  Listing.token_inline_source_exact pal ground covered t style

example : True := by
  fail_if_success have := Oklab.icbrtGo
  fail_if_success have := Oklab.icbrtGo_spec
  fail_if_success have := Oklab.nearestGo
  fail_if_success have := Oklab.nearestChannel
  fail_if_success have := Oklab.toColor
  fail_if_success have := Listing.fontStyle
  trivial

end Tests.ColourInterface
