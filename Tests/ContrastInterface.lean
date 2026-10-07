module

import LeanTex.Core.Contrast
import LeanTex.Core.Check
import LeanTex.Core.SeedPalette

/-! Ordinary consumers can judge shipped ink and use certified generated
palettes without accessing the colour solver's search or traversal state. -/

open LeanTex.Core
open Ir

namespace Tests.ContrastInterface

example : Doc → ColorPair := Contrast.effectivePair
example : Doc → Array Diag := Contrast.docDiags
example : Layout.Geom → Font.FontSet → Layout.Out → Bool → Check.Shipped :=
  Check.Shipped.ofOut
example : Check.Shipped → Array Assertion → Array Diag := Check.all
example : (s : SeedPalette.Seeds) → Option (SeedPalette.Generated s) := SeedPalette.generate

example (doc : Doc) :
    (Contrast.effectivePair doc).fg = (Design.ofDoc doc).fg ∧
    ((Design.ofDoc doc).bgDeclared = true →
      (Contrast.effectivePair doc).bg = (Design.ofDoc doc).bg) :=
  Contrast.judged_pair_is_shipped doc

example (geom : Layout.Geom) (fs : Font.FontSet) (out : Layout.Out)
    (paint : Contrast.RunPaint) (h : Contrast.PaintOccurs out paint) :
    Contrast.judgePaint (Contrast.shippedGrounds geom out) fs out paint ∈
      Contrast.shippedJudgments geom fs out :=
  Contrast.contrast_judged_complete geom fs out paint h

example (s : SeedPalette.Seeds) (p : SeedPalette.Generated s)
    (ink ground : Color) (req : Nat) (h : (ink, ground, req) ∈ SeedPalette.pairs s p.colors) :
    req ≤ Contrast.contrastMilli ink ground :=
  SeedPalette.generated_contract p h

example : True := by
  fail_if_success have := Contrast.realizeCand
  fail_if_success have := Contrast.realizeBisect
  fail_if_success have := Contrast.nearestWeight
  fail_if_success have := Contrast.UseCx
  fail_if_success have := Contrast.UseAcc
  fail_if_success have := Contrast.Judged
  fail_if_success have := Contrast.effectivePairJudged
  fail_if_success have := Contrast.realizePlan
  fail_if_success have := Contrast.textOnly
  fail_if_success have := Check.worstOvershoot
  fail_if_success have := Check.failure
  fail_if_success have := SeedPalette.candidate
  trivial

end Tests.ContrastInterface
