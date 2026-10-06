module

import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.Progress

namespace Tests.FlateInterface

example (hi lo n : Nat) (hn : n < 64)
    (hlo : lo < 2 ^ n) (hhi : hi < 2 ^ (64 - n)) :
    ((hi.toUInt64 <<< n.toUInt64) ||| lo.toUInt64).toNat = hi * 2 ^ n + lo :=
  LeanTex.Core.Flate.BitPacking.packBits_exact hi lo n hn hlo hhi

example {σ : Type} (P : Nat → σ → Prop)
    (step : Nat → σ → Id (ForInStep σ)) (n : Nat) (init : σ)
    (hinit : P 0 init)
    (hstep : ∀ i, 0 ≤ i → i < n → ∀ s, P i s →
      match (step i s).run with
      | .done s' => P n s'
      | .yield s' => P (i + 1) s') :
    P n (forIn [0:n] init step : Id σ).run :=
  LeanTex.Core.Flate.Progress.forIn_range_exact P (P n) step 0 n init
    (Nat.zero_le _) hinit hstep (fun _ h => h)

-- A normal import must not make this implementation lemma nameable.
example : True := by
  fail_if_success have := LeanTex.Core.Flate.BitPacking.maskBits_exact
  trivial

end Tests.FlateInterface
