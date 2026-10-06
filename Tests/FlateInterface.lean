module

import LeanTex.Core.Flate.BitPacking
import LeanTex.Core.Flate.Progress
import LeanTex.Core.Flate.RoundtripProof

namespace Tests.FlateInterface

-- The proof module re-exports the codec API named by its two contracts.
example (raw : ByteArray) :
    LeanTex.Core.Flate.inflate (LeanTex.Core.Flate.deflate raw) raw.size = .ok raw :=
  LeanTex.Core.Flate.inflate_deflate_id raw

example (raw : ByteArray) (capacity : Nat) (h : raw.size ≤ capacity) :
    LeanTex.Core.Flate.inflate (LeanTex.Core.Flate.deflate raw) capacity = .ok raw :=
  LeanTex.Core.Flate.inflate_deflate_bounded_id raw capacity h

-- Image's proof uses these exported equations with an ordinary import.
example (raw : ByteArray) (height rowBytes bpp : Nat) :
    (LeanTex.Core.Flate.unfilterAll raw height rowBytes bpp).size = height * rowBytes := by
  rw [LeanTex.Core.Flate.unfilterAll, LeanTex.Core.Flate.size_build]

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
  fail_if_success have := LeanTex.Core.Flate.tokenize
  fail_if_success have := LeanTex.Core.Flate.deflate_header_exact
  fail_if_success have := LeanTex.Core.Flate.BlockStream.readStep
  fail_if_success have := LeanTex.Core.Flate.Bw
  fail_if_success have := LeanTex.Core.Flate.getElem?_push
  fail_if_success have := LeanTex.Core.Flate.matchToken
  trivial

end Tests.FlateInterface
