/-
The Oklab round-trip walk itself — spawned by scripts/oklab-roundtrip.lean
on a cache miss, never run directly. The split keeps the cache-hit path
free of the LeanTex import (~1 s of olean loading the verdict lookup does
not need). Exhaustive over all 2²⁴ sRGB inputs: `cover 100 bg c` — the
shipped cover function at a fraction of 100%, i.e. sRGB → Oklab → sRGB
with the mix a no-op — must return `c` exactly. This is what makes the
nearest-entry inversion in `Oklab.toColor` an identity rather than an
approximation. An executable oracle, not a theorem (16.7M cube roots
exceed any sane kernel budget).
-/
import LeanTex

open LeanTex.Core.Ir LeanTex.Core.Oklab

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let cov := cover 100 Color.white
  let mut bad := 0
  let mut firstBad : Option (Nat × Nat × Nat) := none
  for r in [0:256] do
    for g in [0:256] do
      for b in [0:256] do
        let c : Color := { r := UInt8.ofNat r, g := UInt8.ofNat g, b := UInt8.ofNat b }
        if cov c != c then
          bad := bad + 1
          if firstBad.isNone then firstBad := some (r, g, b)
  let t1 ← IO.monoMsNow
  IO.println s!"checked 16777216 colours in {t1 - t0} ms: {bad} mismatches"
  if let some (r, g, b) := firstBad then
    IO.println s!"first mismatch at ({r}, {g}, {b})"
  if bad != 0 then
    IO.Process.exit 1
