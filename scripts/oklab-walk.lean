/-
The Oklab round-trip walk over all 2²⁴ sRGB inputs, spawned by scripts/oklab-roundtrip.lean:
`cover 100 bg c` must return `c` exactly.
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
