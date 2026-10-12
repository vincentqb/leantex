module

public import Tests.Support
public import LeanTex.Core.ContrastSolve

public section

open LeanTex.Core

namespace Tests.ColourSolve


/-- Gamut mapping holds a colour's lightness and hue and loses only chroma;
the solver that derives a legible tone holds the hue it was given. Before,
a per-channel clip of an out-of-gamut candidate turned an orange about 15°
toward red. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- An oklch(0.70 0.30 150°) green is outside sRGB: it maps to a fitting
  -- value at its own lightness and direction, with less chroma.
  let green := Oklab.ofLch (7 * 10 ^ 17) (3 * 10 ^ 17) 150000
  let o : Oklab.Okl := { L := green.L, a := green.a, b := green.b, f := Oklab.fracOne }
  t "gamut map: the green is outside sRGB" (!o.inGamut)
  let m := o.gamutMap
  t "gamut map: lightness and direction held, chroma reduced"
    (m.L == o.L && m.a == o.a && m.b == o.b && m.f < o.f)
  t "gamut map: the mapped green fits" m.fits
  t "gamut map: the shipped green keeps its hue within a degree"
    (hueGap (hueOf m.toColor) 150000 ≤ 1000)
  let inside : Oklab.Okl := { o with f := Oklab.fracOne / 8 }
  t "gamut map: an in-gamut value is its own map" (inside.inGamut && inside.gamutMap == inside)
  -- The warm turn: none outside 40°–120°, the full 20° at 80° and full depth.
  t "turn: none at 30°" (Oklab.Okl.turn 30000 Oklab.fracOne == 0)
  t "turn: none at 130°" (Oklab.Okl.turn 130000 Oklab.fracOne == 0)
  t "turn: 20° at 80° and full depth" (Oklab.Okl.turn 80000 Oklab.fracOne == 20000)
  t "turn: half at half depth" (Oklab.Okl.turn 80000 (Oklab.fracOne / 2) == 10000)
  -- A bright orange is no text colour on white: its legible tone is darker
  -- at its own hue.
  let orange : Ir.Color := { r := 0xF0, g := 0x8C, b := 0x14 }
  match ContrastSolve.realizeNearest Contrast.aaText Ir.Color.white orange with
  | none => t "realize: the orange has a legible tone on white" false
  | some c =>
    t "realize: the tone reads on white" (Contrast.aaText ≤ Contrast.contrastMilli c Ir.Color.white)
    t s!"realize: the tone keeps the orange's hue (gap {hueGap (hueOf c) (hueOf orange)} m°)"
      (hueGap (hueOf c) (hueOf orange) ≤ 1500)

end Tests.ColourSolve
