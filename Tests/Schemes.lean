module

public import Tests.Support
public import LeanTex.Core.ContrastSolve

public section

open LeanTex.Core

namespace Tests.Schemes

/-- ΔEOK between two colours, thousandths. -/
private def deltaEMilli (a b : Ir.Color) : Nat :=
  (Nat.sqrt (ContrastSolve.deltaEOkSq a b).toNat) / 10 ^ 15

/-- **The dark screen is the class's seeds carried to a dark page**: the
undeclared document's dark colours — page, ink, muted ink, rule, accent and
code ground — are what the class's default seeds generate there
(`SeedPalette.classSeedsIn`), each within ΔEOK 0.03 of the constants the
stylesheet shipped before (a zinc-900 page and zinc-400 muted ink,
stone-50 ink, a zinc-700 rule, a blue-400 accent and a zinc-800 code
ground, Tailwind v4's), so deleting them moved no colour visibly. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let web : Ir.Palette := { classColors := { row := .web, depth := .documents } }
  let former : List (Ir.Role × Ir.Color) :=
    [(.page, { r := 0x18, g := 0x18, b := 0x1B }), (.ink, { r := 0xFA, g := 0xFA, b := 0xF9 }),
     (.muted, { r := 0xA1, g := 0xA1, b := 0xAA }), (.rule, { r := 0x3F, g := 0x3F, b := 0x46 }),
     (.accent, { r := 0x60, g := 0xA5, b := 0xFA }),
     (.codeSurface, { r := 0x27, g := 0x27, b := 0x2A })]
  for (r, c) in former do
    match Ir.Design.at web .dark r with
    | some d =>
      t s!"the dark {(Ir.ColorRef.role r).key} {d.css} stands within ΔEOK 0.03 of the former {c.css}"
        (deltaEMilli d c ≤ 30)
    | none => t s!"the dark {(Ir.ColorRef.role r).key} resolves" false

end Tests.Schemes
