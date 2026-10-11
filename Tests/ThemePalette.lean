module

import LeanTex.Core.SeedPalette

open LeanTex.Core

namespace Tests.ThemePalette

private def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

-- Ordinary module clients can use the contract without importing a
-- renderer's implementation or reducing a sampled generated palette.
example {s : SeedPalette.Seeds} {t : SeedPalette.Targets} (p : SeedPalette.Generated s t) :
    ∀ x ∈ SeedPalette.sites s t p.colors, x.2.2.2 ≤ Contrast.contrastMilli x.2.1 x.2.2.1 :=
  (SeedPalette.generated_sites_contract p).1

example {s : SeedPalette.Seeds} {t : SeedPalette.Targets} (p : SeedPalette.Generated s t)
    (b : SeedPalette.Blocks) :
    ∀ x ∈ SeedPalette.blockPairs s t p.colors b, t.text ≤ Contrast.contrastMilli x.1 x.2 :=
  (SeedPalette.generated_sites_contract p).2 b

example (s : SeedPalette.Seeds) (c : SeedPalette.Colors) :
    SeedPalette.Colors.role s c .accent = some s.accent :=
  (SeedPalette.generate_seeds_exact s c).2.2

private def hex (r g b : UInt8) : Ir.Color := { r, g, b }

/-- Invented seeds in both polarities. The contract breaks a palette whose
text equals its ground, whose essential edge equals a ground it stands on,
or whose band stands no farther from the page than its body; the export
keeps each named role at its generated colour. -/
public def checks (ref : IO.Ref (List String)) : IO Unit := do
  let dark := hex 25 42 61
  let accent := hex 196 106 119
  for (ink, paper) in [(dark, Ir.Color.white), (Ir.Color.white, dark)] do
    let seeds : SeedPalette.Seeds := { ink, paper, accent }
    let t := seeds.targets .decks
    let .ok palette := SeedPalette.generate seeds t
      | check ref "theme palette generates both polarities" false
    let colors := palette.colors
    check ref "theme palette rejects text equal to its ground"
      (!SeedPalette.contract seeds t { colors with muted := colors.surface } &&
        !SeedPalette.contract seeds t { colors with accentText := seeds.paper })
    check ref "theme palette rejects essential edges equal to any checked ground"
      ([seeds.paper, colors.surface, colors.accentSoft].all fun ground =>
        !SeedPalette.contract seeds t { colors with accentEdge := ground })
    check ref "theme palette rejects a band too near its body"
      (!SeedPalette.contract seeds t { colors with surfaceStrong := colors.surface })
    let st : SeedPalette.SeedState := { seeds, targets := t, blocks := .tonal, colors }
    let declarations := SeedPalette.declarations "sample" st
    let blocks := SeedPalette.beamerDeclarations "sample" st
    check ref "plain palette export does not require Beamer"
      (!declarations.contains "\\setbeamercolor")
    check ref "beamer export keeps every plain declaration"
      (blocks.startsWith declarations)
    check ref "beamer export binds the six block elements"
      (["block title", "block title alerted", "block title example", "block body",
        "block body alerted", "block body example"].all fun e =>
          (blocks.splitOn ("\\setbeamercolor{" ++ e ++ "}{")).length == 2)
    for r in Ir.Role.all do
      if let (some name, some color) := (r.row.exportName, SeedPalette.Colors.role seeds colors r) then
        check ref s!"theme palette exports {name}'s generated RGB"
          (declarations.contains ("\\definecolor{sample" ++ name ++ "}{HTML}{" ++
            Ir.Color.hexByte color.r ++ Ir.Color.hexByte color.g ++
            Ir.Color.hexByte color.b ++ "}"))

end Tests.ThemePalette
