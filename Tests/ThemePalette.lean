module

import LeanTex.Core.SeedPalette

open LeanTex.Core

namespace Tests.ThemePalette

private def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

-- Ordinary module clients can use the contract without importing a
-- renderer's implementation or reducing a sampled generated palette.
example {s : SeedPalette.Seeds} (p : SeedPalette.Generated s) :
    Contrast.aaText ≤ Contrast.contrastMilli p.colors.muted p.colors.surface :=
  SeedPalette.generated_role_contract p (foreground := .muted) (ground := .surface)
    (by simp [SeedPalette.requirements])

example {s : SeedPalette.Seeds} (p : SeedPalette.Generated s) :
    Contrast.aaText ≤ Contrast.contrastMilli p.colors.muted s.paper :=
  SeedPalette.generated_role_contract p (foreground := .muted) (ground := .paper)
    (by simp [SeedPalette.requirements])

example {s : SeedPalette.Seeds} (p : SeedPalette.Generated s) :
    Contrast.aaText ≤ Contrast.contrastMilli p.colors.accentText p.colors.surface :=
  SeedPalette.generated_beamer_contract p (element := "block title alerted")
    (foreground := .accentText) (ground := .surface) (by simp [SeedPalette.beamerBlocks])

/-- Invented seeds in both polarities. The panel witness breaks a palette
that checks text only against the page; the export keeps each named role. -/
public def checks (ref : IO.Ref (List String)) : IO Unit := do
  check ref "theme palette exports every role once"
    (SeedPalette.Role.all.length == 10 &&
      (SeedPalette.Role.all.map (·.name)).eraseDups.length == 10)
  let dark : Ir.Color := { r := 25, g := 42, b := 61 }
  let accent : Ir.Color := { r := 196, g := 106, b := 119 }
  let mut panelWitness := false
  for (ink, paper) in [(dark, Ir.Color.white), (Ir.Color.white, dark)] do
    let seeds : SeedPalette.Seeds := ⟨ink, paper, accent⟩
    let some palette := SeedPalette.generate seeds
      | check ref "theme palette generates both polarities" false
        continue
    let colors := palette.colors
    check ref "theme palette rejects text equal to its ground"
      (!SeedPalette.contract seeds { colors with muted := colors.surface } &&
        !SeedPalette.contract seeds { colors with accentText := seeds.paper })
    if let some paperOnly := SeedPalette.tint Contrast.aaText ink paper paper then
      if Contrast.contrastMilli paperOnly colors.surface < Contrast.aaText then
        panelWitness := true
        check ref "theme palette rejects text passing paper but failing its panel"
          (Contrast.contrastMilli paperOnly paper ≥ Contrast.aaText &&
            !SeedPalette.contract seeds { colors with muted := paperOnly })
    let declarations := SeedPalette.declarations "sample" seeds palette
    let blocks := SeedPalette.beamerDeclarations "sample" seeds palette
    check ref "plain palette export does not require Beamer"
      (!declarations.contains "\\setbeamercolor")
    check ref "filled block export preserves all existing RGB declarations"
      (blocks.startsWith declarations && (blocks.splitOn "\\definecolor{").length == 11)
    let expected := [
      ("block title", "Ink"), ("block title alerted", "AccentText"),
      ("block title example", "Muted"), ("block body", "Ink"),
      ("block body alerted", "Ink"), ("block body example", "Ink")]
    check ref "filled block export binds exactly six elements"
      ((blocks.splitOn "\\setbeamercolor{").length == 7)
    for (element, foreground) in expected do
      check ref s!"filled {element} declares both checked channels"
        ((blocks.splitOn ("\\setbeamercolor{" ++ element ++ "}{fg=sample" ++ foreground ++
          ",bg=sampleSurface}\n")).length == 2)
    for role in SeedPalette.Role.all do
      let color := role.color seeds colors
      check ref s!"theme palette exports {role.name}'s checked RGB"
        (declarations.contains ("\\definecolor{sample" ++ role.name ++ "}{HTML}{" ++
          Ir.Color.hexByte color.r ++ Ir.Color.hexByte color.g ++
          Ir.Color.hexByte color.b ++ "}"))
  check ref "theme palette has a witness requiring both paper and panel" panelWitness

end Tests.ThemePalette
