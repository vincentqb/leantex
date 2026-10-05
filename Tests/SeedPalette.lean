import Tests.Support
import LeanTex.Core.SeedPalette

open LeanTex.Core

/-- Invented seed families, both polarities. The export is exercised through
the real elaborator and both shipped representations, not an IR dump. -/
def seedPaletteChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let inks : List Ir.Color :=
    [{ r := 25, g := 42, b := 61 }, { r := 43, g := 31, b := 53 },
     { r := 32, g := 49, b := 39 }]
  let accents : List Ir.Color :=
    [{ r := 196, g := 106, b := 119 }, { r := 32, g := 147, b := 151 },
     { r := 150, g := 120, b := 190 }]
  for ink in inks do
    for accent in accents do
      for dark in [false, true] do
        let seeds : SeedPalette.Seeds :=
          if dark then ⟨Ir.Color.white, ink, accent⟩ else ⟨ink, Ir.Color.white, accent⟩
        let name := s!"seed palette {reprStr seeds}"
        match SeedPalette.generate seeds with
        | none => t (name ++ " derives all roles") false
        | some palette =>
          t (name ++ " meets every role/ground contract")
            (SeedPalette.contract seeds palette.colors)
          let c := palette.colors
          t (name ++ " separates panel, edge and text in contrast order")
            (Contrast.contrastMilli c.surface seeds.paper <
                Contrast.contrastMilli c.diagramMuted seeds.paper &&
              Contrast.contrastMilli c.diagramMuted seeds.paper <
                Contrast.contrastMilli c.muted seeds.paper &&
              Contrast.contrastMilli c.muted seeds.paper <
                Contrast.contrastMilli seeds.ink seeds.paper)
          let pre := SeedPalette.declarations "sample" seeds palette
          let build (ground role : String) :=
            elabStr ("\\documentclass{article}" ++ pre ++
              "\\palette{bg=" ++ ground ++ ", fg=" ++ role ++ "}" ++
              "\\begin{document}\\textcolor{" ++ role ++ "}{Witness}\\end{document}")
          for (ground, role, color) in [
              ("samplePaper", "sampleMuted", c.muted),
              ("sampleSurface", "sampleMuted", c.muted),
              ("samplePaper", "sampleAccentText", c.accentText),
              ("sampleInk", "sampleMutedOnDark", c.mutedOnDark),
              ("sampleInk", "sampleAccentOnDark", c.accentOnDark)] do
            let (doc, ds) := build ground role
            t (name ++ " exports clean TeX declarations")
              (ds.all (·.severity == .note))
            let out := layoutOf fonts doc
            t (name ++ s!" {ground}/{role} paints PDF glyphs")
              ((allLines out).any fun line => lineText line == "Witness" &&
                line.segs.any fun seg => match seg with
                  | .run _ value _ _ _ _ _ _ _ _ _ => value == color
                  | _ => false)
            let (_, nodes, _) := HtmlDoc.emitTree {} doc
            t (name ++ s!" {ground}/{role} paints typed HTML")
              ((elemStylesList #[] nodes.toList).any fun (text, style) =>
                text == "Witness" &&
                  style == s!"color: var(--{role}, {color.css})")
  for seeds in [
      (⟨Ir.Color.white, Ir.Color.white, Ir.Color.black⟩ : SeedPalette.Seeds),
      (⟨Ir.Color.black, Ir.Color.white, Ir.Color.white⟩ : SeedPalette.Seeds),
      (⟨Ir.Color.black, Ir.Color.white, { r := 140, g := 140, b := 140 }⟩ :
        SeedPalette.Seeds),
      (⟨Ir.Color.white, { r := 32, g := 49, b := 39 },
        { r := 150, g := 111, b := 190 }⟩ : SeedPalette.Seeds),
      (⟨{ Ir.Color.black with cmyk := some (0, 0, 0, 1000) },
        Ir.Color.white, { r := 196, g := 106, b := 119 }⟩ :
        SeedPalette.Seeds)] do
    t "seed palette refuses unsatisfied seed contracts"
      (SeedPalette.generate seeds |>.isNone)
