module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-! A light palette's colours stand at their medium's floor on the paper and no darker: a seed
meeting it ships as itself, and each derived tone is its family's lightest that meets it. -/

namespace Tests.PaletteFloor

/-- How far above its floor a derived tone may stand on the paper: 0.15 of a ratio, two 8-bit
steps of a mid-lightness tone. -/
def floorSlack : Nat := 150

/-- Invented seeds on light papers, the last an orange meeting a deck's floor on white as given. -/
def seeds : List (String × SeedPalette.Seeds) := [
  ("a black ink and a yellow accent",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xFA 0xCC 0x15 }),
  ("a violet ink and an orange accent",
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }),
  ("a warm ink on cream and a teal accent",
    { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
      accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }),
  ("a neutral ink and a magenta accent",
    { ink := Ir.Color.ofHtml 0x1A 0x1A 0x1A, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xC0 0x26 0xD3 }),
  ("an orange meeting a deck's floor",
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xF0 0x6E 0x00 })]

/-- Every colour a light palette generates stands at its floor on the paper, at either depth: the
seed where it meets the floor, else within `floorSlack` of it, a container accent setting no text. -/
def floorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (depth, d, text) in [("a deck", Ir.GroundDepth.decks, 3000),
      ("a document", Ir.GroundDepth.documents, 4500)] do
    for (label, s) in seeds do
      match SeedPalette.generate s (s.targets d) with
      | .error f => t s!"floor, {depth}, {label}: generates, not fail at {reprStr f.role}" false
      | .ok g =>
        let c := g.colors
        let at_ (floor : Nat) (seed : Option Ir.Color) (x : Ir.Color) : Bool :=
          let r := Contrast.contrastMilli x s.paper
          seed.any (· == x) && floor ≤ Contrast.contrastMilli x s.paper ||
            decide (floor ≤ r ∧ r < floor + floorSlack)
        let seedAt (floor : Nat) : Option Ir.Color :=
          if floor ≤ Contrast.contrastMilli s.accent s.paper then some s.accent else none
        if s.container (s.targets d) then
          t s!"floor, {depth}, {label}: the accent serves as a container, marking the alert"
            (c.alertMark == some s.accent && c.alert == s.ink)
        else
          t s!"floor, {depth}, {label}: the accent's text tone stands at the text floor on the paper"
            (at_ text (seedAt text) c.accentText && (seedAt text).all (· == c.accentText))
          t s!"floor, {depth}, {label}: the alert is the accent's text tone" (c.alert == c.accentText)
          t s!"floor, {depth}, {label}: the accent's edge stands at the marks' floor on the paper"
            (at_ 3000 (seedAt 3000) c.accentEdge && (seedAt 3000).all (· == c.accentEdge))
        t s!"floor, {depth}, {label}: the muted ink stands at the text floor on the paper"
          (at_ text none c.muted)
        t s!"floor, {depth}, {label}: the diagram's muted tone stands at the marks' floor"
          (at_ 3000 none c.diagramMuted)

end Tests.PaletteFloor
