import LeanTex.Core.Contrast

namespace LeanTex.Core.SeedPalette

open Ir

structure Seeds where
  ink : Color
  paper : Color
  accent : Color
  deriving Repr, BEq

structure Colors where
  muted : Color
  mutedOnDark : Color
  diagramMuted : Color
  surface : Color
  accentText : Color
  accentOnDark : Color
  accentSoft : Color
  deriving Repr, BEq

/-- A decorative wash's contrast, not an accessibility threshold. One design
token controls both neutral panels and accent tracks. -/
def washRatio : Nat := 1150

/-- Each pair names the surface it actually shares. Text and essential
edges must work on the panel as well as on the page (WCAG 2.2, 1.4.3/1.4.11).
Decorative fills carry no text or essential information of their own. -/
def pairs (s : Seeds) (c : Colors) : List (Color × Color × Nat) :=
  [(s.ink, s.paper, Contrast.aaText),
   (s.ink, c.surface, Contrast.aaText),
   (c.muted, s.paper, Contrast.aaText),
   (c.muted, c.surface, Contrast.aaText),
   (c.mutedOnDark, s.ink, Contrast.aaText),
   (c.accentText, s.paper, Contrast.aaText),
   (c.accentText, c.surface, Contrast.aaText),
   (c.accentOnDark, s.ink, Contrast.aaText),
   (c.diagramMuted, s.paper, Contrast.aaNonText),
   (c.diagramMuted, c.surface, Contrast.aaNonText),
   (s.accent, s.paper, Contrast.aaNonText),
   (s.accent, c.surface, Contrast.aaNonText),
   (s.accent, c.accentSoft, Contrast.aaNonText)]

def contract (s : Seeds) (c : Colors) : Bool :=
  (pairs s c).all fun (ink, ground, req) =>
    decide (req ≤ Contrast.contrastMilli ink ground)

/-- A generated palette carries the contract, never a best-effort colour
substituted for an unsatisfied role. The seeds are parameters, not outputs
the generator is free to change. -/
structure Generated (s : Seeds) where
  colors : Colors
  valid : contract s colors = true

theorem generated_contract {s : Seeds} (p : Generated s)
    {ink ground : Color} {req : Nat} (h : (ink, ground, req) ∈ pairs s p.colors) :
    req ≤ Contrast.contrastMilli ink ground := by
  have hv := List.all_eq_true.mp p.valid _ h
  exact of_decide_eq_true hv

/-- Select from the seed-to-ground Oklab segment, at the existing cover
API's percentage resolution. Search from the ground: the quietest passing
weight wins. This is palette authoring, not a repair of authored colours. -/
def tint (req : Nat) (seed ground under : Color) : Option Color :=
  ((List.range 101).find? fun q =>
    let c := Oklab.cover q ground seed
    decide (req ≤ Contrast.contrastMilli c ground) &&
      decide (req ≤ Contrast.contrastMilli c under)).map fun q =>
        Oklab.cover q ground seed

theorem tint_mem {req : Nat} {seed ground under c : Color}
    (h : tint req seed ground under = some c) :
    ∃ q, q ≤ 100 ∧ c = Oklab.cover q ground seed := by
  obtain ⟨q, hq, hc⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hq
  have : q < 101 := List.mem_range.mp hm
  exact ⟨q, by omega, hc.symm⟩

private def candidate (s : Seeds) : Option Colors := do
  let surface ← tint washRatio s.ink s.paper s.paper
  let accentSoft ← tint washRatio s.accent s.paper s.paper
  let muted ← tint Contrast.aaText s.ink s.paper surface
  let mutedOnDark ← tint Contrast.aaText s.paper s.ink s.ink
  let diagramMuted ← tint Contrast.aaNonText s.ink s.paper surface
  let accentText ← Contrast.realizeNearest Contrast.aaText surface s.accent
  let accentOnDark ← Contrast.realizeNearest Contrast.aaText s.ink s.accent
  return { muted, mutedOnDark, diagramMuted, surface, accentText, accentOnDark, accentSoft }

/-- Opt-in seed authoring: retain the RGB seeds, derive restrained neutrals
from their segment, and reuse the contrast solver for accent text. CMYK is
refused because this sRGB operation cannot preserve its print components.
Material's role/ground model and Radix's text/edge/surface separation motivate
the roles; neither system's fixed colour scale is copied here. -/
def generate (s : Seeds) : Option (Generated s) := do
  if s.ink.cmyk.isSome || s.paper.cmyk.isSome || s.accent.cmyk.isSome then none
  else
    let c ← candidate s
    if h : contract s c = true then some ⟨c, h⟩ else none

/-- The ordinary xcolor declarations both front ends already understand.
There is no generator or colour solver to run when compiling the exported
document. Prefix validation belongs to the authoring tool. -/
def declarations (stem : String) (s : Seeds) (p : Generated s) : String :=
  let c := p.colors
  String.join (([("Ink", s.ink), ("Paper", s.paper), ("Accent", s.accent),
    ("Muted", c.muted), ("MutedOnDark", c.mutedOnDark),
    ("DiagramMuted", c.diagramMuted), ("Surface", c.surface),
    ("AccentText", c.accentText), ("AccentOnDark", c.accentOnDark),
    ("AccentSoft", c.accentSoft)] : List (String × Color)).map fun (role, ink) =>
      "\\definecolor{" ++ stem ++ role ++ "}{HTML}{" ++
        Color.hexByte ink.r ++ Color.hexByte ink.g ++ Color.hexByte ink.b ++ "}\n")

end LeanTex.Core.SeedPalette
