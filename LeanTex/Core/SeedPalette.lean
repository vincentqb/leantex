module

public import LeanTex.Core.Ir
public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Oklab
import LeanTex.Core.Contrast

namespace LeanTex.Core.SeedPalette

open Ir

public structure Seeds where
  ink : Color
  paper : Color
  accent : Color
  deriving Repr, BEq

public structure Colors where
  muted : Color
  mutedOnDark : Color
  diagramMuted : Color
  surface : Color
  accentText : Color
  accentOnDark : Color
  accentSoft : Color
  deriving Repr, BEq

/-- Authoring roles, independent of renderer palette keys. A ground is a
role too: the same ink may have to work on several actual surfaces. -/
public inductive Role where
  | ink | paper | accent | muted | mutedOnDark | diagramMuted
  | surface | accentText | accentOnDark | accentSoft
  deriving Repr, BEq, DecidableEq

public def Role.name : Role → String
  | .ink => "Ink" | .paper => "Paper" | .accent => "Accent"
  | .muted => "Muted" | .mutedOnDark => "MutedOnDark"
  | .diagramMuted => "DiagramMuted" | .surface => "Surface"
  | .accentText => "AccentText" | .accentOnDark => "AccentOnDark"
  | .accentSoft => "AccentSoft"

@[expose] public def Role.color (s : Seeds) (c : Colors) : Role → Color
  | .ink => s.ink | .paper => s.paper | .accent => s.accent
  | .muted => c.muted | .mutedOnDark => c.mutedOnDark
  | .diagramMuted => c.diagramMuted | .surface => c.surface
  | .accentText => c.accentText | .accentOnDark => c.accentOnDark
  | .accentSoft => c.accentSoft

public def Role.all : List Role :=
  [.ink, .paper, .accent, .muted, .mutedOnDark, .diagramMuted,
   .surface, .accentText, .accentOnDark, .accentSoft]

public theorem Role.all_mem (role : Role) : role ∈ Role.all := by
  cases role <;> simp [Role.all]

/-- A decorative wash's contrast, not an accessibility threshold. One design
token controls both neutral panels and accent tracks. -/
public def washRatio : Nat := 1150

/-- Each requirement names the surface it actually shares. Text and essential
edges must work on the panel as well as on the page (WCAG 2.2, 1.4.3/1.4.11).
Decorative fills carry no text or essential information of their own. -/
@[expose] public def requirements : List (Role × Role × Nat) :=
  [(.ink, .paper, Contrast.aaText),
   (.ink, .surface, Contrast.aaText),
   (.muted, .paper, Contrast.aaText),
   (.muted, .surface, Contrast.aaText),
   (.mutedOnDark, .ink, Contrast.aaText),
   (.accentText, .paper, Contrast.aaText),
   (.accentText, .surface, Contrast.aaText),
   (.accentOnDark, .ink, Contrast.aaText),
   (.diagramMuted, .paper, Contrast.aaNonText),
   (.diagramMuted, .surface, Contrast.aaNonText),
   (.accent, .paper, Contrast.aaNonText),
   (.accent, .surface, Contrast.aaNonText),
   (.accent, .accentSoft, Contrast.aaNonText)]

public def pairs (s : Seeds) (c : Colors) : List (Color × Color × Nat) :=
  requirements.map fun (foreground, ground, req) =>
    (foreground.color s c, ground.color s c, req)

public def contract (s : Seeds) (c : Colors) : Bool :=
  (pairs s c).all fun (ink, ground, req) =>
    decide (req ≤ Contrast.contrastMilli ink ground)

/-- A generated palette carries the contract, never a best-effort colour
substituted for an unsatisfied role. The seeds are parameters, not outputs
the generator is free to change. -/
public structure Generated (s : Seeds) where
  colors : Colors
  valid : contract s colors = true

public theorem generated_contract {s : Seeds} (p : Generated s)
    {ink ground : Color} {req : Nat} (h : (ink, ground, req) ∈ pairs s p.colors) :
    req ≤ Contrast.contrastMilli ink ground := by
  have hv := List.all_eq_true.mp p.valid _ h
  exact of_decide_eq_true hv

/-- A named requirement is checked against the generated RGB values, the
same values exported for both backends. -/
public theorem generated_role_contract {s : Seeds} (p : Generated s)
    {foreground ground : Role} {req : Nat} (h : (foreground, ground, req) ∈ requirements) :
    req ≤ Contrast.contrastMilli (foreground.color s p.colors) (ground.color s p.colors) :=
  generated_contract p (List.mem_map.mpr ⟨(foreground, ground, req), h, rfl⟩)

/-- Select from the seed-to-ground Oklab segment, at the existing cover
API's percentage resolution. Search from the ground: the quietest passing
weight wins. This is palette authoring, not a repair of authored colours. -/
public def tint (req : Nat) (seed ground under : Color) : Option Color :=
  ((List.range 101).find? fun q =>
    let c := Oklab.cover q ground seed
    decide (req ≤ Contrast.contrastMilli c ground) &&
      decide (req ≤ Contrast.contrastMilli c under)).map fun q =>
        Oklab.cover q ground seed

public theorem tint_mem {req : Nat} {seed ground under c : Color}
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
public def generate (s : Seeds) : Option (Generated s) := do
  if s.ink.cmyk.isSome || s.paper.cmyk.isSome || s.accent.cmyk.isSome then none
  else
    let c ← candidate s
    if h : contract s c = true then some ⟨c, h⟩ else none

/-- The ordinary xcolor declarations both front ends already understand.
There is no generator or colour solver to run when compiling the exported
document. Prefix validation belongs to the authoring tool. -/
public def declarations (stem : String) (s : Seeds) (p : Generated s) : String :=
  String.join (Role.all.map fun role =>
    let ink := role.color s p.colors
    "\\definecolor{" ++ stem ++ role.name ++ "}{HTML}{" ++
        Color.hexByte ink.r ++ Color.hexByte ink.g ++ Color.hexByte ink.b ++ "}\n")

/-- Opt-in filled blocks share the neutral surface. Title emphasis follows
the existing text roles; body text keeps the primary ink in every kind.
These are standard Beamer element names, resolved by BeamerColor rather
than a second native-key mapping in the authoring layer. -/
@[expose] public def beamerBlocks : List (String × Role × Role) :=
  [("block title", .ink, .surface),
   ("block title alerted", .accentText, .surface),
   ("block title example", .muted, .surface),
   ("block body", .ink, .surface),
   ("block body alerted", .ink, .surface),
   ("block body example", .ink, .surface)]

private theorem beamer_requirement_mem {element : String} {foreground ground : Role}
    (h : (element, foreground, ground) ∈ beamerBlocks) :
    (foreground, ground, Contrast.aaText) ∈ requirements := by
  simp only [beamerBlocks, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
    ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> simp [requirements]

/-- Every exported block pair satisfies the same generated RGB contract.
This is a contrast guarantee, not a judgement of aesthetic preference. -/
public theorem generated_beamer_contract {s : Seeds} (p : Generated s)
    {element : String} {foreground ground : Role}
    (h : (element, foreground, ground) ∈ beamerBlocks) :
    Contrast.aaText ≤ Contrast.contrastMilli
      (foreground.color s p.colors) (ground.color s p.colors) :=
  generated_role_contract p (beamer_requirement_mem h)

/-- Define the same colours as the plain export, then bind all six filled
block elements to those names. Explicit channels avoid theme-dependent
inheritance; theme initialization must precede these declarations. -/
public def beamerDeclarations (stem : String) (s : Seeds) (p : Generated s) : String :=
  declarations stem s p ++ String.join (beamerBlocks.map fun (element, foreground, ground) =>
    "\\setbeamercolor{" ++ element ++ "}{fg=" ++ stem ++ foreground.name ++
      ",bg=" ++ stem ++ ground.name ++ "}\n")

end LeanTex.Core.SeedPalette
