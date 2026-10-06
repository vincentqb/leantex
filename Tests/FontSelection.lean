module

import LeanTex.Core.FontDb
-- The executable guards need the same public interface at compile time.
meta import LeanTex.Core.FontDb

/-! An ordinary consumer of the pure selection interface. Importing it must
not expose the old filesystem entry points, implementation helpers or
implementation imports. Public contracts must work without `import all`. -/

open LeanTex.Core

def regular : FontDb.Face :=
  { path := "Regular.otf", family := "Example Sans", subfamily := "Regular"
    bold := false, italic := false, fixedPitch := false, weight := 400 }

def demi : FontDb.Face :=
  { regular with path := "Demi.otf", subfamily := "Demi", bold := true, weight := 600 }

#guard ((FontDb.resolve #[regular, demi] "example-sans" { bold := true }).map
  fun (face, satisfied) => (face.path, satisfied)) == some ("Demi.otf", true)
#guard ((FontDb.resolve #[regular, demi] "Example Sans" { italic := true }).map
  fun (face, satisfied) => (face.path, satisfied)) == some ("Regular.otf", false)
#guard (FontDb.resolveNamed #[regular, demi] "Demi.otf").map (·.path) == some "Demi.otf"
#guard (FontDb.resolveVariant #[regular] "Example Sans" none {}).isSome
#guard (FontDb.resolveWeight #[] "Absent" none 500 false).isNone
#guard FontDb.hasFontExtension "EXAMPLE.OTF"
#guard !FontDb.hasFontExtension "collection.ttc"

example (faces : Array FontDb.Face) (weight : Nat) (h : 0 < faces.size) :
    (FontDb.pickWeighted faces weight).isSome :=
  FontDb.pickWeighted_total faces weight h

example (lt : FontDb.Face → FontDb.Face → Bool)
    (htrans : ∀ f g h, lt f g → lt g h → lt f h)
    (hasym : ∀ f g, lt f g → ¬ lt g f)
    (a b : Array FontDb.Face) (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ lt f g ∨ lt g f) :
    FontDb.leastBy lt a = FontDb.leastBy lt b :=
  FontDb.leastBy_set_eq lt htrans hasym a b hmem htotal

example (a b : Array FontDb.Face) (body : String)
    (hmem : ∀ f, f ∈ a ↔ f ∈ b)
    (htrans : ∀ f g h, FontDb.faceLt f g → FontDb.faceLt g h → FontDb.faceLt f h)
    (hasym : ∀ f g, FontDb.faceLt f g → ¬ FontDb.faceLt g f)
    (htotal : ∀ f g, f ∈ a → g ∈ a → f = g ∨ FontDb.faceLt f g ∨ FontDb.faceLt g f) :
    FontDb.pickCompanion a body = FontDb.pickCompanion b body :=
  FontDb.pickCompanion_set_eq a b body hmem htrans hasym htotal

/-- error: Unknown identifier `Std.HashSet` -/
#guard_msgs in
#check Std.HashSet

/-- error: Unknown identifier `FontDb.norm` -/
#guard_msgs in
#check FontDb.norm

/-- error: Unknown identifier `FontDb.leastStep` -/
#guard_msgs in
#check FontDb.leastStep

/-- error: Unknown identifier `FontDb.scan` -/
#guard_msgs in
#check FontDb.scan

/-- error: Unknown identifier `FontDb.scanRootsIn` -/
#guard_msgs in
#check FontDb.scanRootsIn

/-- error: Unknown identifier `FontDb.tableImage` -/
#guard_msgs in
#check FontDb.tableImage

/-- error: Unknown identifier `FontDb.pickMathFace` -/
#guard_msgs in
#check FontDb.pickMathFace

/-- error: Unknown identifier `FontDb.fallbackPicks` -/
#guard_msgs in
#check FontDb.fallbackPicks

/-- error: Unknown identifier `Font.classify` -/
#guard_msgs in
#check Font.classify
