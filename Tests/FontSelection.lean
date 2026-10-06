import LeanTex.Core.FontDb

/-! An ordinary consumer of the pure selection interface. Importing it must
not expose the old filesystem entry points or require the font parser. -/

open LeanTex.Core

private def regular : FontDb.Face :=
  { path := "Regular.otf", family := "Example Sans", subfamily := "Regular"
    bold := false, italic := false, fixedPitch := false, weight := 400 }

private def demi : FontDb.Face :=
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
