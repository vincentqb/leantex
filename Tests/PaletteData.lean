module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PaletteData

/-- **The kept palettes are the generator's own answers**: each class
default palette, each shipped bundle's generated palette and each colour a
bundle derives from a lineage colour, as `PaletteData` keeps them, equals a
fresh derivation (`SeedPalette.generate`, `ContrastSolve.realizeNearest`),
and every value a bundle realizes is kept, so no build derives a constant
again and none reads a stale one. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let depths : List Ir.GroundDepth := [.documents, .decks]
  for d in depths do
    let fresh := (SeedPalette.generate SeedPalette.classSeeds
      (SeedPalette.classSeeds.targets d)).toOption.map (·.colors)
    t s!"palette data: the class default at {repr d} is kept as the generator's"
      (fresh.isSome && PaletteData.classGenerated.lookup d == fresh)
  for th in Theme.builtin do
    if let some (seeds, _) := th.seeds then
      for d in depths do
        let kept := PaletteData.bundleGenerated.find? fun e => e.1 == seeds && e.2.1 == d
        t s!"palette data: {th.name}'s palette at {repr d} is kept as the generator's"
          ((th.generatedFresh d).isSome && kept.map (·.2.2) == th.generatedFresh d)
    for (r, seed) in th.derived do
      let kept := PaletteData.bundleDerived.find? fun e => e.1 == th.name && e.2.1 == r
      t s!"palette data: {th.name}'s {(Ir.ColorRef.role r).key} is kept as its lineage realized"
        (kept.map (·.2.2) == some (th.derivedFresh seed))
  t "palette data: nothing kept for a bundle that does not ship it"
    (PaletteData.bundleGenerated.all (fun e => Theme.builtin.any (·.seeds.any (·.1 == e.1))) &&
      PaletteData.bundleDerived.all fun e =>
        (Theme.find? e.1).any fun th => (th.derived.lookup e.2.1).isSome)

end Tests.PaletteData
