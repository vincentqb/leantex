module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PaletteData

/-- The kept palettes are the generator's own answers, and every value a bundle realizes is kept. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let depths : List Ir.GroundDepth := [.documents, .decks]
  let screens : List Ir.Scheme := [.light, .dark, .lightMore, .darkMore]
  for d in depths do
    for sc in screens do
      let seeds := SeedPalette.classSeedsIn sc
      let fresh := (SeedPalette.generate seeds (seeds.targetsIn d sc)).toOption.map (·.colors)
      let kept := PaletteData.classGenerated.find? fun e => e.1 == d && e.2.1 == sc
      t s!"palette data: the class default at {repr d} in {sc.name} is kept as the generator's"
        (fresh.isSome && kept.map (·.2.2) == fresh.map (seeds, ·))
  for th in Theme.builtin do
    if let some (own, _) := th.seeds then
      for d in depths do
        for sc in screens do
          let fresh := (own.carry sc.onDark).bind fun sd =>
            ((SeedPalette.generate sd (sd.targetsIn d sc)).toOption.map (sd, ·.colors))
          let kept := PaletteData.bundleGenerated.find? fun e =>
            fresh.any (·.1 == e.1) && e.2.1 == d && e.2.2.1 == sc
          t s!"palette data: {th.name}'s palette at {repr d} in {sc.name} is kept as the generator's"
            (fresh.isSome && kept.map (fun e => (e.1, e.2.2.2)) == fresh)
      for d in depths do
        t s!"palette data: {th.name}'s own palette at {repr d} reads the kept light one"
          ((th.generatedFresh d).isSome && th.generated d == th.generatedFresh d)
    for (r, seed) in th.derived do
      let kept := PaletteData.bundleDerived.find? fun e => e.1 == th.name && e.2.1 == r
      t s!"palette data: {th.name}'s {(Ir.ColorRef.role r).key} is kept as its rule derives it"
        (kept.map (·.2.2) == some (th.derivedFresh r seed))
  t "palette data: nothing kept for a bundle that does not ship it"
    (PaletteData.bundleGenerated.all (fun e => Theme.builtin.any fun th => th.seeds.any fun (own, _) =>
        screens.any fun sc => (own.carry sc.onDark).any (· == e.1)) &&
      PaletteData.bundleDerived.all fun e =>
        (Theme.find? e.1).any fun th => (th.derived.lookup e.2.1).isSome)

end Tests.PaletteData
