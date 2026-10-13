module

public import Tests.Support
public import LeanTex.Core.SeedSeries
public import LeanTex.Cli.RunBounded

public section

open LeanTex.Core
open LeanTex.Cli

/-! A chart's series colours generated from a palette's seeds: the
generator over invented seeds in both polarities, its prefixes and its
refusals, and the export the script writes. -/

namespace Tests.SeedSeries

private def hex (s : String) : Ir.Color :=
  match Decl.parseColorSpec (some "HTML") s with
  | .ok (.html r g b) => { r, g, b }
  | _ => Ir.Color.black

private def generated (s : SeedPalette.Seeds) (n : Nat) : Except String (List Ir.Color) := do
  let t := s.targets .decks
  let p ← match SeedPalette.generate s t with
    | .ok p => pure p
    | .error f => throw f.detail
  let g ← SeedSeries.generate s t p n
  return g.series

/-- Invented seeds in both polarities each generate the most series asked:
the first the palette's accent text, every one standing out from the paper
as a mark and the first reading on it, no two within the declared gap,
pairwise distinct, and each count's series the most count's prefix. -/
def seriesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let seeds : List (String × SeedPalette.Seeds) := [
    ("a black ink and a yellow accent", { ink := hex "000000", paper := hex "FFFFFF", accent := hex "FACC15" }),
    ("a violet ink and an orange accent", { ink := hex "2B2440", paper := hex "FFFFFF", accent := hex "E85D2A" }),
    ("a warm ink on cream and a teal accent", { ink := hex "3B2F2A", paper := hex "FBF6EC", accent := hex "0D9488" }),
    ("a low-chroma accent", { ink := hex "202020", paper := hex "FFFFFF", accent := hex "8A8F99" }),
    ("a dark paper and an amber accent", { ink := hex "F4F1EA", paper := hex "1B2430", accent := hex "F2A541" })]
  for (label, s) in seeds do
    let tg := s.targets .decks
    match SeedPalette.generate s tg, generated s SeedSeries.maxCount with
    | .ok p, .ok most =>
      t s!"series, {label}: the most series generate" (most.length == SeedSeries.maxCount)
      t s!"series, {label}: the first is the palette's accent text" (most.head? == some p.colors.accentText)
      t s!"series, {label}: each stands out from the paper as a mark"
        (most.all fun c => tg.edge ≤ Contrast.contrastMilli c s.paper)
      t s!"series, {label}: the first reads on the paper as text"
        (most.head?.all fun c => tg.text ≤ Contrast.contrastMilli c s.paper)
      t s!"series, {label}: no two stand within the declared gap"
        (most.Pairwise fun c c' =>
          SeedSeries.minGap * SeedSeries.minGap ≤ ContrastSolve.deltaEOkSq c c')
      t s!"series, {label}: no two are one colour" most.Nodup
      t s!"series, {label}: a count's series are the most count's first"
        ([1, 2, 5, 10].all fun k => generated s k == .ok (most.take k))
      let decls := SeedSeries.declarations "Probe" most
      t s!"series, {label}: the export names every series in order"
        (most.zipIdx.all fun (c, i) => hasStr decls ("\\definecolor{ProbeSeries" ++ toString (i + 1) ++
          "}{HTML}{" ++ Ir.Color.hexByte c.r ++ Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b ++ "}"))
    | _, .error e => t s!"series, {label}: generate, not fail: {e}" false
    | .error f, _ => t s!"series, {label}: the palette generates, not fail at {reprStr f.role}" false
  let s : SeedPalette.Seeds := { ink := hex "2B2440", paper := hex "FFFFFF", accent := hex "E85D2A" }
  t "series: no count is refused" (generated s 0 |>.toOption).isNone
  t "series: a count past the most is refused" (generated s (SeedSeries.maxCount + 1) |>.toOption).isNone

/-- The script writes the series it is asked for after the palette, and its
`--check` passes the include it wrote; a count it cannot generate is a usage
error. -/
def seriesScriptChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (lean, leanPath) ← leanChild "the palette script's series checks"
  let dir ← IO.FS.realPath (← IO.currentDir)
  let tmp := dir / ".lake" / "seed-series-check"
  IO.FS.createDirAll tmp
  let run (args : Array String) :=
    RunBounded.runBounded lean.toString (#["--run", "scripts/palette.lean"] ++ args) dir 120000 100
      (env := #[("LEAN_PATH", some leanPath)])
  let made ← run #["--series", "10", "seed", "2B2440", "FFFFFF", "E85D2A"]
  t s!"series script: writes the include ({made.err})" (made.complete && made.ran == .exited 0)
  t "series script: names ten series and no eleventh"
    ((List.range 10).all (fun i => made.out.contains ("\\definecolor{seedSeries" ++ toString (i + 1) ++ "}")) &&
      !made.out.contains "seedSeries11")
  t "series script: the palette comes first" (made.out.startsWith "\\definecolor{seedPaper}")
  IO.FS.writeFile (tmp / "fresh.tex") made.out
  let fresh ← run #["--series", "10", "--check", (tmp / "fresh.tex").toString, "seed", "2B2440",
    "FFFFFF", "E85D2A"]
  t s!"series script: --check passes a fresh include ({fresh.err})" (fresh.ran == .exited 0)
  let none_ ← run #["--series", "0", "seed", "2B2440", "FFFFFF", "E85D2A"]
  t "series script: no count is a usage error" (none_.ran == .exited 2)

end Tests.SeedSeries
