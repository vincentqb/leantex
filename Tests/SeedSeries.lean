module

public import Tests.Support
public import LeanTex.Core.SeedSeries

public section

open LeanTex.Core
open LeanTex.Cli

/-! A chart's series colours generated from a palette's seeds, and the export the script writes. -/

namespace Tests.SeedSeries

private def generated (s : SeedPalette.Seeds) (n : Nat) : Except String (List Ir.Color) := do
  let t := s.targets .decks
  let p ← match SeedPalette.generate s t with
    | .ok p => pure p
    | .error f => throw f.detail
  let g ← SeedSeries.generate s t p n
  return g.series

/-- Seeds in both polarities generate the most series in farthest-point order, and counts of none or
past the most are refused. -/
def seriesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let white := Ir.Color.white
  let seeds : List (String × SeedPalette.Seeds) := [
    ("a black ink and a yellow accent",
      { ink := Ir.Color.black, paper := white, accent := Ir.Color.ofHtml 0xFA 0xCC 0x15 }),
    ("a violet ink and an orange accent",
      { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := white, accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }),
    ("a warm ink on cream and a teal accent",
      { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
        accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }),
    ("a low-chroma accent",
      { ink := Ir.Color.ofHtml 0x20 0x20 0x20, paper := white, accent := Ir.Color.ofHtml 0x8A 0x8F 0x99 }),
    ("a dark paper and an amber accent",
      { ink := Ir.Color.ofHtml 0xF4 0xF1 0xEA, paper := Ir.Color.ofHtml 0x1B 0x24 0x30,
        accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 })]
  for (label, s) in seeds do
    match generated s SeedSeries.maxCount with
    | .error e => t s!"series, {label}: the most series generate, not fail: {e}" false
    | .ok most =>
      t s!"series, {label}: the most series generate" (most.length == SeedSeries.maxCount)
      let near (k : Nat) : Int :=
        ((most.take k).map Oklab.labOf ++ [Oklab.labOf s.ink]).foldl
          (fun m x => min m (Oklab.distSq (Oklab.labOf (most.getD k Ir.Color.black)) x)) (10 ^ 38)
      t s!"series, {label}: each pick is no farther from its predecessors than the pick before"
        ((List.range (most.length - 2)).all fun k => near (k + 2) ≤ near (k + 1))
      let decls := SeedSeries.declarations "Probe" most
      t s!"series, {label}: the export names every series in order"
        (most.zipIdx.all fun (c, i) => hasStr decls ("\\definecolor{ProbeSeries" ++ toString (i + 1) ++
          "}{HTML}{" ++ Ir.Color.hexByte c.r ++ Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b ++ "}"))
  let s : SeedPalette.Seeds :=
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := white, accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }
  t "series: a count of none is refused" (generated s 0 |>.toOption).isNone
  t "series: a count past the most is refused" (generated s (SeedSeries.maxCount + 1) |>.toOption).isNone

/-- The script writes the series asked for after the palette, its `--check` holds, and an
ungeneratable count is a usage error. -/
def seriesScriptChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let tmp := (← IO.FS.realPath (← IO.currentDir)) / ".lake" / "seed-series-check"
  IO.FS.createDirAll tmp
  let made ← paletteScript #["--series", "10", "seed", "2B2440", "FFFFFF", "E85D2A"]
  t s!"series script: writes the include ({made.err})" (made.complete && made.ran == .exited 0)
  t "series script: names ten series and no eleventh"
    ((List.range 10).all (fun i => made.out.contains ("\\definecolor{seedSeries" ++ toString (i + 1) ++ "}")) &&
      !made.out.contains "seedSeries11")
  t "series script: the palette comes first" (made.out.startsWith "\\definecolor{seedPaper}")
  let hexOf (name : String) : Option String :=
    ((made.out.splitOn ("\\definecolor{" ++ name ++ "}{HTML}{"))[1]?).map (·.take 6 |>.toString)
  t "series script: the first series is the accent's text tone, the page's alert"
    (hexOf "seedSeries1" |>.any fun h => hexOf "seedAccentText" == some h && hexOf "seedAlert" == some h)
  IO.FS.writeFile (tmp / "fresh.tex") made.out
  let fresh ← paletteScript #["--series", "10", "--check", (tmp / "fresh.tex").toString, "seed",
    "2B2440", "FFFFFF", "E85D2A"]
  t s!"series script: --check passes a fresh include ({fresh.err})" (fresh.ran == .exited 0)
  let other ← paletteScript #["--series", "9", "--check", (tmp / "fresh.tex").toString, "seed",
    "2B2440", "FFFFFF", "E85D2A"]
  t "series script: --check fails an include of another count" (other.ran == .exited 1)
  let none_ ← paletteScript #["--series", "0", "seed", "2B2440", "FFFFFF", "E85D2A"]
  t "series script: a count of none is a usage error" (none_.ran == .exited 2)

end Tests.SeedSeries
