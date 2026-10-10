/-
The document-cost gate: how the engine's memory grows with a document, and
what its artifacts weigh. Run from the repository root after
`lake build leantex scripts.doccost`, which builds the engine it measures and
the modules it imports (the scoreboard builds both before any tier runs, and
`bench --doc-cost` before its report):

  lake env lean --run scripts/doccost.lean              regenerate the baseline
  lake env lean --run scripts/doccost.lean --check      gate against the committed one
  lake env lean --run scripts/doccost.lean --report     print what each item reads, write nothing
  lake env lean --run scripts/doccost.lean --selftest   the judges
  lake env lean --run scripts/doccost.lean --bench [--record] [--history <path>]
                                                        the host's numbers (`bench --doc-cost`)

Every item comes from sealed builds of invented documents
(`scripts/DocBench.lean`) — staged corpus fonts and images, no tool on `PATH`,
an empty `HOME`, every face file a build loads a staged one — so every
artifact, and so every size, is a function of the repository. A growth item is
a verdict on a ratio that moves with the host's cores and load (0.9x to 1.9x
so far); the verdict does not, while the ratio stays inside the bound's slack.

* `<family>/<format>/rss-growth`: 1000 when the peak resident set size the
  engine states for itself, above its fixed footprint (a run that reads no
  document), grows at most eightfold from `n` units to `4n`; 999 when it does
  not. Linear phases read at most 4x however one hides another
  (`phasePeak_between`), and twice that where a structure's capacity doubles
  as it fills, so the bound never fails an engine whose needs grow linearly
  (`growthWithin_phasePeak_covers`, `growthWithin_doubled_covers`). A term
  quadratic in the document's size fails an item exactly when its coefficient
  exceeds the item's headroom over `8n²` (`growthWithin_quadratic_exact`),
  which `--report` prints (the provenance states the rule, not the figures,
  which move with the host and the run): the gate sees a quadratic term only
  once it is heavy at these sizes. A peak is the
  process's own, so the verdict survives what else the host runs, where
  milliseconds would not.
* `<family>/<format>/rss-growth-16n`: the same bound from `4n` units to `16n`,
  for the families whose `16n` build is cheap, where it sees a quadratic term
  ten to eighteen times smaller than the `n` pair does.
* `<family>/<format>/size`: 1000 minus the `4n` gate document's size class,
  in quarter octaves of KiB, held while the artifact stays within its
  committed class widened by an eighth of an octave each way (`heldClass`), so
  drift of a few bytes at a boundary moves nothing. An artifact a class
  heavier is a fall, which needs a `# lowered:` line saying why the weight is
  worth it; so does a size item a new family or format brings, since it
  enters below the cap.

Milliseconds are reported by `bench --doc-cost`, and recorded run by run in
`testdata/perf/documents.tsv`, whose format this tier also holds.
`testdata/probes/u106/` holds the engine changes that show the growth items'
power: a page-quadratic allocation fails the `16n` pair that the `n` pair
passes, a page-linear one as heavy fails neither.
-/
import scripts.Board
import scripts.DocBench

open Scoreboard

def growthRule : String :=
  s!"# rss-growth: 1000 when the peak resident set size above the engine's fixed footprint (a run \
that reads no document, least of {DocBench.footprintRuns}), least of {DocBench.gateRuns} builds \
per size, grows from n units to 4n by at most {DocBench.growthBound}x; 999 otherwise. \
rss-growth-16n: the same from 4n to 16n"

def sizeRule : String :=
  "# size: 1000 minus the size class of the 4n gate document's artifact, floor(4 log2(KiB)) — \
one class is a 19% change — held while the artifact stays within its committed class widened by \
an eighth of an octave on each side"

def documentsLine : String :=
  "# documents: n/4n units, and 16n where it is cheap, after a fixed opening that already uses \
every feature a unit does: " ++
  String.intercalate ", " (DocBench.gens.toList.map fun g =>
    s!"{g.name} {g.gate}/{4 * g.gate}{if g.far then s!"/{16 * g.gate}" else ""} {g.unit}") ++
  " — invented (scripts/DocBench.lean), each built to pdf and html in a sealed environment"

/-- What a growth item can see, as a rule: the figures it bounds — each
item's headroom and least failing term — move with the host and the run, so
the file states the rule and `--report` prints the figures, and a
regeneration rewrites no line it did not measure differently. -/
def headroomLine : String :=
  "# power: a growth item fails once a quadratic memory term c·u² exceeds its headroom over \
8n² (growthWithin_quadratic_exact); doccost --report prints each item's headroom and least \
failing term, which move with the host and the run"

def measureTier : IO (Array String × Array Row) := do
  match ← PerfHistory.read DocBench.historyPath with
  | .error e =>
    IO.eprintln s!"doccost: the document-cost history is malformed: {e}"
    return (#[], #[])
  | .ok h =>
    if let some e := (PerfHistory.recordable h.rows)[0]? then
      IO.eprintln s!"doccost: {DocBench.historyPath}: {e}; the committed history names \
committed trees only"
      return (#[], #[])
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  IO.FS.withTempDir fun dir => do
    match ← DocBench.measureAll binary dir DocBench.gateRuns 4 with
    | .error e =>
      IO.eprintln s!"doccost: {e}"
      return (#[], #[])
    | .ok (_, gs) =>
      let committed : Option Tsv := (parse (← readFileOr (tsvPath "doccost"))).toOption
      let held (item : String) : Option Nat :=
        (committed.bind (·.find? item)).bind fun v =>
          if v ≤ debtCap then some (debtCap - v).toNat else none
      let mut rows : Array Row := #[]
      let mut classes : Array String := #[]
      for g in gs do
        unless g.within do
          IO.eprintln s!"doccost: {g.item}: least peaks {g.small} KiB at {g.n} units and {g.big} \
KiB at {4 * g.n}, over a fixed footprint of {g.fixed} KiB: {DocBench.times g.rssPct}, above the \
{DocBench.growthBound}x bound"
        rows := rows.push { item := g.item, value := debtCap - (if g.within then 0 else 1) }
        if g.pair == "rss-growth" then
          let cls := DocBench.heldClass (held (g.key ++ "/size")) g.bytes
          rows := rows.push { item := g.key ++ "/size", value := debtCap - Int.ofNat cls }
          classes := classes.push s!"{g.key} {cls} from {DocBench.classStartKiB cls} KiB"
      return (#[documentsLine, growthRule, headroomLine, sizeRule,
        "# size classes: " ++ String.intercalate "; " classes.toList], rows)

/-- Every item's reading, written nowhere: the footprint, each pair's least
peaks, the ratio, its headroom and the least quadratic term that fails it, and
the larger artifact's bytes and class. What the probes in
`testdata/probes/u106/` print. -/
def report : IO UInt32 := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  IO.FS.withTempDir fun dir => do
    match ← DocBench.measureAll binary dir DocBench.gateRuns 4 with
    | .error e =>
      IO.eprintln s!"doccost: {e}"
      return 1
    | .ok (fixed, gs) =>
      IO.println s!"doccost report: fixed footprint {DocBench.mib fixed} (least of \
{DocBench.footprintRuns}); least of {DocBench.gateRuns} builds per size; bound \
{DocBench.growthBound}x"
      let mut over := 0
      for g in gs do
        unless g.within do over := over + 1
        IO.println s!"  {DocBench.padRight g.item 27} {DocBench.padLeft s!"{g.n}→{4 * g.n}" 9} \
{DocBench.padLeft (DocBench.mib g.small) 10} → {DocBench.padLeft (DocBench.mib g.big) 10}  \
{DocBench.padLeft (DocBench.times g.rssPct) 5}  \
{if g.within then s!"within; headroom {DocBench.mib g.headroomKiB}, quadratic above \
{DocBench.bytesText g.quadraticBytes} per {g.unit}²" else "OVER the bound"}  \
artifact {DocBench.kibOf g.bytes} over {g.pages} pages, class {DocBench.sizeClass g.bytes}"
      IO.println s!"{over} of {gs.size} growth items over the bound"
      return 0

/-- `bench --doc-cost`'s report: the host's numbers, against the last run on
this host class, appended to the history with `--record`. -/
def bench (args : List String) : IO UInt32 := do
  let runs := ((← IO.getEnv "N").bind (·.toNat?)).getD 3
  if runs == 0 then
    IO.eprintln "doc-cost: N must be positive"
    return 1
  let history := match args.dropWhile (· != "--history") with
    | _ :: path :: _ => some (System.FilePath.mk path)
    | [_] => none
    | [] => some DocBench.historyPath
  let some history := history
    | IO.eprintln "doc-cost: --history names the history file to compare with and record into"
      return 1
  let binary := (← IO.getEnv "LEANTEX_BENCH_BINARY").getD ".lake/build/bin/leantex"
  DocBench.runReport (← IO.FS.realPath binary) runs (args.contains "--record") history

def selftest : IO UInt32 := tierSelftest "doccost" fun no => do
  let mib := 1024
  no "growth: linear passes" (DocBench.growthWithin (70 * mib) (130 * mib) (310 * mib))
  no "growth: twice linear, a doubled capacity, passes"
    (DocBench.growthWithin (70 * mib) (130 * mib) (550 * mib))
  no "growth: quadratic fails" (!DocBench.growthWithin (70 * mib) (130 * mib) (1030 * mib))
  no "growth: the bound is eight times what n added, exactly"
    (DocBench.growthWithin (70 * mib) (130 * mib) (70 * mib + 8 * 60 * mib) &&
     !DocBench.growthWithin (70 * mib) (130 * mib) (70 * mib + 8 * 60 * mib + 1))
  no "growth: a doubled capacity over a linear peak passes, which a fourfold bound fails"
    (DocBench.growthWithin 70 (70 + DocBench.phasePeak [(0, 3)] 10)
      (70 + 2 * DocBench.phasePeak [(0, 3)] 40) &&
     !decide (2 * DocBench.phasePeak [(0, 3)] 40 ≤ 4 * DocBench.phasePeak [(0, 3)] 10))
  let g : DocBench.Growth :=
    { gen := "g", unit := "unit", format := "pdf", pair := "rss-growth", n := 10, fixed := 70,
      small := 130, big := 160, smallWall := 0, bigWall := 0, bytes := 0, pages := 0 }
  no "growth: headroom is what 4n may add before the item fails"
    (g.headroomKiB == 390 && DocBench.growthWithin 70 130 (160 + 390) &&
      !DocBench.growthWithin 70 130 (160 + 391))
  no "growth: a quadratic term fails exactly when eight times it exceeds the headroom"
    (DocBench.growthWithin 70 (130 + 48) (160 + 16 * 48) &&
      !DocBench.growthWithin 70 (130 + 49) (160 + 16 * 49))
  no "growth: the least quadratic coefficient is the headroom over 8n², in bytes per unit²"
    (g.quadraticBytes == 499 && { g with n := 40 }.quadraticBytes == 31 &&
      g.item == "g/pdf/rss-growth")
  no "growth: only the families whose 16n build is cheap take the 16n pair"
    ((DocBench.gens.filter (·.far)).map (·.name) == #["deck", "paper", "notes"])
  no "growth: a linear phase overtaking a constant one passes (the old bound failed it)"
    (DocBench.growthWithin 70 (70 + DocBench.phasePeak [(90, 0), (40, 3)] 10)
      (70 + DocBench.phasePeak [(90, 0), (40, 3)] 40))
  no "growth: the model's peak is the largest phase"
    (DocBench.phasePeak [(90, 0), (40, 3)] 10 == 90 &&
     DocBench.phasePeak [(90, 0), (40, 3)] 40 == 160)
  no "size: under a KiB is class 0, a KiB is class 0, two KiB class 4"
    (DocBench.sizeClass 1000 == 0 && DocBench.sizeClass 1024 == 0 && DocBench.sizeClass 2048 == 4)
  no "size: a MiB is class 40, 19% more is class 41"
    (DocBench.sizeClass 1048576 == 40 && DocBench.sizeClass 1248000 == 41)
  no "size: the class start reads back" (DocBench.classStartKiB 26 == "90.5" &&
    DocBench.classStartKiB 0 == "1.0")
  no "size: a committed class holds across its boundary's eighth octave"
    (DocBench.heldClass (some 27) 132000 == 27 && DocBench.sizeClass 132000 == 28 &&
     DocBench.heldClass (some 28) 129000 == 28 && DocBench.sizeClass 129000 == 27)
  no "size: beyond the margin the artifact's own class reads"
    (DocBench.heldClass (some 27) 145000 == 28 && DocBench.heldClass (some 28) 110000 == 26)
  no "size: with nothing committed the artifact's own class reads"
    (DocBench.heldClass none 132000 == 28)
  no "encoding: a heavier artifact never reads higher"
    (debtCap - Int.ofNat (DocBench.sizeClass 300000) ≤
      debtCap - Int.ofNat (DocBench.sizeClass 200000))
  no "text: bytes print in the unit that keeps them short"
    (DocBench.bytesText 499 == "499 B" && DocBench.bytesText 2048 == "2.0 KiB" &&
      DocBench.bytesText 3145728 == "3.0 MiB")
  let summary := "{\"event\":\"summary\",\"file\":\"d.tex\",\"ok\":true,\"output\":\"d.pdf\",\
\"pages\":2,\"errors\":0,\"ms\":40,\"rssKiB\":90000}"
  let font := "{\"event\":\"phase\",\"name\":\"font\",\"detail\":\"Face (/elsewhere/a.otf)\",\
\"ms\":3,\"faces\":[\"/s/fonts/a.otf\",\"/s/fonts/b.ttf\"],\"scanned\":67}"
  let untyped := "{\"event\":\"phase\",\"name\":\"font\",\
\"detail\":\"Face (/s/fonts/a.otf, /s/fonts/b.ttf)\",\"ms\":3}"
  let warn := "{\"event\":\"diagnostic\",\"severity\":\"warning\",\"code\":\"W0001\",\"message\":\"m\"}"
  match DocBench.readReport (String.intercalate "\n" [font, warn, summary]) with
  | .ok b =>
    no "report: the summary's fields read" (b.ms == 40 && b.rssKiB == 90000 && b.pages == 2)
    no "report: losses, phases and the font phase's typed faces read"
      (b.losses == #["W0001"] && b.phases.size == 1 &&
        b.faces == some (#["/s/fonts/a.otf", "/s/fonts/b.ttf"], 67))
    no "sealed: staged faces pass, whatever the detail's prose says"
      (DocBench.fontsSealed { root := "/s" } b)
    no "sealed: a face outside the stage fails"
      (!DocBench.fontsSealed { root := "/t" } b)
    no "sealed: a build that loaded no face fails"
      (!DocBench.fontsSealed { root := "/s" } { b with faces := some (#[], 67) })
  | .error e => no s!"report: a valid report was refused: {e}" false
  match DocBench.readReport (untyped ++ "\n" ++ summary) with
  | .ok b =>
    no "sealed: a font phase without typed faces fails, however its prose reads"
      (b.faces.isNone && !DocBench.fontsSealed { root := "/s" } b)
  | .error e => no s!"report: a font phase without typed faces was refused: {e}" false
  for (why, bad) in [("no summary", font), ("two summaries", summary ++ "\n" ++ summary),
      ("two font phases", font ++ "\n" ++ font ++ "\n" ++ summary),
      ("typed faces with no scan", font.replace ",\"scanned\":67" "" ++ "\n" ++ summary),
      ("typed faces that are not strings", font.replace "\"/s/fonts/b.ttf\"" "7" ++ "\n" ++ summary),
      ("no peak", summary.replace ",\"rssKiB\":90000" ""),
      ("no artifact", summary.replace "\"ok\":true" "\"ok\":false"), ("non-JSON", "crashed")] do
    no s!"report: {why} is refused" (DocBench.readReport bad |>.toOption).isNone
  for g in DocBench.gens do
    let small := g.source g.gate 0
    no s!"{g.name}: deterministic" (small == g.source g.gate 0)
    no s!"{g.name}: the main source is TeX" ((small[0]?.map (·.1.endsWith ".tex")).getD false)
    no s!"{g.name}: units grow the source"
      ((g.source 0 0).foldl (· + ·.2.length) 0 < small.foldl (· + ·.2.length) 0)
    no s!"{g.name}: a revision changes the main source and only it"
      ((g.source g.gate 1)[0]? != small[0]? && (g.source g.gate 1).extract 1 9 == small.extract 1 9)
  for f in PerfHistory.selftest do no s!"history: {f}" false

def main (args : List String) : IO UInt32 := do
  if args.contains "--report" then return ← report
  if args.contains "--bench" then return ← bench args
  tierMain "doccost" (.headroom debtCap) measureTier selftest args
