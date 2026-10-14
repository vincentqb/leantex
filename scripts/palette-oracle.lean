/-
The palette-oracle tier: each generated role's nearness to the step Radix Colors and Tailwind
CSS design for its use, and the least gate margin over an invented seed matrix; hermetic.
Usage: lake env lean --run scripts/palette-oracle.lean [--check | --selftest]
-/
import LeanTex
import scripts.Board

open LeanTex.Core Scoreboard

namespace PaletteOracle

def root : String := "testdata/external/palettes"

/-- The files this repository wrote beside the vendored ones. -/
def ownFiles : List String := ["SHA256SUMS", "PROVENANCE.txt"]

/-- Where a vendored directory stops holding upstream's bytes: a pinned file
whose bytes are not its pin's or that is gone, and a file no pin names. -/
def sumFaults (dir : String) : IO (Array String) := do
  let sums := dir ++ "/SHA256SUMS"
  let entries ← match parsePins sums (← readFileOr sums) with
    | .ok es => pure es
    | .error e => return #[e]
  let mut faults : Array String := #[]
  for e in entries do
    let p := dir ++ "/" ++ e.path
    if e.path.startsWith "/" || (e.path.splitOn "..").length > 1 then
      faults := faults.push s!"{sums}: '{e.path}' leaves the directory"
    else if !(← System.FilePath.pathExists p) then
      faults := faults.push s!"{p}: pinned in {sums}, and absent"
    else if sha256Hex (← IO.FS.readBinFile p) != e.pin then
      faults := faults.push s!"{p}: not the bytes its pin in {sums} names"
  for f in ← System.FilePath.walkDir dir do
    unless ← f.isDir do
      let rel := (f.toString.drop (dir.length + 1)).toString
      unless ownFiles.contains rel || entries.any (·.path == rel) do
        faults := faults.push s!"{f}: in the directory, and pinned by no line of {sums}"
  return faults

/-- A scale: its name and its steps' colours, by step name. -/
structure Scale where
  name : String
  steps : List (String × Ir.Color)

def Scale.step (s : Scale) (n : String) : Option Ir.Color := s.steps.lookup n

/-- The sRGB steps of one Radix light scale: the `:root` block's
`--<name>-<n>: #rrggbb;` lines, before the Display P3 block. -/
def radixScale (name text : String) : Scale := Id.run do
  let mut steps : List (String × Ir.Color) := []
  for l in text.splitOn "\n" do
    let t := l.trimAscii.toString
    if t.startsWith "@supports" then break
    let pre := "--" ++ name ++ "-"
    if t.startsWith pre && t.endsWith ";" then
      match ((t.drop pre.length).toString.dropEnd 1).toString.splitOn ": " with
      | [n, v] =>
        match Decl.parseColorSpec none v.trimAscii.toString with
        | .ok (.html r g b) => steps := steps ++ [(n, ({ r := r, g := g, b := b } : Ir.Color))]
        | _ => pure ()
      | _ => pure ()
  return { name, steps }

/-- Every palette of Tailwind's theme: its `--color-<name>-<step>: oklch(…);`
lines, read through the engine's own `oklch()` reader. -/
def tailwindScales (text : String) : List Scale := Id.run do
  let mut out : List Scale := []
  for l in text.splitOn "\n" do
    let t := l.trimAscii.toString
    unless t.startsWith "--color-" && t.endsWith ";" do continue
    match ((t.drop "--color-".length).toString.dropEnd 1).toString.splitOn ": " with
    | [key, v] =>
      let parts := key.splitOn "-"
      let some step := parts.getLast? | continue
      if !step.all Char.isDigit then continue
      let name := "-".intercalate parts.dropLast
      let color := match Decl.parseColorSpec none v.trimAscii.toString with
        | .ok spec => Ir.Palette.resolveSpec {} spec
        | .error _ => none
      if let some c := color then
        out := match out.find? (·.name == name) with
          | some _ => out.map fun s => if s.name == name then { s with steps := s.steps ++ [(step, c)] } else s
          | none => out ++ [{ name, steps := [(step, c)] }]
    | _ => pure ()
  return out

/-- ΔEOK in thousandths. -/
def deltaMilli (a b : Ir.Color) : Int :=
  (Nat.sqrt (Oklab.distSq (Oklab.labOf a) (Oklab.labOf b)).toNat : Int) * 1000 / 10 ^ 18

/-- The roles scored, the depth each is generated at (the accent's text at a document's, owing
4.5:1), and the step each system designs for the same use. -/
def scored : List (String × (SeedPalette.Colors → Ir.Color) × Ir.GroundDepth × String × String) :=
  [("surface", (·.surface), .decks, "3", "100"), ("surface-strong", (·.surfaceStrong), .decks, "5", "200"),
   ("rule", (·.rule), .decks, "7", "300"), ("accent-edge", (·.accentEdge), .decks, "8", "500"),
   ("accent-text", (·.accentText), .documents, "11", "700")]

/-- One system's scores: per role, the summed ΔEOK and how many scales gave one. -/
def scoreSystem (scales : List Scale) (solid ink : String) (radix : Bool) :
    List (String × Int × Nat) × List String := Id.run do
  let mut acc : List (String × Int × Nat) := scored.map fun (r, _) => (r, 0, 0)
  let mut skipped : List String := []
  for s in scales do
    let (some accent, some text) := (s.step solid, s.step ink) | continue
    let seeds : SeedPalette.Seeds := { ink := text, paper := Ir.Color.white, accent }
    match SeedPalette.generate seeds (seeds.targets .decks), SeedPalette.generate seeds
        (seeds.targets .documents) with
    | .error f, _ | _, .error f => skipped := skipped ++ [s!"{s.name} ({(Ir.ColorRef.role f.role).key})"]
    | .ok deck, .ok doc =>
      acc := acc.map fun (r, sum, n) =>
        match scored.find? (·.1 == r) with
        | some (_, get, depth, rs, ts) =>
          match s.step (if radix then rs else ts) with
          | some want =>
            let colors := if depth == .documents then doc.colors else deck.colors
            (r, sum + deltaMilli (get colors) want, n + 1)
          | none => (r, sum, n)
        | none => (r, sum, n)
  return (acc, skipped)

/-- The invented seed matrix the gate margin ranges over, both polarities. -/
def matrix : List SeedPalette.Seeds :=
  let hex (s : String) : Ir.Color := match Decl.parseColorSpec (some "HTML") s with
    | .ok (.html r g b) => ({ r := r, g := g, b := b } : Ir.Color)
    | _ => Ir.Color.black
  [("2B2440", "FFFFFF", "E85D2A"), ("1A1A1A", "FFFFFF", "2563EB"), ("3B2F2A", "FBF6EC", "0D9488"),
   ("F4F1EA", "1B2430", "F2A541"), ("E8EEF6", "10151C", "4F8EF7"), ("1C1917", "FFFFFF", "FACC15"),
   ("1C1917", "FFFFFF", "F59E0B"), ("202020", "FFFFFF", "8A8F99"), ("241B2F", "FFFFFF", "C026D3"),
   ("14281D", "FFFFFF", "16A34A"), ("1E293B", "FFFFFF", "FDE68A"), ("000000", "FFFFFF", "777777")].map
    fun (i, p, a) => { ink := hex i, paper := hex p, accent := hex a }

/-- The smallest margin above its target's gate any site keeps, in thousandths. -/
def gateMargin : Int × Nat := Id.run do
  let mut least : Int := 1000000
  let mut made := 0
  for s in matrix do
    for d in Ir.GroundDepth.all do
      let t := s.targets d
      if let .ok g := SeedPalette.generate s t then
        made := made + 1
        for (_, i, gr, r) in SeedPalette.sites s t g.colors do
          let gate := if r ≥ Contrast.aaText then Contrast.aaText else Contrast.aaNonText
          least := min least ((Contrast.contrastMilli i gr : Int) - gate)
  return (least, made)

def measureTier : IO (Array String × Array Row) := do
  let mut faults : Array String := #[]
  for dir in [root ++ "/radix", root ++ "/tailwind"] do
    faults := faults ++ (← sumFaults dir)
  unless faults.isEmpty do
    for f in faults do IO.eprintln s!"palette-oracle: {f}"
    return (#[], #[])
  let mut radix : List Scale := []
  for f in (← System.FilePath.readDir (root ++ "/radix")).qsort (·.fileName < ·.fileName) do
    if f.fileName.endsWith ".css" then
      let name := (f.fileName.dropEnd 4).toString
      radix := radix ++ [radixScale name (← IO.FS.readFile f.path)]
  let tailwind := tailwindScales (← IO.FS.readFile (root ++ "/tailwind/theme.css"))
  let (rs, rskip) := scoreSystem radix "9" "12" true
  let (ts, tskip) := scoreSystem tailwind "500" "950" false
  let mut rows : Array Row := #[]
  for (sys, scores) in [("radix", rs), ("tailwind", ts)] do
    for (r, sum, n) in scores do
      if n > 0 then rows := rows.push { item := s!"{sys}.{r}", value := 1000 - sum / n }
  let (margin, made) := gateMargin
  rows := rows.push { item := "gates.least-margin", value := margin }
  let extra := #[
    s!"# radix: {radix.length} light scales, 3.0.0; scored {radix.length - rskip.length}" ++
      (if rskip.isEmpty then "" else s!", generating none from {", ".intercalate rskip}"),
    s!"# tailwind: {tailwind.length} palettes, v4.3.3; scored {tailwind.length - tskip.length}" ++
      (if tskip.isEmpty then "" else s!", generating none from {", ".intercalate tskip}"),
    s!"# gates: {made} palettes from the invented matrix at each depth"]
  return (extra, rows)

def selftest : IO UInt32 := tierSelftest "palette-oracle" fun no => do
  no "delta: a colour is its own match" (deltaMilli Ir.Color.white Ir.Color.white == 0)
  no "delta: black and white stand one lightness apart" (deltaMilli Ir.Color.white Ir.Color.black ≥ 999)
  let rx := radixScale "amber" ":root {\n  --amber-1: #fefdfb;\n  --amber-9: #ffc53d;\n}\n@supports (x) {\n  --amber-1: #000000;\n}\n"
  no "radix: the sRGB block is read" (rx.step "1" == some { r := 0xFE, g := 0xFD, b := 0xFB })
  no "radix: the P3 block is not" (rx.steps.length == 2)
  let tw := tailwindScales "  --color-red-50: oklch(97.1% 0.013 17.38);\n  --color-red-500: oklch(63.7% 0.237 25.331);\n  --color-black: #000;\n"
  no "tailwind: one palette, two steps" (tw.length == 1 && (tw.head?.map (·.steps.length)) == some 2)
  no "tailwind: a colour without a step is no palette" (tw.all (·.name == "red"))
  no "gates: the matrix generates" (gateMargin.2 > 0)
  no "gates: every margin stands above its gate" (gateMargin.1 ≥ 0)

end PaletteOracle

def main (args : List String) : IO UInt32 :=
  tierMain "palette-oracle" .raw PaletteOracle.measureTier PaletteOracle.selftest args
