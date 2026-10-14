import LeanTex.Core.Contrast
import LeanTex.Core.Elab
import LeanTex.Core.FontDb
import LeanTex.Core.HtmlDoc

/-
The in-process passes bench.lean judges by growth, compiled so they time the engine's code: one
`pass <label> <size> <ns>` line per run, a wrong answer exiting 1.
Usage: lake build passBench && .lake/build/bin/passBench [runs]
-/

open LeanTex.Core

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- Each run's nanoseconds, its answer checked before the clock is read again. -/
def timeRuns (n : Nat) (label : String) (size : Nat) (pass : Unit → Bool) : IO Unit := do
  for _ in [0:n] do
    let t0 ← IO.monoNanosNow
    let right ← IO.lazyPure pass
    unless right do die s!"{label} at {size}: the pass answered wrongly"
    IO.println s!"pass\t{label}\t{size}\t{(← IO.monoNanosNow) - t0}"

/-- An article of `n` sections all titled alike. -/
def sameTitled (n : Nat) : Ir.Doc :=
  (Elab.run "t" ("\\documentclass{article}\\begin{document}" ++
    String.join (List.replicate n "\\section{Topic}") ++ "\\end{document}")).1

/-- An invented palette entry coloured over `n` paragraphs, one run each. -/
def colouredRuns (n : Nat) (name : String) (c : Ir.Color) : Ir.Doc :=
  { palette := { entries := #[((.color name), c)] }
    body := (List.range n).toArray.map fun i =>
      Ir.Block.para #[.colored c (some (.color name)) #[.text s!"w{i}"]] }

def main (args : List String) : IO UInt32 := do
  let n := ((args.head?).bind (·.toNat?)).getD 5
  if n == 0 then die "runs must be positive"
  for s in [600, 2400] do
    let doc := sameTitled s
    if doc.body.isEmpty then die "the same-titled article elaborated to nothing"
    timeRuns n "anchors" s fun _ =>
      ((HtmlDoc.emit {} doc).1.splitOn s!"id=\"topic-{s}\"").length == 2
  for s in [30000, 120000] do
    let faces : Array FontDb.Face := (List.range s).toArray.map fun i =>
      { path := s!"/x/{i}.otf", family := s!"Family {i / 3}", subfamily := "Regular"
        bold := false, italic := false, fixedPitch := false, weight := 400 }
    timeRuns n "families" s fun _ => (FontDb.families faces).size == s / 3
  for s in [400000, 1600000] do
    let labels : Ir.RefTable := ((List.range s).map fun i => (s!"k{i}", none)).toArray
    let rows : Ir.RefTable := ((List.range s).map fun i =>
      (s!"k{i}", some ({ num := toString i, kind := some .figure } : Ir.RefBinding))).toArray
    timeRuns n "merge" s fun _ =>
      let merged := Ir.withFloatRows labels rows
      merged.size == s && match merged.back? with
        | some (_, some b) => b.num == toString (s - 1)
        | _ => false
  for s in [20000, 80000] do
    let doc := colouredRuns s "dk" { r := 0x10, g := 0x10, b := 0x10 }
    timeRuns n "legible" s fun _ => (Contrast.docDiags doc).isEmpty
  for s in [6000, 24000] do
    let doc := colouredRuns s "washed" { r := 0x88, g := 0x88, b := 0x88 }
    timeRuns n "failing" s fun _ =>
      ((Contrast.docDiags doc).filter (·.severity == .warning)).size == 1
  let .ok font := Font.parse (← IO.FS.readBinFile "testdata/corpus/fonts/OpenSans-Regular.ttf")
    | die "OpenSans-Regular.ttf does not parse"
  let g := (font.gid 'q').getD 0
  let (pos, thick) := font.band
  timeRuns n "decodes" 2000 fun _ => Id.run do
    let mut k := 0
    for _ in [0:2000] do
      k := k + ((font.inkSrc.get.inkAt g (pos - thick) pos).map (·.size)).getD 0
    return k == 2000
  timeRuns n "reads" 2000000 fun _ => Id.run do
    let mut k := 0
    for _ in [0:2000000] do
      k := k + (font.inkAt g).size
    return k == 2000000
  return 0
