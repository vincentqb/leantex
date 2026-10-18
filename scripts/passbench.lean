import LeanTex.Core.Contrast
import LeanTex.Core.Elab
import LeanTex.Core.Flate
import LeanTex.Core.FontDb
import LeanTex.Core.HtmlDoc
import LeanTex.Core.PdfObj
import LeanTex.Core.MdDesugar

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

/-- A deck of `n` frames all titled alike, each stepped once. -/
def sameTitledDeck (n : Nat) : Ir.Doc :=
  (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
    String.join (List.replicate n "\\begin{frame}{Topic}\nx\\only<2>{y}\n\\end{frame}\n") ++
    "\\end{document}")).1

/-- A markdown text of `n` paragraphs, each a reference to a label one of `n` definitions after them
gives. -/
def referenced (n : Nat) : String :=
  String.join ((List.range n).map fun i => s!"See [w{i}] here.\n\n") ++
    String.join ((List.range n).map fun i => s!"[w{i}]: https://example.org/{i}\n")

/-- An invented palette entry coloured over `n` paragraphs, one run each. -/
def colouredRuns (n : Nat) (name : String) (c : Ir.Color) : Ir.Doc :=
  { palette := { entries := #[((.color name), c)] }
    body := (List.range n).toArray.map fun i =>
      Ir.Block.para #[.colored c (some (.color name)) #[.text s!"w{i}"]] }

/-- `size` invented bytes: words with seeded noise, so the compressor meets literals and matches. -/
def flateInput (size : Nat) : ByteArray := Id.run do
  let words := #["orbit ", "radius ", "invented ", "step ", "lattice ", "placeholder "]
  let mut out := ByteArray.emptyWithCapacity (size + 16)
  let mut seed : UInt64 := 731
  for _ in [0:size] do
    if out.size ≥ size then break
    seed := seed ^^^ (seed >>> 12)
    seed := seed ^^^ (seed <<< 25)
    seed := seed ^^^ (seed >>> 27)
    let r := (seed * 2685821657736338717) >>> 40
    if r % 4 == 0 then out := out.push (r >>> 8).toUInt8
    else out := out ++ (words[(r % 6).toNat]?.getD "").toUTF8
  return out.extract 0 size

/-- Its bytes, behind a call the compiler neither inlines nor shares with another run's. -/
@[noinline] def perRun (_ : Unit) (b : ByteArray) : ByteArray := b

/-- Adler-32 as RFC 1950 §8.2 states it, one modulo per byte. -/
def adlerSpec (data : ByteArray) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in data do
    a := (a + x.toNat) % 65521
    b := (b + a) % 65521
  return b * 65536 + a

def main (args : List String) : IO UInt32 := do
  let n := ((args.head?).bind (·.toNat?)).getD 5
  if n == 0 then die "runs must be positive"
  for s in [600, 2400] do
    let doc := sameTitled s
    if doc.body.isEmpty then die "the same-titled article elaborated to nothing"
    timeRuns n "anchors" s fun _ =>
      ((HtmlDoc.emit {} doc).1.splitOn s!"id=\"topic-{s}\"").length == 2
  for s in [600, 2400] do
    let doc := sameTitledDeck s
    if doc.body.isEmpty then die "the same-titled deck elaborated to nothing"
    timeRuns n "frames" s fun _ =>
      ((HtmlDoc.emit {} doc).1.splitOn s!"aria-label=\"Topic ({s})\"").length == 2
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
  for s in [2000, 8000] do
    let src := referenced s
    timeRuns n "references" s fun _ =>
      ((Md.read "t.md" src).1.filter (· matches .ctrl "href" _)).size == s
  for s in [20000, 80000] do
    let doc := colouredRuns s "dk" { r := 0x10, g := 0x10, b := 0x10 }
    timeRuns n "legible" s fun _ => (Contrast.docDiags doc).isEmpty
  for s in [6000, 24000] do
    let doc := colouredRuns s "washed" { r := 0x88, g := 0x88, b := 0x88 }
    timeRuns n "failing" s fun _ =>
      ((Contrast.docDiags doc).filter (·.severity == .warning)).size == 1
  for s in [100000, 400000] do
    let arr := ("[" ++ String.join (List.replicate s "1 ") ++ "]").toUTF8
    let dict := ("<<" ++ String.join ((List.range s).map fun i => s!"/K{i} 1 ") ++ ">>").toUTF8
    timeRuns n "arrays" s fun _ => match PdfRead.parseVal arr 0 with
      | .ok (.arr xs, _) => xs.size == s
      | _ => false
    timeRuns n "dictionaries" s fun _ => match PdfRead.parseVal dict 0 with
      | .ok (.dict es, _) => es.size == s
      | _ => false
  for s in [1048576, 4194304] do
    let raw := flateInput s
    let sum := adlerSpec raw
    timeRuns n "adler32" s fun _ => Flate.adler32 raw == sum
    let packed := Flate.deflate raw
    unless (match Flate.inflate packed s with | .ok b => b == raw | .error _ => false) do
      die s!"inflate did not give {s} bytes back"
    timeRuns n "deflate" s fun u => Flate.deflate (perRun u raw) == packed
    timeRuns n "inflate" s fun u => match Flate.inflate (perRun u packed) s with
      | .ok b => b == raw
      | .error _ => false
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
