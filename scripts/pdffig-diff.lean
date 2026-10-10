/-
A PDF figure's two web faces against the page itself. Run from the
repository root:

  lake build ScriptsModules && lake env lean --run scripts/pdffig-diff.lean --report
  lake env lean --run scripts/pdffig-diff.lean --selftest

The never-worse report for the PDF figure importer. Each figure is a
committed pdf-native fixture (testdata/pdf-native, invented, made by the
tool the importer meets — lualatex, cairo, the engine's writer — or by
hand in matplotlib's dialect or a print workflow's CMYK one). Its reference is Poppler's raster of the
page (`pdftoppm` at `rasterDpi`). Its two web faces are the engine's own
drawing (`PdfFaces.svgOf` of `PdfGfx.importPage`) and the converter's
(`pdftocairo -svg`), each a standalone SVG Chromium screenshots at the
same scale. Each is held to the reference by ImageMagick's DSSIM at
`dssimScale`, and the native face passes when

  d(native, ref) ≤ d(converter, ref) + ε

with ε the distance between two rasterizations of the one reference —
Poppler's and Cairo's own (`pdftocairo -png`) — which is how far two
conforming renderers of the same page already stand apart. Text regions
are not separated: the native face draws a figure's glyphs from its own
font programs, as Poppler does, so faces do not differ by design here.

`--selftest` injects a mutant into the native face only — its glyphs
dropped, the drawing shifted by a tenth of its width, its fills turned
grey — and fails unless every mutant lands worse than never-worse while
its unmutated face stays within. A report, never a gate: it needs
Poppler, Chromium and ImageMagick, and a missing tool fails the run with
its name.

  lake env lean --run scripts/pdffig-diff.lean --cmyk [--selftest]

`--cmyk` measures the importer's device CMYK preview (`PdfGfx.cmykRgb`)
against Poppler's: a probe page of device CMYK patches — the cube's
sixteen corners, then the lattice {0.2, 0.5, 0.8}⁴ — rasterized by
`pdftoppm` at one pixel per point and read at each patch's centre. A
corner must be the table's colour exactly (`PdfGfx.cmykCorners` is this
measurement), and a lattice colour within one step of a byte per channel
of the interpolation, which is the rounding apart of two evaluations of
one multilinear blend. `--cmyk --selftest` moves the measured pixels and
fails unless the judge catches a corner one step off and a lattice colour
two steps off, and passes a lattice colour one step off. Poppler only.
-/
import LeanTex
import scripts.RasterJudge

open LeanTex.Core LeanTex.Cli

namespace PdfFigDiff

def dir : String := "testdata/pdf-native"

/-- The fixtures the report reads, in a fixed order. -/
def fixtures : Array String :=
  #["cairo-chart.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf", "lualatex-text.pdf",
    "matplotlib-dialect.pdf", "print-dialect.pdf"]

def tool (cmd : String) (args : Array String) : IO IO.Process.Output := do
  match ← runTool cmd args with
  | some out =>
    if out.exitCode == 0 then return out
    throw (IO.userError s!"pdffig-diff: {cmd} exited {out.exitCode}: {out.stderr}")
  | none => throw (IO.userError s!"pdffig-diff: {cmd} is not on PATH")

/-- Poppler's raster of page 1: the reference. -/
def popplerPng (work : System.FilePath) (stem : String) (pdf : System.FilePath) : IO String := do
  let _ ← tool "pdftoppm" #["-r", toString rasterDpi, "-png", "-singlefile", "-f", "1", "-l", "1",
    pdf.toString, (work / s!"{stem}-ref").toString]
  return (work / s!"{stem}-ref.png").toString

/-- Cairo's raster of page 1: the second rendering of the reference ε reads. -/
def cairoPng (work : System.FilePath) (stem : String) (pdf : System.FilePath) : IO String := do
  let _ ← tool "pdftocairo" #["-png", "-r", toString rasterDpi, "-singlefile", "-f", "1", "-l", "1",
    pdf.toString, (work / s!"{stem}-cairo").toString]
  return (work / s!"{stem}-cairo.png").toString

/-- A standalone SVG screenshot by Chromium at the raster scale, its window
the figure's box in CSS pixels. -/
def chromePng (chrome : String) (work : System.FilePath) (stem : String) (box : Gfx.Box)
    (svg : ByteArray) : IO String := do
  let file := work / s!"{stem}.svg"
  IO.FS.writeBinFile file svg
  let ((x0, y0), (x1, y1)) := box
  let cssPx (d : Dim.Sp) : Nat := ((d.toNat * 96 + 72 * 65536 - 1) / (72 * 65536))
  let out := (work / s!"{stem}-svg.png").toString
  let _ ← tool chrome #["--headless=new", "--disable-gpu", "--no-sandbox", "--hide-scrollbars",
    s!"--force-device-scale-factor={(rasterDpi.toFloat / 96.0)}",
    s!"--window-size={cssPx (x1 - x0)},{cssPx (y1 - y0)}", s!"--screenshot={out}",
    s!"file://{file}"]
  return out

/-- The converter's face of page 1: `pdftocairo -svg`. -/
def converterSvg (work : System.FilePath) (stem : String) (pdf : System.FilePath) : IO ByteArray := do
  let out := work / s!"{stem}-converter.svg"
  let _ ← tool "pdftocairo" #["-svg", "-f", "1", "-l", "1", pdf.toString, out.toString]
  IO.FS.readBinFile out

/-- A face's distance from the reference. -/
def distance (work : System.FilePath) (tag : String) (candidate reference : String) : IO Float := do
  match ← dssimAgainst work tag candidate reference with
  | some d => return d
  | none => throw (IO.userError s!"pdffig-diff: no DSSIM for {tag} (is ImageMagick on PATH?)")

/-- What a fixture measures: its native face's, its converter face's and
the two reference rasters' distances. -/
structure Measure where
  native : Float
  converter : Float
  eps : Float

def Measure.ok (m : Measure) : Bool := m.native ≤ m.converter + m.eps

/-- The selftest's mutants of a native figure, each one a reader sees. -/
def mutants : Array (String × (Gfx.Figure Gfx.Run → Gfx.Figure Gfx.Run)) :=
  #[("glyphs dropped", fun fig => { fig with outlines := fig.outlines.map fun _ => #[] }),
    ("shifted a tenth of its width", fun fig =>
      let w := fig.box.2.1 - fig.box.1.1
      { fig with nodes := #[.group ⟨1, 0, 0, 1, (w / 10 : Int), 0⟩ #[] Gfx.Alpha.opaque fig.nodes] }),
    ("fills turned grey", fun fig => fig.recolor (fun _ => { r := 128, g := 128, b := 128 }) id)]

def fmt (f : Float) : String := (toString f).take 7 |>.toString

def measure (chrome : String) (work : System.FilePath) (stem : String) (pdf : System.FilePath)
    (fig : Gfx.Figure Gfx.Run) (ref eps : Float × String) : IO Measure := do
  let native ← chromePng chrome work s!"{stem}-native" fig.box (PdfFaces.svgOf fig)
  let conv ← chromePng chrome work s!"{stem}-conv" fig.box (← converterSvg work stem pdf)
  return { native := ← distance work s!"{stem}-n" native ref.2,
           converter := ← distance work s!"{stem}-c" conv ref.2, eps := eps.1 }

/-- A component in tenths, as a PDF number. -/
def tenths (t : Nat) : String := if t ≥ 10 then "1" else s!"0.{t}"

/-- The CMYK probe's patches, components in tenths: the cube's sixteen
corners, index `8c + 4m + 2y + k` as `PdfGfx.cmykCorners` holds them,
then every colour of the lattice {0.2, 0.5, 0.8}⁴. -/
def cmykPatches : Array (Nat × Nat × Nat × Nat) := Id.run do
  let mut ps : Array (Nat × Nat × Nat × Nat) := #[]
  for i in [0:16] do
    let bit (j : Nat) : Nat := if (i / 2 ^ (3 - j)) % 2 == 1 then 10 else 0
    ps := ps.push (bit 0, bit 1, bit 2, bit 3)
  let lattice : Array Nat := #[2, 5, 8]
  for c in lattice do
    for m in lattice do
      for y in lattice do
        for k in lattice do
          ps := ps.push (c, m, y, k)
  return ps

/-- The probe's grid: patches of `patchSide` points, `patchColumns` to a
row from the top left. -/
def patchColumns : Nat := 16
def patchSide : Nat := 10

def patchRows : Nat := (cmykPatches.size + patchColumns - 1) / patchColumns

/-- A number as an xref offset: ten digits. -/
def pad10 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (10 - s.length) ++ s

/-- The probe page: each patch filled in device CMYK, nothing else. -/
def cmykProbe : ByteArray := Id.run do
  let height := patchRows * patchSide
  let mut ops := ""
  for p in [0:cmykPatches.size] do
    let (c, m, y, k) := cmykPatches[p]?.getD (0, 0, 0, 0)
    let x := (p % patchColumns) * patchSide
    let bottom := height - (p / patchColumns + 1) * patchSide
    ops := ops ++ s!"{tenths c} {tenths m} {tenths y} {tenths k} k {x} {bottom} {patchSide} {patchSide} re f\n"
  let objs : Array String := #["<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {patchColumns * patchSide} {height}] \
/Resources << >> /Contents 4 0 R >>",
    s!"<< /Length {ops.utf8ByteSize} >>\nstream\n{ops}endstream"]
  let mut out := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for i in [0:objs.size] do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{objs[i]?.getD ""}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for o in offsets do
    out := out ++ s!"{pad10 o} 00000 n \n"
  out := out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n"
  return out.toUTF8

/-- A binary PPM's width and samples, as `pdftoppm` writes one: `P6`, then
width, height and 255, each ended by one white-space byte. -/
def readPpm (b : ByteArray) : Option (Nat × ByteArray) := Id.run do
  let mut fields : Array Nat := #[]
  let mut cur : Option Nat := none
  let mut start : Option Nat := none
  for i in [2:min b.size 64] do
    if start.isNone then
      let c := b[i]!
      if c ≥ 48 && c ≤ 57 then
        cur := some (cur.getD 0 * 10 + (c.toNat - 48))
      else if let some n := cur then
        fields := fields.push n
        cur := none
        if fields.size == 3 then start := some (i + 1)
  let some s := start | return none
  let w := fields[0]!
  let h := fields[1]!
  if b.size < 2 || b[0]! != 80 || b[1]! != 54 || fields[2]! != 255 || s + w * h * 3 > b.size then
    return none
  return some (w, b.extract s (s + w * h * 3))

/-- A patch's centre pixel in a raster `w` pixels wide at one pixel per point. -/
def patchPixel (w : Nat) (px : ByteArray) (p : Nat) : Option (UInt8 × UInt8 × UInt8) :=
  let x := (p % patchColumns) * patchSide + patchSide / 2
  let y := (p / patchColumns) * patchSide + patchSide / 2
  let o := (y * w + x) * 3
  if o + 2 < px.size then some (px[o]!, px[o + 1]!, px[o + 2]!) else none

def step (a b : UInt8) : Nat := if a ≥ b then (a - b).toNat else (b - a).toNat

/-- A patch's name: its components. -/
def patchName (p : Nat) : String :=
  let (c, m, y, k) := cmykPatches[p]?.getD (0, 0, 0, 0)
  s!"{tenths c} {tenths m} {tenths y} {tenths k}"

/-- The engine's preview of a patch's colour. -/
def preview (p : Nat) : UInt8 × UInt8 × UInt8 :=
  let (c, m, y, k) := cmykPatches[p]?.getD (0, 0, 0, 0)
  PdfGfx.cmykRgb ((c : Rat) / 10) ((m : Rat) / 10) ((y : Rat) / 10) ((k : Rat) / 10)

/-- How many steps of a byte a pixel stands from a patch's preview, on its
farthest channel. -/
def stepsOff (p : Nat) (px : UInt8 × UInt8 × UInt8) : Nat :=
  let (wr, wg, wb) := preview p
  let (r, g, b) := px
  max (step r wr) (max (step g wg) (step b wb))

/-- **The judge of the CMYK preview**: the patches where the measured pixel
stands from `PdfGfx.cmykRgb` by more than its bound — none for a corner,
whose colour the table holds as measured, one step of a byte per channel
for a lattice colour. -/
def cmykOffences (pixel : Nat → Option (UInt8 × UInt8 × UInt8)) : Array String := Id.run do
  let mut out : Array String := #[]
  for p in [0:cmykPatches.size] do
    let bound := if p < 16 then 0 else 1
    match pixel p with
    | none => out := out.push s!"{patchName p}: no pixel"
    | some (r, g, b) =>
      let d := stepsOff p (r, g, b)
      if d > bound then
        let (wr, wg, wb) := preview p
        out := out.push s!"{patchName p}: Poppler ({r}, {g}, {b}), preview ({wr}, {wg}, {wb}), \
{d} steps over a bound of {bound}"
  return out

/-- The selftest's moves: which patch, how many steps its measured red
channel is put from the preview's, and whether the judge must catch it. -/
def cmykMoves : Array (String × Nat × Nat × Bool) :=
  #[("a corner one step off", 1, 1, true), ("a lattice colour two steps off", 16, 2, true),
    ("a lattice colour one step off", 40, 1, false)]

def cmykMain (selftest : Bool) : IO UInt32 := do
  let work ← IO.FS.createTempDir
  let pdf := work / "cmyk.pdf"
  IO.FS.writeBinFile pdf cmykProbe
  let _ ← tool "pdftoppm" #["-r", "72", "-singlefile", "-f", "1", "-l", "1", pdf.toString,
    (work / "cmyk").toString]
  let version := ((← runTool "pdftoppm" #["-v"]).map fun out => (out.stderr.splitOn "\n").headD "").getD ""
  let some (w, px) := readPpm (← IO.FS.readBinFile (work / "cmyk.ppm")) |
    IO.eprintln "pdffig-diff: pdftoppm's raster of the CMYK probe is no binary PPM"; return 1
  IO.println s!"pdffig-diff --cmyk: {version}; 16 corners, {cmykPatches.size - 16} lattice colours"
  let pixel := patchPixel w px
  let offences := cmykOffences pixel
  for o in offences do IO.println s!"OFF     {o}"
  let mut corners := 0
  let mut lattice := 0
  for p in [0:cmykPatches.size] do
    if let some px := pixel p then
      if p < 16 then corners := max corners (stepsOff p px) else lattice := max lattice (stepsOff p px)
  IO.println s!"{if offences.isEmpty then "within" else "OFF   "}  corners at most {corners} step(s) \
from the table, lattice at most {lattice} from the preview"
  let mut failed := offences.size
  if selftest then
    for (what, patch, steps, caught) in cmykMoves do
      let off := steps.toUInt8
      let wr := (preview patch).1
      let moved : Nat → Option (UInt8 × UInt8 × UInt8) := fun p =>
        (pixel p).map fun (r, g, b) =>
          if p == patch then (if wr ≥ 128 then wr - off else wr + off, g, b) else (r, g, b)
      let flagged := (cmykOffences moved).size > offences.size
      let ok := flagged == caught && offences.isEmpty
      IO.println s!"{if ok then "held  " else "MISSED"}  {what}: {if flagged then "caught" else "passed"}"
      unless ok do failed := failed + 1
  IO.println s!"pdffig-diff: probe and raster under {work}"
  return if failed == 0 then 0 else 1

end PdfFigDiff

open PdfFigDiff in
def main (args : List String) : IO UInt32 := do
  if args.contains "--cmyk" then return ← cmykMain (args.contains "--selftest")
  let some (chrome, version) ← findChrome |
    IO.eprintln "pdffig-diff: no Chrome (LEANTEX_CHROME or Playwright's cache)"; return 2
  let work ← IO.FS.createTempDir
  IO.println s!"pdffig-diff: {version}; DSSIM at {dssimScale}, {rasterDpi} dpi"
  let mut failed := 0
  for name in fixtures do
    let pdf : System.FilePath := (← IO.FS.realPath (dir ++ "/" ++ name))
    let stem := (name.takeWhile (· != '.')).toString
    let imp ← match PdfGfx.importPage (← IO.FS.readBinFile pdf) with
      | .ok imp => pure imp
      | .error e => IO.eprintln s!"pdffig-diff: {name} does not import ({e})"; failed := failed + 1; continue
    let ref ← popplerPng work stem pdf
    let other ← cairoPng work stem pdf
    let eps ← distance work s!"{stem}-eps" other ref
    if args.contains "--selftest" then
      let base ← measure chrome work stem pdf imp.figure (0, ref) (eps, ref)
      for (what, mutate) in mutants do
        -- A mutant that leaves the face's bytes as they were (no glyphs to
        -- drop, no solid fill to grey) shows nothing, and is not run.
        let mutated := mutate imp.figure
        if PdfFaces.svgOf mutated == PdfFaces.svgOf imp.figure then
          IO.println s!"n/a     {name}, {what}: the face has nothing it changes"
          continue
        let m ← measure chrome work s!"{stem}-m" pdf mutated (0, ref) (eps, ref)
        let ok := base.ok && !m.ok
        IO.println s!"{if ok then "caught" else "MISSED"}  {name}, {what}: unmutated {fmt base.native}, \
mutant {fmt m.native}, converter {fmt m.converter}, ε {fmt eps}"
        unless ok do failed := failed + 1
    else
      let m ← measure chrome work stem pdf imp.figure (0, ref) (eps, ref)
      IO.println s!"{if m.ok then "within" else "WORSE "}  {name}: native {fmt m.native}, \
converter {fmt m.converter}, ε {fmt m.eps}"
      unless m.ok do failed := failed + 1
  IO.println s!"pdffig-diff: rasters under {work}"
  return if failed == 0 then 0 else 1
