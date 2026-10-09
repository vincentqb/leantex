/-
A PDF figure's two web faces against the page itself. Run from the
repository root:

  lake build ScriptsModules && lake env lean --run scripts/pdffig-diff.lean --report
  lake env lean --run scripts/pdffig-diff.lean --selftest

The never-worse report for the PDF figure importer. Each figure is a
committed pdf-native fixture (testdata/pdf-native, invented, made by the
tool the importer meets — lualatex, cairo, the engine's writer — or by
hand in matplotlib's dialect). Its reference is Poppler's raster of the
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
-/
import LeanTex
import scripts.RasterJudge

open LeanTex.Core LeanTex.Cli

namespace PdfFigDiff

def dir : String := "testdata/pdf-native"

/-- The fixtures the report reads, in a fixed order. -/
def fixtures : Array String :=
  #["cairo-chart.pdf", "leantex-strokes.pdf", "lualatex-shade.pdf", "lualatex-text.pdf",
    "matplotlib-dialect.pdf"]

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

end PdfFigDiff

open PdfFigDiff in
def main (args : List String) : IO UInt32 := do
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
