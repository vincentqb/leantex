/-
The raster judge the picture oracles share: a tool run that reports a
missing tool as `none`, the Chrome binaries Playwright's cache holds,
ImageMagick's DSSIM at the scale and tolerance pdf-oracles calibrated,
and its numbers parsed back. A library: `scripts/pdf-oracles.lean` and
`scripts/gfx-diff.lean` import it; it runs nothing itself.
-/

def runTool (cmd : String) (args : Array String) : IO (Option IO.Process.Output) := do
  try
    pure (some (← IO.Process.output { cmd, args }))
  catch _ => pure none

/-- The raster judgement's resolution, for Poppler, PDFium and pdf.js alike. -/
def rasterDpi : Nat := 100

/-- The DSSIM (ImageMagick `compare -metric DSSIM`, alpha dropped, both
rasters brought to `dssimScale`) a browser's page may stand from Poppler's
and still pass. Calibrated on the 2026-09-22 run over the 142 corpus pages
(the run record carries every cell): PDFium at most 0.026 (a dense text
page, `valign` p5) and pdf.js at most 0.030 (`deck` p8) against Poppler;
the negative cases the same record keeps lie above — a page against a
different page of the same deck 0.085, a text page against itself rolled
down one 12 pt line 0.043. The window is narrow, `[0.030, 0.043]`, and the
number sits in its middle; a wider one needs a metric that reads ink
positions, not pixels. Not identity: Ghostscript's fast-colour raster
against Poppler measures 0.002 on the image page and is meant to. -/
def dssimTolerance : Float := 0.035

/-- The Chrome binaries to try: `LEANTEX_CHROME` first, then every
`~/.cache/ms-playwright/chromium-*/chrome-linux64/chrome`, newest revision
first — the full browser, whose viewer is PDFium; the `headless_shell`
beside it downloads a PDF instead of showing it. Nothing is installed. -/
def chromeCandidates : IO (Array String) := do
  let mut out : Array String := #[]
  if let some p ← IO.getEnv "LEANTEX_CHROME" then out := out.push p
  if let some home ← IO.getEnv "HOME" then
    let pw : System.FilePath := home / ".cache" / "ms-playwright"
    if ← pw.isDir then
      let revs := ((← pw.readDir).filter (·.fileName.startsWith "chromium-")).qsort
        (·.fileName > ·.fileName)
      for e in revs do
        let c := e.path / "chrome-linux64" / "chrome"
        if ← c.pathExists then out := out.push c.toString
  return out

/-- The first Chrome that reports a version, with it. -/
def findChrome : IO (Option (String × String)) := do
  for c in ← chromeCandidates do
    if let some out ← runTool c #["--version"] then
      if out.exitCode == 0 then
        return some (c, ((out.stdout.trimAscii.toString.splitOn "\n").headD "").trimAscii.toString)
  return none

/-- A decimal as ImageMagick prints it (`0.0197563`, `1.2e-05`), or none. -/
def parseFloat (s : String) : Option Float := do
  let s := s.trimAscii.toString
  let (mant, exp) := match s.splitOn "e" with
    | [m, e] => (m, e.toInt?.getD 0)
    | _ => (s, 0)
  let neg := mant.startsWith "-"
  let mant := if neg then (mant.drop 1).toString else mant
  let (ip, fp) := match mant.splitOn "." with
    | [i, f] => (i, f)
    | [i] => (i, "")
    | _ => ("", "")
  let i ← if ip.isEmpty then some 0 else ip.toNat?
  let f ← if fp.isEmpty then some 0 else fp.toNat?
  let v : Float := Float.ofNat i + Float.ofNat f / Float.ofNat (10 ^ fp.length)
  let v := if exp ≥ 0 then v * Float.ofNat (10 ^ exp.toNat) else v / Float.ofNat (10 ^ (-exp).toNat)
  return if neg then -v else v

/-- `WxH` of a PNG, by `magick identify`. -/
def pngGeometry (png : String) : IO (Option String) := do
  let some out ← runTool "magick" #["identify", "-format", "%wx%h", png] | return none
  if out.exitCode != 0 then return none
  return some out.stdout.trimAscii.toString

/-- The scale both rasters are brought to before they are compared: a
quarter of `rasterDpi`, 25 dpi. At full resolution the distance between
two conforming renderers of one dense text page (glyph anti-aliasing, a
one-pixel registration offset) exceeds the distance between two different
pages; at a quarter the glyphs are the grey they set, and what remains is
where ink lies. -/
def dssimScale : String := "25%"

/-- The candidate with alpha dropped, resampled to the reference's geometry
and then to `dssimScale`; the reference the same way; then `compare -metric
DSSIM`, whose parenthesised number is the normalised distance. -/
def dssimAgainst (dir : System.FilePath) (tag : String) (candidate reference : String) :
    IO (Option Float) := do
  let some geom ← pngGeometry reference | return none
  let a := (dir / s!"{tag}-a.png").toString
  let b := (dir / s!"{tag}-b.png").toString
  let some ca ← runTool "magick"
    #[candidate, "-alpha", "off", "-resize", geom ++ "!", "-resize", dssimScale, a] | return none
  if ca.exitCode != 0 then return none
  let some cb ← runTool "magick" #[reference, "-alpha", "off", "-resize", dssimScale, b] | return none
  if cb.exitCode != 0 then return none
  let some cmp ← runTool "magick" #["compare", "-metric", "DSSIM", a, b, "null:"] | return none
  let text := cmp.stderr ++ cmp.stdout
  match (text.splitOn "(").drop 1 with
  | inner :: _ => return parseFloat ((inner.splitOn ")").headD "")
  | [] => return parseFloat text

