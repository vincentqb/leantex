/-
The raster judge the picture oracles share: a tool runner reporting a missing tool as `none`,
the grey raster `pdftoppm -gray` writes, Playwright's Chrome binaries, and ImageMagick's DSSIM at
the calibrated scale and tolerance.
-/
import scripts.ToolDump

def runTool (cmd : String) (args : Array String) : IO (Option IO.Process.Output) := do
  try
    pure (some (← IO.Process.output { cmd, args }))
  catch _ => pure none

/-- A grayscale raster: width, height, one byte per pixel, 0 black; `pdftoppm -gray`'s binary PGM. -/
structure Gray where
  w : Nat
  h : Nat
  px : ByteArray
deriving Inhabited

/-- The pixel at `(x, y)`, white outside the raster. -/
def Gray.at (g : Gray) (x y : Nat) : Nat :=
  if x < g.w && y < g.h then (g.px.get! (y * g.w + x)).toNat else 255

/-- A binary PGM (`P5`, maximum 255) as `pdftoppm -gray` writes it. -/
def Gray.parse (b : ByteArray) : Option Gray := Id.run do
  let isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9
  let mut fields : Array String := #[]
  let mut cur := ""
  let mut i := 0
  for _ in [0:b.size + 1] do
    if fields.size == 4 then break
    if h : i < b.size then
      let c := b[i]
      i := i + 1
      if isWs c then
        unless cur.isEmpty do
          fields := fields.push cur
          cur := ""
      else cur := cur.push (Char.ofNat c.toNat)
    else break
  match fields.toList with
  | ["P5", ws, hs, "255"] =>
    match ws.toNat?, hs.toNat? with
    | some w, some h =>
      if i + w * h ≤ b.size && w > 0 && h > 0 then
        return some { w, h, px := b.extract i (i + w * h) }
      else return none
    | _, _ => return none
  | _ => return none

/-- The raster judgement's resolution, for Poppler, PDFium and pdf.js alike. -/
def rasterDpi : Nat := 100

/-- The DSSIM a browser's page may stand from Poppler's and still pass: above the corpus's
largest conforming distance (pdf.js, 0.030) and below the nearest negative case (a page
rolled down one line, 0.043). -/
def dssimTolerance : Float := 0.035

/-- The Chrome binaries to try: `LEANTEX_CHROME`, then each Playwright-cached
`chromium-*/chrome-linux64/chrome`, newest first, the full browser whose viewer is
PDFium. -/
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

/-- `WxH` of a PNG, by `magick identify`. -/
def pngGeometry (png : String) : IO (Option String) := do
  let some out ← runTool "magick" #["identify", "-format", "%wx%h", png] | return none
  if out.exitCode != 0 then return none
  return some out.stdout.trimAscii.toString

/-- The scale both rasters are compared at, a quarter of `rasterDpi`, where glyphs read as
the grey they set and what remains is where ink lies. -/
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

