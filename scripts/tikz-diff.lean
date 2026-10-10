/-
External picture differential: the engine's drawing of each invented probe
against LuaLaTeX's, as rasters. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/tikz-diff.lean              draw both, compare, report
  lake env lean --run scripts/tikz-diff.lean --selftest   the comparison over hand-made rasters

A report, never a gate: it needs a TeX installation and Poppler, and writes
only under `.lake/tikz-diff/`. Run it when touching the picture reader
(`Picture.lean`) or the vector model's emission. The probes are the
tikz-native tier's (`scripts/TikzProbes.lean`), invented; the reference sets
each in the standalone class with the libraries its keys belong to.

Each drawing is rasterized by `pdftoppm -gray` at one resolution and read at
three levels, each blind to something the next one sees:

  box    the ink's bounding box in pixels — blind to what stands inside it;
  pixel  the share of the union of ink whose gray differs by more than a
         quarter of the scale, the two boxes aligned at their top left
         corners — blind to differences under that threshold;
  exact  the cropped rasters' bytes — blind to nothing.

A label sets in each engine's own default face, so the pixel level counts
glyph differences too: the report is evidence for a reader, never a
verdict. The structural half — the drawing's geometry against the
reference's, read back from the PDF — waits on the PDF figure reader.
-/
import LeanTex
import scripts.TikzProbes

/-- A grayscale raster: width, height, one byte per pixel, 0 black. -/
structure Gray where
  w : Nat
  h : Nat
  px : ByteArray

/-- The pixel at `(x, y)`, white outside the raster. -/
def Gray.at (g : Gray) (x y : Nat) : Nat :=
  if x < g.w && y < g.h then (g.px.get! (y * g.w + x)).toNat else 255

/-- A binary PGM (`P5`, maximum 255), as `pdftoppm -gray` writes it: the
magic, the width, the height and the maximum as whitespace-separated
decimals, one whitespace byte, then the rows. -/
def parsePgm (b : ByteArray) : Option Gray := Id.run do
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

/-- The bounding box of the ink — pixels darker than three quarters of the
scale, so a hairline straddling two rows of pixels still counts — as
`(x0, y0, x1, y1)`, inclusive; `none` for a blank raster. -/
def inkBox (g : Gray) : Option (Nat × Nat × Nat × Nat) := Id.run do
  let mut box : Option (Nat × Nat × Nat × Nat) := none
  for y in [0:g.h] do
    for x in [0:g.w] do
      if g.at x y < 192 then
        box := some (match box with
          | none => (x, y, x, y)
          | some (x0, y0, x1, y1) => (min x0 x, min y0 y, max x1 x, max y1 y))
  return box

/-- The raster cropped to a box. -/
def crop (g : Gray) (box : Nat × Nat × Nat × Nat) : Gray := Id.run do
  let (x0, y0, x1, y1) := box
  let w := x1 + 1 - x0
  let h := y1 + 1 - y0
  let mut px := ByteArray.emptyWithCapacity (w * h)
  for y in [0:h] do
    for x in [0:w] do
      px := px.push (g.at (x0 + x) (y0 + y)).toUInt8
  return { w, h, px }

/-- The box level: the two inks' bounding boxes are the same size. -/
def boxSame (a b : Gray) : Bool :=
  match inkBox a, inkBox b with
  | some (ax0, ay0, ax1, ay1), some (bx0, by0, bx1, by1) =>
    ax1 - ax0 == bx1 - bx0 && ay1 - ay0 == by1 - by0
  | none, none => true
  | _, _ => false

/-- The pixel level over two cropped inks aligned at their top left
corners: of the pixels either inks (`inkBox`'s threshold), how many in a
thousand differ by more than a quarter of the gray scale. -/
def pixelDiff (a b : Gray) : Nat := Id.run do
  let w := max a.w b.w
  let h := max a.h b.h
  let mut union := 0
  let mut differ := 0
  for y in [0:h] do
    for x in [0:w] do
      let p := a.at x y
      let q := b.at x y
      if p < 192 || q < 192 then
        union := union + 1
        if (if p > q then p - q else q - p) > 64 then differ := differ + 1
  return if union == 0 then 0 else differ * 1000 / union

/-- The exact level: the same size and the same bytes. -/
def exactSame (a b : Gray) : Bool := a.w == b.w && a.h == b.h && a.px == b.px

/-- The reference document: the probe in the standalone class, with the
libraries its keys belong to, the palette entry the probes name, beamer's
`\alert` (its default alerted text is red; the standalone is no beamer, so
the name is undefined there, and the probe that groups statements under it
would stop the run), and the faces the engine resolves for a document that
declares none — set as the boundary sets them (`boundaryFonts`), so a
label's letters are the same letters in both drawings. -/
def referenceDoc (kind : ProbeKind) (body : String) : String :=
  let pre := "\\documentclass[border=0pt]{standalone}\n\\usepackage{tikz}\n" ++
    "\\usetikzlibrary{arrows.meta, shapes.geometric, fit, decorations.pathreplacing, calc}\n" ++
    "\\usepackage{tikz-cd}\n\\usepackage{fontspec}\n\\setmainfont{DejaVu Sans}\n" ++
    "\\usepackage{unicode-math}\n\\setmathfont{TeX Gyre DejaVu Math}\n" ++
    "\\definecolor{grid}{HTML}{2A6F4E}\n\\providecommand{\\alert}[1]{{\\color{red}#1}}\n" ++
    "\\begin{document}\n"
  match kind with
  | .picture => pre ++ "\\begin{tikzpicture}\n" ++ body ++ "\n\\end{tikzpicture}\n\\end{document}\n"
  | .cd => pre ++ "$\\begin{tikzcd}" ++ body ++ "\\end{tikzcd}$\n\\end{document}\n"

/-- The engine's document: the tier's own, loading the libraries the
reference loads — arrows.meta changes the head `->` draws in both — with no
page number to ink. -/
def nativeDoc (kind : ProbeKind) (body : String) : String :=
  (probeDoc kind body).replace "\\begin{document}" ("\\usepackage{tikz}\n" ++
    "\\usetikzlibrary{arrows.meta, shapes.geometric, fit, decorations.pathreplacing, calc}\n" ++
    "\\pagestyle{empty}\n\\begin{document}")

def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    return out.exitCode == 0
  catch _ => return false

/-- One drawing's raster: the PDF at 300 dpi, gray, cropped to its ink. -/
def rasterOf (dir : System.FilePath) (stem : String) : IO (Option Gray) := do
  unless ← run "pdftoppm" #["-r", "300", "-gray", "-f", "1", "-l", "1", stem ++ ".pdf", stem] dir do
    return none
  let path := dir / (stem ++ "-1.pgm")
  unless ← path.pathExists do return none
  let some g := parsePgm (← IO.FS.readBinFile path) | return none
  return (inkBox g).map (crop g)

def report : IO UInt32 := do
  let dir : System.FilePath := ".lake/tikz-diff"
  IO.FS.createDirAll dir
  let leantex ← IO.FS.realPath ".lake/build/bin/leantex"
  IO.println "item\tnative px\treference px\tbox\tpixel ‰\texact"
  for (item, kind, body) in probes do
    IO.FS.writeFile (dir / s!"{item}-native.tex") (nativeDoc kind body)
    IO.FS.writeFile (dir / s!"{item}-ref.tex") (referenceDoc kind body)
    let nOk ← run leantex.toString #[s!"{item}-native.tex", "-o", s!"{item}-native.pdf", "-q"] dir
    let rOk ← run "lualatex" #["-interaction=nonstopmode", "-halt-on-error", s!"{item}-ref.tex"] dir
    let n ← if nOk then rasterOf dir s!"{item}-native" else pure none
    let r ← if rOk then rasterOf dir s!"{item}-ref" else pure none
    match n, r with
    | some a, some b =>
      IO.println s!"{item}\t{a.w}x{a.h}\t{b.w}x{b.h}\t{if boxSame a b then "same" else "differs"}\t\
{pixelDiff a b}\t{if exactSame a b then "same" else "differs"}"
    | none, _ => IO.println s!"{item}\tthe engine drew no ink or did not run"
    | _, none => IO.println s!"{item}\tthe reference drew no ink or did not run"
  return 0

/-- A raster from rows of gray values. -/
def ofRows (rows : List (List Nat)) : Gray :=
  let h := rows.length
  let w := (rows.head?.map (·.length)).getD 0
  { w, h, px := ByteArray.mk (rows.flatten.map (·.toUInt8)).toArray }

def selftest : IO UInt32 := do
  let mut failed := 0
  let check (name : String) (ok : Bool) : IO Nat := do
    unless ok do IO.eprintln s!"tikz-diff selftest: {name}"
    return if ok then 0 else 1
  -- The box level is blind to what stands inside the box; the pixel level
  -- sees it.
  let corners := ofRows [[0, 255, 255, 255], [255, 255, 255, 255], [255, 255, 255, 255],
    [255, 255, 255, 0]]
  let inner := ofRows [[0, 255, 255, 255], [255, 0, 255, 255], [255, 255, 255, 255],
    [255, 255, 255, 0]]
  failed := failed + (← check "box: blind to the inside of the box" (boxSame corners inner))
  failed := failed + (← check "pixel: sees the inside of the box" (pixelDiff corners inner > 0))
  -- The pixel level is blind to a difference under its threshold; the exact
  -- level sees it.
  let dark := ofRows [[0, 255], [255, 0]]
  let lighter := ofRows [[40, 255], [255, 0]]
  failed := failed + (← check "pixel: blind to a difference under a quarter of the scale"
    (pixelDiff dark lighter == 0))
  failed := failed + (← check "exact: sees it" (!exactSame dark lighter))
  -- Each level sees what its own reading is about.
  let shifted := ofRows [[255, 0], [0, 255]]
  failed := failed + (← check "pixel: a moved mark differs" (pixelDiff dark shifted == 1000))
  let wide := ofRows [[0, 255, 0]]
  failed := failed + (← check "box: a wider ink differs" (!boxSame dark wide))
  -- The reader.
  let pgm := "P5\n2 2\n255\n".toUTF8 ++ ByteArray.mk #[0, 255, 255, 0]
  failed := failed + (← check "pgm: reads a raster pdftoppm writes"
    ((parsePgm pgm).map (fun g => g.w == 2 && g.h == 2 && g.px == ByteArray.mk #[0, 255, 255, 0])
      == some true))
  failed := failed + (← check "pgm: refuses a short one"
    (parsePgm ("P5\n2 2\n255\n".toUTF8 ++ ByteArray.mk #[0, 255])).isNone)
  failed := failed + (← check "pgm: refuses another format" (parsePgm "P6\n1 1\n255\nabc".toUTF8).isNone)
  failed := failed + (← check "ink: a blank raster has none" (inkBox (ofRows [[255, 255]])).isNone)
  failed := failed + (← check "crop: to the ink alone"
    ((inkBox inner).map (fun b => (crop inner b).w == 4 && (crop inner b).h == 4) == some true))
  if failed == 0 then IO.println "tikz-diff selftest: all passed"
  return if failed == 0 then 0 else 1

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--selftest"] => selftest
  | [] => report
  | _ => do
    IO.eprintln "usage: tikz-diff [--selftest]"
    return 2
