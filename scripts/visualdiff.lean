/-
Whether two PDFs or two HTML pages differ visibly at stated viewing conditions, a report that never gates:
  lake build visualdiff && .lake/build/bin/visualdiff [--heatmap <dir>] <a> <b>
  .lake/build/bin/visualdiff --selftest
-/
import LeanTex
import scripts.Playwright

open LeanTex.Core

namespace VisualDiff

/-- `x` with `d` decimals, rounded to the nearest or, with `down`, down. -/
def fixed (x : Float) (d : Nat) (down : Bool := false) : String :=
  let scaled := x * (10 ^ d).toFloat
  let n := (if down then scaled.floor else scaled.round).toUInt64.toNat
  let frac := toString (n % 10 ^ d)
  if d == 0 then toString n
  else s!"{n / 10 ^ d}." ++ String.ofList (List.replicate (d - frac.length) '0') ++ frac

/-! ## The viewing model -/

def pi : Float := 3.141592653589793

/-- One arcminute, in radians. -/
def arcmin : Float := pi / 10800

/-- The detail normal (20/20) vision resolves: one arcminute. -/
def acuity : Float := arcmin

/-- Raster samples across the acuity: four, so the eye's point spread and a thin feature's peak
are resolved whatever their phase on the grid. -/
def samplesPerAcuity : Float := 4

/-- One just-noticeable difference in OKLab, `Oklab.okJnd` at unit scale. -/
def jnd : Float := Oklab.okJnd.toFloat / 1e18

/-- A medium as the eye meets it: its viewing distance, one judged sample's width on it, the
length its reach rounds the acuity up to, its black as a fraction of its white, the samples a page
pixel spans along each axis, and its header fields. -/
structure Medium where
  name : String
  distanceMm : Float
  sampleMm : Float
  stepMm : Float
  black : Float
  split : Nat
  detail : String

def Medium.acuityMm (m : Medium) : Float := m.distanceMm * Float.tan acuity

def Medium.acuitySamples (m : Medium) : Float := m.acuityMm / m.sampleMm

/-- The eye's point spread, a Gaussian whose full width at half maximum is the acuity, in samples. -/
def Medium.sigma (m : Medium) : Float := m.acuitySamples / (2 * Float.sqrt (2 * Float.log 2))

/-- The acuity spot's area, a disc as wide as the acuity, in samples. -/
def Medium.spotSamples (m : Medium) : Float := pi / 4 * m.acuitySamples * m.acuitySamples

/-- How far a sample may move and still match, in samples: the acuity, or the medium's step where
that is coarser. -/
def Medium.reach (m : Medium) : Float := max m.acuityMm m.stepMm / m.sampleMm

/-- A printed page is read at 35 cm. -/
def printDistanceMm : Float := 350

/-- Printed black reflects about 2% of what paper white does, an optical density near 1.7. -/
def printBlack : Float := 0.02

/-- The resolution pages are judged at, `samplesPerAcuity` samples across the acuity on paper. -/
def printDpi : Nat :=
  (25.4 * samplesPerAcuity / (printDistanceMm * Float.tan acuity)).round.toUInt64.toNat

/-- Each judged sample is `printSupersample²` pixels averaged in linear light, diluting the
gamma-space antialiasing the rasterizer composites. -/
def printSupersample : Nat := 2

/-- Pages are first drawn at `printDpi / printSplit` to find where they differ. -/
def printSplit : Nat := 2

def print : Medium :=
  { name := "print", distanceMm := printDistanceMm, sampleMm := 25.4 / printDpi.toFloat,
    stepMm := 0, black := printBlack, split := printSplit
    detail := s!"dpi={printDpi} supersample={printSupersample} find_dpi={printDpi / printSplit}" }

/-- A laptop screen is read at arm's length, 60 cm. -/
def screenDistanceMm : Float := 600

/-- The panel: 15.6 inches across, 1920 × 1080 CSS pixels drawn at device pixel ratio 2. -/
def panelDiagonalIn : Float := 15.6
def viewportW : Nat := 1920
def viewportH : Nat := 1080
def panelDpr : Nat := 2

/-- One CSS pixel's width on the panel, in millimetres. -/
def cssPixelMm : Float :=
  panelDiagonalIn * 25.4 /
    Float.sqrt (viewportW.toFloat * viewportW.toFloat + viewportH.toFloat * viewportH.toFloat)

/-- A screen's black under sRGB's reference viewing flare, 1% of white (IEC 61966-2-1). -/
def screenBlack : Float := 0.01

/-- The samples a device pixel spans along each axis, the whole number nearest to putting
`samplesPerAcuity` across the acuity. -/
def screenSplit : Nat :=
  (samplesPerAcuity * cssPixelMm /
    (panelDpr.toFloat * screenDistanceMm * Float.tan acuity)).round.toUInt64.toNat

/-- The screen's step is one CSS pixel, 1.03 arcmin at this distance: a move by one CSS pixel is
judged as a move by the acuity. -/
def screen : Medium :=
  { name := "screen", distanceMm := screenDistanceMm,
    sampleMm := cssPixelMm / panelDpr.toFloat / screenSplit.toFloat, stepMm := cssPixelMm,
    black := screenBlack, split := screenSplit
    detail := s!"viewport={viewportW}x{viewportH} dpr={panelDpr} split={screenSplit} \
css_px_mm={fixed cssPixelMm 4} css_px_arcmin={fixed (cssPixelMm / screenDistanceMm / Float.tan arcmin) 3}" }

/-! ## Rasters -/

/-- An 8-bit sRGB raster, three bytes a sample, row by row. -/
structure Raster where
  w : Nat
  h : Nat
  rgb : ByteArray

@[inline] def byteAt (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then b[i].toNat else 0

@[inline] def floatAt (a : FloatArray) (i : Nat) : Float := if h : i < a.size then a[i] else 0

@[inline] def setAt (a : FloatArray) (i : Nat) (v : Float) : FloatArray :=
  if h : i < a.size then a.set i v h else a

def zeros (n : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for _ in [0:n] do a := a.push 0
  return a

def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push 0
  return b

def be32At (b : ByteArray) (i : Nat) : Nat :=
  ((byteAt b i * 256 + byteAt b (i + 1)) * 256 + byteAt b (i + 2)) * 256 + byteAt b (i + 3)

/-- Interleaved 8-bit samples, `chs` a pixel, as RGB. -/
def toRgb (w h chs : Nat) (px : ByteArray) : Raster := Id.run do
  if chs == 3 then return { w, h, rgb := px }
  let mut rgb := ByteArray.emptyWithCapacity (w * h * 3)
  for k in [0:w * h] do
    rgb := rgb.push (byteAt px (chs * k)).toUInt8
    rgb := rgb.push (byteAt px (chs * k + 1)).toUInt8
    rgb := rgb.push (byteAt px (chs * k + 2)).toUInt8
  return { w, h, rgb }

/-- An uncompressed 8-bit RGB or RGBA TIFF in chunky order, as pdftocairo writes one; alpha is
dropped. -/
def readTiff (b : ByteArray) : Except String Raster := Id.run do
  let le := byteAt b 0 == 73 && byteAt b 1 == 73
  unless le || (byteAt b 0 == 77 && byteAt b 1 == 77) do return .error "not a TIFF"
  let u16 (i : Nat) := if le then byteAt b i + 256 * byteAt b (i + 1) else 256 * byteAt b i + byteAt b (i + 1)
  let u32 (i : Nat) := if le then u16 i + 65536 * u16 (i + 2) else 65536 * u16 i + u16 (i + 2)
  let ifd := u32 4
  let mut tags : Std.HashMap Nat (Nat × Nat × Nat) := {}
  for k in [0:u16 ifd] do
    let e := ifd + 2 + 12 * k
    tags := tags.insert (u16 e) (u16 (e + 2), u32 (e + 4), e + 8)
  let values (tag : Nat) : Array Nat := Id.run do
    let some (ty, n, at_) := tags.get? tag | return #[]
    let size := if ty == 3 then 2 else 4
    let base := if n * size ≤ 4 then at_ else u32 at_
    return (Array.range n).map fun i => if ty == 3 then u16 (base + 2 * i) else u32 (base + 4 * i)
  let one (tag : Nat) (d : Nat) := (values tag)[0]?.getD d
  let (w, h, chs) := (one 256 0, one 257 0, one 277 1)
  if w == 0 || h == 0 then return .error "a TIFF with no samples"
  if one 259 1 != 1 || one 284 1 != 1 || (values 258).any (· != 8) || (chs != 3 && chs != 4) then
    return .error "a TIFF not uncompressed 8-bit RGB in chunky order"
  let mut px := ByteArray.emptyWithCapacity (w * h * chs)
  for (o, n) in (values 273).zip (values 279) do px := px ++ b.extract o (o + n)
  if px.size < w * h * chs then return .error "a truncated TIFF"
  return .ok (toRgb w h chs px)

/-- An 8-bit truecolour PNG, with or without alpha and not interlaced, as Chromium writes a
screenshot; alpha is dropped. -/
def readPng (b : ByteArray) : Except String Raster := Id.run do
  if b.extract 0 8 != PngEncode.signature then return .error "not a PNG"
  let mut i := 8
  let mut head : Option (Nat × Nat × Nat) := none
  let mut idat := ByteArray.empty
  for _ in [0:b.size] do
    if i + 12 > b.size then break
    let len := be32At b i
    let kind := b.extract (i + 4) (i + 8)
    let data := b.extract (i + 8) (i + 8 + len)
    if kind == PngEncode.tagIHDR then
      if byteAt data 8 != 8 || byteAt data 12 != 0 then return .error "a PNG not 8-bit or interlaced"
      let chs := match byteAt data 9 with | 2 => 3 | 6 => 4 | _ => 0
      if chs == 0 then return .error "a PNG neither RGB nor RGBA"
      head := some (be32At data 0, be32At data 4, chs)
    else if kind == PngEncode.tagIDAT then idat := idat ++ data
    else if kind == PngEncode.tagIEND then break
    i := i + 12 + len
  let some (w, h, chs) := head | return .error "a PNG with no header"
  match (Flate.inflate idat (h * (1 + w * chs))).mapError toString >>=
      (Flate.pngUnfilter · h (w * chs) chs) with
  | .error e => return .error e
  | .ok px => return .ok (toRgb w h chs px)

/-- `r` grown to `w × h` by repeating its last column and last row. -/
def extendTo (r : Raster) (w h : Nat) : Raster := Id.run do
  if (w ≤ r.w && h ≤ r.h) || r.w == 0 || r.h == 0 then return r
  let (w, h) := (max w r.w, max h r.h)
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    let src := 3 * (min y (r.h - 1) * r.w)
    rgb := rgb ++ r.rgb.extract src (src + 3 * r.w)
    for _ in [0:w - r.w] do
      for c in [0:3] do rgb := rgb.push (byteAt r.rgb (src + 3 * (r.w - 1) + c)).toUInt8
  return { w, h, rgb }

/-- The `w × h` window of `r` at `(x0, y0)`. -/
def crop (r : Raster) (x0 y0 w h : Nat) : Raster := Id.run do
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    rgb := rgb ++ r.rgb.extract (3 * ((y0 + y) * r.w + x0)) (3 * ((y0 + y) * r.w + x0 + w))
  return { w, h, rgb }

/-- Each pixel of `r` as a `k × k` block of samples. -/
def splitPixels (k : Nat) (r : Raster) : Raster := Id.run do
  if k ≤ 1 then return r
  let mut rgb := ByteArray.emptyWithCapacity (9 * k * k * r.w * r.h)
  for y in [0:r.h * k] do
    let row := 3 * (y / k * r.w)
    for x in [0:r.w] do
      let (c0, c1, c2) := (byteAt r.rgb (row + 3 * x), byteAt r.rgb (row + 3 * x + 1),
        byteAt r.rgb (row + 3 * x + 2))
      for _ in [0:k] do rgb := rgb.push c0.toUInt8 |>.push c1.toUInt8 |>.push c2.toUInt8
  return { w := r.w * k, h := r.h * k, rgb }

/-- The first byte index in `[i, i + n)` where `a` and `b` differ, or `i + n`. -/
def firstDiff (a b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => if byteAt a i != byteAt b i then i else firstDiff a b n (i + 1)

/-- The last byte index in `[lo, lo + n)` where `a` and `b` differ, or `lo`. -/
def lastDiff (a b : ByteArray) (lo : Nat) : Nat → Nat
  | 0 => lo
  | n + 1 => if byteAt a (lo + n) != byteAt b (lo + n) then lo + n else lastDiff a b lo n

/-- The smallest box, in samples, holding every sample where two equal-sized rasters differ. -/
def diffBox (a b : Raster) : Option (Nat × Nat × Nat × Nat) := Id.run do
  let row := 3 * a.w
  let mut box : Option (Nat × Nat × Nat × Nat) := none
  for y in [0:a.h] do
    let f := firstDiff a.rgb b.rgb row (y * row)
    if f < (y + 1) * row then
      let l := lastDiff a.rgb b.rgb (y * row) row
      let (fx, lx) := ((f - y * row) / 3, (l - y * row) / 3)
      box := some <| match box with
        | none => (fx, y, lx, y)
        | some (x0, y0, x1, _) => (min x0 fx, y0, max x1 lx, y)
  return box

/-! ## What the eye sees -/

/-- `Oklab.channelLinear` at unit scale: each 8-bit sRGB channel's linear light. -/
def linear : FloatArray :=
  Oklab.channelLinear.foldl (fun a v => a.push (v.toFloat / 1e7)) (FloatArray.emptyWithCapacity 256)

/-- The bins of linear light `encodeTable` resolves. -/
def encodeBins : Nat := 65536

/-- The 8-bit sRGB channel whose linear light is nearest each bin's centre. -/
def encodeTable : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity encodeBins
  for i in [0:encodeBins] do
    let v := i.toFloat / (encodeBins - 1).toFloat
    let mut lo := 0
    let mut hi := 255
    for _ in [0:8] do
      if hi ≤ lo + 1 then break
      let mid := (lo + hi) / 2
      if floatAt linear mid ≤ v then lo := mid else hi := mid
    out := out.push (if v - floatAt linear lo ≤ floatAt linear hi - v then lo else hi).toUInt8
  return out

/-- The 8-bit sRGB channel whose linear light is nearest `v`. -/
@[inline] def encode (v : Float) : Nat :=
  byteAt encodeTable (max 0 (min v 1) * (encodeBins - 1).toFloat).round.toUInt64.toNat

/-- `r` averaged over `k × k` blocks in linear light. -/
def shrink (k : Nat) (r : Raster) : Raster := Id.run do
  if k ≤ 1 then return r
  let (w, h) := (r.w / k, r.h / k)
  let scale := 1 / (k * k).toFloat
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    let mut acc := zeros (3 * w)
    for j in [0:k] do
      let row := 3 * ((y * k + j) * r.w)
      for x in [0:w * k] do
        let o := 3 * (x / k)
        for c in [0:3] do
          acc := setAt acc (o + c) (floatAt acc (o + c) + floatAt linear (byteAt r.rgb (row + 3 * x + c)))
    for i in [0:3 * w] do rgb := rgb.push (encode (floatAt acc i * scale)).toUInt8
  return { w, h, rgb }

/-- A Gaussian's weights out to three deviations, summing to one. -/
def kernel (sigma : Float) : FloatArray := Id.run do
  let r := (3 * sigma).ceil.toUInt64.toNat
  let raw := (List.range (2 * r + 1)).map fun k =>
    let d := k.toFloat - r.toFloat
    Float.exp (-(d * d) / (2 * sigma * sigma))
  let total := raw.foldl (· + ·) 0
  return raw.foldl (fun a v => a.push (v / total)) (FloatArray.emptyWithCapacity (2 * r + 1))

/-- `s` plus the kernel's weights against the samples `f[base + stride · i']`, `i'` running over
`i - rad + j` clamped into `[0, lim]`. -/
def conv (k f : FloatArray) (base stride i rad lim : Nat) : Nat → Float → Float
  | 0, s => s
  | j + 1, s =>
    conv k f base stride i rad lim j
      (s + floatAt k j * floatAt f (base + stride * min lim (i + j - rad)))

/-- A raster's linear light, three values a sample, with the eye's point spread applied and the
medium's black floor added. -/
def seen (m : Medium) (r : Raster) : FloatArray := Id.run do
  let (w, h) := (r.w, r.h)
  let k := kernel m.sigma
  let rad := k.size / 2
  let mut src := FloatArray.emptyWithCapacity (3 * w * h)
  for i in [0:3 * w * h] do src := src.push (floatAt linear (byteAt r.rgb i))
  let mut across := FloatArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    for x in [0:w] do
      for c in [0:3] do across := across.push (conv k src (3 * y * w + c) 3 x rad (w - 1) k.size 0)
  let mut out := FloatArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    for x in [0:w] do
      for c in [0:3] do
        let s := conv k across (3 * x + c) (3 * w) y rad (h - 1) k.size 0
        out := out.push (m.black + (1 - m.black) * s)
  return out

/-- An 8-bit colour's OKLab coordinates at unit scale, by `Oklab.labOf`. -/
def labUnit (r g b : Nat) : Float × Float × Float :=
  let l := Oklab.labOf { r := r.toUInt8, g := g.toUInt8, b := b.toUInt8 }
  (Float.ofInt l.L / 1e18, Float.ofInt l.a / 1e18, Float.ofInt l.b / 1e18)

/-- Colours already converted to OKLab, keyed by their 24-bit sRGB value. -/
abbrev Memo := Std.HashMap Nat (Float × Float × Float)

/-- Each seen sample's OKLab coordinates, by `labUnit` of its nearest 8-bit sRGB colour. -/
def labField (s : FloatArray) (memo : Memo) : FloatArray × Memo := Id.run do
  let mut out := FloatArray.emptyWithCapacity s.size
  let mut memo := memo
  for p in [0:s.size / 3] do
    let r := encode (floatAt s (3 * p))
    let g := encode (floatAt s (3 * p + 1))
    let b := encode (floatAt s (3 * p + 2))
    let key := (r * 256 + g) * 256 + b
    let mut v := (0, 0, 0)
    match memo.get? key with
    | some found => v := found
    | none =>
      v := labUnit r g b
      memo := memo.insert key v
    out := out.push v.1 |>.push v.2.1 |>.push v.2.2
  return (out, memo)

/-! ## The judge -/

/-- The sample offsets within `reach`, as two parallel arrays. -/
def disc (reach : Float) : Array Int × Array Int := Id.run do
  let r := reach.floor.toUInt64.toNat
  let mut dxs : Array Int := #[]
  let mut dys : Array Int := #[]
  for i in [0:2 * r + 1] do
    for j in [0:2 * r + 1] do
      let dx : Int := (i : Int) - r
      let dy : Int := (j : Int) - r
      if (dx * dx + dy * dy).toNat.toFloat ≤ reach * reach then
        dxs := dxs.push dx
        dys := dys.push dy
  return (dxs, dys)

@[inline] def clampTo (v : Int) (n : Nat) : Nat := (max 0 (min v ((n : Int) - 1))).toNat

@[inline] def excess (v lo hi : Float) : Float := if v < lo then lo - v else if v > hi then v - hi else 0

/-- How far `(v0, v1, v2)` lies outside the box the colours of `f` span over the offsets around
`(x, y)`, the box's corners carried in `l0 … h2`. -/
def gap (dxs dys : Array Int) (f : FloatArray) (x y : Int) (w h : Nat) (v0 v1 v2 : Float) :
    Nat → Float → Float → Float → Float → Float → Float → Float
  | 0, l0, l1, l2, h0, h1, h2 =>
    let e0 := excess v0 l0 h0
    let e1 := excess v1 l1 h1
    let e2 := excess v2 l2 h2
    Float.sqrt (e0 * e0 + e1 * e1 + e2 * e2)
  | n + 1, l0, l1, l2, h0, h1, h2 =>
    let q := 3 * (clampTo (y + dys.getD n 0) h * w + clampTo (x + dxs.getD n 0) w)
    let q0 := floatAt f q
    let q1 := floatAt f (q + 1)
    let q2 := floatAt f (q + 2)
    gap dxs dys f x y w h v0 v1 v2 n (min l0 q0) (min l1 q1) (min l2 q2) (max h0 q0) (max h1 q1)
      (max h2 q2)

/-- Each sample's OKLab distance from what the other side shows within reach, the larger of the
two directions, over the `sw × sh` rectangle at `(ox, oy)` of two `w × h` fields. -/
def distanceField (dxs dys : Array Int) (w h : Nat) (la lb : FloatArray) (ox oy sw sh : Nat) :
    FloatArray := Id.run do
  let mut d := FloatArray.emptyWithCapacity (sw * sh)
  for y in [oy:oy + sh] do
    for x in [ox:ox + sw] do
      let p := 3 * (y * w + x)
      let a0 := floatAt la p
      let a1 := floatAt la (p + 1)
      let a2 := floatAt la (p + 2)
      let b0 := floatAt lb p
      let b1 := floatAt lb (p + 1)
      let b2 := floatAt lb (p + 2)
      if a0 == b0 && a1 == b1 && a2 == b2 then d := d.push 0
      else
        let ab := gap dxs dys lb x y w h a0 a1 a2 dxs.size b0 b1 b2 b0 b1 b2
        let ba := gap dxs dys la x y w h b0 b1 b2 dxs.size a0 a1 a2 a0 a1 a2
        d := d.push (max ab ba)
  return d

/-- The 8-connected regions where the `w × h` field `d` exceeds `t`: each sample's region number
(0 for none), and each region's area in samples and whether it reaches the rectangle
`[x0, x1) × [y0, y1)`, region `k` at index `k - 1`. -/
def regions (w h : Nat) (d : FloatArray) (t : Float) (x0 y0 x1 y1 : Nat) :
    Array Nat × Array (Nat × Bool) := Id.run do
  let mut label : Array Nat := Array.replicate (w * h) 0
  let mut found : Array (Nat × Bool) := #[]
  for p in [0:w * h] do
    if floatAt d p > t && label.getD p 0 == 0 then
      let k := found.size + 1
      label := label.modify p fun _ => k
      let mut stack := #[p]
      let mut area := 0
      let mut reaches := false
      for _ in [0:w * h] do
        let some q := stack.back? | break
        stack := stack.pop
        area := area + 1
        let (qx, qy) := (q % w, q / w)
        reaches := reaches || (x0 ≤ qx && qx < x1 && y0 ≤ qy && qy < y1)
        for dy in [0:3] do
          for dx in [0:3] do
            if (dx != 1 || dy != 1) && 1 ≤ qx + dx && qx + dx ≤ w && 1 ≤ qy + dy && qy + dy ≤ h then
              let n := (qy + dy - 1) * w + (qx + dx - 1)
              if floatAt d n > t && label.getD n 0 == 0 then
                label := label.modify n fun _ => k
                stack := stack.push n
      found := found.push (area, reaches)
  return (label, found)

inductive Verdict where
  | same
  | invisible
  | visible
  deriving BEq

def Verdict.name : Verdict → String
  | .same => "same"
  | .invisible => "invisible"
  | .visible => "visible"

/-- The longest side of an image cairo draws, its `MAX_IMAGE_SIZE`. -/
def cairoSide : Nat := 32767

/-- The longest side drawn at once: pixman composites an image in a 16-bit range, which a piece and
the source pixels an image reaches in it share, so an image of up to this many draws at any
offset. -/
def pieceSide : Nat := cairoSide / 2

/-- The rasterizer a page is drawn with on both sides. -/
inductive Drawer where
  | cairo
  | splash
  deriving BEq

def Drawer.tool : Drawer → String
  | .cairo => "pdftocairo"
  | .splash => "pdftoppm"

/-- How a page is drawn on both sides: its rasterizer and the longest side it draws at once. -/
structure Plan where
  drawer : Drawer
  side : Nat
  deriving BEq

/-- Cairo in pieces of `pieceSide`, how a page with no image wider than one piece is drawn. -/
def cairoPlan : Plan := ⟨.cairo, pieceSide⟩

/-- One page's, slide's or screen's judgement; `reason` when no sample was compared; the largest
OKLab difference after filtering; the area above one JND and the largest region traced around a
tile, in acuity spots; the heat map; and how a page was drawn. -/
structure Judgement where
  verdict : Verdict
  reason : String := ""
  maxDe : Float := 0
  area : Float := 0
  largest : Float := 0
  heat : Option ByteArray := none
  plan : Plan := cairoPlan

/-- The margin, in samples, that the point spread and the reach carry a difference across. -/
def Medium.margin (m : Medium) : Nat :=
  2 * ((kernel m.sigma).size / 2) + m.reach.ceil.toUInt64.toNat + 1

/-- The margin, in samples, within which a tile's regions are traced beyond it: a region cut there
still holds the acuity spot. -/
def Medium.scope (m : Medium) : Nat := m.spotSamples.ceil.toUInt64.toNat

/-- The samples a traced region reads beyond itself: the point spread's and the reach's. -/
def Medium.apron (m : Medium) : Nat := (kernel m.sigma).size / 2 + m.reach.ceil.toUInt64.toNat

/-- `n` samples in page pixels, rounded up. -/
def Medium.pixels (m : Medium) (n : Nat) : Nat := (n + m.split - 1) / m.split

/-- The window, in page pixels, around every difference of two equal-sized pages, widened by the
margin; `none` where they are equal. -/
def window (m : Medium) (a b : Raster) : Option (Nat × Nat × Nat × Nat) := do
  let (bx0, by0, bx1, by1) ← diffBox a b
  let g := m.pixels m.margin
  let (x0, y0) := (bx0 - min bx0 g, by0 - min by0 g)
  return (x0, y0, min (a.w - 1) (bx1 + g) + 1 - x0, min (a.h - 1) (by1 + g) + 1 - y0)

/-- A window's judgement under way: its largest difference, its samples above one JND, the largest
region traced around a tile, and its samples' heat classes. -/
structure Tally where
  maxDe : Float := 0
  above : Nat := 0
  largest : Nat := 0
  heat : Option ByteArray := none

/-- Samples along a tile's side. -/
def tileSide : Nat := 512

/-- The tile of a band whose own samples are rows `[c0, c1)` and columns `[cx0, cx1)`, judged with
its regions traced across the scope around it; with `heat`, its samples' classes: 3 in a region
holding the acuity spot, 2 above one JND, 1 above a quarter of one. -/
def assessTile (m : Medium) (dxs dys : Array Int) (a b : Raster) (c0 c1 cx0 cx1 : Nat) (heat : Bool) :
    Tally := Id.run do
  let (w, h, sc, ap) := (a.w, a.h, m.scope, m.apron)
  let (sx0, sy0, sx1, sy1) := (cx0 - min cx0 sc, c0 - min c0 sc, min w (cx1 + sc), min h (c1 + sc))
  let (px0, py0) := (sx0 - min sx0 ap, sy0 - min sy0 ap)
  let (pw, ph) := (min w (sx1 + ap) - px0, min h (sy1 + ap) - py0)
  let (cw, ch) := (cx1 - cx0, c1 - c0)
  let ta := crop a px0 py0 pw ph
  let tb := crop b px0 py0 pw ph
  if ta.rgb == tb.rgb then return { heat := if heat then some (zeroBytes (cw * ch)) else none }
  let (la, memo) := labField (seen m ta) {}
  let (lb, _) := labField (seen m tb) memo
  let (sw, sh) := (sx1 - sx0, sy1 - sy0)
  let d := distanceField dxs dys pw ph la lb (sx0 - px0) (sy0 - py0) sw sh
  let (ox, oy) := (cx0 - sx0, c0 - sy0)
  let (label, found) := regions sw sh d jnd ox oy (ox + cw) (oy + ch)
  let mut maxDe := 0
  let mut above := 0
  let mut cls := if heat then ByteArray.emptyWithCapacity (cw * ch) else ByteArray.empty
  for y in [oy:oy + ch] do
    for x in [ox:ox + cw] do
      let i := y * sw + x
      let v := floatAt d i
      maxDe := max maxDe v
      if v > jnd then above := above + 1
      if heat then
        let k := label.getD i 0
        cls := cls.push <|
          if k != 0 then if (found.getD (k - 1) (0, false)).1.toFloat ≥ m.spotSamples then 3 else 2
          else if v > jnd / 4 then 1 else 0
  let largest := found.foldl (fun n (area, reaches) => if reaches then max n area else n) 0
  return { maxDe, above, largest, heat := if heat then some cls else none }

/-- `heat`, the classes of a window `ww` samples wide, with a tile's `cw`-wide classes placed at
`(wx, wy)`. -/
def paint (cls : ByteArray) (cw ww wx wy : Nat) (heat : ByteArray) : ByteArray := Id.run do
  let mut heat := heat
  for i in [0:cls.size] do
    let v := byteAt cls i
    if v != 0 then heat := heat.set! ((wy + i / cw) * ww + wx + i % cw) v.toUInt8
  return heat

/-- `t` with a band of two windows judged, its tiles at once: `a` and `b` hold the band's samples,
their first row the window's row `top` and their rows `[c0, c1)` the band's own. -/
def assessBand (m : Medium) (dxs dys : Array Int) (a b : Raster) (top c0 c1 : Nat) (t : Tally) :
    Tally := Id.run do
  let tiles := (List.range ((a.w + tileSide - 1) / tileSide)).map fun k =>
    let (cx0, cx1) := (k * tileSide, min a.w (k * tileSide + tileSide))
    (cx0, cx1, Task.spawn fun _ => assessTile m dxs dys a b c0 c1 cx0 cx1 t.heat.isSome)
  let mut t := t
  for (cx0, cx1, task) in tiles do
    let r := task.get
    let heat := t.heat
    t := { maxDe := max t.maxDe r.maxDe, above := t.above + r.above, largest := max t.largest r.largest }
    t := { t with heat := match heat, r.heat with
      | some hm, some cls => some (paint cls (cx1 - cx0) a.w cx0 (top + c0) hm)
      | hm, _ => hm }
  return t

/-- A finished tally's judgement: visible where a region holds the acuity spot. -/
def Tally.judgement (m : Medium) (t : Tally) (heat : Option ByteArray) : Judgement :=
  { verdict := if t.largest.toFloat ≥ m.spotSamples then .visible else .invisible
    maxDe := t.maxDe, area := t.above.toFloat / m.spotSamples
    largest := t.largest.toFloat / m.spotSamples, heat }

def faint (v : Nat) : UInt8 := (255 - (255 - v) / 4).toUInt8

/-- `page` as a faint grey with its window at `(x0, y0)` marked from the classes `cls` of the
window's samples, `k × k` a pixel: pale yellow above a quarter JND, orange above one JND, red in a
region holding the acuity spot. -/
def heatPng (page : Raster) (k x0 y0 w h : Nat) (cls : ByteArray) : ByteArray := Id.run do
  let sw := k * w
  let mut rows := ByteArray.emptyWithCapacity (3 * page.w * page.h)
  for y in [0:page.h] do
    for x in [0:page.w] do
      let o := 3 * (y * page.w + x)
      let grey := (byteAt page.rgb o * 299 + byteAt page.rgb (o + 1) * 587 +
        byteAt page.rgb (o + 2) * 114) / 1000
      let mut c := 0
      if x0 ≤ x && x < x0 + w && y0 ≤ y && y < y0 + h then
        for j in [0:k] do
          for i in [0:k] do
            c := max c (byteAt cls ((k * (y - y0) + j) * sw + k * (x - x0) + i))
      let (r, g, b) : UInt8 × UInt8 × UInt8 := match c with
        | 3 => (220, 30, 30)
        | 2 => (240, 150, 20)
        | 1 => (250, 225, 120)
        | _ => (faint grey, faint grey, faint grey)
      rows := rows.push r |>.push g |>.push b
  return PngEncode.encode { width := page.w, height := page.h, bitDepth := 8, colorType := 2 } rows

/-- Sample `(x, y)` of a raster. -/
def sampleAt (r : Raster) (x y : Nat) : Nat × Nat × Nat :=
  let i := 3 * (y * r.w + x)
  (byteAt r.rgb i, byteAt r.rgb (i + 1), byteAt r.rgb (i + 2))

/-- A page's ground: the colour its corners and those of its last whole column and row share, or
paper white where they differ. -/
def groundOf (r : Raster) : Nat × Nat × Nat :=
  let c := sampleAt r 0 0
  if r.w < 2 || r.h < 2 then (255, 255, 255)
  else if [(r.w - 2, 0), (0, r.h - 2), (r.w - 2, r.h - 2)].all (fun (x, y) => sampleAt r x y == c)
  then c
  else (255, 255, 255)

/-- Sample `(x, y)` of `s` grown beside `o`, whose ground is `og`: its own where it covers it, else
`og` where `o` shows its ground there and `s`'s nearest sample otherwise; one past both pages reads
as the nearest within their larger width and height. -/
def grownAt (s o : Raster) (og : Nat × Nat × Nat) (x y : Nat) : Nat × Nat × Nat :=
  let (x, y) := (min x (max s.w o.w - 1), min y (max s.h o.h - 1))
  if x < s.w && y < s.h then sampleAt s x y
  else if s.w == 0 || s.h == 0 then (255, 255, 255)
  else if x < o.w && y < o.h && sampleAt o x y == og then og
  else sampleAt s (min x (s.w - 1)) (min y (s.h - 1))

/-- Row `y` of `s` grown to `w` samples beside `o` by `grownAt`. -/
def grownRow (s o : Raster) (og : Nat × Nat × Nat) (w y : Nat) (acc : ByteArray) : ByteArray :=
    Id.run do
  let mut acc := acc
  let own := if y < s.h then min s.w w else 0
  if own > 0 then acc := acc ++ s.rgb.extract (3 * (y * s.w)) (3 * (y * s.w + own))
  for x in [own:w] do
    let (r, g, b) := grownAt s o og x y
    acc := acc.push r.toUInt8 |>.push g.toUInt8 |>.push b.toUInt8
  return acc

/-- `s` grown to `w × h` beside `o` by `grownRow`, or itself where it is that size. -/
def grownTo (s o : Raster) (og : Nat × Nat × Nat) (w h : Nat) : Raster := Id.run do
  if s.w == w && s.h == h then return s
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do rgb := grownRow s o og w y rgb
  return { w, h, rgb }

/-- Two rasters grown to `w × h` together, of pages whose grounds are `ga` and `gb`. -/
def growTogether (a b : Raster) (w h : Nat) (ga gb : Nat × Nat × Nat) : Raster × Raster :=
  (grownTo a b gb w h, grownTo b a ga w h)

/-- Pages whose sizes differ by at most the reach, grown to one size together; `none` where they
differ by more. -/
def sized (m : Medium) (a b : Raster) : Option (Raster × Raster) :=
  let r := m.pixels m.reach.ceil.toUInt64.toNat
  if a.w + r < b.w || b.w + r < a.w || a.h + r < b.h || b.h + r < a.h then none
  else some (growTogether a b (max a.w b.w) (max a.h b.h) (groundOf a) (groundOf b))

/-- The page rows a band holds as its own, and the rows of context it reads beyond them. -/
def bandRows (m : Medium) : Nat × Nat := (tileSide / m.split, m.pixels (m.scope + m.apron))

/-- Two equal-sized pages judged at `m` over the window around their differences, band by band. -/
def judgePages (m : Medium) (heat : Bool) (a b : Raster) : Judgement := Id.run do
  let some (x0, y0, w, h) := window m a b | return { verdict := .same }
  let k := m.split
  let (dxs, dys) := disc m.reach
  let (rows, context) := bandRows m
  let mut t : Tally := { heat := if heat then some (zeroBytes (k * w * (k * h))) else none }
  for i in [0:(h + rows - 1) / rows] do
    let (c0, c1) := (i * rows, min h (i * rows + rows))
    let (r0, r1) := (c0 - min c0 context, min h (c1 + context))
    t := assessBand m dxs dys (splitPixels k (crop a x0 (y0 + r0) w (r1 - r0)))
      (splitPixels k (crop b x0 (y0 + r0) w (r1 - r0))) (k * r0) (k * (c0 - r0)) (k * (c1 - r0)) t
  return t.judgement m (t.heat.map (heatPng a k x0 y0 w h))

/-- The judgement of two pages within the reach of each other's size whose grown samples agree: the
same where their sizes are, else no visible difference. -/
def alike (a b : Raster) : Judgement :=
  { verdict := if a.w == b.w && a.h == b.h then .same else .invisible }

/-- Two pages judged at `m`. -/
def judge (m : Medium) (heat : Bool) (a b : Raster) : Judgement :=
  match sized m a b with
  | none => { verdict := .visible, reason := "size" }
  | some (ga, gb) =>
    let j := judgePages m heat ga gb
    if j.verdict == .same then alike a b else j

/-! ## Rasterizing the artifacts -/

/-- A tool's exit code and its two output streams, or why it could not start. -/
def runOut (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    ExceptT String IO (UInt32 × String × String) := do
  let out ← try IO.Process.output { cmd, args, env } catch e => throw s!"cannot run {cmd}: {e}"
  return (out.exitCode, out.stdout, out.stderr)

/-- The first line of a tool's standard error that reports an error, else its last. -/
def errorLine (err : String) : String :=
  let lines := ((err.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty)
  (lines.find? fun l => (l.toLower.splitOn "error").length > 1).getD (lines.getLastD "")

/-- A tool's standard output; a failure to start or a nonzero exit is the error, named by
`errorLine`. -/
def run (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    ExceptT String IO String := do
  let (code, out, err) ← runOut cmd args env
  if code != 0 then throw s!"{cmd} exited {code}: {errorLine err}"
  return out

/-- `f` over `jobs`, `width` at a time, every job finished before the first error is raised. -/
def parMap {α β : Type} (width : Nat) (jobs : Array α) (f : α → ExceptT String IO β) :
    ExceptT String IO (Array β) := do
  let mut done : Array (Except String β) := #[]
  for k in [0:(jobs.size + width - 1) / width] do
    let tasks ← (jobs.extract (k * width) (k * width + width)).mapM fun j =>
      (IO.asTask (f j).run .dedicated : IO _)
    for t in tasks do
      done := done.push <| match t.get with
        | .ok r => r
        | .error e => .error (toString e)
  done.mapM fun r => match r with
    | .ok v => pure v
    | .error e => throw e

/-- How many pages are judged at once. -/
def workers : Nat := 4

/-- Page `page` of `pdf`'s crop box at `dpi`, or its window `(x, y, w, h)` in that resolution's
pixels, drawn by `drawer` through a file beside `stem`; a drawing with no samples, or one missing an
image its rasterizer could not allocate, is an error. -/
def pdfPage (drawer : Drawer) (pdf : String) (page : Nat) (stem : System.FilePath) (dpi : Nat)
    (window : Option (Nat × Nat × Nat × Nat) := none) : ExceptT String IO Raster := do
  let cut := match window with
    | some (x, y, w, h) => #["-x", toString x, "-y", toString y, "-W", toString w, "-H", toString h]
    | none => #[]
  let (code, _, err) ← runOut drawer.tool (#["-tiff", "-tiffcompression", "none", "-cropbox", "-r",
    toString dpi, "-f", toString page, "-l", toString page] ++ cut ++ #["-singlefile", pdf, stem.toString])
  if code != 0 then throw s!"{drawer.tool} exited {code}: {errorLine err}"
  if ["Bogus memory allocation", "Out of memory"].any fun m => (err.splitOn m).length > 1 then
    throw s!"{pdf} page {page} at {dpi} dpi: {drawer.tool} could not allocate an image it draws"
  let file := stem.toString ++ ".tif"
  let bytes ← IO.FS.readBinFile file
  IO.FS.removeFile file
  match readTiff bytes with
  | .ok r => return r
  | .error e =>
    let why := errorLine err
    throw s!"{pdf} page {page} at {dpi} dpi: {e}{if why.isEmpty then "" else s!" ({why})"}"

def drawable (plan : Plan) (w h : Nat) : Bool := w ≤ plan.side && h ≤ plan.side

/-- `[0, n)` cut evenly into the fewest runs no longer than `side`, each a start and a length. -/
def runs (side n : Nat) : Array (Nat × Nat) :=
  let k := (n + side - 1) / max side 1
  let step := (n + k - 1) / max k 1
  (Array.range k).map fun i => (i * step, min n (i * step + step) - i * step)

/-- The first `cw × ch` pixels of window `(x, y, w, h)` of page `page` at `dpi`, drawn at once where
the window fits a piece and otherwise in the window's pieces laid together, of which only those
along the far edges of what is drawn may come back short, where the page ends. -/
def pdfWindow (plan : Plan) (pdf : String) (page : Nat) (stem : System.FilePath)
    (dpi x y w h cw ch : Nat) : ExceptT String IO Raster := do
  if drawable plan w h then return ← pdfPage plan.drawer pdf page stem dpi (some (x, y, cw, ch))
  let fits (got want start whole : Nat) := got == want || (start + want == whole && got < want)
  let mut rgb := ByteArray.emptyWithCapacity (3 * cw * ch)
  let mut width := 0
  let mut height := 0
  for (py, ph) in (runs plan.side h).filter (·.1 < ch) do
    let ph := min ph (ch - py)
    let mut row : Array Raster := #[]
    for (px, pw) in (runs plan.side w).filter (·.1 < cw) do
      let pw := min pw (cw - px)
      let r ← pdfPage plan.drawer pdf page stem dpi (some (x + px, y + py, pw, ph))
      unless fits r.w pw px cw && fits r.h ph py ch && row.all (·.h == r.h) do
        throw s!"{pdf} page {page} at {dpi} dpi: a piece of {pw}x{ph} at ({x + px}, {y + py}) \
drawn {r.w}x{r.h}"
      row := row.push r
    let across := row.foldl (· + ·.w) 0
    if height > 0 && across != width then
      throw s!"{pdf} page {page} at {dpi} dpi: pieces {across} wide below pieces {width} wide"
    width := across
    let high := (row[0]?.map (·.h)).getD 0
    for j in [0:high] do
      for r in row do rgb := rgb ++ r.rgb.extract (3 * j * r.w) (3 * (j + 1) * r.w)
    height := height + high
  return { w := width, h := height, rgb }

/-- Each page's crop box as pdfinfo prints it, its width and height in micro-points, turned by the
page's rotation. -/
def pdfBoxes (pdf : String) : ExceptT String IO (Array (Nat × Nat)) := do
  let out ← run "pdfinfo" #["-f", "1", "-l", "1000000", "-box", pdf]
  let mut count : Option Nat := none
  let mut boxes : Std.HashMap String (List String) := {}
  let mut turns : Std.HashMap String Nat := {}
  for l in out.splitOn "\n" do
    match (l.splitOn " ").filter (!·.isEmpty) with
    | ["Pages:", n] => count := n.toNat?
    | ["Page", n, "CropBox:", x0, y0, x1, y1] => boxes := boxes.insert n [x0, y0, x1, y1]
    | ["Page", n, "rot:", r] => turns := turns.insert n (r.toNat?.getD 0)
    | _ => pure ()
  let some pages := count | throw s!"pdfinfo printed no page count for {pdf}"
  let micro (v : String) : Option Int := do
    let (m, scale) ← LeanTex.Core.Decl.parseDecimal v
    return m * 1000000 / (scale : Int)
  (Array.range pages).mapM fun i => do
    let some [x0, y0, x1, y1] := (boxes.get? (toString (i + 1))).bind (·.mapM micro)
      | throw s!"pdfinfo printed no crop box for {pdf} page {i + 1}"
    let (w, h) := ((x1 - x0).natAbs, (y1 - y0).natAbs)
    return if turns.getD (toString (i + 1)) 0 % 180 == 90 then (h, w) else (w, h)

/-- Each page's largest image side in source pixels, as `pdfimages -list` prints the images, masks
and soft masks a page draws, and the objects it names them by. -/
def pdfImageSides (pdf : String) : ExceptT String IO (Std.HashMap Nat Nat × Std.HashSet Nat) := do
  let out ← run "pdfimages" #["-list", pdf]
  let mut sides : Std.HashMap Nat Nat := {}
  let mut listed : Std.HashSet Nat := {}
  for l in (out.splitOn "\n").drop 2 do
    let ws := (l.splitOn " ").filter (!·.isEmpty)
    if let (some p, some w, some h) := ((ws[0]?.bind (·.toNat?)), (ws[3]?.bind (·.toNat?)),
        (ws[4]?.bind (·.toNat?))) then
      sides := sides.insert p (max (sides.getD p 0) (max w h))
      if let some n := ws[10]?.bind (·.toNat?) then listed := listed.insert n
  return (sides, listed)

/-- Every image object `pdf` holds, by number, with its largest side in source pixels, as the
engine's reader finds them, inside patterns, glyph procedures and unused ones too. -/
def pdfImageObjects (pdf : String) : ExceptT String IO (Array (Nat × Nat)) := do
  let b ← IO.FS.readBinFile pdf
  let x ← match PdfRead.readXref b with
    | .ok x => pure x
    | .error e => throw e
  let es ← match PdfRead.objectsOf b x with
    | .ok es => pure es.val
    | .error e => throw e
  let side (o : PdfRead.Obj) (k : String) : Nat :=
    (((PdfCensus.deref es ((o.get? k).getD .null)).int?).map (·.toNat)).getD 0
  return es.filterMap fun e =>
    if PdfCensus.kindOf e.val == .image then some (e.num, max (side e.val "Width") (side e.val "Height"))
    else none

/-- How far a composite's extents stay inside pixman's 16-bit range, for its filter's reach. -/
def pixmanMargin : Nat := 64

/-- The shortest side a cairo plan draws at once. -/
def minPiece : Nat := 1024

/-- The plan of a page whose images' largest source side is `s` pixels: cairo in pieces no longer
than the 16-bit range leaves beside the image, which then composites at any offset, else Splash. -/
def planFor (s : Nat) : Plan :=
  if s ≤ pieceSide then cairoPlan
  else if s + pixmanMargin + minPiece ≤ cairoSide then ⟨.cairo, cairoSide - pixmanMargin - s⟩
  else ⟨.splash, pieceSide⟩

/-- A length in micro-points as the whole pixels it spans at `dpi`, rounded up as pdftocairo sizes a
page. -/
def pagePixels (len dpi : Nat) : Nat := (len * dpi + 72000000 - 1) / 72000000

/-- Page `page` of `pdf` at `dpi`, drawn whole where the `w × h` pixels planned for it fit a piece,
and otherwise in their pieces, the page ending within them. -/
def pdfFind (plan : Plan) (pdf : String) (page : Nat) (stem : System.FilePath)
    (dpi w h : Nat) : ExceptT String IO Raster := do
  if drawable plan w h then return ← pdfPage plan.drawer pdf page stem dpi
  let r ← pdfWindow plan pdf page stem dpi 0 0 w h w h
  unless r.w < w && r.h < h do
    throw s!"{pdf} page {page} at {dpi} dpi: drawn {r.w}x{r.h}, the page not ending within the \
{w}x{h} planned for it"
  return r

/-- Rows `[y0, y0 + rows)` of window `(x0, w)` on page `n`, `pw × ph` find-resolution pixels, as
judged samples: the part the page holds, drawn at `printSupersample` times `printDpi` and averaged in
linear light, empty where the page holds none of it. -/
def pdfBand (plan : Plan) (pdf : String) (n : Nat) (stem : System.FilePath)
    (pw ph x0 y0 w rows : Nat) : ExceptT String IO Raster := do
  let s := printSupersample * printSplit
  let (bw, bh) := (min pw (x0 + w) - x0, min ph (y0 + rows) - y0)
  if bw == 0 || bh == 0 then return { w := 0, h := 0, rgb := .empty }
  let r ← pdfWindow plan pdf n stem (printSupersample * printDpi) (s * x0) (s * y0) (s * w)
    (s * rows) (s * bw) (s * bh)
  unless r.w + s > s * bw && r.h + s > s * bh do
    throw s!"{pdf} page {n}: a window of {s * bw}x{s * bh} drawn {r.w}x{r.h}"
  return shrink printSupersample r

/-- Page `n` of two PDFs with crop boxes `ca` and `cb`, drawn by `plan` to find the window around
their differences, judged band by band with the two grown together, the window grown while a
difference nears an edge it can widen, the whole page after eight growths. -/
def judgePdfPage (plan : Plan) (a b : String) (n : Nat) (ca cb : Nat × Nat) (heat : Bool)
    (dir : System.FilePath) : ExceptT String IO Judgement := do
  let m := print
  let k := m.split
  let dpi := printDpi / k
  let (pw, ph) := (pagePixels (max ca.1 cb.1) dpi + 2, pagePixels (max ca.2 cb.2) dpi + 2)
  let fa ← pdfFind plan a n (dir / s!"a-{n}") dpi pw ph
  let fb ← pdfFind plan b n (dir / s!"b-{n}") dpi pw ph
  let pages := #[(a, "a", fa.w, fa.h), (b, "b", fb.w, fb.h)]
  let grounds := (groundOf fa, groundOf fb)
  let some (ra, rb) := sized m fa fb | return { verdict := .visible, reason := "size" }
  let some first := window m ra rb | return alike fa fb
  let (dxs, dys) := disc m.reach
  let (rows, context) := bandRows m
  let (g, mg) := (m.pixels m.margin, m.margin)
  let mut win := first
  for attempt in [0:9] do
    let (x0, y0, w, h) := win
    let mut t : Tally := { heat := if heat then some (zeroBytes (k * w * (k * h))) else none }
    let mut grown := win
    for i in [0:(h + rows - 1) / rows] do
      let (c0, c1) := (i * rows, min h (i * rows + rows))
      let (r0, r1) := (c0 - min c0 context, min h (c1 + context))
      let drawn ← parMap 2 pages fun (pdf, side, pw, ph) =>
        pdfBand plan pdf n (dir / s!"{side}-{n}") pw ph x0 (y0 + r0) w (r1 - r0)
      let (ca, cb) := growTogether (drawn[0]?.getD ⟨0, 0, .empty⟩) (drawn[1]?.getD ⟨0, 0, .empty⟩)
        (k * w) (k * (r1 - r0)) grounds.1 grounds.2
      if attempt < 8 then
        if let some (bx0, by0, bx1, by1) := diffBox ca cb then
          let left := bx0 < mg && x0 > 0
          let right := bx1 + mg ≥ ca.w && x0 + w < ra.w
          let up := r0 == 0 && by0 < mg && y0 > 0
          let down := r1 == h && by1 + mg ≥ ca.h && y0 + h < ra.h
          if left || right || up || down then
            let gx0 := if left then x0 - min x0 g else x0
            let gy0 := if up then y0 - min y0 g else y0
            let gx1 := if right then min ra.w (x0 + w + g) else x0 + w
            let gy1 := if down then min ra.h (y0 + h + g) else y0 + h
            grown := (gx0, gy0, gx1 - gx0, gy1 - gy0)
            break
      t := assessBand m dxs dys ca cb (k * r0) (k * (c0 - r0)) (k * (c1 - r0)) t
    if grown == win then return t.judgement m (t.heat.map (heatPng ra k x0 y0 w h))
    win := if attempt == 7 then (0, 0, ra.w, ra.h) else grown
  throw s!"{a} page {n}: no window settled"

/-- The browser side of a capture: every slide of a deck, or every viewport-high screen of a page,
as a PNG and a `shot` line, on a virtual clock advanced by fixed steps, SVG images redrawn without
their animations and every clock-driven animation stopped at its end or start. -/
def captureJs : String := r#"
const pw = require(process.env.PW_MODULE);
const fs = require('fs');
const url = require('url');
const [html, out, vw, vh, dpr] = process.argv.slice(2);
const watchdog = setTimeout(() => { console.log('error\thard timeout'); process.exit(4); }, 1800000);
(async () => {
  const browser = await pw.chromium.launch({ headless: true,
    args: ['--no-sandbox', '--disable-gpu', '--force-color-profile=srgb'] });
  const page = await browser.newPage({ viewport: { width: +vw, height: +vh },
    deviceScaleFactor: +dpr, colorScheme: 'light' });
  const cdp = await page.context().newCDPSession(page);
  const advance = (ms) => new Promise((resolve, reject) => {
    cdp.once('Emulation.virtualTimeBudgetExpired', resolve);
    cdp.send('Emulation.setVirtualTimePolicy',
      { policy: 'pauseIfNetworkFetchesPending', budget: ms }).catch(reject);
  });
  const freeze = () => page.evaluate(() => {
    for (const a of document.getAnimations()) {
      if (a.timeline !== document.timeline) continue;
      const end = a.effect ? a.effect.getComputedTiming().endTime : 0;
      a.pause();
      a.currentTime = isFinite(end) ? end : 0;
    }
    for (const s of document.querySelectorAll('svg'))
      if (s.pauseAnimations) { s.pauseAnimations(); s.setCurrentTime(0); }
  });
  const settle = async () => { await advance(1000); await freeze(); await advance(100); };
  await cdp.send('Emulation.setVirtualTimePolicy', { policy: 'pause' });
  let loaded = false;
  const nav = page.goto(url.pathToFileURL(html).href, { waitUntil: 'load' })
    .then(() => { loaded = true; });
  for (let k = 0; k < 60 && !loaded; k++) await advance(10000);
  await nav;
  for (let k = 0; k < 60 && await page.evaluate(() => document.fonts.status) !== 'loaded'; k++)
    await advance(1000);
  const files = {};
  for (const src of await page.evaluate(() => [...document.images].map(i => i.currentSrc || i.src)))
    if (src.startsWith('file:') && /\.svg$/i.test(src.split(/[?#]/)[0]))
      try { files[src] = fs.readFileSync(url.fileURLToPath(src), 'utf8'); } catch (e) {}
  await page.evaluate(files => {
    const atRest = text => {
      const doc = new DOMParser().parseFromString(text, 'image/svg+xml');
      if (doc.getElementsByTagName('parsererror').length) return null;
      const moving = doc.querySelectorAll('animate, animateMotion, animateTransform, animateColor, set');
      if (!moving.length && !/animation|transition/i.test(text)) return null;
      for (const e of moving) e.remove();
      const style = doc.createElementNS('http://www.w3.org/2000/svg', 'style');
      style.textContent = '*{animation:none!important;transition:none!important}';
      doc.documentElement.insertBefore(style, doc.documentElement.firstChild);
      return new XMLSerializer().serializeToString(doc);
    };
    for (const img of document.images) {
      const src = img.currentSrc || img.src;
      let text = files[src];
      if (text === undefined && /^data:image\/svg\+xml/i.test(src)) {
        const comma = src.indexOf(',');
        const body = src.slice(comma + 1);
        text = /;base64$/i.test(src.slice(0, comma))
          ? new TextDecoder().decode(Uint8Array.from(atob(body), c => c.charCodeAt(0)))
          : decodeURIComponent(body);
      }
      const still = text === undefined ? null : atRest(text);
      if (still === null) continue;
      img.removeAttribute('srcset');
      img.src = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(still);
    }
  }, files);
  for (let k = 0; k < 60 && !await page.evaluate(() => [...document.images].every(i => i.complete)); k++)
    await advance(100);
  let n = 0;
  const shoot = async (label, opts) => {
    n += 1;
    await page.screenshot({ path: `${out}/shot-${n}.png`, ...opts });
    console.log(['shot', n, String(label).replace(/\s+/g, '_')].join('\t'));
  };
  const snaps = await page.$$eval('[data-snap]',
    els => els.map((e, i) => e.dataset.slideLabel || e.id || String(i + 1)));
  if (snaps.length > 0) {
    console.log('unit\tslide');
    for (let i = 0; i < snaps.length; i++) {
      await page.evaluate(i => {
        const e = document.querySelectorAll('[data-snap]')[i];
        const t = e.getBoundingClientRect().width > 0 ? e : (e.closest('.slide-track') || e);
        t.scrollIntoView({ behavior: 'instant', inline: 'start', block: 'nearest' });
      }, i);
      await settle();
      await shoot(snaps[i], {});
    }
  } else {
    console.log('unit\tscreen');
    await settle();
    const height = Math.max(1, await page.evaluate(() => document.documentElement.scrollHeight));
    for (let y = 0; y < height; y += +vh) {
      await settle();
      await shoot('', { fullPage: true,
        clip: { x: 0, y, width: +vw, height: Math.min(+vh, height - y) } });
    }
  }
  await browser.close();
  clearTimeout(watchdog);
})().catch(e => { console.log('error\t' + String(e && e.message || e).split('\n')[0]); process.exit(4); });
"#

/-- Every slide or screen of `html` as Chromium shows it on the panel, each a label and a PNG
file, and the name of its unit. -/
def htmlShots (module : String) (html : String) (dir : System.FilePath) :
    ExceptT String IO (Array (String × System.FilePath) × String) := do
  IO.FS.createDirAll dir
  let js := dir / "capture.cjs"
  IO.FS.writeFile js captureJs
  let abs ← IO.FS.realPath html
  let (code, out, err) ← runOut "node" #[js.toString, abs.toString, dir.toString,
    toString viewportW, toString viewportH, toString panelDpr] #[("PW_MODULE", some module)]
  let mut shots := #[]
  let mut unit := "screen"
  for l in out.splitOn "\n" do
    match l.splitOn "\t" with
    | ["shot", n, label] => shots := shots.push (label, dir / s!"shot-{n}.png")
    | ["unit", u] => unit := u
    | "error" :: why => throw s!"the capture of {html} failed: {" ".intercalate why}"
    | _ => pure ()
  if code != 0 then
    throw s!"the capture of {html} exited {code}: {((err.splitOn "\n").headD "").trimAscii}"
  return (shots, unit)

def shotRaster (bytes : ByteArray) (file : System.FilePath) : ExceptT String IO Raster :=
  match readPng bytes with
  | .ok r => return r
  | .error e => throw s!"{file}: {e}"

/-- A screen of the page beyond its foot: its last row, `h` rows high. -/
def beyond (last : Raster) (h : Nat) : Raster :=
  extendTo (crop last 0 (last.h - 1) last.w 1) last.w h

/-- The judgement of each slide or screen of two captures; a screen is grown by its last row to
the height of the other's, and a screen one page lacks is that page grown by its last row. -/
def judgeShots (unit : String) (sa sb : Array (String × System.FilePath)) (heat : Bool) :
    ExceptT String IO (Array (String × Judgement)) := do
  let label (i : Nat) (l : String) := if l.isEmpty then toString (i + 1) else s!"{i + 1} {l}"
  let lastOf (s : Array (String × System.FilePath)) : ExceptT String IO (Option Raster) := do
    match s.back? with
    | some (_, f) => return some (← shotRaster (← IO.FS.readBinFile f) f)
    | none => return none
  let (lastA, lastB) ← if unit == "screen" && sa.size != sb.size then
      pure (← lastOf sa, ← lastOf sb) else pure (none, none)
  parMap workers (List.range (max sa.size sb.size)).toArray fun i => do
    match sa[i]?, sb[i]? with
    | some (la, fa), some (_, fb) =>
      let (pa, pb) := (← IO.FS.readBinFile fa, ← IO.FS.readBinFile fb)
      if pa == pb then return (label i la, { verdict := .same })
      let (ra, rb) := (← shotRaster pa fa, ← shotRaster pb fb)
      if unit == "screen" then
        let h := max ra.h rb.h
        return (label i la, judge screen heat (extendTo ra ra.w h) (extendTo rb rb.w h))
      return (label i la, judge screen heat ra rb)
    | some (la, fa), none =>
      match lastB with
      | some last =>
        let ra ← shotRaster (← IO.FS.readBinFile fa) fa
        return (label i la, judge screen heat ra (beyond last ra.h))
      | none => return (label i la, { verdict := .visible, reason := "only-in-a" })
    | none, some (lb, fb) =>
      match lastA with
      | some last =>
        let rb ← shotRaster (← IO.FS.readBinFile fb) fb
        return (label i lb, judge screen heat (beyond last rb.h) rb)
      | none => return (label i lb, { verdict := .visible, reason := "only-in-b" })
    | none, none => return ("", { verdict := .same })

/-! ## Comparing artifacts -/

/-- The judgements of one comparison, each with its unit's label, the unit's name, whether byte
identity settled it, and its notes. -/
structure Outcome where
  medium : Medium
  unit : String
  units : Array (String × Judgement)
  bytes : Bool := false
  /-- What the comparison could not read and how it went on. -/
  notes : Array String := #[]

def Outcome.visible (o : Outcome) : Bool := o.units.any (·.2.verdict == .visible)

def Outcome.result (o : Outcome) : Verdict :=
  if o.visible then .visible else if o.units.all (·.2.verdict == .same) then .same else .invisible

/-- Whether an HTML page may load anything it does not hold: a `src`, `srcset`, `poster`, `href`
outside `<a>` and `<area>`, or CSS `url(…)` that is neither a `data:` URI nor a fragment, or an
`@import`, `<object>`, `<embed>` or `<iframe>`. -/
def loadsBeyond (text : String) : Bool := Id.run do
  let t := text.toLower
  if ["@import", "<object", "<embed", "<iframe"].any (fun w => (t.splitOn w).length > 1) then
    return true
  let opens (rest : String) : Bool :=
    let r := rest.trimAsciiStart.toString
    let v := (if r.startsWith "\"" || r.startsWith "'" then (r.drop 1).toString else r).trimAsciiStart.toString
    !(v.startsWith "data:" || v.startsWith "#")
  if ((t.splitOn "url(").drop 1).any opens then return true
  for tag in (t.splitOn "<").drop 1 do
    let name := String.ofList (tag.toList.takeWhile fun c => c.isAlphanum || c == ':' || c == '-')
    let attrs := (tag.splitOn ">").headD ""
    let named := if name == "a" || name == "area" then ["src=", "srcset=", "poster="]
      else ["src=", "srcset=", "poster=", "href="]
    if named.any fun o => ((attrs.splitOn o).drop 1).any opens then return true
  return false

/-- Whether two artifacts are equal bytes, an HTML page only where it is UTF-8 and loads nothing
beyond itself. -/
def sameBytes (a b : String) (html : Bool) : IO Bool := do
  let ba ← IO.FS.readBinFile a
  if ba != (← IO.FS.readBinFile b) then return false
  if !html then return true
  match String.fromUTF8? ba with
  | some text => return !loadsBeyond text
  | none => return false

def comparePdf (a b : String) (heat : Bool) (dir : System.FilePath) : ExceptT String IO Outcome := do
  if ← sameBytes a b false then return { medium := print, unit := "page", units := #[], bytes := true }
  IO.FS.createDirAll dir
  let boxA ← pdfBoxes a
  let boxB ← pdfBoxes b
  -- A page's plan reads the images it draws, and every image no page is seen to draw, wherever it
  -- stands; what cannot be read is noted, and the rest plans without it.
  let mut notes : Array String := #[]
  let mut pages : Array (Std.HashMap Nat Nat) := #[]
  let mut unseen := 0
  for (pdf, side) in [(a, "a"), (b, "b")] do
    let (drawn, listed) ← try pdfImageSides pdf
      catch e => do
        notes := notes.push s!"image-sizes-unread side={side} why=\"{e}\""
        pure ({}, {})
    let objects ← try pdfImageObjects pdf
      catch e => do
        notes := notes.push s!"image-objects-unread side={side} why=\"{e}\""
        pure #[]
    pages := pages.push drawn
    unseen := objects.foldl (fun m (n, w) => if listed.contains n then m else max m w) unseen
  let sides := (pages[0]?.getD {}, pages[1]?.getD {})
  let (na, nb) := (boxA.size, boxB.size)
  let units ← parMap workers ((List.range (max na nb)).toArray.map (· + 1)) fun n => do
    if n > na then return (toString n, { verdict := .visible, reason := "only-in-b" })
    if n > nb then return (toString n, { verdict := .visible, reason := "only-in-a" })
    let plan := planFor (max unseen (max (sides.1.getD n 0) (sides.2.getD n 0)))
    let j ← judgePdfPage plan a b n (boxA[n - 1]?.getD (0, 0)) (boxB[n - 1]?.getD (0, 0)) heat dir
    return (toString n, { j with plan })
  return { medium := print, unit := "page", units, notes }

/-- The Playwright module whose Chromium launches, found once a run. -/
def chromium (cache : IO.Ref (Option String)) : ExceptT String IO String := do
  if let some m ← cache.get then return m
  discard <| run "node" #["--version"]
  let some (m, _) ← findChromium "node"
    | throw "no cached Playwright module launches Chromium (LEANTEX_PLAYWRIGHT names one)"
  cache.set (some m)
  return m

def compareHtml (a b : String) (heat : Bool) (dir : System.FilePath) (cache : IO.Ref (Option String)) :
    ExceptT String IO Outcome := do
  if ← sameBytes a b true then return { medium := screen, unit := "screen", units := #[], bytes := true }
  let module ← chromium cache
  let captures ← parMap 2 #[(a, dir / "a"), (b, dir / "b")] fun (f, d) => htmlShots module f d
  let ((sa, unit), (sb, _)) := (captures[0]?.getD (#[], ""), captures[1]?.getD (#[], ""))
  return { medium := screen, unit, units := ← judgeShots unit sa sb heat }

def compare (a b : String) (heat : Bool) (dir : System.FilePath) (cache : IO.Ref (Option String)) :
    ExceptT String IO Outcome :=
  if a.endsWith ".pdf" && b.endsWith ".pdf" then comparePdf a b heat dir
  else if a.endsWith ".html" && b.endsWith ".html" then compareHtml a b heat dir cache
  else throw "compare two .pdf files or two .html files"

/-! ## The report -/

def header (m : Medium) : String :=
  s!"visualdiff: medium={m.name} distance_mm={fixed m.distanceMm 0} acuity_mm={fixed m.acuityMm 4} \
sample_mm={fixed m.sampleMm 4} acuity_samples={fixed m.acuitySamples 2} black={fixed m.black 2} \
jnd={fixed jnd 3} spot_samples={fixed m.spotSamples 2} reach_samples={fixed m.reach 2} {m.detail}"

def unitLine (unit label : String) (j : Judgement) (heat : Option String) : String :=
  let (n, rest) := match label.splitOn " " with
    | n :: rest => (n, " ".intercalate rest)
    | [] => (label, "")
  let named := if rest.isEmpty then "" else s!" label={rest}"
  let why := if j.reason.isEmpty then "" else s!" reason={j.reason}"
  let measured := if j.verdict == .same || !j.reason.isEmpty then ""
    else s!" max_de={fixed j.maxDe 4} area_spots={fixed j.area 2 true} \
largest_spots={fixed j.largest 2 true}"
  let map := (heat.map (s!" heatmap={·}")).getD ""
  let drawn := if j.plan.drawer == .splash then " drawer=splash"
    else if j.plan.side != pieceSide then s!" piece={j.plan.side}" else ""
  s!"visualdiff: {unit}={n}{named} verdict={j.verdict.name}{why}{measured}{drawn}{map}"

def summaryLine (o : Outcome) : String :=
  let count (v : Verdict) := (o.units.filter (·.2.verdict == v)).size
  s!"visualdiff: result={o.result.name} units={o.units.size} same={count .same} \
invisible={count .invisible} visible={count .visible}" ++ (if o.bytes then " shortcut=bytes" else "")

/-- Print an outcome, writing heat maps under `heatDir`. -/
def report (o : Outcome) (heatDir : Option System.FilePath) : IO Unit := do
  IO.println (header o.medium)
  for (label, j) in o.units do
    let mut file : Option String := none
    if let (some dir, some png) := (heatDir, j.heat) then
      IO.FS.createDirAll dir
      let f := dir / s!"{o.unit}-{(label.splitOn " ").headD label}.png"
      IO.FS.writeBinFile f png
      file := some f.toString
    IO.println (unitLine o.unit label j file)
  for n in o.notes do IO.println s!"visualdiff: note={n}"
  IO.println (summaryLine o)

/-! ## The selftest -/

/-- The faces the selftest's documents are set in, shipped with the corpus. -/
def selftestFonts : String :=
  "\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\", sans = \"Open Sans\", mono = \"Source Code Pro\" }\n"

/-- An invented article: `words`, a line of words set `shift` from the margin and `drop` below
it, a rule, a swatch of colour `swatch`, and `tail`. -/
def fixture (words shift swatch : String) (drop : String := "0pt") (tail : String := "") : String :=
  "\\documentclass{article}\n" ++ selftestFonts ++ "\\definecolor{swatch}{HTML}{" ++ swatch ++
    "}\n\\begin{document}\n" ++ words ++ "\n\n\\vspace*{" ++ drop ++ "}\\noindent\\hspace*{" ++
    shift ++ "}Shifted, \\textit{slanted} and minimal\n\n\\noindent\\hspace*{" ++ shift ++
    "}\\rule{5cm}{0.4pt}\n\n\\noindent\\textcolor{swatch}{\\rule{3cm}{1cm}}\n" ++ tail ++
    "\\end{document}\n"

/-- An invented deck of two frames, the first in two steps whose second item reads `item`. -/
def deck (item : String) : String :=
  "\\documentclass[aspectratio=169]{beamer}\n" ++ selftestFonts ++ "\\begin{document}\n" ++
    "\\begin{frame}{First frame}\n\\begin{itemize}\n\\item<1-> Plain words on the first step.\n" ++
    "\\item<2-> " ++ item ++ "\n\\end{itemize}\n\\end{frame}\n" ++
    "\\begin{frame}{Second frame}\nQuiet words on a plain slide.\n\\end{frame}\n\\end{document}\n"

/-- An invented article some screens long whose last paragraph reads `last`. -/
def longPage (last : String) : String :=
  "\\documentclass{article}\n" ++ selftestFonts ++ "\\begin{document}\n" ++
    String.join ((List.range 90).map fun i => s!"Plain words of line {i + 1}, set to fill a page.\n\n") ++
    last ++ "\n\\end{document}\n"

def baseWords : String := "Plain words set on an invented page."
def baseSwatch : String := "8AA0C8"

/-- Swatches 0.42 and 3.5 JND from `baseSwatch`. -/
def nearSwatch : String := "8AA3C8"
def farSwatch : String := "6E8CC8"

/-- An invented article: a line of words, then `body` set `drop` below it. -/
def plain (body : String) (drop : String := "0pt") : String :=
  "\\documentclass{article}\n" ++ selftestFonts ++ "\\begin{document}\n" ++ baseWords ++
    "\n\n\\vspace*{" ++ drop ++ "}\\noindent " ++ body ++ "\n\\end{document}\n"

/-- An invented page of `size`, its width and height, inside 2 cm margins: a line of words, then,
`drop` below it, words and rules pushed to both margins and moved `shift` right. -/
def wide (size : String × String) (shift : String) (drop : String := "0pt") : String :=
  "\\documentclass{article}\n\\usepackage[paperwidth=" ++ size.1 ++ ", paperheight=" ++ size.2 ++
    ", margin=2cm]{geometry}\n" ++ selftestFonts ++ "\\begin{document}\n" ++ baseWords ++
    "\n\n\\vspace*{" ++ drop ++ "}\\noindent\\hspace*{" ++ shift ++ "}Words at the left margin\\hfill " ++
    "words at the right margin\\hspace*{-" ++ shift ++ "}\n\n\\noindent\\hspace*{" ++ shift ++
    "}\\rule{4cm}{0.4pt}\\hfill\\rule{4cm}{0.4pt}\\hspace*{-" ++ shift ++ "}\n\\end{document}\n"

/-- An invented page `width` by `page` inside 2 cm margins: `image`, the corpus's rectangles unless
named, stretched across it `height` high and moved `shift` right, then words wrapping across it. -/
def strip (shift : String) (image : String := "rects.png") (width : String := "2400pt")
    (height : String := "1cm") (page : String := "200pt") : String :=
  "\\documentclass{article}\n\\usepackage{graphicx}\n\\usepackage[paperwidth=" ++ width ++ ", " ++
    "paperheight=" ++ page ++ ", margin=2cm]{geometry}\n" ++ selftestFonts ++ "\\begin{document}\n" ++
    "\\noindent\\hspace*{" ++ shift ++ "}\\includegraphics[width=0.99\\linewidth, height=" ++ height ++
    "]{" ++ image ++ "}\n\n" ++
    String.join (List.replicate 12 "Plain words set in a paragraph across a wide invented strip. ") ++
    "\n\\end{document}\n"

/-- An invented letter-wide page `width` wide without margins, on `ground` unless that is empty: a
hairline and a 1 cm bar `rule` long from its left edge, a line of words, then `tail`. -/
def edge (width : String) (rule : String := "612pt") (tail : String := "") (ground : String := "") :
    String :=
  let paint := if ground.isEmpty then ""
    else "\\definecolor{ground}{HTML}{" ++ ground ++ "}\n\\pagecolor{ground}\n"
  "\\documentclass{article}\n\\usepackage[paperwidth=" ++ width ++ ", paperheight=792pt, " ++
    "margin=0pt]{geometry}\n" ++ selftestFonts ++ paint ++ "\\begin{document}\n\\noindent\\rule{" ++
    rule ++ "}{0.4pt}\n\n\\noindent\\rule{" ++ rule ++ "}{1cm}\n\n" ++ baseWords ++ "\n\n" ++ tail ++
    "\\end{document}\n"

/-- An invented image file a selftest case writes: its name, its width in pixels and each column's
colour, eight rows high. -/
structure Stripes where
  name : String
  width : Nat
  colour : Nat → Nat × Nat × Nat

def Stripes.png (s : Stripes) : ByteArray := Id.run do
  let mut row := ByteArray.emptyWithCapacity (3 * s.width)
  for x in [0:s.width] do
    let (r, g, b) := s.colour x
    row := row.push r.toUInt8 |>.push g.toUInt8 |>.push b.toUInt8
  let mut rows := ByteArray.emptyWithCapacity (8 * row.size)
  for _ in [0:8] do rows := rows ++ row
  return PngEncode.encode { width := s.width, height := 8, bitDepth := 8, colorType := 2 } rows

def stripeBlue : Nat × Nat × Nat := (40, 60, 200)
def stripeRed : Nat × Nat × Nat := (200, 40, 40)

/-- A blue image 40000 pixels wide, which cairo never draws. -/
def wideBlue : Stripes := { name := "wide-blue.png", width := 40000, colour := fun _ => stripeBlue }

def wideRed : Stripes := { wideBlue with name := "wide-red.png", colour := fun _ => stripeRed }

/-- A blue image 30000 pixels wide, which a whole cairo piece loses at its far end on a 3500 pt
page. -/
def farBlue : Stripes := { name := "far-blue.png", width := 30000, colour := fun _ => stripeBlue }

/-- `farBlue` with its last 5000 columns red. -/
def farRed : Stripes :=
  { farBlue with name := "far-red.png", colour := fun x => if x ≥ 25000 then stripeRed else stripeBlue }

/-- A blue image 17000 pixels wide, a little wider than a piece. -/
def broadBlue : Stripes := { name := "broad-blue.png", width := 17000, colour := fun _ => stripeBlue }

/-- `broadBlue` with its last 1700 columns red. -/
def broadRed : Stripes :=
  { broadBlue with name := "broad-red.png", colour := fun x => if x ≥ 15300 then stripeRed else stripeBlue }

/-- An invented page of `size` on a coloured ground, holding a line of words. -/
def ground (size : String × String) : String :=
  "\\documentclass{article}\n\\usepackage[paperwidth=" ++ size.1 ++ ", paperheight=" ++ size.2 ++
    "]{geometry}\n" ++ selftestFonts ++ "\\definecolor{swatch}{HTML}{" ++ baseSwatch ++
    "}\n\\pagecolor{swatch}\n\\begin{document}\n" ++ baseWords ++ "\n\\end{document}\n"

/-- An invented A0 poster: a line of words across its face set `shift` from its margin, then an
abstract holding a one-item list whose first level's margin is `margin`. -/
def board (margin shift : String) : String :=
  "\\documentclass{poster}\n" ++ selftestFonts ++ "\\setlength{\\leftmargini}{" ++ margin ++
    "}\n\\begin{document}\n\\begin{frame}{An Invented Board}\n\\hspace*{" ++ shift ++
    "}Plain words running across the whole board, set long enough to reach from one side of its " ++
    "face nearly to the other, so that a change anywhere along them spans the face. Two more short " ++
    "sentences follow them here. They end it.\n\\begin{abstract}\nAbstract words in a paragraph " ++
    "set below them.\n\\begin{itemize}\n\\item Listed words.\n\\end{itemize}\n\\end{abstract}\n" ++
    "\\end{frame}\n\\end{document}\n"

/-- An invented image whose circle pulses forever. -/
def pulseSvg : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"120\" height=\"60\" viewBox=\"0 0 120 60\">\n" ++
  " <rect width=\"120\" height=\"60\" fill=\"#eef2f8\"/>\n" ++
  " <circle cx=\"60\" cy=\"30\" r=\"10\" fill=\"#3a5f9e\">\n" ++
  "  <animate attributeName=\"r\" values=\"6;24;6\" dur=\"0.7s\" repeatCount=\"indefinite\"/>\n" ++
  " </circle>\n</svg>\n"

/-- What a selftest case expects a reader to see in a medium, or that the medium is not built. -/
inductive Expect where
  | seen
  | unseen
  | either
  | skip
  /-- No verdict: the comparison must end in an error. -/
  | refused
  deriving BEq

def Expect.name : Expect → String
  | .seen => "visible"
  | .unseen => "unseen"
  | .either => "either"
  | .skip => "skip"
  | .refused => "refused"

def Expect.meets (e : Expect) (visible : Bool) : Bool :=
  match e with
  | .seen => visible
  | .unseen => !visible
  | .either | .skip => true
  | .refused => false

/-- A selftest case: its two sources, whether the second artifact is the first's with bytes
appended, the files and images written beside them, what a reader sees on paper and on screen, and
how many comparisons of the pair run at once. -/
structure Case where
  name : String
  a : String
  b : String
  appended : Bool := false
  files : List (String × String) := []
  images : List Stripes := []
  paper : Expect
  screen : Expect
  repeats : Nat := 1

/-- The offsets that step a feature across the find resolution's pixel in eighths, as TeX lengths. -/
def phases : List String :=
  (List.range 8).map fun k => fixed (k.toFloat * 72 / (printDpi / printSplit).toFloat / 8) 4 ++ "pt"

/-- Contents moved around the acuity on letter, A0, banner and poster pages; images wider than a piece
moved and recoloured, one drawn too large for any rasterizer; and coloured pages, bars at a page's
edge and a hairline past it, grown by less than the reach. -/
def sizedCases : List Case :=
  let (letter, a0, banner) := (("8.5in", "11in"), ("841mm", "1189mm"), ("30cm", "180cm"))
  let low := "150cm"
  ([("letter", letter), ("a0", a0)].flatMap fun (paper, size) =>
    [("0.05pt", Expect.unseen), ("0.1pt", .unseen), ("0.5pt", .seen), ("2pt", .seen)].map fun (s, e) =>
      { name := s!"{paper}-shift-{s}", a := wide size "0pt", b := wide size s, paper := e,
        screen := .skip }) ++
  [{ name := "a0-drop-0.05pt", a := wide a0 "0pt", b := wide a0 "0pt" "0.05pt", paper := .unseen,
     screen := .skip },
   { name := "a0-drop-1pt", a := wide a0 "0pt", b := wide a0 "0pt" "1pt", paper := .seen, screen := .skip },
   { name := "banner-shift-0.05pt", a := wide banner "0pt" low, b := wide banner "0.05pt" low,
     paper := .unseen, screen := .skip },
   { name := "banner-shift-2pt", a := wide banner "0pt" low, b := wide banner "2pt" low, paper := .seen,
     screen := .skip },
   { name := "board-line-0.05pt", a := board "100pt" "0pt", b := board "100pt" "0.05pt",
     paper := .unseen, screen := .skip },
   { name := "board-list-44.8pt", a := board "100pt" "0pt", b := board "55.2pt" "0.05pt",
     paper := .seen, screen := .skip },
   { name := "strip-image-0.05pt", a := strip "0pt", b := strip "0.05pt", paper := .unseen,
     screen := .skip },
   { name := "strip-image-2pt", a := strip "0pt", b := strip "2pt", paper := .seen, screen := .skip },
   { name := "ground-wider-0.3pt", a := ground ("612pt", "792pt"), b := ground ("612.3pt", "792pt"),
     paper := .unseen, screen := .skip },
   { name := "ground-taller-0.15pt", a := ground ("612pt", "792pt"), b := ground ("612pt", "792.15pt"),
     paper := .unseen, screen := .skip },
   { name := "edge-wider-0.29pt", a := edge "612pt", b := edge "612.29pt", paper := .unseen,
     screen := .skip },
   { name := "edge-wider-0.29pt-shorter-2pt", a := edge "612pt", b := edge "612.29pt" "610pt",
     paper := .seen, screen := .skip },
   { name := "edge-wider-0.29pt-hairline", a := edge "612pt",
     b := edge "612.29pt" "612pt" "\\noindent\\hspace*{612.07pt}\\rule{0.22pt}{600pt}\n",
     paper := .seen, screen := .skip },
   { name := "edge-wider-0.29pt-on-ground", a := edge "612pt" (ground := "FFF4CC"),
     b := edge "612.29pt" (ground := "FFF4CC"), paper := .unseen, screen := .skip },
   { name := "edge-wider-0.29pt-hairline-on-ground", a := edge "612pt" (ground := "FFF4CC"),
     b := edge "612.29pt" "612pt" "\\noindent\\hspace*{612.07pt}\\rule{0.22pt}{600pt}\n" "FFF4CC",
     paper := .seen, screen := .skip },
   { name := "wide-image-recoloured", a := strip "0pt" wideBlue.name, b := strip "0pt" wideRed.name,
     images := [wideBlue, wideRed], paper := .seen, screen := .skip },
   { name := "wide-image-0.05pt", a := strip "0pt" wideBlue.name, b := strip "0.05pt" wideBlue.name,
     images := [wideBlue], paper := .unseen, screen := .skip },
   { name := "wide-image-2pt", a := strip "0pt" wideBlue.name, b := strip "2pt" wideBlue.name,
     images := [wideBlue], paper := .seen, screen := .skip },
   { name := "far-image-recoloured", a := strip "0pt" farBlue.name "3500pt",
     b := strip "0pt" farRed.name "3500pt", images := [farBlue, farRed], paper := .seen,
     screen := .skip },
   { name := "far-image-tall-recoloured", a := strip "0pt" farBlue.name "3500pt" "10cm" "400pt",
     b := strip "0pt" farRed.name "3500pt" "10cm" "400pt", images := [farBlue, farRed],
     paper := .seen, screen := .skip },
   { name := "broad-image-drawn-large-recoloured",
     a := strip "0pt" broadBlue.name "2400pt" "600pt" "700pt",
     b := strip "0pt" broadRed.name "2400pt" "600pt" "700pt", images := [broadBlue, broadRed],
     paper := .seen, screen := .skip },
   { name := "wide-image-drawn-huge", a := strip "0pt" wideBlue.name "2400pt" "650pt" "800pt",
     b := strip "0pt" wideRed.name "2400pt" "650pt" "800pt", images := [wideBlue, wideRed],
     paper := .refused, screen := .skip }]

def cases : List Case :=
  let base := fixture baseWords "0pt" baseSwatch
  let rule (w drop : String) (grey : Bool) :=
    plain ((if grey then "\\textcolor{gray}{" else "{") ++ "\\rule{12cm}{" ++ w ++ "}}") drop
  let speck (s at_ : String) := plain ("\\hspace*{" ++ at_ ++ "}\\rule{" ++ s ++ "}{" ++ s ++ "}") at_
  let pulse := plain "\\includegraphics[width=4cm]{pulse.svg}"
  [{ name := "identical", a := base, b := base, paper := .unseen, screen := .unseen },
   { name := "appended-bytes", a := base, b := base, appended := true, paper := .unseen, screen := .unseen },
   { name := "shift-0.05pt", a := base, b := fixture baseWords "0.05pt" baseSwatch, paper := .unseen,
     screen := .unseen },
   { name := "drop-0.05pt", a := base, b := fixture baseWords "0pt" baseSwatch "0.05pt", paper := .unseen,
     screen := .unseen },
   { name := "shift-0.1pt", a := base, b := fixture baseWords "0.1pt" baseSwatch, paper := .unseen,
     screen := .unseen },
   { name := "shift-1pt", a := base, b := fixture baseWords "1pt" baseSwatch, paper := .seen,
     screen := .either },
   { name := "shift-2pt", a := base, b := fixture baseWords "2pt" baseSwatch, paper := .seen,
     screen := .seen },
   { name := "tint-below", a := base, b := fixture baseWords "0pt" nearSwatch, paper := .unseen,
     screen := .unseen },
   { name := "tint-above", a := base, b := fixture baseWords "0pt" farSwatch, paper := .seen,
     screen := .seen },
   { name := "missing-word", a := base, b := fixture "Plain words set on an page." "0pt" baseSwatch,
     paper := .seen, screen := .seen },
   { name := "extra-page", a := base, b := fixture baseWords "0pt" baseSwatch "0pt" "\\newpage\nAnother page.\n",
     paper := .seen, screen := .seen },
   { name := "deck-copy", a := deck "More words on the second step.", b := deck "More words on the second step.",
     appended := true, paper := .unseen, screen := .unseen },
   { name := "deck-step", a := deck "More words on the second step.", b := deck "Other words on the second step.",
     paper := .seen, screen := .seen },
   { name := "long-copy", a := longPage "The last words.", b := longPage "The last words.", appended := true,
     paper := .unseen, screen := .unseen },
   { name := "long-last", a := longPage "The last words.", b := longPage "The final words.", paper := .seen,
     screen := .seen },
   { name := "long-taller-blank", a := longPage "The last words.",
     b := longPage "The last words.\n\n\\vspace*{24pt}\\mbox{}", paper := .unseen, screen := .unseen },
   { name := "long-taller-ink", a := longPage "The last words.",
     b := longPage "The last words.\n\nA few more words.", paper := .seen, screen := .seen }] ++
  (phases.zip (List.range 8)).flatMap (fun (at_, k) =>
    ["0.25pt", "0.4pt"].map fun w =>
      { name := s!"rule-grey-{w}-{k}", a := rule w at_ false, b := rule w at_ true, paper := .seen,
        screen := .skip }) ++
  ((phases.zip (List.range 8)).filter (·.2 % 2 == 0)).flatMap (fun (at_, k) =>
    [("0.05pt", Expect.unseen), ("0.2pt", Expect.seen)].map fun (s, e) =>
      { name := s!"speck-{s}-{k / 2}", a := plain "", b := speck s at_, paper := e, screen := .skip }) ++
  [{ name := "pulse-copy", a := pulse, b := pulse, appended := true, files := [("pulse.svg", pulseSvg)],
     paper := .skip, screen := .unseen, repeats := 4 }] ++
  sizedCases

def hexColor (s : String) : Nat × Nat × Nat :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - 48 else if c.isUpper then c.toNat - 55 else c.toNat - 87
  let v := s.foldl (fun n c => n * 16 + digit c) 0
  (v / 65536, v / 256 % 256, v % 256)

def deltaE (s t : String) : Float :=
  let ((r, g, b), (r', g', b')) := (hexColor s, hexColor t)
  let ((l0, l1, l2), (m0, m1, m2)) := (labUnit r g b, labUnit r' g' b')
  Float.sqrt ((l0 - m0) * (l0 - m0) + (l1 - m1) * (l1 - m1) + (l2 - m2) * (l2 - m2))

/-- The print medium's judge alone, on rasters drawn at its sample pitch. -/
def drawn : Medium := { print with split := 1 }

/-- A raster `w` samples wide and `h` high: white, a bar of linear light `ink` `bw` samples wide
from `left` antialiased as coverage in linear light, and a band of the flat colour `tint`. -/
def bar (w : Nat) (left bw : Float) (tint : Nat × Nat × Nat) (h : Nat := w) (ink : Float := 0) :
    Raster := Id.run do
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    for x in [0:w] do
      let lo := max left x.toFloat
      let hi := min (left + bw) (x.toFloat + 1)
      let cover := if y < h / 2 then max 0 (hi - lo) else 0
      let (r, g, b) := if y ≥ 3 * h / 4 then tint else (255, 255, 255)
      let mix (v : Nat) : UInt8 := (encode (floatAt linear v * (1 - cover) + ink * cover)).toUInt8
      rgb := rgb.push (mix r) |>.push (mix g) |>.push (mix b)
  return { w, h, rgb }

/-- `r` with a black square of side `s` samples at `(x, y)`, antialiased as coverage in linear
light. -/
def speck (r : Raster) (x y s : Float) : Raster := Id.run do
  let mut rgb := r.rgb
  for j in [0:r.h] do
    for i in [0:r.w] do
      let cx := max 0 (min (x + s) (i.toFloat + 1) - max x i.toFloat)
      let cy := max 0 (min (y + s) (j.toFloat + 1) - max y j.toFloat)
      if cx * cy > 0 then
        for c in [0:3] do
          let k := 3 * (j * r.w + i) + c
          if h : k < rgb.size then
            rgb := rgb.set k (encode (floatAt linear rgb[k].toNat * (1 - cx * cy))).toUInt8 h
  return { r with rgb }

/-- The judge alone, on drawn rasters: bars and hairlines moved within and beyond the acuity, bars
greyed and specks across the grid's phases, rasters a sample taller and two wider beside a bar at or
past the edge, and a flat tint below and above one JND. -/
def judgeCases : List (String × Raster × Raster × Bool) :=
  let a := drawn.acuitySamples
  let grey := (200, 200, 200)
  let n := 128
  let base := bar n 40 (3 * a) grey
  let thin := bar n 40 (a / 2) grey
  let perPt := 25.4 / 72 / drawn.sampleMm
  let half := floatAt linear 128
  [("bar-0.4-acuity", base, bar n (40 + 0.4 * a) (3 * a) grey, false),
   ("bar-0.9-acuity", base, bar n (40 + 0.9 * a) (3 * a) grey, false),
   ("bar-1.2-acuity", base, bar n (40 + 1.2 * a) (3 * a) grey, true),
   ("hairline-half-sample", thin, bar n 40.5 (a / 2) grey, false),
   ("hairline-1.5-acuity", thin, bar n (40 + 1.5 * a) (a / 2) grey, true),
   ("one-sample-taller", base, bar n 40 (3 * a) grey (n + 1), false),
   ("flat-tint-below", base, bar n 40 (3 * a) (206, 200, 200), false),
   ("flat-tint-above", base, bar n 40 (3 * a) (200, 200, 236), true),
   ("edge-bar-two-wider", bar n (n - 8).toFloat 8 grey, bar (n + 2) (n - 8).toFloat 8 grey n, false),
   ("edge-bar-two-wider-moved", bar n (n - 8).toFloat 8 grey, bar (n + 2) (n - 20).toFloat 8 grey n,
     true),
   ("ink-past-the-edge", bar n 0 0 grey, bar (n + 2) n.toFloat 2 grey n, true)] ++
  ((List.range 8).flatMap fun k => [("0.25", 0.25), ("0.4", 0.4)].map fun (name, pt) =>
    let left := 40 + k.toFloat / 8
    (s!"bar-{name}pt-grey-{k}", bar n left (pt * perPt) grey, bar n left (pt * perPt) grey n half, true)) ++
  ((List.range 4).flatMap fun k => [(1, false), (a, true)].map fun (s, seen) =>
    let at_ := 88 + k.toFloat / 4
    (s!"speck-{fixed (s / a) 2}-acuity-{k}", base, speck base at_ (16 + k.toFloat / 4) s, seen))

def leantexBin : String := ".lake/build/bin/leantex"

/-- A case's two artifacts in `ext`, built in `dir` beside a copy of the shipped fonts. -/
def buildCase (dir : System.FilePath) (c : Case) (ext : String) : ExceptT String IO (String × String) := do
  for (name, body) in c.files do IO.FS.writeFile (dir / name) body
  for img in c.images do IO.FS.writeBinFile (dir / img.name) img.png
  IO.FS.writeFile (dir / "a.tex") c.a
  IO.FS.writeFile (dir / "b.tex") c.b
  for side in ["a", "b"] do
    discard <| run leantexBin #["-q", (dir / s!"{side}.tex").toString, "-o", (dir / s!"{side}.{ext}").toString]
  let (a, b) := ((dir / s!"a.{ext}").toString, (dir / s!"b.{ext}").toString)
  if c.appended then
    let tail := if ext == "pdf" then "\n%%\n" else "\n<!-- -->\n"
    IO.FS.writeBinFile b ((← IO.FS.readBinFile a) ++ tail.toUTF8)
  return (a, b)

/-- `f` in a scratch directory holding copies of the shipped fonts and the corpus's rectangles. -/
def withAssets {α : Type} (f : System.FilePath → IO α) : IO α :=
  LeanTex.Cli.Host.withScratch fun dir => do
    let fonts := dir / "fonts"
    IO.FS.createDirAll fonts
    for e in ← System.FilePath.readDir "testdata/corpus/fonts" do
      IO.FS.writeBinFile (fonts / e.fileName) (← IO.FS.readBinFile e.path)
    IO.FS.writeBinFile (dir / "rects.png") (← IO.FS.readBinFile "testdata/corpus/rects.png")
    f dir

/-- Whether a raster holds a sample darker than mid-grey in some channel. -/
def inked (r : Raster) : Bool := r.rgb.foldl (fun seen v => seen || v < 128) false

/-- What goes wrong, if anything, drawing the strip at the judging resolution: a window wider than
cairo draws must be an error or whole drawn at once, and over its image and its words a piece at
every quarter piece across it, and two pieces laid together, must show what a narrow window does. -/
def windowCheck (dir : System.FilePath) : ExceptT String IO (Option String) := do
  IO.FS.writeFile (dir / "w.tex") (strip "0pt")
  let pdf := (dir / "w.pdf").toString
  discard <| run leantexBin #["-q", (dir / "w.tex").toString, "-o", pdf]
  let (dpi, stem, side) := (printSupersample * printDpi, dir / "w", 1024)
  let some (pageW, _) := (← pdfBoxes pdf)[0]? | return some "no-page"
  let across := pagePixels pageW dpi
  let once ← try some <$> pdfPage .cairo pdf 1 stem dpi (some (0, 0, cairoSide + 1, 4)) catch _ => pure none
  if let some r := once then
    unless r.w == cairoSide + 1 && r.h == 4 do return some s!"drawn-at-once-as-{r.w}x{r.h}"
  let shows (r : Raster) (x y h c : Nat) : ExceptT String IO Bool := do
    let direct ← pdfPage .cairo pdf 1 stem dpi (some (x + c - side / 2, y, side, h))
    let part := shrink printSupersample (crop r (c - side / 2) 0 side h)
    return inked direct && (judge drawn false part (shrink printSupersample direct)).verdict != .visible
  for (name, y, h) in [("image", 1800, 256), ("words", 2600, 128)] do
    for k in [0:(across - min across pieceSide) / (pieceSide / 4) + 1] do
      let x := k * (pieceSide / 4)
      let r ← pdfPage .cairo pdf 1 stem dpi (some (x, y, pieceSide, h))
      unless ← shows r x y h (pieceSide / 2) do return some s!"{name}-piece-differs-at-{x}"
    let (x, w) := (across - min across (2 * pieceSide + 128), 2 * pieceSide)
    let r ← pdfWindow cairoPlan pdf 1 stem dpi x y w h w h
    unless r.w == w && r.h == h && r.rgb.size == 3 * w * h do return some s!"{name}-pieced-as-{r.w}x{r.h}"
    for (px, pw) in runs pieceSide w do
      for c in [px + pw / 2, px + pw] do
        if c + side / 2 ≤ w then
          unless ← shows r x y h c do return some s!"{name}-pieced-differs-at-{x + c}"
  return none

/-- A PDF of `objs`, numbered from 1, the first the catalog: each a dictionary and a stream if any,
the stream's length added to its dictionary. -/
def rawPdf (objs : Array (String × Option ByteArray)) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offsets : Array Nat := #[]
  for i in [0:objs.size] do
    let (dict, stream) := objs[i]?.getD ("<< >>", none)
    offsets := offsets.push out.size
    match stream with
    | some data =>
      out := out ++ s!"{i + 1} 0 obj\n<< {dict} /Length {data.size} >>\nstream\n".toUTF8 ++ data ++
        "\nendstream\nendobj\n".toUTF8
    | none => out := out ++ s!"{i + 1} 0 obj\n<< {dict} >>\nendobj\n".toUTF8
  let xref := out.size
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n".toUTF8
  for o in offsets do
    let digits := toString o
    out := out ++ (String.ofList (List.replicate (10 - digits.length) '0') ++ digits ++ " 00000 n \n").toUTF8
  return out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8

/-- An invented 3500 by 200 pt page drawing `img` across it 1 cm high, but only inside the cell of a
tiling pattern that fills the page, which no `pdfimages -list` names. -/
def patternPdf (img : Stripes) : ByteArray := Id.run do
  let mut row := ByteArray.emptyWithCapacity (3 * img.width)
  for x in [0:img.width] do
    let (r, g, b) := img.colour x
    row := row.push r.toUInt8 |>.push g.toUInt8 |>.push b.toUInt8
  let mut pixels := ByteArray.emptyWithCapacity (8 * row.size)
  for _ in [0:8] do pixels := pixels ++ row
  rawPdf #[("/Type /Catalog /Pages 2 0 R", none), ("/Type /Pages /Kids [3 0 R] /Count 1", none),
    ("/Type /Page /Parent 2 0 R /MediaBox [0 0 3500 200] /Resources << /Pattern << /P1 5 0 R >> >> " ++
      "/Contents 4 0 R", none),
    ("", some "/Pattern cs /P1 scn 0 0 3500 200 re f\n".toUTF8),
    ("/Type /Pattern /PatternType 1 /PaintType 1 /TilingType 1 /BBox [0 0 3500 200] /XStep 7000 " ++
      "/YStep 400 /Resources << /XObject << /Im1 6 0 R >> >>",
      some "q 3352.25 0 0 28.35 56.69 114.96 cm /Im1 Do Q\n".toUTF8),
    (s!"/Type /XObject /Subtype /Image /Width {img.width} /Height 8 /ColorSpace /DeviceRGB " ++
      "/BitsPerComponent 8", some pixels)]

/-- What goes wrong, if anything, judging an image drawn only through a tiling pattern: recoloured at
its far end, it reads visible, its page drawn in the narrow pieces its source side asks for. -/
def patternCheck (dir : System.FilePath) : ExceptT String IO (Option String) := do
  let (a, b) := ((dir / "pa.pdf").toString, (dir / "pb.pdf").toString)
  IO.FS.writeBinFile a (patternPdf farBlue)
  IO.FS.writeBinFile b (patternPdf farRed)
  let o ← comparePdf a b false (dir / "pattern")
  let some (_, j) := o.units[0]? | return some "no-unit"
  unless j.plan == planFor farBlue.width do return some s!"planned-{j.plan.side}"
  unless o.visible do return some s!"read-{j.verdict.name}"
  return none

/-- What goes wrong, if anything, drawing images wider than a piece at the judging resolution: cairo
must lose a 30000-pixel image's far end from a whole piece and draw it in its plan's pieces, and draw
none of a 40000-pixel image, which Splash draws, each plan's pieces laid together as narrow windows. -/
def wideImageCheck (dir : System.FilePath) : ExceptT String IO (Option String) := do
  let (dpi, side) := (printSupersample * printDpi, 1024)
  let build (name : String) (img : Stripes) (width : String) : ExceptT String IO String := do
    IO.FS.writeBinFile (dir / img.name) img.png
    IO.FS.writeFile (dir / s!"{name}.tex") (strip "0pt" img.name width)
    let pdf := (dir / s!"{name}.pdf").toString
    discard <| run leantexBin #["-q", (dir / s!"{name}.tex").toString, "-o", pdf]
    return pdf
  -- Two pieces of `plan` laid together across rows `y` of `pdf`, against narrow windows of its drawer.
  let pieced (plan : Plan) (pdf : String) (stem : System.FilePath) (x y w h : Nat) :
      ExceptT String IO (Option String) := do
    let r ← pdfWindow plan pdf 1 stem dpi x y w h w h
    unless r.w == w && r.h == h && r.rgb.size == 3 * w * h do return some s!"pieced-as-{r.w}x{r.h}"
    for (px, pw) in runs plan.side w do
      for c in [px + pw / 2, px + pw] do
        if c + side / 2 ≤ w then
          let direct ← pdfPage plan.drawer pdf 1 stem dpi (some (x + c - side / 2, y, side, h))
          let part := shrink printSupersample (crop r (c - side / 2) 0 side h)
          unless inked direct && (judge drawn false part (shrink printSupersample direct)).verdict
              != .visible do
            return some s!"pieced-differs-at-{x + c}"
    return none
  let far ← build "f" farBlue "3500pt"
  let some (farW, _) := (← pdfBoxes far)[0]? | return some "no-far-page"
  let farAcross := pagePixels farW dpi
  let plan := planFor farBlue.width
  let at_ := (farAcross - pieceSide - 4096, 1800, pieceSide, 64)
  if inked (← pdfPage .cairo far 1 (dir / "f") dpi (some at_)) then
    return some "a-whole-piece-draws-the-far-image"
  if let some why ← pieced plan far (dir / "f") (farAcross - 4096 - 2 * plan.side) 1800 (2 * plan.side)
      64 then
    return some s!"far-image-{why}"
  let wide ← build "s" wideBlue "2400pt"
  if inked (← pdfPage .cairo wide 1 (dir / "s") dpi (some (20000, 1800, side, 64))) then
    return some "cairo-draws-the-wide-image"
  let some (pageW, _) := (← pdfBoxes wide)[0]? | return some "no-wide-page"
  let across := pagePixels pageW dpi
  for (name, y, h) in [("image", 1800, 256), ("words", 2600, 128)] do
    if let some why ← pieced (planFor wideBlue.width) wide (dir / "s")
        (across - min across (2 * pieceSide + 128)) y (2 * pieceSide) h then
      return some s!"wide-{name}-{why}"
  return none

def selftest : IO UInt32 := do
  let cache ← IO.mkRef none
  let mut bad := 0
  for (name, a, b, expect) in judgeCases do
    let j := judge drawn false a b
    let ok := (j.verdict == .visible) == expect
    unless ok do bad := bad + 1
    IO.println s!"visualdiff: selftest case={name} medium=judge \
expect={if expect then "visible" else "unseen"} got={j.verdict.name} max_de={fixed j.maxDe 4} \
largest_spots={fixed j.largest 2 true} ok={ok}"
  let near := deltaE baseSwatch nearSwatch / jnd
  let far := deltaE baseSwatch farSwatch / jnd
  unless near < 0.5 && far > 3 do
    bad := bad + 1
    IO.println s!"visualdiff: selftest swatches stand {fixed near 2} and {fixed far 2} JND apart, \
not below 0.5 and above 3"
  unless ← System.FilePath.pathExists leantexBin do
    IO.eprintln s!"visualdiff: {leantexBin} not found; run lake build first"
    return 2
  let mut unjudged := 0
  let checks : List (String × String × (System.FilePath → ExceptT String IO (Option String))) :=
    [("undrawable-window", "refused-then-pieced", windowCheck),
     ("wide-image-window", "drawn-by-its-plan", wideImageCheck),
     ("pattern-image-recoloured", "visible-in-its-plan", patternCheck)]
  for (name, want, check) in checks do
    match ← withAssets fun dir => (check dir).run with
    | .error e =>
      unjudged := unjudged + 1
      IO.println s!"visualdiff: selftest case={name} medium=print unjudged={e}"
    | .ok why =>
      unless why.isNone do bad := bad + 1
      IO.println s!"visualdiff: selftest case={name} medium=print expect={want} got={why.getD want} \
ok={why.isNone}"
  for c in cases do
    let outcome ← withAssets fun dir => do
      let mut results := #[]
      for (ext, medium, expect) in [("pdf", "print", c.paper), ("html", "screen", c.screen)] do
        if expect == .skip then continue
        let runs ← (do
          let (a, b) ← buildCase dir c ext
          parMap c.repeats (Array.range c.repeats) fun i =>
            compare a b false (dir / ext / toString i) cache : ExceptT String IO (Array Outcome)).run
        match runs with
        | .error e => results := results.push (medium, expect, Except.error e)
        | .ok os => results := results ++ os.map fun o => (medium, expect, .ok o)
      return results
    for (medium, expect, r) in outcome do
      match r with
      | .error e =>
        if expect == .refused then
          let ok : Bool := (e.splitOn "could not allocate").length > 1
          unless ok do bad := bad + 1
          IO.println s!"visualdiff: selftest case={c.name} medium={medium} expect=refused got={e} ok={ok}"
        else
          unjudged := unjudged + 1
          IO.println s!"visualdiff: selftest case={c.name} medium={medium} unjudged={e}"
      | .ok o =>
        let ok := expect.meets o.visible && (c.name != "identical" || o.bytes)
        unless ok do bad := bad + 1
        let worst := o.units.foldl (fun m u => max m u.2.maxDe) 0
        let largest := o.units.foldl (fun m u => max m u.2.largest) 0
        IO.println s!"visualdiff: selftest case={c.name} medium={medium} expect={expect.name} \
got={o.result.name} units={o.units.size} max_de={fixed worst 4} largest_spots={fixed largest 2 true} ok={ok}"
  IO.println s!"visualdiff: selftest failed={bad} unjudged={unjudged}"
  return if bad > 0 then 1 else if unjudged > 0 then 2 else 0

end VisualDiff

open VisualDiff in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--selftest"] => selftest
    | _ =>
      let (heatDir, rest) := match args with
        | "--heatmap" :: dir :: rest => (some (System.FilePath.mk dir), rest)
        | rest => (none, rest)
      let [a, b] := rest
        | IO.eprintln "usage: visualdiff [--heatmap <dir>] <a> <b>   (two .pdf or two .html)\n       visualdiff --selftest"
          return 2
      for f in [a, b] do
        unless ← System.FilePath.pathExists f do throw (IO.userError s!"{f} does not exist")
      let cache ← IO.mkRef none
      match ← LeanTex.Cli.Host.withScratch fun dir => (compare a b heatDir.isSome dir cache).run with
      | .error e =>
        IO.eprintln s!"visualdiff: {e}"
        return 2
      | .ok o =>
        report o heatDir
        return if o.visible then 1 else 0
  catch e =>
    IO.eprintln s!"visualdiff: {e}"
    return 2
