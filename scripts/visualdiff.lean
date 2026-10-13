/-
Whether two PDFs or two HTML pages differ visibly at stated viewing conditions, a report that never gates:
  lake build visualdiff && .lake/build/bin/visualdiff [--heatmap <dir>] <a> <b>
  .lake/build/bin/visualdiff --selftest
-/
import LeanTex
import scripts.Playwright

open LeanTex.Core

namespace VisualDiff

/-! ## The viewing model -/

def pi : Float := 3.141592653589793

/-- One arcminute, in radians. -/
def arcmin : Float := pi / 10800

/-- The detail normal (20/20) vision resolves: one arcminute. -/
def acuity : Float := arcmin

/-- Raster samples across the acuity: two, the Nyquist rate for detail at the acuity. -/
def samplesPerAcuity : Float := 2

/-- One just-noticeable difference in OKLab, `Oklab.okJnd` at unit scale. -/
def jnd : Float := Oklab.okJnd.toFloat / 1e18

/-- A medium as the eye meets it: its viewing distance, one raster sample's width on it, the
smallest step it moves anything by, and its black as a fraction of its white's luminance. -/
structure Medium where
  name : String
  distanceMm : Float
  sampleMm : Float
  stepMm : Float
  black : Float

def Medium.acuityMm (m : Medium) : Float := m.distanceMm * Float.tan acuity

def Medium.acuitySamples (m : Medium) : Float := m.acuityMm / m.sampleMm

/-- The eye's point spread, a Gaussian whose full width at half maximum is the acuity, in samples. -/
def Medium.sigma (m : Medium) : Float := m.acuitySamples / (2 * Float.sqrt (2 * Float.log 2))

/-- The acuity spot, a disc as wide as the acuity, in samples. -/
def Medium.spotSamples (m : Medium) : Float := pi / 4 * m.acuitySamples * m.acuitySamples

/-- How far a sample may move and still match, in samples: the acuity, or the medium's step where
that is coarser. -/
def Medium.reach (m : Medium) : Float := max m.acuityMm m.stepMm / m.sampleMm

/-- A printed page is read at 35 cm. -/
def printDistanceMm : Float := 350

/-- Printed black reflects about 2% of what paper white does, an optical density near 1.7. -/
def printBlack : Float := 0.02

/-- The raster resolution that puts `samplesPerAcuity` samples across the acuity on paper. -/
def printDpi : Nat :=
  (25.4 * samplesPerAcuity / (printDistanceMm * Float.tan acuity)).round.toUInt64.toNat

/-- Each judged print sample is `printSupersample²` pdftoppm pixels averaged in linear light,
diluting the gamma-space antialiasing pdftoppm composites. -/
def printSupersample : Nat := 2

def print : Medium :=
  { name := "print", distanceMm := printDistanceMm, sampleMm := 25.4 / printDpi.toFloat,
    stepMm := 0, black := printBlack }

/-- A laptop screen is read at arm's length, 60 cm. -/
def screenDistanceMm : Float := 600

/-- The panel: 15.6 inches across, 1920 × 1080 CSS pixels at device pixel ratio 1. -/
def panelDiagonalIn : Float := 15.6
def viewportW : Nat := 1920
def viewportH : Nat := 1080

/-- One CSS pixel on the panel: 0.180 mm, 1.03 arcminutes at 60 cm, about the acuity. -/
def cssPixelMm : Float :=
  panelDiagonalIn * 25.4 /
    Float.sqrt (viewportW.toFloat * viewportW.toFloat + viewportH.toFloat * viewportH.toFloat)

/-- The capture's device pixel ratio: the integer nearest `samplesPerAcuity` samples across the
acuity on the panel. -/
def captureScale : Nat :=
  (samplesPerAcuity * cssPixelMm / (screenDistanceMm * Float.tan acuity)).round.toUInt64.toNat

/-- A screen's black under sRGB's reference viewing flare, 1% of white (IEC 61966-2-1). -/
def screenBlack : Float := 0.01

def screen : Medium :=
  { name := "screen", distanceMm := screenDistanceMm, sampleMm := cssPixelMm / captureScale.toFloat,
    stepMm := cssPixelMm, black := screenBlack }

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

/-- A binary portable pixmap (P6, 8-bit), as pdftoppm writes one. -/
def readPpm (b : ByteArray) : Except String Raster := Id.run do
  if byteAt b 0 != 80 || byteAt b 1 != 54 then return .error "not a P6 pixmap"
  let mut i := 2
  let mut fields : Array Nat := #[]
  for _ in [0:b.size] do
    if fields.size == 3 || i ≥ b.size then break
    let c := byteAt b i
    if c == 35 then
      for _ in [0:b.size] do
        if i ≥ b.size || byteAt b i == 10 then break
        i := i + 1
    else if c == 32 || c == 9 || c == 10 || c == 13 then i := i + 1
    else if 48 ≤ c && c ≤ 57 then
      let mut n := 0
      for _ in [0:b.size] do
        let d := byteAt b i
        if i ≥ b.size || d < 48 || d > 57 then break
        n := n * 10 + (d - 48)
        i := i + 1
      fields := fields.push n
    else return .error "a malformed pixmap header"
  let #[w, h, maxval] := fields | return .error "a truncated pixmap header"
  if maxval != 255 then return .error "a pixmap deeper than 8 bits"
  let start := i + 1
  if b.size < start + w * h * 3 then return .error "a truncated pixmap"
  return .ok { w, h, rgb := b.extract start (start + w * h * 3) }

def be32At (b : ByteArray) (i : Nat) : Nat :=
  ((byteAt b i * 256 + byteAt b (i + 1)) * 256 + byteAt b (i + 2)) * 256 + byteAt b (i + 3)

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
  match Flate.inflate idat (h * (1 + w * chs)) >>= (Flate.pngUnfilter · h (w * chs) chs) with
  | .error e => return .error e
  | .ok px =>
    if chs == 3 then return .ok { w, h, rgb := px }
    let mut rgb := ByteArray.emptyWithCapacity (w * h * 3)
    for k in [0:w * h] do
      rgb := rgb.push (byteAt px (4 * k)).toUInt8
      rgb := rgb.push (byteAt px (4 * k + 1)).toUInt8
      rgb := rgb.push (byteAt px (4 * k + 2)).toUInt8
    return .ok { w, h, rgb }

/-- `r` grown to `h` rows by repeating its last row. -/
def extend (r : Raster) (h : Nat) : Raster :=
  if h ≤ r.h || r.h == 0 then r
  else
    let last := r.rgb.extract (3 * r.w * (r.h - 1)) (3 * r.w * r.h)
    { r with h, rgb := (List.replicate (h - r.h) last).foldl (· ++ ·) r.rgb }

/-- The `w × h` window of `r` at `(x0, y0)`. -/
def crop (r : Raster) (x0 y0 w h : Nat) : Raster := Id.run do
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    rgb := rgb ++ r.rgb.extract (3 * ((y0 + y) * r.w + x0)) (3 * ((y0 + y) * r.w + x0 + w))
  return { w, h, rgb }

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

/-- Each seen sample's OKLab coordinates, by `labUnit` of its nearest 8-bit sRGB colour; `memo`
holds colours already converted. -/
def labField (s : FloatArray) (memo : Std.HashMap Nat (Float × Float × Float)) :
    FloatArray × Std.HashMap Nat (Float × Float × Float) := Id.run do
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

/-- Each sample's OKLab distance from what the other side shows within the acuity, the larger of
the two directions: a shift within the acuity is no difference. -/
def distanceField (dxs dys : Array Int) (w h : Nat) (la lb : FloatArray) : FloatArray := Id.run do
  let mut d := FloatArray.emptyWithCapacity (w * h)
  for y in [0:h] do
    for x in [0:w] do
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

/-- The 8-connected regions where `d` exceeds `t`: each sample's region number (0 for none) and
each region's area in samples, region `k` at index `k - 1`. -/
def regions (w h : Nat) (d : FloatArray) (t : Float) : Array Nat × Array Nat := Id.run do
  let mut label : Array Nat := Array.replicate (w * h) 0
  let mut areas : Array Nat := #[]
  for p in [0:w * h] do
    if floatAt d p > t && label.getD p 0 == 0 then
      let k := areas.size + 1
      label := label.modify p fun _ => k
      let mut stack := #[p]
      let mut area := 0
      for _ in [0:w * h] do
        let some q := stack.back? | break
        stack := stack.pop
        area := area + 1
        let (qx, qy) := (q % w, q / w)
        for dy in [0:3] do
          for dx in [0:3] do
            if (dx != 1 || dy != 1) && 1 ≤ qx + dx && qx + dx ≤ w && 1 ≤ qy + dy && qy + dy ≤ h then
              let n := (qy + dy - 1) * w + (qx + dx - 1)
              if floatAt d n > t && label.getD n 0 == 0 then
                label := label.modify n fun _ => k
                stack := stack.push n
      areas := areas.push area
  return (label, areas)

/-- One page's, slide's or screen's judgement: `same` (equal samples), `invisible` or `visible`;
why, when no sample was compared; the largest OKLab difference left after filtering; the area
above one JND and its largest connected region, both in acuity spots; and its heat map. -/
structure Judgement where
  verdict : String
  reason : String := ""
  maxDe : Float := 0
  area : Float := 0
  largest : Float := 0
  heat : Option ByteArray := none

/-- The window, in samples of `m`, around every difference of two equal-sized rasters drawn at `k`
times its resolution, widened by the reach of the point spread and of `Medium.reach`; `none`
where they are equal. -/
def window (m : Medium) (k : Nat) (a b : Raster) : Option (Nat × Nat × Nat × Nat) := do
  let (bx0, by0, bx1, by1) ← diffBox a b
  let margin := 2 * ((kernel m.sigma).size / 2) + m.reach.ceil.toUInt64.toNat + 1
  let (x0, y0) := (bx0 / k - min (bx0 / k) margin, by0 / k - min (by0 / k) margin)
  return (x0, y0, min (a.w / k - 1) (bx1 / k + margin) + 1 - x0,
    min (a.h / k - 1) (by1 / k + margin) + 1 - y0)

def faint (v : Nat) : UInt8 := (255 - (255 - v) / 4).toUInt8

/-- `page` as a faint grey, with the window at `(x0, y0)` marked: samples above one JND in
orange, those in a region of at least the acuity spot in red. -/
def heatPng (page : Raster) (x0 y0 w h : Nat) (d : FloatArray) (label areas : Array Nat)
    (spot : Float) : ByteArray := Id.run do
  let mut rows := ByteArray.emptyWithCapacity (3 * page.w * page.h)
  for y in [0:page.h] do
    for x in [0:page.w] do
      let o := 3 * (y * page.w + x)
      let grey := (byteAt page.rgb o * 299 + byteAt page.rgb (o + 1) * 587 +
        byteAt page.rgb (o + 2) * 114) / 1000
      let inside := x0 ≤ x && x < x0 + w && y0 ≤ y && y < y0 + h
      let p := (y - y0) * w + (x - x0)
      let k := if inside then label.getD p 0 else 0
      let (r, g, b) :=
        if k != 0 then
          if (areas.getD (k - 1) 0).toFloat ≥ spot then ((220 : UInt8), (30 : UInt8), (30 : UInt8))
          else (240, 150, 20)
        else if inside && floatAt d p > jnd / 4 then (250, 225, 120)
        else (faint grey, faint grey, faint grey)
      rows := rows.push r |>.push g |>.push b
  return PngEncode.encode { width := page.w, height := page.h, bitDepth := 8, colorType := 2 } rows

/-- Two equal-sized windows judged at `m`; with `heat`, the page they were cut from and where. -/
def assess (m : Medium) (heat : Option (Raster × Nat × Nat)) (a b : Raster) : Judgement := Id.run do
  let (la, memo) := labField (seen m a) {}
  let (lb, _) := labField (seen m b) memo
  let (dxs, dys) := disc m.reach
  let d := distanceField dxs dys a.w a.h la lb
  let (label, areas) := regions a.w a.h d jnd
  let spot := m.spotSamples
  let largest := areas.foldl max 0
  { verdict := if largest.toFloat ≥ spot then "visible" else "invisible"
    maxDe := d.foldl max 0
    area := (areas.foldl (· + ·) 0).toFloat / spot
    largest := largest.toFloat / spot
    heat := heat.map fun (page, x0, y0) => heatPng page x0 y0 a.w a.h d label areas spot }

/-- Two rasters judged at `m` over the window around their differences. -/
def judge (m : Medium) (heat : Bool) (a b : Raster) : Judgement :=
  if a.w != b.w || a.h != b.h then { verdict := "visible", reason := "size" }
  else match window m 1 a b with
    | none => { verdict := "same" }
    | some (x0, y0, w, h) =>
      assess m (if heat then some (a, x0, y0) else none) (crop a x0 y0 w h) (crop b x0 y0 w h)

/-! ## Rasterizing the artifacts -/

/-- A tool's standard output; a failure to start or a nonzero exit is the error. -/
def run (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    ExceptT String IO String := do
  let out ← try IO.Process.output { cmd, args, env } catch e => throw s!"cannot run {cmd}: {e}"
  if out.exitCode != 0 then
    let why := ((out.stderr.splitOn "\n").find? (!·.trimAscii.isEmpty)).getD ""
    throw s!"{cmd} exited {out.exitCode}: {why.trimAscii}"
  return out.stdout

def pdfPages (pdf : String) : ExceptT String IO Nat := do
  let out ← run "pdfinfo" #[pdf]
  let count := ((out.splitOn "\n").find? (·.startsWith "Pages:")).bind fun l =>
    (l.drop "Pages:".length).toString.trimAscii.toString.toNat?
  match count with
  | some n => return n
  | none => throw s!"pdfinfo printed no page count for {pdf}"

/-- Page `page` of `pdf` at `dpi`, or its window `(x, y, w, h)` in that resolution's pixels,
through a pixmap written beside `stem`. -/
def pdfPage (pdf : String) (page : Nat) (stem : System.FilePath) (dpi : Nat)
    (window : Option (Nat × Nat × Nat × Nat) := none) : ExceptT String IO Raster := do
  let cut := match window with
    | some (x, y, w, h) => #["-x", toString x, "-y", toString y, "-W", toString w, "-H", toString h]
    | none => #[]
  discard <| run "pdftoppm" (#["-r", toString dpi, "-f", toString page, "-l", toString page] ++ cut ++
    #["-singlefile", pdf, stem.toString])
  let file := stem.toString ++ ".ppm"
  let bytes ← IO.FS.readBinFile file
  IO.FS.removeFile file
  match readPpm bytes with
  | .ok r => return r
  | .error e => throw s!"{pdf} page {page}: {e}"

/-- Page `n` of two PDFs judged at the print medium from rasters drawn at `printSupersample`
times `printDpi`, over the window around their differences. -/
def judgePdfPage (a b : String) (n : Nat) (heat : Bool) (dir : System.FilePath) :
    ExceptT String IO Judgement := do
  let k := printSupersample
  let ra ← pdfPage a n (dir / s!"a-{n}") (k * printDpi)
  let rb ← pdfPage b n (dir / s!"b-{n}") (k * printDpi)
  if ra.w != rb.w || ra.h != rb.h then return { verdict := "visible", reason := "size" }
  let some (x0, y0, w, h) := window print k ra rb | return { verdict := "same" }
  let cut (r : Raster) := shrink k (crop r (k * x0) (k * y0) (k * w) (k * h))
  return assess print (if heat then some (shrink k ra, x0, y0) else none) (cut ra) (cut rb)

/-- The browser side of a capture: every slide of a deck, or every viewport-high screen of a page,
as a PNG in the output directory and a `shot` line, on a virtual clock advanced by the same steps
for every page, so an animation stands at the same instant in both captures. -/
def captureJs : String := r#"
const pw = require(process.env.PW_MODULE);
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
  await cdp.send('Emulation.setVirtualTimePolicy', { policy: 'pause' });
  let loaded = false;
  const nav = page.goto(require('url').pathToFileURL(html).href, { waitUntil: 'load' })
    .then(() => { loaded = true; });
  for (let k = 0; k < 120 && !loaded; k++) await advance(1000);
  await nav;
  for (let k = 0; k < 120 && await page.evaluate(() => document.fonts.status) !== 'loaded'; k++)
    await advance(1000);
  await advance(1000);
  let n = 0;
  const shoot = async (label, opts) => {
    n += 1;
    await page.screenshot({ path: `${out}/shot-${n}.png`, ...opts });
    console.log(['shot', n, label].join('\t'));
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
      await advance(1000);
      await shoot(snaps[i], {});
    }
  } else {
    console.log('unit\tscreen');
    const height = Math.max(1, await page.evaluate(() => document.documentElement.scrollHeight));
    for (let y = 0; y < height; y += +vh)
      await shoot('', { fullPage: true,
        clip: { x: 0, y, width: +vw, height: Math.min(+vh, height - y) } });
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
  let out ← run "node" #[js.toString, abs.toString, dir.toString, toString viewportW,
    toString viewportH, toString captureScale] #[("PW_MODULE", some module)]
  let mut shots := #[]
  let mut unit := "screen"
  for l in out.splitOn "\n" do
    match l.splitOn "\t" with
    | ["shot", n, label] => shots := shots.push (label, dir / s!"shot-{n}.png")
    | ["unit", u] => unit := u
    | "error" :: why => throw s!"the capture failed: {"\t".intercalate why}"
    | _ => pure ()
  return (shots, unit)

def pngRaster (file : System.FilePath) : ExceptT String IO Raster := do
  match readPng (← IO.FS.readBinFile file) with
  | .ok r => return r
  | .error e => throw s!"{file}: {e}"

/-- Two shots judged at the screen medium, the shorter screen grown by its last row. -/
def judgeShots (fa fb : System.FilePath) (heat : Bool) : ExceptT String IO Judgement := do
  if (← IO.FS.readBinFile fa) == (← IO.FS.readBinFile fb) then return { verdict := "same" }
  let ra ← pngRaster fa
  let rb ← pngRaster fb
  if ra.w != rb.w then return { verdict := "visible", reason := "size" }
  return judge screen heat (extend ra rb.h) (extend rb ra.h)

/-! ## Comparing artifacts -/

/-- The judgements of one comparison, each with its unit's label, the unit's name, and whether
byte identity settled it. -/
structure Outcome where
  medium : Medium
  unit : String
  units : Array (String × Judgement)
  bytes : Bool := false

def Outcome.visible (o : Outcome) : Bool := o.units.any (·.2.verdict == "visible")

def Outcome.result (o : Outcome) : String :=
  if o.visible then "visible" else if o.units.all (·.2.verdict == "same") then "same" else "invisible"

/-- The local files an HTML page names by a relative `src`, `href` or `url(…)`. -/
def htmlRefs (text : String) : Array String := Id.run do
  let mut out := #[]
  for (opener, close) in [("src=\"", "\""), ("href=\"", "\""), ("url(\"", "\""), ("url('", "'"),
      ("url(", ")")] do
    for part in (text.splitOn opener).drop 1 do
      let ref := ((((part.splitOn close).headD "").splitOn "#").headD "").splitOn "?" |>.headD ""
      let ref := ref.trimAscii.toString
      let scheme := ((ref.splitOn "/").headD "").contains ':'
      if !ref.isEmpty && !scheme && !ref.startsWith "/" && !ref.startsWith "\"" && !ref.startsWith "'" then
        out := out.push ref
  return out

/-- Whether two artifacts are equal bytes, an HTML page together with the local files it names. -/
def sameBytes (a b : String) (html : Bool) : IO Bool := do
  let ba ← IO.FS.readBinFile a
  if ba != (← IO.FS.readBinFile b) then return false
  if !html then return true
  let dirA := (System.FilePath.mk a).parent.getD "."
  let dirB := (System.FilePath.mk b).parent.getD "."
  for ref in htmlRefs (String.fromUTF8! ba) do
    let fa := dirA / ref
    let fb := dirB / ref
    let ea ← fa.pathExists
    if ea != (← fb.pathExists) then return false
    if ea && !(← fa.isDir) && (← IO.FS.readBinFile fa) != (← IO.FS.readBinFile fb) then return false
  return true

/-- `f` over `jobs`, `width` at a time. -/
def parMap {α β : Type} (width : Nat) (jobs : Array α) (f : α → ExceptT String IO β) :
    ExceptT String IO (Array β) := do
  let mut out := #[]
  for k in [0:(jobs.size + width - 1) / width] do
    let tasks ← (jobs.extract (k * width) (k * width + width)).mapM fun j =>
      (IO.asTask (f j).run .dedicated : IO _)
    for t in tasks do
      match t.get with
      | .ok (.ok v) => out := out.push v
      | .ok (.error e) => throw e
      | .error e => throw (toString e)
  return out

/-- How many pages are judged at once. -/
def workers : Nat := 4

def comparePdf (a b : String) (heat : Bool) (dir : System.FilePath) : ExceptT String IO Outcome := do
  if ← sameBytes a b false then return { medium := print, unit := "page", units := #[], bytes := true }
  IO.FS.createDirAll dir
  let na ← pdfPages a
  let nb ← pdfPages b
  let units ← parMap workers ((List.range (max na nb)).toArray.map (· + 1)) fun n => do
    if n > na then return (toString n, { verdict := "visible", reason := "only-in-b" })
    if n > nb then return (toString n, { verdict := "visible", reason := "only-in-a" })
    return (toString n, ← judgePdfPage a b n heat dir)
  return { medium := print, unit := "page", units }

/-- The Playwright module whose Chromium launches, found once a run. -/
def chromium (cache : IO.Ref (Option String)) : ExceptT String IO String := do
  if let some m ← cache.get then return m
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
  let units ← parMap workers (List.range (max sa.size sb.size)).toArray fun i => do
    let label (l : String) := if l.isEmpty then toString (i + 1) else s!"{i + 1} {l}"
    match sa[i]?, sb[i]? with
    | some (la, fa), some (_, fb) => return (label la, ← judgeShots fa fb heat)
    | some (la, _), none => return (label la, { verdict := "visible", reason := "only-in-a" })
    | none, some (lb, _) => return (label lb, { verdict := "visible", reason := "only-in-b" })
    | none, none => return ("", { verdict := "same" })
  return { medium := screen, unit, units }

def compare (a b : String) (heat : Bool) (dir : System.FilePath) (cache : IO.Ref (Option String)) :
    ExceptT String IO Outcome :=
  if a.endsWith ".pdf" && b.endsWith ".pdf" then comparePdf a b heat dir
  else if a.endsWith ".html" && b.endsWith ".html" then compareHtml a b heat dir cache
  else throw "compare two .pdf files or two .html files"

/-! ## The report -/

/-- `x` with `d` decimals. -/
def fixed (x : Float) (d : Nat) : String :=
  let n := (x * (10 ^ d).toFloat).round.toUInt64.toNat
  let frac := toString (n % 10 ^ d)
  if d == 0 then toString n
  else s!"{n / 10 ^ d}." ++ String.ofList (List.replicate (d - frac.length) '0') ++ frac

def header (m : Medium) : String :=
  let common := s!"medium={m.name} distance_mm={fixed m.distanceMm 0} \
acuity_mm={fixed m.acuityMm 4} sample_mm={fixed m.sampleMm 4} black={fixed m.black 2} \
jnd={fixed jnd 3} spot_samples={fixed m.spotSamples 2} reach_samples={fixed m.reach 2}"
  if m.name == "print" then s!"visualdiff: {common} dpi={printDpi} supersample={printSupersample}"
  else s!"visualdiff: {common} viewport={viewportW}x{viewportH} css_px_mm={fixed cssPixelMm 4} \
css_px_arcmin={fixed (cssPixelMm / m.acuityMm) 3} dpr={captureScale}"

def unitLine (unit label : String) (j : Judgement) (heat : Option String) : String :=
  let (n, rest) := match label.splitOn " " with
    | n :: rest => (n, " ".intercalate rest)
    | [] => (label, "")
  let named := if rest.isEmpty then "" else s!" label={rest}"
  let why := if j.reason.isEmpty then "" else s!" reason={j.reason}"
  let measured := if j.verdict == "same" || !j.reason.isEmpty then ""
    else s!" max_de={fixed j.maxDe 4} area_spots={fixed j.area 2} largest_spots={fixed j.largest 2}"
  let map := (heat.map (s!" heatmap={·}")).getD ""
  s!"visualdiff: {unit}={n}{named} verdict={j.verdict}{why}{measured}{map}"

def summaryLine (o : Outcome) : String :=
  let count (v : String) := (o.units.filter (·.2.verdict == v)).size
  s!"visualdiff: result={o.result} units={o.units.size} same={count "same"} \
invisible={count "invisible"} visible={count "visible"}" ++ (if o.bytes then " shortcut=bytes" else "")

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
  IO.println (summaryLine o)

/-! ## The selftest -/

/-- An invented article: `words`, a line of words set `shift` from the margin, a swatch of
colour `swatch`, and `tail`. -/
def fixture (words shift swatch : String) (tail : String := "") : String :=
  "\\documentclass{article}\n\\definecolor{swatch}{HTML}{" ++ swatch ++ "}\n\\begin{document}\n" ++
    words ++ "\n\n\\noindent\\hspace*{" ++ shift ++ "}Shifted, \\textit{slanted} and minimal\n\n" ++
    "\\noindent\\textcolor{swatch}{\\rule{3cm}{1cm}}\n" ++ tail ++ "\\end{document}\n"

def baseWords : String := "Plain words set on an invented page."
def baseSwatch : String := "8AA0C8"

/-- Swatches 0.42 and 3.5 JND from `baseSwatch`. -/
def nearSwatch : String := "8AA3C8"
def farSwatch : String := "6E8CC8"

/-- Each case: its name, its two sources, and whether a reader sees a difference on paper and on
screen, `none` asserting nothing. -/
def cases : List (String × String × String × Option Bool × Option Bool) :=
  let base := fixture baseWords "0pt" baseSwatch
  [("identical", base, base, some false, some false),
   ("shift-0.05pt", base, fixture baseWords "0.05pt" baseSwatch, some false, some false),
   ("shift-1pt", base, fixture baseWords "1pt" baseSwatch, some true, none),
   ("shift-2pt", base, fixture baseWords "2pt" baseSwatch, some true, some true),
   ("tint-below", base, fixture baseWords "0pt" nearSwatch, some false, some false),
   ("tint-above", base, fixture baseWords "0pt" farSwatch, some true, some true),
   ("missing-word", base, fixture "Plain words set on an page." "0pt" baseSwatch, some true, some true),
   ("extra-page", base, fixture baseWords "0pt" baseSwatch "\\newpage\nAnother page.\n", some true,
    some true)]

def hexColor (s : String) : Nat × Nat × Nat :=
  let v := s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0
  (v / 65536, v / 256 % 256, v % 256)

def deltaE (s t : String) : Float :=
  let ((r, g, b), (r', g', b')) := (hexColor s, hexColor t)
  let ((l0, l1, l2), (m0, m1, m2)) := (labUnit r g b, labUnit r' g' b')
  Float.sqrt ((l0 - m0) * (l0 - m0) + (l1 - m1) * (l1 - m1) + (l2 - m2) * (l2 - m2))

/-- A raster `w` samples square: white, a black bar `bw` samples wide from `left` antialiased as
coverage in linear light, and a band of the flat colour `tint`. -/
def bar (w : Nat) (left bw : Float) (tint : Nat × Nat × Nat) : Raster := Id.run do
  let mut rgb := ByteArray.emptyWithCapacity (3 * w * w)
  for y in [0:w] do
    for x in [0:w] do
      let lo := max left x.toFloat
      let hi := min (left + bw) (x.toFloat + 1)
      let cover := if y < w / 2 then max 0 (hi - lo) else 0
      let (r, g, b) := if y ≥ 3 * w / 4 then tint else (255, 255, 255)
      let ink (v : Nat) : UInt8 := (encode (floatAt linear v * (1 - cover))).toUInt8
      rgb := rgb.push (ink r) |>.push (ink g) |>.push (ink b)
  return { w, h := w, rgb }

/-- The judge alone, on drawn rasters at the print medium: bars moved within and beyond the acuity,
and a flat tint moved below and above one JND. -/
def judgeCases : List (String × Raster × Raster × Bool) :=
  let a := print.acuitySamples
  let grey := (200, 200, 200)
  let base := bar 64 20 (3 * a) grey
  let thin := bar 64 20 a grey
  [("bar-0.4-acuity", base, bar 64 (20 + 0.4 * a) (3 * a) grey, false),
   ("bar-0.9-acuity", base, bar 64 (20 + 0.9 * a) (3 * a) grey, false),
   ("bar-1.2-acuity", base, bar 64 (20 + 1.2 * a) (3 * a) grey, true),
   ("hairline-0.3-acuity", thin, bar 64 (20 + 0.3 * a) a grey, false),
   ("hairline-1.2-acuity", thin, bar 64 (20 + 1.2 * a) a grey, true),
   ("flat-tint-below", base, bar 64 20 (3 * a) (206, 200, 200), false),
   ("flat-tint-above", base, bar 64 20 (3 * a) (200, 200, 236), true)]

def leantexBin : String := ".lake/build/bin/leantex"

def selftest : IO UInt32 := do
  let cache ← IO.mkRef none
  let mut bad := 0
  for (name, a, b, expect) in judgeCases do
    let j := judge print false a b
    let ok := (j.verdict == "visible") == expect
    unless ok do bad := bad + 1
    IO.println s!"visualdiff: selftest case={name} medium=judge \
expect={if expect then "visible" else "unseen"} got={j.verdict} max_de={fixed j.maxDe 4} \
largest_spots={fixed j.largest 2} ok={ok}"
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
  for (name, srcA, srcB, onPaper, onScreen) in cases do
    let outcome ← LeanTex.Cli.Host.withScratch fun dir => do
      IO.FS.writeFile (dir / "a.tex") srcA
      IO.FS.writeFile (dir / "b.tex") srcB
      let mut results := #[]
      for ext in ["pdf", "html"] do
        for side in ["a", "b"] do
          discard <| (run leantexBin #["-q", (dir / s!"{side}.tex").toString, "-o",
            (dir / s!"{side}.{ext}").toString]).run
        results := results.push (if ext == "pdf" then "print" else "screen",
          ← (compare (dir / s!"a.{ext}").toString (dir / s!"b.{ext}").toString false (dir / ext)
            cache).run)
      return results
    for (medium, r) in outcome do
      match r with
      | .error e =>
        unjudged := unjudged + 1
        IO.println s!"visualdiff: selftest case={name} medium={medium} unjudged={e}"
      | .ok o =>
        let expect := if medium == "print" then onPaper else onScreen
        let ok := (expect.all (· == o.visible)) && (name != "identical" || o.bytes)
        unless ok do bad := bad + 1
        let worst := o.units.foldl (fun m u => max m u.2.maxDe) 0
        let largest := o.units.foldl (fun m u => max m u.2.largest) 0
        let shown := match expect with | some true => "visible" | some false => "unseen" | none => "either"
        IO.println s!"visualdiff: selftest case={name} medium={medium} expect={shown} got={o.result} \
max_de={fixed worst 4} largest_spots={fixed largest 2} ok={ok}"
  IO.println s!"visualdiff: selftest failed={bad} unjudged={unjudged}"
  return if bad > 0 then 1 else if unjudged > 0 then 2 else 0

end VisualDiff

open VisualDiff in
def main (args : List String) : IO UInt32 := do
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
      unless ← System.FilePath.pathExists f do
        IO.eprintln s!"visualdiff: {f} does not exist"
        return 2
    let cache ← IO.mkRef none
    match ← LeanTex.Cli.Host.withScratch fun dir => (compare a b heatDir.isSome dir cache).run with
    | .error e =>
      IO.eprintln s!"visualdiff: {e}"
      return 2
    | .ok o =>
      report o heatDir
      return if o.visible then 1 else 0
