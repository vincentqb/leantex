/- Oracle for `ContrastSolve.disliked`: its box holds every 8-bit colour Material 3's DislikeAnalyzer
(Palmer & Schloss 2010) flags; after `lake build LeanTex.Core.ContrastSolve`, run
`lake env lean --run scripts/dislike-oracle.lean [--stride N] [--selftest]`. -/
import LeanTex.Core.ContrastSolve

open LeanTex.Core

/-- sRGB channel to linear, ×100 (`ColorUtils.linearized`). -/
def linearized (c : Nat) : Float :=
  let n := c.toFloat / 255.0
  (if n ≤ 0.040449936 then n / 12.92 else Float.pow ((n + 0.055) / 1.055) 2.4) * 100.0

/-- CIELAB L* to Y, ×100 (`ColorUtils.yFromLstar`). -/
def yFromLstar (l : Float) : Float :=
  let ft := (l + 16.0) / 116.0
  100.0 * (if l > 8.0 then ft * ft * ft else l / (24389.0 / 27.0))

/-- Y ×100 to CIELAB L* (`ColorUtils.lstarFromY`). -/
def lstarFromY (y : Float) : Float :=
  let yn := y / 100.0
  if yn > 216.0 / 24389.0 then 116.0 * Float.pow yn (1.0 / 3.0) - 16.0 else (24389.0 / 27.0) * yn

def pi : Float := 3.141592653589793

/-- The library's default viewing conditions (`ViewingConditions.DEFAULT`):
D65, adapting luminance (200/π)·Y(L* 50)/100, background L* 50, average
surround, illuminant not discounted. -/
structure Viewing where
  n : Float
  aw : Float
  nbb : Float
  ncb : Float
  c : Float
  nc : Float
  rgbD : Float × Float × Float
  fl : Float
  z : Float

def viewing : Viewing :=
  let wx := 95.047
  let wy := 100.0
  let wz := 108.883
  let adapting := (200.0 / pi) * yFromLstar 50.0 / 100.0
  let surround := 2.0
  let rW := wx * 0.401288 + wy * 0.650173 + wz * (-0.051461)
  let gW := wx * (-0.250268) + wy * 1.204414 + wz * 0.045854
  let bW := wx * (-0.002079) + wy * 0.048952 + wz * 0.953127
  let f := 0.8 + surround / 10.0
  let c := if f ≥ 0.9 then 0.59 + (0.69 - 0.59) * ((f - 0.9) * 10.0)
    else 0.525 + (0.59 - 0.525) * ((f - 0.8) * 10.0)
  let d0 := f * (1.0 - (1.0 / 3.6) * Float.exp ((-adapting - 42.0) / 92.0))
  let d := if d0 > 1.0 then 1.0 else if d0 < 0.0 then 0.0 else d0
  let rgbD := (d * (100.0 / rW) + 1.0 - d, d * (100.0 / gW) + 1.0 - d, d * (100.0 / bW) + 1.0 - d)
  let k := 1.0 / (5.0 * adapting + 1.0)
  let k4 := k * k * k * k
  let k4F := 1.0 - k4
  let fl := k4 * adapting + 0.1 * k4F * k4F * Float.pow (5.0 * adapting) (1.0 / 3.0)
  let n := yFromLstar 50.0 / wy
  let z := 1.48 + Float.sqrt n
  let nbb := 0.725 / Float.pow n 0.2
  let af (v : Float) : Float := Float.pow (fl * v / 100.0) 0.42
  let rA := 400.0 * af (rgbD.1 * rW) / (af (rgbD.1 * rW) + 27.13)
  let gA := 400.0 * af (rgbD.2.1 * gW) / (af (rgbD.2.1 * gW) + 27.13)
  let bA := 400.0 * af (rgbD.2.2 * bW) / (af (rgbD.2.2 * bW) + 27.13)
  { n, aw := (2.0 * rA + gA + 0.05 * bA) * nbb, nbb, ncb := nbb, c, nc := f, rgbD, fl, z }

/-- HCT hue, chroma and tone of an 8-bit colour. -/
def hct (vc : Viewing) (r g b : Nat) : Float × Float × Float :=
  let rl := linearized r
  let gl := linearized g
  let bl := linearized b
  let x := 0.41233895 * rl + 0.35762064 * gl + 0.18051042 * bl
  let y := 0.2126 * rl + 0.7152 * gl + 0.0722 * bl
  let z := 0.01932141 * rl + 0.11916382 * gl + 0.95034478 * bl
  let rC := 0.401288 * x + 0.650173 * y - 0.051461 * z
  let gC := -0.250268 * x + 1.204414 * y + 0.045854 * z
  let bC := -0.002079 * x + 0.048952 * y + 0.953127 * z
  let rD := vc.rgbD.1 * rC
  let gD := vc.rgbD.2.1 * gC
  let bD := vc.rgbD.2.2 * bC
  let adapt (v : Float) : Float :=
    let af := Float.pow (vc.fl * Float.abs v / 100.0) 0.42
    let sg : Float := if v > 0.0 then 1.0 else if v < 0.0 then -1.0 else 0.0
    sg * 400.0 * af / (af + 27.13)
  let rA := adapt rD
  let gA := adapt gD
  let bA := adapt bD
  let a := (11.0 * rA + -12.0 * gA + bA) / 11.0
  let bb := (rA + gA - 2.0 * bA) / 9.0
  let u := (20.0 * rA + 20.0 * gA + 21.0 * bA) / 20.0
  let p2 := (40.0 * rA + 20.0 * gA + bA) / 20.0
  let deg := Float.atan2 bb a * 180.0 / pi
  let hue := if deg < 0.0 then deg + 360.0 else if deg ≥ 360.0 then deg - 360.0 else deg
  let ac := p2 * vc.nbb
  let j := 100.0 * Float.pow (ac / vc.aw) (vc.c * vc.z)
  let huePrime := if hue < 20.14 then hue + 360.0 else hue
  let eHue := 0.25 * (Float.cos (huePrime * pi / 180.0 + 2.0) + 3.8)
  let p1 := (50000.0 / 13.0) * eHue * vc.nc * vc.ncb
  let t := p1 * Float.sqrt (a * a + bb * bb) / (u + 0.305)
  let alpha := Float.pow t 0.9 * Float.pow (1.64 - Float.pow 0.29 vc.n) 0.73
  (hue, alpha * Float.sqrt (j / 100.0), lstarFromY y)

/-- `DislikeAnalyzer.isDisliked`: hue rounds into 90–111, chroma above 16,
tone below 65. -/
def analyzerFlags (h : Float × Float × Float) : Bool :=
  let hue := h.1.round
  hue ≥ 90.0 && hue ≤ 111.0 && h.2.1.round > 16.0 && h.2.2.round < 65.0

def near (x y tol : Float) : Bool := Float.abs (x - y) ≤ tol

def selftest (vc : Viewing) : IO UInt32 := do
  let red := hct vc 255 0 0
  let olive := hct vc 0x69 0x5F 0x03
  let ochre := hct vc 0xB8 0x8F 0x01
  let checks : List (String × Bool) := [
    ("sRGB red reads as the library reads it", near red.1 27.41 0.05 && near red.2.1 113.36 0.05 &&
      near red.2.2 53.24 0.05),
    ("a dark olive is disliked by both", analyzerFlags olive &&
      ContrastSolve.disliked (({ r := 0x69, g := 0x5F, b := 0x03 } : Ir.Color))),
    ("an ochre just past hue 89 is the analyzer's to keep and the box's to hold",
      !analyzerFlags ochre && ContrastSolve.disliked (({ r := 0xB8, g := 0x8F, b := 0x01 } : Ir.Color)))]
  let mut bad := 0
  for (name, ok) in checks do
    IO.println s!"{if ok then "ok" else "FAIL"}  {name}"
    if !ok then bad := bad + 1
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let vc := viewing
  if args.contains "--selftest" then return ← selftest vc
  let stride := match args with
    | ["--stride", n] => n.toNat?.getD 1
    | _ => 1
  let mut flagged := 0
  let mut held := 0
  let mut missed := 0
  let mut beyond := 0
  let mut i := 0
  while i < 16777216 do
    let r := i / 65536
    let g := (i / 256) % 256
    let b := i % 256
    let a := analyzerFlags (hct vc r g b)
    let e := ContrastSolve.disliked (({ r := r.toUInt8, g := g.toUInt8, b := b.toUInt8 } : Ir.Color))
    if a then flagged := flagged + 1
    if e then held := held + 1
    if a && !e then
      missed := missed + 1
      if missed ≤ 10 then IO.println s!"missed: {r} {g} {b}"
    if e && !a then beyond := beyond + 1
    i := i + stride
  IO.println s!"dislike-oracle: the analyzer flags {flagged}, the box holds {held}, \
{missed} flagged colours outside the box, {beyond} held beyond the analyzer's (stride {stride})"
  return if missed == 0 then 0 else 1
