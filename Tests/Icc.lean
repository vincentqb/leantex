module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.Icc

/-! Invented output profiles, written byte by byte, and the transforms the engine reads from them. -/

private def be16 (n : Nat) : List UInt8 := [n / 256 % 256, n % 256].map UInt8.ofNat

private def be32 (n : Nat) : List UInt8 :=
  [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256].map UInt8.ofNat

private def s15 (v : Int) : List UInt8 := be32 (if v < 0 then (v + 4294967296).toNat else v.toNat)

private def ascii (s : String) : List UInt8 := s.toList.map fun c => UInt8.ofNat c.toNat

private def pad4 (l : List UInt8) : List UInt8 := l ++ List.replicate ((4 - l.length % 4) % 4) 0

/-- A profile of class `prtr` over `space` meeting in `pcs`, its tags in order. -/
def profileOf (major minor : Nat) (space pcs : String) (tags : List (String × List UInt8)) :
    ByteArray := Id.run do
  let blobs := tags.map fun (_, b) => pad4 b
  let start := 128 + 4 + 12 * tags.length
  let mut table : List UInt8 := be32 tags.length
  let mut pos := start
  for ((name, _), b) in tags.zip blobs do
    table := table ++ ascii name ++ be32 pos ++ be32 b.length
    pos := pos + b.length
  let header := [be32 pos, ascii "none", [UInt8.ofNat major, UInt8.ofNat (minor * 16), 0, 0],
    ascii "prtr", ascii space, ascii pcs, List.replicate 12 0, ascii "acsp", List.replicate 24 0,
    be32 0, s15 63190, s15 65536, s15 54061, List.replicate 48 0].flatten
  return ⟨(header ++ table ++ blobs.flatten).toArray⟩

/-- A `desc` tag. -/
def descTag (text : String) : List UInt8 :=
  ascii "desc" ++ [0, 0, 0, 0] ++ be32 (text.length + 1) ++ ascii text ++ [0] ++
    List.replicate (4 + 4 + 2 + 1 + 67) 0

/-- Every grid point of `inputs` inputs at `g` points each, the first input slowest. -/
private def gridPoints (inputs g : Nat) : List (List Nat) :=
  (List.range inputs).foldl (fun acc _ => acc.flatMap fun p => (List.range g).map (p ++ [·])) [[]]

/-- A lut16Type table: identity input and output tables but one, and a grid of `g` points
computing each point's outputs from its coordinates. -/
def mft2 (i o g : Nat) (firstTable : List Nat) (point : List Nat → List Nat) : List UInt8 :=
  let ident := [0, 65535]
  let n := firstTable.length
  let tables := firstTable ++ (List.range (i - 1)).flatMap fun _ =>
    (List.range n).map fun k => k * 65535 / (n - 1)
  ascii "mft2" ++ [0, 0, 0, 0] ++ [UInt8.ofNat i, UInt8.ofNat o, UInt8.ofNat g, 0] ++
    ([65536, 0, 0, 0, 65536, 0, 0, 0, 65536].flatMap s15) ++ be16 n ++ be16 2 ++
    tables.flatMap be16 ++ ((gridPoints i g).flatMap point).flatMap be16 ++
    ((List.range o).flatMap fun _ => ident).flatMap be16

/-- A `para` curve of `kind` with s15Fixed16 parameters. -/
def paraCurve (kind : Nat) (ps : List Int) : List UInt8 :=
  pad4 (ascii "para" ++ [0, 0, 0, 0] ++ be16 kind ++ [0, 0] ++ ps.flatMap s15)

/-- A `curv` table. -/
def curvTable (vs : List Nat) : List UInt8 :=
  pad4 (ascii "curv" ++ [0, 0, 0, 0] ++ be32 vs.length ++ vs.flatMap be16)

/-- A lutAtoBType (`mAB `) or lutBtoAType (`mBA `) table from its parts, each absent when empty. -/
def mab (sig : String) (i o : Nat) (bCurves matrix mCurves clut aCurves : List UInt8) : List UInt8 :=
  Id.run do
  let parts := [bCurves, matrix, mCurves, clut, aCurves]
  let mut offsets : List Nat := []
  let mut body : List UInt8 := []
  for p in parts do
    if p.isEmpty then offsets := offsets ++ [0]
    else
      offsets := offsets ++ [32 + body.length]
      body := body ++ pad4 p
  return ascii sig ++ [0, 0, 0, 0] ++ [UInt8.ofNat i, UInt8.ofNat o, 0, 0] ++
    offsets.flatMap be32 ++ body

/-- A lutAtoBType grid: points per input, precision in bytes, and each point's outputs. -/
def mabClut (grid : List Nat) (width : Nat) (point : List Nat → List Nat) : List UInt8 :=
  let points := grid.foldl (fun acc g => acc.flatMap fun p => (List.range g).map (p ++ [·])) [[]]
  let cell (v : Nat) : List UInt8 := if width == 2 then be16 v else [UInt8.ofNat v]
  pad4 (grid.map UInt8.ofNat ++ List.replicate (16 - grid.length) 0 ++ [UInt8.ofNat width, 0, 0, 0] ++
    (points.flatMap point).flatMap cell)

/-- An invented press's CMYK to CIELAB on a grid of three, lut16Type's legacy encoding: lighter
the less ink, the inks' hues pulling a* and b*. -/
private def pressPoint (p : List Nat) : List Nat :=
  let c := p.getD 0 0
  let m := p.getD 1 0
  let y := p.getD 2 0
  let k := p.getD 3 0
  let L := 65280 * ((4 - c) * (5 - m) * (20 - y) * (5 - 2 * k)) / 2000
  let a : Int := 32768 + 256 * ((35 * (m : Int) - 20 * c - 3 * y) * (2 - (k : Int)) / 2)
  let b : Int := 32768 + 256 * ((42 * (y : Int) - 22 * c - 5 * m) * (2 - (k : Int)) / 2)
  [L, a.toNat, b.toNat]

/-- The invented press's way back, CIELAB to CMYK on a grid of five: ink as the lightness falls,
cyan against red and yellow against blue. -/
private def pressBack (p : List Nat) : List Nat :=
  let L := p.getD 0 0
  let a := p.getD 1 0
  let b := p.getD 2 0
  let shade := (4 - L) * 65535 / 4
  [min 65535 (shade * (8 - a) / 8 + (4 - a) * 4000), min 65535 (shade * a / 8 + a * 3000),
   min 65535 (shade * b / 8 + b * 3000), (4 - L) * (4 - L) * 65535 / 16]

/-- An invented version 2 press profile: lut16Type tables for the colorimetric intent. -/
def press : ByteArray := profileOf 2 1 "CMYK" "Lab "
  [("desc", descTag "Probe Press"), ("A2B1", mft2 4 3 3 [0, 20000, 65535] pressPoint),
   ("B2A1", mft2 3 4 5 [0, 65535] pressBack)]

/-- An invented version 4 press profile: lutAtoBType and lutBtoAType tables whose curves are each
of ICC's parametric families, a table and the identity, a matrix with offsets, a grid of uneven
sides and an 8-bit grid. -/
def pressV4 : ByteArray :=
  let aCurves := paraCurve 0 [117965] ++ paraCurve 3 [157286, 62119, 3417, 5072, 2651] ++
    curvTable [0, 9000, 30000, 50000, 65535] ++ curvTable []
  let mCurves := paraCurve 1 [78643, 65536, 0] ++
    paraCurve 4 [144179, 62259, 3277, 32768, 6554, 1311, 655] ++ paraCurve 2 [65536, 58982, 3277, 0]
  let matrix := ([64225, 1311, 0, 0, 64225, 655, 0, 0, 65536, 0, 262, -197] : List Int).flatMap s15
  let ident := paraCurve 0 [65536] ++ paraCurve 0 [65536] ++ paraCurve 0 [65536]
  let toPcs := mab "mAB " 4 3 ident matrix mCurves
    (mabClut [3, 4, 5, 3] 2 fun p =>
      let (c, m, y, k) := (p.getD 0 0, p.getD 1 0, p.getD 2 0, p.getD 3 0)
      [65535 * ((2 - c) * (3 - m) * (4 - y) * (2 - k) + 24) / 72,
       32896 + 300 * m * (2 - k) - 200 * c, 32896 + 280 * y * (2 - k) - 150 * c])
    aCurves
  let fromPcs := mab "mBA " 3 4 ident
    (([65536, 0, 0, 0, 65536, 0, 0, 0, 65536, 0, 0, 0] : List Int).flatMap s15) ident
    (mabClut [9, 9, 9] 1 fun p =>
      let (L, a, b) := (p.getD 0 0, p.getD 1 0, p.getD 2 0)
      [(8 - L) * (8 - a + 4) * 255 / 96, (8 - L) * (a + 2) * 255 / 80,
       (8 - L) * (b + 2) * 255 / 80, (8 - L) * (8 - L) * 255 / 64])
    (paraCurve 0 [72090] ++ curvTable [] ++ paraCurve 0 [58982] ++ paraCurve 0 [65536])
  profileOf 4 2 "CMYK" "Lab " [("desc", descTag "Probe Press 4"), ("A2B1", toPcs), ("B2A1", fromPcs)]

/-- A percentage of each ink as the 16-bit device values a transform reads. -/
private def inks (c m y k : Nat) : Array Nat := #[c, m, y, k].map fun v => (v * 65535 + 50) / 100

/-- A transform's device values in thousandths. -/
private def milli (vs : Array Nat) : Array Nat := vs.map fun v => (v * 1000 + 32767) / 65535

/-- Within one of each other, channel by channel. -/
private def near (a b : Array Nat) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x ≤ y + 1 && y ≤ x + 1

/-- What LittleCMS 2.19 answers converting relatively colorimetrically (`transicc -t 1`, its sRGB
on the other side) through each invented press: an ink percentage's screen colour, clamped to the
byte, and an sRGB colour's inks in thousandths. -/
private def lcms : List (ByteArray × List ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat)) ×
    List ((Nat × Nat × Nat) × Array Nat)) :=
  [(press,
    [((0, 0, 0, 0), (255, 255, 255)), ((0, 70, 100, 0), (242, 122, 0)),
     ((100, 0, 0, 0), (0, 138, 193)), ((25, 50, 75, 10), (204, 137, 74)),
     ((60, 10, 90, 40), (106, 115, 59)), ((100, 100, 100, 100), (18, 18, 18))],
    [((255, 255, 255), #[125, 93, 93, 1]), ((0, 0, 0), #[872, 342, 342, 1000]),
     ((145, 74, 54), #[509, 296, 290, 373]), ((0, 103, 127), #[617, 206, 203, 382]),
     ((225, 44, 0), #[367, 331, 325, 250]), ((128, 128, 128), #[472, 208, 208, 225])]),
   (pressV4,
    [((0, 0, 0, 0), (44, 255, 250)), ((0, 70, 100, 0), (0, 81, 51)),
     ((100, 0, 0, 0), (0, 81, 65)), ((25, 50, 75, 10), (0, 108, 78)),
     ((60, 10, 90, 40), (0, 88, 63)), ((100, 100, 100, 100), (0, 81, 65))],
    [((255, 255, 255), #[0, 0, 0, 0]), ((0, 0, 0), #[639, 602, 633, 1000]),
     ((145, 74, 54), #[314, 412, 444, 357]), ((0, 103, 127), #[396, 324, 360, 365]),
     ((225, 44, 0), #[209, 405, 438, 246]), ((128, 128, 128), #[274, 277, 315, 216])])]

/-- The engine reads each invented press's colorimetric tables and converts through them as
LittleCMS converts: each screen colour to the byte, each ink to within a thousandth. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  match Icc.Transform.of? press, Icc.Transform.of? pressV4 with
  | some v2, some v4 =>
    t "the version 2 press's tables read: CMYK to CIELAB in lut16Type, and back"
      (v2.space == "CMYK" && v2.pcs == .lab && v2.toPcs.encoding == .legacy16 && v2.fromPcs.isSome)
    t "the version 4 press's tables read: lutAtoBType and lutBtoAType"
      (v4.toPcs.encoding == .normalized && v4.toPcs.stages.size == 5 && v4.fromPcs.isSome)
  | _, _ => t "both invented presses' transforms read" false
  for (bytes, shown, back) in lcms do
    let some tr := Icc.Transform.of? bytes | t "an invented press reads" false
    let name := Icc.description? bytes |>.getD "a press"
    for ((c, m, y, k), srgb) in shown do
      let (r, g, b) := tr.toSrgb (inks c m y k)
      t s!"{name} shows {c}/{m}/{y}/{k} as LittleCMS does" ((r.toNat, g.toNat, b.toNat) == srgb)
    for ((r, g, b), want) in back do
      t s!"{name} prints sRGB {r}/{g}/{b} as LittleCMS does"
        ((tr.fromSrgb (UInt8.ofNat r) (UInt8.ofNat g) (UInt8.ofNat b)).any (near want ∘ milli))
  t "a profile without a device-to-connection table has no transform"
    (Icc.Transform.of? (profileOf 2 1 "CMYK" "Lab " [("desc", descTag "Probe")])).isNone
  t "two transforms of one profile are one, another profile's another"
    ((Icc.Transform.of? press == Icc.Transform.of? press) &&
      !(Icc.Transform.of? press == Icc.Transform.of? pressV4))

end Tests.Icc
