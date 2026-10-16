module

public import Init.Data.ByteArray.Basic
import LeanTex.Core.Oklab

namespace LeanTex.Core.Icc

/-! An ICC profile's header, description and colour transforms ([ICC1] §7.2, §9.2, §10), read
from its bytes. -/

/-- The header fields a PDF output intent is judged by. -/
public structure Header where
  /-- The major and minor version, `(4, 2)` for 4.2. -/
  version : Nat × Nat
  /-- The profile class signature, `prtr` for an output device. -/
  deviceClass : String
  /-- The data colour space signature, `CMYK`, `RGB ` or `GRAY`. -/
  colorSpace : String
  deriving Repr, BEq, Inhabited

private def u8 (b : ByteArray) (i : Nat) : Nat := (b[i]?.map (·.toNat)).getD 0

private def u32 (b : ByteArray) (i : Nat) : Nat :=
  ((u8 b i * 256 + u8 b (i + 1)) * 256 + u8 b (i + 2)) * 256 + u8 b (i + 3)

private def sig (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (u8 b (i + k)))

/-- The header of a well-formed profile: its size field the file's length and its `acsp` mark. -/
public def header? (b : ByteArray) : Option Header :=
  if b.size < 132 || u32 b 0 != b.size || sig b 36 != "acsp" then none
  else some { version := (u8 b 8, u8 b 9 / 16), deviceClass := sig b 12, colorSpace := sig b 16 }

/-- The channel count of a data colour space a PDF output intent may name. -/
public def components : String → Option Nat
  | "GRAY" => some 1
  | "RGB " => some 3
  | "CMYK" => some 4
  | _ => none

/-- The tag table's `(offset, size)` for a tag signature. -/
private def tag? (b : ByteArray) (name : String) : Option (Nat × Nat) :=
  let n := u32 b 128
  ((List.range (min n ((b.size - 132) / 12))).find? fun k => sig b (132 + 12 * k) == name).map
    fun k => (u32 b (136 + 12 * k), u32 b (140 + 12 * k))

/-- A `desc` tag's text: v2's textDescriptionType ASCII, or v4's first multiLocalizedUnicode record. -/
public def description? (b : ByteArray) : Option String := do
  let (off, size) ← tag? b "desc"
  guard (off + size ≤ b.size ∧ 12 ≤ size)
  match sig b off with
  | "desc" =>
    let n := u32 b (off + 8)
    guard (off + 12 + n ≤ b.size)
    let cs := ((List.range n).map fun k => u8 b (off + 12 + k)).takeWhile (· != 0)
    return String.ofList (cs.map Char.ofNat)
  | "mluc" =>
    guard (u32 b (off + 8) ≠ 0)
    let len := u32 b (off + 20)
    let start := off + u32 b (off + 24)
    guard (start + len ≤ b.size)
    let units := (List.range (len / 2)).map fun k =>
      u8 b (start + 2 * k) * 256 + u8 b (start + 2 * k + 1)
    return String.ofList ((units.takeWhile (· != 0)).map Char.ofNat)
  | _ => none

/-! ## Colour transforms -/

/-- A channel's curve over [0, 1] at 16 bits: the identity, a sampled table, or one of ICC's
parametric functions with its s15Fixed16 parameters (ICC.1:2010 §10.15, §10.18). -/
public inductive Curve where
  | identity
  | table (samples : Array Nat)
  | parametric (kind : Nat) (params : Array Int)
  deriving Repr, BEq, Inhabited

/-- A colour lookup table: grid points per input, the first input varying slowest, each grid
point's outputs as 16-bit samples, and whether it interpolates linearly in every input, as a table
over CIELAB, which is no cube, does. -/
public structure Clut where
  grid : Array Nat
  outputs : Nat
  samples : Array Nat
  multilinear : Bool
  deriving Repr, BEq, Inhabited

/-- One stage of a transform over 16-bit values. -/
public inductive Stage where
  | curves (cs : Array Curve)
  | clut (c : Clut)
  /-- A 3×3 matrix and its offsets, s15Fixed16, over values normalized to [0, 1]. -/
  | matrix (m : Array Int) (offset : Array Int)
  deriving Repr, BEq, Inhabited

/-- How a tag spells the connection space at its PCS side: lut16Type's legacy 16-bit encoding,
lut8Type's 8-bit one, or lutAtoBType's and lutBtoAType's normalized one (§10.10, §10.11). -/
public inductive Encoding where
  | legacy16
  | legacy8
  | normalized
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A tag's pipeline between device values and the connection space. -/
public structure Lut where
  stages : Array Stage
  inputs : Nat
  outputs : Nat
  encoding : Encoding
  deriving Repr, BEq, Inhabited

/-- The connection space a profile's tags meet in. -/
public inductive Pcs where
  | lab
  | xyz
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The 16-bit whole. -/
private def full : Nat := 65535

/-- One big-endian 16-bit field. -/
private def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i + 1)

/-- One s15Fixed16Number, 65536 the unit. -/
private def s15 (b : ByteArray) (i : Nat) : Int :=
  let v := u32 b i
  if v ≥ 2147483648 then (v : Int) - 4294967296 else v

/-- `num / den` rounded half up, `den` positive. -/
private def rdiv (num : Int) (den : Nat) : Int := (2 * num + den).fdiv (2 * den)

/-- A value clamped to the 16-bit range. -/
private def clamp16 (v : Int) : Nat := if v ≤ 0 then 0 else if (full : Int) ≤ v then full else v.toNat

/-- A sampled table at `x`, its samples spanning [0, 1], linear between neighbours. -/
private def sample (t : Array Nat) (x : Nat) : Nat :=
  if t.size == 0 then x
  else if t.size == 1 then t[0]?.getD x
  else
    let pos := x * (t.size - 1)
    let i := pos / full
    let f := pos % full
    let a := t[i]?.getD 0
    if f == 0 then a
    else
      let b := t[i + 1]?.getD a
      clamp16 (a + rdiv (((b : Int) - a) * f) full)

/-! ### Powers in fixed point, for the parametric curves -/

/-- 2^30, the unit of the fixed-point power. -/
private def one30 : Nat := 1073741824

/-- `2^(2^-i)` at 2^30 for `i` = 1…30, each the square root of the one before. -/
private def expTable : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut v : Nat := 2 * one30
  for _ in [0:30] do
    v := Nat.sqrt (v * one30)
    out := out.push v
  return out

/-- `log2 (x / 2^30)` at 2^30, for `0 < x ≤ 2^30`. -/
private def log2Unit (x : Nat) : Int := Id.run do
  let e := Nat.log2 x
  let mut m := x * 2 ^ 30 / 2 ^ e
  let mut frac : Nat := 0
  for i in [1:31] do
    m := m * m / one30
    if m ≥ 2 * one30 then
      m := m / 2
      frac := frac + 2 ^ (30 - i)
  return ((e : Int) - 30) * one30 + frac

/-- `2^(t / 2^30)` at 2^30, for `t ≤ 0`. -/
private def exp2Unit (t : Int) : Nat := Id.run do
  let n := ((-t) + one30 - 1) / one30
  let f := (t + n * one30).toNat
  let mut r := one30
  for i in [1:31] do
    if f / 2 ^ (30 - i) % 2 == 1 then r := r * (expTable[i - 1]?.getD one30) / one30
  return r / 2 ^ n.toNat

/-- `x ^ g` for `x` in [0, 1] at 2^30 and an s15Fixed16 exponent. -/
private def powUnit (x : Int) (g : Int) : Int :=
  if x ≤ 0 then (if g == 0 then one30 else 0)
  else if g == 65536 then x
  else
    let x := min x one30
    let l := log2Unit x.toNat * g / 65536
    if l > 0 then one30 else exp2Unit l

/-- A parametric curve at `x` (§10.18, Table 65): `g`, then `a`, `b`, `c`, `d`, `e`, `f` as the
function type uses them. -/
private def paramAt (kind : Nat) (ps : Array Int) (x : Nat) : Nat :=
  let p (i : Nat) : Int := ps[i]?.getD 0
  let X : Int := (x * one30 + full / 2) / full
  let lin (a b : Int) : Int := a * X / 65536 + b * 16384
  let pw (base : Int) : Int := powUnit base (p 0)
  let y : Int := match kind with
    | 0 => pw X
    | 1 => let v := lin (p 1) (p 2); if v ≤ 0 then 0 else pw v
    | 2 => let v := lin (p 1) (p 2); (if v ≤ 0 then 0 else pw v) + p 3 * 16384
    | 3 => if X * 65536 ≥ p 4 * one30 then pw (lin (p 1) (p 2)) else p 3 * X / 65536
    | 4 => if X * 65536 ≥ p 4 * one30 then pw (lin (p 1) (p 2)) + p 5 * 16384
        else p 3 * X / 65536 + p 6 * 16384
    | _ => X
  clamp16 (rdiv (y * full) one30)

/-- A curve at `x`. -/
public def Curve.eval : Curve → Nat → Nat
  | .identity, x => x
  | .table t, x => sample t x
  | .parametric k ps, x => paramAt k ps x

/-! ### The lookup table -/

/-- Linear interpolation between two 16-bit values at `f / 65535`. -/
private def lerp (a b f : Nat) : Nat := clamp16 (a + rdiv (((b : Int) - a) * f) full)

/-- A grid coordinate: the cell's lower index and the fraction past it, in 65535ths; the last
point stands as a cell of its own. -/
private def cell (g x : Nat) : Nat × Nat :=
  if x ≥ full || g ≤ 1 then (g - 1, 0) else ((x * (g - 1)) / full, (x * (g - 1)) % full)

/-- The outputs at a grid point's offset. -/
private def gridAt (c : Clut) (base : Nat) : Array Nat :=
  (Array.range c.outputs).map fun o => c.samples[base + o]?.getD 0

/-- The table's strides, outputs times the grid of the inputs after each. -/
private def strides (c : Clut) : Array Nat :=
  (Array.range c.grid.size).map fun d =>
    c.outputs * ((c.grid.extract (d + 1) c.grid.size).foldl (· * ·) 1)

/-- Tetrahedral interpolation over the last three inputs at `base`, as ICC's reference
implementations interpolate three inputs. -/
private def tetra (c : Clut) (st : Array Nat) (d : Nat) (base : Nat) (xs : Array Nat) :
    Array Nat :=
  let (x0, rx) := cell (c.grid[d]?.getD 1) (xs[d]?.getD 0)
  let (y0, ry) := cell (c.grid[d + 1]?.getD 1) (xs[d + 1]?.getD 0)
  let (z0, rz) := cell (c.grid[d + 2]?.getD 1) (xs[d + 2]?.getD 0)
  let sx := st[d]?.getD 0
  let sy := st[d + 1]?.getD 0
  let sz := st[d + 2]?.getD 0
  let o0 := base + x0 * sx + y0 * sy + z0 * sz
  let dx := if rx == 0 then 0 else sx
  let dy := if ry == 0 then 0 else sy
  let dz := if rz == 0 then 0 else sz
  let v (off : Nat) (k : Nat) : Int := c.samples[o0 + off + k]?.getD 0
  (Array.range c.outputs).map fun k =>
    let c0 := v 0 k
    let (c1, c2, c3) : Int × Int × Int :=
      if rx ≥ ry && ry ≥ rz then
        (v dx k - c0, v (dx + dy) k - v dx k, v (dx + dy + dz) k - v (dx + dy) k)
      else if rx ≥ rz && rz ≥ ry then
        (v dx k - c0, v (dx + dy + dz) k - v (dx + dz) k, v (dx + dz) k - v dx k)
      else if rz ≥ rx && rx ≥ ry then
        (v (dx + dz) k - v dz k, v (dx + dy + dz) k - v (dx + dz) k, v dz k - c0)
      else if ry ≥ rx && rx ≥ rz then
        (v (dx + dy) k - v dy k, v dy k - c0, v (dx + dy + dz) k - v (dx + dy) k)
      else if ry ≥ rz && rz ≥ rx then
        (v (dx + dy + dz) k - v (dy + dz) k, v dy k - c0, v (dy + dz) k - v dy k)
      else
        (v (dx + dy + dz) k - v (dy + dz) k, v (dy + dz) k - v dz k, v dz k - c0)
    clamp16 (c0 + rdiv (c1 * rx + c2 * ry + c3 * rz) full)

/-- The table at `xs` from input `d` on: tetrahedral over three inputs, linear and bilinear over
fewer, and linear in each input before the last three, as ICC's reference implementations
interpolate; linear in every input for a multilinear table. -/
private def interp (c : Clut) (st : Array Nat) (xs : Array Nat) : Nat → Nat → Nat → Array Nat
  | 0, _, base => gridAt c base
  | fuel + 1, d, base =>
    let left := c.grid.size - d
    if left == 0 then gridAt c base
    else if left == 3 && !c.multilinear then tetra c st d base xs
    else
      let (i, f) := cell (c.grid[d]?.getD 1) (xs[d]?.getD 0)
      let s := st[d]?.getD 0
      let lo := interp c st xs fuel (d + 1) (base + i * s)
      if f == 0 then lo
      else
        let hi := interp c st xs fuel (d + 1) (base + (i + 1) * s)
        (lo.zip hi).map fun (a, b) => lerp a b f

/-- The table at a point of its inputs. -/
public def Clut.eval (c : Clut) (xs : Array Nat) : Array Nat :=
  interp c (strides c) xs c.grid.size 0 0

/-! ### Pipelines -/

/-- A matrix stage over 16-bit values normalized to [0, 1]. -/
private def matrixAt (m off : Array Int) (xs : Array Nat) : Array Nat :=
  (Array.range 3).map fun i =>
    let row : Int := (List.range 3).foldl (fun acc j =>
      acc + (m[3 * i + j]?.getD 0) * ((xs[j]?.getD 0 : Nat) : Int)) 0
    clamp16 (rdiv row 65536 + rdiv ((off[i]?.getD 0) * full) 65536)

/-- One stage at a point. -/
private def Stage.eval (xs : Array Nat) : Stage → Array Nat
  | .curves cs => xs.zipIdx.map fun (x, i) => ((cs[i]?).getD .identity).eval x
  | .clut c => c.eval xs
  | .matrix m off => matrixAt m off xs

/-- A pipeline at a point of its inputs. -/
public def Lut.eval (l : Lut) (xs : Array Nat) : Array Nat :=
  l.stages.foldl Stage.eval xs

/-! ### Reading the tags -/

/-- A `curv` or `para` element at `off`, and the bytes it spans, 4-aligned. -/
private def curveAt (b : ByteArray) (off : Nat) : Option (Curve × Nat) :=
  match sig b off with
  | "curv" =>
    let n := u32 b (off + 8)
    let size := 12 + 2 * n
    if off + size > b.size then none
    else
      let c := if n == 0 then Curve.identity
        else if n == 1 then .parametric 0 #[(u16 b (off + 12) : Int) * 256]
        else .table ((Array.range n).map fun k => u16 b (off + 12 + 2 * k))
      some (c, (size + 3) / 4 * 4)
  | "para" =>
    let kind := u16 b (off + 8)
    let count := match kind with
      | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 7 | _ => 0
    if count == 0 || off + 12 + 4 * count > b.size then none
    else some (.parametric kind ((Array.range count).map fun k => s15 b (off + 12 + 4 * k)),
      (12 + 4 * count + 3) / 4 * 4)
  | _ => none

/-- `n` curves in sequence from `off`. -/
private def curvesAt (b : ByteArray) (off n : Nat) : Option (Array Curve) := Id.run do
  let mut out : Array Curve := #[]
  let mut pos := off
  for _ in [0:n] do
    match curveAt b pos with
    | some (c, size) =>
      out := out.push c
      pos := pos + size
    | none => return none
  return some out

/-- A lut16Type or lut8Type table at `off` (§10.10, §10.11): its matrix applied only to an XYZ
input, its input tables, grid and output tables. -/
private def lutAt (b : ByteArray) (off : Nat) (xyzIn labIn : Bool) : Option Lut := do
  let wide ← match sig b off with
    | "mft2" => some true
    | "mft1" => some false
    | _ => none
  let i := u8 b (off + 8)
  let o := u8 b (off + 9)
  let g := u8 b (off + 10)
  guard (0 < i ∧ i ≤ 15 ∧ 0 < o ∧ o ≤ 15 ∧ 1 < g)
  let m := (Array.range 9).map fun k => s15 b (off + 12 + 4 * k)
  let (n, mOut, start, width) :=
    if wide then (u16 b (off + 48), u16 b (off + 50), off + 52, 2) else (256, 256, off + 48, 1)
  guard (2 ≤ n ∧ 2 ≤ mOut)
  let points := g ^ i
  guard (start + width * (n * i + points * o + mOut * o) ≤ b.size)
  let read (pos : Nat) : Nat := if wide then u16 b pos else u8 b pos * 257
  let tables (from_ count len : Nat) : Array Curve :=
    (Array.range count).map fun c => .table ((Array.range len).map fun k =>
      read (from_ + width * (c * len + k)))
  let clutAt := start + width * n * i
  let clut : Clut := { grid := Array.replicate i g, outputs := o, multilinear := labIn
                       samples := (Array.range (points * o)).map fun k => read (clutAt + width * k) }
  let outAt := clutAt + width * points * o
  let pre : Array Stage := if xyzIn && i == 3 then #[.matrix m #[0, 0, 0]] else #[]
  return { stages := pre ++ #[.curves (tables start i n), .clut clut, .curves (tables outAt o mOut)]
           inputs := i, outputs := o, encoding := if wide then .legacy16 else .legacy8 }

/-- A lutAtoBType or lutBtoAType table's grid at `off` (§10.12.3). -/
private def clutAt (b : ByteArray) (off i o : Nat) (labIn : Bool) : Option Clut := do
  let grid := (Array.range i).map fun k => u8 b (off + k)
  guard (grid.all (1 < ·))
  let width := u8 b (off + 16)
  guard (width == 1 || width == 2)
  let points := grid.foldl (· * ·) 1
  guard (off + 20 + width * points * o ≤ b.size)
  let read (k : Nat) : Nat :=
    if width == 2 then u16 b (off + 20 + 2 * k) else u8 b (off + 20 + k) * 257
  return { grid, outputs := o, multilinear := labIn, samples := (Array.range (points * o)).map read }

/-- A lutAtoBType (`toPcs`) or lutBtoAType table at `off` (§10.12, §10.13): its A curves, grid,
M curves, matrix and B curves in the order its direction applies them. -/
private def mabAt (b : ByteArray) (off : Nat) (toPcs labIn : Bool) : Option Lut := do
  guard (sig b off == (if toPcs then "mAB " else "mBA "))
  let i := u8 b (off + 8)
  let o := u8 b (off + 9)
  guard (0 < i ∧ i ≤ 15 ∧ 0 < o ∧ o ≤ 15)
  let field (k : Nat) : Nat := u32 b (off + 12 + 4 * k)
  let (bOff, mtxOff, mOff, clutOff, aOff) := (field 0, field 1, field 2, field 3, field 4)
  -- B curves face the connection space, A curves the device.
  let pcsSide := if toPcs then o else i
  let devSide := if toPcs then i else o
  let bCurves ← curvesAt b (off + bOff) pcsSide
  let opt (o' : Nat) (f : Unit → Option Stage) : Option (Array Stage) :=
    if o' == 0 then some #[] else (f ()).map (#[·])
  let mCurves ← opt mOff fun _ => (curvesAt b (off + mOff) pcsSide).map .curves
  let matrix ← opt mtxOff fun _ =>
    if pcsSide != 3 || off + mtxOff + 48 > b.size then none
    else some (.matrix ((Array.range 9).map fun k => s15 b (off + mtxOff + 4 * k))
      ((Array.range 3).map fun k => s15 b (off + mtxOff + 36 + 4 * k)))
  let clut ← opt clutOff fun _ => (clutAt b (off + clutOff) i o labIn).map .clut
  let aCurves ← opt aOff fun _ => (curvesAt b (off + aOff) devSide).map .curves
  let stages := if toPcs then aCurves ++ clut ++ mCurves ++ matrix ++ #[.curves bCurves]
    else #[.curves bCurves] ++ matrix ++ mCurves ++ clut ++ aCurves
  return { stages, inputs := i, outputs := o, encoding := .normalized }

/-- The first of `names` the profile tags with a table this reader reads, its input the connection
space `pcsIn` names where it reads from it. -/
private def tableOf (b : ByteArray) (names : List String) (toPcs : Bool) (pcsIn : Option Pcs) :
    Option Lut :=
  let xyzIn := pcsIn == some .xyz
  let labIn := pcsIn == some .lab
  names.findSome? fun name => (tag? b name).bind fun (off, _) =>
    (lutAt b off xyzIn labIn).orElse fun _ => mabAt b off toPcs labIn

/-! ### The connection space and sRGB -/

/-- A point in CIELAB at 10⁶, or in CIEXYZ relative to the PCS's D50 white at 10⁹. -/
private def labScale : Int := 1000000

private def xyzScale : Int := 1000000000

/-- The PCS illuminant D50's X and Z, as ICC.1 spells them in s15Fixed16 (§7.2.16), its Y the
unit. -/
private def d50X : Int := 63190

private def d50Z : Int := 54061

/-- sRGB's colorants at the PCS's D50 white, as the ICC's sRGB profile tags them, s15Fixed16, by
row: X, Y and Z of red, green and blue. -/
private def srgbColorants : Array Int :=
  #[28576, 25239, 9375, 14581, 46982, 3972, 912, 6361, 46788]

private def mat (m : Array Int) (i j : Nat) : Int := m[3 * i + j]?.getD 0

/-- A 3×3 matrix's adjugate, by row. -/
private def adjugate (m : Array Int) : Array Int :=
  let a := mat m
  #[a 1 1 * a 2 2 - a 1 2 * a 2 1, a 0 2 * a 2 1 - a 0 1 * a 2 2, a 0 1 * a 1 2 - a 0 2 * a 1 1,
    a 1 2 * a 2 0 - a 1 0 * a 2 2, a 0 0 * a 2 2 - a 0 2 * a 2 0, a 0 2 * a 1 0 - a 0 0 * a 1 2,
    a 1 0 * a 2 1 - a 1 1 * a 2 0, a 0 1 * a 2 0 - a 0 0 * a 2 1, a 0 0 * a 1 1 - a 0 1 * a 1 0]

private def determinant (m : Array Int) : Int :=
  let a := mat m
  a 0 0 * (a 1 1 * a 2 2 - a 1 2 * a 2 1) - a 0 1 * (a 1 0 * a 2 2 - a 1 2 * a 2 0) +
    a 0 2 * (a 1 0 * a 2 1 - a 1 1 * a 2 0)

/-- `num / den` rounded half up for a positive or negative denominator. -/
private def rdivI (num den : Int) : Int :=
  if den < 0 then rdiv (-num) (-den).toNat else rdiv num den.toNat

/-- The CIE's `f⁻¹` at 10⁹: `t³` past 6/29, else its linear foot. -/
private def labFinv (t : Int) : Int :=
  if 29 * t > 6 * xyzScale then t * t * t / (xyzScale * xyzScale)
  else (t - 4 * xyzScale / 29) * 108 / 841

/-- CIELAB at 10⁶ to XYZ at 10⁹ relative to D50. -/
private def xyzOfLab (L a b : Int) : Array Int :=
  let fy := (L + 16 * labScale) * 1000 / 116
  let fx := fy + a * 1000 / 500
  let fz := fy - b * 1000 / 200
  #[labFinv fx * d50X / 65536, labFinv fy, labFinv fz * d50Z / 65536]

/-- The CIE's `f` at 10⁹ of a ratio at 10⁹: its cube root past (6/29)³, taken at 10⁶, else its
linear foot. -/
private def labF (r : Int) : Int :=
  if 24389 * r > 216 * xyzScale then
    (Oklab.icbrt (min r.toNat 1000000000 * 1000000000) : Int) * 1000
  else r * 841 / 108 + 4 * xyzScale / 29

/-- XYZ at 10⁹ relative to D50 to CIELAB at 10⁶. -/
private def labOfXyz (xyz : Array Int) : Int × Int × Int :=
  let fx := labF (xyz[0]?.getD 0 * 65536 / d50X)
  let fy := labF (xyz[1]?.getD 0)
  let fz := labF (xyz[2]?.getD 0 * 65536 / d50Z)
  ((116 * fy - 16 * xyzScale) / 1000, 500 * (fx - fy) / 1000, 200 * (fy - fz) / 1000)

/-- Connection-space values a table writes, as XYZ at 10⁹. -/
private def decodePcs (pcs : Pcs) (enc : Encoding) (vs : Array Nat) : Array Int :=
  let v (i : Nat) : Int := vs[i]?.getD 0
  match pcs with
  | .xyz => (Array.range 3).map fun i => v i * xyzScale / 32768
  | .lab =>
    let (L, a, b) := match enc with
      | .legacy16 => (v 0 * 100 * labScale / 65280, v 1 * labScale / 256 - 128 * labScale,
          v 2 * labScale / 256 - 128 * labScale)
      | .legacy8 => (v 0 * 100 * labScale / 65535, v 1 * labScale / 257 - 128 * labScale,
          v 2 * labScale / 257 - 128 * labScale)
      | .normalized => (v 0 * 100 * labScale / 65535, v 1 * 255 * labScale / 65535 - 128 * labScale,
          v 2 * 255 * labScale / 65535 - 128 * labScale)
    xyzOfLab L a b

/-- XYZ at 10⁹ as a table reads the connection space. -/
private def encodePcs (pcs : Pcs) (enc : Encoding) (xyz : Array Int) : Array Nat :=
  match pcs with
  | .xyz => xyz.map fun x => clamp16 (rdivI (x * 32768) xyzScale)
  | .lab =>
    let (L, a, b) := labOfXyz xyz
    match enc with
    | .legacy16 => #[clamp16 (rdivI (L * 65280) (100 * labScale)),
        clamp16 (rdivI ((a + 128 * labScale) * 256) labScale),
        clamp16 (rdivI ((b + 128 * labScale) * 256) labScale)]
    | .legacy8 => #[clamp16 (rdivI (L * 65535) (100 * labScale)),
        clamp16 (rdivI ((a + 128 * labScale) * 257) labScale),
        clamp16 (rdivI ((b + 128 * labScale) * 257) labScale)]
    | .normalized => #[clamp16 (rdivI (L * 65535) (100 * labScale)),
        clamp16 (rdivI ((a + 128 * labScale) * 65535) (255 * labScale)),
        clamp16 (rdivI ((b + 128 * labScale) * 65535) (255 * labScale))]

/-- `(n / d) ^ (12 / 5)` at 10⁹, by the integer fifth root of the twelfth power. -/
private def pow125 (n d : Nat) : Nat := Id.run do
  let target := n ^ 12 * 1000000000 ^ 5 / d ^ 12
  let mut lo : Nat := 0
  let mut hi : Nat := 1000000001
  for _ in [0:32] do
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if mid ^ 5 ≤ target then lo := mid else hi := mid
  return lo

/-- sRGB's transfer function at an encoded `n / d` (IEC 61966-2-1, CSS Color 4 §10.2): linear
light at 10⁹. -/
private def srgbDecode (n d : Nat) : Nat :=
  if 100000 * n ≤ 4045 * d then n * 1000000000 * 100 / (1292 * d)
  else pow125 (200 * n + 11 * d) (211 * d)

/-- Each 8-bit channel's linear light at 10⁹. -/
private def srgbLinear : Array Nat := (Array.range 256).map fun v => srgbDecode v 255

/-- The linear light half way between each two neighbouring 8-bit channels, at 10⁹, below which a
channel rounds down. -/
private def srgbMidpoints : Array Nat := (Array.range 255).map fun v => srgbDecode (2 * v + 1) 510

/-- The 8-bit channel nearest a linear light at 10⁹ in sRGB's encoding, clamped to the gamut. -/
private def srgbByte (v : Int) : UInt8 := Id.run do
  if v ≤ 0 then return 0
  let v := v.toNat
  let mut lo : Nat := 0
  let mut hi : Nat := 255
  for _ in [0:9] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if srgbMidpoints[mid]?.getD 0 ≤ v then lo := mid + 1 else hi := mid
  return UInt8.ofNat lo

/-- XYZ at 10⁹ relative to D50 as sRGB's 8-bit channels, each clamped to the gamut. -/
private def srgbOfXyz (xyz : Array Int) : UInt8 × UInt8 × UInt8 :=
  let adj := adjugate srgbColorants
  let det := determinant srgbColorants
  let ch (i : Nat) : UInt8 :=
    let row := (List.range 3).foldl (fun acc j => acc + mat adj i j * (xyz[j]?.getD 0)) 0
    srgbByte (rdivI (row * 65536) det)
  (ch 0, ch 1, ch 2)

/-- sRGB's 8-bit channels as XYZ at 10⁹ relative to D50. -/
private def xyzOfSrgb (r g b : UInt8) : Array Int :=
  let lin : Array Int := #[(srgbLinear[r.toNat]?.getD 0 : Int), (srgbLinear[g.toNat]?.getD 0 : Int),
    (srgbLinear[b.toNat]?.getD 0 : Int)]
  (Array.range 3).map fun i =>
    (List.range 3).foldl (fun acc j => acc + mat srgbColorants i j * (lin[j]?.getD 0)) 0 / 65536

/-! ### A profile's transform -/

/-- An output profile's colorimetric transforms: device values to the connection space and back,
by the colorimetric intent's tags where the profile carries them, else the perceptual ones. -/
public structure Transform where
  /-- The profile's bytes' content key, by which two transforms compare. -/
  key : UInt64
  /-- The data colour space signature: `CMYK`, `RGB ` or `GRAY`. -/
  space : String
  pcs : Pcs
  toPcs : Lut
  fromPcs : Option Lut

public instance : BEq Transform where
  beq a b := a.key == b.key

public instance : Repr Transform where
  reprPrec t _ := s!"Icc.Transform {t.space} {t.key}"

/-- FNV-1a over the profile's bytes. -/
private def contentKey (b : ByteArray) : UInt64 :=
  b.foldl (fun h v => (h ^^^ v.toUInt64) * 1099511628211) 14695981039346656037

/-- The transforms of a profile whose header this reader reads and whose device-to-connection
table it reads. -/
public def Transform.of? (b : ByteArray) : Option Transform := do
  let h ← header? b
  let n ← components h.colorSpace
  let pcs ← match sig b 20 with
    | "Lab " => some Pcs.lab
    | "XYZ " => some Pcs.xyz
    | _ => none
  let toPcs ← tableOf b ["A2B1", "A2B0"] true none
  guard (toPcs.inputs == n ∧ toPcs.outputs == 3)
  let fromPcs := (tableOf b ["B2A1", "B2A0"] false (some pcs)).filter fun l =>
    l.inputs == 3 && l.outputs == n
  return { key := contentKey b, space := h.colorSpace, pcs, toPcs, fromPcs }

/-- Device values in [0, 1] at 16 bits as the sRGB a screen shows for them. -/
public def Transform.toSrgb (t : Transform) (device : Array Nat) : UInt8 × UInt8 × UInt8 :=
  srgbOfXyz (decodePcs t.pcs t.toPcs.encoding (t.toPcs.eval device))

/-- An sRGB colour as the device values the profile prints it with, where it states the way back. -/
public def Transform.fromSrgb (t : Transform) (r g b : UInt8) : Option (Array Nat) :=
  t.fromPcs.map fun l => l.eval (encodePcs t.pcs l.encoding (xyzOfSrgb r g b))

end LeanTex.Core.Icc
