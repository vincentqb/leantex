module

/-! Integer trigonometry shared by the figure producers and the colour pipeline: CORDIC at 2⁻³⁰ of
a radian, no `Float`; `scripts/trig-oracle.lean` bounds its error. -/

namespace LeanTex.Core.Gfx.Trig

/-- One radian in 2⁻³⁰ units is `2^30`; angles below are in those units. -/
@[expose] public def unit : Int := 1073741824

/-- π·2³⁰, rounded. -/
@[expose] public def pi : Int := 3373259426

/-- atan(2⁻ⁱ)·2³⁰, rounded, i = 0…30 (`scripts/trig-oracle.lean` recomputes
them). -/
public def atanTable : Array Int := #[
  843314857, 497837829, 263043837, 133525159, 67021687, 33543516, 16775851,
  8388437, 4194283, 2097149, 1048576, 524288, 262144, 131072, 65536, 32768,
  16384, 8192, 4096, 2048, 1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1]

/-- The CORDIC gain ∏ 1/√(1 + 2⁻²ⁱ) over the table, ·2³⁰, rounded. -/
public def gain : Int := 652032874

/-- `x >> i` with floor rounding. -/
private def shr (x : Int) (i : Nat) : Int := x / (2 ^ i : Nat)

/-- Rotation-mode CORDIC from `(x, y)` through angle `z`, |z| ≤ π/2. -/
private def rotate (x y z : Int) : Int × Int := Id.run do
  let mut x := x
  let mut y := y
  let mut z := z
  for h : i in [0:atanTable.size] do
    let t := atanTable[i]
    if 0 ≤ z then
      let x' := x - shr y i
      y := y + shr x i
      x := x'
      z := z - t
    else
      let x' := x + shr y i
      y := y - shr x i
      x := x'
      z := z + t
  return (x, y)

/-- `(cos θ, sin θ)` at 2⁻³⁰ for any angle in 2⁻³⁰ radians, exact on the four axes. -/
public def cosSin (θ : Int) : Int × Int :=
  let twoPi := 2 * pi
  let r := θ % twoPi
  let r := if r > pi then r - twoPi else r
  let half := pi / 2
  if r = 0 then (unit, 0)
  else if r = half then (0, unit)
  else if r = -half then (0, -unit)
  else if r = pi then (-unit, 0)
  else if r > half then
    let (c, s) := rotate gain 0 (r - pi)
    (-c, -s)
  else if r < -half then
    let (c, s) := rotate gain 0 (r + pi)
    (-c, -s)
  else rotate gain 0 r

/-- Vectoring-mode CORDIC: the angle of `(x, y)` with `x > 0`. -/
private def vector (x y : Int) : Int := Id.run do
  let mut x := x
  let mut y := y
  let mut z : Int := 0
  for h : i in [0:atanTable.size] do
    let t := atanTable[i]
    if y < 0 then
      let x' := x - shr y i
      y := y + shr x i
      x := x'
      z := z - t
    else
      let x' := x + shr y i
      y := y - shr x i
      x := x'
      z := z + t
  return z

/-- A vector scaled by a power of two until its larger coordinate stands in `[2³⁰, 2³¹)`. -/
private def lift (x y : Int) : Int × Int :=
  let m := max x.natAbs y.natAbs
  if m == 0 || m ≥ 2 ^ 30 then (x, y) else
  let k := 30 - m.log2
  (x * ((2 ^ k : Nat) : Int), y * ((2 ^ k : Nat) : Int))

/-- `atan2 y x` in 2⁻³⁰ radians, in (−π, π]; `atan2 0 0 = 0`. -/
public def atan2 (y0 x0 : Int) : Int :=
  let v := lift x0 y0
  let x := v.1
  let y := v.2
  if x > 0 then vector x y
  else if x < 0 then
    if 0 ≤ y then vector (-x) (-y) + pi else vector (-x) (-y) - pi
  else if y > 0 then pi / 2
  else if y < 0 then -(pi / 2)
  else 0

/-- `⌊√n⌋`. -/
public def isqrt (n : Nat) : Nat := n.sqrt

/-- `n / d` rounded to the nearest integer, half away from zero (`d > 0`). -/
public def divRound (n d : Int) : Int :=
  if n < 0 then -((-n + d / 2) / d) else (n + d / 2) / d

end LeanTex.Core.Gfx.Trig
