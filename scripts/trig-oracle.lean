/-
The trigonometry oracle for `Gfx.Trig`, the integer CORDIC every figure
producer shares (arcs, rotations, regular polygons). Run it when touching
`Core/Gfx.lean`'s `Trig` or `Kit` sections:

  lake build LeanTex.Core.Gfx && lake env lean --run scripts/trig-oracle.lean

It recomputes the shipped constants from their definitions in binary64 —
`atan(2⁻ⁱ)·2³⁰` for the table, `∏ 1/√(1 + 2⁻²ⁱ)·2³⁰` for the gain, `π·2³⁰` —
and requires each to round to the shipped integer; then sweeps `cosSin`
over angles spanning eight turns (and every multiple of an eighth turn,
where the range reduction folds) against binary64 `cos`/`sin`, and
`atan2` over vectors at eight magnitudes, from one unit up, against
binary64 `atan2` of the same integer vector; and `Kit.arcEndpoint` over
random ellipses, rotations, starts and sweeps, every piece against the
exact ellipse SVG's conversion gives its rounded ends (`arcCentre`,
`arcBound`). The bounds are the
arithmetic's: 31 rotations each floor one unit of x and y and the table
rounds each angle by half a unit — `cosSinBound` and `atanBound` below,
each with its derivation. The first run found `atan2` 0.2° off on a vector
of magnitude 2¹⁰, its floored shifts as coarse as the vector itself; it now
lifts the vector first. Evidence, not a theorem: binary64 is the
reference here, accurate to 2⁻⁵³ relative, far inside the bounds.
-/
import LeanTex.Core.Gfx

open LeanTex.Core

def unitF : Float := 1073741824.0

def piF : Float := 3.141592653589793

/-- The largest error `cosSin` may show, in 2⁻³⁰. Each of the 31 rotations
floors `x` and `y` once, an error vector shorter than √2 that the later
rotations grow by at most ∏ √(1 + 2⁻²ʲ) < 1.6468 — 31·√2·1.6468 < 72.2; the
angle left over after the last rotation, the table's 31 half-unit roundings
and atan 2⁻³⁰, turns the unit vector by under 16.5; the gain's own rounding
grows to under 0.9. 72.2 + 16.5 + 0.9 < 90. -/
def cosSinBound : Float := 90.0

/-- The largest error `atan2` may show, in 2⁻³⁰. The vector is first lifted
to a magnitude of at least 2³⁰ (`Trig.lift`), and rotation only grows it;
each of the 31 floored rotations then moves it by under √2, which turns it
by under √2 units — 31·√2 < 43.9; the table's half-unit roundings add 15.5
and the last residual angle under 1. 43.9 + 15.5 + 1 < 61. -/
def atanBound : Float := 61.0

def roundF (x : Float) : Int :=
  let r := (x + 0.5).floor
  if r < 0 then -(((-r).toUInt64).toNat : Int) else ((r.toUInt64).toNat : Int)

def toF (i : Int) : Float := if i < 0 then -((-i).toNat.toFloat) else i.toNat.toFloat

/-- The largest distance an endpoint arc's piece may stand off its exact
ellipse, measured along that ellipse's radius and scaled by the larger
radius `r` (`ellipseOff`): a cubic through a quarter turn with the control
distance 4/3·tan(δ/4) strays at most 2.73·10⁻⁴ of a circle's radius, and
an ellipse is a circle's affine image, so of `r` (Goldapp 1991); the
integer arithmetic — the centre and each control point rounded once, the
chord's half floored — moves a point under 8 `Sp`, which the measure scales
by the ellipse's eccentricity `r / s`. -/
def arcBound (r s : Float) : Float := 2.73e-4 * r + 8.0 * (r / s)

/-- The centre and radii SVG 2 Appendix B.2.4–5 derive from an endpoint
arc, in binary64: the exact ellipse the integer conversion approximates. -/
def arcCentre (p1 p2 : Float × Float) (rx0 ry0 φ : Float) (large sweep : Bool) :
    (Float × Float) × Float × Float :=
  let c := Float.cos φ
  let s := Float.sin φ
  let hx := (p1.1 - p2.1) / 2
  let hy := (p1.2 - p2.2) / 2
  let x1 := c * hx + s * hy
  let y1 := -(s * hx) + c * hy
  let lam := (x1 * x1) / (rx0 * rx0) + (y1 * y1) / (ry0 * ry0)
  let k := if lam > 1 then Float.sqrt lam else 1
  let rx := rx0 * k
  let ry := ry0 * k
  let num := rx * rx * ry * ry - rx * rx * y1 * y1 - ry * ry * x1 * x1
  let den := rx * rx * y1 * y1 + ry * ry * x1 * x1
  let m := if den == 0 || num ≤ 0 then 0 else Float.sqrt (num / den)
  let m := if large == sweep then -m else m
  let cx1 := m * rx * y1 / ry
  let cy1 := -(m * ry * x1 / rx)
  ((c * cx1 - s * cy1 + (p1.1 + p2.1) / 2, s * cx1 + c * cy1 + (p1.2 + p2.2) / 2), rx, ry)

/-- A point on the cubic from `p0` to `p3` at `t`. -/
def cubicAtF (p0 c1 c2 p3 : Float × Float) (t : Float) : Float × Float :=
  let s := 1 - t
  (s * s * s * p0.1 + 3 * s * s * t * c1.1 + 3 * s * t * t * c2.1 + t * t * t * p3.1,
   s * s * s * p0.2 + 3 * s * s * t * c1.2 + 3 * s * t * t * c2.2 + t * t * t * p3.2)

/-- How far a point stands off the ellipse of centre `c`, radii `(rx, ry)`
turned by `φ`, measured along the ellipse's own radius: the normalized
radius's distance from 1, times the larger radius. -/
def ellipseOff (c : Float × Float) (rx ry φ : Float) (p : Float × Float) : Float :=
  let dx := p.1 - c.1
  let dy := p.2 - c.2
  let x := Float.cos φ * dx + Float.sin φ * dy
  let y := -(Float.sin φ * dx) + Float.cos φ * dy
  let n := Float.sqrt ((x / rx) * (x / rx) + (y / ry) * (y / ry))
  Float.abs (n - 1) * (if rx > ry then rx else ry)

/-- An angle's difference from another, wrapped into (−π, π]. -/
def wrapDiff (a b : Float) : Float := Id.run do
  let mut d := a - b
  while d > piF do d := d - 2 * piF
  while d ≤ -piF do d := d + 2 * piF
  return d

def main : IO UInt32 := do
  let mut failures : Array String := #[]
  -- The shipped constants, recomputed.
  for i in [0:Gfx.Trig.atanTable.size] do
    let want := roundF (Float.atan (Float.pow 2.0 (-(i.toFloat))) * unitF)
    let got := Gfx.Trig.atanTable[i]?.getD 0
    if want != got then failures := failures.push s!"atanTable[{i}] is {got}, recomputed {want}"
  let mut g : Float := 1.0
  for i in [0:Gfx.Trig.atanTable.size] do
    g := g / Float.sqrt (1.0 + Float.pow 2.0 (-(2 * i.toFloat)))
  if roundF (g * unitF) != Gfx.Trig.gain then
    failures := failures.push s!"gain is {Gfx.Trig.gain}, recomputed {roundF (g * unitF)}"
  if roundF (piF * unitF) != Gfx.Trig.pi then
    failures := failures.push s!"pi is {Gfx.Trig.pi}, recomputed {roundF (piF * unitF)}"
  -- cosSin over eight turns, and at every eighth turn and its neighbours.
  let mut worstCS : Float := 0
  let mut worstAt : Int := 0
  let mut samples : Array Int := #[]
  let span : Int := 8 * Gfx.Trig.pi
  let steps : Nat := 200000
  for k in [0:steps + 1] do
    samples := samples.push (-span + 2 * span * (k : Int) / (steps : Int))
  for e in [0:65] do
    let base := (e : Int) * Gfx.Trig.pi / 4 - 8 * Gfx.Trig.pi
    for d in [0:5] do samples := samples.push (base + (d : Int) - 2)
  for θ in samples do
    let (c, s) := Gfx.Trig.cosSin θ
    let θf := toF θ / unitF
    let ec := Float.abs (toF c - Float.cos θf * unitF)
    let es := Float.abs (toF s - Float.sin θf * unitF)
    let e := if ec > es then ec else es
    if e > worstCS then
      worstCS := e
      worstAt := θ
  if worstCS > cosSinBound then
    failures := failures.push s!"cosSin error {worstCS} units at θ = {worstAt} exceeds {cosSinBound}"
  -- atan2 over vectors at five magnitudes, every quadrant and the axes.
  let mut worstAT : Float := 0
  let mut worstV : Int × Int := (0, 0)
  for mag in [1.0, 3.0, 17.0, 1024.0, 65536.0, 16777216.0, 1073741824.0, 68719476736.0] do
    for k in [0:20001] do
      let φ := -piF + 2 * piF * k.toFloat / 20000.0
      let x := roundF (mag * Float.cos φ)
      let y := roundF (mag * Float.sin φ)
      if x == 0 && y == 0 then continue
      let want := Float.atan2 (toF y) (toF x)
      let got := toF (Gfx.Trig.atan2 y x) / unitF
      let e := Float.abs (wrapDiff got want) * unitF
      if e > worstAT then
        worstAT := e
        worstV := (x, y)
  if worstAT > atanBound then
    failures := failures.push s!"atan2 error {worstAT} units at {worstV} exceeds {atanBound}"
  -- Endpoint arcs: ellipses of every proportion, turned, from every start
  -- through every sweep short of a full turn; each piece's start, middle
  -- and end against the ellipse its two ends were read from, and the last
  -- end exactly the declared one.
  let mut worstArc : Float := 0
  let mut arcCount := 0
  let mut seed : UInt64 := 0x9E3779B97F4A7C15
  for _ in [0:6000] do
    let draw (s : UInt64) : UInt64 × Float :=
      let s := s * 6364136223846793005 + 1442695040888963407
      (s, (s >>> 11).toFloat / 9007199254740992.0)
    let (s1, a) := draw seed
    let (s2, b) := draw s1
    let (s3, c) := draw s2
    let (s4, d) := draw s3
    let (s5, e) := draw s4
    seed := s5
    let rx := 65536.0 * (1.0 + 199.0 * a)
    let ry := 65536.0 * (1.0 + 199.0 * b)
    let φ := -piF + 2 * piF * c
    let θ0 := -piF + 2 * piF * d
    let Δ := (if e < 0.5 then -1.0 else 1.0) * (0.05 + (2 * piF - 0.1) * (2 * Float.abs (e - 0.5)))
    let onE (θ : Float) : Float × Float :=
      (Float.cos φ * rx * Float.cos θ - Float.sin φ * ry * Float.sin θ,
       Float.sin φ * rx * Float.cos θ + Float.cos φ * ry * Float.sin θ)
    let p1f := onE θ0
    let p2f := onE (θ0 + Δ)
    let p1 : Gfx.Pt := (roundF p1f.1, roundF p1f.2)
    let p2 : Gfx.Pt := (roundF p2f.1, roundF p2f.2)
    let segs := Gfx.Kit.arcEndpoint p1 (roundF rx) (roundF ry) (roundF (φ * unitF))
      (Float.abs Δ > piF) (Δ > 0) p2
    if p1 == p2 then continue
    arcCount := arcCount + 1
    unless (segs.back?.map Gfx.Seg.endPt) == some p2 do
      failures := failures.push s!"arc from {p1} to {p2} ends at {segs.back?.map Gfx.Seg.endPt}"
    let (centre, erx, ery) := arcCentre (toF p1.1, toF p1.2) (toF p2.1, toF p2.2)
      (toF (roundF rx)) (toF (roundF ry)) φ (Float.abs Δ > piF) (Δ > 0)
    let big := if erx > ery then erx else ery
    let small := if erx > ery then ery else erx
    let mut cur : Float × Float := (toF p1.1, toF p1.2)
    for sg in segs do
      match sg with
      | .cubic c1 c2 q =>
        let fc1 := (toF c1.1, toF c1.2)
        let fc2 := (toF c2.1, toF c2.2)
        let fq := (toF q.1, toF q.2)
        for t in [0.25, 0.5, 0.75, 1.0] do
          let off := ellipseOff centre erx ery φ (cubicAtF cur fc1 fc2 fq t)
          if off > arcBound big small then
            failures := failures.push s!"arc piece off its ellipse by {off} sp (rx {erx}, ry {ery})"
          let rel := off / arcBound big small
          if rel > worstArc then worstArc := rel
        cur := fq
      | .line q => cur := (toF q.1, toF q.2)
  -- The zero vector and the axes, exactly.
  unless Gfx.Trig.atan2 0 0 == 0 && Gfx.Trig.atan2 1 0 == Gfx.Trig.pi / 2 &&
      Gfx.Trig.atan2 (-1) 0 == -(Gfx.Trig.pi / 2) do
    failures := failures.push "atan2 on the axes or the zero vector"
  IO.println s!"trig-oracle: table {Gfx.Trig.atanTable.size} entries, gain, pi recomputed"
  IO.println s!"trig-oracle: cosSin over {samples.size} angles: worst {worstCS} units (bound {cosSinBound})"
  IO.println s!"trig-oracle: atan2 over {8 * 20001} vectors: worst {worstAT} units (bound {atanBound})"
  IO.println s!"trig-oracle: {arcCount} endpoint arcs: worst piece {worstArc} of its bound off its ellipse"
  if failures.isEmpty then
    IO.println "trig-oracle: pass"
    return 0
  for f in failures do IO.eprintln s!"trig-oracle: FAIL {f}"
  return 1
