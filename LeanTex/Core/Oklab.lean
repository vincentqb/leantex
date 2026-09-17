import LeanTex.Core.Ir

/-!
Oklab as pure integer arithmetic over the engine's 8-bit `Color`, for one
purpose: covering. Pending overlay content covers to a fraction of its own
ink mixed toward the surface — per colour, in a perceptual space — so a
covered alert reads as the same orange, quieter, never as a repaint to one
grey. Mixing toward an achromatic surface scales the chromatic coordinates
`(a, b)` by the mix fraction, so hue preservation and chroma reduction are
algebra over these definitions (`hue_preserved`, `chroma_scaled`), not
tolerances.

Sources, and the rule taken from each:

* https://bottosson.github.io/posts/oklab/ (Ottosson, *A perceptual color
  space for image processing*) — the M1/M2 matrices, the cube-root
  nonlinearity, and hue-preserving blends as the design goal.
* https://www.w3.org/TR/css-color-4/ — §19 adopts Oklab with these
  matrices as a normative colour space; §10.2 the sRGB transfer function
  the `channelLinear` table pins (the same linearisation WCAG 2.2's
  relative-luminance formula names, which is why `Contrast` reads the one
  table declared here).
* https://www.w3.org/TR/css-color-5/#color-mix — `color-mix()` interpolates
  in Oklab *by default* (§3.1), so `cover` computes exactly what
  `color-mix(in oklab, ink f%, surface)` means in a browser.
* https://m2.material.io/design/interaction/states.html#disabled —
  Material's disabled state shows content at 38% *opacity*: the ink
  alpha-composited over the surface, per colour. Compositing over an opaque
  surface is linear interpolation toward it, so the rule survives
  translation here; doing it in Oklab rather than gamma-encoded sRGB is
  what keeps the hue.

Everything is `Nat`/`Int` at fixed scales — no floats in core. The forward
direction (`labOf`) does no division at all, so the achromatic-surface
algebra is exact; the inverse (`toColor`) inverts the transfer function by
nearest-entry search over the same `channelLinear` table, so the 8-bit
answer is exact by table and needs no analytic inverse. The end-to-end
identity `cover 100 bg c = c` over all 2²⁴ inputs is checked by
`scripts/oklab-roundtrip.lean` — an executable oracle, not a theorem.
-/

namespace LeanTex.Core.Oklab

open LeanTex.Core.Ir

/-- The sRGB channel linearisation, tabulated: entry `c` is the linearised
value of channel `c` scaled by 10⁷ and rounded to nearest. A table rather
than a `Float` formula so both consumers are total integer arithmetic the
kernel can evaluate inside a theorem — WCAG relative luminance
(`Contrast.luminance`) and the Oklab pipeline below; `Tests.lean` pins
every entry to the spec formula evaluated in `Float`. The formula
(WCAG 2.2 dfn-relative-luminance = CSS Color 4 §10.2): c' = c/255,
c' ≤ 0.04045 → c'/12.92, else ((c'+0.055)/1.055)^2.4. Entries 0–10 take
the first branch (10/255 ≈ 0.0392 ≤ 0.04045). -/
def channelLinear : Array Nat := #[
  0, 3035, 6071, 9106, 12141, 15176, 18212, 21247, 24282, 27317,
  30353, 33465, 36765, 40247, 43914, 47770, 51815, 56054, 60488, 65121,
  69954, 74990, 80232, 85681, 91341, 97212, 103298, 109601, 116122, 122865,
  129830, 137021, 144438, 152085, 159963, 168074, 176420, 185002, 193824, 202886,
  212190, 221739, 231534, 241576, 251869, 262412, 273209, 284260, 295568, 307134,
  318960, 331048, 343398, 356013, 368895, 382044, 395462, 409152, 423114, 437350,
  451862, 466651, 481718, 497066, 512695, 528606, 544803, 561285, 578054, 595112,
  612461, 630100, 648033, 666259, 684782, 703601, 722719, 742136, 761854, 781874,
  802198, 822827, 843762, 865005, 886556, 908417, 930590, 953075, 975873, 998987,
  1022417, 1046165, 1070231, 1094617, 1119324, 1144354, 1169707, 1195384, 1221388, 1247718,
  1274377, 1301365, 1328683, 1356333, 1384316, 1412633, 1441285, 1470273, 1499598, 1529262,
  1559265, 1589608, 1620294, 1651322, 1682694, 1714411, 1746474, 1778884, 1811642, 1844750,
  1878208, 1912017, 1946178, 1980693, 2015563, 2050787, 2086369, 2122308, 2158605, 2195262,
  2232280, 2269659, 2307400, 2345506, 2383976, 2422811, 2462013, 2501583, 2541521, 2581829,
  2622507, 2663556, 2704978, 2746773, 2788943, 2831487, 2874408, 2917706, 2961383, 3005438,
  3049873, 3094689, 3139887, 3185468, 3231432, 3277781, 3324515, 3371636, 3419144, 3467041,
  3515326, 3564001, 3613068, 3662526, 3712377, 3762621, 3813260, 3864294, 3915725, 3967552,
  4019778, 4072402, 4125426, 4178851, 4232677, 4286905, 4341536, 4396572, 4452012, 4507858,
  4564110, 4620770, 4677838, 4735315, 4793202, 4851499, 4910208, 4969330, 5028865, 5088813,
  5149177, 5209956, 5271151, 5332764, 5394795, 5457245, 5520114, 5583404, 5647115, 5711248,
  5775804, 5840784, 5906188, 5972018, 6038273, 6104956, 6172066, 6239604, 6307571, 6375969,
  6444797, 6514056, 6583748, 6653873, 6724432, 6795425, 6866853, 6938718, 7011019, 7083758,
  7156935, 7230551, 7304607, 7379104, 7454042, 7529422, 7605245, 7681511, 7758222, 7835378,
  7912979, 7991027, 8069523, 8148466, 8227858, 8307699, 8387990, 8468732, 8549926, 8631572,
  8713671, 8796224, 8879231, 8962694, 9046612, 9130987, 9215819, 9301109, 9386857, 9473065,
  9559734, 9646862, 9734453, 9822506, 9911021, 10000000]

/-- Binary search on structural fuel: the bracket `[lo, hi)` holds
`lo³ ≤ n < hi³` and halves each step, so the fuel is a bound the spec
discharges — structural recursion, no escape hatch. -/
def icbrtGo : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel + 1, n, lo, hi =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if mid ^ 3 ≤ n then icbrtGo fuel n mid hi else icbrtGo fuel n lo mid
    else lo

/-- Cube root, rounded down, for the Oklab fixed point: LMS values arrive
scaled by 10¹⁸, so results fit in 10⁶ + 1 and 20 halvings close the
bracket. Kernel-reducible (structural fuel), so `decide`-based palette
contracts can evaluate the whole pipeline. -/
def icbrt (n : Nat) : Nat := icbrtGo 20 n 0 1000001

theorem icbrtGo_spec (fuel n lo hi : Nat) (h1 : lo ^ 3 ≤ n) (h2 : n < hi ^ 3)
    (h3 : lo < hi) (hf : hi ≤ lo + 2 ^ fuel) :
    (icbrtGo fuel n lo hi) ^ 3 ≤ n ∧ n < (icbrtGo fuel n lo hi + 1) ^ 3 := by
  induction fuel generalizing lo hi with
  | zero =>
    have : hi = lo + 1 := by simp at hf; omega
    exact ⟨h1, this ▸ h2⟩
  | succ fuel ih =>
    have hp : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by
      rw [Nat.pow_succ]; omega
    simp only [icbrtGo]
    split
    · next h =>
      split
      · next hm => exact ih _ hi hm h2 (by omega) (by omega)
      · next hm => exact ih lo _ h1 (by omega) (by omega) (by omega)
    · next h =>
      have : hi = lo + 1 := by omega
      exact ⟨h1, this ▸ h2⟩

/-- The bracketing spec the fixed-point error bound rests on: `icbrt n` is
the cube root rounded down, exactly. -/
theorem icbrt_spec (n : Nat) (hn : n < 1000000 ^ 3) :
    (icbrt n) ^ 3 ≤ n ∧ n < (icbrt n + 1) ^ 3 :=
  icbrtGo_spec 20 n 0 1000001 (by simp) (by omega) (by omega) (by omega)

-- Kernel-evaluates, the feasibility every `decide` contract below rests on.
example : icbrt 1000000000000000000 = 1000000 := by decide
example : icbrt (10 ^ 18 - 1) = 999999 := by decide

/-- An Oklab value at fixed scale: `labOf` produces coordinates scaled by
10¹⁸ (L in [0, 10¹⁸], a and b in roughly ±4·10¹⁷), `labMix` by 10²⁰. -/
structure Lab where
  L : Int
  a : Int
  b : Int
  deriving Repr, BEq

/-- sRGB to Oklab, forward: linearise by table, the M1 matrix into LMS,
`icbrt` for the cube-root nonlinearity, the M2 matrix into Lab. Matrix
coefficients are Ottosson's (= CSS Color 4 §19) rounded at 10¹⁰, with two
normalisations inside that rounding error so the achromatic algebra is
exact rather than approximate: each M1 row sums to exactly 10¹⁰ (m₂₃ is
+1 from rounding), so equal channels give l = m = s; the a and b rows of
M2 sum to exactly 0 (b₂₃ is −373·10⁻¹⁰ from Ottosson's, under the 10⁻⁶
pipeline granularity), so a grey has a = b = 0 — `labOf_achromatic` is a
theorem, not a measurement. No division anywhere in this direction. -/
def labOf (c : Color) : Lab :=
  let x := channelLinear.getD c.r.toNat 0
  let y := channelLinear.getD c.g.toNat 0
  let z := channelLinear.getD c.b.toNat 0
  let l : Int := icbrt (10 * (4122214708 * x + 5363325363 * y + 514459929 * z))
  let m : Int := icbrt (10 * (2119034982 * x + 6806995451 * y + 1073969567 * z))
  let s : Int := icbrt (10 * (883024619 * x + 2817188376 * y + 6299787005 * z))
  { L := 100 * (2104542553 * l + 7936177850 * m - 40720468 * s)
    a := 100 * (19779984951 * l - 24285922050 * m + 4505937099 * s)
    b := 100 * (259040371 * l + 7827717662 * m - 8086758033 * s) }

/-- The convex combination `f`% of `c` over the rest of `bg`, per
coordinate, kept at the finer 10²⁰ scale so there is no division and the
hue algebra below is exact. This is CSS `color-mix(in oklab, c f%, bg)`
(Color 5 §3.1: Oklab is the default interpolation space). -/
def labMix (f : Nat) (c bg : Lab) : Lab :=
  { L := f * c.L + (100 - (f : Int)) * bg.L
    a := f * c.a + (100 - (f : Int)) * bg.a
    b := f * c.b + (100 - (f : Int)) * bg.b }

/-- Binary search for the greatest table entry ≤ v, on structural fuel:
255 halves to 1 in 8 steps. -/
def nearestGo (v : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if channelLinear.getD mid 0 ≤ v then nearestGo v fuel mid hi
      else nearestGo v fuel lo mid
    else lo

/-- The 8-bit channel whose linearised value is nearest `v` (scale 10⁻⁷):
the transfer function inverted by search over the same table the forward
direction reads, so the answer is exact by table. Out-of-range `v` clamps
to the gamut edge — the standard clip; no shipped role reaches it
(measured, see the 2026-09-17 PLAN entry). -/
def nearestChannel (v : Int) : UInt8 :=
  if v ≤ 0 then 0
  else
    let v := v.toNat
    if 10000000 ≤ v then 255
    else
      let lo := nearestGo v 8 0 255
      let a := channelLinear.getD lo 0
      let b := channelLinear.getD (lo + 1) 0
      if v - a ≤ b - v then UInt8.ofNat lo else UInt8.ofNat (lo + 1)

/-- Round-to-nearest floor division (`d` positive, even). -/
private def rdiv (t d : Int) : Int := (2 * t + d).fdiv (2 * d)

/-- Oklab (at the 10²⁰ `labMix` scale) back to sRGB: the inverse M2 and
inverse LMS matrices (Ottosson), the cube undoing `icbrt`, and
`nearestChannel` undoing the transfer function. Each stage rounds to
nearest; the accumulated error (< 5·10⁻⁵ in linear light, dominated by the
10⁻⁶ cube-root granularity through the ≈7.6 gain of the inverse LMS
matrix) sits well under the half-gap between adjacent table entries
(≥ 1.5·10⁻⁴), which is what makes the round trip an identity —
checked exhaustively by `scripts/oklab-roundtrip.lean`, not assumed. -/
def toColor (lab : Lab) : Color :=
  let lp := rdiv (10000000000 * lab.L + 3963377774 * lab.a + 2158037573 * lab.b) (10 ^ 24)
  let mp := rdiv (10000000000 * lab.L - 1055613458 * lab.a - 638541728 * lab.b) (10 ^ 24)
  let sp := rdiv (10000000000 * lab.L - 894841775 * lab.a - 12914855480 * lab.b) (10 ^ 24)
  let l := lp ^ 3
  let m := mp ^ 3
  let s := sp ^ 3
  { r := nearestChannel (rdiv (40767416621 * l - 33077115913 * m + 2309699292 * s) (10 ^ 21))
    g := nearestChannel (rdiv (-12684380046 * l + 26097574011 * m - 3413193965 * s) (10 ^ 21))
    b := nearestChannel (rdiv (-41960863 * l - 7034186147 * m + 17076147010 * s) (10 ^ 21)) }

/-- The cover of a colour: `f`% of its own Oklab value over the surface —
Material's 38% disabled-state opacity translated to compositing over an
opaque page, computed in the space where mixing preserves hue. Partial
application (`cover f bg`) evaluates the surface once. -/
def cover (f : Nat) (bg : Color) : Color → Color :=
  let bgLab := labOf bg
  fun c => toColor (labMix f (labOf c) bgLab)

-- `decide` below evaluates the pipeline; the limit raised is depth, not trust.
set_option maxRecDepth 8192

-- The measured keystone case: 38% black over white, the byte value the
-- float reference (CSS Color 4 sample code) also lands on. The kernel
-- evaluates the whole pipeline — table, icbrt, both matrix stages, the
-- nearest-entry inversion — inside `decide`.
example : cover 38 Color.white Color.black == { r := 0x86, g := 0x86, b := 0x86 } := by
  decide

/-- Chroma squared, `a² + b²`: chroma itself needs a square root the
theorems below never need — scaling of the square by `f²` is scaling of
chroma by `f`. -/
def chromaSq (l : Lab) : Int := l.a * l.a + l.b * l.b

/-- An exact grey has no chroma: both `(a, b)` coordinates are exactly 0.
Equal channels read one table entry, the normalised M1 rows (each exactly
10¹⁰) make l = m = s, and the normalised a/b rows of M2 (each exactly 0)
annihilate. Both shipped surfaces are exact greys (#FAFAFA, #FFFFFF), so
this hypothesis is the shipped case, not an idealisation. -/
theorem labOf_achromatic (c : Color) (hg : c.g = c.r) (hb : c.b = c.r) :
    (labOf c).a = 0 ∧ (labOf c).b = 0 := by
  simp only [labOf, hg, hb]
  have h1 : 10 * (2119034982 * channelLinear.getD c.r.toNat 0
        + 6806995451 * channelLinear.getD c.r.toNat 0
        + 1073969567 * channelLinear.getD c.r.toNat 0)
      = 10 * (4122214708 * channelLinear.getD c.r.toNat 0
        + 5363325363 * channelLinear.getD c.r.toNat 0
        + 514459929 * channelLinear.getD c.r.toNat 0) := by omega
  have h2 : 10 * (883024619 * channelLinear.getD c.r.toNat 0
        + 2817188376 * channelLinear.getD c.r.toNat 0
        + 6299787005 * channelLinear.getD c.r.toNat 0)
      = 10 * (4122214708 * channelLinear.getD c.r.toNat 0
        + 5363325363 * channelLinear.getD c.r.toNat 0
        + 514459929 * channelLinear.getD c.r.toNat 0) := by omega
  rw [h1, h2]
  constructor <;> omega

/-- Covering preserves hue exactly when the surface is achromatic: the mix
scales both chromatic coordinates by the same non-negative factor `f`, and
hue is their direction (`atan2 b a`), unchanged under positive scaling —
Ottosson's hue-preserving-blend property as algebra over the engine's own
`labMix`, with no tolerance. (The 8-bit quantisation `toColor` applies
afterwards is bounded by the round-trip oracle, measured ≤ 0.5° on every
shipped role.) -/
theorem hue_preserved (f : Nat) (c bg : Color) (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    (labMix f (labOf c) (labOf bg)).a = f * (labOf c).a ∧
    (labMix f (labOf c) (labOf bg)).b = f * (labOf c).b := by
  obtain ⟨ha, hb'⟩ := labOf_achromatic bg hg hb
  simp [labMix, ha, hb']

/-- Chroma scales by exactly the mix fraction over an achromatic surface:
`C(mix) = f · C(c)` stated on squares (the mix is at the 100× finer scale,
so `f²` here is chroma ×(f/100) in real units — at 38%, ×0.38 exactly). -/
theorem chroma_scaled (f : Nat) (c bg : Color) (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    chromaSq (labMix f (labOf c) (labOf bg)) = (f : Int) * f * chromaSq (labOf c) := by
  obtain ⟨h1, h2⟩ := hue_preserved f c bg hg hb
  simp only [chromaSq, h1, h2]
  generalize (labOf c).a = a
  generalize (labOf c).b = b
  calc (f : Int) * a * ((f : Int) * a) + (f : Int) * b * ((f : Int) * b)
      = (f : Int) * f * (a * a) + (f : Int) * f * (b * b) := by
        rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc a, Int.mul_comm a,
          ← Int.mul_assoc b, Int.mul_comm b, Int.mul_assoc, Int.mul_assoc,
          ← Int.mul_assoc (f : Int) (f : Int), ← Int.mul_assoc (f : Int) (f : Int)]
    _ = (f : Int) * f * (a * a + b * b) := by rw [Int.mul_add]

private theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg.mpr h) (Int.neg_nonneg.mpr h)
    simpa [Int.neg_mul_neg] using this

theorem chromaSq_nonneg (l : Lab) : 0 ≤ chromaSq l :=
  Int.add_nonneg (mul_self_nonneg l.a) (mul_self_nonneg l.b)

/-- Covering never adds chroma: at any fraction up to 100%, the covered
chroma is at most the active chroma (both read at the mix's scale). -/
theorem chroma_reduced (f : Nat) (hf : f ≤ 100) (c bg : Color)
    (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    chromaSq (labMix f (labOf c) (labOf bg)) ≤ 100 * 100 * chromaSq (labOf c) := by
  rw [chroma_scaled f c bg hg hb]
  have hff : (f : Int) * f ≤ 100 * 100 := by
    have := Nat.mul_le_mul hf hf
    omega
  exact Int.mul_le_mul_of_nonneg_right hff (chromaSq_nonneg _)

/-- The mix's lightness, isolated: the surface plus `f`% of the way toward
the ink. The identity `toward_surface` rests on. -/
theorem labMix_L (f : Nat) (c s : Lab) :
    (labMix f c s).L = 100 * s.L + (f : Int) * (c.L - s.L) := by
  simp only [labMix, Int.mul_sub, Int.sub_mul]
  generalize (f : Int) * c.L = A
  generalize (f : Int) * s.L = B
  omega

/-- Covering moves toward the surface, definitionally: the covered
lightness lies between the ink's and the surface's (at the mix's 100×
scale), whichever is darker — a dark page covers darker, a light page
covers lighter, never past either. -/
theorem toward_surface (f : Nat) (hf : f ≤ 100) (c s : Lab) (h : s.L ≤ c.L) :
    100 * s.L ≤ (labMix f c s).L ∧ (labMix f c s).L ≤ 100 * c.L := by
  rw [labMix_L]
  have h1 : 0 ≤ (f : Int) * (c.L - s.L) := Int.mul_nonneg (by omega) (by omega)
  have h2 : (f : Int) * (c.L - s.L) ≤ 100 * (c.L - s.L) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  generalize hp : (f : Int) * (c.L - s.L) = p at h1 h2
  omega

end LeanTex.Core.Oklab
