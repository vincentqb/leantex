module

public import LeanTex.Core.Color
import LeanTex.Core.Trig

/-! Oklab [Ottosson2020] as integer arithmetic over 8-bit `Color` ([CSSColor4] §19), for covering
and derived colours: mixes toward an achromatic surface keep hue exactly. -/

namespace LeanTex.Core.Oklab

open LeanTex.Core.Ir

/-- The sRGB channel linearisation (WCAG 2.2 = CSS Color 4 §10.2) tabulated: entry `c` scaled
by 10⁷, rounded to nearest. -/
public def channelLinear : Array Nat := #[
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

/-- Binary search for the cube root, the bracket `[lo, hi)` halving each step. -/
private def icbrtGo : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel + 1, n, lo, hi =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if mid ^ 3 ≤ n then icbrtGo fuel n mid hi else icbrtGo fuel n lo mid
    else lo

/-- Cube root, rounded down, for LMS values scaled by 10¹⁸. -/
public def icbrt (n : Nat) : Nat := icbrtGo 20 n 0 1000001

private theorem icbrtGo_spec (fuel n lo hi : Nat) (h1 : lo ^ 3 ≤ n) (h2 : n < hi ^ 3)
    (h3 : lo < hi) (hf : hi ≤ lo + 2 ^ fuel) :
    (icbrtGo fuel n lo hi) ^ 3 ≤ n ∧ n < (icbrtGo fuel n lo hi + 1) ^ 3 := by
  induction fuel generalizing lo hi with
  | zero =>
    have : hi = lo + 1 := by simp at hf; omega
    exact ⟨h1, this ▸ h2⟩
  | succ fuel ih =>
    simp only [icbrtGo]
    split
    · next h =>
      split
      · next hm => exact ih _ hi hm h2 (by omega) (by omega)
      · next hm => exact ih lo _ h1 (by omega) (by omega) (by omega)
    · next h =>
      have : hi = lo + 1 := by omega
      exact ⟨h1, this ▸ h2⟩

public theorem icbrt_spec (n : Nat) (hn : n ≤ 10 ^ 18) :
    (icbrt n) ^ 3 ≤ n ∧ n < (icbrt n + 1) ^ 3 :=
  icbrtGo_spec 20 n 0 1000001 (by simp) (by omega) (by omega) (by omega)

example : icbrt 1000000000000000000 = 1000000 := by decide
example : icbrt (10 ^ 18 - 1) = 999999 := by decide

example : (icbrt (10 ^ 18)) ^ 3 ≤ 10 ^ 18 ∧ 10 ^ 18 < (icbrt (10 ^ 18) + 1) ^ 3 :=
  icbrt_spec _ (Nat.le_refl _)

/-- An Oklab value at fixed scale: 10¹⁸ from `labOf`, 10²⁰ from `labMix`. -/
public structure Lab where
  L : Int
  a : Int
  b : Int
  deriving Repr, BEq

/-- Linear sRGB channels at `channelLinear`'s 10⁷ scale to Oklab at `labOf`'s scale. -/
public def labOfLinear (x y z : Nat) : Lab :=
  let l : Int := icbrt (10 * (4122214708 * x + 5363325363 * y + 514459929 * z))
  let m : Int := icbrt (10 * (2119034982 * x + 6806995451 * y + 1073969567 * z))
  let s : Int := icbrt (10 * (883024619 * x + 2817188376 * y + 6299787005 * z))
  { L := 100 * (2104542553 * l + 7936177850 * m - 40720468 * s)
    a := 100 * (19779984951 * l - 24285922050 * m + 4505937099 * s)
    b := 100 * (259040371 * l + 7827717662 * m - 8086758033 * s) }

/-- sRGB to Oklab with Ottosson's matrices at 10¹⁰, rows normalised so a grey has `a = b = 0`;
no division. -/
public def labOf (c : Color) : Lab :=
  labOfLinear (channelLinear.getD c.r.toNat 0) (channelLinear.getD c.g.toNat 0)
    (channelLinear.getD c.b.toNat 0)

/-- `f`% of `c` over the rest of `bg` per coordinate at the 10²⁰ scale: CSS
`color-mix(in oklab, c f%, bg)`. -/
public def labMix (f : Nat) (c bg : Lab) : Lab :=
  { L := f * c.L + (100 - (f : Int)) * bg.L
    a := f * c.a + (100 - (f : Int)) * bg.a
    b := f * c.b + (100 - (f : Int)) * bg.b }

/-- Binary search for the greatest table entry ≤ v. -/
private def nearestGo (v : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if channelLinear.getD mid 0 ≤ v then nearestGo v fuel mid hi
      else nearestGo v fuel lo mid
    else lo

/-- The 8-bit channel whose linearised value is nearest `v` (10⁻⁷), clamped to the gamut edge. -/
private def nearestChannel (v : Int) : UInt8 :=
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

/-- Oklab at the 10²⁰ `labMix` scale to linear-light sRGB at 10⁻⁷, before any channel is
clamped. -/
private def linearOf (lab : Lab) : Int × Int × Int :=
  let lp := rdiv (10000000000 * lab.L + 3963377774 * lab.a + 2158037573 * lab.b) (10 ^ 24)
  let mp := rdiv (10000000000 * lab.L - 1055613458 * lab.a - 638541728 * lab.b) (10 ^ 24)
  let sp := rdiv (10000000000 * lab.L - 894841775 * lab.a - 12914855480 * lab.b) (10 ^ 24)
  let l := lp ^ 3
  let m := mp ^ 3
  let s := sp ^ 3
  (rdiv (40767416621 * l - 33077115913 * m + 2309699292 * s) (10 ^ 21),
   rdiv (-12684380046 * l + 26097574011 * m - 3413193965 * s) (10 ^ 21),
   rdiv (-41960863 * l - 7034186147 * m + 17076147010 * s) (10 ^ 21))

/-- Oklab at `labMix`'s 10²⁰ scale back to sRGB; a `labOf`-scale value goes through
`toColorOfLab`. -/
private def toColor (lab : Lab) : Color :=
  let (r, g, b) := linearOf lab
  { r := nearestChannel r, g := nearestChannel g, b := nearestChannel b }

/-- `toColor` for a value at `labOf`'s 10¹⁸ scale. -/
public def toColorOfLab (lab : Lab) : Color :=
  toColor { L := 100 * lab.L, a := 100 * lab.a, b := 100 * lab.b }

/-- Whether a value at `labOf`'s 10¹⁸ scale is an sRGB colour, before any clamping. -/
public def labInGamut (lab : Lab) : Bool :=
  let (r, g, b) := linearOf { L := 100 * lab.L, a := 100 * lab.a, b := 100 * lab.b }
  let ok (v : Int) : Bool := decide (0 ≤ v) && decide (v ≤ 10000000)
  ok r && ok g && ok b

/-- The cover of a colour over a surface given in Oklab: `f`% of its own Oklab value. -/
public def coverOver (f : Nat) (bg : Lab) (c : Color) : Color :=
  toColor (labMix f (labOf c) bg)

/-- The cover of a colour: `f`% of its own Oklab value over the surface. -/
public def cover (f : Nat) (bg c : Color) : Color := coverOver f (labOf bg) c

example : cover 38 Color.white Color.black == { r := 0x86, g := 0x86, b := 0x86 } := by
  rw [Color.beq_screen_exact]
  unfold Color.white Color.black
  decide +kernel

/-- Chroma squared, `a² + b²`. -/
public def chromaSq (l : Lab) : Int := l.a * l.a + l.b * l.b

/-- One just-noticeable difference at `labOf`'s scale: ΔEOK 0.02 (CSS Color 4 §14.2.1). -/
public def okJnd : Nat := 2 * 10 ^ 16

/-- The top of `labOf`'s lightness axis. -/
public def lightTop : Int := 10 ^ 18

public theorem labOf_achromatic (c : Color) (hg : c.g = c.r) (hb : c.b = c.r) :
    (labOf c).a = 0 ∧ (labOf c).b = 0 := by
  simp only [labOf, labOfLinear, hg, hb]
  grind

public theorem hue_preserved (f : Nat) (c bg : Color) (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    (labMix f (labOf c) (labOf bg)).a = f * (labOf c).a ∧
    (labMix f (labOf c) (labOf bg)).b = f * (labOf c).b := by
  obtain ⟨ha, hb'⟩ := labOf_achromatic bg hg hb
  simp [labMix, ha, hb']

public theorem chroma_scaled (f : Nat) (c bg : Color) (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    chromaSq (labMix f (labOf c) (labOf bg)) = (f : Int) * f * chromaSq (labOf c) := by
  obtain ⟨h1, h2⟩ := hue_preserved f c bg hg hb
  simp only [chromaSq, h1, h2]
  grind

private theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg.mpr h) (Int.neg_nonneg.mpr h)
    simpa [Int.neg_mul_neg] using this

public theorem chromaSq_nonneg (l : Lab) : 0 ≤ chromaSq l :=
  Int.add_nonneg (mul_self_nonneg l.a) (mul_self_nonneg l.b)

public theorem chroma_reduced (f : Nat) (hf : f ≤ 100) (c bg : Color)
    (hg : bg.g = bg.r) (hb : bg.b = bg.r) :
    chromaSq (labMix f (labOf c) (labOf bg)) ≤ 100 * 100 * chromaSq (labOf c) := by
  rw [chroma_scaled f c bg hg hb]
  have hff : (f : Int) * f ≤ 100 * 100 := by
    have := Nat.mul_le_mul hf hf
    omega
  exact Int.mul_le_mul_of_nonneg_right hff (chromaSq_nonneg _)

public theorem labMix_L (f : Nat) (c s : Lab) :
    (labMix f c s).L = 100 * s.L + (f : Int) * (c.L - s.L) := by
  simp only [labMix, Int.mul_sub, Int.sub_mul]
  generalize (f : Int) * c.L = A
  generalize (f : Int) * s.L = B
  omega

public theorem toward_surface (f : Nat) (hf : f ≤ 100) (c s : Lab) (h : s.L ≤ c.L) :
    100 * s.L ≤ (labMix f c s).L ∧ (labMix f c s).L ≤ 100 * c.L := by
  rw [labMix_L]
  have h1 : 0 ≤ (f : Int) * (c.L - s.L) := Int.mul_nonneg (by omega) (by omega)
  have h2 : (f : Int) * (c.L - s.L) ≤ 100 * (c.L - s.L) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  generalize (f : Int) * (c.L - s.L) = p at h1 h2
  omega

public theorem toward_surface_light (f : Nat) (hf : f ≤ 100) (c s : Lab) (h : c.L ≤ s.L) :
    100 * c.L ≤ (labMix f c s).L ∧ (labMix f c s).L ≤ 100 * s.L := by
  rw [labMix_L]
  have h1 : (f : Int) * (c.L - s.L) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
  have h2 : 100 * (c.L - s.L) ≤ (f : Int) * (c.L - s.L) := by
    have hc : c.L - s.L ≤ 0 := by omega
    have hf' : (f : Int) ≤ 100 := by omega
    exact Int.mul_le_mul_of_nonpos_right hf' hc
  generalize (f : Int) * (c.L - s.L) = p at h1 h2
  omega

/-- The scale of `Okl.f`: `f = fracOne` is the direction's whole length. -/
public def fracOne : Nat := 1048576

/-- A lightness, a hue direction and a chroma fraction, at `labOf`'s scale. -/
public structure Okl where
  L : Int
  a : Int
  b : Int
  f : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The Oklab value an `Okl` names. -/
@[expose] public def Okl.lab (o : Okl) : Lab :=
  { L := o.L, a := (o.f : Int) * o.a / fracOne, b := (o.f : Int) * o.b / fracOne }

/-- The 8-bit colour: each linear channel clamped into the gamut, then quantized. -/
public def Okl.toColor (o : Okl) : Color := toColorOfLab o.lab

public def Okl.inGamut (o : Okl) : Bool := labInGamut o.lab

/-- The WCAG relative luminance (10⁻⁷) of the value's clamped linear channels. -/
public def Okl.luminance (o : Okl) : Nat :=
  let l := o.lab
  let (r, g, b) := linearOf { L := 100 * l.L, a := 100 * l.a, b := 100 * l.b }
  let c (v : Int) : Nat := (max 0 (min 10000000 v)).toNat
  (2126 * c r + 7152 * c g + 722 * c b) / 10000

/-- ΔEOK², at `labOf`'s scale squared. -/
public def distSq (p q : Lab) : Int :=
  (p.L - q.L) * (p.L - q.L) + (p.a - q.a) * (p.a - q.a) + (p.b - q.b) * (p.b - q.b)

/-- A colour vision the engine simulates: typical and the three dichromacies at full severity
(Machado, Oliveira & Fernandes, IEEE TVCG 15(6), 2009). -/
public inductive Vision where
  | typical
  | protan
  | deutan
  | tritan
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Every simulated vision, the typical first. -/
public def Vision.all : List Vision := [.typical, .protan, .deutan, .tritan]

/-- Machado, Oliveira & Fernandes's severity-1.0 matrix on linear sRGB, ×10⁶, row-major. -/
private def Vision.matrix : Vision → Array Int
  | .typical => #[1000000, 0, 0, 0, 1000000, 0, 0, 0, 1000000]
  | .protan => #[152286, 1052583, -204868, 114503, 786281, 99216, -3882, -48116, 1051998]
  | .deutan => #[367322, 860646, -227968, 280085, 672501, 47413, -11820, 42940, 968881]
  | .tritan => #[1255528, -76749, -178779, -78411, 930809, 147602, 4733, 691367, 303900]

/-- A colour as a reader of vision `v` sees it, in Oklab: its linear channels through the vision's
matrix, clamped into the gamut. -/
public def labIn (v : Vision) (c : Color) : Lab :=
  match v with
  | .typical => labOf c
  | _ =>
    let x : Int := channelLinear.getD c.r.toNat 0
    let y : Int := channelLinear.getD c.g.toNat 0
    let z : Int := channelLinear.getD c.b.toNat 0
    let m := v.matrix
    let ch (i : Nat) : Nat :=
      (max 0 (min 10000000 ((m.getD (3 * i) 0 * x + m.getD (3 * i + 1) 0 * y +
        m.getD (3 * i + 2) 0 * z) / 1000000))).toNat
    labOfLinear (ch 0) (ch 1) (ch 2)

/-- How far the shipped colour stands from the value it ships for, squared. -/
public def Okl.clipErrSq (o : Okl) : Int := distSq (labOf o.toColor) o.lab

/-- An acceptable mapping: in gamut, or shipping within one JND of itself. -/
public def Okl.fits (o : Okl) : Bool :=
  o.inGamut || decide (o.clipErrSq < (okJnd : Int) * okJnd)

/-- Bisection of the chroma fraction: `lo` in gamut (or 0), `hi` not, 12 halvings. -/
private def gamutGo (o : Okl) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    if lo + 1 < hi then
      if ({ o with f := (lo + hi) / 2 } : Okl).inGamut then gamutGo o n ((lo + hi) / 2) hi
      else gamutGo o n lo ((lo + hi) / 2)
    else lo

/-- Into the gamut: the colour itself where it is in sRGB, else the largest in-gamut chroma at
its lightness and hue. -/
public def Okl.toGamut (o : Okl) : Okl :=
  if o.inGamut then o else { o with f := gamutGo o 12 0 o.f }

/-- Gamut mapping as CSS Color 4 §14.2 maps a stated colour: itself where it fits, else
`toGamut`. -/
public def Okl.gamutMap (o : Okl) : Okl :=
  if o.fits then o else o.toGamut

private theorem gamutGo_spec (o : Okl) :
    ∀ (n lo hi : Nat), lo ≤ hi → (lo = 0 ∨ ({ o with f := lo } : Okl).inGamut = true) →
      gamutGo o n lo hi ≤ hi ∧
        (gamutGo o n lo hi = 0 ∨ ({ o with f := gamutGo o n lo hi } : Okl).inGamut = true)
  | 0, _, _, h1, h2 => ⟨h1, h2⟩
  | n + 1, lo, hi, h1, h2 => by
    simp only [gamutGo]
    split
    · split
      · rename_i hfit
        have := gamutGo_spec o n ((lo + hi) / 2) hi (by omega) (Or.inr hfit)
        exact ⟨this.1, this.2⟩
      · have := gamutGo_spec o n lo ((lo + hi) / 2) (by omega) h2
        exact ⟨by omega, this.2⟩
    · exact ⟨h1, h2⟩

public theorem Okl.toGamut_between (o : Okl) :
    o.toGamut.L = o.L ∧ o.toGamut.a = o.a ∧ o.toGamut.b = o.b ∧ o.toGamut.f ≤ o.f ∧
      (o.toGamut.inGamut = true ∨ o.toGamut.f = 0) := by
  unfold Okl.toGamut
  split
  · rename_i h
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, Or.inl h⟩
  · have := gamutGo_spec o 12 0 o.f (Nat.zero_le _) (Or.inl rfl)
    refine ⟨rfl, rfl, rfl, this.1, ?_⟩
    rcases this.2 with h | h
    · exact Or.inr h
    · exact Or.inl h

public theorem Okl.gamutMap_between (o : Okl) :
    o.gamutMap.L = o.L ∧ o.gamutMap.a = o.a ∧ o.gamutMap.b = o.b ∧ o.gamutMap.f ≤ o.f ∧
      (o.gamutMap.fits = true ∨ o.gamutMap.f = 0) := by
  unfold Okl.gamutMap
  split
  · rename_i h
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, Or.inl h⟩
  · have := o.toGamut_between
    refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, ?_⟩
    rcases this.2.2.2.2 with h | h
    · exact Or.inl (by simp [Okl.fits, h])
    · exact Or.inr h

public theorem Okl.gamutMap_id (o : Okl) (h : o.inGamut = true) :
    o.gamutMap = o ∧ o.toGamut = o := by
  unfold Okl.gamutMap Okl.toGamut
  simp [Okl.fits, h]

/-- An Oklab value as CSS Color 4 ships it in sRGB: white or black past either end, else
mapped and quantized. -/
public def ofLab (lab : Lab) : Color :=
  (Okl.gamutMap { L := max 0 (min lightTop lab.L), a := lab.a, b := lab.b, f := fracOne }).toColor

/-- Millidegrees as the CORDIC's 2⁻³⁰ radians. -/
private def radOf (milliDeg : Int) : Int := milliDeg * Gfx.Trig.pi / 180000

/-- The Oklab value at lightness `L`, chroma `C` (`labOf`'s scale) and hue `H` in millidegrees:
CSS `oklch(L C H)`. -/
public def ofLch (L C H : Int) : Lab :=
  let cs := Gfx.Trig.cosSin (radOf H)
  { L, a := C * cs.1 / Gfx.Trig.unit, b := C * cs.2 / Gfx.Trig.unit }

/-- A direction's hue in millidegrees, in [0°, 360°); 0 for the neutral axis. -/
public def hueMilli (a b : Int) : Int :=
  let h := Gfx.Trig.atan2 b a * 180000 / Gfx.Trig.pi
  if h < 0 then h + 360000 else h

/-- `(a, b)` turned counter-clockwise by `θ` millidegrees. -/
public def turnBy (θ : Int) (a b : Int) : Int × Int :=
  let cs := Gfx.Trig.cosSin (radOf θ)
  ((a * cs.1 - b * cs.2) / Gfx.Trig.unit, (a * cs.2 + b * cs.1) / Gfx.Trig.unit)

/-- How far a warm hue turns toward red at `depth`: a sine bump over 40°–120°, at most 20°, as
Tailwind's amber and Radix amber darken. -/
public def Okl.turn (H : Int) (depth : Nat) : Int :=
  if H ≤ 40000 ∨ 120000 ≤ H then 0
  else
    let s := max 0 (min (Gfx.Trig.cosSin (radOf ((H - 40000) * 9 / 4))).2 Gfx.Trig.unit)
    min 20000 (20000 * s / Gfx.Trig.unit * (min depth fracOne : Nat) / fracOne)

public theorem Okl.turn_between (H : Int) (depth : Nat) :
    0 ≤ Okl.turn H depth ∧ Okl.turn H depth ≤ 20000 ∧
      (H ≤ 40000 ∨ 120000 ≤ H → Okl.turn H depth = 0) := by
  unfold Okl.turn
  split
  · exact ⟨Int.le_refl _, by decide, fun _ => rfl⟩
  · rename_i hH
    refine ⟨?_, Int.min_le_left _ _, fun h => absurd h hH⟩
    have hs : (0 : Int) ≤ max 0 (min (Gfx.Trig.cosSin (radOf ((H - 40000) * 9 / 4))).2 Gfx.Trig.unit) :=
      Int.le_max_left _ _
    have h1 : (0 : Int) ≤ 20000 * max 0 (min (Gfx.Trig.cosSin (radOf ((H - 40000) * 9 / 4))).2
        Gfx.Trig.unit) / Gfx.Trig.unit :=
      Int.ediv_nonneg (Int.mul_nonneg (by decide) hs) (by decide)
    have h2 := Int.ediv_nonneg (Int.mul_nonneg h1 (Int.natCast_nonneg (min depth fracOne)))
      (Int.natCast_nonneg fracOne)
    exact Int.le_min.mpr ⟨by decide, h2⟩

end LeanTex.Core.Oklab
