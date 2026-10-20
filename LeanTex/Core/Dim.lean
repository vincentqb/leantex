module

import all Init.Data.ToString.Basic
import all Init.Data.Repr

namespace LeanTex.Core.Dim

/-- Base units per inch: the one place the engine's base unit is defined. -/
@[expose] public def unitsPerInch : Int := 29370528

/-- The engine's one length: an exact count of base units, `unitsPerInch` to the inch. -/
public structure Length where
  ofUnits ::
  units : Int

namespace Length

public instance : DecidableEq Length := fun a b =>
  if h : a.units = b.units then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; cases e; exact h rfl)
public instance : BEq Length := ⟨fun a b => a.units == b.units⟩
public instance : LawfulBEq Length where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq] at h
    simpa using h
  rfl {a} := by cases a; simp [BEq.beq]
public instance : Inhabited Length := ⟨⟨0⟩⟩
public instance : OfNat Length 0 := ⟨⟨0⟩⟩
public instance : Repr Length := ⟨fun l p => reprPrec l.units p⟩
public instance : Hashable Length := ⟨fun l => hash l.units⟩
public instance : Ord Length := ⟨fun a b => compare a.units b.units⟩
public instance : Add Length := ⟨fun a b => ⟨a.units + b.units⟩⟩
public instance : Sub Length := ⟨fun a b => ⟨a.units - b.units⟩⟩
public instance : Neg Length := ⟨fun a => ⟨-a.units⟩⟩
public instance : HMul Int Length Length := ⟨fun k a => ⟨k * a.units⟩⟩
public instance : HMul Nat Length Length := ⟨fun k a => ⟨(k : Int) * a.units⟩⟩
public instance : HMul Length Int Length := ⟨fun a k => ⟨a.units * k⟩⟩
public instance : HMul Length Nat Length := ⟨fun a k => ⟨a.units * (k : Int)⟩⟩
/-- Division by a count rounds as `Int` division does. -/
public instance : HDiv Length Int Length := ⟨fun a k => ⟨a.units / k⟩⟩
public instance : HDiv Length Nat Length := ⟨fun a k => ⟨a.units / (k : Int)⟩⟩
/-- How many whole `b` fit in `a`, as `Int` division rounds. -/
public instance : HDiv Length Length Int := ⟨fun a b => a.units / b.units⟩
/-- The product of two lengths in squared base units, for comparing ratios by cross-multiplying. -/
public instance : HMul Length Length Int := ⟨fun a b => a.units * b.units⟩
public instance : HMod Length Length Length := ⟨fun a b => ⟨a.units % b.units⟩⟩
public instance : LE Length := ⟨fun a b => a.units ≤ b.units⟩
public instance : LT Length := ⟨fun a b => a.units < b.units⟩
public instance (a b : Length) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.units ≤ b.units))
public instance (a b : Length) : Decidable (a < b) := inferInstanceAs (Decidable (a.units < b.units))
public instance : Max Length := ⟨fun a b => ⟨max a.units b.units⟩⟩
public instance : Min Length := ⟨fun a b => ⟨min a.units b.units⟩⟩

@[simp] public theorem units_zero : (0 : Length).units = 0 := rfl
@[simp] public theorem units_add (a b : Length) : (a + b).units = a.units + b.units := rfl
@[simp] public theorem units_sub (a b : Length) : (a - b).units = a.units - b.units := rfl
@[simp] public theorem units_neg (a : Length) : (-a).units = -a.units := rfl
@[simp] public theorem units_imul (k : Int) (a : Length) : (k * a).units = k * a.units := rfl
@[simp] public theorem units_nmul (k : Nat) (a : Length) : (k * a).units = (k : Int) * a.units := rfl
@[simp] public theorem units_muli (a : Length) (k : Int) : (a * k).units = a.units * k := rfl
@[simp] public theorem units_muln (a : Length) (k : Nat) : (a * k).units = a.units * (k : Int) := rfl
@[simp] public theorem units_divi (a : Length) (k : Int) : (a / k).units = a.units / k := rfl
@[simp] public theorem units_divn (a : Length) (k : Nat) : (a / k).units = a.units / (k : Int) := rfl
@[simp] public theorem div_length (a b : Length) : a / b = a.units / b.units := rfl
@[simp] public theorem mul_length (a b : Length) : a * b = a.units * b.units := rfl
@[simp] public theorem units_mod (a b : Length) : (a % b).units = a.units % b.units := rfl
@[simp] public theorem units_max (a b : Length) : (max a b).units = max a.units b.units := rfl
@[simp] public theorem units_min (a b : Length) : (min a b).units = min a.units b.units := rfl
public theorem le_refl (a : Length) : a ≤ a := Int.le_refl _
@[simp] public theorem le_def (a b : Length) : a ≤ b ↔ a.units ≤ b.units := Iff.rfl
@[simp] public theorem lt_def (a b : Length) : a < b ↔ a.units < b.units := Iff.rfl
public theorem ext_iff' (a b : Length) : a = b ↔ a.units = b.units :=
  ⟨fun h => h ▸ rfl, fun h => by cases a; cases b; simp_all⟩
@[simp] public theorem beq_def (a b : Length) : (a == b) = (a.units == b.units) := by
  cases a; cases b; rfl

/-- Truncate toward zero after dividing by `k`, as TeX's `\divide` does (TeX §107). -/
@[expose] public def tdiv (a : Length) (k : Int) : Length := ⟨a.units.tdiv k⟩

@[simp] public theorem units_tdiv (a : Length) (k : Int) : (a.tdiv k).units = a.units.tdiv k := rfl

/-- `a · num / den`, rounded down: scaling by a ratio of lengths. -/
@[expose] public def mulDiv (a num den : Length) : Length := ⟨a.units * num.units / den.units⟩

@[simp] public theorem units_mulDiv (a num den : Length) :
    (a.mulDiv num den).units = a.units * num.units / den.units := rfl

/-- `a · num / den` rounded half away from zero. -/
@[expose] public def scaleRound (a : Length) (num den : Int) : Length :=
  let n := a.units * num
  if n < 0 then ⟨-((-n + den / 2) / den)⟩ else ⟨(n + den / 2) / den⟩

@[expose] public def abs (a : Length) : Length := ⟨(a.units.natAbs : Int)⟩

@[expose] public def sign (a : Length) : Int := a.units.sign

/-- The base unit itself: the rounding quantum, for a bound that must clear rounding. -/
@[expose] public def quantum : Length := ⟨1⟩

@[simp] public theorem units_quantum : quantum.units = 1 := rfl

/-- The exact rational count of base units, for exact affine arithmetic. -/
@[expose] public def toRat (a : Length) : Rat := a.units

/-- A rational count of base units, rounded down. -/
@[expose] public def ofRatFloor (r : Rat) : Length := ⟨r.floor⟩

/-- A rational count of base units, rounded up. -/
@[expose] public def ofRatCeil (r : Rat) : Length := ⟨r.ceil⟩

/-- A rational count of base units, rounded half away from zero. -/
@[expose] public def ofRatRound (r : Rat) : Length :=
  let n := r.num
  let d := (r.den : Int)
  if n < 0 then ⟨-((-n * 2 + d) / (2 * d))⟩ else ⟨(n * 2 + d) / (2 * d)⟩

end Length

/-- Restate every length fact in base units. -/
macro "length_units" : tactic =>
  `(tactic| (try simp only [Length.ext_iff', Length.le_def, Length.lt_def, Length.units_zero,
    Length.units_add, Length.units_sub, Length.units_neg, Length.units_imul, Length.units_nmul,
    Length.units_muli, Length.units_muln, Length.units_divi, Length.units_divn, Length.div_length,
    Length.units_mod, Length.mul_length, Length.units_max, Length.units_min, Length.beq_def,
    Length.units_tdiv, Length.units_quantum, Length.units_mulDiv] at *))

/-- Restate every length fact in base units, then decide it by `omega`. -/
macro "length_omega" : tactic => `(tactic| (length_units; omega))

namespace Length

public theorem add_comm (a b : Length) : a + b = b + a := by length_omega
public theorem add_assoc (a b c : Length) : a + b + c = a + (b + c) := by length_omega
public theorem add_left_comm (a b c : Length) : a + (b + c) = b + (a + c) := by length_omega
public theorem add_right_comm (a b c : Length) : a + b + c = a + c + b := by length_omega
@[simp] public theorem add_zero (a : Length) : a + 0 = a := by length_omega
@[simp] public theorem zero_add (a : Length) : 0 + a = a := by length_omega
@[simp] public theorem sub_zero (a : Length) : a - 0 = a := by length_omega
@[simp] public theorem sub_self (a : Length) : a - a = 0 := by length_omega
@[simp] public theorem neg_neg (a : Length) : - -a = a := by length_omega
@[simp] public theorem neg_zero : -(0 : Length) = 0 := by length_omega
public theorem add_neg_cancel_right (a b : Length) : a + b + -b = a := by length_omega
public theorem add_sub_cancel (a b : Length) : a + b - b = a := by length_omega
public theorem sub_add_cancel (a b : Length) : a - b + b = a := by length_omega
public theorem le_trans {a b c : Length} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Int.le_trans h1 h2
public theorem lt_of_lt_of_le {a b c : Length} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Int.lt_of_lt_of_le h1 h2
public theorem lt_of_le_of_lt {a b c : Length} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  Int.lt_of_le_of_lt h1 h2
public theorem le_of_lt {a b : Length} (h : a < b) : a ≤ b := Int.le_of_lt h
public theorem lt_irrefl (a : Length) : ¬a < a := Int.lt_irrefl _
public theorem le_antisymm {a b : Length} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by length_omega
public theorem not_le {a b : Length} : ¬a ≤ b ↔ b < a := Int.not_le
public theorem not_lt {a b : Length} : ¬a < b ↔ b ≤ a := Int.not_lt
public theorem le_total (a b : Length) : a ≤ b ∨ b ≤ a := Int.le_total _ _
public theorem le_max_left (a b : Length) : a ≤ max a b := by length_omega
public theorem le_max_right (a b : Length) : b ≤ max a b := by length_omega
public theorem min_le_left (a b : Length) : min a b ≤ a := by length_omega
public theorem min_le_right (a b : Length) : min a b ≤ b := by length_omega
public theorem max_comm (a b : Length) : max a b = max b a := by length_omega
public theorem min_comm (a b : Length) : min a b = min b a := by length_omega
public theorem max_le {a b c : Length} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := by length_omega
public theorem le_min {a b c : Length} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ min a b := by length_omega
public theorem add_le_add {a b c d : Length} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  length_omega
public theorem add_le_add_left {a b : Length} (h : a ≤ b) (c : Length) : c + a ≤ c + b := by
  length_omega
public theorem add_le_add_right {a b : Length} (h : a ≤ b) (c : Length) : a + c ≤ b + c := by
  length_omega
public theorem add_lt_add_left {a b : Length} (h : a < b) (c : Length) : c + a < c + b := by
  length_omega
public theorem add_lt_add_right {a b : Length} (h : a < b) (c : Length) : a + c < b + c := by
  length_omega
public theorem sub_le_sub_left {a b : Length} (h : a ≤ b) (c : Length) : c - b ≤ c - a := by
  length_omega
public theorem sub_le_sub_right {a b : Length} (h : a ≤ b) (c : Length) : a - c ≤ b - c := by
  length_omega
public theorem sub_le_sub {a b c d : Length} (h1 : a ≤ b) (h2 : c ≤ d) : a - d ≤ b - c := by
  length_omega
public theorem le_add_of_nonneg_right {a b : Length} (h : 0 ≤ b) : a ≤ a + b := by length_omega
public theorem le_add_of_nonneg_left {a b : Length} (h : 0 ≤ b) : a ≤ b + a := by length_omega
public theorem sub_le_self (a : Length) {b : Length} (h : 0 ≤ b) : a - b ≤ a := by length_omega
public theorem neg_le_neg {a b : Length} (h : a ≤ b) : -b ≤ -a := by length_omega
public theorem le_of_eq {a b : Length} (h : a = b) : a ≤ b := h ▸ le_refl a
public theorem ne_of_lt {a b : Length} (h : a < b) : a ≠ b := by intro e; subst e; exact lt_irrefl _ h
public theorem ne_of_gt {a b : Length} (h : b < a) : a ≠ b := by intro e; subst e; exact lt_irrefl _ h
public theorem lt_of_le_of_ne {a b : Length} (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  have : a.units ≠ b.units := fun e => h2 ((ext_iff' a b).mpr e)
  length_omega
public theorem le_of_not_lt {a b : Length} (h : ¬a < b) : b ≤ a := not_lt.mp h
public theorem lt_of_not_le {a b : Length} (h : ¬a ≤ b) : b < a := not_le.mp h
public theorem max_le_max {a b c d : Length} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d := by
  length_omega
public theorem min_le_min {a b c d : Length} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d := by
  length_omega
public theorem max_eq_left {a b : Length} (h : b ≤ a) : max a b = a := by length_omega
public theorem max_eq_right {a b : Length} (h : a ≤ b) : max a b = b := by length_omega
public theorem min_eq_left {a b : Length} (h : a ≤ b) : min a b = a := by length_omega
public theorem min_eq_right {a b : Length} (h : b ≤ a) : min a b = b := by length_omega
public theorem le_max_of_le_left {a b c : Length} (h : a ≤ b) : a ≤ max b c := by length_omega
public theorem le_max_of_le_right {a b c : Length} (h : a ≤ c) : a ≤ max b c := by length_omega
public theorem min_le_of_left_le {a b c : Length} (h : a ≤ c) : min a b ≤ c := by length_omega
public theorem min_le_of_right_le {a b c : Length} (h : b ≤ c) : min a b ≤ c := by length_omega
public theorem sub_eq_add_neg (a b : Length) : a - b = a + -b := by length_omega
public theorem sub_add_cancel' (a b : Length) : a + (b - a) = b := by length_omega
public theorem add_sub_assoc (a b c : Length) : a + b - c = a + (b - c) := by length_omega
public theorem neg_add (a b : Length) : -(a + b) = -a + -b := by length_omega
public theorem lt_asymm {a b : Length} (h : a < b) : ¬b < a := by length_omega
public theorem le_of_lt_add_quantum {a b : Length} (h : a < b + quantum) : a ≤ b := by length_omega

end Length

@[expose] public def inch (n : Int) : Length := ⟨n * unitsPerInch⟩

/-- The big point and the CSS pixel are whole counts of the base unit. -/
public theorem unitsPerInch_exact : unitsPerInch % 72 = 0 ∧ unitsPerInch % 96 = 0 := by decide

/-- The big point, 1⁄72 in: PDF's and CSS's point. -/
@[expose] public def bp (n : Int) : Length := ⟨n * unitsPerInch / 72⟩

/-- Base units in a big point, PDF's user unit. -/
@[expose] public def bpUnits : Nat := (bp 1).units.toNat

/-- TeX's point, 1⁄72.27 in. -/
@[expose] public def pt (n : Int) : Length := ⟨n * unitsPerInch * 100 / 7227⟩

/-- Millimetres, 1 mm = 10⁄254 in rounded to the base unit. -/
@[expose] public def mm (n : Int) : Length := ⟨n * unitsPerInch * 10 / 254⟩

/-- Hundredths of a millimetre, for standards that specify to 0.01 mm (ISO/IEC 7810's ID-1). -/
@[expose] public def mm100 (n : Int) : Length := ⟨n * unitsPerInch / 2540⟩

/-- The CSS pixel, 1⁄96 in (CSS Values and Units 4 §6.2). -/
@[expose] public def px (n : Int) : Length := ⟨n * unitsPerInch / 96⟩

/-- Thousandths of a big point, rounded half away from zero: the grid PDF and SVG print to. -/
@[expose] public def Length.ofBpMilli (m : Int) : Length :=
  if m < 0 then ⟨-(((-m) * unitsPerInch + 36000) / 72000)⟩ else ⟨(m * unitsPerInch + 36000) / 72000⟩

/-- `num / den` big points, rounded down. -/
@[expose] public def Length.bpFloor (num den : Int) : Length :=
  ⟨Int.fdiv (num * unitsPerInch) (72 * den)⟩

/-- `num / den` big points, rounded up. -/
@[expose] public def Length.bpCeil (num den : Int) : Length :=
  ⟨-Int.fdiv (-(num * unitsPerInch)) (72 * den)⟩

/-- `num / den` of a big point, rounded half up. -/
@[expose] public def Length.bpRound (num den : Nat) : Length :=
  ⟨((num * (unitsPerInch / 72).toNat + den / 2) / den : Nat)⟩

/-- A length `num / den` units of `unit`, rounded down. -/
@[expose] public def Length.ofRatio (unit : Length) (num : Int) (den : Nat) : Length :=
  ⟨unit.units * num / (den : Int)⟩

/-- A length `num / den` units of `unit`, rounded to the nearest: how a reader takes a decimal. -/
@[expose] public def Length.ofRatioRound (unit : Length) (num : Int) (den : Nat) : Length :=
  ⟨(unit.units * num * 2 + (den : Int)) / (2 * (den : Int))⟩

public theorem pt_exact (n : Int) : pt n / pt 1 = n := by
  simp only [pt, unitsPerInch, Length.div_length]
  omega

public theorem bp_units (n : Int) : (bp n).units = n * (bp 1).units := by
  simp only [bp, unitsPerInch]
  omega

public theorem bp_one_pos : 0 < (bp 1).units := by decide

/-- TeX's scaled points in a length, 65536 to the point, rounded to the nearest. -/
@[expose] public def Length.toSp (x : Length) : Int :=
  (x.units * 65536 + (pt 1).units / 2) / (pt 1).units

/-- A count of TeX's scaled points as a length, rounded to the nearest. -/
@[expose] public def Length.ofSp (n : Int) : Length := ⟨((pt 1).units * n + 32768) / 65536⟩

public theorem Length.ofRatioRound_sp (n : Int) : (pt 1).ofRatioRound n 65536 = Length.ofSp n := by
  simp only [Length.ofRatioRound, Length.ofSp, Length.ofUnits.injEq]
  omega

public theorem Length.toSp_ofSp (n : Int) : (Length.ofSp n).toSp = n := by
  simp only [Length.ofSp, Length.toSp, pt, unitsPerInch]
  omega

/-- The length in inches, exactly. -/
@[expose] public def Length.inInches (x : Length) : Rat := (x.units : Rat) / (unitsPerInch : Rat)

/-- A rational count of base units in big points, exactly. -/
@[expose] public def unitsInBp (r : Rat) : Rat := r * 72 / (unitsPerInch : Rat)

public theorem mm_eq_inch (n : Int) : mm (254 * n) = inch (10 * n) := by
  simp only [mm, inch, Length.ofUnits.injEq, unitsPerInch]
  omega

public theorem mm100_eq_mm (n : Int) : mm100 (100 * n) = mm n := by
  simp only [mm100, mm, Length.ofUnits.injEq, unitsPerInch]
  omega

/-- The value `toBpString` spells, in thousandths of a big point, rounded half away from zero. -/
@[expose] public def Length.toBpMilli (x : Length) : Int :=
  if x.units < 0 then -((-x.units * 72000 + unitsPerInch / 2) / unitsPerInch)
  else (x.units * 72000 + unitsPerInch / 2) / unitsPerInch

public theorem Length.toBpMilli_ofBpMilli (m : Int) : (Length.ofBpMilli m).toBpMilli = m := by
  unfold Length.ofBpMilli Length.toBpMilli
  simp only [unitsPerInch]
  split <;> (dsimp only; split <;> omega)

/-- The last `k` decimal digits of `n`, most significant first, zeros kept. -/
@[expose] public def kDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, n => kDigits k (n / 10) ++ [Nat.digitChar (n % 10)]

/-- The `k` digits of a fraction `fr < 10^k`, most significant first, trailing zeros dropped. -/
@[expose] public def fracDigits (k fr : Nat) : List Char :=
  ((kDigits k fr).reverse.dropWhile (· == '0')).reverse

/-- Render as decimal big points, PDF's user unit, with up to three fractional digits (the exact
value rounded to the nearest thousandth, `toBpMilli`). -/
@[expose] public def Length.toBpString (x : Length) : String :=
  let m := x.toBpMilli
  let milli := m.natAbs
  let ip := milli / 1000
  let fr := milli % 1000
  let sign := if m < 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    s!"{sign}{ip}." ++ String.ofList (fracDigits 3 fr)

example : mm 254 = inch 10 := by decide
example : (bp 10).toBpString = "10" := by rfl

/-- The value `toPtString` spells, in thousandths of TeX's point, rounded half away from zero. -/
@[expose] public def Length.toPtMilli (x : Length) : Int :=
  let p := (pt 1).units
  if x.units < 0 then -((-x.units * 2000 + p) / (2 * p)) else (x.units * 2000 + p) / (2 * p)

/-- Render as decimal TeX points with up to three fractional digits (`toPtMilli`). -/
@[expose] public def Length.toPtString (x : Length) : String :=
  let m := x.toPtMilli
  let milli := m.natAbs
  let ip := milli / 1000
  let fr := milli % 1000
  let sign := if m < 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    s!"{sign}{ip}." ++ String.ofList (fracDigits 3 fr)

example : (pt 10).toPtString = "10" := by rfl

/-- A rational `p / q` (`q > 0`) as a decimal rounded once at the ninth digit, half away from
zero: the one matrix-entry printer. -/
@[expose] public def ratString (p q : Int) : String :=
  let neg := p < 0
  let v := (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs
  let ip := v / 1000000000
  let fr := v % 1000000000
  let sign := if neg && v != 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    s!"{sign}{ip}." ++ String.ofList (fracDigits 9 fr)

/-- An exact rational at nine decimals (`ratString`). -/
public def ratDecimal (r : Rat) : String := ratString r.num r.den

/-- A rational count of base units spelled in big points, PDF's user unit, at nine decimals. -/
public def unitsRatBpString (r : Rat) : String := ratString (r.num * 72) ((r.den : Int) * unitsPerInch)

public theorem unitsRatBpString_bp (r : Rat) :
    unitsRatBpString r = ratString (r.num * 72) ((r.den : Int) * 72 * (bpUnits : Int)) := by
  have h : unitsPerInch = 72 * (bpUnits : Int) := by decide
  simp only [unitsRatBpString, h, Int.mul_assoc]

public theorem bpUnits_eq : bpUnits = 407924 := by decide

public theorem inch_div_bp (n : Int) : inch n / (72 : Nat) = bp n := by
  simp only [inch, bp, Length.ext_iff', Length.units_divn]
  rfl

/-- A number's parts `(negative, digits, scale)` in big points as a length, rounded half away from
zero. -/
@[expose] public def Length.ofBpParts (p : Bool × Nat × Nat) : Length :=
  let (neg, n, scale) := p
  let q : Int := ((2 * bpUnits * n + scale) / (2 * scale) : Nat)
  ⟨if neg then -q else q⟩

public theorem pt_eq (n : Int) : pt n = ⟨n * 406400⟩ := by
  simp only [pt, unitsPerInch, Length.ofUnits.injEq]
  omega

public theorem mm_eq (n : Int) : mm n = ⟨n * 1156320⟩ := by
  simp only [mm, unitsPerInch, Length.ofUnits.injEq]
  omega

public theorem px_eq (n : Int) : px n = ⟨n * 305943⟩ := by
  simp only [px, unitsPerInch, Length.ofUnits.injEq]
  omega

public theorem Length.ofBpMilli_units (m : Int) : (Length.ofBpMilli m).units =
    if m < 0 then -(((-m) * bpUnits + 500) / 1000) else (m * bpUnits + 500) / 1000 := by
  have h : (bpUnits : Int) = 407924 := by decide
  unfold Length.ofBpMilli
  simp only [unitsPerInch, h]
  split <;> (dsimp only; omega)


public structure Glue where
  width : Length := 0
  stretch : Length := 0
  shrink : Length := 0
  fil : Bool := false
  /-- Fill that only runs out the rest of a line, yielding to an author's `\hfill`. -/
  parfill : Bool := false
  /-- Interword glue: the space between two words of set text. -/
  word : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Glue.add (a b : Glue) : Glue :=
  { width := a.width + b.width
    stretch := a.stretch + b.stretch
    shrink := a.shrink + b.shrink
    fil := a.fil || b.fil }

public theorem Glue.add_comm (a b : Glue) : a.add b = b.add a := by
  simp only [add, Glue.mk.injEq, Bool.or_comm, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> length_omega

public theorem Glue.add_assoc (a b c : Glue) : (a.add b).add c = a.add (b.add c) := by
  simp only [add, Glue.mk.injEq, Bool.or_assoc, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> length_omega

/-- TeX-style badness: 100·r³ capped at 10000, where r = |delta|/total. -/
@[expose] public def badness (delta total : Length) : Nat :=
  if total.units ≤ 0 then
    10000
  else
    min ((100 * delta.units.natAbs ^ 3) / total.units.natAbs ^ 3) 10000

public theorem badness_le (d t : Length) : badness d t ≤ 10000 := by
  unfold badness
  split
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

/-- A length that may depend on the font: an absolute part plus em and ex parts in thousandths. -/
public structure SymLength where
  fixed : Length := 0
  em : Int := 0
  ex : Int := 0
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace SymLength

@[expose] public def ofLength (v : Length) : SymLength := { fixed := v }

@[expose] public def add (a b : SymLength) : SymLength :=
  { fixed := a.fixed + b.fixed, em := a.em + b.em, ex := a.ex + b.ex }

/-- Componentwise difference, exact. -/
@[expose] public def sub (a b : SymLength) : SymLength :=
  { fixed := a.fixed - b.fixed, em := a.em - b.em, ex := a.ex - b.ex }

/-- Scale by a rational `num/den`, truncating toward zero as TeX's `\divide` and coefficient
scaling do (TeX §107). -/
@[expose] public def scale (l : SymLength) (num : Int) (den : Nat) : SymLength :=
  { fixed := (l.fixed * num).tdiv den
    em := (l.em * num).tdiv den
    ex := (l.ex * num).tdiv den }

/-- Scale by the ratio of two lengths, as `scale` truncates. -/
@[expose] public def scaleRatio (l : SymLength) (num den : Length) : SymLength :=
  l.scale num.units den.units.toNat

/-- Resolve against a font size and x-height. -/
@[expose] public def resolve (l : SymLength) (fontSize xHeight : Length) : Length :=
  l.fixed + l.em * fontSize / 1000 + l.ex * xHeight / 1000

public theorem resolve_ofLength (v fontSize xHeight : Length) :
    (ofLength v).resolve fontSize xHeight = v := by
  simp [resolve, ofLength, Length.ext_iff']

public theorem add_comm (a b : SymLength) : a.add b = b.add a := by
  simp only [add, SymLength.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> length_omega

end SymLength

/-- Glue whose components may be font-relative. -/
public structure SymGlue where
  width : SymLength := {}
  stretch : SymLength := {}
  shrink : SymLength := {}
  /-- First-order infinite stretch, TeX's `fil`; finite components ride beside it. -/
  fil : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace SymGlue

@[expose] public def add (a b : SymGlue) : SymGlue :=
  { width := a.width.add b.width
    stretch := a.stretch.add b.stretch
    shrink := a.shrink.add b.shrink
    fil := a.fil || b.fil }

/-- Componentwise, as `\glueexpr` subtracts glue; an infinite stretch survives subtraction. -/
@[expose] public def sub (a b : SymGlue) : SymGlue :=
  { width := a.width.sub b.width
    stretch := a.stretch.sub b.stretch
    shrink := a.shrink.sub b.shrink
    fil := a.fil || b.fil }

@[expose] public def scale (g : SymGlue) (num : Int) (den : Nat) : SymGlue :=
  { width := g.width.scale num den
    stretch := g.stretch.scale num den
    shrink := g.shrink.scale num den
    fil := g.fil }

/-- Scale by the ratio of two lengths, as `scale` truncates. -/
@[expose] public def scaleRatio (g : SymGlue) (num den : Length) : SymGlue :=
  g.scale num.units den.units.toNat

@[expose] public def resolve (g : SymGlue) (fontSize xHeight : Length) : Glue :=
  { width := g.width.resolve fontSize xHeight
    stretch := g.stretch.resolve fontSize xHeight
    shrink := g.shrink.resolve fontSize xHeight
    fil := g.fil }

end SymGlue

/-- A local measure a length may read, kept distinct until the consumer supplies its context. -/
public inductive Measure where
  | textWidth
  | lineWidth
  | columnWidth
  | textHeight
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The source control word for a local measure. -/
public def Measure.ofName? : String → Option Measure
  | "textwidth" => some .textWidth
  | "linewidth" => some .lineWidth
  | "columnwidth" => some .columnWidth
  | "textheight" => some .textHeight
  | _ => none

/-- A diagnostic label for a typed measure. -/
public def Measure.label : Measure → String
  | .textWidth => "\\textwidth"
  | .lineWidth => "\\linewidth"
  | .columnWidth => "\\columnwidth"
  | .textHeight => "\\textheight"

/-- A typed affine expression whose kept operations preserve TeX's rounding at each scalar
product. -/
public inductive Affine (α : Type) where
  | lit (g : SymGlue)
  | ref (name : α)
  | scale (num : Int) (den : Nat) (e : Affine α)
  | add (a b : Affine α)
  | sub (a b : Affine α)
  deriving Repr, BEq, DecidableEq

public instance [Inhabited α] : Inhabited (Affine α) := ⟨.lit {}⟩

namespace Affine

/-- Canonical rational scaling: equivalent coefficient spellings build the same tree. -/
@[expose] public def scaleQ (num : Int) (den : Nat) (e : Affine α) : Affine α :=
  if den == 0 then .scale num den e
  else
    let g := Nat.gcd num.natAbs den
    .scale (num.tdiv g) (den / g) e

/-- Whether an expression reads a reference satisfying `p`. -/
@[expose] public def anyRef (p : α → Bool) : Affine α → Bool
  | .lit _ => false
  | .ref n => p n
  | .scale _ _ e => anyRef p e
  | .add a b | .sub a b => anyRef p a || anyRef p b

/-- The reference and its permille coefficient when the expression is a non-negative rational
multiple of one `.ref`, else `none`. -/
@[expose] public def refPermille : Affine α → Option (α × Nat)
  | .ref m => some (m, 1000)
  | .scale num den (.ref m) =>
    if den == 0 || num < 0 then none else some (m, num.toNat * 1000 / den)
  | _ => none

/-- Whether every literal is rigid glue. -/
@[expose] public def rigid : Affine α → Bool
  | .lit g => !g.fil && g.stretch == {} && g.shrink == {}
  | .ref _ => true
  | .scale _ _ e => rigid e
  | .add a b | .sub a b => rigid a && rigid b

/-- Whether an expression carries an infinite-stretch literal. -/
@[expose] public def hasFil : Affine α → Bool
  | .lit g => g.fil
  | .ref _ => false
  | .scale _ _ e => hasFil e
  | .add a b | .sub a b => hasFil a || hasFil b

/-- Remove infinite stretch, keeping everything else and the operation order. -/
@[expose] public def withoutFil : Affine α → Affine α
  | .lit g => .lit { g with fil := false }
  | .ref n => .ref n
  | .scale num den e => .scale num den (withoutFil e)
  | .add a b => .add (withoutFil a) (withoutFil b)
  | .sub a b => .sub (withoutFil a) (withoutFil b)

/-- Whether every literal is a rigid absolute length. -/
@[expose] public def rigidAbsolute : Affine α → Bool
  | .lit g => !g.fil && g.stretch == {} && g.shrink == {} &&
      g.width.em == 0 && g.width.ex == 0
  | .ref _ => true
  | .scale _ _ e => rigidAbsolute e
  | .add a b | .sub a b => rigidAbsolute a && rigidAbsolute b

/-- Replace every reference with a typed expression. -/
@[expose] public def bind (f : α → Except ε (Affine β)) : Affine α → Except ε (Affine β)
  | .lit g => .ok (.lit g)
  | .ref n => f n
  | .scale num den e =>
    match bind f e with
    | .ok e' => .ok (.scale num den e')
    | .error x => .error x
  | .add a b =>
    match bind f a, bind f b with
    | .ok a', .ok b' => .ok (.add a' b')
    | .error x, _ => .error x
    | _, .error x => .error x
  | .sub a b =>
    match bind f a, bind f b with
    | .ok a', .ok b' => .ok (.sub a' b')
    | .error x, _ => .error x
    | _, .error x => .error x

/-- Evaluate with a total context. -/
@[expose] public def eval (look : α → SymGlue) : Affine α → SymGlue
  | .lit g => g
  | .ref n => look n
  | .scale num den e => (eval look e).scale num den
  | .add a b => (eval look a).add (eval look b)
  | .sub a b => (eval look a).sub (eval look b)

public theorem eval_names_agree (l₁ l₂ : α → SymGlue) (e : Affine α)
    (h : ∀ n, l₁ n = l₂ n) : eval l₁ e = eval l₂ e := by
  induction e with
  | lit g => rfl
  | ref n => simp [eval, h n]
  | scale num den e ih => simp only [eval, ih]
  | add a b iha ihb => simp only [eval, iha, ihb]
  | sub a b iha ihb => simp only [eval, iha, ihb]

/-- Resolve against one context; an absent variable is returned as that typed variable. -/
@[expose] public def resolve (look : α → Option SymGlue) : Affine α → Except α SymGlue
  | .lit g => .ok g
  | .ref n =>
    match look n with
    | some g => .ok g
    | none => .error n
  | .scale num den e =>
    match resolve look e with
    | .ok g => .ok (g.scale num den)
    | .error n => .error n
  | .add a b =>
    match resolve look a, resolve look b with
    | .ok ga, .ok gb => .ok (ga.add gb)
    | .error n, _ => .error n
    | _, .error n => .error n
  | .sub a b =>
    match resolve look a, resolve look b with
    | .ok ga, .ok gb => .ok (ga.sub gb)
    | .error n, _ => .error n
    | _, .error n => .error n

public theorem resolve_names_agree (l₁ l₂ : α → Option SymGlue) (e : Affine α)
    (h : ∀ n, l₁ n = l₂ n) : resolve l₁ e = resolve l₂ e := by
  induction e with
  | lit g => rfl
  | ref n => simp [resolve, h n]
  | scale num den e ih => simp only [resolve, ih]
  | add a b iha ihb => simp only [resolve, iha, ihb]
  | sub a b iha ihb => simp only [resolve, iha, ihb]

public theorem resolve_lit_exact (look : α → Option SymGlue) (g : SymGlue) :
    resolve look (.lit g) = .ok g := by rfl

end Affine

/-- A fully resolved local-measure context. -/
public structure MeasureValues where
  textWidth : Length
  lineWidth : Length
  columnWidth : Length
  textHeight : Length
  deriving Repr, BEq

/-- Look up one measure as rigid glue. -/
@[expose] public def MeasureValues.find (env : MeasureValues) : Measure → SymGlue
  | .textWidth => { width := .ofLength env.textWidth }
  | .lineWidth => { width := .ofLength env.lineWidth }
  | .columnWidth => { width := .ofLength env.columnWidth }
  | .textHeight => { width := .ofLength env.textHeight }

/-- One value for every horizontal measure, with a separate text height. -/
@[expose] public def MeasureValues.horizontal (measure textHeight : Length) : MeasureValues :=
  { textWidth := measure, lineWidth := measure,
    columnWidth := measure, textHeight := textHeight }

/-- Resolve a typed affine length against the geometry and font metrics at its consuming site:
the only door from `Affine Measure` to sp. -/
@[expose] public def Affine.resolveWidth (e : Affine Measure) (env : MeasureValues)
    (fontSize xHeight : Length := 0) : Length :=
  (e.eval env.find).width.resolve fontSize xHeight

public theorem Affine.resolveWidth_ref_exact (env : MeasureValues) (m : Measure)
    (fontSize xHeight : Length) :
    (Affine.ref m).resolveWidth env fontSize xHeight = (env.find m).width.fixed := by
  cases m <;> simp [Affine.resolveWidth, Affine.eval, MeasureValues.find,
    SymLength.resolve, SymLength.ofLength, Length.ext_iff']

public theorem Affine.resolveWidth_lit_exact (env : MeasureValues) (v : Length)
    (fontSize xHeight : Length) :
    (Affine.lit { width := .ofLength v }).resolveWidth env fontSize xHeight = v := by
  simpa [Affine.resolveWidth, Affine.eval] using SymLength.resolve_ofLength v fontSize xHeight

end LeanTex.Core.Dim
