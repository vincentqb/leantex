module

import all Init.Data.ToString.Basic
import all Init.Data.Repr

namespace LeanTex.Core.Dim

/-- Scaled points, TeX's exact fixed point: 1 pt = 2^16 sp. -/
public abbrev Sp := Int

@[expose] public def spPerPt : Int := 65536

@[expose] public def pt (n : Int) : Sp := n * spPerPt

@[expose] public def inch (n : Int) : Sp := n * 72 * spPerPt

/-- Millimetres: 1 mm = 7200⁄2540 pt, rounded to sp. This engine's `pt` is
the big point, 1⁄72 inch (`inch` and `Decl.unitScale` agree), not TeX's
1⁄72.27: 25.4 mm is exactly 72 pt here. -/
@[expose] public def mm (n : Int) : Sp := n * 7200 * spPerPt / 2540

/-- Hundredths of a millimetre, for standards that specify to 0.01 mm —
ISO/IEC 7810's ID-1 card is 85.60 × 53.98 mm. -/
@[expose] public def mm100 (n : Int) : Sp := n * 7200 * spPerPt / 254000

public theorem pt_exact (n : Int) : pt n / spPerPt = n := by
  simp [pt, spPerPt]

public theorem inch_eq_72pt (n : Int) : inch n = pt (72 * n) := by
  simp only [inch, pt, spPerPt]
  rw [Int.mul_comm n 72]

/-- The two spellings of one length agree: `mm` is defined against the same
1⁄72-inch point as `inch`, so 254 mm and 10 in are the same number of sp. -/
public theorem mm_eq_inch (n : Int) : mm (254 * n) = inch (10 * n) := by
  have h : 254 * n * 7200 * spPerPt = 2540 * (10 * n * 72 * spPerPt) := by
    simp only [spPerPt]
    omega
  simp only [mm, inch, h]
  exact Int.mul_ediv_cancel_left _ (by decide)

/-- The finer spelling names the same lengths: 100 hundredths are one mm. -/
public theorem mm100_eq_mm (n : Int) : mm100 (100 * n) = mm n := by
  have h : 100 * n * 7200 * spPerPt = 100 * (n * 7200 * spPerPt) := by
    simp only [spPerPt]
    omega
  have h2 : (254000 : Int) = 100 * 2540 := by decide
  simp only [mm100, mm, h, h2]
  exact Int.mul_ediv_mul_of_pos _ _ (by decide)

/-- The value `toPtString` spells, in thousandths of a point: the exact sp
value rounded to the nearest thousandth, half away from zero. What a
reader of the spelling gets back — the PDF writer's pen model starts from
it, so the pen it tracks is the one the file states. -/
@[expose] public def Sp.toPtMilli (x : Sp) : Int :=
  let milli : Int := ((x.natAbs * 1000 + 32768) / 65536 : Nat)
  if x < 0 then -milli else milli

/-- Render as decimal points with up to three fractional digits (exact sp
value rounded to the nearest thousandth, `toPtMilli`). -/
public def Sp.toPtString (x : Sp) : String :=
  let m := x.toPtMilli
  let milli := m.natAbs
  let ip := milli / 1000
  let fr := milli % 1000
  let sign := if m < 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (3 - frs.length)) ++ frs
    let frs := (frs.dropEndWhile (· == '0')).toString
    s!"{sign}{ip}.{frs}"

-- The Tests.lean checks these began as, upgraded to the compiler's tier:
-- a decidable ground fact needs no runtime test. The fractional
-- toPtString case does not join them: its String.Slice ops (`pushn`,
-- `dropEndWhile`) reduce for neither `decide`, `decide +kernel`, nor
-- `rfl`, so it stays a runtime check in Tests.lean.
example : mm 254 = inch 10 := by decide
example : (pt 10).toPtString = "10" := by rfl

/-- A rational `p / q` (`q > 0`) as a decimal, rounded once at the ninth
digit, half away from zero: the one printer for a matrix entry in both
artifacts — a PDF form's `/Matrix` and `cm`, an SVG `matrix()` — its scale
entries the reciprocal of a box in points, where one rounding at 1e-9 lands
a placed corner within a nanometre of the exact rational. -/
public def ratString (p q : Int) : String :=
  let neg := p < 0
  let v := (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs
  let ip := v / 1000000000
  let fr := v % 1000000000
  let sign := if neg && v != 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (9 - frs.length)) ++ frs
    let frs := (frs.dropEndWhile (· == '0')).toString
    s!"{sign}{ip}.{frs}"

/-- An exact rational at nine decimals (`ratString`). -/
public def ratDecimal (r : Rat) : String := ratString r.num r.den

public structure Glue where
  width : Sp := 0
  stretch : Sp := 0
  shrink : Sp := 0
  fil : Bool := false
  /-- Fill that only exists to run out the rest of a line, as at the end of a
  paragraph. It yields to an author's `\hfill`: a row that says "name, then
  dates at the margin" means the margin, not halfway to it. -/
  parfill : Bool := false
  /-- Interword glue: the space between two words of set text, set only by
  the token→item path for a space (`Layout.interword`) and copied by the
  glue transforms (`raggedItems`, `displayItems`). Every other glue —
  indent, alignment, kern, fill — is `false`. Read by the line setter onto
  `Seg.gap`'s `word`, the tagger's interword channel. -/
  word : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def Glue.add (a b : Glue) : Glue :=
  { width := a.width + b.width
    stretch := a.stretch + b.stretch
    shrink := a.shrink + b.shrink
    fil := a.fil || b.fil }

public theorem Glue.add_comm (a b : Glue) : a.add b = b.add a := by
  simp [add, Int.add_comm, Bool.or_comm]

public theorem Glue.add_assoc (a b c : Glue) : (a.add b).add c = a.add (b.add c) := by
  simp [add, Int.add_assoc, Bool.or_assoc]

/-- TeX-style badness: 100·r³ capped at 10000, where r = |delta|/total. -/
@[expose] public def badness (delta total : Int) : Nat :=
  if total ≤ 0 then
    10000
  else
    min ((100 * delta.natAbs ^ 3) / total.natAbs ^ 3) 10000

public theorem badness_zero_delta (t : Int) (h : 0 < t) : badness 0 t = 0 := by
  simp [badness]
  omega

public theorem badness_le (d t : Int) : badness d t ≤ 10000 := by
  unfold badness
  split
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

/-- A length that may depend on the font: an absolute part plus em and ex
parts in thousandths. `\tokens` needs this because a token is declared before
any font is chosen, but `1.5ex` can only be resolved once one is. -/
public structure Length where
  sp : Sp := 0
  em : Int := 0
  ex : Int := 0
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Length

@[expose] public def ofSp (v : Sp) : Length := { sp := v }

@[expose] public def add (a b : Length) : Length :=
  { sp := a.sp + b.sp, em := a.em + b.em, ex := a.ex + b.ex }

/-- Componentwise difference, exact: subtraction in a fixed point is
integer subtraction, no rounding anywhere. -/
@[expose] public def sub (a b : Length) : Length :=
  { sp := a.sp - b.sp, em := a.em - b.em, ex := a.ex - b.ex }

/-- Scale by a rational `num/den`, truncating toward zero — TeX's one
rounding: `\divide` truncates (TeXbook ch. 24), and so does the
coefficient scaling `⟨factor⟩⟨dimen⟩` (`xn_over_d`, TeX §107). Only
e-TeX's `\dimexpr` division rounds to nearest instead (e-TeX manual
§3.5), which is why that spelling is refused, not mapped here. -/
@[expose] public def scale (l : Length) (num : Int) (den : Nat) : Length :=
  { sp := (l.sp * num).tdiv den
    em := (l.em * num).tdiv den
    ex := (l.ex * num).tdiv den }

/-- The settled rounding agrees with the floor `scale` used before
wherever the scaled product is nonnegative — truncation toward zero and
Euclidean division (Lean's `Int./`, floor for a positive divisor) differ
only on negative dividends, so every nonnegative value scales exactly as
it always did. -/
public theorem scale_tdiv_eq_of_nonneg (v num : Int) (den : Nat) (h : 0 ≤ v * num) :
    (v * num).tdiv den = v * num / den :=
  Int.tdiv_eq_ediv_of_nonneg h

/-- Resolve against a font size and x-height, both in sp. -/
@[expose] public def resolve (l : Length) (fontSize xHeight : Sp) : Sp :=
  l.sp + l.em * fontSize / 1000 + l.ex * xHeight / 1000

public theorem resolve_ofSp (v fontSize xHeight : Sp) :
    (ofSp v).resolve fontSize xHeight = v := by
  simp [resolve, ofSp]

public theorem add_comm (a b : Length) : a.add b = b.add a := by
  simp [add, Int.add_comm]

end Length

/-- Glue whose components may be font-relative. -/
public structure SymGlue where
  width : Length := {}
  stretch : Length := {}
  shrink : Length := {}
  /-- First-order infinite stretch, TeX's `fil`: `\vspace{\fill}` and
  `\vfill` declare glue whose share of a page's leftover is what places
  the content. Finite components ride beside it as in TeX. -/
  fil : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

namespace SymGlue

@[expose] public def add (a b : SymGlue) : SymGlue :=
  { width := a.width.add b.width
    stretch := a.stretch.add b.stretch
    shrink := a.shrink.add b.shrink
    fil := a.fil || b.fil }

/-- Componentwise, as `\glueexpr` subtracts glue (e-TeX manual, the
`⟨expr⟩` grammar): the rubber components subtract with the widths. An
infinite stretch survives subtraction — TeX's `1fil - 1fil` is `0fil`,
still first-order infinite, and a boolean cannot say finer. -/
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

@[expose] public def resolve (g : SymGlue) (fontSize xHeight : Sp) : Glue :=
  { width := g.width.resolve fontSize xHeight
    stretch := g.stretch.resolve fontSize xHeight
    shrink := g.shrink.resolve fontSize xHeight
    fil := g.fil }

end SymGlue

/-- A local measure a length may read. The names stay distinct until the
consumer supplies its context: a minipage makes all three horizontal
measures its own, while other page models may not. -/
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

/-- A diagnostic label for a typed measure. Source spelling never rides the IR. -/
public def Measure.label : Measure → String
  | .textWidth => "\\textwidth"
  | .lineWidth => "\\linewidth"
  | .columnWidth => "\\columnwidth"
  | .textHeight => "\\textheight"

/-- A typed affine expression: literals and variables combined only by
addition, subtraction, and scalar multiplication. Keeping the operations
rather than flattening coefficients preserves TeX's fixed-point rounding at
each scalar product. -/
public inductive Affine (α : Type) where
  | lit (g : SymGlue)
  | ref (name : α)
  | scale (num : Int) (den : Nat) (e : Affine α)
  | add (a b : Affine α)
  | sub (a b : Affine α)
  deriving Repr, BEq, DecidableEq

public instance [Inhabited α] : Inhabited (Affine α) := ⟨.lit {}⟩

namespace Affine

/-- Canonical rational scaling. Equivalent coefficient spellings construct
the same tree, which makes parser normalization a structural fact. -/
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

/-- The reference, and its coefficient in permille, when the expression is
exactly a non-negative rational multiple of a single `.ref` with no literal,
sum, or difference part: a bare `.ref m` is `(m, 1000)`; `scale num den
(.ref m)` is `(m, num·1000/den)`. Anything else — a literal, a sum, a nested
scale, a different shape, a zero denominator, or a negative coefficient — is
`none`, the signal to a share computation that this length does not reduce to
a clean fraction of a shared measure and must fall back to its affine form. -/
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

/-- Whether an expression carries an infinite-stretch literal. References
are local rigid lengths, so only a literal can contribute one. -/
@[expose] public def hasFil : Affine α → Bool
  | .lit g => g.fil
  | .ref _ => false
  | .scale _ _ e => hasFil e
  | .add a b | .sub a b => hasFil a || hasFil b

/-- Remove infinite stretch while preserving the expression's finite width,
stretch, shrink, references, and fixed-point operation order. -/
@[expose] public def withoutFil : Affine α → Affine α
  | .lit g => .lit { g with fil := false }
  | .ref n => .ref n
  | .scale num den e => .scale num den (withoutFil e)
  | .add a b => .add (withoutFil a) (withoutFil b)
  | .sub a b => .sub (withoutFil a) (withoutFil b)

/-- Whether every literal is a rigid absolute length. Local measures are
rigid by definition; dimension consumers reject rubber and font-relative
literals before the expression reaches their IR. -/
@[expose] public def rigidAbsolute : Affine α → Bool
  | .lit g => !g.fil && g.stretch == {} && g.shrink == {} &&
      g.width.em == 0 && g.width.ex == 0
  | .ref _ => true
  | .scale _ _ e => rigidAbsolute e
  | .add a b | .sub a b => rigidAbsolute a && rigidAbsolute b

/-- Replace every reference with a typed expression. This is the boundary
between source names and the IR: unresolved spellings cannot cross it. -/
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

/-- Evaluate with a total context. Use this only after the source boundary
has proved every variable is representable there. -/
@[expose] public def eval (look : α → SymGlue) : Affine α → SymGlue
  | .lit g => g
  | .ref n => look n
  | .scale num den e => (eval look e).scale num den
  | .add a b => (eval look a).add (eval look b)
  | .sub a b => (eval look a).sub (eval look b)

/-- Total evaluation is also independent of ambient state. -/
public theorem eval_names_agree (l₁ l₂ : α → SymGlue) (e : Affine α)
    (h : ∀ n, l₁ n = l₂ n) : eval l₁ e = eval l₂ e := by
  induction e with
  | lit g => rfl
  | ref n => simp [eval, h n]
  | scale num den e ih => simp only [eval, ih]
  | add a b iha ihb => simp only [eval, iha, ihb]
  | sub a b iha ihb => simp only [eval, iha, ihb]

/-- Resolve an affine expression against one context. An absent variable is
returned as that typed variable, never as zero and never as source text. -/
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

/-- Resolution depends only on the supplied values, not on any ambient
state. -/
public theorem resolve_names_agree (l₁ l₂ : α → Option SymGlue) (e : Affine α)
    (h : ∀ n, l₁ n = l₂ n) : resolve l₁ e = resolve l₂ e := by
  induction e with
  | lit g => rfl
  | ref n => simp [resolve, h n]
  | scale num den e ih => simp only [resolve, ih]
  | add a b iha ihb => simp only [resolve, iha, ihb]
  | sub a b iha ihb => simp only [resolve, iha, ihb]

/-- A literal resolves exactly; no context can change it. -/
public theorem resolve_lit_exact (look : α → Option SymGlue) (g : SymGlue) :
    resolve look (.lit g) = .ok g := by rfl

end Affine

/-- A fully resolved local-measure context, used only after the source
boundary admitted exactly the variables the consumer supplies. -/
public structure MeasureValues where
  textWidth : Sp
  lineWidth : Sp
  columnWidth : Sp
  textHeight : Sp
  deriving Repr, BEq

/-- Look up one measure as rigid glue. -/
@[expose] public def MeasureValues.find (env : MeasureValues) : Measure → SymGlue
  | .textWidth => { width := .ofSp env.textWidth }
  | .lineWidth => { width := .ofSp env.lineWidth }
  | .columnWidth => { width := .ofSp env.columnWidth }
  | .textHeight => { width := .ofSp env.textHeight }

/-- One value for every horizontal measure, with a separate text height. -/
@[expose] public def MeasureValues.horizontal (measure textHeight : Sp) : MeasureValues :=
  { textWidth := measure, lineWidth := measure,
    columnWidth := measure, textHeight := textHeight }

/-- Resolve one typed affine length against the geometry and font metrics at
its consuming site. This is the only door from `Affine Measure` to sp: boxes,
table columns, images, glue, rules, and font-size declarations supply their
actual local context rather than estimating it during elaboration. -/
@[expose] public def Affine.resolveWidth (e : Affine Measure) (env : MeasureValues)
    (fontSize xHeight : Sp := 0) : Sp :=
  (e.eval env.find).width.resolve fontSize xHeight

/-- A local reference resolves to exactly the value its context supplies. -/
public theorem Affine.resolveWidth_ref_exact (env : MeasureValues) (m : Measure)
    (fontSize xHeight : Sp) :
    (Affine.ref m).resolveWidth env fontSize xHeight = (env.find m).width.sp := by
  cases m <;> simp [Affine.resolveWidth, Affine.eval, MeasureValues.find,
    Length.resolve, Length.ofSp]

/-- A rigid literal is independent of every local measure. -/
public theorem Affine.resolveWidth_lit_exact (env : MeasureValues) (v : Sp)
    (fontSize xHeight : Sp) :
    (Affine.lit { width := .ofSp v }).resolveWidth env fontSize xHeight = v := by
  simpa [Affine.resolveWidth, Affine.eval] using Length.resolve_ofSp v fontSize xHeight

end LeanTex.Core.Dim
