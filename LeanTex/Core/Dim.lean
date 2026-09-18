namespace LeanTex.Core.Dim

/-- Scaled points, TeX's exact fixed point: 1 pt = 2^16 sp. -/
abbrev Sp := Int

def spPerPt : Int := 65536

def pt (n : Int) : Sp := n * spPerPt

def inch (n : Int) : Sp := n * 72 * spPerPt

/-- Millimetres: 1 mm = 7200⁄2540 pt, rounded to sp. This engine's `pt` is
the big point, 1⁄72 inch (`inch` and `Decl.unitScale` agree), not TeX's
1⁄72.27: 25.4 mm is exactly 72 pt here. -/
def mm (n : Int) : Sp := n * 7200 * spPerPt / 2540

/-- Hundredths of a millimetre, for standards that specify to 0.01 mm —
ISO/IEC 7810's ID-1 card is 85.60 × 53.98 mm. -/
def mm100 (n : Int) : Sp := n * 7200 * spPerPt / 254000

theorem pt_exact (n : Int) : pt n / spPerPt = n := by
  simp [pt, spPerPt]

theorem inch_eq_72pt (n : Int) : inch n = pt (72 * n) := by
  simp only [inch, pt, spPerPt]
  rw [Int.mul_comm n 72]

/-- The two spellings of one length agree: `mm` is defined against the same
1⁄72-inch point as `inch`, so 254 mm and 10 in are the same number of sp. -/
theorem mm_eq_inch (n : Int) : mm (254 * n) = inch (10 * n) := by
  have h : 254 * n * 7200 * spPerPt = 2540 * (10 * n * 72 * spPerPt) := by
    simp only [spPerPt]
    omega
  simp only [mm, inch, h]
  exact Int.mul_ediv_cancel_left _ (by decide)

/-- The finer spelling names the same lengths: 100 hundredths are one mm. -/
theorem mm100_eq_mm (n : Int) : mm100 (100 * n) = mm n := by
  have h : 100 * n * 7200 * spPerPt = 100 * (n * 7200 * spPerPt) := by
    simp only [spPerPt]
    omega
  have h2 : (254000 : Int) = 100 * 2540 := by decide
  simp only [mm100, mm, h, h2]
  exact Int.mul_ediv_mul_of_pos _ _ (by decide)

/-- Render as decimal points with up to three fractional digits (exact sp
value rounded to the nearest thousandth). -/
def Sp.toPtString (x : Sp) : String :=
  let neg := x < 0
  let n := x.natAbs
  let milli := (n * 1000 + 32768) / 65536
  let ip := milli / 1000
  let fr := milli % 1000
  let sign := if neg && milli != 0 then "-" else ""
  if fr == 0 then
    s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (3 - frs.length)) ++ frs
    let frs := (frs.dropEndWhile (· == '0')).toString
    s!"{sign}{ip}.{frs}"

structure Glue where
  width : Sp := 0
  stretch : Sp := 0
  shrink : Sp := 0
  fil : Bool := false
  /-- Fill that only exists to run out the rest of a line, as at the end of a
  paragraph. It yields to an author's `\hfill`: a row that says "name, then
  dates at the margin" means the margin, not halfway to it. -/
  parfill : Bool := false
  deriving Repr, BEq, Inhabited

def Glue.add (a b : Glue) : Glue :=
  { width := a.width + b.width
    stretch := a.stretch + b.stretch
    shrink := a.shrink + b.shrink
    fil := a.fil || b.fil }

theorem Glue.add_comm (a b : Glue) : a.add b = b.add a := by
  simp [add, Int.add_comm, Bool.or_comm]

theorem Glue.add_assoc (a b c : Glue) : (a.add b).add c = a.add (b.add c) := by
  simp [add, Int.add_assoc, Bool.or_assoc]

/-- TeX-style badness: 100·r³ capped at 10000, where r = |delta|/total. -/
def badness (delta total : Int) : Nat :=
  if total ≤ 0 then
    10000
  else
    min ((100 * delta.natAbs ^ 3) / total.natAbs ^ 3) 10000

theorem badness_zero_delta (t : Int) (h : 0 < t) : badness 0 t = 0 := by
  simp [badness]
  omega

theorem badness_le (d t : Int) : badness d t ≤ 10000 := by
  unfold badness
  split
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

/-- A length that may depend on the font: an absolute part plus em and ex
parts in thousandths. `\tokens` needs this because a token is declared before
any font is chosen, but `1.5ex` can only be resolved once one is. -/
structure Length where
  sp : Sp := 0
  em : Int := 0
  ex : Int := 0
  deriving Repr, BEq, Inhabited

namespace Length

def ofSp (v : Sp) : Length := { sp := v }

def add (a b : Length) : Length :=
  { sp := a.sp + b.sp, em := a.em + b.em, ex := a.ex + b.ex }

/-- Componentwise difference, exact: subtraction in a fixed point is
integer subtraction, no rounding anywhere. -/
def sub (a b : Length) : Length :=
  { sp := a.sp - b.sp, em := a.em - b.em, ex := a.ex - b.ex }

/-- Scale by a rational `num/den`, keeping the fixed point exact. -/
def scale (l : Length) (num : Int) (den : Nat) : Length :=
  { sp := l.sp * num / den, em := l.em * num / den, ex := l.ex * num / den }

/-- Resolve against a font size and x-height, both in sp. -/
def resolve (l : Length) (fontSize xHeight : Sp) : Sp :=
  l.sp + l.em * fontSize / 1000 + l.ex * xHeight / 1000

theorem resolve_ofSp (v fontSize xHeight : Sp) :
    (ofSp v).resolve fontSize xHeight = v := by
  simp [resolve, ofSp]

theorem add_comm (a b : Length) : a.add b = b.add a := by
  simp [add, Int.add_comm]

end Length

/-- Glue whose components may be font-relative. -/
structure SymGlue where
  width : Length := {}
  stretch : Length := {}
  shrink : Length := {}
  /-- First-order infinite stretch, TeX's `fil`: `\vspace{\fill}` and
  `\vfill` declare glue whose share of a page's leftover is what places
  the content. Finite components ride beside it as in TeX. -/
  fil : Bool := false
  deriving Repr, BEq, Inhabited

namespace SymGlue

def add (a b : SymGlue) : SymGlue :=
  { width := a.width.add b.width
    stretch := a.stretch.add b.stretch
    shrink := a.shrink.add b.shrink
    fil := a.fil || b.fil }

/-- Componentwise, as `\glueexpr` subtracts glue (e-TeX manual, the
`⟨expr⟩` grammar): the rubber components subtract with the widths. An
infinite stretch survives subtraction — TeX's `1fil - 1fil` is `0fil`,
still first-order infinite, and a boolean cannot say finer. -/
def sub (a b : SymGlue) : SymGlue :=
  { width := a.width.sub b.width
    stretch := a.stretch.sub b.stretch
    shrink := a.shrink.sub b.shrink
    fil := a.fil || b.fil }

def scale (g : SymGlue) (num : Int) (den : Nat) : SymGlue :=
  { width := g.width.scale num den
    stretch := g.stretch.scale num den
    shrink := g.shrink.scale num den
    fil := g.fil }

def resolve (g : SymGlue) (fontSize xHeight : Sp) : Glue :=
  { width := g.width.resolve fontSize xHeight
    stretch := g.stretch.resolve fontSize xHeight
    shrink := g.shrink.resolve fontSize xHeight
    fil := g.fil }

end SymGlue

end LeanTex.Core.Dim
