namespace LeanTex.Core.Dim

/-- Scaled points, TeX's exact fixed point: 1 pt = 2^16 sp. -/
abbrev Sp := Int

def spPerPt : Int := 65536

def pt (n : Int) : Sp := n * spPerPt

def inch (n : Int) : Sp := n * 72 * spPerPt

theorem pt_exact (n : Int) : pt n / spPerPt = n := by
  simp [pt, spPerPt]

theorem inch_eq_72pt (n : Int) : inch n = pt (72 * n) := by
  simp only [inch, pt, spPerPt]
  rw [Int.mul_comm n 72]

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
  deriving Repr, BEq, Inhabited

namespace SymGlue

def scale (g : SymGlue) (num : Int) (den : Nat) : SymGlue :=
  { width := g.width.scale num den
    stretch := g.stretch.scale num den
    shrink := g.shrink.scale num den }

def resolve (g : SymGlue) (fontSize xHeight : Sp) : Glue :=
  { width := g.width.resolve fontSize xHeight
    stretch := g.stretch.resolve fontSize xHeight
    shrink := g.shrink.resolve fontSize xHeight }

end SymGlue

end LeanTex.Core.Dim
