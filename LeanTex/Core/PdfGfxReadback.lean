module

public import LeanTex.Core.PdfGfx
public import LeanTex.Core.PdfContent
public import LeanTex.Core.PdfContentLexProof
public import LeanTex.Core.DimSpell
public import LeanTex.Core.ColorContract
import all LeanTex.Core.PdfGfx
import all LeanTex.Core.PdfContent
import all LeanTex.Core.PdfContentLex
import all LeanTex.Core.Dim
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfContentLexProof
import all LeanTex.Core.Gfx
import all LeanTex.Core.GfxPdf
import LeanTex.Core.LoopProgress

/-! The figure importer reads back what the PDF writer paints, for plain opaque paths and groups. -/

namespace LeanTex.Core.PdfGfx

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx
open LeanTex.Core.PdfRead (Obj)
open LeanTex.Core.PdfContentLex (Tok)

theorem digitsVal_cons (c : Char) (cs : List Char) :
    digitsVal (c :: cs) = (c.toNat - 48) * 10 ^ cs.length + digitsVal cs := by
  have h := digitsVal_append [c] cs
  simp only [List.singleton_append] at h
  rw [h]
  simp [digitsVal]

theorem digitsOf_digits (ds rest : List Char) (hd : ∀ c ∈ ds, c.isDigit = true)
    (n scale : Nat) (dot seen : Bool) :
    PdfContentLex.numParts?.digitsOf (ds ++ rest) n scale dot seen =
      PdfContentLex.numParts?.digitsOf rest (n * 10 ^ ds.length + digitsVal ds)
        (if dot then scale * 10 ^ ds.length else scale) dot (seen || !ds.isEmpty) := by
  induction ds generalizing n scale seen with
  | nil => simp [digitsVal]
  | cons c cs ih =>
    have hc : c.isDigit = true := hd c (by simp)
    simp only [List.cons_append]
    rw [PdfContentLex.numParts?.digitsOf]
    simp only [hc, ↓reduceIte]
    rw [ih (fun d h => hd d (by simp [h]))]
    have hv := digitsVal_cons c cs
    have e1 : (n * 10 + (c.toNat - 48)) * 10 ^ cs.length + digitsVal cs =
        n * 10 ^ (c :: cs).length + digitsVal (c :: cs) := by
      rw [hv, List.length_cons, Nat.pow_succ]
      grind
    rw [e1]
    cases dot <;> simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10]

theorem digitsVal_toDigits (n : Nat) : digitsVal (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [Nat.toDigits_of_lt_base h]
      simp [digitsVal, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega), digitsVal_append, ih (n / 10) (by omega)]
      simp [digitsVal, Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt n (by decide : 10 > 0))]
      omega

theorem toDigits_digits (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
  fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem negSpell (k : Nat) (hip : 0 < k) :
    (toString (-((k : Nat) : Int))).toList = ['-'] ++ Nat.toDigits 10 k := by
  simp only [Int.toString_eq_repr, Int.repr_eq_ite]
  have hn : ¬ (0 ≤ -((k : Nat) : Int)) := by omega
  simp only [hn, ↓reduceIte, String.toList_append, Int.neg_neg, Int.toNat_natCast,
      Nat.toList_repr]
  rfl

theorem posSpell (k : Nat) : (toString ((k : Nat) : Int)).toList = Nat.toDigits 10 k := by
  simp only [Int.toString_eq_repr, Int.repr_eq_ite]
  have hn : (0 ≤ ((k : Nat) : Int)) := by omega
  simp only [hn, ↓reduceIte, Int.toNat_natCast, Nat.toList_repr]

/-- A length's operand as the writer spells it: an integer for whole points, else a real. -/
def lenObj (x : Length) : Obj :=
  if x.toBpMilli.natAbs % 1000 = 0 then
    .int (if x.toBpMilli < 0 then -((x.toBpMilli.natAbs / 1000 : Nat) : Int)
      else ((x.toBpMilli.natAbs / 1000 : Nat) : Int))
  else .real x.toBpString

theorem lenObj_render (x : Length) : (lenObj x).render = x.toBpString.toUTF8 := by
  unfold lenObj
  split
  · rename_i hf
    simp only [Obj.render, Obj.renderInto, ByteArray.empty_append]
    congr 1
    apply String.ext
    rw [toBpString_chars_exact]
    simp only [hf, ↓reduceIte, List.append_nil]
    by_cases hm : x.toBpMilli < 0
    · rw [ite_eq_left hm, ite_eq_left hm]
      exact negSpell _ (by omega)
    · rw [ite_eq_right hm, ite_eq_right hm, List.nil_append]
      exact posSpell _
  · simp [Obj.render, Obj.renderInto]

theorem numByte_digit {c : Char} (h : c.isDigit = true) : PdfLex.numByte c.toNat = true := by
  have : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by simpa using Char.isDigit_iff_toNat.mp h
  simp only [PdfLex.numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem numParts_decimal (s : String) (neg : Bool) (ds fd : List Char)
    (hs : s.toList = (if neg then ['-'] else []) ++ ds ++ '.' :: fd)
    (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) (hf : ∀ c ∈ fd, c.isDigit = true) :
    PdfContentLex.numParts? (.real s) =
      some (neg, digitsVal ds * 10 ^ fd.length + digitsVal fd, 10 ^ fd.length) := by
  have hread : PdfContentLex.numParts?.digitsOf (ds ++ '.' :: fd) 0 1 false false =
      some (digitsVal ds * 10 ^ fd.length + digitsVal fd, 10 ^ fd.length) := by
    rw [digitsOf_digits ds _ hd]
    rw [PdfContentLex.numParts?.digitsOf]
    have hdot : ('.' : Char).isDigit = false := by decide
    simp only [hdot, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.not_false,
      Bool.and_self]
    have := digitsOf_digits fd [] hf (0 * 10 ^ ds.length + digitsVal ds) 1 true
      (false || !ds.isEmpty)
    simp only [List.append_nil] at this
    rw [this]
    simp [PdfContentLex.numParts?.digitsOf, Nat.zero_mul, hne]
  unfold PdfContentLex.numParts?
  dsimp only
  rw [hs]
  cases neg with
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    rw [hread]
    rfl
  | false =>
    obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := List.exists_cons_of_ne_nil hne
    have hdd : d.isDigit = true := hd d (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append]
    split
    · rename_i rest h
      have : d = '-' := (List.cons.inj h).1
      subst this
      exact absurd hdd (by decide)
    · rename_i rest h
      have : d = '+' := (List.cons.inj h).1
      subst this
      exact absurd hdd (by decide)
    · rw [← List.cons_append, hread]
      rfl

theorem lenObj_spelled (x : Length) : PdfContentLex.ValSpelled (lenObj x) := by
  refine ⟨?_, fun n g h => by unfold lenObj at h; split at h <;> cases h⟩
  unfold lenObj
  split
  · exact .int _
  · rename_i hf
    refine .real ⟨?_, ?_⟩
    · rw [toBpString_chars_exact]
      simp [hf]
    · intro c hc
      rw [toBpString_chars_exact] at hc
      simp only [hf, ↓reduceIte, List.mem_append, List.mem_cons] at hc
      rcases hc with (hc | hc) | hc | hc
      · split at hc <;> simp_all [PdfLex.numByte]
      · exact numByte_digit (toDigits_digits _ c hc)
      · subst hc; decide
      · exact numByte_digit (fracDigits_digits 3 _ c hc)

theorem len?_lenObj (x : Length) : Obj.len? (lenObj x) = some (qLen x) := by
  have hN : bpUnits = 407924 := bpUnits_eq
  unfold lenObj Obj.len?
  split
  · rename_i hf
    simp only [PdfContentLex.numParts?, Option.map_some]
    congr 1
    simp only [qLen, Length.ofBpParts]
    by_cases hm : x.toBpMilli < 0
    · have hip : 0 < x.toBpMilli.natAbs / 1000 := by omega
      generalize hk : x.toBpMilli.natAbs / 1000 = k at hip
      have hmk : x.toBpMilli = -((1000 * k : Nat) : Int) := by omega
      simp only [hm, ↓reduceIte]
      rw [hmk]
      have hneg : decide (-((k : Nat) : Int) < 0) = true := by simp; omega
      simp only [hneg, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast, Nat.mul_one]
      rw [Length.ext_iff']
      simp only [hN, Length.ofBpMilli_units] at *
      split <;> ((try dsimp only) ; omega)
    · generalize hk : x.toBpMilli.natAbs / 1000 = k
      have hmk : x.toBpMilli = ((1000 * k : Nat) : Int) := by omega
      simp only [hm, ↓reduceIte]
      rw [hmk]
      have hneg : decide (((k : Nat) : Int) < 0) = false := by simp
      simp only [hneg, Bool.false_eq_true, ↓reduceIte, Int.natAbs_natCast, Nat.mul_one]
      rw [Length.ext_iff']
      simp only [hN, Length.ofBpMilli_units] at *
      split <;> ((try dsimp only) ; omega)
  · rename_i hf
    have hfr := fracDigits_value_exact 3 (x.toBpMilli.natAbs % 1000) (Nat.mod_lt _ (by decide)) hf
    obtain ⟨hne, hlen, hval⟩ := hfr
    have hp := numParts_decimal x.toBpString (decide (x.toBpMilli < 0))
      (Nat.toDigits 10 (x.toBpMilli.natAbs / 1000)) (fracDigits 3 (x.toBpMilli.natAbs % 1000))
      (by rw [toBpString_chars_exact]; simp [hf])
      (toDigits_digits _) Nat.toDigits_ne_nil (fracDigits_digits 3 _)
    rw [hp]
    simp only [Option.map_some]
    congr 1
    rw [digitsVal_toDigits]
    generalize hL : (fracDigits 3 (x.toBpMilli.natAbs % 1000)).length = L at hlen hval hne
    generalize digitsVal (fracDigits 3 (x.toBpMilli.natAbs % 1000)) = dv at hval
    have hL1 : 1 ≤ L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0
        exact absurd (List.eq_nil_of_length_eq_zero hL) hne
      · exact h0
    simp only [qLen, Length.ofBpParts]
    have key : ((2 * bpUnits * (x.toBpMilli.natAbs / 1000 * 10 ^ L + dv) + 10 ^ L) / (2 * 10 ^ L)) =
        (x.toBpMilli.natAbs * bpUnits + 500) / 1000 := by
      generalize x.toBpMilli.natAbs = N at hval ⊢
      obtain rfl | rfl | rfl : L = 1 ∨ L = 2 ∨ L = 3 := by omega
      all_goals (simp only [hN, Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at hval ⊢; omega)
    by_cases hneg : x.toBpMilli < 0
    · simp only [hneg, decide_true, ↓reduceIte]
      rw [key]
      rw [Length.ext_iff']
      simp only [hN, Length.ofBpMilli_units] at *
      split <;> ((try dsimp only) ; omega)
    · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [key]
      rw [Length.ext_iff']
      simp only [hN, Length.ofBpMilli_units] at *
      split <;> ((try dsimp only) ; omega)

/-- What `Dim.ratString` prints of `p / q` before its point is placed: the
magnitude in billionths, rounded half away from zero. -/
@[expose] public def ratV (p q : Int) : Nat := (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs

/-- A ratio's operand as the writer spells it: an integer without fraction, else a real. -/
def ratObj (p q : Int) : Obj :=
  if ratV p q % 1000000000 = 0 then
    .int (if p < 0 ∧ ratV p q ≠ 0 then -((ratV p q / 1000000000 : Nat) : Int)
      else ((ratV p q / 1000000000 : Nat) : Int))
  else .real (ratString p q)

/-- What a ratio's spelling reads as: `p / q` rounded once at the ninth
decimal, half away from zero. -/
@[expose] public def ratRead (p q : Int) : Rat :=
  if p < 0 then -(mkRat (ratV p q) 1000000000) else mkRat (ratV p q) 1000000000

theorem ratString_chars (p q : Int) :
    (ratString p q).toList = (if p < 0 ∧ ratV p q ≠ 0 then ['-'] else []) ++
      Nat.toDigits 10 (ratV p q / 1000000000) ++
      (if ratV p q % 1000000000 = 0 then [] else '.' :: fracDigits 9 (ratV p q % 1000000000)) :=
  ratString_chars_exact p q

theorem ratObj_render (p q : Int) : (ratObj p q).render = (ratString p q).toUTF8 := by
  unfold ratObj
  split
  · rename_i hf
    simp only [Obj.render, Obj.renderInto, ByteArray.empty_append]
    congr 1
    apply String.ext
    rw [ratString_chars]
    simp only [hf, ↓reduceIte, List.append_nil]
    generalize ratV p q = v at hf ⊢
    by_cases hm : p < 0 ∧ v ≠ 0
    · rw [ite_eq_left hm, ite_eq_left hm]
      exact negSpell _ (by omega)
    · rw [ite_eq_right hm, ite_eq_right hm, List.nil_append]
      exact posSpell _
  · simp [Obj.render, Obj.renderInto]

theorem ratObj_spelled (p q : Int) : PdfContentLex.ValSpelled (ratObj p q) := by
  refine ⟨?_, fun n g h => by unfold ratObj at h; split at h <;> cases h⟩
  unfold ratObj
  split
  · exact .int _
  · rename_i hf
    refine .real ⟨?_, ?_⟩
    · rw [ratString_chars]
      simp [hf]
    · intro c hc
      rw [ratString_chars] at hc
      simp only [hf, ↓reduceIte, List.mem_append, List.mem_cons] at hc
      rcases hc with (hc | hc) | hc | hc
      · split at hc
        · simp only [List.mem_singleton] at hc; subst hc; decide
        · simp at hc
      · exact numByte_digit (toDigits_digits _ c hc)
      · subst hc; decide
      · exact numByte_digit (fracDigits_digits 9 _ c hc)

theorem mkRat_scale (n k : Nat) (hk : k ≠ 0) : mkRat ((n * k : Nat) : Int) k = mkRat (n : Int) 1 := by
  have := Rat.mkRat_mul_right (n := (n : Int)) (d := 1) hk
  rw [Nat.one_mul] at this
  rw [← this]
  push_cast
  rfl

theorem numRat_int (n : Int) : PdfContentLex.numRat? (.int n) =
    some (if n < 0 then -(mkRat (n.natAbs : Int) 1) else mkRat (n.natAbs : Int) 1) := by
  rw [PdfContentLex.numRat?_parts]
  simp only [PdfContentLex.numParts?, Option.map_some, decide_eq_true_eq]

theorem ratOf_int (p q : Int) (hf : ratV p q % 1000000000 = 0) :
    ratOf (.int (if p < 0 ∧ ratV p q ≠ 0 then -((ratV p q / 1000000000 : Nat) : Int)
      else ((ratV p q / 1000000000 : Nat) : Int))) = some (ratRead p q) := by
  unfold ratOf ratRead
  rw [numRat_int]
  congr 1
  generalize ratV p q = v at hf ⊢
  have hv9 : v = v / 1000000000 * 1000000000 := by omega
  generalize hk : v / 1000000000 = k at hv9
  subst hv9
  by_cases hm : p < 0 ∧ k * 1000000000 ≠ 0
  · rw [ite_eq_left hm]
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (by rw [h]) hm.2
      · exact h
    have hn : -((k : Nat) : Int) < 0 := by omega
    rw [ite_eq_left hn, ite_eq_left hm.1, Int.natAbs_neg, Int.natAbs_natCast, mkRat_scale _ _ (by decide)]
  · rw [ite_eq_right hm]
    have hn : ¬ ((k : Nat) : Int) < 0 := by omega
    rw [ite_eq_right hn, Int.natAbs_natCast]
    by_cases hp : p < 0
    · have hk : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact h
        · exact absurd ⟨hp, Nat.mul_ne_zero (by omega) (by decide)⟩ hm
      subst hk
      rw [ite_eq_left hp]
      simp
    · rw [ite_eq_right hp, mkRat_scale _ _ (by decide)]

theorem mkRat_frac (ip dv L K : Nat) (hL : L ≤ K) :
    mkRat (((ip * 10 ^ L + dv : Nat)) : Int) (10 ^ L) =
      mkRat (((ip * 10 ^ K + dv * 10 ^ (K - L) : Nat)) : Int) (10 ^ K) := by
  have hk : 10 ^ (K - L) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
  rw [← Rat.mkRat_mul_right (n := (((ip * 10 ^ L + dv : Nat)) : Int)) (d := 10 ^ L) hk]
  have e1 : 10 ^ L * 10 ^ (K - L) = 10 ^ K := by
    rw [← Nat.pow_add]; congr 1; omega
  have e2 : (((ip * 10 ^ L + dv : Nat)) : Int) * ((10 ^ (K - L) : Nat) : Int) =
      (((ip * 10 ^ K + dv * 10 ^ (K - L) : Nat)) : Int) := by
    rw [← e1]
    push_cast
    rw [Int.add_mul, Int.mul_assoc]
  rw [e1, e2]

theorem ratOf_eq (o : Obj) : ratOf o = PdfContentLex.numRat? o := rfl

theorem ratRead_eq (p q : Int) : ratRead p q =
    if p < 0 then -(mkRat (ratV p q) 1000000000) else mkRat (ratV p q) 1000000000 := rfl

theorem ratOf_real (p q : Int) (hf : ¬ ratV p q % 1000000000 = 0) :
    ratOf (.real (ratString p q)) = some (ratRead p q) := by
  have hv0 : ratV p q ≠ 0 := fun h => hf (by rw [h])
  have hs : (ratString p q).toList = (if decide (p < 0) = true then ['-'] else []) ++
      Nat.toDigits 10 (ratV p q / 1000000000) ++ '.' :: fracDigits 9 (ratV p q % 1000000000) := by
    rw [ratString_chars, ite_eq_right hf]
    have e : (if p < 0 ∧ ratV p q ≠ 0 then ['-'] else ([] : List Char)) =
        (if decide (p < 0) = true then ['-'] else []) := by
      by_cases hp : p < 0
      · rw [ite_eq_left ⟨hp, hv0⟩, ite_eq_left (by simpa using hp)]
      · rw [ite_eq_right (fun h => hp h.1), ite_eq_right (by simpa using hp)]
    rw [e]
  have hfr := fracDigits_value_exact 9 (ratV p q % 1000000000) (Nat.mod_lt _ (by decide)) hf
  obtain ⟨_, hlen, hval⟩ := hfr
  have hp := numParts_decimal (ratString p q) (decide (p < 0))
    (Nat.toDigits 10 (ratV p q / 1000000000)) (fracDigits 9 (ratV p q % 1000000000))
    hs (toDigits_digits _) Nat.toDigits_ne_nil (fracDigits_digits 9 _)
  rw [ratOf_eq, ratRead_eq, PdfContentLex.numRat?_parts, hp, Option.map_some]
  dsimp only
  congr 1
  rw [digitsVal_toDigits]
  generalize (fracDigits 9 (ratV p q % 1000000000)).length = L at hlen hval
  generalize digitsVal (fracDigits 9 (ratV p q % 1000000000)) = dv at hval
  have hm := mkRat_frac (ratV p q / 1000000000) dv L 9 hlen
  have hv : ratV p q / 1000000000 * 10 ^ 9 + dv * 10 ^ (9 - L) = ratV p q := by
    rw [hval]
    have : (10 : Nat) ^ 9 = 1000000000 := rfl
    rw [this]
    omega
  rw [hv] at hm
  have h10 : (10 : Nat) ^ 9 = 1000000000 := rfl
  rw [h10] at hm
  by_cases hneg : p < 0
  · have hd : decide (p < 0) = true := decide_eq_true hneg
    rw [hd, ite_eq_left rfl, ite_eq_left hneg, hm]
  · have hd : decide (p < 0) = false := decide_eq_false hneg
    rw [hd, ite_eq_right (by decide), ite_eq_right hneg, hm]

theorem ratOf_ratObj (p q : Int) : ratOf (ratObj p q) = some (ratRead p q) := by
  by_cases hf : ratV p q % 1000000000 = 0
  · have e : ratObj p q = .int (if p < 0 ∧ ratV p q ≠ 0 then -((ratV p q / 1000000000 : Nat) : Int)
        else ((ratV p q / 1000000000 : Nat) : Int)) := by
      rw [ratObj, ite_eq_left hf]
    rw [e]
    exact ratOf_int p q hf
  · have e : ratObj p q = .real (ratString p q) := by
      rw [ratObj, ite_eq_right hf]
    rw [e]
    exact ratOf_real p q hf

/-- A channel's operand as the writer spells it: the ends integers, anything between a real. -/
def milliObj (v : Nat) : Obj :=
  if v = 0 then .int 0 else if v = 1000 then .int 1 else .real (Ir.Color.pdfMilli v)

theorem intRender (k : Nat) : (Obj.int (k : Int)).render = (toString k).toUTF8 := by
  simp only [Obj.render, Obj.renderInto, ByteArray.empty_append]
  congr 1
  apply String.ext
  rw [posSpell, Nat.toString_eq_repr, Nat.toList_repr]

theorem milliObj_render (v : Nat) : (milliObj v).render = (Ir.Color.pdfMilli v).toUTF8 := by
  by_cases h0 : v = 0
  · subst h0
    rw [milliObj, ite_eq_left rfl, Ir.Color.pdfMilli_zero]
    exact intRender 0
  · by_cases h1 : v = 1000
    · subst h1
      rw [milliObj, ite_eq_right h0, ite_eq_left rfl, Ir.Color.pdfMilli_thousand]
      exact intRender 1
    · rw [milliObj, ite_eq_right h0, ite_eq_right h1]
      simp [Obj.render, Obj.renderInto]

theorem milli_chars (v : Nat) (h0 : 0 < v) (h1 : v < 1000) :
    (Ir.Color.pdfMilli v).toList = ([] : List Char) ++ ['0'] ++ '.' :: fracDigits 3 v := by
  rw [Ir.Color.pdfMilli_frac v h0 h1]
  simp [String.toList_append]

theorem milliObj_spelled (v : Nat) (hv : v ≤ 1000) : PdfContentLex.ValSpelled (milliObj v) := by
  refine ⟨?_, fun n g h => by
    rw [milliObj] at h
    split at h
    · cases h
    · split at h <;> cases h⟩
  rw [milliObj]
  split
  · exact .int _
  split
  · exact .int _
  rename_i h0 h1
  have hc := milli_chars v (by omega) (by omega)
  refine .real ⟨by rw [hc]; simp, ?_⟩
  intro c hc'
  rw [hc] at hc'
  simp only [List.nil_append, List.cons_append, List.mem_cons] at hc'
  rcases hc' with rfl | rfl | hc'
  · decide
  · decide
  · exact numByte_digit (fracDigits_digits 3 _ c hc')

theorem ratOf_milliObj (v : Nat) (hv : v ≤ 1000) : ratOf (milliObj v) = some (mkRat v 1000) := by
  by_cases h0 : v = 0
  · subst h0
    rw [milliObj, ite_eq_left rfl, ratOf_eq, numRat_int]
    simp
  · by_cases h1 : v = 1000
    · subst h1
      rw [milliObj, ite_eq_right h0, ite_eq_left rfl, ratOf_eq, numRat_int]
      have := mkRat_scale 1 1000 (by decide)
      simp only [Nat.one_mul] at this
      rw [ite_eq_right (by decide)]
      exact congrArg some this.symm
    · rw [milliObj, ite_eq_right h0, ite_eq_right h1, ratOf_eq, PdfContentLex.numRat?_parts]
      have hfr := fracDigits_value_exact 3 v (by omega) h0
      obtain ⟨_, hlen, hval⟩ := hfr
      have hp := numParts_decimal (Ir.Color.pdfMilli v) false ['0'] (fracDigits 3 v)
        (milli_chars v (by omega) (by omega)) (by decide) (by decide) (fracDigits_digits 3 _)
      rw [hp, Option.map_some]
      dsimp only
      congr 1
      have hz : digitsVal ['0'] = 0 := rfl
      rw [hz, Nat.zero_mul, Nat.zero_add]
      generalize (fracDigits 3 v).length = L at hlen hval
      generalize digitsVal (fracDigits 3 v) = dv at hval
      have hm := mkRat_frac 0 dv L 3 hlen
      rw [Nat.zero_mul, Nat.zero_add, Nat.zero_mul, Nat.zero_add, hval] at hm
      rw [ite_eq_right (by decide), hm]

theorem unit01_id (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) : unit01 q = q := by
  unfold unit01
  rw [Rat.min_def, Rat.max_def]
  by_cases h : (1 : Rat) ≤ q
  · rw [ite_eq_left h, ite_eq_left (by decide : (0 : Rat) ≤ 1)]
    exact (Rat.le_antisymm h1 h).symm
  · rw [ite_eq_right h, ite_eq_left h0]

theorem mkRat_milli_bounds (v : Nat) (hv : v ≤ 1000) :
    0 ≤ mkRat (v : Int) 1000 ∧ mkRat (v : Int) 1000 ≤ 1 := by
  have h1000 : (0 : Rat) < ((1000 : Nat) : Rat) := Rat.natCast_pos.mpr (by decide)
  rw [Rat.mkRat_eq_div]
  constructor
  · rw [← Rat.not_lt, Rat.div_lt_iff h1000]
    intro h
    have : ((v : Int) : Rat) < 0 := by
      have := Rat.mul_zero (((1000 : Nat) : Rat))
      rw [Rat.zero_mul] at h
      exact h
    have hv0 : (0 : Rat) ≤ ((v : Int) : Rat) := by
      rw [Rat.intCast_natCast]
      exact Rat.natCast_nonneg
    exact absurd this (Rat.not_lt.mpr hv0)
  · rw [← Rat.not_lt, Rat.lt_div_iff h1000]
    intro h
    rw [Rat.one_mul] at h
    have : ((v : Int) : Rat) ≤ ((1000 : Nat) : Rat) := by
      rw [Rat.intCast_natCast]
      exact Rat.natCast_le_natCast.mpr hv
    exact absurd h (Rat.not_lt.mpr this)

theorem byteOf_milli (c : UInt8) :
    byteOf (unit01 ((ratOf (milliObj (Ir.Color.milli c))).getD 0)) = c := by
  have hc := c.toNat_lt
  have hm : Ir.Color.milli c ≤ 1000 := by rw [Ir.Color.milli_eq]; omega
  rw [ratOf_milliObj _ hm, Option.getD_some]
  obtain ⟨b0, b1⟩ := mkRat_milli_bounds _ hm
  rw [unit01_id _ b0 b1]
  unfold byteOf
  generalize hv : Ir.Color.milli c = v at hm
  have hv' : v = (c.toNat * 1000 + 127) / 255 := by rw [← hv, Ir.Color.milli_eq]
  have key : mkRat (v : Int) 1000 * 255 + 1 / 2 = (((510 * v + 1000 : Nat) : Rat) / ((2000 : Nat) : Rat)) := by
    rw [Rat.mkRat_eq_div]
    push_cast
    grind
  have hfl := floor_natDiv (510 * v + 1000) 2000 (by decide)
  dsimp only
  rw [key, hfl]
  have hq : (510 * v + 1000) / 2000 = c.toNat := by omega
  rw [hq]
  have h255 : max 0 (min 255 ((c.toNat : Nat) : Int)) = (c.toNat : Int) := by omega
  rw [h255, Int.toNat_natCast]
  exact UInt8.ofNat_toNat

/-- The colour the importer reads back from a written plain colour: its
three bytes, and the components as the PDF spelled them. -/
def colorRead (c : Ir.Color) : Ir.Color :=
  { r := c.r, g := c.g, b := c.b, origin := .declared
    pdfModel := some (.rgb (Ir.Color.pdfMilli (Ir.Color.milli c.r))
      (Ir.Color.pdfMilli (Ir.Color.milli c.g)) (Ir.Color.pdfMilli (Ir.Color.milli c.b))) }

theorem spelling_milliObj (v : Nat) (hv : v ≤ 1000) : spelling (milliObj v) = Ir.Color.pdfMilli v := by
  by_cases h0 : v = 0
  · subst h0
    rw [milliObj, ite_eq_left rfl, Ir.Color.pdfMilli_zero]
    show toString ((0 : Nat) : Int) = "0"
    apply String.ext
    rw [posSpell]
    rfl
  · by_cases h1 : v = 1000
    · subst h1
      rw [milliObj, ite_eq_right h0, ite_eq_left rfl, Ir.Color.pdfMilli_thousand]
      show toString ((1 : Nat) : Int) = "1"
      apply String.ext
      rw [posSpell]
      rfl
    · rw [milliObj, ite_eq_right h0, ite_eq_right h1]
      rfl

theorem milli_le (c : UInt8) : Ir.Color.milli c ≤ 1000 := by
  have := c.toNat_lt
  rw [Ir.Color.milli_eq]
  omega

theorem deviceColor_milli (c : Ir.Color) :
    deviceColor .rgb #[milliObj (Ir.Color.milli c.r), milliObj (Ir.Color.milli c.g),
      milliObj (Ir.Color.milli c.b)] = colorRead c := by
  unfold deviceColor colorRead Ir.Color.declared
  simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.bind_some, Option.getD_some]
  rw [byteOf_milli, byteOf_milli, byteOf_milli, spelling_milliObj _ (milli_le _),
    spelling_milliObj _ (milli_le _), spelling_milliObj _ (milli_le _)]

/-- One token as the writer spells it: the token the reader meets, its
characters, and the byte the writer puts after it. -/
structure Word where
  tok : Tok
  str : String
  sep : UInt8

def Word.chars (w : Word) : List Char := w.str.toList ++ [Char.ofNat w.sep.toNat]

def wordsChars (ws : List Word) : List Char := (ws.map Word.chars).flatten

@[simp] theorem wordsChars_nil : wordsChars [] = [] := rfl

@[simp] theorem wordsChars_cons (w : Word) (ws : List Word) :
    wordsChars (w :: ws) = w.str.toList ++ Char.ofNat w.sep.toNat :: wordsChars ws := by
  simp [wordsChars, Word.chars]

@[simp] theorem wordsChars_append (a b : List Word) :
    wordsChars (a ++ b) = wordsChars a ++ wordsChars b := by
  simp [wordsChars]

@[simp] theorem sep_space : Char.ofNat (32 : UInt8).toNat = ' ' := rfl

@[simp] theorem sep_nl : Char.ofNat (10 : UInt8).toNat = '\n' := rfl

def opW (n : String) : Word := ⟨.op n, n, 32⟩

def lenW (x : Length) : Word := ⟨.val (lenObj x), x.toBpString, 32⟩

/-- A colour channel's thousandth (`Ir.Color.pdfMilli`). -/
def milliW (v : Nat) : Word := ⟨.val (milliObj v), Ir.Color.pdfMilli v, 32⟩

def ratW (p q : Int) : Word := ⟨.val (ratObj p q), ratString p q, 32⟩

/-- A whole number: a cap's or a join's code. -/
def natW (n : Nat) : Word := ⟨.val (.int n), toString n, 32⟩

/-- A dash array, its lengths one space apart in brackets. -/
def dashW (d : Array Length) : Word :=
  ⟨.val (.arr (d.map lenObj)), "[" ++ " ".intercalate (d.toList.map Length.toBpString) ++ "]", 32⟩

/-- A word ending its line. -/
def Word.nl (w : Word) : Word := { w with sep := 10 }

/-- The last word of a run, ending its line. -/
def endLine : List Word → List Word
  | [] => []
  | [w] => [w.nl]
  | w :: rest => w :: endLine rest

def pathWords : Pdf.PathOp → List Word
  | .moveTo x y => [lenW x, lenW y, opW "m"]
  | .lineTo x y => [lenW x, lenW y, opW "l"]
  | .curveTo a b c d e f => [lenW a, lenW b, lenW c, lenW d, lenW e, lenW f, opW "c"]
  | .close => [opW "h"]
  | .rect x y w h => [lenW x, lenW y, lenW w, lenW h, opW "re"]

theorem ts (s : String) : toString s = s := rfl

theorem pathWords_render (p : Pdf.PathOp) : p.render.toList = wordsChars (pathWords p) := by
  cases p <;> simp [Pdf.PathOp.render, pathWords, lenW, opW, ts, String.toList_append]

/-- A colour with no declared device model: the writer spells its three
thousandths (`Ir.Color.pdfComponents`). -/
@[expose] public def plainColor (c : Ir.Color) : Bool := c.pdfModel.isNone && c.cmyk.isNone

/-- A paint the fragment reads back: a plain device colour. -/
@[expose] public def plainPaint : Pdf.PdfPaint → Bool
  | .solid c => plainColor c
  | .pattern _ _ => false

def colorWords (c : Ir.Color) : List Word :=
  [milliW (Ir.Color.milli c.r), milliW (Ir.Color.milli c.g), milliW (Ir.Color.milli c.b)]

/-- A paint's device colour (black for a pattern, which the read-back
does not cover). -/
def paintColor : Pdf.PdfPaint → Ir.Color
  | .solid c => c
  | .pattern _ _ => Ir.Color.black

def fillWords : Option Pdf.PaintFill → List Word
  | some f => colorWords (paintColor f.paint) ++ [opW "rg"]
  | none => []

def capNum : Cap → Nat
  | .butt => 0
  | .round => 1
  | .square => 2

def joinNum : Join → Nat
  | .miter => 0
  | .round => 1
  | .bevel => 2

def capWords : Option Cap → List Word
  | some c => [natW (capNum c), opW "J"]
  | none => []

def joinWords : Option Join → List Word
  | some j => [natW (joinNum j), opW "j"]
  | none => []

def miterWords : Option Rat → List Word
  | some r => [ratW r.num r.den, opW "M"]
  | none => []

def dashWords : Option (Array Length × Length) → List Word
  | some (d, p) => [dashW d, lenW p, opW "d"]
  | none => []

def strokeWords : Option Pdf.PaintStroke → List Word
  | some s => colorWords (paintColor s.paint) ++ [opW "RG", lenW s.width, opW "w"] ++
      capWords s.cap ++ joinWords s.join ++ miterWords s.miter ++ dashWords s.dash
  | none => []

theorem components_chars (c : Ir.Color) :
    c.pdfComponents.toList = (Ir.Color.pdfMilli (Ir.Color.milli c.r)).toList ++ ' ' ::
      ((Ir.Color.pdfMilli (Ir.Color.milli c.g)).toList ++ ' ' ::
        (Ir.Color.pdfMilli (Ir.Color.milli c.b)).toList) := by
  simp [Ir.Color.pdfComponents, String.toList_append]

theorem fillState_chars (fl : Option Pdf.PaintFill) (h : fl.all (plainPaint ·.paint)) :
    (Pdf.fillState fl).toList = wordsChars (fillWords fl) := by
  cases fl with
  | none => rfl
  | some f =>
    obtain ⟨pp, eo⟩ := f
    cases pp with
    | pattern _ _ => simp [plainPaint] at h
    | solid c =>
      simp only [Option.all_some, plainPaint, plainColor, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      simp only [Pdf.fillState, Pdf.pdfPaintFill, Ir.Color.pdfFill_plain c h.1 h.2, fillWords,
        paintColor, colorWords, milliW, opW, String.toList_append, components_chars]
      simp

def capS : Option Cap → String
  | some c => s!"{Pdf.capCode c} J "
  | none => ""

def joinS : Option Join → String
  | some j => s!"{Pdf.joinCode j} j "
  | none => ""

def miterS : Option Rat → String
  | some r => s!"{ratDecimal r} M "
  | none => ""

def dashS : Option (Array Length × Length) → String
  | some (d, p) => Pdf.dashSpelling d p
  | none => ""

theorem strokeState_some (k : Pdf.PaintStroke) :
    Pdf.strokeState (some k) =
      s!"{Pdf.pdfPaintStroke k.paint} {k.width.toBpString} w " ++ capS k.cap ++ joinS k.join ++
        miterS k.miter ++ dashS k.dash := by
  obtain ⟨pp, w, cap, join, miter, dash⟩ := k
  rcases cap with _ | c <;> rcases join with _ | jn <;> rcases miter with _ | r <;>
    rcases dash with _ | ⟨d, p⟩ <;> rfl

theorem capS_chars (c : Option Cap) : (capS c).toList = wordsChars (capWords c) := by
  rcases c with _ | (_ | _ | _) <;> simp [capS, Pdf.capCode, capWords, capNum, natW, opW, ts,
    String.toList_append]

theorem joinS_chars (c : Option Join) : (joinS c).toList = wordsChars (joinWords c) := by
  rcases c with _ | (_ | _ | _) <;> simp [joinS, Pdf.joinCode, joinWords, joinNum, natW, opW, ts,
    String.toList_append]

theorem ratDecimal_eq (r : Rat) : ratDecimal r = ratString r.num r.den := rfl

theorem miterS_chars (m : Option Rat) : (miterS m).toList = wordsChars (miterWords m) := by
  rcases m with _ | r
  · rfl
  · simp only [miterS, ratDecimal_eq, miterWords, ratW, opW, ts, String.toList_append, wordsChars_cons,
      wordsChars_nil, sep_space]
    simp

theorem dashS_chars (dp : Option (Array Length × Length)) : (dashS dp).toList = wordsChars (dashWords dp) := by
  rcases dp with _ | ⟨d, p⟩
  · rfl
  · simp [dashS, Pdf.dashSpelling, dashWords, dashW, lenW, opW, String.toList_append]

theorem strokeState_chars (st : Option Pdf.PaintStroke) (h : st.all (plainPaint ·.paint)) :
    (Pdf.strokeState st).toList = wordsChars (strokeWords st) := by
  cases st with
  | none => rfl
  | some k =>
    obtain ⟨pp, w, cap, join, miter, dash⟩ := k
    cases pp with
    | pattern _ _ => simp [plainPaint] at h
    | solid c =>
      simp only [Option.all_some, plainPaint, plainColor, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      rw [strokeState_some]
      simp only [String.toList_append, capS_chars, joinS_chars, miterS_chars, dashS_chars, strokeWords,
        wordsChars_append]
      simp [Pdf.pdfPaintStroke, Ir.Color.pdfStroke_plain c h.1 h.2, paintColor, colorWords, milliW, opW,
        lenW, String.toList_append, components_chars, ts]

theorem foldl_append_join {α : Type} (f : α → String) (a : String) (l : List α) :
    l.foldl (fun acc x => acc ++ f x) a = a ++ String.join (l.map f) := by
  induction l generalizing a with
  | nil => simp [String.join_nil]
  | cons x xs ih => simp [ih, String.join_cons, String.append_assoc]

theorem segs_chars_list (l : List Pdf.PathOp) :
    (String.join (l.map Pdf.PathOp.render)).toList = wordsChars (l.flatMap pathWords) := by
  induction l with
  | nil => simp [String.join_nil]
  | cons x xs ih => rw [List.map_cons, String.join_cons, String.toList_append, ih, List.flatMap_cons,
      wordsChars_append, pathWords_render]

theorem segs_chars (segs : Array Pdf.PathOp) :
    (String.join (segs.toList.map Pdf.PathOp.render)).toList = wordsChars (segs.toList.flatMap pathWords) :=
  segs_chars_list segs.toList

/-- A `paint` operation's words: `q`, the fill's and the stroke's state,
the path, the painting operator, `Q` ending its line. -/
def paintWords (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp) :
    List Word :=
  [opW "q"] ++ fillWords fl ++ strokeWords st ++ segs.toList.flatMap pathWords ++
    [opW (Pdf.paintOp fl st), (opW "Q").nl]

theorem paint_chars (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp)
    (hf : fl.all (plainPaint ·.paint)) (hs : st.all (plainPaint ·.paint)) :
    ((Pdf.ContentOp.paint fl st none segs).render ++ "\n").toList = wordsChars (paintWords fl st segs) := by
  simp only [Pdf.ContentOp.render, Pdf.gsState]
  rw [← Array.foldl_toList, foldl_append_join]
  simp only [String.toList_append, fillState_chars fl hf, strokeState_chars st hs, segs_chars, paintWords,
    wordsChars_append]
  simp [opW, Word.nl]

/-- Words each led by a space: what the writer appends after `q` in a
saved state's header. -/
def lead (ws : List Word) : List Char := (ws.map fun w => ' ' :: w.str.toList).flatten

theorem lead_append (a b : List Word) : lead (a ++ b) = lead a ++ lead b := by
  simp [lead]

theorem lead_endLine (a : Word) (ws : List Word) (ha : a.sep = 32) (hs : ∀ w ∈ ws, w.sep = 32) :
    a.str.toList ++ lead ws ++ ['\n'] = wordsChars (endLine (a :: ws)) := by
  induction ws generalizing a with
  | nil => simp [endLine, lead, Word.nl]
  | cons b rest ih =>
    have hb : b.sep = 32 := hs b (by simp)
    have := ih b hb (fun w hw => hs w (by simp [hw]))
    simp only [endLine]
    rw [wordsChars_cons, ← this, ha]
    simp [lead]

/-- A translation in base units as the fraction of a big point `unitsRatBpString` spells. -/
@[expose] public def bpPair (r : Rat) : Int × Int := (r.num * 72, (r.den : Int) * 72 * bpUnits)

theorem unitsRatBpString_pair (r : Rat) :
    unitsRatBpString r = ratString (bpPair r).1 (bpPair r).2 := by
  simp only [bpPair]
  exact unitsRatBpString_bp r

/-- A matrix's words: its six operands (`Gfx.Affine.operands`) and `cm`. -/
def cmWords (m : Affine) : List Word :=
  [ratW m.a.num m.a.den, ratW m.b.num m.b.den, ratW m.c.num m.c.den, ratW m.d.num m.d.den,
   ratW (bpPair m.e).1 (bpPair m.e).2, ratW (bpPair m.f).1 (bpPair m.f).2, opW "cm"]

/-- A clipping path's words: the path, `W` or `W*`, `n`. -/
def clipWords (c : Array Pdf.PathOp × Rule) : List Word :=
  c.1.toList.flatMap pathWords ++
    (match c.2 with
     | .nonzero => [opW "W", opW "n"]
     | .evenOdd => [opW "W*", opW "n"])

/-- A saved state's header words: `q`, its matrix, its clips. -/
def headerWords (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) : List Word :=
  opW "q" :: (((m.map cmWords).getD []) ++ clips.toList.flatMap clipWords)

def clipStr (c : Array Pdf.PathOp × Rule) : String :=
  " " ++ String.join (c.1.toList.map Pdf.PathOp.render) ++
    (match c.2 with
     | .nonzero => "W n"
     | .evenOdd => "W* n")

def cmStr : Option Affine → String
  | some mm => " " ++ mm.operands ++ " cm"
  | none => ""

theorem groupHeader_eq (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    Pdf.groupHeader m none clips = "q" ++ cmStr m ++ String.join (clips.toList.map clipStr) := by
  unfold Pdf.groupHeader
  dsimp only
  rw [String.append_empty]
  have h1 : (match m with
      | some mm => " " ++ mm.operands ++ " cm"
      | none => "") = cmStr m := by
    cases m <;> rfl
  have h2 : (List.map (fun c : Array Pdf.PathOp × Rule => " " ++ String.join (List.map Pdf.PathOp.render c.fst.toList) ++
      match c.snd with
      | Rule.nonzero => "W n"
      | Rule.evenOdd => "W* n") clips.toList) = List.map clipStr clips.toList := by
    congr 1
  exact congr (congrArg HAppend.hAppend (congrArg (HAppend.hAppend "q") h1)) (congrArg String.join h2)

theorem operands_eq (m : Affine) : m.operands =
    ratDecimal m.a ++ " " ++ ratDecimal m.b ++ " " ++ ratDecimal m.c ++ " " ++ ratDecimal m.d ++ " " ++
      ratString (bpPair m.e).1 (bpPair m.e).2 ++ " " ++ ratString (bpPair m.f).1 (bpPair m.f).2 := by
  simp only [Affine.operands, unitsRatBpString_pair]
  rfl

theorem cm_chars (a b c d e f : String) :
    (" " ++ (a ++ " " ++ b ++ " " ++ c ++ " " ++ d ++ " " ++ e ++ " " ++ f) ++ " cm").toList =
      lead [⟨.op "", a, 32⟩, ⟨.op "", b, 32⟩, ⟨.op "", c, 32⟩, ⟨.op "", d, 32⟩, ⟨.op "", e, 32⟩,
        ⟨.op "", f, 32⟩, opW "cm"] := by
  simp [lead, opW, String.toList_append]

theorem lead_str (ws vs : List Word) (h : ws.map Word.str = vs.map Word.str) : lead ws = lead vs := by
  induction ws generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons w rest ih =>
    cases vs with
    | nil => simp at h
    | cons v vrest =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [lead, List.map_cons, List.flatten_cons]
      rw [h.1]
      have := ih vrest h.2
      simp only [lead] at this
      rw [this]

theorem cmStr_chars (m : Option Affine) : (cmStr m).toList = lead ((m.map cmWords).getD []) := by
  cases m with
  | none => rfl
  | some mm =>
    rw [cmStr, operands_eq, ratDecimal_eq, ratDecimal_eq, ratDecimal_eq, ratDecimal_eq, cm_chars,
      Option.map_some, Option.getD_some]
    apply lead_str
    rfl

theorem pathWords_sep (p : Pdf.PathOp) : ∀ w ∈ pathWords p, w.sep = 32 := by
  cases p <;> simp [pathWords, lenW, opW]

theorem spaceShift (ws : List Word) (hws : ∀ w ∈ ws, w.sep = 32) (t : List Char) :
    ' ' :: (wordsChars ws ++ t) = lead ws ++ ' ' :: t := by
  induction ws with
  | nil => simp [lead]
  | cons w rest ihw =>
    have hw : w.sep = 32 := hws w (by simp)
    simp only [wordsChars_cons, hw, sep_space, List.append_assoc, List.cons_append]
    rw [ihw (fun v hv => hws v (by simp [hv]))]
    simp [lead]

theorem flatMap_pathWords_sep (l : List Pdf.PathOp) : ∀ w ∈ l.flatMap pathWords, w.sep = 32 := by
  intro w hw
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hw
  exact pathWords_sep p w hp

theorem clipStr_chars (c : Array Pdf.PathOp × Rule) : (clipStr c).toList = lead (clipWords c) := by
  obtain ⟨segs, rule⟩ := c
  have h := spaceShift (segs.toList.flatMap pathWords) (flatMap_pathWords_sep _) []
  rw [List.append_nil, ← segs_chars] at h
  have e : (clipStr (segs, rule)).toList =
      (' ' :: (String.join (segs.toList.map Pdf.PathOp.render)).toList) ++
        (match rule with
         | .nonzero => "W n"
         | .evenOdd => "W* n").toList := by
    simp [clipStr, String.toList_append]
  rw [e, h, clipWords, lead_append]
  cases rule <;> simp [lead, opW]

theorem clips_chars (cs : List (Array Pdf.PathOp × Rule)) :
    (String.join (cs.map clipStr)).toList = lead (cs.flatMap clipWords) := by
  induction cs with
  | nil => simp [lead, String.join_nil]
  | cons c rest ih => rw [List.map_cons, String.join_cons, String.toList_append, ih, clipStr_chars,
      List.flatMap_cons, lead_append]

theorem headerWords_sep (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    ∀ w ∈ ((m.map cmWords).getD []) ++ clips.toList.flatMap clipWords, w.sep = 32 := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · cases m with
    | none => simp at hw
    | some mm =>
      simp only [Option.map_some, Option.getD_some, cmWords, ratW, opW, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hw
    rw [clipWords, List.mem_append] at hc
    rcases hc with hc | hc
    · exact flatMap_pathWords_sep _ w hc
    · obtain ⟨_, rule⟩ := c
      cases rule <;> simp only [opW, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
        rcases hc with rfl | rfl <;> rfl

theorem groupHeader_chars (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    (Pdf.groupHeader m none clips ++ "\n").toList = wordsChars (endLine (headerWords m clips)) := by
  rw [headerWords, ← lead_endLine (opW "q") _ rfl (headerWords_sep m clips), groupHeader_eq]
  simp only [String.toList_append, cmStr_chars, clips_chars, lead_append, opW]
  simp

/-- What a matrix's six printed operands read back as, each at nine decimals. -/
@[expose] public def readAffine (m : Affine) : Affine :=
  ⟨ratRead m.a.num m.a.den, ratRead m.b.num m.b.den, ratRead m.c.num m.c.den, ratRead m.d.num m.d.den,
   ratRead (bpPair m.e).1 (bpPair m.e).2 * bpU, ratRead (bpPair m.f).1 (bpPair m.f).2 * bpU⟩

mutual

-- conserves: none — a predicate.
/-- The operations the read-back covers: plain opaque paths, and saved states around them with no
ExtGState, no matrix reading back as the identity and no empty clip path. -/
@[expose] public def opPlain : Pdf.ContentOp → Bool
  | .paint fl st gs segs =>
    gs.isNone && fl.all (plainPaint ·.paint) && st.all (plainPaint ·.paint) &&
      (fl.isSome || st.isSome) && !segs.isEmpty
  | .group m gs clips body =>
    gs.isNone && m.all (fun mm => decide (readAffine mm ≠ Affine.unit)) && clips.all (!·.1.isEmpty) &&
      opsPlain body.toList
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => false

@[expose] public def opsPlain : List Pdf.ContentOp → Bool
  | [] => true
  | o :: rest => opPlain o && opsPlain rest

end

mutual

def opWords : Pdf.ContentOp → List Word
  | .paint fl st _ segs => paintWords fl st segs
  | .group m _ clips body => endLine (headerWords m clips) ++ opWordsInto [] body.toList ++ [(opW "Q").nl]
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => []

def opWordsInto (acc : List Word) : List Pdf.ContentOp → List Word
  | [] => acc
  | o :: rest => opWordsInto (acc ++ opWords o) rest

end

def opWordsList (l : List Pdf.ContentOp) : List Word := opWordsInto [] l

theorem opWordsInto_acc (acc : List Word) (l : List Pdf.ContentOp) :
    opWordsInto acc l = acc ++ opWordsInto [] l := by
  induction l generalizing acc with
  | nil => simp [opWordsInto]
  | cons o rest ih =>
    rw [opWordsInto, opWordsInto, ih, ih ([] ++ opWords o)]
    simp

@[simp] theorem opWordsList_nil : opWordsList [] = [] := rfl

theorem opWordsList_cons (o : Pdf.ContentOp) (rest : List Pdf.ContentOp) :
    opWordsList (o :: rest) = opWords o ++ opWordsList rest := by
  unfold opWordsList
  rw [opWordsInto, opWordsInto_acc, List.nil_append]

theorem opWords_group (m : Option Affine) (gs : Option Pdf.ExtG) (clips : Array (Array Pdf.PathOp × Rule))
    (body : Array Pdf.ContentOp) :
    opWords (.group m gs clips body) = endLine (headerWords m clips) ++ opWordsList body.toList ++ [(opW "Q").nl] := by
  rw [opWords]
  rfl

theorem renderLines_eq (acc : String) (l : List Pdf.ContentOp) :
    Pdf.ContentOp.renderLines acc l = acc ++ String.join (l.map fun o => o.render ++ "\n") := by
  induction l generalizing acc with
  | nil => simp [Pdf.ContentOp.renderLines, String.join_nil]
  | cons o rest ih =>
    rw [Pdf.ContentOp.renderLines, ih, List.map_cons, String.join_cons]
    simp [String.append_assoc]

mutual

theorem op_chars : ∀ (o : Pdf.ContentOp), opPlain o = true →
    (o.render ++ "\n").toList = wordsChars (opWords o)
  | .paint fl st gs segs, h => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨hgs, hf⟩, hs⟩, _⟩, _⟩ := h
    subst hgs
    rw [opWords]
    exact paint_chars fl st segs hf hs
  | .group m gs clips body, h => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨hgs, _⟩, _⟩, hb⟩ := h
    subst hgs
    rw [Pdf.ContentOp.render, renderLines_eq, opWords_group]
    simp only [String.toList_append, wordsChars_append]
    rw [← groupHeader_chars, ops_chars body.toList hb]
    simp [opW, Word.nl, String.toList_append]
  | .fill _ _ _ _ _, h | .text _, h | .image _ _ _ _ _, h | .imageMissing _ _ _ _, h | .marked _ _, h
  | .shade _ _, h | .outline _ _ _, h | .xobject _ _ _ _, h => by simp [opPlain] at h

theorem ops_chars : ∀ (l : List Pdf.ContentOp), opsPlain l = true →
    (String.join (l.map fun o => o.render ++ "\n")).toList = wordsChars (opWordsList l)
  | [], _ => by simp [String.join_nil]
  | o :: rest, h => by
    simp only [opsPlain, Bool.and_eq_true] at h
    rw [List.map_cons, String.join_cons, String.toList_append, op_chars o h.1, ops_chars rest h.2,
      opWordsList_cons, wordsChars_append]

end

theorem toUTF8_chars (s : String) : s.toUTF8 = s.toList.utf8Encode := by
  conv => lhs; rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]

/-- A word the tokenizer reads back: its token spelled as its characters,
the token one the writer spells, a space or a line feed after it. -/
structure WordOk (w : Word) : Prop where
  spell : PdfContentLex.spell w.tok = w.str.toUTF8
  tok : PdfContentLex.TokSpelled w.tok
  sep : w.sep = 32 ∨ w.sep = 10

theorem sepBytes (w : UInt8) (h : w = 32 ∨ w = 10) : [Char.ofNat w.toNat].utf8Encode = ⟨#[w]⟩ := by
  rcases h with rfl | rfl <;> rfl

theorem words_bytes (ws : List Word) (hv : ∀ w ∈ ws, WordOk w) :
    (wordsChars ws).utf8Encode = PdfContentLex.renderSep true (ws.map fun w => (w.tok, w.sep)) := by
  induction ws with
  | nil => simp [PdfContentLex.renderSep_nil]
  | cons w rest ih =>
    have hw := hv w (by simp)
    rw [wordsChars_cons, List.map_cons, PdfContentLex.renderSep_cons, PdfContentLex.sepOf_true,
      ← List.singleton_append, List.utf8Encode_append, List.utf8Encode_append, ← toUTF8_chars,
      ← hw.spell, sepBytes w.sep hw.sep, ih (fun v hv' => hv v (by simp [hv'])), ByteArray.append_assoc]

theorem foldl_renderStep (s : String) (l : List Pdf.ContentOp) :
    l.foldl Pdf.renderStep (some s) = some (s ++ String.join (l.map fun o => "\n" ++ o.render)) := by
  induction l generalizing s with
  | nil => simp [String.join_nil]
  | cons o rest ih =>
    rw [List.foldl_cons, Pdf.renderStep, ih, List.map_cons, String.join_cons]
    simp [String.append_assoc]

theorem shift_nl (a : String) (l : List Pdf.ContentOp) :
    (a ++ String.join (l.map fun o => "\n" ++ o.render) ++ "\n").toList =
      (a ++ "\n" ++ String.join (l.map fun o => o.render ++ "\n")).toList := by
  induction l generalizing a with
  | nil => simp [String.join_nil]
  | cons o rest ih =>
    rw [List.map_cons, String.join_cons, List.map_cons, String.join_cons]
    have := ih (a ++ "\n" ++ o.render)
    simp only [String.toList_append, List.append_assoc] at this ⊢
    rw [this]

theorem render_nl_chars (ops : Array Pdf.ContentOp) (h : ops.toList ≠ []) :
    (Pdf.render ops ++ "\n").toList = (String.join (ops.toList.map fun o => o.render ++ "\n")).toList := by
  obtain ⟨o, rest, hl⟩ := List.exists_cons_of_ne_nil h
  unfold Pdf.render
  rw [← Array.foldl_toList, hl, List.foldl_cons, Pdf.renderStep, foldl_renderStep, Option.getD_some,
    shift_nl, List.map_cons, String.join_cons]

theorem renderInto_eq (acc : ByteArray) (o : Obj) : Obj.renderInto acc o = acc ++ o.render := by
  have := PdfRead.Obj.renderInto_append acc ByteArray.empty o
  rw [ByteArray.append_empty] at this
  exact this

theorem renderList_len (acc : ByteArray) : ∀ (d : List Length),
    Obj.renderList acc (d.map lenObj) = acc ++ (" ".intercalate (d.map Length.toBpString)).toUTF8
  | [] => by simp [Obj.renderList, String.intercalate_nil]
  | [x] => by simp [Obj.renderList, String.intercalate_singleton, renderInto_eq, lenObj_render]
  | x :: y :: rest => by
    rw [List.map_cons, List.map_cons, Obj.renderList, ← List.map_cons, renderList_len _ (y :: rest),
      renderInto_eq, lenObj_render]
    · simp only [List.map_cons, String.intercalate_cons_cons]
      apply ByteArray.ext
      have hs : " ".toByteArray.data = #[32] := rfl
      simp only [ByteArray.data_append, ByteArray.data_push, String.toByteArray_append, hs,
        String.toUTF8_eq_toByteArray]
      rw [Array.push_eq_append]
      simp only [Array.append_assoc]
    · simp

theorem dash_render (d : Array Length) :
    (Obj.arr (d.map lenObj)).render = ("[" ++ " ".intercalate (d.toList.map Length.toBpString) ++ "]").toUTF8 := by
  simp only [Obj.render, Obj.renderInto, Array.toList_map, renderList_len]
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.data_push, String.toByteArray_append]
  rfl

theorem lenObj_repr (x : Length) : (lenObj x).Representable := (lenObj_spelled x).1

theorem dash_spelled (d : Array Length) : PdfContentLex.ValSpelled (.arr (d.map lenObj)) := by
  refine ⟨.arr fun x hx => ?_, fun _ _ h => by cases h⟩
  obtain ⟨y, _, rfl⟩ := Array.mem_map.mp hx
  exact lenObj_repr y

macro "opspelled" : tactic =>
  `(tactic| exact ⟨by decide, by decide, by decide, by decide, by decide⟩)

theorem opW_ok (n : String) (h : PdfContentLex.OpSpelled n) : WordOk (opW n) := ⟨rfl, h, Or.inl rfl⟩

theorem lenW_ok (x : Length) : WordOk (lenW x) := ⟨lenObj_render x, lenObj_spelled x, Or.inl rfl⟩

theorem milliW_ok (v : Nat) (hv : v ≤ 1000) : WordOk (milliW v) :=
  ⟨milliObj_render v, milliObj_spelled v hv, Or.inl rfl⟩

theorem ratW_tok (p q : Int) : (ratW p q).tok = .val (ratObj p q) := rfl

theorem ratW_str (p q : Int) : (ratW p q).str = ratString p q := rfl

theorem ratW_sep (p q : Int) : (ratW p q).sep = 32 := rfl

theorem spell_val (o : Obj) : PdfContentLex.spell (.val o) = o.render := rfl

theorem ratW_ok (p q : Int) : WordOk (ratW p q) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ratW_tok, ratW_str, spell_val]
    exact ratObj_render p q
  · rw [ratW_tok]
    exact ratObj_spelled p q
  · rw [ratW_sep]
    exact Or.inl rfl

theorem natW_ok (n : Nat) : WordOk (natW n) :=
  ⟨intRender n, ⟨.int _, fun _ _ h => by cases h⟩, Or.inl rfl⟩

theorem dashW_ok (d : Array Length) : WordOk (dashW d) := ⟨dash_render d, dash_spelled d, Or.inl rfl⟩

theorem nl_ok {w : Word} (h : WordOk w) : WordOk w.nl := ⟨h.spell, h.tok, Or.inr rfl⟩

theorem endLine_ok : ∀ (ws : List Word), (∀ w ∈ ws, WordOk w) → ∀ w ∈ endLine ws, WordOk w
  | [], _ => by simp [endLine]
  | [v], h => by simp only [endLine, List.mem_singleton]; intro w hw; subst hw; exact nl_ok (h v (by simp))
  | v :: u :: rest, h => by
    intro w hw
    simp only [endLine, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact h w (by simp)
    · exact endLine_ok (u :: rest) (fun x hx => h x (by simp_all)) w (by simpa [endLine] using hw)

theorem paintOp_cases (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) :
    Pdf.paintOp fl st = "f" ∨ Pdf.paintOp fl st = "f*" ∨ Pdf.paintOp fl st = "S" ∨
      Pdf.paintOp fl st = "B" ∨ Pdf.paintOp fl st = "B*" ∨ Pdf.paintOp fl st = "n" := by
  rcases fl with _ | ⟨_, _ | _⟩ <;> rcases st with _ | _ <;> simp [Pdf.paintOp]

theorem paintOp_spelled (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) :
    PdfContentLex.OpSpelled (Pdf.paintOp fl st) := by
  rcases paintOp_cases fl st with h | h | h | h | h | h <;> rw [h] <;> opspelled

theorem pathWords_ok (p : Pdf.PathOp) : ∀ w ∈ pathWords p, WordOk w := by
  cases p <;> simp only [pathWords, List.mem_cons, List.not_mem_nil, or_false] <;> intro w hw <;>
    (repeat' rcases hw with rfl | hw) <;>
    first
    | exact lenW_ok _
    | exact opW_ok _ (by opspelled)

theorem flatMap_ok {α : Type} (f : α → List Word) (l : List α) (h : ∀ a ∈ l, ∀ w ∈ f a, WordOk w) :
    ∀ w ∈ l.flatMap f, WordOk w := by
  intro w hw
  obtain ⟨a, ha, hw⟩ := List.mem_flatMap.mp hw
  exact h a ha w hw

theorem colorWords_ok (c : Ir.Color) : ∀ w ∈ colorWords c, WordOk w := by
  simp only [colorWords, List.mem_cons, List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl) <;> exact milliW_ok _ (milli_le _)

theorem fillWords_ok (fl : Option Pdf.PaintFill) : ∀ w ∈ fillWords fl, WordOk w := by
  cases fl with
  | none => simp [fillWords]
  | some f =>
    simp only [fillWords, List.mem_append, List.mem_singleton]
    rintro w (hw | rfl)
    · exact colorWords_ok _ w hw
    · exact opW_ok _ (by opspelled)

theorem strokeWords_ok (st : Option Pdf.PaintStroke) : ∀ w ∈ strokeWords st, WordOk w := by
  cases st with
  | none => simp [strokeWords]
  | some k =>
    simp only [strokeWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro w (((((hw | rfl | rfl | rfl) | hw) | hw) | hw) | hw)
    · exact colorWords_ok _ w hw
    · exact opW_ok _ (by opspelled)
    · exact lenW_ok _
    · exact opW_ok _ (by opspelled)
    · rcases k with ⟨_, _, _ | c, _, _, _⟩ <;> simp only [capWords, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact natW_ok _
      · exact opW_ok _ (by opspelled)
    · rcases k with ⟨_, _, _, _ | j, _, _⟩ <;> simp only [joinWords, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact natW_ok _
      · exact opW_ok _ (by opspelled)
    · rcases k with ⟨_, _, _, _, _ | r, _⟩ <;> simp only [miterWords, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact ratW_ok _ _
      · exact opW_ok _ (by opspelled)
    · rcases k with ⟨_, _, _, _, _, _ | ⟨d, p⟩⟩ <;> simp only [dashWords, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dashW_ok _
      · exact lenW_ok _
      · exact opW_ok _ (by opspelled)

theorem paintWords_ok (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp) :
    ∀ w ∈ paintWords fl st segs, WordOk w := by
  simp only [paintWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro w ((((rfl | hw) | hw) | hw) | rfl | rfl)
  · exact opW_ok _ (by opspelled)
  · exact fillWords_ok fl w hw
  · exact strokeWords_ok st w hw
  · exact flatMap_ok _ _ (fun p _ => pathWords_ok p) w hw
  · exact opW_ok _ (paintOp_spelled fl st)
  · exact nl_ok (opW_ok _ (by opspelled))

theorem headerWords_ok (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    ∀ w ∈ headerWords m clips, WordOk w := by
  simp only [headerWords, List.mem_cons, List.mem_append]
  rintro w (rfl | hw | hw)
  · exact opW_ok _ (by opspelled)
  · cases m with
    | none => simp at hw
    | some mm =>
      simp only [Option.map_some, Option.getD_some, cmWords, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact ratW_ok _ _
        | exact opW_ok _ (by opspelled)
  · refine flatMap_ok _ _ (fun c _ w hw => ?_) w hw
    simp only [clipWords, List.mem_append] at hw
    rcases hw with hw | hw
    · exact flatMap_ok _ _ (fun p _ => pathWords_ok p) w hw
    · obtain ⟨_, rule⟩ := c
      cases rule <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;>
        rcases hw with rfl | rfl <;> exact opW_ok _ (by opspelled)

mutual

theorem opWords_ok : ∀ (o : Pdf.ContentOp), ∀ w ∈ opWords o, WordOk w
  | .paint fl st _ segs => by rw [opWords]; exact paintWords_ok fl st segs
  | .group m _ clips body => by
    rw [opWords_group]
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | hw) | rfl
    · exact endLine_ok _ (headerWords_ok m clips) w hw
    · exact opWordsList_ok body.toList w hw
    · exact nl_ok (opW_ok _ (by opspelled))
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => by simp [opWords]

theorem opWordsList_ok : ∀ (l : List Pdf.ContentOp), ∀ w ∈ opWordsList l, WordOk w
  | [] => by simp
  | o :: rest => by
    rw [opWordsList_cons]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact opWords_ok o w hw
    · exact opWordsList_ok rest w hw

end

theorem spelled_append : ∀ (A B : List Tok), PdfContentLex.Spelled A → PdfContentLex.Spelled B →
    (∀ o, A.getLast? = some (.val o) → PdfContentLex.readByObj o = true →
      ∀ u ∈ B.head?, PdfContentLex.leadR u = false) →
    PdfContentLex.Spelled (A ++ B)
  | [], _, _, hB, _ => hB
  | [t], B, hA, hB, hj => ⟨hA.1, fun o ht hr u hu => hj o (by simp [ht]) hr u hu, hB⟩
  | t :: t' :: rest, B, hA, hB, hj =>
    ⟨hA.1, fun o ht hr u hu => hA.2.1 o ht hr u (by simpa using hu),
      spelled_append (t' :: rest) B hA.2.2 hB (fun o h => hj o (by simpa using h))⟩

/-- A run of words the tokenizer reads back token by token, ending with an
operator — so no array before it can meet an `R` after it. -/
def Good (ws : List Word) : Prop :=
  PdfContentLex.Spelled (ws.map (·.tok)) ∧ ∀ w, ws.getLast? = some w → ∃ n, w.tok = .op n

theorem good_nil : Good [] := ⟨trivial, fun _ h => by simp at h⟩

theorem good_append (A B : List Word) (hA : Good A) (hB : Good B) : Good (A ++ B) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_append]
    refine spelled_append _ _ hA.1 hB.1 (fun o h _ u _ => ?_)
    rw [List.getLast?_map] at h
    cases hl : A.getLast? with
    | none => simp [hl] at h
    | some w =>
      obtain ⟨n, hn⟩ := hA.2 w hl
      simp [hl, hn] at h
  · intro w hw
    rw [List.getLast?_append] at hw
    cases hb : B.getLast? with
    | none => simp [hb] at hw; exact hA.2 w hw
    | some v => simp [hb] at hw; subst hw; exact hB.2 v hb

theorem good_free (ws : List Word) (ht : ∀ w ∈ ws, PdfContentLex.TokSpelled w.tok)
    (hf : ∀ w ∈ ws, ∀ o, w.tok = .val o → PdfContentLex.readByObj o = false)
    (hl : ∀ w, ws.getLast? = some w → ∃ n, w.tok = .op n) : Good ws := by
  refine ⟨?_, hl⟩
  clear hl
  induction ws with
  | nil => trivial
  | cons w rest ih =>
    refine ⟨ht w (by simp), fun o h hr => ?_, ih (fun v hv => ht v (by simp [hv]))
      (fun v hv => hf v (by simp [hv]))⟩
    rw [hf w (by simp) o h] at hr
    exact absurd hr (by decide)

theorem readByObj_lenObj (x : Length) : PdfContentLex.readByObj (lenObj x) = false := by
  unfold lenObj; split <;> rfl

theorem readByObj_milliObj (v : Nat) : PdfContentLex.readByObj (milliObj v) = false := by
  unfold milliObj; split; · rfl
  split <;> rfl

theorem readByObj_ratObj (p q : Int) : PdfContentLex.readByObj (ratObj p q) = false := by
  rw [ratObj]; split <;> rfl

/-- A word whose token is no operand the object reader reads. -/
def FreeW (w : Word) : Prop := ∀ o, w.tok = .val o → PdfContentLex.readByObj o = false

@[simp] theorem free_lenW (x : Length) : FreeW (lenW x) := by
  intro o h; simp only [lenW, Tok.val.injEq] at h; subst h; exact readByObj_lenObj x

@[simp] theorem free_milliW (v : Nat) : FreeW (milliW v) := by
  intro o h; simp only [milliW, Tok.val.injEq] at h; subst h; exact readByObj_milliObj v

@[simp] theorem free_ratW (p q : Int) : FreeW (ratW p q) := by
  intro o h; rw [ratW_tok] at h; simp only [Tok.val.injEq] at h; subst h; exact readByObj_ratObj p q

@[simp] theorem free_natW (n : Nat) : FreeW (natW n) := by
  intro o h; simp only [natW, Tok.val.injEq] at h; subst h; rfl

@[simp] theorem free_opW (n : String) : FreeW (opW n) := by
  intro o h; cases h

@[simp] theorem free_nl (w : Word) : FreeW w.nl ↔ FreeW w := Iff.rfl

theorem good_free' (ws : List Word) (hok : ∀ w ∈ ws, WordOk w) (hf : ∀ w ∈ ws, FreeW w)
    (hl : ∀ w, ws.getLast? = some w → ∃ n, w.tok = .op n) : Good ws :=
  good_free ws (fun w hw => (hok w hw).tok) hf hl

theorem good_opW (n : String) (h : PdfContentLex.OpSpelled n) : Good [opW n] :=
  good_free' _ (by simp only [List.mem_singleton]; rintro w rfl; exact opW_ok n h) (by simp) (by simp [opW])

theorem good_pathWords (p : Pdf.PathOp) : Good (pathWords p) := by
  refine good_free' _ (pathWords_ok p) ?_ ?_
  · cases p <;> simp [pathWords]
  · cases p <;> simp [pathWords, opW]

theorem good_flatMap {α : Type} (f : α → List Word) (h : ∀ a, Good (f a)) :
    ∀ (l : List α), Good (l.flatMap f)
  | [] => good_nil
  | a :: rest => by rw [List.flatMap_cons]; exact good_append _ _ (h a) (good_flatMap f h rest)

theorem good_fillWords (fl : Option Pdf.PaintFill) : Good (fillWords fl) := by
  cases fl with
  | none => exact good_nil
  | some f =>
    refine good_free' _ (fillWords_ok _) ?_ ?_
    · simp [fillWords, colorWords]
    · simp [fillWords, opW]

theorem good_strokeWords (st : Option Pdf.PaintStroke) : Good (strokeWords st) := by
  cases st with
  | none => exact good_nil
  | some k =>
    have hok := strokeWords_ok (some k)
    simp only [strokeWords] at hok
    have hpre : Good (colorWords (paintColor k.paint) ++ [opW "RG", lenW k.width, opW "w"]) :=
      good_free' _ (fun w hw => hok w (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hw)))))
        (by simp [colorWords]) (by simp [opW])
    have hcap : Good (capWords k.cap) := by
      rcases hc : k.cap with _ | c
      · exact good_nil
      · rw [← hc]
        refine good_free' _ (fun w hw => hok w (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ hw))))) ?_ ?_
        · rw [hc]; simp [capWords]
        · rw [hc]; simp [capWords, opW]
    have hjoin : Good (joinWords k.join) := by
      rcases hc : k.join with _ | c
      · exact good_nil
      · rw [← hc]
        refine good_free' _ (fun w hw => hok w (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ hw)))) ?_ ?_
        · rw [hc]; simp [joinWords]
        · rw [hc]; simp [joinWords, opW]
    have hmiter : Good (miterWords k.miter) := by
      rcases hc : k.miter with _ | c
      · exact good_nil
      · rw [← hc]
        refine good_free' _ (fun w hw => hok w (List.mem_append_left _ (List.mem_append_right _ hw))) ?_ ?_
        · rw [hc]; simp [miterWords]
        · rw [hc]; simp [miterWords, opW]
    have hdash : Good (dashWords k.dash) := by
      rcases k.dash with _ | ⟨d, p⟩
      · exact good_nil
      · show Good [dashW d, lenW p, opW "d"]
        have hd : PdfContentLex.OpSpelled "d" := by opspelled
        refine ⟨⟨(dashW_ok d).tok, fun o _ _ u hu => ?_, (lenW_ok p).tok, fun o h hr => ?_,
          hd, (fun o h => by cases h), trivial⟩, by simp [opW]⟩
        · simp [lenW] at hu
          subst hu
          rfl
        · simp only [lenW, Tok.val.injEq] at h
          subst h
          rw [readByObj_lenObj] at hr
          exact absurd hr (by decide)
    simp only [strokeWords]
    exact good_append _ _ (good_append _ _ (good_append _ _ (good_append _ _ hpre hcap) hjoin) hmiter) hdash

theorem endLine_tok : ∀ (ws : List Word), (endLine ws).map (·.tok) = ws.map (·.tok)
  | [] => rfl
  | [_] => rfl
  | w :: u :: rest => by
    have ih := endLine_tok (u :: rest)
    show (w :: endLine (u :: rest)).map (·.tok) = (w :: u :: rest).map (·.tok)
    rw [List.map_cons, ih]
    rfl

theorem endLine_last (ws : List Word) : (endLine ws).getLast?.map (·.tok) = ws.getLast?.map (·.tok) := by
  rw [← List.getLast?_map, ← List.getLast?_map, endLine_tok]

theorem good_endLine (ws : List Word) (h : Good ws) : Good (endLine ws) := by
  refine ⟨by rw [endLine_tok]; exact h.1, fun w hw => ?_⟩
  have := endLine_last ws
  rw [hw] at this
  cases hl : ws.getLast? with
  | none => simp [hl] at this
  | some v =>
    rw [hl] at this
    simp only [Option.map_some, Option.some.injEq] at this
    obtain ⟨n, hn⟩ := h.2 v hl
    exact ⟨n, this.trans hn⟩

theorem good_paintWords (fl : Option Pdf.PaintFill) (st : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp) :
    Good (paintWords fl st segs) := by
  simp only [paintWords]
  refine good_append _ _ (good_append _ _ (good_append _ _ (good_append _ _ (good_opW _ (by opspelled))
    (good_fillWords fl)) (good_strokeWords st)) (good_flatMap _ good_pathWords _)) ?_
  refine good_free' _ ?_ (by simp) (by simp [opW, Word.nl])
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact opW_ok _ (paintOp_spelled fl st)
  · exact nl_ok (opW_ok _ (by opspelled))

theorem good_headerWords (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    Good (endLine (headerWords m clips)) := by
  apply good_endLine
  have hok := headerWords_ok m clips
  simp only [headerWords] at hok ⊢
  rw [← List.singleton_append]
  refine good_append _ _ (good_opW _ (by opspelled)) (good_append _ _ ?_ ?_)
  · cases m with
    | none => exact good_nil
    | some mm =>
      exact good_free' _ (fun w hw => hok w (List.mem_cons_of_mem _ (List.mem_append_left _ hw)))
        (by simp [cmWords]) (by simp [cmWords, opW])
  · refine good_flatMap _ (fun c => ?_) _
    simp only [clipWords]
    refine good_append _ _ (good_flatMap _ good_pathWords _) ?_
    obtain ⟨_, rule⟩ := c
    cases rule
    · exact good_append _ _ (good_opW _ (by opspelled)) (good_opW _ (by opspelled))
    · exact good_append _ _ (good_opW _ (by opspelled)) (good_opW _ (by opspelled))

mutual

theorem good_opWords : ∀ (o : Pdf.ContentOp), Good (opWords o)
  | .paint fl st _ segs => by rw [opWords]; exact good_paintWords fl st segs
  | .group m _ clips body => by
    rw [opWords_group]
    refine good_append _ _ (good_append _ _ (good_headerWords m clips) (good_opWordsList body.toList)) ?_
    refine good_free' _ ?_ (by simp) (by simp [opW, Word.nl])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro w rfl
    exact nl_ok (opW_ok _ (by opspelled))
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => by rw [opWords]; exact good_nil

theorem good_opWordsList : ∀ (l : List Pdf.ContentOp), Good (opWordsList l)
  | [] => good_nil
  | o :: rest => by rw [opWordsList_cons]; exact good_append _ _ (good_opWords o) (good_opWordsList rest)

end

theorem opWords_last (o : Pdf.ContentOp) (h : opPlain o = true) :
    ∃ w, (opWords o).getLast? = some w ∧ w.sep = 10 := by
  cases o with
  | paint fl st gs segs =>
    refine ⟨(opW "Q").nl, ?_, rfl⟩
    rw [opWords, paintWords, List.getLast?_append]
    simp
  | group m gs clips body =>
    refine ⟨(opW "Q").nl, ?_, rfl⟩
    rw [opWords_group, List.getLast?_append]
    simp
  | fill | text | image | imageMissing | marked | shade | outline | xobject => simp [opPlain] at h

theorem opWordsList_last : ∀ (l : List Pdf.ContentOp), opsPlain l = true → l ≠ [] →
    ∃ w, (opWordsList l).getLast? = some w ∧ w.sep = 10
  | [], _, hne => absurd rfl hne
  | [o], h, _ => by
    simp only [opsPlain, Bool.and_eq_true] at h
    rw [opWordsList_cons, opWordsList_nil, List.append_nil]
    exact opWords_last o h.1
  | o :: u :: rest, h, _ => by
    simp only [opsPlain, Bool.and_eq_true] at h
    obtain ⟨w, hw, hs⟩ := opWordsList_last (u :: rest) (by simp only [opsPlain, Bool.and_eq_true]; exact h.2)
      (by simp)
    refine ⟨w, ?_, hs⟩
    rw [opWordsList_cons, List.getLast?_append, hw]
    rfl

theorem bytes_cancel (A B : ByteArray) (w : UInt8) (h : A ++ ⟨#[w]⟩ = B ++ ⟨#[w]⟩) : A = B := by
  have h1 := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [ByteArray.data_append, Array.toList_append] at h1
  have h2 := List.append_cancel_right h1
  apply ByteArray.ext
  exact Array.toList_inj.mp h2

theorem render_bytes (ops : Array Pdf.ContentOp) (h : opsPlain ops.toList = true) :
    (Pdf.render ops).toUTF8 = PdfContentLex.renderSep false ((opWordsList ops.toList).map fun w => (w.tok, w.sep)) := by
  by_cases he : ops.toList = []
  · have he' : ops = #[] := Array.toList_inj.mp he
    subst he'
    rw [show Pdf.render #[] = "" from rfl]
    have e : opWordsList (#[] : Array Pdf.ContentOp).toList = [] := rfl
    rw [e, List.map_nil, String.toUTF8_eq_toByteArray, String.toByteArray_empty]
    rfl
  · obtain ⟨w, hw, hs⟩ := opWordsList_last ops.toList h he
    have hne : (opWordsList ops.toList).map (fun w => (w.tok, w.sep)) ≠ [] := by
      intro hn
      rw [List.map_eq_nil_iff] at hn
      rw [hn] at hw
      simp at hw
    have hlast : (((opWordsList ops.toList).map fun w => (w.tok, w.sep)).getLast hne).2 = 10 := by
      have := List.getLast?_map (f := fun w : Word => (w.tok, w.sep)) (l := opWordsList ops.toList)
      rw [hw, Option.map_some, List.getLast?_eq_some_getLast hne] at this
      simp only [Option.some.injEq] at this
      rw [this]
      exact hs
    have hc := render_nl_chars ops he
    rw [ops_chars ops.toList h] at hc
    have hb : (Pdf.render ops ++ "\n").toUTF8 = (wordsChars (opWordsList ops.toList)).utf8Encode := by
      rw [toUTF8_chars, hc]
    rw [words_bytes _ (opWordsList_ok ops.toList), PdfContentLex.renderSep_true _ hne, hlast] at hb
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_append] at hb
    have hnl : "\n".toByteArray = ⟨#[10]⟩ := rfl
    rw [hnl, ← String.toUTF8_eq_toByteArray] at hb
    exact bytes_cancel _ _ _ hb

theorem scan_render (ops : Array Pdf.ContentOp) (h : opsPlain ops.toList = true) :
    PdfContentLex.scan (Pdf.render ops).toUTF8 = ((opWordsList ops.toList).map (·.tok)).toArray := by
  rw [render_bytes ops h, PdfContentLex.scan_renderSep_exact]
  · simp
  · have := (good_opWordsList ops.toList).1
    rw [List.map_map]
    exact this
  · intro t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    rcases (opWordsList_ok ops.toList w hw).sep with h | h <;> simp [h] <;> decide

theorem tokStep_val (cx : Ctx) (e : Entered) (st : St) (o : Obj) :
    tokStep cx e st (.val o) = { st with ops := st.ops.push o } := rfl

theorem tokStep_op (cx : Ctx) (e : Entered) (st : St) (n : String) :
    tokStep cx e st (.op n) = { stepOp cx e n st with ops := #[] } := rfl

theorem stepOp_rest (cx : Ctx) (e : Entered) (st : St) (n : String) (hq : n ≠ "q") (hQ : n ≠ "Q") :
    stepOp cx e n st = { stepRest cx e n st with saved := st.saved, level := st.level } := by
  rw [stepOp]
  have h1 : (n == "q") = false := by simpa using hq
  have h2 : (n == "Q") = false := by simpa using hQ
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

theorem stepOp_q (cx : Ctx) (e : Entered) (st : St) :
    stepOp cx e "q" st = { st with saved := st.saved.push (st.gs, st.frames.size), level := st.frames.size } := by
  rw [stepOp]
  simp

theorem stepOp_Q (cx : Ctx) (e : Entered) (st : St) (g : GState) (k : Nat)
    (h : st.saved.back? = some (g, k)) :
    stepOp cx e "Q" st = { st with gs := g, saved := st.saved.pop, frames := closeTo st.frames k, level := (st.saved.pop.back?.map (·.2)).getD 1 } := by
  rw [stepOp]
  simp [h]

/-- The operands as lengths. -/
def lenAt (st : St) (i : Nat) : Length := (st.ops.filterMap Obj.len?)[i]?.getD 0

/-- The operands as numbers. -/
def numAt (st : St) (i : Nat) : Rat := (st.ops.filterMap ratOf)[i]?.getD 0

theorem stepRest_l (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "l" st = { st with path := st.path.push (.lineTo (lenAt st 0) (lenAt st 1)), cur := (lenAt st 0, lenAt st 1) } := by
  rw [stepRest]; rfl

theorem stepRest_c (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "c" st = { st with path := st.path.push (.curveTo (lenAt st 0) (lenAt st 1) (lenAt st 2)
      (lenAt st 3) (lenAt st 4) (lenAt st 5)), cur := (lenAt st 4, lenAt st 5) } := by
  rw [stepRest]; rfl

theorem stepRest_m (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "m" st = st.moveTo (lenAt st 0, lenAt st 1) := by
  rw [stepRest]; rfl

theorem stepRest_h (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "h" st = { st with path := st.path.push .close, cur := st.start } := by
  rw [stepRest]

theorem stepRest_re (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "re" st = { st with path := st.path.push (.rect (lenAt st 0) (lenAt st 1) (lenAt st 2) (lenAt st 3)), cur := (lenAt st 0, lenAt st 1), start := (lenAt st 0, lenAt st 1) } := by
  rw [stepRest]; rfl

theorem stepRest_w (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "w" st = { st with gs := { st.gs with width := lenAt st 0 } } := by
  rw [stepRest]; rfl

theorem stepRest_J (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "J" st = { st with gs := { st.gs with
      cap := if numAt st 0 == 1 then .round else if numAt st 0 == 2 then .square else .butt } } := by
  rw [stepRest]; rfl

theorem stepRest_j (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "j" st = { st with gs := { st.gs with
      join := if numAt st 0 == 1 then .round else if numAt st 0 == 2 then .bevel else .miter } } := by
  rw [stepRest]; rfl

theorem stepRest_M (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "M" st = { st with gs := { st.gs with miter := numAt st 0 } } := by
  rw [stepRest]; rfl

theorem stepRest_d (cx : Ctx) (e : Entered) (st : St) (ds : Array Obj) (h : st.ops[0]? = some (.arr ds)) :
    stepRest cx e "d" st = { st with gs := { st.gs with dash := ds.filterMap Obj.len?, phase := (st.ops[1]?.bind Obj.len?).getD 0 } } := by
  rw [stepRest]
  simp only [St.op, h]

theorem stepRest_rg (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "rg" st = { st with gs := { st.gs with fillSpace := .rgb, fill := .color (deviceColor .rgb st.ops) } } := by
  rw [stepRest]
  simp

theorem stepRest_RG (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "RG" st = { st with gs := { st.gs with strokeSpace := .rgb, stroke := .color (deviceColor .rgb st.ops) } } := by
  rw [stepRest]
  simp

theorem stepRest_W (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "W" st = { st with clip := some .nonzero } := by
  rw [stepRest]

theorem stepRest_Wstar (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "W*" st = { st with clip := some .evenOdd } := by
  rw [stepRest]

theorem stepRest_n (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "n" st = paintPath cx st none false false := by
  rw [stepRest]

theorem stepRest_S (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "S" st = paintPath cx st none true false := by
  rw [stepRest]

theorem stepRest_f (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "f" st = paintWith cx e st (some .nonzero) false false := by
  rw [stepRest]

theorem stepRest_fstar (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "f*" st = paintWith cx e st (some .evenOdd) false false := by
  rw [stepRest]

theorem stepRest_B (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "B" st = paintWith cx e st (some .nonzero) true false := by
  rw [stepRest]

theorem stepRest_Bstar (cx : Ctx) (e : Entered) (st : St) :
    stepRest cx e "B*" st = paintWith cx e st (some .evenOdd) true false := by
  rw [stepRest]

theorem stepRest_cm (cx : Ctx) (e : Entered) (st : St) (m : Affine)
    (h : affineOf (st.ops.filterMap ratOf) = some m) :
    stepRest cx e "cm" st = st.concat m := by
  rw [stepRest]
  simp only [St.nums, h]

/-- A path operator as the importer reads it back, its lengths on the milli-point grid. -/
@[expose] public def pathRead : Pdf.PathOp → Pdf.PathOp
  | .moveTo x y => .moveTo (qLen x) (qLen y)
  | .lineTo x y => .lineTo (qLen x) (qLen y)
  | .curveTo a b c d e f => .curveTo (qLen a) (qLen b) (qLen c) (qLen d) (qLen e) (qLen f)
  | .close => .close
  | .rect x y w h => .rect (qLen x) (qLen y) (qLen w) (qLen h)

/-- Tokens read from `st` on. -/
def run (cx : Ctx) (e : Entered) (st : St) (ws : List Word) : St :=
  (ws.map (·.tok)).foldl (tokStep cx e) st

theorem run_append (cx : Ctx) (e : Entered) (st : St) (a b : List Word) :
    run cx e st (a ++ b) = run cx e (run cx e st a) b := by
  simp [run, List.foldl_append]

theorem run_nil (cx : Ctx) (e : Entered) (st : St) : run cx e st [] = st := rfl

theorem run_pathWords (cx : Ctx) (e : Entered) (st : St) (p : Pdf.PathOp) (hops : st.ops = #[]) :
    ∃ c s, run cx e st (pathWords p) = { st with path := st.path.push (pathRead p), cur := c, start := s } := by
  cases p with
  | moveTo x y =>
    refine ⟨(qLen x, qLen y), (qLen x, qLen y), ?_⟩
    simp only [run, pathWords, lenW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      tokStep_val, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_m]
    simp [hops, St.moveTo, lenAt, len?_lenObj, pathRead]
  | lineTo x y =>
    refine ⟨(qLen x, qLen y), st.start, ?_⟩
    simp only [run, pathWords, lenW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      tokStep_val, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_l]
    simp [hops, lenAt, len?_lenObj, pathRead]
  | curveTo a b c d f g =>
    refine ⟨(qLen f, qLen g), st.start, ?_⟩
    simp only [run, pathWords, lenW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      tokStep_val, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_c]
    simp [hops, lenAt, len?_lenObj, pathRead]
  | close =>
    refine ⟨st.start, st.start, ?_⟩
    simp only [run, pathWords, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_h]
    simp [hops, pathRead]
  | rect x y w h =>
    refine ⟨(qLen x, qLen y), (qLen x, qLen y), ?_⟩
    simp only [run, pathWords, lenW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      tokStep_val, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_re]
    simp [hops, lenAt, len?_lenObj, pathRead]

theorem run_colorWords_op (cx : Ctx) (e : Entered) (st : St) (c : Ir.Color) (n : String)
    (hq : n ≠ "q") (hQ : n ≠ "Q") (hops : st.ops = #[]) :
    run cx e st (colorWords c ++ [opW n]) =
      { stepRest cx e n { st with ops := #[milliObj (Ir.Color.milli c.r), milliObj (Ir.Color.milli c.g),
          milliObj (Ir.Color.milli c.b)] } with saved := st.saved, level := st.level, ops := #[] } := by
  simp only [run, colorWords, milliW, opW, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, tokStep_val, tokStep_op]
  rw [stepOp_rest _ _ _ _ hq hQ]
  simp [hops]

theorem run_fillWords (cx : Ctx) (e : Entered) (st : St) (f : Pdf.PaintFill) (hops : st.ops = #[]) :
    run cx e st (fillWords (some f)) =
      { st with gs := { st.gs with fillSpace := .rgb, fill := .color (colorRead (paintColor f.paint)) } } := by
  rw [fillWords, run_colorWords_op _ _ _ _ _ (by decide) (by decide) hops, stepRest_rg, deviceColor_milli]
  simp [hops]

/-- The graphics state a stroke's words leave: its colour, its width, and
what it states of caps, joins, the miter limit and the dash. -/
def strokeGs (g : GState) (k : Pdf.PaintStroke) : GState :=
  { g with
    strokeSpace := .rgb
    stroke := .color (colorRead (paintColor k.paint))
    width := qLen k.width
    cap := k.cap.getD g.cap
    join := k.join.getD g.join
    miter := (k.miter.map fun r => ratRead r.num r.den).getD g.miter
    dash := (k.dash.map fun dp => dp.1.map qLen).getD g.dash
    phase := (k.dash.map fun dp => qLen dp.2).getD g.phase }

theorem ratOf_nat (n : Nat) : ratOf (.int (n : Int)) = some (n : Rat) := by
  rw [ratOf_eq, numRat_int]
  have : ¬ ((n : Int) < 0) := by omega
  rw [ite_eq_right this, Int.natAbs_natCast, Rat.mkRat_one]
  rfl

theorem numAt_int (st : St) (n : Nat) (h : st.ops = #[.int n]) : numAt st 0 = (n : Rat) := by
  simp [numAt, h, ratOf_nat]

theorem cap_decode (c : Cap) :
    (if ((capNum c : Nat) : Rat) == 1 then Cap.round else if ((capNum c : Nat) : Rat) == 2 then .square else .butt) = c := by
  cases c <;> decide

theorem join_decode (j : Join) :
    (if ((joinNum j : Nat) : Rat) == 1 then Join.round else if ((joinNum j : Nat) : Rat) == 2 then .bevel else .miter) = j := by
  cases j <;> decide

theorem run_one (cx : Ctx) (e : Entered) (st : St) (o : Obj) (n : String) (hq : n ≠ "q") (hQ : n ≠ "Q")
    (hops : st.ops = #[]) (w₁ w₂ : Word) (h₁ : w₁.tok = .val o) (h₂ : w₂.tok = .op n) :
    run cx e st [w₁, w₂] = { stepRest cx e n { st with ops := #[o] } with saved := st.saved, level := st.level, ops := #[] } := by
  simp only [run, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, h₁, h₂, tokStep_val, tokStep_op]
  rw [stepOp_rest _ _ _ _ hq hQ]
  simp [hops]

theorem run_width (cx : Ctx) (e : Entered) (st : St) (w : Length) (hops : st.ops = #[]) :
    run cx e st [lenW w, opW "w"] = { st with gs := { st.gs with width := qLen w } } := by
  rw [run_one cx e st (lenObj w) "w" (by decide) (by decide) hops _ _ rfl rfl, stepRest_w]
  simp [lenAt, len?_lenObj, hops]

theorem run_capWords (cx : Ctx) (e : Entered) (st : St) (c : Option Cap) (hops : st.ops = #[]) :
    run cx e st (capWords c) = { st with gs := { st.gs with cap := c.getD st.gs.cap } } := by
  cases c with
  | none => simp [capWords, run_nil]
  | some c =>
    rw [capWords, run_one cx e st (.int (capNum c)) "J" (by decide) (by decide) hops _ _ rfl rfl, stepRest_J,
      numAt_int _ _ rfl, cap_decode]
    simp [hops]

theorem run_joinWords (cx : Ctx) (e : Entered) (st : St) (j : Option Join) (hops : st.ops = #[]) :
    run cx e st (joinWords j) = { st with gs := { st.gs with join := j.getD st.gs.join } } := by
  cases j with
  | none => simp [joinWords, run_nil]
  | some j =>
    rw [joinWords, run_one cx e st (.int (joinNum j)) "j" (by decide) (by decide) hops _ _ rfl rfl, stepRest_j,
      numAt_int _ _ rfl, join_decode]
    simp [hops]

theorem run_miterWords (cx : Ctx) (e : Entered) (st : St) (m : Option Rat) (hops : st.ops = #[]) :
    run cx e st (miterWords m) =
      { st with gs := { st.gs with miter := (m.map fun r => ratRead r.num r.den).getD st.gs.miter } } := by
  cases m with
  | none => simp [miterWords, run_nil]
  | some r =>
    rw [miterWords, run_one cx e st (ratObj r.num r.den) "M" (by decide) (by decide) hops _ _ (ratW_tok _ _) rfl,
      stepRest_M]
    simp [hops, numAt, ratOf_ratObj]

theorem run_dashWords (cx : Ctx) (e : Entered) (st : St) (dp : Option (Array Length × Length)) (hops : st.ops = #[]) :
    run cx e st (dashWords dp) =
      { st with gs := { st.gs with
          dash := (dp.map fun dp => dp.1.map qLen).getD st.gs.dash
          phase := (dp.map fun dp => qLen dp.2).getD st.gs.phase } } := by
  cases dp with
  | none => simp [dashWords, run_nil]
  | some dp =>
    obtain ⟨d, p⟩ := dp
    simp only [run, dashWords, dashW, lenW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      tokStep_val, tokStep_op]
    rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_d _ _ _ (d.map lenObj) (by simp [hops])]
    have hf0 : (d.map lenObj).filterMap Obj.len? = d.map qLen := by
      rw [Array.filterMap_map]
      simp [Function.comp_def, len?_lenObj]
    have hf : Array.filterMap Obj.len? (Array.map lenObj d) 0 d.size = Array.map qLen d := by
      have e : d.size = (d.map lenObj).size := (Array.size_map ..).symm
      rw [e]
      exact hf0
    simp [hops, hf, len?_lenObj]

theorem run_strokeWords (cx : Ctx) (e : Entered) (st : St) (k : Pdf.PaintStroke) (hops : st.ops = #[]) :
    run cx e st (strokeWords (some k)) = { st with gs := strokeGs st.gs k } := by
  have es : strokeWords (some k) = (colorWords (paintColor k.paint) ++ [opW "RG"]) ++ [lenW k.width, opW "w"] ++
      capWords k.cap ++ joinWords k.join ++ miterWords k.miter ++ dashWords k.dash := by
    simp [strokeWords]
  rw [es, run_append, run_append, run_append, run_append, run_append,
    run_colorWords_op _ _ _ _ _ (by decide) (by decide) hops, stepRest_RG, deviceColor_milli]
  rw [run_width _ _ _ _ (by simp), run_capWords _ _ _ _ (by simp), run_joinWords _ _ _ _ (by simp),
    run_miterWords _ _ _ _ (by simp), run_dashWords _ _ _ _ (by simp)]
  simp [strokeGs, hops]

/-- The geometry the importer gives a path (`St.geom`). -/
def stGeom (path : Array Pdf.PathOp) : Geom :=
  match GfxPdf.geomOf path.toList with
  | .rect x y w h => if w < 0 || h < 0 then .path #[Kit.rectPath x y w h] else .rect x y w h
  | .ellipse cx cy rx ry => .ellipse cx cy rx ry
  | .path subs => .path subs

theorem st_geom (st : St) : st.geom = stGeom st.path := rfl

def inkColor : Ink → Ir.Color
  | .color c => c
  | .pattern _ _ => Ir.Color.black

def fillOf (g : GState) (r : Rule) : Fill := { paint := .solid (inkColor g.fill), rule := r, alpha := g.fillAlpha }

def strokeOf (g : GState) : Stroke :=
  { paint := .solid (inkColor g.stroke), width := g.width, cap := g.cap, join := g.join, miterLimit := g.miter
    dash := Kit.normDash g.dash, phase := g.phase, alpha := g.strokeAlpha }

/-- A frame's kids, one node more. -/
def St.pushKid (st : St) (n : Node Run) : St :=
  match st.frames.back? with
  | some top => { st with frames := st.frames.pop.push { top with kids := top.kids.push n } }
  | none => st

@[simp] theorem pushKid_clip (st : St) (n : Node Run) : (st.pushKid n).clip = st.clip := by
  unfold St.pushKid; split <;> rfl

@[simp] theorem pushKid_path (st : St) (n : Node Run) : (st.pushKid n).path = st.path := by
  unfold St.pushKid; split <;> rfl

@[simp] theorem pushKid_gs (st : St) (n : Node Run) : (st.pushKid n).gs = st.gs := by
  unfold St.pushKid; split <;> rfl

theorem emit_plain (st : St) (n : Node Run) (hh : st.hidden = 0) (hm : st.gs.maskClip = none) :
    st.emit n = st.pushKid n := by
  unfold St.emit St.masked St.pushKid
  have hh' : ¬ st.hidden > 0 := by omega
  simp only [hh', ↓reduceIte, hm]
  cases n <;> (cases hb : st.frames.back? <;> simp)

theorem paintPath_plain (cx : Ctx) (st : St) (fill : Option Rule) (stroke : Bool)
    (hfill : fill.isSome → ∃ c, st.gs.fill = .color c) (hstroke : stroke = true → ∃ c, st.gs.stroke = .color c)
    (hpath : st.path ≠ #[]) (hpaint : fill.isSome ∨ stroke = true) (hclip : st.clip = none)
    (hh : st.hidden = 0) (hm : st.gs.maskClip = none) :
    paintPath cx st fill stroke false =
      { st.pushKid (.draw (stGeom st.path) (fill.map (fillOf st.gs)) (if stroke then some (strokeOf st.gs) else none)) with
        path := #[], clip := none } := by
  have hne : st.path.isEmpty = false := by simpa using hpath
  rcases fill with _ | r <;> cases stroke
  · simp at hpaint
  · obtain ⟨cs, hcs⟩ := hstroke rfl
    simp only [paintPath, paintOf, hcs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hne, 
      Option.isNone_some, Option.isNone_none, Bool.and_true, Bool.or_false, Option.bind_some,
      Option.map_some, Option.map_none, Option.bind_none, Bool.and_false]
    rw [emit_plain _ _ hh hm]
    simp [st_geom, strokeOf, inkColor, hcs, hclip]
  · obtain ⟨cf, hcf⟩ := hfill rfl
    simp only [paintPath, paintOf, hcf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hne, 
      Option.isNone_some, Option.isNone_none, Bool.and_true, Bool.or_false, Option.bind_some,
      Option.map_some, Option.bind_none]
    rw [emit_plain _ _ hh hm]
    simp [st_geom, inkColor, hcf, fillOf, hclip]
  · obtain ⟨cf, hcf⟩ := hfill rfl
    obtain ⟨cs, hcs⟩ := hstroke rfl
    simp only [paintPath, paintOf, hcf, hcs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hne, 
      Option.isNone_some, Option.isNone_none, Bool.and_true, Bool.or_false, Option.bind_some,
      Option.map_some, Bool.and_false]
    rw [emit_plain _ _ hh hm]
    simp [st_geom, strokeOf, inkColor, hcf, hcs, fillOf, hclip]

theorem closeTo_noop (fs : Array Open) (n : Nat) (h : fs.size ≤ max n 1) : closeTo fs n = fs := by
  unfold closeTo
  cases hk : fs.size with
  | zero =>
    have : fs = #[] := Array.eq_empty_of_size_eq_zero hk
    subst this
    simp
  | succ k =>
    apply Loop.forIn_range_stops_exact (n := 1) _ _ (by omega)
    apply Loop.Stops.done
    rw [ite_eq_left h]
    rfl

theorem closeTo_one (F : Array Open) (T G : Open) :
    closeTo ((F.push T).push G) (F.size + 1) = F.push (closeInto T G) := by
  unfold closeTo
  apply Loop.forIn_range_stops_exact (n := 2) _ _ (by simp)
  apply Loop.Stops.yield (b := F.push (closeInto T G))
  · have h : ¬ (((F.push T).push G).size ≤ max (F.size + 1) 1) := by simp
    rw [ite_eq_right h]
    simp
  · apply Loop.Stops.done
    have h : (F.push (closeInto T G)).size ≤ max (F.size + 1) 1 := by simp
    rw [ite_eq_left h]
    rfl

/-- The importer's state between covered operations: PDF's initial
graphics state under the current matrix, no path, no pending clip, no
operands, nothing hidden, the level the stack's top saw. -/
structure Calm (st : St) : Prop where
  gs : st.gs = GState.initial st.gs.ctm
  path : st.path = #[]
  clip : st.clip = none
  ops : st.ops = #[]
  hidden : st.hidden = 0
  level : st.level = (st.saved.back?.map (·.2)).getD 1

theorem run_paths (cx : Ctx) (e : Entered) : ∀ (l : List Pdf.PathOp) (st : St), st.ops = #[] →
    ∃ c s, run cx e st (l.flatMap pathWords) = { st with path := st.path ++ (l.map pathRead).toArray, cur := c, start := s }
  | [], st, _ => ⟨st.cur, st.start, by simp [run_nil]⟩
  | p :: rest, st, hops => by
    obtain ⟨c, s, h⟩ := run_pathWords cx e st p hops
    rw [List.flatMap_cons, run_append, h]
    obtain ⟨c', s', h'⟩ := run_paths cx e rest { st with path := st.path.push (pathRead p), cur := c, start := s } hops
    refine ⟨c', s', ?_⟩
    rw [h']
    have hp : (st.path.push (pathRead p)) ++ (rest.map pathRead).toArray = st.path ++ ((p :: rest).map pathRead).toArray := by
      apply Array.toList_inj.mp
      simp
    rw [hp]

theorem run_q (cx : Ctx) (e : Entered) (st : St) (hops : st.ops = #[]) :
    run cx e st [opW "q"] = { st with saved := st.saved.push (st.gs, st.frames.size), level := st.frames.size } := by
  simp only [run, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op, stepOp_q]
  simp [hops]

theorem run_Q (cx : Ctx) (e : Entered) (st : St) (g : GState) (k : Nat) (hops : st.ops = #[])
    (h : st.saved.back? = some (g, k)) :
    run cx e st [(opW "Q").nl] = { st with gs := g, saved := st.saved.pop, frames := closeTo st.frames k, level := (st.saved.pop.back?.map (·.2)).getD 1 } := by
  simp only [run, opW, Word.nl, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op,
    stepOp_Q cx e st g k h]
  simp [hops]

/-- A fill as the importer reads a covered one back: its colour's bytes,
its rule, opaque. -/
def fillRead (f : Pdf.PaintFill) : Fill :=
  { paint := .solid (colorRead (paintColor f.paint)), rule := if f.evenOdd then .evenOdd else .nonzero
    alpha := Alpha.opaque }

/-- A stroke as the importer reads a covered one back: what it states, on
the print grid, and PDF's initial state for what it leaves unstated. -/
def strokeRead (k : Pdf.PaintStroke) : Stroke :=
  { paint := .solid (colorRead (paintColor k.paint)), width := qLen k.width, cap := k.cap.getD .butt
    join := k.join.getD .miter, miterLimit := (k.miter.map fun r => ratRead r.num r.den).getD 10
    dash := Kit.normDash ((k.dash.map fun dp => dp.1.map qLen).getD #[])
    phase := (k.dash.map fun dp => qLen dp.2).getD 0, alpha := Alpha.opaque }

/-- The node the importer builds for a covered `paint`. -/
def drawRead (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp) :
    Node Run :=
  .draw (stGeom (segs.map pathRead)) (fl.map fillRead) (sk.map strokeRead)

theorem paintWith_color (cx : Ctx) (e : Entered) (st : St) (fill : Option Rule) (stroke close : Bool)
    (c : Ir.Color) (h : st.gs.fill = .color c) :
    paintWith cx e st fill stroke close = paintPath cx st fill stroke close := by
  rw [paintWith]
  simp [h]

theorem alpha_opaque : alphaProduct Alpha.opaque Alpha.opaque = Alpha.opaque := by decide

/-- The graphics state a covered `paint`'s state words leave. -/
def gsAfter (g : GState) (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke) : GState :=
  let g1 := match fl with
    | some f => { g with fillSpace := .rgb, fill := .color (colorRead (paintColor f.paint)) }
    | none => g
  match sk with
  | some k => strokeGs g1 k
  | none => g1

theorem run_states (cx : Ctx) (e : Entered) (st : St) (fl : Option Pdf.PaintFill)
    (sk : Option Pdf.PaintStroke) (hops : st.ops = #[]) :
    run cx e st (fillWords fl ++ strokeWords sk) = { st with gs := gsAfter st.gs fl sk } := by
  rw [run_append]
  cases fl with
  | none =>
    cases sk with
    | none => simp [fillWords, strokeWords, run_nil, gsAfter]
    | some k =>
      rw [show fillWords none = [] from rfl, run_nil, run_strokeWords _ _ _ _ hops]
      rfl
  | some f =>
    rw [run_fillWords _ _ _ _ hops]
    cases sk with
    | none => simp [strokeWords, run_nil, gsAfter]
    | some k =>
      rw [run_strokeWords _ _ _ _ (by simp [hops])]
      rfl

def ruleOf (f : Pdf.PaintFill) : Rule := if f.evenOdd then .evenOdd else .nonzero

theorem run_paintOp (cx : Ctx) (e : Entered) (st : St) (fl : Option Pdf.PaintFill)
    (sk : Option Pdf.PaintStroke) (hfs : fl.isSome ∨ sk.isSome)
    (hcol : fl.isSome → ∃ c, st.gs.fill = .color c) :
    run cx e st [opW (Pdf.paintOp fl sk)] =
      { paintPath cx st (fl.map ruleOf) sk.isSome false with saved := st.saved, level := st.level, ops := #[] } := by
  simp only [run, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op]
  rcases fl with _ | ⟨fp, eo⟩ <;> rcases sk with _ | k
  · simp at hfs
  · rw [show Pdf.paintOp none (some k) = "S" from rfl, stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_S]
    rfl
  · obtain ⟨c, hc⟩ := hcol rfl
    cases eo
    · rw [show Pdf.paintOp (some ⟨fp, false⟩) none = "f" from rfl, stepOp_rest _ _ _ _ (by decide) (by decide),
        stepRest_f, paintWith_color _ _ _ _ _ _ c hc]
      rfl
    · rw [show Pdf.paintOp (some ⟨fp, true⟩) none = "f*" from rfl, stepOp_rest _ _ _ _ (by decide) (by decide),
        stepRest_fstar, paintWith_color _ _ _ _ _ _ c hc]
      rfl
  · obtain ⟨c, hc⟩ := hcol rfl
    cases eo
    · rw [show Pdf.paintOp (some ⟨fp, false⟩) (some k) = "B" from rfl, stepOp_rest _ _ _ _ (by decide) (by decide),
        stepRest_B, paintWith_color _ _ _ _ _ _ c hc]
      rfl
    · rw [show Pdf.paintOp (some ⟨fp, true⟩) (some k) = "B*" from rfl, stepOp_rest _ _ _ _ (by decide) (by decide),
        stepRest_Bstar, paintWith_color _ _ _ _ _ _ c hc]
      rfl

theorem gsAfter_fill (g : GState) (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke) (f : Pdf.PaintFill)
    (h : fl = some f) : (gsAfter g fl sk).fill = .color (colorRead (paintColor f.paint)) := by
  subst h
  cases sk <;> rfl

theorem draw_read (g : GState) (hg : g = GState.initial g.ctm) (fl : Option Pdf.PaintFill)
    (sk : Option Pdf.PaintStroke) (segs : Array Pdf.PathOp) :
    Node.draw (stGeom (#[] ++ (segs.toList.map pathRead).toArray))
        ((fl.map ruleOf).map (fillOf (gsAfter g fl sk)))
        (if sk.isSome then some (strokeOf (gsAfter g fl sk)) else none) =
      drawRead fl sk segs := by
  have hp : (#[] : Array Pdf.PathOp) ++ (segs.toList.map pathRead).toArray = segs.map pathRead := by
    apply Array.toList_inj.mp; simp
  rw [hp, drawRead]
  rw [hg]
  rcases fl with _ | f <;> rcases sk with _ | k <;>
    simp [gsAfter, fillOf, strokeOf, fillRead, strokeRead, ruleOf, inkColor, strokeGs, GState.initial,
      GState.fillAlpha, GState.strokeAlpha, alpha_opaque]

theorem pushKid_back (st : St) (T : Open) (h : st.frames.back? = some T) (n : Node Run) :
    st.pushKid n = { st with frames := st.frames.pop.push { T with kids := T.kids.push n } } := by
  unfold St.pushKid
  rw [h]

theorem gsAfter_mask (g : GState) (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke) :
    (gsAfter g fl sk).maskClip = g.maskClip := by
  rcases fl with _ | f <;> rcases sk with _ | k <;> rfl

theorem gsAfter_stroke (g : GState) (fl : Option Pdf.PaintFill) (k : Pdf.PaintStroke) :
    (gsAfter g fl (some k)).stroke = .color (colorRead (paintColor k.paint)) := by
  rcases fl with _ | f <;> rfl

theorem pop_push_size (fs : Array Open) (T : Open) (h : fs.back? = some T) (x : Open) :
    (fs.pop.push x).size = fs.size := by
  have : 0 < fs.size := by
    rcases fs with ⟨l⟩
    cases l with
    | nil => simp [Array.back?] at h
    | cons a l => simp
  simp
  omega

theorem run_paint (cx : Ctx) (e : Entered) (st : St) (hc : Calm st) (T : Open)
    (hT : st.frames.back? = some T) (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke)
    (segs : Array Pdf.PathOp) (hfs : fl.isSome ∨ sk.isSome) (hsegs : segs ≠ #[]) :
    ∃ c s, run cx e st (paintWords fl sk segs) =
      { st with frames := st.frames.pop.push { T with kids := T.kids.push (drawRead fl sk segs) }, cur := c, start := s } := by
  obtain ⟨hgs, hpath0, hclip0, hops0, hhid0, hlev0⟩ := hc
  obtain ⟨gs, saved, level, frames, path, cur, start, clip, tm, tlm, inText, words, ops, hidden, marks,
    compat, store⟩ := st
  simp only at hgs hpath0 hclip0 hops0 hhid0 hlev0 hT ⊢
  subst hpath0 hclip0 hops0 hhid0
  have e1 : paintWords fl sk segs = ([opW "q"] ++ (fillWords fl ++ strokeWords sk)) ++
      segs.toList.flatMap pathWords ++ [opW (Pdf.paintOp fl sk)] ++ [(opW "Q").nl] := by
    simp [paintWords]
  rw [e1, run_append, run_append, run_append, run_append, run_q _ _ _ rfl, run_states _ _ _ _ _ rfl]
  obtain ⟨c, s, hpath⟩ := run_paths cx e segs.toList _ (rfl : (⟨gsAfter gs fl sk, saved.push (gs, frames.size),
    frames.size, frames, #[], cur, start, none, tm, tlm, inText, words, #[], 0, marks, compat, store⟩ : St).ops = #[])
  refine ⟨c, s, ?_⟩
  simp only at hpath ⊢
  rw [hpath]
  have hcol : fl.isSome → ∃ c, (gsAfter gs fl sk).fill = .color c := by
    intro hf
    obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.mp hf
    exact ⟨_, gsAfter_fill gs (some f) sk f rfl⟩
  rw [run_paintOp _ _ _ _ _ hfs hcol]
  have hne : (#[] : Array Pdf.PathOp) ++ (segs.toList.map pathRead).toArray ≠ #[] := by
    intro h
    apply hsegs
    apply Array.toList_inj.mp
    have := congrArg Array.toList h
    simpa using this
  rw [paintPath_plain _ _ _ _ (fun hf => by
      obtain ⟨f, hf'⟩ := Option.isSome_iff_exists.mp (by simpa using hf)
      exact hcol (by simp [hf']))
    (fun hs => ?_) hne (by simpa [Option.isSome_map] using hfs) rfl rfl ?_]
  · simp only []
    rw [pushKid_back _ T hT, run_Q _ _ _ gs frames.size rfl (by simp)]
    simp only []
    rw [closeTo_noop _ _ (by rw [pop_push_size _ T hT]; omega), draw_read gs hgs fl sk segs]
    simp [hlev0]
  · show (gsAfter gs fl sk).maskClip = none
    rw [gsAfter_mask, hgs]
    rfl
  · obtain ⟨k, rfl⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨_, gsAfter_stroke gs fl k⟩

theorem run_endLine (cx : Ctx) (e : Entered) (st : St) (ws : List Word) :
    run cx e st (endLine ws) = run cx e st ws := by
  simp only [run, endLine_tok]

theorem concat_push (st : St) (m : Affine) (hm : m ≠ Affine.unit) (T : Open) (hT : st.frames.back? = some T)
    (hl : st.level = st.frames.size) :
    st.concat m = { st with
      gs := { st.gs with ctm := st.gs.ctm.compose m }
      frames := st.frames.push { xf := m, clips := #[], alpha := Alpha.opaque, kids := #[] } } := by
  unfold St.concat
  rw [ite_eq_right hm, hT]
  have : ¬ (st.frames.size > st.levelBase) := by simp [St.levelBase, hl]
  simp [this]

theorem addClip_push (st : St) (c : Clip) (T : Open) (hT : st.frames.back? = some T)
    (hl : st.level = st.frames.size) :
    st.addClip c = { st with frames := st.frames.push { xf := Affine.unit, clips := #[c], alpha := Alpha.opaque, kids := #[] } } := by
  unfold St.addClip
  rw [hT]
  have : ¬ (st.frames.size > st.levelBase) := by simp [St.levelBase, hl]
  simp [this]

theorem addClip_fold (st : St) (c : Clip) (G : Open) (hG : st.frames.back? = some G) (hk : G.kids = #[])
    (hl : st.frames.size > st.level) :
    st.addClip c = { st with frames := st.frames.pop.push { G with clips := G.clips.push c } } := by
  unfold St.addClip
  rw [hG]
  simp [St.levelBase, hl, hk]

theorem addClip_eq (st : St) (c : Clip) : st.addClip c = { st with frames := (st.addClip c).frames } := by
  unfold St.addClip
  split
  · split <;> rfl
  · rfl

theorem addClip_frames_congr (st st' : St) (c : Clip) (hf : st.frames = st'.frames) (hl : st.level = st'.level) :
    (st.addClip c).frames = (st'.addClip c).frames := by
  unfold St.addClip St.levelBase
  rw [hf, hl]
  split <;> (try split) <;> simp [hf]

theorem paintPath_clip (cx : Ctx) (st : St) (r : Rule) (hc : st.clip = some r) (hp : st.path ≠ #[]) :
    paintPath cx st none false false = { st.addClip { geom := stGeom st.path, rule := r } with path := #[], clip := none } := by
  have hne : st.path.isEmpty = false := by simpa using hp
  simp only [paintPath, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hne, hc, Option.isNone_none,
    Bool.and_self, Bool.or_true]
  rfl

theorem affineOf_cm (mm : Affine) :
    affineOf ((#[ratObj mm.a.num mm.a.den, ratObj mm.b.num mm.b.den, ratObj mm.c.num mm.c.den,
      ratObj mm.d.num mm.d.den, ratObj (bpPair mm.e).1 (bpPair mm.e).2,
      ratObj (bpPair mm.f).1 (bpPair mm.f).2] : Array Obj).filterMap ratOf) = some (readAffine mm) := by
  simp [affineOf, ratOf_ratObj, readAffine]

theorem run_cmWords (cx : Ctx) (e : Entered) (st : St) (mm : Affine) (hops : st.ops = #[])
    (hm : readAffine mm ≠ Affine.unit) (T : Open) (hT : st.frames.back? = some T) (hl : st.level = st.frames.size) :
    run cx e st (cmWords mm) = { st with
      gs := { st.gs with ctm := st.gs.ctm.compose (readAffine mm) }
      frames := st.frames.push { xf := readAffine mm, clips := #[], alpha := Alpha.opaque, kids := #[] } } := by
  simp only [run, cmWords, ratW, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_val,
    tokStep_op]
  have push6 : ∀ (a b c d e f : Obj),
      ((((((#[] : Array Obj).push a).push b).push c).push d).push e).push f = #[a, b, c, d, e, f] :=
    fun _ _ _ _ _ _ => rfl
  rw [stepOp_rest _ _ _ _ (by decide) (by decide), stepRest_cm _ _ _ (readAffine mm) (by simp only [hops, push6]; exact affineOf_cm mm),
    concat_push _ _ hm T (by simpa using hT) (by simpa using hl)]
  simp [hops]

/-- A clip as the importer reads a covered one back. -/
def clipRead (c : Array Pdf.PathOp × Rule) : Clip :=
  { geom := stGeom (c.1.map pathRead), rule := c.2 }

theorem run_clipWords (cx : Ctx) (e : Entered) (st : St) (c : Array Pdf.PathOp × Rule)
    (hops : st.ops = #[]) (hpath : st.path = #[]) (hclip : st.clip = none) (hne : c.1 ≠ #[]) :
    ∃ cu sa, run cx e st (clipWords c) =
      { st with frames := (st.addClip (clipRead c)).frames, cur := cu, start := sa } := by
  obtain ⟨segs, rule⟩ := c
  simp only at hne
  rw [clipWords, run_append]
  obtain ⟨cu, sa, hp⟩ := run_paths cx e segs.toList st hops
  refine ⟨cu, sa, ?_⟩
  rw [hp]
  have hpp : st.path ++ (segs.toList.map pathRead).toArray = segs.map pathRead := by
    rw [hpath]; apply Array.toList_inj.mp; simp
  have hpne : st.path ++ (segs.toList.map pathRead).toArray ≠ #[] := by
    rw [hpp]; intro h; apply hne; apply Array.toList_inj.mp; have := congrArg Array.toList h; simpa using this
  cases rule with
  | nonzero =>
    simp only [run, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op]
    rw [stepOp_rest _ _ _ "W" (by decide) (by decide), stepRest_W, stepOp_rest _ _ _ "n" (by decide) (by decide),
      stepRest_n]
    simp only []
    rw [paintPath_clip _ _ .nonzero rfl hpne, addClip_eq]
    simp only [hops, clipRead, hpp]
    rw [hpath, hclip]
    congr 1
    exact addClip_frames_congr _ _ _ rfl rfl
  | evenOdd =>
    simp only [run, opW, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, tokStep_op]
    rw [stepOp_rest _ _ _ "W*" (by decide) (by decide), stepRest_Wstar, stepOp_rest _ _ _ "n" (by decide) (by decide),
      stepRest_n]
    simp only []
    rw [paintPath_clip _ _ .evenOdd rfl hpne, addClip_eq]
    simp only [hops, clipRead, hpp]
    rw [hpath, hclip]
    congr 1
    exact addClip_frames_congr _ _ _ rfl rfl

/-- The state after a `q`. -/
def St.saveQ (st : St) : St := { st with saved := st.saved.push (st.gs, st.frames.size), level := st.frames.size }

theorem run_q' (cx : Ctx) (e : Entered) (st : St) (hops : st.ops = #[]) :
    run cx e st [opW "q"] = st.saveQ := run_q cx e st hops

theorem calm_saveQ (st : St) (hc : Calm st) : Calm st.saveQ :=
  ⟨hc.gs, hc.path, hc.clip, hc.ops, hc.hidden, by simp [St.saveQ]⟩

/-- A saved state's frame, as its header leaves it: its matrix read back,
its clips read back, nothing painted yet. -/
def hdr (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) : Open :=
  { xf := (m.map readAffine).getD Affine.unit, clips := clips.map clipRead, alpha := Alpha.opaque, kids := #[] }

/-- The graphics state after a header's matrix. -/
def ctmAfter (g : GState) : Option Affine → GState
  | some mm => { g with ctm := g.ctm.compose (readAffine mm) }
  | none => g

theorem run_clips_fold (cx : Ctx) (e : Entered) : ∀ (cs : List (Array Pdf.PathOp × Rule)) (st : St)
    (F : Array Open) (G : Open), st.ops = #[] → st.path = #[] → st.clip = none → st.frames = F.push G →
    G.kids = #[] → st.frames.size > st.level → (∀ c ∈ cs, c.1 ≠ #[]) →
    ∃ cu sa, run cx e st (cs.flatMap clipWords) =
      { st with frames := F.push { G with clips := G.clips ++ (cs.map clipRead).toArray }, cur := cu, start := sa }
  | [], st, F, G, _, _, _, hf, _, _, _ => by
    refine ⟨st.cur, st.start, ?_⟩
    have hG : { G with clips := G.clips ++ ([].map clipRead).toArray } = G := by
      cases G; simp
    rw [hG, ← hf]
    rfl
  | c :: cs, st, F, G, hops, hpath, hclip, hf, hk, hl, hne => by
    obtain ⟨cu, sa, h1⟩ := run_clipWords cx e st c hops hpath hclip (hne c (by simp))
    have hG : st.frames.back? = some G := by rw [hf]; simp
    have hfr : (st.addClip (clipRead c)).frames = F.push { G with clips := G.clips.push (clipRead c) } := by
      rw [addClip_fold st (clipRead c) G hG hk hl]; simp [hf]
    rw [List.flatMap_cons, run_append, h1, hfr]
    obtain ⟨cu', sa', h2⟩ := run_clips_fold cx e cs
      { st with frames := F.push { G with clips := G.clips.push (clipRead c) }, cur := cu, start := sa } F
      { G with clips := G.clips.push (clipRead c) } hops hpath hclip rfl hk (by simp [hf] at hl ⊢; omega)
      (fun c' hc' => hne c' (by simp [hc']))
    refine ⟨cu', sa', ?_⟩
    rw [h2]
    have hc : G.clips.push (clipRead c) ++ (cs.map clipRead).toArray = G.clips ++ ((c :: cs).map clipRead).toArray := by
      apply Array.toList_inj.mp; simp
    simp only [hc]

theorem run_header_plain (cx : Ctx) (e : Entered) (st : St) (hops : st.ops = #[]) :
    run cx e st (endLine (headerWords none #[])) = st.saveQ := by
  rw [run_endLine]
  exact run_q cx e st hops

theorem headerWords_split (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) :
    headerWords m clips = [opW "q"] ++ (m.map cmWords).getD [] ++ clips.toList.flatMap clipWords := by
  simp [headerWords]

theorem run_header_frame (cx : Ctx) (e : Entered) (st : St) (hc : Calm st) (T : Open)
    (hT : st.frames.back? = some T) (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule))
    (hm : m.all (fun mm => decide (readAffine mm ≠ Affine.unit)) = true) (hcl : clips.all (fun c => !c.1.isEmpty) = true)
    (hnon : m.isSome = true ∨ clips ≠ #[]) :
    ∃ cu sa, run cx e st (endLine (headerWords m clips)) =
      { st.saveQ with gs := ctmAfter st.gs m, frames := st.frames.push (hdr m clips), cur := cu, start := sa } := by
  have hne : ∀ c ∈ clips.toList, c.1 ≠ #[] := by
    intro c hc'
    have := Array.all_eq_true.mp hcl
    rw [Array.mem_toList_iff] at hc'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc'
    have := this i hi
    simpa using this
  rw [run_endLine, headerWords_split, run_append, run_append, run_q' _ _ _ hc.ops]
  have hq := calm_saveQ st hc
  have hTq : st.saveQ.frames.back? = some T := hT
  have hlq : st.saveQ.level = st.saveQ.frames.size := rfl
  cases m with
  | some mm =>
    have hmm : readAffine mm ≠ Affine.unit := by
      simp only [Option.all_some] at hm
      exact of_decide_eq_true hm
    rw [Option.map_some, Option.getD_some, run_cmWords _ _ _ _ hq.ops hmm T hTq hlq]
    obtain ⟨cu, sa, h⟩ := run_clips_fold cx e clips.toList
      { st.saveQ with
        gs := { st.saveQ.gs with ctm := st.saveQ.gs.ctm.compose (readAffine mm) }
        frames := st.saveQ.frames.push { xf := readAffine mm, clips := #[], alpha := Alpha.opaque, kids := #[] } }
      st.frames { xf := readAffine mm, clips := #[], alpha := Alpha.opaque, kids := #[] } hq.ops hq.path hq.clip rfl rfl
      (by simp [St.saveQ]) hne
    refine ⟨cu, sa, ?_⟩
    rw [h]
    have hh : ({ xf := readAffine mm, clips := #[] ++ (clips.toList.map clipRead).toArray, alpha := Alpha.opaque, kids := #[] } : Open) = hdr (some mm) clips := by
      simp only [hdr, Option.map_some, Option.getD_some]
      congr 1
      apply Array.toList_inj.mp
      simp
    rw [hh]
    rfl
  | none =>
    have hcne : clips ≠ #[] := by simpa using hnon
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, clips.toList = c :: cs := by
      cases h : clips.toList with
      | nil => exact absurd (Array.toList_inj.mp (by simpa using h)) hcne
      | cons c cs => exact ⟨c, cs, rfl⟩
    rw [Option.map_none, Option.getD_none, run_nil, hcs, List.flatMap_cons, run_append]
    obtain ⟨cu, sa, h1⟩ := run_clipWords cx e st.saveQ c hq.ops hq.path hq.clip (hne c (by simp [hcs]))
    rw [h1, addClip_push _ _ T hTq hlq]
    obtain ⟨cu', sa', h2⟩ := run_clips_fold cx e cs
      { st.saveQ with
        frames := st.saveQ.frames.push { xf := Affine.unit, clips := #[clipRead c], alpha := Alpha.opaque, kids := #[] }
        cur := cu, start := sa }
      st.frames { xf := Affine.unit, clips := #[clipRead c], alpha := Alpha.opaque, kids := #[] } hq.ops hq.path
      hq.clip rfl rfl (by simp [St.saveQ]) (fun c' hc' => hne c' (by simp [hcs, hc']))
    refine ⟨cu', sa', ?_⟩
    rw [h2]
    have hh : ({ xf := Affine.unit, clips := #[clipRead c] ++ (cs.map clipRead).toArray, alpha := Alpha.opaque, kids := #[] } : Open) = hdr none clips := by
      simp only [hdr, Option.map_none, Option.getD_none]
      congr 1
      apply Array.toList_inj.mp
      simp [hcs]
    rw [hh]
    rfl

/-- The nodes a covered saved state with a frame adds where it closes:
none when it painted nothing, else the group of what it painted. -/
def groupRead (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule))
    (kids : Array (Node Run)) : Array (Node Run) :=
  if kids.isEmpty then #[]
  else #[.group ((m.map readAffine).getD Affine.unit) (clips.map clipRead) Alpha.opaque kids]

mutual

-- conserves: none — the importer's nodes for a covered stream.
/-- The nodes the importer builds for a covered operation. -/
def opRead : Pdf.ContentOp → Array (Node Run)
  | .paint fl sk _ segs => #[drawRead fl sk segs]
  | .group m _ clips body =>
    if m.isNone && clips.isEmpty then opsReadInto #[] body.toList
    else groupRead m clips (opsReadInto #[] body.toList)
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => #[]

def opsReadInto (acc : Array (Node Run)) : List Pdf.ContentOp → Array (Node Run)
  | [] => acc
  | o :: rest => opsReadInto (acc ++ opRead o) rest

end

def opsRead (l : List Pdf.ContentOp) : Array (Node Run) := opsReadInto #[] l

theorem opsReadInto_acc (acc : Array (Node Run)) (l : List Pdf.ContentOp) :
    opsReadInto acc l = acc ++ opsReadInto #[] l := by
  induction l generalizing acc with
  | nil => simp [opsReadInto]
  | cons o rest ih =>
    rw [opsReadInto, opsReadInto, ih, ih (#[] ++ opRead o)]
    simp [Array.append_assoc]

@[simp] theorem opsRead_nil : opsRead [] = #[] := rfl

theorem opsRead_cons (o : Pdf.ContentOp) (rest : List Pdf.ContentOp) :
    opsRead (o :: rest) = opRead o ++ opsRead rest := by
  unfold opsRead
  rw [opsReadInto, opsReadInto_acc, Array.empty_append]

theorem opRead_group (m : Option Affine) (gs : Option Pdf.ExtG) (clips : Array (Array Pdf.PathOp × Rule))
    (body : Array Pdf.ContentOp) :
    opRead (.group m gs clips body) =
      if m.isNone && clips.isEmpty then opsRead body.toList else groupRead m clips (opsRead body.toList) := by
  rw [opRead]
  rfl

theorem closeInto_frame (T : Open) (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule))
    (K : Array (Node Run)) (hm : m.all (fun mm => decide (readAffine mm ≠ Affine.unit)) = true)
    (hnon : m.isSome = true ∨ clips ≠ #[]) :
    closeInto T { hdr m clips with kids := #[] ++ K } = { T with kids := T.kids ++ groupRead m clips K } := by
  unfold closeInto groupRead
  simp only [Array.empty_append]
  by_cases hk : K.isEmpty = true
  · rw [ite_eq_left hk, ite_eq_left hk]
    cases T; simp
  · rw [ite_eq_right hk, ite_eq_right hk]
    have hnt : ¬ ((hdr m clips).xf = Affine.unit ∧ (clips.map clipRead).isEmpty = true ∧
        (hdr m clips).alpha = Alpha.opaque) := by
      intro ⟨hx, hc, _⟩
      cases m with
      | some mm =>
        simp only [Option.all_some, decide_eq_true_eq] at hm
        exact hm (by simpa [hdr] using hx)
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, false_or] at hnon
        apply hnon
        simpa using hc
    simp only [hdr] at hnt ⊢
    rw [ite_eq_right hnt]
    rfl

theorem calm_header (st : St) (hc : Calm st) (m : Option Affine) (fs : Array Open) (cu sa : Pt) :
    Calm { st.saveQ with gs := ctmAfter st.gs m, frames := fs, cur := cu, start := sa } := by
  refine ⟨?_, hc.path, hc.clip, hc.ops, hc.hidden, by simp [St.saveQ]⟩
  have hg := hc.gs
  cases m with
  | none => simp only [ctmAfter]; exact hg
  | some mm =>
    simp only [ctmAfter]
    rw [hg]
    rfl

theorem frames_split (fs : Array Open) (T : Open) (h : fs.back? = some T) : fs = fs.pop.push T := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp h
  simp

theorem calm_frames (st : St) (hc : Calm st) (fs : Array Open) (cu sa : Pt) :
    Calm { st with frames := fs, cur := cu, start := sa } :=
  ⟨hc.gs, hc.path, hc.clip, hc.ops, hc.hidden, hc.level⟩

mutual

theorem sim_op (cx : Ctx) (e : Entered) : ∀ (o : Pdf.ContentOp) (st : St), opPlain o = true → Calm st →
    ∀ T, st.frames.back? = some T →
    ∃ cu sa, run cx e st (opWords o) =
      { st with frames := st.frames.pop.push { T with kids := T.kids ++ opRead o }, cur := cu, start := sa }
  | .paint fl sk gs segs, st, h, hc, T, hT => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨hgs, _⟩, _⟩, hfs⟩, hsegs⟩ := h
    subst hgs
    rw [opWords]
    obtain ⟨cu, sa, hr⟩ := run_paint cx e st hc T hT fl sk segs (by simpa using hfs) (by simpa using hsegs)
    refine ⟨cu, sa, ?_⟩
    rw [hr, show opRead (.paint fl sk none segs) = #[drawRead fl sk segs] from rfl, ← Array.push_eq_append]
  | .group m gs clips body, st, h, hc, T, hT => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨hgs, hm⟩, hcl⟩, hb⟩ := h
    subst hgs
    rw [opWords_group, run_append, run_append]
    by_cases htriv : m.isNone = true ∧ clips = #[]
    · obtain ⟨hmn, hcn⟩ := htriv
      have hmn' : m = none := by simpa using hmn
      subst hmn' hcn
      rw [run_header_plain _ _ _ hc.ops]
      obtain ⟨cu, sa, hbody⟩ := sim_list cx e body.toList st.saveQ hb (calm_saveQ st hc) T hT
      refine ⟨cu, sa, ?_⟩
      rw [hbody, run_Q _ _ _ st.gs st.frames.size (by simp [St.saveQ, hc.ops]) (by simp [St.saveQ])]
      rw [closeTo_noop _ _ (by simp only [St.saveQ]; rw [pop_push_size _ T hT]; omega)]
      have hr : opRead (.group none none #[] body) = opsRead body.toList := by
        rw [opRead_group]; rfl
      rw [hr]
      simp only [St.saveQ, Array.pop_push]
      rw [← hc.level]
    · have hnon : m.isSome = true ∨ clips ≠ #[] := by
        cases m with
        | some _ => exact Or.inl rfl
        | none =>
          right
          intro hcn
          exact htriv ⟨rfl, hcn⟩
      obtain ⟨cu, sa, hh⟩ := run_header_frame cx e st hc T hT m clips hm hcl hnon
      rw [hh]
      obtain ⟨cu', sa', hbody⟩ := sim_list cx e body.toList
        { st.saveQ with gs := ctmAfter st.gs m, frames := st.frames.push (hdr m clips), cur := cu, start := sa }
        hb (calm_header st hc m _ cu sa) (hdr m clips) (by simp)
      refine ⟨cu', sa', ?_⟩
      rw [hbody, run_Q _ _ _ st.gs st.frames.size (by simp [St.saveQ, hc.ops]) (by simp [St.saveQ])]
      have hsplit := frames_split st.frames T hT
      have hc2 : closeTo ((st.frames.push (hdr m clips)).pop.push { hdr m clips with kids := (hdr m clips).kids ++ opsRead body.toList })
          st.frames.size = st.frames.pop.push { T with kids := T.kids ++ groupRead m clips (opsRead body.toList) } := by
        rw [Array.pop_push]
        conv => lhs; rw [hsplit]
        rw [Array.size_push, closeTo_one, show (hdr m clips).kids = #[] from rfl, closeInto_frame T m clips _ hm hnon]
      rw [hc2]
      have hr : opRead (.group m none clips body) = groupRead m clips (opsRead body.toList) := by
        rw [opRead_group]
        have : (m.isNone && clips.isEmpty) = false := by
          cases m with
          | some _ => rfl
          | none =>
            simp only [Option.isNone_none, Bool.true_and]
            cases hce : clips.isEmpty
            · rfl
            · exact absurd (Array.isEmpty_iff.mp hce) (by simpa using hnon)
        rw [this]
        rfl
      rw [hr]
      simp only [St.saveQ, Array.pop_push]
      rw [← hc.level]
  | .fill _ _ _ _ _, _, h, _, _, _ | .text _, _, h, _, _, _ | .image _ _ _ _ _, _, h, _, _, _
  | .imageMissing _ _ _ _, _, h, _, _, _ | .marked _ _, _, h, _, _, _ | .shade _ _, _, h, _, _, _
  | .outline _ _ _, _, h, _, _, _ | .xobject _ _ _ _, _, h, _, _, _ => by simp [opPlain] at h

theorem sim_list (cx : Ctx) (e : Entered) : ∀ (l : List Pdf.ContentOp) (st : St), opsPlain l = true →
    Calm st → ∀ T, st.frames.back? = some T →
    ∃ cu sa, run cx e st (opWordsList l) =
      { st with frames := st.frames.pop.push { T with kids := T.kids ++ opsRead l }, cur := cu, start := sa }
  | [], st, _, _, T, hT => by
    refine ⟨st.cur, st.start, ?_⟩
    rw [opWordsList_nil, run_nil, opsRead_nil, Array.append_empty]
    have : ({ T with kids := T.kids } : Open) = T := rfl
    rw [this, ← frames_split st.frames T hT]
  | o :: rest, st, h, hc, T, hT => by
    simp only [opsPlain, Bool.and_eq_true] at h
    rw [opWordsList_cons, run_append]
    obtain ⟨cu, sa, h1⟩ := sim_op cx e o st h.1 hc T hT
    rw [h1]
    obtain ⟨cu', sa', h2⟩ := sim_list cx e rest
      { st with frames := st.frames.pop.push { T with kids := T.kids ++ opRead o }, cur := cu, start := sa }
      h.2 (calm_frames st hc _ cu sa) { T with kids := T.kids ++ opRead o } (by simp)
    refine ⟨cu', sa', ?_⟩
    rw [h2, opsRead_cons]
    simp [Array.append_assoc]

end

theorem calm_initial : Calm (St.initial (GState.initial Affine.unit) Store.empty) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem readStream_render (cx : Ctx) (ops : Array Pdf.ContentOp) (h : opsPlain ops.toList = true) :
    let fig := readStream cx (Pdf.render ops).toUTF8
    fig.nodes = opsRead ops.toList ∧ fig.losses = #[] ∧ fig.outlines = #[] ∧ fig.symbols = #[] := by
  intro fig
  have hrun : runToks cx Entered.empty
      (PdfContentLex.scan (Pdf.render ops).toUTF8) 0 (St.initial (GState.initial Affine.unit) Store.empty) =
      run cx Entered.empty
        (St.initial (GState.initial Affine.unit) Store.empty) (opWordsList ops.toList) := by
    rw [runToks_foldl, scan_render ops h, run]
    simp
  obtain ⟨cu, sa, hs⟩ := sim_list cx Entered.empty
    ops.toList _ h calm_initial { xf := Affine.unit, clips := #[], alpha := Alpha.opaque, kids := #[] } rfl
  have hst : runToks cx Entered.empty
      (PdfContentLex.scan (Pdf.render ops).toUTF8) 0 (St.initial (GState.initial Affine.unit) Store.empty) =
      { St.initial (GState.initial Affine.unit) Store.empty with
        frames := #[{ xf := Affine.unit, clips := #[], alpha := Alpha.opaque, kids := opsRead ops.toList }]
        cur := cu, start := sa } := by
    rw [hrun, hs]
    simp [St.initial]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (runToks cx _ _ 0 _).finish = _
    rw [hst]
    unfold St.finish
    rw [closeTo_noop _ _ (by simp)]
    simp [St.initial]
  · show (runToks cx _ _ 0 _).store.losses = _
    rw [hst]
    rfl
  · show (runToks cx _ _ 0 _).store.outlines = _
    rw [hst]
    rfl
  · show (runToks cx _ _ 0 _).store.symbols = _
    rw [hst]
    rfl

/-- The identity placement: a figure read where it was written. -/
@[expose] public def isoId : Iso := { flipY := false, dx := 0, dy := 0 }

/-- A colour as a screen compares it: its device spelling and who chose it forgotten. -/
@[expose] public def colorScreen (c : Ir.Color) : Ir.Color :=
  { c with pdfModel := none, origin := .declared }

@[expose] public def stopScreen (s : Stop) : Stop := { s with color := colorScreen s.color }

@[expose] public def gradScreen : Gradient → Gradient
  | .linear p0 p1 st xf => .linear p0 p1 (st.map stopScreen) xf
  | .radial c0 r0 c1 r1 st xf => .radial c0 r0 c1 r1 (st.map stopScreen) xf

@[expose] public def paintScreen : Paint → Paint
  | .solid c => .solid (colorScreen c)
  | .gradient g => .gradient (gradScreen g)

@[expose] public def fillScreen (f : Fill) : Fill := { f with paint := paintScreen f.paint }

@[expose] public def strokeScreen (s : Stroke) : Stroke := { s with paint := paintScreen s.paint }

/-- A mark as a screen compares it, every colour's device spelling forgotten. -/
@[expose] public def markScreen : Mark → Mark
  | .paint ctm g fl sk clips alphas => .paint ctm g (fl.map fillScreen) (sk.map strokeScreen) clips alphas
  | .raster ctm k clips alphas => .raster ctm k clips alphas
  | .shading g clips alphas => .shading (gradScreen g) clips alphas

/-- A stroke with every number the writer prints read back, its dash as both readers draw it. -/
@[expose] public def strokeBack (k : Pdf.PaintStroke) : Pdf.PaintStroke :=
  { k with
    width := qLen k.width
    miter := k.miter.map fun r => ratRead r.num r.den
    dash := k.dash.map fun dp => (Kit.normDash (dp.1.map qLen), qLen dp.2) }

mutual

-- conserves: none — a read-back of the numbers an operation prints.
/-- A path or saved state with every number it prints read back; any other operation is kept as it
is. -/
@[expose] public def opBack : Pdf.ContentOp → Pdf.ContentOp
  | .paint fl sk gs segs => .paint fl (sk.map strokeBack) gs (segs.map pathRead)
  | .group m gs clips body =>
    .group (m.map readAffine) gs (clips.map fun c => (c.1.map pathRead, c.2)) (opsBack body.toList).toArray
  | .fill c x y w h => .fill c x y w h
  | .text t => .text t
  | .image x y w h r => .image x y w h r
  | .imageMissing x y w h => .imageMissing x y w h
  | .marked t b => .marked t b
  | .shade r g => .shade r g
  | .outline f s p => .outline f s p
  | .xobject m r k b => .xobject m r k b

@[expose] public def opsBack : List Pdf.ContentOp → List Pdf.ContentOp
  | [] => []
  | o :: rest => opBack o :: opsBack rest

end

theorem isoId_apply (p : Pt) : isoId.inv.apply p = p := by
  obtain ⟨x, y⟩ := p
  simp [isoId, Iso.inv, Iso.apply]

theorem mapIso_isoId (g : Geom) : g.mapIso isoId.inv = g := by
  have hs : ∀ s : Subpath, s.map isoId.inv.apply = s := by
    intro s
    obtain ⟨st, segs, c⟩ := s
    have hseg : Seg.map isoId.inv.apply = id := by
      funext sg; cases sg <;> simp [Seg.map, isoId_apply]
    simp [Subpath.map, isoId_apply, hseg]
  cases g with
  | rect x y w h => simp [Geom.mapIso, Iso.rect, isoId, Iso.inv]
  | ellipse cx cy rx ry => simp [Geom.mapIso, isoId_apply]
  | path subs =>
    have hs' : Subpath.map isoId.inv.apply = id := funext hs
    simp [Geom.mapIso, hs']

theorem stGeom_drawn (P : Array Pdf.PathOp) (d : Bool) :
    (stGeom P).drawn d = (GfxPdf.geomOf P.toList).drawn d := by
  unfold stGeom
  split
  · next x y w h hr =>
    rw [hr]
    by_cases hn : (w < 0 || h < 0) = true
    · rw [ite_eq_left hn]
      have hn' : ¬ (0 < w ∧ 0 < h) := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
        intro ⟨hw, hh⟩
        rcases hn with hn | hn
        · exact absurd hw (Int.lt_asymm hn)
        · exact absurd hh (Int.lt_asymm hn)
      have hnu : 0 < w.units → h.units ≤ 0 := fun hw => by
        have := hn'
        length_omega
      cases d
      · simp only [Geom.drawn, Geom.traced, Geom.normal]
        simpa using hnu
      · simp [Geom.drawn, Geom.traced]
    · rw [ite_eq_right hn]
  · next a b c e hr => rw [hr]
  · next subs hr => rw [hr]

theorem isoId_toAffine : isoId.inv.toAffine = Affine.unit := by
  simp [isoId, Iso.inv, Iso.toAffine, Affine.unit, Length.toRat]

/-- Where the importer's figure walk and PDF's own reading stand together:
one frame, one clip stack, no group alpha but the one each reads, PDF's
initial colour and line state. -/
structure Agree (cx : Gfx.Ctx) (rs : GfxPdf.RState) : Prop where
  place : rs.place = isoId
  frame : rs.frameCtm = cx.ctm
  user : rs.userCtm = cx.ctm
  clips : rs.clips = cx.clips
  alphas : rs.alphas = cx.alphas
  ca : rs.ca = Alpha.opaque
  cA : rs.cA = Alpha.opaque
  pen : rs.pen = GfxPdf.Pen.initial

theorem agree_root : Agree Gfx.Ctx.root (GfxPdf.RState.root isoId) := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [GfxPdf.RState.userCtm, GfxPdf.RState.root, ↓reduceIte, Gfx.Ctx.root]
  exact isoId_toAffine

theorem colorScreen_read (c : Ir.Color) (h : c.cmyk = none) : colorScreen (colorRead c) = colorScreen c := by
  obtain ⟨r, g, b, cm, pm, o⟩ := c
  simp only at h
  subst h
  rfl

theorem plain_solid {p : Pdf.PdfPaint} (h : plainPaint p = true) :
    p = .solid (paintColor p) ∧ (paintColor p).cmyk = none := by
  cases p with
  | solid c =>
    simp only [plainPaint, plainColor, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact ⟨rfl, h.2⟩
  | pattern _ _ => simp [plainPaint] at h

theorem normDash_nil : Kit.normDash #[] = #[] := by simp [Kit.normDash]

theorem plain_cmyk {c : Ir.Color} (h : plainPaint (.solid c) = true) : c.cmyk = none := by
  simp only [plainPaint, plainColor, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h.2

theorem fill_agree (rs : GfxPdf.RState) (ha : Agree cx rs) (m : Affine) (f : Pdf.PaintFill)
    (h : plainPaint f.paint = true) :
    fillScreen ((fillRead f).under m) = fillScreen (GfxPdf.readFill rs none f) := by
  obtain ⟨pp, eo⟩ := f
  cases pp with
  | pattern _ _ => simp [plainPaint] at h
  | solid c =>
    have hc := plain_cmyk h
    cases eo <;> simp [fillRead, Fill.under, Paint.under, GfxPdf.readFill, GfxPdf.readPaint, fillScreen,
      paintScreen, paintColor, ha.ca, colorScreen_read c hc]

theorem stroke_agree (rs : GfxPdf.RState) (ha : Agree cx rs) (m : Affine) (k : Pdf.PaintStroke)
    (h : plainPaint k.paint = true) :
    strokeScreen ((strokeRead k).under m) = strokeScreen (GfxPdf.readStroke rs none (strokeBack k)) := by
  obtain ⟨pp, w, cap, join, miter, dash⟩ := k
  cases pp with
  | pattern _ _ => simp [plainPaint] at h
  | solid c =>
    have hc := plain_cmyk h
    cases dash <;> simp [strokeRead, Stroke.under, Paint.under, GfxPdf.readStroke, GfxPdf.readPaint, strokeScreen,
      paintScreen, paintColor, strokeBack, ha.cA, ha.pen, GfxPdf.Pen.initial, GfxPdf.pdfMiter,
      colorScreen_read c hc, normDash_nil]

theorem dash_agree (rs : GfxPdf.RState) (ha : Agree cx rs) (k : Pdf.PaintStroke) :
    (GfxPdf.readStroke rs none (strokeBack k)).dash = (strokeRead k).dash := by
  obtain ⟨pp, w, cap, join, miter, dash⟩ := k
  cases dash <;> simp [GfxPdf.readStroke, strokeBack, strokeRead, ha.pen, GfxPdf.Pen.initial, normDash_nil]

theorem dashed_agree (rs : GfxPdf.RState) (ha : Agree cx rs) (sk : Option Pdf.PaintStroke) :
    ((sk.map strokeBack).map (GfxPdf.readStroke rs none)).any Stroke.dashed = (sk.map strokeRead).any Stroke.dashed := by
  cases sk with
  | none => rfl
  | some k => simp [Stroke.dashed, dash_agree rs ha k]

theorem geom_agree' (rs : GfxPdf.RState) (ha : Agree cx rs) (P : Array Pdf.PathOp) (d : Bool) :
    rs.geom P d = (stGeom P).drawn d := by
  rw [stGeom_drawn]
  unfold GfxPdf.RState.geom
  split
  · rw [ha.place, mapIso_isoId]
  · rfl

theorem map_push_screen (a b : Array Mark) (x y : Mark) (h : a.map markScreen = b.map markScreen)
    (hxy : markScreen x = markScreen y) : (a.push x).map markScreen = (b.push y).map markScreen := by
  simp [Array.map_push, h, hxy]

theorem marks_paint (rs : GfxPdf.RState) (ha : Agree cx rs) (macc racc : Array Mark)
    (hacc : macc.map markScreen = racc.map markScreen) (fl : Option Pdf.PaintFill) (sk : Option Pdf.PaintStroke)
    (segs : Array Pdf.PathOp) (hf : fl.all (plainPaint ·.paint) = true) (hs : sk.all (plainPaint ·.paint) = true) :
    (Node.marksList #[] cx macc (#[drawRead fl sk segs] : Array (Node Run)).toList).map markScreen =
      (GfxPdf.readOne rs racc (.paint fl (sk.map strokeBack) none (segs.map pathRead))).map markScreen := by
  simp only [drawRead, Node.marksList, Node.marksOne, GfxPdf.readOne]
  apply map_push_screen _ _ _ _ hacc
  simp only [markScreen, ha.frame, ha.clips, ha.alphas, geom_agree' rs ha, dashed_agree rs ha]
  congr 1
  · cases fl with
    | none => rfl
    | some f =>
      simp only [Option.map_some, Option.some.injEq]
      exact fill_agree rs ha cx.ctm f (by simpa using hf)
  · cases sk with
    | none => rfl
    | some k =>
      simp only [Option.map_some, Option.some.injEq]
      exact stroke_agree rs ha cx.ctm k (by simpa using hs)

theorem agree_enter (rs : GfxPdf.RState) (ha : Agree cx rs) (m : Option Affine)
    (clips : Array (Array Pdf.PathOp × Rule)) :
    Agree (cx.enter ((m.map readAffine).getD Affine.unit) (clips.map clipRead) Alpha.opaque)
      (rs.enterGroup (m.map readAffine) none (clips.map fun c => (c.1.map pathRead, c.2))) := by
  have hcm : ∀ (mm : Option Affine), (rs.cm mm).place = rs.place := by
    intro mm; cases mm <;> rfl
  have hframe : (rs.cm (m.map readAffine)).frameCtm = cx.ctm.compose ((m.map readAffine).getD Affine.unit) := by
    cases m with
    | none => simp [GfxPdf.RState.cm, ha.frame, (Affine.compose_unit_id _).1]
    | some mm =>
      show rs.userCtm.compose (readAffine mm) = _
      rw [ha.user]
      rfl
  have huser : (rs.cm (m.map readAffine)).userCtm = cx.ctm.compose ((m.map readAffine).getD Affine.unit) := by
    cases m with
    | none => simp [GfxPdf.RState.cm, ha.user, (Affine.compose_unit_id _).1]
    | some mm =>
      show rs.userCtm.compose (readAffine mm) = _
      rw [ha.user]
      rfl
  have hpl : (rs.cm (m.map readAffine)).place = isoId := by rw [hcm, ha.place]
  have hrs1 : ∀ (mm : Option Affine), (rs.cm mm).clips = rs.clips ∧ (rs.cm mm).alphas = rs.alphas ∧
      (rs.cm mm).ca = rs.ca ∧ (rs.cm mm).cA = rs.cA ∧ (rs.cm mm).pen = rs.pen := by
    intro mm; cases mm <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrs1 (m.map readAffine)
  refine ⟨hpl, hframe, huser, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : ∀ c : Array Pdf.PathOp × Rule,
        (rs.cm (m.map readAffine)).geom (c.1.map pathRead) false = (stGeom (c.1.map pathRead)).normal := by
      intro c
      unfold GfxPdf.RState.geom
      rw [← stGeom_drawn]
      split
      · rw [hpl, mapIso_isoId]; rfl
      · rfl
    simp only [GfxPdf.RState.enterGroup, Gfx.Ctx.enter, h1, ha.clips, Array.map_map]
    congr 1
    congr 1
    funext c
    simp only [Function.comp_def, clipRead, hframe, hg]
  · simp [GfxPdf.RState.enterGroup, Gfx.Ctx.enter, h2, ha.alphas]
  · simp [GfxPdf.RState.enterGroup, h3, ha.ca]
  · simp [GfxPdf.RState.enterGroup, h4, ha.cA]
  · simp [GfxPdf.RState.enterGroup, h5, ha.pen]

theorem agree_plainGroup (rs : GfxPdf.RState) (ha : Agree cx rs) :
    Agree cx (rs.enterGroup none none #[]) := by
  refine ⟨ha.place, ha.frame, ha.user, ?_, ha.alphas, ha.ca, ha.cA, ha.pen⟩
  simp [GfxPdf.RState.enterGroup, GfxPdf.RState.cm, ha.clips]

mutual

theorem marks_op : ∀ (o : Pdf.ContentOp) (cx : Gfx.Ctx) (rs : GfxPdf.RState) (macc racc : Array Mark),
    opPlain o = true → Agree cx rs → macc.map markScreen = racc.map markScreen →
    (Node.marksList #[] cx macc (opRead o).toList).map markScreen =
      (GfxPdf.readOne rs racc (opBack o)).map markScreen
  | .paint fl sk gs segs, cx, rs, macc, racc, h, ha, hacc => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨hgs, hf⟩, hs⟩, _⟩, _⟩ := h
    subst hgs
    rw [opRead, opBack]
    exact marks_paint rs ha macc racc hacc fl sk segs hf hs
  | .group m gs clips body, cx, rs, macc, racc, h, ha, hacc => by
    simp only [opPlain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨hgs, _⟩, _⟩, hb⟩ := h
    subst hgs
    rw [opRead_group, opBack]
    simp only [GfxPdf.readOne]
    by_cases ht : (m.isNone && clips.isEmpty) = true
    · rw [ite_eq_left ht]
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Array.isEmpty_iff] at ht
      obtain ⟨hm, hc⟩ := ht
      subst hm hc
      have e : (Option.map readAffine none : Option Affine) = none := rfl
      have e2 : (Array.map (fun c : Array Pdf.PathOp × Rule => (Array.map pathRead c.fst, c.snd)) #[]) = #[] := by
        simp
      rw [e, e2]
      exact marks_ops body.toList cx _ macc racc hb (agree_plainGroup rs ha) hacc
    · rw [ite_eq_right ht]
      have hih := marks_ops body.toList _ _ macc racc hb (agree_enter rs ha m clips) hacc
      unfold groupRead
      by_cases hk : (opsRead body.toList).isEmpty = true
      · rw [ite_eq_left hk]
        rw [Array.isEmpty_iff.mp hk] at hih
        rw [← hih]
        rfl
      · rw [ite_eq_right hk]
        simp only [Node.marksList, Node.marksOne]
        exact hih
  | .fill _ _ _ _ _, _, _, _, _, h, _, _ | .text _, _, _, _, _, h, _, _
  | .image _ _ _ _ _, _, _, _, _, h, _, _ | .imageMissing _ _ _ _, _, _, _, _, h, _, _
  | .marked _ _, _, _, _, _, h, _, _ | .shade _ _, _, _, _, _, h, _, _
  | .outline _ _ _, _, _, _, _, h, _, _ | .xobject _ _ _ _, _, _, _, _, h, _, _ => by simp [opPlain] at h

theorem marks_ops : ∀ (l : List Pdf.ContentOp) (cx : Gfx.Ctx) (rs : GfxPdf.RState) (macc racc : Array Mark),
    opsPlain l = true → Agree cx rs → macc.map markScreen = racc.map markScreen →
    (Node.marksList #[] cx macc (opsRead l).toList).map markScreen =
      (GfxPdf.readList rs racc (opsBack l)).map markScreen
  | [], _, _, _, _, _, _, hacc => by simpa [opsBack, Node.marksList, GfxPdf.readList] using hacc
  | o :: rest, cx, rs, macc, racc, h, ha, hacc => by
    simp only [opsPlain, Bool.and_eq_true] at h
    rw [opsRead_cons, opsBack, Array.toList_append, Node.marksList_append, GfxPdf.readList]
    exact marks_ops rest cx rs _ _ h.2 ha (marks_op o cx rs macc racc h.1 ha hacc)

end

mutual

theorem expandOne_free {L : Type} (done : Array (Array (Node L))) (bound : Nat) :
    ∀ (n : Node L) (acc : Array (Node L)), Node.useFree n = true → Node.expandOne done bound acc n = acc.push n
  | .draw _ _ _, _, _ => rfl
  | .group xf clips alpha kids, acc, h => by
    simp only [Node.useFree] at h
    rw [Node.expandOne, expandList_free done bound kids.toList #[] h]
    simp
  | .use _ _, _, h => by simp [Node.useFree] at h
  | .stamp _ _ _ _, _, _ => rfl
  | .image _ _, _, _ => rfl
  | .label _, _, _ => rfl
  | .words _, _, _ => rfl

theorem expandList_free {L : Type} (done : Array (Array (Node L))) (bound : Nat) :
    ∀ (l : List (Node L)) (acc : Array (Node L)), Node.useFreeList l = true →
      Node.expandList done bound acc l = acc ++ l.toArray
  | [], acc, _ => by simp [Node.expandList]
  | n :: rest, acc, h => by
    simp only [Node.useFreeList, Bool.and_eq_true] at h
    rw [Node.expandList, expandOne_free done bound n acc h.1, expandList_free done bound rest _ h.2]
    simp

end

theorem groupRead_free (m : Option Affine) (clips : Array (Array Pdf.PathOp × Rule)) (K : Array (Node Run))
    (h : Node.useFreeList K.toList = true) : Node.useFreeList (groupRead m clips K).toList = true := by
  unfold groupRead
  split
  · rfl
  · simp [Node.useFreeList, Node.useFree, h]

mutual

theorem opRead_free : ∀ (o : Pdf.ContentOp), Node.useFreeList (opRead o).toList = true
  | .paint _ _ _ _ => rfl
  | .group m _ clips body => by
    rw [opRead_group]
    split
    · exact opsRead_free body.toList
    · exact groupRead_free m clips _ (opsRead_free body.toList)
  | .fill _ _ _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ | .marked _ _ | .shade _ _
  | .outline _ _ _ | .xobject _ _ _ _ => by rw [opRead]; rfl

theorem opsRead_free : ∀ (l : List Pdf.ContentOp), Node.useFreeList (opsRead l).toList = true
  | [] => rfl
  | o :: rest => by
    rw [opsRead_cons, Array.toList_append, Node.useFreeList_append, opRead_free o, opsRead_free rest]
    rfl

end

public theorem readback_exact (cx : Ctx) (ops : Array Pdf.ContentOp) (h : opsPlain ops.toList = true) :
    (readStream cx (Pdf.render ops).toUTF8).losses = #[] ∧
      (readStream cx (Pdf.render ops).toUTF8).marks.map markScreen =
        (GfxPdf.readMarks isoId (opsBack ops.toList).toArray).map markScreen := by
  obtain ⟨hn, hl, ho, hs⟩ := readStream_render cx ops h
  refine ⟨hl, ?_⟩
  unfold Figure.marks Figure.expanded Figure.bodies GfxPdf.readMarks
  rw [ho, hs, hn]
  simp only [Array.size_empty]
  rw [expandList_free _ _ _ _ (opsRead_free ops.toList), Array.empty_append, List.toList_toArray]
  exact marks_ops ops.toList Gfx.Ctx.root _ #[] #[] h agree_root rfl

/-- A fill the read-back covers: a plain device colour, opaque. -/
@[expose] public def fillPlain (f : Fill) : Bool :=
  match f.paint with
  | .solid c => plainColor c && decide (f.alpha = Alpha.opaque)
  | .gradient _ => false

/-- A stroke the read-back covers: a plain device colour, opaque. -/
@[expose] public def strokePlain (s : Stroke) : Bool :=
  match s.paint with
  | .solid c => plainColor c && decide (s.alpha = Alpha.opaque)
  | .gradient _ => false

/-- A geometry with a path to paint. -/
@[expose] public def geomInked : Geom → Bool
  | .rect _ _ _ _ => true
  | .ellipse _ _ _ _ => true
  | .path subs => !subs.isEmpty

mutual

-- conserves: none — a predicate.
/-- A figure node the read-back covers: a plain opaque fill or stroke on a path, an opaque group of
such nodes whose clips each have a path, or words. -/
@[expose] public def nodePlain : Node Empty → Bool
  | .draw g fl sk => geomInked g && fl.all fillPlain && sk.all strokePlain && (fl.isSome || sk.isSome)
  | .group _ clips alpha kids =>
    decide (alpha = Alpha.opaque) && clips.all (geomInked ·.geom) && nodesPlain kids.toList
  | .words _ => true
  | .use _ _ | .stamp _ _ _ _ | .image _ _ | .label _ => false

@[expose] public def nodesPlain : List (Node Empty) → Bool
  | [] => true
  | n :: rest => nodePlain n && nodesPlain rest

end

theorem opsPlain_append (a b : List Pdf.ContentOp) : opsPlain (a ++ b) = (opsPlain a && opsPlain b) := by
  induction a with
  | nil => simp [opsPlain]
  | cons o rest ih => simp [opsPlain, ih, Bool.and_assoc]

theorem opsBack_append (a b : List Pdf.ContentOp) : opsBack (a ++ b) = opsBack a ++ opsBack b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [opsBack, ih]

theorem opsBack_length (a : List Pdf.ContentOp) : (opsBack a).length = a.length := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [opsBack, ih]

theorem fixed_append (a b : List Pdf.ContentOp) (h : opsBack (a ++ b) = a ++ b) :
    opsBack a = a ∧ opsBack b = b := by
  rw [opsBack_append] at h
  exact List.append_inj h (opsBack_length a)

theorem subpathOps_ne (sp : Subpath) : GfxPdf.subpathOps sp ≠ [] := by
  simp [GfxPdf.subpathOps]

theorem flatMap_subpathOps_ne (l : List Subpath) (h : l ≠ []) : l.flatMap GfxPdf.subpathOps ≠ [] := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [List.flatMap_cons, subpathOps_ne]

theorem geomOps_ne (g : Geom) (h : geomInked g = true) : GfxPdf.geomOps g ≠ [] := by
  cases g with
  | rect _ _ _ _ => simp [GfxPdf.geomOps]
  | ellipse cx cy rx ry =>
    simp only [GfxPdf.geomOps, Kit.ellipse]
    exact flatMap_subpathOps_ne _ (by simp)
  | path subs =>
    simp only [geomInked, Bool.not_eq_true', Array.isEmpty_eq_false_iff] at h
    simp only [GfxPdf.geomOps]
    exact flatMap_subpathOps_ne _ (by simpa using h)

theorem isoId_toAffine' : isoId.toAffine = Affine.unit := by
  simp [isoId, Iso.toAffine, Affine.unit, Length.toRat]

theorem frameOps_ne (fr : GfxPdf.Frame) (hfr : fr.iso = some isoId ∨ fr.iso = none) (g : Geom)
    (h : geomInked g = true) (d : Bool) : fr.geomOps g d ≠ [] := by
  unfold GfxPdf.Frame.geomOps
  rcases hfr with hf | hf <;> rw [hf]
  · simp only [isoId, Bool.false_eq_true, ↓reduceIte]
    cases g with
    | rect x y w hh => simp [GfxPdf.geomOps, Geom.mapIso]
    | ellipse cx cy rx ry =>
      apply geomOps_ne
      simp [Geom.normal, Geom.mapIso, geomInked, Kit.ellipse]
    | path subs =>
      apply geomOps_ne
      simp only [geomInked, Bool.not_eq_true', Array.isEmpty_eq_false_iff] at h
      simp [Geom.normal, Geom.mapIso, geomInked, h]
  · exact geomOps_ne g h

theorem lift_eq (fr : GfxPdf.Frame) (hfr : fr.iso = some isoId ∨ fr.iso = none) (xf : Affine) :
    fr.lift xf = xf := by
  unfold GfxPdf.Frame.lift
  rcases hfr with hf | hf <;> rw [hf]
  · simp only
    rw [isoId_toAffine']
    exact (Affine.compose_unit_id xf).2

theorem enter_iso (fr : GfxPdf.Frame) (hfr : fr.iso = some isoId ∨ fr.iso = none) (m : Option Affine) :
    (fr.enter m).iso = some isoId ∨ (fr.enter m).iso = none := by
  cases m with
  | none => exact hfr
  | some _ => exact Or.inr rfl

theorem fill_plainPaint (ix : GfxPdf.Request → Nat) (fr : GfxPdf.Frame) (f : Fill) (h : fillPlain f = true) :
    plainPaint (GfxPdf.paintFill ix fr f).paint = true := by
  obtain ⟨pp, r, a⟩ := f
  cases pp with
  | solid c =>
    simp only [fillPlain, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [GfxPdf.paintFill, GfxPdf.pdfPaint, plainPaint, h.1]
  | gradient _ => simp [fillPlain] at h

theorem stroke_plainPaint (ix : GfxPdf.Request → Nat) (fr : GfxPdf.Frame) (s : Stroke) (h : strokePlain s = true) :
    plainPaint (GfxPdf.paintStroke ix fr s).paint = true := by
  obtain ⟨pp, w, cap, join, ml, dash, ph, a⟩ := s
  cases pp with
  | solid c =>
    simp only [strokePlain, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [GfxPdf.paintStroke, GfxPdf.pdfPaint, plainPaint, h.1]
  | gradient _ => simp [strokePlain] at h

theorem fill_alpha (f : Fill) (h : fillPlain f = true) : f.alpha = Alpha.opaque := by
  obtain ⟨pp, r, a⟩ := f
  cases pp with
  | solid c => simp only [fillPlain, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  | gradient _ => simp [fillPlain] at h

theorem stroke_alpha (s : Stroke) (h : strokePlain s = true) : s.alpha = Alpha.opaque := by
  obtain ⟨pp, w, cap, join, ml, dash, ph, a⟩ := s
  cases pp with
  | solid c => simp only [strokePlain, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  | gradient _ => simp [strokePlain] at h

theorem draw_plain (ix : GfxPdf.Request → Nat) (fr : GfxPdf.Frame) (hfr : fr.iso = some isoId ∨ fr.iso = none)
    (g : Geom) (fl : Option Fill) (sk : Option Stroke)
    (h : nodePlain (.draw g fl sk) = true) : opPlain (GfxPdf.drawOp ix fr g fl sk) = true := by
  simp only [nodePlain, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hg, hf⟩, hs⟩, hfs⟩ := h
  have hfa : (fl.map (·.alpha)).getD Alpha.opaque = Alpha.opaque := by
    cases fl with
    | none => rfl
    | some f => simpa using fill_alpha f (by simpa using hf)
  have hsa : (sk.map (·.alpha)).getD Alpha.opaque = Alpha.opaque := by
    cases sk with
    | none => rfl
    | some k => simpa using stroke_alpha k (by simpa using hs)
  simp only [GfxPdf.drawOp, opPlain, hfa, hsa, GfxPdf.extOf, and_self, ↓reduceIte, Option.isNone_none,
    Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, Option.isSome_map, Bool.not_eq_true',
    Array.isEmpty_eq_false_iff]
  refine ⟨⟨⟨?_, ?_⟩, hfs⟩, ?_⟩
  · cases fl with
    | none => rfl
    | some f => simpa using fill_plainPaint ix fr f (by simpa using hf)
  · cases sk with
    | none => rfl
    | some k => simpa using stroke_plainPaint ix fr k (by simpa using hs)
  · intro he
    exact frameOps_ne fr hfr g hg _ (by simpa using he)

/-- The label setter of a `Figure Empty`, which sets none. -/
@[expose] public def noLabels : GfxPdf.Frame → Empty → Array Pdf.ContentOp := fun _ e => nomatch e

mutual

theorem plain_emitOne (ix : GfxPdf.Request → Nat) (outlines : Array (Array Subpath))
    (bodyOps : Array (Array Pdf.ContentOp)) :
    ∀ (n : Node Empty) (fr : GfxPdf.Frame), (fr.iso = some isoId ∨ fr.iso = none) → nodePlain n = true →
      opsBack (GfxPdf.emitOne ix noLabels outlines bodyOps fr #[] n).toList =
        (GfxPdf.emitOne ix noLabels outlines bodyOps fr #[] n).toList →
      opsPlain (GfxPdf.emitOne ix noLabels outlines bodyOps fr #[] n).toList = true
  | .draw g fl sk, fr, hfr, hn, _ => by
    simp only [GfxPdf.emitOne, Array.toList_push, List.nil_append, opsPlain, Bool.and_true]
    exact draw_plain ix fr hfr g fl sk hn
  | .group xf clips alpha kids, fr, hfr, hn, hfix => by
    have hn' := hn
    simp only [nodePlain, Bool.and_eq_true, decide_eq_true_eq] at hn'
    obtain ⟨⟨ha, hcl⟩, hk⟩ := hn'
    simp only [GfxPdf.emitOne] at hfix ⊢
    split
    · next hp =>
      rw [ite_eq_left hp] at hfix
      exact plain_emitList ix outlines bodyOps kids.toList fr hfr hk hfix
    · next hp =>
      rw [ite_eq_right hp] at hfix
      rw [ite_eq_left ha] at hfix
      simp only [Array.toList_push, List.nil_append, opsPlain, Bool.and_true] at hfix ⊢
      simp only [opsBack, opBack, List.cons.injEq, Pdf.ContentOp.group.injEq] at hfix
      obtain ⟨⟨hm, _, _, hb⟩, _⟩ := hfix
      have hb' : opsBack (GfxPdf.emitList ix noLabels outlines bodyOps
          (fr.enter (GfxPdf.groupCm fr xf)) #[] kids.toList).toList =
          (GfxPdf.emitList ix noLabels outlines bodyOps
            (fr.enter (GfxPdf.groupCm fr xf)) #[] kids.toList).toList := by
        have := congrArg Array.toList hb
        simpa using this
      simp only [opPlain, Option.isNone_none, Bool.true_and, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, plain_emitList ix outlines bodyOps kids.toList _ (enter_iso fr hfr _) hk hb'⟩
      · unfold GfxPdf.groupCm at hm ⊢
        split
        · rfl
        · next hx =>
          rw [ite_eq_right hx] at hm
          simp only [Option.map_some, Option.some.injEq] at hm
          simp only [Option.all_some, decide_eq_true_eq]
          rw [hm, lift_eq fr hfr]
          exact hx
      · simp only [GfxPdf.clipOpsOf, Array.all_map, Function.comp_def]
        rw [Array.all_eq_true]
        intro i hi
        have hgi : geomInked clips[i].geom = true := by
          have := Array.all_eq_true.mp hcl i hi
          simpa using this
        have hne := frameOps_ne _ (enter_iso fr hfr (GfxPdf.groupCm fr xf)) _ hgi false
        simpa [List.isEmpty_iff] using hne
  | .words _, _, _, _, _ => rfl
  | .use _ _, _, _, hn, _ => by simp [nodePlain] at hn
  | .stamp _ _ _ _, _, _, hn, _ => by simp [nodePlain] at hn
  | .image _ _, _, _, hn, _ => by simp [nodePlain] at hn
  | .label l, _, _, _, _ => nomatch l

theorem plain_emitList (ix : GfxPdf.Request → Nat) (outlines : Array (Array Subpath))
    (bodyOps : Array (Array Pdf.ContentOp)) :
    ∀ (l : List (Node Empty)) (fr : GfxPdf.Frame), (fr.iso = some isoId ∨ fr.iso = none) → nodesPlain l = true →
      opsBack (GfxPdf.emitList ix noLabels outlines bodyOps fr #[] l).toList =
        (GfxPdf.emitList ix noLabels outlines bodyOps fr #[] l).toList →
      opsPlain (GfxPdf.emitList ix noLabels outlines bodyOps fr #[] l).toList = true
  | [], _, _, _, _ => rfl
  | n :: rest, fr, hfr, hn, hfix => by
    simp only [nodesPlain, Bool.and_eq_true] at hn
    simp only [GfxPdf.emitList] at hfix ⊢
    rw [GfxPdf.emitList_acc, Array.toList_append] at hfix ⊢
    obtain ⟨h1, h2⟩ := fixed_append _ _ hfix
    rw [opsPlain_append, plain_emitOne ix outlines bodyOps n fr hfr hn.1 h1,
      plain_emitList ix outlines bodyOps rest fr hfr hn.2 h2]
    rfl

end

public theorem readback_id (cx : Ctx) (ix : GfxPdf.Request → Nat) (fig : Figure Empty)
    (hp : nodesPlain fig.nodes.toList = true)
    (hg : (opsBack (GfxPdf.emit ix noLabels isoId fig).toList).toArray = GfxPdf.emit ix noLabels isoId fig) :
    (readStream cx (Pdf.render (GfxPdf.emit ix noLabels isoId fig)).toUTF8).losses = #[] ∧
      (readStream cx (Pdf.render (GfxPdf.emit ix noLabels isoId fig)).toUTF8).marks.map markScreen =
        fig.marks.map markScreen := by
  have hfix : opsBack (GfxPdf.emit ix noLabels isoId fig).toList = (GfxPdf.emit ix noLabels isoId fig).toList := by
    have := congrArg Array.toList hg
    rwa [List.toList_toArray] at this
  have hplain : opsPlain (GfxPdf.emit ix noLabels isoId fig).toList = true := by
    unfold GfxPdf.emit at hfix ⊢
    exact plain_emitList ix fig.outlines _ fig.nodes.toList _ (Or.inl rfl) hp hfix
  obtain ⟨hl, hm⟩ := readback_exact cx _ hplain
  refine ⟨hl, ?_⟩
  rw [hm, hg, GfxPdf.marks_projects ix _ (fun _ l => nomatch l) isoId fig]

end LeanTex.Core.PdfGfx
