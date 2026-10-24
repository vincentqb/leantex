module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! The PDF colour printer's injectivity and spelling, in a leaf off the import chain. -/

namespace LeanTex.Core.Ir

public theorem Color.pdfMilli_no_space (v : Nat) :
    (pdfMilli v).toList.all (· != ' ') = true := by
  unfold pdfMilli
  dsimp only
  split
  · decide
  split
  · decide
  simp only [String.toList_append, String.toList_ofList, List.all_append,
    List.all_reverse, Bool.and_eq_true]
  constructor
  · decide
  rw [List.all_eq_true]
  intro c hc
  have hm := List.mem_reverse.mp (List.dropWhile_subset _ hc)
  rcases List.mem_append.mp hm with hm | hm
  · have hz := (List.mem_replicate.mp hm).2
    subst c
    decide
  · simp only [bne_iff_ne]
    intro hspace
    subst c
    have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm
    contradiction

private theorem sep_inj (a a' r r' : List Char)
    (ha : a.all (· != ' ') = true) (ha' : a'.all (· != ' ') = true)
    (h : a ++ ' ' :: r = a' ++ ' ' :: r') : a = a' ∧ r = r' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons c cs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      simp [← h.1] at ha'
  | cons c cs ih =>
    cases a' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      simp [h.1] at ha
    | cons c' cs' =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [List.all_cons, Bool.and_eq_true] at ha ha'
      have := ih cs' ha.2 ha'.2 h.2
      exact ⟨by rw [h.1, this.1], this.2⟩

public theorem Color.pdfComponents_inj (a b : Color) (h : a.pdfComponents = b.pdfComponents) :
    a.r = b.r ∧ a.g = b.g ∧ a.b = b.b := by
  have hl := congrArg String.toList h
  have hs : " ".toList = [' '] := rfl
  simp only [pdfComponents, String.toList_append, List.append_assoc, hs,
    List.singleton_append] at hl
  have ns (v : UInt8) := pdfMilli_no_space (milli v)
  obtain ⟨h1, hl⟩ := sep_inj _ _ _ _ (ns a.r) (ns b.r) hl
  obtain ⟨h2, h3⟩ := sep_inj _ _ _ _ (ns a.g) (ns b.g) hl
  have dec (x y : UInt8) (e : (pdfMilli (milli x)).toList = (pdfMilli (milli y)).toList) :
      x = y := by
    have e' := congrArg decodeMilli (String.ext e)
    rw [pdfMilli_decode _ (milli_lt x), pdfMilli_decode _ (milli_lt y)] at e'
    exact milli_inj _ _ e'
  exact ⟨dec _ _ h1, dec _ _ h2, dec _ _ h3⟩

public theorem Color.milli_eq (v : UInt8) : milli v = (v.toNat * 1000 + 127) / 255 := by
  unfold milli; rfl

public theorem Color.pdfMilli_zero : pdfMilli 0 = "0" := by
  unfold pdfMilli; rfl

public theorem Color.pdfMilli_thousand : pdfMilli 1000 = "1" := by
  unfold pdfMilli; rfl

private theorem pad3 (v : Nat) (h1 : v < 1000) :
    List.replicate (3 - (Nat.toDigits 10 v).length) '0' ++ Nat.toDigits 10 v = Dim.kDigits 3 v := by
  simp only [Dim.kDigits, List.nil_append, List.singleton_append]
  by_cases hten : v < 10
  · rw [Nat.toDigits_of_lt_base hten]
    have h1 : v / 10 / 10 = 0 := by omega
    have h2 : v / 10 % 10 = 0 := by omega
    have h3 : v % 10 = v := by omega
    simp [h1, h2, h3]
  · rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v)]
    by_cases hh : v < 100
    · rw [Nat.toDigits_of_lt_base (by omega : v / 10 < 10)]
      have h1 : v / 10 / 10 = 0 := by omega
      have h2 : v / 10 % 10 = v / 10 := by omega
      simp [h1, h2]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v / 10),
        Nat.toDigits_of_lt_base (by omega : v / 10 / 10 < 10)]
      have h1 : v / 10 / 10 % 10 = v / 10 / 10 := by omega
      simp [h1]

public theorem Color.pdfMilli_frac (v : Nat) (h0 : 0 < v) (h1 : v < 1000) :
    pdfMilli v = "0." ++ String.ofList (Dim.fracDigits 3 v) := by
  have hmin : min v 1000 = v := Nat.min_eq_left (by omega)
  have hz : (v == 0) = false := by simp; omega
  have hu : (v == 1000) = false := by simp; omega
  simp only [pdfMilli, hmin, hz, hu, Bool.false_eq_true, ↓reduceIte, Dim.fracDigits, pad3 v h1]

public theorem Color.pdfFill_plain (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfFill = c.pdfComponents ++ " rg" := by
  simp only [pdfFill, hm, hc]
  rfl

public theorem Color.pdfFill_eq (c : Color) : c.pdfFill =
    match c.pdfModel with
    | some (.rgb r g b) => r ++ " " ++ g ++ " " ++ b ++ " rg"
    | some (.gray v) => v ++ " g"
    | some (.cmyk cy m y k) => cy ++ " " ++ m ++ " " ++ y ++ " " ++ k ++ " k"
    | some (.separation i t) =>
      "/" ++ PdfLex.escapeName i.resKey ++ " cs " ++ Dim.ratString t.num t.den ++ " scn"
    | none =>
      match c.cmyk with
      | some (cy, m, y, k) =>
        pdfMilli cy ++ " " ++ pdfMilli m ++ " " ++ pdfMilli y ++ " " ++ pdfMilli k ++ " k"
      | none => c.pdfComponents ++ " rg" := by
  unfold pdfFill
  cases h : c.pdfModel with
  | none =>
    cases h' : c.cmyk with
    | none => rfl
    | some q => obtain ⟨cy, m, y, k⟩ := q; rfl
  | some p => cases p <;> rfl

public theorem Color.pdfStroke_eq (c : Color) : c.pdfStroke =
    match c.pdfModel with
    | some (.rgb r g b) => r ++ " " ++ g ++ " " ++ b ++ " RG"
    | some (.gray v) => v ++ " G"
    | some (.cmyk cy m y k) => cy ++ " " ++ m ++ " " ++ y ++ " " ++ k ++ " K"
    | some (.separation i t) =>
      "/" ++ PdfLex.escapeName i.resKey ++ " CS " ++ Dim.ratString t.num t.den ++ " SCN"
    | none =>
      match c.cmyk with
      | some (cy, m, y, k) =>
        pdfMilli cy ++ " " ++ pdfMilli m ++ " " ++ pdfMilli y ++ " " ++ pdfMilli k ++ " K"
      | none => c.pdfComponents ++ " RG" := by
  unfold pdfStroke
  cases h : c.pdfModel with
  | none =>
    cases h' : c.cmyk with
    | none => rfl
    | some q => obtain ⟨cy, m, y, k⟩ := q; rfl
  | some p => cases p <;> rfl

public theorem Color.pdfStroke_plain (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfStroke = c.pdfComponents ++ " RG" := by
  simp only [pdfStroke, hm, hc]
  rfl

end LeanTex.Core.Ir
