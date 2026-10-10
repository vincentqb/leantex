module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! The PDF colour printer's injectivity and its spelling, off the import
chain.

These contracts read the printer through its private implementation view.
The separator proof follows decimal digit membership and applies to every
input, including values the printer clamps. None is needed by the renderer,
so the default build checks them outside its import chain; the figure
importer's read-back statement reads the spelling ones. -/

namespace LeanTex.Core.Ir

/-- No printed thousandth contains the separator the components are
joined with — what lets `pdfComponents_inj` split the string. -/
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

/-- Two colours never share a printed component triple unless they agree
as sRGB: the PDF twin of `cssColor_inj`, so the two backends keep apart
exactly the same inks. The CMYK rider is not determined and not claimed:
it is the `k` operator's channel (`cmyk_components_kept`), never printed
through `pdfComponents`. -/
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

/-! The printer's spelling, as a reader of the PDF meets it: a thousandth
between the two ends is a point and its digits (`Dim.fracDigits`, which
drops the trailing zeros), and a colour with no declared device model
prints its three thousandths before `rg` or `RG` — what the figure
importer reads a written colour back from. -/

/-- A channel's thousandth, as the printer computes it. -/
public theorem Color.milli_eq (v : UInt8) : milli v = (v.toNat * 1000 + 127) / 255 := by
  unfold milli; rfl

/-- The ends print as integers. -/
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

/-- A thousandth between the ends prints as a point and its digits. -/
public theorem Color.pdfMilli_frac (v : Nat) (h0 : 0 < v) (h1 : v < 1000) :
    pdfMilli v = "0." ++ String.ofList (Dim.fracDigits 3 v) := by
  have hmin : min v 1000 = v := Nat.min_eq_left (by omega)
  have hz : (v == 0) = false := by simp; omega
  have hu : (v == 1000) = false := by simp; omega
  simp only [pdfMilli, hmin, hz, hu, Bool.false_eq_true, ↓reduceIte, Dim.fracDigits, pad3 v h1]

/-- A colour with no declared device model fills with its three printed
thousandths (`pdfComponents`). -/
public theorem Color.pdfFill_plain (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfFill = c.pdfComponents ++ " rg" := by
  simp only [pdfFill, hm, hc]
  rfl

public theorem Color.pdfStroke_plain (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfStroke = c.pdfComponents ++ " RG" := by
  simp only [pdfStroke, hm, hc]
  rfl

end LeanTex.Core.Ir
