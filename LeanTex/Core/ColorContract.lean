module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! The PDF colour printer's injectivity, off the import chain.

These contracts read the printer through its private implementation view.
The separator proof follows decimal digit membership and applies to every
input, including values the printer clamps. Neither contract is needed by
the renderer, so the default build checks them outside its import chain. -/

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

end LeanTex.Core.Ir
