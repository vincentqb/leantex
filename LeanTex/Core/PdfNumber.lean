module

import Init.Data.Nat.ToString
import Init.Data.Int.ToString
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Lemmas.Pattern.TakeDrop.Char
import Init.Data.String.Lemmas.Pattern.Find.Char
import all Init.Data.String.Slice
import all Init.Data.String.Search

namespace LeanTex.Core.PdfRead.Number

public theorem nat_chars (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  intro c hc
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc

public theorem nat_nonempty (n : Nat) : (toString n).toList ≠ [] := by simp

public theorem int_chars (n : Int) :
    ∀ c ∈ (toString n).toList, c.isDigit = true ∨ c = '-' := by
  cases n with
  | ofNat n =>
    simp only [Int.toString_eq_repr, Int.repr_eq_ite]
    exact fun c hc => Or.inl (nat_chars n c hc)
  | negSucc n =>
    have hs : toString (Int.negSucc n) = "-" ++ toString (n+1) := by
      simp [Int.toString_eq_repr, Int.repr_eq_ite]
    rw [hs]
    intro c hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Or.inr (by simpa using hc)
    · exact Or.inl (nat_chars (n+1) c hc)

public theorem int_nonempty (n : Int) : (toString n).toList ≠ [] := by
  cases n <;> simp [Int.toString_eq_repr, Int.repr_eq_ite]

public theorem int_noDot (n : Int) : (toString n).contains '.' = false := by
  rw [String.contains_char_eq]
  apply decide_eq_false
  intro h
  have hh := int_chars n '.' h
  simp [Char.isDigit] at hh

private def natStep (c : Char) (s : Option Bool × Bool) : Id (ForInStep (Option Bool × Bool)) :=
  if c = '_' then
    if !s.2 then pure (.done (some false, s.2)) else pure (.yield (none, false))
  else if c.isDigit then pure (.yield (none, true)) else pure (.done (some false, s.2))

private theorem natScan (cs : List Char) (hd : ∀ c ∈ cs, c.isDigit = true) (b : Bool) :
    (forIn cs (none, b) natStep : Id _).run = (none, if cs.isEmpty then b else true) := by
  induction cs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    have hc := hd c (by simp)
    have hne : c ≠ '_' := by rintro rfl; simp [Char.isDigit] at hc
    simp only [List.forIn_cons, natStep, hne, ↓reduceIte, hc]
    simpa only [Id.run, bind, pure, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ite_self] using ih (fun c hm => hd c (by simp [hm])) true

private theorem slice_isNat (s : String.Slice) (hd : ∀ c ∈ s.copy.toList, c.isDigit = true)
    (hn : s.copy.toList ≠ []) : s.isNat = true := by
  simp only [String.Slice.isNat, String.Slice.forIn_eq_forIn_toList]
  simp only [Id.run, bind, pure]
  have h := natScan s.copy.toList hd false
  unfold natStep at h
  simp only [Id.run, pure] at h
  rw [h]
  simp [hn]

public theorem digits_value (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun a c => a * 10 + (c.toNat - 48)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · simp [Nat.toDigits_of_lt_base h, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · rw [Nat.toDigits_of_base_le (by omega) (by omega), List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih (n / 10) (Nat.div_lt_self (by omega) (by omega)),
        Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt n (by omega))]
      omega

private theorem slice_nat (s : String.Slice) (n : Nat) (hs : s.copy = toString n) :
     s.toNat? = some n := by
   have hd : ∀ c ∈ s.copy.toList, c.isDigit = true := by
     intro c hc
     rw [hs, Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
     exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
   have hn : s.copy.toList ≠ [] := by simp [hs]
   rw [String.Slice.toNat?, slice_isNat s hd hn]
   simp only [↓reduceIte, String.Slice.foldl_eq_foldl_toList]
   have he : (s.copy.toList.foldl
       (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0) =
       s.copy.toList.foldl (fun n c => n * 10 + (c.toNat - 48)) 0 := by
     generalize s.copy.toList = cs at hd ⊢
     generalize (0 : Nat) = acc
     induction cs generalizing acc with
     | nil => rfl
     | cons c cs ih =>
       have hc := hd c (by simp)
       have hne : c ≠ '_' := by rintro rfl; simp [Char.isDigit] at hc
       simp only [List.foldl_cons, hne, ↓reduceIte]
       exact ih (fun c hm => hd c (by simp [hm])) _
   rw [he, hs, Nat.toString_eq_ofList_toDigits, String.toList_ofList, digits_value]

private theorem slice_nat_int (s : String.Slice) (n : Nat) (hs : s.copy = toString n) :
     s.toInt? = some (Int.ofNat n) := by
   have hprefix : s.dropPrefix? '-' = none := by
     rw [String.Slice.dropPrefix?_eq_none_iff, String.Slice.startsWith_char_eq_head?]
     apply Bool.eq_false_iff.mpr
     intro h
     have hm : '-' ∈ s.copy.toList := List.mem_of_head? (by simpa using h)
     rw [hs, Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hm
     have := Nat.isDigit_of_mem_toDigits (by omega) (by omega) hm
     contradiction
   rw [String.Slice.toInt?, hprefix, slice_nat s n hs]
   rfl

private theorem slice_neg_int (s : String.Slice) (n : Nat) (hs : s.copy = "-" ++ toString n) :
     s.toInt? = some (Int.negOfNat n) := by
   cases he : s.dropPrefix? '-' with
   | none =>
     rw [String.Slice.dropPrefix?_eq_none_iff, String.Slice.startsWith_char_eq_head?] at he
     simp [hs, String.toList_append] at he
   | some rest =>
     have heq := String.Slice.eq_append_of_dropPrefix?_char_eq_some he
     have hr : rest.copy = toString n := by
       rw [hs] at heq
       exact (String.append_right_inj "-").mp heq.symm
     simp only [String.Slice.toInt?, he, slice_nat rest n hr, Option.map_some]

/-- Decimal integer spellings round-trip for every magnitude and sign.
The proof follows the standard library digit generator and scanner; it
does not bound the integer or evaluate a sample. -/
public theorem int_toString_id (n : Int) : (toString n).toInt? = some n := by
   cases n with
   | ofNat n =>
     simp only [Int.toString_eq_repr, Int.repr_eq_ite, String.toInt?]
     exact slice_nat_int _ n (by simp)
   | negSucc n =>
     have hs : toString (Int.negSucc n) = "-" ++ toString (n+1) := by
       simp [Int.toString_eq_repr, Int.repr_eq_ite]
     rw [hs, String.toInt?]
     exact slice_neg_int _ (n+1) (by simp)

end LeanTex.Core.PdfRead.Number
