module

public import LeanTex.Core.PdfLexProof
import all LeanTex.Core.PdfLex
import LeanTex.Core.LoopProgress

namespace LeanTex.Core.PdfLex

private theorem char_byte_exact (n : Nat) (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp only [Char.ofNat, dite_eq_left hv, Char.ofNatAux, Char.toNat, UInt32.toNat, BitVec.toNat_ofNatLT]

private theorem hexChar_nat (n : Nat) : (hexChar n).toNat = if n%16<10 then 48+n%16 else 55+n%16 := by
  unfold hexChar
  dsimp only
  split <;> apply char_byte_exact <;> omega

private theorem hexChar_value (n : Nat) : hexVal (hexChar n).toNat = some (n%16) := by
  rw [hexChar_nat]
  have hm := Nat.mod_lt n (by omega : 0<16)
  by_cases hn : n%16<10
  · rw [ite_eq_left hn]
    simp only [hexVal, show (48 ≤ 48+n%16 && 48+n%16 ≤ 57) = true by simp; omega, ↓reduceIte]
    simp only [Nat.add_sub_cancel_left]
  · rw [ite_eq_right hn]
    simp only [hexVal, show (48 ≤ 55+n%16 && 55+n%16 ≤ 57) = false by simp; omega,
      show (65 ≤ 55+n%16 && 55+n%16 ≤ 70) = true by simp; omega, ↓reduceIte]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]

private theorem keep_char (c : Char) (h : (c.isAlphanum || c == '-' || c == '.') = true) :
    c.toNat < 128 ∧ isWs c.toNat = false ∧ isDelim c.toNat = false ∧ c.toNat ≠ 35 := by
  simp only [Bool.or_eq_true, beq_iff_eq, Char.isAlphanum, Char.isAlpha,
    Char.isUpper, Char.isLower, Char.isDigit, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, UInt32.le_iff_toNat_le, ge_iff_le] at h
  simp only [isWs, isDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  change ((((65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122)) ∨
    (48 ≤ c.toNat ∧ c.toNat ≤ 57)) ∨ c = '-') ∨ c = '.' at h
  rcases h with (((h|h)|h)|h)|h
  · omega
  · omega
  · omega
  · subst c; decide
  · subst c; decide

/-- ISO 32000-2 §7.3.5 byte escaping. The byte bound is imposed on the
original name by the round-trip contract, not by the writer. -/
public def nameChars (c : Char) : List Char :=
  if c.isAlphanum || c == '-' || c == '.' then [c]
  else ['#', hexChar (c.toNat / 16), hexChar c.toNat]

public theorem nameChars_nonempty (c : Char) : (nameChars c).length > 0 := by
  unfold nameChars
  split <;> simp

public theorem nameChars_ascii (c : Char) : ∀ d ∈ nameChars c, d.toNat < 128 := by
  unfold nameChars
  split
  · intro d hd; simp only [List.mem_singleton] at hd; subst d
    exact (keep_char c (by assumption)).1
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl|rfl|rfl
    · decide
    · rw [hexChar_nat]; split <;> omega
    · rw [hexChar_nat]; split <;> omega

private theorem escapeLoop (cs : List Char) (out : String) :
    (forIn cs out (fun c out => if c.isAlphanum || c == '-' || c == '.' then pure (.yield (out.push c))
      else pure (.yield (out ++ "#" ++ String.ofList [hexChar (c.toNat / 16), hexChar c.toNat]))) : Id String).run
      = out ++ String.ofList (cs.flatMap nameChars) := by
  induction cs generalizing out with
  | nil => simp
  | cons c cs ih =>
    rw [List.forIn_cons]
    simp only [pure, Id.run] at ih ⊢
    split <;> simp only [bind] <;> rw [ih]
    all_goals simp only [List.flatMap_cons, String.ofList_append, nameChars,
      String.push_eq_append, String.ofList_cons, String.ofList_nil,
      String.append_empty, String.append_assoc]
    all_goals simp_all only [Bool.false_eq_true, ↓reduceIte, String.ofList_cons, String.ofList_nil,
      String.append_empty, String.append_assoc]
    all_goals rfl

public theorem escapeName_exact (s : String) (hne : s ≠ "") :
    escapeName s = String.ofList (s.toList.flatMap nameChars) := by
  have hcs : s.toList ≠ [] := by simpa using hne
  have hc : s.toList.flatMap nameChars ≠ [] := by
    cases h : s.toList with
    | nil => exact (hcs h).elim
    | cons c cs =>
      simp only [List.flatMap_cons]
      intro hn
      have hn := List.append_eq_nil_iff.mp hn
      have hlen := nameChars_nonempty c
      simp [hn.1] at hlen
  unfold escapeName
  simp only [Id.run, bind, pure]
  have hh := escapeLoop s.toList ""
  simp only [Id.run, pure] at hh
  rw [hh]
  simp [hc]

private theorem nameStep_exact {b : ByteArray} {i : Nat} (c : Char)
    (h : Span b i ((nameChars c).map Char.toNat)) (hc : c.toNat < 256) (out : String) :
    nameStep b ⟨i,out⟩ = .yield ⟨i+(nameChars c).length,out.push c⟩ := by
  unfold nameChars at h ⊢
  split at h
  · rename_i hk
    have hp := keep_char c hk
    simp only [hk, ↓reduceIte]
    simp [nameStep, h.head, hp.2.1, hp.2.2.1, hp.2.2.2, Char.ofNat_toNat,
      show c.toNat ≠ 256 by omega]
  · rename_i hk
    simp only [hk]
    have h0 := h.head
    have h1 := h.tail.head
    have h2 := h.tail.tail.head
    have hv : c.toNat / 16 % 16 * 16 + c.toNat % 16 = c.toNat := by
      have hdiv : c.toNat / 16 < 16 := Nat.div_lt_of_lt_mul hc
      rw [Nat.mod_eq_of_lt hdiv]
      omega
    have h2' : at? b (i+2) = (hexChar c.toNat).toNat := by simpa [Nat.add_assoc] using h2
    simp [nameStep, h0, h1, h2', isWs, isDelim, hexChar_value, hv]

private theorem nameSteps_stops {b : ByteArray} {i : Nat} {cs : List Char}
    (h : Span b i ((cs.flatMap nameChars).map Char.toNat))
    (hc : ∀ c ∈ cs, c.toNat < 256)
    (he : at? b (i+(cs.flatMap nameChars).length) = 256 ∨
      isWs (at? b (i+(cs.flatMap nameChars).length)) = true ∨
      isDelim (at? b (i+(cs.flatMap nameChars).length)) = true) (out : String) :
    Loop.Stops (fun s => pure (nameStep b s)) (TextState.mk i out) (cs.length+1)
      (TextState.mk (i+(cs.flatMap nameChars).length) (out ++ String.ofList cs)) := by
  induction cs generalizing i out with
  | nil =>
    apply Loop.Stops.done
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at he ⊢
    have hh : (at? b i == 256 || isWs (at? b i) || isDelim (at? b i)) = true := by simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using he
    simp only [nameStep, hh, ↓reduceIte, String.ofList_nil, String.append_empty, Id.run, pure]
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.map_append] at h
    have hs := nameStep_exact c h.append_left (hc c (by simp)) out
    have ht := ih (by simpa using h.append_right) (fun d hd => hc d (by simp [hd]))
      (by simpa [List.flatMap_cons, Nat.add_assoc] using he) (out.push c)
    have hh := Loop.Stops.yield (step := fun s => pure (nameStep b s)) hs ht
    simpa only [List.flatMap_cons, List.length_cons, List.length_append, Nat.add_assoc, String.push_eq_append,
      String.ofList_cons, String.append_assoc] using hh

public theorem parseName_exact {b : ByteArray} {i : Nat} {s : String}
    (h : Span b (i+1) ((s.toList.flatMap nameChars).map Char.toNat))
    (hc : ∀ c ∈ s.toList, c.toNat < 256)
    (he : at? b (i+1+(s.toList.flatMap nameChars).length) = 256 ∨
      isWs (at? b (i+1+(s.toList.flatMap nameChars).length)) = true ∨
      isDelim (at? b (i+1+(s.toList.flatMap nameChars).length)) = true) :
    parseName b i = (s,i+1+(s.toList.flatMap nameChars).length) := by
  have hn : s.toList.length ≤ (s.toList.flatMap nameChars).length := by
    generalize s.toList = cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have := nameChars_nonempty c
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega
  have hs := Loop.forIn_range_stops_exact (nameSteps_stops h hc he "") (b.size+1)
    (by have := h.bound; simp only [List.length_map] at this; omega)
  unfold parseName
  rw [hs]
  simp

/-- The actual name writer and decoder are inverses on nonempty byte-valued
names. Unicode scalars above 255 are outside this byte codec. -/
public theorem parseName_escapeName_id (s : String) (hne : s ≠ "")
    (hc : ∀ c ∈ s.toList, c.toNat < 256) :
    parseName ("/" ++ escapeName s).toUTF8 0 =
      (s, ("/" ++ escapeName s).toUTF8.size) := by
  rw [escapeName_exact s hne]
  let cs := s.toList.flatMap nameChars
  change parseName ("/" ++ String.ofList cs).toUTF8 0 =
    (s, ("/" ++ String.ofList cs).toUTF8.size)
  have ha : ∀ c ∈ ('/' :: cs), c.toNat < 128 := by
    intro c h
    rcases List.mem_cons.mp h with rfl | h
    · decide
    · obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp h
      exact nameChars_ascii d c hd
  have hslash : String.singleton '/' = "/" := by decide
  have hs := Span.of_ascii ByteArray.empty ByteArray.empty ('/' :: cs) ha
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    String.ofList_cons, hslash, List.map_cons] at hs
  have hb : ("/" ++ String.ofList cs).toUTF8.size = 1+cs.length := by
    rw [← hslash, ← String.ofList_cons]
    rw [ascii_utf8 _ ha]
    simp [Nat.add_comm]
  have hr := parseName_exact hs.tail hc
    (Or.inl (at?_ge _ _ (by rw [hb]; change 1+cs.length ≤ 0+1+cs.length; omega)))
  change parseName ("/" ++ String.ofList cs).toUTF8 0 = (s, 0+1+cs.length) at hr
  simpa only [Nat.zero_add, hb] using hr

end LeanTex.Core.PdfLex
