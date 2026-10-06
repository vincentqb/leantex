import LeanTex.Core.PdfLex
import LeanTex.Core.LoopProgress
import LeanTex.Core.PdfNumber
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Lemmas.Basic

namespace LeanTex.Core.PdfLex

/-- Byte lists are used only to state source spans; the scanner and writer
continue to operate on `ByteArray`. -/
def octets (b : ByteArray) : List Nat := b.data.toList.map UInt8.toNat

@[simp] theorem octets_length (b : ByteArray) : (octets b).length = b.size := by
  simp [octets]

@[simp] theorem octets_append (a b : ByteArray) : octets (a++b) = octets a ++ octets b := by
  simp [octets, ByteArray.data_append]

@[simp] theorem octets_push (a : ByteArray) (c : UInt8) :
    octets (a.push c) = octets a ++ [c.toNat] := by
  simp [octets, ByteArray.data_push]

@[simp] theorem octets_empty : octets ByteArray.empty = [] := rfl

theorem at?_lt (b : ByteArray) (i : Nat) (h : i < b.size) :
    at? b i = b[i].toNat := by simp [at?, getElem?_pos b i h]

theorem at?_ge (b : ByteArray) (i : Nat) (h : b.size ≤ i) :
    at? b i = 256 := by simp [at?, getElem?_neg b i (by omega : ¬i < b.size)]

theorem at?_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    at? (a ++ b) i = at? a i := by
  rw [at?_lt _ _ (by simp; omega), at?_lt _ _ h, ByteArray.getElem_append_left h]

theorem at?_append_right (a b : ByteArray) (i : Nat) :
    at? (a ++ b) (a.size + i) = at? b i := by
  by_cases h : i < b.size
  · rw [at?_lt _ _ (by simp; omega), at?_lt _ _ h,
      ByteArray.getElem_append_right (by omega)]
    simp
  · rw [at?_ge _ _ (by simp; omega), at?_ge _ _ (by omega)]

theorem ascii_utf8 (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    (String.ofList cs).toUTF8 = (cs.map Char.toUInt8).toByteArray := by
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c.utf8Size = 1 := by
      rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
      exact Nat.le_of_lt_succ (h c (by simp))
    rw [List.utf8Encode_cons, List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton hc, ih (fun d hd => h d (by simp [hd]))]
    rw [← List.toByteArray_append]
    rfl

theorem octets_ascii (cs : List Char) (h : ∀ c ∈ cs, c.toNat < 128) :
    octets (String.ofList cs).toUTF8 = cs.map Char.toNat := by
  rw [ascii_utf8 cs h]
  simp only [octets, List.data_toByteArray, List.toList_toArray, List.map_map]
  apply List.map_congr_left
  intro c hc
  change c.toNat % 256 = c.toNat
  exact Nat.mod_eq_of_lt (by have := h c hc; omega)

/-- A source span describes its bytes and bounds, independently of any
scanner or parsed result. -/
structure Span (b : ByteArray) (i : Nat) (cs : List Nat) : Prop where
  bound : i + cs.length ≤ b.size
  byte : ∀ j, (h : j < cs.length) → at? b (i + j) = cs[j]

theorem Span.nil (b : ByteArray) (i : Nat) (hi : i ≤ b.size) : Span b i [] :=
  ⟨by simpa using hi, by simp⟩

theorem Span.head {b i c cs} (h : Span b i (c :: cs)) : at? b i = c := by
  exact h.byte 0 (by simp)

theorem Span.tail {b i c cs} (h : Span b i (c :: cs)) : Span b (i+1) cs := by
  refine ⟨by have := h.bound; simp only [List.length_cons] at this; omega, ?_⟩
  intro j hj
  have he := h.byte (j+1) (by simp; omega)
  change at? b (i + (j+1)) = cs[j] at he
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem Span.append_left {b i cs ds} (h : Span b i (cs ++ ds)) : Span b i cs := by
  refine ⟨by have := h.bound; simp at this; omega, ?_⟩
  intro j hj
  have he := h.byte j (by simp; omega)
  rw [List.getElem_append_left hj] at he
  exact he

theorem Span.append_right {b i cs ds} (h : Span b i (cs ++ ds)) : Span b (i+cs.length) ds := by
  refine ⟨by simpa [Nat.add_assoc] using h.bound, ?_⟩
  intro j hj
  have he := h.byte (cs.length+j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at he
  simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using he

theorem Span.of_bytes (pre raw post : ByteArray) :
    Span (pre ++ raw ++ post) pre.size (raw.data.toList.map UInt8.toNat) := by
  refine ⟨by simp only [ByteArray.size_append, List.length_map, Array.length_toList, ByteArray.size_data]; omega, ?_⟩
  intro j hj
  have hj' : j < raw.size := by simpa only [List.length_map, Array.length_toList, ByteArray.size_data] using hj
  rw [at?_append_left _ _ _ (by simp; omega), at?_append_right, at?_lt _ _ hj']
  simp [ByteArray.getElem_eq_getElem_data]

/-- Extracting a bounded span preserves every source byte. -/
theorem Span.extract_exact {b raw : ByteArray} {i : Nat}
    (h : Span b i (raw.data.toList.map UInt8.toNat)) :
    b.extract i (i+raw.size) = raw := by
  have hb : i+raw.size ≤ b.size := by simpa using h.bound
  apply ByteArray.ext_getElem (by simp [Nat.min_eq_left hb])
  intro j hj hj'
  rw [ByteArray.getElem_extract hj]
  apply UInt8.toNat_inj.mp
  have he := h.byte j (by simpa using hj')
  rw [at?_lt _ _ (by omega)] at he
  simpa [ByteArray.getElem_eq_getElem_data] using he

theorem Span.of_ascii (pre post : ByteArray) (cs : List Char)
    (h : ∀ c ∈ cs, c.toNat < 128) :
    Span (pre ++ (String.ofList cs).toUTF8 ++ post) pre.size (cs.map Char.toNat) := by
  rw [ascii_utf8 cs h]
  have hh := Span.of_bytes pre (String.ofList cs).toUTF8 post
  rw [ascii_utf8 cs h] at hh
  suffices ((cs.map Char.toUInt8).toByteArray.data.toList.map UInt8.toNat) = cs.map Char.toNat by
    rw [this] at hh
    exact hh
  simp only [List.data_toByteArray, List.toList_toArray, List.map_map]
  apply List.map_congr_left
  intro c hc
  change c.toNat % 256 = c.toNat
  exact Nat.mod_eq_of_lt (by have := h c hc; omega)
theorem numberStep_stops {b : ByteArray} {i : Nat} {cs : List Char}
    (h : Span b i (cs.map Char.toNat))
    (hc : ∀ c ∈ cs, numByte c.toNat = true)
    (he : numByte (at? b (i+cs.length)) = false) (out : String) :
    Loop.Stops (fun s => pure (numberStep b s)) (TextState.mk i out) (cs.length+1)
      (TextState.mk (i+cs.length) (out ++ String.ofList cs)) := by
  induction cs generalizing i out with
  | nil =>
    apply Loop.Stops.done
    simp only [numberStep, Id.run, pure, List.length_nil, Nat.add_zero,
      String.ofList_nil, String.append_empty] at he ⊢
    simp [he]
  | cons c cs ih =>
    have hs : numberStep b ⟨i,out⟩ = .yield ⟨i+1,out.push c⟩ := by
      have hh := h.head
      simp only [numberStep, hh, hc c (by simp), ↓reduceIte, Char.ofNat_toNat]
    have ht := ih h.tail (fun d hd => hc d (by simp [hd]))
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he)
      (out.push c)
    have hh := Loop.Stops.yield (step := fun s => pure (numberStep b s)) hs ht
    simpa only [List.length_cons, String.ofList_cons, String.push_eq_append,
      String.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem scanNumber_exact {b : ByteArray} {i : Nat} {cs : List Char}
    (h : Span b i (cs.map Char.toNat))
    (hc : ∀ c ∈ cs, numByte c.toNat = true)
    (he : numByte (at? b (i+cs.length)) = false) :
    scanNumber b i = (String.ofList cs, i+cs.length) := by
  have hs := Loop.forIn_range_stops_exact (numberStep_stops h hc he "") (b.size+1)
    (by have := h.bound; simp only [List.length_map] at this; omega)
  unfold scanNumber
  rw [hs]
  simp

theorem skipWs_fixed_point {b : ByteArray} {i : Nat}
    (hw : isWs (at? b i) = false) (hc : at? b i ≠ 37) : skipWs b i = i := by
  apply Loop.forIn_range_stops_exact (n := 1) (budget := b.size+1)
  · apply Loop.Stops.done
    simp [skipStep, hw, hc]
  · omega

theorem skipWs_whitespace_exact {b : ByteArray} {i : Nat}
    (h : isWs (at? b i) = true) (hw : isWs (at? b (i+1)) = false)
    (hc : at? b (i+1) ≠ 37) (hi : i < b.size) : skipWs b i = i+1 := by
  apply Loop.forIn_range_stops_exact (n := 2) (budget := b.size+1)
  · apply Loop.Stops.yield (b := i+1)
    · simp [skipStep, h]
    · apply Loop.Stops.done
      simp [skipStep, hw, hc]
  · omega

theorem skipWs_one_exact {b : ByteArray} {i : Nat}
    (h : at? b i = 32) (hw : isWs (at? b (i+1)) = false)
    (hc : at? b (i+1) ≠ 37) (hi : i < b.size) : skipWs b i = i+1 :=
  skipWs_whitespace_exact (by rw [h]; rfl) hw hc hi

theorem uintStep_stops {b : ByteArray} {i : Nat} {cs : List Char}
    (h : Span b i (cs.map Char.toNat))
    (hc : ∀ c ∈ cs, c.isDigit = true)
    (he : ¬ (48 ≤ at? b (i+cs.length) ∧ at? b (i+cs.length) ≤ 57))
    (v : Nat) (seen : Bool) :
    Loop.Stops (fun s => pure (uintStep b s)) (UIntState.mk i v seen) (cs.length+1)
      (UIntState.mk (i+cs.length)
        (cs.foldl (fun a c => a*10+(c.toNat-48)) v) (if cs.isEmpty then seen else true)) := by
  induction cs generalizing i v seen with
  | nil =>
    apply Loop.Stops.done
    simp only [List.length_nil, Nat.add_zero] at he
    simp [uintStep, he]
  | cons c cs ih =>
    have hd := (Char.isDigit_iff_toNat.mp (hc c (by simp)))
    have hs : uintStep b ⟨i,v,seen⟩ = .yield ⟨i+1,v*10+(c.toNat-48),true⟩ := by
      simp only [uintStep, h.head, Bool.and_eq_true, decide_eq_true_eq]
      simp only [show 48 ≤ c.toNat from hd.1, show c.toNat ≤ 57 from hd.2, and_self, ↓reduceIte]
    have ht := ih h.tail (fun d hd => hc d (by simp [hd]))
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he)
      (v*10+(c.toNat-48)) true
    have hh := Loop.Stops.yield (step := fun s => pure (uintStep b s)) hs ht
    simpa only [List.length_cons, List.foldl_cons, List.isEmpty_cons,
      Bool.false_eq_true, ↓reduceIte, ite_self,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem parseUInt_exact {b : ByteArray} {i : Nat} {cs : List Char}
    (h : Span b i (cs.map Char.toNat))
    (hc : ∀ c ∈ cs, c.isDigit = true) (hne : cs ≠ [])
    (he : ¬ (48 ≤ at? b (i+cs.length) ∧ at? b (i+cs.length) ≤ 57)) :
    parseUInt b i = some (cs.foldl (fun a c => a*10+(c.toNat-48)) 0, i+cs.length) := by
  have hs := Loop.forIn_range_stops_exact (uintStep_stops h hc he 0 false) (b.size+1)
    (by have := h.bound; simp only [List.length_map] at this; omega)
  unfold parseUInt
  rw [hs]
  simp [hne]

theorem parseUInt_none {b : ByteArray} {i : Nat}
    (he : ¬ (48 ≤ at? b i ∧ at? b i ≤ 57)) : parseUInt b i = none := by
  have hs : Loop.Stops (fun s => pure (uintStep b s)) (UIntState.mk i 0 false) 1
      (UIntState.mk i 0 false) := .done (by simp [uintStep, he])
  unfold parseUInt
  rw [Loop.forIn_range_stops_exact hs (b.size+1) (by omega)]
  rfl

/-- Every step compares the stated byte. With an exact source span the
loop cannot take its mismatch exit, and its Boolean remains true. -/
theorem keywordAt_exact {b : ByteArray} {i : Nat} {kw : String}
    (h : Span b i (octets kw.toUTF8))
    (he : at? b (i+kw.toUTF8.size) = 256 ∨
      isWs (at? b (i+kw.toUTF8.size)) = true ∨
      isDelim (at? b (i+kw.toUTF8.size)) = true) :
    keywordAt b i kw = some (i+kw.toUTF8.size) := by
  have hm := Loop.forIn_range_inv (· = true)
    (fun k s => pure (keywordStep b i kw.toUTF8 k s)) 0 kw.toUTF8.size true rfl
    (by
      intro k _ hk s _
      have hh := h.byte k (by simpa using hk)
      simp only [octets, List.getElem_map, Array.getElem_toList,
        ← ByteArray.getElem_eq_getElem_data] at hh
      simp only [keywordStep, hh, getElem?_pos kw.toUTF8 k hk, Option.getD_some,
        beq_self_eq_true, ↓reduceIte]
      rfl)
  have hb : (at? b (i+kw.toUTF8.size) == 256 ||
      isWs (at? b (i+kw.toUTF8.size)) ||
      isDelim (at? b (i+kw.toUTF8.size))) = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using he
  simp only [keywordAt, hm, hb, Bool.true_and, ↓reduceIte]

theorem keywordAt_ne {b : ByteArray} {i : Nat} {kw : String}
    (hn : 0 < kw.toUTF8.size)
    (h : at? b i ≠ (kw.toUTF8[0]?.getD 0).toNat) : keywordAt b i kw = none := by
  have hm : (forIn [0:kw.toUTF8.size] true
      (fun k s => pure (keywordStep b i kw.toUTF8 k s)) : Id Bool).run = false := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one]
    obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : kw.toUTF8.size ≠ 0)
    rw [he, List.range'_succ, List.forIn_cons]
    simp only [keywordStep, Nat.add_zero, show (at? b i == (kw.toUTF8[0]?.getD 0).toNat) = false
      from beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [keywordAt, hm, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end LeanTex.Core.PdfLex
