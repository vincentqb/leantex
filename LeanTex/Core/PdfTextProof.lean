module

public import LeanTex.Core.PdfText
public import LeanTex.Core.PdfObjProof

namespace LeanTex.Core.PdfRead

open PdfLex

private theorem literalByte_body (c : Nat) (hc : c < 256) (rest : List Nat)
    (h : LiteralBody rest) : LiteralBody (literalByte c ++ rest) := by
  unfold literalByte
  split
  · exact LiteralBody.escape hc h
  · next hd =>
    split
    · exact LiteralBody.escape (by decide) h
    · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hd
      exact LiteralBody.byte hc hd.1.1 hd.1.2 hd.2 h

private theorem flatMap_literalByte_body (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    LiteralBody (bs.flatMap literalByte) := by
  induction bs with
  | nil => exact .nil
  | cons b rest ih =>
    simp only [List.flatMap_cons]
    exact literalByte_body b (h b (by simp)) _ (ih fun x hx => h x (by simp [hx]))

private theorem strOf_octets (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    (bs.map Nat.toUInt8).map UInt8.toNat = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb : b < 256 := h b (by simp)
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih fun x hx => h x (by simp [hx])⟩
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    omega

private theorem strOf_representable (bs : List Nat) (h : ∀ b ∈ bs, b < 256)
    (hs : Obj.StringSpelling bs) : (strOf bs).Representable := by
  refine Obj.Representable.str ?_
  simpa [strOf, strOf_octets bs h] using hs

private theorem literalBytes_spelled (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    (∀ b ∈ literalBytes bs, b < 256) ∧ Obj.StringSpelling (literalBytes bs) := by
  have hb := flatMap_literalByte_body bs h
  refine ⟨fun b hb' => ?_, Obj.StringSpelling.literal hb⟩
  simp only [literalBytes, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hb'
  rcases hb' with (rfl | hb') | rfl
  · decide
  · exact hb.bytes b hb'
  · decide

/-- A byte string reads back as the one string object written. -/
public theorem literal_representable (bs : ByteArray) : (literal bs).Representable := by
  have h : ∀ b ∈ bs.data.toList.map UInt8.toNat, b < 256 := by
    intro b hb
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
    exact u.toNat_lt
  have hl := literalBytes_spelled _ h
  exact strOf_representable _ hl.1 hl.2

private theorem hexDigit_spelled (c : Char) (hc : ∃ k, c = Hex.spell true k) :
    c.toNat < 256 ∧ Hex.val? c.toNat ≠ none := by
  obtain ⟨k, rfl⟩ := hc
  refine ⟨by have := Hex.spell_ascii true k; omega, ?_⟩
  rw [Hex.val?_spell_exact]
  simp

private theorem utf16Hex_spelled (c x : Char) (hx : x ∈ (utf16Hex c).toList) :
    ∃ k, x = Hex.spell true k := by
  dsimp only [utf16Hex] at hx
  split at hx
  · exact Hex.digitList_mem (by simpa [Hex.digits] using hx)
  · simp only [Hex.digits, String.toList_append, String.toList_ofList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Hex.digitList_mem hx
    · exact Hex.digitList_mem hx

/-- A text string reads back as the one string object written. -/
public theorem textString_representable (s : String) : (textString s).Representable := by
  unfold textString textStringBytes
  split
  · next hall =>
    have h : ∀ b ∈ s.toList.map Char.toNat, b < 256 := by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      have := List.all_eq_true.mp hall c hc
      simp only [decide_eq_true_eq] at this
      omega
    have hl := literalBytes_spelled _ h
    exact strOf_representable _ hl.1 hl.2
  · have hd : ∀ x ∈ ("FEFF" ++ String.join (s.toList.map utf16Hex)).toList,
        x.toNat < 256 ∧ Hex.val? x.toNat ≠ none := by
      intro x hx
      simp only [String.toList_append, List.mem_append, String.toList_join,
        List.mem_flatMap, List.mem_map] at hx
      rcases hx with hx | ⟨_, ⟨c, _, rfl⟩, hx⟩
      · have : x = 'F' ∨ x = 'E' := by
          simp only [show "FEFF".toList = ['F', 'E', 'F', 'F'] from rfl, List.mem_cons,
            List.mem_nil_iff, or_false] at hx
          rcases hx with h | h | h | h <;> simp [h]
        rcases this with rfl | rfl <;> decide
      · exact hexDigit_spelled x (utf16Hex_spelled c x hx)
    refine strOf_representable _ ?_ (Obj.StringSpelling.hex ?_)
    · intro b hb
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | ⟨x, hx, rfl⟩) | rfl
      · decide
      · exact (hd x hx).1
      · decide
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      exact Or.inl (hd x hx).2

private theorem xmpChar_admitted (c x : Char) (hx : x ∈ xmpChar c) :
    x ≠ '<' ∧ Xml.xmlChar x.toNat = true := by
  have amp : ∀ y ∈ "&amp;".toList, y ≠ '<' ∧ Xml.xmlChar y.toNat = true := by decide
  have lt : ∀ y ∈ "&lt;".toList, y ≠ '<' ∧ Xml.xmlChar y.toNat = true := by decide
  have gt : ∀ y ∈ "&gt;".toList, y ≠ '<' ∧ Xml.xmlChar y.toNat = true := by decide
  have cr : ∀ y ∈ "&#13;".toList, y ≠ '<' ∧ Xml.xmlChar y.toNat = true := by decide
  unfold xmpChar at hx
  split at hx
  · exact amp x hx
  · split at hx
    · exact lt x hx
    · next hl =>
      split at hx
      · exact gt x hx
      · split at hx
        · exact cr x hx
        · split at hx
          · next hc =>
            obtain rfl := List.mem_singleton.mp hx
            exact ⟨by simpa using hl, hc⟩
          · simp at hx

/-- XMP character data holds no `<` and only characters XML admits. -/
public theorem xmpText_admitted (s : String) :
    ∀ x ∈ (xmpText s).toList, x ≠ '<' ∧ Xml.xmlChar x.toNat = true := by
  intro x hx
  simp only [xmpText, String.toList_ofList, List.mem_flatMap] at hx
  obtain ⟨c, _, hc⟩ := hx
  exact xmpChar_admitted c x hc

end LeanTex.Core.PdfRead
