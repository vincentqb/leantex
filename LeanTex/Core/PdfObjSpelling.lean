module

public import LeanTex.Core.PdfObjProof
public import LeanTex.Core.PdfLexBoundary
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfLex
import LeanTex.Core.PdfNumber

namespace LeanTex.Core.PdfRead

open PdfLex

public theorem utf8_append (s t : String) : (s++t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append]

/-- The actual array renderer's remaining bytes, including its closer. -/
def Obj.arrayBody (xs : List Obj) : List Nat :=
  octets (Obj.renderList ByteArray.empty xs) ++ [93]

/-- The actual dictionary renderer's remaining bytes, including its closer. -/
def Obj.dictBody (es : List (String × Obj)) : List Nat :=
  octets (Obj.renderEntries ByteArray.empty es) ++ [62,62]

theorem Obj.render_arr_octets (xs : Array Obj) :
    octets (Obj.arr xs).render = 91 :: Obj.arrayBody xs.toList := by
  change octets ((Obj.renderList (ByteArray.empty.push 91) xs.toList).push 93) = _
  rw [Obj.renderList_exact]
  simp only [octets_push,
    octets_append, octets_empty, List.nil_append, Obj.arrayBody]
  rfl

theorem Obj.render_dict_octets (es : Array (String × Obj)) :
    octets (Obj.dict es).render = 60 :: 60 :: 32 :: Obj.dictBody es.toList := by
  change octets (Obj.renderEntries (ByteArray.empty ++ "<< ".toUTF8) es.toList ++ ">>".toUTF8) = _
  rw [Obj.renderEntries_exact]
  simp only [
    octets_append, octets_empty, List.nil_append, Obj.dictBody,
    String.toUTF8_eq_toByteArray]
  rfl

theorem Obj.arrayBody_nil : Obj.arrayBody [] = [93] := rfl

theorem Obj.arrayBody_single (x : Obj) :
    Obj.arrayBody [x] = octets x.render ++ [93] := rfl

theorem Obj.arrayBody_cons (x y : Obj) (xs : List Obj) :
    Obj.arrayBody (x::y::xs) = octets x.render ++ 32 :: Obj.arrayBody (y::xs) := by
  change octets (Obj.renderList (x.render.push 32) (y::xs)) ++ [93] = _
  rw [Obj.renderList_exact]
  simp only [Obj.arrayBody,
    octets_append, octets_push, List.append_assoc]
  rfl

theorem Obj.dictBody_nil : Obj.dictBody [] = [62,62] := rfl

theorem Obj.dictBody_cons (k : String) (v : Obj) (es : List (String × Obj)) :
    Obj.dictBody ((k,v)::es) =
      octets ("/" ++ escapeName k).toUTF8 ++
        32 :: (octets v.render ++ 32 :: Obj.dictBody es) := by
  change octets (Obj.renderEntries
    ((v.renderInto (ByteArray.empty ++ ("/" ++ escapeName k ++ " ").toUTF8)).push 32) es) ++
      [62,62] = _
  rw [Obj.renderEntries_exact, Obj.renderInto_exact]
  simp only [Obj.dictBody, utf8_append, ByteArray.empty_append,
    octets_append, octets_push, List.append_assoc]
  simp only [String.toUTF8_eq_toByteArray]
  rfl

theorem Obj.render_ref_octets (num gen : Nat) :
    octets (Obj.ref num gen).render =
      octets (toString num).toUTF8 ++
        32 :: (octets (toString gen).toUTF8 ++ [32,82]) := by
  simp only [Obj.render, Obj.renderInto, ByteArray.empty_append,
    utf8_append, octets_append, List.append_assoc]
  simp only [String.toUTF8_eq_toByteArray]
  rfl

public theorem numeric_octets (s : String) (hc : ∀ c ∈ s.toList, numByte c.toNat = true) :
    octets s.toUTF8 = s.toList.map Char.toNat := by
  simpa only [String.ofList_toList] using
    octets_ascii s.toList (fun c hm => (number_byte (hc c hm)).1)

public theorem numeric_size (s : String) (hc : ∀ c ∈ s.toList, numByte c.toNat = true) :
    s.toUTF8.size = s.toList.length := by
  simpa only [octets_length, List.length_map] using congrArg List.length (numeric_octets s hc)

theorem digit_numeric {c : Char} (h : c.isDigit = true) : numByte c.toNat = true := by
  have hc := Char.isDigit_iff_toNat.mp h
  simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact Or.inl (Or.inl (Or.inl hc))

public theorem nat_numeric (n : Nat) : ∀ c ∈ (toString n).toList, numByte c.toNat = true :=
  fun c hm => digit_numeric (Number.nat_chars n c hm)

theorem int_numeric (n : Int) : ∀ c ∈ (toString n).toList, numByte c.toNat = true := by
  intro c hm
  rcases Number.int_chars n c hm with hd | rfl
  · exact digit_numeric hd
  · rfl

theorem scan_numeric {b : ByteArray} {i : Nat} {s : String}
    (h : Span b i (octets s.toUTF8))
    (hc : ∀ c ∈ s.toList, numByte c.toNat = true)
    (he : EndByte (at? b (i+s.toUTF8.size))) :
    scanNumber b i = (s,i+s.toUTF8.size) := by
  rw [numeric_octets s hc] at h
  have hn := scanNumber_exact h hc
    (by simpa only [numeric_size s hc] using he.not_number)
  simpa only [String.ofList_toList, numeric_size s hc] using hn

public theorem parse_nat {b : ByteArray} {i n : Nat}
    (h : Span b i (octets (toString n).toUTF8))
    (he : EndByte (at? b (i+(toString n).toUTF8.size))) :
    parseUInt b i = some (n,i+(toString n).toUTF8.size) := by
  rw [numeric_octets _ (nat_numeric n)] at h
  have hn := parseUInt_exact h (Number.nat_chars n) (Number.nat_nonempty n)
    (by simpa only [numeric_size _ (nat_numeric n)] using not_number_not_digit he.not_number)
  rw [numeric_size _ (nat_numeric n)]
  simpa only [Nat.toString_eq_ofList_toDigits, String.toList_ofList, Number.digits_value] using hn

namespace ObjReader

/-- A token start cannot be whitespace, a comment, or the reference
marker. Unsigned lookahead at this start also cannot consume a reference.
These facts will be derived from rendered syntax, never assumed at the
public round-trip boundary. -/
public structure Start (b : ByteArray) (i : Nat) : Prop where
  whitespace : isWs (at? b i) = false
  comment : at? b i ≠ 37
  marker : at? b i ≠ 82
  reference : tryRef b i = none

public theorem Start.skip {b i} (h : Start b i) : skipWs b i = i :=
  skipWs_fixed_point h.whitespace h.comment

/-- Suffix facts for one object, including the reader's integer lookahead. -/
public structure Stop (b : ByteArray) (i : Nat) : Prop where
  boundary : EndByte (at? b i)
  marker : at? b (skipWs b i) ≠ 82
  reference : tryRef b i = none

public theorem Start.non_numeric {b i}
    (hw : isWs (at? b i) = false) (hc : at? b i ≠ 37)
    (hr : at? b i ≠ 82) (hd : ¬ (48 ≤ at? b i ∧ at? b i ≤ 57)) : Start b i := by
  refine ⟨hw,hc,hr,?_⟩
  have hs := skipWs_fixed_point hw hc
  simp only [tryRef, hs, parseUInt_none hd]
  rfl

public theorem Start.numeric {b : ByteArray} {i : Nat} {s : String}
    (h : Span b i (octets s.toUTF8))
    (hn : s.toList ≠ []) (hc : ∀ c ∈ s.toList, numByte c.toNat = true)
    (he : EndByte (at? b (i+s.toUTF8.size)))
    (hr : at? b (skipWs b (i+s.toUTF8.size)) ≠ 82) : Start b i := by
  rw [numeric_octets s hc] at h
  have hne : s.toList.map Char.toNat ≠ [] := by simpa using hn
  have hcs : ∀ c ∈ s.toList.map Char.toNat, numByte c = true := by
    intro c hm
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
    exact hc d hd
  have hp := number_byte (h.first_number hne hcs)
  refine ⟨hp.2.1,hp.2.2.1,hp.2.2.2.1,?_⟩
  exact tryRef_numeric_none h hne hcs
    (by simpa only [List.length_map, numeric_size s hc] using he)
    (by simpa only [List.length_map, numeric_size s hc] using hr)

public theorem Stop.of_start {b i} (h : Start b i) (he : EndByte (at? b i)) : Stop b i :=
  ⟨he, by simpa only [h.skip] using h.marker, h.reference⟩

public theorem Stop.whitespace {b i} (h : isWs (at? b i) = true) (hi : i < b.size)
    (hn : Start b (i+1)) : Stop b i := by
  have hs := skipWs_whitespace_exact h hn.whitespace hn.comment hi
  refine ⟨Or.inr (Or.inl h), ?_, ?_⟩
  · simpa only [hs] using hn.marker
  · simpa only [tryRef, hs, hn.skip] using hn.reference

public theorem Stop.space {b i} (h : at? b i = 32) (hi : i < b.size)
    (hn : Start b (i+1)) : Stop b i :=
  Stop.whitespace (by rw [h]; rfl) hi hn

public theorem Start.close_array {b i} (h : at? b i = 93) : Start b i :=
  Start.non_numeric (by rw [h]; rfl) (by rw [h]; decide) (by rw [h]; decide)
    (by rw [h]; omega)

public theorem Start.close_dict {b i} (h : at? b i = 62) : Start b i :=
  Start.non_numeric (by rw [h]; rfl) (by rw [h]; decide) (by rw [h]; decide)
    (by rw [h]; omega)

public theorem Stop.close_array {b i} (h : at? b i = 93) : Stop b i :=
  Stop.of_start (Start.close_array h) (Or.inr (Or.inr (by rw [h]; rfl)))

public theorem Stop.close_dict {b i} (h : at? b i = 62) : Stop b i :=
  Stop.of_start (Start.close_dict h) (Or.inr (Or.inr (by rw [h]; rfl)))

public theorem Stop.eof {b i} (h : b.size ≤ i) : Stop b i := by
  have he := at?_ge b i h
  exact Stop.of_start
    (Start.non_numeric (by rw [he]; rfl) (by rw [he]; decide)
      (by rw [he]; decide) (by rw [he]; omega)) (Or.inl he)

end ObjReader
end LeanTex.Core.PdfRead
