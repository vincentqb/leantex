import LeanTex.Core.PdfObjProof
import LeanTex.Core.PdfObjMachine
import LeanTex.Core.PdfLexBoundary

namespace LeanTex.Core.PdfRead.ObjReader

open PdfLex

theorem readToken_name {b : ByteArray} {i : Nat} {s : String}
    (h : Span b i (octets ("/" ++ escapeName s).toUTF8))
    (hs : Obj.NameSpelling s)
    (he : EndByte (at? b (i+("/" ++ escapeName s).toUTF8.size))) :
    readToken b i = .ok (.value (.name s), i+("/" ++ escapeName s).toUTF8.size) := by
  rw [Obj.name_octets s hs.1] at h
  have hp := parseName_exact h.tail hs.2
    (by simpa only [EndByte, Obj.name_size s hs.1, Nat.add_assoc] using he)
  rw [Obj.name_size s hs.1]
  simp only [readToken, h.head, hp]
  simp only [Nat.add_assoc]
  rfl

theorem readToken_literal {b raw : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i (octets raw)) (hc : LiteralBody cs)
    (hr : octets raw = 40 :: cs ++ [41]) :
    readToken b i = .ok (.value (.str raw), i+raw.size) := by
  have hsize : raw.size = cs.length+2 := by
    simpa using congrArg List.length hr
  have hx := h.extract_exact
  rw [hr] at h
  have hp := scanLitString_exact h.tail hc
  have hp' : scanLitString b i = some (i+raw.size) := by
    simpa only [hsize, Nat.add_assoc] using hp
  simp [readToken, h.head, hp', hx]
  rfl

theorem readToken_hex {b raw : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i (octets raw))
    (hc : ∀ c ∈ cs, hexVal c ≠ none ∨ isWs c = true)
    (hr : octets raw = 60 :: cs ++ [62]) :
    readToken b i = .ok (.value (.str raw), i+raw.size) := by
  have hp : ∀ c ∈ cs, c ≠ 60 ∧ c ≠ 62 ∧ c ≠ 256 := by
    intro c hm
    have hh := hc c hm
    refine ⟨?_,?_,?_⟩ <;> intro he <;> subst c <;> simp [hexVal,isWs] at hh
  have hsize : raw.size = cs.length+2 := by
    simpa using congrArg List.length hr
  have hx := h.extract_exact
  rw [hr] at h
  have hopen : at? b (i+1) ≠ 60 := by
    cases cs with
    | nil => rw [h.tail.head]; decide
    | cons c cs => rw [h.tail.head]; exact (hp c (by simp)).1
  have scan := scanHexEnd_exact h.tail (fun c hm => (hp c hm).2)
  have hend : at? b (i+1+cs.length) = 62 := by
    have hh := h.tail.append_right.head
    simpa using hh
  have hi : i+1+cs.length+1 = i+raw.size := by omega
  simp [readToken, h.head, hopen, scan, hend, hi, hx]
  rfl

theorem readToken_string {b raw : ByteArray} {i : Nat}
    (h : Span b i (octets raw)) (hs : Obj.StringSpelling (octets raw)) :
    readToken b i = .ok (.value (.str raw), i+raw.size) := by
  generalize hr : octets raw = cs at hs
  cases hs with
  | literal hc => exact readToken_literal h hc hr
  | hex hc => exact readToken_hex h hc hr

theorem num_head {c : Nat} (hc : numByte c = true) :
    c ≠ 256 ∧ c ≠ 91 ∧ c ≠ 93 ∧ c ≠ 60 ∧ c ≠ 62 ∧ c ≠ 40 ∧ c ≠ 47 := by
  simp only [numByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  omega

theorem readToken_real {b : ByteArray} {i j : Nat} {s : String}
    (hc : numByte (at? b i) = true) (hn : scanNumber b i = (s,j))
    (hd : s.contains '.' = true) :
    readToken b i = .ok (.value (.real s), j) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := num_head hc
  simp [readToken, h0,h1,h2,h3,h4,h5,h6,hc,hn,hd]
  rfl

theorem readToken_int {b : ByteArray} {i j : Nat} {n : Int}
    (hc : numByte (at? b i) = true) (hn : scanNumber b i = (toString n,j))
    (hr : tryRef b j = none) :
    readToken b i = .ok (.value (.int n), j) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := num_head hc
  simp only [readToken, Bool.and_eq_true, beq_iff_eq, h0,h1,h2,h3,h4,h5,h6,
    false_and, ↓reduceIte, hc, hn, Number.int_noDot, Bool.false_eq_true,
    Number.int_toString_id, hr, ite_self]
  rfl

theorem readToken_ref {b : ByteArray} {i j k num gen : Nat}
    (hc : numByte (at? b i) = true) (hn : scanNumber b i = (toString num,j))
    (hr : tryRef b j = some (gen,k)) :
    readToken b i = .ok (.value (.ref num gen), k) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := num_head hc
  have ht : toString (Int.ofNat num) = toString num := rfl
  have hd := Number.int_noDot (Int.ofNat num)
  have hi := Number.int_toString_id (Int.ofNat num)
  rw [ht] at hd hi
  simp only [readToken, Bool.and_eq_true, beq_iff_eq, h0,h1,h2,h3,h4,h5,h6,
    false_and, ↓reduceIte, hc, hn, hd, Bool.false_eq_true, hi,
    show (Int.ofNat num) ≥ 0 from Int.natCast_nonneg num, hr]
  rfl

theorem readToken_true {b : ByteArray} {i : Nat}
    (h : Span b i [116,114,117,101]) (he : EndByte (at? b (i+4))) :
    readToken b i = .ok (.value (.bool true),i+4) := by
  have hk := keywordAt_exact (kw := "true") h he
  simp [readToken,h.head,numByte,hk]
  rfl

theorem readToken_false {b : ByteArray} {i : Nat}
    (h : Span b i [102,97,108,115,101]) (he : EndByte (at? b (i+5))) :
    readToken b i = .ok (.value (.bool false),i+5) := by
  have ht := keywordAt_ne (b := b) (i := i) (kw := "true") (by decide)
    (by change at? b i ≠ 116; rw [h.head]; decide)
  have hk := keywordAt_exact (kw := "false") h he
  simp [readToken,h.head,numByte,ht,hk]
  rfl

theorem readToken_null {b : ByteArray} {i : Nat}
    (h : Span b i [110,117,108,108]) (he : EndByte (at? b (i+4))) :
    readToken b i = .ok (.value .null,i+4) := by
  have ht := keywordAt_ne (b := b) (i := i) (kw := "true") (by decide)
    (by change at? b i ≠ 116; rw [h.head]; decide)
  have hf := keywordAt_ne (b := b) (i := i) (kw := "false") (by decide)
    (by change at? b i ≠ 102; rw [h.head]; decide)
  have hk := keywordAt_exact (kw := "null") h he
  simp [readToken,h.head,numByte,ht,hf,hk]
  rfl

end LeanTex.Core.PdfRead.ObjReader
