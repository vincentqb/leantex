module

public import LeanTex.Core.PdfObjProof
import LeanTex.Core.PdfReadProof

namespace LeanTex.Core.PdfRead
open PdfLex

/-! Executable spelling checks for source objects, before serialization.
These inspect the encoder's input grammar; they never run the PDF reader
or compare a recovered object with its source. -/

/-- The native literal encoder escapes every parenthesis and backslash.
Accept that flat spelling, ending at exactly one closing parenthesis. -/
private def literalTail : List Nat → Bool
  | [] => false
  | 41 :: [] => true
  | 92 :: c :: cs => decide (c < 256) && literalTail cs
  | c :: cs =>
    decide (c < 256 ∧ c ≠ 40 ∧ c ≠ 41 ∧ c ≠ 92) && literalTail cs

private theorem literalTail_sound (cs : List Nat) (h : literalTail cs = true) :
    ∃ body, cs = body ++ [41] ∧ LiteralBody body := by
  fun_induction literalTail cs with
  | case1 => simp at h
  | case2 => exact ⟨[], rfl, .nil⟩
  | case3 c cs ih =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨body, rfl, hb⟩ := ih h.2
    exact ⟨92 :: c :: body, rfl, .escape h.1 hb⟩
  | case4 c cs _ _ ih =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨body, rfl, hb⟩ := ih h.2
    exact ⟨c :: body, rfl, .byte h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 hb⟩

private def hexTail : List Nat → Bool
  | [] => false
  | 62 :: [] => true
  | c :: cs => ((hexVal c).isSome || isWs c) && hexTail cs

private theorem hexTail_sound (cs : List Nat) (h : hexTail cs = true) :
    ∃ body, cs = body ++ [62] ∧
      ∀ c ∈ body, hexVal c ≠ none ∨ isWs c = true := by
  fun_induction hexTail cs with
  | case1 => simp at h
  | case2 => exact ⟨[], rfl, by simp⟩
  | case3 c cs _ ih =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isSome_iff_ne_none] at h
    obtain ⟨body, rfl, hb⟩ := ih h.2
    exact ⟨c :: body, rfl, by simpa using And.intro h.1 hb⟩

/-- Exact delimiters around a native escaped literal or a hexadecimal
string. Balanced nested literals are valid PDF but outside this encoder's
checked source domain. -/
def Obj.stringEncodable : List Nat → Bool
  | 40 :: cs => literalTail cs
  | 60 :: cs => hexTail cs
  | _ => false

theorem Obj.stringEncodable_contract (cs : List Nat) (h : stringEncodable cs = true) :
    StringSpelling cs := by
  unfold stringEncodable at h
  split at h
  · obtain ⟨body, rfl, hb⟩ := literalTail_sound _ h
    exact .literal hb
  · obtain ⟨body, rfl, hb⟩ := hexTail_sound _ h
    exact .hex hb
  · contradiction

instance (s : String) : Decidable (Obj.NameSpelling s) :=
  inferInstanceAs (Decidable (s ≠ "" ∧ ∀ c ∈ s.toList, c.toNat < 256))

instance (s : String) : Decidable (Obj.RealSpelling s) :=
  inferInstanceAs (Decidable ('.' ∈ s.toList ∧ ∀ c ∈ s.toList, numByte c.toNat = true))

mutual

/-- Check every raw spelling the object encoder accepts. The recursive
container checks share the same source tree as `Obj.renderInto`. -/
public def Obj.encodable : Obj → Bool
  | .null | .bool _ | .int _ | .ref _ _ => true
  | .name s => decide (NameSpelling s)
  | .real s => decide (RealSpelling s)
  | .str b => stringEncodable (b.data.toList.map UInt8.toNat)
  | .arr xs => encodableList xs.toList
  | .dict es => encodableEntries es.toList

def Obj.encodableList : List Obj → Bool
  | [] => true
  | v :: vs => v.encodable && encodableList vs

def Obj.encodableEntries : List (String × Obj) → Bool
  | [] => true
  | (k,v) :: es => decide (NameSpelling k) && v.encodable && encodableEntries es

end

mutual

/-- The executable source check establishes the syntactic domain of the
proved production parser/renderer round trip. -/
private theorem Obj.encodable_sound (v : Obj) (h : v.encodable = true) :
    v.Representable := by
  cases v with
  | null => exact .null
  | bool b => exact .bool b
  | int n => exact .int n
  | ref n g => exact .ref n g
  | name s => exact .name (of_decide_eq_true h)
  | real s => exact .real (of_decide_eq_true h)
  | str b => exact .str (stringEncodable_contract _ h)
  | arr xs =>
    exact .arr (fun x hx => encodableList_contract _ h x (Array.mem_toList_iff.mpr hx))
  | dict es =>
    have he := encodableEntries_contract _ h
    exact .dict
      (fun e hm => (he e (Array.mem_toList_iff.mpr hm)).1)
      (fun e hm => (he e (Array.mem_toList_iff.mpr hm)).2)

private theorem Obj.encodableList_contract (vs : List Obj) (h : encodableList vs = true) :
    ∀ v ∈ vs, v.Representable := by
  cases vs with
  | nil => simp
  | cons v vs =>
    simp only [encodableList, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact encodable_sound v h.1
    · exact encodableList_contract vs h.2 x hx

private theorem Obj.encodableEntries_contract (es : List (String × Obj))
    (h : encodableEntries es = true) :
    ∀ e ∈ es, NameSpelling e.1 ∧ e.2.Representable := by
  cases es with
  | nil => simp
  | cons e es =>
    rcases e with ⟨k,v⟩
    simp only [encodableEntries, Bool.and_eq_true, decide_eq_true_eq] at h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨h.1.1, encodable_sound v h.1.2⟩
    · exact encodableEntries_contract es h.2 e he

end

/-- The source checker establishes the encoder's complete representable domain. -/
public theorem Obj.encodable_contract (v : Obj) (h : v.encodable = true) :
    v.Representable := encodable_sound v h

/-- The executable grammar check supplies the complete parser/renderer
round trip. This is quantified over arbitrary source trees and bytes,
including nested containers and raw string spellings. -/
public theorem Obj.encodable_render_exact (o : Obj) (h : o.encodable = true) :
    parseVal o.render 0 = .ok (o, o.render.size) :=
  parseVal_render_id o (o.encodable_contract h)

end LeanTex.Core.PdfRead
