module

public import LeanTex.Core.PdfReadProof
public import LeanTex.Core.Flate
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfLex
import all LeanTex.Core.Flate
import LeanTex.Core.Loop

namespace LeanTex.Core.Pdf
open PdfLex PdfRead

/-! The typed dictionary and exact byte spelling of the writer's xref
stream. This is an artifact grammar contract, independent of the IR. -/

private def HexChars (s : String) : Prop :=
  ∀ c ∈ s.toList, hexVal c.toNat ≠ none ∧ c.toNat < 128

private theorem hex_digit (n : Nat) :
    hexVal ("0123456789ABCDEF".toList.toArray[n]?.getD '0').toNat ≠ none ∧
    ("0123456789ABCDEF".toList.toArray[n]?.getD '0').toNat < 128 := by
  cases h : "0123456789ABCDEF".toList.toArray[n]? with
  | none => decide
  | some c =>
    have hm := Array.mem_of_getElem? h
    change c ∈ #['0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'] at hm
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem hex16_chars (x : UInt64) : HexChars (Flate.hex16 x) := by
  unfold Flate.hex16
  apply Loop.bind_of_inv (P := fun s : String × UInt64 => HexChars s.1)
  · apply Loop.forIn_range_inv (P := fun s : String × UInt64 => HexChars s.1)
    · intro c hc
      simp at hc
    · intro i hlo hhi s hs
      change HexChars (String.ofList [_] ++ s.1)
      intro c hc
      simp only [String.toList_append, String.toList_ofList, List.mem_append,
        List.mem_singleton] at hc
      rcases hc with rfl | hc
      · exact hex_digit _
      · exact hs c hc
  · intro s hs
    exact hs

public theorem hex16_string_exact (x : UInt64) :
    (Obj.str (("<" ++ Flate.hex16 x ++ ">").toUTF8)).Representable := by
  apply Obj.Representable.str
  have hx := hex16_chars x
  have hb : octets (Flate.hex16 x).toUTF8 =
      (Flate.hex16 x).toList.map Char.toNat := by
    simpa only [String.ofList_toList] using
      octets_ascii (Flate.hex16 x).toList (fun c hc => (hx c hc).2)
  change Obj.StringSpelling (octets ("<" ++ Flate.hex16 x ++ ">").toUTF8)
  simp only [utf8_append, octets_append, hb,
    show octets "<".toUTF8 = [60] from by rw [String.toUTF8_eq_toByteArray]; rfl,
    show octets ">".toUTF8 = [62] from by rw [String.toUTF8_eq_toByteArray]; rfl,
    List.singleton_append]
  apply Obj.StringSpelling.hex
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact Or.inl (hx d hd).1

/-- The typed value of the xref dictionary the writer spells. The hashes
are the same 64-bit values used for the two file identifiers. -/
public def xrefStreamDict (count info : Nat) (idA idB : UInt64) (filtered : Bool)
    (len : Nat) : Obj :=
  .dict (#[ ("Type", .name "XRef"), ("Size", .int count),
    ("W", .arr #[.int 1, .int 4, .int 2]),
    ("Index", .arr #[.int 0, .int count]), ("Root", .ref 1 0),
    ("Info", .ref info 0),
    ("ID", .arr #[.str (("<" ++ Flate.hex16 idA ++ ">").toUTF8),
      .str (("<" ++ Flate.hex16 idB ++ ">").toUTF8)])] ++
    (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int len)])

public theorem xrefStreamDict_fields_exact (count info : Nat) (idA idB : UInt64)
    (filtered : Bool) (len : Nat) :
    let d := xrefStreamDict count info idA idB filtered len
    d.get? "Length" = some (.int len) ∧
    d.get? "W" = some (.arr #[.int 1, .int 4, .int 2]) ∧
    d.get? "Size" = some (.int count) ∧
    d.get? "Index" = some (.arr #[.int 0, .int count]) ∧
    d.get? "Prev" = none ∧ d.get? "Root" = some (.ref 1 0) ∧
    d.get? "Filter" = (if filtered then some (.name "FlateDecode") else none) ∧
    d.get? "DL" = none ∧ d.get? "DecodeParms" = none := by
  cases filtered <;> simp [xrefStreamDict, Obj.get?]

public theorem xrefStreamDict_representable_exact (count info : Nat) (idA idB : UInt64)
    (filtered : Bool) (len : Nat) :
    (xrefStreamDict count info idA idB filtered len).Representable := by
  cases filtered <;> unfold xrefStreamDict <;>
    apply Obj.Representable.dict
  all_goals intro e he
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, Array.mem_append,
    or_false, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at he
  repeat (any_goals (rcases he with he | he))
  all_goals try subst e
  all_goals first
    | exact Obj.Representable.name (by simp [Obj.NameSpelling])
    | exact Obj.Representable.int _
    | exact Obj.Representable.ref _ _
    | solve | simp [Obj.NameSpelling]
    | skip
  all_goals apply Obj.Representable.arr
  all_goals intro x hx
  all_goals simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
  repeat (any_goals (rcases hx with hx | hx))
  all_goals try subst x
  all_goals first | exact Obj.Representable.int _ | exact hex16_string_exact _

private theorem push_append (b : ByteArray) (c : UInt8) :
    b.push c = b ++ ⟨#[c]⟩ := by
  apply ByteArray.ext
  rw [ByteArray.data_push, ByteArray.data_append]
  exact Array.push_eq_append

set_option maxRecDepth 4096 in
public theorem xrefStreamDict_render_exact (count info : Nat) (idA idB : UInt64)
    (filtered : Bool) (len : Nat) :
    (xrefStreamDict count info idA idB filtered len).render =
      (s!"<< /Type /XRef /Size {count} /W [1 4 2] /Index [0 {count}] /Root 1 0 R /Info {info} 0 R /ID [<{Flate.hex16 idA}> <{Flate.hex16 idB}>]" ++
        (if filtered then " /Filter /FlateDecode" else "") ++
        s!" /Length {len} >>").toUTF8 := by
  cases filtered <;>
    simp only [xrefStreamDict, Bool.false_eq_true, ↓reduceIte,
      Obj.render, Obj.renderInto, Array.toList_append, List.append_nil,
      List.cons_append, List.nil_append, Obj.renderEntries,
      Obj.renderList, push_append, utf8_append, ByteArray.append_assoc,
      ByteArray.empty_append]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append]
  all_goals simp only [String.toUTF8_eq_toByteArray, Int.toString_eq_repr,
    Int.repr_eq_ite, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  all_goals simp only [show (0 : Int) ≤ 0 from by omega, show (0 : Int) ≤ 1 from by omega,
    show (0 : Int) ≤ 2 from by omega, show (0 : Int) ≤ 4 from by omega, ↓reduceIte,
    show (0 : Int).toNat = 0 from by omega, show (1 : Int).toNat = 1 from by omega,
    show (2 : Int).toNat = 2 from by omega, show (4 : Int).toNat = 4 from by omega]
  all_goals simp only [Nat.toString_eq_repr, Nat.repr_of_lt (n := 0) (by omega),
    Nat.repr_of_lt (n := 1) (by omega), Nat.repr_of_lt (n := 2) (by omega),
    Nat.repr_of_lt (n := 4) (by omega),
    Nat.digitChar_eq_zero.mpr rfl, Nat.digitChar_eq_one.mpr rfl,
    Nat.digitChar_eq_two.mpr rfl, Nat.digitChar_eq_four.mpr rfl,
    String.singleton_eq_ofList]
  all_goals rfl

end LeanTex.Core.Pdf
