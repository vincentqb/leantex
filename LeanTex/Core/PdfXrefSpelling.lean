import LeanTex.Core.PdfReadProof
import LeanTex.Core.Flate
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

theorem hex16_string_exact (x : UInt64) :
    (Obj.str (("<" ++ Flate.hex16 x ++ ">").toUTF8)).Representable := by
  apply Obj.Representable.str
  have hx := hex16_chars x
  have hb : octets (Flate.hex16 x).toUTF8 =
      (Flate.hex16 x).toList.map Char.toNat := by
    simpa only [String.ofList_toList] using
      octets_ascii (Flate.hex16 x).toList (fun c hc => (hx c hc).2)
  change Obj.StringSpelling (octets ("<" ++ Flate.hex16 x ++ ">").toUTF8)
  simp only [utf8_append, octets_append, hb]
  apply Obj.StringSpelling.hex
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact Or.inl (hx d hd).1

/-- The typed value of the xref dictionary the writer spells. The hashes
are the same 64-bit values used for the two file identifiers. -/
def xrefStreamDict (count info : Nat) (idA idB : UInt64) (filtered : Bool)
    (len : Nat) : Obj :=
  .dict (#[ ("Type", .name "XRef"), ("Size", .int count),
    ("W", .arr #[.int 1, .int 4, .int 2]),
    ("Index", .arr #[.int 0, .int count]), ("Root", .ref 1 0),
    ("Info", .ref info 0),
    ("ID", .arr #[.str (("<" ++ Flate.hex16 idA ++ ">").toUTF8),
      .str (("<" ++ Flate.hex16 idB ++ ">").toUTF8)])] ++
    (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int len)])

theorem xrefStreamDict_fields_exact (count info : Nat) (idA idB : UInt64)
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

theorem xrefStreamDict_representable_exact (count info : Nat) (idA idB : UInt64)
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
theorem xrefStreamDict_render_exact (count info : Nat) (idA idB : UInt64)
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
  all_goals rfl

end LeanTex.Core.Pdf
