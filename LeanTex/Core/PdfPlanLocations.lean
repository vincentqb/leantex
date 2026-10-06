import LeanTex.Core.PdfObjectRecovery

namespace LeanTex.Core.Pdf
open PdfRead

/-! Locations read from the actual file, joined to the producer's source
objects and serializer offsets. These are artifact contracts. -/

/-- The xref value computed by the production reader on a bounded plan. -/
def WritePlan.readback (p : WritePlan) : PdfRead.Xref :=
  (readXrefSubsection (Xref.encode p.entries) 1 4 2 0 p.table.size 0
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)}).1

theorem WritePlan.readback_exact (p : WritePlan) (h : p.WithinBounds) :
    readXref p.bytes = .ok p.readback :=
  p.readXref_exact h

theorem WritePlan.readback_locations_exact (p : WritePlan) (h : p.WithinBounds)
    (hs : p.entries.size = p.table.size) (id : Nat) :
    p.readback.locs.get? id = p.entries[id]?.bind xrefEntryLocation := by
  have hx := p.xref_locations_exact h
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)} rfl id
  simpa only [WritePlan.readback, p.measure_xref_exact, hs,
    Std.HashMap.get?_eq_getElem?] using hx

/-- An in-range id with one source position selects that exact position,
through the real dense object-stream index. -/
theorem compressedIndex_entry_exact (size : Nat) (objects : List (Nat × Obj))
    (id i : Nat) (value : Obj) (hid : id < size)
    (hi : objects[i]? = some (id,value))
    (hn : (objects.map Prod.fst).Nodup) :
    ((compressedIndex size objects)[id]?).join = some i := by
  have hm : id ∈ objects.map Prod.fst :=
    List.mem_map.mpr ⟨(id,value), List.mem_of_getElem? hi, rfl⟩
  obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp
    (compressedIndex_covers size objects id hid hm)
  obtain ⟨v,hv⟩ := compressedIndex_mem size objects id j hj
  have he : i = j := hn.eq_of_getElem?_eq
    (by simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hi).1)
    (by simp only [List.getElem?_map, hi, hv, Option.map_some])
  simpa only [← he] using hj

theorem compressedIndex_absent_exact (size : Nat) (objects : List (Nat × Obj))
    (id : Nat) (h : id ∉ objects.map Prod.fst) :
    ((compressedIndex size objects)[id]?).join = none := by
  cases hi : ((compressedIndex size objects)[id]?).join with
  | none => rfl
  | some i =>
    obtain ⟨v,hv⟩ := compressedIndex_mem size objects id i hi
    exact False.elim (h (List.mem_map.mpr ⟨(id,v), List.mem_of_getElem? hv, rfl⟩))

/-- The allocation's consecutive id transcript makes the array position
the id itself. The actual producer proves this transcript separately. -/
theorem WritePlan.entry_index_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (id : Nat) (hid : id < p.table.size) :
    p.entries[id]? = some (if id = 0 then .free 0 65535 else
      xrefEntry p.table
        (fun n => ((compressedIndex p.table.size p.compressed)[n]?).join)
        (fun n => ((indexObjects p.table.size p.serialized.2.toList)[n]?).join)
        p.serialized.1.size id) := by
  have ha : p.table.ids = (List.range' 1 (p.table.size - 1)).toArray := by
    rw [← ht, Array.toArray_toList]
  cases id with
  | zero => simp [WritePlan.entries, writerXrefEntries, xrefEntries,
      Array.getElem?_append]
  | succ id =>
    simp only [WritePlan.entries, writerXrefEntries, xrefEntries, ha,
      Array.getElem?_append, Array.size_singleton, Nat.succ_lt_succ_iff,
      Nat.not_lt_zero, ↓reduceIte, Nat.add_one_sub_one, Array.getElem?_map,
      List.getElem?_toArray]
    simp [show id < p.table.size - 1 by omega, Nat.add_comm]

theorem WritePlan.entries_size_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (hpos : 0 < p.table.size) :
    p.entries.size = p.table.size := by
  have hn := congrArg List.length ht
  simp only [Array.length_toList, List.length_range'] at hn
  simp only [WritePlan.entries, writerXrefEntries, xrefEntries, Array.size_append,
    Array.size_singleton, Array.size_map, hn]
  omega

/-- The object-stream row is appended last, so its recorded offset is
exact even without a uniqueness premise on preceding direct rows. -/
theorem WritePlan.object_offset_exact (p : WritePlan)
    (hi : p.table.objStmId < p.table.size) :
    ((indexObjects p.table.size p.serialized.2.toList)[p.table.objStmId]?).join =
      some (serialize p.head p.direct).1.size := by
  have hs : p.serialized.2 =
      (serialize p.head p.direct).2.push
        (p.table.objStmId, (serialize p.head p.direct).1.size) := by
    change (serialize p.head (p.direct.push (flateRow p.table.objStmId
      s!"/Type /ObjStm /N {p.compressed.length} /First {(objectStream p.compressed).header.utf8ByteSize}"
      (objectStream p.compressed).bytes))).2 = _
    simp only [serialize, Array.toList_push, serializeList_append, serializeList]
    unfold flateRow zRow
    split <;> rfl
  rw [hs, Array.toList_push]
  exact indexObjects_entry_exact _ _ [] _ _ hi (by simp)

theorem WritePlan.object_location_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (hpos : 0 < p.table.objStmId) (hi : p.table.objStmId < p.table.size)
    (hx : p.table.objStmId ≠ p.table.xrefId)
    (hc : p.table.objStmId ∉ p.compressed.map Prod.fst) :
    p.readback.locs.get? p.table.objStmId =
      some (.direct (serialize p.head p.direct).1.size) := by
  rw [p.readback_locations_exact h (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi]
  simp only [show p.table.objStmId ≠ 0 by omega, ↓reduceIte, Option.bind_some,
    xrefEntry, show (p.table.objStmId == p.table.xrefId) = false from
      beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true,
    compressedIndex_absent_exact _ _ _ hc, p.object_offset_exact hi,
    xrefEntryLocation]

theorem WritePlan.compressed_location_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (id i : Nat) (value : Obj) (hpos : 0 < id) (hi : id < p.table.size)
    (hx : id ≠ p.table.xrefId) (hs : p.compressed[i]? = some (id,value))
    (hn : (p.compressed.map Prod.fst).Nodup) :
    p.readback.locs.get? id = some (.inStm p.table.objStmId i) := by
  rw [p.readback_locations_exact h (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi]
  simp only [show id ≠ 0 by omega, ↓reduceIte, Option.bind_some, xrefEntry,
    show (id == p.table.xrefId) = false from beq_eq_false_iff_ne.mpr hx,
    Bool.false_eq_true, compressedIndex_entry_exact _ _ _ _ _ hi hs hn,
    xrefEntryLocation]

/-- Complete compressed-object recovery through the actual file's xref.
The premises concern source allocation, numeric bounds, and grammar.
There is no supplied parser, location, or decompression result. -/
theorem WritePlan.compressed_readback_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (hstm : 0 < p.table.objStmId ∧ p.table.objStmId < p.table.size ∧
      p.table.objStmId ≠ p.table.xrefId ∧
      p.table.objStmId ∉ p.compressed.map Prod.fst)
    (hn : (p.compressed.map Prod.fst).Nodup)
    (before after : List (Nat × Obj)) (id : Nat) (v : Obj)
    (hs : p.compressed = before ++ (id,v)::after)
    (hi : 0 < id ∧ id < p.table.size ∧ id ≠ p.table.xrefId)
    (hv : v.Representable) (ha : ∀ e ∈ after, e.2.Representable) :
    readXref p.bytes = .ok p.readback ∧
      ({num := id, header := id, loc := .inStm p.table.objStmId before.length,
        val := v, stream := none} : Entry).Reads p.bytes p.readback.locs none := by
  refine ⟨p.readback_exact h, p.compressed_reads_exact h _ before after id v hs hv ha
    (p.object_location_exact h ht hstm.1 hstm.2.1 hstm.2.2.1 hstm.2.2.2) ?_⟩
  apply p.compressed_location_exact h ht id before.length v hi.1 hi.2.1 hi.2.2 _ hn
  simp only [hs, List.getElem?_append_right (Nat.le_refl before.length), Nat.sub_self,
    List.getElem?_cons_zero]

end LeanTex.Core.Pdf
