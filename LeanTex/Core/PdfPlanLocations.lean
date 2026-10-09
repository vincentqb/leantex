module

public import LeanTex.Core.PdfObjectRecovery
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfProducerProof
import all LeanTex.Core.PdfObjectRecovery

namespace LeanTex.Core.Pdf
open PdfRead

/-! Locations read from the actual file, joined to the producer's source
objects and serializer offsets. These are artifact contracts. -/

/-- The xref value computed by the production reader on a bounded plan. -/
public def WritePlan.readback (p : WritePlan) : PdfRead.Xref :=
  (readXrefSubsection (Xref.encode p.widths p.entries) 1 p.widths.first p.widths.second
    0 p.table.size 0
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)}).1

public theorem WritePlan.readback_exact (p : WritePlan) (h : p.WithinBounds) :
    readXref p.bytes = .ok p.readback :=
  p.readXref_exact h

public theorem WritePlan.readback_locations_exact (p : WritePlan)
    (hs : p.entries.size = p.table.size) (id : Nat) :
    p.readback.locs.get? id = p.entries[id]?.bind xrefEntryLocation := by
  have hx := p.xref_locations_exact
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)} rfl id
  simpa only [WritePlan.readback, p.measure_xref_exact, hs,
    Std.HashMap.get?_eq_getElem?] using hx

/-- An in-range id with one source position selects that exact position,
through the real dense object-stream index. -/
public theorem compressedIndex_entry_exact (size : Nat) (objects : List (Nat × Obj))
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

public theorem compressedIndex_absent_exact (size : Nat) (objects : List (Nat × Obj))
    (id : Nat) (h : id ∉ objects.map Prod.fst) :
    ((compressedIndex size objects)[id]?).join = none := by
  cases hi : ((compressedIndex size objects)[id]?).join with
  | none => rfl
  | some i =>
    obtain ⟨v,hv⟩ := compressedIndex_mem size objects id i hi
    exact False.elim (h (List.mem_map.mpr ⟨(id,v), List.mem_of_getElem? hv, rfl⟩))

/-- The allocation's consecutive id transcript makes the array position
the id itself. The actual producer proves this transcript separately. -/
public theorem WritePlan.entry_index_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (id : Nat) (hid : id < p.table.size) :
    p.entries[id]? = some (if id = 0 then freeHead else
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

public theorem WritePlan.entries_size_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (hpos : 0 < p.table.size) :
    p.entries.size = p.table.size := by
  have hn := congrArg List.length ht
  simp only [Array.length_toList, List.length_range'] at hn
  simp only [WritePlan.entries, writerXrefEntries, xrefEntries, Array.size_append,
    Array.size_singleton, Array.size_map, hn]
  omega

public theorem indexObjects_unique_exact {α : Type} (size : Nat)
    (rows : List (Nat × α)) (id : Nat) (v : α) (hi : id < size)
    (hm : (id,v) ∈ rows) (hn : (rows.map Prod.fst).Nodup) :
    ((indexObjects size rows)[id]?).join = some v := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hm
  apply indexObjects_entry_exact _ _ _ _ _ hi
  have hafter := (List.nodup_append.mp
    (by simpa only [List.map_append] using hn)).2.1
  have hnot := (List.nodup_cons.mp hafter).1
  intro r hr he
  exact hnot (List.mem_map.mpr ⟨r, hr, he⟩)

/-- Each object stream's recorded offset is where its serializer wrote it,
given the rows' ids are distinct. -/
public theorem WritePlan.stm_offset_exact (p : WritePlan) (k : Nat) (c : List (Nat × Obj))
    (hk : p.chunks[k]? = some c) (hi : p.table.objStmId k < p.table.size)
    (hn : (p.rows.toList.map Row.id).Nodup) :
    ((indexObjects p.table.size p.serialized.2.toList)[p.table.objStmId k]?).join =
      some (p.stmOffset k) := by
  have hr : (stmRowsOf p.table p.packed).toList[k]? =
      some (objStmRow (p.table.objStmId k) c.length (objectStream c)) := by
    simp only [stmRowsOf, List.toList_toArray, List.getElem?_map, List.getElem?_zipIdx,
      WritePlan.packed, hk, Option.map_some, Nat.zero_add]
  have hlt : k < (stmRowsOf p.table p.packed).toList.length :=
    (List.getElem?_eq_some_iff.mp hr).1
  have he : objStmRow (p.table.objStmId k) c.length (objectStream c) =
      (stmRowsOf p.table p.packed).toList[k] :=
    ((List.getElem_eq_iff hlt).mpr hr).symm
  have hrows : p.rows =
      (p.direct.toList ++ (stmRowsOf p.table p.packed).toList.take k).toArray ++
        #[objStmRow (p.table.objStmId k) c.length (objectStream c)] ++
        ((stmRowsOf p.table p.packed).toList.drop (k + 1)).toArray := by
    apply Array.toList_inj.mp
    simp only [WritePlan.rows, Array.toList_append, List.append_assoc, List.singleton_append]
    congr 1
    rw [he, List.getElem_cons_drop, List.take_append_drop]
  have hoff := (serialize_row_exact p.head
    (p.direct.toList ++ (stmRowsOf p.table p.packed).toList.take k).toArray
    ((stmRowsOf p.table p.packed).toList.drop (k + 1)).toArray
    (objStmRow (p.table.objStmId k) c.length (objectStream c))).1
  rw [← hrows] at hoff
  have hid : (objStmRow (p.table.objStmId k) c.length (objectStream c)).id =
      p.table.objStmId k := flateRow_id ..
  rw [hid] at hoff
  apply indexObjects_unique_exact _ _ _ _ hi
  · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hoff)
  · exact (serialize_locs_covers p.head p.rows).symm ▸ hn

/-- The reader finds each object stream at its recorded offset. -/
public theorem WritePlan.stm_location_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (k : Nat) (c : List (Nat × Obj)) (hk : p.chunks[k]? = some c)
    (hpos : 0 < p.table.objStmId k) (hi : p.table.objStmId k < p.table.size)
    (hx : p.table.objStmId k ≠ p.table.xrefId)
    (hc : p.table.objStmId k ∉ p.compressed.map Prod.fst)
    (hn : (p.rows.toList.map Row.id).Nodup) :
    p.readback.locs.get? (p.table.objStmId k) = some (.direct (p.stmOffset k)) := by
  rw [p.readback_locations_exact (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi]
  simp only [show p.table.objStmId k ≠ 0 by omega, ↓reduceIte, Option.bind_some,
    xrefEntry, show (p.table.objStmId k == p.table.xrefId) = false from
      beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true,
    compressedIndex_absent_exact _ _ _ hc, p.stm_offset_exact k c hk hi hn,
    xrefEntryLocation]

/-- The reader finds the compressed object at position `i` in object
stream `i / objStmCapacity`, at index `i % objStmCapacity`. -/
public theorem WritePlan.compressed_location_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (id i : Nat) (value : Obj) (hpos : 0 < id) (hi : id < p.table.size)
    (hx : id ≠ p.table.xrefId) (hs : p.compressed[i]? = some (id,value))
    (hn : (p.compressed.map Prod.fst).Nodup) :
    p.readback.locs.get? id =
      some (.inStm (p.table.objStmId (i / objStmCapacity)) (i % objStmCapacity)) := by
  rw [p.readback_locations_exact (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi]
  simp only [show id ≠ 0 by omega, ↓reduceIte, Option.bind_some, xrefEntry,
    show (id == p.table.xrefId) = false from beq_eq_false_iff_ne.mpr hx,
    Bool.false_eq_true, compressedIndex_entry_exact _ _ _ _ _ hi hs hn,
    xrefEntryLocation]

/-- **`compressed_stream_between`**: reading any one compressed object
inflates exactly one object stream, which holds at most `objStmCapacity`
objects — the reader's location for the object at position `i` names
stream `i / objStmCapacity`, whose dictionary declares its own count,
and the object's index lies inside it. -/
public theorem WritePlan.compressed_stream_between (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (id i : Nat) (v : Obj) (hpos : 0 < id) (hi : id < p.table.size)
    (hx : id ≠ p.table.xrefId) (hs : p.compressed[i]? = some (id, v))
    (hn : (p.compressed.map Prod.fst).Nodup) :
    ∃ c, p.readback.locs.get? id =
        some (.inStm (p.table.objStmId (i / objStmCapacity)) (i % objStmCapacity)) ∧
      p.chunks[i / objStmCapacity]? = some c ∧
      (chunkDict c).get? "N" = some (.int c.length) ∧
      i % objStmCapacity < c.length ∧ c.length ≤ objStmCapacity := by
  have hlt : i < p.compressed.length := (List.getElem?_eq_some_iff.mp hs).1
  have he : p.compressed[i] = (id, v) := (List.getElem_eq_iff hlt).mpr hs
  have hsplit : p.compressed = p.compressed.take i ++ (id, v) :: p.compressed.drop (i + 1) := by
    rw [← he, List.getElem_cons_drop, List.take_append_drop]
  obtain ⟨cb, ca, hk, hcb, _⟩ :=
    objStmChunks_entry_exact (p.compressed.take i) (p.compressed.drop (i + 1)) (id, v)
  rw [← hsplit, List.length_take_of_le (Nat.le_of_lt hlt)] at hk
  rw [List.length_take_of_le (Nat.le_of_lt hlt)] at hcb
  change p.chunks[i / objStmCapacity]? = some (cb ++ (id, v) :: ca) at hk
  have hb := objStmChunks_between p.compressed _ (List.mem_of_getElem? hk)
  refine ⟨cb ++ (id, v) :: ca, p.compressed_location_exact ht id i v hpos hi hx hs hn, hk,
    (chunkDict_fields_exact _).2.1, ?_, hb.2⟩
  simp only [List.length_append, List.length_cons]
  omega

/-- Complete compressed-object recovery through the actual file's xref,
from the object stream that holds it. The premises concern source
allocation, numeric bounds, and grammar. There is no supplied parser,
location, or decompression result. -/
public theorem WritePlan.compressed_readback_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (hstm : ∀ k, k < p.chunks.length → 0 < p.table.objStmId k ∧
      p.table.objStmId k < p.table.size ∧ p.table.objStmId k ≠ p.table.xrefId ∧
      p.table.objStmId k ∉ p.compressed.map Prod.fst)
    (hn : (p.compressed.map Prod.fst).Nodup)
    (hrows : (p.rows.toList.map Row.id).Nodup)
    (before after : List (Nat × Obj)) (id : Nat) (v : Obj)
    (hs : p.compressed = before ++ (id,v)::after)
    (hi : 0 < id ∧ id < p.table.size ∧ id ≠ p.table.xrefId)
    (hv : v.Representable) (ha : ∀ e ∈ after, e.2.Representable) :
    readXref p.bytes = .ok p.readback ∧
      ({num := id, header := id,
        loc := .inStm (p.table.objStmId (before.length / objStmCapacity))
          (before.length % objStmCapacity),
        val := v, stream := none} : Entry).Reads p.bytes p.readback.locs none := by
  obtain ⟨cb, ca, hk, _, _⟩ := objStmChunks_entry_exact before after (id, v)
  rw [← hs] at hk
  change p.chunks[before.length / objStmCapacity]? = some (cb ++ (id, v) :: ca) at hk
  have hkl := (List.getElem?_eq_some_iff.mp hk).1
  have hk' := hstm _ hkl
  refine ⟨p.readback_exact h, p.compressed_reads_exact h _ before after id v hs hv ha
    (p.stm_location_exact ht _ _ hk hk'.1 hk'.2.1 hk'.2.2.1 hk'.2.2.2 hrows) ?_⟩
  apply p.compressed_location_exact ht id before.length v hi.1 hi.2.1 hi.2.2 _ hn
  simp only [hs, List.getElem?_append_right (Nat.le_refl before.length), Nat.sub_self,
    List.getElem?_cons_zero]

end LeanTex.Core.Pdf
