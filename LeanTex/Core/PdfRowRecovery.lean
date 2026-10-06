import LeanTex.Core.PdfPlanLocations
import LeanTex.Core.PdfNativeStream

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Recovery of native stream rows from the serializer's own offsets. -/

theorem indexObjects_unique_exact {α : Type} (size : Nat)
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

theorem WritePlan.direct_suffix_exact (p : WritePlan) :
    ∃ tail, p.bytes = (serialize p.head p.direct).1 ++ tail := by
  rw [WritePlan.bytes, p.measure.bytes_stream_exact, p.object_body_exact]
  simp only [ByteArray.append_assoc]
  exact ⟨_, rfl⟩

theorem serializeList_row_span_exact (head : ByteArray)
    (before after : List Row) (r : Row) :
    PdfLex.Span (serializeList head #[] (before ++ r::after)).1
      (serializeList head #[] before).1.size
      (octets (rowInto ByteArray.empty r.id r.body)) := by
  rw [serializeList_append]
  simp only [serializeList]
  rw [serializeList_bytes, rowInto_bytes]
  exact PdfLex.Span.of_bytes _ _ _

private theorem span_append {b : ByteArray} {off : Nat} {cs : List Nat}
    (h : PdfLex.Span b off cs) (tail : ByteArray) : PdfLex.Span (b ++ tail) off cs := by
  refine ⟨?_, ?_⟩
  · have := h.bound
    simp only [ByteArray.size_append]
    omega
  · intro j hj
    rw [at?_append_left b tail (off+j) (by have := h.bound; omega)]
    exact h.byte j hj

theorem WritePlan.direct_span_exact (p : WritePlan) (before after : List Row)
    (r : Row) (hs : p.direct.toList = before ++ r::after) :
    PdfLex.Span p.bytes (serializeList p.head #[] before).1.size
      (octets (rowInto ByteArray.empty r.id r.body)) := by
  obtain ⟨tail, ht⟩ := p.direct_suffix_exact
  rw [ht]
  apply span_append
  change PdfLex.Span (serializeList p.head #[] p.direct.toList).1 _ _
  rw [hs]
  exact serializeList_row_span_exact ..

theorem WritePlan.direct_offset_exact (p : WritePlan) (before after : List Row)
    (r : Row) (hs : p.direct.toList = before ++ r::after)
    (hi : r.id < p.table.size) (hn : (p.rows.toList.map Row.id).Nodup) :
    ((indexObjects p.table.size p.serialized.2.toList)[r.id]?).join =
      some (serializeList p.head #[] before).1.size := by
  apply indexObjects_unique_exact _ _ _ _ hi
  · have hrows : p.rows.toList = before ++ r ::
        (after ++ [flateRow p.table.objStmId
          s!"/Type /ObjStm /N {p.compressed.length} /First {(objectStream p.compressed).header.utf8ByteSize}"
          (objectStream p.compressed).bytes]) := by
      change (p.direct.push _).toList = _
      simp only [Array.toList_push, hs, List.append_assoc,
        List.cons_append]
    have hoff := (serialize_row_exact p.head before.toArray
      (after ++ [flateRow p.table.objStmId
        s!"/Type /ObjStm /N {p.compressed.length} /First {(objectStream p.compressed).header.utf8ByteSize}"
        (objectStream p.compressed).bytes]).toArray r).1
    have hs' : p.rows = before.toArray ++ #[r] ++
        (after ++ [flateRow p.table.objStmId
          s!"/Type /ObjStm /N {p.compressed.length} /First {(objectStream p.compressed).header.utf8ByteSize}"
          (objectStream p.compressed).bytes]).toArray := by
      apply Array.toList_inj.mp
      simpa only [Array.toList_append, List.toList_toArray,
        List.singleton_append, List.append_assoc] using hrows
    rw [← hs'] at hoff
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hoff)
  · exact (serialize_locs_covers p.head p.rows).symm ▸ hn

theorem WritePlan.direct_location_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (before after : List Row) (r : Row)
    (hs : p.direct.toList = before ++ r::after)
    (hi : 0 < r.id ∧ r.id < p.table.size ∧ r.id ≠ p.table.xrefId)
    (hc : r.id ∉ p.compressed.map Prod.fst)
    (hn : (p.rows.toList.map Row.id).Nodup) :
    p.readback.locs.get? r.id =
      some (.direct (serializeList p.head #[] before).1.size) := by
  rw [p.readback_locations_exact h (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi.2.1]
  simp only [show r.id ≠ 0 by omega, ↓reduceIte, Option.bind_some,
    xrefEntry, show (r.id == p.table.xrefId) = false from
      beq_eq_false_iff_ne.mpr hi.2.2, Bool.false_eq_true,
    compressedIndex_absent_exact _ _ _ hc,
    p.direct_offset_exact before after r hs hi.2.1 hn, xrefEntryLocation]

/-- A native source row is read from the complete file at the offset
recorded by its actual serializer. The retained stream bytes are exact;
neither an external decoder nor a supplied reader result is assumed. -/
theorem WritePlan.native_readback_exact (p : WritePlan) (h : p.WithinBounds)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (before after : List Row) (r : Row)
    (hs : p.direct.toList = before ++ r::after)
    (hi : 0 < r.id ∧ r.id < p.table.size ∧ r.id ≠ p.table.xrefId)
    (hc : r.id ∉ p.compressed.map Prod.fst)
    (hn : (p.rows.toList.map Row.id).Nodup)
    (pref : StreamPrefix) (filtered : Bool) (raw : ByteArray)
    (hb : r.body = .stream (pref.fragment filtered) raw) :
    let off := (serializeList p.head #[] before).1.size
    let dict := pref.dict filtered raw.size
    ({num := r.id, header := r.id, loc := .direct off, val := dict,
      stream := some raw} : Entry).Reads p.bytes p.readback.locs
      (some (off + (s!"{r.id} 0 obj\n").toUTF8.size +
        (pref.spelling filtered raw.size).size)) := by
  apply Entry.reads_stream_spelling_exact _ _ _ _ _
    (pref.spelling filtered raw.size) (pref.spelling_exact filtered raw.size) raw
  · have hs := p.direct_span_exact before after r hs
    rw [hb, native_row_bytes_exact] at hs
    simpa only [octets_append, List.append_assoc] using hs
  · exact pref.length_exact ..
  · exact p.direct_location_exact h ht before after r hs hi hc hn

end LeanTex.Core.Pdf
