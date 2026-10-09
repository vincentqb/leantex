module

public import LeanTex.Core.PdfPlanLocations
public import LeanTex.Core.PdfNativeStream
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfWriteContract
import all LeanTex.Core.PdfPlanLocations
import all LeanTex.Core.PdfNativeStream

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Recovery of native stream rows from the serializer's own offsets. -/

public theorem WritePlan.direct_suffix_exact (p : WritePlan) :
    ∃ tail, p.bytes = (serialize p.head p.direct).1 ++ tail := by
  obtain ⟨tail, ht⟩ := p.rows_suffix_exact
  rw [ht]
  change ∃ tail', (serializeList p.head #[] (p.direct ++ stmRowsOf p.table p.packed).toList).1 ++
    tail = (serialize p.head p.direct).1 ++ tail'
  rw [Array.toList_append, serializeList_append, serializeList_bytes]
  exact ⟨_, by rw [ByteArray.append_assoc]; rfl⟩

public theorem WritePlan.direct_span_exact (p : WritePlan) (before after : List Row)
    (r : Row) (hs : p.direct.toList = before ++ r::after) :
    PdfLex.Span p.bytes (serialize p.head before.toArray).1.size
      (octets (rowInto ByteArray.empty r.id r.body)) := by
  apply p.row_span_exact before (after ++ (stmRowsOf p.table p.packed).toList) r
  simp only [WritePlan.rows, Array.toList_append, hs, List.append_assoc, List.cons_append]

public theorem WritePlan.direct_offset_exact (p : WritePlan) (before after : List Row)
    (r : Row) (hs : p.direct.toList = before ++ r::after)
    (hi : r.id < p.table.size) (hn : (p.rows.toList.map Row.id).Nodup) :
    ((indexObjects p.table.size p.serialized.2.toList)[r.id]?).join =
      some (serialize p.head before.toArray).1.size := by
  apply indexObjects_unique_exact _ _ _ _ hi
  · have hs' : p.rows = before.toArray ++ #[r] ++
        (after ++ (stmRowsOf p.table p.packed).toList).toArray := by
      apply Array.toList_inj.mp
      simp only [WritePlan.rows, Array.toList_append, hs, List.append_assoc, List.cons_append,
        List.nil_append]
    have hoff := (serialize_row_exact p.head before.toArray
      (after ++ (stmRowsOf p.table p.packed).toList).toArray r).1
    rw [← hs'] at hoff
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hoff)
  · exact (serialize_locs_covers p.head p.rows).symm ▸ hn

public theorem WritePlan.direct_location_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (before after : List Row) (r : Row)
    (hs : p.direct.toList = before ++ r::after)
    (hi : 0 < r.id ∧ r.id < p.table.size ∧ r.id ≠ p.table.xrefId)
    (hc : r.id ∉ p.compressed.map Prod.fst)
    (hn : (p.rows.toList.map Row.id).Nodup) :
    p.readback.locs.get? r.id =
      some (.direct (serialize p.head before.toArray).1.size) := by
  rw [p.readback_locations_exact (p.entries_size_exact ht (by omega)),
    p.entry_index_exact ht _ hi.2.1]
  simp only [show r.id ≠ 0 by omega, ↓reduceIte, Option.bind_some,
    xrefEntry, show (r.id == p.table.xrefId) = false from
      beq_eq_false_iff_ne.mpr hi.2.2, Bool.false_eq_true,
    compressedIndex_absent_exact _ _ _ hc,
    p.direct_offset_exact before after r hs hi.2.1 hn, xrefEntryLocation]

/-- A native source row is read from the complete file at the offset
recorded by its actual serializer. The retained stream bytes are exact;
neither an external decoder nor a supplied reader result is assumed. -/
public theorem WritePlan.native_readback_exact (p : WritePlan)
    (ht : p.table.ids.toList = List.range' 1 (p.table.size - 1))
    (before after : List Row) (r : Row)
    (hs : p.direct.toList = before ++ r::after)
    (hi : 0 < r.id ∧ r.id < p.table.size ∧ r.id ≠ p.table.xrefId)
    (hc : r.id ∉ p.compressed.map Prod.fst)
    (hn : (p.rows.toList.map Row.id).Nodup)
    (pref : StreamPrefix) (filtered : Bool) (raw : ByteArray)
    (hb : r.body = .stream (pref.fragment filtered) raw) :
    let off := (serialize p.head before.toArray).1.size
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
  · exact p.direct_location_exact ht before after r hs hi hc hn

end LeanTex.Core.Pdf
