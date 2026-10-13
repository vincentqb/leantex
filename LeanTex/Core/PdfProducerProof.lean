module

public import LeanTex.Core.PdfWriteContract
public import LeanTex.Core.PdfXrefSpelling
public import LeanTex.Core.PdfFlateProof
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfWriteContract
import all LeanTex.Core.PdfRead

namespace LeanTex.Core.Pdf
open PdfRead

/-! Contracts over the complete bytes the checked producer returns. -/

/-- The xref dictionary the writer emits, with its compression choice and two identifiers. -/
public def WriteMeasurement.xrefDict (m : WriteMeasurement) (t : ObjTable) : Obj :=
  let z := Flate.deflate m.xrefPayload
  let filtered := decide (z.size < m.xrefPayload.size)
  xrefStreamDict t.size t.infoId m.widths
    (Flate.fnv64 14695981039346656037 m.body)
    (Flate.fnv64 1099511628211 m.body) filtered
    (if z.size < m.xrefPayload.size then z.size else m.xrefPayload.size)

public theorem WriteMeasurement.bytes_stream_exact (m : WriteMeasurement) (t : ObjTable) :
    let z := Flate.deflate m.xrefPayload
    let raw := if z.size < m.xrefPayload.size then z else m.xrefPayload
    m.bytes t =
      m.body ++ (s!"{t.xrefId} 0 obj\n").toUTF8 ++ (m.xrefDict t).render ++
        "\nstream\n".toUTF8 ++ raw ++ "\nendstream\nendobj\n".toUTF8 ++
        (s!"startxref\n{m.body.size}\n%%EOF\n").toUTF8 := by
  unfold WriteMeasurement.bytes WriteMeasurement.xrefDict WriteMeasurement.xrefDictText
  simp only [serialize, serializeList, flateRow, zRow]
  split <;> rename_i h
  all_goals simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
    xrefStreamDict_render_exact]
  all_goals simp only [rowInto, toString, String.append_assoc, utf8_append,
    ByteArray.append_assoc]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append,
    String.toUTF8_eq_toByteArray]
  all_goals rfl

public theorem WriteMeasurement.readXref_exact (m : WriteMeasurement) (t : ObjTable)
    (hb : m.body.size < 2^64) (hp : m.xrefPayload.size ≤ maxDecoded) :
    readXref (m.bytes t) =
      .ok ((readXrefSubsection m.xrefPayload 1 m.widths.first m.widths.second 0 t.size 0
        {start := m.body.size, root := some 1, trailer := some (m.xrefDict t)}).1) := by
  rw [m.bytes_stream_exact]
  let z := Flate.deflate m.xrefPayload
  have fields := xrefStreamDict_fields_exact t.size t.infoId m.widths
    (Flate.fnv64 14695981039346656037 m.body)
    (Flate.fnv64 1099511628211 m.body)
    (decide (z.size < m.xrefPayload.size))
    (if z.size < m.xrefPayload.size then z.size else m.xrefPayload.size)
  have hd : (m.xrefDict t).Representable := xrefStreamDict_representable_exact ..
  apply readXref_stream_exact m.body t.xrefId (m.xrefDict t) hd _ m.xrefPayload t.size 1
    m.widths hb
  · split <;> rename_i h <;>
      simpa only [WriteMeasurement.xrefDict, z, h, decide_true, decide_false, ↓reduceIte]
        using fields.1
  · by_cases h : z.size < m.xrefPayload.size
    · simp only [show (Flate.deflate m.xrefPayload).size < m.xrefPayload.size from h,
        ↓reduceIte]
      apply decodeStream_deflate_exact _ _ hp
      · simpa only [WriteMeasurement.xrefDict, z, h, decide_true, ↓reduceIte]
          using fields.2.2.2.2.2.2.1
      · exact fields.2.2.2.2.2.2.2.1
      · exact fields.2.2.2.2.2.2.2.2
    · simp only [show ¬ (Flate.deflate m.xrefPayload).size < m.xrefPayload.size from h,
        ↓reduceIte]
      apply decodeStream_unfiltered_exact
      simpa only [WriteMeasurement.xrefDict, z, h, decide_false, Bool.false_eq_true, ↓reduceIte]
        using fields.2.2.2.2.2.2.1
  · exact fields.2.1
  · exact fields.2.2.1
  · exact fields.2.2.2.1
  · exact fields.2.2.2.2.1
  · exact fields.2.2.2.2.2.1

public theorem WritePlan.readXref_exact (p : WritePlan) (h : p.WithinBounds) :
    readXref p.bytes =
      .ok ((readXrefSubsection (Xref.encode p.widths p.entries) 1 p.widths.first
        p.widths.second 0 p.table.size 0
        {start := p.measure.body.size, root := some 1,
         trailer := some (p.measure.xrefDict p.table)}).1) := by
  exact p.measure.readXref_exact p.table h.1 h.2.2

public theorem WritePlan.readXref_contract (p : WritePlan) (bounds : p.WithinBounds) :
    ∃ x, readXref p.bytes = .ok x ∧ x.root = some 1 ∧
      (x.trailer.bind (·.get? "Size")).bind Obj.int? = some p.table.size ∧
      x.start = p.measure.body.size := by
  let x0 : PdfRead.Xref :=
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)}
  refine ⟨(readXrefSubsection (Xref.encode p.widths p.entries) 1 p.widths.first
    p.widths.second 0 p.table.size 0 x0).1, p.readXref_exact bounds, ?_⟩
  have hm := readXrefSubsection_metadata_exact (Xref.encode p.widths p.entries)
    1 p.widths.first p.widths.second 0 p.table.size 0 x0
  refine ⟨hm.1, ?_, hm.2.2⟩
  rw [hm.2.1]
  have fields := xrefStreamDict_fields_exact p.table.size p.table.infoId p.measure.widths
    (Flate.fnv64 14695981039346656037 p.measure.body)
    (Flate.fnv64 1099511628211 p.measure.body)
    (decide ((Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size))
    (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
      then (Flate.deflate p.measure.xrefPayload).size else p.measure.xrefPayload.size)
  change ((p.measure.xrefDict p.table).get? "Size").bind Obj.int? = some p.table.size
  rw [show (p.measure.xrefDict p.table).get? "Size" =
    some (.int p.table.size) from fields.2.2.1]
  rfl

public theorem WritePlan.checked_readXref_contract (p : WritePlan) (b : ByteArray)
    (h : p.checked = .ok b) :
    ∃ x, readXref b = .ok x ∧ x.root = some 1 ∧
      (x.trailer.bind (·.get? "Size")).bind Obj.int? = some p.table.size ∧
      x.start = p.measure.body.size := by
  obtain ⟨domain, rfl⟩ := (p.checked_exact b).mp h
  exact p.readXref_contract domain.1

public theorem write_readXref_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry) (streams : Array (ByteArray × Option ByteArray))
    (tree : Struct.Tree) (ops : Array (Array ContentOp))
    (programs : Array (ByteArray × Bool))
    (h : (prepare geom fs pages info imgs outline streams tree ops programs).WithinBounds) :
    ∃ x, readXref (write geom fs pages info imgs outline streams tree ops programs) = .ok x ∧
      x.root = some 1 ∧
      (x.trailer.bind (·.get? "Size")).bind Obj.int? = some (x.locs.size + 1) := by
  let p := prepare geom fs pages info imgs outline streams tree ops programs
  change p.WithinBounds at h
  change ∃ x, readXref p.bytes = .ok x ∧ x.root = some 1 ∧
    (x.trailer.bind (·.get? "Size")).bind Obj.int? = some (x.locs.size + 1)
  obtain ⟨x, hx, hr, hs, _⟩ := p.readXref_contract h
  have he := prepare_entries_contract geom fs pages info imgs outline streams tree ops programs
  change p.entries.size = p.table.size ∧
    p.entries[0]?.bind xrefEntryLocation = none ∧
    (∀ i, 0 < i → i < p.entries.size →
      (p.entries[i]?.bind xrefEntryLocation).isSome = true) at he
  let x0 : PdfRead.Xref :=
    {start := p.measure.body.size, root := some 1,
     trailer := some (p.measure.xrefDict p.table)}
  have hv : x =
      (readXrefSubsection (Xref.encode p.widths p.entries) 1 p.widths.first p.widths.second
        0 p.table.size 0 x0).1 := by
    have hp := p.readXref_exact h
    rw [hx] at hp
    exact Except.ok.inj hp
  have hn : x.locs.size = p.table.size - 1 := by
    rw [hv]
    exact readXrefSubsection_size_exact p.widths p.entries p.entries_fits
      he.2.1 he.2.2 p.table.size (by omega) x0 rfl
  have hp : 0 < p.table.size := by
    have ht := prepare_table_exact geom fs pages info imgs outline streams tree ops programs
    change p.table = tableOf geom fs pages imgs outline tree at ht
    rw [ht]
    simp only [tableOf, objTable]
    omega
  refine ⟨x, hx, hr, ?_⟩
  rw [hs]
  have hcount : p.table.size = x.locs.size + 1 := by omega
  rw [hcount]

public theorem writeChecked_readXref_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry) (streams : Array (ByteArray × Option ByteArray))
    (tree : Struct.Tree) (ops : Array (Array ContentOp))
    (programs : Array (ByteArray × Bool)) (b : ByteArray)
    (h : writeChecked geom fs pages info imgs outline streams tree ops programs = .ok b) :
    ∃ x, readXref b = .ok x ∧ x.root = some 1 ∧
      (x.trailer.bind (·.get? "Size")).bind Obj.int? = some (x.locs.size + 1) := by
  obtain ⟨_, bounds, hb⟩ := (writeChecked_exact geom fs pages info imgs outline streams
    tree ops programs b).mp h
  rw [← hb]
  exact write_readXref_exact geom fs pages info imgs outline streams tree ops programs bounds.1

end LeanTex.Core.Pdf
