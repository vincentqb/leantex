module

public import LeanTex.Core.PdfAllocation
public import LeanTex.Core.PdfRowRecovery
public import LeanTex.Core.PdfSortProof
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfWriteContract
import all LeanTex.Core.PdfProducerProof
import all LeanTex.Core.PdfObjectRecovery
import all LeanTex.Core.PdfPlanLocations
import all LeanTex.Core.PdfRead
import all LeanTex.Core.PdfCensus
import all LeanTex.Core.PdfXrefSpelling

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Recovery of every object of an allocated native plan. The source
premises describe allocation, spelling, and numeric storage; none names
a parser result. -/

/-- The two source transcripts partition the consecutive allocation. -/
public structure WritePlan.Allocated (p : WritePlan) : Prop where
  ids : p.table.ids.toList = List.range' 1 (p.table.size - 1)
  sources : (p.compressed.map Prod.fst ++ p.direct.toList.map Row.id ++
    [p.table.objStmId, p.table.xrefId]).Perm p.table.ids.toList

public theorem prepare_allocated_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    (prepare geom fs pages info imgs outline streams tree ops programs).Allocated :=
  ⟨prepare_ids_exact .., prepare_allocation_exact ..⟩

private theorem WritePlan.Allocated.nodup {p : WritePlan} (h : p.Allocated) :
    (p.compressed.map Prod.fst ++ p.direct.toList.map Row.id ++
      [p.table.objStmId, p.table.xrefId]).Nodup := by
  apply h.sources.symm.nodup
  rw [h.ids]
  exact List.nodup_range' 1

private theorem WritePlan.Allocated.range {p : WritePlan} (h : p.Allocated)
    (id : Nat) :
    id ∈ p.compressed.map Prod.fst ++ p.direct.toList.map Row.id ++
      [p.table.objStmId, p.table.xrefId] ↔ 0 < id ∧ id < p.table.size := by
  rw [h.sources.mem_iff, h.ids, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hi
    exact ⟨id-1, by omega, by omega⟩

private theorem WritePlan.Allocated.parts {p : WritePlan} (h : p.Allocated) :
    (p.compressed.map Prod.fst).Nodup ∧
    (p.rows.toList.map Row.id).Nodup ∧
    (∀ id ∈ p.direct.toList.map Row.id, id ∉ p.compressed.map Prod.fst) ∧
    p.table.objStmId ∉ p.compressed.map Prod.fst ∧
    p.table.xrefId ∉ p.compressed.map Prod.fst ∧
    (∀ id ∈ p.direct.toList.map Row.id, id ≠ p.table.xrefId) ∧
    p.table.objStmId ≠ p.table.xrefId := by
  have hn := h.nodup
  rw [List.append_assoc, List.nodup_append] at hn
  have hd := List.nodup_append.mp hn.2.1
  refine ⟨hn.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (p.direct.push _).toList.map Row.id |>.Nodup
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨hd.1, by simp, ?_⟩
    intro id hi n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst n
    apply hd.2.2 id hi
    simp only [flateRow, zRow]
    split <;> simp
  · intro id hi hc
    exact hn.2.2 id hc id (by simp [hi]) rfl
  · intro hc
    exact hn.2.2 _ hc _ (by simp) rfl
  · intro hc
    exact hn.2.2 _ hc _ (by simp) rfl
  · intro id hi
    exact hd.2.2 id hi _ (by simp)
  · simpa using (List.nodup_cons.mp hd.2.1).1

private theorem WritePlan.Allocated.stm {p : WritePlan} (h : p.Allocated) :
    0 < p.table.objStmId ∧ p.table.objStmId < p.table.size ∧
      p.table.objStmId ≠ p.table.xrefId ∧
      p.table.objStmId ∉ p.compressed.map Prod.fst := by
  have hr := (h.range p.table.objStmId).mp (by simp)
  exact ⟨hr.1, hr.2, h.parts.2.2.2.2.2.2, h.parts.2.2.2.1⟩

private theorem WritePlan.Allocated.xref {p : WritePlan} (h : p.Allocated) :
    0 < p.table.xrefId ∧ p.table.xrefId < p.table.size :=
  (h.range p.table.xrefId).mp (by simp)

private theorem WritePlan.readback_metadata (p : WritePlan) :
    p.readback.start = p.measure.body.size ∧
      p.readback.trailer = some (p.measure.xrefDict p.table) := by
  have h := readXrefSubsection_metadata_exact (Xref.encode p.entries)
    1 4 2 0 p.table.size 0
    {start := p.measure.body.size, root := some 1,
      trailer := some (p.measure.xrefDict p.table)}
  exact ⟨h.2.2, h.2.1⟩

private theorem WritePlan.xref_location (p : WritePlan)
    (hb : p.WithinBounds) (ha : p.Allocated) :
    p.readback.locs.get? p.table.xrefId = some (.direct p.measure.body.size) := by
  rw [p.readback_locations_exact hb (p.entries_size_exact ha.ids (by
    have := ha.xref; omega)), p.entry_index_exact ha.ids _ ha.xref.2]
  simp only [show p.table.xrefId ≠ 0 by have := ha.xref; omega,
    ↓reduceIte, Option.bind_some, xrefEntry, beq_self_eq_true, xrefEntryLocation]
  rw [p.measure_body_exact]

private theorem WritePlan.xref_reads (p : WritePlan) (hb : p.WithinBounds)
    (ha : p.Allocated) :
    let z := Flate.deflate p.measure.xrefPayload
    let raw := if z.size < p.measure.xrefPayload.size then z else p.measure.xrefPayload
    ({num := p.table.xrefId, header := p.table.xrefId,
      loc := .direct p.measure.body.size, val := p.measure.xrefDict p.table,
      stream := some raw} : Entry).Reads p.bytes p.readback.locs
      (some (p.measure.body.size + (s!"{p.table.xrefId} 0 obj\n").toUTF8.size +
        (p.measure.xrefDict p.table).render.size)) := by
  dsimp only
  have hd : (p.measure.xrefDict p.table).Representable :=
    xrefStreamDict_representable_exact ..
  apply Entry.reads_stream_exact _ _ _ _ _ hd _
  · rw [WritePlan.bytes, p.measure.bytes_stream_exact]
    have hs := PdfLex.Span.of_bytes p.measure.body
      ((s!"{p.table.xrefId} 0 obj\n").toUTF8 ++
        (p.measure.xrefDict p.table).render ++ "\nstream\n".toUTF8 ++
        (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
          then Flate.deflate p.measure.xrefPayload else p.measure.xrefPayload) ++
        "\nendstream\nendobj\n".toUTF8)
      (s!"startxref\n{p.measure.body.size}\n%%EOF\n").toUTF8
    change PdfLex.Span _ _ (octets
      ((s!"{p.table.xrefId} 0 obj\n").toUTF8 ++
        (p.measure.xrefDict p.table).render ++ "\nstream\n".toUTF8 ++
        (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
          then Flate.deflate p.measure.xrefPayload else p.measure.xrefPayload) ++
        "\nendstream\nendobj\n".toUTF8)) at hs
    simpa only [octets_append, List.append_assoc, ByteArray.append_assoc] using hs
  · have hf := (xrefStreamDict_fields_exact p.table.size p.table.infoId
      (Flate.fnv64 14695981039346656037 p.measure.body)
      (Flate.fnv64 1099511628211 p.measure.body)
      (decide ((Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size))
      (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
        then (Flate.deflate p.measure.xrefPayload).size else p.measure.xrefPayload.size)).1
    change (p.measure.xrefDict p.table).get? "Length" = _ at hf
    by_cases h : (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
    all_goals simpa only [h, ↓reduceIte] using hf
  · exact p.xref_location hb ha

private theorem WritePlan.start_boundary (p : WritePlan) :
    (isWs (at? p.bytes p.readback.start) || at? p.bytes p.readback.start == 256 ||
      (p.readback.start > 0 && !(isWs (at? p.bytes (p.readback.start - 1)) ||
        isDelim (at? p.bytes (p.readback.start - 1))))) = false := by
  rw [p.readback_metadata.1]
  have ht : ∃ tail, p.bytes = p.measure.body ++ tail := by
    rw [WritePlan.bytes, p.measure.bytes_stream_exact]
    simp only [ByteArray.append_assoc]
    exact ⟨_, rfl⟩
  have hn : PdfLex.Span p.bytes p.measure.body.size (octets (toString p.table.xrefId).toUTF8) := by
    rw [WritePlan.bytes, p.measure.bytes_stream_exact]
    rw [show (s!"{p.table.xrefId} 0 obj\n").toUTF8 =
      (toString p.table.xrefId).toUTF8 ++ " 0 obj\n".toUTF8 from
      utf8_append (toString p.table.xrefId) " 0 obj\n"]
    change PdfLex.Span (p.measure.body ++
      ((toString p.table.xrefId).toUTF8 ++ " 0 obj\n".toUTF8) ++
      (p.measure.xrefDict p.table).render ++ "\nstream\n".toUTF8 ++
      (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
        then Flate.deflate p.measure.xrefPayload else p.measure.xrefPayload) ++
      "\nendstream\nendobj\n".toUTF8 ++
      (s!"startxref\n{p.measure.body.size}\n%%EOF\n").toUTF8) _ _
    simp only [ByteArray.append_assoc]
    simpa only [ByteArray.append_assoc, octets] using PdfLex.Span.of_bytes p.measure.body
      (toString p.table.xrefId).toUTF8
      (" 0 obj\n".toUTF8 ++ (p.measure.xrefDict p.table).render ++ "\nstream\n".toUTF8 ++
        (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
          then Flate.deflate p.measure.xrefPayload else p.measure.xrefPayload) ++
        "\nendstream\nendobj\n".toUTF8 ++
        (s!"startxref\n{p.measure.body.size}\n%%EOF\n").toUTF8)
  have hd := number_byte (ObjReader.numeric_first hn
    (Number.nat_nonempty p.table.xrefId) (nat_numeric p.table.xrefId))
  have hp : ∃ pre, p.measure.body = pre ++ "\n".toUTF8 := by
    rw [p.object_body_exact, show "\nendstream\nendobj\n".toUTF8 =
      "\nendstream\nendobj".toUTF8 ++ "\n".toUTF8 from by
        simp only [String.toUTF8_eq_toByteArray]
        rfl]
    rw [← ByteArray.append_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨pre, hp⟩ := hp
  obtain ⟨tail, ht⟩ := ht
  have hw : at? p.bytes (p.measure.body.size - 1) = 10 := by
    have hs : p.measure.body.size = pre.size + 1 := by
      rw [hp, ByteArray.size_append]
      simp only [String.toUTF8_eq_toByteArray]
      rfl
    rw [ht, at?_append_left _ _ _ (by omega), hs, hp]
    simp only [Nat.add_sub_cancel]
    have h := PdfLex.Span.of_bytes pre "\n".toUTF8 ByteArray.empty
    simp only [String.toUTF8_eq_toByteArray] at h
    change PdfLex.Span _ _ [10] at h
    simpa only [ByteArray.append_empty, String.toUTF8_eq_toByteArray] using h.head
  simp only [hd.2.1, beq_eq_false_iff_ne.mpr hd.2.2.2.2, hw]
  simp only [show isWs 10 = true from rfl, Bool.true_or, Bool.not_true,
    Bool.and_false, Bool.false_or]

private def WritePlan.SourceValue (p : WritePlan) (id : Nat) (v : Obj) : Prop :=
  (id,v) ∈ p.compressed ∨
    (id ∉ p.compressed.map Prod.fst ∧ PdfCensus.kindOf v ≠ .font)

private theorem WritePlan.source_reads (p : WritePlan)
    (hb : p.WithinBounds) (ha : p.Allocated)
    (hc : ∀ e ∈ p.compressed, e.2.Representable)
    (hn : ∀ r ∈ p.direct, r.body.Native)
    (id : Nat) (hi : 0 < id ∧ id < p.table.size) :
    ∃ e : Entry × Option Nat, e.1.num = id ∧
      e.1.Reads p.bytes p.readback.locs e.2 ∧ p.SourceValue id e.1.val := by
  have hm := (ha.range id).mpr hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with (hm | hm) | hm | hm
  · obtain ⟨⟨n,v⟩, hv, hid⟩ := List.mem_map.mp hm
    dsimp only at hid
    subst n
    obtain ⟨before, after, hs⟩ := List.mem_iff_append.mp hv
    have hr := (p.compressed_readback_exact hb ha.ids ha.stm ha.parts.1
      before after id v hs ⟨hi.1, hi.2, by
        intro he; exact ha.parts.2.2.2.2.1 (he ▸ List.mem_map.mpr ⟨(id,v),hv,rfl⟩)⟩
      (hc _ hv) (by
        intro e he
        apply hc e
        simp only [hs, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inr he))).2
    exact ⟨(_, none), rfl, hr, Or.inl hv⟩
  · obtain ⟨r, hr, hid⟩ := List.mem_map.mp hm
    subst id
    obtain ⟨before, after, hs⟩ := List.mem_iff_append.mp hr
    obtain ⟨pref, filtered, raw, hbody⟩ := hn r (Array.mem_toList_iff.mp hr)
    have hnot := ha.parts.2.2.1 r.id (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hx := ha.parts.2.2.2.2.2.1 r.id (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hh := p.native_readback_exact hb ha.ids before after r hs
      ⟨hi.1, hi.2, hx⟩ hnot ha.parts.2.1 pref filtered raw hbody
    exact ⟨(_, _), rfl, hh, Or.inr ⟨hnot, pref.kind_exact filtered raw.size⟩⟩
  · subst id
    have hh := p.object_reads_exact p.readback.locs
      (p.object_location_exact hb ha.ids ha.stm.1 ha.stm.2.1
        ha.stm.2.2.1 ha.stm.2.2.2)
    refine ⟨(_, _), rfl, hh, Or.inr ⟨ha.stm.2.2.2, ?_⟩⟩
    have hk (count first : Nat) (filtered : Bool) (len : Nat) :
        PdfCensus.kindOf (objectStreamDict count first filtered len) ≠ .font := by
      cases filtered <;> change PdfCensus.Kind.objStm ≠ .font <;> decide
    exact hk _ _ _ _
  · subst id
    refine ⟨(_, _), rfl, p.xref_reads hb ha,
      Or.inr ⟨ha.parts.2.2.2.2.1, ?_⟩⟩
    have hk (count info : Nat) (idA idB : UInt64) (filtered : Bool) (len : Nat) :
        PdfCensus.kindOf (xrefStreamDict count info idA idB filtered len) ≠ .font := by
      cases filtered <;> change PdfCensus.Kind.xref ≠ .font <;> decide
    exact hk _ _ _ _ _ _

private theorem WritePlan.keys_mem_iff (p : WritePlan) (id : Nat) :
    id ∈ p.readback.locs.keysArray.qsort (· < ·) ↔
      (p.readback.locs.get? id).isSome = true := by
  rw [(qsort_perm_exact _ _).mem_iff, Std.HashMap.mem_keysArray,
    Std.HashMap.mem_iff_isSome_getElem?, Std.HashMap.get?_eq_getElem?]

private theorem WritePlan.keys_range (p : WritePlan)
    (hb : p.WithinBounds) (ha : p.Allocated)
    (id : Nat) (hi : id ∈ p.readback.locs.keysArray.qsort (· < ·)) :
    0 < id ∧ id < p.table.size := by
  have hs := p.entries_size_exact ha.ids (by have := ha.xref; omega)
  have hm := (p.keys_mem_iff id).mp hi
  rw [p.readback_locations_exact hb hs] at hm
  have hr : id < p.table.size := by
    by_cases h : id < p.table.size
    · exact h
    · rw [Array.getElem?_eq_none (by omega)] at hm
      contradiction
  have hz : id ≠ 0 := by
    intro h
    subst id
    rw [p.entry_index_exact ha.ids 0 hr] at hm
    contradiction
  exact ⟨by omega, hr⟩

private theorem WritePlan.compressed_unique (p : WritePlan) (ha : p.Allocated)
    (id : Nat) (u v : Obj) (hu : (id,u) ∈ p.compressed)
    (hv : (id,v) ∈ p.compressed) : u = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have hij := ha.parts.1.eq_of_getElem?_eq (i := i) (j := j)
    (by simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hi).1)
    (by simp only [List.getElem?_map, hi, hj, Option.map_some])
  have he : (id,u) = (id,v) := Option.some.inj (by rw [← hi, hij, hj])
  exact congrArg Prod.snd he

/-- Every font dictionary read from an allocated native plan is one of its
compressed source objects, and every compressed source reference resolves
to its original value. This composes the actual xref parser, both stream
codecs, object-stream lookup, key enumeration, and object reader. -/
public theorem WritePlan.objects_recovered_exact (p : WritePlan)
    (hb : p.WithinBounds) (ha : p.Allocated)
    (hc : ∀ e ∈ p.compressed, e.2.Representable)
    (hn : ∀ r ∈ p.direct, r.body.Native) :
    ∃ es, objectsOf p.bytes p.readback = .ok es ∧
      (∀ e ∈ es.val, PdfCensus.kindOf e.val = .font →
        (e.num, e.val) ∈ p.compressed) ∧
      (∀ id v, (id,v) ∈ p.compressed →
        PdfCensus.deref es.val (.ref id 0) = v) := by
  classical
  let model (id : Nat) : Entry × Option Nat :=
    if h : 0 < id ∧ id < p.table.size then
      Classical.choose (p.source_reads hb ha hc hn id h) else default
  have hm (id : Nat) (hi : 0 < id ∧ id < p.table.size) :
      (model id).1.num = id ∧
        (model id).1.Reads p.bytes p.readback.locs (model id).2 ∧
          p.SourceValue id (model id).1.val := by
    dsimp only [model]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (p.source_reads hb ha hc hn id hi)
  have hkeys (id : Nat) (hi : 0 < id ∧ id < p.table.size) :
      id ∈ p.readback.locs.keysArray.qsort (· < ·) := by
    apply (p.keys_mem_iff id).mpr
    have hloc := (hm id hi).2.1.2.1
    rw [(hm id hi).1] at hloc
    rw [hloc]
    rfl
  obtain ⟨es, he, hem⟩ := objectsOf_reads_exact p.bytes p.readback model
    p.start_boundary (by
      intro id hi size hs
      rw [p.readback_metadata.2] at hs
      have hsize := (xrefStreamDict_fields_exact p.table.size p.table.infoId
        (Flate.fnv64 14695981039346656037 p.measure.body)
        (Flate.fnv64 1099511628211 p.measure.body)
        (decide ((Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size))
        (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
          then (Flate.deflate p.measure.xrefPayload).size else p.measure.xrefPayload.size)).2.2.1
      change (p.measure.xrefDict p.table).get? "Size" = _ at hsize
      simp only [Option.bind_some, hsize, Obj.int?, Option.map_some,
        Int.toNat_natCast, Option.mem_some_iff] at hs
      subst size
      exact (p.keys_range hb ha id hi).2)
    (by
      intro id hi
      exact ⟨(hm id (p.keys_range hb ha id hi)).1,
        (hm id (p.keys_range hb ha id hi)).2.1⟩)
  have hmodel (id : Nat) (v : Obj) (hv : (id,v) ∈ p.compressed) :
      (model id).1.val = v := by
    have hid : id ∈ p.compressed.map Prod.fst :=
      List.mem_map.mpr ⟨(id,v), hv, rfl⟩
    have hi := (ha.range id).mp (by simp only [List.mem_append]; exact Or.inl (Or.inl hid))
    rcases (hm id hi).2.2 with h | h
    · exact p.compressed_unique ha id _ v h hv
    · exact False.elim (h.1 hid)
  refine ⟨es, he, ?_, ?_⟩
  · intro e he hf
    rw [hem] at he
    obtain ⟨id, hi, rfl⟩ := Array.mem_map.mp he
    have hh := hm id (p.keys_range hb ha id hi)
    rw [hh.1]
    rcases hh.2.2 with hc | hc
    · exact hc
    · exact False.elim (hc.2 hf)
  · intro id v hv
    have hid : id ∈ p.compressed.map Prod.fst :=
      List.mem_map.mpr ⟨(id,v), hv, rfl⟩
    have hi := (ha.range id).mp (by simp only [List.mem_append]; exact Or.inl (Or.inl hid))
    have hmem : (model id).1 ∈ es.val := by
      rw [hem]
      exact Array.mem_map.mpr ⟨id, hkeys id hi, rfl⟩
    have hfound : (es.val.find? (fun e => e.num == id)).isSome = true :=
      Array.find?_isSome.mpr ⟨(model id).1, hmem, by simp only [(hm id hi).1, beq_self_eq_true]⟩
    obtain ⟨e, hfind⟩ := Option.isSome_iff_exists.mp hfound
    have hnume : e.num = id :=
      beq_iff_eq.mp (Array.find?_some (p := fun (e : Entry) => e.num == id) hfind)
    have hmem := Array.mem_of_find?_eq_some hfind
    rw [hem] at hmem
    obtain ⟨j, hj, rfl⟩ := Array.mem_map.mp hmem
    have hjid : j = id := (hm j (p.keys_range hb ha j hj)).1.symm.trans hnume
    subst j
    simp only [PdfCensus.deref, hfind, Option.map_some, Option.getD_some,
      hmodel id v hv]

end LeanTex.Core.Pdf
