module

public import LeanTex.Core.PdfProducerProof
public import LeanTex.Core.PdfObjectHeaderProof
public import LeanTex.Core.PdfObjectStreamProof
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfWriteContract
import all LeanTex.Core.PdfRead
import all LeanTex.Core.PdfObjectHeaderProof
import all LeanTex.Core.PdfObj
import all LeanTex.Core.PdfLex

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Recovery from the production file's object streams. The source domain
describes spelling and numeric storage; no parser or codec result is an
assumption. This is a contract of the serialized artifact. -/

/-- The fields of one of the writer's object streams, including its
actual compression choice and the length of the retained payload. -/
public def objectStreamDict (count first : Nat) (filtered : Bool) (len : Nat) : Obj :=
  .dict (#[("Type", .name "ObjStm"), ("N", .int count), ("First", .int first)] ++
    (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int len)])

public theorem objectStreamDict_fields_exact (count first : Nat) (filtered : Bool) (len : Nat) :
    let d := objectStreamDict count first filtered len
    d.get? "Length" = some (.int len) ∧
    d.get? "N" = some (.int count) ∧
    d.get? "First" = some (.int first) ∧
    d.get? "Filter" = (if filtered then some (.name "FlateDecode") else none) ∧
    d.get? "DL" = none ∧ d.get? "DecodeParms" = none := by
  cases filtered <;> simp [objectStreamDict, Obj.get?]

public theorem objectStreamDict_representable_exact (count first : Nat)
    (filtered : Bool) (len : Nat) :
    (objectStreamDict count first filtered len).Representable := by
  cases filtered <;> unfold objectStreamDict <;> apply Obj.Representable.dict
  all_goals intro e he
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, Array.mem_append,
    or_false, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
  repeat (any_goals (rcases he with he | he))
  all_goals try subst e
  all_goals first
    | exact Obj.Representable.name (by simp [Obj.NameSpelling])
    | exact Obj.Representable.int _
    | solve | simp [Obj.NameSpelling]

private theorem push_append (b : ByteArray) (c : UInt8) :
    b.push c = b ++ ⟨#[c]⟩ := by
  apply ByteArray.ext
  rw [ByteArray.data_push, ByteArray.data_append]
  exact Array.push_eq_append

public theorem objectStreamDict_render_exact (count first : Nat) (filtered : Bool) (len : Nat) :
    (objectStreamDict count first filtered len).render =
      (s!"<< /Type /ObjStm /N {count} /First {first}" ++
        (if filtered then " /Filter /FlateDecode" else "") ++
        s!" /Length {len} >>").toUTF8 := by
  cases filtered <;>
    simp only [objectStreamDict, Bool.false_eq_true, ↓reduceIte,
      Obj.render, Obj.renderInto, Array.toList_append, List.append_nil,
      List.cons_append, List.nil_append, Obj.renderEntries,
      push_append, utf8_append, ByteArray.append_assoc,
      ByteArray.empty_append]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append]
  all_goals simp only [String.toUTF8_eq_toByteArray, Int.toString_eq_repr,
    Int.repr_eq_ite, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  all_goals rfl

/-- The dictionary the writer spells for the object stream holding `c`:
its count, its header's size, and its compression choice. -/
public def chunkDict (c : List (Nat × Obj)) : Obj :=
  let data := (objectStream c).bytes
  let z := Flate.deflate data
  objectStreamDict c.length (objectStream c).header.utf8ByteSize
    (decide (z.size < data.size)) (if z.size < data.size then z.size else data.size)

/-- The stream bytes the writer retains for the object stream holding `c`. -/
public def chunkRaw (c : List (Nat × Obj)) : ByteArray :=
  let data := (objectStream c).bytes
  let z := Flate.deflate data
  if z.size < data.size then z else data

/-- One object stream's row spells exactly its typed dictionary and its
retained bytes, whichever compression choice it made. -/
public theorem objStmRow_bytes_exact (id : Nat) (c : List (Nat × Obj)) :
    rowInto ByteArray.empty id (objStmRow id c.length (objectStream c)).body =
      (s!"{id} 0 obj\n").toUTF8 ++ (chunkDict c).render ++ "\nstream\n".toUTF8 ++
        chunkRaw c ++ "\nendstream\nendobj\n".toUTF8 := by
  unfold chunkDict chunkRaw objStmRow flateRow zRow
  split <;> rename_i h
  all_goals simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
    objectStreamDict_render_exact, rowInto, toString, String.append_assoc,
    utf8_append, ByteArray.append_assoc, ByteArray.empty_append]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append,
    String.toUTF8_eq_toByteArray]
  all_goals rfl

private theorem span_append {b : ByteArray} {off : Nat} {cs : List Nat}
    (h : PdfLex.Span b off cs) (tail : ByteArray) :
    PdfLex.Span (b ++ tail) off cs := by
  refine ⟨?_, ?_⟩
  · have := h.bound
    simp only [ByteArray.size_append]
    omega
  · intro j hj
    rw [at?_append_left b tail (off+j) (by have := h.bound; omega)]
    exact h.byte j hj

/-- The complete file begins with the serialized rows, direct rows then
object streams; the xref and footer follow them. -/
public theorem WritePlan.rows_suffix_exact (p : WritePlan) :
    ∃ tail, p.bytes = (serialize p.head p.rows).1 ++ tail := by
  rw [WritePlan.bytes, p.measure.bytes_stream_exact, p.measure_body_exact]
  simp only [ByteArray.append_assoc]
  exact ⟨_, rfl⟩

private theorem serializeList_row_span_exact (head : ByteArray)
    (before after : List Row) (r : Row) :
    PdfLex.Span (serializeList head #[] (before ++ r::after)).1
      (serializeList head #[] before).1.size
      (octets (rowInto ByteArray.empty r.id r.body)) := by
  rw [serializeList_append]
  simp only [serializeList]
  rw [serializeList_bytes, rowInto_bytes]
  exact PdfLex.Span.of_bytes _ _ _

/-- Every row of the plan, direct or object stream, is spelled in the
complete file at the offset its serializer reaches it. -/
public theorem WritePlan.row_span_exact (p : WritePlan) (before after : List Row) (r : Row)
    (hs : p.rows.toList = before ++ r :: after) :
    PdfLex.Span p.bytes (serialize p.head before.toArray).1.size
      (octets (rowInto ByteArray.empty r.id r.body)) := by
  obtain ⟨tail, ht⟩ := p.rows_suffix_exact
  rw [ht]
  apply span_append
  change PdfLex.Span (serializeList p.head #[] p.rows.toList).1 _ _
  rw [hs]
  exact serializeList_row_span_exact ..

/-- The object-stream rows, as a list. -/
private theorem stmRowsOf_getElem? (t : ObjTable) (p : WritePlan) (k : Nat)
    (c : List (Nat × Obj)) (hk : p.chunks[k]? = some c) :
    (stmRowsOf t p.packed).toList[k]? = some (objStmRow (t.objStmId k) c.length (objectStream c)) := by
  simp only [stmRowsOf, List.toList_toArray, List.getElem?_map, List.getElem?_zipIdx,
    WritePlan.packed, hk, Option.map_some, Nat.zero_add]

/-- Where object stream `k` is written: after the direct rows and every
stream before it. -/
public def WritePlan.stmOffset (p : WritePlan) (k : Nat) : Nat :=
  (serialize p.head (p.direct.toList ++ (stmRowsOf p.table p.packed).toList.take k).toArray).1.size

/-- Object stream `k` spells its dictionary and retained bytes at its
offset in the complete file, for every stream the plan writes. -/
public theorem WritePlan.stm_span_exact (p : WritePlan) (k : Nat) (c : List (Nat × Obj))
    (hk : p.chunks[k]? = some c) :
    PdfLex.Span p.bytes (p.stmOffset k)
      (octets (s!"{p.table.objStmId k} 0 obj\n").toUTF8 ++ octets (chunkDict c).render ++
        octets "\nstream\n".toUTF8 ++ octets (chunkRaw c) ++
        octets "\nendstream\nendobj\n".toUTF8) := by
  have hr := stmRowsOf_getElem? p.table p k c hk
  have hlt : k < (stmRowsOf p.table p.packed).toList.length := by
    have := (List.getElem?_eq_some_iff.mp hr).1
    exact this
  have hrows : p.rows.toList =
      (p.direct.toList ++ (stmRowsOf p.table p.packed).toList.take k) ++
        objStmRow (p.table.objStmId k) c.length (objectStream c) ::
          (stmRowsOf p.table p.packed).toList.drop (k + 1) := by
    rw [WritePlan.rows, Array.toList_append, List.append_assoc]
    congr 1
    have he : objStmRow (p.table.objStmId k) c.length (objectStream c) =
        (stmRowsOf p.table p.packed).toList[k] :=
      ((List.getElem_eq_iff hlt).mpr hr).symm
    rw [he, List.getElem_cons_drop, List.take_append_drop]
  have hs := p.row_span_exact _ _ _ hrows
  have hid : (objStmRow (p.table.objStmId k) c.length (objectStream c)).id =
      p.table.objStmId k := flateRow_id ..
  rw [hid, objStmRow_bytes_exact] at hs
  simpa only [WritePlan.stmOffset, octets_append, List.append_assoc] using hs

private theorem objectStreamDict_decode_exact (count first : Nat) (data : ByteArray)
    (h : data.size ≤ maxDecoded) :
    let z := Flate.deflate data
    decodeStream
      (objectStreamDict count first (decide (z.size < data.size))
        (if z.size < data.size then z.size else data.size))
      (if z.size < data.size then z else data) = .ok data := by
  let z := Flate.deflate data
  change decodeStream
    (objectStreamDict count first (decide (z.size < data.size))
      (if z.size < data.size then z.size else data.size))
    (if z.size < data.size then z else data) = .ok data
  by_cases hz : z.size < data.size
  · simp only [hz, decide_true, ↓reduceIte]
    have f := objectStreamDict_fields_exact count first true z.size
    exact decodeStream_deflate_exact _ data h f.2.2.2.1 f.2.2.2.2.1 f.2.2.2.2.2
  · simp only [hz, decide_false, ↓reduceIte]
    exact decodeStream_unfiltered_exact _ data
      (objectStreamDict_fields_exact count first false data.size).2.2.2.1

/-- Every object stream of a bounded plan decodes to its exact payload. -/
public theorem WritePlan.stm_decode_exact (p : WritePlan) (h : p.WithinBounds)
    (c : List (Nat × Obj)) (hc : c ∈ p.chunks) :
    decodeStream (chunkDict c) (chunkRaw c) = .ok (objectStream c).bytes :=
  objectStreamDict_decode_exact c.length (objectStream c).header.utf8ByteSize
    (objectStream c).bytes (h.2.1 c hc)

private theorem objectStreamDict_retained_fields (count first : Nat) (data : ByteArray) :
    let z := Flate.deflate data
    let d := objectStreamDict count first (decide (z.size < data.size))
      (if z.size < data.size then z.size else data.size)
    d.get? "Length" =
      some (.int (if z.size < data.size then z else data).size) ∧
    d.get? "N" = some (.int count) ∧
    d.get? "First" = some (.int first) := by
  let z := Flate.deflate data
  change
    (objectStreamDict count first (decide (z.size < data.size))
      (if z.size < data.size then z.size else data.size)).get? "Length" =
      some (.int (if z.size < data.size then z else data).size) ∧
    (objectStreamDict count first (decide (z.size < data.size))
      (if z.size < data.size then z.size else data.size)).get? "N" =
      some (.int count) ∧
    (objectStreamDict count first (decide (z.size < data.size))
      (if z.size < data.size then z.size else data.size)).get? "First" =
      some (.int first)
  have h := objectStreamDict_fields_exact count first
    (decide (z.size < data.size)) (if z.size < data.size then z.size else data.size)
  refine ⟨?_, h.2.1, h.2.2.1⟩
  by_cases hz : z.size < data.size
  · simpa only [hz, ↓reduceIte] using h.1
  · simpa only [hz, ↓reduceIte] using h.1

/-- The retained stream's dictionary declares exactly its retained byte
length and the stream's object count and payload boundary. -/
public theorem chunkDict_fields_exact (c : List (Nat × Obj)) :
    (chunkDict c).get? "Length" = some (.int (chunkRaw c).size) ∧
    (chunkDict c).get? "N" = some (.int c.length) ∧
    (chunkDict c).get? "First" = some (.int (objectStream c).header.utf8ByteSize) :=
  objectStreamDict_retained_fields c.length (objectStream c).header.utf8ByteSize
    (objectStream c).bytes

/-- The production file itself supplies each object stream's reading. The
location premise is discharged by the writer's xref-location contract. -/
public theorem WritePlan.stm_reads_exact (p : WritePlan) (k : Nat) (c : List (Nat × Obj))
    (hk : p.chunks[k]? = some c) (locs : Std.HashMap Nat Loc)
    (hloc : locs.get? (p.table.objStmId k) = some (.direct (p.stmOffset k))) :
    ({num := p.table.objStmId k, header := p.table.objStmId k, loc := .direct (p.stmOffset k),
      val := chunkDict c, stream := some (chunkRaw c)} : Entry).Reads p.bytes locs
      (some (p.stmOffset k + (s!"{p.table.objStmId k} 0 obj\n").toUTF8.size +
        (chunkDict c).render.size)) :=
  Entry.reads_stream_exact p.bytes locs (p.table.objStmId k) (p.stmOffset k) (chunkDict c)
    (objectStreamDict_representable_exact ..) (chunkRaw c)
    (p.stm_span_exact k c hk) (chunkDict_fields_exact c).1 hloc

private theorem payload_cons_size (id : Nat) (v : Obj) (xs : List (Nat × Obj)) :
    (objectStream ((id,v)::xs)).payload.size =
      v.render.size + 1 + (objectStream xs).payload.size := by
  change (objectStreamList (({} : ObjectStream).push id v) xs).payload.size = _
  rw [objectStreamList_payload]
  simp only [ObjectStream.push, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty, Nat.zero_add]

/-- A header slot points to the size of the actual preceding payload. -/
public theorem objectStreamPositions_entry_exact (before after : List (Nat × Obj))
    (offset num : Nat) (v : Obj) :
    (objectStreamPositions offset (before ++ (num,v)::after))[before.length]? =
      some (num,offset+(objectStream before).payload.size) := by
  induction before generalizing offset with
  | nil =>
    simp only [List.nil_append, objectStreamPositions, List.length_nil,
      List.getElem?_cons_zero, objectStream, objectStreamList, ByteArray.size_empty,
      Nat.add_zero]
  | cons row before ih =>
    rcases row with ⟨id,w⟩
    simp only [List.cons_append, objectStreamPositions, List.length_cons,
      List.getElem?_cons_succ, ih, payload_cons_size]
    congr 2
    omega

/-- A representable source object is recovered from the writer's complete
file, through its own object stream's spelling, compression decision,
decoder, decimal header, and payload parser: the stream at
`before.length / objStmCapacity`, at index `before.length % objStmCapacity`.
Only the two locations still have to be supplied by the actual xref
transcript; no reader result is assumed. -/
public theorem WritePlan.compressed_reads_exact (p : WritePlan) (h : p.WithinBounds)
    (locs : Std.HashMap Nat Loc) (before after : List (Nat × Obj))
    (num : Nat) (v : Obj)
    (hsource : p.compressed = before ++ (num,v)::after)
    (hv : v.Representable) (ha : ∀ e ∈ after, e.2.Representable)
    (hstm : locs.get? (p.table.objStmId (before.length / objStmCapacity)) =
      some (.direct (p.stmOffset (before.length / objStmCapacity))))
    (hloc : locs.get? num = some (.inStm (p.table.objStmId (before.length / objStmCapacity))
      (before.length % objStmCapacity))) :
    ({num, header := num, loc := .inStm (p.table.objStmId (before.length / objStmCapacity))
        (before.length % objStmCapacity),
      val := v, stream := none} : Entry).Reads p.bytes locs none := by
  obtain ⟨cb, ca, hk, hcb, hca⟩ := objStmChunks_entry_exact before after (num, v)
  rw [← hsource] at hk
  change p.chunks[before.length / objStmCapacity]? = some (cb ++ (num, v) :: ca) at hk
  rw [← hcb] at hloc ⊢
  let c := cb ++ (num, v) :: ca
  apply Entry.reads_compressed_exact p.bytes locs num
    (p.table.objStmId (before.length / objStmCapacity)) cb.length
    (p.stmOffset (before.length / objStmCapacity))
    (p.stmOffset (before.length / objStmCapacity) +
      (s!"{p.table.objStmId (before.length / objStmCapacity)} 0 obj\n").toUTF8.size +
        (chunkDict c).render.size)
    c.length (objectStream c).header.utf8ByteSize
    (objectStream cb).payload.size
    ((objectStream c).header.utf8ByteSize +
      (objectStream cb).payload.size + v.render.size)
    (chunkDict c) v (chunkRaw c) (objectStream c).bytes
    (objectStreamPositions 0 c).toArray
    (p.stm_reads_exact _ c hk locs hstm)
    (p.stm_decode_exact h c (List.mem_of_getElem? hk))
    (chunkDict_fields_exact c).2.1 (chunkDict_fields_exact c).2.2
    (objectStream_header_exact c) ?_ ?_ hloc
  · simpa only [List.getElem?_toArray, Nat.zero_add] using
      objectStreamPositions_entry_exact cb ca 0 num v
  · simpa only [String.toUTF8_eq_toByteArray, String.size_toByteArray] using
      objectStream_parse_entry_exact cb ca num v hv (fun e he => ha e (hca e he))

end LeanTex.Core.Pdf
