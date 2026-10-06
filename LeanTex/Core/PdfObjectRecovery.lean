import LeanTex.Core.PdfProducerProof
import LeanTex.Core.PdfObjectHeaderProof
import LeanTex.Core.PdfObjectStreamProof

namespace LeanTex.Core.Pdf
open PdfRead PdfLex

/-! Recovery from the production file's object stream. The source domain
describes spelling and numeric storage; no parser or codec result is an
assumption. This is a contract of the serialized artifact. -/

/-- The fields of the writer's single object stream, including its
actual compression choice and the length of the retained payload. -/
def objectStreamDict (count first : Nat) (filtered : Bool) (len : Nat) : Obj :=
  .dict (#[("Type", .name "ObjStm"), ("N", .int count), ("First", .int first)] ++
    (if filtered then #[("Filter", .name "FlateDecode")] else #[]) ++
    #[("Length", .int len)])

theorem objectStreamDict_fields_exact (count first : Nat) (filtered : Bool) (len : Nat) :
    let d := objectStreamDict count first filtered len
    d.get? "Length" = some (.int len) ∧
    d.get? "N" = some (.int count) ∧
    d.get? "First" = some (.int first) ∧
    d.get? "Filter" = (if filtered then some (.name "FlateDecode") else none) ∧
    d.get? "DL" = none ∧ d.get? "DecodeParms" = none := by
  cases filtered <;> simp [objectStreamDict, Obj.get?]

theorem objectStreamDict_representable_exact (count first : Nat)
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

theorem objectStreamDict_render_exact (count first : Nat) (filtered : Bool) (len : Nat) :
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
  all_goals rfl

def WritePlan.objectDict (p : WritePlan) : Obj :=
  let data := (objectStream p.compressed).bytes
  let z := Flate.deflate data
  objectStreamDict p.compressed.length (objectStream p.compressed).header.utf8ByteSize
    (decide (z.size < data.size)) (if z.size < data.size then z.size else data.size)

def WritePlan.objectRaw (p : WritePlan) : ByteArray :=
  let data := (objectStream p.compressed).bytes
  let z := Flate.deflate data
  if z.size < data.size then z else data

theorem WritePlan.object_body_exact (p : WritePlan) :
    p.measure.body =
      (serialize p.head p.direct).1 ++ (s!"{p.table.objStmId} 0 obj\n").toUTF8 ++
      p.objectDict.render ++ "\nstream\n".toUTF8 ++ p.objectRaw ++
      "\nendstream\nendobj\n".toUTF8 := by
  rw [p.measure_body_exact]
  change (serialize p.head (p.direct.push (flateRow p.table.objStmId
    s!"/Type /ObjStm /N {p.compressed.length} /First {(objectStream p.compressed).header.utf8ByteSize}"
    (objectStream p.compressed).bytes))).1 = _
  simp only [serialize, Array.toList_push, serializeList_append, serializeList]
  unfold WritePlan.objectDict WritePlan.objectRaw flateRow zRow
  split <;> rename_i h
  all_goals simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
    objectStreamDict_render_exact, rowInto, toString, String.append_assoc,
    utf8_append, ByteArray.append_assoc]
  all_goals apply ByteArray.ext
  all_goals apply Array.toList_inj.mp
  all_goals simp only [ByteArray.data_append, Array.toList_append]
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

theorem WritePlan.object_span_exact (p : WritePlan) :
    PdfLex.Span p.bytes (serialize p.head p.direct).1.size
      (octets (s!"{p.table.objStmId} 0 obj\n").toUTF8 ++ octets p.objectDict.render ++
        octets "\nstream\n".toUTF8 ++ octets p.objectRaw ++
        octets "\nendstream\nendobj\n".toUTF8) := by
  have hs : PdfLex.Span p.measure.body (serialize p.head p.direct).1.size
      (octets (s!"{p.table.objStmId} 0 obj\n").toUTF8 ++ octets p.objectDict.render ++
        octets "\nstream\n".toUTF8 ++ octets p.objectRaw ++
        octets "\nendstream\nendobj\n".toUTF8) := by
    rw [p.object_body_exact]
    have hs := PdfLex.Span.of_bytes (serialize p.head p.direct).1
        ((s!"{p.table.objStmId} 0 obj\n").toUTF8 ++ p.objectDict.render ++
          "\nstream\n".toUTF8 ++ p.objectRaw ++ "\nendstream\nendobj\n".toUTF8)
        ByteArray.empty
    change PdfLex.Span _ _ (octets
      ((s!"{p.table.objStmId} 0 obj\n").toUTF8 ++ p.objectDict.render ++
        "\nstream\n".toUTF8 ++ p.objectRaw ++ "\nendstream\nendobj\n".toUTF8)) at hs
    simpa only [octets_append, ByteArray.append_assoc, ByteArray.append_empty,
      List.append_assoc]
      using hs
  have h := span_append hs
      ((s!"{p.table.xrefId} 0 obj\n").toUTF8 ++
        (p.measure.xrefDict p.table).render ++ "\nstream\n".toUTF8 ++
        (if (Flate.deflate p.measure.xrefPayload).size < p.measure.xrefPayload.size
          then Flate.deflate p.measure.xrefPayload else p.measure.xrefPayload) ++
        "\nendstream\nendobj\n".toUTF8 ++
        (s!"startxref\n{p.measure.body.size}\n%%EOF\n").toUTF8)
  rw [WritePlan.bytes, p.measure.bytes_stream_exact]
  simpa only [ByteArray.append_assoc] using h

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

theorem WritePlan.object_decode_exact (p : WritePlan) (h : p.WithinBounds) :
    decodeStream p.objectDict p.objectRaw = .ok (objectStream p.compressed).bytes :=
  objectStreamDict_decode_exact p.compressed.length
    (objectStream p.compressed).header.utf8ByteSize
    (objectStream p.compressed).bytes h.2.2.2.2.1

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
length and the producer's object count and payload boundary. -/
theorem WritePlan.object_fields_exact (p : WritePlan) :
    p.objectDict.get? "Length" = some (.int p.objectRaw.size) ∧
    p.objectDict.get? "N" = some (.int p.compressed.length) ∧
    p.objectDict.get? "First" =
      some (.int (objectStream p.compressed).header.utf8ByteSize) :=
  objectStreamDict_retained_fields p.compressed.length
    (objectStream p.compressed).header.utf8ByteSize (objectStream p.compressed).bytes

/-- The production file itself supplies the object-stream reading. The
location premise is discharged by the writer's xref-location contract. -/
theorem WritePlan.object_reads_exact (p : WritePlan) (locs : Std.HashMap Nat Loc)
    (hloc : locs.get? p.table.objStmId =
      some (.direct (serialize p.head p.direct).1.size)) :
    ({num := p.table.objStmId, header := p.table.objStmId,
      loc := .direct (serialize p.head p.direct).1.size,
      val := p.objectDict, stream := some p.objectRaw} : Entry).Reads p.bytes locs
      (some ((serialize p.head p.direct).1.size +
        (s!"{p.table.objStmId} 0 obj\n").toUTF8.size + p.objectDict.render.size)) :=
  Entry.reads_stream_exact p.bytes locs p.table.objStmId
    (serialize p.head p.direct).1.size p.objectDict
    (objectStreamDict_representable_exact ..) p.objectRaw
    p.object_span_exact p.object_fields_exact.1 hloc

private theorem payload_cons_size (id : Nat) (v : Obj) (xs : List (Nat × Obj)) :
    (objectStream ((id,v)::xs)).payload.size =
      v.render.size + 1 + (objectStream xs).payload.size := by
  change (objectStreamList (({} : ObjectStream).push id v) xs).payload.size = _
  rw [objectStreamList_payload]
  simp only [ObjectStream.push, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty, Nat.zero_add]

/-- A header slot points to the size of the actual preceding payload. -/
theorem objectStreamPositions_entry_exact (before after : List (Nat × Obj))
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
file, through its actual stream spelling, compression decision, decoder,
decimal header, and payload parser. Only the two locations still have to
be supplied by the actual xref transcript; no reader result is assumed. -/
theorem WritePlan.compressed_reads_exact (p : WritePlan) (h : p.WithinBounds)
    (locs : Std.HashMap Nat Loc) (before after : List (Nat × Obj))
    (num : Nat) (v : Obj)
    (hsource : p.compressed = before ++ (num,v)::after)
    (hv : v.Representable) (ha : ∀ e ∈ after, e.2.Representable)
    (hstm : locs.get? p.table.objStmId =
      some (.direct (serialize p.head p.direct).1.size))
    (hloc : locs.get? num = some (.inStm p.table.objStmId before.length)) :
    ({num, header := num, loc := .inStm p.table.objStmId before.length,
      val := v, stream := none} : Entry).Reads p.bytes locs none := by
  apply Entry.reads_compressed_exact p.bytes locs num p.table.objStmId before.length
    (serialize p.head p.direct).1.size
    ((serialize p.head p.direct).1.size +
      (s!"{p.table.objStmId} 0 obj\n").toUTF8.size + p.objectDict.render.size)
    p.compressed.length (objectStream p.compressed).header.utf8ByteSize
    (objectStream before).payload.size
    ((objectStream p.compressed).header.utf8ByteSize +
      (objectStream before).payload.size + v.render.size)
    p.objectDict v p.objectRaw (objectStream p.compressed).bytes
    (objectStreamPositions 0 p.compressed).toArray
    (p.object_reads_exact locs hstm) (p.object_decode_exact h)
    p.object_fields_exact.2.1 p.object_fields_exact.2.2
    (objectStream_header_exact p.compressed) ?_ ?_ hloc
  · rw [hsource]
    simpa only [List.getElem?_toArray, Nat.zero_add] using
      objectStreamPositions_entry_exact before after 0 num v
  · rw [hsource]
    exact objectStream_parse_entry_exact before after num v hv ha

end LeanTex.Core.Pdf
