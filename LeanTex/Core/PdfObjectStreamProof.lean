module

public import LeanTex.Core.Pdf
public import LeanTex.Core.PdfReadProof
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfRead

namespace LeanTex.Core.Pdf
open PdfRead PdfLex PdfRead.ObjReader

/-! Object recovery in the payload the PDF writer actually builds. These
proofs preserve the writer's accumulator and derive lexical boundaries
from subsequent rendered entries. -/

private theorem payload_cons (id : Nat) (v : Obj) (xs : List (Nat × Obj)) :
    (objectStream ((id,v)::xs)).payload =
      v.render ++ (ByteArray.empty.push 10) ++ (objectStream xs).payload := by
  change (objectStreamList (({} : ObjectStream).push id v) xs).payload = _
  rw [objectStreamList_payload]
  simp only [ObjectStream.push, ByteArray.empty_append]
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_append, Array.push_eq_append,
    ByteArray.data_empty, Array.empty_append]

private theorem payload_start (xs : List (Nat × Obj))
    (hx : ∀ e ∈ xs, e.2.Representable) {b : ByteArray} {i : Nat}
    (hs : PdfLex.Span b i (octets (objectStream xs).payload))
    (he : Start b (i+(objectStream xs).payload.size)) : Start b i := by
  induction xs generalizing i with
  | nil => simpa only [objectStream, objectStreamList, ByteArray.size_empty, Nat.add_zero] using he
  | cons e xs ih =>
    rw [payload_cons] at hs he
    simp only [octets_append, octets_push, octets_empty, List.nil_append] at hs
    have hv := hs.append_left.append_left
    have ht := hs.append_right
    have hn := hs.append_left.append_right
    simp only [octets_length, List.length_append, List.length_singleton] at ht hn
    have hx' : ∀ e ∈ xs, e.2.Representable := fun e hm => hx e (List.mem_cons_of_mem _ hm)
    have he' : Start b (i+e.2.render.size+1+(objectStream xs).payload.size) := by
      simpa only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        Nat.zero_add, Nat.add_assoc] using he
    have hc := ih hx' ht he'
    have stop : Stop b (i+e.2.render.size) :=
      Stop.whitespace (by rw [hn.head]; rfl) (by have := hn.bound; simp at this; omega) hc
    exact (hx e (List.mem_cons_self)).start hv stop.boundary stop.marker


private theorem payload_append (before after : List (Nat × Obj)) :
    (objectStream (before ++ after)).payload =
      (objectStream before).payload ++ (objectStream after).payload := by
  rw [objectStream, objectStreamList_append, objectStreamList_payload]
  rfl

/-- The actual object-stream payload and actual value parser compose.
The offset is the header's `/First` plus the preceding payload's measured
size, and the parser consumes exactly this entry's rendered bytes. The
following objects need only the renderer's structural representability
predicate: their syntax supplies the integer-reference lookahead boundary.
No parser result or decompressor result occurs among the premises.

This artifact theorem closes payload recovery; reading the object-stream
header, selecting its xref index, and inflating its bytes remain separate
composition steps. -/
public theorem objectStream_parse_entry_exact (before after : List (Nat × Obj))
    (id : Nat) (v : Obj) (hv : v.Representable)
    (ha : ∀ e ∈ after, e.2.Representable) :
    let out := objectStream (before ++ (id,v)::after)
    let start := out.header.toUTF8.size + (objectStream before).payload.size
    parseVal out.bytes start = .ok (v,start+v.render.size) := by
  dsimp only
  let out := objectStream (before ++ (id,v)::after)
  let pre := out.header.toUTF8 ++ (objectStream before).payload
  have hb : out.bytes = pre ++ v.render ++ (ByteArray.empty.push 10) ++
      (objectStream after).payload := by
    simp only [out, ObjectStream.bytes, pre, payload_append, payload_cons,
      ByteArray.append_assoc]
  have hvSpan : PdfLex.Span out.bytes pre.size (octets v.render) := by
    rw [hb]
    simpa only [octets, ByteArray.append_assoc] using
      PdfLex.Span.of_bytes pre v.render ((ByteArray.empty.push 10) ++ (objectStream after).payload)
  have hnSpan : PdfLex.Span out.bytes (pre.size+v.render.size) [10] := by
    rw [hb]
    simpa [octets, ByteArray.size_append, ByteArray.push] using
      PdfLex.Span.of_bytes (pre ++ v.render) (ByteArray.empty.push 10) (objectStream after).payload
  have haSpan : PdfLex.Span out.bytes (pre.size+v.render.size+1)
      (octets (objectStream after).payload) := by
    rw [hb]
    simpa only [octets, ByteArray.size_append, ByteArray.append_empty,
      ByteArray.size_push, ByteArray.size_empty, Nat.zero_add] using
      PdfLex.Span.of_bytes (pre ++ v.render ++ (ByteArray.empty.push 10))
        (objectStream after).payload ByteArray.empty
  have he : Start out.bytes (pre.size+v.render.size+1+(objectStream after).payload.size) := by
    have hs : out.bytes.size = pre.size+v.render.size+1+(objectStream after).payload.size := by
      rw [hb]
      simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, Nat.zero_add]
    have hat := at?_ge out.bytes (pre.size+v.render.size+1+(objectStream after).payload.size) (by omega)
    apply Start.non_numeric
    · rw [hat]; rfl
    · rw [hat]; decide
    · rw [hat]; decide
    · rw [hat]; omega
  have hstart := payload_start after ha haSpan he
  have hstop : Stop out.bytes (pre.size+v.render.size) :=
    Stop.whitespace (by rw [hnSpan.head]; rfl)
      (by have := hnSpan.bound; simp at this; omega) hstart
  have result := parseVal_render_span_exact v hv hvSpan hstop
    (hv.start hvSpan hstop.boundary hstop.marker).skip
  simpa only [pre, ByteArray.size_append] using result

end LeanTex.Core.Pdf
