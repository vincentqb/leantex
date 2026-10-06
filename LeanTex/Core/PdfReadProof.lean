import LeanTex.Core.PdfObjContainers

namespace LeanTex.Core.PdfRead

open PdfLex ObjReader

/-- Syntactic representability supplies the entire execution contract,
including reference lookahead, nested stack transitions and a transition
count bounded by the rendered bytes. -/
theorem Obj.Representable.reads {o : Obj} (h : o.Representable) : Reads o := by
  induction h with
  | null => exact Reads.null
  | bool v => exact Reads.bool v
  | int n => exact Reads.int n
  | real hs => exact Reads.real hs
  | str hs => exact Reads.str hs
  | name hs => exact Reads.name hs
  | arr _ ih => exact Reads.arr ih
  | dict hk _ ih => exact Reads.dict hk ih
  | ref num gen => exact Reads.ref num gen

/-- Recover a rendered object in its enclosing file. The premises describe
source bytes, lexical separation, and the starting whitespace; none
assumes a parser result. The execution bound comes from the source span. -/
theorem parseVal_render_span_exact {b : ByteArray} {i p : Nat}
    (o : Obj) (h : o.Representable) (hs : Span b i (octets o.render))
    (he : Stop b (i+o.render.size)) (hw : skipWs b p = i) :
    parseVal b p = .ok (o,i+o.render.size) := by
  obtain ⟨n,hn,htrace⟩ := h.reads.run #[] hs he hw
  rw [accept_empty] at htrace
  apply parseVal_of_runs htrace
  have hb := hs.bound
  simp only [octets_length] at hb
  omega

/-- The actual object reader inverts the actual renderer on the recursive
syntactic domain. The result also certifies full byte consumption. Raw
strings must carry exactly one complete string spelling; names and keys
are nonempty byte strings; real spellings are numeric tokens containing a
decimal point. No depth, object-count or integer-width bound is needed:
the proof bounds execution by the finite rendered byte array. -/
theorem parseVal_render_id (o : Obj) (h : o.Representable) :
    parseVal o.render 0 = .ok (o,o.render.size) := by
  have hs : Span o.render 0 (octets o.render) := by
    simpa only [octets,ByteArray.empty_append,ByteArray.append_empty,ByteArray.size_empty]
      using Span.of_bytes ByteArray.empty o.render ByteArray.empty
  have he : Stop o.render (0+o.render.size) := Stop.eof (by omega)
  have hr := h.reads
  have hstart := hr.start hs he.boundary he.marker
  simpa only [Nat.zero_add] using parseVal_render_span_exact o h hs he hstart.skip

/-- A nonnumeric token following the writer's line feed blocks integer
reference lookahead, independently of every later byte. -/
theorem parseVal_render_delimited_exact (pre post : ByteArray)
    (o : Obj) (h : o.Representable) (c : UInt8)
    (hw : isWs c.toNat = false) (hc : c.toNat ≠ 37) (hr : c.toNat ≠ 82)
    (hd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) :
    parseVal (pre ++ o.render ++ (ByteArray.empty.push 10).push c ++ post) pre.size =
      .ok (o,pre.size+o.render.size) := by
  let b := pre ++ o.render ++ (ByteArray.empty.push 10).push c ++ post
  have hs : Span b pre.size (octets o.render) := by
    simpa only [b, octets, ByteArray.append_assoc] using
      Span.of_bytes pre o.render ((ByteArray.empty.push 10).push c ++ post)
  have ht : Span b (pre.size+o.render.size) [10,c.toNat] := by
    simpa [b, octets, ByteArray.size_append, ByteArray.push] using
      Span.of_bytes (pre ++ o.render) ((ByteArray.empty.push 10).push c) post
  have hn : Start b (pre.size+o.render.size+1) :=
    Start.non_numeric (by rw [ht.tail.head]; exact hw)
      (by rw [ht.tail.head]; exact hc) (by rw [ht.tail.head]; exact hr)
      (by rw [ht.tail.head]; exact hd)
  have he : Stop b (pre.size+o.render.size) :=
    Stop.whitespace (by rw [ht.head]; rfl) (by have := ht.bound; simp at this; omega) hn
  exact parseVal_render_span_exact o h hs he (h.reads.start hs he.boundary he.marker).skip

end LeanTex.Core.PdfRead
