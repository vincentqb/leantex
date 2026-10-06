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
  obtain ⟨n,hn,htrace⟩ := hr.run #[] hs he hstart.skip
  rw [accept_empty] at htrace
  apply parseVal_of_runs (by simpa only [Nat.zero_add] using htrace)
  omega

end LeanTex.Core.PdfRead
