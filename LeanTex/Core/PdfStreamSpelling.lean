import LeanTex.Core.PdfReadProof

namespace LeanTex.Core.PdfRead

open PdfLex ObjReader

/-- The native stream writer leaves a second space when its dictionary
prefix is empty. This spelling preserves those emitted bytes. -/
def Obj.paddedDict (es : Array (String × Obj)) : ByteArray :=
  Obj.renderEntries "<<  ".toUTF8 es.toList ++ ">>".toUTF8

theorem Obj.paddedDict_octets_exact (es : Array (String × Obj)) :
    octets (Obj.paddedDict es) = 60 :: 60 :: 32 :: 32 :: Obj.dictBody es.toList := by
  unfold Obj.paddedDict
  rw [Obj.renderEntries_exact]
  simp only [octets_append, Obj.dictBody]
  rfl

private theorem paddedDict_start {es : Array (String × Obj)} {b : ByteArray} {i : Nat}
    (hs : Span b i (octets (Obj.paddedDict es))) : Start b i := by
  rw [Obj.paddedDict_octets_exact] at hs
  apply Start.non_numeric <;> rw [hs.head]
  · rfl
  · decide
  · decide
  · omega

private theorem skip_two_spaces {b : ByteArray} {i : Nat}
    (h : at? b i = 32) (h' : at? b (i+1) = 32)
    (hw : isWs (at? b (i+2)) = false) (hc : at? b (i+2) ≠ 37)
    (hi : i+1 < b.size) : skipWs b i = i+2 := by
  apply Loop.forIn_range_stops_exact (n := 3) (budget := b.size+1)
  · apply Loop.Stops.yield (b := i+1)
    · simp [skipStep, h, isWs]
    · apply Loop.Stops.yield (b := i+2)
      · simp [skipStep, h', isWs, Nat.add_assoc]
      · apply Loop.Stops.done
        simp [skipStep, hw, hc]
  · omega

private theorem parseVal_paddedDict_span_exact {b : ByteArray} {i p : Nat}
    (es : Array (String × Obj)) (hk : ∀ e ∈ es, Obj.NameSpelling e.1)
    (hv : ∀ e ∈ es, e.2.Representable)
    (hs : Span b i (octets (Obj.paddedDict es))) (hw : skipWs b p = i) :
    parseVal b p = .ok (.dict es, i+(Obj.paddedDict es).size) := by
  have hsize : (Obj.paddedDict es).size = 4+(Obj.dictBody es.toList).length := by
    have hh := congrArg List.length (Obj.paddedDict_octets_exact es)
    simp only [octets_length, List.length_cons] at hh
    omega
  rw [Obj.paddedDict_octets_exact] at hs
  obtain ⟨htStart, htRun⟩ := dictBody_reads es.toList
    (fun e he => hk e (by simpa using he))
    (fun e he => (hv e (by simpa using he)).reads) hs.tail.tail.tail.tail
  have hi : i+1+1+1 < b.size := by
    have := hs.tail.tail.tail.bound
    simp only [List.length_cons] at this
    omega
  have hskip : skipWs b (i+2) = i+4 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      skip_two_spaces hs.tail.tail.head hs.tail.tail.tail.head
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using htStart.whitespace)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using htStart.comment) hi
  obtain ⟨n, hn, htRun⟩ := htRun #[] #[] (i+2)
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hskip)
  have htrace := Runs.cons (step_dict_open #[] hw hs.head hs.tail.head) htRun
  simp only [Array.toArray_toList, Array.empty_append, accept_empty] at htrace
  have htrace' : Runs b (.scan #[] p) (n+1)
      (.done (.result (.ok (.dict es, i+(Obj.paddedDict es).size)))) := by
    simpa only [hsize, Nat.add_assoc, Nat.reduceAdd] using htrace
  apply parseVal_of_runs htrace'
  have hb := hs.bound
  simp only [List.length_cons] at hb
  omega

/-- Concrete encoder spellings accepted by the stream composition proof.
The constructors describe source syntax, never a parser result. -/
inductive Obj.Spelling : Obj → ByteArray → Prop where
  | render {o : Obj} (h : o.Representable) : Spelling o o.render
  | paddedDict {es : Array (String × Obj)} (h : (Obj.dict es).Representable) :
      Spelling (.dict es) (Obj.paddedDict es)

theorem Obj.Spelling.start {o : Obj} {raw b : ByteArray} {i : Nat}
    (h : o.Spelling raw) (hs : Span b i (octets raw))
    (he : Stop b (i+raw.size)) : Start b i := by
  cases h with
  | render h => exact h.reads.start hs he.boundary he.marker
  | paddedDict _ => exact paddedDict_start hs

/-- Both concrete stream-dictionary spellings execute through the actual
object reader, with their own byte lengths and lexical context. -/
theorem parseVal_spelling_span_exact {b raw : ByteArray} {i p : Nat}
    (o : Obj) (h : o.Spelling raw) (hs : Span b i (octets raw))
    (he : Stop b (i+raw.size)) (hw : skipWs b p = i) :
    parseVal b p = .ok (o, i+raw.size) := by
  cases h with
  | render h => exact parseVal_render_span_exact o h hs he hw
  | paddedDict h =>
    cases h with
    | dict hk hv => exact parseVal_paddedDict_span_exact _ hk hv hs hw

end LeanTex.Core.PdfRead
