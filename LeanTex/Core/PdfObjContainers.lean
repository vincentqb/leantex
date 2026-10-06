import LeanTex.Core.PdfObjScalar

namespace LeanTex.Core.PdfRead.ObjReader

open PdfLex

theorem step_array_open {b : ByteArray} {p i : Nat} (stack : Array Frame)
    (hw : skipWs b p = i) (hc : at? b i = 91) :
    step b (.scan stack p) = .yield (.scan (stack.push (.arr #[])) (i+1)) := by
  have ht : readToken b i = .ok (.arrayOpen,i+1) := by simp [readToken,hc]; rfl
  simp only [step,hw,ht]

theorem step_array_close {b : ByteArray} {p i : Nat} (stack : Array Frame) (acc : Array Obj)
    (hw : skipWs b p = i) (hc : at? b i = 93) :
    step b (.scan (stack.push (.arr acc)) p) = accept stack (.arr acc) (i+1) := by
  have ht : readToken b i = .ok (.arrayClose,i+1) := by simp [readToken,hc]; rfl
  simp only [step,hw,ht,Array.back?_push,Array.pop_push]

theorem step_dict_open {b : ByteArray} {p i : Nat} (stack : Array Frame)
    (hw : skipWs b p = i) (hc : at? b i = 60) (hc' : at? b (i+1) = 60) :
    step b (.scan stack p) = .yield (.scan (stack.push (.dct #[] none)) (i+2)) := by
  have ht : readToken b i = .ok (.dictOpen,i+2) := by simp [readToken,hc,hc']; rfl
  simp only [step,hw,ht]

theorem step_dict_close {b : ByteArray} {p i : Nat} (stack : Array Frame)
    (acc : Array (String × Obj)) (hw : skipWs b p = i)
    (hc : at? b i = 62) (hc' : at? b (i+1) = 62) :
    step b (.scan (stack.push (.dct acc none)) p) = accept stack (.dict acc) (i+2) := by
  have ht : readToken b i = .ok (.dictClose,i+2) := by simp [readToken,hc,hc']; rfl
  simp only [step,hw,ht,Array.back?_push,Array.pop_push]

theorem push_append_toArray {α : Type} (acc : Array α) (x : α) (xs : List α) :
    acc.push x ++ xs.toArray = acc ++ (x::xs).toArray := by
  rw [List.toArray_cons,Array.append_singleton_assoc]

/-- Read the remaining array elements and the actual closing byte. The
tail is proved first, so each numeric element's reference lookahead is
discharged from the following rendered token. -/
theorem arrayBody_reads (xs : List Obj) (hx : ∀ x ∈ xs, Reads x)
    {b : ByteArray} {i : Nat} (h : Span b i (Obj.arrayBody xs)) :
    Start b i ∧
      ∀ (stack : Array Frame) (acc : Array Obj) (p : Nat), skipWs b p = i →
        ∃ n, n ≤ (Obj.arrayBody xs).length ∧
          Runs b (.scan (stack.push (.arr acc)) p) n
            (accept stack (.arr (acc ++ xs.toArray)) (i+(Obj.arrayBody xs).length)) := by
  induction xs generalizing i with
  | nil =>
    have hh : Span b i [93] := h
    refine ⟨Start.close_array hh.head,?_⟩
    intro stack acc p hw
    refine ⟨1,Nat.le_refl _,?_⟩
    simpa only [Obj.arrayBody_nil,List.length_cons,List.length_nil,Nat.zero_add,
      List.toArray,Array.append_empty] using
      Runs.last (step_array_close stack acc hw hh.head)
  | cons x xs ih =>
    have hx' := hx x (by simp)
    cases xs with
    | nil =>
      rw [Obj.arrayBody_single] at h
      have hv := h.append_left
      have ht : Span b (i+x.render.size) (Obj.arrayBody []) := by
        simpa only [octets_length,Obj.arrayBody_nil] using h.append_right
      obtain ⟨htStart,htRun⟩ := ih (by simp) ht
      have he := Stop.close_array ht.head
      refine ⟨hx'.start hv he.boundary he.marker,?_⟩
      intro stack acc p hw
      obtain ⟨m,hm,hvRun⟩ := hx'.run (stack.push (.arr acc)) hv he hw
      rw [accept_array] at hvRun
      obtain ⟨n,hn,htRun⟩ := htRun stack (acc.push x) (i+x.render.size) htStart.skip
      refine ⟨m+n,?_,?_⟩
      · simp only [Obj.arrayBody_single,List.length_append,octets_length,
          List.length_cons,List.length_nil] at ⊢
        simp only [Obj.arrayBody_nil,List.length_cons,List.length_nil] at hn
        omega
      · have hc := hvRun.trans htRun
        simpa only [push_append_toArray,Obj.arrayBody_single,Obj.arrayBody_nil,List.length_append,
          octets_length,List.length_cons,List.length_nil,Nat.add_assoc] using hc
    | cons y ys =>
      rw [Obj.arrayBody_cons] at h
      have hv := h.append_left
      have hs : Span b (i+x.render.size) (32 :: Obj.arrayBody (y::ys)) := by
        simpa only [octets_length] using h.append_right
      obtain ⟨htStart,htRun⟩ := ih (fun v hv => hx v (by simp [hv])) hs.tail
      have hi : i+x.render.size < b.size := by have := hs.bound; simp only [List.length_cons] at this; omega
      have he := Stop.space hs.head hi htStart
      have htSkip := skipWs_one_exact hs.head htStart.whitespace htStart.comment hi
      refine ⟨hx'.start hv he.boundary he.marker,?_⟩
      intro stack acc p hw
      obtain ⟨m,hm,hvRun⟩ := hx'.run (stack.push (.arr acc)) hv he hw
      rw [accept_array] at hvRun
      obtain ⟨n,hn,htRun⟩ := htRun stack (acc.push x) (i+x.render.size) htSkip
      refine ⟨m+n,?_,?_⟩
      · simp only [Obj.arrayBody_cons,List.length_append,octets_length,List.length_cons]
        omega
      · have hc := hvRun.trans htRun
        simpa only [push_append_toArray,Obj.arrayBody_cons,List.length_append,
          octets_length,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc

theorem dictBody_reads (es : List (String × Obj))
    (hk : ∀ e ∈ es, Obj.NameSpelling e.1) (hv : ∀ e ∈ es, Reads e.2)
    {b : ByteArray} {i : Nat} (h : Span b i (Obj.dictBody es)) :
    Start b i ∧
      ∀ (stack : Array Frame) (acc : Array (String × Obj)) (p : Nat), skipWs b p = i →
        ∃ n, n ≤ (Obj.dictBody es).length ∧
          Runs b (.scan (stack.push (.dct acc none)) p) n
            (accept stack (.dict (acc ++ es.toArray)) (i+(Obj.dictBody es).length)) := by
  induction es generalizing i with
  | nil =>
    have hh : Span b i [62,62] := h
    refine ⟨Start.close_dict hh.head,?_⟩
    intro stack acc p hw
    refine ⟨1,by decide,?_⟩
    simpa only [Obj.dictBody_nil,List.length_cons,List.length_nil,Nat.zero_add,
      List.toArray,Array.append_empty] using
      Runs.last (step_dict_close stack acc hw hh.head hh.tail.head)
  | cons e es ih =>
    rcases e with ⟨k,v⟩
    have hkey := Reads.name (hk (k,v) (by simp))
    have hval := hv (k,v) (by simp)
    have hr : (Obj.name k).render = ("/" ++ escapeName k).toUTF8 := by
      simp only [Obj.render,Obj.renderInto,ByteArray.empty_append]
    rw [Obj.dictBody_cons,← hr] at h
    have hkeySpan := h.append_left
    have hspace : Span b (i+(Obj.name k).render.size)
        (32 :: (octets v.render ++ 32 :: Obj.dictBody es)) := by
      simpa only [octets_length] using h.append_right
    have hvalSpan := hspace.tail.append_left
    have hspace' : Span b (i+(Obj.name k).render.size+1+v.render.size)
        (32 :: Obj.dictBody es) := by
      simpa only [octets_length] using hspace.tail.append_right
    obtain ⟨htStart,htRun⟩ := ih (fun e he => hk e (by simp [he]))
      (fun e he => hv e (by simp [he])) hspace'.tail
    have hi' : i+(Obj.name k).render.size+1+v.render.size < b.size := by
      have := hspace'.bound
      simp only [List.length_cons] at this
      omega
    have hvalEnd := Stop.space hspace'.head hi' htStart
    have htailSkip := skipWs_one_exact hspace'.head htStart.whitespace htStart.comment hi'
    have hvalStart := hval.start hvalSpan hvalEnd.boundary hvalEnd.marker
    have hi : i+(Obj.name k).render.size < b.size := by
      have := hspace.bound
      simp only [List.length_cons,List.length_append] at this
      omega
    have hkeyEnd := Stop.space hspace.head hi hvalStart
    have hvalSkip := skipWs_one_exact hspace.head hvalStart.whitespace hvalStart.comment hi
    refine ⟨hkey.start hkeySpan hkeyEnd.boundary hkeyEnd.marker,?_⟩
    intro stack acc p hw
    obtain ⟨nk,hkBound,hkeyRun⟩ := hkey.run (stack.push (.dct acc none)) hkeySpan hkeyEnd hw
    rw [accept_key] at hkeyRun
    obtain ⟨nv,hvBound,hvalRun⟩ := hval.run (stack.push (.dct acc (some k)))
      hvalSpan hvalEnd hvalSkip
    rw [accept_value] at hvalRun
    obtain ⟨nt,htBound,htRun⟩ := htRun stack (acc.push (k,v))
      (i+(Obj.name k).render.size+1+v.render.size) htailSkip
    refine ⟨nk+nv+nt,?_,?_⟩
    · simp only [Obj.dictBody_cons,← hr,List.length_append,octets_length,List.length_cons]
      dsimp only at hkBound hvBound
      omega
    · have hc := (hkeyRun.trans hvalRun).trans htRun
      simpa only [push_append_toArray,Obj.dictBody_cons,← hr,List.length_append,
        octets_length,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc

theorem Reads.arr {xs : Array Obj} (hx : ∀ x ∈ xs, Reads x) : Reads (.arr xs) := by
  have hsize : (Obj.arr xs).render.size = 1+(Obj.arrayBody xs.toList).length := by
    have hh := congrArg List.length (Obj.render_arr_octets xs)
    simpa only [octets_length,List.length_cons,Nat.add_comm] using hh
  refine ⟨by omega,?_,?_⟩
  · intro b i h _ _
    rw [Obj.render_arr_octets] at h
    apply Start.non_numeric <;> rw [h.head]
    · rfl
    · decide
    · decide
    · omega
  · intro b i p stack h _ hw
    rw [Obj.render_arr_octets] at h
    obtain ⟨htStart,htRun⟩ := arrayBody_reads xs.toList
      (fun x hm => hx x (by simpa using hm)) h.tail
    obtain ⟨n,hn,htRun⟩ := htRun stack #[] (i+1) htStart.skip
    refine ⟨n+1,by omega,?_⟩
    have hc := Runs.cons (step_array_open stack hw h.head) htRun
    simpa only [Array.toArray_toList,Array.empty_append,hsize,← Nat.add_assoc] using hc

theorem Reads.dict {es : Array (String × Obj)}
    (hk : ∀ e ∈ es, Obj.NameSpelling e.1) (hv : ∀ e ∈ es, Reads e.2) : Reads (.dict es) := by
  have hsize : (Obj.dict es).render.size = 3+(Obj.dictBody es.toList).length := by
    have hh := congrArg List.length (Obj.render_dict_octets es)
    simp only [octets_length,List.length_cons] at hh
    omega
  refine ⟨by omega,?_,?_⟩
  · intro b i h _ _
    rw [Obj.render_dict_octets] at h
    apply Start.non_numeric <;> rw [h.head]
    · rfl
    · decide
    · decide
    · omega
  · intro b i p stack h _ hw
    rw [Obj.render_dict_octets] at h
    obtain ⟨htStart,htRun⟩ := dictBody_reads es.toList
      (fun e hm => hk e (by simpa using hm)) (fun e hm => hv e (by simpa using hm)) h.tail.tail.tail
    have hi : i+1+1 < b.size := by
      have := h.tail.tail.bound
      simp only [List.length_cons] at this
      omega
    have hskip := skipWs_one_exact h.tail.tail.head htStart.whitespace htStart.comment hi
    obtain ⟨n,hn,htRun⟩ := htRun stack #[] (i+1+1) hskip
    refine ⟨n+1,by omega,?_⟩
    have hc := Runs.cons (step_dict_open stack hw h.head h.tail.head)
      (by simpa only [Nat.add_assoc] using htRun)
    simpa only [Array.toArray_toList,Array.empty_append,hsize,← Nat.add_assoc] using hc

end LeanTex.Core.PdfRead.ObjReader
