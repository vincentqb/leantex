import LeanTex.Core.PdfObjSpelling

namespace LeanTex.Core.PdfRead.ObjReader

open PdfLex

/-- The compositional contract for one rendered object. `run` follows
the actual stack transitions; its count is bounded by consumed bytes.
The syntax induction discharges both lexical and execution fields. -/
structure Reads (o : Obj) : Prop where
  size_pos : 0 < o.render.size
  start : ∀ {b : ByteArray} {i : Nat}, Span b i (octets o.render) →
    EndByte (at? b (i+o.render.size)) →
    at? b (skipWs b (i+o.render.size)) ≠ 82 → Start b i
  run : ∀ {b : ByteArray} {i p : Nat} (stack : Array Frame),
    Span b i (octets o.render) → Stop b (i+o.render.size) →
    skipWs b p = i →
    ∃ n, n ≤ o.render.size ∧ Runs b (.scan stack p) n (accept stack o (i+o.render.size))

theorem Reads.atom {o : Obj} (hn : 0 < o.render.size)
    (hs : ∀ {b i}, Span b i (octets o.render) →
      EndByte (at? b (i+o.render.size)) →
      at? b (skipWs b (i+o.render.size)) ≠ 82 → Start b i)
    (ht : ∀ {b i}, Span b i (octets o.render) → Stop b (i+o.render.size) →
      readToken b i = .ok (.value o,i+o.render.size)) : Reads o := by
  refine ⟨hn,hs,?_⟩
  intro b i p stack h he hw
  refine ⟨1,hn,.last ?_⟩
  simp only [step,hw,ht h he]

theorem numeric_first {b : ByteArray} {i : Nat} {s : String}
    (h : Span b i (octets s.toUTF8)) (hn : s.toList ≠ [])
    (hc : ∀ c ∈ s.toList, numByte c.toNat = true) : numByte (at? b i) = true := by
  rw [numeric_octets s hc] at h
  apply h.first_number (by simpa using hn)
  intro c hm
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
  exact hc d hd

theorem numeric_size_pos (s : String) (hn : s.toList ≠ [])
    (hc : ∀ c ∈ s.toList, numByte c.toNat = true) : 0 < s.toUTF8.size := by
  rw [numeric_size s hc]
  exact List.length_pos_iff.mpr hn

theorem Reads.null : Reads .null := by
  apply Reads.atom (by decide)
  · intro b i h _ _
    change Span b i [110,117,108,108] at h
    apply Start.non_numeric <;> rw [h.head]
    · rfl
    · decide
    · decide
    · omega
  · intro b i h he
    exact readToken_null h he.boundary

theorem Reads.bool (v : Bool) : Reads (.bool v) := by
  cases v with
  | false =>
    apply Reads.atom (by decide)
    · intro b i h _ _
      change Span b i [102,97,108,115,101] at h
      apply Start.non_numeric <;> rw [h.head]
      · rfl
      · decide
      · decide
      · omega
    · intro b i h he
      exact readToken_false h he.boundary
  | true =>
    apply Reads.atom (by decide)
    · intro b i h _ _
      change Span b i [116,114,117,101] at h
      apply Start.non_numeric <;> rw [h.head]
      · rfl
      · decide
      · decide
      · omega
    · intro b i h he
      exact readToken_true h he.boundary

theorem Reads.int (n : Int) : Reads (.int n) := by
  have hr : (Obj.int n).render = (toString n).toUTF8 := by
    simp only [Obj.render,Obj.renderInto,ByteArray.empty_append]
  apply Reads.atom (by rw [hr]; exact numeric_size_pos _ (Number.int_nonempty n) (int_numeric n))
  · intro b i h he hR
    rw [hr] at h he hR
    exact Start.numeric h (Number.int_nonempty n) (int_numeric n) he hR
  · intro b i h he
    rw [hr] at h he ⊢
    exact readToken_int (numeric_first h (Number.int_nonempty n) (int_numeric n))
      (scan_numeric h (int_numeric n) he.boundary) he.reference

theorem Reads.real {s : String} (hs : Obj.RealSpelling s) : Reads (.real s) := by
  have hn : s.toList ≠ [] := by
    intro he
    have hd := hs.1
    simp only [he,List.not_mem_nil] at hd
  have hr : (Obj.real s).render = s.toUTF8 := by
    simp only [Obj.render,Obj.renderInto,ByteArray.empty_append]
  apply Reads.atom (by rw [hr]; exact numeric_size_pos _ hn hs.2)
  · intro b i h he hR
    rw [hr] at h he hR
    exact Start.numeric h hn hs.2 he hR
  · intro b i h he
    rw [hr] at h he ⊢
    exact readToken_real (numeric_first h hn hs.2) (scan_numeric h hs.2 he.boundary)
      (by simpa only [String.contains_char_eq,decide_eq_true_eq] using hs.1)

theorem Reads.name {s : String} (hs : Obj.NameSpelling s) : Reads (.name s) := by
  have hr : (Obj.name s).render = ("/" ++ escapeName s).toUTF8 := by
    simp only [Obj.render,Obj.renderInto,ByteArray.empty_append]
  apply Reads.atom (by rw [hr,Obj.name_size s hs.1]; omega)
  · intro b i h _ _
    rw [hr,Obj.name_octets s hs.1] at h
    apply Start.non_numeric <;> rw [h.head]
    · rfl
    · decide
    · decide
    · omega
  · intro b i h he
    rw [hr] at h he ⊢
    exact readToken_name h hs he.boundary

theorem Reads.str {raw : ByteArray} (hs : Obj.StringSpelling (octets raw)) : Reads (.str raw) := by
  have hp : ∃ c cs, octets raw = c::cs ∧ (c=40 ∨ c=60) := by
    generalize he : octets raw = cs at hs
    cases hs with
    | literal hc => exact ⟨40,_,rfl,Or.inl rfl⟩
    | hex hc => exact ⟨60,_,rfl,Or.inr rfl⟩
  have hr : (Obj.str raw).render = raw := by
    simp only [Obj.render,Obj.renderInto,ByteArray.empty_append]
  apply Reads.atom
  · rw [hr]
    obtain ⟨c,cs,he,_⟩ := hp
    have := congrArg List.length he
    simp only [octets_length,List.length_cons] at this
    omega
  · intro b i h _ _
    obtain ⟨c,cs,he,hc⟩ := hp
    rw [hr,he] at h
    rcases hc with rfl | rfl
    all_goals
      apply Start.non_numeric <;> rw [h.head]
      · rfl
      · decide
      · decide
      · omega
  · intro b i h _
    rw [hr] at h ⊢
    exact readToken_string h hs

theorem tryRef_generation {b : ByteArray} {i gen : Nat}
    (h : Span b i (32 :: (octets (toString gen).toUTF8 ++ [32,82])))
    (he : EndByte (at? b (i+(toString gen).toUTF8.size+3))) :
    tryRef b i = some (gen,i+(toString gen).toUTF8.size+3) := by
  have hg := h.tail.append_left
  have ht : Span b (i+1+(toString gen).toUTF8.size) [32,82] := by
    simpa only [octets_length] using h.tail.append_right
  have hp := number_byte (numeric_first hg (Number.nat_nonempty gen) (nat_numeric gen))
  have hw := skipWs_one_exact h.head hp.2.1 hp.2.2.1
    (by have := h.bound; simp only [List.length_cons,List.length_append,octets_length] at this; omega)
  have hu := parse_nat hg (Or.inr (Or.inl (by rw [ht.head]; rfl)))
  have hR := skipWs_one_exact ht.head (by rw [ht.tail.head]; rfl)
    (by rw [ht.tail.head]; decide)
    (by have := ht.bound; simp only [List.length_cons,List.length_nil] at this; omega)
  have hc : (at? b (i+1+(toString gen).toUTF8.size+1+1) == 256 ||
      isWs (at? b (i+1+(toString gen).toUTF8.size+1+1)) ||
      isDelim (at? b (i+1+(toString gen).toUTF8.size+1+1))) = true := by
    have hi : i+1+(toString gen).toUTF8.size+1+1 = i+(toString gen).toUTF8.size+3 := by omega
    rw [hi]
    simpa only [EndByte, Bool.or_eq_true, beq_iff_eq, or_assoc] using he
  simp only [tryRef,hw,hu]
  dsimp only [Bind.bind,Option.bind]
  simp only [hR,ht.tail.head,beq_self_eq_true,hc,↓reduceIte]
  congr 2
  omega

theorem reference_lex {b : ByteArray} {i num gen : Nat}
    (h : Span b i (octets (Obj.ref num gen).render))
    (he : EndByte (at? b (i+(Obj.ref num gen).render.size))) :
    Start b i ∧ readToken b i = .ok (.value (.ref num gen),i+(Obj.ref num gen).render.size) := by
  have hsize : (Obj.ref num gen).render.size =
      (toString num).toUTF8.size+(toString gen).toUTF8.size+3 := by
    have hh := congrArg List.length (Obj.render_ref_octets num gen)
    simp only [octets_length,List.length_append,List.length_cons,List.length_nil] at hh
    omega
  rw [Obj.render_ref_octets] at h
  have hnum := h.append_left
  have hs : Span b (i+(toString num).toUTF8.size)
      (32 :: (octets (toString gen).toUTF8 ++ [32,82])) := by
    simpa only [octets_length] using h.append_right
  have hgen := hs.tail.append_left
  have hp := number_byte (numeric_first hgen (Number.nat_nonempty gen) (nat_numeric gen))
  have hw := skipWs_one_exact hs.head hp.2.1 hp.2.2.1
    (by have := hs.bound; simp only [List.length_cons,List.length_append,octets_length] at this; omega)
  have hend : EndByte (at? b (i+(toString num).toUTF8.size)) :=
    Or.inr (Or.inl (by rw [hs.head]; rfl))
  refine ⟨Start.numeric hnum (Number.nat_nonempty num) (nat_numeric num) hend ?_,?_⟩
  · simpa only [hw] using hp.2.2.2.1
  · have htry := tryRef_generation hs (by simpa only [hsize,Nat.add_assoc] using he)
    have hh := readToken_ref (numeric_first hnum (Number.nat_nonempty num) (nat_numeric num))
      (scan_numeric hnum (nat_numeric num) hend) htry
    simpa only [hsize,Nat.add_assoc] using hh

theorem Reads.ref (num gen : Nat) : Reads (.ref num gen) := by
  apply Reads.atom
  · have hh := congrArg List.length (Obj.render_ref_octets num gen)
    simp only [octets_length,List.length_append,List.length_cons,List.length_nil] at hh
    omega
  · intro b i h he _
    exact (reference_lex h he).1
  · intro b i h he
    exact (reference_lex h he.boundary).2

end LeanTex.Core.PdfRead.ObjReader
