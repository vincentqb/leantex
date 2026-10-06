import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.CodeLengths

abbrev Entry := Nat × Nat × Nat

/-- The run is a range of the actual code-length vector. -/
def Run (seq : Array Nat) (p count value : Nat) : Prop :=
  p + count ≤ seq.size ∧ ∀ k < count, seq[p + k]?.getD 0 = value

/-- A code-length entry spells this part of the vector. The repeat entry
reads its previous value from the already decoded prefix. -/
inductive Step (seq : Array Nat) : Nat → Entry → Nat → Prop where
  | literal (p v : Nat) (hv : v < 16) (h : Run seq p 1 v) :
      Step seq p (v, 0, 0) (p + 1)
  | repeat16 (p count v : Nat) (hc : 3 ≤ count ∧ count ≤ 6)
      (hp : 0 < p) (prev : seq[p - 1]?.getD 0 = v) (h : Run seq p count v) :
      Step seq p (16, count - 3, 2) (p + count)
  | zeros17 (p count : Nat) (hc : 3 ≤ count ∧ count ≤ 10)
      (h : Run seq p count 0) :
      Step seq p (17, count - 3, 3) (p + count)
  | zeros18 (p count : Nat) (hc : 11 ≤ count ∧ count ≤ 138)
      (h : Run seq p count 0) :
      Step seq p (18, count - 11, 7) (p + count)

/-- A progress-indexed account of the entries emitted by the actual RLE
loop. It keeps the consumed vector position, including across repeats. -/
inductive Covers (seq : Array Nat) (start : Nat) : Array Entry → Nat → Prop where
  | empty (h : start ≤ seq.size) : Covers seq start #[] start
  | push {out : Array Entry} {p q : Nat} {entry : Entry}
      (prior : Covers seq start out p) (step : Step seq p entry q) :
      Covers seq start (out.push entry) q

def Entry.Valid (entry : Entry) : Prop :=
  entry.1 < 19 ∧ entry.2.2 ≤ 7 ∧ entry.2.1 < 2 ^ entry.2.2

theorem Step.contract {seq : Array Nat} {p q : Nat} {entry : Entry}
    (h : Step seq p entry q) : p < q ∧ q ≤ seq.size ∧ entry.Valid := by
  cases h with
  | literal v hv hr =>
    exact ⟨by omega, hr.1, by dsimp only [Entry.Valid]; omega⟩
  | repeat16 count v hc hp prev hr =>
    exact ⟨by omega, hr.1, by dsimp only [Entry.Valid]; omega⟩
  | zeros17 count hc hr =>
    exact ⟨by omega, hr.1, by dsimp only [Entry.Valid]; omega⟩
  | zeros18 count hc hr =>
    exact ⟨by omega, hr.1, by dsimp only [Entry.Valid]; omega⟩

theorem Covers.contract {seq : Array Nat} {start p : Nat} {out : Array Entry}
    (h : Covers seq start out p) :
    start + out.size ≤ p ∧ p ≤ seq.size ∧ ∀ entry ∈ out.toList, entry.Valid := by
  induction h with
  | empty h => exact ⟨by simp, h, by simp⟩
  | @push out p q entry _ step ih =>
    have hs := step.contract
    refine ⟨by simp only [Array.size_push]; omega, hs.2.1, ?_⟩
    intro e he
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ih.2.2 e he
    · exact hs.2.2

/-- Find a run using the encoder's bounds-checked scan. -/
def runLength (seq : Array Nat) (p v : Nat) : Nat := Id.run do
  let mut r := 1
  for _ in [0:seq.size] do
    if p + r < seq.size && seq[p + r]?.getD 99 == v then r := r + 1 else break
  return r

theorem runLength_covers (seq : Array Nat) (p : Nat) (hp : p < seq.size) :
    0 < runLength seq p (seq[p]?.getD 0) ∧
      Run seq p (runLength seq p (seq[p]?.getD 0)) (seq[p]?.getD 0) := by
  let P (r : Nat) := 0 < r ∧ Run seq p r (seq[p]?.getD 0)
  unfold runLength
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact (fun _ => P) P _ 0 seq.size _
    (Nat.zero_le _) ?_ ?_ (fun _ h => h)
  · refine ⟨by omega, by omega, ?_⟩
    intro k hk
    have : k = 0 := by omega
    simp [this]
  · intro i _ _ r hr
    by_cases h : p + r < seq.size ∧ seq[p + r]?.getD 99 = seq[p]?.getD 0
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h]
      change P (r + 1)
      refine ⟨by omega, by omega, ?_⟩
      intro k hk
      by_cases he : k = r
      · subst k
        simpa only [getElem?_pos seq (p + r) h.1, Option.getD_some] using h.2
      · exact hr.2.2 k (by omega)
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h, ite_false]
      exact hr

theorem Run.slice {seq : Array Nat} {p count v : Nat} (h : Run seq p count v)
    (offset take : Nat) (ht : offset + take ≤ count) :
    Run seq (p + offset) take v := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro k hk
  simpa only [Nat.add_assoc] using h.2 (offset + k) (by omega)

/-- Append the remaining literal code lengths to the existing array. -/
def literals (out : Array Entry) (v count : Nat) : Array Entry := Id.run do
  let mut out := out
  for _ in [0:count] do
    out := out.push (v, 0, 0)
  return out

theorem literals_covers {seq : Array Nat} {start p count v : Nat} {out : Array Entry}
    (hp : Covers seq start out p) (hv : v < 16) (hr : Run seq p count v) :
    Covers seq start (literals out v count) (p + count) := by
  unfold literals
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact
    (fun i out => Covers seq start out (p + i))
    (fun out => Covers seq start out (p + count)) _ 0 count _
    (Nat.zero_le _) (by simpa using hp) ?_ (fun _ h => h)
  intro i _ hi out h
  change Covers seq start (out.push (v, 0, 0)) (p + (i + 1))
  simpa only [Nat.add_assoc] using h.push (.literal (p + i) v hv
    (hr.slice i 1 (by omega)))

/-- Emit six-at-a-time repeat codes, retaining the short literal tail. -/
def repeats (bound : Nat) (out : Array Entry) (p left : Nat) :
    Array Entry × Nat × Nat := Id.run do
  let mut out := out
  let mut p := p
  let mut left := left
  for _ in [0:bound] do
    if left ≥ 3 then
      let take := min left 6
      out := out.push (16, take - 3, 2)
      left := left - take
      p := p + take
    else break
  return (out, p, left)

theorem repeats_covers {seq : Array Nat} {start p₀ count v p left bound : Nat}
    {out : Array Entry} (hp : Covers seq start out p)
    (hr : Run seq p₀ count v) (hpos : p₀ < p) (hcons : p + left = p₀ + count)
    (hb : left ≤ bound) :
    Covers seq start (repeats bound out p left).1 (repeats bound out p left).2.1 ∧
    p₀ < (repeats bound out p left).2.1 ∧
    (repeats bound out p left).2.1 + (repeats bound out p left).2.2 = p₀ + count ∧
    (repeats bound out p left).2.2 < 3 := by
  let P (i : Nat) (s : Array Entry × Nat × Nat) : Prop :=
    Covers seq start s.1 s.2.1 ∧ p₀ < s.2.1 ∧
      s.2.1 + s.2.2 = p₀ + count ∧ s.2.2 + i ≤ left
  let Q (s : Array Entry × Nat × Nat) : Prop :=
    Covers seq start s.1 s.2.1 ∧ p₀ < s.2.1 ∧
      s.2.1 + s.2.2 = p₀ + count ∧ s.2.2 < 3
  unfold repeats
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact P Q _ 0 bound _ (Nat.zero_le _)
    ⟨hp, hpos, hcons, Nat.le_refl _⟩ ?_ ?_
  · intro i _ _ s hs
    rcases hs with ⟨hc, hpos, hcons, hleft⟩
    by_cases hl : 3 ≤ s.2.2
    · simp only [hl, ite_true]
      change P (i + 1) (s.1.push (16, min s.2.2 6 - 3, 2),
        s.2.1 + min s.2.2 6, s.2.2 - min s.2.2 6)
      dsimp only [P]
      have ht : 3 ≤ min s.2.2 6 ∧ min s.2.2 6 ≤ 6 ∧ min s.2.2 6 ≤ s.2.2 := by omega
      refine ⟨?_, by omega, by omega, by omega⟩
      refine hc.push (.repeat16 s.2.1 (min s.2.2 6) v ⟨ht.1, ht.2.1⟩
        (by omega) ?_ ?_)
      · have he : p₀ + (s.2.1 - 1 - p₀) = s.2.1 - 1 := by omega
        have := hr.2 (s.2.1 - 1 - p₀) (by omega)
        simpa only [he] using this
      · have he : p₀ + (s.2.1 - p₀) = s.2.1 := by omega
        simpa only [he] using hr.slice (s.2.1 - p₀) (min s.2.2 6) (by omega)
    · simp only [hl, ite_false]
      change Q s
      exact ⟨hc, hpos, hcons, by omega⟩
  · intro s hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1, by have := hs.2.2.2; omega⟩

/-- Emit one nonempty run, reusing the array of all preceding entries. -/
def emitRun (bound : Nat) (out : Array Entry) (p v r : Nat) :
    Array Entry × Nat := Id.run do
  if v == 0 then
    if r < 3 then
      return (literals out 0 r, p + r)
    else if r ≤ 10 then
      return (out.push (17, r - 3, 3), p + r)
    else
      let take := min r 138
      return (out.push (18, take - 11, 7), p + take)
  else
    let (out, p, left) := repeats bound (out.push (v, 0, 0)) (p + 1) (r - 1)
    return (literals out v left, p + left)

theorem emitRun_covers {seq : Array Nat} {start p v r bound : Nat} {out : Array Entry}
    (hp : Covers seq start out p) (hr : Run seq p r v) (hpos : 0 < r)
    (hv : v < 16) (hb : r ≤ bound) :
    Covers seq start (emitRun bound out p v r).1 (emitRun bound out p v r).2 ∧
    p < (emitRun bound out p v r).2 ∧ (emitRun bound out p v r).2 ≤ p + r := by
  unfold emitRun
  simp only [Id.run, pure]
  by_cases hz : v = 0
  · subst v
    simp only [beq_self_eq_true, ite_true]
    split
    · exact ⟨literals_covers hp (by omega) hr, by omega, Nat.le_refl _⟩
    · split
      · exact ⟨hp.push (.zeros17 p r ⟨by omega, by assumption⟩ hr), by omega,
          Nat.le_refl _⟩
      · have ht : 11 ≤ min r 138 ∧ min r 138 ≤ 138 ∧ min r 138 ≤ r := by omega
        refine ⟨hp.push (.zeros18 p (min r 138) ⟨ht.1, ht.2.1⟩ ?_), by omega, by omega⟩
        simpa only [Nat.add_zero] using hr.slice 0 (min r 138) (by omega)
  · simp only [beq_iff_eq, hz, ite_false]
    let result := repeats bound (out.push (v, 0, 0)) (p + 1) (r - 1)
    have hfirst : Covers seq start (out.push (v, 0, 0)) (p + 1) :=
      hp.push (.literal p v hv (by simpa only [Nat.add_zero] using hr.slice 0 1 hpos))
    have hs := repeats_covers hfirst hr (by omega) (by omega) (by omega : r - 1 ≤ bound)
    change Covers seq start (literals result.1 v result.2.2)
      (result.2.1 + result.2.2) ∧ p < result.2.1 + result.2.2 ∧
      result.2.1 + result.2.2 ≤ p + r
    change Covers seq start result.1 result.2.1 ∧ p < result.2.1 ∧
      result.2.1 + result.2.2 = p + r ∧ result.2.2 < 3 at hs
    refine ⟨literals_covers hs.1 hv ?_, by omega, by omega⟩
    have he : p + (result.2.1 - p) = result.2.1 := by omega
    simpa only [he] using hr.slice (result.2.1 - p) result.2.2 (by omega)

/-- RFC 1951 code-length RLE. Each iteration consumes at least one length. -/
def encode (seq : Array Nat) : Array Entry := Id.run do
  let mut out : Array Entry := #[]
  let mut p := 0
  for _ in [0:seq.size] do
    if p ≥ seq.size then break
    let v := seq[p]?.getD 0
    let r := runLength seq p v
    (out, p) := emitRun seq.size out p v r
  return out

theorem encode_covers (seq : Array Nat) (hv : ∀ i < seq.size, seq[i]?.getD 0 < 16) :
    Covers seq 0 (encode seq) seq.size := by
  let P (i : Nat) (s : Array Entry × Nat) : Prop :=
    Covers seq 0 s.1 s.2 ∧ i ≤ s.2 ∧ s.2 ≤ seq.size
  let Q (s : Array Entry × Nat) : Prop :=
    Covers seq 0 s.1 seq.size
  unfold encode
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact P Q _ 0 seq.size _ (Nat.zero_le _)
    ⟨.empty (Nat.zero_le _), Nat.le_refl _, Nat.zero_le _⟩ ?_ ?_
  · intro i _ _ s hs
    by_cases hp : seq.size ≤ s.2
    · simp only [hp, ite_true]
      change Q s
      have he : s.2 = seq.size := by omega
      simpa only [Q, he] using hs.1
    · simp only [hp, ite_false]
      have hrun := runLength_covers seq s.2 (by omega)
      have he := emitRun_covers (bound := seq.size) hs.1 hrun.2 hrun.1 (hv s.2 (by omega))
        (by have := hrun.2.1; omega)
      exact ⟨he.1, by have := he.2.1; have := hs.2.1; omega,
        by have := he.2.2; have := hrun.2.1; omega⟩
  · intro s hs
    have he : s.2 = seq.size := by have := hs.2; omega
    simpa only [Q, he] using hs.1

/-- The real RLE emits only encodable symbols/payloads, and its entry count
fits the decoder's progress bound. -/
theorem encode_contract (seq : Array Nat) (hv : ∀ i < seq.size, seq[i]?.getD 0 < 16) :
    (encode seq).size ≤ seq.size ∧ ∀ entry ∈ (encode seq).toList, entry.Valid := by
  have h := (encode_covers seq hv).contract
  exact ⟨by simpa only [Nat.zero_add] using h.1, h.2.2⟩

end LeanTex.Core.Flate.CodeLengths
