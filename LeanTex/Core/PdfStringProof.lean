import LeanTex.Core.PdfLexProof

namespace LeanTex.Core.PdfLex

/-- Balanced literal-string bytes (§7.3.4.2). An escape consumes its next
byte; unescaped parentheses delimit a nested body. -/
inductive LiteralBody : List Nat → Prop
  | nil : LiteralBody []
  | byte {c cs} : c < 256 → c ≠ 40 → c ≠ 41 → c ≠ 92 →
      LiteralBody cs → LiteralBody (c::cs)
  | escape {c cs} : c < 256 → LiteralBody cs → LiteralBody (92::c::cs)
  | nest {cs ds} : LiteralBody cs → LiteralBody ds →
      LiteralBody (40 :: cs ++ 41 :: ds)

theorem LiteralBody.bytes {cs} (h : LiteralBody cs) : ∀ c ∈ cs, c < 256 := by
  induction h with
  | nil => simp
  | byte hc _ _ _ _ ih => simpa using And.intro hc ih
  | escape hc _ ih => simpa using And.intro (by omega : 92<256) (And.intro hc ih)
  | nest _ _ ih jh =>
    intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with (rfl | hc) | (rfl | hc)
    · omega
    · exact ih c hc
    · omega
    · exact jh c hc

private theorem literalBody_yields {cs : List Nat} (hc : LiteralBody cs)
    {b : ByteArray} {i : Nat} (h : Span b i cs) (depth : Nat) :
    ∃ n, n ≤ cs.length ∧ Loop.Yields (fun s => pure (literalStep b s))
      (LiteralState.mk i (depth+1) none) n (LiteralState.mk (i+cs.length) (depth+1) none) := by
  induction hc generalizing i depth with
  | nil => exact ⟨0, by simp, .nil⟩
  | @byte c cs hc hn1 hn2 hn3 _ ih =>
    obtain ⟨n, hn, ht⟩ := ih h.tail depth
    refine ⟨n+1, by simpa using hn, ?_⟩
    have hs : literalStep b (LiteralState.mk i (depth+1) none) =
        .yield (LiteralState.mk (i+1) (depth+1) none) := by
      simp [literalStep, h.head, hn1, hn2, hn3, show c ≠ 256 by omega]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Loop.Yields.cons (step := fun s => pure (literalStep b s)) hs ht
  | @escape c cs hc _ ih =>
    obtain ⟨n, hn, ht⟩ := ih h.tail.tail depth
    refine ⟨n+1, by simp; omega, ?_⟩
    have hs : literalStep b (LiteralState.mk i (depth+1) none) =
        .yield (LiteralState.mk (i+2) (depth+1) none) := by simp [literalStep, h.head]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Loop.Yields.cons (step := fun s => pure (literalStep b s)) hs ht
  | @nest cs ds _ _ ih jh =>
    obtain ⟨m, hm, ht⟩ := ih h.tail.append_left (depth+1)
    have hend := h.tail.append_right
    obtain ⟨n, hn, hu⟩ := jh hend.tail depth
    refine ⟨(m+n)+2, by simp; omega, ?_⟩
    have hopen : literalStep b (LiteralState.mk i (depth+1) none) =
        .yield (LiteralState.mk (i+1) (depth+2) none) := by simp [literalStep, h.head]
    have hclose : literalStep b (LiteralState.mk (i+1+cs.length) (depth+2) none) =
        .yield (LiteralState.mk (i+1+cs.length+1) (depth+1) none) := by
      simp [literalStep, hend.head]
    have hh := Loop.Yields.cons (step := fun s => pure (literalStep b s)) hopen (ht.trans (Loop.Yields.cons (step := fun s => pure (literalStep b s)) hclose hu))
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- A balanced body followed by its closing parenthesis is consumed
exactly, including nested bodies and escaped bytes. -/
theorem scanLitString_exact {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b (i+1) (cs ++ [41])) (hc : LiteralBody cs) :
    scanLitString b i = some (i+cs.length+2) := by
  obtain ⟨n, hn, ht⟩ := literalBody_yields hc h.append_left 0
  have hend := h.append_right.head
  have hs : literalStep b (LiteralState.mk (i+1+cs.length) 1 none) =
      .done (LiteralState.mk (i+cs.length+2) 0 (some (i+cs.length+2))) := by
    simp only [literalStep, hend]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have stop := ht.stops (Loop.Stops.done hs)
  have hr := Loop.forIn_range_stops_exact stop (b.size+1)
    (by have := h.bound; simp at this; omega)
  unfold scanLitString
  rw [hr]

/-- The hex-string scanner stops at the first closing delimiter.
This is a delimiter contract; it does not claim to validate hex digits. -/
theorem scanHexEnd_exact {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i (cs ++ [62])) (hc : ∀ c ∈ cs, c ≠ 62 ∧ c ≠ 256) :
    scanHexEnd b i = i+cs.length := by
  have hs : Loop.Stops (fun j => pure (hexStep b j)) i (cs.length+1) (i+cs.length) := by
    induction cs generalizing i with
    | nil => apply Loop.Stops.done; simp [hexStep, h.head]
    | cons c cs ih =>
      have hn := hc c (by simp)
      have hh : hexStep b i = .yield (i+1) := by simp [hexStep, h.head, hn]
      have ht := ih h.tail (fun d hd => hc d (by simp [hd]))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Loop.Stops.yield (step := fun j => pure (hexStep b j)) hh ht
  exact Loop.forIn_range_stops_exact hs (b.size+1) (by have := h.bound; simp at this; omega)

end LeanTex.Core.PdfLex
