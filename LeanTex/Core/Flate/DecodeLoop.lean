module

import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.DecodeLoop

/-- A bounded decoder keeps its continuation state separate from a completed
answer. Terminal branches must not retain the previous continuation: that
would share its output buffer across `step` and copy the prefix on append.
The bound is the format's input or output bound, supplied by its caller. -/
@[specialize] public def run {ε σ α : Type} (count : Nat)
    (step : σ → Except ε (Sum α σ)) (initial : σ) (exhausted : ε) : Except ε α :=
  let result := (forIn [0:count] (.inr initial) fun _ state => do
    match state with
    | .inl answer => return .done (.inl answer)
    | .inr current =>
      match step current with
      | .error e => return .done (.inl (.error e))
      | .ok (.inl answer) => return .done (.inl (.ok answer))
      | .ok (.inr next) => return .yield (.inr next) :
      Id (Sum (Except ε α) σ)).run
  match result with
  | .inl answer => answer
  | .inr _ => .error exhausted

/-- A successful execution trace of the real one-step reader. The final step
is counted, so the statement includes the decoder's termination budget. -/
inductive Finishes {ε σ α : Type} (step : σ → Except ε (Sum α σ)) :
    σ → Nat → α → Prop
  | done {state answer} (h : step state = .ok (.inl answer)) :
      Finishes step state 1 answer
  | next {state state' count answer} (h : step state = .ok (.inr state'))
      (rest : Finishes step state' count answer) :
      Finishes step state (count + 1) answer

theorem Finishes.positive {ε σ α : Type} {step : σ → Except ε (Sum α σ)}
    {state count answer} (h : Finishes step state count answer) : 0 < count := by
  cases h <;> omega

/-- A successful trace that fits the actual loop bound returns its answer. -/
theorem run_exact {ε σ α : Type} (step : σ → Except ε (Sum α σ))
    (initial : σ) (answer : α) (count budget : Nat) (exhausted : ε)
    (h : Finishes step initial count answer) (hb : count ≤ budget) :
    run budget step initial exhausted = .ok answer := by
  let P (k : Nat) (state : Sum (Except ε α) σ) : Prop :=
    match state with
    | .inl _ => False
    | .inr current => ∃ n, n + k ≤ budget ∧ Finishes step current n answer
  let Q (state : Sum (Except ε α) σ) : Prop :=
    state = .inl (.ok answer)
  have hf := Progress.forIn_range_exact P Q
    (fun _ state => do
      match state with
      | .inl a => return .done (.inl a)
      | .inr current =>
        match step current with
        | .error e => return .done (.inl (.error e))
        | .ok (.inl a) => return .done (.inl (.ok a))
        | .ok (.inr next) => return .yield (.inr next))
    0 budget (.inr initial) (Nat.zero_le _)
    ⟨count, by omega, h⟩ ?_ ?_
  · simp only [run, Q] at hf ⊢
    rw [hf]
  · intro i _ _ state hs
    cases state with
    | inl _ => exact hs.elim
    | inr current =>
      obtain ⟨n, hn, ht⟩ := hs
      cases ht with
      | done he => simp only [he]; rfl
      | next he rest =>
        simp only [he]
        exact ⟨_, by omega, rest⟩
  · intro state hs
    cases state with
    | inl _ => exact hs.elim
    | inr current =>
      obtain ⟨n, hn, ht⟩ := hs
      have := ht.positive
      omega

/-- Continuation steps, before the final marker has been read. -/
inductive Steps {ε σ α : Type} (step : σ → Except ε (Sum α σ)) :
    σ → Nat → σ → Prop
  | refl (state) : Steps step state 0 state
  | snoc {initial count state state'} (earlier : Steps step initial count state)
      (h : step state = .ok (.inr state')) :
      Steps step initial (count + 1) state'

theorem Steps.finish {ε σ α : Type} {step : σ → Except ε (Sum α σ)}
    {initial count state answer} (h : Steps step initial count state)
    {rest} (hf : Finishes step state rest answer) :
    Finishes step initial (rest + count) answer := by
  induction h generalizing rest with
  | refl => simpa using hf
  | snoc earlier he ih =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (.next he hf)

end LeanTex.Core.Flate.DecodeLoop
