import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.Frequencies

/-- Increment a symbol in a bounded alphabet. Out-of-alphabet symbols leave the
table unchanged, as `Array.set!` does in the encoder. -/
def bump (freqs : Array Nat) (symbol : Nat) : Array Nat :=
  freqs.set! symbol (freqs[symbol]?.getD 0 + 1)

theorem bump_size (freqs : Array Nat) (symbol : Nat) :
    (bump freqs symbol).size = freqs.size := Array.size_set! ..

theorem bump_positive (freqs : Array Nat) (symbol : Nat) (h : symbol < freqs.size) :
    0 < (bump freqs symbol)[symbol]?.getD 0 := by
  simp [bump, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h]

theorem bump_monotone (freqs : Array Nat) (symbol index : Nat) :
    freqs[index]?.getD 0 ≤ (bump freqs symbol)[index]?.getD 0 := by
  by_cases h : index = symbol
  · subst index
    by_cases hi : symbol < freqs.size
    · simp [bump, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hi]
    · simp [bump, Array.set!_eq_setIfInBounds, hi]
  · simp [bump, Array.set!_eq_setIfInBounds, Ne.symm h]

/-- Count the selected alphabet symbol of each entry. `none` is an entry that
does not use this alphabet, such as a literal in the distance table. -/
@[specialize] def count {α : Type} (key : α → Option Nat)
    (entries : Array α) (initial : Array Nat) : Array Nat := Id.run do
  let mut freqs := initial
  for entry in entries do
    freqs := match key entry with
      | some symbol => bump freqs symbol
      | none => freqs
  return freqs

/-- The actual counter keeps its alphabet size, preserves the initial
frequencies, and gives every in-range emitted symbol positive frequency. -/
theorem count_contract {α : Type} (key : α → Option Nat)
    (entries : Array α) (initial : Array Nat) :
    (count key entries initial).size = initial.size ∧
      (∀ i : Nat, initial[i]?.getD 0 ≤ (count key entries initial)[i]?.getD 0) ∧
      (∀ entry ∈ entries.toList, ∀ symbol, key entry = some symbol →
        symbol < initial.size → 0 < (count key entries initial)[symbol]?.getD 0) := by
  let P (seen : List α) (freqs : Array Nat) : Prop :=
    freqs.size = initial.size ∧
      (∀ i : Nat, initial[i]?.getD 0 ≤ freqs[i]?.getD 0) ∧
      (∀ entry ∈ seen, ∀ symbol, key entry = some symbol →
        symbol < initial.size → 0 < freqs[symbol]?.getD 0)
  change P entries.toList
    (forIn entries initial (fun entry freqs => pure (.yield
      (match key entry with | some s => bump freqs s | none => freqs))) : Id _).run
  apply Progress.forIn_array_exact P (P entries.toList) _ entries initial
    ⟨rfl, fun _ => Nat.le_refl _, by simp⟩ ?_ (fun _ h => h)
  intro before entry after _ freqs hs
  cases hk : key entry with
  | none =>
    refine ⟨hs.1, hs.2.1, ?_⟩
    intro e he s hkey hi
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hs.2.2 e he s hkey hi
    · simp [hk] at hkey
  | some symbol =>
    refine ⟨(bump_size freqs symbol).trans hs.1, ?_, ?_⟩
    · intro i
      exact Nat.le_trans (hs.2.1 i) (bump_monotone freqs symbol i)
    · intro e he s hkey hi
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact Nat.lt_of_lt_of_le (hs.2.2 e he s hkey hi)
          (bump_monotone freqs symbol s)
      · have heq : symbol = s := Option.some.inj (hk.symm.trans hkey)
        subst s
        exact bump_positive freqs symbol (by omega)

end LeanTex.Core.Flate.Frequencies
