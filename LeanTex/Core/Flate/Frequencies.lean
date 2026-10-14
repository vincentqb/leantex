module

import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.Frequencies

/-- Increments a symbol's frequency; an out-of-alphabet symbol leaves the table unchanged. -/
public def bump (freqs : Array Nat) (symbol : Nat) : Array Nat :=
  freqs.set! symbol (freqs[symbol]?.getD 0 + 1)

public theorem bump_size (freqs : Array Nat) (symbol : Nat) :
    (bump freqs symbol).size = freqs.size := Array.size_set! ..

public theorem bump_positive (freqs : Array Nat) (symbol : Nat) (h : symbol < freqs.size) :
    0 < (bump freqs symbol)[symbol]?.getD 0 := by
  simp [bump, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h]

public theorem bump_monotone (freqs : Array Nat) (symbol index : Nat) :
    freqs[index]?.getD 0 ≤ (bump freqs symbol)[index]?.getD 0 := by
  by_cases h : index = symbol
  · subst index
    by_cases hi : symbol < freqs.size
    · simp [bump, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hi]
    · simp [bump, Array.set!_eq_setIfInBounds, hi]
  · simp [bump, Array.set!_eq_setIfInBounds, Ne.symm h]

/-- Two different symbols of positive frequency make two live symbols. -/
public theorem live_two (freqs : Array Nat) (i j : Nat) (hi : i < freqs.size) (hj : j < freqs.size)
    (hne : i ≠ j) (hpi : 0 < freqs[i]?.getD 0) (hpj : 0 < freqs[j]?.getD 0) :
    1 < ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).size := by
  have hm (k : Nat) (hk : k < freqs.size) (hp : 0 < freqs[k]?.getD 0) :
      k ∈ ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0).toList := by
    simp only [Array.mem_toList_iff, Array.mem_filter, Array.mem_range, decide_eq_true_eq]
    exact ⟨hk, hp⟩
  have hmi := hm i hi hpi
  have hmj := hm j hj hpj
  generalize ((Array.range freqs.size).filter fun s => freqs[s]?.getD 0 > 0) = live at hmi hmj
  rcases hlv : live.toList with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · simp [hlv] at hmi
  · simp only [hlv, List.mem_singleton] at hmi hmj
    exact absurd (hmi.trans hmj.symm) hne
  · have := congrArg List.length hlv
    simp only [Array.length_toList, List.length_cons] at this
    omega

/-- Counts each entry's symbol in the alphabet `key` selects; `none` skips the entry. -/
@[specialize] public def count {α : Type} (key : α → Option Nat)
    (entries : Array α) (initial : Array Nat) : Array Nat := Id.run do
  let mut freqs := initial
  for entry in entries do
    freqs := match key entry with
      | some symbol => bump freqs symbol
      | none => freqs
  return freqs

public theorem count_contract {α : Type} (key : α → Option Nat)
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
