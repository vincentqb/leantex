module

import LeanTex.Core.Flate.TokenSymbols
import LeanTex.Core.Flate.Alphabet
import LeanTex.Core.Flate.Frequencies
import LeanTex.Core.Flate.Progress

namespace LeanTex.Core.Flate.TokenBlock

/-- The two Huffman alphabet keys of a packed token. A literal has no
distance key; a match is unpacked once for both counters. -/
def symbols (t : UInt32) : Nat × Option Nat :=
  if t < 256 then (t.toNat, none)
  else
    let (len, _, di) := matchOf t
    (257 + lenSymTab[len]?.getD 0, some di)

/-- Count both alphabets in one pass, with the mandatory end-of-block symbol
present before the first token. -/
def frequencies (tokens : Array UInt32) : Array Nat × Array Nat := Id.run do
  let mut freqs := ((Array.replicate 286 0).set! 256 1, Array.replicate 30 0)
  for t in tokens do
    let (ls, ds) := symbols t
    freqs := (Frequencies.bump freqs.1 ls,
      match ds with
      | none => freqs.2
      | some s => Frequencies.bump freqs.2 s)
  return freqs

theorem frequencies_contract (tokens : Array UInt32) :
    (frequencies tokens).1.size = 286 ∧ (frequencies tokens).2.size = 30 ∧
      0 < (frequencies tokens).1[256]?.getD 0 ∧
      ∀ t ∈ tokens.toList,
        ((symbols t).1 < 286 → 0 < (frequencies tokens).1[(symbols t).1]?.getD 0) ∧
        (∀ s, (symbols t).2 = some s → s < 30 →
          0 < (frequencies tokens).2[s]?.getD 0) := by
  let P (seen : List UInt32) (freqs : Array Nat × Array Nat) : Prop :=
    freqs.1.size = 286 ∧ freqs.2.size = 30 ∧
      0 < freqs.1[256]?.getD 0 ∧
      ∀ t ∈ seen,
        ((symbols t).1 < 286 → 0 < freqs.1[(symbols t).1]?.getD 0) ∧
        (∀ s, (symbols t).2 = some s → s < 30 → 0 < freqs.2[s]?.getD 0)
  change P tokens.toList
    (forIn tokens ((Array.replicate 286 0).set! 256 1, Array.replicate 30 0)
      (fun t freqs => pure (.yield
        (Frequencies.bump freqs.1 (symbols t).1,
          match (symbols t).2 with
          | none => freqs.2
          | some s => Frequencies.bump freqs.2 s))) : Id _).run
  apply Progress.forIn_array_exact P (P tokens.toList) _ tokens _
    (by simp [P, Array.set!_eq_setIfInBounds]) ?_ (fun _ h => h)
  intro before t after _ freqs hs
  have hlSize := Frequencies.bump_size freqs.1 (symbols t).1
  have heob := Nat.lt_of_lt_of_le hs.2.2.1
    (Frequencies.bump_monotone freqs.1 (symbols t).1 256)
  cases hkey : (symbols t).2 with
  | none =>
    refine ⟨hlSize.trans hs.1, hs.2.1, heob, ?_⟩
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · refine ⟨fun hi => Nat.lt_of_lt_of_le ((hs.2.2.2 u hu).1 hi)
        (Frequencies.bump_monotone freqs.1 (symbols t).1 _),
        (hs.2.2.2 u hu).2⟩
    · refine ⟨fun hi => Frequencies.bump_positive _ _ (by omega), ?_⟩
      intro s hk _
      simp [hkey] at hk
  | some s =>
    refine ⟨hlSize.trans hs.1, (Frequencies.bump_size freqs.2 s).trans hs.2.1, heob, ?_⟩
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact ⟨fun hi => Nat.lt_of_lt_of_le ((hs.2.2.2 u hu).1 hi)
        (Frequencies.bump_monotone freqs.1 (symbols t).1 _),
        fun i hk hi => Nat.lt_of_lt_of_le ((hs.2.2.2 u hu).2 i hk hi)
          (Frequencies.bump_monotone freqs.2 s i)⟩
    · refine ⟨fun hi => Frequencies.bump_positive _ _ (by omega), ?_⟩
      intro i hk hi
      have heq : s = i := Option.some.inj (hkey.symm.trans hk)
      subst i
      exact Frequencies.bump_positive _ _ (by omega)

/-- Trim only unused suffixes, before assigning codes. Thus both the writer
and the declared wire alphabet use exactly the same length vector. -/
public def alphabets (tokens : Array UInt32) : Array Nat × Array Nat :=
  let (lit, dist) := frequencies tokens
  (Frequencies.trim 257 lit, Frequencies.trim 1 dist)

theorem alphabets_contract (tokens : Array UInt32) :
    (257 ≤ (alphabets tokens).1.size ∧ (alphabets tokens).1.size ≤ 286) ∧
      (1 ≤ (alphabets tokens).2.size ∧ (alphabets tokens).2.size ≤ 30) ∧
      0 < (alphabets tokens).1[256]?.getD 0 ∧
      ∀ t ∈ tokens.toList,
        ((symbols t).1 < 286 → 0 < (alphabets tokens).1[(symbols t).1]?.getD 0) ∧
        (∀ s, (symbols t).2 = some s → s < 30 →
          0 < (alphabets tokens).2[s]?.getD 0) := by
  have hf := frequencies_contract tokens
  have hl := Frequencies.trim_contract 257 (frequencies tokens).1
  have hd := Frequencies.trim_contract 1 (frequencies tokens).2
  dsimp only [alphabets]
  refine ⟨⟨by have := hl.1; omega, by have := hl.2.1; omega⟩,
    ⟨by have := hd.1; omega, by have := hd.2.1; omega⟩, ?_, ?_⟩
  · simpa only [hl.2.2] using hf.2.2.1
  · intro t ht
    simpa only [hl.2.2, hd.2.2] using hf.2.2.2 t ht

end LeanTex.Core.Flate.TokenBlock
