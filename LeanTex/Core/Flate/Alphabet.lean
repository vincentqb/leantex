import LeanTex.Core.Flate.Frequencies

namespace LeanTex.Core.Flate.Frequencies

/-- The declared alphabet ends after its last live symbol, retaining the
format's mandatory prefix. This runs before package-merge, so the wire length
vector is exactly the vector the writer and decoder use. -/
def usedCount (minimum : Nat) (freqs : Array Nat) : Nat := Id.run do
  let mut n := min minimum freqs.size
  for s in [0:freqs.size] do
    n := if 0 < freqs[s]?.getD 0 then max n (s + 1) else n
  return n

theorem usedCount_contract (minimum : Nat) (freqs : Array Nat) :
    min minimum freqs.size ≤ usedCount minimum freqs ∧
      usedCount minimum freqs ≤ freqs.size ∧
      ∀ s, 0 < freqs[s]?.getD 0 → s < usedCount minimum freqs := by
  let P (k n : Nat) : Prop :=
    min minimum freqs.size ≤ n ∧ n ≤ freqs.size ∧
      ∀ s < k, 0 < freqs[s]?.getD 0 → s < n
  have h : P freqs.size (usedCount minimum freqs) := by
    change P freqs.size
      (forIn [0:freqs.size] (min minimum freqs.size) (fun s n =>
        pure (.yield (if 0 < freqs[s]?.getD 0 then max n (s + 1) else n))) : Id Nat).run
    apply Progress.forIn_range_exact P (P freqs.size) _ 0 freqs.size _
      (Nat.zero_le _) ⟨Nat.le_refl _, Nat.min_le_right .., by simp⟩ ?_ (fun _ h => h)
    intro k _ hk n hn
    change P (k + 1) (if 0 < freqs[k]?.getD 0 then max n (k + 1) else n)
    split
    · refine ⟨by have := hn.1; omega, by have := hn.2.1; omega, ?_⟩
      intro s hs hp
      by_cases heq : s = k
      · subst s; omega
      · have := hn.2.2 s (by omega) hp
        omega
    · rename_i hz
      refine ⟨hn.1, hn.2.1, ?_⟩
      intro s hs hp
      by_cases heq : s = k
      · subst s; contradiction
      · exact hn.2.2 s (by omega) hp
  refine ⟨h.1, h.2.1, ?_⟩
  intro s hs
  have hi : s < freqs.size := by
    by_cases hi : s < freqs.size
    · exact hi
    · simp [getElem?_neg freqs s hi] at hs
  exact h.2.2 s hi hs

def trim (minimum : Nat) (freqs : Array Nat) : Array Nat :=
  freqs.extract 0 (usedCount minimum freqs)

/-- Trimming removes only zero frequencies. Every symbol's frequency,
including a live symbol at the final retained index, is preserved exactly. -/
theorem trim_contract (minimum : Nat) (freqs : Array Nat) :
    min minimum freqs.size ≤ (trim minimum freqs).size ∧
      (trim minimum freqs).size ≤ freqs.size ∧
      ∀ s : Nat, (trim minimum freqs)[s]?.getD 0 = freqs[s]?.getD 0 := by
  have hn := usedCount_contract minimum freqs
  have hsize : (trim minimum freqs).size = usedCount minimum freqs := by
    simp only [trim, Array.size_extract, Nat.min_eq_left hn.2.1, Nat.sub_zero]
  refine ⟨hsize ▸ hn.1, hsize ▸ hn.2.1, ?_⟩
  intro s
  by_cases hs : s < usedCount minimum freqs
  · simp only [trim, Array.getElem?_extract, Nat.min_eq_left hn.2.1,
      Nat.zero_add, Nat.sub_zero, hs, ite_true]
  · have hz : freqs[s]?.getD 0 = 0 := by
      have := hn.2.2 s
      omega
    rw [getElem?_neg _ s (by rw [hsize]; exact hs), Option.getD_none, hz]

end LeanTex.Core.Flate.Frequencies
