module

public import LeanTex.Core.Marker
public import LeanTex.Core.Lex
import all LeanTex.Core.Marker

/-! Kernel checks of the engine's declaration markers: each reads back from its name, and no
control word a document writes reads as one. -/

namespace LeanTex.Core.Marker

/-- Every marker reads back from its name. -/
public theorem read_name_exact (k : Kind) (v : String) : read? (name k v) = some (k, v) := by
  have h : ' ' ∉ k.word.toList := by cases k <;> decide +kernel
  have hl : Kind.words.lookup k.word = some k := by cases k <;> decide +kernel
  simp [name, read?, String.front?_eq, String.toList_append, KeyVal.cutAt_append _ _ _ h,
    KeyVal.cutAt, hl]

/-- A control name Lex reads, one character or a run of name characters, is no marker's. -/
public theorem read_ctrlWord_exact (n : String)
    (h : n.toList.length ≤ 1 ∨ n.toList.all Lex.nameChar = true) : read? n = none := by
  unfold read?
  rw [String.front?_eq]
  cases hn : n.toList with
  | nil => simp
  | cons c rest =>
    by_cases hc : c = ' '
    · subst hc
      rcases h with h | h
      · have : rest = [] := by rw [hn] at h; simpa using h
        subst this
        simp [KeyVal.cutAt]
      · rw [hn] at h
        simp [Lex.nameChar] at h
    · simp [hc]

end LeanTex.Core.Marker
