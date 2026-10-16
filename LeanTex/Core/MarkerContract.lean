module

public import LeanTex.Core.Marker
import all LeanTex.Core.Marker

/-! Kernel checks of the engine's declaration markers: each reads back from its name, and no
document's control word spells one. -/

namespace LeanTex.Core.Marker

/-- Every marker reads back from its name. -/
public theorem read_name_exact (k : Kind) (v : String) : read? (name k v) = some (k, v) := by
  have h : ' ' ∉ k.word.toList := by cases k <;> decide +kernel
  have hl : Kind.words.lookup k.word = some k := by cases k <;> decide +kernel
  simp [name, read?, String.toList_append, KeyVal.cutAt_append _ _ _ h, KeyVal.cutAt, hl]

/-- Every marker's name opens on a space, which no control word longer than one character holds. -/
public theorem name_unforgeable (k : Kind) (v : String) :
    ∃ rest, (name k v).toList = ' ' :: rest ∧ rest ≠ [] :=
  ⟨(k.word ++ " " ++ v).toList, by simp [name, String.toList_append], by simp⟩

end LeanTex.Core.Marker
