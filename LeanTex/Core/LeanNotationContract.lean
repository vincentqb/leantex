module

public import LeanTex.Core.LeanNotation
import all LeanTex.Core.LeanNotation

/-! # The notation table determines its constants

What the table shows for a constant names that constant: no two constants show alike. -/

namespace LeanTex.Core.LeanNotation

private theorem keys_inj : ∀ a ∈ notations, ∀ b ∈ notations,
    (a.glyph, a.shape) = (b.glyph, b.shape) → a = b := by decide +kernel

/-- The table's output determines the constant it was given. -/
public theorem shownOf_inj (c₁ c₂ : String) (h : shownOf c₁ = shownOf c₂) : c₁ = c₂ := by
  unfold shownOf at h
  cases h₁ : notations.find? (·.const == c₁) <;> cases h₂ : notations.find? (·.const == c₂) <;>
    simp only [h₁, h₂, reduceCtorEq, Shown.notation.injEq, Shown.name.injEq] at h
  · exact h
  · rename_i n₁ n₂
    have e₁ := List.find?_some h₁
    have e₂ := List.find?_some h₂
    have hn := keys_inj n₁ (List.mem_of_find?_eq_some h₁) n₂ (List.mem_of_find?_eq_some h₂)
      (by rw [h.1, h.2])
    subst hn
    simp only [beq_iff_eq] at e₁ e₂
    exact e₁.symm.trans e₂

end LeanTex.Core.LeanNotation
