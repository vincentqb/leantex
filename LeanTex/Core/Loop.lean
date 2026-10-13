module

public section

/-! Invariant readings of imperative `forIn` loops that may `break`: a state invariant the body
preserves holds of every exit. A pure invariant cannot see progress; `LoopProgress` can. -/

namespace LeanTex.Core.Loop

/-- A pure invariant: a predicate the body preserves holds of whatever the loop returns, by
`break` or exhaustion. -/
theorem forIn_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β)) :
    ∀ (l : List α) (init : β), P init →
      (∀ a ∈ l, ∀ b, P b → P (f a b).run.value) →
      P (forIn l init f : Id β).run := by
  intro l
  induction l with
  | nil => intro init h0 _; exact h0
  | cons a rest ih =>
    intro init h0 hstep
    have ha : P (f a init).run.value := hstep a (by simp) init h0
    rw [List.forIn_cons]
    show P (match (f a init).run with
            | .done b => b
            | .yield b => (forIn rest b f : Id β).run)
    cases hv : (f a init).run with
    | done b => rw [hv] at ha; exact ha
    | yield b =>
      rw [hv] at ha
      exact ih b ha (fun x hx => hstep x (by simp [hx]))

/-- `forIn_inv` over an array: `for x in xs do …`. -/
theorem forIn_array_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (xs : Array α) (init : β) (h0 : P init)
    (hstep : ∀ a ∈ xs, ∀ b, P b → P (f a b).run.value) :
    P (forIn xs init f : Id β).run := by
  rw [← Array.forIn_toList]
  exact forIn_inv P f _ init h0 (fun a ha b hb => hstep a (by simpa using ha) b hb)

/-- `forIn_inv` over an index range, the step assuming its index in range. -/
theorem forIn_range_inv {β : Type} (P : β → Prop) (f : Nat → β → Id (ForInStep β))
    (lo hi : Nat) (init : β) (h0 : P init)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ b, P b → P (f i b).run.value) :
    P (forIn [lo:hi] init f : Id β).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_inv P f _ init h0 ?_
  intro a ha b hb
  rw [List.mem_range'_1] at ha
  exact hstep a (by simp at ha; omega) (by simp [Std.Legacy.Range.size] at ha ⊢; omega) b hb

/-- Peel one loop off a block: the goal becomes the rest of the block over a state the invariant
holds of. -/
theorem bind_eq_of_inv {β γ : Type} (P : β → Prop) (L : Id β) (k : β → Id γ) (r : γ)
    (hL : P L.run) (hk : ∀ b, P b → (k b).run = r) :
    (L >>= k : Id γ).run = r := hk _ hL

/-- `bind_eq_of_inv` for a goal that is not an equation; supply `Q` explicitly. -/
theorem bind_of_inv {β γ : Type} (P : β → Prop) (Q : γ → Prop) (L : Id β) (k : β → Id γ)
    (hL : P L.run) (hk : ∀ b, P b → Q (k b).run) :
    Q (L >>= k : Id γ).run := hk _ hL

/-- A successful result satisfies `P`; a failure makes no claim. -/
@[expose] def OnSuccess {ε α : Type} (P : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => P a

theorem onSuccess_true {ε α : Type} (x : Except ε α) :
    OnSuccess (fun _ => True) x := by
  cases x <;> trivial

/-- Peel a fallible computation off a block; only a successful value reaches the continuation. -/
theorem except_bind_of_inv {ε β γ : Type} (P : β → Prop) (Q : γ → Prop)
    (L : Except ε β) (k : β → Except ε γ)
    (hL : OnSuccess P L) (hk : ∀ b, P b → OnSuccess Q (k b)) :
    OnSuccess Q (L >>= k) := by
  cases L with
  | error e => trivial
  | ok b => exact hk b hL

/-- A pure invariant over a fallible loop: neither `break` nor a throw invents a success. -/
theorem except_forIn_inv {ε α β : Type} (P : β → Prop)
    (f : α → β → Except ε (ForInStep β)) :
    ∀ (l : List α) (init : β), P init →
      (∀ a ∈ l, ∀ b, P b → OnSuccess (fun s => P s.value) (f a b)) →
      OnSuccess P (forIn l init f : Except ε β) := by
  intro l
  induction l with
  | nil => intro init h0 _; exact h0
  | cons a rest ih =>
    intro init h0 hstep
    have ha := hstep a (by simp) init h0
    rw [List.forIn_cons]
    cases hf : f a init with
    | error e => trivial
    | ok step =>
      rw [hf] at ha
      cases step with
      | done b => exact ha
      | yield b =>
        exact ih b ha (fun x hx => hstep x (by simp [hx]))

/-- `except_forIn_inv` over the index ranges used by fallible scanners. -/
theorem except_forIn_range_inv {ε β : Type} (P : β → Prop)
    (f : Nat → β → Except ε (ForInStep β))
    (lo hi : Nat) (init : β) (h0 : P init)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ b, P b →
      OnSuccess (fun s => P s.value) (f i b)) :
    OnSuccess P (forIn [lo:hi] init f : Except ε β) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine except_forIn_inv P f _ init h0 ?_
  intro a ha b hb
  rw [List.mem_range'_1] at ha
  exact hstep a (by simp at ha; omega)
    (by simp [Std.Legacy.Range.size] at ha ⊢; omega) b hb

end LeanTex.Core.Loop
