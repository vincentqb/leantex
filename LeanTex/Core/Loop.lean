module

public section

/-!
# Loops, statable

A hot path here is an imperative loop — `Id.run do … for … break`, an
`Array` or a `mut` accumulator threaded through — because that is what the
performance rule asks for. The cost was that no theorem could reach inside
one: `forIn` over a range whose body may `break` has no equational theory an
induction can enter, so seventeen owed obligations named the same wall from
seven modules.

The stdlib closes half of it. `List.idRun_forIn_yield_eq_foldl` and its
`Array`/`forIn'` siblings turn a loop into a `foldl` — but only a loop that
never breaks, because a `ForInStep.done` has no fold to become. Every engine
loop bounded `[0:n + 1]` with `if … then break` is exactly the excluded case.

What is here is the other half, and it is a *reading* layer, not a
refactor: nothing below mentions the engine, and no loop had to change shape
to be read by it.

* `forIn_inv` — a state invariant that survives `break`. Whatever the loop
  leaves, by `yield` or by `done`, satisfies any predicate its body
  preserves. Proved by induction on the list, one `ForInStep` case split.
* `forIn_array_inv`, `forIn_range_inv` — the two shapes the engine writes,
  over `Array` and over `[lo:hi]`.
* `bind_eq_of_inv`, `bind_of_inv` — the composition. An engine function is
  not one loop but a chain of them inside one `Id.run do`, and these peel
  one loop off the front: the invariant discharges the loop, and the rest of
  the block becomes the next goal with the loop's state replaced by an
  arbitrary value the invariant holds of. Applied n times for n loops.
* `OnSuccess`, `except_forIn_inv`, `except_bind_of_inv` — the same reading
  for a scan that can fail. An error propagates without a value; every
  successful exit, including `break`, preserves the invariant.

The discipline this supports is recorded in AGENTS.md's obligation table:
a loop owes the invariant its statement will be read through, named beside
it. What the pair does *not* reach, so it is not mistaken for more than it
is: a pure invariant cannot see how much of the input the loop has
consumed, so a claim about the loop's *value* (a census, a round trip)
needs either the break-free `foldl` bridge above or its own
progress-indexed argument. `_covers`-shaped safety claims are what this
layer is for.
-/

namespace LeanTex.Core.Loop

/-- **A `break` does not escape an invariant.** A predicate the body
preserves holds of whatever the loop returns, whether it ran out of input
or stopped early: `ForInStep.value` reads the state out of `done` and
`yield` alike, so the two exits are one channel as far as a safety property
is concerned.

The `Id` reading is unconditional; `except_forIn_inv` gives the corresponding
success postcondition for a scan that can also throw. -/
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

/-- `forIn_inv` over an index range: `for i in [lo:hi] do …`, the shape an
index loop over an array's bounds takes. The step may assume the index is
in range, which is how a body that reads `xs[i]` is discharged. -/
theorem forIn_range_inv {β : Type} (P : β → Prop) (f : Nat → β → Id (ForInStep β))
    (lo hi : Nat) (init : β) (h0 : P init)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ b, P b → P (f i b).run.value) :
    P (forIn [lo:hi] init f : Id β).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_inv P f _ init h0 ?_
  intro a ha b hb
  rw [List.mem_range'_1] at ha
  exact hstep a (by simp at ha; omega) (by simp [Std.Legacy.Range.size] at ha ⊢; omega) b hb

/-- **Peel one loop off a block.** An engine function is a chain of loops in
one `Id.run do`, and this is what walks the chain: give the front loop's
invariant, and the goal becomes the rest of the block over an arbitrary
state the invariant holds of. The conclusion is an equation rather than a
predicate so that the unification is first-order — `(?L >>= ?k)` against the
block — which is what lets `refine` find the split without the loop or its
continuation being spelled out. -/
theorem bind_eq_of_inv {β γ : Type} (P : β → Prop) (L : Id β) (k : β → Id γ) (r : γ)
    (hL : P L.run) (hk : ∀ b, P b → (k b).run = r) :
    (L >>= k : Id γ).run = r := hk _ hL

/-- `bind_eq_of_inv` for a goal that is not an equation. The postcondition
must be supplied explicitly (`(Q := …)`): it appears only applied, so the
unifier cannot recover it from the goal. -/
theorem bind_of_inv {β γ : Type} (P : β → Prop) (Q : γ → Prop) (L : Id β) (k : β → Id γ)
    (hL : P L.run) (hk : ∀ b, P b → Q (k b).run) :
    Q (L >>= k : Id γ).run := hk _ hL

/-- A successful result satisfies `P`. Failure supplies no value and makes
no claim about one; in particular this is not a termination or success
guarantee. -/
def OnSuccess {ε α : Type} (P : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => P a

/-- No information is needed from a computation whose result is ignored
by the invariant. Its failures still propagate through `except_bind_of_inv`. -/
theorem onSuccess_true {ε α : Type} (x : Except ε α) :
    OnSuccess (fun _ => True) x := by
  cases x <;> trivial

/-- **Peel a fallible computation off a block.** Only a successful value
reaches the continuation. An error on either side remains an error. -/
theorem except_bind_of_inv {ε β γ : Type} (P : β → Prop) (Q : γ → Prop)
    (L : Except ε β) (k : β → Except ε γ)
    (hL : OnSuccess P L) (hk : ∀ b, P b → OnSuccess Q (k b)) :
    OnSuccess Q (L >>= k) := by
  cases L with
  | error e => trivial
  | ok b => exact hk b hL

/-- **Neither `break` nor a throw can invent a successful state.** The
body's invariant covers `done` and `yield`; a thrown error bypasses both
the tail of the loop and its continuation. -/
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
