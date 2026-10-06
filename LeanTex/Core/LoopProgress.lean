module

import LeanTex.Core.Loop

namespace LeanTex.Core.Loop

/-- A finite execution ending in `break`. Its length records consumed
iterations, unlike a safety invariant, which cannot distinguish an early
exit from an exhausted loop. This relation is used only in proofs. -/
public inductive Stops {α : Type} (step : α → Id (ForInStep α)) : α → Nat → α → Prop
  | done {a b} : (step a).run = .done b → Stops step a 1 b
  | yield {a b c n} : (step a).run = .yield b →
      Stops step b n c → Stops step a (n + 1) c

/-- A finite prefix which consumes iterations without taking `break`. -/
public inductive Yields {α : Type} (step : α → Id (ForInStep α)) : α → Nat → α → Prop
  | nil {a} : Yields step a 0 a
  | cons {a b c n} : (step a).run = .yield b →
      Yields step b n c → Yields step a (n + 1) c

public theorem Yields.trans {α : Type} {step : α → Id (ForInStep α)}
    {a b c : α} {m n : Nat} (h : Yields step a m b) (g : Yields step b n c) :
    Yields step a (m+n) c := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Yields.cons hs (ih g)

public theorem Yields.stops {α : Type} {step : α → Id (ForInStep α)}
    {a b c : α} {m n : Nat} (h : Yields step a m b) (g : Stops step b n c) :
    Stops step a (m+n) c := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Stops.yield hs (ih g)

/-- An exhausted loop executes exactly its yielding trace. Unlike a
safety invariant, the trace records that every iteration was consumed. -/
public theorem forIn_yields_exact {α β : Type} {step : α → Id (ForInStep α)}
    {a b : α} {n : Nat} (h : Yields step a n b) :
    ∀ xs : List β, xs.length = n →
      (forIn xs a (fun _ => step) : Id α).run = b := by
  induction h with
  | nil =>
    intro xs hn
    have hx : xs = [] := List.length_eq_zero_iff.mp hn
    subst xs
    rfl
  | cons hs _ ih =>
    intro xs hn
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      simp only [Id.run] at hs
      simp only [List.forIn_cons, bind, Id.run, hs]
      exact ih xs (by simpa using hn)

/-- A sufficient iteration budget executes the entire trace, independently
of unused iterations after its `break`. -/
public theorem forIn_stops_exact {α β : Type} {step : α → Id (ForInStep α)}
    {a b : α} {n : Nat} (h : Stops step a n b) :
    ∀ (xs : List β), n ≤ xs.length →
      (forIn xs a (fun _ => step) : Id α).run = b := by
  induction h with
  | done hs =>
    intro xs hn
    cases xs with
    | nil => simp at hn
    | cons x xs => simp [List.forIn_cons, hs]
  | yield hs _ ih =>
    intro xs hn
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      simp only [Id.run] at hs
      simp only [List.forIn_cons, bind, Id.run, hs]
      exact ih xs (by simpa using hn)

/-- The progress-indexed reading of a bounded scanner loop. -/
public theorem forIn_range_stops_exact {α : Type} {step : α → Id (ForInStep α)}
    {a b : α} {n : Nat} (h : Stops step a n b) (budget : Nat)
    (hn : n ≤ budget) :
    (forIn [0:budget] a (fun _ => step) : Id α).run = b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_stops_exact h
  simpa [Std.Legacy.Range.size] using hn

end LeanTex.Core.Loop
