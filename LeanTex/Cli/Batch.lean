module

import Std

namespace LeanTex.Cli.Batch

/-- Take a bounded source prefix, stopping before a repeated resource key.
The remainder is untouched, so repeated requests serialize without changing
the order of results or allowing concurrent writes to one cache slot. -/
private def takeBatch [DecidableEq κ] (key : α → κ) : Nat → List κ → List α → List α × List α
  | 0, _, xs => ([], xs)
  | _ + 1, _, [] => ([], [])
  | n + 1, seen, x :: xs =>
    if key x ∈ seen then ([], x :: xs)
    else
      let (front, rest) := takeBatch key n (key x :: seen) xs
      (x :: front, rest)

private theorem takeBatch_exact [DecidableEq κ] (key : α → κ) (n : Nat)
    (seen : List κ) (xs : List α) :
    (takeBatch key n seen xs).1 ++ (takeBatch key n seen xs).2 = xs := by
  induction n generalizing seen xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [takeBatch]
      split
      · rfl
      · simp only [List.cons_append, List.cons.injEq, true_and]
        exact ih _ _

private theorem takeBatch_length_le [DecidableEq κ] (key : α → κ) (n : Nat)
    (seen : List κ) (xs : List α) :
    (takeBatch key n seen xs).1.length ≤ n := by
  induction n generalizing seen xs with
  | zero => simp [takeBatch]
  | succ n ih =>
    cases xs with
    | nil => simp [takeBatch]
    | cons x xs =>
      simp only [takeBatch]
      split
      · simp
      · simpa using Nat.succ_le_succ (ih (key x :: seen) xs)

private theorem takeBatch_rest_le [DecidableEq κ] (key : α → κ) (n : Nat)
    (seen : List κ) (xs : List α) :
    (takeBatch key n seen xs).2.length ≤ xs.length := by
  have h := congrArg List.length (takeBatch_exact key n seen xs)
  simp only [List.length_append] at h
  omega

private theorem takeBatch_fresh [DecidableEq κ] (key : α → κ) (n : Nat)
    (seen : List κ) (xs : List α) :
    ∀ k ∈ (takeBatch key n seen xs).1.map key, k ∉ seen := by
  induction n generalizing seen xs with
  | zero => simp [takeBatch]
  | succ n ih =>
    cases xs with
    | nil => simp [takeBatch]
    | cons x xs =>
      simp only [takeBatch]
      split
      · simp
      · intro k h
        rcases List.mem_cons.mp h with rfl | h
        · assumption
        · exact fun hs => ih (key x :: seen) xs k h (List.mem_cons_of_mem _ hs)

private theorem takeBatch_keys_nodup [DecidableEq κ] (key : α → κ) (n : Nat)
    (seen : List κ) (xs : List α) :
    ((takeBatch key n seen xs).1.map key).Nodup := by
  induction n generalizing seen xs with
  | zero => simp [takeBatch]
  | succ n ih =>
    cases xs with
    | nil => simp [takeBatch]
    | cons x xs =>
      simp only [takeBatch]
      split
      · simp
      · apply List.nodup_cons.mpr
        exact ⟨fun h => takeBatch_fresh key n (key x :: seen) xs (key x) h
          (List.mem_cons_self ..), ih _ _⟩

/-- `extra + 1` is the concurrency bound; zero extra workers still makes
progress. Each batch owns distinct resource keys. -/
public def plan [DecidableEq κ] (extra : Nat) (key : α → κ) (xs : List α) : List (List α) :=
  match xs with
  | [] => []
  | x :: xs =>
    let cut := takeBatch key extra [key x] xs
    (x :: cut.1) :: plan extra key cut.2
termination_by xs.length
decreasing_by
  have := takeBatch_rest_le key extra [key x] xs
  simp only [List.length_cons]
  omega

public theorem plan_exact [DecidableEq κ] (extra : Nat) (key : α → κ) (xs : List α) :
    (plan extra key xs).flatten = xs := by
  induction xs using (plan.induct extra key) with
  | case1 => simp [plan]
  | case2 x xs cut ih =>
    rw [plan]
    change (plan extra key (takeBatch key extra [key x] xs).2).flatten =
      (takeBatch key extra [key x] xs).2 at ih
    simp only [List.flatten_cons, List.cons_append]
    rw [ih]
    exact congrArg (List.cons x) (takeBatch_exact key extra [key x] xs)

public theorem plan_bounded [DecidableEq κ] (extra : Nat) (key : α → κ) (xs : List α) :
    ∀ batch ∈ plan extra key xs, batch.length ≤ extra + 1 := by
  induction xs using (plan.induct extra key) with
  | case1 => simp [plan]
  | case2 x xs cut ih =>
    rw [plan]
    intro batch h
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.succ_le_succ (takeBatch_length_le key extra [key x] xs)
    · exact ih _ h

public theorem plan_keys_nodup [DecidableEq κ] (extra : Nat) (key : α → κ) (xs : List α) :
    ∀ batch ∈ plan extra key xs, (batch.map key).Nodup := by
  induction xs using (plan.induct extra key) with
  | case1 => simp [plan]
  | case2 x xs cut ih =>
    rw [plan]
    intro batch h
    rcases List.mem_cons.mp h with rfl | h
    · apply List.nodup_cons.mpr
      exact ⟨fun h => takeBatch_fresh key extra [key x] xs (key x) h
        (List.mem_cons_self ..), takeBatch_keys_nodup key extra [key x] xs⟩
    · exact ih _ h

/-- Execute the checked source partition. All started tasks are joined,
including after a failure; an exception cannot leave cache writers running.
Results are collected in source order, independently of completion order. -/
public def map [DecidableEq κ] (limit : Nat) (key : α → κ)
    (f : α → IO β) (xs : Array α) : IO (Array β) := do
  let mut result := #[]
  for batch in plan (limit - 1) key xs.toList do
    let tasks ← batch.mapM fun x => IO.asTask (f x) Task.Priority.dedicated
    let mut failure : Option IO.Error := none
    for task in tasks do
      match task.get with
      | .ok value => result := result.push value
      | .error error => if failure.isNone then failure := some error
    if let some error := failure then throw error
  return result

end LeanTex.Cli.Batch
