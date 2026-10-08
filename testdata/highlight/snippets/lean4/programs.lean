import Std.Data.HashMap
open Std

/-!
# Counting words

A module docstring opens with `/-!`.
-/

def countWords (text : String) : HashMap String Nat := Id.run do
  let mut counts : HashMap String Nat := {}
  for word in text.splitOn " " do
    unless word.isEmpty do
      counts := counts.insert word (counts.getD word 0 + 1)
  return counts

private def collatz (n : Nat) (steps : Nat := 0) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

#eval collatz 27

variable {α : Type} [Inhabited α]

def firstOr (xs : List α) : α := xs.headD default

set_option maxRecDepth 2000 in
example : 2 ^ 10 = 1024 := rfl
