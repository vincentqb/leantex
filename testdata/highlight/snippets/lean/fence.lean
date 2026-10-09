-- A `lean` fence holds Lean 4.
theorem two_eq : 1 + 1 = 2 := rfl

def rowsPlanted : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * rowsPlanted n

#eval rowsPlanted 4 -- 16
