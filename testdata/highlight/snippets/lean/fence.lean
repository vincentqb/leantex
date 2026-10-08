-- A `lean` fence holds Lean 4.
theorem two_eq : 1 + 1 = 2 := rfl

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 10 -- 55
