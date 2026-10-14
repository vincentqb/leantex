/-- The number of steps a tide takes to rise `n` marks. -/
def steps (n : Nat) : Nat := 2 * n

theorem steps_zero : steps 0 = 0 := rfl
