/-- The oil a lantern holds. -/
def oil : Nat := 5

/-- Burning takes one unit
    per hour. -/
theorem oil_pos : 0 < oil := by decide
