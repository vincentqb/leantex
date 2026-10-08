namespace Garden

/-- A plot of land, measured in whole metres. -/
structure Plot where
  width : Nat
  depth : Nat
  deriving Repr

def Plot.area (p : Plot) : Nat := p.width * p.depth

@[simp] theorem Plot.area_comm (p : Plot) : p.area = p.depth * p.width := by
  unfold Plot.area
  exact Nat.mul_comm _ _

theorem pending (n : ℕ) : n + 0 = n := by admit

example : (3 : Nat) ≤ 5 := by decide

end Garden
