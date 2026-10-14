structure Lamp where
  /-- The lamp's height. -/
  height : Nat
  /-- The lamp's width. -/
  width : Nat

inductive Shade where
  /-- A paper shade. -/
  | paper
  /-- A glass shade. -/
  | glass
