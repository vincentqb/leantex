mutual
/-- Whether a count is even. -/
def evenly : Nat → Bool
  | 0 => true
  | n + 1 => oddly n
/-- Whether a count is odd. -/
def oddly : Nat → Bool
  | 0 => false
  | n + 1 => evenly n
end
