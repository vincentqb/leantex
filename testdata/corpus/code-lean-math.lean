-- leantex: show = math, code, facts = code-lean-math.facts
/-! # Long statements

Invented statements longer than a line, which the math view breaks inside their parentheses. -/

namespace Weir

/-- A negated conjunction and a quantified hypothesis, each wider than the measure. -/
theorem gate_flow (a b c d : Nat)
    (_h : Not (And (a < b) (Or (b < c) (Or (c < d) (d + a < b + c))))) :
    (forall n : Nat, n < a ->
      And (Or (n < b) (Or (n + 1 < c) (n + 2 < d)))
        (Exists fun m : Nat => And (m < c) (And (n + m < d) (m + n < a + b + c + d)))) ->
    a + b <= a + b + c + d :=
  fun _ => by omega

end Weir
