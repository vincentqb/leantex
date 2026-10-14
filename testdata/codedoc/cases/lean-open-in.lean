namespace Lantern

open Nat in
/-- A wick's length, in a section of its own. -/
def wick : Nat := succ 2

open Nat in
set_option autoImplicit false in
/-- Two layers of `in`. -/
theorem wick_pos : 0 < wick := by decide

end Lantern
