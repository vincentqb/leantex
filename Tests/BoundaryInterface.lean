module

import LeanTex.Cli.Boundary

/-! Ordinary clients can classify and withdraw answered requests while
retaining unfinished attempts. Refusal projection remains private. -/

open LeanTex.Core LeanTex.Cli
open LeanTex.Cli.Boundary

namespace Tests.BoundaryInterface

example : System.FilePath → String → String → Option Span → IO (Except Diag ByteArray) :=
  @coldPicture
example : Repr Withdrawal := inferInstance
example : Repr Undrawn := inferInstance
example (ids : Array String) (standing : Array (String × Diag)) (notes : Array Diag) :
    Withdrawal := { ids, standing, notes }
example (w : Withdrawal) : Array String × Array (String × Diag) × Array Diag :=
  (w.ids, w.standing, w.notes)
example (d : Diag) (said : Option String) : Array Undrawn :=
  #[.answered d said, .unfinished d]
example (u : Undrawn) : Diag :=
  match u with
  | .answered d _ => d
  | .unfinished d => d
example : String → PicCache.Outcome → Option Span → Option Undrawn := undrawnOf
example : String → Array String → Array (String × Span) →
    Withdrawal → String × Undrawn → Withdrawal := withdrawStep
example : String → Array String → Array (String × Undrawn) →
    Array (String × Span) → Withdrawal := withdraw
example : Array String → Array String → Array String := htmlWithdraw

example (tool : String) (fallbacks : Array String) (spans : Array (String × Span))
    (w : Withdrawal) (src : String) (d : Diag) :
    withdrawStep tool fallbacks spans w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } :=
  withdrawStep_unfinished_exact tool fallbacks spans w src d

example : True := by
  fail_if_success have := Boundary.Undrawn.why
  trivial

end Tests.BoundaryInterface
