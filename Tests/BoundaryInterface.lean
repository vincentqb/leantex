module

import LeanTex.Cli.Boundary

/-! Ordinary clients can classify and withdraw answered requests while
retaining unfinished attempts. Refusal projection remains private. -/

open LeanTex.Core LeanTex.Cli
open LeanTex.Cli.Boundary

namespace Tests.BoundaryInterface

example : System.FilePath → String → String → Option Span → String → IO (Except Diag ByteArray) :=
  @coldPicture
example : Repr Withdrawal := inferInstance
example : Repr Undrawn := inferInstance
example (ids : Array String) (standing : Array (String × Diag))
    (said : Array (String × Option String)) : Withdrawal := { ids, standing, said }
example (w : Withdrawal) : Array String × Array (String × Diag) × Array (String × Option String) :=
  (w.ids, w.standing, w.said)
example (d : Diag) (said : Option String) : Array Undrawn :=
  #[.answered d said, .unfinished d]
example (u : Undrawn) : Diag :=
  match u with
  | .answered d _ => d
  | .unfinished d => d
example : String → PicCache.Outcome → Option Span → String → Option Undrawn := undrawnOf
example : Array String → Withdrawal → String × Undrawn → Withdrawal := withdrawStep
example : Array String → Array (String × Undrawn) → Withdrawal := withdraw
example : String → Diag → Bool := fragmentOf
example : String → Diag → Bool := inlineOf
example : (String → Bool) → String → String → Array Diag → Diag → Diag := lineOf
example (block : String) (inline : Option String) : LineHelp := { block, inline }
example : String → Option String → LineHelp := withdrawnLine
example : LineHelp := declinedLine
example : String → Withdrawal → Array String → Array (String × LineHelp) := linesOf
example : Array String → Bool → Array (String × LineHelp) → Array Diag → Array Diag := foldLines
example : Array String → Bool → String → Withdrawal → Array Diag → Array Diag := fold
example : Array String → Array String → Array String := htmlWithdraw
example : String := facelessReason
example : Image.Loaded → Bool := faceless
example : Image.Store → Image.Store := markFaceless

example (s : Image.Store) :
    ∀ en ∈ (markFaceless s).entries, en.src.startsWith Ir.picSrcPrefix = true →
      en.webSvg.isSome = true ∨ en.webError.isSome = true :=
  markFaceless_covers s
example (s : Image.Store) :
    (markFaceless s).entries.map (fun en => { en with webError := none }) =
      s.entries.map (fun en => { en with webError := none }) :=
  markFaceless_info_exact s
example (s : Image.Store) (k : Nat) (en : Image.Loaded) (h : s.get? k = some en)
    (hface : faceless en = false) : (markFaceless s).get? k = some en :=
  markFaceless_face_exact s k en h hface

example (fallbacks : Array String) (w : Withdrawal) (src : String) (d : Diag) :
    withdrawStep fallbacks w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } :=
  withdrawStep_unfinished_exact fallbacks w src d

example (allow : Array String) (allowAll : Bool) (tool : String) (w : Withdrawal)
    (ds : Array Diag) (d : Diag) (hd : d ∈ ds)
    (h : ∀ p ∈ w.said, fragmentOf p.1 d = false ∧ inlineOf p.1 d = false) :
    d ∈ fold allow allowAll tool w ds :=
  fold_covers allow allowAll tool w ds d hd h
example (allow : Array String) (allowAll : Bool) (lines : Array (String × LineHelp))
    (ds : Array Diag) (d : Diag) (hd : d ∈ ds)
    (h : ∀ p ∈ lines, fragmentOf p.1 d = false ∧ inlineOf p.1 d = false) :
    d ∈ foldLines allow allowAll lines ds :=
  foldLines_covers allow allowAll lines ds d hd h

example : True := by
  fail_if_success have := Boundary.Undrawn.why
  fail_if_success have := Boundary.markOne
  fail_if_success have := Boundary.markStopped
  trivial

end Tests.BoundaryInterface
