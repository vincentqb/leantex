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
example : ByteArray → PicCache.Outcome → Except String ByteArray := checkedFace
example : ByteArray → IO (Except String ByteArray) := htmlFace
example (svg : ByteArray) (o : PicCache.Outcome) (why : String) :
    checkedFace svg o = .error why ↔ o = .inconclusive why :=
  checkedFace_unfinished_exact svg o why
example (svg : ByteArray) (o : PicCache.Outcome) (h : ∀ why, o ≠ .inconclusive why) :
    checkedFace svg o = .ok svg :=
  checkedFace_verdict_exact svg o h
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

example : String := unplannedReason
example : Array Image.Request → Image.Loaded → Bool := unplanned
example : Array Image.Request → Image.Store → Image.Store := markUnplanned
example (stopped : Array Image.Request) (s : Image.Store) :
    ∀ en ∈ (markUnplanned stopped s).entries, stopped.contains en.toRequest = true →
      en.info.isNone = true → en.webError.isSome = true :=
  markUnplanned_covers stopped s
example (stopped : Array Image.Request) (s : Image.Store) :
    (markUnplanned stopped s).entries.map (fun en => { en with webError := none }) =
      s.entries.map (fun en => { en with webError := none }) :=
  markUnplanned_info_exact stopped s
example (stopped : Array Image.Request) (s : Image.Store) (k : Nat) (en : Image.Loaded)
    (h : s.get? k = some en) (hkept : unplanned stopped en = false) :
    (markUnplanned stopped s).get? k = some en :=
  markUnplanned_kept_exact stopped s k en h hkept

example (tool : String) (fallbacks : Array String) (spans : Array (String × Span))
    (w : Withdrawal) (src : String) (d : Diag) :
    withdrawStep tool fallbacks spans w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } :=
  withdrawStep_unfinished_exact tool fallbacks spans w src d

example : True := by
  fail_if_success have := Boundary.Undrawn.why
  fail_if_success have := Boundary.markOne
  fail_if_success have := Boundary.markStopped
  trivial

end Tests.BoundaryInterface
