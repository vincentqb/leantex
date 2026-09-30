import LeanTex.Core.MathMl

open LeanTex.Core LeanTex.Core.Math

mutual

/-- Read the target's font-size level from the emitted tree. MathML Core
§2.1.6 and §3.4.1: an `msup` script child increments inherited math-depth;
an explicit `scriptlevel` replaces that increment on that element.
`+0` on a descendant only preserves the depth its parent already has.
Unrecognised levels remain `none`, so they cannot certify a size. -/
private def cancelTargetDepths (parent : Option Nat) (script : Bool)
    (acc : List (Option Nat)) : Html.Node → List (Option Nat)
  | .text s => if s == "7" then parent :: acc else acc
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let depth := match attrs.find? (·.1 == "scriptlevel") with
      | some (_, "+0") => parent
      | some (_, n) => n.toNat?
      | none => parent.map (· + if script then 1 else 0)
    cancelTargetDepthList depth (tag == "msup") 0 acc kids.toList

private def cancelTargetDepthList (parent : Option Nat) (sup : Bool) (index : Nat)
    (acc : List (Option Nat)) : List Html.Node → List (Option Nat)
  | [] => acc
  | n :: ns =>
    cancelTargetDepthList parent sup (index + 1)
      (cancelTargetDepths parent (sup && index == 1) acc n) ns

end

private def cancelStyleDepth : MathStyle → Nat
  | .display _ | .text _ => 0
  | .script _ => 1
  | .scriptscript _ => 2

/-- Room allocation cannot change a cancellation target's font-size level.
The expected level comes from the same IR style rule the PDF layout reads.
Smaller targets still step down; `samesize` also preserves inherited script
and scriptscript size. The checks read emitted MathML, not the IR dump. -/
def cancelHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (name :: ·)
  let target := Html.Node.elem "mn" #[] #[.text "7"]
  let base := Html.Node.elem "mi" #[] #[.text "x"]
  let same := Html.Node.elem "mrow" #[("scriptlevel", "+0")] #[target]
  let direct := Html.Node.elem "msup" #[] #[base, same]
  let wrapped := Html.Node.elem "msup" #[] #[base, .elem "mpadded" #[] #[same]]
  t "cancel HTML size judge distinguishes a script slot from its descendant"
    (cancelTargetDepths (some 0) false [] direct == [some 0] &&
      cancelTargetDepths (some 0) false [] wrapped == [some 1])
  let one (c : Char) : MList := .cons (.atom .ord (.sym c) .nil .nil false) .nil
  let styles : List MathStyle := [.display false, .text false]
  let cases : List (String × CancelSize × List MathStyle) :=
    [("samesize", .same, allStyles), ("smaller", .step, styles), ("Smaller", .sup, styles)]
  for (label, size, contexts) in cases do
    for st in contexts do
      for room in [true, false] do
        let spec : CancelSpec := { size, room }
        let node := Html.Node.elem "mrow" (MathMl.styleAttrs (some st))
          #[MathMl.nucNode {} (st matches .display _) .ord
            (.cancel .to spec (one '7') (one 'x'))]
        let allocation := if room then "makeroom" else "overlap"
        t s!"cancel HTML {allocation}+{label} keeps the IR target size in {repr st}"
          (cancelTargetDepths (some 0) false [] node ==
            [some (cancelStyleDepth (spec.size.style st))])
