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

/-- Read only the named element's attribute. A descendant's triangle mask
does not clip its containing box, nor reserve room for that box. -/
private def cancelAttr (key : String) : Html.Node → String
  | .elem _ attrs _ => (attrs.find? (·.1 == key)).map (·.2) |>.getD ""
  | _ => ""

private def cancelKids : Html.Node → Array Html.Node
  | .elem _ _ kids => kids
  | _ => #[]

/-- Whether `hay` contains `needle`. -/
private def cancelHasStr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

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

  -- These are ownership facts about the emitted tree. A triangle's own
  -- clip-path says nothing about containment in its parent: rendered
  -- checks must establish the platform's motion-path placement and bounds.
  let emit (mark : CancelMark) (room thick : Bool) : Html.Node :=
    MathMl.nucNode {} false .ord
      (.cancel mark { room, thick } (if mark == .to then one '7' else .nil) (one 'x'))
  let boxOf (mark : CancelMark) (n : Html.Node) : Html.Node :=
    if mark == .to then (cancelKids n).getD 0 (.text "") else n
  let ownsBands (mark : CancelMark) (node : Html.Node) : Bool :=
    let css := cancelAttr "style" (boxOf mark node)
    cancelHasStr css "padding:" && cancelHasStr css "background-image:" &&
      (css.splitOn "linear-gradient(").length == (if mark == .cross then 3 else 2) &&
      cancelHasStr css (if mark == .down then "to top right" else "to top left") &&
      (mark != .cross || cancelHasStr css "to top right")
  for mark in [CancelMark.up, .down, .cross, .to] do
    for room in [true, false] do
      for thick in [true, false] do
        let node := emit mark room thick
        let box := boxOf mark node
        let css := cancelAttr "style" box
        let label := s!"{repr mark}/room={room}/thick={thick}"
        t s!"cancel HTML: {label} padded operand owns every diagonal band"
          (ownsBands mark node)
        let misplacedBox := Html.Node.elem "mrow" #[] #[box]
        let misplaced := if mark == .to then
            Html.Node.elem "msup" #[] #[misplacedBox, (cancelKids node).getD 1 (.text "")]
          else misplacedBox
        t s!"cancel HTML: {label} band judge rejects paint owned by a descendant"
          (!ownsBands mark misplaced)
        t s!"cancel HTML: {label} room mode governs the operand's own margins"
          (cancelHasStr css "margin-left: -" == !room &&
            cancelHasStr css "margin-right: -" == !room)
        if mark == .to then
          let head := (cancelKids box).getD 1 (.text "")
          let value := (cancelKids node).getD 1 (.text "")
          let valueRow := if room then value else (cancelKids value).getD 0 (.text "")
          t s!"cancel HTML: {label} arrowhead belongs to the struck row"
            ((cancelKids box).size == 2 &&
              cancelHasStr (cancelAttr "style" head) "clip-path: polygon")
          t s!"cancel HTML: {label} target owns its clearance and room"
            (cancelHasStr (cancelAttr "style" valueRow) "padding-left:" &&
              cancelAttr "width" value == (if room then "" else "0"))
      t s!"cancel HTML: {repr mark}/room={room} thicklines changes the painted band"
        (cancelAttr "style" (boxOf mark (emit mark room true)) !=
          cancelAttr "style" (boxOf mark (emit mark room false)))
