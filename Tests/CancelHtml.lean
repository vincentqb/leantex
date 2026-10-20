module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Math

mutual

/-- The target's font-size level read from the emitted tree, by MathML Core's math-depth rules
(§2.1.6, §3.4.1); an unrecognised level stays `none`. -/
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

/-- A corner triangle's whole containing rectangle lies in the operand: anchors and percentage caps
govern both axes, and every polygon coordinate lies inside. -/
private def cancelHeadPlaced (rule : Nat) (box : Html.Node) : Bool :=
  let head := (nodeKids box).back?.getD (.text "")
  let css := nodeAttr "style" head
  let size := s!"min({MathMl.milliEm (4 * rule)}, 100%)"
  nodeCss "position" box == "relative" &&
    nodeCss "position" head == "absolute" &&
    nodeCss "right" head == "0" && nodeCss "top" head == "0" &&
    (nodeCss "left" head).isEmpty &&
    nodeCss "width" head == size && nodeCss "height" head == size &&
    nodeCss "clip-path" head == "polygon(0 50%, 100% 0, 50% 100%)" &&
    !hasStr css "offset-" && !hasStr css "transform" &&
    (nodeKids head).isEmpty

private def cancelTag : Html.Node → String
  | .elem tag _ _ => tag
  | _ => ""

/-- Mutations change the emitted artifact before its coordinates are read, so they exercise the
parser and the judge together. -/
private def cancelSetAttr (key value : String) : Html.Node → Html.Node
  | .elem tag attrs kids => .elem tag ((attrs.filter (·.1 != key)).push (key, value)) kids
  | other => other

private def cancelSetChild (i : Nat) (child : Html.Node) : Html.Node → Html.Node
  | .elem tag attrs kids => .elem tag attrs (kids.set! i child)
  | other => other

/-- Coordinates read from the emitted SVG viewport and the native MathML placement boxes along the
pen, the SVG's downward y mapped to the parent baseline. -/
private structure CancelHtmlRead where
  width : Int
  top : Int
  bot : Int
  body : Int × Int
  value : Int × Int
  polys : Array (Array (Int × Int))
  target : Html.Node
  svg : Html.Node

/-- A placement box's start past the pen, its advance and its raise. -/
private def cancelBox (em : Int) (n : Html.Node) : Option (Int × Int × Int) := do
  if cancelTag n != "mpadded" || nodeAttr "lspace" n != "0" then none else do
    let left ← if (nodeCss "margin-left" n).isEmpty then some 0
      else readEm em (nodeCss "margin-left" n)
    let w ← readEm em (nodeAttr "width" n)
    let right ← readEm em (nodeCss "margin-right" n)
    let y ← readEm em (nodeAttr "voffset" n)
    return (left, w + right, y)

private def cancelRead (em : Int) (node : Html.Node) : Option CancelHtmlRead := do
  if cancelTag node != "mpadded" || !(nodeCss "position" node).isEmpty then none else do
    let boxWidth ← readEm em (nodeAttr "width" node)
    let margin ← if (nodeCss "margin-inline-end" node).isEmpty then some 0
      else readEm em (nodeCss "margin-inline-end" node)
    let width := boxWidth + margin
    let top ← readEm em (nodeAttr "height" node)
    let depth ← readEm em (nodeAttr "depth" node)
    let text ← (nodeKids node)[0]?
    let b ← (nodeKids node)[1]?
    let v ← (nodeKids node)[2]?
    if (MathMl.nodeChars #[] b) != #['x'] || (MathMl.nodeChars #[] v) != #['7'] then none else do
      let (bl, ba, by_) ← cancelBox em b
      let (vl, _, vy) ← cancelBox em v
      let target ← (nodeKids v)[0]?
      let svg ← (nodeKids text)[0]?
      if cancelTag text != "mtext" || cancelTag svg != "svg" ||
          !(nodeCss "position" svg).isEmpty || nodeCss "vertical-align" svg != "baseline" ||
          nodeCss "overflow" svg != "visible" ||
          !(nodeAttr "preserveAspectRatio" svg).isEmpty then none else do
        let ox ← readEm em (nodeCss "margin-left" svg)
        let ob ← readEm em (nodeCss "margin-bottom" svg)
        let right ← readEm em (nodeCss "margin-right" svg)
        let sw ← readEm em (nodeCss "width" svg)
        let sh ← readEm em (nodeCss "height" svg)
        let vb ← ((nodeAttr "viewBox" svg).splitOn " ").mapM String.toInt?
        match vb with
        | [x0, y0, w, h] =>
          -- The strike takes no advance and keeps its viewBox's aspect.
          if w ≤ 0 || h ≤ 0 || sw ≤ 0 || sh ≤ 0 || (ox + sw + right).natAbs > 1 ||
              (sw * h - sh * w).natAbs > w + h then none else do
            let polys ← (nodeKids svg).mapM fun poly => do
              if cancelTag poly != "polygon" || !(nodeKids poly).isEmpty then none else do
                let pts ← ((nodeAttr "points" poly).splitOn " ").mapM fun p => do
                  match p.splitOn "," with
                  | [xs, ys] =>
                    let x ← xs.toInt?
                    let y ← ys.toInt?
                    return (ox + (x - x0) * sw / w, ob + sh - (y - y0) * sh / h)
                  | _ => none
                return pts.toArray
            return {
              width, top, bot := -depth, body := (bl, by_), value := (bl + ba + vl, vy)
              polys, target, svg }
        | _ => none

/-- Six-decimal em serialization and this reader's rounding can each lose half a provider unit:
arithmetic slack, no perceptual allowance. -/
private def cancelEpsilon (em : Int) : Int := (em + 1999999) / 2000000 + 1

private def cancelNear (eps a b : Int) : Bool := (a - b).natAbs ≤ eps.toNat

/-- Source parity as a projection check: the points SVG maps against the shared geometry, after the
one common room translation. -/
private def cancelProjection (em : Int) (i : CancelIn) (room : Bool)
    (r : CancelHtmlRead) : Bool :=
  let g := Math.cancelGeom .to room i
  let pad := r.body.1 - g.shift
  let eps := 4 * cancelEpsilon em
  r.polys.size == g.polys.size &&
    (List.zip r.polys.toList g.polys.toList).all (fun (got, want) =>
      got.size == want.size &&
      (List.zip got.toList want.toList).all (fun (p, q) =>
        cancelNear eps p.1 (q.1 + pad) && cancelNear eps p.2 q.2)) &&
    cancelNear eps r.body.2 0 &&
    cancelNear eps r.value.1 (g.valueX + pad) && cancelNear eps r.value.2 g.valueY

private def cancelContained (metric : CancelMetric) (room : Bool)
    (r : CancelHtmlRead) : Bool :=
  let i := metric.input
  let eps := cancelEpsilon metric.em
  let points := r.polys.foldl (· ++ ·) #[]
  let points := points ++ #[(r.body.1, i.bot), (r.body.1 + i.w, i.top),
    (r.body.1 + metric.bodyLeft, i.bot), (r.body.1 + metric.bodyRight, i.top),
    (r.value.1 + i.vleft, r.value.2 + i.vbot),
    (r.value.1 + i.vright, r.value.2 + i.vtop),
    (r.value.1, r.value.2), (r.value.1 + i.vw, r.value.2)]
  let logical := #[r.body.1, r.body.1 + i.w, r.value.1, r.value.1 + i.vw]
  points.all (fun (_, y) => y + eps ≥ r.bot && y - eps ≤ r.top) &&
    (!room || logical.all fun x => x + eps ≥ 0 && x - eps ≤ r.width) &&
    (room || (cancelNear eps r.width i.w && cancelNear eps r.body.1 0))

/-- Room allocation never changes a cancellation target's font-size level, read off the emitted
MathML against the IR's style rule. -/
def cancelHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
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

  -- Ownership and bounded placement are separate: the triangle's clip-path proves no containment.
  let emit (mark : CancelMark) (room thick : Bool) : Html.Node :=
    MathMl.nucNode {} false .ord
      (.cancel mark { room, thick } (if mark == .to then one '7' else .nil) (one 'x'))
  let boxOf (mark : CancelMark) (n : Html.Node) : Html.Node :=
    if mark == .to then (nodeKids n).getD 0 (.text "") else n
  let ownsBands (mark : CancelMark) (node : Html.Node) : Bool :=
    let css := nodeAttr "style" (boxOf mark node)
    hasStr css "padding:" && hasStr css "background-image:" &&
      (css.splitOn "linear-gradient(").length == (if mark == .cross then 3 else 2) &&
      hasStr css (if mark == .down then "to top right" else "to top left") &&
      (mark != .cross || hasStr css "to top right")
  for mark in [CancelMark.up, .down, .cross, .to] do
    for room in [true, false] do
      for thick in [true, false] do
        let node := emit mark room thick
        let box := boxOf mark node
        let css := nodeAttr "style" box
        let label := s!"{repr mark}/room={room}/thick={thick}"
        t s!"cancel HTML: {label} padded operand owns every diagonal band"
          (ownsBands mark node)
        let misplacedBox := Html.Node.elem "mrow" #[] #[box]
        let misplaced := if mark == .to then
            Html.Node.elem "msup" #[] #[misplacedBox, (nodeKids node).getD 1 (.text "")]
          else misplacedBox
        t s!"cancel HTML: {label} band judge rejects paint owned by a descendant"
          (!ownsBands mark misplaced)
        t s!"cancel HTML: {label} room mode governs the operand's own margins"
          (hasStr css "margin-left: -" == !room &&
            hasStr css "margin-right: -" == !room)
        if mark == .to then
          let head := (nodeKids box).getD 1 (.text "")
          let value := (nodeKids node).getD 1 (.text "")
          let valueRow := if room then value else (nodeKids value).getD 0 (.text "")
          t s!"cancel HTML: {label} arrowhead belongs to the struck row"
            ((nodeKids box).size == 2 &&
              hasStr (nodeAttr "style" head) "clip-path: polygon")
          let rule := ({} : MathMl.Marks).rule * (if thick then 2 else 1)
          t s!"cancel HTML: {label} arrowhead is bounded at the upper-right corner"
            (cancelHeadPlaced rule box)
          for bad in ["left: 0", "right: 1em", "top: -1em", "width: 1em", "height: 1em",
              "offset-path: shape(from 100% 0%, line to 0% 100%)",
              "transform: translateX(-100%)"] do
            let moved := Html.Node.elem "mspace"
              #[("style", nodeAttr "style" head ++ "; " ++ bad)] #[]
            let mutated := Html.Node.elem "mrow" #[("style", css)] #[base, moved]
            t s!"cancel HTML: {label} placement judge rejects {bad}"
              (!cancelHeadPlaced rule mutated)
          t s!"cancel HTML: {label} target owns its clearance and room"
            (hasStr (nodeAttr "style" valueRow) "padding-left:" &&
              nodeAttr "width" value == (if room then "" else "0"))
      t s!"cancel HTML: {repr mark}/room={room} thicklines changes the painted band"
        (nodeAttr "style" (boxOf mark (emit mark room true)) !=
          nodeAttr "style" (boxOf mark (emit mark room false)))

  -- Invented asymmetric ink: its baseline and advance are neither its ink centre nor its edge.
  let input : CancelIn := {
    rule := 28, w := 1000, top := 710, bot := -190
    vw := 610, vleft := -35, vright := 540, vtop := 370, vbot := -120
    axis := 250, supDrop := 250, supUp := 363 }
  for em in [1000, 655360] do
    let metric : CancelMetric := { em, input, bodyLeft := -20, bodyRight := 1030 }
    for room in [false, true] do
      for st in allStyles do
        for size in [CancelSize.same, .step, .sup] do
          let spec : CancelSpec := { room, size }
          let mk : MathMl.Marks :=
            { style := st, scales := { script := 73, scriptscript := 47 }
              metric := fun s sp b v =>
                if s == st && sp == spec && b == one 'x' && v == one '7' then
                  some metric else none }
          let node := MathMl.nucNode mk (st.rank == 3) .ord
            (.cancel .to spec (one '7') (one 'x'))
          let label := s!"{em}/{repr st}/{repr size}/room={room}"
          let read := cancelRead em node
          t s!"cancel HTML measured {label}: emitted polygons and placements are readable"
            read.isSome
          if let some r := read then
            t s!"cancel HTML measured {label}: SVG mapping projects shared geometry"
              (cancelProjection em input room r)
            t s!"cancel HTML measured {label}: emitted room contains the measured reach"
              (cancelContained metric room r)
            let ts := spec.size.style st
            let relative := readEm (Math.sizeFor mk.scales 100 st)
              (nodeCss "font-size" r.target)
            t s!"cancel HTML measured {label}: target sets its size without browser rescaling"
              (nodeAttr "scriptlevel" r.target == "+0" &&
                (nodeCss "math-depth" r.target).isEmpty &&
                relative == some (Math.sizeFor mk.scales 100 ts) &&
                (elemNodesOne (· == "msup") #[] node).isEmpty)
            let a := HtmlDoc.a11yFacts false false #[node]
            t s!"cancel HTML measured {label}: native text stays visible; SVG is decorative"
              (MathMl.nodeChars #[] node == #['x', '7'] &&
                nodeAttr "aria-hidden" node != "true" &&
                nodeAttr "aria-hidden" r.target != "true" &&
                nodeAttr "aria-hidden" r.svg == "true" &&
                nodeAttr "focusable" r.svg == "false" &&
                a.svgsUnnamed == 0 && a.hiddenTabStops == 0)
            t s!"cancel HTML measured {label}: parity judge rejects a lowered target"
              (let value := cancelSetAttr "voffset"
                  (MathMl.measuredEm (r.value.2 - 200) em) (nodeKids node)[2]!
               let bad := cancelRead em (cancelSetChild 2 value node)
               bad.isSome && !(bad.any (cancelProjection em input room)))
            t s!"cancel HTML measured {label}: a stretched strike is unreadable"
              ((cancelRead em (cancelSetChild 0 (cancelSetChild 0
                (cancelSetAttr "preserveAspectRatio" "none" r.svg) (nodeKids node)[0]!)
                node)).isNone)
            t s!"cancel HTML measured {label}: bounds judge rejects clipped height"
              (let bad := cancelRead em (cancelSetAttr "height" "0" node)
               bad.isSome && !(bad.any (cancelContained metric room)))
            let moved := match ((nodeAttr "viewBox" r.svg).splitOn " ").map String.toInt? with
              | [some x, some y, some w, some h] => s!"{x + em} {y} {w} {h}"
              | _ => ""
            let svg := cancelSetAttr "viewBox" moved r.svg
            let text := cancelSetChild 0 svg (nodeKids node)[0]!
            t s!"cancel HTML measured {label}: parity judge rejects a changed SVG origin"
              (let bad := cancelRead em (cancelSetChild 0 text node)
               bad.isSome && !(bad.any (cancelProjection em input room)))

  -- Body ink past its advance overhangs as cancel.sty's box lets it; the box is the mark's advance.
  let metric : CancelMetric := {
    em := 1000, input := { input with w := 120 }, bodyLeft := -2300, bodyRight := 5100 }
  for room in [false, true] do
    let mk : MathMl.Marks := { metric := fun _ _ _ _ => some metric }
    let node := MathMl.nucNode mk false .ord
      (.cancel .to { room } (one '7') (one 'x'))
    t s!"cancel HTML body ink overhang/room={room}: the box is the shared advance"
      ((cancelRead metric.em node).any fun r =>
        cancelContained metric room r &&
          cancelNear 2 r.width (Math.cancelGeom .to room metric.input).advance)

  for mu in [-12, -3, 0, 3, 18] do
    let node := MathMl.itemNode {} false (.space mu)
    let width := readEm 1800000 (nodeAttr "width" node)
    let margin := if mu < 0 then
        readEm 1800000 (nodeCss "margin-inline-end" node)
      else some 0
    t s!"cancel HTML signed mu {mu}: emitted advance keeps sign and precision"
      (cancelTag node == "mspace" && (nodeKids node).isEmpty &&
        width.isSome && margin.isSome &&
        cancelNear 1 (width.getD 0 + margin.getD 0) (mu * 100000) &&
        (mu ≥ 0 || width == some 0))

  let spec : CancelSpec := {}
  let cn : MNucleus := .cancel .to spec (one '7') (one 'x')
  let cell : MList := .cons (.atom .ord cn .nil .nil false) .nil
  let rows : MRows := .cons (.cons cell .nil) .nil
  let accepts (st : MathStyle) : MathMl.Marks := {
    metric := fun s sp b v =>
      if s == st && sp == spec && b == one 'x' && v == one '7' then some metric else none }
  for st in allStyles do
    let contexts : List (String × MathStyle × MItem) := [
      ("sup", st.sup, .atom .ord (.sym 'z') cell .nil false),
      ("sub", st.sub, .atom .ord (.sym 'z') .nil cell false),
      ("num", st.fracNum, .atom .ord (.frac {} cell (one 'z')) .nil .nil false),
      ("den", st.fracDen, .atom .ord (.frac {} (one 'z') cell) .nil .nil false),
      ("radicand", st.cramp, .atom .ord (.rad .nil cell) .nil .nil false),
      ("degree", .scriptscript st.cramped,
        .atom .ord (.rad cell (one 'z')) .nil .nil false),
      ("accent", st.cramp, .atom .ord (.accent '^' false cell) .nil .nil false),
      ("smallmatrix", .script false, .atom .ord (.grid .small rows) .nil .nil false),
      ("align", .display false, .atom .ord (.grid .align rows) .nil .nil false),
      ("array", if st.rank == 3 then .text st.cramped else st,
        .atom .ord (.grid (.array #[.center] 1000) rows) .nil .nil false)]
    for (label, expected, item) in contexts do
      let mk := { accepts expected with style := st }
      t s!"cancel HTML style callback {repr st}/{label}: exact context and arguments"
        ((elemNodesOne (· == "svg") #[] (MathMl.itemNode mk (st.rank == 3) item)).size == 1)
    for display in [false, true] do
      let expected := if display then MathStyle.display false else .text false
      t s!"cancel HTML formula seeds {display} independently of inherited {repr st}"
        ((elemNodesOne (· == "svg") #[] (MathMl.formula display #[] cell
          { accepts expected with style := st })).size == 1)

  for em in [0, -1] do
    let mk : MathMl.Marks := { metric := fun _ _ _ _ => some { metric with em } }
    let node := MathMl.nucNode mk false .ord cn
    t s!"cancel HTML nonpositive em {em}: readable explicitly unmeasured fallback"
      (nodeAttr "data-cancel-metric" node == "unmeasured" &&
        (elemNodesOne (· == "svg") #[] node).isEmpty &&
        MathMl.nodeChars #[] node == #['x', '7'])

  let size : Dim.SymGlue := { width := { fixed := Dim.pt 24 } }
  let leading : Dim.SymGlue := { width := { fixed := Dim.pt 28 } }
  let sized := Ir.Style.fontSize (.lit size) (.lit leading)
  let role := Ir.titlePartRole 0 0
  let part : Ir.TitlePart := {
    datum := none, size := some size, leading := some leading }
  let styles : Ir.Styles := { entries := #[("titlepage", { slots := #[{ parts := #[part] }] })] }
  let formula : Ir.Inline := .formula false "" cell
  let history := #[Ir.Style.italic]
  for (name, content, expected) in
      [("styled", Ir.Inline.styled .sans #[.styled sized #[formula]], history ++ #[.sans, sized]),
       ("title role", Ir.Inline.role role #[.styled .sans #[formula]], history ++ #[sized, .sans]),
       ("ordinary role", Ir.Inline.role "test" #[formula], history)] do
    let cfg : HtmlDoc.Config := {
      styles, mathStyles := history
      cancelMetric := fun _ ss st sp b v =>
        if ss == expected then (accepts (.text false)).metric st sp b v else none }
    t s!"cancel HTML {name}: provider receives ordered ambient style history"
      ((elemNodesOne (· == "svg") #[] (HtmlDoc.blockNode cfg (.para #[content]))).size == 1)
  let font : Font := { (default : Font) with
    unitsPerEm := 1000
    math := some { (default : Font.MathConsts) with scales := { script := 73, scriptscript := 47 } } }
  let cfg : HtmlDoc.Config := {
    fonts := some { fonts := #[font], math := some 0 }
    cancelMetric := fun _ _ _ _ _ _ => some metric
    mathEm := fun _ _ _ => some metric.em }
  t "cancel HTML font MATH scales and metric callback both reach the formula"
    ((HtmlDoc.mathMarks cfg).scales == { script := 73, scriptscript := 47 } &&
      ((HtmlDoc.mathMarks cfg).metric (.text false) spec (one 'x') (one '7')).isSome &&
      (HtmlDoc.mathMarks cfg).em (.text false) == some metric.em)

  let unmeasured := MathMl.nucNode {} false .ord
    (.frac { rule := some (Dim.Length.ofBpMilli 400) } (one 'x') (one 'z'))
  t "math HTML fraction: an unmeasured rule spells its points to the thousandth"
    ((elemNodesOne (· == "mfrac") #[] unmeasured).any (nodeAttr "linethickness" · == "0.400pt"))
  -- A fraction style's browser transition is relative, so rule widths use the same measured em.
  let scales : ScriptScales := { script := 73, scriptscript := 47 }
  for ambient in allStyles do
    for chosen in allStyles do
      let em := Math.sizeFor scales (Dim.pt 19).units chosen
      let mk : MathMl.Marks := {
        style := ambient, scales
        em := fun st => some (Math.sizeFor scales (Dim.pt 19).units st) }
      for rule in [none, some 0, some (-Dim.pt 1), some (Dim.pt 8)] do
        let fraction : FracSpec := { style := some chosen, rule }
        let node := MathMl.nucNode mk (ambient.rank == 3) .ord
          (.frac fraction (one 'x') (one 'z'))
        let label := s!"{repr ambient}/{repr chosen}/{repr rule}"
        let parentSize := Math.sizeFor scales 100 ambient
        t s!"math HTML fraction {label}: parent uses the resolved style transition"
          (readEm parentSize (nodeCss "font-size" node) ==
              some (Math.sizeFor scales 100 chosen) &&
            nodeAttr "scriptlevel" node == "+0" &&
            (nodeCss "math-depth" node).isEmpty)
        let bars := elemNodesOne (· == "mfrac") #[] node
        t s!"math HTML fraction {label}: one rule scales with its measured em"
          (bars.size == 1 && bars.any fun bar =>
            match rule with
            | none => (nodeAttr "linethickness" bar).isEmpty
            | some width => (readEm em (nodeAttr "linethickness" bar)).any
                (fun actual => cancelNear (cancelEpsilon em) actual (max 0 width).units))
        t s!"math HTML fraction {label}: style and rule preserve readable operands"
          (MathMl.nodeChars #[] node == #['x', 'z'])
