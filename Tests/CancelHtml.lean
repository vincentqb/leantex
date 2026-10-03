import Tests.Support

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

/-- The own CSS declaration, rather than a substring that may name a
property on a different element. -/
private def cancelCss (key : String) (node : Html.Node) : String :=
  let decls := (cancelAttr "style" node).splitOn ";"
  let fields := decls.map fun decl =>
    let parts := decl.splitOn ":"
    (parts.headD "" |>.trimAscii.toString,
      String.intercalate ":" parts.tail |>.trimAscii.toString)
  (fields.reverse.find? (·.1 == key)).map (·.2) |>.getD ""

/-- A corner triangle's whole containing rectangle lies in the operand:
right/top anchors and percentage caps govern both axes, and every polygon
coordinate lies inside that rectangle. A motion path or transform would
invalidate this argument, even if the other declarations still appeared.
The browser raster oracle independently checks the platform's paint. -/
private def cancelHeadPlaced (rule : Nat) (box : Html.Node) : Bool :=
  let head := (cancelKids box).back?.getD (.text "")
  let css := cancelAttr "style" head
  let size := s!"min({MathMl.milliEm (4 * rule)}, 100%)"
  cancelCss "position" box == "relative" &&
    cancelCss "position" head == "absolute" &&
    cancelCss "right" head == "0" && cancelCss "top" head == "0" &&
    (cancelCss "left" head).isEmpty &&
    cancelCss "width" head == size && cancelCss "height" head == size &&
    cancelCss "clip-path" head == "polygon(0 50%, 100% 0, 50% 100%)" &&
    !cancelHasStr css "offset-" && !cancelHasStr css "transform" &&
    (cancelKids head).isEmpty

/-- Read a CSS length back into the provider's units, rounding only after
parsing the file's decimal. Unitless zero is legal; missing or foreign
units are not a measurement. -/
private def cancelReadEm (em : Int) (s : String) : Option Int := do
  if s == "0" then return 0
  if !s.endsWith "em" then none else do
    let (n, d) ← Decl.parseDecimal (s.dropEnd 2).toString
    return (n * em + (d : Int) / 2) / d

/-- CSS margins carry signed offsets; MathML lspace itself must be
nonnegative, and the balancing margin keeps the attachment advance zero. -/
private def cancelReadOffset (em : Int) (node : Html.Node) : Option Int := do
  let space ← cancelReadEm em (cancelAttr "lspace" node)
  let left ← cancelReadEm em (cancelCss "margin-left" node)
  let right ← cancelReadEm em (cancelCss "margin-right" node)
  if space < 0 || left + right != 0 then none else some (space + left)

private def cancelTag : Html.Node → String
  | .elem tag _ _ => tag
  | _ => ""

/-- Mutations change the emitted artifact before its coordinates are read,
so they exercise the parser and judge together. -/
private def cancelSetAttr (key value : String) : Html.Node → Html.Node
  | .elem tag attrs kids => .elem tag ((attrs.filter (·.1 != key)).push (key, value)) kids
  | other => other

private def cancelSetChild (i : Nat) (child : Html.Node) : Html.Node → Html.Node
  | .elem tag attrs kids => .elem tag attrs (kids.set! i child)
  | other => other

/-- Coordinates read from the emitted SVG viewport and the actual native
MathML placement boxes. The SVG's downward y is mapped to the parent
baseline; changing a viewBox, viewport, or offset changes this reading. -/
private structure CancelHtmlRead where
  width : Int
  top : Int
  bot : Int
  body : Int × Int
  value : Int × Int
  polys : Array (Array (Int × Int))
  target : Html.Node
  svg : Html.Node

private def cancelRead (em : Int) (node : Html.Node) : Option CancelHtmlRead := do
  if cancelTag node != "mpadded" || !(cancelCss "position" node).isEmpty then none else do
    let boxWidth ← cancelReadEm em (cancelAttr "width" node)
    let margin ← if (cancelCss "margin-inline-end" node).isEmpty then some 0
      else cancelReadEm em (cancelCss "margin-inline-end" node)
    let width := boxWidth + margin
    let top ← cancelReadEm em (cancelAttr "height" node)
    let depth ← cancelReadEm em (cancelAttr "depth" node)
    let b ← (cancelKids node)[0]?
    let v ← (cancelKids node)[1]?
    if cancelTag b != "mpadded" || cancelTag v != "mpadded" ||
        (MathMl.nodeChars #[] b) != #['x'] ||
        (MathMl.nodeChars #[] v) != #['7'] then none else do
      if [b, v].any (fun n => cancelAttr "width" n != "0" ||
          cancelAttr "height" n != "0" || cancelAttr "depth" n != "0") then none else do
        let bx ← cancelReadOffset em b
        let by_ ← cancelReadEm em (cancelAttr "voffset" b)
        let vx ← cancelReadOffset em v
        let vy ← cancelReadEm em (cancelAttr "voffset" v)
        let target ← (cancelKids v)[0]?
        let overlay ← (cancelKids node)[2]?
        let text ← (cancelKids overlay)[0]?
        let svg ← (cancelKids text)[0]?
        if cancelTag overlay != "mpadded" || cancelTag text != "mtext" ||
            cancelTag svg != "svg" || cancelAttr "width" overlay != "0" ||
            cancelAttr "height" overlay != "0" || cancelAttr "depth" overlay != "0" ||
            !(cancelCss "position" svg).isEmpty || !(cancelCss "left" svg).isEmpty ||
            !(cancelCss "top" svg).isEmpty || cancelCss "vertical-align" svg != "baseline" ||
            cancelCss "overflow" svg != "visible" ||
            cancelAttr "preserveAspectRatio" svg != "none" then none else do
          let ox ← cancelReadOffset em overlay
          let oy ← cancelReadEm em (cancelAttr "voffset" overlay)
          let sw ← cancelReadEm em (cancelCss "width" svg)
          let sh ← cancelReadEm em (cancelCss "height" svg)
          let vb ← ((cancelAttr "viewBox" svg).splitOn " ").mapM String.toInt?
          match vb with
          | [x0, y0, w, h] =>
            if w ≤ 0 || h ≤ 0 || sw ≤ 0 || sh ≤ 0 then none else do
              let polys ← (cancelKids svg).mapM fun poly => do
                if cancelTag poly != "polygon" || !(cancelKids poly).isEmpty then none else do
                  let pts ← ((cancelAttr "points" poly).splitOn " ").mapM fun p => do
                    match p.splitOn "," with
                    | [xs, ys] =>
                      let x ← xs.toInt?
                      let y ← ys.toInt?
                      return (ox + (x - x0) * sw / w,
                        oy + sh - (y - y0) * sh / h)
                    | _ => none
                  return pts.toArray
              return {
                width, top, bot := -depth, body := (bx, by_), value := (vx, vy)
                polys, target, svg }
          | _ => none

/-- Six decimal em serialization and this reader's nearest-unit rounding
can each lose half a provider unit. This is arithmetic slack, not a
perceptual alignment allowance. -/
private def cancelEpsilon (em : Int) : Int := (em + 1999999) / 2000000 + 1

private def cancelNear (eps a b : Int) : Bool := (a - b).natAbs ≤ eps.toNat

/-- Source parity is a projection check: compare the points actually
mapped by SVG with the shared geometry, after the one common room
translation read from the operand. It does not certify the geometry
formula; the independent ray and containment checks below judge that
projection's attachment and bounds. -/
private def cancelProjection (em : Int) (i : CancelIn) (room : Bool)
    (r : CancelHtmlRead) : Bool :=
  let g := Math.cancelGeom .to room i
  let pad := r.body.1 - g.shift
  let eps := cancelEpsilon em
  r.polys.size == g.polys.size &&
    (List.zip r.polys.toList g.polys.toList).all (fun (got, want) =>
      got.size == want.size &&
      (List.zip got.toList want.toList).all (fun (p, q) =>
        cancelNear eps p.1 (q.1 + pad) && cancelNear eps p.2 q.2)) &&
    cancelNear eps r.body.2 0 &&
    cancelNear eps r.value.1 (g.valueX + pad) && cancelNear eps r.value.2 g.valueY

private def cancelRay (em : Int) (i : CancelIn) (r : CancelHtmlRead) : Bool := Id.run do
  let some shaft := r.polys[0]? | return false
  let some head := r.polys.back? | return false
  let some tail := shaft[0]? | return false
  let some tip := head[0]? | return false
  let dx := tip.1 - tail.1
  let dy := tip.2 - tail.2
  let cx := 2 * r.value.1 + i.vleft + i.vright - 2 * tip.1
  let cy := 2 * r.value.2 + i.vbot + i.vtop - 2 * tip.2
  let eps := cancelEpsilon em
  -- The direction and centre both contain serialized coordinates. Bound
  -- their propagated cross-product error rather than choosing a slope band.
  let bound := max dx dy + eps *
    (4 * (dx.natAbs + dy.natAbs : Nat) + 2 * (cx.natAbs + cy.natAbs : Nat))
  return head.size == 3 && dx > 0 && dy > 0 &&
    (dx * cy - dy * cx).natAbs ≤ bound.toNat &&
    dx * cx + dy * cy > 0 &&
    (r.value.1 + i.vleft + 2 * eps ≥ tip.1 + i.gap ||
      r.value.2 + i.vbot + 2 * eps ≥ tip.2 + i.gap)

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
  points.all (fun (x, y) =>
    y + eps ≥ r.bot && y - eps ≤ r.top &&
      (!room || (x + eps ≥ 0 && x - eps ≤ r.width))) &&
    (room || (cancelNear eps r.width i.w && cancelNear eps r.body.1 0))

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

  -- Ownership and bounded placement are separate facts: the triangle's
  -- own clip-path alone does not establish containment in the operand.
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
          let rule := ({} : MathMl.Marks).rule * (if thick then 2 else 1)
          t s!"cancel HTML: {label} arrowhead is bounded at the upper-right corner"
            (cancelHeadPlaced rule box)
          for bad in ["left: 0", "right: 1em", "top: -1em", "width: 1em", "height: 1em",
              "offset-path: shape(from 100% 0%, line to 0% 100%)",
              "transform: translateX(-100%)"] do
            let moved := Html.Node.elem "mspace"
              #[("style", cancelAttr "style" head ++ "; " ++ bad)] #[]
            let mutated := Html.Node.elem "mrow" #[("style", css)] #[base, moved]
            t s!"cancel HTML: {label} placement judge rejects {bad}"
              (!cancelHeadPlaced rule mutated)
          t s!"cancel HTML: {label} target owns its clearance and room"
            (cancelHasStr (cancelAttr "style" valueRow) "padding-left:" &&
              cancelAttr "width" value == (if room then "" else "0"))
      t s!"cancel HTML: {repr mark}/room={room} thicklines changes the painted band"
        (cancelAttr "style" (boxOf mark (emit mark room true)) !=
          cancelAttr "style" (boxOf mark (emit mark room false)))

  -- Invented, asymmetric target ink: its baseline and advance are neither
  -- its ink centre nor its near edge. The callback is synthetic; the
  -- separate shared-provider checks establish what real font ink supplies.
  let input : CancelIn := {
    rule := 28, gap := 85, w := 1000, top := 710, bot := -190
    vw := 610, vleft := -35, vright := 540, vtop := 370, vbot := -120, space := 45 }
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
            t s!"cancel HTML measured {label}: target ink centre follows the emitted ray"
              (cancelRay em input r)
            t s!"cancel HTML measured {label}: emitted room contains the measured reach"
              (cancelContained metric room r)
            let ts := spec.size.style st
            let relative := cancelReadEm (Math.sizeFor mk.scales 100 st)
              (cancelCss "font-size" r.target)
            t s!"cancel HTML measured {label}: target sets its size without browser rescaling"
              (cancelAttr "scriptlevel" r.target == "+0" &&
                (cancelCss "math-depth" r.target).isEmpty &&
                relative == some (Math.sizeFor mk.scales 100 ts) &&
                (elemNodesOne (· == "msup") #[] node).isEmpty)
            let a := HtmlDoc.a11yFacts false false #[node]
            t s!"cancel HTML measured {label}: native text stays visible; SVG is decorative"
              (MathMl.nodeChars #[] node == #['x', '7'] &&
                cancelAttr "aria-hidden" node != "true" &&
                cancelAttr "aria-hidden" r.target != "true" &&
                cancelAttr "aria-hidden" r.svg == "true" &&
                cancelAttr "focusable" r.svg == "false" &&
                a.svgsUnnamed == 0 && a.hiddenTabStops == 0)
            t s!"cancel HTML measured {label}: ray judge rejects a lowered target"
              (let value := cancelSetAttr "voffset"
                  (MathMl.measuredEm (r.value.2 - 200) em) (cancelKids node)[1]!
               let bad := cancelRead em (cancelSetChild 1 value node)
               bad.isSome && !(bad.any (cancelRay em input)))
            t s!"cancel HTML measured {label}: bounds judge rejects clipped height"
              (let bad := cancelRead em (cancelSetAttr "height" "0" node)
               bad.isSome && !(bad.any (cancelContained metric room)))
            let svg := cancelSetAttr "viewBox" s!"0 0 {em} {em}" r.svg
            let overlay := (cancelKids node)[2]!
            let text := (cancelKids overlay)[0]!
            let overlay := cancelSetChild 0 (cancelSetChild 0 svg text) overlay
            t s!"cancel HTML measured {label}: parity judge rejects a changed SVG origin"
              (let bad := cancelRead em (cancelSetChild 2 overlay node)
               bad.isSome && !(bad.any (cancelProjection em input room)))

  -- Trailing negative mu can leave the operand's advance far inside its
  -- visible glyph hull. Both its left overhang and right ink must reserve
  -- room, even when the arrow and value fit well inside that hull.
  let metric : CancelMetric := {
    em := 1000, input := { input with w := 120 }, bodyLeft := -2300, bodyRight := 5100 }
  for room in [false, true] do
    let mk : MathMl.Marks := { metric := fun _ _ _ _ => some metric }
    let node := MathMl.nucNode mk false .ord
      (.cancel .to { room } (one '7') (one 'x'))
    t s!"cancel HTML body ink overhang/room={room}: measured hull is reserved"
      ((cancelRead metric.em node).any fun r =>
        cancelContained metric room r &&
          (!room || (cancelNear 2 (r.body.1 + metric.bodyLeft) 0 &&
            cancelNear 2 r.width (metric.bodyRight - metric.bodyLeft))))

  for mu in [-12, -3, 0, 3, 18] do
    let node := MathMl.itemNode {} false (.space mu)
    let width := cancelReadEm 1800000 (cancelAttr "width" node)
    let margin := if mu < 0 then
        cancelReadEm 1800000 (cancelCss "margin-inline-end" node)
      else some 0
    t s!"cancel HTML signed mu {mu}: emitted advance keeps sign and precision"
      (cancelTag node == "mspace" && (cancelKids node).isEmpty &&
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
      (cancelAttr "data-cancel-metric" node == "unmeasured" &&
        (elemNodesOne (· == "svg") #[] node).isEmpty &&
        MathMl.nodeChars #[] node == #['x', '7'])

  let size : Dim.SymGlue := { width := { sp := 24 * 65536 } }
  let leading : Dim.SymGlue := { width := { sp := 28 * 65536 } }
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
  let font : Font.Font := { (default : Font.Font) with
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

  -- Explicit fraction styles are absolute in the IR, but their browser
  -- transition is relative to the surrounding style. Physical rule widths
  -- must use that same measured em so responsive pages scale them together.
  let scales : ScriptScales := { script := 73, scriptscript := 47 }
  for ambient in allStyles do
    for chosen in allStyles do
      let em := Math.sizeFor scales (19 * 65536) chosen
      let mk : MathMl.Marks := {
        style := ambient, scales
        em := fun st => some (Math.sizeFor scales (19 * 65536) st) }
      for rule in [none, some 0, some (-65536), some (8 * 65536)] do
        let fraction : FracSpec := { style := some chosen, rule }
        let node := MathMl.nucNode mk (ambient.rank == 3) .ord
          (.frac fraction (one 'x') (one 'z'))
        let label := s!"{repr ambient}/{repr chosen}/{repr rule}"
        let parentSize := Math.sizeFor scales 100 ambient
        t s!"math HTML fraction {label}: parent uses the resolved style transition"
          (cancelReadEm parentSize (cancelCss "font-size" node) ==
              some (Math.sizeFor scales 100 chosen) &&
            cancelAttr "scriptlevel" node == "+0" &&
            (cancelCss "math-depth" node).isEmpty)
        let bars := elemNodesOne (· == "mfrac") #[] node
        t s!"math HTML fraction {label}: one rule scales with its measured em"
          (bars.size == 1 && bars.any fun bar =>
            match rule with
            | none => (cancelAttr "linethickness" bar).isEmpty
            | some width => (cancelReadEm em (cancelAttr "linethickness" bar)).any
                (fun actual => cancelNear (cancelEpsilon em) actual (max 0 width)))
        t s!"math HTML fraction {label}: style and rule preserve readable operands"
          (MathMl.nodeChars #[] node == #['x', 'z'])
