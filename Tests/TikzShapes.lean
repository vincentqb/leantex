module

public import Tests.TikzLongTail

public section

open LeanTex.Core LeanTex.Cli Tests.TikzCoverage

mutual

/-- Every clipping group's clips in a figure's nodes, outermost first. -/
def nodeClipsOne {L : Type} (acc : Array (Array Gfx.Clip)) : Gfx.Node L → Array (Array Gfx.Clip)
  | .group _ cs _ kids => nodeClipsList (if cs.isEmpty then acc else acc.push cs) kids.toList
  | .draw .. | .use .. | .stamp .. | .image .. | .label _ | .words _ => acc

def nodeClipsList {L : Type} (acc : Array (Array Gfx.Clip)) : List (Gfx.Node L) → Array (Array Gfx.Clip)
  | [] => acc
  | n :: rest => nodeClipsList (nodeClipsOne acc n) rest

end

/-- The figures a page of pictures ships, each in its own frame. -/
def figsOf (oneFace : Font.FontSet) (src : String) : Array (Gfx.Figure (Nat × Nat)) :=
  (layoutOf oneFace (elabStr src).1).pages.flatMap fun p => p.inks.map (·.fig)

/-- A figure's draws, geometry and paint, in the figure's own frame. -/
def figDraws (oneFace : Font.FontSet) (src : String) :
    Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke) :=
  (figsOf oneFace src).flatMap fun f => nodeDrawsList #[] f.nodes.toList

/-- A picture's long tail draws what TikZ's keys say: shadings, clips, shapes, tips, labels, pins,
fits and braces. -/
def tikzShapeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let grid : Ir.Color := { r := 42, g := 111, b := 78 }
  let axial := picDoc "" "\\shade[left color=grid, right color=white] (0,0) rectangle (2,1);"
  t "shade: an axial shading names no loss" (lossesOf axial).isEmpty
  t "shade: pgf's stops: right colour to a quarter, mix at half, left from three quarters"
    (match (figDraws oneFace axial).toList with
     | [(_, some { paint := .gradient (.linear _ _ stops _), .. }, _)] =>
       stops.map (·.color) == #[Ir.Color.white, Ir.Color.white, Ir.Color.mix grid 50 Ir.Color.white,
         grid, grid] && stops.map (·.offset.val) == #[0, 16384, 32768, 49152, 65536]
     | _ => false)
  t "shade: the left colour on the box's left edge, the right on its right"
    (match (figDraws oneFace axial).toList with
     | [(.rect x y w h, some { paint := .gradient (.linear _ _ _ xf), .. }, _)] =>
       xf.apply (0, (Dim.bp 25).toRat) == (x.toRat, y.toRat + h.toRat / 2) &&
         xf.apply (0, -(Dim.bp 25).toRat) == (x.toRat + w.toRat, y.toRat + h.toRat / 2)
     | _ => false)
  let radial := picDoc "" "\\shade[inner color=white, outer color=grid] (0,0) circle (1);"
  t "shade: radial from the box's centre, inner to outer at half its radius"
    (match (figDraws oneFace radial).toList with
     | [(.ellipse ex ey _ _, some { paint := .gradient (.radial c0 r0 c1 r1 stops xf), .. }, _)] =>
       c0 == (0, 0) && r0 == 0 && c1 == (0, 0) && r1 == Dim.bp 50 &&
         stops.map (·.color) == #[Ir.Color.white, grid, grid] &&
         stops.map (·.offset.val) == #[0, 32768, 65536] && xf.apply (0, 0) == (ex.toRat, ey.toRat)
     | _ => false)
  let ball := picDoc "" "\\shade[ball color=grid] (0,0) circle (1);"
  t "shade: a ball's highlight starts 10 bp up-left of centre, stops mixed from its colour"
    (match (figDraws oneFace ball).toList with
     | [(_, some { paint := .gradient (.radial c0 _ _ _ stops _), .. }, _)] =>
       c0 == (-(Dim.bp 10), Dim.bp 10) &&
         stops.map (·.color) == #[Ir.Color.mix grid 15 Ir.Color.white, Ir.Color.mix grid 75 Ir.Color.white,
           Ir.Color.mix grid 70 Ir.Color.black, Ir.Color.mix grid 50 Ir.Color.black, Ir.Color.black]
     | _ => false)
  let shadedraw := picDoc "" "\\shadedraw[top color=grid] (0,0) rectangle (1,1);"
  t "shadedraw: the shading paints first and the outline strokes it"
    ((lossesOf shadedraw).isEmpty && match (figDraws oneFace shadedraw).toList with
     | [(_, some { paint := .gradient _, .. }, some _)] => true
     | _ => false)
  let clipped := picDoc "" "\\clip (0,0) rectangle (1,1);\\fill[grid] (0,0) circle (1);"
  t "clip: no loss is named" (lossesOf clipped).isEmpty
  t "clip: what follows paints inside one group the clip rectangle clips"
    (match (figsOf oneFace clipped).toList with
     | [f] => match (nodeClipsList #[] f.nodes.toList).toList with
       | [cs] => match cs.toList with
         | [{ geom := .rect _ _ w h, .. }] => w == Dim.mm 10 && h == Dim.mm 10
         | _ => false
       | _ => false
     | _ => false)
  t "clip: the picture is the clip's size, not the circle's"
    (match (figsOf oneFace clipped).toList with
     | [f] => f.box.2.1 - f.box.1.1 == Dim.mm 10 && f.box.2.2 - f.box.1.2 == Dim.mm 10
     | _ => false)
  let scopedClip := picDoc ""
    "\\begin{scope}\\clip (0,0) rectangle (1,1);\\fill (0,0) circle (1);\\end{scope}\\fill (2,0) circle (0.5);"
  t "clip: it ends with its scope: what follows the scope paints unclipped"
    ((lossesOf scopedClip).isEmpty && match (figsOf oneFace scopedClip).toList with
     | [f] => (nodeClipsList #[] f.nodes.toList).size == 1 &&
       (nodeDrawsList #[] f.nodes.toList).size == 2
     | _ => false)
  let inside := picDoc "" "\\clip (0,0) rectangle (2,2);\\node at (1,1) {a};"
  t "clip: a node inside a rectangular clip is cut by nothing, and names nothing"
    (lossesOf inside).isEmpty
  let outside := picDoc "" "\\clip (0,0) rectangle (1,1);\\node at (3,3) {a};"
  t "clip: a node the clip would cut is named"
    ((lossesOf outside).any fun d => d.code == "W0334" && hasStr (diagWords d) "clip")
  let leak := picDoc "" "{\\clip (0,0) rectangle (1,1);}\\fill (0,0) circle (1);"
  t "clip: one inside a group, which pgf carries past it, is named"
    ((lossesOf leak).any fun d => d.code == "W0334" && hasStr (diagWords d) "clip")
  let order := picDoc "" ("\\clip (0,0) rectangle (2,2);\\fill[blue] (0,0) rectangle (1,1);" ++
    "\\node at (1,1) {a};\\fill[red] (0,0) rectangle (2,2);")
  let kind : Gfx.Node (Nat × Nat) → String := fun n => match n with
    | .label _ => "label"
    | .group _ cs _ _ => if cs.isEmpty then "group" else "clip"
    | _ => "other"
  t "clip: a node between two fills stays between them on the PDF page"
    ((lossesOf order).isEmpty && match (figsOf oneFace order).toList with
     | [f] => f.nodes.toList.map kind == ["clip", "label", "clip"]
     | _ => false)
  let svgKids (src : String) : List String :=
    match elemNodesList (· == "svg") #[] (HtmlDoc.emitTree {} (elabStr src).1).2.1.toList |>.toList with
    | [.elem _ _ kids] => kids.toList.filterMap fun k => match k with
      | .elem tag _ _ => some tag
      | _ => none
    | _ => []
  t "clip: and on the web page"
    ((svgKids order).filter (· != "defs") == ["g", "text", "g"])
  let htmlOf (src : String) : Array Html.Node := (HtmlDoc.emitTree {} (elabStr src).1).2.1
  let tagged (tag : String) (body : Array Html.Node) : Array Html.Node :=
    elemNodesList (· == tag) #[] body.toList
  let attrOf (n : Html.Node) (key : String) : Option String := match n with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs key
    | _ => none
  let refsTo (body : Array Html.Node) (key id : String) : Bool :=
    (elemNodesList (fun _ => true) #[] body.toList).any fun n =>
      attrOf n key == some s!"url(#{id})"
  for (what, src, tag, stops) in [
      ("an axial shading", axial, "linearGradient", 5),
      ("a radial shading", radial, "radialGradient", 3),
      ("a ball shading", ball, "radialGradient", 5)] do
    let body := htmlOf src
    match (tagged tag body).toList with
    | [g] =>
      let id := (attrOf g "id").getD ""
      t s!"html: {what} is one {tag} with pgf's {stops} stops, in the user space it paints"
        ((tagged "stop" #[g]).size == stops && attrOf g "gradientUnits" == some "userSpaceOnUse" &&
          (attrOf g "gradientTransform").isSome)
      t s!"html: the shape {what} fills names its gradient"
        (!id.isEmpty && refsTo body "fill" id)
    | _ => t s!"html: {what} ships one {tag}" false
  let clipBody := htmlOf clipped
  match (tagged "clipPath" clipBody).toList with
  | [c] =>
    let id := (attrOf c "id").getD ""
    t "html: a clip is one clipPath in its target's user space, holding the rectangle"
      (attrOf c "clipPathUnits" == some "userSpaceOnUse" && (tagged "rect" #[c]).size == 1)
    t "html: the group the clip clips names it, and holds the clipped circle"
      (!id.isEmpty && (tagged "g" clipBody).any fun g =>
        attrOf g "clip-path" == some s!"url(#{id})" &&
          ((tagged "circle" #[g]).size + (tagged "ellipse" #[g]).size +
            (tagged "path" #[g]).size) == 1)
  | _ => t "html: a clip ships one clipPath" false
  -- An ellipse's radii are the rectangle's half extents × 1.4142136; a diamond's half diagonals their sum.
  let boxesOf (src : String) : Array (Dim.Length × Dim.Length × Dim.Length × Dim.Length) :=
    ((censusOf #[] (layoutOf oneFace (elabMeasured oneFace src).1))[0]?.map (·.pathBoxes)).getD #[]
  let rectB := boxesOf (picDoc "" "\\node[draw] at (0,0) {aa};")
  let ellB := boxesOf (picDoc "" "\\node[ellipse, draw] at (0,0) {aa};")
  let diaB := boxesOf (picDoc "" "\\node[diamond, draw] at (0,0) {aa};")
  t "ellipse and diamond: no loss is named"
    ((lossesOf (picDoc "" "\\node[ellipse, draw] at (0,0) {aa};")).isEmpty &&
      (lossesOf (picDoc "" "\\node[shape=diamond, draw] at (0,0) {aa};")).isEmpty)
  t "ellipse: its radii are the rectangle's half extents times 1.4142136"
    (match rectB[0]?, ellB[0]? with
     | some (_, _, rw, rh), some (_, _, ew, eh) =>
       near2 (ew / 2) (rw / 2 * 14142136 / 10000000) && near2 (eh / 2) (rh / 2 * 14142136 / 10000000)
     | _, _ => false)
  t "diamond: half diagonals sum the rectangle's half extents, a line-width fraction in"
    (match rectB[0]?, diaB[0]? with
     | some (_, _, rw, rh), some (_, _, dw, dh) =>
       let sum := rw / 2 + rh / 2
       let inset := Ir.Pic.thinWidth / 2 * 414213 / 1000000
       near2 (dw / 2) (sum - inset) && near2 (dh / 2) (sum - inset)
     | _, _ => false)
  let toEll := picDoc "" "\\node[ellipse, draw] (e) at (0,0) {aa};\\draw (3,2) -- (e);"
  -- The anchors stand one outer sep beyond the drawn ellipse, so the edge ends there.
  t "ellipse: an edge ends on its anchors' ellipse, not its bounding box"
    (match ((layoutOf oneFace (elabMeasured oneFace toEll).1).pages.flatMap pageDraws).toList with
     | [(.ellipse cx cy rx0 ry0, _, _), (.path subs, _, _)] =>
       match (subpathSegs subs).toList with
       | [.line _ _ ex ey] =>
         let rx := rx0 + Ir.Pic.thinWidth / 2
         let ry := ry0 + Ir.Pic.thinWidth / 2
         let dx := ex - cx
         let dy := ey - cy
         let lhs := dx * dx * ry * ry + dy * dy * rx * rx
         let rhs := rx * rx * ry * ry
         decide (lhs - rhs ≤ rhs / 1000 ∧ rhs - lhs ≤ rhs / 1000)
       | _ => false
     | _ => false)
  let stealth := picDoc "" "\\draw[-Stealth] (0,0) -- (1,0);"
  t "Stealth: no loss is named" (lossesOf stealth).isEmpty
  let perPt : Float := Float.ofInt (Dim.pt 1).units
  let lw : Float := Float.ofInt Ir.Pic.thinWidth.units / perPt
  let len := 3 + 4.5 * lw
  let wid := 0.75 * len
  let ins := 0.325 * len
  let alw := min lw ((len - ins) / 4)
  let front := alw / 2 * Float.sqrt (1 + 4 * (len / wid) * (len / wid))
  let insetMiter := alw / 2 * Float.sqrt (1 + 4 * (ins / wid) * (ins / wid))
  let sp (x : Float) : Dim.Length := .ofUnits (x * perPt).round.toInt64.toInt
  t "Stealth: a closed, filled, stroked dart, its front a miter short of the end"
    (match (drawsOf oneFace stealth).toList with
     | [(.path shaft, none, some _), (.path #[dart], some _, some _)] =>
       match (subpathSegs shaft).toList with
       | [.line x0 _ x1 _] =>
         let tipEnd := x0 + Dim.mm 10
         dart.closed && dart.segs.size == 3 && decide ((dart.start.1 - (tipEnd - sp front)).abs ≤ 3 * Dim.Length.quantum) &&
           decide ((x1 - (tipEnd - sp len + sp (ins + insetMiter - alw / 4))).abs ≤
             3 * Dim.Length.quantum)
       | _ => false
     | _ => false)
  let linesOf (src : String) : Array CensusLine :=
    ((censusOf #[] (layoutOf oneFace (elabMeasured oneFace src).1))[0]?.map (·.lines)).getD #[]
  let lineOf (src s : String) : Option CensusLine := (linesOf src).find? (·.text.trimAscii.toString == s)
  let above := picDoc "" "\\node[draw, label=above:x] at (0,0) {b};"
  t "label: no loss is named" (lossesOf above).isEmpty
  t "label: above its node, centred on it"
    (match lineOf above "x", lineOf above "b" with
     | some x, some b => x.y < b.y && near2 (x.x + x.width / 2) (b.x + b.width / 2)
     | _, _ => false)
  let right := picDoc "" "\\node[draw, label=right:x] at (0,0) {b};"
  t "label: right of its node, past its border"
    (match lineOf right "x", lineOf right "b" with
     | some x, some b => decide (b.x + b.width < x.x)
     | _, _ => false)
  let pin := picDoc "" "\\node[draw, pin=above:x] at (0,0) {b};"
  t "pin: farther above its node than a label, joined to it by a help line"
    (match lineOf pin "x", lineOf pin "b", lineOf above "x", lineOf above "b" with
     | some p, some pb, some l, some lb => lb.y - l.y < pb.y - p.y &&
       ((censusOf #[] (layoutOf oneFace (elabMeasured oneFace pin).1))[0]?.map fun pg =>
         pg.pathStrokes.any (· == ({ r := 128, g := 128, b := 128 }, Dim.pt 2 / 10))).getD false
     | _, _, _, _ => false)
  let coordLabel := picDoc "" "\\coordinate[label=below:x] (c) at (0,0);\\draw (c) -- (1,0);"
  t "label: a coordinate's label stands below its point by the angle's sector"
    ((lossesOf coordLabel).isEmpty && (lineOf coordLabel "x").isSome)
  let fit := picDoc "" "\\node (a) at (0,0) {a};\\node (b) at (2,1) {b};\\node[draw, fit=(a) (b)] {};"
  t "fit: no loss is named" (lossesOf fit).isEmpty
  t "fit: its frame covers both nodes' letters, one inner sep and more out"
    (match boxesOf fit, lineOf fit "a", lineOf fit "b" with
     | #[(fx, fy, fw, fh)], some a, some b =>
       fx < a.x && a.x + a.width < fx + fw && fx < b.x && b.x + b.width < fx + fw &&
         fy < b.y && a.y < fy + fh
     | _, _, _ => false)
  let brace := picDoc "" "\\draw[decorate, decoration={brace, amplitude=4pt}] (0,0) -- (2,0);"
  t "brace: no loss is named" (lossesOf brace).isEmpty
  t "brace: two lines and four curves, its tip the amplitude up at the middle"
    (match (strokedSegs oneFace brace).toList with
     | [segs] => match segs.toList with
       | [.cubic x0 y0 _ _ _ _ _ _, .line .., .cubic _ _ _ _ _ _ tx ty, .cubic .., .line .., .cubic _ _ _ _ _ _ x1 y1] =>
         near2 tx ((x0 + x1) / 2) && near2 (y0 - ty) (Dim.pt 4) && y1 == y0
       | _ => false
     | _ => false)
  let mirrored := picDoc "" "\\draw[decorate, decoration={brace, mirror}] (0,0) -- (2,0);"
  t "brace: mirrored, its tip points the other way"
    (match (strokedSegs oneFace mirrored).toList with
     | [segs] => match segs.toList with
       | [.cubic _ y0 _ _ _ _ _ _, _, .cubic _ _ _ _ _ _ _ ty, _, _, _] => decide (ty > y0)
       | _ => false
     | _ => false)
  -- A translucent fill composites over what it covers, so it is no opaque ground.
  let q (n : Int) : Dim.Length := n * Dim.Length.quantum
  let blue : Ir.Color := { r := 0, g := 0, b := 255 }
  let wash : Ir.Pic.Shape := .ink (.draw (.rect 0 0 (q 100) (q 100))
    (some { paint := .solid blue, rule := .nonzero, alpha := ⟨200, by decide⟩ }) none)
  let solid : Ir.Pic.Shape := .ink (.draw (.rect 0 0 (q 100) (q 100)) (some (Ir.Pic.solidFill blue)) none)
  t "ground: a translucent fill blends over the picture's ground"
    (Ir.Pic.fillUnder (some Ir.Color.white) #[wash] (q 50) (q 50) == some { r := 204, g := 204, b := 255 })
  t "ground: an opaque fill is its own colour, over a translucent one too"
    (Ir.Pic.fillUnder (some Ir.Color.white) #[solid] (q 50) (q 50) == some blue &&
      Ir.Pic.fillUnder (some Ir.Color.white) #[wash, solid] (q 50) (q 50) == some blue)
  t "ground: a fill that misses the anchor leaves the picture's ground"
    (Ir.Pic.fillUnder (some Ir.Color.white) #[wash] (q 500) (q 50) == some Ir.Color.white)
  t "ground: a translucent fill over a ground the walk cannot name names none"
    (Ir.Pic.fillUnder none #[wash] (q 50) (q 50) == none)
  let faded : Ir.Pic.Shape := .ink (.group Gfx.Affine.unit #[] ⟨500, by decide⟩
    #[.draw (.rect 0 0 (q 100) (q 100)) (some (Ir.Pic.solidFill blue)) none])
  t "ground: a group faded to half its kids paints them half over the ground"
    (Ir.Pic.fillUnder (some Ir.Color.white) #[faded] (q 50) (q 50) == some { r := 128, g := 128, b := 255 })
