module

public import LeanTex.Core.Ir
public import LeanTex.Core.GfxAffine

/-!
# A TikZ picture as a figure

The elaborator evaluates a picture into concrete `Ir.Pic.Shape`s; this is
their lowering onto the vector model, which both backends then emit. A shape
is one top-level node, so a label's node index is its shape index: a fill
is a draw, a node outline a draw, an edge a group of its stroked path and its
tip, a label an engine-set label. Continuous edge segments share one subpath
— the PDF already merged them, and the SVG now draws the same joins.
-/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

/-- A picture label as the shape carried it: its anchor, content, colour,
per-mille size and alignment. Engine-set: the backends' label emitters set
it, the model only places it. -/
public structure LabelSpec where
  x : Sp
  y : Sp
  content : Array Ir.Inline
  color : Ir.Color
  scale : Nat
  align : Ir.Pic.LabelAlign
  deriving Repr, Inhabited

/-- A solid opaque fill under the nonzero rule: every TikZ fill. -/
@[expose] public def solidFill (c : Ir.Color) : Fill :=
  { paint := .solid c, rule := .nonzero, alpha := Alpha.opaque }

/-- pgf's miter limit, PDF's initial value (pgf manual §15.3.1: pgf leaves
the limit at the PDF default of 10). -/
@[expose] public def pgfMiterLimit : Rat := 10

/-- A picture stroke in the model: pgf's butt caps, miter joins and miter
limit, its declared colour and width, and its dash rhythm — pgf manual
§15.3.2: `dashed` is on 3 pt off 3 pt, `dotted` on the line width off 1 pt
(the `densely dotted` rhythm the subset keeps). -/
@[expose] public def strokeOf (k : Ir.Pic.Stroke) : Stroke :=
  { paint := .solid k.color, width := k.width, cap := .butt, join := .miter
    miterLimit := pgfMiterLimit
    dash := match k.dash with
      | .solid => #[]
      | .dashed => #[Dim.pt 3, Dim.pt 3]
      | .dotted => #[k.width, Dim.pt 1]
    phase := 0, alpha := Alpha.opaque }

/-- An edge's segments as subpaths: a segment that starts where the last
ended continues its subpath, any other opens a new one. -/
@[expose] public def edgeSubpaths (segs : Array Ir.Pic.PathSeg) : Array Subpath :=
  let step (acc : Array Subpath) (sg : Ir.Pic.PathSeg) : Array Subpath :=
    let (start, seg) : Pt × Seg := match sg with
      | .line x1 y1 x2 y2 => ((x1, y1), .line (x2, y2))
      | .cubic x1 y1 c1x c1y c2x c2y x2 y2 => ((x1, y1), .cubic (c1x, c1y) (c2x, c2y) (x2, y2))
    match acc.back? with
    | some cur =>
      if cur.endPt == start then acc.pop.push { cur with segs := cur.segs.push seg }
      else acc.push { start := start, segs := #[seg], closed := false }
    | none => acc.push { start := start, segs := #[seg], closed := false }
  segs.foldl step #[]

/-- An arrow tip's triangle, closed. -/
@[expose] public def tipSubpath (t : Ir.Pic.Tip) : Subpath :=
  { start := (t.x1, t.y1), segs := #[.line (t.x2, t.y2), .line (t.x3, t.y3)], closed := true }

/-- One shape as one node. -/
@[expose] public def ofShape : Ir.Pic.Shape → Node LabelSpec
  | .rect x y w h c =>
    .draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h))) (some (solidFill c)) none
  | .label x y content color scale align =>
    .label { x := x, y := y, content := content, color := color, scale := scale, align := align }
  | .circle x y r st fl =>
    .draw (.ellipse x y (max r (-r)) (max r (-r))) (fl.map solidFill) (st.map strokeOf)
  | .frame x y w h st fl =>
    .draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h)))
      (fl.map solidFill) (st.map strokeOf)
  | .edge segs st tip =>
    .group Affine.unit #[] Alpha.opaque
      (#[.draw (.path (edgeSubpaths segs)) none (some (strokeOf st))] ++
        match tip with
        | some t => #[.draw (.path #[tipSubpath t]) (some (solidFill st.color)) none]
        | none => #[])

/-- A picture as a figure in a box its caller already measured. -/
@[expose] public def ofPictureIn (box : Box) (pic : Ir.Pic.Picture) : Figure LabelSpec :=
  { box := box, clipToBox := false, nodes := pic.shapes.map ofShape
    outlines := #[], symbols := #[], rasters := #[], title := none, losses := #[] }

/-- **A picture as a figure**: its shapes as nodes in source order, its box
the IR's one box under the measurement (`Ir.Pic.Picture.box`) — so no
picture moves — never clipping (pgf §15.8). -/
@[expose] public def ofPicture (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) : Figure LabelSpec :=
  ofPictureIn (pic.box m) pic

/-- The figure reserves exactly the picture's box (`_exact`). -/
public theorem ofPicture_box_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) :
    (ofPicture m pic).box = pic.box m := rfl

/-- **A shape is a node** (`_exact`): node `i` of the figure is shape `i`
lowered, so a label's node index is its shape index. -/
public theorem ofPicture_nodes_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) (i : Nat) :
    (ofPicture m pic).nodes[i]? = pic.shapes[i]?.map ofShape := by
  simp [ofPicture, ofPictureIn]

/-- The label a shape carries, if it is one. -/
@[expose] public def labelOf? : Ir.Pic.Shape → Option LabelSpec
  | .label x y content color scale align =>
    some { x := x, y := y, content := content, color := color, scale := scale, align := align }
  | .rect _ _ _ _ _ => none
  | .circle _ _ _ _ _ => none
  | .frame _ _ _ _ _ _ => none
  | .edge _ _ _ => none

/-- The label a node carries at its top level, if it is one. -/
@[expose] public def Node.label? {L : Type} : Node L → Option L
  | .label l => some l
  | .draw _ _ _ => none
  | .group _ _ _ _ => none
  | .use _ _ => none
  | .stamp _ _ _ _ => none
  | .image _ _ => none
  | .words _ => none

/-- **The figure carries exactly the picture's labels** (`_exact`): every
node's label is its shape's, in shape order, and only labels are labels. -/
public theorem ofPicture_labels_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) :
    (ofPicture m pic).nodes.map Node.label? = pic.shapes.map labelOf? := by
  simp only [ofPicture, ofPictureIn, Array.map_map]
  apply Array.map_congr_left
  intro s _
  cases s with
  | rect => rfl
  | label => rfl
  | circle => rfl
  | frame => rfl
  | edge segs st tip => cases tip <;> rfl

private theorem imageFreeList_append {L : Type} (a b : List (Node L)) :
    Node.imageFreeList (a ++ b) = (Node.imageFreeList a && Node.imageFreeList b) := by
  induction a with
  | nil => simp [Node.imageFreeList]
  | cons n rest ih => simp [Node.imageFreeList, ih, Bool.and_assoc]

private theorem ofShape_imageFree (s : Ir.Pic.Shape) : (ofShape s).imageFree = true := by
  cases s with
  | rect => rfl
  | label => rfl
  | circle => rfl
  | frame => rfl
  | edge segs st tip => cases tip <;> rfl

mutual

private theorem dropLabelsOne_imageFree {L : Type} (acc : Array (Node Empty))
    (hacc : Node.imageFreeList acc.toList = true) :
    ∀ n : Node L, n.imageFree = true →
      Node.imageFreeList (Node.dropLabelsOne acc n).toList = true
  | .draw g fl st, _ => by
    simp [Node.dropLabelsOne, imageFreeList_append, hacc, Node.imageFree, Node.imageFreeList]
  | .group xf clips alpha kids, h => by
    simp only [Node.imageFree] at h
    have := dropLabelsList_imageFree #[] (by rfl) kids.toList h
    simp [Node.dropLabelsOne, imageFreeList_append, hacc, Node.imageFree, Node.imageFreeList,
      this]
  | .use k xf, _ => by
    simp [Node.dropLabelsOne, imageFreeList_append, hacc, Node.imageFree, Node.imageFreeList]
  | .stamp o xf fl st, _ => by
    simp [Node.dropLabelsOne, imageFreeList_append, hacc, Node.imageFree, Node.imageFreeList]
  | .image _ _, h => by simp [Node.imageFree] at h
  | .label _, _ => by simpa [Node.dropLabelsOne] using hacc
  | .words w, _ => by
    simp [Node.dropLabelsOne, imageFreeList_append, hacc, Node.imageFree, Node.imageFreeList]

private theorem dropLabelsList_imageFree {L : Type} (acc : Array (Node Empty))
    (hacc : Node.imageFreeList acc.toList = true) :
    ∀ xs : List (Node L), Node.imageFreeList xs = true →
      Node.imageFreeList (Node.dropLabelsList acc xs).toList = true
  | [], _ => by simpa [Node.dropLabelsList] using hacc
  | n :: rest, h => by
    simp only [Node.imageFreeList, Bool.and_eq_true] at h
    simp only [Node.dropLabelsList]
    exact dropLabelsList_imageFree _ (dropLabelsOne_imageFree acc hacc n h.1) rest h.2

end

private theorem imageFreeList_map (xs : List Ir.Pic.Shape) :
    Node.imageFreeList (xs.map ofShape) = true := by
  induction xs with
  | nil => rfl
  | cons s rest ih => simp [Node.imageFreeList, ofShape_imageFree, ih]

/-- **A picture's ink paints no raster** (`_exact`): every node the
lowering makes, its labels taken out, is a draw or a group of draws — so a
page's ink never asks the PDF writer for an image it has no table for. -/
public theorem ofPictureIn_imageFree_exact (box : Box) (pic : Ir.Pic.Picture) :
    (ofPictureIn box pic).dropLabels.imageFree = true := by
  have h := dropLabelsList_imageFree #[] rfl _ (imageFreeList_map pic.shapes.toList)
  simp [Figure.imageFree, Figure.dropLabels, ofPictureIn, h]

/-- A label repainted. -/
@[expose] public def LabelSpec.recolor (f : Ir.Color → Ir.Color) (l : LabelSpec) : LabelSpec :=
  { l with color := f l.color }

private theorem strokeOf_recolor (f : Ir.Color → Ir.Color) (k : Ir.Pic.Stroke) :
    strokeOf { k with color := f k.color } = (strokeOf k).recolor f := by
  cases k with
  | mk c w d => cases d <;> rfl

private theorem ofShape_recolor (f : Ir.Color → Ir.Color) (s : Ir.Pic.Shape) :
    ofShape (s.recolor f) = Node.recolorOne f (LabelSpec.recolor f) (ofShape s) := by
  cases s with
  | rect x y w h c => rfl
  | label x y content color scale align => rfl
  | circle x y r st fl =>
    cases st <;> cases fl <;>
      simp [ofShape, Ir.Pic.Shape.recolor, Node.recolorOne, strokeOf_recolor, Fill.recolor,
        solidFill, Paint.recolor]
  | frame x y w h st fl =>
    cases st <;> cases fl <;>
      simp [ofShape, Ir.Pic.Shape.recolor, Node.recolorOne, strokeOf_recolor, Fill.recolor,
        solidFill, Paint.recolor]
  | edge segs st tip =>
    cases tip <;>
      simp [ofShape, Ir.Pic.Shape.recolor, Node.recolorOne, Node.recolorList,
        strokeOf_recolor, Fill.recolor, solidFill, Paint.recolor]

private theorem recolorList_map (f : Ir.Color → Ir.Color) (fl : LabelSpec → LabelSpec)
    (acc : Array (Node LabelSpec)) (xs : List (Node LabelSpec)) :
    Node.recolorList f fl acc xs = acc ++ (xs.map (Node.recolorOne f fl)).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.recolorList]
  | cons x rest ih => simp [Node.recolorList, ih]

/-- **Lowering commutes with repainting** (`_exact`): dimming a picture
under an overlay cover and lowering it is lowering it and dimming the
figure, labels included. -/
public theorem ofPicture_recolor_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture)
    (f : Ir.Color → Ir.Color) :
    ofPicture m (pic.recolor f) = (ofPicture m pic).recolor f (LabelSpec.recolor f) := by
  have hb := Ir.Pic.Picture.recolor_box_id pic f m
  simp only [ofPicture, ofPictureIn, Figure.recolor, recolorList_map, Array.map_empty,
    Array.empty_append]
  rw [hb]
  simp only [Figure.mk.injEq, true_and, and_true]
  apply Array.ext'
  simp only [Ir.Pic.Picture.recolor, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro s _
  exact ofShape_recolor f s

end LeanTex.Core.Gfx
