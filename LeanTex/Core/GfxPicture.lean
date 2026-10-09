module

public import LeanTex.Core.Ir
public import LeanTex.Core.GfxAffine

/-!
# A TikZ picture as a figure

The elaborator evaluates a picture into `Ir.Pic.Shape`s: labels, and ink —
nodes of the vector model already (`Ir.Pic.Shape.ink`). This is their
lowering onto a figure both backends then emit. A shape is one top-level
node, so a label's node index is its shape index: ink is its own node, a
label an engine-set label.
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

mutual

-- conserves: none — a relabelling of the empty label type, node for node.
/-- A label-free node at any label type: the ink a picture's shape carries,
as a node of the figure that also holds labels. -/
@[expose] public def Node.lift {L : Type} : Node Empty → Node L
  | .draw g fl st => .draw g fl st
  | .group xf clips alpha kids => .group xf clips alpha (Node.liftList #[] kids.toList)
  | .use k xf => .use k xf
  | .stamp o xf fl st => .stamp o xf fl st
  | .image k xf => .image k xf
  | .label l => nomatch l
  | .words s => .words s

@[expose] public def Node.liftList {L : Type} (acc : Array (Node L)) :
    List (Node Empty) → Array (Node L)
  | [] => acc
  | n :: rest => Node.liftList (acc.push (Node.lift n)) rest

end

/-- The lifting walk as a map over its list. -/
public theorem Node.liftList_map {L : Type} (acc : Array (Node L)) (xs : List (Node Empty)) :
    Node.liftList acc xs = acc ++ (xs.map Node.lift).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.liftList]
  | cons x rest ih => simp [Node.liftList, ih]

/-- One shape as one node. -/
@[expose] public def ofShape : Ir.Pic.Shape → Node LabelSpec
  | .label x y content color scale align =>
    .label { x := x, y := y, content := content, color := color, scale := scale, align := align }
  | .ink n => n.lift

/-- **Today's shapes lower as they always did** (`_id`): each of the four
the subset drew before ink was general — a fill, a circle, a frame, an
edge with its tip — is the node the lowering wrote for it, so no picture
drawn before moves a mark. -/
public theorem ofPicture_ink_id (x y w h r : Sp) (c : Ir.Color) (st : Option Ir.Pic.Stroke)
    (fl : Option Ir.Color) (segs : Array Ir.Pic.PathSeg) (k : Ir.Pic.Stroke)
    (tip : Option Ir.Pic.Tip) :
    ofShape (.rect x y w h c) =
        .draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h)))
          (some (Ir.Pic.solidFill c)) none ∧
      ofShape (.circle x y r st fl) =
        .draw (.ellipse x y (max r (-r)) (max r (-r))) (fl.map Ir.Pic.solidFill)
          (st.map Ir.Pic.strokeOf) ∧
      ofShape (.frame x y w h st fl) =
        .draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h)))
          (fl.map Ir.Pic.solidFill) (st.map Ir.Pic.strokeOf) ∧
      ofShape (.edge segs k tip) =
        .group Affine.unit #[] Alpha.opaque
          (#[.draw (.path (Ir.Pic.edgeSubpaths segs)) none (some (Ir.Pic.strokeOf k))] ++
            match tip with
            | some t => #[.draw (.path #[Ir.Pic.tipSubpath t]) (some (Ir.Pic.solidFill k.color)) none]
            | none => #[]) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases tip <;> rfl

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

/-- Whether a shape lowers to exactly one element of a picture's tree: a
label, or ink that draws, groups, stamps or maps a raster — the ink a
picture's evaluator builds. Recovered words and a symbol use paint no
element of their own there. -/
@[expose] public def shapeOneEl : Ir.Pic.Shape → Bool
  | .label .. => true
  | .ink (.draw ..) => true
  | .ink (.group ..) => true
  | .ink (.stamp ..) => true
  | .ink (.image ..) => true
  | .ink (.use ..) => false
  | .ink (.words _) => false
  | .ink (.label l) => nomatch l

/-- The label a shape carries, if it is one. -/
@[expose] public def labelOf? : Ir.Pic.Shape → Option LabelSpec
  | .label x y content color scale align =>
    some { x := x, y := y, content := content, color := color, scale := scale, align := align }
  | .ink _ => none

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
  | label => rfl
  | ink n => cases n <;> first | rfl | (rename_i l; exact nomatch l)

private theorem imageFreeList_append {L : Type} (a b : List (Node L)) :
    Node.imageFreeList (a ++ b) = (Node.imageFreeList a && Node.imageFreeList b) := by
  induction a with
  | nil => simp [Node.imageFreeList]
  | cons n rest ih => simp [Node.imageFreeList, ih, Bool.and_assoc]

/-- Whether a shape's ink paints no raster: a label paints none. -/
@[expose] public def shapeImageFree : Ir.Pic.Shape → Bool
  | .label _ _ _ _ _ _ => true
  | .ink n => n.imageFree

mutual

private theorem lift_imageFree {L : Type} :
    ∀ n : Node Empty, n.imageFree = true → (Node.lift n : Node L).imageFree = true
  | .draw g fl st, _ => rfl
  | .group xf clips alpha kids, h => by
    simp only [Node.imageFree] at h
    simp only [Node.lift, Node.imageFree]
    exact liftList_imageFree #[] rfl kids.toList h
  | .use k xf, _ => rfl
  | .stamp o xf fl st, _ => rfl
  | .image _ _, h => by simp [Node.imageFree] at h
  | .label l, _ => nomatch l
  | .words w, _ => rfl

private theorem liftList_imageFree {L : Type} (acc : Array (Node L))
    (hacc : Node.imageFreeList acc.toList = true) :
    ∀ xs : List (Node Empty), Node.imageFreeList xs = true →
      Node.imageFreeList (Node.liftList acc xs).toList = true
  | [], _ => by simpa [Node.liftList] using hacc
  | n :: rest, h => by
    simp only [Node.imageFreeList, Bool.and_eq_true] at h
    simp only [Node.liftList]
    apply liftList_imageFree _ _ rest h.2
    simp [imageFreeList_append, hacc, Node.imageFreeList, lift_imageFree n h.1]

end

private theorem ofShape_imageFree (s : Ir.Pic.Shape) (h : shapeImageFree s = true) :
    (ofShape s).imageFree = true := by
  cases s with
  | label => rfl
  | ink n => exact lift_imageFree n h

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

private theorem imageFreeList_map (xs : List Ir.Pic.Shape) (h : ∀ s ∈ xs, shapeImageFree s = true) :
    Node.imageFreeList (xs.map ofShape) = true := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    simp [Node.imageFreeList, ofShape_imageFree s (h s (List.mem_cons_self ..)),
      ih fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]

/-- **A picture's ink paints no raster** (`_exact`) where its shapes'
ink holds none: every node the lowering makes, its labels taken out, is
the shapes' own ink — so a page's ink asks the PDF writer for an image only
where a shape's node held one, which no evaluator door builds; the writer
refuses that case (`Pdf.inkRasterPage?`). -/
public theorem ofPictureIn_imageFree_exact (box : Box) (pic : Ir.Pic.Picture)
    (h : ∀ s ∈ pic.shapes, shapeImageFree s = true) :
    (ofPictureIn box pic).dropLabels.imageFree = true := by
  have h' := dropLabelsList_imageFree #[] rfl _
    (imageFreeList_map pic.shapes.toList fun s hs => h s (Array.mem_toList_iff.mp hs))
  simp [Figure.imageFree, Figure.dropLabels, ofPictureIn, h']

/-- A label repainted. -/
@[expose] public def LabelSpec.recolor (f : Ir.Color → Ir.Color) (l : LabelSpec) : LabelSpec :=
  { l with color := f l.color }

mutual

private theorem lift_recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) :
    ∀ n : Node Empty,
      (Node.lift (Node.recolorOne f id n) : Node L) = Node.recolorOne f fl (Node.lift n)
  | .draw g fill st => rfl
  | .group xf clips alpha kids => by
    simp only [Node.recolorOne, Node.lift, Node.recolorList_map, Array.toList_append,
      List.nil_append]
    congr 1
    have h := liftList_recolor f fl #[] kids.toList
    simp only [Array.map_empty] at h
    rw [h]
    apply Array.ext'
    simp
  | .use k xf => rfl
  | .stamp o xf fill st => rfl
  | .image k xf => rfl
  | .label l => nomatch l
  | .words w => rfl

private theorem liftList_recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (acc : Array (Node L)) :
    ∀ xs : List (Node Empty),
      Node.liftList (acc.map (Node.recolorOne f fl)) (xs.map (Node.recolorOne f id)) =
        (Node.liftList acc xs).map (Node.recolorOne f fl)
  | [] => rfl
  | n :: rest => by
    simp only [List.map_cons, Node.liftList]
    rw [lift_recolor f fl n, ← Array.map_push]
    exact liftList_recolor f fl (acc.push (Node.lift n)) rest

end

private theorem ofShape_recolor (f : Ir.Color → Ir.Color) (s : Ir.Pic.Shape) :
    ofShape (s.recolor f) = Node.recolorOne f (LabelSpec.recolor f) (ofShape s) := by
  cases s with
  | label x y content color scale align => rfl
  | ink n => exact lift_recolor f (LabelSpec.recolor f) n

/-- **Lowering commutes with repainting** (`_exact`): dimming a picture
under an overlay cover and lowering it is lowering it and dimming the
figure, labels included. -/
public theorem ofPicture_recolor_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture)
    (f : Ir.Color → Ir.Color) :
    ofPicture m (pic.recolor f) = (ofPicture m pic).recolor f (LabelSpec.recolor f) := by
  have hb := Ir.Pic.Picture.recolor_box_id pic f m
  simp only [ofPicture, ofPictureIn, Figure.recolor, Node.recolorList_map, Array.map_empty,
    Array.empty_append]
  rw [hb]
  simp only [Figure.mk.injEq, true_and, and_true]
  apply Array.ext'
  simp only [Ir.Pic.Picture.recolor, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro s _
  exact ofShape_recolor f s

end LeanTex.Core.Gfx
