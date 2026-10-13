module

public import LeanTex.Core.Ir
public import LeanTex.Core.GfxAffine
public import LeanTex.Core.GfxSteps

/-! A TikZ picture's evaluated shapes lowered onto a figure, one top-level node per shape. -/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

/-- A picture label as its shape carries it: anchor, content, colour, per-mille size and alignment. -/
public structure LabelSpec where
  x : Sp
  y : Sp
  content : Array Ir.Inline
  color : Ir.Color
  scale : Nat
  align : Ir.Pic.LabelAlign
  deriving Repr, Inhabited

mutual

-- conserves: none — a relabelling of the empty label type.
/-- A label-free node at any label type. -/
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

public theorem Node.liftList_map {L : Type} (acc : Array (Node L)) (xs : List (Node Empty)) :
    Node.liftList acc xs = acc ++ (xs.map Node.lift).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.liftList]
  | cons x rest ih => simp [Node.liftList, ih]

@[expose] public def ofShape : Ir.Pic.Shape → Node LabelSpec
  | .label x y content color scale align =>
    .label { x := x, y := y, content := content, color := color, scale := scale, align := align }
  | .ink n => n.lift

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

/-- A picture as a figure: its shapes as nodes in source order in the IR's one box, never clipping. -/
@[expose] public def ofPicture (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) : Figure LabelSpec :=
  ofPictureIn (pic.box m) pic

public theorem ofPicture_box_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) :
    (ofPicture m pic).box = pic.box m := rfl

public theorem ofPicture_nodes_exact (m : Ir.Pic.LabelMetric) (pic : Ir.Pic.Picture) (i : Nat) :
    (ofPicture m pic).nodes[i]? = pic.shapes[i]?.map ofShape := by
  simp [ofPicture, ofPictureIn]

/-- Whether a shape lowers to exactly one element of a picture's tree: a label, or ink that draws,
groups, stamps or maps a raster. -/
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

public theorem ofPictureIn_imageFree_exact (box : Box) (pic : Ir.Pic.Picture)
    (h : ∀ s ∈ pic.shapes, shapeImageFree s = true) :
    (ofPictureIn box pic).dropLabels.imageFree = true := by
  have h' := dropLabelsList_imageFree #[] rfl _
    (imageFreeList_map pic.shapes.toList fun s hs => h s (Array.mem_toList_iff.mp hs))
  simp [Figure.imageFree, Figure.dropLabels, ofPictureIn, h']

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

/-- A label-free figure as one of any label type. -/
@[expose] public def Figure.lift {L : Type} (fig : Figure Empty) : Figure L :=
  { box := fig.box, clipToBox := fig.clipToBox, nodes := fig.nodes.map Node.lift
    outlines := fig.outlines, symbols := fig.symbols.map (·.map Node.lift)
    rasters := fig.rasters, title := fig.title, losses := fig.losses }

/-- A picture as the page's ink, each label keyed by the picture `id` and its shape index. -/
@[expose] public def ofPictureKeyed (id : Nat) (box : Box) (pic : Ir.Pic.Picture) :
    Figure (Nat × Nat) :=
  { box := box, clipToBox := false
    nodes := (ofPictureIn box pic).nodes.mapIdx fun i n => n.mapLabelsOne fun _ => (id, i)
    outlines := #[], symbols := #[], rasters := #[], title := none, losses := #[] }

mutual

private theorem lift_labelFree {L : Type} : ∀ n : Node Empty, (Node.lift n : Node L).labelFree = true
  | .draw .. => rfl
  | .group _ _ _ kids => by
    simp only [Node.lift, Node.labelFree, Node.liftList_map, Array.toList_append, List.nil_append]
    exact liftList_labelFree kids.toList
  | .use .. => rfl
  | .stamp .. => rfl
  | .image .. => rfl
  | .label l => nomatch l
  | .words _ => rfl

private theorem liftList_labelFree {L : Type} :
    ∀ xs : List (Node Empty), Node.labelFreeList (xs.map (Node.lift (L := L))) = true
  | [] => rfl
  | n :: rest => by
    simp only [List.map_cons, Node.labelFreeList, lift_labelFree n, liftList_labelFree rest,
      Bool.and_self]

end

mutual

private theorem mapLabels_labelFree {L L' : Type} (f : L → L') :
    ∀ n : Node L, (n.mapLabelsOne f).labelFree = n.labelFree
  | .draw .. => rfl
  | .group _ _ _ kids => by
    simp only [Node.mapLabelsOne, Node.labelFree, Node.mapLabelsList_map, Array.toList_append,
      List.nil_append]
    exact mapLabelsList_labelFree f kids.toList
  | .use .. => rfl
  | .stamp .. => rfl
  | .image .. => rfl
  | .label _ => rfl
  | .words _ => rfl

private theorem mapLabelsList_labelFree {L L' : Type} (f : L → L') :
    ∀ xs : List (Node L),
      Node.labelFreeList (xs.map (Node.mapLabelsOne f)) = Node.labelFreeList xs
  | [] => rfl
  | n :: rest => by
    simp only [List.map_cons, Node.labelFreeList, mapLabels_labelFree f n,
      mapLabelsList_labelFree f rest]

end

private theorem mapLabels_topOk {L L' : Type} (f : L → L') (n : Node L) :
    (n.mapLabelsOne f).topOk = n.topOk := by
  cases n with
  | group _ _ _ kids =>
    simp only [Node.mapLabelsOne, Node.topOk, Node.mapLabelsList_map, Array.toList_append,
      List.nil_append]
    exact mapLabelsList_labelFree f kids.toList
  | draw | use | stamp | image | label | words => rfl

private theorem ofShape_topOk (s : Ir.Pic.Shape) : (ofShape s).topOk = true := by
  cases s with
  | label => rfl
  | ink n =>
    cases n with
    | group _ _ _ kids =>
      simp only [ofShape, Node.lift, Node.topOk, Node.liftList_map, Array.toList_append,
        List.nil_append]
      exact liftList_labelFree kids.toList
    | label l => exact nomatch l
    | draw | use | stamp | image | words => rfl

public theorem ofPictureIn_labelsTop_exact (box : Box) (pic : Ir.Pic.Picture) :
    (ofPictureIn box pic).labelsTop = true := by
  have hn : (ofPictureIn box pic).nodes.all Node.topOk = true := by
    rw [Array.all_eq_true]
    intro i hi
    simp only [ofPictureIn, Array.getElem_map]
    exact ofShape_topOk _
  simp only [Figure.labelsTop, hn, Bool.true_and]
  simp [ofPictureIn]

public theorem ofPictureKeyed_labelsTop_exact (id : Nat) (box : Box) (pic : Ir.Pic.Picture) :
    (ofPictureKeyed id box pic).labelsTop = true := by
  have hn : (ofPictureKeyed id box pic).nodes.all Node.topOk = true := by
    rw [Array.all_eq_true]
    intro i hi
    simp only [ofPictureKeyed, Array.getElem_mapIdx, mapLabels_topOk]
    simp only [ofPictureIn, Array.getElem_map]
    exact ofShape_topOk _
  simp only [Figure.labelsTop, hn, Bool.true_and]
  simp [ofPictureKeyed]

mutual

private theorem mapLabels_imageFree {L L' : Type} (f : L → L') :
    ∀ n : Node L, (n.mapLabelsOne f).imageFree = n.imageFree
  | .draw .. => rfl
  | .group _ _ _ kids => by
    simp only [Node.mapLabelsOne, Node.imageFree, Node.mapLabelsList_map, Array.toList_append,
      List.nil_append]
    exact mapLabelsList_imageFree f kids.toList
  | .use .. => rfl
  | .stamp .. => rfl
  | .image .. => rfl
  | .label _ => rfl
  | .words _ => rfl

private theorem mapLabelsList_imageFree {L L' : Type} (f : L → L') :
    ∀ xs : List (Node L),
      Node.imageFreeList (xs.map (Node.mapLabelsOne f)) = Node.imageFreeList xs
  | [] => rfl
  | n :: rest => by
    simp only [List.map_cons, Node.imageFreeList, mapLabels_imageFree f n,
      mapLabelsList_imageFree f rest]

end

private theorem imageFreeList_mapIdx {L L' : Type} (f : Nat → L → L') :
    ∀ xs : List (Node L),
      Node.imageFreeList (xs.mapIdx fun i n => n.mapLabelsOne (f i)) = Node.imageFreeList xs := by
  intro xs
  induction xs generalizing f with
  | nil => rfl
  | cons n rest ih =>
    rw [List.mapIdx_cons]
    simp only [Node.imageFreeList, mapLabels_imageFree]
    rw [ih (fun i => f (i + 1))]

public theorem ofPictureKeyed_imageFree_exact (id : Nat) (box : Box) (pic : Ir.Pic.Picture)
    (h : ∀ s ∈ pic.shapes, shapeImageFree s = true) :
    (ofPictureKeyed id box pic).imageFree = true := by
  have h' := imageFreeList_map pic.shapes.toList fun s hs => h s (Array.mem_toList_iff.mp hs)
  simp only [Figure.imageFree, ofPictureKeyed, Array.toList_mapIdx, ofPictureIn, Array.toList_map]
  rw [imageFreeList_mapIdx (fun i (_ : LabelSpec) => (id, i)), h']
  simp

private theorem marks_mapIdx {L L' : Type} (outlines : Array (Array Subpath)) (cx : Ctx)
    (f : Nat → L → L') :
    ∀ (xs : List (Node L)) (acc : Array Mark),
      Node.marksList outlines cx acc
          (Node.expandList (#[] : Array (Array (Node L'))) 0 #[]
            (xs.mapIdx fun i n => n.mapLabelsOne (f i))).toList =
        Node.marksList outlines cx acc
          (Node.expandList (#[] : Array (Array (Node L))) 0 #[] xs).toList := by
  intro xs
  induction xs generalizing f with
  | nil => intro acc; rfl
  | cons n rest ih =>
    intro acc
    rw [List.mapIdx_cons]
    simp only [Node.expandList]
    rw [Node.expandList_acc, Node.expandList_acc (#[] : Array (Array (Node L))),
      Array.toList_append, Array.toList_append, Node.marksList_append, Node.marksList_append,
      Node.expandOne_mapLabels, Array.toList_map, Node.marksList_mapLabels,
      ih (fun i => f (i + 1))]

public theorem ofPictureKeyed_marks_exact (id : Nat) (box : Box) (pic : Ir.Pic.Picture) :
    (ofPictureKeyed id box pic).marks = (ofPictureIn box pic).marks := by
  have hb : (ofPictureKeyed id box pic).bodies = #[] := by simp [ofPictureKeyed, Figure.bodies]
  have hb' : (ofPictureIn box pic).bodies = #[] := by simp [ofPictureIn, Figure.bodies]
  unfold Figure.marks Figure.expanded
  rw [hb, hb']
  simp only [Array.size_empty]
  have hn : (ofPictureKeyed id box pic).nodes.toList =
      (ofPictureIn box pic).nodes.toList.mapIdx fun i n => n.mapLabelsOne fun _ => (id, i) := by
    simp [ofPictureKeyed]
  rw [hn]
  exact marks_mapIdx #[] Ctx.root (fun i (_ : LabelSpec) => (id, i)) _ #[]

private theorem flatMap_mapIdx {α β γ : Type} (g : Nat → α → β) (h₁ : β → List γ)
    (h₂ : α → List γ) (h : ∀ i a, h₁ (g i a) = h₂ a) :
    ∀ xs : List α, (xs.mapIdx g).flatMap h₁ = xs.flatMap h₂ := by
  intro xs
  induction xs generalizing g with
  | nil => rfl
  | cons a rest ih =>
    rw [List.mapIdx_cons, List.flatMap_cons, List.flatMap_cons, h 0 a,
      ih (fun i => g (i + 1)) (fun i a => h (i + 1) a)]

public theorem ofPictureKeyed_steps_exact (id : Nat) (box : Box) (pic : Ir.Pic.Picture) :
    (ofPictureKeyed id box pic).steps.map (Step.mapLabel fun _ => ()) =
      (ofPictureIn box pic).steps.map (Step.mapLabel fun _ => ()) := by
  rw [Figure.steps_eq, Figure.steps_eq]
  apply Array.toList_inj.mp
  simp only [Array.toList_map, List.map_flatMap]
  have hn : (ofPictureKeyed id box pic).nodes.toList =
      (ofPictureIn box pic).nodes.toList.mapIdx fun i n => n.mapLabelsOne fun _ => (id, i) := by
    simp [ofPictureKeyed]
  rw [hn]
  apply flatMap_mapIdx
  intro i n
  rw [Figure.nodeSteps_mapLabels_exact (fun _ => (id, i)) (ofPictureIn box pic)
    (ofPictureKeyed id box pic) rfl rfl rfl n]
  simp only [Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

end LeanTex.Core.Gfx
