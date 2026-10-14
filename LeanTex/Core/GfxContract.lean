module

public import LeanTex.Core.GfxPdf
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.GfxPicture

/-! The statements that need both emitters: the two artifacts paint one figure and set its labels in one order. -/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

private theorem expandList_append {L : Type} (done : Array (Array (Node L))) (bound : Nat)
    (a b : List (Node L)) :
    Node.expandList done bound #[] (a ++ b) =
      Node.expandList done bound #[] a ++ Node.expandList done bound #[] b := by
  induction a with
  | nil => simp [Node.expandList]
  | cons n rest ih =>
    simp only [List.cons_append, Node.expandList]
    rw [Node.expandList_acc, ih, Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest,
      Array.append_assoc]

mutual

public theorem Node.dropLabelsOne_acc {L : Type} (acc : Array (Node Empty)) (n : Node L) :
    Node.dropLabelsOne acc n = acc ++ Node.dropLabelsOne #[] n := by
  cases n <;> simp [Node.dropLabelsOne]

public theorem Node.dropLabelsList_acc {L : Type} (acc : Array (Node Empty)) (xs : List (Node L)) :
    Node.dropLabelsList acc xs = acc ++ Node.dropLabelsList #[] xs := by
  match xs with
  | [] => simp [Node.dropLabelsList]
  | n :: rest =>
    simp only [Node.dropLabelsList]
    rw [Node.dropLabelsList_acc _ rest, Node.dropLabelsList_acc (Node.dropLabelsOne #[] n) rest,
      Node.dropLabelsOne_acc acc n, Array.append_assoc]

end

private theorem dropLabelsList_append {L : Type} (a b : List (Node L)) :
    Node.dropLabelsList #[] (a ++ b) = Node.dropLabelsList #[] a ++ Node.dropLabelsList #[] b := by
  induction a with
  | nil => simp [Node.dropLabelsList]
  | cons n rest ih =>
    simp only [List.cons_append, Node.dropLabelsList]
    rw [Node.dropLabelsList_acc, ih, Node.dropLabelsList_acc (Node.dropLabelsOne #[] n) rest,
      Array.append_assoc]

/-- A node list map that keeps every use and group, their transforms by `xf` and clips by `cl`. -/
private structure KeepsUses {L L' : Type} (M : List (Node L) → Array (Node L')) (xf : Affine → Affine)
    (cl : Array Clip → Array Clip) : Prop where
  nil : M [] = #[]
  append : ∀ a b, M a ++ M b = M (a ++ b)
  group : ∀ x c α kids, M [.group x c α kids] = #[.group (xf x) (cl c) α (M kids.toList)]
  use : ∀ k x, M [.use k x] = #[.use k (xf x)]
  noClips : cl #[] = #[]
  draw : ∀ D b g fl st, Node.expandList D b #[] (M [.draw g fl st]).toList = M [.draw g fl st]
  stamp : ∀ D b o x fl st,
    Node.expandList D b #[] (M [.stamp o x fl st]).toList = M [.stamp o x fl st]
  image : ∀ D b k x, Node.expandList D b #[] (M [.image k x]).toList = M [.image k x]
  label : ∀ D b l, Node.expandList D b #[] (M [.label l]).toList = M [.label l]
  words : ∀ D b s, Node.expandList D b #[] (M [.words s]).toList = M [.words s]

section Keeps

variable {L L' : Type} {M : List (Node L) → Array (Node L')} {xf : Affine → Affine}
  {cl : Array Clip → Array Clip}

mutual

private theorem expand_keeps_one (h : KeepsUses M xf cl) (done : Array (Array (Node L))) (bound : Nat) :
    ∀ n : Node L,
      Node.expandList (done.map (M ·.toList)) bound #[] (M [n]).toList =
        M (Node.expandOne done bound #[] n).toList
  | .draw g fl st => by rw [h.draw]; rfl
  | .group x c α kids => by
    rw [h.group]
    simp only [Node.expandOne, Node.expandList, Array.push_empty]
    rw [h.group, expand_keeps_list h done bound kids.toList]
  | .use k x => by
    rw [h.use]
    simp only [Node.expandOne, Node.expandList, Array.getElem?_map, Array.push_empty]
    split
    · cases done[k]? with
      | none => simp [h.nil]
      | some b => simp [h.group, h.noClips]
    · simp [h.nil]
  | .stamp o x fl st => by rw [h.stamp]; rfl
  | .image k x => by rw [h.image]; rfl
  | .label l => by rw [h.label]; rfl
  | .words s => by rw [h.words]; rfl

private theorem expand_keeps_list (h : KeepsUses M xf cl) (done : Array (Array (Node L))) (bound : Nat) :
    ∀ xs : List (Node L),
      Node.expandList (done.map (M ·.toList)) bound #[] (M xs).toList =
        M (Node.expandList done bound #[] xs).toList
  | [] => by simp [h.nil, Node.expandList]
  | n :: rest => by
    rw [show n :: rest = [n] ++ rest from rfl, ← h.append, Array.toList_append, expandList_append,
      expand_keeps_one h done bound n, expand_keeps_list h done bound rest, List.singleton_append,
      Node.expandList, Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest,
      Array.toList_append, ← h.append]

end

/-- A figure whose nodes and symbols are mapped by `M` expands to the mapped expansion. -/
private theorem expanded_keeps (h : KeepsUses M xf cl) (fig : Figure L) (fig' : Figure L')
    (hn : fig'.nodes = M fig.nodes.toList) (hs : fig'.symbols = fig.symbols.map (M ·.toList)) :
    fig'.expanded = M fig.expanded.toList := by
  have hb : fig'.bodies = fig.bodies.map (M ·.toList) := by
    unfold Figure.bodies
    rw [hs, Array.foldl_map]
    suffices hl : ∀ (l : List (Array (Node L))) (done : Array (Array (Node L))),
        l.foldl (fun d (sym : Array (Node L)) =>
            d.push (Node.expandList d d.size #[] (M sym.toList).toList)) (done.map (M ·.toList)) =
          (l.foldl (fun d (sym : Array (Node L)) =>
            d.push (Node.expandList d d.size #[] sym.toList)) done).map (M ·.toList) by
      simpa [Array.foldl_toList] using hl fig.symbols.toList #[]
    intro l
    induction l with
    | nil => intro done; rfl
    | cons sym rest ih =>
      intro done
      simp only [List.foldl_cons]
      rw [← ih, Array.size_map, expand_keeps_list h done done.size sym.toList, Array.map_push]
  unfold Figure.expanded
  rw [hb, Array.size_map, hn]
  exact expand_keeps_list h fig.bodies fig.bodies.size fig.nodes.toList

end Keeps

private theorem dropKeeps {L : Type} : KeepsUses (L := L) (Node.dropLabelsList #[]) id id where
  nil := rfl
  append a b := (dropLabelsList_append a b).symm
  group _ _ _ _ := rfl
  use _ _ := rfl
  noClips := rfl
  draw _ _ _ _ _ := rfl
  stamp _ _ _ _ _ _ := rfl
  image _ _ _ _ := rfl
  label _ _ _ := rfl
  words _ _ _ := rfl

mutual

private theorem marks_drop_one {L : Type} (outlines : Array (Array Subpath)) :
    ∀ (n : Node L) (cx : Ctx) (acc : Array Mark),
      Node.marksList outlines cx acc (Node.dropLabelsOne #[] n).toList =
        Node.marksOne outlines cx acc n
  | .draw g fl st, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]
  | .group xf clips alpha kids, cx, acc => by
    simp only [Node.dropLabelsOne, Array.toList_push, List.nil_append, Node.marksList,
      Node.marksOne]
    exact marks_drop_list outlines kids.toList _ acc
  | .use k xf, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]
  | .stamp o xf fl st, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]
  | .image k xf, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]
  | .label l, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]
  | .words w, cx, acc => by simp [Node.dropLabelsOne, Node.marksList, Node.marksOne]

private theorem marks_drop_list {L : Type} (outlines : Array (Array Subpath)) :
    ∀ (xs : List (Node L)) (cx : Ctx) (acc : Array Mark),
      Node.marksList outlines cx acc (Node.dropLabelsList #[] xs).toList =
        Node.marksList outlines cx acc xs
  | [], cx, acc => by simp [Node.dropLabelsList, Node.marksList]
  | n :: rest, cx, acc => by
    simp only [Node.dropLabelsList, Node.marksList]
    rw [Node.dropLabelsList_acc, Array.toList_append, Node.marksList_append,
      marks_drop_one outlines n cx acc, marks_drop_list outlines rest cx _]

end

public theorem Figure.dropLabels_marks_id {L : Type} (fig : Figure L) :
    fig.dropLabels.marks = fig.marks := by
  unfold Figure.marks
  rw [expanded_keeps dropKeeps fig fig.dropLabels rfl rfl, marks_drop_list]
  rfl

public theorem backend_marks_agree {L : Type} (ix : GfxPdf.Request → Nat)
    (labelOps : GfxPdf.Frame → L → Array Pdf.ContentOp)
    (hl : ∀ fr l rs acc, GfxPdf.readList rs acc (labelOps fr l).toList = acc)
    (labelEl : GfxSvg.SFrame → L → Html.Node) (rasters : Array GfxSvg.RasterRef)
    (pdfPlace svgPlace : Iso) (fig : Figure L) :
    GfxPdf.readMarks pdfPlace (GfxPdf.emit ix labelOps pdfPlace fig) =
      GfxSvg.readMarks svgPlace (GfxSvg.tree labelEl rasters svgPlace fig) :=
  (GfxPdf.marks_projects ix labelOps hl pdfPlace fig).trans
    (GfxSvg.marks_projects labelEl rasters svgPlace fig).symm

public theorem picture_marks_agree (ix : GfxPdf.Request → Nat) (pdfPlace svgPlace : Iso)
    (tx : Nat × Nat → Option (Array Pdf.TextOp))
    (labelEl : GfxSvg.SFrame → LabelSpec → Html.Node) (id : Nat) (box : Box)
    (pic : Ir.Pic.Picture) :
    GfxPdf.readMarks pdfPlace
        (GfxPdf.emit ix (fun _ k => (tx k).toArray.map GfxPdf.textGroup) pdfPlace
          (ofPictureKeyed id box pic)) =
      GfxSvg.readMarks svgPlace (GfxSvg.tree labelEl #[] svgPlace (ofPictureIn box pic)) := by
  have hl : ∀ (fr : GfxPdf.Frame) (k : Nat × Nat) (rs : GfxPdf.RState) (acc : Array Mark),
      GfxPdf.readList rs acc ((tx k).toArray.map GfxPdf.textGroup).toList = acc := by
    intro fr k rs acc
    cases tx k with
    | none => simp [GfxPdf.readList]
    | some t => simp [GfxPdf.readList, GfxPdf.readOne, GfxPdf.textGroup]
  rw [GfxPdf.marks_projects ix _ hl pdfPlace _, ofPictureKeyed_marks_exact, GfxSvg.marks_projects]

mutual

private theorem words_recolor_one {L : Type} (text : L → String) (f : Ir.Color → Ir.Color)
    (fl : L → L) (hfl : ∀ l, text (fl l) = text l) :
    ∀ (n : Node L) (acc : Array String),
      Node.wordsOne text acc (Node.recolorOne f fl n) = Node.wordsOne text acc n
  | .draw _ _ _, _ => rfl
  | .group _ _ _ kids, acc => words_recolor_list text f fl hfl kids.toList acc
  | .use _ _, _ => rfl
  | .stamp _ _ _ _, _ => rfl
  | .image _ _, _ => rfl
  | .label l, acc => by simp [Node.recolorOne, Node.wordsOne, hfl]
  | .words _, _ => rfl

private theorem words_recolor_list {L : Type} (text : L → String) (f : Ir.Color → Ir.Color)
    (fl : L → L) (hfl : ∀ l, text (fl l) = text l) :
    ∀ (xs : List (Node L)) (acc : Array String),
      Node.wordsList text acc (Node.recolorList f fl #[] xs).toList = Node.wordsList text acc xs
  | [], _ => rfl
  | n :: rest, acc => by
    simp only [Node.recolorList]
    rw [Node.recolorList_acc, Array.toList_append, Node.wordsList_append]
    simp only [Array.toList_push, List.nil_append, Node.wordsList]
    rw [words_recolor_one text f fl hfl n acc, words_recolor_list text f fl hfl rest]

end

mutual

private theorem words_quantize_one {L : Type} (text : L → String) (ql : L → L)
    (hql : ∀ l, text (ql l) = text l) :
    ∀ (n : Node L) (acc : Array String),
      Node.wordsOne text acc (Node.quantizeOne ql n) = Node.wordsOne text acc n
  | .draw _ _ _, _ => rfl
  | .group _ _ _ kids, acc => words_quantize_list text ql hql kids.toList acc
  | .use _ _, _ => rfl
  | .stamp _ _ _ _, _ => rfl
  | .image _ _, _ => rfl
  | .label l, acc => by simp [Node.quantizeOne, Node.wordsOne, hql]
  | .words _, _ => rfl

private theorem words_quantize_list {L : Type} (text : L → String) (ql : L → L)
    (hql : ∀ l, text (ql l) = text l) :
    ∀ (xs : List (Node L)) (acc : Array String),
      Node.wordsList text acc (Node.quantizeList ql #[] xs).toList = Node.wordsList text acc xs
  | [], _ => rfl
  | n :: rest, acc => by
    simp only [Node.quantizeList]
    rw [Node.quantizeList_acc, Array.toList_append, Node.wordsList_append]
    simp only [Array.toList_push, List.nil_append, Node.wordsList]
    rw [words_quantize_one text ql hql n acc, words_quantize_list text ql hql rest]

end

private theorem recolorList_append {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (a b : List (Node L)) :
    Node.recolorList f fl #[] (a ++ b) = Node.recolorList f fl #[] a ++ Node.recolorList f fl #[] b := by
  induction a with
  | nil => simp [Node.recolorList]
  | cons n rest ih =>
    simp only [List.cons_append, Node.recolorList]
    rw [Node.recolorList_acc, ih, Node.recolorList_acc _ _ (#[].push _) rest, Array.append_assoc]

private theorem quantizeList_append' {L : Type} (ql : L → L) (a b : List (Node L)) :
    Node.quantizeList ql #[] (a ++ b) = Node.quantizeList ql #[] a ++ Node.quantizeList ql #[] b := by
  induction a with
  | nil => simp [Node.quantizeList]
  | cons n rest ih =>
    simp only [List.cons_append, Node.quantizeList]
    rw [Node.quantizeList_acc, ih, Node.quantizeList_acc _ (#[].push _) rest, Array.append_assoc]

private theorem recolorKeeps {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) :
    KeepsUses (Node.recolorList f fl #[]) id id where
  nil := rfl
  append a b := (recolorList_append f fl a b).symm
  group _ _ _ _ := rfl
  use _ _ := rfl
  noClips := rfl
  draw _ _ _ _ _ := rfl
  stamp _ _ _ _ _ _ := rfl
  image _ _ _ _ := rfl
  label _ _ _ := rfl
  words _ _ _ := rfl

private theorem quantizeKeeps {L : Type} (ql : L → L) :
    KeepsUses (Node.quantizeList ql #[]) Affine.quantize (·.map Clip.quantize) where
  nil := rfl
  append a b := (quantizeList_append' ql a b).symm
  group _ _ _ _ := rfl
  use _ _ := rfl
  noClips := by simp
  draw _ _ _ _ _ := rfl
  stamp _ _ _ _ _ _ := rfl
  image _ _ _ _ := rfl
  label _ _ _ := rfl
  words _ _ _ := rfl

public theorem Figure.said_text {L : Type} (text : L → String) (f : Ir.Color → Ir.Color)
    (fl ql : L → L) (hfl : ∀ l, text (fl l) = text l) (hql : ∀ l, text (ql l) = text l) :
    Ir.Conserves (Figure.said text) (Figure.recolor f fl) ∧
      Ir.Conserves (Figure.said text) (Figure.quantize ql) := by
  refine ⟨fun fig => ?_, fun fig => ?_⟩
  · simp only [Figure.said]
    rw [expanded_keeps (recolorKeeps f fl) fig (fig.recolor f fl) rfl rfl, words_recolor_list text f fl hfl]
  · simp only [Figure.said]
    rw [expanded_keeps (quantizeKeeps ql) fig (fig.quantize ql) rfl rfl, words_quantize_list text ql hql]

private theorem flatMap_labelsBy_single {L α : Type} (g : L → α) (xs : Array (Step L)) :
    xs.flatMap (Step.labelsBy fun l => #[g l]) = xs.map (Step.mapLabel g) := by
  apply Array.toList_inj.mp
  simp only [Array.toList_flatMap, Array.toList_map]
  induction xs.toList with
  | nil => rfl
  | cons s rest ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    cases s with
    | mark m => rfl
    | label l => simp [Step.labelsBy, Step.mapLabel]

private theorem mapLabel_comp {L α β : Type} (f : L → α) (g : α → β) (xs : Array (Step L)) :
    (xs.map (Step.mapLabel f)).map (Step.mapLabel g) = xs.map (Step.mapLabel (g ∘ f)) := by
  rw [Array.map_map]
  apply Array.map_congr_left
  intro s _
  cases s <;> rfl

public theorem labelOrder_agree {L K : Type} (ix : GfxPdf.Request → Nat)
    (tx : L → Array Pdf.TextOp) (labelEl : GfxSvg.SFrame → L → Html.Node)
    (rasters : Array GfxSvg.RasterRef) (pdfPlace svgPlace : Iso)
    (k₁ : Array Pdf.TextOp → K) (k₂ : Html.Node → K)
    (hk : ∀ l, k₁ (tx l) = k₂ (labelEl { iso := some svgPlace } l))
    (fig : Figure L) (h : fig.labelsTop = true) :
    (GfxPdf.readSteps pdfPlace
        (GfxPdf.emit ix (fun _ l => #[GfxPdf.textGroup (tx l)]) pdfPlace fig)).map
        (Step.mapLabel k₁) =
      (GfxSvg.readSteps svgPlace (GfxSvg.tree labelEl rasters svgPlace fig)).map
        (Step.mapLabel k₂) := by
  have hp := GfxPdf.steps_projects ix (fun l => some (tx l)) pdfPlace fig h
  have hs := GfxSvg.steps_projects labelEl rasters svgPlace fig h
  have hops : (fun (_ : GfxPdf.Frame) (l : L) => #[GfxPdf.textGroup (tx l)]) =
      fun _ l => ((some (tx l)).toArray.map GfxPdf.textGroup) := by
    funext _ l
    simp
  rw [hops, hp, hs]
  have hsingle : (Step.labelsBy fun l => (some (tx l)).toArray) =
      (Step.labelsBy fun l => #[tx l] : Step L → Array (Step (Array Pdf.TextOp))) := by
    funext s
    cases s <;> rfl
  rw [hsingle, flatMap_labelsBy_single, mapLabel_comp, mapLabel_comp]
  apply Array.map_congr_left
  intro s _
  cases s with
  | mark m => rfl
  | label l => simp [Step.mapLabel, hk l]

public theorem picture_labelOrder_agree (ix : GfxPdf.Request → Nat) (id : Nat) (box : Box)
    (pic : Ir.Pic.Picture) (tx : Nat × Nat → Array Pdf.TextOp)
    (labelEl : GfxSvg.SFrame → LabelSpec → Html.Node) (rasters : Array GfxSvg.RasterRef)
    (pdfPlace svgPlace : Iso) :
    (GfxPdf.readSteps pdfPlace (GfxPdf.emit ix (fun _ k => #[GfxPdf.textGroup (tx k)]) pdfPlace
        (ofPictureKeyed id box pic))).map (Step.mapLabel fun _ => ()) =
      (GfxSvg.readSteps svgPlace (GfxSvg.tree labelEl rasters svgPlace (ofPictureIn box pic))).map
        (Step.mapLabel fun _ => ()) := by
  have hp := GfxPdf.steps_projects ix (fun k => some (tx k)) pdfPlace (ofPictureKeyed id box pic)
    (ofPictureKeyed_labelsTop_exact id box pic)
  have hs := GfxSvg.steps_projects labelEl rasters svgPlace (ofPictureIn box pic)
    (ofPictureIn_labelsTop_exact box pic)
  have hops : (fun (_ : GfxPdf.Frame) (k : Nat × Nat) => #[GfxPdf.textGroup (tx k)]) =
      fun _ k => ((some (tx k)).toArray.map GfxPdf.textGroup) := by
    funext _ k
    simp
  rw [hops, hp, hs]
  have hsingle : (Step.labelsBy fun k => (some (tx k)).toArray) =
      (Step.labelsBy fun k => #[tx k] : Step (Nat × Nat) → Array (Step (Array Pdf.TextOp))) := by
    funext s
    cases s <;> rfl
  rw [hsingle, flatMap_labelsBy_single, mapLabel_comp, mapLabel_comp]
  have hk := ofPictureKeyed_steps_exact id box pic
  have e1 : (Step.mapLabel ((fun (_ : Array Pdf.TextOp) => ()) ∘ tx)) =
      (Step.mapLabel (fun (_ : Nat × Nat) => ())) := by
    funext s
    cases s <;> rfl
  have e2 : (Step.mapLabel ((fun (_ : Html.Node) => ()) ∘ labelEl { iso := some svgPlace })) =
      (Step.mapLabel (fun (_ : LabelSpec) => ())) := by
    funext s
    cases s <;> rfl
  rw [e1, e2, hk]

end LeanTex.Core.Gfx
