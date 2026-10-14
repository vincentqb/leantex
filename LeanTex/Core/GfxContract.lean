module

public import LeanTex.Core.GfxPdf
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.GfxPicture

/-! The statements that need both emitters: the two artifacts paint one figure and set its labels in one order. -/

namespace LeanTex.Core.Gfx

open LeanTex.Core LeanTex.Core.Dim

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

private theorem dropKeeps {L : Type} : KeepsUses (L := L) (Node.dropLabelsList #[]) id id where
  nil := rfl
  cons _ rest := (Node.dropLabelsList_acc _ rest).symm
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

section Words

variable {L : Type} {M : List (Node L) → Array (Node L)} {xf : Affine → Affine}
  {cl : Array Clip → Array Clip}

mutual

private theorem words_keeps_one (h : KeepsUses M xf cl) (text : L → String)
    (hleaf : ∀ n acc, (∀ x c α kids, n ≠ .group x c α kids) →
      Node.wordsList text acc (M [n]).toList = Node.wordsOne text acc n) :
    ∀ (n : Node L) (acc : Array String),
      Node.wordsList text acc (M [n]).toList = Node.wordsOne text acc n
  | .group x c α kids, acc => by
    rw [h.group]
    exact words_keeps_list h text hleaf kids.toList acc
  | .draw g fl st, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)
  | .use k x, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)
  | .stamp o x fl st, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)
  | .image k x, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)
  | .label l, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)
  | .words s, acc => hleaf _ acc (fun _ _ _ _ h => by cases h)

private theorem words_keeps_list (h : KeepsUses M xf cl) (text : L → String)
    (hleaf : ∀ n acc, (∀ x c α kids, n ≠ .group x c α kids) →
      Node.wordsList text acc (M [n]).toList = Node.wordsOne text acc n) :
    ∀ (xs : List (Node L)) (acc : Array String),
      Node.wordsList text acc (M xs).toList = Node.wordsList text acc xs
  | [], _ => by rw [h.nil]
  | n :: rest, acc => by
    rw [← h.cons, Array.toList_append, Node.wordsList_append, words_keeps_one h text hleaf n acc,
      words_keeps_list h text hleaf rest]
    rfl

end

end Words

private theorem recolorKeeps {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) :
    KeepsUses (Node.recolorList f fl #[]) id id where
  nil := rfl
  cons _ rest := (Node.recolorList_acc f fl _ rest).symm
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
  cons _ rest := (Node.quantizeList_acc ql _ rest).symm
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
    rw [expanded_keeps (recolorKeeps f fl) fig (fig.recolor f fl) rfl rfl,
      words_keeps_list (recolorKeeps f fl) text (fun n acc hn => by
        cases n <;>
          first
          | exact absurd rfl (hn _ _ _ _)
          | simp [Node.recolorList, Node.recolorOne, Node.wordsList, Node.wordsOne, hfl])]
  · simp only [Figure.said]
    rw [expanded_keeps (quantizeKeeps ql) fig (fig.quantize ql) rfl rfl,
      words_keeps_list (quantizeKeeps ql) text (fun n acc hn => by
        cases n <;>
          first
          | exact absurd rfl (hn _ _ _ _)
          | simp [Node.quantizeList, Node.quantizeOne, Node.wordsList, Node.wordsOne, hql])]

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
