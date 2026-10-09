module

public import LeanTex.Core.GfxPdf
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.GfxPicture

/-!
# The two artifacts paint one figure

The statements that need both emitters. `backend_marks_agree` is the
invariant whose absence let a picture's two artifacts differ — rectangle
fills painted before every path in one, continuing segments broken into
caps in the other, a zero width invisible, corners bevelled at SVG's miter
limit: the marks the PDF says and the marks the SVG says are one reading,
because each is the figure's (`GfxPdf.marks_projects`,
`GfxSvg.marks_projects`). Labels are not ink: their order is each backend's
own (HTML in source order, PDF in the page's text object), and a statement
that they agree waits for figure text to be set inside the figure.
-/

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

/-! ## Taking labels out moves no mark -/

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

/-- A body with its labels taken out. -/
private def dropBody {L : Type} (b : Array (Node L)) : Array (Node Empty) :=
  Node.dropLabelsList #[] b.toList

mutual

/-- Expanding a tree and taking its labels out commute, given bodies that
already agree. -/
private theorem expand_drop_one {L : Type} (done : Array (Array (Node L))) (bound : Nat) :
    ∀ n : Node L,
      Node.expandList (done.map dropBody) bound #[] (Node.dropLabelsOne #[] n).toList =
        Node.dropLabelsList #[] (Node.expandOne done bound #[] n).toList
  | .draw g fl st => by simp [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList]
  | .group xf clips alpha kids => by
    simp only [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList,
      Array.push_empty]
    rw [expand_drop_list done bound kids.toList]
  | .use k xf => by
    simp only [Node.dropLabelsOne, Node.expandOne, Array.toList_push, List.nil_append,
      Node.expandList, Array.getElem?_map]
    split
    · cases hb : done[k]? with
      | none => simp [Node.dropLabelsList]
      | some b => simp [Node.dropLabelsList, Node.dropLabelsOne, dropBody]
    · simp [Node.dropLabelsList]
  | .stamp o xf fl st => by
    simp [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList]
  | .image k xf => by
    simp [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList]
  | .label l => by
    simp [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList]
  | .words w => by
    simp [Node.dropLabelsOne, Node.expandOne, Node.expandList, Node.dropLabelsList]

private theorem expand_drop_list {L : Type} (done : Array (Array (Node L))) (bound : Nat) :
    ∀ xs : List (Node L),
      Node.expandList (done.map dropBody) bound #[] (Node.dropLabelsList #[] xs).toList =
        Node.dropLabelsList #[] (Node.expandList done bound #[] xs).toList
  | [] => by simp [Node.dropLabelsList, Node.expandList]
  | n :: rest => by
    simp only [Node.dropLabelsList, Node.expandList]
    rw [Node.dropLabelsList_acc (Node.dropLabelsOne #[] n) rest, Array.toList_append,
      expandList_append, expand_drop_one done bound n, expand_drop_list done bound rest,
      Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest, Array.toList_append,
      dropLabelsList_append]

end


private theorem bodies_drop {L : Type} (fig : Figure L) :
    fig.dropLabels.bodies = fig.bodies.map dropBody := by
  unfold Figure.bodies Figure.dropLabels
  simp only
  rw [Array.foldl_map]
  suffices h : ∀ (l : List (Array (Node L))) (done : Array (Array (Node L))),
      l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] (Node.dropLabelsList #[] sym.toList).toList))
        (done.map dropBody) =
      (l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] sym.toList)) done).map dropBody by
    have := h fig.symbols.toList #[]
    simpa [Array.foldl_toList] using this
  intro l
  induction l with
  | nil => intro done; rfl
  | cons sym rest ih =>
    intro done
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Array.size_map, expand_drop_list done done.size sym.toList]
    simp [dropBody, Array.map_push]

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

/-- **Taking a figure's labels out moves no mark** (`_id`): a picture's ink
on the page — its figure with the labels the page sets as lines — paints
exactly what the whole figure paints. -/
public theorem Figure.dropLabels_marks_id {L : Type} (fig : Figure L) :
    fig.dropLabels.marks = fig.marks := by
  unfold Figure.marks Figure.expanded
  rw [bodies_drop, Array.size_map]
  have h := expand_drop_list fig.bodies fig.bodies.size fig.nodes.toList
  simp only [Figure.dropLabels] at h ⊢
  rw [h, marks_drop_list]

/-- **The two artifacts paint one figure** (`_agree`): the PDF's operators
read with PDF's meaning and the SVG's typed tree read with SVG's meaning
are the same marks, whatever the figure, the placements and the resource
naming — because each is the figure's (`GfxPdf.marks_projects`,
`GfxSvg.marks_projects`). The invariant whose absence let a picture's
rectangle fills paint first on one page and in order on the other, an
edge's joins become caps in one, a zero width disappear and a corner bevel
there: each of those is a pair of readings that differ. Ink only; labels
are each backend's own text. -/
public theorem backend_marks_agree {L : Type} (ix : GfxPdf.Request → Nat)
    (labelOps : GfxPdf.Frame → L → Array Pdf.ContentOp)
    (hl : ∀ fr l rs acc, GfxPdf.readList rs acc (labelOps fr l).toList = acc)
    (labelEl : GfxSvg.SFrame → L → Html.Node) (rasters : Array GfxSvg.RasterRef)
    (pdfPlace svgPlace : Iso) (fig : Figure L) :
    GfxPdf.readMarks pdfPlace (GfxPdf.emit ix labelOps pdfPlace fig) =
      GfxSvg.readMarks svgPlace (GfxSvg.tree labelEl rasters svgPlace fig) :=
  (GfxPdf.marks_projects ix labelOps hl pdfPlace fig).trans
    (GfxSvg.marks_projects labelEl rasters svgPlace fig).symm

/-- **A picture's PDF ink and its SVG paint the same marks** (`_agree`): the
page's ink (the lowered picture without its labels, `Layout.pictureInk`)
under any placement, and the HTML's typed tree of the whole lowered picture
(`HtmlDoc.pictureTree`), read back as one list. -/
public theorem picture_marks_agree (ix : GfxPdf.Request → Nat) (pdfPlace svgPlace : Iso)
    (labelEl : GfxSvg.SFrame → LabelSpec → Html.Node) (box : Box) (pic : Ir.Pic.Picture) :
    GfxPdf.readMarks pdfPlace
        (GfxPdf.emit ix (fun _ e => nomatch e) pdfPlace (ofPictureIn box pic).dropLabels) =
      GfxSvg.readMarks svgPlace (GfxSvg.tree labelEl #[] svgPlace (ofPictureIn box pic)) := by
  rw [GfxPdf.marks_projects ix _ (fun _ e => nomatch e) pdfPlace _, Figure.dropLabels_marks_id,
    GfxSvg.marks_projects]

/-! ## What a figure says survives a repaint and the print grid -/

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

/-! ## Expanding commutes with repainting and the print grid -/

private def recolorBody {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) (b : Array (Node L)) :
    Array (Node L) := Node.recolorList f fl #[] b.toList

private def quantizeBody {L : Type} (ql : L → L) (b : Array (Node L)) : Array (Node L) :=
  Node.quantizeList ql #[] b.toList

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

mutual

private theorem expand_recolor_one {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (done : Array (Array (Node L))) (bound : Nat) :
    ∀ n : Node L,
      Node.expandOne (done.map (recolorBody f fl)) bound #[] (Node.recolorOne f fl n) =
        Node.recolorList f fl #[] (Node.expandOne done bound #[] n).toList
  | .draw g fill st => by simp [Node.recolorOne, Node.expandOne, Node.recolorList]
  | .group xf clips alpha kids => by
    simp only [Node.recolorOne, Node.expandOne, Node.recolorList, Array.push_empty]
    rw [expand_recolor_list f fl done bound kids.toList]
  | .use k xf => by
    simp only [Node.recolorOne, Node.expandOne, Array.getElem?_map]
    split
    · cases hb : done[k]? with
      | none => simp [Node.recolorList]
      | some b => simp [Node.recolorList, Node.recolorOne, recolorBody]
    · simp [Node.recolorList]
  | .stamp o xf fill st => by simp [Node.recolorOne, Node.expandOne, Node.recolorList]
  | .image k xf => by simp [Node.recolorOne, Node.expandOne, Node.recolorList]
  | .label l => by simp [Node.recolorOne, Node.expandOne, Node.recolorList]
  | .words w => by simp [Node.recolorOne, Node.expandOne, Node.recolorList]

private theorem expand_recolor_list {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L)
    (done : Array (Array (Node L))) (bound : Nat) :
    ∀ xs : List (Node L),
      Node.expandList (done.map (recolorBody f fl)) bound #[] (Node.recolorList f fl #[] xs).toList =
        Node.recolorList f fl #[] (Node.expandList done bound #[] xs).toList
  | [] => by simp [Node.recolorList, Node.expandList]
  | n :: rest => by
    simp only [Node.recolorList, Node.expandList]
    rw [Node.recolorList_acc, Array.toList_append, expandList_append]
    simp only [Array.toList_push, List.nil_append, Node.expandList]
    rw [Node.expandList_acc, Array.empty_append, expand_recolor_one f fl done bound n,
      expand_recolor_list f fl done bound rest,
      Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest, Array.toList_append,
      recolorList_append]

end

mutual

private theorem expand_quantize_one {L : Type} (ql : L → L) (done : Array (Array (Node L)))
    (bound : Nat) :
    ∀ n : Node L,
      Node.expandOne (done.map (quantizeBody ql)) bound #[] (Node.quantizeOne ql n) =
        Node.quantizeList ql #[] (Node.expandOne done bound #[] n).toList
  | .draw g fill st => by simp [Node.quantizeOne, Node.expandOne, Node.quantizeList]
  | .group xf clips alpha kids => by
    simp only [Node.quantizeOne, Node.expandOne, Node.quantizeList, Array.push_empty]
    rw [expand_quantize_list ql done bound kids.toList]
  | .use k xf => by
    simp only [Node.quantizeOne, Node.expandOne, Array.getElem?_map]
    split
    · cases hb : done[k]? with
      | none => simp [Node.quantizeList]
      | some b => simp [Node.quantizeList, Node.quantizeOne, quantizeBody]
    · simp [Node.quantizeList]
  | .stamp o xf fill st => by simp [Node.quantizeOne, Node.expandOne, Node.quantizeList]
  | .image k xf => by simp [Node.quantizeOne, Node.expandOne, Node.quantizeList]
  | .label l => by simp [Node.quantizeOne, Node.expandOne, Node.quantizeList]
  | .words w => by simp [Node.quantizeOne, Node.expandOne, Node.quantizeList]

private theorem expand_quantize_list {L : Type} (ql : L → L) (done : Array (Array (Node L)))
    (bound : Nat) :
    ∀ xs : List (Node L),
      Node.expandList (done.map (quantizeBody ql)) bound #[] (Node.quantizeList ql #[] xs).toList =
        Node.quantizeList ql #[] (Node.expandList done bound #[] xs).toList
  | [] => by simp [Node.quantizeList, Node.expandList]
  | n :: rest => by
    simp only [Node.quantizeList, Node.expandList]
    rw [Node.quantizeList_acc, Array.toList_append, expandList_append]
    simp only [Array.toList_push, List.nil_append, Node.expandList]
    rw [Node.expandList_acc, Array.empty_append, expand_quantize_one ql done bound n,
      expand_quantize_list ql done bound rest,
      Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest, Array.toList_append,
      quantizeList_append']

end

private theorem bodies_recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) (fig : Figure L) :
    (fig.recolor f fl).bodies = fig.bodies.map (recolorBody f fl) := by
  unfold Figure.bodies Figure.recolor
  simp only
  rw [Array.foldl_map]
  suffices h : ∀ (l : List (Array (Node L))) (done : Array (Array (Node L))),
      l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] (Node.recolorList f fl #[] sym.toList).toList))
        (done.map (recolorBody f fl)) =
      (l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] sym.toList)) done).map (recolorBody f fl) by
    have := h fig.symbols.toList #[]
    simpa [Array.foldl_toList] using this
  intro l
  induction l with
  | nil => intro done; rfl
  | cons sym rest ih =>
    intro done
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Array.size_map, expand_recolor_list f fl done done.size sym.toList]
    simp [recolorBody, Array.map_push]

private theorem bodies_quantize {L : Type} (ql : L → L) (fig : Figure L) :
    (fig.quantize ql).bodies = fig.bodies.map (quantizeBody ql) := by
  unfold Figure.bodies Figure.quantize
  simp only
  rw [Array.foldl_map]
  suffices h : ∀ (l : List (Array (Node L))) (done : Array (Array (Node L))),
      l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] (Node.quantizeList ql #[] sym.toList).toList))
        (done.map (quantizeBody ql)) =
      (l.foldl (fun d (sym : Array (Node L)) =>
          d.push (Node.expandList d d.size #[] sym.toList)) done).map (quantizeBody ql) by
    have := h fig.symbols.toList #[]
    simpa [Array.foldl_toList] using this
  intro l
  induction l with
  | nil => intro done; rfl
  | cons sym rest ih =>
    intro done
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Array.size_map, expand_quantize_list ql done done.size sym.toList]
    simp [quantizeBody, Array.map_push]

/-- A repainted figure's expansion is its expansion repainted. -/
private theorem expanded_recolor {L : Type} (f : Ir.Color → Ir.Color) (fl : L → L) (fig : Figure L) :
    (fig.recolor f fl).expanded = Node.recolorList f fl #[] fig.expanded.toList := by
  unfold Figure.expanded
  rw [bodies_recolor, Array.size_map]
  exact expand_recolor_list f fl fig.bodies fig.bodies.size fig.nodes.toList

/-- A quantized figure's expansion is its expansion quantized. -/
private theorem expanded_quantize {L : Type} (ql : L → L) (fig : Figure L) :
    (fig.quantize ql).expanded = Node.quantizeList ql #[] fig.expanded.toList := by
  unfold Figure.expanded
  rw [bodies_quantize, Array.size_map]
  exact expand_quantize_list ql fig.bodies fig.bodies.size fig.nodes.toList

/-- **What a figure says survives a repaint and the print grid** (`_text`):
dimming a figure under an overlay cover and quantizing it to the grid both
emitters print keep its words — a symbol's, read through each use, included
— given label rewrites that keep each label's text: the census a picture's
alternative text and the figure's text layer read. -/
public theorem Figure.said_text {L : Type} (text : L → String) (f : Ir.Color → Ir.Color)
    (fl ql : L → L) (hfl : ∀ l, text (fl l) = text l) (hql : ∀ l, text (ql l) = text l) :
    Ir.Conserves (Figure.said text) (Figure.recolor f fl) ∧
      Ir.Conserves (Figure.said text) (Figure.quantize ql) := by
  refine ⟨fun fig => ?_, fun fig => ?_⟩
  · simp only [Figure.said]
    rw [expanded_recolor, words_recolor_list text f fl hfl]
  · simp only [Figure.said]
    rw [expanded_quantize, words_quantize_list text ql hql]

end LeanTex.Core.Gfx
