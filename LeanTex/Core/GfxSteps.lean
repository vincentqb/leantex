module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxAffine

/-!
# Labels among a figure's ink

The facts about a figure's steps — its marks with its labels in their
places (`Figure.steps`) — both artifacts' readers and the picture lowering
rest on: a figure's steps are its nodes', and relabelling a figure moves no
mark and no label's place.
-/

namespace LeanTex.Core.Gfx

/-- A list's flattening reads each element through the function it is given,
so two functions that agree on the list's elements flatten it alike. -/
public theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun a' h' => h a' (List.mem_cons_of_mem _ h')]

/-! ## Relabelling moves no mark and no label's place -/

public theorem Node.mapLabelsList_map {L L' : Type} (f : L → L') (acc : Array (Node L'))
    (xs : List (Node L)) :
    Node.mapLabelsList f acc xs = acc ++ (xs.map (Node.mapLabelsOne f)).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.mapLabelsList]
  | cons x rest ih => simp [Node.mapLabelsList, ih]

mutual

/-- Relabelling commutes with expansion against no symbols. -/
public theorem Node.expandOne_mapLabels {L L' : Type} (f : L → L') :
    ∀ n : Node L,
      Node.expandOne (#[] : Array (Array (Node L'))) 0 #[] (n.mapLabelsOne f) =
        (Node.expandOne (#[] : Array (Array (Node L))) 0 #[] n).map (Node.mapLabelsOne f)
  | .draw g fl st => by simp [Node.mapLabelsOne, Node.expandOne]
  | .group xf clips alpha kids => by
    simp only [Node.mapLabelsOne, Node.expandOne, Node.mapLabelsList_map, Array.toList_append,
      List.nil_append, Array.push_empty, Array.map_singleton]
    rw [Node.expandList_mapLabels f kids.toList]
    have h : ∀ a : Array (Node L), (a.toList.map (Node.mapLabelsOne f)).toArray =
        a.map (Node.mapLabelsOne f) := fun a => by
      apply Array.toList_inj.mp
      simp
    simp [h]
  | .use k xf => by simp [Node.mapLabelsOne, Node.expandOne]
  | .stamp o xf fl st => by simp [Node.mapLabelsOne, Node.expandOne]
  | .image k xf => by simp [Node.mapLabelsOne, Node.expandOne]
  | .label l => by simp [Node.mapLabelsOne, Node.expandOne]
  | .words w => by simp [Node.mapLabelsOne, Node.expandOne]

public theorem Node.expandList_mapLabels {L L' : Type} (f : L → L') :
    ∀ xs : List (Node L),
      Node.expandList (#[] : Array (Array (Node L'))) 0 #[] (xs.map (Node.mapLabelsOne f)) =
        (Node.expandList (#[] : Array (Array (Node L))) 0 #[] xs).map (Node.mapLabelsOne f)
  | [] => by simp [Node.expandList]
  | n :: rest => by
    simp only [List.map_cons, Node.expandList]
    rw [Node.expandList_acc, Node.expandList_acc (#[] : Array (Array (Node L))),
      Node.expandOne_mapLabels f n, Node.expandList_mapLabels f rest, Array.map_append]

end

mutual

/-- Relabelling paints the same marks. -/
public theorem Node.marksOne_mapLabels {L L' : Type} (f : L → L')
    (outlines : Array (Array Subpath)) :
    ∀ (n : Node L) (cx : Ctx) (acc : Array Mark),
      Node.marksOne outlines cx acc (n.mapLabelsOne f) = Node.marksOne outlines cx acc n
  | .draw g fl st, _, _ => rfl
  | .group xf clips alpha kids, cx, acc => by
    simp only [Node.mapLabelsOne, Node.marksOne, Node.mapLabelsList_map, Array.toList_append,
      List.nil_append]
    exact Node.marksList_mapLabels f outlines kids.toList _ acc
  | .use k xf, _, _ => rfl
  | .stamp o xf fl st, _, _ => rfl
  | .image k xf, _, _ => rfl
  | .label l, _, _ => rfl
  | .words w, _, _ => rfl

public theorem Node.marksList_mapLabels {L L' : Type} (f : L → L')
    (outlines : Array (Array Subpath)) :
    ∀ (xs : List (Node L)) (cx : Ctx) (acc : Array Mark),
      Node.marksList outlines cx acc (xs.map (Node.mapLabelsOne f)) =
        Node.marksList outlines cx acc xs
  | [], _, _ => rfl
  | n :: rest, cx, acc => by
    simp only [List.map_cons, Node.marksList]
    rw [Node.marksOne_mapLabels f outlines n cx acc]
    exact Node.marksList_mapLabels f outlines rest cx _

end

/-- A top-level node that is no label, where labels stand at the top level,
holds none. -/
public theorem Node.labelFree_of_topOk {L : Type} (n : Node L) (h : n.topOk = true)
    (hn : ∀ l, n ≠ .label l) : n.labelFree = true := by
  cases n with
  | label l => exact absurd rfl (hn l)
  | group _ _ _ kids => simpa [Node.topOk, Node.labelFree] using h
  | draw | use | stamp | image | words => rfl

/-- A figure's steps, as the flattening of its nodes'. -/
public theorem Figure.steps_eq {L : Type} (fig : Figure L) :
    fig.steps = (fig.nodes.toList.flatMap fun n => (fig.nodeSteps n).toList).toArray := by
  unfold Figure.steps
  rw [← Array.foldl_toList]
  suffices h : ∀ (xs : List (Node L)) (acc : Array (Step L)),
      xs.foldl (fun acc n => acc ++ fig.nodeSteps n) acc =
        acc ++ (xs.flatMap fun n => (fig.nodeSteps n).toList).toArray by
    simpa using h fig.nodes.toList #[]
  intro xs
  induction xs with
  | nil => intro acc; simp
  | cons n rest ih =>
    intro acc
    simp only [List.foldl_cons, List.flatMap_cons, ih, Array.append_assoc]
    congr 1
    apply Array.toList_inj.mp
    simp

/-- **Relabelling a node moves no step** (`_exact`): in a figure with no
symbols, a top-level node read through `f` steps as the node does, each
label read through `f` — the same marks, each label in its place. -/
public theorem Figure.nodeSteps_mapLabels_exact {L L' : Type} (f : L → L') (fig : Figure L)
    (fig' : Figure L') (ho : fig'.outlines = fig.outlines) (hs : fig.symbols = #[])
    (hs' : fig'.symbols = #[]) (n : Node L) :
    fig'.nodeSteps (n.mapLabelsOne f) = (fig.nodeSteps n).map (Step.mapLabel f) := by
  have hb : fig.bodies = #[] := by simp [Figure.bodies, hs]
  have hb' : fig'.bodies = #[] := by simp [Figure.bodies, hs']
  have marks : ∀ m : Node L,
      Node.marksList fig'.outlines Ctx.root #[]
          (Node.expandOne fig'.bodies fig'.bodies.size #[] (m.mapLabelsOne f)).toList =
        Node.marksList fig.outlines Ctx.root #[]
          (Node.expandOne fig.bodies fig.bodies.size #[] m).toList := by
    intro m
    rw [hb, hb', ho]
    simp only [Array.size_empty]
    rw [Node.expandOne_mapLabels f m, Array.toList_map, Node.marksList_mapLabels]
  have step : ∀ m : Node L, (∀ l, m ≠ .label l) →
      fig'.nodeSteps (m.mapLabelsOne f) =
        (Node.marksList fig.outlines Ctx.root #[]
          (Node.expandOne fig.bodies fig.bodies.size #[] m).toList).map .mark := by
    intro m hm
    rw [← marks m]
    cases m with
    | label l => exact absurd rfl (hm l)
    | draw | group | use | stamp | image | words => rfl
  cases n with
  | label l => simp [Figure.nodeSteps, Node.mapLabelsOne, Step.mapLabel]
  | draw | group | use | stamp | image | words =>
    rw [step _ (fun l h => by cases h)]
    simp [Figure.nodeSteps, Array.map_map, Function.comp_def, Step.mapLabel]

end LeanTex.Core.Gfx
