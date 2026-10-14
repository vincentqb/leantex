module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxAffine

/-! The facts about a figure's steps that both artifacts' readers and the picture lowering rest on. -/

namespace LeanTex.Core.Gfx

public theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun a' h' => h a' (List.mem_cons_of_mem _ h')]

public theorem Node.mapLabelsList_map {L L' : Type} (f : L → L') (acc : Array (Node L'))
    (xs : List (Node L)) :
    Node.mapLabelsList f acc xs = acc ++ (xs.map (Node.mapLabelsOne f)).toArray := by
  induction xs generalizing acc with
  | nil => simp [Node.mapLabelsList]
  | cons x rest ih => simp [Node.mapLabelsList, ih]

mutual

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

public theorem Node.labelFree_of_topOk {L : Type} (n : Node L) (h : n.topOk = true)
    (hn : ∀ l, n ≠ .label l) : n.labelFree = true := by
  cases n with
  | label l => exact absurd rfl (hn l)
  | group _ _ _ kids => simpa [Node.topOk, Node.labelFree] using h
  | draw | use | stamp | image | words => rfl

public theorem foldl_append_flatMap_exact {α β : Type} (f : α → Array β) (xs : Array α) :
    xs.foldl (fun acc x => acc ++ f x) #[] = (xs.toList.flatMap fun x => (f x).toList).toArray := by
  rw [show xs.foldl (fun acc x => acc ++ f x) #[] = xs.flatMap f from rfl]
  apply Array.toList_inj.mp
  simp

public theorem Figure.steps_eq {L : Type} (fig : Figure L) :
    fig.steps = (fig.nodes.toList.flatMap fun n => (fig.nodeSteps n).toList).toArray :=
  foldl_append_flatMap_exact _ _

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
