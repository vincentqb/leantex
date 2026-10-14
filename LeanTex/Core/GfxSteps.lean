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

/-- A node list map that keeps every use and group, their transforms by `xf` and clips by `cl`. -/
public structure KeepsUses {L L' : Type} (M : List (Node L) → Array (Node L')) (xf : Affine → Affine)
    (cl : Array Clip → Array Clip) : Prop where
  nil : M [] = #[]
  cons : ∀ n rest, M [n] ++ M rest = M (n :: rest)
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

public theorem KeepsUses.append (h : KeepsUses M xf cl) (a b : List (Node L)) :
    M a ++ M b = M (a ++ b) := by
  induction a with
  | nil => simp [h.nil]
  | cons n rest ih =>
    rw [List.cons_append, ← h.cons n (rest ++ b), ← h.cons n rest, Array.append_assoc, ih]

mutual

public theorem expand_keeps_one (h : KeepsUses M xf cl) (done : Array (Array (Node L))) (bound : Nat) :
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

public theorem expand_keeps_list (h : KeepsUses M xf cl) (done : Array (Array (Node L))) (bound : Nat) :
    ∀ xs : List (Node L),
      Node.expandList (done.map (M ·.toList)) bound #[] (M xs).toList =
        M (Node.expandList done bound #[] xs).toList
  | [] => by simp [h.nil, Node.expandList]
  | n :: rest => by
    rw [show n :: rest = [n] ++ rest from rfl, ← h.append _ _, Array.toList_append, expandList_append,
      expand_keeps_one h done bound n, expand_keeps_list h done bound rest, List.singleton_append,
      Node.expandList, Node.expandList_acc done bound (Node.expandOne done bound #[] n) rest,
      Array.toList_append, ← h.append _ _]

end

/-- A figure whose nodes and symbols are mapped by `M` expands to the mapped expansion. -/
public theorem expanded_keeps (h : KeepsUses M xf cl) (fig : Figure L) (fig' : Figure L')
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

private theorem mapLabelsKeeps {L L' : Type} (f : L → L') :
    KeepsUses (Node.mapLabelsList f #[]) id id where
  nil := rfl
  cons n rest := by simp [Node.mapLabelsList_map]
  group _ _ _ _ := rfl
  use _ _ := rfl
  noClips := rfl
  draw _ _ _ _ _ := rfl
  stamp _ _ _ _ _ _ := rfl
  image _ _ _ _ := rfl
  label _ _ _ := rfl
  words _ _ _ := rfl

public theorem Node.expandList_mapLabels {L L' : Type} (f : L → L') (xs : List (Node L)) :
    Node.expandList (#[] : Array (Array (Node L'))) 0 #[] (xs.map (Node.mapLabelsOne f)) =
      (Node.expandList (#[] : Array (Array (Node L))) 0 #[] xs).map (Node.mapLabelsOne f) := by
  have h := expand_keeps_list (mapLabelsKeeps f) #[] 0 xs
  simp only [Array.map_empty, Node.mapLabelsList_map, Array.empty_append] at h
  rw [h]
  apply Array.toList_inj.mp
  simp

public theorem Node.expandOne_mapLabels {L L' : Type} (f : L → L') (n : Node L) :
    Node.expandOne (#[] : Array (Array (Node L'))) 0 #[] (n.mapLabelsOne f) =
      (Node.expandOne (#[] : Array (Array (Node L))) 0 #[] n).map (Node.mapLabelsOne f) := by
  have h := Node.expandList_mapLabels f [n]
  simp only [List.map_cons, List.map_nil, Node.expandList] at h
  rw [Node.expandOne_acc, Node.expandOne_acc (#[] : Array (Array (Node L)))] at h
  simpa using h

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
