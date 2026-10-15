module

public import LeanTex.Core.Xml
import LeanTex.Core.Loop

/-! The XML reader's budget contract: an accepted document lies within its depth, node and text budgets. -/

namespace LeanTex.Core.Xml

mutual

-- conserves: none — a measure of a tree's nesting.
@[expose] public def Node.depth : Node → Nat
  | .elem _ _ kids => Node.depthList kids.toList + 1
  | .text _ => 0
@[expose] public def Node.depthList : List Node → Nat
  | [] => 0
  | n :: rest => max (Node.depth n) (Node.depthList rest)
end

mutual

-- conserves: none — a census of a tree's nodes.
@[expose] public def Node.size : Node → Nat
  | .elem _ _ kids => Node.sizeList kids.toList + 1
  | .text _ => 1
@[expose] public def Node.sizeList : List Node → Nat
  | [] => 0
  | n :: rest => Node.size n + Node.sizeList rest
end

private theorem Node.depthList_append (a b : List Node) :
    Node.depthList (a ++ b) = max (Node.depthList a) (Node.depthList b) := by
  induction a with
  | nil => simp [Node.depthList]
  | cons n rest ih => simp only [List.cons_append, Node.depthList, ih]; omega

private theorem Node.sizeList_append (a b : List Node) :
    Node.sizeList (a ++ b) = Node.sizeList a + Node.sizeList b := by
  induction a with
  | nil => simp [Node.sizeList]
  | cons n rest ih => simp only [List.cons_append, Node.sizeList, ih]; omega

private theorem Node.depthList_le (l : List Node) (D : Nat) (h : ∀ k ∈ l, k.depth ≤ D) : Node.depthList l ≤ D := by
  induction l with
  | nil => simp [Node.depthList]
  | cons n rest ih =>
    simp only [Node.depthList]
    have := h n (by simp)
    have := ih (fun k hk => h k (by simp [hk]))
    omega

private def Frame.size (f : Frame) : Nat := Node.sizeList f.kids.toList + (if f.text.isEmpty then 0 else 1) + 1

private def framesSize : List Frame → Nat
  | [] => 0
  | f :: rest => f.size + framesSize rest

private theorem framesSize_append (a b : List Frame) : framesSize (a ++ b) = framesSize a + framesSize b := by
  induction a with
  | nil => simp [framesSize]
  | cons f rest ih => simp only [List.cons_append, framesSize, ih]; omega

private def State.total (s : State) : Nat := framesSize s.stack.toList + (s.root.map Node.size).getD 0

private def framesFit (D : Nat) : Nat → List Frame → Prop
  | _, [] => True
  | i, f :: rest => (∀ k ∈ f.kids.toList, k.depth + i + 1 ≤ D) ∧ framesFit D (i + 1) rest

private theorem framesFit_append (D i : Nat) (l : List Frame) (f : Frame) :
    framesFit D i (l ++ [f]) ↔ framesFit D i l ∧ ∀ k ∈ f.kids.toList, k.depth + (i + l.length) + 1 ≤ D := by
  induction l generalizing i with
  | nil => simp [framesFit]
  | cons g rest ih =>
    simp only [List.cons_append, framesFit, ih, List.length_cons]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun k hk => by have := h3 k hk; omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, fun k hk => by have := h3 k hk; omega⟩

private structure Inv (bud : Budget) (s : State) : Prop where
  depth : s.stack.size ≤ bud.depth
  fit : framesFit bud.depth 0 s.stack.toList
  root : ∀ r, s.root = some r → r.depth ≤ bud.depth
  total : s.total ≤ s.nodes
  nodes : s.nodes ≤ bud.nodes

private theorem back_split {α : Type} (a : Array α) (x : α) (h : a.back? = some x) :
    a.toList = a.pop.toList ++ [x] := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp h
  simp

private theorem Frame.flush_size (f : Frame) : Node.sizeList f.flush.kids.toList + 1 = f.size := by
  unfold Frame.flush Frame.size
  split
  · simp_all
  · simp_all [Node.sizeList_append, Node.size, Node.sizeList]

private theorem Frame.flush_text_empty (f : Frame) : f.flush.text.isEmpty := by
  unfold Frame.flush; split <;> simp_all

private theorem Frame.flush_kids (f : Frame) (D d : Nat) (hD : d + 1 ≤ D) (h : ∀ k ∈ f.kids.toList, k.depth + d + 1 ≤ D) :
    ∀ k ∈ f.flush.kids.toList, k.depth + d + 1 ≤ D := by
  unfold Frame.flush
  split
  · exact h
  · intro k hk
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact h k hk
    · simp [Node.depth]; omega

private theorem Frame.close_size (f : Frame) : f.close.size = f.size := by
  unfold Frame.close
  simp only [Node.size]
  exact Frame.flush_size f

private theorem Frame.close_depth (f : Frame) (D d : Nat) (hD : d + 1 ≤ D) (h : ∀ k ∈ f.kids.toList, k.depth + d + 1 ≤ D) :
    f.close.depth + d ≤ D := by
  unfold Frame.close
  simp only [Node.depth]
  have := Node.depthList_le f.flush.kids.toList (D - d - 1)
    (fun k hk => by have := Frame.flush_kids f D d hD h k hk; omega)
  omega

private theorem State.chars_inv (bud : Budget) (s : State) (t : String) (h : Inv bud s) :
    (s.chars t).stack.size ≤ bud.depth ∧ framesFit bud.depth 0 (s.chars t).stack.toList ∧
      (∀ r, (s.chars t).root = some r → r.depth ≤ bud.depth) ∧ (s.chars t).total ≤ s.total + 1 := by
  unfold State.chars
  split
  · next f hb =>
    have hsplit := back_split s.stack f hb
    refine ⟨?_, ?_, h.root, ?_⟩
    · show (s.stack.pop.push _).size ≤ bud.depth
      have hne : s.stack.size ≠ 0 := by
        intro h0; have := congrArg List.length hsplit; simp [h0] at this
      rw [Array.size_push, Array.size_pop]; have := h.depth; omega
    · have hfit := h.fit
      rw [hsplit, framesFit_append] at hfit
      show framesFit bud.depth 0 (s.stack.pop.push _).toList
      rw [Array.toList_push, framesFit_append]
      exact ⟨hfit.1, fun k hk => hfit.2 k hk⟩
    · unfold State.total
      show framesSize (s.stack.pop.push _).toList + _ ≤ framesSize s.stack.toList + _ + 1
      rw [Array.toList_push, framesSize_append, hsplit, framesSize_append]
      simp only [framesSize, Frame.size]
      split <;> split <;> omega
  · exact ⟨h.depth, h.fit, h.root, by omega⟩

private theorem State.give_inv (bud : Budget) (s : State) (n : Node) (h : Inv bud s)
    (hn : n.depth + s.stack.size ≤ bud.depth) :
    (s.give n).stack.size ≤ bud.depth ∧ framesFit bud.depth 0 (s.give n).stack.toList ∧
      (∀ r, (s.give n).root = some r → r.depth ≤ bud.depth) ∧ (s.give n).total ≤ s.total + n.size := by
  unfold State.give
  split
  · next f hb =>
    have hsplit := back_split s.stack f hb
    have hlen : s.stack.pop.toList.length + 1 = s.stack.size := by
      have := congrArg List.length hsplit; simp at this ⊢; omega
    have hfit := h.fit
    rw [hsplit, framesFit_append] at hfit
    refine ⟨?_, ?_, h.root, ?_⟩
    · show (s.stack.pop.push _).size ≤ bud.depth
      rw [Array.size_push, Array.size_pop]; have := h.depth; omega
    · show framesFit bud.depth 0 (s.stack.pop.push _).toList
      rw [Array.toList_push, framesFit_append]
      refine ⟨hfit.1, fun k hk => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | rfl
      · have := Frame.flush_kids f bud.depth (0 + s.stack.pop.toList.length)
          (by have := h.depth; omega) hfit.2 k hk
        exact this
      · omega
    · unfold State.total
      show framesSize (s.stack.pop.push _).toList + _ ≤ framesSize s.stack.toList + _ + n.size
      rw [Array.toList_push, framesSize_append, hsplit, framesSize_append]
      have hfs := Frame.flush_size f
      have hte := Frame.flush_text_empty f
      simp only [framesSize, Frame.size, Array.toList_push, Node.sizeList_append, Node.sizeList,
        hte, ↓reduceIte] at hfs ⊢
      omega
  · next hb =>
    have hempty : s.stack.size = 0 := by
      have := Array.back?_eq_none_iff.mp hb
      simp [this]
    refine ⟨h.depth, h.fit, ?_, ?_⟩
    · intro r hr
      simp only [Option.some.injEq] at hr
      subst hr; omega
    · unfold State.total
      have : s.stack.toList = [] := by simp [← Array.length_toList] at hempty; exact List.eq_nil_of_length_eq_zero (by simpa using hempty)
      simp [this, framesSize]

private theorem State.tick_ok (bud : Budget) (s s' : State) (h : s.tick bud = .ok s') :
    s' = { s with nodes := s.nodes + 1 } ∧ s.nodes + 1 ≤ bud.nodes := by
  unfold State.tick at h
  split at h
  · cases h
  · next hn => cases h; exact ⟨rfl, by omega⟩

private theorem State.charsTick_inv (bud : Budget) (s s' : State) (t : String) (h : Inv bud s)
    (ht : (s.chars t).tick bud = .ok s') (p : Nat) : Inv bud { s' with pos := p } := by
  obtain ⟨rfl, hn⟩ := State.tick_ok bud _ _ ht
  obtain ⟨h1, h2, h3, h4⟩ := State.chars_inv bud s t h
  have hnodes : (s.chars t).nodes = s.nodes := by unfold State.chars; split <;> rfl
  have htot : (s.chars t).total ≤ s.total + 1 := h4
  have := h.total
  exact ⟨h1, h2, h3, by simp only [State.total] at htot ⊢; rw [hnodes]; unfold State.total at this; omega,
    by rw [hnodes] at hn ⊢; omega⟩

private theorem State.give_nodes (s : State) (n : Node) : (s.give n).nodes = s.nodes := by
  unfold State.give; split <;> rfl

private theorem State.close_inv (bud : Budget) (s : State) (f : Frame) (h : Inv bud s)
    (hb : s.stack.back? = some f) (p : Nat) :
    Inv bud { (s.popped.give f.close) with pos := p } := by
  have hsplit := back_split s.stack f hb
  have hne : s.stack.size ≠ 0 := by
    intro h0; have := congrArg List.length hsplit; simp [h0] at this
  have hfit := h.fit
  rw [hsplit, framesFit_append] at hfit
  have hlen : s.stack.pop.toList.length = s.stack.size - 1 := by simp
  have hframes : framesSize s.stack.toList = framesSize s.stack.pop.toList + f.size := by
    rw [hsplit, framesSize_append]; simp [framesSize]
  have hptot : s.popped.total + f.size = s.total := by
    unfold State.total State.popped; dsimp only; rw [hframes]; omega
  have hs0 : Inv bud s.popped := by
    refine ⟨?_, hfit.1, h.root, ?_, h.nodes⟩
    · show s.stack.pop.size ≤ bud.depth
      rw [Array.size_pop]; have := h.depth; omega
    · have := h.total
      show s.popped.total ≤ s.nodes
      omega
  have hcd := Frame.close_depth f bud.depth (0 + s.stack.pop.toList.length)
    (by rw [hlen]; have := h.depth; omega) hfit.2
  obtain ⟨g1, g2, g3, g4⟩ := State.give_inv bud s.popped f.close hs0
    (by show f.close.depth + s.stack.pop.size ≤ bud.depth
        rw [Array.size_pop]; rw [hlen] at hcd; omega)
  have hcs := Frame.close_size f
  have hgn := State.give_nodes s.popped f.close
  refine ⟨g1, g2, g3, ?_, ?_⟩
  · show (s.popped.give f.close).total ≤ (s.popped.give f.close).nodes
    rw [hgn]
    have := h.total
    show _ ≤ s.nodes
    omega
  · show (s.popped.give f.close).nodes ≤ bud.nodes
    rw [hgn]; exact h.nodes

private theorem State.push_inv (bud : Budget) (s s' : State) (fr : Frame) (h : Inv bud s)
    (ht : s.tick bud = .ok s') (hk : fr.kids = #[]) (htx : fr.text = "")
    (hd : ¬ (s'.stack.size + 1 > bud.depth)) (p : Nat) :
    Inv bud { s' with stack := s'.stack.push fr, pos := p } := by
  obtain ⟨rfl, hn⟩ := State.tick_ok bud _ _ ht
  refine ⟨?_, ?_, h.root, ?_, hn⟩
  · show (s.stack.push fr).size ≤ bud.depth
    rw [Array.size_push]; simp at hd; omega
  · show framesFit bud.depth 0 (s.stack.push fr).toList
    rw [Array.toList_push, framesFit_append]
    exact ⟨h.fit, by simp [hk]⟩
  · have := h.total
    unfold State.total at this ⊢
    show framesSize (s.stack.push fr).toList + _ ≤ s.nodes + 1
    rw [Array.toList_push, framesSize_append]
    simp [framesSize, Frame.size, hk, htx, Node.sizeList]
    omega

private theorem State.empty_inv (bud : Budget) (s s' : State) (n : Node) (h : Inv bud s)
    (ht : s.tick bud = .ok s') (hn1 : n.depth ≤ 1) (hs1 : n.size = 1)
    (hd : ¬ (s'.stack.size + 1 > bud.depth)) (p : Nat) :
    Inv bud { (s'.give n) with pos := p } := by
  obtain ⟨rfl, hn⟩ := State.tick_ok bud _ _ ht
  have hs' : Inv bud { s with nodes := s.nodes + 1 } :=
    ⟨h.depth, h.fit, h.root, by have := h.total; unfold State.total at this ⊢; simpa using (by omega), hn⟩
  obtain ⟨g1, g2, g3, g4⟩ := State.give_inv bud _ n hs' (by simp at hd ⊢; omega)
  have hgn := State.give_nodes { s with nodes := s.nodes + 1 } n
  refine ⟨g1, g2, g3, ?_, ?_⟩
  · show (State.give _ n).total ≤ (State.give _ n).nodes
    rw [hgn]
    have := h.total
    have : ({ s with nodes := s.nodes + 1 } : State).total = s.total := rfl
    show _ ≤ s.nodes + 1
    omega
  · show (State.give _ n).nodes ≤ bud.nodes
    rw [hgn]; exact hn

private theorem State.chars_none (s : State) (t : String) (hb : s.stack.isEmpty = true) : s.chars t = s := by
  unfold State.chars
  have : s.stack.back? = none := by
    rw [Array.back?_eq_none_iff]; simpa using hb
  rw [this]

private theorem Inv.at (bud : Budget) (s : State) (h : Inv bud s) (p : Nat) : Inv bud (s.at p) :=
  ⟨h.depth, h.fit, h.root, h.total, h.nodes⟩

private theorem endTag_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : endTag bud b s = .ok s') : Inv bud s' := by
  unfold endTag at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · next f hb =>
        split at h
        · cases h
        · cases h
          exact State.close_inv bud s f hs hb _

private theorem markup_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : markup bud b s = .ok s') : Inv bud s' := by
  unfold markup at h
  dsimp only [Except.map] at h
  split at h
  · split at h
    · cases h
    · next p _ => cases h; exact hs.at bud s p
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · next s1 ht => cases h; exact State.charsTick_inv bud s s1 _ hs ht _
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · next p _ => cases h; exact ⟨hs.depth, hs.fit, hs.root, hs.total, hs.nodes⟩
      · cases h

private theorem startTag_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : startTag bud b s = .ok s') : Inv bud s' := by
  unfold startTag at h
  split at h
  · cases h
  · split at h
    · cases h
    · next s1 ht =>
      split at h
      · cases h
      · next name attrs empty j _ =>
        split at h
        · cases h
        · next hd =>
          split at h
          · cases h
            exact State.empty_inv bud s s1 _ hs ht (by simp [Node.depth, Node.depthList])
              (by simp [Node.size, Node.sizeList]) hd _
          · cases h
            exact State.push_inv bud s s1 _ hs ht rfl rfl hd _

private theorem reference_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : reference bud b s = .ok s') : Inv bud s' := by
  unfold reference at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next s1 ht => cases h; exact State.charsTick_inv bud s s1 _ hs ht _

private theorem charData_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : charData bud b s = .ok s') : Inv bud s' := by
  unfold charData at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · split at h
    · next he =>
      split at h
      · cases h
      · cases h
        rw [State.chars_none s _ he]
        exact hs.at bud s _
    · split at h
      · cases h
      · split at h
        · cases h
        · next s1 ht => cases h; exact State.charsTick_inv bud s s1 _ hs ht _

private theorem step_inv (bud : Budget) (b : ByteArray) (s s' : State) (hs : Inv bud s)
    (h : step bud b s = .ok s') : Inv bud s' := by
  unfold step at h
  dsimp only at h
  split at h
  · split at h
    · exact endTag_inv bud b s s' hs h
    · split at h
      · exact markup_inv bud b s s' hs h
      · split at h
        · split at h <;> cases h
        · exact startTag_inv bud b s s' hs h
  · split at h
    · exact reference_inv bud b s s' hs h
    · exact charData_inv bud b s s' hs h

private def Carried (bud : Budget) : Except Refusal State → Prop
  | .ok s => Inv bud s
  | .error _ => True

private theorem run_inv (bud : Budget) (b : ByteArray) (start : Nat) (s : State)
    (h : run bud b start = .ok s) : Inv bud s := by
  have hc : Carried bud (run bud b start) := by
    unfold run
    dsimp only
    refine LeanTex.Core.Loop.forIn_range_inv (Carried bud) _ 0 (b.size + 1) _ ?_ ?_
    · exact ⟨by simp, by simp [framesFit], by simp, by simp [State.total, framesSize], by simp⟩
    · intro i _ _ acc hacc
      cases acc with
      | error e => simp [Carried]
      | ok s0 =>
        simp only [Carried] at hacc
        dsimp only [pure, Id.run]
        split
        · exact hacc
        · split
          · simp [Carried]
          · next s1 hs1 =>
            split
            · simp [Carried]
            · exact step_inv bud b s0 s1 hacc hs1
  rw [h] at hc
  exact hc

mutual

-- conserves: none — a condition on a tree's texts.
@[expose] public def Node.textsWithin (m : Nat) : Node → Prop
  | .elem _ _ kids => Node.textsWithinList m kids.toList
  | .text t => t.utf8ByteSize ≤ m
@[expose] public def Node.textsWithinList (m : Nat) : List Node → Prop
  | [] => True
  | n :: rest => Node.textsWithin m n ∧ Node.textsWithinList m rest
end

private theorem Node.textsWithinList_iff (m : Nat) (l : List Node) :
    Node.textsWithinList m l ↔ ∀ k ∈ l, k.textsWithin m := by
  induction l with
  | nil => simp [Node.textsWithinList]
  | cons n rest ih => simp [Node.textsWithinList, ih]

private def Frame.textsWithin (m : Nat) (f : Frame) : Prop :=
  f.text.utf8ByteSize ≤ m ∧ ∀ k ∈ f.kids.toList, k.textsWithin m

private structure TextInv (bud : Budget) (s : State) : Prop where
  frames : ∀ f ∈ s.stack.toList, f.textsWithin bud.text
  root : ∀ r, s.root = some r → r.textsWithin bud.text

private theorem Frame.flush_texts (m : Nat) (f : Frame) (h : f.textsWithin m) : f.flush.textsWithin m := by
  unfold Frame.flush
  split
  · exact h
  · refine ⟨by simp, ?_⟩
    intro k hk
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact h.2 k hk
    · exact h.1

private theorem Frame.close_texts (m : Nat) (f : Frame) (h : f.textsWithin m) : f.close.textsWithin m := by
  unfold Frame.close
  simp only [Node.textsWithin]
  exact (Node.textsWithinList_iff _ _).mpr (Frame.flush_texts m f h).2

private theorem frames_push (m : Nat) (a : Array Frame) (f g : Frame) (hb : a.back? = some f)
    (h : ∀ x ∈ a.toList, x.textsWithin m) (hg : g.textsWithin m) :
    ∀ x ∈ (a.pop.push g).toList, x.textsWithin m := by
  have hsplit := back_split a f hb
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x (by rw [hsplit]; exact List.mem_append_left _ hx)
  · exact hg

private theorem State.chars_texts (bud : Budget) (s : State) (t : String) (h : TextInv bud s)
    (ht : (s.stack.back?.map fun x => x.text.utf8ByteSize + t.utf8ByteSize).getD 0 ≤ bud.text) :
    TextInv bud (s.chars t) := by
  unfold State.chars
  split
  · next f hb =>
    have hsplit := back_split s.stack f hb
    have hf := h.frames f (by rw [hsplit]; simp)
    rw [hb] at ht
    simp only [Option.map_some, Option.getD_some] at ht
    exact ⟨frames_push _ s.stack f _ hb h.frames ⟨by simp only [String.utf8ByteSize_append]; exact ht, hf.2⟩,
      h.root⟩
  · exact h

private theorem State.give_texts (bud : Budget) (s : State) (n : Node) (h : TextInv bud s)
    (hn : n.textsWithin bud.text) : TextInv bud (s.give n) := by
  unfold State.give
  split
  · next f hb =>
    have hsplit := back_split s.stack f hb
    have hf := Frame.flush_texts _ f (h.frames f (by rw [hsplit]; simp))
    refine ⟨frames_push _ s.stack f _ hb h.frames ⟨hf.1, ?_⟩, h.root⟩
    intro k hk
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact hf.2 k hk
    · exact hn
  · refine ⟨h.frames, ?_⟩
    intro r hr
    simp only [Option.some.injEq] at hr
    subst hr
    exact hn

private theorem State.charsTick_texts (bud : Budget) (s s' : State) (t : String) (h : TextInv bud s)
    (hb : ¬ ((s.stack.back?.map fun x => x.text.utf8ByteSize + t.utf8ByteSize).getD 0 > bud.text))
    (ht : (s.chars t).tick bud = .ok s') (p : Nat) : TextInv bud { s' with pos := p } := by
  obtain ⟨rfl, _⟩ := State.tick_ok bud _ _ ht
  have := State.chars_texts bud s t h (by omega)
  exact ⟨this.frames, this.root⟩

private theorem State.close_texts (bud : Budget) (s : State) (f : Frame) (h : TextInv bud s)
    (hb : s.stack.back? = some f) (p : Nat) : TextInv bud { (s.popped.give f.close) with pos := p } := by
  have hsplit := back_split s.stack f hb
  have hf := h.frames f (by rw [hsplit]; simp)
  have hp : TextInv bud s.popped :=
    ⟨fun x hx => h.frames x (by rw [hsplit]; exact List.mem_append_left _ hx), h.root⟩
  have := State.give_texts bud s.popped f.close hp (Frame.close_texts _ f hf)
  exact ⟨this.frames, this.root⟩

private theorem endTag_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : endTag bud b s = .ok s') : TextInv bud s' := by
  unfold endTag at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · next f hb =>
        split at h
        · cases h
        · cases h
          exact State.close_texts bud s f hs hb _

private theorem markup_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : markup bud b s = .ok s') : TextInv bud s' := by
  unfold markup at h
  dsimp only [Except.map] at h
  split at h
  · split at h
    · cases h
    · next p _ => cases h; exact ⟨hs.frames, hs.root⟩
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · next hb =>
            split at h
            · cases h
            · next s1 ht => cases h; exact State.charsTick_texts bud s s1 _ hs hb ht _
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · next p _ => cases h; exact ⟨hs.frames, hs.root⟩
      · cases h

private theorem startTag_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : startTag bud b s = .ok s') : TextInv bud s' := by
  unfold startTag at h
  split at h
  · cases h
  · split at h
    · cases h
    · next s1 ht =>
      obtain ⟨rfl, _⟩ := State.tick_ok bud _ _ ht
      split at h
      · cases h
      · next name attrs empty j _ =>
        split at h
        · cases h
        · split at h
          · cases h
            have := State.give_texts bud { s with nodes := s.nodes + 1 } (.elem name attrs #[])
              ⟨hs.frames, hs.root⟩ (by simp [Node.textsWithin, Node.textsWithinList])
            exact ⟨this.frames, this.root⟩
          · cases h
            refine ⟨?_, hs.root⟩
            intro x hx
            simp only [State.openAt, Array.toList_push, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hs.frames x hx
            · exact ⟨by simp, by simp⟩

private theorem reference_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : reference bud b s = .ok s') : TextInv bud s' := by
  unfold reference at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · next hb =>
        split at h
        · cases h
        · next s1 ht =>
          cases h
          exact State.charsTick_texts bud s s1 _ hs (by rwa [String.utf8ByteSize_singleton]) ht _

private theorem charData_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : charData bud b s = .ok s') : TextInv bud s' := by
  unfold charData at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · split at h
    · next he =>
      split at h
      · cases h
      · cases h
        rw [State.chars_none s _ he]
        exact ⟨hs.frames, hs.root⟩
    · split at h
      · cases h
      · next hb =>
        split at h
        · cases h
        · next s1 ht => cases h; exact State.charsTick_texts bud s s1 _ hs hb ht _

private theorem step_texts (bud : Budget) (b : ByteArray) (s s' : State) (hs : TextInv bud s)
    (h : step bud b s = .ok s') : TextInv bud s' := by
  unfold step at h
  dsimp only at h
  split at h
  · split at h
    · exact endTag_texts bud b s s' hs h
    · split at h
      · exact markup_texts bud b s s' hs h
      · split at h
        · split at h <;> cases h
        · exact startTag_texts bud b s s' hs h
  · split at h
    · exact reference_texts bud b s s' hs h
    · exact charData_texts bud b s s' hs h

private def CarriedTexts (bud : Budget) : Except Refusal State → Prop
  | .ok s => TextInv bud s
  | .error _ => True

private theorem run_texts (bud : Budget) (b : ByteArray) (start : Nat) (s : State)
    (h : run bud b start = .ok s) : TextInv bud s := by
  have hc : CarriedTexts bud (run bud b start) := by
    unfold run
    dsimp only
    refine LeanTex.Core.Loop.forIn_range_inv (CarriedTexts bud) _ 0 (b.size + 1) _ ?_ ?_
    · exact ⟨by simp, by simp⟩
    · intro i _ _ acc hacc
      cases acc with
      | error e => simp [CarriedTexts]
      | ok s0 =>
        simp only [CarriedTexts] at hacc
        dsimp only [pure, Id.run]
        split
        · exact hacc
        · split
          · simp [CarriedTexts]
          · next s1 hs1 =>
            split
            · simp [CarriedTexts]
            · exact step_texts bud b s0 s1 hacc hs1
  rw [h] at hc
  exact hc

public theorem parseWith_between (bud : Budget) (input : ByteArray) (n : Node)
    (h : parseWith bud input = .ok n) :
    n.depth ≤ bud.depth ∧ n.size ≤ bud.nodes ∧ n.textsWithin bud.text := by
  unfold parseWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · next bs start _ =>
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · next s hs =>
            have hinv := run_inv bud bs start s hs
            have htexts := run_texts bud bs start s hs
            split at h
            · cases h
            · split at h
              · cases h
              · next hempty =>
                split at h
                · next r hr =>
                  cases h
                  refine ⟨hinv.root _ hr, ?_, htexts.root _ hr⟩
                  have ht := hinv.total
                  have hn := hinv.nodes
                  have : s.stack.toList = [] := by simpa using hempty
                  unfold State.total at ht
                  rw [this, hr] at ht
                  simp [framesSize] at ht
                  omega
                · cases h

end LeanTex.Core.Xml
