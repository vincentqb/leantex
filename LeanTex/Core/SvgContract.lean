module

public import LeanTex.Core.SvgJudge
public import LeanTex.Core.SvgImport
public import LeanTex.Core.Image
public import LeanTex.Core.FigureLoss

/-! The native SVG route's accounting: refused sources and import losses are named, and uses expand within budget. -/

namespace LeanTex.Core.Svg

open LeanTex.Core LeanTex.Core.Gfx

public theorem import_named (t : Xml.Item) (lang : String) (moving : Bool) (src : String)
    (why : FigureLoss.Unconverted) (converted : Bool) (l : Gfx.Loss)
    (h : l ∈ (importTree t lang).fig.losses) :
    ∃ d ∈ FigureLoss.diags (if converted then FigureLoss.svgConvertedDiag moving src
        else FigureLoss.svgLostDiag moving src why) (importTree t lang).fig.losses,
      d.subject = some (FigureLoss.subject "svg" l) :=
  FigureLoss.svgDiags_named moving src why converted _ l h

public theorem viewBox_exact (vb : ViewBox) (vx vy vw vh : Rat) (hw : vb.w ≠ 0) (hh : vb.h ≠ 0) :
    let m := viewMap vb { align := none, slice := false } vx vy vw vh
    m.apply (vb.x * pxSp.toRat, vb.y * pxSp.toRat) = (vx * pxSp.toRat, vy * pxSp.toRat) ∧
      m.apply ((vb.x + vb.w) * pxSp.toRat, (vb.y + vb.h) * pxSp.toRat) =
        ((vx + vw) * pxSp.toRat, (vy + vh) * pxSp.toRat) := by
  simp only [viewMap, viewScale, Affine.apply]
  refine ⟨?_, ?_⟩
  · simp only [Prod.mk.injEq]; constructor <;> grind
  · simp only [Prod.mk.injEq]; constructor <;> grind

public theorem viewBox_meet_between (vb : ViewBox) (al : Align × Align) (vw vh : Rat)
    (hw : 0 < vb.w) (hh : 0 < vb.h) :
    let s := (viewScale vb { align := some al, slice := false } vw vh).1
    vb.w * s ≤ vw ∧ vb.h * s ≤ vh ∧ (vb.w * s = vw ∨ vb.h * s = vh) := by
  have hw0 : vb.w ≠ 0 := fun h => by simp [h] at hw
  have hh0 : vb.h ≠ 0 := fun h => by simp [h] at hh
  have h1 : vb.w * (vw / vb.w) = vw := by rw [Rat.mul_comm]; exact Rat.div_mul_cancel hw0
  have h2 : vb.h * (vh / vb.h) = vh := by rw [Rat.mul_comm]; exact Rat.div_mul_cancel hh0
  simp only [viewScale]
  by_cases hc : vw / vb.w < vh / vb.h
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    refine ⟨by rw [h1]; exact Rat.le_refl, ?_, .inl h1⟩
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hc) (Rat.le_of_lt hh)
    rw [h2] at this
    exact this
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    refine ⟨?_, by rw [h2]; exact Rat.le_refl, .inr h2⟩
    have hle : vh / vb.h ≤ vw / vb.w := by
      exact Rat.not_lt.mp hc
    have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hw)
    rw [h1] at this
    exact this

public theorem length_exact :
    LenUnit.factor .inch = 96 ∧ 72 * LenUnit.factor .pt = LenUnit.factor .inch ∧
    6 * LenUnit.factor .pc = LenUnit.factor .inch ∧
    (254 / 100 : Rat) * LenUnit.factor .cm = LenUnit.factor .inch ∧
    (254 / 10 : Rat) * LenUnit.factor .mm = LenUnit.factor .inch ∧
    LenUnit.factor .pt * pxSp.toRat = (Dim.bp 1).toRat := by decide +kernel

mutual

-- conserves: none — a census of a tree's nodes.
@[expose] public def Node.count : Node Run → Nat
  | .group _ _ _ kids => Node.countList kids.toList + 1
  | .draw _ _ _ => 1
  | .use _ _ => 1
  | .stamp _ _ _ _ => 1
  | .image _ _ => 1
  | .label _ => 1
  | .words _ => 1
@[expose] public def Node.countList : List (Node Run) → Nat
  | [] => 0
  | n :: rest => Node.count n + Node.countList rest
end

private theorem Node.countList_append (a b : List (Node Run)) :
    Node.countList (a ++ b) = Node.countList a + Node.countList b := by
  induction a with
  | nil => simp [Node.countList]
  | cons n rest ih => simp only [List.cons_append, Node.countList, ih]; omega

mutual
private theorem expandOne_acc (done : Array (Array (Node Run))) (bound : Nat) (acc : Array (Node Run)) :
    ∀ n : Node Run, Node.countList (Node.expandOne done bound acc n).toList =
      Node.countList acc.toList + Node.countList (Node.expandOne done bound #[] n).toList
  | .draw _ _ _ => by simp [Node.expandOne, Node.countList_append]
  | .group xf clips alpha kids => by simp [Node.expandOne, Node.countList_append]
  | .use k xf => by
    simp only [Node.expandOne]
    split
    · split <;> simp [Node.countList_append, Node.countList]
    · simp [Node.countList]
  | .stamp _ _ _ _ => by simp [Node.expandOne, Node.countList_append]
  | .image _ _ => by simp [Node.expandOne, Node.countList_append]
  | .label _ => by simp [Node.expandOne, Node.countList_append]
  | .words _ => by simp [Node.expandOne, Node.countList_append]
end

private theorem expandList_acc (done : Array (Array (Node Run))) (bound : Nat) :
    ∀ (xs : List (Node Run)) (acc : Array (Node Run)),
      Node.countList (Node.expandList done bound acc xs).toList =
        Node.countList acc.toList + Node.countList (Node.expandList done bound #[] xs).toList
  | [], acc => by simp [Node.expandList, Node.countList]
  | n :: rest, acc => by
    simp only [Node.expandList]
    rw [expandList_acc done bound rest (Node.expandOne done bound acc n),
      expandList_acc done bound rest (Node.expandOne done bound #[] n), expandOne_acc]
    omega

mutual
private theorem expandOne_none : ∀ n : Node Run,
    Node.countList (Node.expandOne #[] 0 #[] n).toList ≤ Node.count n
  | .draw _ _ _ => by simp [Node.expandOne, Node.countList, Node.count]
  | .group xf clips alpha kids => by
    simp only [Node.expandOne, Array.toList_push, List.nil_append,
      Node.countList, Node.count]
    have := expandList_none kids.toList
    omega
  | .use k xf => by simp [Node.expandOne, Node.countList, Node.count]
  | .stamp _ _ _ _ => by simp [Node.expandOne, Node.countList, Node.count]
  | .image _ _ => by simp [Node.expandOne, Node.countList, Node.count]
  | .label _ => by simp [Node.expandOne, Node.countList, Node.count]
  | .words _ => by simp [Node.expandOne, Node.countList, Node.count]
private theorem expandList_none : ∀ xs : List (Node Run),
    Node.countList (Node.expandList #[] 0 #[] xs).toList ≤ Node.countList xs
  | [] => by simp [Node.expandList, Node.countList]
  | n :: rest => by
    simp only [Node.expandList]
    rw [expandList_acc]
    have := expandOne_none n
    have := expandList_none rest
    simp only [Node.countList]
    omega
end

private def SizesCover (cap : Nat) (done : Array (Array (Node Run))) (sizes : Array Nat) : Prop :=
  ∀ k, k < done.size → min cap (Node.countList (done[k]?.getD #[]).toList) ≤ sizes[k]?.getD 0

mutual
private theorem expandedOne_covers (cap : Nat) (done : Array (Array (Node Run))) (sizes : Array Nat)
    (bound : Nat) (hb : bound ≤ done.size) (hc : SizesCover cap done sizes) :
    ∀ (n : Node Run) (a : Nat),
      min cap (a + Node.countList (Node.expandOne done bound #[] n).toList) ≤ expandedOne sizes cap a n
  | .draw _ _ _, a => by simp [Node.expandOne, Node.countList, Node.count, expandedOne]
  | .group xf clips alpha kids, a => by
    simp only [Node.expandOne, Array.toList_push, List.nil_append,
      Node.countList, Node.count, expandedOne]
    have := expandedList_covers cap done sizes bound hb hc kids.toList (min cap (a + 1))
    omega
  | .use k xf, a => by
    simp only [Node.expandOne, expandedOne]
    split
    · next hk =>
      have hd := hc k (by omega)
      split
      · next body hbody =>
        simp only [hbody, Option.getD_some] at hd
        simp only [Array.toList_push, List.nil_append, Node.countList,
          Node.count]
        omega
      · simp [Node.countList]; omega
    · simp [Node.countList]; omega
  | .stamp _ _ _ _, a => by simp [Node.expandOne, Node.countList, Node.count, expandedOne]
  | .image _ _, a => by simp [Node.expandOne, Node.countList, Node.count, expandedOne]
  | .label _, a => by simp [Node.expandOne, Node.countList, Node.count, expandedOne]
  | .words _, a => by simp [Node.expandOne, Node.countList, Node.count, expandedOne]
private theorem expandedList_covers (cap : Nat) (done : Array (Array (Node Run))) (sizes : Array Nat)
    (bound : Nat) (hb : bound ≤ done.size) (hc : SizesCover cap done sizes) :
    ∀ (xs : List (Node Run)) (a : Nat),
      min cap (a + Node.countList (Node.expandList done bound #[] xs).toList) ≤ expandedList sizes cap a xs
  | [], a => by simp [Node.expandList, Node.countList, expandedList]; omega
  | n :: rest, a => by
    simp only [Node.expandList, expandedList]
    rw [expandList_acc]
    have h1 := expandedOne_covers cap done sizes bound hb hc n a
    have h2 := expandedList_covers cap done sizes bound hb hc rest (expandedOne sizes cap a n)
    omega
end

/-- A figure's symbol bodies, expanded in order (`Figure.bodies`). -/
@[expose] public def bodiesOf (syms : Array (Array (Node Run))) : Array (Array (Node Run)) :=
  syms.foldl (fun done sym => done.push (Node.expandList done done.size #[] sym.toList)) #[]

private theorem fold_cover (cap : Nat) : ∀ (syms : List (Array (Node Run))) (done : Array (Array (Node Run)))
    (sizes : Array Nat), SizesCover cap done sizes → done.size = sizes.size →
    SizesCover cap (syms.foldl (fun done sym => done.push (Node.expandList done done.size #[] sym.toList)) done)
      (syms.foldl (fun acc b => acc.push (expandedList acc cap 0 b.toList)) sizes) ∧
    (syms.foldl (fun done sym => done.push (Node.expandList done done.size #[] sym.toList)) done).size =
      (syms.foldl (fun acc b => acc.push (expandedList acc cap 0 b.toList)) sizes).size
  | [], done, sizes, h, hs => ⟨h, hs⟩
  | sym :: rest, done, sizes, h, hs => by
    simp only [List.foldl_cons]
    apply fold_cover cap rest
    · intro k hk
      simp only [Array.size_push] at hk
      simp only [Array.getElem?_push]
      by_cases hlt : k < done.size
      · have hne1 : k ≠ done.size := by omega
        have hne2 : k ≠ sizes.size := by omega
        simp only [hne1, hne2, ↓reduceIte]
        exact h k hlt
      · have hk' : k = done.size := by omega
        simp only [hk', ↓reduceIte, Option.getD_some]
        rw [ite_eq_left hs, Option.getD_some]
        have := expandedList_covers cap done sizes done.size (Nat.le_refl _) h sym.toList 0
        simpa using this
    · simp [hs]

public theorem boundUses_between (bud : Budget) (symbols : Array (Array (Node Run))) (body : Array (Node Run)) :
    let r := boundUses bud symbols body
    Node.countList (Node.expandList (bodiesOf r.1) (bodiesOf r.1).size #[] r.2.1.toList).toList ≤
      max bud.expanded (Node.countList r.2.1.toList) := by
  unfold boundUses
  split
  · have he : bodiesOf #[] = #[] := rfl
    dsimp only
    rw [he]
    have h1 := expandList_none (unuseList #[] body.toList).toList
    simp only [Array.size_empty]
    omega
  · next hover =>
    dsimp only
    have hc := (fold_cover (bud.expanded + 1) symbols.toList #[] #[] (by intro k hk; simp at hk) rfl)
    rw [Array.foldl_toList, Array.foldl_toList] at hc
    have := expandedList_covers (bud.expanded + 1) (bodiesOf symbols) _ (bodiesOf symbols).size
      (Nat.le_refl _) hc.1 body.toList 0
    simp only [Nat.zero_add] at this
    have hE : expandedSize symbols (bud.expanded + 1) body =
        expandedList (symbols.foldl (fun acc b => acc.push (expandedList acc (bud.expanded + 1) 0 b.toList)) #[])
          (bud.expanded + 1) 0 body.toList := rfl
    rw [hE] at hover
    omega

public theorem expand_between_of (bud : Budget) (symbols : Array (Array (Node Run))) (body : Array (Node Run))
    (fig : Figure Run) (xf : Affine) (a : Alpha)
    (hs : fig.symbols = (boundUses bud symbols body).1)
    (hn : fig.nodes = #[Node.group xf #[] a (boundUses bud symbols body).2.1]) :
    Node.countList fig.expanded.toList ≤ max (bud.expanded + 1) (Node.countList fig.nodes.toList) := by
  have h := boundUses_between bud symbols body
  have hb : fig.bodies = bodiesOf (boundUses bud symbols body).1 := by
    unfold Figure.bodies bodiesOf; rw [hs]
  unfold Figure.expanded
  rw [hb, hn]
  simp only [Node.expandList, Node.expandOne, Array.toList_push, List.nil_append, Node.countList,
    Node.count]
  dsimp only at h
  omega

public theorem expand_between (t : Xml.Item) (lang : String) (bud : Budget) :
    let f := (importTree t lang bud).fig
    Node.countList f.expanded.toList ≤ max (bud.expanded + 1) (Node.countList f.nodes.toList) := by
  obtain ⟨symbols, body, xf, a, hs, hn⟩ := importTree_shape t lang bud
  exact expand_between_of bud symbols body _ xf a hs hn

end LeanTex.Core.Svg
