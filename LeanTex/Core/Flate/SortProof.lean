module

import all Init.Data.Array.QSort.Basic
public import Init.Data.Vector.Perm

namespace LeanTex.Core.Flate

private theorem partitionLoop_perm {α : Type} {n : Nat}
    (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]
    simp only [dite_eq_left h, ite_eq_left hlt]
    exact ih.trans (Vector.swap_perm _ _)
  | case2 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]
    simp only [dite_eq_left h, ite_eq_right hlt]
    exact ih
  | case3 as i k ilo ik w h =>
    rw [Array.qpartition.loop]
    simp only [dite_eq_right h]
    exact Vector.swap_perm _ _

private theorem partition_perm {α : Type} {n : Nat}
    (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.Perm as := by
  let mid := (lo + hi) / 2
  have hm : mid < n := by dsimp [mid]; omega
  let a := if lt as[mid] as[lo] then as.swap lo mid else as
  have ha : a.Perm as := by
    dsimp [a]
    split
    · exact Vector.swap_perm _ _
    · exact Vector.Perm.refl _
  let b := if lt a[hi] a[lo] then a.swap lo hi else a
  have hb : b.Perm a := by
    dsimp [b]
    split
    · exact Vector.swap_perm _ _
    · exact Vector.Perm.refl _
  let c := if lt b[mid] b[hi] then b.swap mid hi else b
  have hc : c.Perm b := by
    dsimp [c]
    split
    · exact Vector.swap_perm _ _
    · exact Vector.Perm.refl _
  exact (partitionLoop_perm lt lo hi hhi c[hi] c lo lo (Nat.le_refl _)
    (Nat.le_refl _) w).trans (hc.trans (hb.trans ha))

private theorem sort_perm {α : Type} {n : Nat}
    (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).Perm as := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hm next heq hstop =>
    rw [Array.qsort.sort]
    simp only [dite_eq_left h, heq, dite_eq_left hstop]
    have hp := partition_perm as lt lo hi w hlo hhi
    simpa only [heq] using hp
  | case2 as lo hi w hlo hhi h mid hm next heq hmore ih₁ _ ih₂ =>
    rw [Array.qsort.sort]
    simp only [dite_eq_left h, heq, dite_eq_right hmore]
    have hp := partition_perm as lt lo hi w hlo hhi
    simp only [heq] at hp
    exact ih₂.trans (ih₁.trans hp)
  | case3 as lo hi w hlo hhi h =>
    rw [Array.qsort.sort]
    simp only [dite_eq_right h]
    exact Vector.Perm.refl _

/-- The encoder's existing in-place quicksort only permutes symbols.
The proof follows the actual partition swaps and recursive calls; it
requires no comparator law and changes no runtime sorting algorithm. -/
public theorem qsort_perm_exact {α : Type} (as : Array α) (lt : α → α → Bool)
    (lo := 0) (hi := as.size - 1) : (as.qsort lt lo hi).Perm as := by
  unfold Array.qsort
  split
  · exact Array.Perm.refl _
  · exact Vector.perm_iff_toArray_perm.mp (sort_perm lt _ _ _ _ _ _)

end LeanTex.Core.Flate
