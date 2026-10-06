module
import all Init.Data.Array.QSort.Basic
import Init.Data.Vector.Perm
import Init.Data.Vector.Lemmas
import Init.Omega

namespace LeanTex.Core.PdfRead

/-! Sorting the xref keys preserves exactly the keys the reader visits.
This proves the permutation invariant of the standard library's actual
quicksort, including its partition loop; no ordering assumption is needed. -/

private theorem partition_loop_perm {α : Type u} {n : Nat}
    (lt : α → α → Bool) (lo hi : Nat) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.Perm as := by
  induction as, i, k, ilo, ik, w using
      Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h ht ih =>
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_left ht]
    exact ih.trans (Vector.swap_perm _ _)
  | case2 as i k ilo ik w h ht ih =>
    rw [Array.qpartition.loop, dite_eq_left h, ite_eq_right ht]
    exact ih
  | case3 as i k ilo ik w h =>
    rw [Array.qpartition.loop, dite_eq_right h]
    exact Vector.swap_perm (by omega) hhi

private theorem partition_perm {α : Type u} {n : Nat}
    (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.Perm as := by
  unfold Array.qpartition
  apply (partition_loop_perm ..).trans
  split <;> split <;> split
  all_goals repeat (first | exact .rfl |
    apply (Vector.swap_perm (by omega) (by omega)).trans)

private theorem sort_perm {α : Type u} (lt : α → α → Bool) {n : Nat}
    (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).Perm as := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid next hp hm =>
    rw [Array.qsort.sort, dite_eq_left h, hp]
    simp only [dite_eq_left hm]
    have := partition_perm as lt lo hi w hlo hhi
    simpa only [hp] using this
  | case2 as lo hi w hlo hhi h mid hmid next hp hm ih _ ih' =>
    rw [Array.qsort.sort, dite_eq_left h, hp]
    simp only [dite_eq_right hm]
    apply (ih'.trans ih).trans
    have := partition_perm as lt lo hi w hlo hhi
    simpa only [hp] using this
  | case3 as lo hi w hlo hhi h =>
    rw [Array.qsort.sort, dite_eq_right h]

/-- The actual sort used by object enumeration neither loses nor invents
xref keys, for any comparison and any subarray bounds. -/
public theorem qsort_perm_exact {α : Type u} (as : Array α)
    (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) :
    (as.qsort lt lo hi).Perm as := by
  unfold Array.qsort
  split
  · exact .rfl
  · exact (sort_perm ..).toArray

end LeanTex.Core.PdfRead
