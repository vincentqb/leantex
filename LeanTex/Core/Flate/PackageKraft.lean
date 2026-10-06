module

import all LeanTex.Core.Flate.PackageMergeProof
import all LeanTex.Core.Flate.SortProof
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Nat.Sum

namespace LeanTex.Core.Flate.PackageMerge

private theorem get_not_mem_take (sorted : Array Nat) (hn : sorted.toList.Nodup)
    (i : Nat) (hi : i < sorted.size) :
    sorted[i] ∉ sorted.toList.take i := by
  intro hm
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hm
  have hj' : j < sorted.toList.length := by omega
  have hi' : i < sorted.toList.length := by simpa using hi
  have hij : j = i := hn.eq_of_getElem_eq hj' hi' (by simpa using he)
  omega

/-- Each selected leaf gains exactly one bit, and all other symbols keep
their length. This follows the encoder's actual array update loop. -/
theorem addBits_exact (sorted lens : Array Nat) (leaves : Nat)
    (hn : sorted.toList.Nodup)
    (hv : ∀ s ∈ sorted.toList, s < lens.size) (hl : leaves ≤ sorted.size) :
    (addBits sorted lens leaves).size = lens.size ∧
    ∀ s, (addBits sorted lens leaves)[s]?.getD 0 =
      lens[s]?.getD 0 + if s ∈ sorted.toList.take leaves then 1 else 0 := by
  let P (j : Nat) (out : Array Nat) : Prop :=
    out.size = lens.size ∧ ∀ s, out[s]?.getD 0 =
      lens[s]?.getD 0 + if s ∈ sorted.toList.take j then 1 else 0
  unfold addBits
  simp only [Id.run, bind, pure]
  apply Progress.forIn_range_exact P (P leaves) _ 0 leaves _ (Nat.zero_le _)
    (by simp [P]) _ (fun _ h => h)
  intro j _ hj out ho
  have hjs : j < sorted.size := by omega
  have hjl : j < sorted.toList.length := by simpa using hjs
  have hvj : sorted[j] < out.size := by
    rw [ho.1]
    exact hv _ (by simp)
  have hnew := get_not_mem_take sorted hn j hjs
  have htake := List.take_succ_eq_append_getElem hjl
  simp only [getElem?_pos sorted j hjs, Option.getD_some]
  change P (j + 1) (out.set! sorted[j] (out[sorted[j]]?.getD 0 + 1))
  refine ⟨by simpa using ho.1, ?_⟩
  intro s
  by_cases he : sorted[j] = s
  · subst s
    have hold := ho.2 sorted[j]
    simp only [getElem?_pos out sorted[j] hvj, Option.getD_some, hnew, ite_false,
      Nat.add_zero] at hold
    simp [hvj, htake, hold]
  · simp [he, ho.2, htake, Ne.symm he]

/-- The integer-scaled Kraft mass of the live alphabet. The scale is
`2^limit`, so there is no rational arithmetic in the backtrace invariant. -/
def mass (limit : Nat) (sorted lens : Array Nat) : Nat :=
  (sorted.toList.map fun s => 2 ^ (limit - lens[s]?.getD 0)).sum

private theorem sum_decrease {α : Type} (xs : List α) (f g : α → Nat) (coin : Nat)
    (h : ∀ s ∈ xs, g s + coin ≤ f s) :
    (xs.map g).sum + xs.length * coin ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have hs := h s (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem bit_mass_decrease (limit i width : Nat) (hi : i < limit)
    (hw : width ≤ i) :
    2 ^ (limit - (width + 1)) + 2 ^ (limit - 1 - i) ≤ 2 ^ (limit - width) := by
  have hc : 2 ^ (limit - 1 - i) ≤ 2 ^ (limit - (width + 1)) :=
    Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have he : limit - width = (limit - (width + 1)) + 1 := by omega
  rw [he, Nat.pow_succ]
  omega

private theorem mass_split (limit : Nat) (sorted lens : Array Nat) (leaves : Nat) :
    mass limit sorted lens =
      ((sorted.toList.take leaves).map fun s => 2 ^ (limit - lens[s]?.getD 0)).sum +
      ((sorted.toList.drop leaves).map fun s => 2 ^ (limit - lens[s]?.getD 0)).sum := by
  unfold mass
  conv => lhs; rw [← List.take_append_drop leaves sorted.toList]
  rw [List.map_append, List.sum_append]

/-- Buying a bit at level `i` removes at least that level's denomination
from Kraft mass. Earlier purchases only increase this reduction. -/
theorem addBits_mass_monotone (sorted lens : Array Nat) (leaves limit i : Nat)
    (hn : sorted.toList.Nodup)
    (hv : ∀ s ∈ sorted.toList, s < lens.size) (hl : leaves ≤ sorted.size)
    (hi : i < limit) (hw : ∀ s ∈ sorted.toList, lens[s]?.getD 0 ≤ i) :
    mass limit sorted (addBits sorted lens leaves) + leaves * 2 ^ (limit - 1 - i) ≤
      mass limit sorted lens := by
  have he := addBits_exact sorted lens leaves hn hv hl
  have hd : ∀ s ∈ sorted.toList.take leaves, ∀ t ∈ sorted.toList.drop leaves, s ≠ t :=
    (List.nodup_append.mp (by simpa only [List.take_append_drop] using hn)).2.2
  have hp := sum_decrease (sorted.toList.take leaves)
    (fun s => 2 ^ (limit - lens[s]?.getD 0))
    (fun s => 2 ^ (limit - (addBits sorted lens leaves)[s]?.getD 0))
    (2 ^ (limit - 1 - i)) (by
      intro s hs
      rw [he.2 s, ite_eq_left hs]
      exact bit_mass_decrease limit i _ hi (hw s (List.mem_of_mem_take hs)))
  have ht :
      ((sorted.toList.drop leaves).map fun s =>
        2 ^ (limit - (addBits sorted lens leaves)[s]?.getD 0)) =
      ((sorted.toList.drop leaves).map fun s => 2 ^ (limit - lens[s]?.getD 0)) := by
    apply List.map_congr_left
    intro s hs
    have hno : s ∉ sorted.toList.take leaves := fun hm => hd s hm s hs rfl
    simp only [he.2 s, ite_eq_right hno, Nat.add_zero]
  simp only [List.length_take, Array.length_toList, Nat.min_eq_left hl] at hp
  rw [mass_split limit sorted (addBits sorted lens leaves) leaves,
    mass_split limit sorted lens leaves, ht]
  omega

/-- The properties consumed by canonical-code construction. The alphabet
is explicit: unused symbols must keep length zero. -/
structure LengthsFor (sorted : Array Nat) (size limit : Nat) (lens : Array Nat) : Prop where
  size_eq : lens.size = size
  width_le : ∀ s : Nat, lens[s]?.getD 0 ≤ limit
  unused_zero : ∀ s, s ∉ sorted.toList → lens[s]?.getD 0 = 0
  kraft : mass limit sorted lens ≤ 2 ^ limit

private structure TraceFor (sorted : Array Nat) (size limit i : Nat)
    (lens : Array Nat) (take : Nat) : Prop where
  size_eq : lens.size = size
  width_le : ∀ s : Nat, lens[s]?.getD 0 ≤ i
  unused_zero : ∀ s, s ∉ sorted.toList → lens[s]?.getD 0 = 0
  enough : i < limit → take ≤ capacity sorted.size (limit - 1 - i)
  more : take = 0 ∨ i < limit
  credit : mass limit sorted lens + (sorted.size - 1) * 2 ^ limit ≤
    sorted.size * 2 ^ limit + take * 2 ^ (limit - 1 - i)

private theorem selected_credit (limit i leaves pairs : Nat) (hi : i < limit)
    (hlast : i + 1 = limit → pairs = 0) :
    leaves * 2 ^ (limit - 1 - i) +
      (2 * pairs) * 2 ^ (limit - 1 - (i + 1)) =
      (leaves + pairs) * 2 ^ (limit - 1 - i) := by
  by_cases he : i + 1 = limit
  · simp [hlast he]
  · have hk : limit - 1 - i = (limit - 1 - (i + 1)) + 1 := by omega
    rw [Nat.add_mul]
    congr 1
    rw [hk, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm]

private theorem trace_step (sorted : Array Nat) (size limit i : Nat)
    (lens : Array Nat) (take : Nat) (flags : Array Bool)
    (hn : sorted.toList.Nodup) (hv : ∀ s ∈ sorted.toList, s < size)
    (hi : i < limit) (hf : LevelFor sorted.size (limit - 1 - i) flags)
    (hs : TraceFor sorted size limit i lens take) :
    TraceFor sorted size limit (i + 1)
      (addBits sorted lens (selected flags take).1) (2 * (selected flags take).2) := by
  have ht : take ≤ flags.size := by rw [hf.1]; exact hs.enough hi
  rcases selected_counts_exact flags take ht with ⟨hcount, hleaves, hpairs⟩
  rw [hf.2.1] at hleaves
  have hv' : ∀ s ∈ sorted.toList, s < lens.size := by
    simpa only [hs.size_eq] using hv
  have hadd := addBits_exact sorted lens (selected flags take).1 hn hv' hleaves
  have hdrop := addBits_mass_monotone sorted lens (selected flags take).1 limit i
    hn hv' hleaves hi (fun s _ => hs.width_le s)
  have hlast : i + 1 = limit → (selected flags take).2 = 0 := by
    intro he
    have hk : limit - 1 - i = 0 := by omega
    simp only [hf.2.2, hk, ite_true] at hpairs
    omega
  have hcredit := selected_credit limit i (selected flags take).1
    (selected flags take).2 hi hlast
  rw [hcount] at hcredit
  refine ⟨hadd.1.trans hs.size_eq, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hadd.2 s]
    have hw := hs.width_le s
    split <;> omega
  · intro s hno
    have hprefix : s ∉ sorted.toList.take (selected flags take).1 :=
      fun h => hno (List.mem_of_mem_take h)
    simp only [hadd.2 s, ite_eq_right hprefix, Nat.add_zero, hs.unused_zero s hno]
  · intro hnext
    have hk : limit - 1 - i ≠ 0 := by omega
    rw [hf.2.2, ite_eq_right hk] at hpairs
    have hexp : limit - 1 - i - 1 = limit - 1 - (i + 1) := by omega
    rw [hexp] at hpairs
    omega
  · by_cases he : i + 1 = limit
    · exact Or.inl (by simp [hlast he])
    · exact Or.inr (by omega)
  · have hold := hs.credit
    omega

private theorem trace_finish (sorted : Array Nat) (size limit i : Nat)
    (lens : Array Nat) (hn : 0 < sorted.size) (hi : i ≤ limit)
    (hs : TraceFor sorted size limit i lens 0) : LengthsFor sorted size limit lens := by
  refine ⟨hs.size_eq, fun s => Nat.le_trans (hs.width_le s) hi, hs.unused_zero, ?_⟩
  have hc := hs.credit
  have he : sorted.size * 2 ^ limit = (sorted.size - 1) * 2 ^ limit + 2 ^ limit := by
    calc
      sorted.size * 2 ^ limit = ((sorted.size - 1) + 1) * 2 ^ limit :=
        congrArg (· * 2 ^ limit) (by omega)
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]
  rw [he, Nat.zero_mul, Nat.add_zero] at hc
  omega

/-- The actual package backtrace produces bounded lengths satisfying
Kraft's inequality. Its premises are alphabet bounds and the proven
leaf/package counts at each level, not an encoder/decoder inversion. -/
theorem backtrace_contract (sorted : Array Nat) (size : Nat) (levels : Array (Array Bool))
    (hn : sorted.toList.Nodup) (hv : ∀ s ∈ sorted.toList, s < size)
    (hpos : 0 < sorted.size) (hl : 0 < levels.size) (hfit : sorted.size ≤ 2 ^ levels.size)
    (hlevels : ∀ k < levels.size, LevelFor sorted.size k (levels[k]?.getD #[])) :
    LengthsFor sorted size levels.size (backtrace sorted size levels) := by
  let P (i : Nat) (s : Array Nat × Nat) : Prop :=
    TraceFor sorted size levels.size i s.1 s.2
  let Q (s : Array Nat × Nat) : Prop := LengthsFor sorted size levels.size s.1
  have hzero : ∀ s : Nat, (Array.replicate size 0)[s]?.getD 0 = 0 := by
    intro s
    by_cases he : s < size <;> simp [he]
  unfold backtrace
  simp only [Id.run, bind, pure]
  generalize hres : (forIn [0:levels.size]
    (Array.replicate size 0, 2 * sorted.size - 2) _ :
      Id (Array Nat × Nat)) = result
  have hq : Q result := by
    rw [← hres]
    apply Progress.forIn_range_exact P Q _ 0 levels.size _ (Nat.zero_le _) ?_ ?_ ?_
    · refine ⟨by simp, ?_, ?_, ?_, Or.inr hl, ?_⟩
      · intro s
        simp only [hzero, Nat.le_refl]
      · intro s _
        exact hzero s
      · intro _
        simpa using capacity_solution_between sorted.size levels.size hl hfit
      · have hm : mass levels.size sorted (Array.replicate size 0) =
            sorted.size * 2 ^ levels.size := by
          simp [mass, hzero, List.map_const', List.sum_replicate_nat]
        have he : (sorted.size - 1) * 2 ^ levels.size =
            (2 * sorted.size - 2) * 2 ^ (levels.size - 1) := by
          have hsize : levels.size = (levels.size - 1) + 1 := by omega
          have hn' : 2 * sorted.size - 2 = (sorted.size - 1) * 2 := by omega
          conv => lhs; rw [hsize, Nat.pow_succ]
          rw [hn']
          simp only [Nat.mul_assoc, Nat.mul_comm]
        dsimp only
        simpa only [hm, Nat.sub_zero, he] using Nat.le_refl
          (sorted.size * 2 ^ levels.size + (2 * sorted.size - 2) * 2 ^ (levels.size - 1))
    · intro i _ hi s hs
      have hk : levels.size - 1 - i < levels.size := by omega
      have step := trace_step sorted size levels.size i s.1 s.2
        (levels[levels.size - 1 - i]?.getD #[]) hn hv hi
        (hlevels _ hk) hs
      simp only [Id.run]
      by_cases hz : 2 * (selected (levels[levels.size - 1 - i]?.getD #[]) s.2).2 = 0
      · simp only [beq_iff_eq, hz, ite_true]
        rw [hz] at step
        exact trace_finish sorted size levels.size (i + 1) _ hpos (by omega) step
      · simp only [beq_iff_eq, hz, ite_false]
        exact step
    · intro s hs
      change TraceFor sorted size levels.size levels.size s.1 s.2 at hs
      have hz : s.2 = 0 := hs.more.resolve_right (by omega)
      rw [hz] at hs
      exact trace_finish sorted size levels.size levels.size s.1 hpos (Nat.le_refl _) hs
  exact hq

end LeanTex.Core.Flate.PackageMerge
