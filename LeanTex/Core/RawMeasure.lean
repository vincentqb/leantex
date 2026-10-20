module

public import LeanTex.Core.Parse

public section

/-! Pointwise measures summed over lists and array slices, the termination measures of the walks
that read raws through an index. -/

namespace LeanTex.Core

open Parse

variable {α : Type}

/-- The sum of a pointwise measure over a list. -/
@[expose] public def measList (μ : α → Nat) : List α → Nat
  | [] => 0
  | x :: rest => μ x + measList μ rest

public theorem measList_append (μ : α → Nat) (a b : List α) :
    measList μ (a ++ b) = measList μ a + measList μ b := by
  induction a with
  | nil => simp [measList]
  | cons x xs ih => simp [measList, ih]; omega

public theorem measList_push (μ : α → Nat) (a : Array α) (x : α) :
    measList μ (a.push x).toList = measList μ a.toList + μ x := by
  simp [Array.toList_push, measList_append, measList]

public theorem measList_drop_le (μ : α → Nat) (l : List α) (i : Nat) :
    measList μ (l.drop i) ≤ measList μ l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, measList]
      omega

public theorem measList_take_le (μ : α → Nat) (l : List α) (i : Nat) :
    measList μ (l.take i) ≤ measList μ l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [measList]
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, measList]
      omega

public theorem measList_mem_le {μ : α → Nat} {l : List α} {x : α}
    (h : x ∈ l) : μ x ≤ measList μ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [measList]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

public theorem measList_le_of_le {μ ν : α → Nat} (h : ∀ x, μ x ≤ ν x)
    (l : List α) : measList μ l ≤ measList ν l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have := h x
    simp only [measList]
    omega

public theorem measList_extract_le (μ : α → Nat) (body : Array α) (a b : Nat) :
    measList μ (body.extract a b).toList ≤ measList μ body.toList := by
  rw [Array.toList_extract]
  exact Nat.le_trans (measList_take_le ..) (measList_drop_le ..)

/-- The pointwise measure summed over the slice from `i`. -/
@[expose] public def sliceMeas (μ : α → Nat) (raws : Array α) (i : Nat) : Nat :=
  measList μ (raws.toList.drop i)

public theorem sliceMeas_here (μ : α → Nat) (raws : Array α) {i : Nat}
    (h : i < raws.size) :
    sliceMeas μ raws i = μ raws[i] + sliceMeas μ raws (i + 1) := by
  unfold sliceMeas
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [measList]

public theorem sliceMeas_le (μ : α → Nat) (raws : Array α) {i j : Nat}
    (hij : i ≤ j) : sliceMeas μ raws j ≤ sliceMeas μ raws i := by
  unfold sliceMeas
  rw [show raws.toList.drop j = (raws.toList.drop i).drop (j - i) by
    rw [List.drop_drop]; congr 1; omega]
  exact measList_drop_le ..

public theorem sliceMeas_end (μ : α → Nat) (raws : Array α) {j : Nat}
    (h : raws.size ≤ j) : sliceMeas μ raws j = 0 := by
  unfold sliceMeas
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

public theorem sliceMeas_elem_le {μ : α → Nat} {raws : Array α} {j : Nat}
    {x : α} (h : raws[j]? = some x) {i : Nat} (hij : i ≤ j) :
    μ x ≤ sliceMeas μ raws i := by
  obtain ⟨hj, hx⟩ := Array.getElem?_eq_some_iff.mp h
  have h1 := sliceMeas_here μ raws hj
  have h2 := sliceMeas_le μ raws hij
  rw [hx] at h1
  omega

public theorem sliceMeas_extract_le (μ : α → Nat) (raws : Array α) (a b : Nat) :
    measList μ (raws.extract a b).toList ≤ sliceMeas μ raws a := by
  rw [Array.toList_extract]
  exact measList_take_le ..

public theorem sliceMeas_splice {μ : α → Nat} {raws : Array α} {i : Nat}
    (h : i < raws.size) (seg : Array α) :
    sliceMeas μ (raws.extract 0 i ++ seg ++ raws.extract (i + 1) raws.size) i + μ raws[i]
      ≤ sliceMeas μ raws i + measList μ seg.toList := by
  have hlen : (raws.extract 0 i).toList.length = i := by
    simp [Array.length_toList]; omega
  have hdrop : (raws.extract 0 i ++ seg
      ++ raws.extract (i + 1) raws.size).toList.drop i
      = seg.toList ++ (raws.extract (i + 1) raws.size).toList := by
    simp only [Array.toList_append, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  have h1 := sliceMeas_here μ raws h
  have h3 : measList μ (raws.extract (i + 1) raws.size).toList
      ≤ measList μ (raws.toList.drop (i + 1)) := by
    rw [Array.toList_extract]
    exact measList_take_le ..
  unfold sliceMeas at h1 ⊢
  rw [hdrop, measList_append]
  omega


public theorem sliceMeas_extract_split (μ : α → Nat) (raws : Array α) {a b : Nat}
    (hab : a ≤ b) : measList μ (raws.extract a b).toList + sliceMeas μ raws b = sliceMeas μ raws a := by
  unfold sliceMeas
  rw [Array.toList_extract]
  have hd : raws.toList.drop b = (raws.toList.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hd, ← measList_append]
  exact congrArg (measList μ) (List.take_append_drop (b - a) (raws.toList.drop a))

mutual
/-- The environments a raw holds, itself included, at every depth. -/
@[expose] public def Parse.Raw.envs : Raw → Nat
  | .group body _ => envsList body.toList
  | .math _ body _ => envsList body.toList
  | .env _ body _ => 1 + envsList body.toList
  | _ => 0

@[expose] public def envsList : List Raw → Nat
  | [] => 0
  | r :: rest => r.envs + envsList rest
end

public theorem envsList_eq (l : List Raw) : envsList l = measList Raw.envs l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [envsList, measList, ih]

/-- Splicing an environment's body in its place at the cursor, between raws that hold no
environment, lowers the environments from the cursor. -/
public theorem sliceMeas_envs_splice {raws : Array Raw} {i : Nat} (h : i < raws.size)
    {n : String} {body : Array Raw} {p : Pos} (hr : raws[i] = .env n body p)
    (pre post : Array Raw) (hpre : measList Raw.envs pre.toList = 0)
    (hpost : measList Raw.envs post.toList = 0) :
    sliceMeas Raw.envs (raws.extract 0 i ++ (pre ++ body ++ post) ++ raws.extract (i + 1) raws.size) i
      < sliceMeas Raw.envs raws i := by
  have hs := sliceMeas_splice (μ := Raw.envs) h (pre ++ body ++ post)
  have he : Raw.envs raws[i] = 1 + measList Raw.envs body.toList := by
    rw [hr]; simp [Raw.envs, envsList_eq]
  simp only [Array.toList_append, measList_append, hpre, hpost] at hs
  omega

/-- `sliceMeas_envs_splice` with the body alone in the environment's place. -/
public theorem sliceMeas_envs_unwrap {raws : Array Raw} {i : Nat} (h : i < raws.size)
    {n : String} {body : Array Raw} {p : Pos} (hr : raws[i] = .env n body p) :
    sliceMeas Raw.envs (raws.extract 0 i ++ body ++ raws.extract (i + 1) raws.size) i
      < sliceMeas Raw.envs raws i := by
  simpa using sliceMeas_envs_splice h hr #[] #[] rfl rfl

/-- A cursor moving forward over a slice whose measure does not grow decreases lexicographically. -/
public theorem cursor_advance_lex {m m' n n' : Nat} (hm : m' ≤ m) (hn : n' < n) :
    Prod.Lex (· < ·) (· < ·) (m', n') (m, n) := by
  rcases Nat.lt_or_eq_of_le hm with h | h
  · exact .left _ _ h
  · subst h; exact .right _ hn

end LeanTex.Core
