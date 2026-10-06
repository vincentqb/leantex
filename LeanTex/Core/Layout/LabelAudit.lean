module

public import LeanTex.Core.Diag

namespace LeanTex.Core.Layout.LabelAudit

/-- An occurrence selected by collection, before pagination can lose it. -/
public structure Request where
  origin : Nat × Nat
  key : String
  source : Option Span
  blank : Bool
  deriving Repr

/-- The actual label producer's reserve, relative to its painted baseline.
Vertical placement moves that baseline and its reserve together. -/
public structure Stamp where
  origin : Nat × Nat
  key : String
  source : Option Span
  above : Int
  below : Int
  lineCount : Nat
  deriving Repr, DecidableEq

/-- A reading of a shipped line, including every actual run's outline
answer. The layout adapter proves the meaning of these two checks. -/
public structure Observation where
  stamp : Stamp
  known : Bool
  bounded : Bool
  deriving Repr

public def Matches (r : Request) (o : Observation) : Prop :=
  o.stamp.origin = r.origin ∧ o.stamp.key = r.key

public instance (r : Request) (o : Observation) : Decidable (Matches r o) :=
  inferInstanceAs (Decidable (o.stamp.origin = r.origin ∧ o.stamp.key = r.key))

/-- Full source equality includes macro ancestry and the written token;
the diagnostic position's ordinary `BEq` deliberately ignores both. -/
public def named (key : String) (source : Option Span) (kind : DiagCode)
    (ds : Array Diag) : Prop :=
  ∃ d ∈ ds, d.kind = kind ∧ d.subject = some key ∧ d.span = source

public def accounted (r : Request) (os : Array Observation) (ds : Array Diag) : Prop :=
  (r.blank = true ∧ ¬ ∃ o ∈ os, Matches r o) ∨
    (∃ o ∈ os, Matches r o ∧ o.known = true ∧ o.bounded = true ∧ o.stamp.lineCount ≤ 1) ∨
    (∃ d ∈ ds, d.subject = some r.key ∧
      (d.kind ∈ ([.W0328, .W0394, .E0395, .W0396] : List DiagCode) ∨
        (d.kind.loss == .dropped || d.kind.loss == .pending) = true) ∧
      (d.span = r.source ∨ ∃ o ∈ os, Matches r o ∧ d.span = o.stamp.source))

private def ensure (key : String) (source : Option Span) (kind : DiagCode)
    (message : String) (ds : Array Diag) : Array Diag :=
  if ds.any (fun d =>
      decide (d.kind = kind ∧ d.subject = some key ∧ d.span = source)) then ds
  else ds.push { kind := kind, message := message, subject := some key, span := source }

private theorem ensure_keeps (key : String) (source : Option Span) (kind : DiagCode)
    (message : String) (ds : Array Diag) (d : Diag) (hd : d ∈ ds) :
    d ∈ ensure key source kind message ds := by
  unfold ensure
  split
  · exact hd
  · exact Array.mem_push.mpr (Or.inl hd)

private theorem ensure_named (key : String) (source : Option Span) (kind : DiagCode)
    (message : String) (ds : Array Diag) :
    named key source kind (ensure key source kind message ds) := by
  unfold ensure
  split
  · rename_i h
    obtain ⟨d, hd, he⟩ := Array.any_eq_true'.mp h
    exact ⟨d, hd, of_decide_eq_true he⟩
  · exact ⟨_, Array.mem_push.mpr (Or.inr rfl), rfl, rfl, rfl⟩

public theorem named_mono (key : String) (source : Option Span) (kind : DiagCode)
    (a b : Array Diag) (h : named key source kind a)
    (keep : ∀ d ∈ a, d ∈ b) : named key source kind b := by
  obtain ⟨d, hd, hk, hs, hp⟩ := h
  exact ⟨d, keep d hd, hk, hs, hp⟩

private theorem named_ensure (key : String) (source : Option Span) (kind : DiagCode)
    (ds : Array Diag) (other : String) (atSource : Option Span) (code : DiagCode)
    (message : String) (h : named key source kind ds) :
    named key source kind (ensure other atSource code message ds) :=
  named_mono _ _ _ _ _ h (ensure_keeps _ _ _ _ _)

public theorem accounted_mono (r : Request) (os : Array Observation)
    (a b : Array Diag) (h : accounted r os a)
    (keep : ∀ d ∈ a, d ∈ b) : accounted r os b := by
  rcases h with hb | hg | ⟨d, hd, hs, hk, hp⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl hg)
  · exact Or.inr (Or.inr ⟨d, keep d hd, hs, hk, hp⟩)

/-- Every failed check is accounted independently: truncation must never
suppress an unresolved outline in the line that remains. -/
private def observe (ds : Array Diag) (o : Observation) : Array Diag :=
  let ds := if 1 < o.stamp.lineCount then
    ensure o.stamp.key o.stamp.source .W0328
      "picture label spans multiple lines; only its first line is kept" ds else ds
  let ds := if o.known then ds else
    ensure o.stamp.key o.stamp.source .W0394
      "picture label has glyphs without measured outline bounds" ds
  if o.bounded then ds else
    ensure o.stamp.key o.stamp.source .W0396
      "picture label extends beyond its reserved glyph box" ds

private theorem observe_keeps (ds : Array Diag) (o : Observation) (d : Diag)
    (hd : d ∈ ds) : d ∈ observe ds o := by
  simp only [observe]
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals split
  all_goals repeat first | exact hd | apply ensure_keeps

public def Good (o : Observation) : Prop :=
  o.known = true ∧ o.bounded = true ∧ o.stamp.lineCount ≤ 1

public def Observed (o : Observation) (ds : Array Diag) : Prop :=
  Good o ∨ ∃ kind ∈ ([.W0328, .W0394, .W0396] : List DiagCode),
    named o.stamp.key o.stamp.source kind ds

private theorem observe_accounts (ds : Array Diag) (o : Observation) :
    Observed o (observe ds o) := by
  by_cases hc : 1 < o.stamp.lineCount
  · right
    refine ⟨.W0328, by simp, ?_⟩
    simp only [observe, hc, ↓reduceIte]
    split <;> try dsimp only
    all_goals split
    all_goals repeat first | exact ensure_named _ _ _ _ _ | apply named_ensure
  · cases hk : o.known with
    | false =>
      right
      refine ⟨.W0394, by simp, ?_⟩
      simp only [observe, hc, hk, Bool.false_eq_true, ↓reduceIte]
      split
      all_goals repeat first | exact ensure_named _ _ _ _ _ | apply named_ensure
    | true =>
      cases hb : o.bounded with
      | false =>
        right
        refine ⟨.W0396, by simp, ?_⟩
        simp only [observe, hc, hk, hb, Bool.false_eq_true, ↓reduceIte]
        exact ensure_named _ _ _ _ _
      | true =>
        exact Or.inl ⟨hk, hb, by omega⟩

private theorem observe_unknown_named (ds : Array Diag) (o : Observation)
    (hu : o.known = false) :
    named o.stamp.key o.stamp.source .W0394 (observe ds o) := by
  simp only [observe, hu, Bool.false_eq_true, ↓reduceIte]
  split <;> try dsimp only
  all_goals split
  all_goals repeat first | exact ensure_named _ _ _ _ _ | apply named_ensure

public theorem Observed.mono (o : Observation) (a b : Array Diag)
    (h : Observed o a) (keep : ∀ d ∈ a, d ∈ b) : Observed o b := by
  rcases h with hg | ⟨code, hc, hn⟩
  · exact Or.inl hg
  · exact Or.inr ⟨code, hc, named_mono _ _ _ _ _ hn keep⟩

private def missing (os : Array Observation) (ds : Array Diag) (r : Request) : Array Diag :=
  if r.blank || os.any (fun o => decide (Matches r o)) then ds
  else if ds.any (fun d =>
      decide (d.subject = some r.key ∧ d.span = r.source) &&
        (d.kind.loss == .dropped || d.kind.loss == .pending)) then ds
  else ensure r.key r.source .E0395 "picture label produced no line" ds

private theorem missing_keeps (os : Array Observation) (ds : Array Diag)
    (r : Request) (d : Diag) (hd : d ∈ ds) : d ∈ missing os ds r := by
  unfold missing
  split
  · exact hd
  · split
    · exact hd
    · exact ensure_keeps _ _ _ _ _ _ hd

/-- This is a check over two independently produced censuses: collection's
requests and the lines that actually survived into the final pages. -/
public def finish (rs : Array Request) (os : Array Observation) (ds : Array Diag) : Array Diag :=
  rs.foldl (missing os) (os.foldl observe ds)

private theorem fold_keeps {α : Type} (f : Array Diag → α → Array Diag)
    (keeps : ∀ ds x d, d ∈ ds → d ∈ f ds x) (xs : Array α) (ds : Array Diag)
    (d : Diag) (hd : d ∈ ds) : d ∈ xs.foldl f ds := by
  refine Array.foldl_induction (motive := fun _ acc => d ∈ acc) hd ?_
  intro i acc ih
  exact keeps acc xs[i] d ih

public theorem finish_keeps (rs : Array Request) (os : Array Observation)
    (ds : Array Diag) (d : Diag) (hd : d ∈ ds) :
    d ∈ finish rs os ds :=
  fold_keeps _ (fun ds r d hd => missing_keeps os ds r d hd) _ _ _
    (fold_keeps _ observe_keeps _ _ _ hd)

private theorem observe_all (os : Array Observation) (ds : Array Diag)
    (o : Observation) (ho : o ∈ os) : Observed o (os.foldl observe ds) := by
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp ho
  have all : j < os.size → Observed o (os.foldl observe ds) := by
    refine Array.foldl_induction
      (motive := fun n acc => j < n → Observed o acc) (by omega) ?_
    intro i acc ih hn
    by_cases hprev : j < i.val
    · exact Observed.mono _ _ _ (ih hprev) (observe_keeps acc os[i])
    · have hij : i.val = j := by omega
      have heq : os[i] = o := by
        change os[i.val] = o
        simpa only [hij] using he
      rw [heq]
      exact observe_accounts _ _
  exact all hj

/-- Every observed line has its own account, even when several output
lines carry one source identity. One good duplicate cannot hide another
line's failed outline check. -/
public theorem finish_observed_accounts (rs : Array Request) (os : Array Observation)
    (ds : Array Diag) (o : Observation) (ho : o ∈ os) :
    Observed o (finish rs os ds) :=
  Observed.mono _ _ _ (observe_all os ds o ho)
    (fold_keeps _ (fun ds r d hd => missing_keeps os ds r d hd) _ _)

public theorem finish_unknown_named (rs : Array Request) (os : Array Observation)
    (ds : Array Diag) (o : Observation) (ho : o ∈ os) (hu : o.known = false) :
    named o.stamp.key o.stamp.source .W0394 (finish rs os ds) := by
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp ho
  have all : j < os.size →
      named o.stamp.key o.stamp.source .W0394 (os.foldl observe ds) := by
    refine Array.foldl_induction
      (motive := fun n acc => j < n → named o.stamp.key o.stamp.source .W0394 acc)
      (by omega) ?_
    intro i acc ih hn
    by_cases hprev : j < i.val
    · exact named_mono _ _ _ _ _ (ih hprev) (observe_keeps acc os[i])
    · have hij : i.val = j := by omega
      have heq : os[i] = o := by
        change os[i.val] = o
        simpa only [hij] using he
      rw [heq]
      exact observe_unknown_named _ _ hu
  exact named_mono _ _ _ _ _ (all hj)
    (fold_keeps _ (fun ds r d hd => missing_keeps os ds r d hd) _ _)

private theorem missing_accounts (os : Array Observation) (ds : Array Diag)
    (r : Request) (observed : ∀ o ∈ os, Observed o ds) :
    accounted r os (missing os ds r) := by
  by_cases hm : ∃ o ∈ os, Matches r o
  · obtain ⟨o, ho, hm⟩ := hm
    rcases observed o ho with hg | ⟨code, hc, d, hd, hk, hs, hp⟩
    · exact Or.inr (Or.inl ⟨o, ho, hm, hg⟩)
    · refine Or.inr (Or.inr ⟨d, missing_keeps _ _ _ _ hd, ?_, ?_, ?_⟩)
      · simpa only [hm.2] using hs
      · left
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        rcases hc with h | h | h
        · exact Or.inl (hk.trans h)
        · exact Or.inr (Or.inl (hk.trans h))
        · exact Or.inr (Or.inr (Or.inr (hk.trans h)))
      · exact Or.inr ⟨o, ho, hm, hp⟩
  · by_cases hb : r.blank = true
    · exact Or.inl ⟨hb, hm⟩
    have ha : os.any (fun o => decide (Matches r o)) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨o, ho, hm'⟩ := Array.any_eq_true'.mp h
      exact hm ⟨o, ho, of_decide_eq_true hm'⟩
    have hb' : r.blank = false := Bool.eq_false_iff.mpr hb
    simp only [missing, hb', ha, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i h
      obtain ⟨d, hd, htest⟩ := Array.any_eq_true'.mp h
      obtain ⟨hwhere, hloss⟩ := Bool.and_eq_true_iff.mp htest
      obtain ⟨hs, hp⟩ := of_decide_eq_true hwhere
      exact Or.inr (Or.inr ⟨d, hd, hs, Or.inr hloss, Or.inl hp⟩)
    · obtain ⟨d, hd, hk, hs, hp⟩ := ensure_named r.key r.source .E0395
        "picture label produced no line" ds
      exact Or.inr (Or.inr ⟨d, hd, hs, Or.inl (by simp [hk]), Or.inl hp⟩)

/-- Every requested occurrence is present with checked glyph bounds, blank,
or paid for by an accurate diagnostic. No premise about the producer or
placement is supplied: the two censuses are inspected by the actual check. -/
public theorem finish_accounts (rs : Array Request) (os : Array Observation)
    (ds : Array Diag) (r : Request) (hr : r ∈ rs) :
    accounted r os (finish rs os ds) := by
  obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp hr
  have all : (∀ o ∈ os, Observed o (finish rs os ds)) ∧
      (j < rs.size → accounted r os (finish rs os ds)) := by
    refine Array.foldl_induction
      (motive := fun n acc =>
        (∀ o ∈ os, Observed o acc) ∧ (j < n → accounted r os acc)) ?_ ?_
    · exact ⟨observe_all os ds, by omega⟩
    · intro i acc ih
      refine ⟨fun o ho => Observed.mono _ _ _ (ih.1 o ho)
        (missing_keeps os acc rs[i]), ?_⟩
      intro hn
      by_cases hprev : j < i.val
      · exact accounted_mono _ _ _ _ (ih.2 hprev) (missing_keeps os acc rs[i])
      · have hij : i.val = j := by omega
        have heq : rs[i] = r := by
          change rs[i.val] = r
          simpa only [hij] using he
        rw [heq]
        exact missing_accounts os acc r ih.1
  exact all.2 hj

end LeanTex.Core.Layout.LabelAudit
