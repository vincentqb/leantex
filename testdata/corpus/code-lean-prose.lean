-- leantex: show = prose, code, facts = code-lean-prose.facts, phrase.Heavy = "#1 is heavy", phrase.labelOf = "the label of #1"
/-! # Laid-out statements

Invented statements whose scopes the prose view sets as indented blocks and whose clauses it
sets as numbered lists. -/

namespace Ebb

/-- A quantified hypothesis stands as a block under its condition. -/
theorem none_all (h : forall n : Nat, n = 0) : False :=
  absurd (h 1) (by omega)

/-- An equivalence a conclusion holds stands as a block under it. -/
theorem iff_after (p q : Prop) (_hp : p) : q <-> q := Iff.rfl

/-- An equivalence of conjunctions under a quantifier sets each side a block deeper. -/
theorem swap (p q : Prop) : And p q <-> And q p := And.comm

theorem neg_all : Not (forall n : Nat, n = 0) :=
  fun h => absurd (h 1) (by omega)

theorem both_all : And (forall n : Nat, 0 <= n) (exists m : Nat, m = m) :=
  And.intro Nat.zero_le (Exists.intro 0 rfl)

theorem chain (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  Nat.le_trans h1 h2

structure Crate where
  id : Nat
  weight : Nat

def Heavy (c : Crate) : Prop := 0 < c.weight

def ledger (cs : List Crate) (_bin : String) (_log : List (String × Nat)) :
    List String × Nat :=
  ([], cs.length)

def labelOf (c : Crate) : String := toString c.id

def FairSwap (_bin : String) (_log : List (String × Nat)) (_cs : List Crate)
    (c d : Crate) : Prop :=
  c.id = d.id

def samples (_n : Nat) : List Bool := []

def allSet (b : Bool) : Bool := b

def weightOdds (n : Nat) : Nat := n

/-- Three clauses over typed parameters, a witness pair and an identity of lengths. -/
theorem ledger_summary (cs : List Crate) (bin : String)
    (log : List (String × Nat)) :
    And (forall c, Membership.mem cs c -> Or (Heavy c) (c.weight = 0))
      (And (forall tag, Membership.mem (ledger cs bin log).1 tag -> exists c d,
          And (tag = labelOf d) (FairSwap bin log (cs.take 2) c d))
        (forall n, 1 <= n ->
          (samples n).length = (samples n).countP allSet * weightOdds n)) := by
  refine And.intro (fun c _ => ?_) (And.intro (fun tag h => ?_) (fun n _ => ?_))
  · unfold Heavy; omega
  · simp [ledger] at h
  · simp [samples]

/-- Three clauses, the second of two clauses its own. -/
theorem crate_bounds (cs : List Crate) (cap : Nat) :
    And (forall c, Membership.mem cs c -> c.weight <= c.weight + cap)
      (And (forall c, Membership.mem cs c ->
          And (forall k : Nat, k < c.id -> k + 1 <= c.id)
            (exists m : Nat, m = c.weight + cap))
        (cs.length <= cs.length + cap)) :=
  And.intro (fun _ _ => Nat.le_add_right _ _)
    (And.intro (fun _ _ => And.intro (fun _ hk => hk) (Exists.intro _ rfl))
      (Nat.le_add_right _ _))

end Ebb
