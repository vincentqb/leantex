-- leantex: show = prose, code, facts = code-lean-prose.facts, glossary = where, phrase.Moored = "#1 is moored", phrase.nameOf = "the name of #1"
/-! # Laid-out statements

Invented statements whose scopes the prose view sets as indented blocks and whose clauses it
sets as numbered lists. -/

/-- Each statement of a list implies every other, as Mathlib's TFAE says. -/
def List.TFAE (l : List Prop) : Prop := forall x, Membership.mem l x ->
  forall y, Membership.mem l y -> (x <-> y)

namespace Ebb

/-- A quantified hypothesis stands as a block under its condition. -/
theorem none_all (h : forall n : Nat, n = 0) : False :=
  absurd (h 1) (by omega)

/-- An equivalence a conclusion holds stands as a block under it. -/
theorem iff_after (p q : Prop) (_hp : p) : q <-> q := Iff.rfl

/-- An equivalence of conjunctions under a quantifier stands as a block, its sides bare. -/
theorem swap (p q : Prop) : And p q <-> And q p := And.comm

/-- An equivalence a quantifier opens lists its two sides. -/
theorem all_iff (p : Prop) : (forall n : Nat, Or p (n = n)) <-> True :=
  Iff.intro (fun _ => True.intro) (fun _ _ => Or.inr rfl)

theorem neg_all : Not (forall n : Nat, n = 0) :=
  fun h => absurd (h 1) (by omega)

theorem both_all : And (forall n : Nat, 0 <= n) (exists m : Nat, m = m) :=
  And.intro Nat.zero_le (Exists.intro 0 rfl)

/-- List literals and a function ignoring its argument, as Lean writes them. -/
theorem list_lits :
    And ([1, 2, 3].length = 3) (List.map (fun _ => 0) [5] = [0]) :=
  And.intro rfl rfl

theorem chain (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  Nat.le_trans h1 h2

structure Barge where
  hull : Nat
  draft : Nat

def Moored (b : Barge) : Prop := 0 < b.draft

def nameOf (b : Barge) : String := toString b.hull

/-- Three clauses over a list: a disjunction, a witness and a bound. -/
theorem harbor_log (bs : List Barge) :
    And (forall b, Membership.mem bs b -> Or (b.draft = 0) (Moored b))
      (And (forall s, Membership.mem (bs.map nameOf) s ->
          exists b, And (Membership.mem bs b) (nameOf b = s))
        (forall n : Nat, (bs.drop n).length <= bs.length)) :=
  And.intro (fun b _ => by unfold Moored; omega)
    (And.intro (fun _ h => List.mem_map.mp h)
      (fun n => by rw [List.length_drop]; omega))

/-- Three clauses, the second of two clauses its own. -/
theorem barge_bounds (bs : List Barge) (cap : Nat) :
    And (forall b, Membership.mem bs b -> b.draft <= b.draft + cap)
      (And (forall b, Membership.mem bs b ->
          And (forall k : Nat, k < b.hull -> k + 1 <= b.hull)
            (exists m : Nat, m = b.draft + cap))
        (bs.length <= bs.length + cap)) :=
  And.intro (fun _ _ => Nat.le_add_right _ _)
    (And.intro (fun _ _ => And.intro (fun _ hk => hk) (Exists.intro _ rfl))
      (Nat.le_add_right _ _))

/-- A hypothesis about the bound name alone reads as a relative clause. -/
theorem moored_draft : forall b : Barge, Moored b -> 0 < b.draft :=
  fun _ h => h

/-- An existential's first statement about its name reads as one too. -/
theorem some_moored : exists b : Barge, And (Moored b) (b.hull = 0) :=
  Exists.intro (Barge.mk 0 1) (And.intro (by unfold Moored; decide) rfl)

/-- Three equivalent statements, one a quantifier's, listed. -/
theorem parity (n : Nat) :
    List.TFAE [n % 2 = 0, (n + 2) % 2 = 0,
      forall k : Nat, k = n -> k % 2 = 0] := by
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  have h : (forall k : Nat, k = n -> k % 2 = 0) <-> n % 2 = 0 :=
    Iff.intro (fun f => f n rfl) (fun e k hk => hk ▸ e)
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    (try simp only [h]) <;> omega

end Ebb
