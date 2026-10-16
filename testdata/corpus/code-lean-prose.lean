-- leantex: show = prose, code, facts = code-lean-prose.facts
/-! # Laid-out statements

Invented statements whose scopes the prose view sets as indented blocks. -/

namespace Ebb

/-- A quantified hypothesis stands as a block under its condition. -/
theorem none_all (h : forall n : Nat, n = 0) : False :=
  absurd (h 1) (by omega)

/-- An equivalence a conclusion holds stands as a block under it. -/
theorem iff_after (p q : Prop) (_hp : p) : q <-> q := Iff.rfl

/-- An equivalence of conjunctions under a quantifier sets its first side a block deeper. -/
theorem swap (p q : Prop) : And p q <-> And q p := And.comm

theorem neg_all : Not (forall n : Nat, n = 0) :=
  fun h => absurd (h 1) (by omega)

theorem both_all : And (forall n : Nat, 0 <= n) (exists m : Nat, m = m) :=
  And.intro Nat.zero_le (Exists.intro 0 rfl)

theorem chain (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  Nat.le_trans h1 h2

end Ebb
