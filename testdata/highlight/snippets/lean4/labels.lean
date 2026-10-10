theorem t (h : ?a:Nat) : True := trivial
example : ~b' ≠ ?x := by simp only [?lemma] -- labels
def notLabel := ?x + ~y
