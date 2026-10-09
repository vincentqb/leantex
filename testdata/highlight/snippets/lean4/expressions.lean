/- A block comment /- with a nested one -/ still open
   across lines -/
-- a line comment with "quotes" and λ
#eval (fun x => x + 1) 41
#check `Nat.succ
#print ``Garden.Plot

def greet (name : String) : String :=
  s!"hello, {name}\n" ++ "tab\there" ++ "quote \" end"

def pick (xs : Array Nat) (i : Nat) : Nat := xs[i]! + xs[0]?.getD 7

def third (xs : Array Nat) (h : 2 < xs.size) : Nat := xs[2]'h + xs[1]!

def shapes : List (ℕ × ℝ) := [(1, 2.5), (2, 3.0e2), (3, .5)]

instance : ToString Unit := ⟨fun _ => "()"⟩

theorem and_swap {p q : Prop} (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

def admitted : ∀ n : Nat, ∃ m, m > n := fun n => ⟨n + 1, by admit⟩

macro "twice" t:term : term => `($t + $t)

def compose (f : β → γ) (g : α → β) : α → γ := f ∘ g
