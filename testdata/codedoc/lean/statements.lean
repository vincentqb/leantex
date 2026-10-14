-- leantex: show = math, code
/-! # Tide arithmetic

Invented facts about tides, each statement set above its code. -/

namespace Tide

/-- The height a tide reaches after `n` steps of `rise`. -/
def height (rise n : Nat) : Nat := rise * n

/-- Rising twice as long reaches twice as high. -/
theorem height_double (rise n : Nat) : height rise (2 * n) = 2 * height rise n := by
  unfold height; exact Nat.mul_left_comm rise 2 n

theorem height_pos {rise n : Nat} (hr : 0 < rise) (hn : 0 < n) : 0 < height rise n := by
  unfold height; exact Nat.mul_pos hr hn

theorem exists_step : ∃ n : Nat, n + 2 = 5 := ⟨3, rfl⟩

theorem le_or_gt (a b : Nat) : a ≤ b ∨ b < a := by omega

theorem swap_and (p q : Prop) : p ∧ q ↔ q ∧ p := And.comm

theorem not_both (p : Prop) : ¬(p ∧ ¬p) := fun h => h.2 h.1

theorem pow_succ' (a n : Nat) : a ^ (n + 1) = a ^ n * a := Nat.pow_succ ..

theorem mem_cons (x : Nat) (xs : List Nat) : x ∈ x :: xs := List.mem_cons_self

theorem sub_le (a b : Nat) : a - b ≤ a := Nat.sub_le a b

theorem div_mod (a b : Nat) : b * (a / b) + a % b = a := Nat.div_add_mod a b

theorem dvd_mul (a b : Nat) : a ∣ a * b := Nat.dvd_mul_right a b

theorem neg_neg' (z : Int) : -(-z) = z := Int.neg_neg z

def total {α : Type} [Add α] (zero : α) (xs : List α) : α := xs.foldl (· + ·) zero

theorem strict_hyp (h : ∀ ⦃n : Nat⦄, n = 0) : False := by
  have := @h 1
  omega

theorem imp_iff (p q : Prop) (_h : p) : q ↔ q := Iff.rfl

private def depth : Nat := 7

theorem depth_val : depth = 7 := rfl

def holds (p : Prop) : Prop := p

theorem holds_ex : holds (∃ n : Nat, n = 0) := ⟨0, rfl⟩

theorem fixes (f : Nat → Nat) (h : f 0 = 0) : f (f 0) = 0 := by rw [h, h]

open Nat in
/-- Read under an open namespace. -/
theorem succ_eq (n : Nat) : succ n = n + 1 := rfl

open Nat in
theorem succ_pos' (n : Nat) : 0 < succ n := Nat.succ_pos n

theorem iff_nest (p : Prop) : p ↔ (p ↔ True) := by simp

theorem chars_len : "a~b^c\\d\n\t\"{}_#$%&".length = 17 := rfl

universe u

def same (α : Type u) (a : α) : α := a

theorem pos_ne {n : Nat} {h : n > 0} : n ≠ 0 := by omega

theorem nz (n : Nat) [NeZero n] : n ≠ 0 := NeZero.ne n

theorem dep_hyp (n : Nat) (h : 0 < n) : (⟨0, h⟩ : Fin n).val = 0 := rfl

theorem nested_dep (f : (n : Nat) → n > 0 → Nat) (hf : ∀ n (h : n > 0), f n h = n) :
    f 1 Nat.one_pos = 1 := hf 1 _

theorem long_sum (a b c d e f g h i j k l m n o p q r : Nat) :
    a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r =
      r + q + p + o + n + m + l + k + j + i + h + g + f + e + d + c + b + a := by omega

theorem unfinished (n : Nat) : n + 0 = n := by
  exact Nat.zero_add n

theorem rests (n : Nat) : n + 0 = n := unfinished n

theorem placeholder (n : Nat) : n = Nat.notAThing n := rfl

theorem refused (n : Nat) : n + (1 : String) = n := rfl

end Tide
