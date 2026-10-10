module

public import LeanTex.Core.Dim

/-!
# The decimal printers, digit by digit

What `Sp.toPtString` and `ratString` print, as the characters a reader of
the decimal meets: a sign, the integer part's digits, and — where there is
a fraction — a point and the fraction's digits with its trailing zeros
dropped (`fracDigits`), whose value is the fraction
(`fracDigits_value_exact`): what a reader of the spelling
(`PdfContentLex.numParts?`) needs to recover the printed value.
-/

namespace LeanTex.Core.Dim

/-- A digit list's value, most significant first: what a reader of a
decimal accumulates. -/
@[expose] public def digitsVal (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

private theorem digitsVal_acc (acc : Nat) (b : List Char) :
    b.foldl (fun a c => a * 10 + (c.toNat - 48)) acc = acc * 10 ^ b.length + digitsVal b := by
  induction b generalizing acc with
  | nil => simp [digitsVal]
  | cons c rest ih =>
    simp only [List.foldl_cons, List.length_cons, digitsVal]
    rw [ih, ih (0 * 10 + (c.toNat - 48))]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_succ]
    grind

/-- A digit list's value over an append. -/
public theorem digitsVal_append (a b : List Char) :
    digitsVal (a ++ b) = digitsVal a * 10 ^ b.length + digitsVal b := by
  simp only [digitsVal, List.foldl_append]
  exact digitsVal_acc _ b

private theorem digitsVal_zeros (ds : List Char) (h : ∀ c ∈ ds, c = '0') : digitsVal ds = 0 := by
  induction ds with
  | nil => rfl
  | cons c rest ih =>
    have hc : c = '0' := h c (by simp)
    subst hc
    have hr := ih (fun d hd => h d (by simp [hd]))
    have e : digitsVal ('0' :: rest) = (0 * 10 + ('0'.toNat - 48)) * 10 ^ rest.length + digitsVal rest := by
      simp only [digitsVal, List.foldl_cons]
      exact digitsVal_acc _ rest
    rw [e, hr]
    simp

/-- `kDigits` spells digits. -/
public theorem kDigits_digits (k n : Nat) : ∀ c ∈ kDigits k n, c.isDigit = true := by
  induction k generalizing n with
  | zero => simp [kDigits]
  | succ k ih =>
    intro c hc
    simp only [kDigits, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih (n / 10) c hc
    · rw [Nat.isDigit_digitChar]; exact decide_eq_true (Nat.mod_lt n (by decide))

public theorem kDigits_length (k n : Nat) : (kDigits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [kDigits, ih]

/-- **The last `k` digits are the number modulo `10^k`** (`_exact`). -/
public theorem kDigits_value_exact (k n : Nat) : digitsVal (kDigits k n) = n % 10 ^ k := by
  induction k generalizing n with
  | zero => simp [kDigits, digitsVal, Nat.mod_one]
  | succ k ih =>
    simp only [kDigits]
    rw [digitsVal_append, ih]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_one, digitsVal,
      List.foldl_cons, List.foldl_nil, Nat.zero_mul,
      Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt n (by decide))]
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, Nat.mod_mul]
    grind

private theorem rev_split (l : List Char) :
    l = (l.reverse.dropWhile (· == '0')).reverse ++ (l.reverse.takeWhile (· == '0')).reverse := by
  have h := List.takeWhile_append_dropWhile (p := (· == '0')) (l := l.reverse)
  calc l = l.reverse.reverse := (List.reverse_reverse l).symm
    _ = (l.reverse.takeWhile (· == '0') ++ l.reverse.dropWhile (· == '0')).reverse := by rw [h]
    _ = _ := List.reverse_append

/-- `fracDigits` spells digits. -/
public theorem fracDigits_digits (k fr : Nat) : ∀ c ∈ fracDigits k fr, c.isDigit = true := by
  intro c hc
  have hsplit := rev_split (kDigits k fr)
  apply kDigits_digits k fr c
  rw [hsplit]
  exact List.mem_append_left _ hc

/-- **A fraction's digits are the fraction** (`_exact`): a nonzero fraction
below `10^k` prints at least one digit and at most `k`, and its digits,
scaled back by the trailing zeros dropped, are the fraction. -/
public theorem fracDigits_value_exact (k fr : Nat) (h : fr < 10 ^ k) (h0 : fr ≠ 0) :
    fracDigits k fr ≠ [] ∧ (fracDigits k fr).length ≤ k ∧
      digitsVal (fracDigits k fr) * 10 ^ (k - (fracDigits k fr).length) = fr := by
  have hsplit := rev_split (kDigits k fr)
  have hzeros : ∀ c ∈ ((kDigits k fr).reverse.takeWhile (· == '0')).reverse, c = '0' := by
    intro c hc
    rw [List.mem_reverse] at hc
    have := List.all_eq_true.mp (List.all_takeWhile (p := (· == '0')) (l := (kDigits k fr).reverse)) c hc
    simpa using this
  have hlen : (fracDigits k fr).length + ((kDigits k fr).reverse.takeWhile (· == '0')).reverse.length = k := by
    have := congrArg List.length hsplit
    simp only [List.length_append, kDigits_length] at this
    simp only [fracDigits]
    omega
  have hval := kDigits_value_exact k fr
  rw [hsplit, digitsVal_append, digitsVal_zeros _ hzeros, Nat.mod_eq_of_lt h, Nat.add_zero] at hval
  have hk : k - (fracDigits k fr).length = ((kDigits k fr).reverse.takeWhile (· == '0')).reverse.length := by
    omega
  refine ⟨?_, by omega, ?_⟩
  · intro he
    simp only [fracDigits] at he
    rw [he] at hval
    simp [digitsVal] at hval
    exact h0 hval.symm
  · rw [hk]
    exact hval


/-- **What `toPtString` prints, character by character** (`_exact`): a sign
where the thousandths are negative, the integer part's digits, and where
there is a fraction, a point and its digits (`fracDigits`). -/
public theorem toPtString_chars_exact (x : Sp) :
    (Sp.toPtString x).toList = (if x.toPtMilli < 0 then ['-'] else []) ++
      Nat.toDigits 10 (x.toPtMilli.natAbs / 1000) ++
      (if x.toPtMilli.natAbs % 1000 = 0 then [] else '.' :: fracDigits 3 (x.toPtMilli.natAbs % 1000)) := by
  have ts : ∀ s : String, toString s = s := fun _ => rfl
  unfold Sp.toPtString
  simp only
  by_cases hf : x.toPtMilli.natAbs % 1000 = 0
  · simp only [hf, beq_self_eq_true, ↓reduceIte, List.append_nil]
    by_cases hm : x.toPtMilli < 0 <;> simp [hm, ts]
  · have hf' : (x.toPtMilli.natAbs % 1000 == 0) = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, ↓reduceIte, hf]
    by_cases hm : x.toPtMilli < 0 <;> simp [hm, ts, String.toList_ofList]


/-- **What `ratString` prints, character by character** (`_exact`): the
magnitude rounded once at the ninth decimal (`v`), a sign where the ratio is
negative and rounds to no zero, `v`'s integer part's digits, and where
there is a fraction, a point and its digits (`fracDigits`). -/
public theorem ratString_chars_exact (p q : Int) :
    (ratString p q).toList =
      (if p < 0 ∧ (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs ≠ 0 then ['-'] else []) ++
      Nat.toDigits 10 ((p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs / 1000000000) ++
      (if (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs % 1000000000 = 0 then []
       else '.' :: fracDigits 9 ((p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs % 1000000000)) := by
  have ts : ∀ s : String, toString s = s := fun _ => rfl
  unfold ratString
  simp only
  generalize (p.natAbs * 1000000000 + q.natAbs / 2) / max 1 q.natAbs = v
  by_cases hf : v % 1000000000 = 0
  · simp only [hf, beq_self_eq_true, ↓reduceIte, List.append_nil]
    by_cases hm : p < 0 <;> by_cases hv : v = 0 <;> simp [hm, hv, ts]
  · have hf' : (v % 1000000000 == 0) = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, ↓reduceIte, hf]
    by_cases hm : p < 0 <;> by_cases hv : v = 0 <;> simp [hm, hv, ts]

end LeanTex.Core.Dim
