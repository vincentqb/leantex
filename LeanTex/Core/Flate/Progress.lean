namespace LeanTex.Core.Flate.Progress

/-- A loop's partial-state invariant records its consumed index. An early
return must already establish the final postcondition. -/
theorem forIn_range'_exact {σ : Type} (P : Nat → σ → Prop) (Q : σ → Prop)
    (f : Nat → σ → Id (ForInStep σ)) (lo count : Nat) (init : σ)
    (h0 : P lo init)
    (hstep : ∀ i, lo ≤ i → i < lo + count → ∀ s, P i s →
      match (f i s).run with
      | .done s' => Q s'
      | .yield s' => P (i + 1) s')
    (hfinish : ∀ s, P (lo + count) s → Q s) :
    Q (forIn (List.range' lo count) init f : Id σ).run := by
  induction count generalizing lo init with
  | zero => exact hfinish init (by simpa using h0)
  | succ count ih =>
    have hs := hstep lo (Nat.le_refl _) (by omega) init h0
    rw [List.range'_succ, List.forIn_cons]
    show Q (match (f lo init).run with
      | .done s => s
      | .yield s => (forIn (List.range' (lo + 1) count) s f : Id σ).run)
    cases heq : (f lo init).run with
    | done s => rw [heq] at hs; exact hs
    | yield s =>
      rw [heq] at hs
      exact ih (lo + 1) s hs
        (fun i hlo hhi s hp => hstep i (by omega) (by omega) s hp)
        (fun s hp => hfinish s
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp))

/-- Progress and early-return postconditions for the actual range loop. -/
theorem forIn_range_exact {σ : Type} (P : Nat → σ → Prop) (Q : σ → Prop)
    (f : Nat → σ → Id (ForInStep σ)) (lo hi : Nat) (init : σ)
    (hle : lo ≤ hi) (h0 : P lo init)
    (hstep : ∀ i, lo ≤ i → i < hi → ∀ s, P i s →
      match (f i s).run with
      | .done s' => Q s'
      | .yield s' => P (i + 1) s')
    (hfinish : ∀ s, P hi s → Q s) :
    Q (forIn [lo:hi] init f : Id σ).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_range'_exact P Q f _ _ init h0
  · intro i hlo hhi s hp
    apply hstep i hlo _ s hp
    simp [Std.Legacy.Range.size] at hhi
    omega
  · intro s hp
    apply hfinish s
    simpa [Std.Legacy.Range.size, Nat.add_sub_cancel' hle] using hp

/-- A value invariant records the consumed prefix, including when the values
repeat. Early returns must already establish the final postcondition. -/
theorem forIn_list_exact {α σ : Type} (P : List α → σ → Prop) (Q : σ → Prop)
    (f : α → σ → Id (ForInStep σ)) (xs consumed : List α) (init : σ)
    (h0 : P consumed init)
    (hstep : ∀ before x after, xs = before ++ x :: after → ∀ s,
      P (consumed ++ before) s →
        match (f x s).run with
        | .done s' => Q s'
        | .yield s' => P (consumed ++ before ++ [x]) s')
    (hfinish : ∀ s, P (consumed ++ xs) s → Q s) :
    Q (forIn xs init f : Id σ).run := by
  induction xs generalizing consumed init with
  | nil => exact hfinish init (by simpa using h0)
  | cons x xs ih =>
    have hs := hstep [] x xs rfl init (by simpa using h0)
    rw [List.forIn_cons]
    show Q (match (f x init).run with
      | .done s => s
      | .yield s => (forIn xs s f : Id σ).run)
    cases heq : (f x init).run with
    | done s => rw [heq] at hs; exact hs
    | yield s =>
      rw [heq] at hs
      apply ih (consumed ++ [x]) s (by simpa using hs)
      · intro before y after hrest s hs
        have hwhole : x :: xs = (x :: before) ++ y :: after := by
          simp only [List.cons_append, hrest]
        simpa only [List.append_assoc, List.singleton_append] using
          hstep (x :: before) y after hwhole s
            (by simpa only [List.append_assoc, List.singleton_append] using hs)
      · intro s hs
        apply hfinish s
        simpa only [List.append_assoc, List.singleton_append] using hs

/-- The consumed-prefix invariant applies to the actual array loop. -/
theorem forIn_array_exact {α σ : Type} (P : List α → σ → Prop) (Q : σ → Prop)
    (f : α → σ → Id (ForInStep σ)) (xs : Array α) (init : σ)
    (h0 : P [] init)
    (hstep : ∀ before x after, xs.toList = before ++ x :: after → ∀ s,
      P before s →
        match (f x s).run with
        | .done s' => Q s'
        | .yield s' => P (before ++ [x]) s')
    (hfinish : ∀ s, P xs.toList s → Q s) :
    Q (forIn xs init f : Id σ).run := by
  rw [← Array.forIn_toList]
  exact forIn_list_exact P Q f xs.toList [] init h0
    (by simpa only [List.nil_append] using hstep)
    (by simpa only [List.nil_append] using hfinish)

end LeanTex.Core.Flate.Progress
