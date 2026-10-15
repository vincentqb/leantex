module

public import Std.Data.HashMap

/-! Names claimed apart: a base takes its first free numbered form, and a memo per base keeps
each claim's probing from re-reading the forms earlier claims hold. -/

namespace LeanTex.Core.NameClaim

/-- How a base's forms from the second on are spelled: never the base, never one form twice. -/
public structure Spelling where
  spell : String → Nat → String
  spell_inj : ∀ base i j, 2 ≤ i → 2 ≤ j → spell base i = spell base j → i = j
  spell_ne : ∀ base n, 2 ≤ n → spell base n ≠ base

/-- The `n`th form of `base`: `base` itself, then `s.spell base n` from the second. -/
public def formAt (s : Spelling) (base : String) (n : Nat) : String :=
  if n ≤ 1 then base else s.spell base n

/-- The first free form of `base` among `taken` (`base`, then its second form, …), and the
holder met first whose title is not `text`. -/
public def probe (s : Spelling) (taken : Std.HashMap String String) (base text : String) :
    String × Option String := Id.run do
  let mut id := base
  let mut clash : Option String := none
  for n in [2 : taken.size + 3] do
    match taken.get? id with
    | some holder =>
      if holder != text && clash.isNone then
        clash := some holder
      id := s.spell base n
    | none => break
  return (id, clash)

/-- The first two distinct titles holding a run of forms, in order: all a clash reads of it. -/
public structure Holders where
  first : Option String := none
  other : Option String := none

/-- The run's holders after one more form held by `title`. -/
public def Holders.note (h : Holders) (title : String) : Holders :=
  match h.first with
  | none => { first := some title }
  | some f => if h.other.isNone && f != title then { h with other := some title } else h

/-- The holder of the run met first whose title is not `text`. -/
public def Holders.clash (h : Holders) (text : String) : Option String :=
  h.first.bind fun f => if f != text then some f else h.other

/-- From the `k`th form of `base`, probing at most `left` forms: the index of the first free
one, and the holders of the forms before it noted onto `held`. -/
public def scanFrom (s : Spelling) (taken : Std.HashMap String String) (base : String) :
    Nat → Nat → Holders → Nat × Holders
  | k, 0, held => (k, held)
  | k, left + 1, held =>
    match taken[formAt s base k]? with
    | some h => scanFrom s taken base (k + 1) left (held.note h)
    | none => (k, held)

/-- The names claimed so far, each with its holder's title, and per base the index of its first
form that may be free with the holders of the forms before it. -/
public structure Ledger where
  taken : Std.HashMap String String := {}
  next : Std.HashMap String (Nat × Holders) := {}

/-- One claim over a ledger, probing from the memo's index for `base`: the form, the holder met
first whose title differs from `text`, and the ledger holding the form. -/
@[expose] public def Ledger.claim (c : Ledger) (s : Spelling) (base text : String) :
    String × Option String × Ledger :=
  let e := (c.next.get? base).getD (1, {})
  let r := scanFrom s c.taken base e.1 (c.taken.size + 2 - e.1) e.2
  let id := formAt s base r.1
  (id, r.2.clash text,
    { taken := c.taken.insert id text, next := c.next.insert base (r.1 + 1, r.2.note text) })

/-- The holders of `base`'s forms `1` to `k` in `taken`, or `none` when one of them is free. -/
public def heldRun (s : Spelling) (taken : Std.HashMap String String) (base : String) :
    Nat → Option Holders
  | 0 => some {}
  | k + 1 => (heldRun s taken base k).bind fun h => (taken[formAt s base (k + 1)]?).map h.note

/-- Every memo entry is a lower bound: the forms of its base before its index are held, by the
titles it notes. -/
public def Ledger.Inv (c : Ledger) (s : Spelling) : Prop :=
  ∀ base k held, c.next.get? base = some (k, held) →
    1 ≤ k ∧ heldRun s c.taken base (k - 1) = some held

/-- A base and its numbered forms, `base-2`, `base-3`, …. -/
public def Spelling.dashed : Spelling where
  spell base n := s!"{base}-{n}"
  spell_inj base i j _ _ h := by
    have h' := congrArg String.toList ((String.append_right_inj (base ++ "-")).mp h)
    simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at h'
    rw [← Nat.ofDigitChars_ten_toDigits (n := i), ← Nat.ofDigitChars_ten_toDigits (n := j), h']
  spell_ne base n _ h := by
    have := congrArg String.length h
    simp only [String.length_append] at this
    have : (toString base).length = base.length := rfl
    have : (toString "-").length = 1 := rfl
    omega

/-- A name and its numbered forms, `name (2)`, `name (3)`, …. -/
public def Spelling.parenthesized : Spelling where
  spell name n := s!"{name} ({n})"
  spell_inj name i j _ _ h := by
    simp only [String.append_assoc] at h
    have h1 := (String.append_right_inj name).mp h
    have h2 := (String.append_right_inj " (").mp h1
    have h3 := congrArg String.toList ((String.append_left_inj ")").mp h2)
    simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at h3
    rw [← Nat.ofDigitChars_ten_toDigits (n := i), ← Nat.ofDigitChars_ten_toDigits (n := j), h3]
  spell_ne name n _ h := by
    have := congrArg String.length h
    simp only [String.length_append] at this
    have : (toString name).length = name.length := rfl
    have : (toString " (").length = 2 := rfl
    omega

theorem formAt_succ (s : Spelling) (base : String) {k : Nat} (hk : 1 ≤ k) :
    formAt s base (k + 1) = s.spell base (k + 1) := by
  simp only [formAt]; split <;> first | omega | rfl

theorem formAt_inj (s : Spelling) (base : String) {i j : Nat} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : formAt s base i = formAt s base j) : i = j := by
  unfold formAt at h
  split at h <;> split at h
  · omega
  · exact absurd h.symm (s.spell_ne base j (by omega))
  · exact absurd h (s.spell_ne base i (by omega))
  · exact s.spell_inj base i j (by omega) (by omega) h

theorem Holders.note_clash (h : Holders) (t text : String) :
    (h.note t).clash text =
      if t != text && (h.clash text).isNone then some t else h.clash text := by
  obtain ⟨f, o⟩ := h
  cases f with
  | none => simp [Holders.note, Holders.clash]
  | some f =>
    by_cases hft : f = text
    · subst hft
      cases o with
      | none =>
        by_cases htf : t = f
        · subst htf; simp [Holders.note, Holders.clash]
        · simp [Holders.note, Holders.clash, htf, Ne.symm htf]
      | some o => simp [Holders.note, Holders.clash]
    · by_cases htf : f = t
      · subst htf; cases o <;> simp [Holders.note, Holders.clash, hft]
      · cases o <;> simp [Holders.note, Holders.clash, hft, htf]

theorem forIn_scan (s : Spelling) (taken : Std.HashMap String String) (base text : String)
    (f : Nat → String × Option String → Id (ForInStep (String × Option String)))
    (hf : ∀ i id clash, f i (id, clash) = match taken.get? id with
      | some holder => ForInStep.yield (s.spell base i,
          if holder != text && clash.isNone then some holder else clash)
      | none => ForInStep.done (id, clash)) :
    ∀ (n k : Nat) (held : Holders), 1 ≤ k →
      (forIn (List.range' (k + 1) n) (formAt s base k, held.clash text) f : Id _).run =
        (formAt s base (scanFrom s taken base k n held).1,
          (scanFrom s taken base k n held).2.clash text) := by
  intro n
  induction n with
  | zero => intro k held _; simp [scanFrom]
  | succ n ih =>
    intro k held hk
    rw [List.range'_succ, List.forIn_cons, hf, Std.HashMap.get?_eq_getElem?]
    simp only [scanFrom]
    cases ht : taken[formAt s base k]? with
    | none => rfl
    | some holder =>
      have := ih (k + 1) (held.note holder) (by omega)
      rw [Holders.note_clash, formAt_succ s base hk] at this
      exact this

theorem forIn_scan_base (s : Spelling) (taken : Std.HashMap String String)
    (base text : String) (n : Nat)
    (f : Nat → String × Option String → Id (ForInStep (String × Option String)))
    (hf : ∀ i id clash, f i (id, clash) = match taken.get? id with
      | some holder => ForInStep.yield (s.spell base i,
          if holder != text && clash.isNone then some holder else clash)
      | none => ForInStep.done (id, clash)) :
    (forIn (List.range' 2 n) (base, none) f : Id _).run =
      (formAt s base (scanFrom s taken base 1 n {}).1,
        (scanFrom s taken base 1 n {}).2.clash text) :=
  forIn_scan s taken base text f hf n 1 {} (Nat.le_refl 1)

theorem probe_scan_exact (s : Spelling) (taken : Std.HashMap String String) (base text : String) :
    probe s taken base text =
      (formAt s base (scanFrom s taken base 1 (taken.size + 1) {}).1,
        (scanFrom s taken base 1 (taken.size + 1) {}).2.clash text) := by
  unfold probe
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have e : [2:taken.size + 3].size = taken.size + 1 := by
    simp only [Std.Legacy.Range.size]; omega
  rw [e]
  simp only [Id.run_bind]
  rw [forIn_scan_base s taken base text]
  · rfl
  · intro i id clash
    dsimp only
    cases taken.get? id with
    | none => rfl
    | some holder => dsimp only; split <;> rfl

theorem heldRun_succ {s : Spelling} {taken : Std.HashMap String String} {base : String}
    {k : Nat} {h : Holders} (hr : heldRun s taken base (k + 1) = some h) :
    ∃ h₀ t, heldRun s taken base k = some h₀ ∧ taken[formAt s base (k + 1)]? = some t ∧
      h = h₀.note t := by
  simp only [heldRun, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
  obtain ⟨h₀, h0, t, ht, rfl⟩ := hr
  exact ⟨h₀, t, h0, ht, rfl⟩

theorem heldRun_prefix {s : Spelling} {taken : Std.HashMap String String} {base : String} :
    ∀ {m : Nat} {h : Holders}, heldRun s taken base m = some h →
      ∀ i, i ≤ m → ∃ h', heldRun s taken base i = some h'
  | 0, _, hr, i, hi => by
    obtain rfl : i = 0 := by omega
    exact ⟨_, hr⟩
  | m + 1, _, hr, i, hi => by
    by_cases him : i = m + 1
    · exact ⟨_, him ▸ hr⟩
    · obtain ⟨h₀, _, h0, _, _⟩ := heldRun_succ hr
      exact heldRun_prefix h0 i (by omega)

theorem heldRun_held {s : Spelling} {taken : Std.HashMap String String} {base : String}
    {m : Nat} {h : Holders} (hr : heldRun s taken base m = some h) :
    ∀ i, 1 ≤ i → i ≤ m → formAt s base i ∈ taken := by
  intro i hi him
  obtain ⟨h', hp⟩ := heldRun_prefix hr i him
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨_, t, _, ht, _⟩ := heldRun_succ hp
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [ht])

/-- A held run of `m` forms names `m` distinct keys. -/
theorem heldRun_le_size {s : Spelling} {taken : Std.HashMap String String} {base : String}
    {m : Nat} {h : Holders} (hr : heldRun s taken base m = some h) : m ≤ taken.size := by
  let l := (List.range m).map fun i => formAt s base (i + 1)
  have hnd : l.Nodup := by
    refine List.Pairwise.map _ (fun a b hab heq => hab ?_) List.nodup_range
    have := formAt_inj s base (by omega) (by omega) heq
    omega
  have hsub : l ⊆ taken.keys := by
    intro x hx
    simp only [l, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Std.HashMap.mem_keys.mpr (heldRun_held hr (i + 1) (by omega) (by omega))
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa [l] using this

theorem scanFrom_restart {s : Spelling} {taken : Std.HashMap String String}
    {base : String} :
    ∀ (m k left : Nat) (held held' : Holders), 1 ≤ k → m ≤ left →
      heldRun s taken base (k - 1) = some held →
      heldRun s taken base (k - 1 + m) = some held' →
      scanFrom s taken base k left held = scanFrom s taken base (k + m) (left - m) held'
  | 0, k, left, held, held', _, _, h0, hm => by
    rw [Nat.add_zero] at hm
    rw [h0] at hm
    cases hm
    rfl
  | m + 1, k, left, held, held', hk, hml, h0, hm => by
    obtain ⟨hk', hpk⟩ := heldRun_prefix hm k (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨h₀, t, hj, ht, rfl⟩ := heldRun_succ hpk
    rw [Nat.add_sub_cancel] at h0
    rw [h0] at hj
    cases hj
    obtain ⟨l, rfl⟩ : ∃ l, left = l + 1 := ⟨left - 1, by omega⟩
    simp only [scanFrom, ht]
    have := scanFrom_restart m (j + 1 + 1) l (held.note t) held' (by omega) (by omega)
      (by simpa using hpk) (by rw [show j + 1 + 1 - 1 + m = j + 1 - 1 + (m + 1) by omega]; exact hm)
    rw [this]
    congr 1 <;> omega

theorem scanFrom_free {s : Spelling} {taken : Std.HashMap String String}
    {base : String} :
    ∀ (left k : Nat) (held : Holders), 1 ≤ k → heldRun s taken base (k - 1) = some held →
      let r := scanFrom s taken base k left held
      k ≤ r.1 ∧ heldRun s taken base (r.1 - 1) = some r.2 ∧
        (r.1 < k + left → taken[formAt s base r.1]? = none) ∧ r.1 ≤ k + left
  | 0, k, held, _, h0 => by simp [scanFrom, h0]
  | left + 1, k, held, hk, h0 => by
    simp only [scanFrom]
    cases ht : taken[formAt s base k]? with
    | none => simp [h0, ht]
    | some t =>
      dsimp only
      have hr : heldRun s taken base (k + 1 - 1) = some (held.note t) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at h0
        simp [heldRun, h0, ht]
      obtain ⟨h1, h2, h3, h4⟩ := scanFrom_free left (k + 1) (held.note t) (by omega) hr
      exact ⟨by omega, h2, fun hlt => h3 (by omega), by omega⟩

public theorem Ledger.empty_pinned (s : Spelling) : ({} : Ledger).Inv s := by
  intro base k held h
  simp at h

theorem Ledger.entry_held {c : Ledger} {s : Spelling} (hc : c.Inv s) (base : String) :
    1 ≤ ((c.next.get? base).getD (1, {})).1 ∧
      heldRun s c.taken base (((c.next.get? base).getD (1, {})).1 - 1) =
        some ((c.next.get? base).getD (1, {})).2 := by
  cases hn : c.next.get? base with
  | none => exact ⟨Nat.le_refl 1, rfl⟩
  | some e => exact hc base e.1 e.2 hn

theorem Ledger.claim_exact {c : Ledger} {s : Spelling} (hc : c.Inv s) (base text : String) :
    ((c.claim s base text).1, (c.claim s base text).2.1) = probe s c.taken base text := by
  rw [probe_scan_exact]
  obtain ⟨h1, hr⟩ := c.entry_held hc base
  unfold Ledger.claim
  generalize (c.next.get? base).getD (1, {}) = e at h1 hr ⊢
  have hle := heldRun_le_size hr
  have := scanFrom_restart (e.1 - 1) 1 (c.taken.size + 1) {} e.2 (Nat.le_refl 1) (by omega)
    rfl (by simpa using hr)
  rw [this, show 1 + (e.1 - 1) = e.1 by omega,
    show c.taken.size + 1 - (e.1 - 1) = c.taken.size + 2 - e.1 by omega]

public theorem Ledger.claim_fresh {c : Ledger} {s : Spelling} (hc : c.Inv s) (base text : String) :
    c.taken[(c.claim s base text).1]? = none := by
  obtain ⟨h1, hr⟩ := c.entry_held hc base
  unfold Ledger.claim
  generalize (c.next.get? base).getD (1, {}) = e at h1 hr ⊢
  obtain ⟨_, hs2, hs3, hs4⟩ := scanFrom_free (c.taken.size + 2 - e.1) e.1 e.2 h1 hr
  by_cases hlt : (scanFrom s c.taken base e.1 (c.taken.size + 2 - e.1) e.2).1 <
      e.1 + (c.taken.size + 2 - e.1)
  · exact hs3 hlt
  · have := heldRun_le_size hs2
    omega

public theorem Ledger.claim_pinned {c : Ledger} {s : Spelling} (hc : c.Inv s) (base text : String) :
    (c.claim s base text).2.2.Inv s := by
  have hfree := c.claim_fresh hc base text
  obtain ⟨h1, hr⟩ := c.entry_held hc base
  unfold Ledger.claim at hfree ⊢
  dsimp only at hfree ⊢
  generalize (c.next.get? base).getD (1, {}) = e at h1 hr hfree ⊢
  obtain ⟨hs1, hs2, _, _⟩ := scanFrom_free (c.taken.size + 2 - e.1) e.1 e.2 h1 hr
  generalize scanFrom s c.taken base e.1 (c.taken.size + 2 - e.1) e.2 = r at hs1 hs2 hfree ⊢
  have hmono : ∀ b m h, heldRun s c.taken b m = some h →
      heldRun s (c.taken.insert (formAt s base r.1) text) b m = some h := by
    intro b m
    induction m with
    | zero => intro h hm; simpa [heldRun] using hm
    | succ m ih =>
      intro h hm
      obtain ⟨h₀, t, h0, ht, rfl⟩ := heldRun_succ hm
      have hne : (formAt s base r.1 == formAt s b (m + 1)) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        rw [heq, ht] at hfree
        cases hfree
      simp [heldRun, ih h₀ h0, Std.HashMap.getElem?_insert, hne, ht]
  intro b k' h' hb
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hb
  split at hb
  · rename_i hbb
    have hbb : base = b := by simpa using hbb
    subst hbb
    cases hb
    refine ⟨by omega, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, r.1 = j + 1 := ⟨r.1 - 1, by omega⟩
    rw [hj] at hs2 hmono ⊢
    simp only [Nat.add_sub_cancel] at hs2 ⊢
    simp [heldRun, hmono _ _ _ hs2]
  · obtain ⟨hk1, hkr⟩ := hc b k' h' (by rw [Std.HashMap.get?_eq_getElem?]; exact hb)
    exact ⟨hk1, hmono _ _ _ hkr⟩

/-- Names claimed apart under one spelling, the memo a lower bound for every claim. -/
public structure Claims (s : Spelling) where
  ledger : Ledger
  pinned : ledger.Inv s

public instance {s : Spelling} : EmptyCollection (Claims s) := ⟨⟨{}, Ledger.empty_pinned s⟩⟩

/-- Claim `base`'s first free form for a title `text`: the form, the holder met first whose
title differs, and the claims holding it. -/
@[expose] public def Claims.claim {s : Spelling} (c : Claims s) (base text : String) :
    String × Option String × Claims s :=
  let r := c.ledger.claim s base text
  (r.1, r.2.1, ⟨r.2.2, Ledger.claim_pinned c.pinned base text⟩)

/-- A claim answers as probing every form from the base among the names claimed before it: the
same form, and the same first holder whose title differs. -/
public theorem Claims.claim_exact {s : Spelling} (c : Claims s) (base text : String) :
    ((c.claim base text).1, (c.claim base text).2.1) = probe s c.ledger.taken base text :=
  Ledger.claim_exact c.pinned base text

/-- A claim adds its form, held by its title, to the names claimed before it. -/
public theorem Claims.claim_taken {s : Spelling} (c : Claims s) (base text : String) :
    (c.claim base text).2.2.ledger.taken = c.ledger.taken.insert (c.claim base text).1 text :=
  rfl

/-- A claim's form is none of the names claimed before it. -/
public theorem Claims.claim_fresh {s : Spelling} (c : Claims s) (base text : String) :
    c.ledger.taken[(c.claim base text).1]? = none :=
  Ledger.claim_fresh c.pinned base text

end LeanTex.Core.NameClaim
