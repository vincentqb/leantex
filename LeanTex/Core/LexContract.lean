module

public import LeanTex.Core.Lex
import all LeanTex.Core.Lex

namespace LeanTex.Core.Lex

/-- A form whose argument the lexer reads raw: a blind environment's body up to its closer, `\verb`'s
text between two copies of its delimiter, and a url.sty argument with its delimiters. -/
public inductive Capture where
  | env (closer : Array Char)
  | verb
  | url

/-- A line end, which no one-line capture crosses. -/
@[expose] public def lineEnd (c : Char) : Bool := c == '\n' || c == '\r'

/-- The characters of `p` stand in `cs` from `m`. -/
@[expose] public def occursAt (cs p : Array Char) (m : Nat) : Prop :=
  ∀ t (h : t < p.size), cs[m + t]? = some p[t]

/-- Every character strictly between `a` and `b` is neither `d` nor a line end. -/
@[expose] public def plainBetween (cs : Array Char) (d : Char) (a b : Nat) : Prop :=
  ∀ m, a < m → m < b → ∃ c, cs[m]? = some c ∧ c ≠ d ∧ lineEnd c = false

/-- What a capture read from `j` owes: its text is the source characters it spans, `\verb*` showing
each space as `␣`, ending at its closer's first copy, or where none stands on its line or in the input. -/
@[expose] public def Capture.Exact : Capture → Array Char → Nat → Nat × Bool × String → Prop
  | .env closer, cs, start, (stop, closed, s) =>
    ∃ k, s.toList = (cs.extract start k).toList ∧
      (∀ m, start ≤ m → m < k → ¬ occursAt cs closer m) ∧
      (if closed then start ≤ k ∧ occursAt cs closer k ∧ stop = k + closer.size
        else k = cs.size ∧ stop = cs.size)
  | .verb, cs, j, (stop, closed, s) =>
    let star := cs[j]? == some '*'
    let k₀ := if star then j + 1 else j
    ∃ k, k₀ ≤ k ∧ (∀ m, k₀ ≤ m → m < k → cs[m]? = some ' ' ∨ cs[m]? = some '\t') ∧
      (∀ c, cs[k]? = some c → c ≠ ' ' ∧ c ≠ '\t') ∧
      match cs[k]? with
      | some d =>
        if lineEnd d then stop = k ∧ closed = false ∧ s = ""
        else ∃ e, k < e ∧ plainBetween cs d k e ∧
          s.toList = (cs.extract (k + 1) e).toList.map
            (fun c => if star && c == ' ' then '␣' else c) ∧
          (closed = true ↔ cs[e]? = some d) ∧
          (closed = false → ∀ c, cs[e]? = some c → lineEnd c = true) ∧
          stop = (if closed then e + 1 else e)
      | none => stop = k ∧ closed = false ∧ s = ""
  | .url, cs, k, (stop, closed, s) =>
    ∃ d e, cs[k]? = some d ∧ lineEnd d = false ∧ k < e ∧ plainBetween cs d k e ∧
      s.toList = (cs.extract k stop).toList ∧
      (closed = true ↔ cs[e]? = some d) ∧
      (closed = false → ∀ c, cs[e]? = some c → lineEnd c = true) ∧
      stop = (if closed then e + 1 else e)

private theorem scanWhile_ge (cs : Array Char) (j : Nat) (p : Char → Bool) :
    j ≤ scanWhile cs j p := by
  fun_induction scanWhile cs j p <;> omega

private theorem scanWhile_all (cs : Array Char) (j : Nat) (p : Char → Bool) :
    ∀ m, j ≤ m → m < scanWhile cs j p → ∃ c, cs[m]? = some c ∧ p c = true := by
  fun_induction scanWhile cs j p with
  | case1 j h hp ih =>
    intro m hm hlt
    by_cases he : m = j
    · subst he; exact ⟨cs[m], by simp [h], hp⟩
    · exact ih m (by omega) hlt
  | case2 j _ _ => intro m hm hlt; omega
  | case3 j _ => intro m hm hlt; omega

private theorem scanWhile_stop (cs : Array Char) (j : Nat) (p : Char → Bool) :
    ∀ c, cs[scanWhile cs j p]? = some c → p c = false := by
  fun_induction scanWhile cs j p with
  | case1 _ _ _ ih => exact ih
  | case2 j h hp =>
    intro c hc
    rw [Array.getElem?_eq_getElem h] at hc
    cases hc
    simpa using hp
  | case3 j h =>
    intro c hc
    rw [Array.getElem?_eq_none (by omega)] at hc
    cases hc

private theorem strFrom_toList (cs : Array Char) (a b : Nat) :
    (strFrom cs a b).toList = (cs.extract a b).toList := by
  unfold strFrom
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList]
  have go : ∀ (l : List Char) (s : String), (l.foldl String.push s).toList = s.toList ++ l := by
    intro l
    induction l with
    | nil => simp
    | cons c rest ih => intro s; simp [ih]
  simpa using go (cs.extract a b).toList ""

private theorem matchFrom_iff (cs ps : Array Char) (i k : Nat) :
    matchFrom cs ps i k = true ↔ ∀ t, k ≤ t → (h : t < ps.size) → cs[i + t]? = some ps[t] := by
  fun_induction matchFrom cs ps i k with
  | case1 k h c hc ih =>
    rw [Bool.and_eq_true, ih]
    constructor
    · intro ⟨h1, h2⟩ t ht htp
      by_cases he : t = k
      · subst he; rw [hc]; simp at h1; rw [h1]
      · exact h2 t (by omega) htp
    · intro hall
      refine ⟨?_, fun t ht htp => hall t (by omega) htp⟩
      have := hall k (Nat.le_refl k) h
      rw [hc] at this
      simp at this
      simp [this]
  | case2 k h hc =>
    simp only [Bool.false_eq_true, false_iff]
    intro hall
    have := hall k (Nat.le_refl k) h
    rw [hc] at this
    cases this
  | case3 k h =>
    simp only [true_iff]
    intro t ht htp
    omega

private theorem matchAt_occurs (cs ps : Array Char) (i : Nat) (h : matchAt cs i ps = true) :
    occursAt cs ps i := by
  unfold matchAt at h
  rw [Bool.and_eq_true] at h
  intro t ht
  exact (matchFrom_iff cs ps i 0).1 h.2 t (Nat.zero_le t) ht

private theorem occurs_matchAt (cs ps : Array Char) (i : Nat) (hi : i < cs.size)
    (h : occursAt cs ps i) : matchAt cs i ps = true := by
  unfold matchAt
  rw [Bool.and_eq_true]
  refine ⟨?_, (matchFrom_iff cs ps i 0).2 fun t _ ht => h t ht⟩
  by_cases hp : ps.size = 0
  · simp [hp]; omega
  · have := h (ps.size - 1) (by omega)
    have hlt : i + (ps.size - 1) < cs.size := by
      rcases Nat.lt_or_ge (i + (ps.size - 1)) cs.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at this; cases this
    simp; omega

private theorem findSub_some (cs pat : Array Char) (k r : Nat) (h : findSub cs k pat = some r) :
    k ≤ r ∧ r < cs.size ∧ matchAt cs r pat = true ∧
      ∀ m, k ≤ m → m < r → matchAt cs m pat = false := by
  fun_induction findSub cs k pat with
  | case1 k hk hm =>
    cases h
    exact ⟨Nat.le_refl _, hk, hm, fun m h1 h2 => by omega⟩
  | case2 k hk hm ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih h
    refine ⟨by omega, h1, h2, fun m hm1 hm2 => ?_⟩
    by_cases he : m = k
    · subst he; simpa using hm
    · exact h3 m (by omega) hm2
  | case3 _ _ => cases h

private theorem findSub_none (cs pat : Array Char) (k : Nat) (h : findSub cs k pat = none) :
    ∀ m, k ≤ m → m < cs.size → matchAt cs m pat = false := by
  fun_induction findSub cs k pat with
  | case1 _ _ _ => cases h
  | case2 k hk hm ih =>
    intro m hm1 hm2
    by_cases he : m = k
    · subst he; simpa using hm
    · exact ih h m (by omega) hm2
  | case3 k hk => intro m hm1 hm2; omega

private theorem envRead_exact (cs closer : Array Char) (start : Nat) :
    (Capture.env closer).Exact cs start (envRead cs start closer) := by
  unfold envRead
  cases hf : findSub cs start closer with
  | some k =>
    obtain ⟨h1, hk, h2, h3⟩ := findSub_some cs closer start k hf
    refine ⟨k, strFrom_toList cs start k, fun m hm1 hm2 ho => ?_, ?_⟩
    · have := occurs_matchAt cs closer m (by omega) ho
      rw [h3 m hm1 hm2] at this
      cases this
    · simp only [↓reduceIte, and_true]
      exact ⟨h1, matchAt_occurs cs closer k h2⟩
  | none =>
    refine ⟨cs.size, strFrom_toList cs start cs.size, fun m hm1 hm2 ho => ?_, ?_⟩
    · have := occurs_matchAt cs closer m hm2 ho
      rw [findSub_none cs closer start hf m hm1 hm2] at this
      cases this
    · simp

private theorem lineEnd_iff (c : Char) : lineEnd c = true ↔ c = '\n' ∨ c = '\r' := by
  simp [lineEnd]

private theorem verbRead_exact (cs : Array Char) (j : Nat) :
    Capture.verb.Exact cs j (verbRead cs j) := by
  unfold verbRead
  simp only [Capture.Exact]
  generalize hstar : (cs[j]? == some '*') = star
  generalize hk : scanWhile cs (if star = true then j + 1 else j) (fun c => c == ' ' || c == '\t') = k
  refine ⟨k, hk ▸ scanWhile_ge _ _ _, fun m h1 h2 => ?_, fun c hc => ?_, ?_⟩
  · obtain ⟨c, hc, hp⟩ := scanWhile_all cs _ _ m h1 (hk ▸ h2)
    simp at hp
    rcases hp with hp | hp <;> simp [hc, hp]
  · have := scanWhile_stop cs _ _ c (hk ▸ hc)
    simp at this
    exact this
  · cases hd : cs[k]? with
    | none => simp
    | some d =>
      simp only [Option.getD_some]
      by_cases hl : lineEnd d = true
      · rcases (lineEnd_iff d).1 hl with h | h <;> subst h <;> simp [lineEnd]
      · have hl' : (d == '\n' || d == '\r') = false := by simpa [lineEnd] using hl
        simp only [hl, Bool.false_eq_true, ↓reduceIte, hl']
        generalize he : scanWhile cs (k + 1) (fun c => c != d && c != '\n' && c != '\r') = e
        have hle := scanWhile_ge cs (k + 1) (fun c => c != d && c != '\n' && c != '\r')
        have hd' : (d != '\n' && d != '\r') = true := by
          simp only [lineEnd, Bool.or_eq_true, beq_iff_eq, not_or] at hl
          simp [hl.1, hl.2]
        refine ⟨e, by omega, fun m h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
        · obtain ⟨c, hc, hp⟩ := scanWhile_all cs _ _ m (by omega) (he ▸ h2)
          refine ⟨c, hc, ?_, ?_⟩
          · simp at hp; exact hp.1.1
          · simp at hp; simp [lineEnd, hp.1.2, hp.2]
        · cases star <;> simp [strFrom_toList]
        · simp [hd']
        · intro hcl c hc
          have hq := scanWhile_stop cs _ _ c (he ▸ hc)
          have hne : c ≠ d := by
            intro hcd; subst hcd; simp [hd', hc] at hcl
          simp [hne] at hq
          simp [lineEnd]
          rcases Classical.em (c = '\n') with h | h
          · exact Or.inl h
          · exact Or.inr (hq h)
        · simp [hd']

private theorem guard_bind_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {x : α}
    (h : (guard p : Option Unit).bind f = some x) : p ∧ f () = some x := by
  unfold guard at h
  by_cases hp : p
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
  · simp only [hp, ↓reduceIte] at h; cases h

private theorem urlFrom_exact (cs : Array Char) (k : Nat) (r : Nat × Bool × String)
    (h : urlFrom cs k = some r) : Capture.url.Exact cs k r := by
  unfold urlFrom at h
  cases hd : cs[k]? with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    obtain ⟨hg, h⟩ := guard_bind_some h
    obtain ⟨_, h⟩ := guard_bind_some h
    obtain ⟨_, h⟩ := guard_bind_some h
    obtain ⟨_, h⟩ := guard_bind_some h
    generalize he : scanWhile cs (k + 1) (fun c => c != d && c != '\n' && c != '\r') = e at h
    have hle := scanWhile_ge cs (k + 1) (fun c => c != d && c != '\n' && c != '\r')
    have hl : lineEnd d = false := by
      cases hc : lineEnd d
      · rfl
      · rcases (lineEnd_iff d).1 hc with h' | h' <;> subst h' <;> simp at hg
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨d, e, hd, hl, by omega, fun m h1 h2 => ?_, strFrom_toList cs k _, by simp, ?_, ?_⟩
    · obtain ⟨c, hc, hp⟩ := scanWhile_all cs _ _ m (by omega) (he ▸ h2)
      refine ⟨c, hc, ?_, ?_⟩
      · simp at hp; exact hp.1.1
      · simp at hp; simp [lineEnd, hp.1.2, hp.2]
    · intro hcl c hc
      have hq := scanWhile_stop cs _ _ c (he ▸ hc)
      have hne : c ≠ d := by
        intro hcd; subst hcd; simp [hc] at hcl
      simp [hne] at hq
      simp [lineEnd]
      rcases Classical.em (c = '\n') with h | h
      · exact Or.inl h
      · exact Or.inr (hq h)
    · by_cases hc : cs[e]? = some d <;> simp [hc]

/-- Each capture the lexer's raw readers make is exactly the source characters it spans, `\verb*`
showing each space as `␣`: a blind environment's body before any rewrite, `\verb`'s text, and a
url.sty argument from the delimiter its gap leads to. -/
public theorem lex_verbatim_exact (cs : Array Char) :
    (∀ closer start, (Capture.env closer).Exact cs start (envRead cs start closer)) ∧
    (∀ j, Capture.verb.Exact cs j (verbRead cs j)) ∧
    (∀ j r, urlDelimited cs j = some r →
      ∃ k, argGap cs j (comments := false) = some k ∧ Capture.url.Exact cs k r) := by
  refine ⟨fun closer start => envRead_exact cs closer start, verbRead_exact cs, fun j r h => ?_⟩
  unfold urlDelimited at h
  cases hg : argGap cs j (comments := false) with
  | none => simp [hg] at h
  | some k =>
    simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨k, rfl, urlFrom_exact cs k r h⟩

end LeanTex.Core.Lex
