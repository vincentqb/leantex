module

public import LeanTex.Core.PathData
import LeanTex.Core.PdfNumber

/-! `PathData.parse` reads back what `PathData.render` writes (`parse_render_exact`), for command
lists opening with a moveto whose decimals hold `Dec.ok`. -/

namespace LeanTex.Core.PathData

/-- A digit character's value. -/
private def dval (c : Char) : Nat := c.toNat - 48

private def pushC (r : Run) (c : Char) : Run := r.push (dval c)

private theorem digitRun_append (r : Run) (ds rest : List Char) (hd : ∀ c ∈ ds, c.isDigit = true)
    (hr : ∀ c ∈ rest.head?, c.isDigit = false) :
    digitRun r (ds ++ rest) = (ds.foldl pushC r, rest) := by
  induction ds generalizing r with
  | nil =>
    cases rest with
    | nil => simp [digitRun]
    | cons c cs =>
      have := hr c (by simp)
      simp [digitRun, this]
  | cons c cs ih =>
    have hc := hd c (by simp)
    simp only [List.cons_append, digitRun, hc, ↓reduceIte, List.foldl_cons]
    exact ih _ (fun x hx => hd x (by simp [hx]))

/-- The run invariant: nothing dropped, `kept` the digit count of `acc`. -/
private def Run.inv (r : Run) : Prop :=
  r.dropped = 0 ∧ r.acc < 10 ^ r.kept ∧ (0 < r.kept → 10 ^ (r.kept - 1) ≤ r.acc)

private theorem Run.inv_empty : Run.inv Run.empty := by
  simp [Run.inv, Run.empty]

private theorem Run.push_inv (r : Run) (d : Nat) (hr : r.inv) (hd : d < 10) (hv : r.acc * 10 + d < 10 ^ maxSig) :
    (r.push d).inv ∧ (r.push d).acc = r.acc * 10 + d := by
  obtain ⟨h0, h1, h2⟩ := hr
  unfold Run.push
  by_cases hz : r.acc = 0 ∧ d = 0
  · obtain ⟨ha, hdz⟩ := hz
    simp only [ha, hdz, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    refine ⟨⟨h0, ?_, ?_⟩, by simp⟩
    · simpa [ha] using h1
    · intro hk
      have := h2 hk
      have : 0 < 10 ^ (r.kept - 1) := Nat.pow_pos (by decide)
      omega
  · have hne : (r.acc == 0 && d == 0) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      by_cases ha : r.acc = 0
      · exact Or.inr (fun h => hz ⟨ha, h⟩)
      · exact Or.inl ha
    have hk : r.kept < maxSig := by
      by_cases hk0 : r.kept = 0
      · rw [hk0]; decide
      · have hp := h2 (by omega)
        have : 10 ^ r.kept ≤ r.acc * 10 + d := by
          have e : 10 ^ r.kept = 10 ^ (r.kept - 1) * 10 := by
            rw [← Nat.pow_succ]; congr 1; omega
          omega
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp (by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hk]
    refine ⟨⟨h0, ?_, ?_⟩, ?_⟩
    rotate_left 2
    · trivial
    · show r.acc * 10 + d < 10 ^ (r.kept + 1)
      rw [Nat.pow_succ]
      omega
    · intro _
      show 10 ^ (r.kept + 1 - 1) ≤ r.acc * 10 + d
      simp only [Nat.add_sub_cancel]
      by_cases hk0 : r.kept = 0
      · rw [hk0]
        have : ¬(r.acc = 0 ∧ d = 0) := hz
        have : r.acc = 0 := by
          have : r.acc < 1 := by simpa [hk0] using h1
          omega
        simp only [Nat.pow_zero]
        omega
      · have hp := h2 (by omega)
        have e : 10 ^ r.kept = 10 ^ (r.kept - 1) * 10 := by
          rw [← Nat.pow_succ]; congr 1; omega
        omega


private def dfold (a : Nat) (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + dval c) a

private theorem dfold_ge : ∀ (a : Nat) (ds : List Char), a ≤ dfold a ds
  | a, [] => by simp [dfold]
  | a, c :: cs => by
    have := dfold_ge (a * 10 + dval c) cs
    simp only [dfold, List.foldl_cons] at this ⊢
    omega

private theorem dval_lt {c : Char} (h : c.isDigit = true) : dval c < 10 := by
  unfold Char.isDigit at h
  simp at h
  have : c.toNat ≤ 57 := h.2
  unfold dval
  omega

private theorem pushes_value : ∀ (r : Run) (ds : List Char), r.inv → (∀ c ∈ ds, c.isDigit = true) →
    dfold r.acc ds < 10 ^ maxSig →
    (ds.foldl pushC r).inv ∧ (ds.foldl pushC r).acc = dfold r.acc ds ∧
      (ds.foldl pushC r).count = r.count + ds.length
  | r, [], hr, _, _ => by simp [dfold, hr]
  | r, c :: cs, hr, hd, hv => by
    have hc := hd c (by simp)
    have hge := dfold_ge (r.acc * 10 + dval c) cs
    have hv' : dfold (r.acc * 10 + dval c) cs < 10 ^ maxSig := by simpa [dfold] using hv
    obtain ⟨hi, ha⟩ := Run.push_inv r (dval c) hr (dval_lt hc) (by omega)
    have ih := pushes_value (r.push (dval c)) cs hi (fun x hx => hd x (by simp [hx])) (by rw [ha]; exact hv')
    simp only [List.foldl_cons, pushC, List.length_cons] at ih ⊢
    refine ⟨ih.1, ?_, ?_⟩
    · rw [ih.2.1, ha]; rfl
    · rw [ih.2.2, Run.push_count]; omega


private theorem sign_digit (c : Char) (cs : List Char) (h : c.isDigit = true) : sign (c :: cs) = (false, c :: cs) := by
  unfold sign
  split
  · next heq => cases heq; simp at h
  · next heq => cases heq; simp at h
  · rfl

private theorem exponent_rest (rest : List Char) (hr : ∀ c ∈ rest.head?, c = ' ') : exponent rest = (0, rest) := by
  cases rest with
  | nil => rfl
  | cons c cs =>
    have : c = ' ' := hr c (by simp)
    subst this
    simp [exponent]

private theorem fraction_rest (r : Run) (rest : List Char) (hr : ∀ c ∈ rest.head?, c = ' ') :
    fraction r rest = (r, 0, rest) := by
  cases rest with
  | nil => rfl
  | cons c cs =>
    have : c = ' ' := hr c (by simp)
    subst this
    simp [fraction]

private theorem number_parts (neg : Bool) (ip fp rest : List Char) (hip : ip ≠ [])
    (hd : ∀ c ∈ ip ++ fp, c.isDigit = true) (hr : ∀ c ∈ rest.head?, c = ' ')
    (hv : dfold 0 (ip ++ fp) < 10 ^ maxSig) :
    ∃ r : Run, r.acc = dfold 0 (ip ++ fp) ∧
      number ((if neg then ['-'] else []) ++ ip ++ (if fp.isEmpty then [] else '.' :: fp) ++ rest) =
        (decOf neg r (-(fp.length : Int))).map (·, rest) := by
  obtain ⟨hiv, hacc, hcnt⟩ := pushes_value Run.empty (ip ++ fp) Run.inv_empty hd (by simpa [Run.empty] using hv)
  refine ⟨(ip ++ fp).foldl pushC Run.empty, by simpa [Run.empty] using hacc, ?_⟩
  have hipd : ∀ c ∈ ip, c.isDigit = true := fun c hc => hd c (List.mem_append_left _ hc)
  have hfpd : ∀ c ∈ fp, c.isDigit = true := fun c hc => hd c (List.mem_append_right _ hc)
  have hipv : dfold 0 ip < 10 ^ maxSig := by
    have : dfold 0 (ip ++ fp) = dfold (dfold 0 ip) fp := by simp [dfold, List.foldl_append]
    have := dfold_ge (dfold 0 ip) fp
    omega
  obtain ⟨hiv1, _, hcnt1⟩ := pushes_value Run.empty ip Run.inv_empty hipd (by simpa [Run.empty] using hipv)
  have hsign : sign ((if neg then ['-'] else []) ++ ip ++ (if fp.isEmpty then [] else '.' :: fp) ++ rest) =
      (neg, ip ++ ((if fp.isEmpty then [] else '.' :: fp) ++ rest)) := by
    cases neg with
    | true => simp [sign]
    | false =>
      obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hip
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, List.append_assoc]
      exact sign_digit c _ (hipd c (by simp))
  have hfrHead : ∀ c ∈ ((if fp.isEmpty then [] else '.' :: fp) ++ rest).head?, c.isDigit = false := by
    intro c hc
    by_cases he : fp.isEmpty = true
    · simp only [he, ↓reduceIte, List.nil_append] at hc
      have := hr c hc
      subst this; decide
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.head?_cons,
        Option.mem_def, Option.some.injEq] at hc
      subst hc; decide
  have hip' := digitRun_append Run.empty ip ((if fp.isEmpty then [] else '.' :: fp) ++ rest) hipd hfrHead
  have hfr : fraction (ip.foldl pushC Run.empty) ((if fp.isEmpty then [] else '.' :: fp) ++ rest) =
      ((ip ++ fp).foldl pushC Run.empty, fp.length, rest) := by
    by_cases he : fp.isEmpty = true
    · have : fp = [] := List.isEmpty_iff.mp he
      subst this
      simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append, List.append_nil, List.length_nil]
      exact fraction_rest _ rest hr
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.cons_append, fraction]
      have hfpHead : ∀ c ∈ rest.head?, c.isDigit = false := by
        intro c hc; have := hr c hc; subst this; decide
      rw [digitRun_append _ fp rest hfpd hfpHead]
      simp only [List.foldl_append, Prod.mk.injEq, true_and]
      obtain ⟨_, _, hc2⟩ := pushes_value (ip.foldl pushC Run.empty) fp hiv1 hfpd (by
        rw [‹(List.foldl pushC Run.empty ip).acc = _›]
        have : dfold 0 (ip ++ fp) = dfold (dfold 0 ip) fp := by simp [dfold, List.foldl_append]
        simpa [Run.empty, this] using hv)
      rw [hc2]
      exact ⟨by omega, trivial⟩
  unfold number
  dsimp only
  rw [hsign, hip', hfr]
  have hne : ((ip.foldl pushC Run.empty).count + fp.length == 0) = false := by
    have h0 : (ip.foldl pushC Run.empty).count = ip.length := by simpa [Run.empty] using hcnt1
    have : ip.length ≠ 0 := by simpa using hip
    rw [h0]
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte, exponent_rest rest hr]
  rw [hiv.1]
  simp


private theorem dfold_zeros (k : Nat) (ds : List Char) : dfold 0 (List.replicate k '0' ++ ds) = dfold 0 ds := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, dfold, List.foldl_cons] at ih ⊢
    simpa [dval] using ih

private theorem decOf_exact (d : Dec) (r : Run) (hr : r.acc = d.m.natAbs) (he : d.e ≤ maxExp + maxSig) :
    decOf (decide (d.m < 0)) r (-(d.e : Int)) = some d := by
  obtain ⟨m, e⟩ := d
  simp only at hr he
  have hm : (if decide (m < 0) = true then -(r.acc : Int) else (r.acc : Int)) = m := by
    rw [hr]
    by_cases h : m < 0
    · simp [h]; omega
    · simp [h]; omega
  unfold decOf
  dsimp only
  rw [hm]
  have h1 : ¬ ((maxExp : Int) < -(e : Int)) := by unfold maxExp; omega
  simp only [h1, ↓reduceIte]
  by_cases h0 : e = 0
  · subst h0; simp
  · have h2 : ¬ (0 ≤ -(e : Int)) := by omega
    have h3 : ¬ (maxExp + maxSig < e) := by omega
    simp only [h2, ↓reduceIte, Int.neg_neg, Int.toNat_natCast, h3]

public theorem number_chars (d : Dec) (rest : List Char) (hm : d.m.natAbs < 10 ^ maxSig)
    (he : d.e ≤ maxExp + maxSig) (hr : ∀ c ∈ rest.head?, c = ' ') :
    number (d.chars ++ rest) = some (d, rest) := by
  have hdig : ∀ c ∈ Nat.toDigits 10 d.m.natAbs, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  let s := List.replicate (d.e + 1 - (Nat.toDigits 10 d.m.natAbs).length) '0' ++ Nat.toDigits 10 d.m.natAbs
  have hsl : d.e + 1 ≤ s.length := by simp [s]; omega
  have hsd : ∀ c ∈ s, c.isDigit = true := by
    intro c hc
    simp only [s, List.mem_append, List.mem_replicate] at hc
    rcases hc with ⟨_, rfl⟩ | hc
    · decide
    · exact hdig c hc
  have hsv : dfold 0 s = d.m.natAbs := by
    simp only [s, dfold_zeros]
    exact LeanTex.Core.PdfRead.Number.digits_value _
  let ip := s.take (s.length - d.e)
  let fp := s.drop (s.length - d.e)
  have hsplit : ip ++ fp = s := List.take_append_drop _ _
  have hfpl : fp.length = d.e := by simp [fp]; omega
  have hip : ip ≠ [] := by
    intro h
    have : ip.length = 0 := by simp [h]
    simp [ip] at this; omega
  have hfe : fp.isEmpty = (d.e == 0) := by
    cases h : d.e with
    | zero => simp [List.isEmpty_iff, ← List.length_eq_zero_iff, hfpl, h]
    | succ k =>
      have : fp.length ≠ 0 := by omega
      simp [← List.length_eq_zero_iff, this]
  have hchars : d.chars = (if decide (d.m < 0) then ['-'] else []) ++ ip ++
      (if fp.isEmpty then [] else '.' :: fp) := by
    rw [hfe]
    simp only [Dec.chars, decide_eq_true_eq]
    rfl
  obtain ⟨r, hracc, hnum⟩ := number_parts (decide (d.m < 0)) ip fp rest hip (by rw [hsplit]; exact hsd) hr
    (by rw [hsplit, hsv]; exact hm)
  rw [hchars, hnum, hfpl]
  rw [decOf_exact d r (by rw [hracc, hsplit, hsv]) he]
  rfl


private theorem cmds_nil (acc : Array Cmd) (cur : Option Char) : cmds acc cur [] = (acc, .done) := by
  rw [cmds]

private theorem cmds_space (acc : Array Cmd) (cur : Option Char) (rest : List Char) :
    cmds acc cur (' ' :: rest) = cmds acc cur rest := by
  rw [cmds.eq_def]; simp [isWsp]

private theorem cmds_close (acc : Array Cmd) (cur : Option Char) (rest : List Char) :
    cmds acc cur ('Z' :: rest) = cmds (acc.push .close) none rest := by
  rw [cmds.eq_def]; simp [isWsp]

private theorem cmds_letter (acc : Array Cmd) (cur : Option Char) (c : Char) (rest : List Char)
    (cmd : Cmd) (r : List Char) (hw : isWsp c = false) (hcomma : c ≠ ',') (ha : c.isAlpha = true)
    (hz : c ≠ 'Z' ∧ c ≠ 'z') (h : operands c rest = some (cmd, r)) :
    cmds acc cur (c :: rest) = cmds (acc.push cmd) (some (repeatOf c)) r := by
  rw [cmds.eq_def]
  simp only [hw, Bool.false_or, ha, ↓reduceIte, beq_iff_eq, hcomma]
  have : (c == 'Z' || c == 'z') = false := by simp [hz.1, hz.2]
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  split
  · next cmd' r' heq => rw [h] at heq; cases heq; rfl
  · next heq => rw [h] at heq; cases heq


/-- A decimal the reader reads back as written. -/
@[expose] public def Dec.ok (d : Dec) : Prop := d.m.natAbs < 10 ^ maxSig ∧ d.e ≤ maxExp + maxSig

private theorem Dec.chars_head (d : Dec) : ∃ c rest, d.chars = c :: rest ∧ (c = '-' ∨ c.isDigit = true) := by
  unfold Dec.chars
  dsimp only
  by_cases h : d.m < 0
  · simp only [h, ↓reduceIte]
    exact ⟨'-', _, rfl, .inl rfl⟩
  · simp only [h, ↓reduceIte, List.nil_append]
    let s := List.replicate (d.e + 1 - (Nat.toDigits 10 d.m.natAbs).length) '0' ++ Nat.toDigits 10 d.m.natAbs
    have hsl : d.e + 1 ≤ s.length := by simp [s]; omega
    have hsd : ∀ c ∈ s, c.isDigit = true := by
      intro c hc
      simp only [s, List.mem_append, List.mem_replicate] at hc
      rcases hc with ⟨_, rfl⟩ | hc
      · decide
      · exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
    have hne : s.take (s.length - d.e) ≠ [] := by
      intro he
      have : (s.take (s.length - d.e)).length = 0 := by simp [he]
      simp at this; omega
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨c, cs ++ (if d.e == 0 then [] else '.' :: s.drop (s.length - d.e)), ?_, .inr ?_⟩
    · show s.take (s.length - d.e) ++ _ = _
      rw [hcs]; rfl
    · exact hsd c (List.mem_of_mem_take (by rw [hcs]; simp))

private theorem skipWs_chars (d : Dec) (rest : List Char) : skipWs (d.chars ++ rest) = d.chars ++ rest := by
  obtain ⟨c, cs, h, hc⟩ := d.chars_head
  rw [h]
  have : isWsp c = false := by
    rcases hc with rfl | hc
    · decide
    · unfold Char.isDigit at hc
      simp at hc
      unfold isWsp
      have h1 : 48 ≤ c.toNat := hc.1
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro heq <;> subst heq <;> simp at h1
  simp [skipWs, skipSep.skipWs, this]

private theorem skipSep_chars (d : Dec) (rest : List Char) : skipSep (d.chars ++ rest) = d.chars ++ rest := by
  obtain ⟨c, cs, h, hc⟩ := d.chars_head
  rw [h]
  have hw : isWsp c = false := by
    have := skipWs_chars d rest
    rw [h] at this
    by_cases hc' : isWsp c = true
    · simp [skipWs, skipSep.skipWs, hc'] at this
      have := congrArg List.length this
      have := skipWs_length_le (cs ++ rest)
      simp at *; omega
    · simpa using hc'
  have hcomma : (c == ',') = false := by
    rcases hc with rfl | hc
    · decide
    · simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; subst e; simp at hc
  simp [skipSep, hw, hcomma]

private theorem numbers_space (n : Nat) (cs : List Char) : numbers (n + 1) (' ' :: cs) = numbers (n + 1) cs := by
  simp [numbers, skipWs, skipSep.skipWs, isWsp]

private theorem skipSep_space (cs : List Char) : skipSep (' ' :: cs) = skipSep cs := by
  simp [skipSep, isWsp]

private theorem skipWs_space (cs : List Char) : skipWs (' ' :: cs) = skipWs cs := by
  simp [skipWs, skipSep.skipWs, isWsp]

/-- The operands a command writes, each after a space. -/
private def ops (ds : List Dec) : List Char := ds.flatMap fun d => ' ' :: d.chars

private theorem numbers_ops : ∀ (ds : List Dec) (tail : List Char), ds ≠ [] → (∀ d ∈ ds, d.ok) →
    (∀ c ∈ tail.head?, c = ' ') → numbers ds.length (ops ds ++ tail) = some (ds, skipSep tail)
  | [], _, h, _, _ => absurd rfl h
  | [d], tail, _, hd, ht => by
    obtain ⟨hm, he⟩ := hd d (by simp)
    simp only [ops, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_singleton,
      List.cons_append]
    rw [numbers_space]
    simp only [numbers, skipWs_chars, number_chars d tail hm he ht, Option.bind_some, Option.map_some]
  | d :: d' :: rest, tail, _, hd, ht => by
    obtain ⟨hm, he⟩ := hd d (by simp)
    have ih := numbers_ops (d' :: rest) tail (by simp) (fun x hx => hd x (by simp_all)) ht
    have hops : ops (d :: d' :: rest) ++ tail = ' ' :: (d.chars ++ (ops (d' :: rest) ++ tail)) := by
      simp [ops]
    have hhead : ∀ c ∈ (ops (d' :: rest) ++ tail).head?, c = ' ' := by simp [ops]
    rw [hops, show (d :: d' :: rest).length = (rest.length + 1) + 1 by simp, numbers_space]
    simp only [numbers, skipWs_chars, number_chars d _ hm he hhead, Option.bind_some]
    have hsk : skipSep (ops (d' :: rest) ++ tail) = d'.chars ++ (ops rest ++ tail) := by
      simp only [ops, List.flatMap_cons, List.cons_append, List.append_assoc]
      rw [skipSep_space, skipSep_chars]
    rw [hsk]
    have : (d' :: rest).length = rest.length + 1 := by simp
    rw [this] at ih
    have hops' : ops (d' :: rest) ++ tail = ' ' :: (d'.chars ++ (ops rest ++ tail)) := by simp [ops]
    rw [hops', numbers_space] at ih
    simp only [numbers] at ih ⊢
    rw [ih]
    rfl


/-- Every decimal a command writes. -/
@[expose] public def Cmd.decs : Cmd → List Dec
  | .move _ x y => [x, y]
  | .line _ x y => [x, y]
  | .horiz _ x => [x]
  | .vert _ y => [y]
  | .cubic _ a b c d e f => [a, b, c, d, e, f]
  | .smooth _ a b x y => [a, b, x, y]
  | .quad _ a b x y => [a, b, x, y]
  | .smoothQuad _ x y => [x, y]
  | .arc _ rx ry rot _ _ x y => [rx, ry, rot, x, y]
  | .close => []

private theorem chars_ops (ds : List Dec) : Cmd.chars.ops ds = ops ds := rfl

private theorem ops2 (ds : List Dec) (tail : List Char) (hd : ∀ d ∈ ds, d.ok) (hne : ds ≠ [])
    (ht : ∀ c ∈ tail.head?, c = ' ') :
    numbers ds.length (ops ds ++ tail) = some (ds, skipSep tail) := numbers_ops ds tail hne hd ht

private theorem flag_chars (b : Bool) (rest : List Char) : flag (flagChar b :: rest) = some (b, rest) := by
  cases b <;> rfl

private theorem skipSep_flag (b : Bool) (rest : List Char) : skipSep (flagChar b :: rest) = flagChar b :: rest := by
  cases b <;> rfl

private theorem arcArgs_chars (rx ry rot x y : Dec) (l sw : Bool) (hd : ∀ d ∈ [rx, ry, rot, x, y], d.ok)
    (tail : List Char) (ht : ∀ c ∈ tail.head?, c = ' ') :
    arcArgs (ops [rx, ry, rot] ++ [' ', flagChar l, ' ', flagChar sw] ++ ops [x, y] ++ tail) =
      some ((rx, ry, rot, l, sw, x, y), tail) := by
  have ok (d : Dec) (h : d ∈ [rx, ry, rot, x, y]) := hd d h
  obtain ⟨m1, e1⟩ := ok rx (by simp)
  obtain ⟨m2, e2⟩ := ok ry (by simp)
  obtain ⟨m3, e3⟩ := ok rot (by simp)
  obtain ⟨m4, e4⟩ := ok x (by simp)
  obtain ⟨m5, e5⟩ := ok y (by simp)
  have sp : ∀ X : List Char, ∀ c ∈ (' ' :: X).head?, c = ' ' := by simp
  simp only [ops, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.append_assoc, List.nil_append, arcArgs]
  rw [skipWs_space, skipWs_chars, number_chars rx _ m1 e1 (sp _)]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_chars, number_chars ry _ m2 e2 (sp _)]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_chars, number_chars rot _ m3 e3 (sp _)]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_flag, flag_chars]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_flag, flag_chars]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_chars, number_chars x _ m4 e4 (sp _)]
  simp only [Option.bind_some]
  rw [skipSep_space, skipSep_chars, number_chars y _ m5 e5 ht]
  rfl

public theorem cmds_cmd (c : Cmd) (hd : ∀ d ∈ c.decs, d.ok) (acc : Array Cmd) (cur : Option Char)
    (tail : List Char) (ht : ∀ x ∈ tail.head?, x = ' ') :
    ∃ cur' r, cmds acc cur (c.chars ++ tail) = cmds (acc.push c) cur' r ∧
      (r = skipSep tail ∨ r = tail) := by
  have n (ds : List Dec) (h : ∀ d ∈ ds, d.ok) (hne : ds ≠ []) := ops2 ds tail h hne ht
  cases c with
  | close => exact ⟨none, tail, cmds_close acc cur tail, .inr rfl⟩
  | move rel x y =>
    have hn : numbers 2 (ops [x, y] ++ tail) = some ([x, y], skipSep tail) :=
      n [x, y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'M' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'm' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | line rel x y =>
    have hn : numbers 2 (ops [x, y] ++ tail) = some ([x, y], skipSep tail) :=
      n [x, y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'L' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'l' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | horiz rel x =>
    have hn : numbers 1 (ops [x] ++ tail) = some ([x], skipSep tail) :=
      n [x] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'H' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'h' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | vert rel y =>
    have hn : numbers 1 (ops [y] ++ tail) = some ([y], skipSep tail) :=
      n [y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'V' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'v' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | cubic rel a b c' d e f =>
    have hn : numbers 6 (ops [a, b, c', d, e, f] ++ tail) = some ([a, b, c', d, e, f], skipSep tail) :=
      n [a, b, c', d, e, f] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'C' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'c' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | smooth rel a b x y =>
    have hn : numbers 4 (ops [a, b, x, y] ++ tail) = some ([a, b, x, y], skipSep tail) :=
      n [a, b, x, y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'S' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 's' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | quad rel a b x y =>
    have hn : numbers 4 (ops [a, b, x, y] ++ tail) = some ([a, b, x, y], skipSep tail) :=
      n [a, b, x, y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'Q' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 'q' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | smoothQuad rel x y =>
    have hn : numbers 2 (ops [x, y] ++ tail) = some ([x, y], skipSep tail) :=
      n [x, y] hd (by simp)
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append]
    cases rel
    · exact ⟨_, _, cmds_letter acc cur 'T' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
    · exact ⟨_, _, cmds_letter acc cur 't' _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by simp [operands, hn]), .inl rfl⟩
  | arc rel rx ry rot l sw x y =>
    have ha := arcArgs_chars rx ry rot x y l sw hd tail ht
    simp only [List.cons_append, List.nil_append, List.append_assoc] at ha
    simp only [Cmd.chars, Cmd.chars.letter, chars_ops, List.cons_append, List.append_assoc,
      List.nil_append]
    cases rel
    · refine ⟨_, _, cmds_letter acc cur 'A' _ _ _ (by decide) (by decide) (by decide) (by decide) ?_,
        .inr rfl⟩
      have hu : 'A'.toUpper = 'A' := by decide
      have hl : 'A'.isLower = false := by decide
      simp only [operands, hu, hl]
      rw [ha]; rfl
    · refine ⟨_, _, cmds_letter acc cur 'a' _ _ _ (by decide) (by decide) (by decide) (by decide) ?_,
        .inr rfl⟩
      have hu : 'a'.toUpper = 'A' := by decide
      have hl : 'a'.isLower = true := by decide
      simp only [operands, hu, hl]
      rw [ha]; rfl


private theorem Cmd.chars_head (c : Cmd) : ∃ L tl, c.chars = L :: tl ∧ isWsp L = false ∧ (L == ',') = false := by
  cases c with
  | close => exact ⟨'Z', [], rfl, by decide, by decide⟩
  | move rel _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | line rel _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | horiz rel _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | vert rel _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | cubic rel _ _ _ _ _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | smooth rel _ _ _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | quad rel _ _ _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | smoothQuad rel _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩
  | arc rel _ _ _ _ _ _ _ => cases rel <;> exact ⟨_, _, rfl, by decide, by decide⟩

private theorem renderChars_skipSep (c : Cmd) (rest : List Cmd) :
    skipSep (renderChars (c :: rest)) = renderChars (c :: rest) := by
  obtain ⟨L, tl, h, hw, hc⟩ := c.chars_head
  cases rest with
  | nil => simp only [renderChars, h]; simp [skipSep, hw, hc]
  | cons c' rest' => simp only [renderChars, h, List.cons_append]; simp [skipSep, hw, hc]

public theorem cmds_render : ∀ (cs : List Cmd) (acc : Array Cmd) (cur : Option Char),
    (∀ c ∈ cs, ∀ d ∈ c.decs, d.ok) → cmds acc cur (renderChars cs) = (acc ++ cs.toArray, .done)
  | [], acc, cur, _ => by simp [renderChars, cmds_nil]
  | [c], acc, cur, hd => by
    obtain ⟨cur', r, h, hr⟩ := cmds_cmd c (hd c (by simp)) acc cur [] (by simp)
    simp only [List.append_nil] at h
    simp only [renderChars, h]
    rcases hr with rfl | rfl <;> simp [skipSep, cmds_nil]
  | c :: c' :: rest, acc, cur, hd => by
    obtain ⟨cur', r, h, hr⟩ := cmds_cmd c (hd c (by simp)) acc cur (' ' :: renderChars (c' :: rest))
      (by simp)
    have ih := cmds_render (c' :: rest) (acc.push c) cur' (fun x hx => hd x (by simp_all))
    have hr' : cmds (acc.push c) cur' r = cmds (acc.push c) cur' (renderChars (c' :: rest)) := by
      rcases hr with rfl | rfl
      · rw [skipSep_space, renderChars_skipSep]
      · rw [cmds_space]
    simp only [renderChars] at h ⊢
    rw [h, hr', ih]
    simp

public theorem parse_render_exact (cs : Array Cmd)
    (hfirst : ∀ c ∈ cs[0]?, ∃ rel x y, c = .move rel x y)
    (hd : ∀ c ∈ cs, ∀ d ∈ c.decs, d.ok) :
    parse (render cs) = (cs, .done) := by
  unfold parse render
  rw [String.toList_ofList, cmds_render cs.toList #[] none (fun c hc => hd c (by simpa using hc))]
  simp only [Array.toArray_toList, Array.empty_append]
  cases h0 : cs[0]? with
  | none => rfl
  | some c =>
    obtain ⟨rel, x, y, rfl⟩ := hfirst c (by simp [h0])
    rfl

end LeanTex.Core.PathData
