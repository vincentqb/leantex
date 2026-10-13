module

/-!
# SVG path data

The `d` attribute's grammar (SVG 2 §9.3.9): commands `M L H V C S Q T A Z`
in both cases, numbers in the compact syntax exporters write — `1.5.5` is
two numbers, `1-2` is two, an arc's flags need no separator — and implicit
repetition (after `M` further pairs are line segments). A number is kept
as the decimal it spells (`Dec`) to `maxSig` significant digits, past which
a digit only moves the point: far finer than any coordinate needs (a
double holds 17), and what keeps the reader linear in the digits a number
spells. What is rounded further, and where, is the importer's decision.

The reader follows SVG 2 §9.5.4's error rule: it reads the path up to the
last command that parsed whole, and says where and why it stopped — at a
spelling no reader accepts, or at a number past the reader's range, where a
browser's double would still have read on (`Stop`). Every step consumes
input (`number_lt`, `operands_lt`), which is the walk's termination measure,
so the reader is linear in the path. `render` writes commands back, and the
reader reads every rendered spelling back as it stands
(`PathDataContract`'s `parse_render_exact`).
-/

namespace LeanTex.Core.PathData

/-- A decimal as spelled: `m · 10^(-e)`. -/
public structure Dec where
  m : Int
  e : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Its value. -/
@[expose] public def Dec.toRat (d : Dec) : Rat := (d.m : Rat) / ((10 ^ d.e : Nat) : Rat)

@[expose] public def Dec.zero : Dec := ⟨0, 0⟩

/-- One path command, absolute or relative (`rel`), its operands as spelled. -/
public inductive Cmd where
  | move (rel : Bool) (x y : Dec)
  | line (rel : Bool) (x y : Dec)
  | horiz (rel : Bool) (x : Dec)
  | vert (rel : Bool) (y : Dec)
  | cubic (rel : Bool) (x1 y1 x2 y2 x y : Dec)
  | smooth (rel : Bool) (x2 y2 x y : Dec)
  | quad (rel : Bool) (x1 y1 x y : Dec)
  | smoothQuad (rel : Bool) (x y : Dec)
  | arc (rel : Bool) (rx ry rot : Dec) (large sweep : Bool) (x y : Dec)
  | close
  deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Numbers -/

@[expose] public def isWsp (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- White space and at most one comma. -/
@[expose] public def skipSep : List Char → List Char
  | c :: rest => if isWsp c then skipSep rest else if c == ',' then skipWs rest else c :: rest
  | [] => []
where
  skipWs : List Char → List Char
    | c :: rest => if isWsp c then skipWs rest else c :: rest
    | [] => []

@[expose] public def skipWs : List Char → List Char := skipSep.skipWs

public theorem skipWs_length_le : ∀ l : List Char, (skipSep.skipWs l).length ≤ l.length
  | [] => by simp [skipSep.skipWs]
  | c :: rest => by
    simp only [skipSep.skipWs]
    split
    · have := skipWs_length_le rest
      simp only [List.length_cons]; omega
    · simp

/-- Skipping a separator never lengthens the text. -/
public theorem skipSep_length_le : ∀ l : List Char, (skipSep l).length ≤ l.length
  | [] => by simp [skipSep]
  | c :: rest => by
    simp only [skipSep]
    split
    · have := skipSep_length_le rest
      simp only [List.length_cons]; omega
    · split
      · have := skipWs_length_le rest
        simp only [List.length_cons]; omega
      · simp

/-- The significant digits a number keeps. -/
@[expose] public def maxSig : Nat := 40

/-- The decimal exponent past which a number is no coordinate any figure
means: larger is out of the reader's range, smaller than `-(maxExp + maxSig)`
reads as zero. -/
@[expose] public def maxExp : Nat := 40

/-- An exponent's value saturates here: past any digit count a file can
hold, so saturation never changes which side of the range a number falls. -/
@[expose] public def expCap : Nat := 1000000000000000000

/-- A run of mantissa digits read so far: the significant digits kept, as a
natural — leading zeros skipped, at most `maxSig` of them — how many digits
were dropped past those, and how many digits the run held in all. -/
public structure Run where
  acc : Nat
  kept : Nat
  dropped : Nat
  count : Nat
  deriving Repr, Inhabited

@[expose] public def Run.empty : Run := ⟨0, 0, 0, 0⟩

/-- One mantissa digit onto a run: a leading zero only counts, a digit
past `maxSig` only counts as dropped. -/
@[expose] public def Run.push (r : Run) (d : Nat) : Run :=
  if r.acc == 0 && d == 0 then { r with count := r.count + 1 }
  else if r.kept < maxSig then
    { acc := r.acc * 10 + d, kept := r.kept + 1, dropped := r.dropped, count := r.count + 1 }
  else { r with dropped := r.dropped + 1, count := r.count + 1 }

/-- The digits at the front of a list onto a run. -/
@[expose] public def digitRun (r : Run) : List Char → Run × List Char
  | c :: rest => if c.isDigit then digitRun (r.push (c.toNat - 48)) rest else (r, c :: rest)
  | [] => (r, [])

/-- An exponent's digits: their value, saturating at `expCap`, and how many
there were. -/
@[expose] public def expDigits (v n : Nat) : List Char → Nat × Nat × List Char
  | c :: rest =>
    if c.isDigit then expDigits (min (v * 10 + (c.toNat - 48)) expCap) (n + 1) rest
    else (v, n, c :: rest)
  | [] => (v, n, [])

/-- An optional sign. -/
@[expose] public def sign : List Char → Bool × List Char
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | cs => (false, cs)

/-- A fraction after the integer digits: the run continued over the digits
after a point, and how many those were. -/
@[expose] public def fraction (r : Run) : List Char → Run × Nat × List Char
  | '.' :: rest =>
    let f := digitRun r rest
    (f.1, f.1.count - r.count, f.2)
  | cs => (r, 0, cs)

/-- An optional exponent: its signed value and the text after it; an `e`
with no digit after it is no exponent. -/
@[expose] public def exponent : List Char → Int × List Char
  | e :: rest =>
    if e == 'e' || e == 'E' then
      let s := sign rest
      let d := expDigits 0 0 s.2
      if d.2.1 == 0 then (0, e :: rest) else (if s.1 then -(d.1 : Int) else d.1, d.2.2)
    else (0, e :: rest)
  | [] => (0, [])

/-- The decimal a sign, a run and its point's exponent spell: `none` past
`maxExp`, zero below `-(maxExp + maxSig)`. -/
@[expose] public def decOf (neg : Bool) (r : Run) (E : Int) : Option Dec :=
  let m : Int := if neg then -(r.acc : Int) else r.acc
  if (maxExp : Int) < E then none
  else if 0 ≤ E then some ⟨m * (10 ^ E.toNat : Nat), 0⟩
  else if maxExp + maxSig < (-E).toNat then some ⟨0, 0⟩
  else some ⟨m, (-E).toNat⟩

/-- A number at the front: an optional sign, digits with an optional
fraction (one side may be empty, not both), an optional exponent. -/
@[expose] public def number (cs : List Char) : Option (Dec × List Char) :=
  let s := sign cs
  let ip := digitRun Run.empty s.2
  let fr := fraction ip.1 ip.2
  if ip.1.count + fr.2.1 == 0 then none else
  let ex := exponent fr.2.2
  (decOf s.1 fr.1 ((fr.1.dropped : Int) + ex.1 - fr.2.1)).map (·, ex.2)

/-- Why a number is none: its spelling, or its range. -/
@[expose] public def outOfRange (cs : List Char) : Bool :=
  let s := sign cs
  let ip := digitRun Run.empty s.2
  let fr := fraction ip.1 ip.2
  ip.1.count + fr.2.1 != 0 && (number cs).isNone

/-! ### Every number consumes what it reads -/

public theorem Run.push_count (r : Run) (d : Nat) : (r.push d).count = r.count + 1 := by
  unfold Run.push
  split
  · rfl
  · split <;> rfl

public theorem digitRun_length : ∀ (r : Run) (cs : List Char),
    (digitRun r cs).2.length + ((digitRun r cs).1.count - r.count) = cs.length ∧
      r.count ≤ (digitRun r cs).1.count
  | r, [] => by simp [digitRun]
  | r, c :: rest => by
    simp only [digitRun]
    split
    · obtain ⟨h1, h2⟩ := digitRun_length (r.push (c.toNat - 48)) rest
      rw [Run.push_count] at h1 h2
      simp only [List.length_cons]
      omega
    · simp

public theorem expDigits_length_le : ∀ (v n : Nat) (cs : List Char),
    (expDigits v n cs).2.2.length ≤ cs.length
  | v, n, [] => by simp [expDigits]
  | v, n, c :: rest => by
    simp only [expDigits]
    split
    · have := expDigits_length_le (min (v * 10 + (c.toNat - 48)) expCap) (n + 1) rest
      simp only [List.length_cons]; omega
    · simp

public theorem sign_length_le (cs : List Char) : (sign cs).2.length ≤ cs.length := by
  unfold sign
  split <;> simp

public theorem fraction_length (r : Run) (cs : List Char) :
    (fraction r cs).2.2.length + (fraction r cs).2.1 ≤ cs.length := by
  unfold fraction
  split
  · next rest =>
    obtain ⟨h1, _⟩ := digitRun_length r rest
    simp only [List.length_cons]
    omega
  · simp

public theorem exponent_length_le (cs : List Char) : (exponent cs).2.length ≤ cs.length := by
  unfold exponent
  split
  · next e rest =>
    dsimp only
    split
    · split
      · simp
      · have h1 := expDigits_length_le 0 0 (sign rest).2
        have h2 := sign_length_le rest
        simp only [List.length_cons]; omega
    · simp
  · simp

/-- **A number consumes what it reads** (`_lt`): whatever follows it is
shorter than what it was read from. -/
public theorem number_lt {cs : List Char} {d : Dec} {r : List Char} (h : number cs = some (d, r)) :
    r.length < cs.length := by
  unfold number at h
  dsimp only at h
  split at h
  · cases h
  · next hz =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    have h1 := exponent_length_le (fraction (digitRun Run.empty (sign cs).2).1
      (digitRun Run.empty (sign cs).2).2).2.2
    have h2 := fraction_length (digitRun Run.empty (sign cs).2).1 (digitRun Run.empty (sign cs).2).2
    obtain ⟨h3, _⟩ := digitRun_length Run.empty (sign cs).2
    have h4 := sign_length_le cs
    simp only [beq_iff_eq] at hz
    simp only [Run.empty] at *
    omega

/-- An arc flag: one `0` or `1`, no separator needed after it. -/
@[expose] public def flag : List Char → Option (Bool × List Char)
  | '0' :: rest => some (false, rest)
  | '1' :: rest => some (true, rest)
  | _ => none

public theorem flag_lt {cs : List Char} {b : Bool} {r : List Char} (h : flag cs = some (b, r)) :
    r.length < cs.length := by
  unfold flag at h
  split at h <;> simp_all

/-! ## Commands -/

/-- `n` numbers, separated, from the front. -/
@[expose] public def numbers : Nat → List Char → Option (List Dec × List Char)
  | 0, cs => some ([], cs)
  | n + 1, cs =>
    (number (skipWs cs)).bind fun p =>
      (numbers n (skipSep p.2)).map fun q => (p.1 :: q.1, q.2)

public theorem numbers_le : ∀ (n : Nat) {cs : List Char} {ds : List Dec} {r : List Char},
    numbers n cs = some (ds, r) → r.length ≤ cs.length
  | 0, cs, ds, r, h => by simp only [numbers, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; omega
  | n + 1, cs, ds, r, h => by
    simp only [numbers, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨d, rest⟩, hn, ⟨ds', rest'⟩, hm, _, rfl⟩ := h
    dsimp only at hm hn ⊢
    have := numbers_le n hm
    have := skipSep_length_le rest
    have := number_lt hn
    have := skipWs_length_le cs
    unfold skipWs at *
    omega

public theorem numbers_lt (n : Nat) {cs : List Char} {ds : List Dec} {r : List Char}
    (h : numbers (n + 1) cs = some (ds, r)) : r.length < cs.length := by
  simp only [numbers, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨d, rest⟩, hn, ⟨ds', rest'⟩, hm, _, rfl⟩ := h
  dsimp only at hm hn ⊢
  have := numbers_le n hm
  have := skipSep_length_le rest
  have := number_lt hn
  have := skipWs_length_le cs
  unfold skipWs at *
  omega

/-- An arc's seven operands. -/
@[expose] public def arcArgs (cs : List Char) :
    Option ((Dec × Dec × Dec × Bool × Bool × Dec × Dec) × List Char) :=
  (number (skipWs cs)).bind fun (rx, c1) =>
  (number (skipSep c1)).bind fun (ry, c2) =>
  (number (skipSep c2)).bind fun (rot, c3) =>
  (flag (skipSep c3)).bind fun (large, c4) =>
  (flag (skipSep c4)).bind fun (sweep, c5) =>
  (number (skipSep c5)).bind fun (x, c6) =>
  (number (skipSep c6)).map fun (y, c7) => ((rx, ry, rot, large, sweep, x, y), c7)

public theorem arcArgs_lt {cs : List Char} {a : Dec × Dec × Dec × Bool × Bool × Dec × Dec}
    {r : List Char} (h : arcArgs cs = some (a, r)) : r.length < cs.length := by
  simp only [arcArgs, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨rx, c1⟩, h1, ⟨ry, c2⟩, h2, ⟨rot, c3⟩, h3, ⟨lg, c4⟩, h4, ⟨sw, c5⟩, h5, ⟨x, c6⟩, h6,
    ⟨y, c7⟩, h7, _, rfl⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7 ⊢
  have := number_lt h1; have := number_lt h2; have := number_lt h3
  have := flag_lt h4; have := flag_lt h5; have := number_lt h6; have := number_lt h7
  have := skipWs_length_le cs
  have := skipSep_length_le c1; have := skipSep_length_le c2; have := skipSep_length_le c3
  have := skipSep_length_le c4; have := skipSep_length_le c5; have := skipSep_length_le c6
  unfold skipWs at *
  omega

/-- One command's operands for command letter `c`. -/
@[expose] public def operands (c : Char) (cs : List Char) : Option (Cmd × List Char) :=
  let rel := c.isLower
  match c.toUpper with
  | 'M' => (numbers 2 cs).bind fun (ds, r) => match ds with
    | [x, y] => some (.move rel x y, r) | _ => none
  | 'L' => (numbers 2 cs).bind fun (ds, r) => match ds with
    | [x, y] => some (.line rel x y, r) | _ => none
  | 'H' => (numbers 1 cs).bind fun (ds, r) => match ds with
    | [x] => some (.horiz rel x, r) | _ => none
  | 'V' => (numbers 1 cs).bind fun (ds, r) => match ds with
    | [y] => some (.vert rel y, r) | _ => none
  | 'C' => (numbers 6 cs).bind fun (ds, r) => match ds with
    | [a, b, c', d, e, f] => some (.cubic rel a b c' d e f, r) | _ => none
  | 'S' => (numbers 4 cs).bind fun (ds, r) => match ds with
    | [a, b, x, y] => some (.smooth rel a b x y, r) | _ => none
  | 'Q' => (numbers 4 cs).bind fun (ds, r) => match ds with
    | [a, b, x, y] => some (.quad rel a b x y, r) | _ => none
  | 'T' => (numbers 2 cs).bind fun (ds, r) => match ds with
    | [x, y] => some (.smoothQuad rel x y, r) | _ => none
  | 'A' => (arcArgs cs).map fun ((rx, ry, rot, l, s, x, y), r) => (.arc rel rx ry rot l s x y, r)
  | 'Z' => some (.close, cs)
  | _ => none

private theorem bindList_lt {k : Nat} {cs : List Char} {cmd : Cmd} {r : List Char}
    {g : List Dec × List Char → Option (Cmd × List Char)}
    (hg : ∀ x cmd r, g x = some (cmd, r) → r = x.2)
    (h : (numbers (k + 1) cs).bind g = some (cmd, r)) : r.length < cs.length := by
  cases hn : numbers (k + 1) cs with
  | none => simp [hn] at h
  | some p =>
    simp only [hn, Option.bind_some] at h
    rw [hg _ _ _ h]
    exact numbers_lt k hn

/-- **A command with operands consumes what it reads** (`_lt`): every
command letter but `Z` reads at least one number. -/
public theorem operands_lt {c : Char} {cs : List Char} {cmd : Cmd} {r : List Char}
    (h : operands c cs = some (cmd, r)) (hz : c.toUpper ≠ 'Z') : r.length < cs.length := by
  unfold operands at h
  dsimp only at h
  split at h
  · refine bindList_lt (k := 1) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 1) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 0) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 0) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 5) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 3) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 3) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · refine bindList_lt (k := 1) (fun ⟨ds, r'⟩ cmd r hf => ?_) h
    simp only at hf; split at hf <;> simp_all
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r'⟩, ha, he⟩ := h
    simp only [Prod.mk.injEq] at he
    rw [← he.2]
    exact arcArgs_lt ha
  · next hc => exact absurd hc hz
  · cases h

/-- A command letter's operands never lengthen the text. -/
public theorem operands_le {c : Char} {cs : List Char} {cmd : Cmd} {r : List Char}
    (h : operands c cs = some (cmd, r)) : r.length ≤ cs.length := by
  by_cases hz : c.toUpper = 'Z'
  · unfold operands at h
    dsimp only at h
    rw [hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; omega
  · exact Nat.le_of_lt (operands_lt h hz)

/-- After a command, the letter an implicit repetition repeats: a moveto
repeats as a lineto (§9.3.3). -/
@[expose] public def repeatOf (c : Char) : Char :=
  if c == 'M' then 'L' else if c == 'm' then 'l' else c

/-- Where the reader stopped: at the end, at a spelling no reader accepts,
or at a number past the reader's range (`maxExp`), which a browser's
double would still have read. -/
public inductive Stop where
  | done
  | syntax
  | range
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The path's commands onto `acc`, from the front of `cs` under the
command letter in force; stops at the first command that does not parse,
returning what parsed and where it stopped. Each step consumes at least
one character (`operands_lt`), the walk's measure. -/
@[expose] public def cmds (acc : Array Cmd) (cur : Option Char) (cs : List Char) : Array Cmd × Stop :=
  match cs with
  | [] => (acc, .done)
  | c :: rest =>
    if isWsp c || c == ',' then cmds acc cur rest
    else if c.isAlpha then
      if c == 'Z' || c == 'z' then cmds (acc.push .close) none rest
      else match _h : operands c rest with
        | some (cmd, r) => cmds (acc.push cmd) (some (repeatOf c)) r
        | none => (acc, if outOfRange (skipWs rest) then .range else .syntax)
    else
      match cur with
      | some l =>
        if _hz : l.toUpper = 'Z' then (acc, .syntax) else
        match _h : operands l (c :: rest) with
        | some (cmd, r) => cmds (acc.push cmd) (some (repeatOf l)) r
        | none => (acc, if outOfRange (c :: rest) then .range else .syntax)
      | none => (acc, .syntax)
termination_by cs.length
decreasing_by
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · have := operands_le _h
    simp only [List.length_cons]; omega
  · exact operands_lt _h _hz

/-- **A path's `d` as commands**, up to the first that does not parse, and
where the reader stopped. A path must start with a moveto (§9.5.4); one
that does not draws nothing. -/
@[expose] public def parse (s : String) : Array Cmd × Stop :=
  let (out, stop) := cmds #[] none s.toList
  match out[0]? with
  | some (Cmd.move _ _ _) => (out, stop)
  | none => (out, stop)
  | some _ => (#[], .syntax)

/-! ## Writing -/

/-- A decimal's digits, `e` of them after the point. -/
@[expose] public def Dec.chars (d : Dec) : List Char :=
  let s := (Nat.toDigits 10 d.m.natAbs)
  let s := List.replicate (d.e + 1 - s.length) '0' ++ s
  let ip := s.take (s.length - d.e)
  let fp := s.drop (s.length - d.e)
  (if d.m < 0 then ['-'] else []) ++ ip ++ (if d.e == 0 then [] else '.' :: fp)

@[expose] public def flagChar (b : Bool) : Char := if b then '1' else '0'

/-- One command as it is written: its letter, then each operand after a
space. -/
@[expose] public def Cmd.chars : Cmd → List Char
  | .move rel x y => letter 'M' rel ++ ops [x, y]
  | .line rel x y => letter 'L' rel ++ ops [x, y]
  | .horiz rel x => letter 'H' rel ++ ops [x]
  | .vert rel y => letter 'V' rel ++ ops [y]
  | .cubic rel a b c d e f => letter 'C' rel ++ ops [a, b, c, d, e, f]
  | .smooth rel a b x y => letter 'S' rel ++ ops [a, b, x, y]
  | .quad rel a b x y => letter 'Q' rel ++ ops [a, b, x, y]
  | .smoothQuad rel x y => letter 'T' rel ++ ops [x, y]
  | .arc rel rx ry rot l s x y =>
    letter 'A' rel ++ ops [rx, ry, rot] ++ [' ', flagChar l, ' ', flagChar s] ++ ops [x, y]
  | .close => ['Z']
where
  letter (c : Char) (rel : Bool) : List Char := [if rel then c.toLower else c]
  ops (ds : List Dec) : List Char := ds.flatMap fun d => ' ' :: d.chars

/-- Commands as a `d` attribute's characters, one space between commands. -/
@[expose] public def renderChars : List Cmd → List Char
  | [] => []
  | [c] => c.chars
  | c :: rest => c.chars ++ ' ' :: renderChars rest

/-- **Commands as a `d` attribute**: each command and its operands, one
space between commands. -/
@[expose] public def render (cs : Array Cmd) : String := String.ofList (renderChars cs.toList)

end LeanTex.Core.PathData
