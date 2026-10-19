module

import LeanTex.Core.PygmentsLexData
import LeanTex.Core.Hex

/-! What the native lexers share: the text, the Unicode classes their patterns name, word lists
and the raw token stream. Each lexer mirrors one Pygments `RegexLexer` (pygments/lexer.py,
BSD-licensed: testdata/highlight/LICENSE-Pygments). -/
namespace LeanTex.Core.Highlight

/-- A token of a raw stream: the scalars `[start, stop)` of the lexed text
and their Pygments token type, as its dotted path below `Token`. -/
public structure Raw where
  start : Nat
  stop : Nat
  kind : String
  deriving Repr, BEq, Inhabited

-- The Pygments token types the lexers write (pygments/token.py).
namespace Ty
public def text : String := "Text"
public def whitespace : String := "Text.Whitespace"
public def error : String := "Error"
public def keyword : String := "Keyword"
public def keywordConstant : String := "Keyword.Constant"
public def keywordDeclaration : String := "Keyword.Declaration"
public def keywordNamespace : String := "Keyword.Namespace"
public def keywordType : String := "Keyword.Type"
public def name : String := "Name"
public def nameBuiltin : String := "Name.Builtin"
public def nameBuiltinPseudo : String := "Name.Builtin.Pseudo"
public def nameClass : String := "Name.Class"
public def nameDecorator : String := "Name.Decorator"
public def nameException : String := "Name.Exception"
public def nameFunction : String := "Name.Function"
public def nameFunctionMagic : String := "Name.Function.Magic"
public def nameNamespace : String := "Name.Namespace"
public def nameVariable : String := "Name.Variable"
public def nameVariableMagic : String := "Name.Variable.Magic"
public def string : String := "Literal.String"
public def stringAffix : String := "Literal.String.Affix"
public def stringBacktick : String := "Literal.String.Backtick"
public def stringDoc : String := "Literal.String.Doc"
public def stringDouble : String := "Literal.String.Double"
public def stringEscape : String := "Literal.String.Escape"
public def stringInterpol : String := "Literal.String.Interpol"
public def stringSingle : String := "Literal.String.Single"
public def stringSymbol : String := "Literal.String.Symbol"
public def number : String := "Literal.Number"
public def numberBin : String := "Literal.Number.Bin"
public def numberFloat : String := "Literal.Number.Float"
public def numberHex : String := "Literal.Number.Hex"
public def numberInteger : String := "Literal.Number.Integer"
public def numberOct : String := "Literal.Number.Oct"
public def operator : String := "Operator"
public def operatorWord : String := "Operator.Word"
public def punctuation : String := "Punctuation"
public def comment : String := "Comment"
public def commentHashbang : String := "Comment.Hashbang"
public def commentMultiline : String := "Comment.Multiline"
public def commentSingle : String := "Comment.Single"
public def genericError : String := "Generic.Error"
public def genericOutput : String := "Generic.Output"
public def genericPrompt : String := "Generic.Prompt"
public def genericPromptVirtualEnv : String := "Generic.Prompt.VirtualEnv"
end Ty

/-- Classes as sorted inclusive ranges, two entries per range. -/
private structure Classes where
  word : Array UInt32
  space : Array UInt32
  digit : Array UInt32
  leanStart : Array UInt32
  leanRest : Array UInt32
  pyStart : Array UInt32
  pyRest : Array UInt32

private def hexRanges (s : String) : Array UInt32 := Id.run do
  let bs := s.toUTF8
  let mut out : Array UInt32 := Array.mkEmpty (bs.size / 6)
  for i in [0:bs.size / 6] do
    let mut v : UInt32 := 0
    for k in [0:6] do
      v := v * 16 + ((Hex.val? (bs[i * 6 + k]?.getD 0x30).toNat).getD 0).toUInt32
    out := out.push v
  return out

private def loadClasses (_ : Unit) : Classes :=
  { word := hexRanges PygmentsLexData.word
    space := hexRanges PygmentsLexData.space
    digit := hexRanges PygmentsLexData.digit
    leanStart := hexRanges PygmentsLexData.leanNameStart
    leanRest := hexRanges PygmentsLexData.leanNameRest
    pyStart := hexRanges PygmentsLexData.pyNameStart
    pyRest := hexRanges PygmentsLexData.pyNameRest }

/-- Built once per process, on first use. -/
private def classes : Thunk Classes := Thunk.mk loadClasses

/-- Membership in sorted inclusive ranges, by binary search. -/
private def inRanges (rs : Array UInt32) (v : UInt32) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size / 2
  for _ in [0:rs.size + 1] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if v < rs.getD (2 * mid) 0 then hi := mid
      else if rs.getD (2 * mid + 1) 0 < v then lo := mid + 1
      else return true
    else break
  return false

/-- `\w`. -/
public def wordChar (c : Char) : Bool :=
  if c.val < 0x80 then c.isAlphanum || c == '_' else inRanges classes.get.word c.val

/-- `\s`: ASCII `[\t\n\v\f\r\x1c-\x1f ]`, then the table. -/
public def spaceChar (c : Char) : Bool :=
  if c.val < 0x80 then (9 ≤ c.val && c.val ≤ 13) || (28 ≤ c.val && c.val ≤ 32)
  else inRanges classes.get.space c.val

/-- `\d`. -/
public def digitChar (c : Char) : Bool :=
  if c.val < 0x80 then c.isDigit else inRanges classes.get.digit c.val

/-- The first scalar of a Lean 4 name segment. -/
public def leanNameStart (c : Char) : Bool :=
  if c.val < 0x80 then c.isAlpha || c == '_' else inRanges classes.get.leanStart c.val

/-- A later scalar of a Lean 4 name segment. -/
public def leanNameRest (c : Char) : Bool :=
  if c.val < 0x80 then c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  else inRanges classes.get.leanRest c.val

/-- The first scalar of a Python name. -/
public def pyNameStart (c : Char) : Bool :=
  if c.val < 0x80 then c.isAlpha || c == '_' else inRanges classes.get.pyStart c.val

/-- A later scalar of a Python name. -/
public def pyNameRest (c : Char) : Bool :=
  if c.val < 0x80 then c.isAlphanum || c == '_' else inRanges classes.get.pyRest c.val

/-- What the ASCII fast paths and the tables answer for one scalar, side by side. -/
public def asciiAgrees (c : Char) : Bool :=
  let t := classes.get
  wordChar c == inRanges t.word c.val && spaceChar c == inRanges t.space c.val &&
    digitChar c == inRanges t.digit c.val && leanNameStart c == inRanges t.leanStart c.val &&
    leanNameRest c == inRanges t.leanRest c.val && pyNameStart c == inRanges t.pyStart c.val &&
    pyNameRest c == inRanges t.pyRest c.val

/-- The text a lexer reads, its positions counting scalars as Pygments' offsets do. -/
public structure Src where
  chars : Array Char
  deriving Inhabited

namespace Src

public def ofString (s : String) : Src :=
  ⟨s.foldl (fun a c => a.push c) (Array.mkEmpty s.utf8ByteSize)⟩

@[inline] public def size (s : Src) : Nat := s.chars.size

@[inline] public def is (s : Src) (i : Nat) (c : Char) : Bool :=
  if h : i < s.chars.size then s.chars[i] == c else false

/-- The scalar at `i` satisfies `p`; nothing past the end does. -/
@[inline] public def sat (s : Src) (i : Nat) (p : Char → Bool) : Bool :=
  if h : i < s.chars.size then p s.chars[i] else false

@[inline] public def word (s : Src) (i : Nat) : Bool := s.sat i wordChar
@[inline] public def space (s : Src) (i : Nat) : Bool := s.sat i spaceChar
@[inline] public def digit (s : Src) (i : Nat) : Bool := s.sat i digitChar

/-- `\b` at `i`: a word scalar on exactly one side. -/
public def boundary (s : Src) (i : Nat) : Bool :=
  (i > 0 && s.word (i - 1)) != s.word i

/-- `\b` as a pattern's continuation: `i` where it holds. -/
public def boundaryAt (s : Src) (i : Nat) : Option Nat := if s.boundary i then some i else none

/-- `^` under `re.MULTILINE`. -/
@[inline] public def lineStart (s : Src) (i : Nat) : Bool := i == 0 || s.is (i - 1) '\n'

/-- The end of the longest run of scalars from `i` satisfying `p`. -/
public def run (s : Src) (i : Nat) (p : Char → Bool) : Nat :=
  if h : i < s.chars.size then (if p s.chars[i] then s.run (i + 1) p else i) else i
termination_by s.chars.size - i

/-- The end of the longest run of scalars in `[i, lim)` satisfying `p`. -/
public def runTo (s : Src) (i lim : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut stop := i
  for h : j in [i:min lim s.chars.size] do
    have : j < s.chars.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_right _ _)
    if !p s.chars[j] then break
    stop := j + 1
  return stop

/-- The literal scalars `w` stand at `i`. -/
public def lit (s : Src) (i : Nat) (w : Array Char) : Bool := Id.run do
  if i + w.size > s.chars.size then return false
  for h : k in [0:w.size] do
    if s.chars.getD (i + k) w[k] != w[k] then return false
  return true

end Src

/-- What a scan does at a position: stop with its answer, or go on from a
later one. -/
public inductive Step (α : Type) where
  | stop (a : α)
  | next (j : Nat)

namespace Step

variable {α : Type}

/-- The answer a scan from `i` reaches in a text of `n` scalars; a move not forward or out of the
text stops with `dflt`. -/
public def follow (f : Nat → Step α) (dflt : α) (n i : Nat) : α :=
  match f i with
  | .stop a => a
  | .next j => if _h : i < j ∧ j ≤ n then follow f dflt n j else dflt
termination_by n + 1 - i

private theorem follow_eq (f : Nat → Step α) (dflt : α) (n i : Nat) :
    follow f dflt n i = match f i with
      | .stop a => a
      | .next j => if i < j ∧ j ≤ n then follow f dflt n j else dflt := by
  rw [follow]
  cases f i with
  | stop a => rfl
  | next j => by_cases h : i < j ∧ j ≤ n <;> simp [h]

/-- The answer at `k`, the answers past it read from `t`. -/
@[inline] private def answer (f : Nat → Step α) (dflt : α) (n : Nat) (t : Array α) (k : Nat) : α :=
  match f k with
  | .stop a => a
  | .next j => if k < j ∧ j ≤ n then t.getD j dflt else dflt

/-- Positions `k - 1` down to `0` answered, each from the answers past it. -/
private def fill (f : Nat → Step α) (dflt : α) (n : Nat) : Nat → Array α → Array α
  | 0, t => t
  | k + 1, t => fill f dflt n k (t.set! k (answer f dflt n t k))

private theorem fill_follow (f : Nat → Step α) (dflt : α) (n : Nat) :
    ∀ k (t : Array α), k ≤ n + 1 → t.size = n + 1 →
      (∀ i, k ≤ i → i ≤ n → t.getD i dflt = follow f dflt n i) →
      ∀ i, i ≤ n → (fill f dflt n k t).getD i dflt = follow f dflt n i := by
  intro k
  induction k with
  | zero => intro t _ _ h i hi; exact h i (Nat.zero_le _) hi
  | succ k ih =>
    intro t hk hsize h i hi
    simp only [fill]
    apply ih
    · omega
    · simp [hsize]
    · intro i' hki' hi'
      have hk' : k < t.size := by omega
      by_cases hik : i' = k
      · subst hik
        simp only [Array.set!, Array.getD_eq_getD_getElem?,
          Array.getElem?_setIfInBounds_self_of_lt hk', Option.getD_some]
        rw [follow_eq]
        unfold answer
        cases f i' with
        | stop a => rfl
        | next j =>
          by_cases hj : i' < j ∧ j ≤ n
          · simp only [hj, and_self, ite_true]
            exact h j (by omega) hj.2
          · simp [hj]
      · simp only [Array.set!, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_setIfInBounds_ne (Ne.symm hik), ← Array.getD_eq_getD_getElem?]
        exact h i' (by omega) hi'
    · exact hi

end Step

/-- A scan answered at every position of a text of `n` scalars, filled from the end. -/
public structure Memo (α : Type) where
  step : Nat → Step α
  dflt : α
  n : Nat
  answers : Array α

namespace Memo

variable {α : Type}

public def of (f : Nat → Step α) (dflt : α) (n : Nat) : Memo α :=
  ⟨f, dflt, n, Step.fill f dflt n (n + 1) (Array.replicate (n + 1) dflt)⟩

/-- The scan's answer from `i`: the table's within the text, one move past it. -/
@[inline] public def read (m : Memo α) (i : Nat) : α :=
  if i ≤ m.n then m.answers.getD i m.dflt
  else match m.step i with
    | .stop a => a
    | .next _ => m.dflt

public theorem read_exact (f : Nat → Step α) (dflt : α) (n i : Nat) :
    (Memo.of f dflt n).read i = Step.follow f dflt n i := by
  unfold read of
  simp only
  split
  · exact Step.fill_follow f dflt n (n + 1) _ (Nat.le_refl _) (by simp)
      (fun _ _ _ => by omega) i (by assumption)
  · rw [Step.follow_eq]
    cases f i with
    | stop a => rfl
    | next j => simp; omega

end Memo

/-- A scan's table, built the first time a rule asks it anything. -/
public structure Table (α : Type) where
  memo : Thunk (Memo α)

namespace Table

variable {α : Type}

public def of (f : Nat → Step α) (dflt : α) (n : Nat) : Table α :=
  ⟨Thunk.mk fun _ => Memo.of f dflt n⟩

@[inline] public def read (t : Table α) (i : Nat) : α := t.memo.get.read i

public theorem read_exact (f : Nat → Step α) (dflt : α) (n i : Nat) :
    (Table.of f dflt n).read i = Step.follow f dflt n i :=
  Memo.read_exact f dflt n i

end Table

namespace Src

/-- `run`'s move: on through a scalar of the class, else stop. -/
@[inline] public def runStep (s : Src) (p : Char → Bool) (i : Nat) : Step Nat :=
  if s.sat i p then .next (i + 1) else .stop i

private theorem runStep_follow (s : Src) (p : Char → Bool) (d : Nat) :
    ∀ i, Step.follow (s.runStep p) d s.size i = s.run i p := by
  intro i
  induction i using Src.run.induct s p with
  | case1 i h hp ih =>
    rw [Step.follow_eq, run]
    have : i < i + 1 ∧ i + 1 ≤ s.chars.size := ⟨Nat.lt_succ_self _, h⟩
    simp only [runStep, sat, h, dite_true, hp, ite_true, size, this, and_self]
    exact ih
  | case2 i h hp =>
    rw [Step.follow_eq, run]
    simp [runStep, sat, h, hp]
  | case3 i h =>
    rw [Step.follow_eq, run]
    simp [runStep, sat, h]

/-- Every position's run of `p`: what `run` answers, in constant time. -/
public def runs (s : Src) (p : Char → Bool) : Table Nat := Table.of (s.runStep p) 0 s.size

public theorem runs_exact (s : Src) (p : Char → Bool) (i : Nat) : (s.runs p).read i = s.run i p := by
  rw [runs, Table.read_exact, runStep_follow]

end Src

/-- A list of literal words by first scalar, ASCII buckets their own, longest first. -/
public structure WordSet where
  buckets : Array (Array (Array Char))
  deriving Inhabited

public def WordSet.of (ws : Array String) : WordSet := Id.run do
  let mut buckets : Array (Array (Array Char)) := Array.replicate 129 #[]
  for w in ws do
    let cs := (Src.ofString w).chars
    if let some c := cs[0]? then
      let b := if c.val < 0x80 then c.val.toNat else 128
      buckets := buckets.modify b (·.push cs)
  return { buckets := buckets.map fun b => b.qsort (fun x y => x.size > y.size) }

/-- The end of the longest word standing at `i` whose end `suffix` admits:
a Pygments `words` pattern after its prefix assertion. -/
public def WordSet.longest (ws : WordSet) (s : Src) (i : Nat) (suffix : Nat → Bool) :
    Option Nat := Id.run do
  if h : i < s.chars.size then
    let c := s.chars[i]
    let b := if c.val < 0x80 then c.val.toNat else 128
    for w in ws.buckets.getD b #[] do
      if s.lit i w && suffix (i + w.size) then return some (i + w.size)
  return none

/-- A regex alternation's words, in its order. -/
public def alternatives (ws : Array String) : Array (Array Char) :=
  ws.map fun w => (Src.ofString w).chars

/-- The first alternative standing at `i` whose continuation succeeds, as
an ordered alternation backtracks into its next branch. -/
public def firstAlt {α : Type} (alts : Array (Array Char)) (s : Src) (i : Nat)
    (cont : Nat → Option α) : Option α := Id.run do
  for w in alts do
    if s.lit i w then
      if let some a := cont (i + w.size) then return some a
  return none

/-- A lexer's state between rules: the tokens written, the position, and the state stack, top
first, the root always last. -/
public structure Machine (σ : Type) where
  out : Array Raw
  pos : Nat
  stack : List σ
  depth : Nat

namespace Machine

variable {σ : Type}

/-- One token, written unless empty, as `bygroups` skips an empty group. -/
@[inline] public def tok (m : Machine σ) (a b : Nat) (k : String) : Machine σ :=
  if a < b then { m with out := m.out.push ⟨a, b, k⟩, pos := b } else { m with pos := b }

@[inline] public def push (m : Machine σ) (st : σ) : Machine σ :=
  { m with stack := st :: m.stack, depth := m.depth + 1 }

/-- `#pop`, which never empties the stack. -/
@[inline] public def pop (m : Machine σ) : Machine σ :=
  match m.stack with
  | _ :: rest@(_ :: _) => { m with stack := rest, depth := m.depth - 1 }
  | _ => m

/-- `#push`: the current state again. -/
@[inline] public def dup (m : Machine σ) : Machine σ :=
  match m.stack with
  | st :: _ => m.push st
  | [] => m

/-- The state the next rule is drawn from. -/
@[inline] public def top? (m : Machine σ) : Option σ := m.stack.head?

/-- No rule matched: a newline resets to the root, anything else is one `Error` scalar. -/
public def fallback (m : Machine σ) (s : Src) (root : σ) : Machine σ :=
  let p := m.pos
  if s.is p '\n' then { m.tok p (p + 1) Ty.whitespace with stack := [root], depth := 1 }
  else m.tok p (p + 1) Ty.error

private theorem fallback_pos (m : Machine σ) (s : Src) (root : σ) :
    (m.fallback s root).pos = m.pos + 1 := by
  simp only [fallback]
  split <;> simp [tok]

/-- Whether a step from `m` to `next` read a scalar or popped a state:
what every rule of a terminating Pygments lexer does. -/
private def advanced (m next : Machine σ) : Prop :=
  m.pos < next.pos ∨ (next.pos = m.pos ∧ next.depth < m.depth)

private instance (m next : Machine σ) : Decidable (advanced m next) :=
  inferInstanceAs (Decidable (m.pos < next.pos ∨ (next.pos = m.pos ∧ next.depth < m.depth)))

/-- One step from `m`, starting from an empty token array; where the step
would not advance, the fallback's instead. -/
private def advance (root : σ) (step : Src → Machine σ → Machine σ) (s : Src)
    (m : Machine σ) : { next : Machine σ // m.advanced next } :=
  let m0 : Machine σ := { m with out := #[] }
  let next := step s m0
  if h : m0.advanced next then ⟨next, h⟩
  else ⟨m0.fallback s root, Or.inl (by
    show m.pos < (m0.fallback s root).pos
    rw [fallback_pos]
    exact Nat.lt_succ_self _)⟩

end Machine

/-- Run a lexer from `stack`, top first, to the end of the text; a step that neither reads nor
pops takes the fallback, which resets to the root. -/
public def driveFrom {σ : Type} (root : σ) (stack : List σ) (step : Src → Machine σ → Machine σ)
    (s : Src) : Array Raw :=
  let stack := if stack.isEmpty then [root] else stack
  go { out := #[], pos := 0, stack, depth := stack.length } #[]
where
  go (m : Machine σ) (out : Array Raw) : Array Raw :=
    if _hlt : m.pos < s.size then
      match m.advance root step s with
      | ⟨next, _h⟩ => go next (out ++ next.out)
    else out
  termination_by (s.size - m.pos, m.depth)
  decreasing_by
    simp only [Machine.advanced] at *
    rw [Prod.lex_def]
    omega

/-- Run a lexer from its root state to the end of the text. -/
public def drive {σ : Type} (root : σ) (step : Src → Machine σ → Machine σ) (s : Src) :
    Array Raw :=
  driveFrom root [root] step s

end LeanTex.Core.Highlight
