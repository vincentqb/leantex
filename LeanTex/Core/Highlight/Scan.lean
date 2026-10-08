module

import LeanTex.Core.PygmentsLexData

/-!
What the native lexers share: the text they read, the Unicode classes
their patterns name, word lists, and the raw token stream they write.

Each lexer mirrors one Pygments `RegexLexer` (pygments/lexer.py): at every
position the current state's rules are tried in order and the first match
wins; `#pop` keeps the root state; when nothing matches, a newline resets
the stack to the root and is whitespace, and any other scalar is one
`Error` token. A Python `re` pattern's semantics is what a rule's code
reproduces, so a class it names is Python's: `\w`, `\s` and `\d` are the
installed Python's Unicode answers, generated into `PygmentsLexData` with
the rest of the lexers' data. A `words` list matches its longest listed
word that the suffix admits, which the generator checks against Pygments'
own compiled pattern before writing the list.
-/
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

/-- A hex digit's value. The generator emits `[0-9a-f]` only. -/
private def nib (b : UInt8) : UInt32 :=
  if b ≤ 0x39 then b.toUInt32 - 0x30 else b.toUInt32 - 0x57

private def hexRanges (s : String) : Array UInt32 := Id.run do
  let bs := s.toUTF8
  let mut out : Array UInt32 := Array.mkEmpty (bs.size / 6)
  for i in [0:bs.size / 6] do
    let mut v : UInt32 := 0
    for k in [0:6] do
      v := v * 16 + nib (bs[i * 6 + k]?.getD 0x30)
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

/-- Built once per process, on first use: `loadClasses` takes a `Unit` so
a process that lexes nothing parses no table. -/
private def classes : Thunk Classes := Thunk.mk loadClasses

/-- Membership in sorted inclusive ranges, by binary search. -/
private def inRanges (rs : Array UInt32) (v : UInt32) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size / 2
  for _ in [0:rs.size + 1] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if v < rs[2 * mid]?.getD 0 then hi := mid
      else if rs[2 * mid + 1]?.getD 0 < v then lo := mid + 1
      else return true
    else break
  return false

/-- `\w`. The generator checks that the table's ASCII members are these. -/
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

/-- What the ASCII fast paths answer, beside what the tables answer, for one
scalar: the suite holds every ASCII scalar's pair equal. -/
public def asciiAgrees (c : Char) : Bool :=
  let t := classes.get
  wordChar c == inRanges t.word c.val && spaceChar c == inRanges t.space c.val &&
    digitChar c == inRanges t.digit c.val && leanNameStart c == inRanges t.leanStart c.val &&
    leanNameRest c == inRanges t.leanRest c.val && pyNameStart c == inRanges t.pyStart c.val &&
    pyNameRest c == inRanges t.pyRest c.val

/-- The text a lexer reads. Positions count scalars, as Pygments' offsets do. -/
public structure Src where
  chars : Array Char
  deriving Inhabited

namespace Src

public def ofString (s : String) : Src :=
  ⟨s.foldl (fun a c => a.push c) (Array.mkEmpty s.utf8ByteSize)⟩

@[inline] public def size (s : Src) : Nat := s.chars.size

@[inline] public def is (s : Src) (i : Nat) (c : Char) : Bool := s.chars[i]? == some c

/-- The scalar at `i` satisfies `p`; nothing past the end does. -/
@[inline] public def sat (s : Src) (i : Nat) (p : Char → Bool) : Bool :=
  match s.chars[i]? with
  | some c => p c
  | none => false

@[inline] public def word (s : Src) (i : Nat) : Bool := s.sat i wordChar
@[inline] public def space (s : Src) (i : Nat) : Bool := s.sat i spaceChar
@[inline] public def digit (s : Src) (i : Nat) : Bool := s.sat i digitChar

/-- `\b` at `i`: a word scalar on exactly one side. -/
public def boundary (s : Src) (i : Nat) : Bool :=
  (i > 0 && s.word (i - 1)) != s.word i

/-- `^` under `re.MULTILINE`. -/
@[inline] public def lineStart (s : Src) (i : Nat) : Bool := i == 0 || s.is (i - 1) '\n'

/-- The end of the longest run of scalars from `i` satisfying `p`. -/
public def run (s : Src) (i : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut stop := i
  for h : j in [i:s.chars.size] do
    if !p s.chars[j] then break
    stop := j + 1
  return stop

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
    if s.chars[i + k]? != some w[k] then return false
  return true

/-- The first occurrence of `w`'s first `k` scalars starting at or after
`from`: a backreference's search. -/
public def find (s : Src) (fromPos : Nat) (w : Array Char) (k : Nat) : Option Nat := Id.run do
  if k == 0 then return some fromPos
  for j in [fromPos:s.chars.size + 1 - min k (s.chars.size + 1)] do
    let mut hit := true
    for t in [0:k] do
      if s.chars[j + t]? != w[t]? then
        hit := false
        break
    if hit then return some j
  return none

end Src

/-- A list of literal words, by first scalar: an ASCII scalar's bucket is
its own, every other scalar shares the last. Longest first in a bucket. -/
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
  let some c := s.chars[i]? | return none
  let b := if c.val < 0x80 then c.val.toNat else 128
  for w in ws.buckets[b]?.getD #[] do
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

/-- A lexer's state between rules: the tokens written, the position, and
the state stack, whose bottom is always the root. -/
public structure Machine (σ : Type) where
  out : Array Raw
  pos : Nat
  stack : Array σ

namespace Machine

variable {σ : Type}

/-- One token, written unless empty, as `bygroups` skips an empty group. -/
@[inline] public def tok (m : Machine σ) (a b : Nat) (k : String) : Machine σ :=
  if a < b then { m with out := m.out.push ⟨a, b, k⟩, pos := b } else { m with pos := b }

@[inline] public def push (m : Machine σ) (st : σ) : Machine σ := { m with stack := m.stack.push st }

/-- `#pop`, which never empties the stack. -/
@[inline] public def pop (m : Machine σ) : Machine σ :=
  if m.stack.size > 1 then { m with stack := m.stack.pop } else m

/-- `#push`: the current state again. -/
@[inline] public def dup (m : Machine σ) : Machine σ :=
  match m.stack.back? with
  | some st => m.push st
  | none => m

/-- No rule matched: a newline resets to the root, anything else is one
`Error` scalar. -/
public def fallback (m : Machine σ) (s : Src) (root : σ) : Machine σ :=
  let p := m.pos
  if s.is p '\n' then { m.tok p (p + 1) Ty.whitespace with stack := #[root] }
  else m.tok p (p + 1) Ty.error

end Machine

/-- Run a lexer whose every step consumes a scalar or pops a state no
consuming step had not pushed: at most `2n + 1` steps for `n` scalars. -/
public def drive {σ : Type} (root : σ) (step : Src → Machine σ → Machine σ) (s : Src) :
    Array Raw := Id.run do
  let mut m : Machine σ := { out := #[], pos := 0, stack := #[root] }
  for _ in [0:2 * s.size + 1] do
    if m.pos ≥ s.size then break
    m := step s m
  return m.out

end LeanTex.Core.Highlight
