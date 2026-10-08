module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.Highlight.Bash

/-!
Pygments' `BashSessionLexer` (`ShellSessionBaseLexer`,
pygments/lexers/shell.py): each line is a prompt and the code after it, a
continuation of a backslash-ended command, or output. A block of prompted
lines lexes as one Bash text, the prompts inserted back where they stood
(do_insertions in pygments/lexer.py).

The prompt pattern backtracks across several of its branches, so it is
matched by the backtracking it is written for, over the pattern's own
structure (`ps1`), first success in the pattern's order, as Python's `re`
answers.

Pygments emits a virtual-environment prefix's tokens before the code they
precede, but reports offsets for them from an earlier block's start: the
text is in order and the offsets are not. These tokens carry the text's
own positions.
-/
namespace LeanTex.Core.Highlight.Console

/-- A regular expression with no captures, in Python `re`'s priority order:
`alt` tries its left branch first, `star` tries one more iteration first
when greedy and last when lazy. -/
private inductive Re where
  | empty
  | cls (p : Char → Bool)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (r : Re) (greedy : Bool)
  deriving Inhabited

/-- The first end, in priority order, of a match of `re` from `i` within
`lim` that the continuation `k` accepts. An iteration that consumes
nothing ends its loop, as Python's `re` ends one. -/
private def Re.run (s : Src) (lim : Nat) : Re → Nat → (Nat → Option Nat) → Option Nat
  | .empty, i, k => k i
  | .cls p, i, k => if i < lim && s.sat i p then k (i + 1) else none
  | .seq a b, i, k => a.run s lim i fun j => b.run s lim j k
  | .alt a b, i, k => (a.run s lim i k).orElse fun _ => b.run s lim i k
  | .star r true, i, k =>
    (r.run s lim i fun j =>
      if _h : i < j ∧ j ≤ lim then (Re.star r true).run s lim j k else none).orElse fun _ => k i
  | .star r false, i, k =>
    (k i).orElse fun _ => r.run s lim i fun j =>
      if _h : i < j ∧ j ≤ lim then (Re.star r false).run s lim j k else none
termination_by re i => (sizeOf re, lim + 1 - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

private def lit (c : Char) : Re := .cls (· == c)
private def plus (r : Re) : Re := .seq r (.star r true)
private def opt (r : Re) : Re := .alt r .empty
private def seqs : List Re → Re
  | [] => .empty
  | [r] => r
  | r :: rs => .seq r (seqs rs)
private def alts : List Re → Re
  | [] => .empty
  | [r] => r
  | r :: rs => .alt r (alts rs)

/-- `_ps1rgx` without its final `\s*` and rest-of-line group, which always
match: `(?:\[.*?\]|(?:\(\S+\))?(?:| |sh\S*?|\w+\S+[@:]\S+(?:\s+\S+)?|
\[\S+[@:][^\n]+\].+))\s*[$#%]`. -/
private def ps1 : Re :=
  let dot := Re.cls (· != '\n')
  let nonSpace := Re.cls (fun c => !spaceChar c)
  let space := Re.cls spaceChar
  let atColon := Re.cls (fun c => c == '@' || c == ':')
  let bracketed := seqs [lit '[', .star dot false, lit ']']
  let venv := opt (seqs [lit '(', plus nonSpace, lit ')'])
  let shell := seqs [lit 's', lit 'h', .star nonSpace false]
  let userHost := seqs [plus (.cls wordChar), plus nonSpace, atColon, plus nonSpace,
    opt (.seq (plus space) (plus nonSpace))]
  let bracketHost := seqs [lit '[', plus nonSpace, atColon, plus (.cls (· != '\n')), lit ']',
    plus dot]
  seqs [.alt bracketed (.seq venv (alts [.empty, lit ' ', shell, userHost, bracketHost])),
    .star space true, .cls (fun c => c == '$' || c == '#' || c == '%')]

/-- What the session lexer writes: a type and a length, at the running
position. -/
private abbrev Piece := String × Nat

/-- Pygments' do_insertions: the code's tokens, each split where an insertion
falls inside it, with every insertion's pieces after the code before its
index. -/
private def insertAll (tokens : Array Raw) (insertions : Array (Nat × Array Piece)) :
    Array Piece := Id.run do
  let mut out : Array Piece := #[]
  let mut next := 0
  for t in tokens do
    let len := t.stop - t.start
    let mut oldi := 0
    for _ in [next:insertions.size] do
      let some (index, pieces) := insertions[next]? | break
      if t.start + len < index then break
      let cut := index - t.start
      if cut > oldi then out := out.push (t.kind, cut - oldi)
      out := out ++ pieces
      oldi := cut
      next := next + 1
    if oldi < len then out := out.push (t.kind, len - oldi)
  for (_, pieces) in insertions.extract next insertions.size do
    out := out ++ pieces
  return out

private structure Block where
  code : Array Char := #[]
  insertions : Array (Nat × Array Piece) := #[]
  continued : Bool := false

private def Block.flush (b : Block) (out : Array Piece) : Array Piece :=
  if b.insertions.isEmpty then out
  else out ++ insertAll (Bash.lex ⟨b.code⟩) b.insertions

private def endsContinued (code : Array Char) : Bool :=
  code.size ≥ 2 && code[code.size - 2]? == some '\\' && code.back? == some '\n'

/-- The raw token stream Pygments' `BashSessionLexer` writes, at the
positions of the text it writes. -/
public def lex (s : Src) : Array Raw := Id.run do
  let mut pieces : Array Piece := #[]
  let mut b : Block := {}
  let mut ls := 0
  for _ in [0:s.size + 1] do
    if ls ≥ s.size then break
    let nl := s.run ls (· != '\n')
    if nl ≥ s.size then break
    let le := nl + 1
    let mut v := ls
    if s.is ls '(' then
      let r := s.runTo (ls + 1) le (· != ')')
      if r < le && s.is r ')' then
        let w := s.runTo (r + 1) le spaceChar
        b := { b with insertions := b.insertions.push (b.code.size, #[(Ty.genericPromptVirtualEnv, r + 1 - ls)]) }
        if w > r + 1 then
          b := { b with insertions := b.insertions.push (b.code.size, #[(Ty.text, w - (r + 1))]) }
        v := w
    match ps1.run s le v some with
    | some e =>
      let prompt := s.runTo e le spaceChar
      let tail := s.chars.extract prompt le
      let code := b.code ++ tail
      b := { b with insertions := b.insertions.push (b.code.size, #[(Ty.genericPrompt, prompt - v)])
                    code, continued := endsContinued code }
    | none =>
      if b.continued then
        if v + 2 ≤ le && s.is v '>' && s.is (v + 1) ' ' then
          let code := b.code ++ s.chars.extract (v + 2) le
          b := { b with insertions := b.insertions.push (b.code.size, #[(Ty.genericPrompt, 2)])
                        code, continued := endsContinued code }
        else
          let tail := s.chars.extract v le
          let code := b.code ++ tail
          b := { b with code, continued := endsContinued code }
      else
        pieces := b.flush pieces
        pieces := pieces.push (Ty.genericOutput, le - v)
        b := {}
    ls := le
  pieces := b.flush pieces
  let mut out : Array Raw := #[]
  let mut at_ := 0
  for (kind, len) in pieces do
    if len > 0 then out := out.push ⟨at_, at_ + len, kind⟩
    at_ := at_ + len
  return out

end LeanTex.Core.Highlight.Console
