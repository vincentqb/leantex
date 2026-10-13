module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.Highlight.Bash

/-! Pygments' `BashSessionLexer` (pygments/lexers/shell.py; BSD-licensed, its licence is
testdata/highlight/LICENSE-Pygments), its prompt pattern matched in linear time. -/
namespace LeanTex.Core.Highlight.Console

/-- A regular expression with no captures whose every repeat is of one
scalar class, in Python `re`'s priority order: `alt` tries its left branch
first; a greedy `star` tries one more scalar first, a lazy one the rest of
the pattern first. -/
public inductive Re where
  | empty
  | cls (p : Char → Bool)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (p : Char → Bool) (greedy : Bool)
  deriving Inhabited

/-- A compiled pattern's instruction: read one scalar of a class and go on
at `next`, fork with `first` preferred, or accept. -/
private inductive Inst where
  | read (p : Char → Bool) (next : Nat)
  | fork (first second : Nat)
  | accept
  deriving Inhabited

/-- `r` compiled in front of the instruction `k`: its entry, and the program grown by its
instructions. -/
private def Re.compile : Re → Nat → Array Inst → Nat × Array Inst
  | .empty, k, prog => (k, prog)
  | .cls p, k, prog => (prog.size, prog.push (.read p k))
  | .seq a b, k, prog =>
    let (eb, prog) := b.compile k prog
    a.compile eb prog
  | .alt a b, k, prog =>
    let (ea, prog) := a.compile k prog
    let (eb, prog) := b.compile k prog
    (prog.size, prog.push (.fork ea eb))
  | .star p greedy, k, prog =>
    let reads := prog.size
    let prog := prog.push (.read p (reads + 1))
    (reads + 1, prog.push (if greedy then .fork reads k else .fork k reads))

/-- A compiled pattern, and for each instruction the instructions its
forks reach without reading — reads and the accept — in priority order,
each once. -/
private structure Prog where
  insts : Array Inst
  entry : Nat
  reach : Array (Array Nat)

/-- Every instruction's reach, upward: a fork's targets stand below it, so
their reach is known when it is; a target above it would reach nothing. -/
private def reaches (insts : Array Inst) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.mkEmpty insts.size
  for inst in insts do
    match inst with
    | .fork a b =>
      let first := out.getD a #[]
      out := out.push ((out.getD b #[]).foldl (init := first) fun acc q =>
        if acc.contains q then acc else acc.push q)
    | _ => out := out.push #[out.size]
  return out

private def Prog.of (r : Re) : Prog :=
  let (entry, insts) := r.compile 0 #[.accept]
  { insts, entry, reach := reaches insts }

/-- The end of the match Python's `re.match` finds at `start`, the text ending at `lim`, every
way through the pattern advancing together. -/
private def Prog.firstEnd (g : Prog) (s : Src) (start lim : Nat) : Option Nat := Id.run do
  let mut ways := g.reach.getD g.entry #[]
  let mut found : Option Nat := none
  let mut held : Array Nat := Array.replicate g.insts.size 0
  for i in [start:lim + 1] do
    let mut next : Array Nat := #[]
    for pc in ways do
      match g.insts[pc]? with
      | some .accept =>
        found := some i
        break
      | some (.read p k) =>
        if i < lim && s.sat i p then
          for q in g.reach.getD k #[] do
            if held.getD q 0 != i + 1 then
              held := held.setIfInBounds q (i + 1)
              next := next.push q
      | _ => pure ()
    if next.isEmpty then break
    ways := next
  return found

/-- `r` compiled once: where `re.match` ends a match of it at `start` in a
text ending at `lim`, first in priority order. -/
public def Re.matcher (r : Re) : Src → Nat → Nat → Option Nat :=
  let g := Prog.of r
  fun s start lim => g.firstEnd s start lim

private def lit (c : Char) : Re := .cls (· == c)
private def plus (p : Char → Bool) : Re := .seq (.cls p) (.star p true)
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
\[\S+[@:][^\n]+\].+))\s*[$#%❯]`. -/
public def ps1 : Re :=
  let dot : Char → Bool := (· != '\n')
  let nonSpace : Char → Bool := fun c => !spaceChar c
  let atColon := Re.cls (fun c => c == '@' || c == ':')
  let bracketed := seqs [lit '[', .star dot false, lit ']']
  let venv := opt (seqs [lit '(', plus nonSpace, lit ')'])
  let shell := seqs [lit 's', lit 'h', .star nonSpace false]
  let userHost := seqs [plus wordChar, plus nonSpace, atColon, plus nonSpace,
    opt (.seq (plus spaceChar) (plus nonSpace))]
  let bracketHost := seqs [lit '[', plus nonSpace, atColon, plus dot, lit ']', plus dot]
  seqs [.alt bracketed (.seq venv (alts [.empty, lit ' ', shell, userHost, bracketHost])),
    .star spaceChar true, .cls (fun c => c == '$' || c == '#' || c == '%' || c == '❯')]

/-- `ps1`, compiled once per process, on first use. -/
private def prompt : Thunk Prog := Thunk.mk fun _ => Prog.of ps1

/-- Where the prompt pattern's match at `start` ends, the line ending at
`lim`. -/
public def promptEnd (s : Src) (start lim : Nat) : Option Nat :=
  prompt.get.firstEnd s start lim

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

private def flush (code : Array Char) (insertions : Array (Nat × Array Piece))
    (out : Array Piece) : Array Piece :=
  if insertions.isEmpty then out else out ++ insertAll (Bash.lex ⟨code⟩) insertions

private def endsContinued (code : Array Char) : Bool :=
  code.size ≥ 2 && code[code.size - 2]? == some '\\' && code.back? == some '\n'

/-- The raw token stream Pygments' `BashSessionLexer` writes, at the positions of its text. -/
public def lex (s : Src) : Array Raw := Id.run do
  let mut pieces : Array Piece := #[]
  let mut code : Array Char := #[]
  let mut insertions : Array (Nat × Array Piece) := #[]
  let mut continued := false
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
        insertions := insertions.push (code.size, #[(Ty.genericPromptVirtualEnv, r + 1 - ls)])
        if w > r + 1 then
          insertions := insertions.push (code.size, #[(Ty.text, w - (r + 1))])
        v := w
    match promptEnd s v le with
    | some e =>
      let prompt := s.runTo e le spaceChar
      insertions := insertions.push (code.size, #[(Ty.genericPrompt, prompt - v)])
      code := code ++ s.chars.extract prompt le
      continued := endsContinued code
    | none =>
      if continued then
        if v + 2 ≤ le && s.is v '>' && s.is (v + 1) ' ' then
          insertions := insertions.push (code.size, #[(Ty.genericPrompt, 2)])
          code := code ++ s.chars.extract (v + 2) le
        else
          code := code ++ s.chars.extract v le
        continued := endsContinued code
      else
        pieces := flush code insertions pieces
        pieces := pieces.push (Ty.genericOutput, le - v)
        code := #[]
        insertions := #[]
    ls := le
  pieces := flush code insertions pieces
  let mut out : Array Raw := #[]
  let mut at_ := 0
  for (kind, len) in pieces do
    if len > 0 then out := out.push ⟨at_, at_ + len, kind⟩
    at_ := at_ + len
  return out

end LeanTex.Core.Highlight.Console
