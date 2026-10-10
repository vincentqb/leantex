module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.PygmentsLexData

/-!
Pygments' `Lean4Lexer` (pygments/lexers/lean.py), rule for rule; the rule
structure it mirrors is testdata/highlight/pygments-rules.txt. A port of
BSD-licensed code: Pygments' licence is testdata/highlight/LICENSE-Pygments. Every state
falls through to a rule that consumes, except `string`, whose unlisted
escapes take the shared fallback.
-/
namespace LeanTex.Core.Highlight.Lean4

private inductive St where
  | root | attr | comment | docstring | string
  deriving Inhabited

private structure Sets where
  keywordNamespace : WordSet
  keyword : WordSet
  keywordType : WordSet
  errorWords : WordSet
  operators : WordSet
  punctuation : WordSet

private def sets : Thunk Sets := Thunk.mk fun _ =>
  { keywordNamespace := .of PygmentsLexData.lean4KeywordNamespace
    keyword := .of PygmentsLexData.lean4Keyword
    keywordType := .of PygmentsLexData.lean4KeywordType
    errorWords := .of PygmentsLexData.lean4ErrorWords
    operators := .of PygmentsLexData.lean4Operators
    punctuation := .of PygmentsLexData.lean4Punctuation }

private abbrev M := Machine St

/-- The text, and the one table a rule reads past the scalars it writes:
the end of a run of `\w` and `'`, which `[~?][a-z][\w']*:` reads before it
knows whether its colon follows. -/
private structure Ix where
  s : Src
  label : Table Nat

private def Ix.of (s : Src) : Ix := { s, label := s.runs fun c => wordChar c || c == '\'' }

/-- A name segment, by the Lean 4 lexer's name pattern. -/
private def segmentEnd (s : Src) (i : Nat) : Option Nat :=
  if s.sat i leanNameStart then some (s.run (i + 1) leanNameRest) else none

/-- `(\.` segment `)*`, greedy: every iteration consumes two scalars. -/
private def dottedEnd (s : Src) (i : Nat) : Nat := Id.run do
  let mut e := i
  for _ in [0:s.size] do
    if !s.is e '.' then break
    match segmentEnd s (e + 1) with
    | some e' => e := e'
    | none => break
  return e

private def asciiDigit (c : Char) : Bool := c.isDigit

/-- `(\d+\.\d*)([eE][+-]?[0-9]+)?` past its fraction's end `f`. -/
private def exponentEnd (s : Src) (f : Nat) : Nat :=
  if !(s.is f 'e' || s.is f 'E') then f
  else
    let q := if s.is (f + 1) '+' || s.is (f + 1) '-' then f + 2 else f + 1
    if s.sat q asciiDigit then s.run q asciiDigit else f

private def expression (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let t := sets.get
  if s.space p then return some (m.tok p (s.run p spaceChar) Ty.whitespace)
  if s.is p '/' && s.is (p + 1) '-' && s.is (p + 2) '-' then
    return some ((m.tok p (p + 3) Ty.stringDoc).push .docstring)
  if s.is p '/' && s.is (p + 1) '-' then
    return some ((m.tok p (p + 2) Ty.comment).push .comment)
  if s.is p '-' && s.is (p + 1) '-' then
    return some (m.tok p (s.run p (· != '\n')) Ty.commentSingle)
  if s.boundary p then
    if let some e := t.keywordType.longest s p s.boundary then
      return some (m.tok p e Ty.keywordType)
    if let some e := t.errorWords.longest s p s.boundary then
      return some (m.tok p e Ty.genericError)
  if let some e := t.operators.longest s p (fun _ => true) then
    return some (m.tok p e Ty.nameBuiltinPseudo)
  if let some e := t.punctuation.longest s p (fun _ => true) then
    return some (m.tok p e Ty.operator)
  if let some e := segmentEnd s p then return some (m.tok p e Ty.name)
  if s.is p '`' then
    let q := if s.is (p + 1) '`' then p + 2 else p + 1
    if let some e := segmentEnd s q then
      return some (m.tok p (dottedEnd s e) Ty.stringSymbol)
  if p > 0 && s.is (p - 1) '.' && s.digit p then
    return some (m.tok p (s.run p digitChar) Ty.number)
  if s.digit p then
    let d := s.run p digitChar
    if s.is d '.' then
      return some (m.tok p (exponentEnd s (s.run (d + 1) digitChar)) Ty.numberFloat)
    return some (m.tok p d Ty.numberInteger)
  if s.is p '"' then return some ((m.tok p (p + 1) Ty.stringDouble).push .string)
  if (s.is p '~' || s.is p '?') && s.sat (p + 1) (fun c => 'a' ≤ c && c ≤ 'z') then
    let e := ix.label.read (p + 2)
    if s.is e ':' then return some (m.tok p (e + 1) Ty.nameVariable)
  if p < s.size then return some (m.tok p (p + 1) Ty.nameBuiltinPseudo)
  return none

private def root (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let t := sets.get
  if s.boundary p then
    if let some e := t.keywordNamespace.longest s p s.boundary then
      return some (m.tok p e Ty.keywordNamespace)
    if let some e := t.keyword.longest s p s.boundary then
      return some (m.tok p e Ty.keyword)
  if s.is p '@' && s.is (p + 1) '[' then
    return some ((m.tok p (p + 2) Ty.keywordDeclaration).push .attr)
  return expression ix m

private def attr (ix : Ix) (m : M) : Option M :=
  if ix.s.is m.pos ']' then some ((m.tok m.pos (m.pos + 1) Ty.keywordDeclaration).pop)
  else expression ix m

private def notSlashDash (c : Char) : Bool := c != '/' && c != '-'

private def comment (s : Src) (m : M) : Option M :=
  let p := m.pos
  if s.sat p notSlashDash then some (m.tok p (s.run p notSlashDash) Ty.commentMultiline)
  else if s.is p '/' && s.is (p + 1) '-' then some ((m.tok p (p + 2) Ty.commentMultiline).dup)
  else if s.is p '-' && s.is (p + 1) '/' then some ((m.tok p (p + 2) Ty.commentMultiline).pop)
  else if s.is p '/' || s.is p '-' then some (m.tok p (p + 1) Ty.commentMultiline)
  else none

private def docstring (s : Src) (m : M) : Option M :=
  let p := m.pos
  if s.sat p notSlashDash then some (m.tok p (s.run p notSlashDash) Ty.stringDoc)
  else if s.is p '-' && s.is (p + 1) '/' then some ((m.tok p (p + 2) Ty.stringDoc).pop)
  else if s.is p '/' || s.is p '-' then some (m.tok p (p + 1) Ty.stringDoc)
  else none

private def plainString (c : Char) : Bool := c != '\\' && c != '"'

private def string (s : Src) (m : M) : Option M :=
  let p := m.pos
  if s.sat p plainString then some (m.tok p (s.run p plainString) Ty.stringDouble)
  else if s.is p '\\' && s.sat (p + 1) (fun c => c == 'n' || c == '"' || c == '\\' || c == '\n') then
    some (m.tok p (p + 2) Ty.stringEscape)
  else if s.is p '"' then some ((m.tok p (p + 1) Ty.stringDouble).pop)
  else none

private def step (ix : Ix) (m : M) : M :=
  let next := match m.top? with
    | some .root | none => root ix m
    | some .attr => attr ix m
    | some .comment => comment ix.s m
    | some .docstring => docstring ix.s m
    | some .string => string ix.s m
  match next with
  | some m' => m'
  | none => m.fallback ix.s .root

/-- The raw token stream Pygments' `Lean4Lexer` writes. -/
public def lex (s : Src) : Array Raw :=
  let ix := Ix.of s
  drive .root (fun _ m => step ix m) s

end LeanTex.Core.Highlight.Lean4
