module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.PygmentsLexData

/-!
Pygments' `BashLexer` (pygments/lexers/shell.py), rule for rule; the rule
structure it mirrors is testdata/highlight/pygments-rules.txt. Every state
but `string` ends in the root's rules, so the shared fallback is reached
only by a quote the data rules leave unclosed.
-/
namespace LeanTex.Core.Highlight.Bash

private inductive St where
  | root | string | curly | paren | math | backticks
  deriving Inhabited

private structure Sets where
  keywords : Array (Array Char)
  builtins : Array (Array Char)

private def sets : Thunk Sets := Thunk.mk fun _ =>
  { keywords := alternatives PygmentsLexData.bashKeywords
    builtins := alternatives PygmentsLexData.bashBuiltins }

private abbrev M := Machine St

/-- `<<-?\s*(\'?)\\?(\w+)[\w\W]+?\2`. Only the delimiter's length can
backtrack: giving back an optional mark leaves `\w+` facing that mark. The
longest prefix of the delimiter that recurs after it wins, at its first
recurrence. -/
private def heredocEnd (s : Src) (p : Nat) : Option Nat := Id.run do
  if !(s.is p '<' && s.is (p + 1) '<') then return none
  let mut a := p + 2
  if s.is a '-' then a := a + 1
  a := s.run a spaceChar
  if s.is a '\'' then a := a + 1
  if s.is a '\\' then a := a + 1
  let g := a
  let len := s.run g wordChar - g
  let word := s.chars.extract g (g + len)
  for i in [0:len] do
    let k := len - i
    if let some q := s.find (g + k + 1) word k then return some (q + k)
  return none

/-- `(?s)\$?"(\\.|[^"\\$])*"`: a double-quoted string with nothing to
interpolate, in one token. -/
private def plainDoubleEnd (s : Src) (p : Nat) : Option Nat := Id.run do
  let a := if s.is p '$' && s.is (p + 1) '"' then p + 1 else p
  if !s.is a '"' then return none
  let mut j := a + 1
  for _ in [0:s.size + 1] do
    if s.is j '\\' && j + 1 < s.size then j := j + 2
    else if s.is j '"' then return some (j + 1)
    else if j < s.size && !s.is j '$' && !s.is j '\\' then j := j + 1
    else return none
  return none

/-- `(?s)\$'(\\\\|\\[0-7]+|\\.|[^'\\])*'`. -/
private def ansiEnd (s : Src) (p : Nat) : Option Nat := Id.run do
  if !(s.is p '$' && s.is (p + 1) '\'') then return none
  let mut j := p + 2
  for _ in [0:s.size + 1] do
    if s.is j '\\' && j + 1 < s.size then j := j + 2
    else if s.is j '\'' then return some (j + 1)
    else if j < s.size && !s.is j '\\' then j := j + 1
    else return none
  return none

private def textScalar (c : Char) : Bool := !spaceChar c && !"=[]{}()$\"'`\\<&|;".contains c

private def basic (s : Src) (m : M) : Option M := Id.run do
  let p := m.pos
  let t := sets.get
  if s.boundary p then
    let afterKeyword (e : Nat) : Option (Nat × Nat) :=
      let w := s.run e spaceChar
      if w > e then some (e, if s.word w then w else e)
      else if s.boundary e then some (e, e) else none
    if let some (e, w) := firstAlt t.keywords s p afterKeyword then
      return some ((m.tok p e Ty.keyword).tok e w Ty.whitespace)
    let before (e : Nat) : Option Nat :=
      if s.sat e (fun c => spaceChar c || c == ')' || c == '`') then some e else none
    if let some e := firstAlt t.builtins s p before then return some (m.tok p e Ty.nameBuiltin)
  if p == 0 && s.is 0 '#' && s.is 1 '!' && s.sat 2 (· != '\n') then
    let e := s.run 2 (· != '\n')
    if s.is e '\n' then return some (m.tok p (e + 1) Ty.commentHashbang)
  if s.is p '#' then
    let e := s.run p (· != '\n')
    if s.is e '\n' then return some (m.tok p (e + 1) Ty.commentSingle)
  if s.is p '\\' && p + 1 < s.size then return some (m.tok p (p + 2) Ty.stringEscape)
  if s.boundary p && s.word p then
    let w := s.run p wordChar
    let ws := s.run w spaceChar
    let op := if s.is ws '+' && s.is (ws + 1) '=' then ws + 2 else if s.is ws '=' then ws + 1 else ws
    if op > ws then
      return some (((m.tok p w Ty.nameVariable).tok w ws Ty.whitespace).tok ws op Ty.operator)
  if s.sat p (fun c => "[]{}()=".contains c) then return some (m.tok p (p + 1) Ty.operator)
  if s.is p '<' && s.is (p + 1) '<' && s.is (p + 2) '<' then return some (m.tok p (p + 3) Ty.operator)
  if let some e := heredocEnd s p then return some (m.tok p e Ty.string)
  if (s.is p '&' && s.is (p + 1) '&') || (s.is p '|' && s.is (p + 1) '|') then
    return some (m.tok p (p + 2) Ty.operator)
  return none

private def data (s : Src) (m : M) : Option M := Id.run do
  let p := m.pos
  if let some e := plainDoubleEnd s p then return some (m.tok p e Ty.stringDouble)
  if s.is p '"' then return some ((m.tok p (p + 1) Ty.stringDouble).push .string)
  if let some e := ansiEnd s p then return some (m.tok p e Ty.stringSingle)
  if s.is p '\'' then
    if let some q := s.find (p + 1) #['\''] 1 then return some (m.tok p (q + 1) Ty.stringSingle)
  if s.sat p (fun c => c == ';' || c == '&' || c == '|') then
    return some (m.tok p (p + 1) Ty.punctuation)
  if s.space p then return some (m.tok p (s.run p spaceChar) Ty.whitespace)
  if s.digit p then
    let e := s.run p digitChar
    if !s.word e then return some (m.tok p e Ty.number)
  if s.sat p textScalar then return some (m.tok p (s.run p textScalar) Ty.text)
  if s.is p '<' then return some (m.tok p (p + 1) Ty.text)
  return none

private def asciiStart (c : Char) : Bool := c.isAlpha || c == '_'

private def interp (s : Src) (m : M) : Option M := Id.run do
  let p := m.pos
  if !s.is p '$' then return none
  if s.is (p + 1) '(' && s.is (p + 2) '(' then return some ((m.tok p (p + 3) Ty.keyword).push .math)
  if s.is (p + 1) '(' then return some ((m.tok p (p + 2) Ty.keyword).push .paren)
  if s.is (p + 1) '{' then
    return some ((m.tok p (if s.is (p + 2) '#' then p + 3 else p + 2) Ty.stringInterpol).push .curly)
  if s.sat (p + 1) asciiStart then return some (m.tok p (s.run (p + 2) wordChar) Ty.nameVariable)
  if s.digit (p + 1) then return some (m.tok p (s.run (p + 1) digitChar) Ty.nameVariable)
  if s.sat (p + 1) (fun c => "#$?!_*@-".contains c) then return some (m.tok p (p + 2) Ty.nameVariable)
  return some (m.tok p (p + 1) Ty.text)

private def root (s : Src) (m : M) : Option M :=
  basic s m <|>
    (if s.is m.pos '`' then some ((m.tok m.pos (m.pos + 1) Ty.stringBacktick).push .backticks)
     else none) <|>
    data s m <|> interp s m

/-- `(?s)(\\\\|\\[0-7]+|\\.|[^"\\$])+`: a backslash takes the scalar after
it, whatever the branch, and the run stops at `"`, `$` or a last backslash. -/
private def stringRunEnd (s : Src) (p : Nat) : Nat := Id.run do
  let mut j := p
  for _ in [0:s.size + 1] do
    if s.is j '\\' && j + 1 < s.size then j := j + 2
    else if j < s.size && !s.is j '"' && !s.is j '$' && !s.is j '\\' then j := j + 1
    else break
  return j

private def string (s : Src) (m : M) : Option M :=
  let p := m.pos
  if s.is p '"' then some ((m.tok p (p + 1) Ty.stringDouble).pop)
  else
    let e := stringRunEnd s p
    if e > p then some (m.tok p e Ty.stringDouble) else interp s m

private def curly (s : Src) (m : M) : Option M :=
  let p := m.pos
  let punct (c : Char) := !"}:\"'`$\\".contains c
  if s.is p '}' then some ((m.tok p (p + 1) Ty.stringInterpol).pop)
  else if s.is p ':' && s.is (p + 1) '-' then some (m.tok p (p + 2) Ty.keyword)
  else if s.word p then some (m.tok p (s.run p wordChar) Ty.nameVariable)
  else if s.sat p punct then some (m.tok p (s.run p punct) Ty.punctuation)
  else if s.is p ':' then some (m.tok p (p + 1) Ty.punctuation)
  else root s m

private def paren (s : Src) (m : M) : Option M :=
  if s.is m.pos ')' then some ((m.tok m.pos (m.pos + 1) Ty.keyword).pop) else root s m

private def math (s : Src) (m : M) : Option M := Id.run do
  let p := m.pos
  if s.is p ')' && s.is (p + 1) ')' then return some ((m.tok p (p + 2) Ty.keyword).pop)
  let two (a b : Char) := s.is p a && s.is (p + 1) b
  if two '*' '*' || two '|' '|' || two '<' '<' || two '>' '>' then
    return some (m.tok p (p + 2) Ty.operator)
  if s.sat p (fun c => "-+*/%^|&<>".contains c) then return some (m.tok p (p + 1) Ty.operator)
  if s.digit p then
    let d := s.run p digitChar
    if s.is d '#' then
      let based (c : Char) := digitChar c || (c.val < 0x80 && c.isAlpha)
      if s.sat (d + 1) based then return some (m.tok p (s.run (d + 1) based) Ty.number)
      if !s.is (d + 1) ' ' then return some (m.tok p (d + 1) Ty.number)
  if s.is p '0' && (s.is (p + 1) 'x' || s.is (p + 1) 'X') then
    let hexish (c : Char) := digitChar c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
    if s.sat (p + 2) hexish then return some (m.tok p (s.run (p + 2) hexish) Ty.number)
  if s.digit p then return some (m.tok p (s.run p digitChar) Ty.number)
  if s.sat p asciiStart then return some (m.tok p (s.run (p + 1) wordChar) Ty.nameVariable)
  return root s m

private def backticks (s : Src) (m : M) : Option M :=
  if s.is m.pos '`' then some ((m.tok m.pos (m.pos + 1) Ty.stringBacktick).pop) else root s m

private def step (s : Src) (m : M) : M :=
  let next := match m.stack.back? with
    | some .root | none => root s m
    | some .string => string s m
    | some .curly => curly s m
    | some .paren => paren s m
    | some .math => math s m
    | some .backticks => backticks s m
  next.getD (m.fallback s .root)

/-- The raw token stream Pygments' `BashLexer` writes. -/
public def lex (s : Src) : Array Raw := drive .root step s

end LeanTex.Core.Highlight.Bash
