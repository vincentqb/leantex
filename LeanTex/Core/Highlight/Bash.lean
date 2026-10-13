module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.PygmentsLexData
import Std.Data.HashMap

/-! Pygments' `BashLexer` (pygments/lexers/shell.py) rule for rule, mirroring
testdata/highlight/pygments-rules.txt. A port of BSD-licensed code: Pygments' licence is
testdata/highlight/LICENSE-Pygments. -/
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

@[inline] private def moveKey (v : Nat) (c : Char) : Nat := v * 0x110000 + c.val.toNat

/-- The suffix automaton of a text (Blumer et al., 1985), built in linear time, its moves hashed. -/
private structure Sam where
  moves : Std.HashMap Nat Nat
  lastEnd : Array Nat

private def Sam.of (cs : Array Char) : Sam := Id.run do
  let mut len : Array Nat := #[0]
  let mut link : Array Nat := #[0]
  let mut ends : Array Nat := #[0]
  let mut head : Array Nat := #[0]
  let mut edgeChar : Array Char := #[]
  let mut edgeNext : Array Nat := #[]
  let mut moves : Std.HashMap Nat Nat := {}
  let mut last := 0
  for h : i in [0:cs.size] do
    let c := cs[i]
    let cur := len.size
    len := len.push (len.getD last 0 + 1)
    link := link.push 0
    ends := ends.push (i + 1)
    head := head.push 0
    let mut v := last
    let mut fell := false
    for _ in [0:cur + 1] do
      if moves.contains (moveKey v c) then break
      moves := moves.insert (moveKey v c) cur
      edgeChar := edgeChar.push c
      edgeNext := edgeNext.push (head.getD v 0)
      head := head.set! v edgeChar.size
      if v == 0 then
        fell := true
        break
      v := link.getD v 0
    if !fell then
      let q := moves.getD (moveKey v c) 0
      if len.getD v 0 + 1 == len.getD q 0 then
        link := link.set! cur q
      else
        let clone := len.size
        len := len.push (len.getD v 0 + 1)
        link := link.push (link.getD q 0)
        ends := ends.push 0
        head := head.push 0
        let mut e := head.getD q 0
        for _ in [0:edgeChar.size + 1] do
          if e == 0 then break
          let d := edgeChar.getD (e - 1) c
          moves := moves.insert (moveKey clone d) (moves.getD (moveKey q d) 0)
          edgeChar := edgeChar.push d
          edgeNext := edgeNext.push (head.getD clone 0)
          head := head.set! clone edgeChar.size
          e := edgeNext.getD (e - 1) 0
        let mut r := v
        for _ in [0:clone + 1] do
          if moves.get? (moveKey r c) != some q then break
          moves := moves.insert (moveKey r c) clone
          if r == 0 then break
          r := link.getD r 0
        link := (link.set! q clone).set! cur clone
    last := cur
  let states := len.size
  let mut start : Array Nat := Array.replicate (cs.size + 2) 0
  for v in [0:states] do
    start := start.modify (len.getD v 0 + 1) (· + 1)
  for k in [0:cs.size + 1] do
    start := start.set! (k + 1) (start.getD (k + 1) 0 + start.getD k 0)
  let mut order : Array Nat := Array.replicate states 0
  for v in [0:states] do
    let l := len.getD v 0
    order := order.set! (start.getD l 0) v
    start := start.modify l (· + 1)
  let mut lastEnd := ends
  for k in [0:states] do
    let v := order.getD (states - 1 - k) 0
    if v != 0 then
      let u := link.getD v 0
      lastEnd := lastEnd.set! u (max (lastEnd.getD u 0) (lastEnd.getD v 0))
  return { moves, lastEnd }

/-- The length of the longest prefix of `[g, g + len)` standing again at least one scalar past its
own end. -/
private def Sam.recurring (t : Sam) (s : Src) (g len : Nat) : Nat := Id.run do
  let mut v := 0
  let mut best := 0
  for k in [1:len + 1] do
    match t.moves.get? (moveKey v (s.chars.getD (g + k - 1) ' ')) with
    | none => break
    | some w =>
      v := w
      if t.lastEnd.getD w 0 ≥ g + 2 * k + 1 then best := k else break
  return best

/-- `(?s)\$?"(\\.|[^"\\$])*"`'s scan past the quote. -/
private def doubleStep (s : Src) (j : Nat) : Step (Option Nat) :=
  if s.is j '\\' && j + 1 < s.size then .next (j + 2)
  else if s.is j '"' then .stop (some (j + 1))
  else if j < s.size && !s.is j '$' && !s.is j '\\' then .next (j + 1)
  else .stop none

/-- `(?s)\$'(\\\\|\\[0-7]+|\\.|[^'\\])*'`'s scan past the quote. -/
private def ansiStep (s : Src) (j : Nat) : Step (Option Nat) :=
  if s.is j '\\' && j + 1 < s.size then .next (j + 2)
  else if s.is j '\'' then .stop (some (j + 1))
  else if j < s.size && !s.is j '\\' then .next (j + 1)
  else .stop none

/-- The text, and the tables its rules read past the scalars they write. -/
private structure Ix where
  s : Src
  space : Table Nat
  word : Table Nat
  digit : Table Nat
  line : Table Nat
  quote : Table Nat
  double : Table (Option Nat)
  ansi : Table (Option Nat)
  sam : Thunk Sam

private def Ix.of (s : Src) : Ix :=
  { s
    space := s.runs spaceChar
    word := s.runs wordChar
    digit := s.runs digitChar
    line := s.runs (· != '\n')
    quote := s.runs (· != '\'')
    double := Table.of (doubleStep s) none s.size
    ansi := Table.of (ansiStep s) none s.size
    sam := Thunk.mk fun _ => Sam.of s.chars }

/-- `<<-?\s*(\'?)\\?(\w+)[\w\W]+?\2`, in time linear in the token: the delimiter's longest
prefix recurring past its own length wins, at its first recurrence. -/
private def heredocAt (ix : Ix) (p : Nat) : Option Nat := Id.run do
  let s := ix.s
  if !(s.is p '<' && s.is (p + 1) '<') then return none
  let mut a := p + 2
  if s.is a '-' then a := a + 1
  a := ix.space.read a
  if s.is a '\'' then a := a + 1
  if s.is a '\\' then a := a + 1
  let g := a
  let word := ix.word.read g - g
  if word == 0 then return none
  let len := ix.sam.get.recurring s g word
  if len == 0 then return none
  let w := s.chars.extract g (g + len)
  let mut zw : Array Nat := Array.replicate len 0
  let mut l := 0
  let mut r := 0
  for i in [1:len] do
    let mut k := if i < r then min (r - i) (zw.getD (i - l) 0) else 0
    if i + k ≥ r then
      for _ in [0:len] do
        if i + k < len && w.getD k ' ' == w.getD (i + k) ' ' then k := k + 1 else break
      if i + k > r then
        l := i
        r := i + k
    zw := zw.setIfInBounds i k
  l := 0
  r := 0
  let mut best := 0
  let mut bestAt := 0
  for q in [g + 1:s.size] do
    let mut k := if q < r then min (r - q) (zw.getD (q - l) 0) else 0
    if q + k ≥ r then
      for _ in [0:len] do
        if k < len && w.getD k ' ' == s.chars.getD (q + k) ' ' && q + k < s.size then k := k + 1
        else break
      if q + k > r then
        l := q
        r := q + k
    let v := min k (q - g - 1)
    if v > best then
      best := v
      bestAt := q
    if best == len then break
  if best == 0 then return none
  return some (bestAt + best)

/-- `heredocAt` over a text of its own. -/
public def heredocEnd (s : Src) (p : Nat) : Option Nat := heredocAt (Ix.of s) p

/-- `(?s)\$?"(\\.|[^"\\$])*"`: a double-quoted string with nothing to
interpolate, in one token. -/
private def plainDoubleEnd (ix : Ix) (p : Nat) : Option Nat :=
  let s := ix.s
  let a := if s.is p '$' && s.is (p + 1) '"' then p + 1 else p
  if s.is a '"' then ix.double.read (a + 1) else none

/-- `(?s)\$'(\\\\|\\[0-7]+|\\.|[^'\\])*'`. -/
private def ansiEnd (ix : Ix) (p : Nat) : Option Nat :=
  if ix.s.is p '$' && ix.s.is (p + 1) '\'' then ix.ansi.read (p + 2) else none

private def textScalar (c : Char) : Bool := !spaceChar c && !"=[]{}()$\"'`\\<&|;".contains c

private def basic (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let t := sets.get
  if s.boundary p then
    let afterKeyword (e : Nat) : Option (Nat × Nat) :=
      if s.sat e (fun c => wordChar c || "#$?!*@-".contains c) then none
      else some (e, s.run e spaceChar)
    if let some (e, w) := firstAlt t.keywords s p afterKeyword then
      return some ((m.tok p e Ty.keyword).tok e w Ty.whitespace)
    let before (e : Nat) : Option Nat :=
      if s.sat e (fun c => spaceChar c || c == ')' || c == '`') then some e else none
    if let some e := firstAlt t.builtins s p before then return some (m.tok p e Ty.nameBuiltin)
  if p == 0 && s.is 0 '#' && s.is 1 '!' && s.sat 2 (· != '\n') then
    let e := ix.line.read 2
    if s.is e '\n' then return some (m.tok p (e + 1) Ty.commentHashbang)
  if s.is p '#' then
    let e := ix.line.read p
    if s.is e '\n' then return some (m.tok p (e + 1) Ty.commentSingle)
  if s.is p '\\' && p + 1 < s.size then return some (m.tok p (p + 2) Ty.stringEscape)
  if s.boundary p && s.word p then
    let w := ix.word.read p
    let ws := ix.space.read w
    let op := if s.is ws '+' && s.is (ws + 1) '=' then ws + 2 else if s.is ws '=' then ws + 1 else ws
    if op > ws then
      return some (((m.tok p w Ty.nameVariable).tok w ws Ty.whitespace).tok ws op Ty.operator)
  if s.sat p (fun c => "[]{}()=".contains c) then return some (m.tok p (p + 1) Ty.operator)
  if s.is p '<' && s.is (p + 1) '<' && s.is (p + 2) '<' then return some (m.tok p (p + 3) Ty.operator)
  if let some e := heredocAt ix p then return some (m.tok p e Ty.string)
  if (s.is p '&' && s.is (p + 1) '&') || (s.is p '|' && s.is (p + 1) '|') then
    return some (m.tok p (p + 2) Ty.operator)
  return none

private def data (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  if let some e := plainDoubleEnd ix p then return some (m.tok p e Ty.stringDouble)
  if s.is p '"' then return some ((m.tok p (p + 1) Ty.stringDouble).push .string)
  if let some e := ansiEnd ix p then return some (m.tok p e Ty.stringSingle)
  if s.is p '\'' then
    let q := ix.quote.read (p + 1)
    if s.is q '\'' then return some (m.tok p (q + 1) Ty.stringSingle)
  if s.sat p (fun c => c == ';' || c == '&' || c == '|') then
    return some (m.tok p (p + 1) Ty.punctuation)
  if s.space p then return some (m.tok p (s.run p spaceChar) Ty.whitespace)
  if s.digit p then
    let e := ix.digit.read p
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

private def root (ix : Ix) (m : M) : Option M :=
  basic ix m <|>
    (if ix.s.is m.pos '`' then some ((m.tok m.pos (m.pos + 1) Ty.stringBacktick).push .backticks)
     else none) <|>
    data ix m <|> interp ix.s m

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

private def curly (ix : Ix) (m : M) : Option M :=
  let s := ix.s
  let p := m.pos
  let punct (c : Char) := !"}:\"'`$\\".contains c
  if s.is p '}' then some ((m.tok p (p + 1) Ty.stringInterpol).pop)
  else if s.is p ':' && s.is (p + 1) '-' then some (m.tok p (p + 2) Ty.keyword)
  else if s.word p then some (m.tok p (s.run p wordChar) Ty.nameVariable)
  else if s.sat p punct then some (m.tok p (s.run p punct) Ty.punctuation)
  else if s.is p ':' then some (m.tok p (p + 1) Ty.punctuation)
  else root ix m

private def paren (ix : Ix) (m : M) : Option M :=
  if ix.s.is m.pos ')' then some ((m.tok m.pos (m.pos + 1) Ty.keyword).pop) else root ix m

private def math (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  if s.is p ')' && s.is (p + 1) ')' then return some ((m.tok p (p + 2) Ty.keyword).pop)
  let two (a b : Char) := s.is p a && s.is (p + 1) b
  if two '*' '*' || two '|' '|' || two '<' '<' || two '>' '>' then
    return some (m.tok p (p + 2) Ty.operator)
  if s.sat p (fun c => "-+*/%^|&<>".contains c) then return some (m.tok p (p + 1) Ty.operator)
  if s.digit p then
    let d := ix.digit.read p
    if s.is d '#' then
      let based (c : Char) := digitChar c || (c.val < 0x80 && c.isAlpha)
      if s.sat (d + 1) based then return some (m.tok p (s.run (d + 1) based) Ty.number)
      if !s.is (d + 1) ' ' then return some (m.tok p (d + 1) Ty.number)
  if s.is p '0' && (s.is (p + 1) 'x' || s.is (p + 1) 'X') then
    let hexish (c : Char) := digitChar c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
    if s.sat (p + 2) hexish then return some (m.tok p (s.run (p + 2) hexish) Ty.number)
  if s.digit p then return some (m.tok p (s.run p digitChar) Ty.number)
  if s.sat p asciiStart then return some (m.tok p (s.run (p + 1) wordChar) Ty.nameVariable)
  return root ix m

private def backticks (ix : Ix) (m : M) : Option M :=
  if ix.s.is m.pos '`' then some ((m.tok m.pos (m.pos + 1) Ty.stringBacktick).pop) else root ix m

private def step (ix : Ix) (m : M) : M :=
  let next := match m.top? with
    | some .root | none => root ix m
    | some .string => string ix.s m
    | some .curly => curly ix m
    | some .paren => paren ix m
    | some .math => math ix m
    | some .backticks => backticks ix m
  match next with
  | some m' => m'
  | none => m.fallback ix.s .root

/-- The raw token stream Pygments' `BashLexer` writes. -/
public def lex (s : Src) : Array Raw :=
  let ix := Ix.of s
  drive .root (fun _ m => step ix m) s

end LeanTex.Core.Highlight.Bash
