module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.PygmentsLexData

/-!
Pygments' `PythonLexer` (pygments/lexers/python.py), rule for rule; the rule
structure it mirrors is testdata/highlight/pygments-rules.txt. A port of
BSD-licensed code: Pygments' licence is testdata/highlight/LICENSE-Pygments.

A string state is one of Pygments' combined states: the escape rules its
prefix selects (`Esc`), then its quote's own rules, then the formatting
rules of an f-string or of an ordinary string. A soft keyword's pattern
case lexes the text before its `_` as a text of its own (`using(this)`),
from the root and blind to what surrounds it; that text holds no `_`, so
the lexer it runs never reaches the rule again.
-/
namespace LeanTex.Core.Highlight.Python

private inductive Quote where
  | dq | sq | tdq | tsq
  deriving Inhabited, BEq

private def Quote.ty : Quote → String
  | .dq | .tdq => Ty.stringDouble
  | .sq | .tsq => Ty.stringSingle

/-- A combined string state's leading escape rules: `rfstringescape`,
`fstringescape`, `stringescape`, `bytesescape`, or none for a raw string. -/
private inductive Esc where
  | raw | rf | f | s | b
  deriving Inhabited, BEq

private def Esc.fstring : Esc → Bool
  | .rf | .f => true
  | .raw | .s | .b => false

private inductive St where
  | root | fexpr | fexprInner | softInner | funcname | classname | imports | fromimport
  | str (esc : Esc) (q : Quote)
  deriving Inhabited

private structure Sets where
  keywords : WordSet
  constants : WordSet
  exprKeywords : WordSet
  builtins : WordSet
  exceptions : WordSet
  magicFuncs : WordSet
  magicVars : WordSet
  softStops : WordSet
  pseudo : Array (Array Char)
  operatorWords : Array (Array Char)

private def sets : Thunk Sets := Thunk.mk fun _ =>
  { keywords := .of PygmentsLexData.pythonKeywords
    constants := .of PygmentsLexData.pythonConstants
    exprKeywords := .of PygmentsLexData.pythonExprKeywords
    builtins := .of PygmentsLexData.pythonBuiltins
    exceptions := .of PygmentsLexData.pythonExceptions
    magicFuncs := .of PygmentsLexData.pythonMagicFuncs
    magicVars := .of PygmentsLexData.pythonMagicVars
    softStops := .of PygmentsLexData.pythonSoftStops
    pseudo := alternatives PygmentsLexData.pythonPseudo
    operatorWords := alternatives PygmentsLexData.pythonOperatorWords }

private abbrev M := Machine St

/-- `{word[…]` field's tail past its first name, `(\.\w+|\[[^\]]+\])*`: on
through a dotted name or a bracketed key, else stop. -/
private def groupStep (s : Src) (word close : Table Nat) (j : Nat) : Step Nat :=
  if s.is j '.' && s.word (j + 1) then .next (word.read (j + 1))
  else if s.is j '[' && s.sat (j + 1) (· != ']') then
    let c := close.read (j + 1)
    if s.is c ']' then .next (c + 1) else .stop j
  else .stop j

/-- `(?:\s|\\\s)*`: on through a space or an escaped one, else stop. -/
private def blanksStep (s : Src) (j : Nat) : Step Nat :=
  if s.space j then .next (j + 1)
  else if s.is j '\\' && s.space (j + 1) then .next (j + 2)
  else .stop j

/-- The first `quote` tripled at or after a position. -/
private def tripleStep (s : Src) (quote : Char) (j : Nat) : Step (Option Nat) :=
  if s.lit j #[quote, quote, quote] then .stop (some j)
  else if j < s.size then .next (j + 1) else .stop none

private def flag (c : Char) : Bool := "-#0 +".contains c

private def asciiDigit (c : Char) : Bool := c.isDigit

/-- The text, and the tables its rules read past the scalars they write. -/
private structure Ix where
  s : Src
  space : Table Nat
  tab : Table Nat
  blanks : Table Nat
  word : Table Nat
  digit : Table Nat
  asciiDigits : Table Nat
  flags : Table Nat
  softRest : Table Nat
  braceLine : Table Nat
  groups : Table Nat
  tdq : Table (Option Nat)
  tsq : Table (Option Nat)

private def Ix.of (s : Src) : Ix :=
  let word := s.runs wordChar
  let close := s.runs (· != ']')
  { s, word
    space := s.runs spaceChar
    tab := s.runs fun c => c == ' ' || c == '\t'
    blanks := Table.of (blanksStep s) 0 s.size
    digit := s.runs digitChar
    asciiDigits := s.runs asciiDigit
    flags := s.runs flag
    softRest := s.runs fun c => c != '\n' && c != '_'
    braceLine := s.runs fun c => c != '}' && c != '\n'
    groups := Table.of (groupStep s word close) 0 s.size
    tdq := Table.of (tripleStep s '"') none s.size
    tsq := Table.of (tripleStep s '\'') none s.size }

/-- A name, by the Python lexer's name pattern. -/
private def nameEnd (s : Src) (i : Nat) : Option Nat :=
  if s.sat i pyNameStart then some (s.run (i + 1) pyNameRest) else none

/-- The end of `(?:_?P)*` from `i`: greedy, one optional underscore before
each scalar. -/
private def underscored (s : Src) (i : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut j := i
  for _ in [0:s.size + 1] do
    if s.sat j p then j := j + 1
    else if s.is j '_' && s.sat (j + 1) p then j := j + 2
    else break
  return j

/-- `\d(?:_?\d)*`. -/
private def digitPart (s : Src) (i : Nat) : Option Nat :=
  if s.digit i then some (underscored s (i + 1) digitChar) else none

/-- `([eE][+-]?\d(?:_?\d)*)?` from `f`. -/
private def exponentEnd (s : Src) (f : Nat) : Nat :=
  if !(s.is f 'e' || s.is f 'E') then f
  else
    let q := if s.is (f + 1) '+' || s.is (f + 1) '-' then f + 2 else f + 1
    match digitPart s q with
    | some e => e
    | none => f

/-- `numbers`, in its order. -/
private def number (s : Src) (p : Nat) : Option (Nat × String) := Id.run do
  match digitPart s p with
  | some d =>
    if s.is d '.' then
      return some (exponentEnd s ((digitPart s (d + 1)).getD (d + 1)), Ty.numberFloat)
  | none =>
    if s.is p '.' then
      if let some f := digitPart s (p + 1) then return some (exponentEnd s f, Ty.numberFloat)
  if let some d := digitPart s p then
    if s.is d 'e' || s.is d 'E' then
      let q := if s.is (d + 1) '+' || s.is (d + 1) '-' then d + 2 else d + 1
      if let some e := digitPart s q then
        return some (if s.is e 'j' then e + 1 else e, Ty.numberFloat)
  if s.is p '0' then
    let radix (lower upper : Char) (ok : Char → Bool) (kind : String) : Option (Nat × String) :=
      if s.is (p + 1) lower || s.is (p + 1) upper then
        let e := underscored s (p + 2) ok
        if e > p + 2 then some (e, kind) else none
      else none
    if let some r := radix 'o' 'O' (fun c => '0' ≤ c && c ≤ '7') Ty.numberOct then return some r
    if let some r := radix 'b' 'B' (fun c => c == '0' || c == '1') Ty.numberBin then return some r
    if let some r := radix 'x' 'X' Char.isHexDigit Ty.numberHex then return some r
  return (digitPart s p).map (·, Ty.numberInteger)

/-- `!=|==|<<|>>|:=|[-~+/*%=<>&^|.]`. -/
private def operatorEnd (s : Src) (p : Nat) : Option Nat :=
  let two (a b : Char) := s.is p a && s.is (p + 1) b
  if two '!' '=' || two '=' '=' || two '<' '<' || two '>' '>' || two ':' '=' then some (p + 2)
  else if s.sat p (fun c => "-~+/*%=<>&^|.".contains c) then some (p + 1)
  else none

private def quoteAt (s : Src) (e : Nat) : Option (Quote × Nat) :=
  if s.is e '"' then
    if s.is (e + 1) '"' && s.is (e + 2) '"' then some (.tdq, e + 3) else some (.dq, e + 1)
  else if s.is e '\'' then
    if s.is (e + 1) '\'' && s.is (e + 2) '\'' then some (.tsq, e + 3) else some (.sq, e + 1)
  else none

/-- `expr`'s twenty string openings, in their order: the prefix's end, the
escapes it selects, the quote and the quote's end. Within one prefix
pattern only one alternative can stand before a quote, so the order of
its quote rules is `quoteAt`'s. A template string (`t`) opens as an
f-string does. -/
private def stringStart (s : Src) (p : Nat) : Option (Nat × Esc × Quote × Nat) := Id.run do
  let r (i : Nat) := s.is i 'r' || s.is i 'R'
  let f (i : Nat) := s.is i 'f' || s.is i 'F' || s.is i 't' || s.is i 'T'
  let b (i : Nat) := s.is i 'b' || s.is i 'B'
  let u (i : Nat) := s.is i 'u' || s.is i 'U'
  let opening (e : Nat) (esc : Esc) := (quoteAt s e).map fun (q, qe) => (e, esc, q, qe)
  if (r p && f (p + 1)) || (f p && r (p + 1)) then
    if let some x := opening (p + 2) .rf then return some x
  if f p then
    if let some x := opening (p + 1) .f then return some x
  if (r p && b (p + 1)) || (b p && r (p + 1)) then
    if let some x := opening (p + 2) .raw then return some x
  if r p then
    if let some x := opening (p + 1) .raw then return some x
  if u p then
    if let some x := opening (p + 1) .s then return some x
  if let some x := opening p .s then return some x
  if b p then
    if let some x := opening (p + 1) .b then return some x
  return none

private def boundaryAt (s : Src) (e : Nat) : Option Nat := if s.boundary e then some e else none

private def expr (s : Src) (m : M) : Option M := Id.run do
  let p := m.pos
  let t := sets.get
  if let some (e, esc, q, qe) := stringStart s p then
    return some (((m.tok p e Ty.stringAffix).tok e qe q.ty).push (.str esc q))
  let blank (c : Char) := spaceChar c && c != '\n'
  if s.sat p blank then return some (m.tok p (s.run p blank) Ty.text)
  if let some (e, k) := number s p then return some (m.tok p e k)
  if let some e := operatorEnd s p then return some (m.tok p e Ty.operator)
  if s.sat p (fun c => "]{}:(),;[".contains c) then return some (m.tok p (p + 1) Ty.punctuation)
  if let some e := firstAlt t.operatorWords s p (boundaryAt s) then
    return some (m.tok p e Ty.operatorWord)
  if let some e := t.exprKeywords.longest s p s.boundary then return some (m.tok p e Ty.keyword)
  if let some e := t.constants.longest s p s.boundary then
    return some (m.tok p e Ty.keywordConstant)
  if !(p > 0 && s.is (p - 1) '.') then
    if let some e := t.builtins.longest s p s.boundary then
      return some (m.tok p e Ty.nameBuiltin)
    if let some e := firstAlt t.pseudo s p (boundaryAt s) then
      return some (m.tok p e Ty.nameBuiltinPseudo)
    if let some e := t.exceptions.longest s p s.boundary then
      return some (m.tok p e Ty.nameException)
  if let some e := t.magicFuncs.longest s p s.boundary then
    return some (m.tok p e Ty.nameFunctionMagic)
  if let some e := t.magicVars.longest s p s.boundary then
    return some (m.tok p e Ty.nameVariableMagic)
  if s.is p '@' then
    if let some e := nameEnd s (p + 1) then return some (m.tok p e Ty.nameDecorator)
    return some (m.tok p (p + 1) Ty.operator)
  if let some e := nameEnd s p then return some (m.tok p e Ty.name)
  return none

/-- `^(\s*)([rRuUbB]{,2})("""[\s\S]*?""")` and its `'''` twin: the
whitespace's end, the prefix's end and the docstring's end. -/
private def docstring (ix : Ix) (p : Nat) (quote : Char) : Option (Nat × Nat × Nat) := Id.run do
  let s := ix.s
  let w := ix.space.read p
  let affix (c : Char) := "rRuUbB".contains c
  let a := if s.sat w affix then (if s.sat (w + 1) affix then w + 2 else w + 1) else w
  if !s.lit a #[quote, quote, quote] then return none
  match (if quote == '"' then ix.tdq else ix.tsq).read (a + 3) with
  | some q => return some (w, a, q + 3)
  | none => return none

/-- `soft-keywords`: indentation, then `match` or `case` that the rest of
the line does not reveal as a name. -/
private def softKeyword (ix : Ix) (p : Nat) : Option (Nat × Nat) := Id.run do
  let s := ix.s
  if !s.lineStart p then return none
  let w := ix.tab.read p
  let e := if s.lit w #['m', 'a', 't', 'c', 'h'] then w + 5
    else if s.lit w #['c', 'a', 's', 'e'] then w + 4 else w
  if e == w || !s.boundary e then return none
  let q := ix.tab.read e
  if s.sat q (fun c => ":,;=^&|@~)]}".contains c) then return none
  if (sets.get.softStops.longest s q s.boundary).isSome then return none
  return some (w, e)

private def root (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let t := sets.get
  if s.is p '\n' then return some (m.tok p (p + 1) Ty.whitespace)
  if s.lineStart p then
    for quote in ['"', '\''] do
      if let some (w, a, e) := docstring ix p quote then
        return some (((m.tok p w Ty.whitespace).tok w a Ty.stringAffix).tok a e Ty.stringDoc)
  if p == 0 && s.is 0 '#' && s.is 1 '!' && s.sat 2 (· != '\n') then
    return some (m.tok p (s.run 2 (· != '\n')) Ty.commentHashbang)
  if s.is p '#' then return some (m.tok p (s.run p (· != '\n')) Ty.commentSingle)
  if s.is p '\\' then
    return some (m.tok p (if s.is (p + 1) '\n' then p + 2 else p + 1) Ty.text)
  if let some e := t.keywords.longest s p s.boundary then return some (m.tok p e Ty.keyword)
  if let some e := t.constants.longest s p s.boundary then
    return some (m.tok p e Ty.keywordConstant)
  if let some (w, e) := softKeyword ix p then
    return some (((m.tok p w Ty.text).tok w e Ty.keyword).push .softInner)
  let opener (word : Array Char) (kind : String) (st : St) : Option M :=
    if s.lit p word then
      let e := p + word.size
      let w := ix.blanks.read e
      if w > e then some (((m.tok p e kind).tok e w Ty.whitespace).push st) else none
    else none
  let fromWord := #['f', 'r', 'o', 'm']
  let importWord := #['i', 'm', 'p', 'o', 'r', 't']
  let lazy (word : Array Char) (st : St) : Option M := Id.run do
    if !(s.lineStart p && s.lit p #['l', 'a', 'z', 'y']) then return none
    let w := ix.blanks.read (p + 4)
    if w == p + 4 || !s.lit w word then return none
    let e := w + word.size
    let w2 := ix.blanks.read e
    if w2 == e then return none
    return some (((((m.tok p (p + 4) Ty.keywordNamespace).tok (p + 4) w Ty.whitespace).tok w e
      Ty.keywordNamespace).tok e w2 Ty.whitespace).push st)
  return opener #['d', 'e', 'f'] Ty.keyword .funcname <|>
    opener #['c', 'l', 'a', 's', 's'] Ty.keyword .classname <|>
    lazy fromWord .fromimport <|> lazy importWord .imports <|>
    opener fromWord Ty.keywordNamespace .fromimport <|>
    opener importWord Ty.keywordNamespace .imports <|> expr s m

/-- `(=\s*)?(\![sraf])?` from `p`, before the `}` or `:` that closes a
replacement field. -/
private def fieldTailEnd (ix : Ix) (p : Nat) : Nat :=
  let s := ix.s
  let a := if s.is p '=' then ix.space.read (p + 1) else p
  if s.is a '!' && s.sat (a + 1) (fun c => "sraf".contains c) then a + 2 else a

private def fexpr (ix : Ix) (m : M) : Option M :=
  let s := ix.s
  let p := m.pos
  let a := fieldTailEnd ix p
  if s.sat p (fun c => "{([".contains c) then some ((m.tok p (p + 1) Ty.punctuation).push .fexprInner)
  else if s.is a '}' then some ((m.tok p (a + 1) Ty.stringInterpol).pop)
  else if s.is a ':' then some ((m.tok p (a + 1) Ty.stringInterpol).pop)
  else if s.space p then some (m.tok p (s.run p spaceChar) Ty.whitespace)
  else expr s m

private def fexprInner (s : Src) (m : M) : Option M :=
  let p := m.pos
  if s.sat p (fun c => "{([".contains c) then some ((m.tok p (p + 1) Ty.punctuation).push .fexprInner)
  else if s.sat p (fun c => "])}".contains c) then some ((m.tok p (p + 1) Ty.punctuation).pop)
  else if s.space p then some (m.tok p (s.run p spaceChar) Ty.whitespace)
  else expr s m

/-- `(\s+)([^\n_]*)(_\b)`, the middle group lexed by `inner` as a text of
its own, or `default('#pop')`. -/
private def softInner (inner : Src → Array Raw) (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let w := ix.space.read p
  if w > p then
    let g := ix.softRest.read w
    if s.is g '_' && s.boundary (g + 1) then
      let m := m.tok p w Ty.whitespace
      let shifted := (inner ⟨s.chars.extract w g⟩).map fun r =>
        { r with start := r.start + w, stop := r.stop + w }
      return some ({ m with out := m.out ++ shifted }.tok g (g + 1) Ty.keyword)
  return some m.pop

private def funcname (s : Src) (m : M) : Option M :=
  let p := m.pos
  match sets.get.magicFuncs.longest s p s.boundary with
  | some e => some (m.tok p e Ty.nameFunctionMagic)
  | none =>
    match nameEnd s p with
    | some e => some ((m.tok p e Ty.nameFunction).pop)
    | none => some m.pop

private def classname (s : Src) (m : M) : Option M :=
  (nameEnd s m.pos).map fun e => (m.tok m.pos e Ty.nameClass).pop

private def imports (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let w := ix.space.read p
  if w > p && s.lit w #['a', 's'] then
    let w2 := ix.space.read (w + 2)
    if w2 > w + 2 then
      return some (((m.tok p w Ty.whitespace).tok w (w + 2) Ty.keyword).tok (w + 2) w2 Ty.whitespace)
  if s.is p '.' then return some (m.tok p (p + 1) Ty.nameNamespace)
  if let some e := nameEnd s p then return some (m.tok p e Ty.nameNamespace)
  if s.is w ',' then
    let w2 := ix.space.read (w + 1)
    return some (((m.tok p w Ty.whitespace).tok w (w + 1) Ty.operator).tok (w + 1) w2 Ty.whitespace)
  return some m.pop

private def fromimport (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let w := ix.space.read p
  if w > p && s.lit w #['i', 'm', 'p', 'o', 'r', 't'] && s.boundary (w + 6) then
    return some (((m.tok p w Ty.whitespace).tok w (w + 6) Ty.keywordNamespace).pop)
  if s.is p '.' then return some (m.tok p (p + 1) Ty.nameNamespace)
  if s.lit p #['N', 'o', 'n', 'e'] && s.boundary (p + 4) then
    return some ((m.tok p (p + 4) Ty.keywordConstant).pop)
  if let some e := nameEnd s p then return some (m.tok p e Ty.nameNamespace)
  return some m.pop

private def hex (s : Src) (i n : Nat) : Bool := Id.run do
  for k in [0:n] do
    if !s.sat (i + k) Char.isHexDigit then return false
  return true

/-- `stringescape`'s pattern: `\N{…}`, `\uXXXX`, `\UXXXXXXXX`. -/
private def unicodeEscape (ix : Ix) (p : Nat) : Option Nat := Id.run do
  let s := ix.s
  if !s.is p '\\' then return none
  if s.is (p + 1) 'N' && s.is (p + 2) '{' then
    let close := ix.braceLine.read (p + 3)
    if s.is close '}' then return some (close + 1)
  if s.is (p + 1) 'u' && hex s (p + 2) 4 then return some (p + 6)
  if s.is (p + 1) 'U' && hex s (p + 2) 8 then return some (p + 10)
  return none

private def octal (c : Char) : Bool := '0' ≤ c && c ≤ '7'

/-- `bytesescape`'s pattern. -/
private def bytesEscape (s : Src) (p : Nat) : Option Nat :=
  if !s.is p '\\' then none
  else if s.sat (p + 1) (fun c => "\\abfnrtv\"'".contains c) || s.is (p + 1) '\n' then some (p + 2)
  else if s.is (p + 1) 'x' && hex s (p + 2) 2 then some (p + 4)
  else if s.sat (p + 1) octal then
    some (if s.sat (p + 2) octal then (if s.sat (p + 3) octal then p + 4 else p + 3) else p + 2)
  else none

/-- `%(\(\w+\))?[-#0 +]*([0-9]+|[*])?(\.([0-9]+|[*]))?[hlL]?[E-GXc-giorsaux%]`.
Every part's scalars stay out of the parts after it, so only the greedy
reading can end on a conversion. -/
private def percentEnd (ix : Ix) (p : Nat) : Option Nat := Id.run do
  let s := ix.s
  if !s.is p '%' then return none
  let mut a := p + 1
  if s.is a '(' then
    let b := ix.word.read (a + 1)
    if b > a + 1 && s.is b ')' then a := b + 1
  a := ix.flags.read a
  if s.sat a asciiDigit then a := ix.asciiDigits.read a
  else if s.is a '*' then a := a + 1
  if s.is a '.' then
    if s.sat (a + 1) asciiDigit then a := ix.asciiDigits.read (a + 1)
    else if s.is (a + 1) '*' then a := a + 2
  if s.sat a (fun c => "hlL".contains c) then a := a + 1
  if s.sat a (fun c => "EFGXcdefgiorsaux%".contains c) then return some (a + 1)
  return none

/-- A format spec after its fill and alignment:
`[-+ ]?#?0?(\d+)?,?(\.\d+)?[E-GXb-gnosx%]?`, greedy, since no part's
scalars include the `}` that must follow. -/
private def specRestEnd (ix : Ix) (b : Nat) : Nat := Id.run do
  let s := ix.s
  let mut a := b
  if s.sat a (fun c => "-+ ".contains c) then a := a + 1
  if s.is a '#' then a := a + 1
  if s.is a '0' then a := a + 1
  a := ix.digit.read a
  if s.is a ',' then a := a + 1
  if s.is a '.' && s.digit (a + 1) then a := ix.digit.read (a + 1)
  if s.sat a (fun c => "EFGXbcdefgnosx%".contains c) then a := a + 1
  return a

/-- `\{((\w+)((\.\w+)|(\[[^\]]+\]))*)?(\![sra])?(\:(.?[<>=\^])?…)?\}`. The
field and conversion read greedily; the spec's fill and alignment are tried
in the pattern's order, two scalars, the alignment alone, then neither. -/
private def braceEnd (ix : Ix) (p : Nat) : Option Nat := Id.run do
  let s := ix.s
  if !s.is p '{' then return none
  let mut a := p + 1
  if s.word a then a := ix.groups.read (ix.word.read a)
  if s.is a '!' && s.sat (a + 1) (fun c => "sra".contains c) then a := a + 2
  if s.is a ':' then
    let align (c : Char) := "<>=^".contains c
    let fills : List Nat :=
      (if s.sat (a + 1) (· != '\n') && s.sat (a + 2) align then [a + 3] else []) ++
      (if s.sat (a + 1) align then [a + 2] else []) ++ [a + 1]
    for b in fills do
      let e := specRestEnd ix b
      if s.is e '}' then return some (e + 1)
  if s.is a '}' then return some (a + 1)
  return none

private def strState (esc : Esc) (q : Quote) (ix : Ix) (m : M) : Option M := Id.run do
  let s := ix.s
  let p := m.pos
  let ty := q.ty
  if esc == .rf || esc == .f then
    if s.is p '{' && s.is (p + 1) '{' then return some (m.tok p (p + 2) Ty.stringEscape)
    if s.is p '}' && s.is (p + 1) '}' then return some (m.tok p (p + 2) Ty.stringEscape)
  if esc == .f || esc == .s then
    if let some e := unicodeEscape ix p then return some (m.tok p e Ty.stringEscape)
  if esc == .f || esc == .s || esc == .b then
    if let some e := bytesEscape s p then return some (m.tok p e Ty.stringEscape)
  match q with
  | .dq | .sq =>
    let c := if q == .dq then '"' else '\''
    if s.is p c then return some ((m.tok p (p + 1) ty).pop)
    if s.is p '\\' && s.sat (p + 1) (fun d => d == '\\' || d == c || d == '\n') then
      return some (m.tok p (p + 2) Ty.stringEscape)
  | .tdq | .tsq =>
    let c := if q == .tdq then '"' else '\''
    if s.lit p #[c, c, c] then return some ((m.tok p (p + 3) ty).pop)
  if esc.fstring then
    if s.is p '}' then return some (m.tok p (p + 1) Ty.stringInterpol)
    if s.is p '{' then return some ((m.tok p (p + 1) Ty.stringInterpol).push .fexpr)
    let plain (c : Char) := !"\\'\"{}\n".contains c
    if s.sat p plain then return some (m.tok p (s.run p plain) ty)
  else
    if let some e := percentEnd ix p then return some (m.tok p e Ty.stringInterpol)
    if let some e := braceEnd ix p then return some (m.tok p e Ty.stringInterpol)
    let plain (c : Char) := !"\\'\"%{\n".contains c
    if s.sat p plain then return some (m.tok p (s.run p plain) ty)
  if s.sat p (fun c => "'\"\\".contains c) then return some (m.tok p (p + 1) ty)
  if !esc.fstring then
    if s.is p '%' then return some (m.tok p (p + 1) ty)
    if s.is p '{' then return some (m.tok p (if s.is (p + 1) '{' then p + 2 else p + 1) ty)
  if (q == .tdq || q == .tsq) && s.is p '\n' then return some (m.tok p (p + 1) ty)
  return none

private def step (inner : Src → Array Raw) (ix : Ix) (m : M) : M :=
  let next := match m.top? with
    | some .root | none => root ix m
    | some .fexpr => fexpr ix m
    | some .fexprInner => fexprInner ix.s m
    | some .softInner => softInner inner ix m
    | some .funcname => funcname ix.s m
    | some .classname => classname ix.s m
    | some .imports => imports ix m
    | some .fromimport => fromimport ix m
    | some (.str esc q) => strState esc q ix m
  match next with
  | some m' => m'
  | none => m.fallback ix.s .root

/-- One text lexed from the root, its tables its own. -/
private def lexWith (inner : Src → Array Raw) (s : Src) : Array Raw :=
  let ix := Ix.of s
  drive .root (fun _ m => step inner ix m) s

/-- The raw token stream Pygments' `PythonLexer` writes. -/
public def lex (s : Src) : Array Raw :=
  lexWith (lexWith fun _ => #[]) s

end LeanTex.Core.Highlight.Python
