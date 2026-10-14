module

/- Shared lexical conventions for the line-scanning source checks; the compiler and axiom
audit remain authoritative. -/

public section

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Whether `line` contains `word` delimited by non-word characters. -/
def hasWord (line word : String) : Bool :=
  (line.split (fun c => !isWordChar c)).any (·.toString == word)

def containsSub (line pat : String) : Bool :=
  (line.splitOn pat).length > 1

/-- Does `lit` occur in `cs` at index `i`? -/
def litAt (cs : Array Char) (i : Nat) (lit : String) : Bool := Id.run do
  let mut k := i
  for c in lit.toList do
    if cs[k]? != some c then return false
    k := k + 1
  return true

/-- The class the shared lexer gives one character of Lean source. -/
inductive LexCls where
  /-- Code outside every literal and comment. -/
  | code
  /-- The first character of a string, raw string or character literal. -/
  | litOpen
  /-- The rest of a literal: its delimiters, escapes, gaps and a character literal's character. -/
  | lit
  /-- A string's text: its characters, and each escape's character without its backslash. -/
  | strText
  /-- The `/` opening a block comment. -/
  | blockOpen
  /-- The first `-` of a line comment's `--`. -/
  | lineOpen
  /-- The `/` closing an outermost block comment. -/
  | blockClose
  /-- A comment's other delimiters: the rest of each opener, doc markers, nested markers. -/
  | mark
  /-- A comment's prose. -/
  | prose
  | newline
  deriving BEq, Inhabited, Repr

/-- Where the lexer stands between two characters; `gap` is a string's line after a `\` break. -/
private inductive LexMode where
  | code
  | line
  | block (depth : Nat)
  | str
  | gap
  | raw (hashes : Nat)

/-- How many `#` stand at `cs[k]` onward. -/
private def lexHashes (cs : Array Char) (k : Nat) : Nat := Id.run do
  let mut n := 0
  for j in [k:cs.size] do
    if cs[j]? == some '#' then n := n + 1 else break
  return n

/-- The length of the character literal a quote at `i` opens where no identifier precedes it: an
escape's `\x` two digits, `\u` four, else one character. -/
private def lexCharLen (cs : Array Char) (i : Nat) : Option Nat :=
  let close (n : Nat) : Option Nat := if cs[i + n - 1]? == some '\'' then some n else none
  match cs[i + 1]? with
  | some '\\' => match cs[i + 2]? with
    | some 'x' => close 6
    | some 'u' => close 8
    | some '\n' | none => none
    | some _ => close 4
  | some '\n' | some '\'' | none => none
  | some _ => close 3

/-- Every character of a Lean source classed: nested block comments with their doc markers, line
comments, strings with escapes and gaps, raw strings, and character literals apart from an
identifier's primes, an interpolation read flat, so a quote inside its braces closes the string. -/
def lexClasses (text : String) : Array (Char × LexCls) := Id.run do
  let cs := text.toList.toArray
  let chr (k : Nat) : Char := cs[k]?.getD ' '
  let mut out : Array (Char × LexCls) := #[]
  let mut mode : LexMode := .code
  let mut ident := false
  let mut i := 0
  for _ in [0:2 * cs.size] do
    if i ≥ cs.size then break
    let c := chr i
    if c == '\n' then
      out := out.push (c, .newline)
      ident := false
      if mode matches .line then mode := .code
      i := i + 1
      continue
    match mode with
    | .line => out := out.push (c, .prose); i := i + 1
    | .block depth =>
      if c == '/' && chr (i + 1) == '-' then
        mode := .block (depth + 1)
        out := (out.push (c, .mark)).push ('-', .mark)
        i := i + 2
      else if c == '-' && chr (i + 1) == '/' then
        out := (out.push (c, .mark)).push ('/', if depth ≤ 1 then .blockClose else .mark)
        mode := if depth ≤ 1 then .code else .block (depth - 1)
        i := i + 2
      else
        out := out.push (c, .prose)
        i := i + 1
    | .gap =>
      if c == ' ' || c == '\t' then
        out := out.push (c, .lit)
        i := i + 1
      else mode := .str
    | .str =>
      if c == '\\' then
        if i + 1 ≥ cs.size || chr (i + 1) == '\n' then
          out := out.push (c, .lit)
          mode := .gap
          i := i + 1
        else
          out := (out.push (c, .lit)).push (chr (i + 1), .strText)
          i := i + 2
      else if c == '"' then
        out := out.push (c, .lit)
        mode := .code
        i := i + 1
      else
        out := out.push (c, .strText)
        i := i + 1
    | .raw hashes =>
      if c == '"' && lexHashes cs (i + 1) ≥ hashes then
        out := out.push (c, .lit)
        for k in [0:hashes] do out := out.push (chr (i + 1 + k), .lit)
        mode := .code
        i := i + 1 + hashes
      else
        out := out.push (c, .strText)
        i := i + 1
    | .code =>
      if c == '-' && chr (i + 1) == '-' then
        out := (out.push (c, .lineOpen)).push ('-', .mark)
        mode := .line
        ident := false
        i := i + 2
      else if c == '/' && chr (i + 1) == '-' then
        out := (out.push (c, .blockOpen)).push ('-', .mark)
        mode := .block 1
        ident := false
        i := i + 2
        if chr i == '-' || chr i == '!' then
          out := out.push (chr i, .mark)
          i := i + 1
      else if c == '"' then
        out := out.push (c, .litOpen)
        mode := .str
        ident := false
        i := i + 1
      else if c == 'r' && !ident && cs[i + 1 + lexHashes cs (i + 1)]? == some '"' then
        let n := lexHashes cs (i + 1)
        out := out.push (c, .litOpen)
        for k in [0:n + 1] do out := out.push (chr (i + 1 + k), .lit)
        mode := .raw n
        i := i + 2 + n
      else if c == '\'' && !ident && !(i > 0 && chr (i - 1) == ']') then
        match lexCharLen cs i with
        | some n =>
          out := out.push (c, .litOpen)
          for k in [1:n] do out := out.push (chr (i + k), .lit)
          i := i + n
        | none =>
          out := out.push (c, .code)
          i := i + 1
      else
        out := out.push (c, .code)
        ident := if ident then Lean.isIdRest c || (c == '.' && Lean.isIdFirst (chr (i + 1)))
          else Lean.isIdFirst c
        i := i + 1
  return out

/-- A source's lines, each holding its characters of the classes `keep` admits, with one space where
a character of a class `opens` admits stands. -/
def lexView (text : String) (keep : LexCls → Bool) (opens : LexCls → Bool := fun _ => false) :
    Array String := Id.run do
  let mut lines : Array String := #[]
  let mut cur := ""
  for (c, k) in lexClasses text do
    if k == .newline then
      lines := lines.push cur
      cur := ""
    else if opens k then cur := cur.push ' '
    else if keep k then cur := cur.push c
  return lines.push cur

private def LexCls.comment : LexCls → Bool
  | .blockOpen | .lineOpen | .blockClose | .mark | .prose => true
  | .code | .litOpen | .lit | .strText | .newline => false

private def LexCls.literal : LexCls → Bool
  | .litOpen | .lit | .strText => true
  | .code | .blockOpen | .lineOpen | .blockClose | .mark | .prose | .newline => false

/-- The line with its string, raw string and character literals removed, its comments kept, lexed
alone, so the text of a string an earlier line opened reads as code. -/
def stripLiterals (l : String) : String :=
  if l.any fun c => c == '"' || c == '\'' || c == '\n' then (lexView l (!·.literal))[0]?.getD ""
  else l

/-- The line with its comments removed, its literals kept, lexed alone, so the text of a string an
earlier line opened reads as code. -/
def stripComments (l : String) : String :=
  if containsSub l "--" || containsSub l "/-" || l.any (· == '\n') then
    (lexView l (!·.comment))[0]?.getD ""
  else l

/-- The `## ` headings of a markdown document. -/
def docHeadings (text : String) : List String :=
  (text.splitOn "\n").filterMap fun l =>
    if l.startsWith "## " then some (l.drop 3).toString.trimAscii.toString else none

/-- A line-leading declaration's normalized modifiers and attributes, with whether it is
private; a lexical aid, not the Lean parser. -/
def declarationHead (line : String) : Bool × String := Id.run do
  if (line.toList.head?.map Char.isWhitespace).getD false then return (false, "")
  let mut hidden := false
  let mut brackets := 0
  let mut started := false
  let mut words : List String := []
  for part in (stripComments line).split Char.isWhitespace do
    let word := part.toString
    if word.isEmpty then continue
    if started then words := word :: words
    else if brackets > 0 || word.startsWith "@[" then
      for c in word.toList do
        if c == '[' then brackets := brackets + 1
        else if c == ']' then brackets := brackets - 1
    else if ["public", "private", "protected", "noncomputable", "unsafe",
        "partial", "meta"].contains word then
      hidden := hidden || word == "private"
    else
      started := true
      words := [word]
  return (hidden, String.intercalate " " words.reverse)

/-- Composed so no gate script's own source holds the banned word as a token. -/
def kwSorry : String := "sor" ++ "ry"

/-- Shared spelling for the totality convention. -/
def kwPartial : String := "par" ++ "tial"

/-- A banned keyword as a code token: word-delimited, outside literals and comments, its line lexed
alone. -/
def bannedWord (kw l : String) : Bool :=
  hasWord (stripComments (stripLiterals l)) kw
