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
  /-- The rest of a literal: its delimiters, escapes and gaps. -/
  | lit
  /-- A character a string literal's value holds: an escape's character, not its backslash. -/
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
  /-- A line break. -/
  | newline
  deriving BEq, Inhabited, Repr

/-- A character that continues an identifier, so a quote after it is a prime. -/
def lexIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- How many `#` stand at `cs[k]` onward. -/
def lexHashes (cs : Array Char) (k : Nat) : Nat := Id.run do
  let mut n := 0
  for j in [k:cs.size] do
    if cs[j]? == some '#' then n := n + 1 else break
  return n

/-- The length of the character literal opening at `i`, none where the quote is a prime or opens no
literal. -/
def lexCharLen (cs : Array Char) (i : Nat) : Option Nat :=
  if i > 0 && lexIdentChar (cs[i - 1]?.getD ' ') then none
  else match cs[i + 1]? with
    | some '\\' =>
      (List.range 10).findSome? fun k =>
        if k ≥ 1 && cs[i + 2 + k]? == some '\'' then some (k + 3) else none
    | some c => if c != '\n' && cs[i + 2]? == some '\'' then some 3 else none
    | none => none

/-- Every character of a Lean source classed: nested block comments with their doc markers, line
comments, strings with escapes and gaps, raw strings, and character literals apart from primes. -/
def lexClasses (text : String) : Array (Char × LexCls) := Id.run do
  let cs := text.toList.toArray
  let chr (k : Nat) : Char := cs[k]?.getD ' '
  let mut out : Array (Char × LexCls) := #[]
  -- 0 code, 1 line comment, 2 block comment, 3 string, 4 raw string
  let mut mode := 0
  let mut depth := 0
  let mut hashes := 0
  let mut i := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := chr i
    if c == '\n' then
      out := out.push (c, .newline)
      if mode == 1 then mode := 0
      i := i + 1
      continue
    match mode with
    | 1 => out := out.push (c, .prose); i := i + 1
    | 2 =>
      if c == '/' && chr (i + 1) == '-' then
        depth := depth + 1
        out := (out.push (c, .mark)).push ('-', .mark)
        i := i + 2
      else if c == '-' && chr (i + 1) == '/' then
        depth := depth - 1
        out := (out.push (c, .mark)).push ('/', if depth == 0 then .blockClose else .mark)
        i := i + 2
        if depth == 0 then mode := 0
      else
        out := out.push (c, .prose)
        i := i + 1
    | 3 =>
      if c == '\\' then
        if chr (i + 1) == '\n' then
          out := out.push (c, .lit)
          i := i + 1
        else
          out := (out.push (c, .lit)).push (chr (i + 1), .strText)
          i := i + 2
      else if c == '"' then
        out := out.push (c, .lit)
        mode := 0
        i := i + 1
      else
        out := out.push (c, .strText)
        i := i + 1
    | 4 =>
      if c == '"' && lexHashes cs (i + 1) ≥ hashes then
        out := out.push (c, .lit)
        for k in [0:hashes] do out := out.push (chr (i + 1 + k), .lit)
        mode := 0
        i := i + 1 + hashes
      else
        out := out.push (c, .strText)
        i := i + 1
    | _ =>
      if c == '-' && chr (i + 1) == '-' then
        out := (out.push (c, .lineOpen)).push ('-', .mark)
        mode := 1
        i := i + 2
      else if c == '/' && chr (i + 1) == '-' then
        out := (out.push (c, .blockOpen)).push ('-', .mark)
        mode := 2
        depth := 1
        i := i + 2
        if chr i == '-' || chr i == '!' then
          out := out.push (chr i, .mark)
          i := i + 1
      else if c == '"' then
        out := out.push (c, .litOpen)
        mode := 3
        i := i + 1
      else if c == 'r' && !(i > 0 && lexIdentChar (chr (i - 1))) &&
          cs[i + 1 + lexHashes cs (i + 1)]? == some '"' then
        hashes := lexHashes cs (i + 1)
        out := out.push (c, .litOpen)
        for k in [0:hashes + 1] do out := out.push (chr (i + 1 + k), .lit)
        mode := 4
        i := i + 2 + hashes
      else if c == '\'' then
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

/-- Whether a class is a comment's. -/
def LexCls.comment : LexCls → Bool
  | .blockOpen | .lineOpen | .blockClose | .mark | .prose => true
  | .code | .litOpen | .lit | .strText | .newline => false

/-- Whether a class is a literal's. -/
def LexCls.literal : LexCls → Bool
  | .litOpen | .lit | .strText => true
  | .code | .blockOpen | .lineOpen | .blockClose | .mark | .prose | .newline => false

/-- The line with its string and character literals removed, its comments kept, as one line lexes
alone. -/
def stripStrings (l : String) : String :=
  (lexView l (!·.literal))[0]?.getD ""

/-- The line with its comments removed, its literals kept, as one line lexes alone. -/
def stripLineComment (l : String) : String :=
  (lexView l (!·.comment))[0]?.getD ""

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
  for part in (stripLineComment line).split Char.isWhitespace do
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

/-- A banned keyword as a code token: word-delimited, outside strings and `--`
comments. -/
def bannedWord (kw l : String) : Bool :=
  hasWord (stripLineComment (stripStrings l)) kw
