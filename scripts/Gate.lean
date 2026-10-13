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

/-- The line with string-literal content removed, escapes honoured; a literal a multi-line
string leaves open strips to the line's end, and a char literal holding a double quote
reads as opening one. -/
def stripStrings (l : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut esc := false
  for c in l.toList do
    if inStr then
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then
      inStr := true
    else
      out := out.push c
  return out

/-- The line with any `--` comment stripped; a block comment's continuation lines still
read as code, and a string holding `--` truncates the code after it. -/
def stripLineComment (l : String) : String :=
  (l.splitOn "--").headD l

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
