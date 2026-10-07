/-
The line-scanner helpers both gate scripts share. precommit.lean and
owed.lean once each carried a copy of these; the copies were identical
except that the hook's banned-word scan did not strip `--` comments while
owed's hole counter did — one keyword, two behaviours, so a comment naming
the hole keyword failed a commit the ratchet would have passed. One module,
one behaviour: gates that must agree read the same definition.
-/

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Does `line` contain `word` delimited by non-word characters — the
`(^|[^[:alnum:]_])word([^[:alnum:]_]|$)` grep the shell hook used. -/
def hasWord (line word : String) : Bool :=
  (line.split (fun c => !isWordChar c)).any (·.toString == word)

def containsSub (line pat : String) : Bool :=
  (line.splitOn pat).length > 1

/-- The line with its string-literal content removed: a banned keyword is a
code token, and a string mentioning one — the math tables' command-name
entry for TeX's derivative symbol was the escape — is data, not a
declaration. Escapes are honoured. Two stated line-scanner limitations,
like `ioInCore`'s: a literal left open by a multi-line string strips to the
line's end, and a char literal holding a double quote reads as opening one. -/
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

/-- The line with any `--` comment stripped: a line comment, or a doc/block
comment's opening line. Blind spots, accepted rather than parsed around
(a line scanner has no comment state): a continuation line inside a block
comment still looks like code, and a string literal containing `--`
truncates the code after it — strip strings first when both apply. -/
def stripLineComment (l : String) : String :=
  (l.splitOn "--").headD l

/-- Normalize a line-leading declaration's modifiers and attributes for source
conventions, retaining whether it is private. Nested declarations do not
count. Attributes must finish on this line; comment and string state remain
the caller's responsibility. This is a lexical aid, not the Lean parser. -/
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

/-- Composed so no gate script's own staged diff contains the banned word
as a word-delimited token — the hook scans every .lean file, these
included. -/
def kwSorry : String := "sor" ++ "ry"

/-- A banned keyword as a code token: word-delimited, string content and
`--` comments aside. Strings are stripped first, so a literal containing
`--` does not hide the code after it. -/
def bannedWord (kw l : String) : Bool :=
  hasWord (stripLineComment (stripStrings l)) kw

/-- An import of the owed-theorem staging area: legal only inside it. The
gated library must never depend on a statement whose proof is open. -/
def importsObligations (l : String) : Bool :=
  ((stripLineComment l).trimAscii.toString).startsWith "import Obligations"

/-- The value of `-- <key>: <value>` when the line is one — the field form an
owed record is written in. Two gates read it: `scripts/owed.lean`, which is
the ratchet, and the scoreboard's obligations tier, which counts the same
records per owner. One definition, so the two cannot disagree about what a
record says; that is what this module is for. -/
def fieldOf (l key : String) : Option String :=
  let t := l.trimAscii.toString
  let pre := "-- " ++ key ++ ":"
  if t.startsWith pre then some (((t.drop pre.length).toString).trimAscii.toString)
  else none
