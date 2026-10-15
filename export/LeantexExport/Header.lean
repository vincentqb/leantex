/-! A Lean file's header as the exporter reads it: the modules it imports. -/

namespace LeantexExport

/-- Whether a character is white space between a header's words. -/
def isWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

private def at? (src : Array Char) (i : Nat) (c : Char) : Bool := src[i]? == some c

/-- Characters as a string, through the one spelling every Lean the exporter builds on shares. -/
def ofChars (cs : List Char) : String := cs.foldl String.push ""

/-- The index of the line end at or after `i`, the source's end when no line ends. -/
private def lineEnd (src : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:src.size] do
    if at? src j '\n' then return j
    j := j + 1
  return src.size

/-- Past the end of a block comment whose body starts at `i`, nested comments read; `none` when it
never closes. -/
private def blockEnd (src : Array Char) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  let mut depth := 1
  for _ in [0:src.size] do
    if j ≥ src.size then return none
    if at? src j '/' && at? src (j + 1) '-' then
      depth := depth + 1
      j := j + 2
    else if at? src j '-' && at? src (j + 1) '/' then
      depth := depth - 1
      j := j + 2
      if depth == 0 then return some j
    else j := j + 1
  return none

/-- The modules a Lean file's header imports, in order; `none` for a `prelude` file, whose
statements elaborate without `Init`. -/
def imports? (text : String) : Option (Array String) := Id.run do
  let src := text.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  let mut expectModule := false
  for _ in [0:src.size + 1] do
    if i ≥ src.size then break
    let c := src.getD i ' '
    if isWhite c then i := i + 1
    else if c == '-' && at? src (i + 1) '-' then i := lineEnd src i
    else if c == '/' && at? src (i + 1) '-' && !at? src (i + 2) '!' && !at? src (i + 2) '-' then
      i := (blockEnd src (i + 2)).getD src.size
    else
      let mut j := i
      for _ in [i:src.size] do
        if isWhite (src.getD j ' ') then break
        j := j + 1
      let word := ofChars (src.extract i j).toList
      i := j
      if expectModule then
        if word != "all" then
          out := out.push word
          expectModule := false
      else if word == "prelude" then return none
      else if word == "import" then expectModule := true
      else if !["module", "public", "private", "meta"].contains word then break
  return some out

end LeantexExport
