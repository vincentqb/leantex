module

import LeanTex.Core.CiteKey

/-! Pandoc's smart punctuation's abbreviations, which the markdown reader joins to the word after
them and the markdown twin keeps apart where the document did not. -/

namespace LeanTex.Core.MdSmart

/-- Pandoc's default abbreviations (its data file `abbreviations`), each joined by its smart
punctuation to the word after it with a non-breaking space. -/
public def abbreviations : List String :=
  ["aet.", "aetat.", "al.", "Apr.", "Aug.", "bk.", "Bros.", "c.", "Capt.", "cf.", "ch.", "chap.",
   "chs.", "Co.", "col.", "Corp.", "cp.", "d.", "Dec.", "Dr.", "e.g.", "ed.", "eds.", "esp.", "f.",
   "fasc.", "Feb.", "ff.", "fig.", "fl.", "fol.", "fols.", "Fr.", "Gen.", "Gov.", "Hon.", "i.e.",
   "ill.", "Inc.", "incl.", "Jan.", "Jr.", "Jul.", "Jun.", "Ltd.", "M.A.", "M.D.", "Mar.", "Mr.",
   "Mrs.", "Ms.", "n.", "n.b.", "nn.", "No.", "Nov.", "Oct.", "p.", "Ph.D.", "pp.", "Pres.", "Prof.",
   "pt.", "q.v.", "Rep.", "Rev.", "s.v.", "s.vv.", "saec.", "sec.", "Sen.", "Sep.", "Sept.", "Sgt.",
   "Sr.", "St.", "univ.", "viz.", "vol.", "vs."]

/-- The longest abbreviation's length, past which no word is one. -/
public def longest (_ : Unit) : Nat := abbreviations.foldl (fun m a => max m a.length) 0

/-- A character Pandoc's `str` reads a word of: a letter or digit of any script, or a dot. -/
def wordChar (c : Char) : Bool := CiteKey.isAlnum c || c == '.'

/-- The word Pandoc's `str` reads ending at `i`, which a run of dots opens past its ellipses, where
it is no longer than an abbreviation, else `""`. -/
public def strBefore (cs : Array Char) (i : Nat) : String := Id.run do
  let bound := longest ()
  let mut j := i
  for _ in [0:bound + 1] do
    match j with
    | 0 => break
    | k + 1 => if (cs[k]?.map wordChar).getD false then j := k else break
  let mut pair : Option Nat := none
  for d in [0:i - j] do
    let k := i - 1 - d
    if k ≥ 1 && cs[k]? == some '.' && cs[k - 1]? == some '.' then
      pair := some k
      break
  let start ← match pair with
    | none => pure j
    | some k => do
      let mut e := k + 1
      for _ in [k + 1:i] do
        if cs[e]? == some '.' then e := e + 1 else break
      let mut s := k
      for _ in [0:k] do
        match s with
        | 0 => break
        | m + 1 => if cs[m]? == some '.' then s := m else break
      pure (if (e - s) % 3 == 0 then e else e - 1)
  if i - start > bound then return ""
  return String.ofList (cs.extract start i).toList

/-- Whether spaces at `i` follow an abbreviation, which Pandoc's smart punctuation joins to the
word after them. -/
public def joinsAt (cs : Array Char) (i : Nat) : Bool := abbreviations.contains (strBefore cs i)

/-- Whether a citation key Pandoc's `citeKey` reads opens at `j`: `@` or `-@` before a key's first
character or a brace closing with no white space inside. -/
def keyAt (cs : Array Char) (j : Nat) : Bool := Id.run do
  let k := if cs[j]? == some '-' then j + 1 else j
  unless cs[k]? == some '@' do return false
  match cs[k + 1]? with
  | some '{' =>
    for m in [k + 2:cs.size] do
      match cs[m]? with
      | some '}' => return true
      | some d => if d == ' ' || d == '\t' || d == '\n' then return false
      | none => return false
    return false
  | some d => return CiteKey.isAlnum d || d == '_' || d == '*'
  | none => return false

/-- Whether `j` of written text opens an author's key or a bracket holding a key at its start or
after white space before its close, an escaped character no key. -/
public def citesAt (cs : Array Char) (j : Nat) : Bool := Id.run do
  if keyAt cs j then return true
  unless cs[j]? == some '[' do return false
  let mut k := j + 1
  for _ in [j + 1:cs.size] do
    match cs[k]? with
    | some ']' | some '[' | none => return false
    | some '\\' => k := k + 2
    | some _ =>
      let opens := k == j + 1 || (cs[k - 1]?.any fun d => d == ' ' || d == '\t' || d == '\n')
      if opens && keyAt cs k then return true
      k := k + 1
  return false

end LeanTex.Core.MdSmart
