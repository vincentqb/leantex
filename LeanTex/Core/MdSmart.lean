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
public def longest : Nat := abbreviations.foldl (fun m a => max m a.length) 0

/-- A character Pandoc's `str` reads a word of: a letter or digit of any script, or a dot. -/
def wordChar (c : Char) : Bool := CiteKey.isAlnum c || c == '.'

/-- The word Pandoc's `str` reads ending at `i`, where it is no longer than an abbreviation; `""`
otherwise. Its letters, digits and dots, but a dot before a dot, which no `str` holds: of a run of
dots only an ellipsis's remainder's last one opens the word after it, as `str` resumes there. -/
public def strBefore (cs : Array Char) (i : Nat) : String := Id.run do
  let mut j := i
  for _ in [0:longest + 1] do
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
  if i - start > longest then return ""
  return String.ofList (cs.extract start i).toList

/-- Whether spaces at `i` follow an abbreviation, which Pandoc's smart punctuation joins to the
word after them. -/
public def joinsAt (cs : Array Char) (i : Nat) : Bool := abbreviations.contains (strBefore cs i)

/-- Whether a citation key Pandoc's `citeKey` reads opens at `j`: `@` or `-@` before a key's first
character. -/
def keyAt (cs : Array Char) (j : Nat) : Bool :=
  let k := if cs[j]? == some '-' then j + 1 else j
  cs[k]? == some '@' &&
    (cs[k + 1]?.any fun c => CiteKey.isAlnum c || c == '_' || c == '*' || c == '{')

/-- Whether a citation's spelling opens at `j`, which Pandoc's smart punctuation joins nothing
before: an author's key, or a bracket holding a key after no word before its close. -/
public def citesAt (cs : Array Char) (j : Nat) : Bool := Id.run do
  if keyAt cs j then return true
  unless cs[j]? == some '[' do return false
  for k in [j + 1:cs.size] do
    match cs[k]? with
    | some ']' | some '[' | none => return false
    | some _ =>
      if keyAt cs k && !(cs[k - 1]?.any CiteKey.isAlnum) then return true
  return false

end LeanTex.Core.MdSmart
