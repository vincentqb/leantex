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

/-- The word Pandoc's `str` reads ending at `i`, letters, digits and single dots, where it is no
longer than an abbreviation; `""` otherwise. -/
public def strBefore (cs : Array Char) (i : Nat) : String := Id.run do
  let mut j := i
  for _ in [0:8] do
    match j with
    | 0 => break
    | k + 1 =>
      if (cs[k]?.map fun c => CiteKey.isAlnum c || c == '.').getD false then j := k else break
  if i - j ≥ 8 then return ""
  let w := String.ofList (cs.extract j i).toList
  return if (w.splitOn "..").length > 1 then "" else w

/-- Whether spaces at `i` follow an abbreviation, which Pandoc's smart punctuation joins to the
word after them. -/
public def joinsAt (cs : Array Char) (i : Nat) : Bool := abbreviations.contains (strBefore cs i)

end LeanTex.Core.MdSmart
