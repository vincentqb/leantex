module

import LeanTex.Core.Nfc
import LeanTex.Core.TextSymData

/-! TeX's accent and letter commands as characters, shared by the bibliography
and the elaborator so a name sets identically in both. -/

namespace LeanTex.Core.Bib

/-- Word commands that are one character. -/
public def charCommands : Array (String × String) :=
  #[("ss", "ß"), ("o", "ø"), ("O", "Ø"), ("ae", "æ"), ("AE", "Æ"),
    ("aa", "å"), ("AA", "Å"), ("l", "ł"), ("L", "Ł"), ("i", "ı")]

/-- The scalar NFC composes an accent's combining mark and a
base letter to, if any. -/
public def composeAccent (mark base : Char) : Option Char :=
  match (Nfc.normalize (String.ofList [base, mark])).toList with
  | [c] => if c != base then some c else none
  | _ => none

/-- TeX's accent `\<mark>` over a base letter, or the base letter when no
precomposed form exists. -/
public def accentOf (mark base : Char) : Char :=
  ((TextSymData.accents.lookup (String.ofList [mark])).bind (composeAccent · base)).getD base

end LeanTex.Core.Bib
