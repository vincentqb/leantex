module

import LeanTex.Core.Nfc
import LeanTex.Core.TextSymData

/-! The letters a `.bib` value spells with TeX's accent and letter commands,
shared by the bibliography's value reading (`Bib.text`) and the
elaborator's, so a name sets identically in a reference-list entry and in
the body. -/

namespace LeanTex.Core.Bib

/-- Word commands that are one character. -/
public def charCommands : Array (String × String) :=
  #[("ss", "ß"), ("o", "ø"), ("O", "Ø"), ("ae", "æ"), ("AE", "Æ"),
    ("aa", "å"), ("AA", "Å"), ("l", "ł"), ("L", "Ł"), ("i", "ı")]

/-- An accent's combining mark over a base letter, as the one scalar NFC
composes the pair to: the scalar lualatex sets under TU, whose composites
are each such a canonical composition (`textSymChecks` holds all of them).
A pair with no precomposed form has none. -/
public def composeAccent (mark base : Char) : Option Char :=
  match (Nfc.normalize (String.ofList [base, mark])).toList with
  | [c] => if c != base then some c else none
  | _ => none

/-- TeX's accent `\<mark>` over a base letter (`\'e`, `\"{o}`, `\c{c}`,
`\v{c}`), through TU's accent table and NFC, so a name renders identically
in text and in a bibliography entry. A pair with no precomposed form keeps
its base letter: a name never loses a character to an accent. -/
public def accentOf (mark base : Char) : Char :=
  ((TextSymData.accents.lookup (String.ofList [mark])).bind (composeAccent · base)).getD base

end LeanTex.Core.Bib
