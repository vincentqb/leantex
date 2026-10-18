module

namespace LeanTex.Core.Ir

/-- The token grammar a listing's declared language must fit: an ASCII
lowercase letter, then lowercase letters, digits, `+`, `#`, `-`, `.`. -/
public def listingLangOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    c.isLower && rest.all fun d =>
      d.isLower || d.isDigit || d == '+' || d == '#' || d == '-' || d == '.'

/-- A listing language the grammar admits. -/
public abbrev ListingLang := { s : String // listingLangOk s = true }

/-- An author's language spelling, trimmed and ASCII-lowercased, admitted only
when the grammar does. -/
public def listingLang? (raw : String) : Option ListingLang :=
  let s := raw.trimAscii.toString.toLower
  if h : listingLangOk s = true then some ⟨s, h⟩ else none

end LeanTex.Core.Ir
