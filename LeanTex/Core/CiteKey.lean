module

import LeanTex.Core.Nfc

/-! Pandoc's citation-key grammar [Pandoc].

Bibliography: [references.bib](../../docs/references.bib) -/

namespace LeanTex.Core.CiteKey

/-- A letter or a number, beyond ASCII by Unicode's letter and number categories as Haskell's
`isAlphaNum` reads them: what a citation key is spelled in, and what keeps an `@` inside a word text. -/
public def isAlnum (c : Char) : Bool :=
  c.isAlphanum || (c.toNat > 127 && (Nfc.isLetter c || Nfc.isNumber c))

/-- A key's regular character: a letter, a digit or `_`. -/
public def regular (c : Char) : Bool := isAlnum c || c == '_'

/-- Pandoc's internal punctuation of a citation key: kept only before a regular character. -/
public def internal (c : Char) : Bool := ":.#$%&-+?<>~/".any (· == c)

/-- The length of the bare key Pandoc's `simpleCiteIdentifier` reads at the head of `cs`, zero
where none starts there; `*` opens one, the citation of every entry. -/
public def bareLen : List Char → Nat
  | [] => 0
  | c :: rest => if regular c || c == '*' then 1 + restLen rest else 0
where
  restLen : List Char → Nat
    | [] => 0
    | c :: rest =>
      if regular c then 1 + restLen rest
      else match rest with
        | d :: _ =>
          if (internal c && regular d) || ((c == ':' || c == '/') && d == '/') then 1 + restLen rest
          else 0
        | [] => 0

/-- How a key is written after its `@`: bare where Pandoc reads it whole and nothing after it
would lengthen it, else braced; `none` where no spelling reads back. -/
public def spelling? (key : String) (next : Option Char) : Option String :=
  let cs := key.toList
  let extends_ := next.any fun d => regular d || internal d
  if !cs.isEmpty && bareLen cs == cs.length && !extends_ then some ("@" ++ key)
  else if !cs.isEmpty && !cs.any (fun c => c == ' ' || c == '\t' || c == '\n' || c == '{' || c == '}')
  then some ("@{" ++ key ++ "}")
  else none

end LeanTex.Core.CiteKey
