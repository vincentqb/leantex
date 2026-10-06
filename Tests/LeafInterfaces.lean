module

import LeanTex.Core.Color
import LeanTex.Core.Locale
import LeanTex.Core.Utf8
import LeanTex.Core.ListingHighlight
import LeanTex.Cli.PicCache

/-! Ordinary consumers can name the value types and contracts; lexical
traversal helpers remain implementation details. Serialization bodies needed
by downstream algebraic proofs are explicitly exposed. -/

open LeanTex.Core LeanTex.Cli

example : Ir.Color → String := Ir.Color.css
example (c : Ir.Color) :
    c.css = "#" ++ Ir.Color.hexByte c.r false ++ Ir.Color.hexByte c.g false ++
      Ir.Color.hexByte c.b false := by rfl
example : String → String := Locale.babelTagOf
example : ByteArray → Option Utf8.Err := Utf8.validate
example : Utf8.Err → String → Diag := Utf8.Err.toDiag
example : ListingHighlight.Language → Array String → Array (Array ListingHighlight.Token) :=
  ListingHighlight.tokenize
example (tokens : Array ListingHighlight.Token) :
    ListingHighlight.lineText tokens = tokens.foldl (fun s t => s ++ t.text) "" := by rfl
example (drawn : Bool) (refusal : Option String) :
    PicCache.step drawn refusal = .run ↔ drawn = false ∧ refusal = none :=
  PicCache.step_cold_exact drawn refusal

example : True := by
  fail_if_success have := Utf8.seq
  fail_if_success have := Utf8.validate.go
  fail_if_success have := ListingHighlight.tokenAt
  fail_if_success have := ListingHighlight.scanWhile
  trivial
