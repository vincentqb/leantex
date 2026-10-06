module

import LeanTex.Core.PdfLex
import LeanTex.Core.PdfLexBoundary
import LeanTex.Core.PdfNameProof
import LeanTex.Core.PdfStringProof

/-! Ordinary readers share the byte rules and token scanners. Loop state
and individual scanner steps belong to the implementation and its proofs. -/

open LeanTex.Core.PdfLex

namespace Tests.PdfReaderInterface

example : Nat → Bool := isWs
example : Nat → Bool := isDelim
example : ByteArray → Nat → Nat := at?
example : ByteArray → Nat → Nat := skipWs
example : ByteArray → Nat → Option (Nat × Nat) := parseUInt
example : ByteArray → Nat → String → Option Nat := keywordAt
example : Nat → Option Nat := hexVal
example : ByteArray → Nat → Option Nat := scanLitString
example : ByteArray → Nat → Nat := scanHexEnd
example : ByteArray → Nat → String × Nat := parseName
example : Nat → Bool := numByte
example : ByteArray → Nat → String × Nat := scanNumber
example : ByteArray → Nat → Option (Nat × Nat) := tryRef
example : String → String := escapeName

example (s : String) (hne : s ≠ "")
    (hc : ∀ c ∈ s.toList, c.toNat < 256) :
    parseName ("/" ++ escapeName s).toUTF8 0 =
      (s, ("/" ++ escapeName s).toUTF8.size) :=
  parseName_escapeName_id s hne hc

example {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b (i+1) (cs ++ [41])) (hc : LiteralBody cs) :
    scanLitString b i = some (i+cs.length+2) :=
  scanLitString_exact h hc

example {b : ByteArray} {i : Nat} {cs : List Nat}
    (h : Span b i (cs ++ [62])) (hc : ∀ c ∈ cs, c ≠ 62 ∧ c ≠ 256) :
    scanHexEnd b i = i+cs.length :=
  scanHexEnd_exact h hc

example {b : ByteArray} {i : Nat}
    (h : at? b i = 32) (h' : at? b (i+1) = 32)
    (hw : isWs (at? b (i+2)) = false) (hc : at? b (i+2) ≠ 37)
    (hi : i+1 < b.size) : skipWs b i = i+2 :=
  skipWs_two_exact h h' hw hc hi

public def checks : Array (String × Bool) := #[
  ("comment and whitespace boundary", skipWs " % comment\n42".toUTF8 0 == 11),
  ("unsigned token boundary", parseUInt "42 rest".toUTF8 0 == some (42, 2)),
  ("keyword before delimiter", keywordAt "true/Name".toUTF8 0 "true" == some 4),
  ("keyword prefix refused", keywordAt "truest".toUTF8 0 "true" == none),
  ("name byte escape", parseName "/A#20B rest".toUTF8 0 == ("A B", 6)),
  ("invalid name escape retained", parseName "/A#zz ".toUTF8 0 == ("A#zz", 5)),
  ("literal nesting and escaped close", scanLitString "(a\\)b(c)) rest".toUTF8 0 == some 9),
  ("unclosed literal refused", scanLitString "(unclosed".toUTF8 0 == none),
  ("hex string boundary", scanHexEnd "0a>rest".toUTF8 0 == 2),
  ("raw real spelling", scanNumber "-.25 x".toUTF8 0 == ("-.25", 4)),
  ("reference before delimiter", tryRef " 7 R/Name".toUTF8 0 == some (7, 4)),
  ("reference marker prefix refused", tryRef " 7 Reader".toUTF8 0 == none),
  ("name escape spelling", escapeName "A B" == "A#20B")]

example : True := by
  fail_if_success have := UIntState
  fail_if_success have := LiteralState
  fail_if_success have := TextState
  fail_if_success have := skipStep
  fail_if_success have := uintStep
  fail_if_success have := keywordStep
  fail_if_success have := literalStep
  fail_if_success have := hexStep
  fail_if_success have := nameStep
  fail_if_success have := numberStep
  fail_if_success have := hexChar
  fail_if_success have := numberStep_stops
  fail_if_success have := uintStep_stops
  fail_if_success have := uint_numeric_stops
  fail_if_success have := literalBody_yields
  trivial

end Tests.PdfReaderInterface
