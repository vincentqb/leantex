module

import LeanTex.Core.PdfLex
import LeanTex.Core.PdfLexBoundary
import LeanTex.Core.PdfNameProof
import LeanTex.Core.PdfStringProof
import LeanTex.Core.PdfStreamSpelling

/-! Ordinary readers share the byte rules and token scanners. Loop state
and individual scanner steps belong to the implementation and its proofs. -/

open LeanTex.Core.PdfLex
open LeanTex.Core.PdfRead (Obj parseVal parseVal_render_id parseVal_render_span_exact
  parseVal_spelling_span_exact)

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

example : ByteArray → Nat → Except String (Obj × Nat) := parseVal
example : Obj → ByteArray := Obj.render
example : ByteArray → Obj → ByteArray := Obj.renderInto
example : ByteArray → List Obj → ByteArray := Obj.renderList
example : ByteArray → List (String × Obj) → ByteArray := Obj.renderEntries
example : Array (String × Obj) → ByteArray := Obj.paddedDict

example (n : Int) : (Obj.int n).int? = some n := rfl
example : (Obj.null).get? "absent" = none := rfl

example (pre : ByteArray) (o : Obj) : o.renderInto pre = pre ++ o.render :=
  Obj.renderInto_exact pre o

example (o : Obj) (h : o.Representable) :
    parseVal o.render 0 = .ok (o, o.render.size) :=
  parseVal_render_id o h

example {b : ByteArray} {i : Nat} (o : Obj) (h : o.Representable)
    (hs : Span b i (octets o.render))
    (he : LeanTex.Core.PdfRead.ObjReader.Stop b (i+o.render.size)) :
    parseVal b i = .ok (o, i+o.render.size) :=
  parseVal_render_span_exact o h hs he (h.start hs he.boundary he.marker).skip

example {b raw : ByteArray} {i p : Nat} (o : Obj) (h : o.Spelling raw)
    (hs : Span b i (octets raw))
    (he : LeanTex.Core.PdfRead.ObjReader.Stop b (i+raw.size))
    (hw : skipWs b p = i) : parseVal b p = .ok (o, i+raw.size) :=
  parseVal_spelling_span_exact o h hs he hw

private def sameResult (actual expected : Except String (Obj × Nat)) : Bool :=
  match actual, expected with
  | .ok a, .ok e => a == e
  | .error a, .error e => a == e
  | _, _ => false

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
  ("name escape spelling", escapeName "A B" == "A#20B"),
  ("object null boundary", sameResult (parseVal "null/Next".toUTF8 0) (.ok (.null, 4))),
  ("object raw real spelling", sameResult (parseVal "1.x".toUTF8 0) (.ok (.real "1.", 2))),
  ("object reference boundary", sameResult (parseVal "17 2 R/Next".toUTF8 0) (.ok (.ref 17 2, 6))),
  ("object duplicate dictionary keys", Id.run do
    let b := "<< /A [1 (x) /N] /A 2 >>".toUTF8
    return sameResult (parseVal b 0) (.ok (.dict #[
      ("A", .arr #[.int 1, .str "(x)".toUTF8, .name "N"]), ("A", .int 2)], b.size))),
  ("object missing dictionary value", sameResult (parseVal "<< /A >>".toUTF8 0)
    (.error "malformed PDF: dictionary key /A has no value")),
  ("object non-name dictionary key", sameResult (parseVal "<< 1 2 >>".toUTF8 0)
    (.error "malformed PDF: a dictionary key is not a name")),
  ("object unmatched array close", sameResult (parseVal "]".toUTF8 0)
    (.error "malformed PDF: unbalanced ']'")),
  ("object truncated string", sameResult (parseVal "(x".toUTF8 0)
    (.error "truncated PDF: a string never closes")),
  ("object truncated hex string", sameResult (parseVal "<aa".toUTF8 0)
    (.error "truncated PDF: a hex string never closes"))]

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
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.Frame
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.Token
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.State
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.readToken
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.accept
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.step
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.Runs
  fail_if_success have := LeanTex.Core.PdfRead.ObjReader.Reads
  fail_if_success have := Obj.Representable.reads
  fail_if_success have := Obj.arrayBody
  fail_if_success have := Obj.dictBody
  fail_if_success have := Obj.paddedDict_octets_exact
  trivial

end Tests.PdfReaderInterface
