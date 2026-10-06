module

import LeanTex.Core.PdfLex
import LeanTex.Core.PdfLexBoundary
import LeanTex.Core.PdfNameProof
import LeanTex.Core.PdfStringProof
import LeanTex.Core.PdfStreamSpelling
import LeanTex.Core.PdfFooter
import LeanTex.Core.PdfXref
import LeanTex.Core.PdfXrefSpelling
import LeanTex.Core.PdfRead

/-! Ordinary readers share the byte rules and token scanners. Loop state
and individual scanner steps belong to the implementation and its proofs. -/

open LeanTex.Core.PdfLex
open LeanTex.Core.PdfRead (Obj parseVal parseVal_render_id parseVal_render_span_exact
  parseVal_spelling_span_exact readStartxref readStartxref_footer_exact)

open LeanTex.Core.Pdf

open LeanTex.Core

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

example : ByteArray → Except String Nat := readStartxref
example : UInt8 → Nat → Nat → ByteArray := Xref.row
example : Xref.Entry → ByteArray := Xref.Entry.bytes
example : Array Xref.Entry → ByteArray := Xref.encode

example (offset gen : Nat) :
    (Xref.Entry.direct offset gen).fields = (1, offset, gen) := rfl

example (e : Xref.Entry) :
    e.Fits ↔ e.fields.2.1 < 256^4 ∧ e.fields.2.2 < 256^2 := Iff.rfl

example (kind : UInt8) (first second : Nat)
    (hf : first < 256^4) (hs : second < 256^2) (pre post : ByteArray) :
    LeanTex.Core.Binary.readNatBE 4 (pre ++ Xref.row kind first second ++ post)
      (pre.size+1) = some first :=
  (Xref.row_fields_exact kind first second hf hs pre post).2.1

example (pre : ByteArray) (offset : Nat) (h : offset < 256^4) :
    readStartxref (pre ++ (s!"startxref\n{offset}\n%%EOF\n").toUTF8) = .ok offset :=
  readStartxref_footer_exact pre offset h

example (count info : Nat) (idA idB : UInt64) (filtered : Bool) (len : Nat) :
    (xrefStreamDict count info idA idB filtered len).Representable :=
  xrefStreamDict_representable_exact count info idA idB filtered len

example (count info : Nat) (idA idB : UInt64) (filtered : Bool) (len : Nat) :
    (xrefStreamDict count info idA idB filtered len).get? "Length" = some (.int len) :=
  (xrefStreamDict_fields_exact count info idA idB filtered len).1

example : Obj → Option LeanTex.Core.Dim.Sp := PdfRead.Obj.sp?
example : Obj → ByteArray → Except String ByteArray := PdfRead.decodeStream
example : ByteArray → Except String PdfRead.Xref := PdfRead.readXref
example : ByteArray → Nat → Except String (Array (Nat × Nat)) :=
  PdfRead.readObjectStreamHeader
example : ByteArray → PdfRead.Xref →
    Except String { es : Array PdfRead.Entry // PdfRead.entriesWf es } := PdfRead.objectsOf
example : ByteArray → Except String { es : Array PdfRead.Entry // PdfRead.entriesWf es } :=
  PdfRead.objects
example : ByteArray → Except String Obj := PdfRead.trailer
example : ByteArray → PdfRead.PageSelection → Except String Nat :=
  fun b page => PdfRead.pageNumber b page
example : ByteArray → PdfRead.PageSelection → Except String { f : PdfRead.Form // f.wf } :=
  fun b page => PdfRead.readForm b page

example (f : PdfRead.Form) : f.w = f.x1 - f.x0 := rfl
example (f : PdfRead.Form) : f.h = f.y1 - f.y0 := rfl
example (e : PdfRead.Entry) : e.wf = (e.header == e.num) := rfl

example (es : { es : Array PdfRead.Entry // PdfRead.entriesWf es }) :
    ∀ e ∈ es.val, e.header = e.num := PdfRead.objects_num_covers es

example (f : { f : PdfRead.Form // f.wf }) : f.val.wf = true :=
  PdfRead.resources_closed f

example (es : Array Xref.Entry) (i : Nat) (e : Xref.Entry)
    (hi : es[i]? = some e) (he : e.Fits) (pre post : ByteArray) :
    PdfRead.readXrefRow (pre ++ Xref.encode es ++ post) (pre.size + 7*i) 1 4 2 =
      PdfRead.xrefEntryLocation e :=
  PdfRead.readXrefRow_encode_exact es i e hi he pre post

example (data : ByteArray) (w0 w1 w2 start count row0 : Nat) (x : PdfRead.Xref) :
    (PdfRead.readXrefSubsection data w0 w1 w2 start count row0 x).2 = row0 + count :=
  PdfRead.readXrefSubsection_row_exact data w0 w1 w2 start count row0 x

example (b : ByteArray) (locs : Std.HashMap Nat PdfRead.Loc)
    (num off : Nat) (dict : Obj) (hd : dict.Representable) (raw : ByteArray)
    (hs : Span b off (octets (s!"{num} 0 obj\n").toUTF8 ++
      octets dict.render ++ octets "\nstream\n".toUTF8 ++ octets raw ++
      octets "\nendstream\nendobj\n".toUTF8))
    (hl : dict.get? "Length" = some (.int raw.size))
    (hn : locs.get? num = some (.direct off)) :
    ({num, header := num, loc := .direct off, val := dict, stream := some raw} : PdfRead.Entry).Reads b locs
      (some (off + (s!"{num} 0 obj\n").toUTF8.size + dict.render.size)) :=
  PdfRead.Entry.reads_stream_exact b locs num off dict hd raw hs hl hn

private def sameResult (actual expected : Except String (Obj × Nat)) : Bool :=
  match actual, expected with
  | .ok a, .ok e => a == e
  | .error a, .error e => a == e
  | _, _ => false

private def footerIs (source : String) (expected : Nat) : Bool :=
  match readStartxref source.toUTF8 with
  | .ok actual => actual == expected
  | .error _ => false

private def footerRefuses (source message : String) : Bool :=
  match readStartxref source.toUTF8 with
  | .error actual => actual == message
  | .ok _ => false

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
    (.error "truncated PDF: a hex string never closes")),
  ("footer decimal offset", footerIs "%PDF-2.0\nstartxref\n257\n%%EOF\n" 257),
  ("footer last revision", footerIs "startxref\n1\n%%EOF\nstartxref\n23\n%%EOF\n" 23),
  ("footer missing offset refused", footerRefuses "startxref\n%%EOF\n"
    "malformed PDF: unreadable startxref offset"),
  ("footer keyword prefix refused", footerRefuses "startxrefs\n1\n%%EOF\n"
    "malformed PDF: no startxref"),
  ("xref direct row spelling", (Xref.Entry.direct 258 3).bytes ==
    ([1,0,0,1,2,0,3] : List UInt8).toByteArray),
  ("xref compressed row spelling", (Xref.Entry.compressed 4 5).bytes ==
    ([2,0,0,0,4,0,5] : List UInt8).toByteArray),
  ("xref out-of-domain fields retain truncation", Xref.row 1 (256^4+2) (256^2+3) ==
    ([1,0,0,0,2,0,3] : List UInt8).toByteArray),
  ("xref row array order", Xref.encode #[.free 0 65535, .direct 12 0] ==
    ([0,0,0,0,0,255,255,1,0,0,0,12,0,0] : List UInt8).toByteArray),
  ("reader unfiltered stream retained", match PdfRead.decodeStream (.dict #[]) "raw".toUTF8 with
    | .ok actual => actual == "raw".toUTF8
    | .error _ => false),
  ("reader unsupported filter names refusal", match PdfRead.decodeStream
      (.dict #[("Filter", .name "Unknown")]) ByteArray.empty with
    | .error message => message == "PDF stream filter /Unknown is not supported"
    | .ok _ => false),
  ("reader object stream header order", match PdfRead.readObjectStreamHeader "7 0 3 5 rest".toUTF8 2 with
    | .ok actual => actual == #[(7,0),(3,5)]
    | .error _ => false),
  ("reader truncated object stream header refused", match PdfRead.readObjectStreamHeader "7".toUTF8 1 with
    | .error message => message == "malformed PDF: unreadable object stream header"
    | .ok _ => false),
  ("reader encoded direct row", match PdfRead.readXrefRow (Xref.Entry.direct 258 3).bytes 0 1 4 2 with
    | some (.direct off) => off == 258
    | _ => false),
  ("reader encoded compressed row", match PdfRead.readXrefRow (Xref.Entry.compressed 4 5).bytes 0 1 4 2 with
    | some (.inStm stm idx) => stm == 4 && idx == 5
    | _ => false),
  ("reader free row has no location", (PdfRead.readXrefRow (Xref.Entry.free 0 65535).bytes 0 1 4 2).isNone),
  ("reader truncated row has no location", (PdfRead.readXrefRow ByteArray.empty 0 1 4 2).isNone),
  ("reader malformed header refused", match PdfRead.objects ByteArray.empty with
    | .error message => message == "not a PDF file (no %PDF header)"
    | .ok _ => false)]

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
  fail_if_success have := LeanTex.Core.PdfRead.scanStep
  fail_if_success have := LeanTex.Core.PdfRead.findStartxref
  fail_if_success have := LeanTex.Core.PdfRead.footer_number
  fail_if_success have := Xref.encodeList
  fail_if_success have := Xref.encodeList_bytes
  fail_if_success have := LeanTex.Core.Pdf.HexChars
  fail_if_success have := LeanTex.Core.Pdf.hex16_chars
  fail_if_success have := PdfRead.Reader
  fail_if_success have := PdfRead.parseIndirectAt
  fail_if_success have := PdfRead.beField
  fail_if_success have := PdfRead.Xref.add
  fail_if_success have := PdfRead.Xref.seen
  fail_if_success have := PdfRead.readClassicSection
  fail_if_success have := PdfRead.readStreamSection
  fail_if_success have := PdfRead.readXrefFrom
  fail_if_success have := PdfRead.ObjectScan
  fail_if_success have := PdfRead.Page
  fail_if_success have := PdfRead.selectPage
  fail_if_success have := PdfRead.SerSt
  fail_if_success have := PdfRead.serObj
  fail_if_success have := PdfRead.chunksWf
  trivial

end Tests.PdfReaderInterface
