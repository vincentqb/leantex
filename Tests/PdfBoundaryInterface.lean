module

import LeanTex.Core.PdfEncoding
import LeanTex.Core.PdfFooter

/-! The encoding boundary exports its input check and universal contracts.
Ordinary clients do not depend on recursive scanner or container helpers. -/

open LeanTex.Core.PdfRead

namespace Tests.PdfBoundaryInterface

example : Obj → Bool := Obj.encodable
example : ByteArray → Except String Nat := readStartxref

example (o : Obj) (h : o.encodable = true) : o.Representable :=
  o.encodable_contract h

example (o : Obj) (h : o.encodable = true) :
    parseVal o.render 0 = .ok (o, o.render.size) :=
  o.encodable_render_exact h

example (pre : ByteArray) (offset : Nat) (h : offset < 2^64) :
    readStartxref (pre ++ (s!"startxref\n{offset}\n%%EOF\n").toUTF8) = .ok offset :=
  readStartxref_footer_exact pre offset h

example : True := by
  fail_if_success have := Obj.stringEncodable
  fail_if_success have := Obj.stringEncodable_contract
  fail_if_success have := Obj.encodableList
  fail_if_success have := Obj.encodableList_contract
  fail_if_success have := Obj.encodableEntries
  fail_if_success have := Obj.encodableEntries_contract
  fail_if_success have := LeanTex.Core.PdfRead.literalTail
  fail_if_success have := LeanTex.Core.PdfRead.hexTail
  fail_if_success have := LeanTex.Core.PdfRead.scanStep
  fail_if_success have := LeanTex.Core.PdfRead.findStartxref
  trivial

end Tests.PdfBoundaryInterface
