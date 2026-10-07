import LeanTex.Core.PdfStruct

/-! An ordinary consumer can use the structure producer's observable
projections without depending on allocation or traversal helpers. -/

namespace Tests.PdfInterfaces

open LeanTex.Core

example : Repr Pdf.StructKid := inferInstance
example : Repr Pdf.StructElem := inferInstance
example : Struct.Tree → Array Pdf.StructElem := Pdf.skeleton

example (tree : Struct.Tree) : Pdf.Unfilled (Pdf.skeleton tree) :=
  Pdf.skeleton_unfilled_contract tree

example (alternative : Ir.Alt) :
    (Pdf.altElem #[Pdf.rootElem] 0 0 alternative).back?.bind (·.alt) =
      match alternative with
      | .described text => some text
      | .undeclared | .decorative => none :=
  Pdf.altElem_root_alt_exact alternative

example (elements : Array Pdf.StructElem) (parent leaf : Nat) (alternative : Ir.Alt) :
    (Pdf.altElem elements parent leaf alternative).size =
      elements.size + match alternative with
      | .decorative => 0
      | .undeclared | .described _ => 1 :=
  Pdf.altElem_size_exact elements parent leaf alternative

example : True := by
  fail_if_success have := Pdf.structTypeOf
  fail_if_success have := Pdf.inPdf2Namespace
  fail_if_success have := Pdf.headingLevelOf
  fail_if_success have := Pdf.isHolder
  fail_if_success have := Pdf.elemOf
  fail_if_success have := Pdf.pushElem
  fail_if_success have := Pdf.addKid
  fail_if_success have := Pdf.bibEntryElems
  fail_if_success have := Pdf.skelList
  fail_if_success have := Pdf.skelStep
  trivial

end Tests.PdfInterfaces
