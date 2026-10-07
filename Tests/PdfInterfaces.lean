import LeanTex.Core.PdfStruct
import LeanTex.Core.PdfRowRecovery

/-! Ordinary consumers use typed content operations and structure
projections without depending on rendering, allocation, or traversal helpers. -/

namespace Tests.PdfInterfaces

open LeanTex.Core

example : Repr Pdf.PathOp := inferInstance
example : BEq Pdf.TextItem := inferInstance
example : Inhabited Pdf.ContentOp := inferInstance

example (operations : Array Pdf.ContentOp) :
    Pdf.render operations = Pdf.joinLines (Pdf.lines operations) :=
  Pdf.render_lines_exact operations

example (operations : Array Pdf.ContentOp) :
    (Pdf.lines operations).countP Pdf.Line.isOpen =
      (Pdf.lines operations).countP Pdf.Line.isEmc :=
  Pdf.lines_marked_balanced operations

example (left right : Array Nat)
    (hl : ∀ glyph ∈ left, glyph < 65536)
    (hr : ∀ glyph ∈ right, glyph < 65536)
    (h : (Pdf.TextItem.glyphs left).render = (Pdf.TextItem.glyphs right).render) :
    left = right :=
  Pdf.glyphs_inj hl hr h

example (geom : Layout.Geom) (remap : Array Nat) (widths : Array (Array Int))
    (images : Array (Option Nat)) (tags : Array (Option String)) (page : Layout.PageOut) :
    Pdf.runsOf (Pdf.contentOps geom remap widths images tags page) = Pdf.pageRuns page :=
  Pdf.contentOps_text geom remap widths images tags page

example (geom : Layout.Geom) (remap : Array Nat) (widths : Array (Array Int))
    (images : Array (Option Nat)) (tags : Array (Option String)) (page : Layout.PageOut) :
    Pdf.inkOps (Pdf.contentOps geom remap widths images tags page) =
      Pdf.contentOpsPlain geom remap widths images tags page :=
  Pdf.mark_ink_exact geom remap widths images tags page

example (plan : Pdf.WritePlan) (before after : List Pdf.Row) (row : Pdf.Row)
    (h : plan.direct.toList = before ++ row :: after) :
    PdfLex.Span plan.bytes (Pdf.serialize plan.head before.toArray).1.size
      (PdfLex.octets (Pdf.rowInto ByteArray.empty row.id row.body)) :=
  plan.direct_span_exact before after row h

example : Repr Pdf.StructKid := inferInstance
example : Repr Pdf.StructElem := inferInstance
example : Struct.Tree → Array Pdf.StructElem := Pdf.skeleton

example (tree : Struct.Tree) : Pdf.Unfilled (Pdf.skeleton tree) :=
  Pdf.skeleton_unfilled_contract tree

example (elements : Array Pdf.StructElem) (leafPages : Array (Array (Nat × Nat))) :
    (Pdf.fill elements leafPages).size = elements.size :=
  Pdf.fill_size_exact elements leafPages

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
  fail_if_success have := Pdf.serializeList_row_span_exact
  fail_if_success have := Pdf.pushGid
  fail_if_success have := Pdf.dashOp
  fail_if_success have := Pdf.paintOp
  fail_if_success have := Pdf.strokeOp
  fail_if_success have := Pdf.fillOp
  fail_if_success have := Pdf.renderStep
  fail_if_success have := Pdf.TextOp.renderLines
  fail_if_success have := Pdf.ContentOp.renderLines
  fail_if_success have := Pdf.widthμOf
  fail_if_success have := Pdf.penTarget
  fail_if_success have := Pdf.TextSt.closeTJ
  fail_if_success have := Pdf.TextSt.moveTo
  fail_if_success have := Pdf.TextSt.setFace
  fail_if_success have := Pdf.stepRun
  fail_if_success have := Pdf.stepSeg
  fail_if_success have := Pdf.pathGroupsList
  fail_if_success have := Pdf.TextOp.numberList
  fail_if_success have := Pdf.ContentOp.numberList
  trivial

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
  fail_if_success have := Pdf.fillKid
  fail_if_success have := Pdf.leafIdsOf
  fail_if_success have := Pdf.skelLeafIds
  fail_if_success have := Pdf.fillKids_mcid_exact
  trivial

end Tests.PdfInterfaces
