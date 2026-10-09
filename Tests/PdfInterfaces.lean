module

import LeanTex.Core.PdfStruct
import LeanTex.Core.PdfRowRecovery
import LeanTex.Core.PdfAgreement

/-! Ordinary consumers use typed content operations and structure
projections without depending on rendering, allocation, or traversal helpers. -/

namespace Tests.PdfInterfaces

open LeanTex.Core

example : Repr Pdf.PathOp := inferInstance
example : BEq Pdf.TextItem := inferInstance
example : Inhabited Pdf.ContentOp := inferInstance
example : Pdf.Rect → String := Pdf.Rect.render

example (_rect : Pdf.Rect) : True := by
  fail_if_success
    have : _rect.render =
        s!"[{Dim.Sp.toPtString _rect.x0} {Dim.Sp.toPtString _rect.y0} {Dim.Sp.toPtString _rect.x1} {Dim.Sp.toPtString _rect.y1}]" :=
      by rfl
  trivial

example : ({} : Ir.OutputContract).unmet Pdf.profile = #[] :=
  Pdf.pdf_default_contract_exact

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

example : Repr Pdf.WriteError := inferInstance
example : BEq Pdf.WriteError := inferInstance
example (plan : Pdf.WritePlan) : Decidable plan.WithinDomain := inferInstance

example (plan : Pdf.WritePlan) (bytes : ByteArray) :
    plan.checked = .ok bytes ↔ plan.WithinDomain ∧ plan.bytes = bytes :=
  plan.checked_exact bytes

example (plan : Pdf.WritePlan) (error : Pdf.WriteError)
    (h : plan.checked = .error error) : ¬ plan.WithinDomain :=
  plan.checked_error_gated error h

example (plan : Pdf.WritePlan) :
    ∀ entry ∈ plan.entries, entry.Fits plan.widths :=
  plan.entries_fits

example (plan : Pdf.WritePlan) :
    ∀ chunk ∈ plan.chunks, 0 < chunk.length ∧ chunk.length ≤ Pdf.objStmCapacity :=
  plan.chunks_between

example (geom : Layout.Geom) (fonts : Font.FontSet) (pages : Array Layout.PageOut)
    (info : Ir.Meta) (images : Image.Store) (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (operations : Array (Array Pdf.ContentOp)) (programs : Array (ByteArray × Bool))
    (bytes : ByteArray) :
    Pdf.writeChecked geom fonts pages info images outline streams tree operations programs =
        .ok bytes ↔
      (Pdf.prepare geom fonts pages info images outline streams tree operations programs).WithinDomain ∧
      Pdf.write geom fonts pages info images outline streams tree operations programs = bytes :=
  Pdf.writeChecked_exact geom fonts pages info images outline streams tree operations programs bytes

/-- Typed publishers can inspect every refusal without reading serializer internals. -/
example (error : Pdf.WriteError) : Nat :=
  match error with
  | .byteOffset bytes => bytes
  | .objectStreamSize bytes => bytes
  | .xrefStreamSize bytes => bytes
  | .objectSpelling id => id

example (fonts : Font.FontSet) (pages : Array Layout.PageOut)
    (h : 0 < fonts.fonts.size) :
    ∀ k ∈ Pdf.keepFaces fonts pages,
      ∃ face ∈ HtmlDoc.shipFaces fonts, face.index = k :=
  Pdf.html_fonts_cover_pdf fonts pages h

example (features : Ir.Features) :
    (!(HtmlDoc.kernCssFor features).isEmpty) = Layout.kernEnabled features :=
  Pdf.features_agree features

example (floor : String) (alternative : Ir.Alt) :
    (Pdf.altElem #[Pdf.rootElem] 0 0 alternative).size = 1 ↔
      HtmlDoc.attrOf? (HtmlDoc.pictureAltAttrs floor alternative) "aria-hidden" =
        some "true" :=
  Pdf.alt_hidden_agree floor alternative

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
  fail_if_success have := Pdf.serializeList
  fail_if_success have := Pdf.indexObjectsList
  fail_if_success have := Pdf.objectStreamList
  fail_if_success have := Pdf.ImgExtra
  fail_if_success have := Pdf.Rect.obj
  fail_if_success have := Pdf.ptObj
  fail_if_success have := Pdf.WritePlan.find_unencodable_none
  fail_if_success have := Pdf.pushGid
  fail_if_success have := Pdf.dashOp
  fail_if_success have := Pdf.paintOp
  fail_if_success have := Pdf.strokeOp
  fail_if_success have := Pdf.fillOp
  fail_if_success have := Pdf.renderStep
  fail_if_success have := Pdf.TextOp.renderLines
  fail_if_success have := Pdf.ContentOp.renderLines
  fail_if_success have := Pdf.TextOp.render_lines
  fail_if_success have := Pdf.ContentOp.render_lines
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
