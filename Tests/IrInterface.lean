module

import LeanTex.Core.Ir

/-! Ordinary consumers construct the document IR, read its semantic census,
apply its conserving maps, and request its supported diagnostic dump.
Template traversal, formatting, and local proof machinery stay private. -/

namespace Tests.IrInterface

open LeanTex.Core

example : Repr Ir.Inline := inferInstance
example : BEq Ir.Inline := inferInstance
example : Repr Ir.Block := inferInstance
example : BEq Ir.Block := inferInstance
example : Inhabited Ir.Doc := inferInstance
example : Ir.DocClass → Ir.ClassRecord := Ir.DocClass.record

example (span : Span) (body : Array Ir.Inline) : Ir.Block :=
  .para #[.located span body]

example : Array Ir.Inline → String := Ir.plainText
example : Array Ir.Block → String := Ir.blocksText
example : Array Ir.Inline → Array Ir.Inline → Array Ir.Inline := Ir.fillTemplate
example : Dim.SymGlue → String := Ir.dumpGlue -- ir tier: public API visibility
example : String → Array Ir.Block → String := Ir.dumpBlocks -- ir tier: public API visibility
example : Ir.Doc → Array Diag → String := Ir.dump -- ir tier: public API visibility

example (f : Ir.Inline → Ir.Inline)
    (hf : ∀ x, Ir.plainTextOne (f x) = Ir.plainTextOne x) :
    Ir.Conserves Ir.plainText (Ir.mapInlines f) :=
  Ir.mapInlines_text f hf

example (f : Ir.Inline → Ir.Inline)
    (hf : ∀ x, Ir.plainTextOne (f x) = Ir.plainTextOne x) :
    Ir.Conserves Ir.blocksText (Ir.mapBlocks f) :=
  Ir.mapBlocks_text f hf

example (kind : Ir.FloatKind) (body : Array Ir.Block) :
    Ir.floatNumsList kind [] (Ir.numberFloats body).toList =
      List.range' 1 (Ir.floatNumsList kind [] (Ir.numberFloats body).toList).length :=
  Ir.numberFloats_exact kind body

example (loc : Locale) (table : Ir.RefTable) (body : Array Ir.Block) :
    Ir.resolveRefs loc table body = Ir.mapBlocks (fun x => match x with
      | .ref key form _ _ => Ir.resolveOneRef loc table key form
      | _ => x) body :=
  Ir.resolveRefs_agree loc table body

example (loc : Locale) (table : Ir.RefTable) (text : String) :
    Ir.resolveRefs loc table #[.para #[.text text]] = #[.para #[.text text]] := by
  rw [Ir.resolveRefs_agree]
  rfl

/-- The text equations needed by paragraph and listing consumers are visible. -/
example (text : String) : Ir.plainText #[.text text] = text := by
  simp [Ir.plainText, Ir.plainTextList, Ir.plainTextOne]

example (body : Array Ir.Inline) :
    Ir.unwrapItemStep (.para body) = .para body :=
  Ir.unwrapItemStep_para_exact body

/-- The public colour contract is usable without seeing the printer body. -/
example (v : Nat) (hv : v < 1001) :
    Ir.Color.decodeMilli (Ir.Color.pdfMilli v) = v :=
  Ir.Color.pdfMilli_decode v hv

example (v : Nat) : Ir.Color.pdfMilli v = Ir.Color.pdfMilli v := by
  fail_if_success unfold Ir.Color.pdfMilli
  rfl

example (template body : Array Ir.Inline) :
    Ir.fillTemplate template body = Ir.fillTemplate template body := by
  fail_if_success unfold Ir.fillTemplate
  rfl

example (doc : Ir.Doc) (diags : Array Diag) :
    Ir.dump doc diags = Ir.dump doc diags := by -- ir tier: body opacity guard
  fail_if_success unfold Ir.dump -- ir tier: body opacity guard
  rfl

example : True := by
  fail_if_success have := Ir.Color.cmykPreviewByte
  fail_if_success have := Ir.Palette.resolve_go_model_exact
  fail_if_success have := Ir.fillOne
  fail_if_success have := Ir.fillList
  fail_if_success have := Ir.dumpSourcedGlue -- ir tier: helper privacy
  fail_if_success have := Ir.dumpOverlayRange -- ir tier: helper privacy
  fail_if_success have := Ir.dumpMathNucleus -- ir tier: helper privacy
  fail_if_success have := Ir.dumpMathRows -- ir tier: helper privacy
  fail_if_success have := Ir.dumpInlines -- ir tier: helper privacy
  fail_if_success have := Ir.dumpInlineList -- ir tier: helper privacy
  fail_if_success have := Ir.dumpInline -- ir tier: helper privacy
  fail_if_success have := Ir.dumpTableCells -- ir tier: helper privacy
  fail_if_success have := Ir.dumpBlockList -- ir tier: helper privacy
  fail_if_success have := Ir.dumpItems -- ir tier: helper privacy
  fail_if_success have := Ir.dumpBlock -- ir tier: helper privacy
  fail_if_success have := Ir.dumpDiag -- ir tier: helper privacy
  fail_if_success have := Ir.FormulaText.list
  fail_if_success have := Ir.indexStep
  fail_if_success have := Ir.Color.mixStep
  fail_if_success have := Ir.displaySkipsTable
  fail_if_success have := Ir.Pic.boxFoldList
  fail_if_success have := Ir.FloatCtr
  fail_if_success have := Ir.numberFloatList
  fail_if_success have := Ir.slugGo
  fail_if_success have := Ir.navLinkList
  fail_if_success have := Ir.dimBlockList
  fail_if_success have := Ir.footnoteBlockList
  fail_if_success have := Ir.outlineWalk
  fail_if_success have := Ir.RoleRecolorState
  fail_if_success have := Ir.recolorRolesList
  fail_if_success have := Ir.textLeavesList
  fail_if_success have := Ir.orphanFreeList
  fail_if_success have := Ir.imageRequestPush
  fail_if_success have := Ir.resolveRefLeaf
  fail_if_success have := Ir.unwrapItemStepList
  fail_if_success have := Ir.unwrapItemStepItems
  fail_if_success have := Ir.unwrapItemStepCols
  trivial

end Tests.IrInterface
