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
  trivial

end Tests.IrInterface
