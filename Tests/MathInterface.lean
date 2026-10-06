module

import LeanTex.Core.Math
import LeanTex.Core.MathMl
import LeanTex.Core.MathSymData

/-! Ordinary consumers share the typed math AST, its semantic operations and
contracts, and the MathML projection. Unicode table machinery, resolution
walkers and node-construction helpers remain private to their owners. -/

open LeanTex.Core
open LeanTex.Core.Math

namespace Tests.MathInterface

example : Repr MList := inferInstance
example : BEq MList := inferInstance
example : Inhabited MList := inferInstance
example : Inhabited MRows := inferInstance
example : DecidableEq MathStyle := inferInstance
example : DecidableEq MathAlphabet := inferInstance
example : MathClass → String := MathClass.label

example (c : Ir.Color) (body value : MList) (rows : MRows) : MList :=
  .cons (.ink c none)
    (.cons (.atom .inner
      (.cancel .to {} value
        (.cons (.atom .inner (.grid (.array #[.center] 1000) rows) .nil .nil false) body))
      .nil .nil false) .nil)

example : MathAlphabetCoverage → MList → MList := resolveMathAlphas
example : MathAlphabetCoverage → MList → Array MathAlphabet := missingMathAlphas
example : Bool → Array (String × String) → MList → MathMl.Marks → Html.Node :=
  fun display extra body marks => MathMl.formula display extra body marks
example : List (String × MathClass × Char) := MathSymData.rows
example : List String := MathSymData.amsfonts
example : List String := MathSymData.amssymb
example : List String := MathSymData.refused

example (acc : Array Char) : MList.scalarsList acc .nil = acc := by
  simp only [MList.scalarsList]

example (f : Ir.Color → Option String → Ir.Color) :
    MList.mapInk f .nil = .nil := rfl

example (f : Ir.Color → Option String → Ir.Color) (body : MList) (acc : Array Char) :
    (MList.mapInk f body).scalarsList acc = body.scalarsList acc :=
  MList.mapInk_scalars f body acc

example (a b base : Int) (hb : 0 ≤ base) (style : MathStyle) :
    sizeFor (ScriptScales.clamp a b) base style.sup ≤
      sizeFor (ScriptScales.clamp a b) base style ∧
    sizeFor (ScriptScales.clamp a b) base style.sub ≤
      sizeFor (ScriptScales.clamp a b) base style :=
  sizes_shrink a b base hb style

example (coverage : MathAlphabetCoverage) (body : MList) :
    resolveMathAlphas coverage (resolveMathAlphas coverage body) =
      resolveMathAlphas coverage body :=
  resolveMathAlphas_fixed_point coverage body

example (alphabet : MathAlphabet) (c : Char) :
    alphabet.sourceRangeOf .sym c = alphabet.rangeOf c :=
  MathAlphabet.sourceRangeOf_sym_exact alphabet c

example (room : Bool) (input : CancelIn) :
    (cancelGeom .to room input).polys.size ≤ 2 := by
  rw [cancelGeom_to_polys_exact]
  split <;> simp

example (display : Bool) (extra : Array (String × String)) (body : MList)
    (marks : MathMl.Marks) :
    MathMl.nodeChars #[] (MathMl.formula display extra body marks) =
      MathMl.listChars #[] body :=
  MathMl.mathml_glyphs_agree display extra body marks

example : True := by
  fail_if_success have := Math.alphaHoles
  fail_if_success have := Math.MathAlphabet.hole
  fail_if_success have := Math.degrade_go_length
  fail_if_success have := Math.resolveAlphaNucleus
  fail_if_success have := MathMl.charText
  fail_if_success have := MathMl.pushChars
  fail_if_success have := MathMl.delimMo
  fail_if_success have := MathMl.cancelPolygon
  fail_if_success have := MathMl.paint_chars
  trivial

end Tests.MathInterface
