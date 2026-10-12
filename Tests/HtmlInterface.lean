module

import LeanTex.Core.HtmlDoc

/-! The HTML backend exposes document emission, captured resources and
artifact contracts. Its stylesheet assembly and traversal state stay private. -/

namespace Tests.HtmlInterface

open LeanTex.Core

example : HtmlDoc.Config → Ir.Doc → String × Array Diag := HtmlDoc.emit
example (cfg : HtmlDoc.Config) (doc : Ir.Doc) (svgChecked : Array ByteArray) :
    Except String (HtmlDoc.ClosedPage cfg.mathRenderer) × Array Diag :=
  HtmlDoc.emitClosed cfg doc svgChecked
example : HtmlDoc.Config → Array HtmlResource.Embedded := HtmlDoc.resources
example : Bool → Bool → Array Html.Node → HtmlDoc.A11yFacts := HtmlDoc.a11yFacts

example (fs : Font.FontSet) {k : Nat} (hk : k < fs.fonts.size) :
    ∃ ff ∈ HtmlDoc.shipFaces fs, ff.index = k :=
  HtmlDoc.shipFaces_covers fs hk

example (cfg : HtmlDoc.Config) (pic : Ir.Pic.Picture) :
    (HtmlDoc.blockNode cfg (.picture pic)).tag? = some "svg" ∧
      (pic.alternative ≠ .decorative →
        HtmlDoc.carriesName (HtmlDoc.blockNode cfg (.picture pic)) = true) :=
  HtmlDoc.picture_svg_named_contract cfg pic

example : True := by
  fail_if_success have := HtmlDoc.fontFileName
  fail_if_success have := HtmlDoc.fontFaceRule
  fail_if_success have := HtmlDoc.tokenVars
  fail_if_success have := HtmlDoc.deckStageRule
  fail_if_success have := HtmlDoc.stepRules
  fail_if_success have := HtmlDoc.inlineNodeInto
  fail_if_success have := HtmlDoc.blockNodesInto
  fail_if_success have := HtmlDoc.listItem
  fail_if_success have := HtmlDoc.AlgTree
  fail_if_success have := HtmlDoc.a11yOne
  fail_if_success have := HtmlDoc.Config.fontsDir
  fail_if_success have := HtmlDoc.Config.assetsDir
  fail_if_success have := HtmlDoc.FontAsset
  fail_if_success have := HtmlDoc.fontAssets
  trivial

end Tests.HtmlInterface
