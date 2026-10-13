module

import LeanTex.Cli.ImageAssets

/-! Captured vector bytes cross one typed conversion interface. Converter
recipes, temporary files and cache policy are private implementation. -/

open LeanTex.Core LeanTex.Cli

namespace Tests.ImageAssetsInterface

example : String := ImageAssets.browserFaceContract
example : String := ImageAssets.canonicalPdfRecipe
example : ByteArray → IO PicCache.Outcome := ImageAssets.validateSvgResult
example : PdfRead.PageSelection → Except String Bool := ImageAssets.svgPosterAtEnd
example : Image.PlanParams → ByteArray → Bool →
    Option (IO.Process.SpawnArgs → IO IO.Process.Output) → IO (Except String Image.Plan) :=
  @ImageAssets.canonicalPlan
example : ByteArray → PdfRead.PageSelection →
    Option (IO.Process.SpawnArgs → IO IO.Process.Output) → IO (Except String ByteArray) :=
  @ImageAssets.canonicalPoster
example : ByteArray → PdfRead.PageSelection → IO (Except String ByteArray) :=
  ImageAssets.pdfSvg
example : ByteArray → IO (Except String ByteArray) := ImageAssets.picFace

example : True := by
  fail_if_success have := ImageAssets.runChecked
  fail_if_success have := ImageAssets.finishSvg
  fail_if_success have := ImageAssets.convert
  fail_if_success have := ImageAssets.convertResult
  trivial

end Tests.ImageAssetsInterface
