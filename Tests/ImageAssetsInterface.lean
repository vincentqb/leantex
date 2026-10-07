module

import LeanTex.Cli.ImageAssets

/-! Captured vector bytes cross one typed conversion interface. Converter
recipes, temporary files and cache policy are private implementation. -/

open LeanTex.Core LeanTex.Cli

namespace Tests.ImageAssetsInterface

example : String := ImageAssets.browserFaceContract
example : String → Except String Bool := ImageAssets.svgSaxBoundary
example : ByteArray → Image.PlanParams → IO (Except String Image.Plan) :=
  @ImageAssets.validateSvg
example : PdfRead.PageSelection → Except String Bool := ImageAssets.svgPosterAtEnd
example : Image.PlanParams → ByteArray → PdfRead.PageSelection →
    Option (IO.Process.SpawnArgs → IO IO.Process.Output) → IO (Except String Image.Plan) :=
  @ImageAssets.svgPlan
example : ByteArray → PdfRead.PageSelection → IO (Except String ByteArray) :=
  @ImageAssets.svgPoster
example : ByteArray → PdfRead.PageSelection → IO (Except String ByteArray) :=
  ImageAssets.pdfSvg
example : ByteArray → IO (Except String ByteArray) := ImageAssets.picFace

example : True := by
  fail_if_success have := ImageAssets.supportedSvg
  fail_if_success have := ImageAssets.fontIndependentSvg
  fail_if_success have := ImageAssets.runChecked
  fail_if_success have := ImageAssets.checkSvgFile
  fail_if_success have := ImageAssets.finishSvg
  fail_if_success have := ImageAssets.convert
  trivial

end Tests.ImageAssetsInterface
