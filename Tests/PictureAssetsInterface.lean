module

import LeanTex.Cli.PictureAssets

/-! The asset executor exposes requests and answers. Process execution,
log parsing and cache replay stay behind that interface. -/

open LeanTex.Cli

namespace Tests.PictureAssetsInterface

example : String → String := PictureAssets.key
example : String → String → String → String → String := PictureAssets.slotName
example : IO (Option System.FilePath) := PictureAssets.cacheDir
example : System.FilePath → String → IO (Option ByteArray) := PictureAssets.previous
example : Option System.FilePath → String → String → String → String →
    IO PictureAssets.Answer := PictureAssets.fulfil
example (answer : PictureAssets.Answer) : ConvCache.Result := answer.result
example (answer : PictureAssets.Answer) : Bool := answer.cached

example : True := by
  fail_if_success have := PictureAssets.readAnswer
  fail_if_success have := PictureAssets.logTail
  fail_if_success have := PictureAssets.produce
  fail_if_success have := PictureAssets.replay
  trivial

end Tests.PictureAssetsInterface
