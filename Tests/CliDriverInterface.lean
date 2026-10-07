module

import LeanTex.Cli.Driver

/-! The CLI implementation exports its entry point. Consumers cannot depend
on its UI state, orchestration records, phase handlers or IO helpers. -/

namespace Tests.CliDriverInterface

example : List String → IO UInt32 := LeanTex.Cli.Driver.main

example (argv : List String) :
    LeanTex.Cli.Driver.main argv = LeanTex.Cli.Driver.main argv := by
  fail_if_success unfold LeanTex.Cli.Driver.main
  rfl

example : True := by
  fail_if_success have := LeanTex.Cli.Driver.Ui
  fail_if_success have := LeanTex.Cli.Driver.Front
  fail_if_success have := LeanTex.Cli.Driver.PicResult
  fail_if_success have := LeanTex.Cli.Driver.frontend
  fail_if_success have := LeanTex.Cli.Driver.build
  fail_if_success have := LeanTex.Cli.Driver.dump
  fail_if_success have := LeanTex.Cli.Driver.resolvePictures
  fail_if_success have := LeanTex.Cli.Driver.imageBrowserFaces
  fail_if_success have := LeanTex.Cli.Driver.picsToSvg
  trivial

end Tests.CliDriverInterface
