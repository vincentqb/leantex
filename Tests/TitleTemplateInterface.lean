module

import LeanTex.Core.TitleTemplate

/-! A title-template consumer reads a declared template and emits its native settings; scanners stay
private. -/

open LeanTex.Core

namespace Tests.TitleTemplateInterface

example : List (String × TitleTemplate.Font) → Array Parse.Raw →
    Option TitleTemplate.Read := TitleTemplate.read
example : TitleTemplate.Read → Array Native.Setting := TitleTemplate.settings
example : String → Bool := TitleTemplate.fontDecl
example : Array String → String × String × Option String :=
  TitleTemplate.unplacedLoss
example : String → String → String × String := TitleTemplate.skippedLoss
example : String → Bool → String × String × Option String :=
  TitleTemplate.mixedLoss

example : True := by
  fail_if_success have := TitleTemplate.scanList
  fail_if_success have := TitleTemplate.nodeStmt
  fail_if_success have := TitleTemplate.fillStmt
  fail_if_success have := TitleTemplate.srcListInto
  fail_if_success have := TitleTemplate.takeBracket
  fail_if_success have := TitleTemplate.Style
  fail_if_success have := TitleTemplate.Scan
  trivial

end Tests.TitleTemplateInterface
