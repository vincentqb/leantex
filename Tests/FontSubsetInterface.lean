module

import LeanTex.Core.FontSubset

/-! Ordinary consumers can subset a parsed face and exercise the CFF path
with its prepared outline source. Byte serialization and glyf rewriting
remain implementation details. -/

open LeanTex.Core

namespace Tests.FontSubsetInterface

example : Font.Font → Array Nat → ByteArray × Bool := FontSubset.program
example : ByteArray → Ink.Table → Array Bool → Ink.Src → (Nat → Bool) →
    Option ByteArray := FontSubset.cffDrop

example : True := by
  fail_if_success have := LeanTex.Core.FontSubset.droppedTables
  fail_if_success have := LeanTex.Core.FontSubset.assemble
  fail_if_success have := LeanTex.Core.FontSubset.glyfDrop
  fail_if_success have := LeanTex.Core.FontSubset.checksum
  fail_if_success have := LeanTex.Core.FontSubset.components
  trivial

end Tests.FontSubsetInterface
