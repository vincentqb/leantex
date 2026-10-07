import LeanTex.Core.ListMark

/-! Ordinary clients can build markers and use their numbering and text
contracts. The two reduction checks pin the bodies read by HtmlDoc and
Elab; the negative checks keep the digit and roman decoders internal. -/

open LeanTex.Core

namespace Tests.StructureInterface

example : Bool → Nat → Nat → (Char → Bool) → Array Ir.Inline := ListMark.marker
example : Bool → Nat → String := ListMark.scalars
example : List Char → Nat := ListMark.romanVal

example (n : Nat) :
    ListMark.arabicN n = String.ofList (ListMark.digitsRev n).reverse := rfl

example (n : Nat) :
    ListMark.AlphN n = ListMark.letterN 'A'.toNat n := rfl

example {m n : Nat} (h : ListMark.arabicN m = ListMark.arabicN n) : m = n :=
  ListMark.arabicN_inj h

example {level m n : Nat} (hl : level ≠ 3)
    (h : ListMark.enumLabel level m = ListMark.enumLabel level n) : m = n :=
  ListMark.enumLabel_inj hl h

example (level n : Nat) (covered : Char → Bool) :
    Ir.plainText (ListMark.marker true level n covered) = ListMark.enumLabel level n :=
  ListMark.ordered_marker_shows_order level n covered

example : True := by
  fail_if_success have := LeanTex.Core.ListMark.digitVal
  fail_if_success have := LeanTex.Core.ListMark.undigitsRev
  fail_if_success have := LeanTex.Core.ListMark.romanTable
  fail_if_success have := LeanTex.Core.ListMark.romanCharVal
  fail_if_success have := LeanTex.Core.ListMark.itemGlyph
  trivial

end Tests.StructureInterface
