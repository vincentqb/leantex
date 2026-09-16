import LeanTex.Core.Diag
import LeanTex.Core.Ir
import LeanTex.Core.Layout

namespace LeanTex.Core.Check

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Layout

/-- What the engine actually shipped, which is what assertions are judged
against — never the intent, always the result. -/
structure Shipped where
  pages : Nat
  fontsEmbedded : Bool

def Shipped.ofOut (out : Out) (fontsEmbedded : Bool) : Shipped :=
  { pages := out.pages.size, fontsEmbedded := fontsEmbedded }

private def failure (a : Assertion) (actual : String) : Diag :=
  { severity := .error
    code := "E0330"
    message := s!"assertion failed: {a.kind.source} (actual: {actual})"
    span := a.span
    help := some "the document shipped this; change the source or the assertion" }

/-- Check one assertion, returning a diagnostic when it does not hold. -/
def one (shipped : Shipped) (a : Assertion) : Option Diag :=
  match a.kind with
  | .pages op n =>
    if op.holds shipped.pages n then none
    else some (failure a s!"{shipped.pages}")
  | .fontsAllEmbedded =>
    if shipped.fontsEmbedded then none
    else some (failure a "a font was not embedded")

/-- Check every assertion. Empty result means the document satisfied them. -/
def all (shipped : Shipped) (asserts : Array Assertion) : Array Diag :=
  asserts.filterMap (one shipped)

end LeanTex.Core.Check
