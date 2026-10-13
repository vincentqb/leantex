module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! Kernel checks of the reference list's shipped values, in a leaf module off
the elaborator's import chain. -/

namespace LeanTex.Core.Ir

/-- An undeclared reference list reads natbib's own values. -/
public theorem bibList_default_exact :
    bibHang {} = { width := { em := 1000 } } ∧
    (bibSep {} (Dim.pt 10)).width.sp = Dim.pt 8 ∧
    (bibSep {} (Dim.pt 11)).width.sp = Dim.pt 9 ∧
    (bibSep {} (Dim.pt 12)).width.sp = Dim.pt 10 :=
  ⟨rfl, by decide, by decide, by decide⟩

end LeanTex.Core.Ir
