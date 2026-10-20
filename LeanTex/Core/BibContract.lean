module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

/-! Kernel checks of the reference list's shipped values. -/

namespace LeanTex.Core.Ir

/-- An undeclared reference list reads natbib's own values. -/
public theorem bibList_default_exact :
    bibHang {} = { width := { em := 1000 } } ∧
    (bibSep {} (Dim.pt 10)).width.fixed = Dim.pt 8 ∧
    (bibSep {} (Dim.pt 11)).width.fixed = Dim.pt 9 ∧
    (bibSep {} (Dim.pt 12)).width.fixed = Dim.pt 10 :=
  ⟨rfl, by decide, by decide, by decide⟩

end LeanTex.Core.Ir
