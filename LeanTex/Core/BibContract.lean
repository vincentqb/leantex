import LeanTex.Core.Ir

/-! The reference list's shipped values, checked by the kernel in a leaf
module: nothing on the import chain to the elaborator waits for these
checks. -/

namespace LeanTex.Core.Ir

/-- **An undeclared reference list reads natbib's own values** at the three
standard bases — the sourced rows `bibSepDefault` holds, exactly, and a
one-em hang. -/
theorem bibList_default_exact :
    bibHang {} = { width := { em := 1000 } } ∧
    (bibSep {} (Dim.pt 10)).width.sp = Dim.pt 8 ∧
    (bibSep {} (Dim.pt 11)).width.sp = Dim.pt 9 ∧
    (bibSep {} (Dim.pt 12)).width.sp = Dim.pt 10 :=
  ⟨rfl, by decide, by decide, by decide⟩

end LeanTex.Core.Ir
