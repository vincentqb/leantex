module

public import LeanTex.Core.Hex

namespace LeanTex.Core.Ir

/-! The colour value, in a module small enough for a formula to carry one. -/

/-- The PDF device model a source colour declared, as canonical decimal components. -/
public inductive PdfColor where
  | rgb (r g b : String)
  | gray (v : String)
  | cmyk (c m y k : String)
  deriving Repr, BEq, DecidableEq

/-- A colour: its sRGB screen preview, a CMYK mix rider, and the exact PDF device model. -/
public structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  /-- CMYK components in thousandths, for mix arithmetic. -/
  cmyk : Option (Nat × Nat × Nat × Nat) := none
  pdfModel : Option PdfColor := none
  deriving Repr, Inhabited, DecidableEq

/-- Equality compares the screen preview and the CMYK rider, never `pdfModel`. -/
public instance : BEq Color where
  beq a b := a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk

public theorem Color.beq_screen_exact (a b : Color) :
    (a == b) = (a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk) := by rfl

@[expose] public def Color.black : Color := { r := 0, g := 0, b := 0 }

@[expose] public def Color.white : Color := { r := 255, g := 255, b := 255 }

/-- The colour as six hex digits, upper-case and behind `#` unless asked otherwise. -/
@[expose] public def Color.hex (c : Color) (hash upper : Bool := true) : String :=
  (if hash then "#" else "") ++ Hex.byte upper c.r ++ Hex.byte upper c.g ++ Hex.byte upper c.b

/-- The colour as CSS serializes it: `#rrggbb`, lowercase. -/
@[expose] public def Color.css (c : Color) : String := c.hex (upper := false)

end LeanTex.Core.Ir
