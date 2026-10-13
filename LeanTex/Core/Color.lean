module

namespace LeanTex.Core.Ir

/-! The colour value, in a leaf module so a formula can carry one. -/

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

/-- One byte as two hex digits, uppercase unless `upper` is false. -/
@[expose] public def Color.hexByte (v : UInt8) (upper : Bool := true) : String :=
  let d := (if upper then "0123456789ABCDEF" else "0123456789abcdef").toList
  String.ofList [d.getD (v.toNat / 16) '0', d.getD (v.toNat % 16) '0']

/-- The colour as CSS serializes it: `#rrggbb`, lowercase. -/
@[expose] public def Color.css (c : Color) : String :=
  let r := Color.hexByte c.r false
  let g := Color.hexByte c.g false
  let b := Color.hexByte c.b false
  "#" ++ r ++ g ++ b

end LeanTex.Core.Ir
