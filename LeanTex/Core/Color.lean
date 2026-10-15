module

public import LeanTex.Core.Hex

namespace LeanTex.Core.Ir

/-! The colour value, in a module small enough for a formula to carry one. -/

/-- A printing ink: the colorant name its separation carries and its DeviceCMYK alternate at full
tint. -/
public structure Ink where
  name : String
  c : Rat
  m : Rat
  y : Rat
  k : Rat
  deriving Repr, BEq, DecidableEq

/-- The PDF device model a source colour declared, as canonical decimal components, or a tint of
an ink in its `/Separation` space. -/
public inductive PdfColor where
  | rgb (r g b : String)
  | gray (v : String)
  | cmyk (c m y k : String)
  | separation (ink : Ink) (tint : Rat)
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

/-- The ink and tint a colour paints with. -/
@[expose] public def Color.ink? (c : Color) : Option (Ink × Rat) :=
  match c.pdfModel with
  | some (.separation i t) => some (i, t)
  | some (.rgb ..) | some (.gray _) | some (.cmyk ..) | none => none

/-- Equality compares the screen preview, the CMYK rider and the ink, never another device
spelling. -/
public instance : BEq Color where
  beq a b := a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk && a.ink? == b.ink?

public theorem Color.beq_screen_exact (a b : Color) :
    (a == b) = (a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk &&
      a.ink? == b.ink?) := by rfl

/-- xcolor's screen projection of one CMYK channel at `v` over black `k`, `1 - min(1, v + k)`,
through TeX's 16-bit fixed point. -/
@[expose] public def inkPreviewByte (v k : Rat) : UInt8 :=
  let scale := v.den * k.den
  let used := min scale (v.num.toNat * k.den + k.num.toNat * v.den)
  let sp := ((scale - used) * 65536 + scale / 2) / scale
  UInt8.ofNat ((sp * 255 + 32768) / 65536)

/-- A tint of an ink: the alternate scaled by the tint on screen and in the CMYK rider, the ink
itself in the PDF. -/
@[expose] public def Color.ofInk (i : Ink) (tint : Rat) : Color :=
  let unit (v : Rat) : Rat := if v < 0 then 0 else if 1 < v then 1 else v
  let t := unit tint
  let part (v : Rat) : Rat := unit (v * t)
  let milli (v : Rat) : Nat := (v.num.toNat * 1000 + v.den / 2) / v.den
  let black := part i.k
  { r := inkPreviewByte (part i.c) black, g := inkPreviewByte (part i.m) black,
    b := inkPreviewByte (part i.y) black,
    cmyk := some (milli (part i.c), milli (part i.m), milli (part i.y), milli black),
    pdfModel := some (.separation i t) }

/-- Whether a colour is the paper itself: white with no ink, in any model. -/
@[expose] public def Color.isPaper (c : Color) : Bool :=
  c.ink?.isNone && match c.cmyk with
    | some q => q == (0, 0, 0, 0)
    | none => c.r == 255 && c.g == 255 && c.b == 255

@[expose] public def Color.black : Color := { r := 0, g := 0, b := 0 }

@[expose] public def Color.white : Color := { r := 255, g := 255, b := 255 }

/-- Black ink alone, in DeviceGray as the PDF's initial fill and xcolor's `black` are. -/
@[expose] public def Color.blackInk : Color :=
  { r := 0, g := 0, b := 0, pdfModel := some (.gray "0") }

/-- The colour as six hex digits, upper-case and behind `#` unless asked otherwise. -/
@[expose] public def Color.hex (c : Color) (hash upper : Bool := true) : String :=
  (if hash then "#" else "") ++ Hex.byte upper c.r ++ Hex.byte upper c.g ++ Hex.byte upper c.b

/-- The colour as CSS serializes it: `#rrggbb`, lowercase. -/
@[expose] public def Color.css (c : Color) : String := c.hex (upper := false)

end LeanTex.Core.Ir
