namespace LeanTex.Core.Ir

/-! The colour value, alone in a leaf module so a formula can carry one:
`Math` sits below `Ir` in the import graph, and a colour inside math is the
very value the text path resolves, never a copy of its fields. Colour
arithmetic and PDF operators stay in `Ir`. -/

/-- The PDF device model a source colour declared. Its components are
canonical decimal spellings validated by `Decl.parseColorSpec`; retaining them
lets the PDF backend preserve rgb, gray, and cmyk without quantizing through
the screen preview. -/
inductive PdfColor where
  | rgb (r g b : String)
  | gray (v : String)
  | cmyk (c m y k : String)
  deriving Repr, BEq

/-- A source colour's screen preview plus its exact PDF device-model rider.
`r g b` are always populated for HTML, contrast judgement, and dimming.
`pdfModel` is present for an explicit xcolor model; legacy/native palette
bytes use the established derived DeviceRGB spelling. `cmyk` remains the
thousandth projection used by xcolor mix arithmetic and print registration. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  /-- CMYK components projected to thousandths for the existing model-closed
  mix arithmetic. Exact source components live in `pdfModel` and reach PDF. -/
  cmyk : Option (Nat × Nat × Nat × Nat) := none
  pdfModel : Option PdfColor := none
  deriving Repr, Inhabited

/-- Colour equality is screen-and-mix equality. `pdfModel` is source
projection provenance: PDF emission reads it directly, while contrast,
palette diffing, and equivalent model spellings compare the shared preview
and the CMYK arithmetic rider. -/
instance : BEq Color where
  beq a b := a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk

/-- One byte as two hex digits; `upper` picks the alphabet's case. The dump
printers and diagnostics quote colours uppercase; CSS serializes lowercase
(`Color.css`). One printer for every reader, so a byte cannot render two
ways. -/
def Color.hexByte (v : UInt8) (upper : Bool := true) : String :=
  let d := (if upper then "0123456789ABCDEF" else "0123456789abcdef").toList
  String.ofList [d.getD (v.toNat / 16) '0', d.getD (v.toNat % 16) '0']

/-- The colour as CSS serializes it: `#rrggbb`, lowercase. Both HTML
emitters — the text runs and the MathML — print through it. -/
def Color.css (c : Color) : String :=
  let r := Color.hexByte c.r false
  let g := Color.hexByte c.g false
  let b := Color.hexByte c.b false
  "#" ++ r ++ g ++ b

end LeanTex.Core.Ir
