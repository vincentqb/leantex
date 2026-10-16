module

public import LeanTex.Core.PdfFigures
public import LeanTex.Core.Icc
import LeanTex.Core.Ir

/-! The press a document's output intent characterizes, and the engine's own colours in its space:
a colour no declaration gave a device model is printed as the intent's profile prints its sRGB. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Gfx

/-- The hairline drawn where an image did not load, a neutral grey. -/
public def placeholderInk : Ir.Color := { r := 158, g := 158, b := 168 }

/-- A 16-bit device value in thousandths, as a PDF decimal. -/
private def decimal16 (v : Nat) : String := Ir.Color.pdfMilli ((v * 1000 + 32767) / 65535)

/-- An sRGB colour in DeviceCMYK as xcolor's `cmyk:rgb` converts it, full undercolour removal
and black generation, in thousandths. -/
private def xcolorCmyk (c : Ir.Color) : Nat × Nat × Nat × Nat :=
  let cy := 1000 - Ir.Color.milli c.r
  let m := 1000 - Ir.Color.milli c.g
  let y := 1000 - Ir.Color.milli c.b
  let k := min cy (min m y)
  (cy - k, m - k, y - k, k)

/-- An sRGB colour in DeviceGray as xcolor's `gray:rgb` converts it, in thousandths. -/
private def xcolorGray (c : Ir.Color) : Nat :=
  (300 * Ir.Color.milli c.r + 590 * Ir.Color.milli c.g + 110 * Ir.Color.milli c.b + 500) / 1000

/-- An engine colour, which no declaration gave a device model, in a CMYK or gray profile's space
through its way back, else as xcolor converts, its screen value kept; any other as it stands. -/
public def pressColor (t : Icc.Transform) (c : Ir.Color) : Ir.Color :=
  if c.pdfModel.isSome || c.cmyk.isSome || c.ink?.isSome then c else
  match t.space, t.fromSrgb c.r c.g c.b with
  | "CMYK", some vs =>
    { c with pdfModel := some (.cmyk (decimal16 (vs[0]?.getD 0)) (decimal16 (vs[1]?.getD 0))
        (decimal16 (vs[2]?.getD 0)) (decimal16 (vs[3]?.getD 0))) }
  | "CMYK", none =>
    let (cy, m, y, k) := xcolorCmyk c
    { c with pdfModel := some (.cmyk (Ir.Color.pdfMilli cy) (Ir.Color.pdfMilli m)
        (Ir.Color.pdfMilli y) (Ir.Color.pdfMilli k)) }
  | "GRAY", some vs => { c with pdfModel := some (.gray (decimal16 (vs[0]?.getD 0))) }
  | "GRAY", none => { c with pdfModel := some (.gray (Ir.Color.pdfMilli (xcolorGray c))) }
  | _, _ => c

/-- A paint recoloured. -/
private def PdfPaint.recolor (f : Ir.Color → Ir.Color) : PdfPaint → PdfPaint
  | .solid c => .solid (f c)
  | .pattern res g => .pattern res (g.recolor f)

private def PaintStroke.recolor (f : Ir.Color → Ir.Color) (s : PaintStroke) : PaintStroke :=
  { s with paint := s.paint.recolor f }

private def XKind.recolor (f : Ir.Color → Ir.Color) : XKind → XKind
  | .stamp fp sp gs => .stamp (fp.map (·.recolor f)) (sp.map (·.recolor f)) gs
  | .symbol => .symbol
  | .group => .group
  | .raster k => .raster k

mutual

/-- A text operator recoloured. -/
public def TextOp.recolor (f : Ir.Color → Ir.Color) : TextOp → TextOp
  | .color c => .color (f c)
  | .marked tag body => .marked tag (TextOp.recolorList f #[] body.toList)
  | .scale p => .scale p
  | .move x y => .move x y
  | .font res size => .font res size
  | .show items => .show items

private def TextOp.recolorList (f : Ir.Color → Ir.Color) (acc : Array TextOp) :
    List TextOp → Array TextOp
  | [] => acc
  | o :: rest => TextOp.recolorList f (acc.push (TextOp.recolor f o)) rest

end

mutual

/-- A content operator recoloured, the placeholder box drawn as a stroke in its ink so the ink can
be recoloured too. -/
public def ContentOp.recolor (f : Ir.Color → Ir.Color) : ContentOp → ContentOp
  | .fill c x y w h => .fill (f c) x y w h
  | .paint fl st gs segs =>
    .paint (fl.map fun p => { p with paint := p.paint.recolor f }) (st.map (·.recolor f)) gs segs
  | .text ops => .text (TextOp.recolorList f #[] ops.toList)
  | .image x y w h res => .image x y w h res
  | .imageMissing x y w h =>
    .paint none (some { paint := .solid (f placeholderInk), width := Dim.pt 3 / 4, cap := none
                        join := none, miter := none, dash := none }) none #[.rect x y w h]
  | .marked tag body => .marked tag (ContentOp.recolorList f #[] body.toList)
  | .group m gs clips body => .group m gs clips (ContentOp.recolorList f #[] body.toList)
  | .shade res g => .shade res (g.recolor f)
  | .outline fl st segs => .outline fl st segs
  | .xobject m res kind body =>
    .xobject m res (kind.recolor f) (ContentOp.recolorList f #[] body.toList)

private def ContentOp.recolorList (f : Ir.Color → Ir.Color) (acc : Array ContentOp) :
    List ContentOp → Array ContentOp
  | [] => acc
  | o :: rest => ContentOp.recolorList f (acc.push (ContentOp.recolor f o)) rest

end

/-- A figure resource recoloured. -/
public def FigRes.recolor (f : Ir.Color → Ir.Color) : FigRes → FigRes
  | .extG a b => .extG a b
  | .pattern g => .pattern (g.recolor f)
  | .shading g => .shading (g.recolor f)
  | .form kind body => .form kind (body.map (ContentOp.recolor f))

/-- The transform of the output profile a file embeds, when it characterizes CMYK or gray, the
spaces whose press the engine's own colours are printed in. -/
public def pressOf (profile : Option ByteArray) : Option Icc.Transform :=
  (profile.bind Icc.Transform.of?).filter fun t => t.space == "CMYK" || t.space == "GRAY"

end LeanTex.Core.Pdf
