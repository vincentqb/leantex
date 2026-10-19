module

public import LeanTex.Core.PdfFigures
public import LeanTex.Core.Icc
import LeanTex.Core.Ir

/-! The press a document's output intent characterizes, and the engine's own colours in its space:
a colour the engine chose that would paint in RGB is printed as the intent's profile prints its
sRGB, a declared colour as declared. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Gfx

/-- The hairline drawn where an image did not load, a neutral grey. -/
public def placeholderInk : Ir.Color := { r := 158, g := 158, b := 168, origin := .engine }

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

/-- Whether a colour is the engine's that would paint in DeviceRGB. -/
public def enginesRgb (c : Ir.Color) : Bool :=
  c.origin == .engine && c.cmyk.isNone && match c.pdfModel with
    | none | some (.rgb ..) => true
    | some (.gray _) | some (.cmyk ..) | some (.separation ..) => false

/-- An engine colour that would paint in RGB, in a CMYK or gray profile's space through its way
back, else as xcolor converts, an engine neutral in black ink alone as light as the profile shows
it, its screen value kept; any other as it stands. -/
public def pressColor (t : Icc.Transform) (c : Ir.Color) : Ir.Color :=
  if !enginesRgb c then c else
  if t.space == "CMYK" && c.r == c.g && c.g == c.b then
    { c with pdfModel := some (.gray (decimal16 (65535 - t.blackFor c.g))) }
  else
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

/-- A gradient's stops recoloured. -/
private def gradientM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color) :
    Gfx.Gradient → m Gfx.Gradient
  | .linear p0 p1 st xf => return .linear p0 p1 (← st.mapM fun s => return { s with color := ← f s.color }) xf
  | .radial c0 r0 c1 r1 st xf =>
    return .radial c0 r0 c1 r1 (← st.mapM fun s => return { s with color := ← f s.color }) xf

/-- A paint recoloured. -/
private def PdfPaint.recolorM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color) :
    PdfPaint → m PdfPaint
  | .solid c => return .solid (← f c)
  | .pattern res g => return .pattern res (← gradientM f g)

private def PaintStroke.recolorM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color)
    (s : PaintStroke) : m PaintStroke :=
  return { s with paint := ← s.paint.recolorM f }

private def XKind.recolorM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color) :
    XKind → m XKind
  | .stamp fp sp gs => return .stamp (← fp.mapM (·.recolorM f)) (← sp.mapM (·.recolorM f)) gs
  | .symbol => return .symbol
  | .group => return .group
  | .raster k => return .raster k

mutual

/-- A text operator recoloured. -/
private def TextOp.recolorM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color) :
    TextOp → m TextOp
  | .color c => return .color (← f c)
  | .marked tag body => return .marked tag (← TextOp.recolorListM f #[] body.toList)
  | .scale p => return .scale p
  | .move x y => return .move x y
  | .font res size => return .font res size
  | .show items => return .show items

private def TextOp.recolorListM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color)
    (acc : Array TextOp) : List TextOp → m (Array TextOp)
  | [] => return acc
  | o :: rest => do TextOp.recolorListM f (acc.push (← TextOp.recolorM f o)) rest

end

mutual

/-- A content operator recoloured, the placeholder box drawn as a stroke in its ink so the ink can
be recoloured too. -/
private def ContentOp.recolorM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color) :
    ContentOp → m ContentOp
  | .fill c x y w h => return .fill (← f c) x y w h
  | .paint fl st gs segs => do
    let fl ← fl.mapM fun p => return { p with paint := ← p.paint.recolorM f }
    return .paint fl (← st.mapM (·.recolorM f)) gs segs
  | .text ops => return .text (← TextOp.recolorListM f #[] ops.toList)
  | .image x y w h res => return .image x y w h res
  | .imageMissing x y w h => do
    let ink ← f placeholderInk
    return .paint none (some { paint := .solid ink, width := Dim.bp 3 / 4, cap := none
                               join := none, miter := none, dash := none }) none #[.rect x y w h]
  | .marked tag body => return .marked tag (← ContentOp.recolorListM f #[] body.toList)
  | .group mx gs clips body => return .group mx gs clips (← ContentOp.recolorListM f #[] body.toList)
  | .shade res g => return .shade res (← gradientM f g)
  | .outline fl st segs => return .outline fl st segs
  | .xobject mx res kind body =>
    return .xobject mx res (← kind.recolorM f) (← ContentOp.recolorListM f #[] body.toList)

private def ContentOp.recolorListM {m : Type → Type} [Monad m] (f : Ir.Color → m Ir.Color)
    (acc : Array ContentOp) : List ContentOp → m (Array ContentOp)
  | [] => return acc
  | o :: rest => do ContentOp.recolorListM f (acc.push (← ContentOp.recolorM f o)) rest

end

/-- The press's colours computed so far, keyed by screen value. -/
private abbrev PressCache := Std.HashMap UInt32 Ir.PdfColor

/-- `pressColor`, computed once per screen value the engine chose. -/
private def pressCached (t : Icc.Transform) (c : Ir.Color) : StateM PressCache Ir.Color := do
  if !enginesRgb c then return c
  let key := (c.r.toUInt32 <<< 16) ||| (c.g.toUInt32 <<< 8) ||| c.b.toUInt32
  match (← get)[key]? with
  | some model => return { c with pdfModel := some model }
  | none =>
    let pressed := pressColor t c
    if let some model := pressed.pdfModel then modify (·.insert key model)
    return pressed

/-- Pages' or forms' operators with the engine's own colours in the press, each computed once. -/
public def pressedOps (t : Icc.Transform) (ops : Array (Array ContentOp)) :
    Array (Array ContentOp) :=
  (ops.mapM fun (page : Array ContentOp) => page.mapM (ContentOp.recolorM (pressCached t))).run' {}

/-- A figure resource with the engine's own colours in the press. -/
public def pressedFig (t : Icc.Transform) : FigRes → FigRes
  | .extG a b => .extG a b
  | .pattern g => .pattern ((gradientM (pressCached t) g).run' {})
  | .shading g => .shading ((gradientM (pressCached t) g).run' {})
  | .form kind body => .form kind ((body.mapM (ContentOp.recolorM (pressCached t))).run' {})

/-- The transform of the output profile a file embeds, when it characterizes CMYK or gray, the
spaces whose press the engine's own colours are printed in. -/
public def pressOf (profile : Option ByteArray) : Option Icc.Transform :=
  (profile.bind Icc.Transform.of?).filter fun t => t.space == "CMYK" || t.space == "GRAY"

end LeanTex.Core.Pdf
