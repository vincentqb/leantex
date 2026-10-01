import Tests.Support

open LeanTex.Core

namespace CancelAlignment

/-- Tight vertical bounds in page coordinates with y pointing upward.
Unlike an operand's layout extent, this box never includes baseline zero
unless a painted glyph reaches it. -/
structure InkBounds where
  bottom : Dim.Sp
  top : Dim.Sp
  deriving BEq, Repr

/-- Read a shipped glyph's own outline metrics at its actual size and
baseline. Missing outline evidence is a failed measurement, never a
cap-height or advance-width substitute. -/
def glyphInk (fonts : Font.FontSet) (g : ShippedGlyph) : Except String InkBounds := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  if font.unitsPerEm == 0 then throw "target face has zero units per em"
  let some (lo, hi) := font.yExtent g.glyph | throw "target outline is missing"
  let upem : Int := font.unitsPerEm
  return { bottom := -g.y + lo * g.size / upem
           top := -g.y + hi * g.size / upem }

/-- Union only the target glyphs' ink. Starting from the first glyph is
essential for an annotation whose entire contents are raised. -/
def targetInk (fonts : Font.FontSet) (glyphs : Array ShippedGlyph) :
    Except String InkBounds := do
  let some first := glyphs[0]? | throw "target has no painted glyphs"
  let mut bounds ← glyphInk fonts first
  for g in glyphs.extract 1 glyphs.size do
    let b ← glyphInk fonts g
    bounds := { bottom := min bounds.bottom b.bottom, top := max bounds.top b.top }
  return bounds

/-- Shipped polygons in the same upward page coordinates as `glyphInk`.
The pen advances through every width-bearing segment, including rules. -/
def polygonsAt (line : Layout.LineOut) : Array (Array (Dim.Sp × Dim.Sp)) := Id.run do
  let mut pen := line.x
  let mut polys := #[]
  for seg in line.segs do
    match seg with
    | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .rule w _ _ _ | .image _ w _ =>
      pen := pen + w
    | .poly points _ =>
      polys := polys.push (points.map fun (x, y) => (pen + x, y - line.y))
  return polys

/-- These probes contain one northeast cancellation arrow. Its tip is
the triangle's joint upper-right extreme; a malformed or absent head
cannot make an alignment check pass vacuously. -/
def arrowTip (polys : Array (Array (Dim.Sp × Dim.Sp))) :
    Except String (Dim.Sp × Dim.Sp) := do
  let heads := polys.filter (·.size == 3)
  let #[head] := heads | throw "expected one triangular arrowhead"
  let some p := head[0]? | throw "arrowhead has no vertices"
  let tip := head.foldl (fun (x, y) q => (max x q.1, max y q.2)) p
  unless head.contains tip do throw "arrowhead lacks its upper-right tip"
  let area := head.zipIdx.foldl (fun acc (a, i) =>
    let b := head[(i + 1) % head.size]!
    acc + a.1 * b.2 - a.2 * b.1) 0
  if area == 0 then throw "arrowhead has no painted area"
  return tip

/-- The lower-left endpoint actually present in the shipped shaft.
Head-only arrows have no shaft direction to report. -/
def shaftTail (polys : Array (Array (Dim.Sp × Dim.Sp))) :
    Option (Dim.Sp × Dim.Sp) := do
  let shaft ← (polys.filter (·.size > 3))[0]?
  let p ← shaft[0]?
  let tail := shaft.foldl (fun (x, y) q => (min x q.1, min y q.2)) p
  if shaft.contains tail then some tail else none

structure Witness where
  tip : Dim.Sp × Dim.Sp
  tail : Option (Dim.Sp × Dim.Sp)
  ink : InkBounds
  originX : Dim.Sp
  fontGap : Dim.Sp
  glyphs : Array ShippedGlyph
  deriving Repr

/-- Twice the signed distance from the target's vertical ink centre to
the arrow tip. Positive means the target is too high on the page. -/
def Witness.centreError2 (w : Witness) : Dim.Sp :=
  w.ink.top + w.ink.bottom - 2 * w.tip.2

/-- One sp on the doubled centre admits exactly integer-half rounding.
This is tip attachment; the shaft's slope does not move the target. -/
def Witness.centred (w : Witness) : Bool := w.centreError2.natAbs ≤ 1

/-- Horizontal clearance is the advance origin's distance from the tip.
It makes no claim about horizontal outline bounds or raster collisions. -/
def Witness.originGap (w : Witness) : Dim.Sp := w.originX - w.tip.1

def Witness.originGapped (w : Witness) : Bool := w.originGap == w.fontGap

/-- Read a one-line synthetic page. The `u` immediately before the
construct witnesses its actual style size and math face, so the expected
gap is scaled from that font's MATH table rather than guessed from text
size or copied from cancellation geometry. Target scalars are disjoint
from every operand and carrier in `probes`. -/
def measure (fonts : Font.FontSet) (out : Layout.Out) (target : String) :
    Except String Witness := do
  let #[line] := bodyLines out | throw "expected one body line"
  if line.expand != 0 then throw "probe unexpectedly expands its glyphs"
  let polys := polygonsAt line
  let tip ← arrowTip polys
  let all := shippedBodyGlyphs out
  let glyphs := all.filter fun g => target.toList.contains g.scalar
  unless String.ofList (glyphs.toList.map (·.scalar)) == target do
    throw "target glyph census differs from the probe"
  let ink ← targetInk fonts glyphs
  let some first := glyphs[0]? | throw "target origin is missing"
  let #[anchor] := all.filter (·.scalar == '𝑢') | throw "style witness is missing"
  let some font := fonts.fonts[anchor.face]? | throw "style face is missing"
  let some math := font.math | throw "style face lacks its MATH constants"
  return { tip, tail := shaftTail polys, ink, originX := first.x, glyphs
           fontGap := math.overbarVerticalGap * anchor.size / (font.unitsPerEm : Int) }

structure Probe where
  label : String
  body : String
  target : String
  options : String
  deriving Repr

/-- Invented operands span narrow, shallow, steep and degenerate arrows.
The fourth target contains only a superscript on an empty base: all its ink
is away from its local baseline, exposing a bounds helper that includes zero. -/
def probes : Array Probe := Id.run do
  let shapes := [("narrow", "i"), ("wide", "x+x+x+x+x+x"),
    ("tall", "\\frac{x}{\\frac{x}{x}}"), ("empty", ""),
    ("negative-advance", "x\\!\\!\\!\\!\\!\\!")]
  let styles := [("text", "$", "$"), ("display", "\\[", "\\]"),
    ("script", "$z^{", "}$"), ("scriptscript", "$z^{z^{", "}}$")]
  let targets := [("zero", "0", "0"), ("descender", "g", "𝑔"),
    ("multiple", "0g", "0𝑔"), ("raised-zero", "{}^{0}", "0")]
  let mut result := #[]
  for (shape, operand) in shapes do
    for (style, before, after) in styles do
      for (name, value, target) in targets do
        for options in ["makeroom", "overlap"] do
          result := result.push {
            label := s!"{shape}/{style}/{name}/{options}"
            body := before ++ "u\\cancelto{" ++ value ++ "}{" ++ operand ++ "}v" ++ after
            target, options }
  return result

def layProbe (fonts : Font.FontSet) (p : Probe) : Layout.Out × Array Diag :=
  let (doc, ds) := elabStr (dvDoc ("\\usepackage[" ++ p.options ++ "]{cancel}") p.body)
  (layoutOf fonts doc, ds)

/-- Deliberately translate only the target runs in an already shipped
probe. This supplies positive controls and broken pages for the judge;
it is never used to repair a page before the regression check. -/
private def shiftTarget (out : Layout.Out) (target : String) (dy : Dim.Sp) : Layout.Out :=
  { out with pages := out.pages.map fun page =>
      { page with lines := page.lines.map fun line =>
          { line with segs := line.segs.map fun seg =>
              match seg with
              | .run face color link width glyphs size leading underline raise ground attr =>
                if !glyphs.isEmpty && glyphs.all (fun (_, scalar, _) =>
                    target.toList.contains scalar) then
                  .run face color link width glyphs size leading underline (raise + dy) ground attr
                else seg
              | .gap _ _ | .rule _ _ _ _ | .image _ _ _ | .poly _ _ => seg } } }

/-- Judge controls over real glyph outlines. Translating a target clear
of either side of coordinate zero must translate both bounds. Recentring
an otherwise unchanged page must pass, and moving its target by two sp
must fail in either direction. The horizontal origin is checked exactly. -/
def judgeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in probes.filter (fun p => p.label.startsWith "narrow/text/") do
    let (out, _) := layProbe fonts p
    match measure fonts out p.target with
    | .error e => check ref s!"cancel alignment judge: {p.label}: {e}" false
    | .ok w =>
      for dy in [1 - w.ink.bottom, -1 - w.ink.top] do
        let moved := w.glyphs.map fun g => { g with y := g.y - dy }
        check ref s!"cancel alignment judge: {p.label} translates both tight bounds"
          (targetInk fonts moved == .ok
            { bottom := w.ink.bottom + dy, top := w.ink.top + dy })
      let centred := shiftTarget out p.target (-(w.centreError2 / 2))
      match measure fonts centred p.target with
      | .error e => check ref s!"cancel alignment judge: {p.label} recentered: {e}" false
      | .ok c =>
        check ref s!"cancel alignment judge: {p.label} accepts centred ink"
          (c.centred && c.originGapped)
        for dy in [-2, 2] do
          check ref s!"cancel alignment judge: {p.label} detects a vertical displacement"
            (match measure fonts (shiftTarget centred p.target dy) p.target with
              | .ok broken => !broken.centred && broken.originGapped
              | .error _ => false)
        check ref s!"cancel alignment judge: {p.label} detects a one-sp origin displacement"
          (!({ c with originX := c.originX + 1 } : Witness).originGapped)
  check ref "cancel alignment judge: an absent head cannot certify alignment"
    (match arrowTip #[] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: a zero-area head cannot certify alignment"
    (match arrowTip #[#[(0, 0), (1, 1), (2, 2)]] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: an absent target cannot certify alignment"
    (match targetInk fonts #[] with | .error _ => true | .ok _ => false)

/-- Public suite entry point. Judged entirely on the shipped page and
font outlines; no expected offset comes from `Math.cancelGeom`. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  judgeChecks ref oneFace
  let fonts ← mathSetOf oneFace
  for p in probes do
    let (out, ds) := layProbe fonts p
    check ref s!"cancel alignment: {p.label} needs no recovery"
      (!(ds ++ out.diags).any fun d => d.code == "W0012" || d.code == "W0389")
    match measure fonts out p.target with
    | .error e => check ref s!"cancel alignment: {p.label}: {e}" false
    | .ok w =>
      check ref s!"cancel alignment: {p.label} centres target ink at the arrow tip"
        w.centred
      check ref s!"cancel alignment: {p.label} preserves the font-derived origin gap"
        w.originGapped

end CancelAlignment
