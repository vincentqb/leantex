import Tests.Support

open LeanTex.Core

namespace CancelAlignment

/-- Outline hull in page coordinates with y pointing upward. Control
points are included; these are measured bounds, not raster extrema.
Neither baseline zero nor logical advance belongs to the hull. -/
structure InkBounds where
  left : Dim.Sp
  bottom : Dim.Sp
  right : Dim.Sp
  top : Dim.Sp
  deriving BEq, Repr

def InkBounds.shift (b : InkBounds) (dx dy : Dim.Sp) : InkBounds :=
  { left := b.left + dx, right := b.right + dx
    bottom := b.bottom + dy, top := b.top + dy }

def outlinePoints : Ink.Cmd → Array (Int × Int)
  | .move x y | .line x y => #[(x, y)]
  | .quad cx cy x y => #[(cx, cy), (x, y)]
  | .cube x₁ y₁ x₂ y₂ x y => #[(x₁, y₁), (x₂, y₂), (x, y)]

def InkBounds.union (a b : InkBounds) : InkBounds :=
  { left := min a.left b.left, bottom := min a.bottom b.bottom
    right := max a.right b.right, top := max a.top b.top }

/-- Decode the shipped glyph independently of the layout's bounds helper.
Every point uses its actual pen position, size and baseline. Missing
outline evidence fails; an empty or zero-area hull contributes no ink. -/
def glyphInk (fonts : Font.FontSet) (g : ShippedGlyph) :
    Except String (Option InkBounds) := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  if font.unitsPerEm == 0 then throw "target face has zero units per em"
  if g.expand != 0 then throw "target glyph unexpectedly expands"
  let some cmds := font.inkSrc.get.cmdsAt g.glyph | throw "target outline is missing"
  let upem : Int := font.unitsPerEm
  let mut bounds : Option InkBounds := none
  for cmd in cmds do
    for (x, y) in outlinePoints cmd do
      let px := g.x + x * g.size / upem
      let py := -g.y + y * g.size / upem
      let point : InkBounds := ⟨px, py, px, py⟩
      bounds := some (match bounds with | none => point | some b => b.union point)
  return bounds.filter fun b => b.left < b.right && b.bottom < b.top

/-- Whether a shipped glyph has outline commands. Empty-outline spaces
still belong to the source census and advance the pen, but paint no ink.
An undecodable outline is a failed measurement rather than an empty one. -/
def glyphPaints (fonts : Font.FontSet) (g : ShippedGlyph) : Except String Bool := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  let some cmds := font.inkSrc.get.cmdsAt g.glyph | throw "target outline is missing"
  return !cmds.isEmpty

/-- Union only the target glyphs' ink, ignoring decoded empty outlines.
Starting from the first painted glyph is essential for an annotation whose
entire visible contents are raised; a space's baseline must not join it. -/
def targetInk (fonts : Font.FontSet) (glyphs : Array ShippedGlyph) :
    Except String InkBounds := do
  let mut bounds : Option InkBounds := none
  for g in glyphs do
    if let some b ← glyphInk fonts g then
      bounds := some (match bounds with
        | none => b
        | some old => old.union b)
  let some ink := bounds | throw "target has no painted glyphs"
  return ink

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
  let #[shaft] := polys.filter (·.size > 3) | none
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

/-- A diagnostic only: the first source glyph may follow a glyphless
prefix, and the attachment may move the whole logical origin left. -/
def Witness.originGap (w : Witness) : Dim.Sp := w.originX - w.tip.1

def Witness.direction (w : Witness) : Option (Dim.Sp × Dim.Sp) := do
  let tail ← w.tail
  let dx := w.tip.1 - tail.1
  let dy := w.tip.2 - tail.2
  if dx ≥ 0 && dy ≥ 0 && dx + dy > 0 then some (dx, dy) else none

def Witness.centreFromTip2 (w : Witness) : Dim.Sp × Dim.Sp :=
  (w.ink.left + w.ink.right - 2 * w.tip.1,
   w.ink.bottom + w.ink.top - 2 * w.tip.2)

def Witness.rayError2 (w : Witness) : Option Int := do
  let (dx, dy) ← w.direction
  let (cx, cy) := w.centreFromTip2
  return dx * cy - dy * cx

/-- Judge the forward ray of the shipped shaft. In doubled centre
coordinates, rounding one free coordinate by at most half an sp gives
the tight cross-product bound `max dx dy`. No placement routine is read. -/
def Witness.alongRay (w : Witness) : Bool :=
  match w.direction with
  | none => false
  | some (dx, dy) =>
    let (cx, cy) := w.centreFromTip2
    dx * cx + dy * cy > 0 &&
      (dx * cy - dy * cx).natAbs ≤ (max dx dy).natAbs

/-- One near ink edge meets the positive font gap exactly; the other is
no farther than that gap. This admits either attachment axis without
reproducing the axis-selection algorithm. -/
def Witness.clearsTip (w : Witness) : Bool :=
  let x := w.ink.left - w.tip.1
  let y := w.ink.bottom - w.tip.2
  w.fontGap > 0 && ((x == w.fontGap && y ≤ w.fontGap) ||
    (y == w.fontGap && x ≤ w.fontGap))

/-- Read a one-line synthetic page. The `u` immediately before the
construct witnesses its actual style size and math face, so the expected
gap is scaled from that font's MATH table rather than guessed from text
size or copied from cancellation geometry. Target scalars are disjoint
from every operand and carrier in `probes`. `originX` records the first
source glyph, including an empty-outline space, for diagnostics only. -/
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
  ordinary : String
  deriving Repr

/-- Invented operands span narrow, shallow, steep and degenerate arrows.
The fourth target contains only a superscript on an empty base: all its ink
is away from its local baseline, exposing a bounds helper that includes zero. -/
def probes : Array Probe := Id.run do
  let shapes := [("narrow", "i"), ("wide", "x+x+x+x+x+x"),
    ("tall", "\\frac{x}{\\frac{x}{x}}"), ("empty", ""),
    ("negative-advance", "x\\!\\!\\!\\!\\!\\!")]
  let styles := [("text", "$", "$", "$z^{", "}$"),
    ("display", "\\[", "\\]", "$", "$"),
    ("script", "$z^{", "}$", "$z^{z^{", "}}$"),
    ("scriptscript", "$z^{z^{", "}}$", "$z^{z^{", "}}$")]
  let targets := [("zero", "0", "0"), ("descender", "g", "𝑔"),
    ("multiple", "0g", "0𝑔"), ("raised-zero", "{}^{0}", "0")]
  let mut result := #[]
  for (shape, operand) in shapes do
    for (style, before, after, ordinaryBefore, ordinaryAfter) in styles do
      for (name, value, target) in targets do
        for options in ["makeroom", "overlap"] do
          result := result.push {
            label := s!"{shape}/{style}/{name}/{options}"
            body := before ++ "u\\cancelto{" ++ value ++ "}{" ++ operand ++ "}v" ++ after
            ordinary := ordinaryBefore ++ "u" ++ value ++ "v" ++ ordinaryAfter
            target, options }
  return result

def layProbe (fonts : Font.FontSet) (p : Probe) : Layout.Out × Array Diag :=
  let (doc, ds) := elabStr (dvDoc ("\\usepackage[" ++ p.options ++ "]{cancel}") p.body)
  (layoutOf fonts doc, ds)

inductive NonpaintingItem where
  | leadingSpace | trailingSpace | emptyRule | anchoredEmptyRule
  deriving BEq, Repr

structure NonpaintingProbe where
  item : NonpaintingItem
  probe : Probe
  reference : Probe
  deriving Repr

/-- Each altered target has exactly the raised zero of its reference.
The added space has source and advance but no outline; the empty fraction
has logical width but its zero-width bar never reaches the shipped page.
Wide and tall operands exercise shallow and steep arrows in every style. -/
def nonpaintingProbes : Array NonpaintingProbe := Id.run do
  let shapes := [("wide", "x+x+x+x+x+x"), ("tall", "\\frac{x}{\\frac{x}{x}}")]
  let styles := [("text", "$", "$", "$z^{", "}$"),
    ("display", "\\[", "\\]", "$", "$"),
    ("script", "$z^{", "}$", "$z^{z^{", "}}$"),
    ("scriptscript", "$z^{z^{", "}}$", "$z^{z^{", "}}$")]
  let variants : List (NonpaintingItem × String × String × String) := [
    (.leadingSpace, "leading-space", "\\text{ }{}^{0}", " 0"),
    (.trailingSpace, "trailing-space", "{}^{0}\\text{ }", "0 "),
    (.emptyRule, "zero-width-rule", "\\frac{}{}{}^{0}", "0"),
    (.anchoredEmptyRule, "space-zero-width-rule", "\\text{ }\\frac{}{}{}^{0}", " 0")]
  let mut result := #[]
  for (shape, operand) in shapes do
    for (style, before, after, ordinaryBefore, ordinaryAfter) in styles do
      for options in ["makeroom", "overlap"] do
        let body (value : String) :=
          before ++ "u\\cancelto{" ++ value ++ "}{" ++ operand ++ "}v" ++ after
        let ordinary (value : String) :=
          ordinaryBefore ++ "u" ++ value ++ "v" ++ ordinaryAfter
        let reference : Probe := {
          label := s!"{shape}/{style}/raised-zero/{options}"
          body := body "{}^{0}", ordinary := ordinary "{}^{0}", target := "0", options }
        for (item, name, value, target) in variants do
          result := result.push {
            item, reference
            probe := { label := s!"{shape}/{style}/{name}/{options}"
                       body := body value, ordinary := ordinary value, target, options } }
  return result

/-- Distance between the two source neighbours. Relative positions remove
display centring and page placement from the construct's advance check. -/
def neighbourSpan (out : Layout.Out) : Except String Dim.Sp := do
  let all := shippedBodyGlyphs out
  let #[before] := all.filter (·.scalar == '𝑢') | throw "left neighbour is missing"
  let #[after] := all.filter (·.scalar == '𝑣') | throw "right neighbour is missing"
  unless before.page == after.page && before.line == after.line do
    throw "neighbours are on different lines"
  return after.x - before.x

/-- Source geometry up to translation, including nonpainting glyphs and
the actual advances used by the shipped pen. -/
def relativeSource (glyphs : Array ShippedGlyph) :
    Array (Nat × Nat × Char × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) :=
  let x := (glyphs[0]?).map (·.x) |>.getD 0
  let y := (glyphs[0]?).map (·.y) |>.getD 0
  glyphs.map fun g => (g.face, g.glyph, g.scalar, g.size, g.advance, g.x - x, g.y - y)

/-- An ordinary rendering at the target's style independently witnesses
its internal source advances. Its following `v` also witnesses the logical
run end, including trailing script space. Translating from a source glyph
does not identify that glyph with the target's logical origin. -/
def sourceAndRoomChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (p : Probe) (out : Layout.Out) (w : Witness) : IO Unit := do
  let (ordinary, ds) := layProbe fonts { p with body := p.ordinary }
  let name := s!"cancel source: {p.label}"
  check ref s!"{name} ordinary control needs no recovery"
    (!(ds ++ ordinary.diags).any fun d => d.code == "W0012" || d.code == "W0389")
  let readings : Except String (Array ShippedGlyph × Dim.Sp × Dim.Sp) := do
    let all := shippedBodyGlyphs ordinary
    let glyphs := all.filter fun g => p.target.toList.contains g.scalar
    unless String.ofList (glyphs.toList.map (·.scalar)) == p.target do
      throw "ordinary target census differs"
    let some first := glyphs[0]? | throw "ordinary target is missing"
    let some placedFirst := w.glyphs[0]? | throw "placed target is missing"
    let #[endGlyph] := all.filter (·.scalar == '𝑣') | throw "ordinary run end is missing"
    let #[next] := (shippedBodyGlyphs out).filter (·.scalar == '𝑣') |
      throw "right neighbour is missing"
    return (glyphs, placedFirst.x + endGlyph.x - first.x, next.x)
  match readings with
  | .error e => check ref s!"{name}: {e}" false
  | .ok (glyphs, logicalEnd, neighbourX) =>
    check ref s!"{name} preserves relative glyph positions and source advances"
      (relativeSource w.glyphs == relativeSource glyphs)
    if p.options == "makeroom" then
      check ref s!"{name} reserves the painted hull and logical run end"
        (neighbourX ≥ max w.ink.right logicalEnd)

/-- Empty outlines and zero-width rules change source spacing, not the
painted hull's attachment. An empty space before the empty fraction makes
that fraction's internal advance observable after the whole target moves. -/
def nonpaintingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in nonpaintingProbes do
    let (out, ds) := layProbe fonts p.probe
    let (control, cds) := layProbe fonts p.reference
    let name := s!"cancel visible ink: {p.probe.label}"
    check ref s!"{name} needs no recovery"
      (!(ds ++ out.diags ++ cds ++ control.diags).any fun d =>
        d.code == "W0012" || d.code == "W0389")
    let readings : Except String (Witness × Witness × Dim.Sp × ShippedGlyph × ShippedGlyph) := do
      let w ← measure fonts out p.probe.target
      let c ← measure fonts control p.reference.target
      let span ← neighbourSpan out
      let controlSpan ← neighbourSpan control
      let #[zero] := w.glyphs.filter (·.scalar == '0') | throw "visible target is missing"
      let #[controlZero] := c.glyphs | throw "reference target is missing"
      return (w, c, span - controlSpan, zero, controlZero)
    match readings with
    | .error e => check ref s!"{name}: {e}" false
    | .ok (w, c, growth, zero, controlZero) =>
      check ref s!"{name} centres visible target ink along the forward arrow ray" w.alongRay
      check ref s!"{name} clears the tip by the font gap" w.clearsTip
      sourceAndRoomChecks ref fonts p.probe out w
      check ref s!"{name} preserves the visible target glyph and size"
        (zero.face == controlZero.face && zero.glyph == controlZero.glyph &&
          zero.size == controlZero.size && zero.advance == controlZero.advance)
      check ref s!"{name} attaches the same painted ink despite invisible spacing"
        (zero.x - w.tip.1 == controlZero.x - c.tip.1 &&
          -zero.y - w.tip.2 == -controlZero.y - c.tip.2)
      let all := shippedBodyGlyphs out
      check ref s!"{name} preserves the remaining source census"
        ((all.filter (·.scalar != ' ')).map ShippedGlyph.scalar ==
          (shippedBodyGlyphs control).map ShippedGlyph.scalar)
      check ref s!"{name} ships no added rule"
        ((metricRuleSegs out).map (fun (width, height, _, _) => (width, height)) ==
          (metricRuleSegs control).map (fun (width, height, _, _) => (width, height)))
      if p.probe.options == "overlap" then
        check ref s!"{name} preserves overlapping neighbour advance" (growth == 0)
      match p.item with
      | .leadingSpace | .trailingSpace | .anchoredEmptyRule =>
        match w.glyphs.filter (·.scalar == ' ') with
        | #[space] =>
          check ref s!"{name} retains a nonpainting space with positive advance"
            (glyphPaints fonts space == .ok false && space.advance > 0)
          check ref s!"{name} does not measure the space baseline as ink"
            (targetInk fonts #[space] == .error "target has no painted glyphs")
          if p.item == .leadingSpace then
            check ref s!"{name} retains the source space before the visible glyph"
              (zero.x - space.x == space.advance)
          if p.item == .anchoredEmptyRule then
            check ref s!"{name} retains the glyphless fraction's internal advance"
              (zero.x - space.x > space.advance)
        | _ => check ref s!"{name} retains exactly one source space" false
      | .emptyRule => pure ()

/-- Deliberately translate only target runs on a shipped page. Balanced
gaps leave every other segment's pen position unchanged. Used solely to
test the measurement, never to repair a page before a regression check. -/
private def shiftTarget (out : Layout.Out) (target : String) (dx dy : Dim.Sp) : Layout.Out :=
  { out with pages := out.pages.map fun page =>
      { page with lines := page.lines.map fun line =>
          { line with segs := line.segs.flatMap fun seg =>
              match seg with
              | .run face color link width glyphs size leading underline raise ground attr =>
                if !glyphs.isEmpty && glyphs.all (fun (_, scalar, _) =>
                    target.toList.contains scalar) then
                  #[.gap dx false,
                    .run face color link width glyphs size leading underline (raise + dy) ground attr,
                    .gap (-dx) false]
                else #[seg]
              | .gap _ _ | .rule _ _ _ _ | .image _ _ _ | .poly _ _ => #[seg] } } }

/-- Real outline translations test all four bounds and the shipped pen
measurement. Small integral witnesses then exercise the exact rounding
boundary, forward direction and clearance independently of placement. -/
def judgeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in probes.filter (fun p => p.label.startsWith "narrow/text/") do
    let (out, _) := layProbe fonts p
    match measure fonts out p.target with
    | .error e => check ref s!"cancel alignment judge: {p.label}: {e}" false
    | .ok w =>
      for (dx, dy) in [(1 - w.ink.left, 1 - w.ink.bottom),
          (-1 - w.ink.right, -1 - w.ink.top)] do
        let moved := w.glyphs.map fun g => { g with x := g.x + dx, y := g.y - dy }
        check ref s!"cancel alignment judge: {p.label} translates all four outline bounds"
          (targetInk fonts moved == .ok (w.ink.shift dx dy))
        check ref s!"cancel alignment judge: {p.label} measures translated shipped runs"
          (match measure fonts (shiftTarget out p.target dx dy) p.target with
            | .error _ => false
            | .ok m => m.ink == w.ink.shift dx dy && m.tip == w.tip && m.tail == w.tail)
  let sample : Witness := {
    tip := (0, 0), tail := some (-4, -3), ink := ⟨2, 2, 6, 5⟩
    originX := 0, fontGap := 2, glyphs := #[] }
  for b in [⟨2, 2, 6, 5⟩, ⟨2, 2, 6, 3⟩] do
    let w := { sample with ink := b }
    check ref "cancel alignment judge: accepts either tight half-sp rounding boundary"
      (w.alongRay && w.clearsTip && w.rayError2.map Int.natAbs == some 4)
  for (dx, dy) in [(-1, 0), (0, 1)] do
    check ref "cancel alignment judge: rejects a one-sp move beyond the rounding boundary"
      (!({ sample with ink := sample.ink.shift dx dy } : Witness).alongRay)
  check ref "cancel alignment judge: rejects the looser sum-of-axes error bound"
    (!({ sample with ink := ⟨2, 2, 4, 4⟩ } : Witness).alongRay)
  check ref "cancel alignment judge: a backwards centre is not on the forward ray"
    (!({ sample with ink := ⟨-5, -4, -3, -2⟩ } : Witness).alongRay)
  for tail in [none, some (0, 0), some (4, 3)] do
    check ref "cancel alignment judge: missing, zero and reversed directions cannot pass"
      (!({ sample with tail } : Witness).alongRay)
  for (tail, ink) in [(some (-4, 0), ⟨2, -1, 6, 1⟩),
      (some (0, -4), ⟨-1, 2, 1, 6⟩)] do
    let w := { sample with tail, ink }
    check ref "cancel alignment judge: axis-aligned forward rays remain defined"
      (w.alongRay && w.clearsTip)
  for gap in [0, 1, 3] do
    check ref "cancel alignment judge: rejects zero, insufficient and excessive clearance"
      (!({ sample with fontGap := gap } : Witness).clearsTip)
  check ref "cancel alignment judge: the other edge may not exceed the gap by even one sp"
    (({ sample with ink := sample.ink.shift 0 (-1) } : Witness).clearsTip &&
      !({ sample with ink := sample.ink.shift 0 1 } : Witness).clearsTip)
  check ref "cancel alignment judge: an absent head cannot certify alignment"
    (match arrowTip #[] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: a zero-area head cannot certify alignment"
    (match arrowTip #[#[(0, 0), (1, 1), (2, 2)]] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: an absent target cannot certify alignment"
    (match targetInk fonts #[] with | .error _ => true | .ok _ => false)

end CancelAlignment

open CancelAlignment in
/-- Public suite entry point. Judged entirely on the shipped page and
font outlines; no expected offset comes from `Math.cancelGeom`. -/
def CancelAlignment.checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  judgeChecks ref oneFace
  nonpaintingChecks ref oneFace
  let fonts ← mathSetOf oneFace
  for p in probes do
    let (out, ds) := layProbe fonts p
    check ref s!"cancel alignment: {p.label} needs no recovery"
      (!(ds ++ out.diags).any fun d => d.code == "W0012" || d.code == "W0389")
    match measure fonts out p.target with
    | .error e => check ref s!"cancel alignment: {p.label}: {e}" false
    | .ok w =>
      check ref s!"cancel alignment: {p.label} centres target ink along the forward arrow ray"
        w.alongRay
      check ref s!"cancel alignment: {p.label} clears the tip by the font gap"
        w.clearsTip
      sourceAndRoomChecks ref fonts p out w
