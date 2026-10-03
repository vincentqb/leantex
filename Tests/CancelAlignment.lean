import Tests.Support

open LeanTex.Core

namespace CancelAlignment

open ShippedInk

/-- These probes contain one northeast cancellation arrow. The head's
first vertex is its emitted tip; perpendicular wings may exceed either
coordinate of that tip. Area and ray-shape judges below reject malformed
heads instead of imposing an operand-box constraint on the triangle. -/
def arrowTip (polys : Array (Array (Dim.Sp × Dim.Sp))) :
    Except String (Dim.Sp × Dim.Sp) := do
  let heads := polys.filter (·.size == 3)
  let #[head] := heads | throw "expected one triangular arrowhead"
  let some tip := head[0]? | throw "arrowhead has no vertices"
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

/-- A triangular head retains both wings about the shipped shaft's ray.
The full transverse width is three font rule thicknesses. Symmetry is
judged across and along the ray: cross-products alone cannot detect a
wing sliding along the shaft. Each coordinate's division error is below
one sp, so a wing-to-wing projection errs by at most twice the sum of
the direction coordinates. A merely nonzero triangle is not enough. -/
def headHasWings (polys : Array (Array (Dim.Sp × Dim.Sp))) (rule : Int) : Bool :=
  match arrowTip polys, shaftTail polys, (polys.filter (·.size == 3))[0]? with
  | .ok tip, some tail, some head =>
    let dx := tip.1 - tail.1
    let dy := tip.2 - tail.2
    let cross := fun p : Int × Int => dx * (p.2 - tip.2) - dy * (p.1 - tip.1)
    let a := cross head[1]!
    let b := cross head[2]!
    let along := dx * (head[1]!.1 - head[2]!.1) + dy * (head[1]!.2 - head[2]!.2)
    let length := (Nat.sqrt (dx.natAbs ^ 2 + dy.natAbs ^ 2) : Int)
    let rounding := 2 * (dx.natAbs + dy.natAbs)
    a > 0 && b < 0 && (a + b).natAbs ≤ rounding && along.natAbs ≤ rounding &&
      a - b + rounding ≥ 3 * rule * length
  | _, _, _ => false

/-- Fixed head aspect measured from the shipped shaft and triangle, not
from a geometry constructor. Axial depth is four font rules and transverse
width three. Multiplying projections by the integral diagonal length
avoids another division: each coordinate was rounded below one sp, so the
error is bounded by twice that length times the sum of the ray coordinates.
The assertion requires a positive rule and a nonzero northeast ray. -/
def headHasShape (polys : Array (Array (Dim.Sp × Dim.Sp))) (rule : Int) : Bool :=
  match arrowTip polys, shaftTail polys, (polys.filter (·.size == 3))[0]? with
  | .ok tip, some tail, some head =>
    let dx := tip.1 - tail.1
    let dy := tip.2 - tail.2
    let a := head[1]!
    let b := head[2]!
    let length := (Nat.sqrt (dx.natAbs ^ 2 + dy.natAbs ^ 2) : Int)
    let norm2 := dx * dx + dy * dy
    let depth2 := dx * (2 * tip.1 - a.1 - b.1) + dy * (2 * tip.2 - a.2 - b.2)
    let width := dx * (a.2 - b.2) - dy * (a.1 - b.1)
    let rounding := 2 * length * (dx.natAbs + dy.natAbs)
    rule > 0 && dx ≥ 0 && dy ≥ 0 && length > 0 && headHasWings polys rule &&
      (depth2 * length - 8 * rule * norm2).natAbs ≤ rounding &&
      (width * length - 3 * rule * norm2).natAbs ≤ rounding
  | _, _, _ => false

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
no farther than that gap, and its far edge reaches the tip's coordinate.
This admits either attachment axis without reproducing axis selection. -/
def Witness.clearsTip (w : Witness) : Bool :=
  let x := w.ink.left - w.tip.1
  let y := w.ink.bottom - w.tip.2
  w.fontGap > 0 && ((x == w.fontGap && y ≤ w.fontGap && w.tip.2 ≤ w.ink.top) ||
    (y == w.fontGap && x ≤ w.fontGap && w.tip.1 ≤ w.ink.right))

/-- Positive separation between target outline ink and every shipped mark
hull, including full head wings outside the operand rectangle. A tip gap
alone cannot certify this: the target must also clear the actual marks. -/
def Witness.clearsMarks (w : Witness) (polys : Array (Array (Dim.Sp × Dim.Sp))) : Bool :=
  !polys.isEmpty && polys.all fun pts =>
    (polygonHull pts).any fun mark =>
      mark.right < w.ink.left || w.ink.right < mark.left ||
        mark.top < w.ink.bottom || w.ink.top < mark.bottom

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
is away from its local baseline, exposing a bounds helper that includes zero.
Narrow and tall operands also carry a wide label, so a steep attachment
must accommodate ink extending left of the tip as well as a logical end. -/
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
    let shapeTargets := if shape == "narrow" || shape == "tall" then
        targets ++ [("wide-label", "000000g", "000000𝑔")]
      else targets
    for (style, before, after, ordinaryBefore, ordinaryAfter) in styles do
      for (name, value, target) in shapeTargets do
        for options in ["makeroom", "overlap"] do
          result := result.push {
            label := s!"{shape}/{style}/{name}/{options}"
            body := before ++ "u\\cancelto{" ++ value ++ "}{" ++ operand ++ "}v" ++ after
            ordinary := ordinaryBefore ++ "u" ++ value ++ "v" ++ ordinaryAfter
            target, options }
          if name == "wide-label" then
            let wide := "000000000000g"
            result := result.push {
              label := s!"{shape}/{style}/wide-neighbours/{options}"
              body := before ++ "\\frac{\\frac{a}{a}}{a}u\\cancelto{" ++ wide ++
                "}{" ++ operand ++ "}v\\frac{\\frac{b}{b}}{b}" ++ after
              ordinary := ordinaryBefore ++ "u" ++ wide ++ "v" ++ ordinaryAfter
              target := "000000000000𝑔", options }
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

/-- Actual horizontal construct endpoints come from the adjacent ordinary
source glyphs, never the target's first visible glyph or a polygon's pen. -/
def constructEndpoints (out : Layout.Out) : Except String (Dim.Sp × Dim.Sp) := do
  let all := shippedBodyGlyphs out
  let #[before] := all.filter (·.scalar == '𝑢') | throw "left neighbour is missing"
  let #[after] := all.filter (·.scalar == '𝑣') | throw "right neighbour is missing"
  unless before.page == after.page && before.line == after.line do
    throw "neighbours are on different lines"
  return (before.x + before.advance, after.x)

/-- Read painted rules at their shipped pens, independently of item bounds.
The tall neighbours' fraction bars matter as well as their glyph outlines. -/
def rulesAt (line : Layout.LineOut) : Array InkBounds := Id.run do
  let mut pen := line.x
  let mut result := #[]
  for seg in line.segs do
    match seg with
    | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
    | .image _ w _ => pen := pen + w
    | .rule w t raise _ | .decoration _ w t raise _ =>
      if w != 0 && t != 0 then
        result := result.push ⟨min pen (pen + w), min raise (raise + t) - line.y,
          max pen (pen + w), max raise (raise + t) - line.y⟩
      pen := pen + w
    | .poly _ _ => pure ()
  return result

structure RoomWitness where
  left : Dim.Sp
  right : Dim.Sp
  assembly : Array InkBounds
  before : Array InkBounds
  after : Array InkBounds
  deriving Repr

def RoomWitness.containsInk (r : RoomWitness) : Bool :=
  r.left ≤ r.right && !r.assembly.isEmpty &&
    r.assembly.all (·.inRoom r.left r.right)

def RoomWitness.clearsBefore (r : RoomWitness) : Bool :=
  !r.before.isEmpty && r.assembly.all fun a => r.before.all a.disjoint

def RoomWitness.clearsAfter (r : RoomWitness) : Bool :=
  !r.after.isEmpty && r.assembly.all fun a => r.after.all a.disjoint

/-- Decode the target, marks and neighbouring ink directly from the page.
Neighbour letters are disjoint from the operand and target census. The
fraction bars wholly outside the construct belong to the tall neighbours.
Room is checked on both sides even when only the right neighbour moved. -/
def roomWitness (fonts : Font.FontSet) (out : Layout.Out) (w : Witness) :
    Except String RoomWitness := do
  let #[line] := bodyLines out | throw "expected one body line"
  let (left, right) ← constructEndpoints out
  let marks := (polygonsAt line).filterMap polygonHull
  if marks.isEmpty then throw "cancellation marks are missing"
  let mut before := #[]
  let mut after := #[]
  for g in shippedBodyGlyphs out do
    if g.scalar == '𝑎' || g.scalar == '𝑢' then
      if let some ink ← glyphInk fonts g then before := before.push ink
    if g.scalar == '𝑏' || g.scalar == '𝑣' then
      if let some ink ← glyphInk fonts g then after := after.push ink
  for b in rulesAt line do
    if b.right ≤ left then before := before.push b
    if right ≤ b.left then after := after.push b
  return { left, right, assembly := #[w.ink] ++ marks, before, after }

/-- Read the head and thickness from actual shipped pages over shallow,
steep and ordinary operands, all four math styles and both room policies.
Nonzero rays and positive font rules permit a visible bounded-aspect head;
its perpendicular wings need not fit inside the operand rectangle. -/
def headWingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for (shape, operand) in [("ordinary", "x"), ("wide", "x+x+x+x+x+x"),
      ("very-wide", "x+x+x+x+x+x+x+x+x+x+x+x"),
      ("tall", "\\frac{x}{\\frac{x}{x}}") ] do
    for (style, before, after) in [("text", "$", "$"), ("display", "\\[", "\\]"),
        ("script", "$z^{", "}$"), ("scriptscript", "$z^{z^{", "}}$")] do
      for thick in [false, true] do
        for room in [false, true] do
          let options := (if thick then "thicklines," else "") ++
            (if room then "makeroom" else "overlap")
          let (doc, _) := elabStr (dvDoc ("\\usepackage[" ++ options ++ "]{cancel}")
            (before ++ "u\\cancelto{0}{" ++ operand ++ "}v" ++ after))
          let out := layoutOf fonts doc
          let #[line] := bodyLines out | check ref "cancel wings: missing body line" false
          let #[anchor] := (shippedBodyGlyphs out).filter (·.scalar == '𝑢') |
            check ref "cancel wings: missing style witness" false
          let some font := fonts.fonts[anchor.face]? |
            check ref "cancel wings: missing font" false
          let some math := font.math | check ref "cancel wings: missing MATH table" false
          let rule := math.overbarRuleThickness * anchor.size / (font.unitsPerEm : Int) *
            (if thick then 2 else 1)
          check ref s!"cancel wings: {shape}/{style}/{options} keeps full symmetric wings"
            (headHasWings (polygonsAt line) rule)
          check ref s!"cancel head aspect: {shape}/{style}/{options} keeps four-rule depth and three-rule width"
            (headHasShape (polygonsAt line) rule)
          let .ok w := measure fonts out "0" |
            check ref "cancel head aspect: missing target measurement" false
          check ref s!"cancel head aspect: {shape}/{style}/{options} keeps target ray and font gap"
            (w.alongRay && w.clearsTip && w.clearsMarks (polygonsAt line))
          if room then
            match roomWitness fonts out w with
            | .error e => check ref s!"cancel head aspect: {shape}/{style}/{options}: {e}" false
            | .ok r =>
              check ref s!"cancel head aspect: {shape}/{style}/{options} reserves full wings and target"
                (r.containsInk && r.clearsBefore && r.clearsAfter)

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
  check ref s!"{name} separates actual arrow marks from target ink"
    (w.clearsMarks ((bodyLines out).flatMap polygonsAt))
  check ref s!"{name} ordinary control needs no recovery"
    (!(ds ++ ordinary.diags).any fun d => d.code == "W0012" || d.code == "W0389")
  let readings : Except String (Array ShippedGlyph × Dim.Sp × Dim.Sp) := do
    let all := shippedBodyGlyphs ordinary
    let glyphs := all.filter fun g => p.target.toList.contains g.scalar
    unless String.ofList (glyphs.toList.map (·.scalar)) == p.target do
      throw "ordinary target census differs"
    let some first := glyphs[0]? | throw "ordinary target is missing"
    let some placedFirst := w.glyphs[0]? | throw "placed target is missing"
    let #[startGlyph] := all.filter (·.scalar == '𝑢') | throw "ordinary run start is missing"
    let #[endGlyph] := all.filter (·.scalar == '𝑣') | throw "ordinary run end is missing"
    return (glyphs, placedFirst.x + startGlyph.x + startGlyph.advance - first.x,
      placedFirst.x + endGlyph.x - first.x)
  match readings with
  | .error e => check ref s!"{name}: {e}" false
  | .ok (glyphs, logicalStart, logicalEnd) =>
    check ref s!"{name} preserves relative glyph positions and source advances"
      (relativeSource w.glyphs == relativeSource glyphs)
    if p.options == "makeroom" then
      match roomWitness fonts out w with
      | .error e => check ref s!"{name}: {e}" false
      | .ok r =>
        check ref s!"{name} reserves both logical target endpoints"
          (r.left ≤ min logicalStart logicalEnd && max logicalStart logicalEnd ≤ r.right)
        check ref s!"{name} contains target ink and marks between construct endpoints"
          r.containsInk
        check ref s!"{name} separates target and marks from preceding ink hulls"
          r.clearsBefore
        check ref s!"{name} separates target and marks from following ink hulls"
          r.clearsAfter

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

/-- Every triangle from these vertices has zero area. Unlike a signed
polygon-area sum this cannot hide cancellation between opposite windings,
and duplicate initial vertices do not conceal a later noncollinear one. -/
def collinear (points : Array (Dim.Sp × Dim.Sp)) : Bool :=
  points.all fun a => points.all fun b => points.all fun c =>
    (b.1 - a.1) * (c.2 - a.2) == (b.2 - a.2) * (c.1 - a.1)

/-- Mutate only the fixture's MATH rule constant. A zero-thickness
cancellation still ships its polygon vertices but fills no area. -/
def zeroRuleFonts (fonts : Font.FontSet) : Font.FontSet :=
  { fonts with fonts := fonts.fonts.map fun f =>
      { f with math := f.math.map fun m => { m with overbarRuleThickness := 0 } } }

structure NestedMarkProbe where
  probe : Probe
  reference : Probe
  deriving Repr

/-- The added nested mark is collinear, including when its diagonal hull
has positive width and height. Raised and descender targets keep actual
paint away from the invisible mark's corners. -/
def nestedMarkProbes : Array NestedMarkProbe := Id.run do
  let shapes := [("narrow", "i"), ("wide", "x+x+x+x+x+x"),
    ("tall", "\\frac{x}{\\frac{x}{x}}")]
  let styles := [("text", "$", "$"), ("display", "\\[", "\\]"),
    ("script", "$z^{", "}$"), ("scriptscript", "$z^{z^{", "}}$")]
  let targets := [("raised-zero", "{}^{0}", "0"), ("descender", "0g", "0𝑔")]
  let mut result := #[]
  for (shape, operand) in shapes do
    for (style, before, after) in styles do
      for (name, value, target) in targets do
        for options in ["makeroom", "overlap"] do
          let body (v : String) :=
            before ++ "u\\cancelto{" ++ v ++ "}{" ++ operand ++ "}v" ++ after
          let reference : Probe := {
            label := s!"{shape}/{style}/{name}/{options}"
            body := body value, ordinary := "", target, options }
          result := result.push {
            reference
            probe := { reference with body := body ("\\cancel{" ++ value ++ "}") } }
  return result

/-- The painted target's placement relative to an actual operand glyph.
Using the operand removes page centring and common room padding. With the
zero-rule fixture the outer arrow also has no fill: this paired witness
tests whether invisible marks move ink, not whether that arrow paints. -/
def operandRelativeInk (fonts : Font.FontSet) (out : Layout.Out) (target : String) :
    Except String (InkBounds × Array ShippedGlyph) := do
  let #[line] := bodyLines out | throw "expected one body line"
  if line.expand != 0 then throw "probe unexpectedly expands its glyphs"
  let all := shippedBodyGlyphs out
  let glyphs := all.filter fun g => target.toList.contains g.scalar
  unless String.ofList (glyphs.toList.map (·.scalar)) == target do
    throw "target glyph census differs from the probe"
  let ink ← targetInk fonts glyphs
  let some origin := all.find? (fun g => g.scalar == '𝑖' || g.scalar == '𝑥')
    | throw "operand anchor is missing"
  return (ink.shift (-origin.x) origin.y, glyphs)

/-- Adding a known nonpainting polygon must not move the same painted
target. Source advances remain a separate assertion; no expected placement
comes from a bounds or attachment helper in production. -/
def nestedMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts := zeroRuleFonts (← mathSetOf oneFace)
  for p in nestedMarkProbes do
    let (out, ds) := layProbe fonts p.probe
    let (control, cds) := layProbe fonts p.reference
    let name := s!"cancel nonpainting polygon: {p.probe.label}"
    check ref s!"{name} needs no recovery"
      (!(ds ++ out.diags ++ cds ++ control.diags).any fun d =>
        d.code == "W0012" || d.code == "W0389" || d.severity == .error)
    let polys := (bodyLines out).flatMap polygonsAt
    let controls := (bodyLines control).flatMap polygonsAt
    let diagonal (ps : Array (Dim.Sp × Dim.Sp)) : Bool :=
      (polygonHull ps).any fun b => b.left < b.right && b.bottom < b.top
    check ref s!"{name} adds exactly one nonpainting diagonal with a nonempty hull"
      (controls.size == 2 && polys.size == 3 &&
        controls.all collinear && polys.all collinear &&
        (polys.filter diagonal).size == (controls.filter diagonal).size + 1)
    check ref s!"{name} preserves source and rule census"
      ((shippedBodyGlyphs out).map ShippedGlyph.scalar ==
        (shippedBodyGlyphs control).map ShippedGlyph.scalar &&
        (metricRuleSegs out).map (fun (w, t, _, _) => (w, t)) ==
        (metricRuleSegs control).map (fun (w, t, _, _) => (w, t)))
    match operandRelativeInk fonts out p.probe.target,
        operandRelativeInk fonts control p.reference.target with
    | .ok (ink, glyphs), .ok (reference, source) =>
      check ref s!"{name} preserves relative source positions and advances"
        (relativeSource glyphs == relativeSource source)
      check ref s!"{name} leaves painted target attachment unchanged" (ink == reference)
    | .error e, _ | _, .error e => check ref s!"{name}: {e}" false
    if p.probe.options == "overlap" then
      match neighbourSpan out, neighbourSpan control with
      | .ok span, .ok other =>
        check ref s!"{name} preserves overlapping neighbour advance" (span == other)
      | .error e, _ | _, .error e => check ref s!"{name}: {e}" false

/-- Deliberately translate only target runs on a shipped page. Balanced
gaps leave every other segment's pen position unchanged. Used solely to
test the measurement, never to repair a page before a regression check. -/
private def shiftTarget (out : Layout.Out) (target : String) (dx dy : Dim.Sp) : Layout.Out :=
  { out with pages := out.pages.map fun page =>
      { page with lines := page.lines.map fun line =>
          { line with segs := line.segs.flatMap fun seg =>
              match seg with
              | .run face color link width glyphs size leading decorations raise ground attr =>
                if !glyphs.isEmpty && glyphs.all (fun (_, scalar, _) =>
                    target.toList.contains scalar) then
                  #[.gap dx false,
                    .run face color link width glyphs size leading decorations (raise + dy) ground attr,
                    .gap (-dx) false]
                else #[seg]
              | .gap _ _ | .decoratedGap _ _ _ | .rule _ _ _ _
                | .decoration _ _ _ _ _ | .image _ _ _ | .poly _ _ => #[seg] } } }

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
  for ink in [⟨2, -3, 6, -1⟩, ⟨-3, 2, -1, 6⟩] do
    check ref "cancel alignment judge: a near-edge gap cannot hide a far edge behind the tip"
      (!({ sample with ink } : Witness).clearsTip)
  let room : RoomWitness := {
    left := 0, right := 10, assembly := #[⟨0, 2, 10, 5⟩]
    before := #[⟨-2, 1, 0, 6⟩], after := #[⟨10, 1, 12, 6⟩] }
  check ref "cancel room judge: touching hull boundaries do not overlap interiors"
    (room.containsInk && room.clearsBefore && room.clearsAfter)
  for (dx, before) in [(-1, true), (1, false)] do
    let moved : RoomWitness := { room with assembly := room.assembly.map (fun b => b.shift dx 0) }
    check ref "cancel room judge: one-sp overhang and neighbouring intersection are detected"
      (!moved.containsInk && if before then !moved.clearsBefore else !moved.clearsAfter)
    let high : RoomWitness := { moved with assembly := moved.assembly.map (fun b => b.shift 0 4) }
    check ref "cancel room judge: vertical separation clears neighbours but not overhang"
      (!high.containsInk && high.clearsBefore && high.clearsAfter)
  let shaft : Array (Int × Int) := #[(0, 0), (3, 0), (371, 272), (365, 280), (0, 4)]
  let head : Array (Int × Int) := #[(400, 300), (359, 288), (377, 264)]
  check ref "cancel wing judge: accepts a symmetric head at full rule width"
    (headHasWings #[shaft, head] 10)
  for wing in [1, 2] do
    for (dx, dy) in [(-40, -30), (40, 30)] do
      let slipped := head.modify wing (fun (x, y) => (x + dx, y + dy))
      check ref "cancel wing judge: rejects a wing sliding along the shaft"
        (!headHasWings #[shaft, slipped] 10)
  check ref "cancel head judge: accepts the sourced four-rule by three-rule triangle"
    (headHasShape #[shaft, head] 10)
  check ref "cancel clearance judge: accepts a separated target and rejects missing marks"
    (({ sample with ink := ⟨425, 315, 435, 325⟩ } : Witness).clearsMarks #[shaft, head] &&
      !sample.clearsMarks #[])
  for ink in [⟨400, 300, 410, 310⟩, ⟨377, 283, 380, 286⟩] do
    check ref "cancel clearance judge: rejects touching or overlapping target and head hulls"
      (!({ sample with ink } : Witness).clearsMarks #[shaft, head])
  for (dx, dy) in [(-40, -30), (4, 3)] do
    let stretched := head.modify 1 (fun (x, y) => (x + dx, y + dy))
      |>.modify 2 (fun (x, y) => (x + dx, y + dy))
    check ref "cancel head judge: symmetric wings cannot hide stretched or shortened depth"
      (headHasWings #[shaft, stretched] 10 && !headHasShape #[shaft, stretched] 10)
  let widened := head.modify 1 (fun (x, y) => (x - 9, y + 12))
    |>.modify 2 (fun (x, y) => (x + 9, y - 12))
  check ref "cancel head judge: a minimum width cannot certify excessive width"
    (headHasWings #[shaft, widened] 10 && !headHasShape #[shaft, widened] 10)
  for rule in [0, -10] do
    check ref "cancel head judge: a nonpositive rule cannot certify painted shape"
      (!headHasShape #[shaft, head] rule)
  check ref "cancel alignment judge: an absent head cannot certify alignment"
    (match arrowTip #[] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: a zero-area head cannot certify alignment"
    (match arrowTip #[#[(0, 0), (1, 1), (2, 2)]] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: an absent target cannot certify alignment"
    (match targetInk fonts #[] with | .error _ => true | .ok _ => false)
  check ref "cancel polygon judge: a diagonal can have a hull but no filled area"
    (collinear #[(0, 0), (0, 0), (3, 4), (6, 8), (0, 0)] &&
      polygonHull #[(0, 0), (3, 4), (6, 8)] == some ⟨0, 0, 6, 8⟩)
  check ref "cancel polygon judge: duplicate vertices cannot hide a painted triangle"
    (!collinear #[(0, 0), (0, 0), (3, 4), (6, 7)])

end CancelAlignment

open CancelAlignment in
/-- Public suite entry point. Judged entirely on the shipped page and
font outlines; no expected offset comes from `Math.cancelGeom`. -/
def CancelAlignment.checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  judgeChecks ref oneFace
  headWingChecks ref oneFace
  nonpaintingChecks ref oneFace
  nestedMarkChecks ref oneFace
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
