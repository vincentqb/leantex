module

public import Tests.Support

public section

open LeanTex.Core

namespace CancelAlignment

open ShippedInk

/-- `n` base units: the synthetic witnesses' rounding scale. -/
private def q (n : Int) : Dim.Length := n * Dim.Length.quantum

private def qp (p : Int × Int) : Dim.Length × Dim.Length := (q p.1, q p.2)

private def qb (l b r t : Int) : InkBounds := ⟨q l, q b, q r, q t⟩

/-- The emitted tip of a probe's one northeast cancellation arrow: its head's first vertex. -/
def arrowTip (polys : Array (Array (Dim.Length × Dim.Length))) :
    Except String (Dim.Length × Dim.Length) := do
  let heads := polys.filter (·.size == 3)
  let #[head] := heads | throw "expected one triangular arrowhead"
  let some tip := head[0]? | throw "arrowhead has no vertices"
  let area := head.zipIdx.foldl (fun acc (a, i) =>
    let b := head[(i + 1) % head.size]!
    acc + a.1 * b.2 - a.2 * b.1) (0 : Int)
  if area == 0 then throw "arrowhead has no painted area"
  return tip

/-- The start of the shipped shaft's centre line, the midpoint of its first and last vertices; a
head-only arrow reports none. -/
def shaftTail (polys : Array (Array (Dim.Length × Dim.Length))) :
    Option (Dim.Length × Dim.Length) := do
  let #[shaft] := polys.filter (·.size == 4) | none
  let a ← shaft[0]?
  let b ← shaft[3]?
  some ((a.1 + b.1) / (2 : Int), (a.2 + b.2) / (2 : Int))

/-- The head measured from the shipped shaft and triangle: line10's depth and back, its wings
symmetric across the shaft's ray, within the rounding bound. -/
def headHasShape (polys : Array (Array (Dim.Length × Dim.Length))) : Bool :=
  match arrowTip polys, shaftTail polys, (polys.filter (·.size == 3))[0]? with
  | .ok tip, some tail, some head =>
    let dx := (tip.1 - tail.1).units
    let dy := (tip.2 - tail.2).units
    let a := head[1]!
    let b := head[2]!
    let length := (Nat.sqrt (dx.natAbs ^ 2 + dy.natAbs ^ 2) : Int)
    let norm2 := dx * dx + dy * dy
    let cross := fun p : Dim.Length × Dim.Length =>
      dx * (p.2 - tip.2).units - dy * (p.1 - tip.1).units
    let depth2 := dx * (2 * tip.1 - a.1 - b.1).units + dy * (2 * tip.2 - a.2 - b.2).units
    let rounding := 4 * length * (dx.natAbs + dy.natAbs)
    let width := (cross a - cross b).natAbs
    dx > 0 && dy > 0 && length > 0 && cross a * cross b < 0 &&
      (cross a + cross b).natAbs ≤ rounding &&
      (depth2 * length - 2 * Math.cancelHeadDepth * norm2).natAbs ≤ rounding &&
      ((width : Int) * length - 2 * Math.cancelHeadHalf * norm2).natAbs ≤ rounding
  | _, _, _ => false

structure Witness where
  tip : Dim.Length × Dim.Length
  tail : Option (Dim.Length × Dim.Length)
  ink : InkBounds
  glyphs : Array ShippedGlyph
  deriving Repr

/-- The kerns cancel.sty sets a value at past the tip, one per slope class. -/
def valueKerns : List Int := [13, 8, 3, -12, -7, -2].map Math.cancelTenths

/-- The visible target's first glyph stands one of cancel.sty's kerns past the tip, to the base
unit. -/
def Witness.kernedFromTip (w : Witness) : Bool :=
  match w.glyphs[0]? with
  | some g => valueKerns.any fun k =>
    (g.x - w.tip.1 - Dim.Length.ofUnits k).abs ≤ 2 * Dim.Length.quantum
  | none => false

/-- Positive separation between the target's outline ink and every shipped mark hull, head wings
included. -/
def Witness.clearsMarks (w : Witness) (polys : Array (Array (Dim.Length × Dim.Length))) : Bool :=
  !polys.isEmpty && polys.all fun pts =>
    (polygonHull pts).any fun mark =>
      mark.right < w.ink.left || w.ink.right < mark.left ||
        mark.top < w.ink.bottom || w.ink.top < mark.bottom

/-- Read a one-line synthetic page: the arrow's tip and tail and the target's glyphs and ink. -/
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
  return { tip, tail := shaftTail polys, ink, glyphs }

structure Probe where
  label : String
  body : String
  target : String
  options : String
  ordinary : String
  deriving Repr

/-- Invented operands spanning narrow, shallow, steep and degenerate arrows, with wide labels and a
superscript on an empty base. -/
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

/-- Targets each altered by a nonpainting part (an outline-less space, an empty fraction) beside
their reference. -/
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

/-- The distance between the two source neighbours, free of display centring and page placement. -/
def neighbourSpan (out : Layout.Out) : Except String Dim.Length := do
  let all := shippedBodyGlyphs out
  let #[before] := all.filter (·.scalar == '𝑢') | throw "left neighbour is missing"
  let #[after] := all.filter (·.scalar == '𝑣') | throw "right neighbour is missing"
  unless before.page == after.page && before.line == after.line do
    throw "neighbours are on different lines"
  return after.x - before.x

/-- The construct's horizontal endpoints, from the adjacent ordinary source glyphs. -/
def constructEndpoints (out : Layout.Out) : Except String (Dim.Length × Dim.Length) := do
  let all := shippedBodyGlyphs out
  let #[before] := all.filter (·.scalar == '𝑢') | throw "left neighbour is missing"
  let #[after] := all.filter (·.scalar == '𝑣') | throw "right neighbour is missing"
  unless before.page == after.page && before.line == after.line do
    throw "neighbours are on different lines"
  return (before.x + before.advance, after.x)

structure RoomWitness where
  left : Dim.Length
  right : Dim.Length
  target : InkBounds
  tail : Option (Dim.Length × Dim.Length)
  deriving Repr

/-- The value's ink stands between the construct's endpoints and the shaft starts at or after
the first, as cancel.sty's box makes room. -/
def RoomWitness.containsTarget (r : RoomWitness) : Bool :=
  r.left ≤ r.right && r.target.inRoom r.left r.right &&
    r.tail.all fun t => r.left ≤ t.1 + Dim.Length.quantum

/-- The target and the shaft's tail against the construct's endpoints. -/
def roomWitness (_fonts : Font.FontSet) (out : Layout.Out) (w : Witness) :
    Except String RoomWitness := do
  let (left, right) ← constructEndpoints out
  return { left, right, target := w.ink, tail := w.tail }

/-- Over shallow, steep and ordinary operands, all four math styles and both room policies, the
shipped head has line10's shape and the target its kern. -/
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
          check ref s!"cancel head aspect: {shape}/{style}/{options} keeps line10's depth, back and wings"
            (headHasShape (polygonsAt line))
          let .ok w := measure fonts out "0" |
            check ref "cancel head aspect: missing target measurement" false
          check ref s!"cancel head aspect: {shape}/{style}/{options} kerns the target past the tip"
            (w.kernedFromTip && w.clearsMarks (polygonsAt line))
          if room then
            match roomWitness fonts out w with
            | .error e => check ref s!"cancel head aspect: {shape}/{style}/{options}: {e}" false
            | .ok r =>
              check ref s!"cancel head aspect: {shape}/{style}/{options} reserves the target"
                r.containsTarget

/-- Source geometry up to translation, nonpainting glyphs and shipped advances included. -/
def relativeSource (glyphs : Array ShippedGlyph) :
    Array (Nat × Nat × Char × Dim.Length × Dim.Length × Dim.Length × Dim.Length) :=
  let x := (glyphs[0]?).map (·.x) |>.getD 0
  let y := (glyphs[0]?).map (·.y) |>.getD 0
  glyphs.map fun g => (g.face, g.glyph, g.scalar, g.size, g.advance, g.x - x, g.y - y)

/-- An ordinary rendering at the target's style witnesses its source advances and logical run end,
and the cancellation reserves its room. -/
def sourceAndRoomChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (p : Probe) (out : Layout.Out) (w : Witness) : IO Unit := do
  let (ordinary, ds) := layProbe fonts { p with body := p.ordinary }
  let name := s!"cancel source: {p.label}"
  -- A descender may dip to the head's hull, as cancel.sty's superscript lets it.
  if !p.target.contains '𝑔' then
    check ref s!"{name} separates actual arrow marks from target ink"
      (w.clearsMarks ((bodyLines out).flatMap polygonsAt))
  check ref s!"{name} ordinary control needs no recovery"
    (!(ds ++ ordinary.diags).any fun d => d.code == "W0012" || d.code == "W0389")
  let readings : Except String (Array ShippedGlyph × Dim.Length × Dim.Length) := do
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
        check ref s!"{name} contains target ink and the shaft's start between construct endpoints"
          r.containsTarget

/-- Empty outlines and zero-width rules change source spacing, never the painted hull's attachment. -/
def nonpaintingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in nonpaintingProbes do
    let (out, ds) := layProbe fonts p.probe
    let (control, cds) := layProbe fonts p.reference
    let name := s!"cancel visible ink: {p.probe.label}"
    check ref s!"{name} needs no recovery"
      (!(ds ++ out.diags ++ cds ++ control.diags).any fun d =>
        d.code == "W0012" || d.code == "W0389")
    let (ordinary, _) := layProbe fonts { p.probe with body := p.probe.ordinary }
    let (ordinaryControl, _) := layProbe fonts { p.reference with body := p.reference.ordinary }
    -- Where the visible glyph stands in the value's own list, from its ordinary rendering.
    let inList (o : Layout.Out) : Except String (Dim.Length × Dim.Length) := do
      let all := shippedBodyGlyphs o
      let #[u] := all.filter (·.scalar == '𝑢') | throw "ordinary run start is missing"
      let #[zero] := all.filter (·.scalar == '0') | throw "ordinary target is missing"
      return (zero.x - u.x - u.advance, u.y - zero.y)
    let readings : Except String
        (Witness × Witness × Dim.Length × ShippedGlyph × ShippedGlyph ×
          (Dim.Length × Dim.Length) × (Dim.Length × Dim.Length)) := do
      let w ← measure fonts out p.probe.target
      let c ← measure fonts control p.reference.target
      let span ← neighbourSpan out
      let controlSpan ← neighbourSpan control
      let #[zero] := w.glyphs.filter (·.scalar == '0') | throw "visible target is missing"
      let #[controlZero] := c.glyphs | throw "reference target is missing"
      return (w, c, span - controlSpan, zero, controlZero, ← inList ordinary,
        ← inList ordinaryControl)
    match readings with
    | .error e => check ref s!"{name}: {e}" false
    | .ok (w, c, growth, zero, controlZero, at_, controlAt) =>
      sourceAndRoomChecks ref fonts p.probe out w
      check ref s!"{name} preserves the visible target glyph and size"
        (zero.face == controlZero.face && zero.glyph == controlZero.glyph &&
          zero.size == controlZero.size && zero.advance == controlZero.advance)
      -- Two base units of rounding, one per laid side.
      let slack := 2 * Dim.Length.quantum
      check ref s!"{name} moves the visible glyph from the tip as its own list moves it"
        ((zero.x - w.tip.1 - (controlZero.x - c.tip.1) - (at_.1 - controlAt.1)).abs ≤ slack &&
          (-zero.y - w.tip.2 - (-controlZero.y - c.tip.2) - (at_.2 - controlAt.2)).abs ≤ slack)
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

/-- Whether every triangle from these vertices has zero area, which no opposite windings can hide. -/
def collinear (points : Array (Dim.Length × Dim.Length)) : Bool :=
  points.all fun a => points.all fun b => points.all fun c =>
    (b.1 - a.1) * (c.2 - a.2) == (b.2 - a.2) * (c.1 - a.1)

structure NestedMarkProbe where
  probe : Probe
  reference : Probe
  deriving Repr

/-- Targets with an added nested strike over the value. -/
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

/-- The painted target's placement relative to an operand glyph, free of page centring and room
padding. -/
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

/-- A strike nested over the value adds its one band and, overlapping, moves nothing. -/
def nestedMarkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in nestedMarkProbes do
    let (out, ds) := layProbe fonts p.probe
    let (control, cds) := layProbe fonts p.reference
    let name := s!"cancel nonpainting polygon: {p.probe.label}"
    check ref s!"{name} needs no recovery"
      (!(ds ++ out.diags ++ cds ++ control.diags).any fun d =>
        d.code == "W0012" || d.code == "W0389" || d.severity == .error)
    let polys := (bodyLines out).flatMap polygonsAt
    let controls := (bodyLines control).flatMap polygonsAt
    check ref s!"{name} adds exactly one band"
      (controls.size == 2 && polys.size == 3 &&
        (polys.filter (·.size == 4)).size == (controls.filter (·.size == 4)).size + 1)
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
      if p.probe.options == "overlap" then
        check ref s!"{name} leaves painted target attachment unchanged" (ink == reference)
    | .error e, _ | _, .error e => check ref s!"{name}: {e}" false
    if p.probe.options == "overlap" then
      match neighbourSpan out, neighbourSpan control with
      | .ok span, .ok other =>
        check ref s!"{name} preserves overlapping neighbour advance" (span == other)
      | .error e, _ | _, .error e => check ref s!"{name}: {e}" false

/-- Translate only the target's runs on a shipped page, to test the measurement. -/
private def shiftTarget (out : Layout.Out) (target : String) (dx dy : Dim.Length) : Layout.Out :=
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
              | .gap _ _ | .decoratedGap _ _ _ | .rule _ _ _ _ _
                | .decoration _ _ _ _ _ _ | .image _ _ _ _ _ _ | .poly _ _ => #[seg] } } }

/-- Outline translations and small integral witnesses test the judges' bounds, rounding, direction
and clearance. -/
def judgeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  for p in probes.filter (fun p => p.label.startsWith "narrow/text/") do
    let (out, _) := layProbe fonts p
    match measure fonts out p.target with
    | .error e => check ref s!"cancel alignment judge: {p.label}: {e}" false
    | .ok w =>
      for (dx, dy) in [(q 1 - w.ink.left, q 1 - w.ink.bottom),
          (q (-1) - w.ink.right, q (-1) - w.ink.top)] do
        let moved := w.glyphs.map fun g => { g with x := g.x + dx, y := g.y - dy }
        check ref s!"cancel alignment judge: {p.label} translates all four outline bounds"
          (targetInk fonts moved == .ok (w.ink.shift dx dy))
        check ref s!"cancel alignment judge: {p.label} measures translated shipped runs"
          (match measure fonts (shiftTarget out p.target dx dy) p.target with
            | .error _ => false
            | .ok m => m.ink == w.ink.shift dx dy && m.tip == w.tip && m.tail == w.tail)
  let glyph : ShippedGlyph :=
    { (default : ShippedGlyph) with scalar := '0', x := Dim.Length.ofUnits (Math.cancelTenths 13) }
  let sample : Witness := {
    tip := (0, 0), tail := some (qp (-4, -1)), ink := qb 2 2 6 5, glyphs := #[glyph] }
  check ref "cancel kern judge: accepts cancel.sty's kern past the tip"
    sample.kernedFromTip
  for dx in [(-3 : Int), 3, Math.cancelPt] do
    check ref "cancel kern judge: rejects a glyph off every kern"
      (!({ sample with glyphs := #[{ glyph with x := glyph.x + q dx }] } : Witness).kernedFromTip)
  check ref "cancel kern judge: a target without glyphs cannot pass"
    (!({ sample with glyphs := #[] } : Witness).kernedFromTip)
  let room : RoomWitness := { left := 0, right := q 10, target := qb 2 2 10 5, tail := some (0, 0) }
  check ref "cancel room judge: a target and tail inside the endpoints pass"
    room.containsTarget
  check ref "cancel room judge: a target past the end or a tail before the start fails"
    (!({ room with target := qb 2 2 11 5 } : RoomWitness).containsTarget &&
      !({ room with tail := some (q (-2), 0) } : RoomWitness).containsTarget)
  -- An invented arrow at slope 1/4, its head line10's depth and back.
  let len := Math.cancelPt * 40
  let l := Math.cancelLength len (len / 4)
  let tip : Int × Int := (len, len / 4)
  let back : Int × Int := (len - len * Math.cancelHeadDepth / l, len / 4 - len / 4 * Math.cancelHeadDepth / l)
  let wing (s : Int) : Int × Int :=
    (back.1 - s * (len / 4) * Math.cancelHeadHalf / l, back.2 + s * len * Math.cancelHeadHalf / l)
  let head : Array (Dim.Length × Dim.Length) := #[tip, wing 1, wing (-1)].map
    fun (x, y) => (Dim.Length.ofUnits x, Dim.Length.ofUnits y)
  let shaft : Array (Dim.Length × Dim.Length) := #[(0, 10), (back.1, back.2 + 10),
    (back.1, back.2 - 10), (0, -10)].map fun (x, y) => (Dim.Length.ofUnits x, Dim.Length.ofUnits y)
  check ref "cancel head judge: accepts line10's head on its shaft"
    (headHasShape #[shaft, head])
  for (dx, dy) in [((-40000 : Int), (-10000 : Int)), (40000, 10000)] do
    let slipped := head.modify 1 (fun (x, y) => (x + q dx, y + q dy))
    check ref "cancel head judge: rejects a wing sliding along the shaft"
      (!headHasShape #[shaft, slipped])
  let widened := head.modify 1 (fun (x, y) => (x - q 9000, y + q 36000))
    |>.modify 2 (fun (x, y) => (x + q 9000, y - q 36000))
  check ref "cancel head judge: rejects a wider back"
    (!headHasShape #[shaft, widened])
  check ref "cancel clearance judge: accepts a separated target and rejects missing marks"
    (({ sample with ink := ⟨q (len + 1000000), q 0, q (len + 2000000), q 1000000⟩ } : Witness).clearsMarks
        #[shaft, head] && !sample.clearsMarks #[])
  check ref "cancel clearance judge: rejects a target touching the head's hull"
    (!({ sample with ink := ⟨q (len - 10), q (len / 4 - 10), q (len + 10), q (len / 4 + 10)⟩ } :
      Witness).clearsMarks #[shaft, head])
  check ref "cancel alignment judge: an absent head cannot certify alignment"
    (match arrowTip #[] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: a zero-area head cannot certify alignment"
    (match arrowTip #[#[(0, 0), (1, 1), (2, 2)].map qp] with | .error _ => true | .ok _ => false)
  check ref "cancel alignment judge: an absent target cannot certify alignment"
    (match targetInk fonts #[] with | .error _ => true | .ok _ => false)
  check ref "cancel polygon judge: a diagonal can have a hull but no filled area"
    (collinear (#[(0, 0), (0, 0), (3, 4), (6, 8), (0, 0)].map qp) &&
      polygonHull (#[(0, 0), (3, 4), (6, 8)].map qp) == some (qb 0 0 6 8))
  check ref "cancel polygon judge: duplicate vertices cannot hide a painted triangle"
    (!collinear (#[(0, 0), (0, 0), (3, 4), (6, 7)].map qp))

end CancelAlignment

open CancelAlignment in
/-- Cancellation alignment judged on the shipped page and font outlines alone, the target kerned
past the arrow's tip. -/
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
      check ref s!"cancel alignment: {p.label} kerns the target past the tip as cancel.sty does"
        (p.label.contains "raised" || w.kernedFromTip)
      sourceAndRoomChecks ref fonts p out w
