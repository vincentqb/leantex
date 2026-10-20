module

public import Tests.CancelMetric

public section

open LeanTex.Core

namespace CancelReview

private def optionalEm (em : Int) (s : String) : Option Int :=
  if s.isEmpty then some 0 else readEm em s

private def margin (em : Int) (logical physical : String) (node : Html.Node) : Option Int :=
  let own := nodeCss logical node
  optionalEm em (if own.isEmpty then nodeCss physical node else own)

private def margins (em : Int) (node : Html.Node) : Option (Int × Int) := do
  let left ← margin em "margin-inline-start" "margin-left" node
  let right ← margin em "margin-inline-end" "margin-right" node
  return (left, right)

private def near (em a b : Int) : Bool :=
  (a - b).natAbs ≤ ((em + 1999999) / 2000000 + 2).toNat

/-- The advance a node gives the following atom: its width clamped at zero plus its CSS margins. -/
private def advance (em : Int) (node : Html.Node) : Option Int := do
  let w ← readEm em (nodeAttr "width" node)
  let (left, right) ← margins em node
  return max 0 w + left + right

private structure Offset where
  chromiumX : Int
  firefoxX : Int
  y : Int
  advance : Int

/-- A node's placement as Chromium reads it (negative lspace clamped) and as Firefox does, none
under CSS positioning. -/
private def offset (em : Int) (node : Html.Node) : Option Offset := do
  if ["position", "left", "top", "transform"].any (fun key => !(nodeCss key node).isEmpty) then
    none
  else do
    let ls ← optionalEm em (nodeAttr "lspace" node)
    let y ← optionalEm em (nodeAttr "voffset" node)
    let (left, _) ← margins em node
    let a ← advance em node
    return { chromiumX := max 0 ls + left, firefoxX := ls + left, y, advance := a }

private structure Witness where
  em : Int
  origin : Int
  baseline : Int
  nativeAdvance : Int
  line : Layout.LineOut
  lineExtents : Array Int
  flowBaselines : Array Int
  glyphs : Array ShippedGlyph
  node : Html.Node

private def docWitness (fonts : Font.FontSet) (doc : Ir.Doc) (ds : Array Diag) :
    Except String Witness := do
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fonts doc geom
  let (_, nodes, hds) := HtmlDoc.emitTree {
    fonts := some fonts
    cancelMetric := fun measures ss st spec body value =>
      Layout.cancelMetric geom fonts ss st spec body value (some measures)
    mathEm := fun measures ss st => Layout.mathEm geom fonts ss st (some measures)
    mathTextEm := fun measures ss st => Layout.mathTextEm geom fonts ss st (some measures) } doc
  if (ds ++ out.diags ++ hds).any (fun d =>
      d.code == "W0012" || d.code == "W0301" || d.code == "W0302") then
    throw "source unexpectedly refused"
  let #[line] := bodyLines out | throw "expected one native body line"
  let font := fonts.body
  let scale (u : Int) := u * geom.fontSize / font.unitsPerEm
  let box := Layout.lineExtent fonts geom.fontSize (scale font.ascent)
    (scale font.capHeight) (scale (-font.descent)) geom.leading line.size line.segs
  let flowDoc : Ir.Doc := { doc with
    body := #[.para #[.text "a"]] ++ doc.body ++ #[.para #[.text "b"]] }
  let flow := layoutOf fonts flowDoc geom
  if flow.pages.size != 1 then throw "expected one native flow page"
  let #[above, middle, below] := bodyLines flow | throw "expected three native flow lines"
  let glyphs := shippedBodyGlyphs out
  let #[anchor] := glyphs.filter (·.scalar == '𝑢') | throw "missing native em witness"
  let (left, right) ← CancelAlignment.constructEndpoints out
  let #[node] := (elemNodesList (· == "mpadded") #[] nodes.toList).filter
    (nodeAttr "data-cancel-metric" · == "measured") | throw "missing measured HTML construct"
  return {
    em := anchor.size.units, origin := left.units, baseline := anchor.y.units
    nativeAdvance := (right - left).units, line
    lineExtents := #[box.above.units, box.below.units, box.inkAbove.units, box.inkBelow.units]
    flowBaselines := #[(middle.y - above.y).units, (below.y - middle.y).units]
    glyphs, node }

private def witness (fonts : Font.FontSet) (options before body target after : String) :
    Except String Witness :=
  let source := dvDoc ("\\usepackage[" ++ options ++ "]{cancel}")
    (before ++ "u\\cancelto{" ++ target ++ "}{" ++ body ++ "}v" ++ after)
  let (doc, ds) := elabStr source
  docWitness fonts doc ds

private def zeroExtentWitness (fonts : Font.FontSet) (room : Bool) (value : Math.MList) :
    Except String Witness := do
  let some body := CancelMetric.formula fonts "x" | throw "missing plain body"
  let atom (c : Char) : Math.MItem := .atom .ord (.sym c) .nil .nil false
  let formula := Math.MList.ofList [
    atom '𝑢', .atom .ord (.cancel .to { room } value body) .nil .nil false, atom '𝑣']
  let (base, ds) := elabStr (dvDoc "" "$x$")
  let doc : Ir.Doc := { base with body := #[.para #[.formula false "" formula]] }
  docWitness fonts doc ds

private def advanceAgrees (w : Witness) : Bool :=
  (advance w.em w.node).any (near w.em · w.nativeAdvance)

/-- The value's placement after the operand's measured advance, as both browsers read it. -/
private def targetAgrees (w : Witness) : Bool := (do
  let body ← (nodeKids w.node)[1]?
  let value ← (nodeKids w.node)[2]?
  let pen ← offset w.em body
  let placement ← offset w.em value
  let first ← w.glyphs.find? (fun (g : ShippedGlyph) => g.scalar == '0')
  return near w.em (pen.advance + placement.chromiumX) (first.x.units - w.origin) &&
    near w.em (pen.advance + placement.firefoxX) (first.x.units - w.origin) &&
    near w.em placement.y (w.baseline - first.y.units)).getD false

/-- The top and bottom of the shipped line's one zero-width math strut, cancellation's reservation. -/
private def reservation (w : Witness) : Option (Int × Int) := do
  let struts := w.line.segs.filterMap fun seg => match seg with
    | .run _ _ _ width glyphs size metrics _ raise _ _ =>
      if width == 0 && glyphs.isEmpty && size == Dim.Length.quantum then
        metrics.math.map fun m =>
          let delta := raise.units - (w.line.y.units - w.baseline)
          (m.top.units + delta, m.bottom.units + delta)
      else none
    | _ => none
  let #[bounds] := struts | none
  return bounds

private def htmlReservation (w : Witness) : Option (Int × Int) := do
  let h ← readEm w.em (nodeAttr "height" w.node)
  let d ← readEm w.em (nodeAttr "depth" w.node)
  return (h, -d)

private def reachAgrees (w : Witness) : Bool := (do
  let (top, bot) ← reservation w
  let (h, bot') ← htmlReservation w
  return near w.em h top && near w.em bot' bot).getD false

/-- The script size and the width `source` occupies between two superscript letters, laid out
without cancellation. -/
private def targetSpacePen (fonts : Font.FontSet) (source : String) :
    Except String (Int × Int) := do
  let (doc, ds) := elabStr (dvDoc "" ("$z^{u" ++ source ++ "v}$"))
  let out := layoutOf fonts doc (Layout.Geom.ofPage doc.page)
  if (ds ++ out.diags).any (fun d =>
      d.code == "W0012" || d.code == "W0301" || d.code == "W0302") then
    throw "plain spacing control unexpectedly refused"
  let #[anchor] := (shippedBodyGlyphs out).filter (·.scalar == '𝑢') |
    throw "missing plain script em witness"
  let (left, right) ← CancelAlignment.constructEndpoints out
  return (anchor.size.units, (right - left).units)

private def targetSpaceAdvance (w : Witness) : Option (Int × Int) := do
  let placed ← (nodeKids w.node)[2]?
  let styled ← (nodeKids placed)[0]?
  let em ← readEm w.em (nodeCss "font-size" styled)
  let spaces := elemNodesOne (· == "mspace") #[] styled
  if spaces.isEmpty then none else do
    let mut total : Int := 0
    for node in spaces do
      total := total + (← advance em node)
    return (em, total)

private def readerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let placed (lspace style : String) := Html.Node.elem "mpadded"
    #[("width", "0"), ("height", "0"), ("depth", "0"),
      ("lspace", lspace), ("voffset", "1em"), ("style", style)] #[]
  let correct := offset 1000000 (placed "0"
    "margin-left: -2em; margin-right: 2em")
  check ref "cancel reader: balanced signed margins preserve zero advance"
    (correct.any fun r => r.chromiumX == -2000000 && r.firefoxX == -2000000 &&
      r.y == 1000000 && r.advance == 0)
  let clamped := offset 1000000 (placed "-2em" "")
  check ref "cancel reader: negative lspace exposes browser disagreement"
    (clamped.any fun r => r.chromiumX == 0 && r.firefoxX == -2000000)
  let unbalanced := offset 1000000 (placed "0" "margin-left: -2em")
  check ref "cancel reader: missing balancing margin leaks advance"
    (unbalanced.any fun r => r.advance == -2000000)
  let signed := Html.Node.elem "mpadded"
    #[("width", "0"), ("style", "margin-inline-end: -0.5em")] #[]
  let clampedWidth := Html.Node.elem "mpadded" #[("width", "-0.5em")] #[]
  check ref "cancel reader: signed CSS advance survives nonnegative width"
    (advance 1000000 signed == some (-500000))
  check ref "cancel reader: negative width alone loses signed advance"
    (advance 1000000 clampedWidth == some 0)

end CancelReview

open CancelReview in
/-- Cancellation's MathML agrees with the native layout: neighbour pens, target baselines,
reservation struts and line spacing. -/
def CancelReview.checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  readerChecks ref
  for options in ["overlap", "makeroom"] do
    let empty := (witness fonts options "$" "x" "" "$").toOption
    check ref s!"cancel spacing {options}: empty reservation control" empty.isSome
    for (style, before, after) in [
        ("text", "$", "$"), ("script", "$z^{", "}$")] do
      for body in ["x", "x\\!\\!\\!\\!\\!\\!", "\\!\\!x\\!\\!\\!\\!"] do
        let name := s!"{options}/{style}/{body}"
        match witness fonts options before body "0" after with
        | .error err => check ref s!"cancel signed {name}: {err}" false
        | .ok w =>
          check ref s!"cancel signed {name}: native neighbour advance" (advanceAgrees w)
          check ref s!"cancel signed {name}: portable target placement" (targetAgrees w)
          if options == "overlap" && body != "x" then
            check ref s!"cancel signed {name}: witness is negative" (w.nativeAdvance < 0)
      let body := "\\frac{x}{\\frac{x}{x}}"
      match witness fonts options before body "000000000000g" after with
      | .error err => check ref s!"cancel wide {options}/{style}: {err}" false
      | .ok w =>
        check ref s!"cancel wide {options}/{style}: portable target placement"
          (targetAgrees w)
        check ref s!"cancel wide {options}/{style}: native neighbour advance"
          (advanceAgrees w)
    for target in ["", "\\color{red}", "{}", "\\,", "\\!", "\\color{red}\\,"] do
      match witness fonts options "$" "x" target "$" with
      | .error err => check ref s!"cancel empty {options}/{target}: {err}" false
      | .ok w =>
        check ref s!"cancel empty {options}/{target}: native reservation struts"
          (reachAgrees w)
        check ref s!"cancel empty {options}/{target}: native advance retained"
          (advanceAgrees w)
        check ref s!"cancel empty {options}/{target}: empty to-value node retained"
          ((nodeKids w.node).size == 3 &&
            (MathMl.nodeChars #[] ((nodeKids w.node)[2]!)).isEmpty)
        if ["\\,", "\\!", "\\color{red}\\,"].contains target then
          check ref s!"cancel spacing {options}/{target}: native height ignores spacing"
            (empty.any fun e => (reservation e).any fun expected =>
              reservation w == some expected)
          check ref s!"cancel spacing {options}/{target}: native line extent ignores spacing"
            (empty.any fun e => w.lineExtents == e.lineExtents)
          check ref s!"cancel spacing {options}/{target}: native line baselines ignore spacing"
            (empty.any fun e => w.flowBaselines == e.flowBaselines)
          check ref s!"cancel spacing {options}/{target}: HTML height ignores spacing"
            (empty.any fun e => (htmlReservation e).any fun expected =>
              (htmlReservation w).any fun actual =>
                near w.em actual.1 expected.1 && near w.em actual.2 expected.2)
          match targetSpacePen fonts target with
          | .error err => check ref s!"cancel spacing {options}/{target}: {err}" false
          | .ok (em, expected) =>
            check ref s!"cancel spacing {options}/{target}: signed target advance retained"
              ((targetSpaceAdvance w).any fun (actualEm, actual) =>
                near w.em actualEm em && near em actual expected)
            check ref s!"cancel spacing {options}/{target}: signed control is nonzero"
              (if target == "\\!" then expected < 0 else expected > 0)
    for (name, value) in [
        ("zero-mu", Math.MList.cons (.space 0) .nil),
        ("balanced-mu", .cons (.space 18) (.cons (.space (-18)) .nil))] do
      match zeroExtentWitness fonts (options == "makeroom") value with
      | .error err => check ref s!"cancel zero extent {options}/{name}: {err}" false
      | .ok w =>
        check ref s!"cancel zero extent {options}/{name}: native reservation struts"
          (reachAgrees w)
        check ref s!"cancel zero extent {options}/{name}: native advance retained"
          (advanceAgrees w)
        check ref s!"cancel zero extent {options}/{name}: native height ignores spacing"
          (empty.any fun e => (reservation e).any fun expected =>
            reservation w == some expected)
        check ref s!"cancel zero extent {options}/{name}: native line extent ignores spacing"
          (empty.any fun e => w.lineExtents == e.lineExtents)
        check ref s!"cancel zero extent {options}/{name}: native line baselines ignore spacing"
          (empty.any fun e => w.flowBaselines == e.flowBaselines)
        check ref s!"cancel zero extent {options}/{name}: HTML height ignores spacing"
          (empty.any fun e => (htmlReservation e).any fun expected =>
            (htmlReservation w).any fun actual =>
              near w.em actual.1 expected.1 && near w.em actual.2 expected.2)
        check ref s!"cancel zero extent {options}/{name}: zero net target advance retained"
          ((targetSpaceAdvance w).any (·.2 == 0))
