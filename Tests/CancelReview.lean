import Tests.CancelMetric

open LeanTex.Core

namespace CancelReview

private def rootAttribute (key : String) : Html.Node → String
  | .elem tag attrs _ => (attrValuesOf (fun _ => true) key (.elem tag attrs #[])).getD 0 ""
  | _ => ""

private def children : Html.Node → Array Html.Node
  | .elem _ _ kids => kids
  | _ => #[]

private def css (key : String) (node : Html.Node) : String :=
  let fields := ((rootAttribute "style" node).splitOn ";").map fun decl =>
    let parts := decl.splitOn ":"
    (parts.headD "" |>.trimAscii.toString,
      String.intercalate ":" parts.tail |>.trimAscii.toString)
  (fields.reverse.find? (·.1 == key)).map (·.2) |>.getD ""

private def readEm (em : Int) (s : String) : Option Int := do
  if s == "0" then return 0
  if !s.endsWith "em" then none else do
    let (n, d) ← Decl.parseDecimal (s.dropEnd 2).toString
    return (n * em + (d : Int) / 2) / d

private def optionalEm (em : Int) (s : String) : Option Int :=
  if s.isEmpty then some 0 else readEm em s

private def margin (em : Int) (logical physical : String) (node : Html.Node) : Option Int :=
  optionalEm em (if (css logical node).isEmpty then css physical node else css logical node)

private def margins (em : Int) (node : Html.Node) : Option (Int × Int) := do
  let left ← margin em "margin-inline-start" "margin-left" node
  let right ← margin em "margin-inline-end" "margin-right" node
  return (left, right)

private def near (em a b : Int) : Bool :=
  (a - b).natAbs ≤ ((em + 1999999) / 2000000 + 2).toNat

/-- MathML width cannot carry a negative advance. Read the declared CSS
margins too; a negative attribute alone does not move the following atom. -/
private def advance (em : Int) (node : Html.Node) : Option Int := do
  let w ← readEm em (rootAttribute "width" node)
  let (left, right) ← margins em node
  return max 0 w + left + right

private structure Offset where
  chromiumX : Int
  firefoxX : Int
  y : Int
  advance : Int

/-- Chromium clamps negative mpadded lspace, while Firefox accepts it.
The two readings must agree with the native pen. Balanced CSS margins
are read from the actual placement element, outside its child's size step. -/
private def offset (em : Int) (node : Html.Node) : Option Offset := do
  if ["position", "left", "top", "transform"].any (fun key => !(css key node).isEmpty) then
    none
  else do
    let ls ← optionalEm em (rootAttribute "lspace" node)
    let y ← optionalEm em (rootAttribute "voffset" node)
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
    cancelMetric := Layout.cancelMetric geom fonts
    mathEm := Layout.mathEm geom fonts } doc
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
    (rootAttribute "data-cancel-metric" · == "measured") | throw "missing measured HTML construct"
  return {
    em := anchor.size, origin := left, baseline := anchor.y
    nativeAdvance := right - left, line
    lineExtents := #[box.above, box.below, box.inkAbove, box.inkBelow]
    flowBaselines := #[middle.y - above.y, below.y - middle.y]
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

private def targetAgrees (w : Witness) : Bool := (do
  let value ← (children w.node)[1]?
  let placement ← offset w.em value
  let first ← w.glyphs.find? (fun (g : ShippedGlyph) => g.scalar == '0')
  return near w.em placement.chromiumX (first.x - w.origin) &&
    near w.em placement.firefoxX (first.x - w.origin) &&
    near w.em placement.y (w.baseline - first.y) &&
    near w.em placement.advance 0).getD false

/-- Read the native zero-width, one-sp strut runs actually shipped.
These cases have a plain x body, so the only two struts are cancellation's
own reservation; neither geometry constructors nor target ink predict it. -/
private def reservation (w : Witness) : Option (Int × Int) := do
  let struts := w.line.segs.filterMap fun seg => match seg with
    | .run _ _ _ width glyphs size _ _ raise _ _ =>
      if width == 0 && glyphs.isEmpty && size == 1 then
        some (raise - (w.line.y - w.baseline))
      else none
    | _ => none
  let #[top, bot] := struts | none
  return (top, bot)

private def htmlReservation (w : Witness) : Option (Int × Int) := do
  let h ← readEm w.em (rootAttribute "height" w.node)
  let d ← readEm w.em (rootAttribute "depth" w.node)
  return (h, -d)

private def reachAgrees (w : Witness) : Bool := (do
  let (top, bot) ← reservation w
  let (h, bot') ← htmlReservation w
  return near w.em h top && near w.em bot' bot).getD false

/-- A plain script witnesses target spacing without cancellation geometry
or either metric callback supplying the expected pen displacement. -/
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
  return (anchor.size, right - left)

private def targetSpaceAdvance (w : Witness) : Option (Int × Int) := do
  let placed ← (children w.node)[1]?
  let styled ← (children placed)[0]?
  let em ← readEm w.em (css "font-size" styled)
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
  check ref "cancel review reader: balanced signed margins preserve zero advance"
    (correct.any fun r => r.chromiumX == -2000000 && r.firefoxX == -2000000 &&
      r.y == 1000000 && r.advance == 0)
  let clamped := offset 1000000 (placed "-2em" "")
  check ref "cancel review reader: negative lspace exposes browser disagreement"
    (clamped.any fun r => r.chromiumX == 0 && r.firefoxX == -2000000)
  let unbalanced := offset 1000000 (placed "0" "margin-left: -2em")
  check ref "cancel review reader: missing balancing margin leaks advance"
    (unbalanced.any fun r => r.advance == -2000000)
  let signed := Html.Node.elem "mpadded"
    #[("width", "0"), ("style", "margin-inline-end: -0.5em")] #[]
  let clampedWidth := Html.Node.elem "mpadded" #[("width", "-0.5em")] #[]
  check ref "cancel review reader: signed CSS advance survives nonnegative width"
    (advance 1000000 signed == some (-500000))
  check ref "cancel review reader: negative width alone loses signed advance"
    (advance 1000000 clampedWidth == some 0)

end CancelReview

open CancelReview in
/- check: CancelReview.checks -/
/-- Guard the native-to-HTML cancellation boundary with actual shipped
neighbour pens, target baselines, reservation struts and line spacing.
The signed-offset reader models the independently observed browser
disagreement explicitly. -/
def CancelReview.checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let fonts ← mathSetOf oneFace
  readerChecks ref
  for options in ["overlap", "makeroom"] do
    let empty := (witness fonts options "$" "x" "" "$").toOption
    check ref s!"cancel review spacing {options}: empty reservation control" empty.isSome
    for (style, before, after) in [
        ("text", "$", "$"), ("script", "$z^{", "}$")] do
      for body in ["x", "x\\!\\!\\!\\!\\!\\!", "\\!\\!x\\!\\!\\!\\!"] do
        let name := s!"{options}/{style}/{body}"
        match witness fonts options before body "0" after with
        | .error err => check ref s!"cancel review signed {name}: {err}" false
        | .ok w =>
          check ref s!"cancel review signed {name}: native neighbour advance" (advanceAgrees w)
          check ref s!"cancel review signed {name}: portable target placement" (targetAgrees w)
          if options == "overlap" && body != "x" then
            check ref s!"cancel review signed {name}: witness is negative" (w.nativeAdvance < 0)
      let body := "\\frac{x}{\\frac{x}{x}}"
      match witness fonts options before body "000000000000g" after with
      | .error err => check ref s!"cancel review wide {options}/{style}: {err}" false
      | .ok w =>
        check ref s!"cancel review wide {options}/{style}: portable target placement"
          (targetAgrees w)
        check ref s!"cancel review wide {options}/{style}: native neighbour advance"
          (advanceAgrees w)
        if options == "overlap" then
          check ref s!"cancel review wide {options}/{style}: target starts left of origin"
            ((w.glyphs.find? (·.scalar == '0')).any (·.x < w.origin))
    for target in ["", "\\color{red}", "{}", "\\,", "\\!", "\\color{red}\\,"] do
      match witness fonts options "$" "x" target "$" with
      | .error err => check ref s!"cancel review empty {options}/{target}: {err}" false
      | .ok w =>
        check ref s!"cancel review empty {options}/{target}: native reservation struts"
          (reachAgrees w)
        check ref s!"cancel review empty {options}/{target}: native advance retained"
          (advanceAgrees w)
        check ref s!"cancel review empty {options}/{target}: empty to-value node retained"
          ((children w.node).size == 3 &&
            (MathMl.nodeChars #[] ((children w.node)[1]!)).isEmpty)
        if ["\\,", "\\!", "\\color{red}\\,"].contains target then
          check ref s!"cancel review spacing {options}/{target}: native height ignores spacing"
            (empty.any fun e => (reservation e).any fun expected =>
              reservation w == some expected)
          check ref s!"cancel review spacing {options}/{target}: native line extent ignores spacing"
            (empty.any fun e => w.lineExtents == e.lineExtents)
          check ref s!"cancel review spacing {options}/{target}: native line baselines ignore spacing"
            (empty.any fun e => w.flowBaselines == e.flowBaselines)
          check ref s!"cancel review spacing {options}/{target}: HTML height ignores spacing"
            (empty.any fun e => (htmlReservation e).any fun expected =>
              (htmlReservation w).any fun actual =>
                near w.em actual.1 expected.1 && near w.em actual.2 expected.2)
          match targetSpacePen fonts target with
          | .error err => check ref s!"cancel review spacing {options}/{target}: {err}" false
          | .ok (em, expected) =>
            check ref s!"cancel review spacing {options}/{target}: signed target advance retained"
              ((targetSpaceAdvance w).any fun (actualEm, actual) =>
                near w.em actualEm em && near em actual expected)
            check ref s!"cancel review spacing {options}/{target}: signed control is nonzero"
              (if target == "\\!" then expected < 0 else expected > 0)
    for (name, value) in [
        ("zero-mu", Math.MList.cons (.space 0) .nil),
        ("balanced-mu", .cons (.space 18) (.cons (.space (-18)) .nil))] do
      match zeroExtentWitness fonts (options == "makeroom") value with
      | .error err => check ref s!"cancel review zero extent {options}/{name}: {err}" false
      | .ok w =>
        check ref s!"cancel review zero extent {options}/{name}: native reservation struts"
          (reachAgrees w)
        check ref s!"cancel review zero extent {options}/{name}: native advance retained"
          (advanceAgrees w)
        check ref s!"cancel review zero extent {options}/{name}: native height ignores spacing"
          (empty.any fun e => (reservation e).any fun expected =>
            reservation w == some expected)
        check ref s!"cancel review zero extent {options}/{name}: native line extent ignores spacing"
          (empty.any fun e => w.lineExtents == e.lineExtents)
        check ref s!"cancel review zero extent {options}/{name}: native line baselines ignore spacing"
          (empty.any fun e => w.flowBaselines == e.flowBaselines)
        check ref s!"cancel review zero extent {options}/{name}: HTML height ignores spacing"
          (empty.any fun e => (htmlReservation e).any fun expected =>
            (htmlReservation w).any fun actual =>
              near w.em actual.1 expected.1 && near w.em actual.2 expected.2)
        check ref s!"cancel review zero extent {options}/{name}: zero net target advance retained"
          ((targetSpaceAdvance w).any (·.2 == 0))
