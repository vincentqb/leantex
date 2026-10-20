module

public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.Layout
public import LeanTex.Core.ContrastPaint

namespace LeanTex.Core.Check

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Layout LeanTex.Core.Dim

/-- The facts of the shipped artifact that assertions are judged against. -/
public structure Shipped where
  pages : Nat
  fontsEmbedded : Bool
  /-- Every run's ink, from cap height to full descent, lies inside the margins. -/
  inArea : Bool := true
  /-- The worst offender, for the failure message. -/
  areaActual : String := ""
  /-- The smallest x-height set anywhere, from each run's font at its size. -/
  minXHeight : Option Length := none
  /-- Failing or unverified accessibility rows. -/
  a11y : Array String := #[]
  /-- The rules of the declared PDF profiles that the built file's census breaks. -/
  pdfViolations : Array String := #[]

/-- The worse of `cur` and one ink rectangle's overshoot past the text area, with its edge. -/
private def worstOvershoot (left right top bottom x0 x1 y0 y1 : Length)
    (cur : Length × String) : Length × String :=
  let past (d : Length) (edge : String) (cur : Length × String) : Length × String :=
    if d > cur.1 then (d, edge) else cur
  past (y1 - bottom) "bottom" (past (top - y0) "top"
    (past (x1 - right) "right" (past (left - x0) "left" cur)))

/-- Measure the shipped pages; running furniture is exempt from the area judgement. -/
public def Shipped.ofOut (geom : Geom) (fs : Font.FontSet) (out : Out)
    (fontsEmbedded : Bool) : Shipped := Id.run do
  let mut worstAt : Length × String := (0, "")
  let mut minX : Option Length := none
  let right := geom.pageW - geom.hmargin
  let bottom := geom.bodyBottom
  for p in out.pages do
    for l in p.lines do
      let mut x := l.x
      for seg in l.segs do
        match seg with
        | .gap w _ | .decoratedGap w _ _ => x := x + w
        | .image _ w h _ raise _ =>
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - raise - h) (l.y - raise) worstAt
          x := x + w
        | .rule w thickness raise _ _ | .decoration _ w thickness raise _ _ =>
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - raise - thickness) (l.y - raise) worstAt
          x := x + w
        | .poly pts _ =>
          unless l.furniture do
            if let some (px, py) := pts[0]? then
              let (xmin, xmax, ymin, ymax) := pts.foldl
                (fun (xmin, xmax, ymin, ymax) (px, py) =>
                  (min xmin px, max xmax px, min ymin py, max ymax py))
                (px, px, py, py)
              worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
                (x + xmin) (x + xmax) (l.y - ymax) (l.y - ymin) worstAt
        | .run idx _ _ w glyphs size _ _ raise _ _ =>
          unless glyphs.isEmpty do
            let font := fs.get idx
            let sz := if size == 0 then l.size else size
            let upem : Int := font.unitsPerEm
            let asc := font.inkAscent * sz / upem
            let desc := (-font.descent) * sz / upem
            let base := l.y - raise
            unless l.furniture do
              worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
                x (x + w) (base - asc) (base + desc) worstAt
            let xhUnits := if font.xHeight > 0 then font.xHeight else upem / 2
            let xh := xhUnits * sz / upem
            minX := some (match minX with
              | some v => min v xh
              | none => xh)
          x := x + w
  return {
    pages := out.pages.size
    fontsEmbedded := fontsEmbedded
    inArea := worstAt.1 ≤ 0
    areaActual := s!"ink {worstAt.1.toPtString}pt past the {worstAt.2} margin"
    minXHeight := minX }

private def failure (a : Assertion) (actual : String) : Diag :=
  Diag.of .E0330 s!"assertion failed: {a.kind.source} (actual: {actual})" a.span
    (help := some (a.help.getD
      "the document shipped this; change the source or the \\assert")) (subject := a.subject)

/-- The diagnostic codes carrying a judged WCAG 2.2 fact: the rows `accessibility = AA` reads. -/
private def a11yCodes : List DiagCode :=
  [.W0315, .W0330, .W0345, .W0320, .W0321, .N0376]

/-- The failing AA rows: each judged accessibility code that fired, and an undeclared language. -/
public def a11ySummary (doc : Doc) (diags : Array Diag) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in a11yCodes do
    let n := (diags.filter (·.kind == c)).size
    if n > 0 then
      out := out.push (if n == 1 then s!"{c.code}: {c.meaning}"
        else s!"{c.code} ×{n}: {c.meaning}")
  if doc.info.language.isNone then
    out := out.push ("no declared language (WCAG 2.2 SC 3.1.1): declare " ++
      "\\pdfmeta{ language = ... } or babel's language option")
  return out

/-- The AA rows of a PDF, with every placed text run whose contrast fails or is unverified. -/
public def pdfA11ySummary (doc : Doc) (diags : Array Diag) (geom : Geom)
    (fs : Font.FontSet) (out : Out) : Array String :=
  a11ySummary doc diags ++ (Contrast.shippedContrastIssues geom fs out).map fun j =>
    let site := s!"page {j.paint.page + 1}, line {j.paint.line + 1}, run {j.paint.segment + 1}"
    let issue := match j.verdict with
      | .unverified .metrics => "text contrast unverified: font metrics are missing"
      | .unverified .nonpositiveSize => "text contrast unverified: font size is not positive"
      | .unverified .ground => "text contrast unverified: a uniform background has not been established"
      | .measured _ _ _ pair =>
        s!"text contrast {pair.ratio}/1000 is below {pair.required}/1000; no exemption was established"
    s!"{site}: {issue}"

public theorem pdfA11ySummary_clear_contract (doc : Doc) (diags : Array Diag)
    (geom : Geom) (fs : Font.FontSet) (out : Out) :
    pdfA11ySummary doc diags geom fs out = #[] ↔
      a11ySummary doc diags = #[] ∧
      ∀ paint, Contrast.PaintOccurs out paint →
        Contrast.TextVerified (Contrast.shippedGrounds geom out) fs out paint := by
  simp only [pdfA11ySummary, Array.append_eq_empty_iff, Array.map_eq_empty_iff,
    Contrast.shippedContrast_clear_contract]

/-- Check one assertion, returning a diagnostic when it does not hold. -/
public def one (shipped : Shipped) (a : Assertion) : Option Diag :=
  match a.kind with
  | .pages op n =>
    if op.holds shipped.pages n then none
    else some (failure a s!"{shipped.pages}")
  | .fontsAllEmbedded =>
    if shipped.fontsEmbedded then none
    else some (failure a "a font was not embedded")
  | .textInArea =>
    if shipped.inArea then none
    else some (failure a shipped.areaActual)
  | .minXHeight m =>
    match shipped.minXHeight with
    | none => none
    | some v =>
      if v ≥ m then none
      else some (failure a s!"{v.toPtString}pt x-height")
  | .accessibilityAA =>
    if shipped.a11y.isEmpty then none
    else some (failure a (String.intercalate "; " shipped.a11y.toList))
  | .pdfProfile _ =>
    if shipped.pdfViolations.isEmpty then none
    else some (failure a (String.intercalate "; " shipped.pdfViolations.toList))

/-- Check every assertion; empty when the document satisfies them all. -/
public def all (shipped : Shipped) (asserts : Array Assertion) : Array Diag :=
  asserts.filterMap (one shipped)

end LeanTex.Core.Check
