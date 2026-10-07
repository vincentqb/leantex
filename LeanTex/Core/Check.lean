module

public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.Layout
public import LeanTex.Core.ContrastPaint

namespace LeanTex.Core.Check

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Layout LeanTex.Core.Dim

/-- What the engine actually shipped, which is what assertions are judged
against — never the intent, always the result. -/
public structure Shipped where
  pages : Nat
  fontsEmbedded : Bool
  /-- Every piece of ink inside the margins, judged from the shipped lines
  with the fonts' own metrics: cap height above the baseline — the height a
  line of text measures from its glyphs, where the hhea ascent reserves
  accent headroom that is usually blank — and the full descent below. An
  accent above the caps on a margin-tight line is outside this measure,
  and that approximation is deliberate. On a card the margins are the
  print safe zone. -/
  inArea : Bool := true
  /-- The worst offender, for the failure message. -/
  areaActual : String := ""
  /-- The smallest x-height set anywhere, from each run's font at its size. -/
  minXHeight : Option Sp := none
  /-- Failing or unverified accessibility rows. Source diagnostics retain
  language, alternatives and outline facts; PDF assertions also inspect
  the actual placed text through `pdfA11ySummary`. -/
  a11y : Array String := #[]
  /-- The rules of the declared profile set's contract the built PDF's
  census breaks, rendered one per entry — filled by the driver from the
  contract module over the census of the bytes, only when a profile is
  declared. Empty when the file satisfies the contract, or when none is
  declared. -/
  pdfViolations : Array String := #[]

/-- The worse of `cur` and one ink rectangle's overshoot past the text
area, with the edge it overshot. Every ink-bearing segment kind is judged
here, so a kind added later cannot arrive with its own copy of these four
comparisons — nor with one of them missing. -/
private def worstOvershoot (left right top bottom x0 x1 y0 y1 : Sp)
    (cur : Sp × String) : Sp × String :=
  let past (d : Sp) (edge : String) (cur : Sp × String) : Sp × String :=
    if d > cur.1 then (d, edge) else cur
  past (y1 - bottom) "bottom" (past (top - y0) "top"
    (past (x1 - right) "right" (past (left - x0) "left" cur)))

/-- Measure the shipped pages. A glyph run's ink box is its advance across
and its font's ascent/descent at the run's size vertically; a rule's is the
rectangle it fills. A font that declares no x-height is read at the
conventional half of its size — the same ratio the legibility literature
uses to convert between x-height and nominal size. The caller skips this
walk when no assertion reads it.

Engine-placed running furniture (`LineOut.furniture`) is exempt from the
area judgement: a running head stands in the margin by design — LaTeX's
own page styles put it there — and the furniture pass places it inside
its reserved band by construction (`furnitureBand`, W0328's single-line
rule), so judging it against the text-area margins would fail every page
whose furniture works as declared. Its glyphs still feed the x-height
floor: margin text must stay legible too. -/
public def Shipped.ofOut (geom : Geom) (fs : Font.FontSet) (out : Out)
    (fontsEmbedded : Bool) : Shipped := Id.run do
  let mut worstAt : Sp × String := (0, "")
  let mut minX : Option Sp := none
  let right := geom.pageW - geom.hmargin
  let bottom := geom.bodyBottom
  for p in out.pages do
    for l in p.lines do
      let mut x := l.x
      for seg in l.segs do
        match seg with
        | .gap w _ | .decoratedGap w _ _ => x := x + w
        | .image _ w h =>
          -- The image box is ink: its full rectangle must respect the area.
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - h) l.y worstAt
          x := x + w
        | .rule w thickness raise _ | .decoration _ w thickness raise _ =>
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - raise - thickness) (l.y - raise) worstAt
          x := x + w
        | .poly pts _ =>
          -- A polygon is ink: its bounding box must respect the area.
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
            -- A raised run's ink is judged from its own baseline: a
            -- superscript rides above the line's.
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
      "the document shipped this; change the source or the \\assert"))

/-- The diagnostic codes that carry a judged WCAG 2.2 fact — the rows
`accessibility = AA` reads. Contrast pairs (SC 1.4.3 / 1.4.11: W0315
declared, W0330 defaulted ink, W0345 themed resolution), the heading
outline (SC 1.3.1, technique G141: W0320 the skip, W0321 the misplaced
title), and images with no text alternative (SC 1.1.1: N0376). Motion has
no row: every emitted animation carries its reduced-motion guard by
construction (`motionCss_guarded` and its siblings), so the fact cannot
fail. -/
private def a11yCodes : List DiagCode :=
  [.W0315, .W0330, .W0345, .W0320, .W0321, .N0376]

/-- The failing AA rows of a document: each judged accessibility code that
fired, with its count and registered meaning, plus the one non-diagnostic
row — an undeclared document language (SC 3.1.1 asks that the page's
default language be programmatically determinable; the PDF then carries no
`/Lang`, and the HTML's `en` is the engine's assumption, not the
document's declaration). Read from the diagnostics before `\allow`
resolution, independently of severity: advice and accepted warnings remain
facts. The deliberate escapes (a decorative declaration, an alt) remove the
fact itself, at the judge. -/
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

/-- Accessibility observations for a PDF, including every placed text
run. A background or exemption that has not been established cannot turn
an assertion green merely because no earlier warning fired. -/
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

/-- The summary consumed by the PDF assertion is clear only when its
source observations are clear and every actual text occurrence satisfies
the placed-paint judge. An unresolved occurrence contributes a message
just as a measured failure does. -/
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

/-- Check every assertion. Empty result means the document satisfied them. -/
public def all (shipped : Shipped) (asserts : Array Assertion) : Array Diag :=
  asserts.filterMap (one shipped)

end LeanTex.Core.Check
