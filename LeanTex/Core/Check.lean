import LeanTex.Core.Diag
import LeanTex.Core.Ir
import LeanTex.Core.Layout

namespace LeanTex.Core.Check

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Layout LeanTex.Core.Dim

/-- What the engine actually shipped, which is what assertions are judged
against — never the intent, always the result. -/
structure Shipped where
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
  /-- The document's failing WCAG 2.2 AA rows, one line each — filled by
  the driver from `a11ySummary` over the document and its elaborated
  diagnostics, because the accessibility judges (contrast, alt, outline)
  speak before layout runs and their facts are not recoverable from the
  page tree alone. Empty when nothing failed. -/
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
def Shipped.ofOut (geom : Geom) (fs : Font.FontSet) (out : Out)
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
        | .gap w _ => x := x + w
        | .image _ w h =>
          -- The image box is ink: its full rectangle must respect the area.
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - h) l.y worstAt
          x := x + w
        | .rule w thickness raise _ =>
          unless l.furniture do
            worstAt := worstOvershoot geom.hmargin right geom.vmargin bottom
              x (x + w) (l.y - raise - thickness) (l.y - raise) worstAt
          x := x + w
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
title), and images with no text alternative (SC 1.1.1: W0376). Motion has
no row: every emitted animation carries its reduced-motion guard by
construction (`motionCss_guarded` and its siblings), so the fact cannot
fail. -/
def a11yCodes : List String :=
  ["W0315", "W0330", "W0345", "W0320", "W0321", "W0376"]

/-- The failing AA rows of a document: each judged accessibility code that
fired, with its count and registered meaning, plus the one non-diagnostic
row — an undeclared document language (SC 3.1.1 asks that the page's
default language be programmatically determinable; the PDF then carries no
`/Lang`, and the HTML's `en` is the engine's assumption, not the
document's declaration). Read from the diagnostics before `\allow`
resolution: accepting a warning quiets the report, not the fact — the
deliberate escapes (a decorative declaration, an alt) remove the fact
itself, at the judge. -/
def a11ySummary (doc : Doc) (diags : Array Diag) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in a11yCodes do
    let n := (diags.filter (·.code == c)).size
    if n > 0 then
      let meaning := ((DiagCode.ofString? c).map (·.meaning)).getD ""
      out := out.push (if n == 1 then s!"{c}: {meaning}"
        else s!"{c} ×{n}: {meaning}")
  if doc.info.language.isNone then
    out := out.push ("no declared language (WCAG 2.2 SC 3.1.1): declare " ++
      "\\pdfmeta{ language = ... } or babel's language option")
  return out

/-- Check one assertion, returning a diagnostic when it does not hold. -/
def one (shipped : Shipped) (a : Assertion) : Option Diag :=
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
def all (shipped : Shipped) (asserts : Array Assertion) : Array Diag :=
  asserts.filterMap (one shipped)

end LeanTex.Core.Check
