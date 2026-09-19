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

/-- Measure the shipped pages. A glyph run's ink box is its advance across
and its font's ascent/descent at the run's size vertically; a rule's is the
rectangle it fills. A font that declares no x-height is read at the
conventional half of its size — the same ratio the legibility literature
uses to convert between x-height and nominal size. The caller skips this
walk when no assertion reads it.

Engine-placed running furniture (`LineOut.furniture`) is exempt from the
area judgement: a running head stands in the margin by design — LaTeX's
own page styles put it there — and the furniture pass places it inside
its reserved band by construction (`headBandFor`, W0328's single-line
rule), so judging it against the text-area margins would fail every page
whose furniture works as declared. Its glyphs still feed the x-height
floor: margin text must stay legible too. -/
def Shipped.ofOut (geom : Geom) (fs : Font.FontSet) (out : Out)
    (fontsEmbedded : Bool) : Shipped := Id.run do
  let mut worst : Sp := 0
  let mut worstEdge := ""
  let mut minX : Option Sp := none
  let right := geom.pageW - geom.hmargin
  let bottom := geom.bodyBottom
  for p in out.pages do
    for l in p.lines do
      let mut x := l.x
      for seg in l.segs do
        match seg with
        | .gap w => x := x + w
        | .image _ w h =>
          -- The image box is ink: its full rectangle must respect the area.
          unless l.furniture do
            if geom.hmargin - x > worst then
              worst := geom.hmargin - x
              worstEdge := "left"
            if x + w - right > worst then
              worst := x + w - right
              worstEdge := "right"
            if geom.vmargin - (l.y - h) > worst then
              worst := geom.vmargin - (l.y - h)
              worstEdge := "top"
            if l.y - bottom > worst then
              worst := l.y - bottom
              worstEdge := "bottom"
          x := x + w
        | .rule w thickness raise _ =>
          unless l.furniture do
            if geom.hmargin - x > worst then
              worst := geom.hmargin - x
              worstEdge := "left"
            if x + w - right > worst then
              worst := x + w - right
              worstEdge := "right"
            if geom.vmargin - (l.y - raise - thickness) > worst then
              worst := geom.vmargin - (l.y - raise - thickness)
              worstEdge := "top"
            if l.y - raise - bottom > worst then
              worst := l.y - raise - bottom
              worstEdge := "bottom"
          x := x + w
        | .run idx _ _ w glyphs size _ raise =>
          unless glyphs.isEmpty do
            let font := fs.get idx
            let sz := if size == 0 then l.size else size
            let upem : Int := font.unitsPerEm
            let asc := (if font.capHeight > 0 then font.capHeight else font.ascent)
              * sz / upem
            let desc := (-font.descent) * sz / upem
            -- A raised run's ink is judged from its own baseline: a
            -- superscript rides above the line's.
            let base := l.y - raise
            unless l.furniture do
              if geom.hmargin - x > worst then
                worst := geom.hmargin - x
                worstEdge := "left"
              if x + w - right > worst then
                worst := x + w - right
                worstEdge := "right"
              if geom.vmargin - (base - asc) > worst then
                worst := geom.vmargin - (base - asc)
                worstEdge := "top"
              if base + desc - bottom > worst then
                worst := base + desc - bottom
                worstEdge := "bottom"
            let xhUnits := if font.xHeight > 0 then font.xHeight else upem / 2
            let xh := xhUnits * sz / upem
            minX := some (match minX with
              | some v => min v xh
              | none => xh)
          x := x + w
  return {
    pages := out.pages.size
    fontsEmbedded := fontsEmbedded
    inArea := worst ≤ 0
    areaActual := s!"ink {worst.toPtString}pt past the {worstEdge} margin"
    minXHeight := minX }

private def failure (a : Assertion) (actual : String) : Diag :=
  Diag.of .E0330 s!"assertion failed: {a.kind.source} (actual: {actual})" a.span
    (help := some (a.help.getD
      "the document shipped this; change the source or the \\assert"))

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

/-- Check every assertion. Empty result means the document satisfied them. -/
def all (shipped : Shipped) (asserts : Array Assertion) : Array Diag :=
  asserts.filterMap (one shipped)

end LeanTex.Core.Check
