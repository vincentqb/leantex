module

public import Tests.Support
public import LeanTex.Core.Layout.TextConservation

public section

namespace LeanTex.Tests.LayoutTextConservation

open Core Core.Dim Core.Font Core.Ir Core.Layout

private def glyphsAccounted (out : Out) : Bool :=
  !out.diags.any fun d => d.kind == .E0405 || d.kind == .W0009

/-- These checks read the final shipped pages. They exercise source ownership
across inline and paragraph boundaries, physical spills, running furniture,
and spacing characters that advance the pen without painting a glyph. -/
def textConservationChecks (fs : FontSet) : Array (String × Bool) :=
  let geom : Geom := {
    pageW := pt 130, pageH := pt 72
    hmargin := pt 10, vmargin := pt 10, fontSize := pt 10
    hyphenate := false, justify := false }
  let split : Doc := {
    head := some #[.text "HEAD"], foot := some #[.text "FOOT"]
    body := #[.para #[.text "Alpha", .text "Beta"], .para #[.text "Gamma"]] }
  let splitOut := run geom fs none split
  let spaced := run geom fs none {
    body := #[.para #[.text "A\u2009V\u2002T\u00a0o\u00adB"]] }
  let para := Block.para #[.text "Several ordinary words remain in their original order. "]
  let repeated := Array.replicate 18 para
  let body := #[.para #[], .para #[.text " "]] ++ repeated
  let long : Doc := {
    body, head := some #[.text "HEAD"], foot := some #[.text "FOOT"] }
  let longOut := run geom fs none long
  let justified := run { geom with justify := true } fs none long
  let noPatterns := run { geom with hyphenate := true } fs none long
  let expected := inkCensus (blocksText body).toList
  let owned (out : Out) := (List.range (Struct.ofDoc long).leaves.size).all fun k =>
    inkCensus (Census.leafPages out.pages k) == paragraphSourceInk body k
  let empty := run geom fs none { body := #[.para #[], .para #[.text ""]] }
  let missing := run geom fs none {
    body := #[.para #[.text (String.singleton (Char.ofNat 0x10ffff))]] }
  #[
    ("body text excludes authored running furniture",
      glyphsAccounted splitOut &&
      inkCensus (Census.bodyPages splitOut.pages) == "AlphaBetaGamma".toList &&
      (allLines splitOut).any (fun l => l.furniture && hasGlyphRun l)),
    ("one paragraph owns all of its literal inline segments",
      glyphsAccounted splitOut &&
      inkCensus (Census.leafPages splitOut.pages 0) == "AlphaBeta".toList &&
      Census.leafPages splitOut.pages 1 == [] &&
      inkCensus (Census.leafPages splitOut.pages 2) == "Gamma".toList),
    ("source ownership is computed without consulting placed lines",
      paragraphSourceInk split.body 0 == "AlphaBeta".toList &&
      paragraphSourceInk split.body 1 == [] &&
      paragraphSourceInk split.body 2 == "Gamma".toList),
    ("fixed spaces omit glyphs and the ink census excludes retained soft hyphens",
      glyphsAccounted spaced &&
      Census.bodyPages spaced.pages == "AVTo\u00adB".toList &&
      inkCensus (Census.bodyPages spaced.pages) == "AVToB".toList),
    ("ordered body census survives multiple physical spills",
      glyphsAccounted longOut && longOut.pages.size > 1 &&
      inkCensus (Census.bodyPages longOut.pages) == expected && owned longOut),
    ("justification preserves ordered body and paragraph censuses",
      glyphsAccounted justified && justified.pages.size > 1 &&
      inkCensus (Census.bodyPages justified.pages) == expected && owned justified),
    ("absent patterns prevent automatic hyphen insertion",
      glyphsAccounted noPatterns && noPatterns.pages.size > 1 &&
      inkCensus (Census.bodyPages noPatterns.pages) == expected && owned noPatterns),
    ("empty paragraphs add no body or attributed glyphs",
      glyphsAccounted empty && Census.bodyPages empty.pages == [] &&
      Census.leafPages empty.pages 0 == []),
    ("missing source glyphs violate the observable theorem premise",
      !glyphsAccounted missing)]

end LeanTex.Tests.LayoutTextConservation
