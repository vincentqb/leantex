import Tests.Support

namespace LeanTex.Tests.LayoutContracts

open Core Core.Dim Core.Ir Core.Layout Core.Font

private def noDroppedGlyph (out : Out) : Bool :=
  !out.diags.any fun d => d.kind == .E0405 || d.kind == .W0009

/-- Executable counterexamples to the old universal Layout contracts.
These exercise legitimate pagination and furniture decisions, not a font
failure or a desired geometry fix encoded as expected broken behaviour.
They pin why the replacement statements need body ink, physical-page
coordinates, actual spill counts, and the shared standout footer decision. -/
def counterexamples (fs : FontSet) : Array (String × Bool) := Id.run do
  let geom : Geom := {
    pageW := pt 220, pageH := pt 80
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let a : Array Inline := #[.text "First"]
  let b : Array Inline := #[.text "Second"]
  let plain : Doc := { body := #[.para a, .para b] }
  let ordinary := run geom fs none plain
  let spaced := run geom fs none { plain with body := #[.para a,
    .spaced (Sourced.bare { width := Length.ofSp (pt 80) }) #[.para b]] }
  let ordinaryLines := (bodyLines ordinary).filter fun l => !l.note && hasGlyphRun l
  let spacedLines := (bodyLines spaced).filter fun l => !l.note && hasGlyphRun l
  let chrome : Chrome := { footerRight := some .frameNumber }
  let frameGeom := { geom with pageH := pt 120 }
  let frame := Block.frame #[.text "Title"] false .top false #[.para #[.text "Body"]]
  let spilling := Block.frame #[.text "Title"] false .top false
    (Array.replicate 24 (.para #[.text "Body"]))
  let spillDoc : Doc := { docClass := .slides, chrome, body := #[spilling] }
  let spills := run frameGeom fs none spillDoc
  let standoutDoc : Doc := {
    docClass := .slides, chrome
    body := #[.frame #[.text "Title"] true .center false #[.para #[.text "Body"]]] }
  let standout := run frameGeom fs none standoutDoc
  let restart := run frameGeom fs none {
    docClass := .slides, chrome, frameRestart := some 1, body := #[frame, frame] }
  return #[
    ("undeclared running bands still ship the plain page number",
      plain.head.isNone && plain.foot.isNone && noDroppedGlyph ordinary &&
      String.join (ordinaryLines.map (lineText · false)).toList == "FirstSecond" &&
      String.join ((allLines ordinary).map (lineText · false)).toList == "FirstSecond1"),
    ("positive element space can lower a page-local baseline by paginating",
      noDroppedGlyph ordinary && noDroppedGlyph spaced &&
      ordinary.pages.size == 1 && spaced.pages.size == 2 &&
      ordinaryLines.size == 2 && spacedLines.size == 2 &&
      ((spacedLines.back?).map (·.y)).getD 0 <
        ((ordinaryLines.back?).map (·.y)).getD 0),
    ("a countable frame can ship more pages than its overlay count",
      noDroppedGlyph spills && frameSteps spilling == 1 &&
      (spills.pages.filter (·.frame == some 1)).size > frameSteps spilling &&
      spills.diags.any (·.kind == .W0384)),
    ("a numbered standout intentionally selects no chrome footer",
      standoutDoc.chrome.hasFooter && standoutDoc.foot.isNone &&
      noDroppedGlyph standout && standout.pages.size == 1 &&
      standout.pages.all (fun p => p.frame == some 1 && p.foot.isNone)),
    ("restarted frame numbers do not identify distinct source frames",
      noDroppedGlyph restart && restart.pages.size == 2 &&
      restart.pages.all (·.frame == some 1))]

end LeanTex.Tests.LayoutContracts
