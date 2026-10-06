import Tests.Support

namespace LeanTex.Tests.LayoutContracts

open Core Core.Dim Core.Ir Core.Layout Core.Font

private def noDroppedGlyph (out : Out) : Bool :=
  !out.diags.any fun d => d.kind == .E0405 || d.kind == .W0009

/-- Frame ownership survives an authored running footer: suppressing the
chrome band changes furniture, not which frame produced a physical page. -/
def ownershipChecks (fs : FontSet) : Array (String × Bool) :=
  let geom : Geom := {
    pageW := pt 220, pageH := pt 120
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let frame := Block.frame #[.text "Title"] false .top false #[.para #[.text "Body"]]
  let out := run geom fs none {
    docClass := .slides, foot := some #[.text "Running footer"], body := #[frame] }
  let chrome : Chrome := { footerRight := some .frameNumber }
  let splitFrame := Block.frame #[.text "Title"] false .top false
    #[.para #[.text "Before"], .pagebreak, .para #[.text "After"]]
  let split := run geom fs none { docClass := .slides, chrome, body := #[splitFrame] }
  let following := run geom fs none {
    docClass := .slides, chrome, body := #[frame, .para #[.text "Outside"]] }
  let restarted := run geom fs none {
    docClass := .slides, chrome, frameRestart := some 1, body := #[frame, frame] }
  let spilling := run geom fs none {
    docClass := .slides, chrome, body := #[.frame #[.text "Title"] false .top false
      (Array.replicate 24 (.para #[.text "Body"]))] }
  let stepped := run geom fs none {
    docClass := .slides, chrome, body := #[.frame #[.text "Title"] false .top false
      #[.para #[.text "Body"],
        .onSteps { first := 2, last := none } #[.para #[.text "Later"]]]] }
  #[("authored running footer preserves displayed frame attribution",
    noDroppedGlyph out && out.pages.size == 1 &&
    out.pages.all (fun p => p.frame == some 1 && p.foot.isNone &&
      p.frameOrigin == some ⟨0, 1⟩)),
    ("authored page breaks retain the frame source and shared footer",
      noDroppedGlyph split && split.pages.size == 2 &&
      split.pages.all (fun p => p.frameOrigin == some ⟨0, 1⟩ &&
        p.frame == some 1 && p.foot == chrome.frameFootBand none #[] (some 1) 1 false)),
    ("flow after a closed frame has no inherited frame ownership or chrome",
      noDroppedGlyph following && following.pages.size == 2 &&
      following.pages[0]?.bind (·.frameOrigin) == some ⟨0, 1⟩ &&
      following.pages[1]?.bind (·.frameOrigin) == none &&
      following.pages[1]?.bind (·.frame) == none &&
      following.pages[1]?.bind (·.foot) == none),
    ("source identity distinguishes restarted display counters",
      noDroppedGlyph restarted && restarted.pages.size == 2 &&
      restarted.pages.all (·.frame == some 1) &&
      restarted.pages.map (·.frameOrigin) == #[some ⟨0, 1⟩, some ⟨1, 1⟩]),
    ("spill pages retain one source identity and one selected footer",
      noDroppedGlyph spilling && spilling.pages.size > 1 &&
      spilling.pages.all (fun p => p.frameOrigin == some ⟨0, 1⟩ &&
        p.foot == chrome.frameFootBand none #[] (some 1) 1 false)),
    ("overlays share a source while retaining their actual step identity",
      noDroppedGlyph stepped && stepped.pages.size == 2 &&
      stepped.pages.map (·.frameOrigin) == #[some ⟨0, 1⟩, some ⟨0, 2⟩] &&
      stepped.pages.all (·.frame == some 1))]

/-- Executable counterexamples to the old universal Layout contracts.
These exercise legitimate pagination and furniture decisions, not a font
failure or a desired geometry fix encoded as expected broken behaviour.
They pin why the replacement statements need body ink, physical-page
coordinates, actual spill counts, the shared standout footer decision,
and the distinction between an authored line end and a paragraph end. -/
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
  let reflowGeom := { geom with pageW := pt 100, pageH := pt 250 }
  let prose := String.join (List.replicate 14 "ordinary prose ")
  let lastWrap := run reflowGeom fs none {
    body := #[.para #[.text "First", .linebreak {}, .text prose]] }
  let declaredWrap := run reflowGeom fs none {
    body := #[.para #[.text prose, .linebreak {}, .text "Last"]] }
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
      restart.pages.all (·.frame == some 1)),
    ("wrapping the final paragraph segment loses no authored line end",
      noDroppedGlyph lastWrap && noDroppedGlyph declaredWrap &&
      (bodyLines lastWrap).size > 2 &&
      ((bodyLines lastWrap)[0]?.map lineText) == some "First" &&
      !lastWrap.diags.any (·.kind == .W0386) &&
      (bodyLines declaredWrap).size > 2 &&
      declaredWrap.diags.any (·.kind == .W0386))]

private def keyedReflows (out : Out) : Bool :=
  out.paragraphBreaks.all fun p =>
    p.reflows.isEmpty || out.diags.any fun d =>
      d.kind == .W0386 && d.subject == some p.subject

private def sequentialParagraphs (out : Out) : Bool :=
  out.paragraphBreaks.zipIdx.all fun (p, i) => p.site == i

/-- Read actual breaker choices from shipment, including float retries and
column joins. A replay must neither duplicate its abandoned trial nor
reuse a key; deduplication must retain separate paragraphs' warnings. -/
def reflowChecks (fs : FontSet) : Array (String × Bool) :=
  let geom : Geom := {
    pageW := pt 100, pageH := pt 250
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let prose := String.join (List.replicate 14 "ordinary prose ")
  let declared := Block.para #[.text prose, .linebreak {}, .text "Last"]
  let held := run geom fs none {
    body := #[.para #[.text "First", .linebreak {}, .text "Last"]] }
  let split := run geom fs none { body := #[declared] }
  let tail := run geom fs none {
    body := #[.para #[.text "First", .linebreak {}, .text prose]] }
  let twice := run geom fs none { body := #[declared, declared] }
  let frame := Block.frame #[] false .top false #[declared]
  let framed := run geom fs none {
    docClass := .slides, frameRestart := some 1, body := #[frame, frame] }
  let short := { geom with pageH := pt 80 }
  let replay := run short fs none {
    body := #[.para #[.text "Before"], .float .figure none false #[declared] #[]] }
  let columns := run { geom with pageW := pt 220 } fs none {
    body := #[.columns #[
      (.abs (pt 76), #[declared]), (.abs (pt 76), #[declared])]] }
  #[
    ("held authored ends record the real choices without naming reflow",
      noDroppedGlyph held && held.paragraphBreaks.size == 1 &&
      held.paragraphBreaks.all (fun p => p.forced.size == 2 && p.reflows.isEmpty) &&
      !held.diags.any (·.kind == .W0386)),
    ("a split before an authored end carries its paragraph key",
      noDroppedGlyph split && split.paragraphBreaks.size == 1 &&
      split.paragraphBreaks.any (fun p => !p.reflows.isEmpty) &&
      keyedReflows split && sequentialParagraphs split),
    ("wrapping only the final segment records no lost authored end",
      noDroppedGlyph tail && tail.paragraphBreaks.size == 1 &&
      tail.paragraphBreaks.all (fun p => p.chosen.size > p.forced.size &&
        p.reflows.isEmpty) &&
      !tail.diags.any (·.kind == .W0386)),
    ("diagnostic deduplication retains two distinct reflowing paragraphs",
      noDroppedGlyph twice &&
      (twice.paragraphBreaks.filter (fun p => !p.reflows.isEmpty)).size == 2 &&
      (twice.diags.filter (·.kind == .W0386)).size == 2 &&
      keyedReflows twice && sequentialParagraphs twice),
    ("restarted frame counters preserve source identity in paragraph choices",
      noDroppedGlyph framed &&
      framed.paragraphBreaks.any (·.frame == some ⟨0, 1⟩) &&
      framed.paragraphBreaks.any (·.frame == some ⟨1, 1⟩) &&
      keyedReflows framed && sequentialParagraphs framed),
    ("a float retry retains one record for the committed reflowing paragraph",
      noDroppedGlyph replay && replay.diags.any (·.kind == .W0358) &&
      (replay.paragraphBreaks.filter (fun p => !p.reflows.isEmpty)).size == 1 &&
      keyedReflows replay && sequentialParagraphs replay),
    ("joined columns retain both reflow records and their distinct diagnostics",
      noDroppedGlyph columns &&
      (columns.paragraphBreaks.filter (fun p => !p.reflows.isEmpty)).size == 2 &&
      (columns.diags.filter (·.kind == .W0386)).size == 2 &&
      keyedReflows columns && sequentialParagraphs columns)]

end LeanTex.Tests.LayoutContracts
