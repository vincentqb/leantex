import Tests.Support
import LeanTex.Core.Layout.FramePartition

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

private def selectedFooters (geom : Geom) (fs : FontSet) (doc : Doc) (out : Out) : Bool :=
  let openings := frameOpenings geom fs none doc
  out.pages.all fun p =>
    (p.frameOrigin.isNone && p.frame.isNone && p.foot.isNone) ||
      openings.any (fun f =>
        p.frameOrigin == f.origin && p.frame == f.number && p.foot == f.footer)

private def furnitureHas (p : PageOut) (text : String) : Bool :=
  p.lines.any fun line => line.furniture && lineText line == text

private def htmlFooters (doc : Doc) : Array (String × String) :=
  slideFootsList #[] (HtmlDoc.emitTree {} doc).2.1.toList

/-- Footer decisions are read at the actual source opening and survive
physical placement. These checks also inspect shipped furniture ink and
the typed HTML footer, including the intentional absence on a standout.
The older counterexample above remains a guard against restoring the
false requirement that every numbered frame have a footer. -/
def footerChecks (fs : FontSet) : Array (String × Bool) :=
  let geom : Geom := {
    pageW := pt 220, pageH := pt 120
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let chrome : Chrome := { footerRight := some .frameNumber, standoutNote := some true }
  let frame := Block.frame #[.text "Title"] false .top false #[.para #[.text "Body"]]
  let standout := Block.frame #[.text "Title"] true .center false #[.para #[.text "Body"]]
  let notedDoc : Doc := {
    docClass := .slides, chrome, body := #[.framefoot #[.text "Note"], frame] }
  let noted := run geom fs none notedDoc
  let plainDoc : Doc := { docClass := .slides, chrome, body := #[standout] }
  let plain := run geom fs none plainDoc
  let restoredDoc := { notedDoc with body := #[.framefoot #[.text "Note"], standout] }
  let restored := run geom fs none restoredDoc
  let runningDoc := { notedDoc with foot := some #[.text "Running"] }
  let running := run geom fs none runningDoc
  let spilledDoc : Doc := {
    docClass := .slides, chrome, body := #[.framefoot #[.text "Note"],
      .frame #[.text "Title"] false .top false
        (Array.replicate 24 (.para #[.text "Body"]))] }
  let spilled := run geom fs none spilledDoc
  let steppedDoc : Doc := {
    docClass := .slides, chrome, frameRestart := some 2,
    body := #[.framefoot #[.text "Note"],
      .frame #[.text "Title"] false .top false
        #[.para #[.text "Body"], .onSteps { first := 2, last := none }
          #[.para #[.text "Later"]]], frame] }
  let stepped := run geom fs none steppedDoc
  let dividedDoc : Doc := {
    docClass := .slides, chrome := { footerLeft := some .sectionTitle },
    body := #[.section 1 true none #[.text "Outer"],
      .frame #[] false .top false
        #[.para #[.text "Before"], .section 1 true none #[.text "Local"]],
      .section 1 true none #[.text "Next"], frame] }
  let divided := run geom fs none dividedDoc
  let columnsDoc : Doc := {
    docClass := .slides, chrome, body := #[.framefoot #[.text "Note"],
      .frame #[] false .top false #[.columns #[
        (.abs (pt 76), Array.replicate 16 (.para #[.text "Left"])),
        (.abs (pt 76), Array.replicate 20 (.para #[.text "Right"]))]]] }
  let columns := run geom fs none columnsDoc
  let floatDoc : Doc := {
    docClass := .slides, chrome, body := #[.framefoot #[.text "Note"],
      .frame #[] false .top false #[
        .para #[.text "Before"], .float .figure none false
          (Array.replicate 20 (.para #[.text "Floating"])) #[]]] }
  let floated := run geom fs none floatDoc
  #[
    ("ordinary frame footer is the shared band and ships its note and number",
      noDroppedGlyph noted && noted.pages.size == 1 && selectedFooters geom fs notedDoc noted &&
      pdfFoots noted == #[("Note", "1")] && htmlFooters notedDoc == #[("Note", "1")] &&
      noted.pages.all (fun p => furnitureHas p "Note" && furnitureHas p "1")),
    ("plain standout keeps its frame number and ships no footer ink",
      noDroppedGlyph plain && plain.pages.size == 1 && selectedFooters geom fs plainDoc plain &&
      plain.pages.all (fun p => p.frame == some 1 && p.foot.isNone &&
        !furnitureHas p "1") &&
      (pdfFoots plain).isEmpty && (htmlFooters plainDoc).isEmpty),
    ("restored standout footer ships only the authored note in both artifacts",
      noDroppedGlyph restored && restored.pages.size == 1 &&
      selectedFooters geom fs restoredDoc restored &&
      pdfFoots restored == #[("Note", "")] && htmlFooters restoredDoc == #[("Note", "")] &&
      restored.pages.all (fun p => furnitureHas p "Note" && !furnitureHas p "1")),
    ("authored running footer suppresses frame chrome without losing source ownership",
      noDroppedGlyph running && running.pages.size == 1 &&
      selectedFooters geom fs runningDoc running && (pdfFoots running).isEmpty &&
      (htmlFooters runningDoc).isEmpty &&
      running.pages.all (fun p => p.frameOrigin.isSome && furnitureHas p "Running" &&
        !furnitureHas p "Note")),
    ("every actual spill carries and paints the one selected frame footer",
      noDroppedGlyph spilled && spilled.pages.size > 1 &&
      selectedFooters geom fs spilledDoc spilled &&
      (pdfFoots spilled).size == spilled.pages.size &&
      dedupConsecutive (pdfFoots spilled) == htmlFooters spilledDoc &&
      spilled.pages.all (fun p => furnitureHas p "Note" && furnitureHas p "1")),
    ("overlays and restarted counters keep their actual opening decisions",
      noDroppedGlyph stepped && stepped.pages.size == 3 &&
      selectedFooters geom fs steppedDoc stepped &&
      (pdfFoots stepped).size == 3 &&
      (pdfFoots stepped).all (· == ("Note", "1")) &&
      htmlFooters steppedDoc == #[("Note", "1"), ("Note", "1")]),
    ("section dividers clear frame ownership and following frames select their own section",
      noDroppedGlyph divided && divided.pages.size == 4 &&
      selectedFooters geom fs dividedDoc divided &&
      pdfFoots divided == #[("Outer", ""), ("Next", "")] &&
      htmlFooters dividedDoc == #[("Outer", ""), ("Next", "")]),
    ("column page merges preserve selected footer and paint it on every continuation",
      noDroppedGlyph columns && columns.pages.size > 1 &&
      selectedFooters geom fs columnsDoc columns &&
      (pdfFoots columns).size == columns.pages.size &&
      columns.pages.all (fun p => furnitureHas p "Note" && furnitureHas p "1")),
    ("float retry and continuation preserve the selected footer",
      noDroppedGlyph floated && floated.pages.size > 1 &&
      selectedFooters geom fs floatDoc floated &&
      (pdfFoots floated).size == floated.pages.size &&
      floated.pages.all (fun p => furnitureHas p "Note" && furnitureHas p "1"))]

/-- The partition is over physical output. Two overlays with an authored
page break contribute four pages per source, even when the next source
restarts the displayed counter. Natural overflow, flow pages, column
merges and float replay exercise the same accounting boundary. -/
def partitionChecks (fs : FontSet) : Array (String × Bool) :=
  let geom : Geom := {
    pageW := pt 220, pageH := pt 160
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let frame := Block.frame #[.text "Title"] false .top false
    #[.para #[.text "Before"], .pagebreak, .para #[.text "After"],
      .onSteps { first := 2, last := none } #[.para #[.text "Later"]]]
  let doc : Doc := {
    docClass := .slides, frameRestart := some 1, body := #[frame, frame] }
  let out := run geom fs none doc
  let openings := frameOpenings geom fs none doc
  let actual := FramePartition.origins openings
  let count := fun origin => (FramePartition.pages out (some origin)).size
  let flowDoc : Doc := { docClass := .slides, body := #[
    .para #[.text "Outside"], frame, .para #[.text "Following"]] }
  let flow := run geom fs none flowDoc
  let small := { geom with pageH := pt 100 }
  let spilling := run small fs none {
    docClass := .slides, body := #[.frame #[.text "Title"] false .top false
      (Array.replicate 24 (.para #[.text "Body"]))] }
  let standout := run geom fs none {
    docClass := .slides, body := #[.frame #[.text "Title"] true .center false
      #[.para #[.text "Body"]]] }
  let columnDoc : Doc := {
    docClass := .slides, body := #[.frame #[] false .top false #[.columns #[
      (.abs (pt 76), Array.replicate 16 (.para #[.text "Left"])),
      (.abs (pt 76), Array.replicate 20 (.para #[.text "Right"]))]]] }
  let columns := run small fs none columnDoc
  let floated := run small fs none {
    docClass := .slides, body := #[.frame #[] false .top false #[
      .para #[.text "Before"], .float .figure none false
        (Array.replicate 20 (.para #[.text "Floating"])) #[]]] }
  #[
    ("collector keys distinguish sources and overlays despite restarted counters",
      actual == [⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩] &&
      noDroppedGlyph out && out.pages.all (·.frame == some 1)),
    ("authored breaks count physical pages instead of predicting overlay counts",
      out.pages.size == 8 && actual.all (fun origin => count origin == 2) &&
      (FramePartition.pages out none).isEmpty &&
      (actual.map count).sum == out.pages.size),
    ("each source total includes all of its actual overlay pages",
      (FramePartition.sourcePages out 0).size == 4 &&
      (FramePartition.sourcePages out 1).size == 4 &&
      (FramePartition.sourcePages out 2).isEmpty &&
      FramePartition.steps openings 0 == [⟨0, 1⟩, ⟨0, 2⟩] &&
      FramePartition.steps openings 1 == [⟨1, 1⟩, ⟨1, 2⟩]),
    ("flow before and after a frame belongs only to the unowned bucket",
      noDroppedGlyph flow && flow.pages.size == 6 &&
      (FramePartition.pages flow none).size == 2 &&
      (FramePartition.sourcePages flow 1).size == 4 &&
      (FramePartition.sourcePages flow 0).isEmpty),
    ("natural spills all contribute to the actual source and step count",
      noDroppedGlyph spilling && spilling.pages.size > 1 &&
      (FramePartition.pages spilling (some ⟨0, 1⟩)).size == spilling.pages.size &&
      (FramePartition.sourcePages spilling 0).size == spilling.pages.size),
    ("a missing standout footer does not remove physical frame ownership",
      noDroppedGlyph standout && standout.pages.size == 1 &&
      standout.pages.all (·.foot.isNone) &&
      (FramePartition.pages standout (some ⟨0, 1⟩)).size == 1),
    ("column merges count every continuation once under the actual frame",
      noDroppedGlyph columns && columns.pages.size > 1 &&
      (FramePartition.pages columns (some ⟨0, 1⟩)).size == columns.pages.size &&
      (FramePartition.pages columns none).isEmpty),
    ("float replay counts every continuation once under the actual frame",
      noDroppedGlyph floated && floated.pages.size > 1 &&
      (FramePartition.pages floated (some ⟨0, 1⟩)).size == floated.pages.size &&
      (FramePartition.pages floated none).isEmpty)]

end LeanTex.Tests.LayoutContracts
