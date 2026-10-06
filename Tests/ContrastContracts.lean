import Tests.Support

open LeanTex.Core

namespace ContrastContracts

/-- An independent observation of actual placed glyphs. Empty glyph arrays
and non-text paint do not witness a text-contrast claim. -/
private def observedContrastRuns (out : Layout.Out) :
    Array (String × Ir.Color × Option Ir.Color) := Id.run do
  let mut runs := #[]
  for page in out.pages do
    for line in page.lines do
      for seg in line.segs do
        match seg with
        | .run _ color _ _ glyphs _ _ _ _ ground _ =>
          unless glyphs.isEmpty do
            runs := runs.push
              (String.ofList (glyphs.toList.map (·.2.1)), color, ground)
        | _ => pure ()
  return runs

private def unplannedContrastRun (doc : Ir.Doc)
    (run : String × Ir.Color × Option Ir.Color) : Bool :=
  !(Contrast.judgedPairs doc).contains
    (run.2.1, run.2.2.getD (Contrast.effectivePair doc).bg)

private def contrastAddressAgrees (out : Layout.Out) (paint : Contrast.RunPaint) : Bool :=
  let seg? := do
    let page ← out.pages[paint.page]?
    let line ← page.lines[paint.line]?
    line.segs[paint.segment]?
  match seg? with
  | some (.run _ ink _ _ glyphs _ _ _ _ ground _) =>
    !glyphs.isEmpty && ink == paint.ink && ground == paint.ground
  | _ => false

/-- Counterexamples to the former claim that the document plan enumerates
every nonempty placed run. These assertions inspect `Layout.run`, including
overlay steps and picture paint; no elaboration dump supplies the witness.

Covered paint intentionally has its own quietness contract. Picture labels
also expose the separate ground problem: a run's absent ground does not say
that there is no fill behind it. Neither omission licenses a blanket text
warning over all unplanned pairs. -/
def runContrastContractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := fun name ok => check ref s!"contrast contracts: {name}" ok
  let data ← IO.FS.readBinFile "tests/corpus/fonts/OpenSans-Regular.ttf"
  let .ok font := Font.parse data |
    throw (IO.userError "contrast contract fixture font failed to parse")
  let fs := oneFaceOf font
  let render := fun (doc : Ir.Doc) => Layout.run (Layout.Geom.ofPage doc.page) fs none doc
  let ordinary : Ir.Doc := { body := #[.para #[.text "Ordinary"]] }
  let ordinaryOut := render ordinary
  let ordinaryRuns := observedContrastRuns ordinaryOut
  t "ordinary body paint is in the document plan"
    (ordinaryRuns.any fun r => r.1 == "Ordinary" && !unplannedContrastRun ordinary r)
  let pending : Ir.Doc := { body := #[
    .frame #[] false .center false #[
      .para #[.text "Shown ", .step 2 none #[.text "Pending"]]]] }
  let pendingOut := render pending
  let pendingRuns := observedContrastRuns pendingOut
  t "a real two-step frame ships computed covered paint outside the plan"
    (pendingOut.pages.size == 2 && pendingRuns.any fun r =>
      r.1 == "Pending" && r.2.1 == (Ir.Design.ofDoc pending).cover.plain &&
        unplannedContrastRun pending r &&
        Contrast.contrastMilli r.2.1
          (r.2.2.getD (Contrast.effectivePair pending).bg) < Contrast.aaText)
  t "the same overlay content also ships its active paint"
    (pendingRuns.any fun r =>
      r.1 == "Pending" && r.2.1 == Ir.Color.black && !unplannedContrastRun pending r)
  let red : Ir.Color := { r := 200, g := 0, b := 0 }
  let colored : Ir.Doc := { body := #[
    .frame #[] false .center false #[
      .para #[.step 2 none #[.colored red none #[.text "Red"]]]]] }
  let coloredOut := render colored
  let coloredRuns := observedContrastRuns coloredOut
  t "a coloured overlay computes a second unplanned pair"
    (coloredRuns.any fun r =>
      r.1 == "Red" && r.2.1 == (Ir.Design.ofDoc colored).cover.of red &&
        unplannedContrastRun colored r)
  t "the active coloured pair remains planned"
    (coloredRuns.any fun r =>
      r.1 == "Red" && r.2.1 == red && !unplannedContrastRun colored r)
  let (picture, _) := elabStr
    "\\documentclass{article}\\begin{document}\\begin{tikzpicture}\
     \\node[text=red, fill=black] {Label};\\end{tikzpicture}\\end{document}"
  let pictureOut := render picture
  let pictureRuns := observedContrastRuns pictureOut
  t "a real picture label ships ink outside the document plan"
    (pictureRuns.any fun r =>
      r.1 == "Label" && r.2.1 == ({ r := 255, g := 0, b := 0 } : Ir.Color) &&
        unplannedContrastRun picture r)
  t "picture paint includes a fill despite the label's absent ground"
    (pictureOut.pages.any fun page => page.lines.any fun line =>
      (line.segs.any fun
        | .run _ _ _ _ glyphs _ _ _ _ ground _ =>
          String.ofList (glyphs.toList.map (·.2.1)) == "Label" && ground.isNone
        | _ => false) &&
      page.paths.any fun path =>
        path.fill == some Ir.Color.black && path.leaf == line.leaf)
  for (name, doc, out) in #[
      ("ordinary", ordinary, ordinaryOut), ("pending", pending, pendingOut),
      ("coloured pending", colored, coloredOut), ("picture", picture, pictureOut)] do
    let audit := Contrast.shippedAudit (Contrast.effectivePair doc).bg Contrast.aaText out
    let observed := observedContrastRuns out
    t s!"{name}: audit retains every observed pair in order, including repeated paint"
      (audit.map (fun a => (a.paint.ink, a.paint.ground)) ==
        observed.map (fun r => (r.2.1, r.2.2)))
    t s!"{name}: every audit address points to its actual nonempty run"
      (audit.all fun a => contrastAddressAgrees out a.paint)
    t s!"{name}: every observed below-threshold occurrence remains in failures"
      ((Contrast.shippedFailures (Contrast.effectivePair doc).bg Contrast.aaText out).size ==
        (observed.filter fun r =>
          Contrast.contrastMilli r.2.1
            (r.2.2.getD (Contrast.effectivePair doc).bg) < Contrast.aaText).size)
  let pendingAudit :=
    Contrast.shippedAudit (Contrast.effectivePair pending).bg Contrast.aaText pendingOut
  t "covered paint remains a raw arithmetic observation"
    (pendingAudit.any fun a =>
      a.paint.ink == (Ir.Design.ofDoc pending).cover.plain && !a.assessment.passes)
  t "equal active ink on distinct pages retains distinct addresses"
    ((pendingAudit.filter fun a =>
      a.paint.page == 0 && a.paint.ink == Ir.Color.black).size > 0 &&
      (pendingAudit.filter fun a =>
        a.paint.page == 1 && a.paint.ink == Ir.Color.black).size > 0)
  t "ordinary text has no arithmetic failure"
    ((Contrast.shippedFailures (Contrast.effectivePair ordinary).bg
      Contrast.aaText ordinaryOut).isEmpty)

end ContrastContracts

def contrastContractChecks := ContrastContracts.runContrastContractChecks
