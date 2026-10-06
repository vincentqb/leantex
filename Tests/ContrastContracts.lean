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
  let data ← IO.FS.readBinFile "testdata/corpus/fonts/OpenSans-Regular.ttf"
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
  let en : Ir.Doc := { ordinary with info := { language := some "en" } }
  let pdfSummary := Check.pdfA11ySummary en #[] (Layout.Geom.ofPage en.page) fs
  let pdfAssert := fun (out : Layout.Out) =>
    Check.all { pages := out.pages.size, fontsEmbedded := true, a11y := pdfSummary out }
      #[{ kind := .accessibilityAA }]
  t "a PDF assertion accepts ordinary high-contrast text"
    (pdfAssert ordinaryOut).isEmpty
  t "a filled picture cannot borrow the document plan's clean contrast result"
    (!(pdfAssert pictureOut).isEmpty)
  t "covered runs keep an explicit unverified result without an exemption witness"
    (!(pdfAssert pendingOut).isEmpty)
  let lowInk : Ir.Color := { r := 136, g := 136, b := 136 }
  let small : Ir.Doc := { body := #[.para #[.styled (.fontSize
      (.lit { width := { sp := Dim.pt 12 } }) (.lit { width := { sp := Dim.pt 14 } }))
      #[.colored lowInk none #[.text "Small"]]]] }
  t "a low-contrast shipped run cannot pass using absent diagnostic evidence"
    (!(pdfAssert (render small)).isEmpty)
  let tinyFill : Layout.Fill :=
    { x := 0, y := 0, w := Dim.pt 1, h := Dim.pt 1, color := Ir.Color.black }
  let partialGround := { ordinaryOut with
    pages := ordinaryOut.pages.map fun page => { page with fills := page.fills.push tinyFill } }
  t "a nonuniform page ground is explicitly unverified"
    (!(pdfAssert partialGround).isEmpty)
  let boldData ← IO.FS.readBinFile "testdata/corpus/fonts/OpenSans-Bold.ttf"
  let .ok boldFont := Font.parse boldData |
    throw (IO.userError "contrast contract bold fixture failed to parse")
  let geom := Layout.Geom.ofPage ordinary.page
  let atSize := fun size (face : Font.Font) =>
    Layout.run geom (oneFaceOf face) none
      { ordinary with body := #[.para #[.styled
        (.fontSize (.lit { width := { sp := size } })
          (.lit { width := { sp := size * 6 / 5 } }))
        #[.colored lowInk none #[.text "Size"]]]] }
  for (name, size, face, expected) in #[
      ("regular below large", Dim.pt 17, font, false),
      ("regular large", Dim.pt 18, font, true),
      ("bold below large", Dim.pt 13, boldFont, false),
      ("bold large", Dim.pt 14, boldFont, true)] do
    let out := atSize size face
    let judgments := Contrast.shippedJudgments geom (oneFaceOf face) out
    let body := judgments.filter fun judgment =>
      (do
        let page ← out.pages[judgment.paint.page]?
        let line ← page.lines[judgment.paint.line]?
        pure (!line.furniture)).getD false
    let furniture := judgments.filter fun judgment =>
      (do
        let page ← out.pages[judgment.paint.page]?
        let line ← page.lines[judgment.paint.line]?
        pure line.furniture).getD false
    t s!"{name}: threshold reads the placed size and parsed font weight"
      (!body.isEmpty && body.all fun judgment =>
        match judgment.verdict with
        | .measured _ actualSize actualWeight pair =>
          actualSize == size && actualWeight == face.weight && pair.passes == expected
        | .unverified _ => false)
    t s!"{name}: generated furniture retains its own measured type size"
      (!furniture.isEmpty && furniture.all fun judgment =>
        match judgment.verdict with
        | .measured _ actualSize actualWeight pair =>
          actualSize == Dim.pt 10 && actualWeight == face.weight && pair.passes
        | .unverified _ => false)
  t "missing font metrics cannot certify a placed run"
    ((Contrast.shippedJudgments geom { fonts := #[] } ordinaryOut).all fun judgment =>
      judgment.verdict == .unverified .metrics)
  let withoutPositiveSize := { ordinaryOut with
    pages := ordinaryOut.pages.map fun page =>
      { page with
        lines := page.lines.map fun line =>
          { line with
            size := 0
            segs := line.segs.map fun
              | .run f c link w glyphs _ leading decoration raise ground attr =>
                .run f c link w glyphs 0 leading decoration raise ground attr
              | seg => seg } } }
  t "a nonpositive placed size is unverified"
    ((Contrast.shippedJudgments geom fs withoutPositiveSize).all fun judgment =>
      judgment.verdict == .unverified .nonpositiveSize)
  let mediumFill : Layout.Fill :=
    { x := -geom.bleed, y := -geom.bleed,
      w := geom.pageW + 2 * geom.bleed, h := geom.pageH + 2 * geom.bleed,
      color := Ir.Color.black }
  for page in ordinaryOut.pages do
    t "a complete later ground owns the background"
      (Contrast.uniformTextGround? geom { page with fills := #[mediumFill] } ==
        some Ir.Color.black)
    t "absence of page paint uses the PDF paper ground"
      (Contrast.uniformTextGround? geom { page with fills := #[] } == some Ir.Color.white)

end ContrastContracts

def contrastContractChecks := ContrastContracts.runContrastContractChecks
