import Tests.Artifact

open LeanTex.Core
open LeanTex.Core.Dim (Sp pt)

private structure AlphaGlyph where
  scalar : Char
  face : Nat
  x : Sp
  y : Sp
  advance : Sp
  size : Sp
  bottom : Sp
  top : Sp

private structure AlphaInk where
  glyphs : Array AlphaGlyph := #[]
  bars : Array ArtRect := #[]

private def alphaLaidInk (fs : Font.FontSet) (geom : Layout.Geom)
    (out : Layout.Out) : Except String AlphaInk := do
  let mut ink : AlphaInk := {}
  for line in bodyLines out do
    unless line.expand == 0 do throw "the probe unexpectedly expands a line"
    let y := geom.bleed + geom.pageH - line.y
    let mut x := geom.bleed + line.x
    for seg in line.segs do
      match seg with
      | .run fi _ _ w gs size _ _ raise _ _ =>
        let f := fs.get fi
        let mut pen := x
        for (gid, scalar, advance) in gs do
          let some (lo, hi) := f.yExtent gid | throw s!"{f.psName}: no outline for {scalar}"
          ink := { ink with glyphs := ink.glyphs.push {
            scalar, face := fi, x := pen, y := y + raise, advance, size
            bottom := y + raise + lo * size / f.unitsPerEm
            top := y + raise + hi * size / f.unitsPerEm } }
          pen := pen + advance
        x := x + w
      | .rule w thick raise _ =>
        ink := { ink with bars := ink.bars.push {
          x0 := x, x1 := x + w, y0 := y + raise, y1 := y + raise + thick } }
        x := x + w
      | .gap w _ => x := x + w
      | .poly _ _ | .image _ _ _ => throw "unexpected ink in the math probe"
  return ink

private def alphaPaintedInk (fs : Font.FontSet) (pdf : ByteArray)
    (pages : Array ArtPage) : Except String AlphaInk := do
  unless pages.size == 1 do throw "the probe must paint exactly one page"
  let es := (← PdfRead.objects pdf).val
  let deref := PdfCensus.deref es
  let embedded ← artEmbedded pdf
  let mut names : Array (String × Nat) := #[]
  for e in es do
    unless e.val.get? "Type" == some (.name "Page") do continue
    let res := deref ((e.val.get? "Resources").getD .null)
    let .dict fonts := deref ((res.get? "Font").getD .null)
      | throw "the page has no font resources"
    for (name, v) in fonts do
      let .arr descendants := deref ((deref v).get? "DescendantFonts" |>.getD .null)
        | throw s!"{name}: no descendant font"
      let cid := deref (descendants[0]?.getD .null)
      let fd := deref ((cid.get? "FontDescriptor").getD .null)
      let some (.name fn) := fd.get? "FontName" | throw s!"{name}: no font name"
      let some fi := fs.fonts.findIdx? (·.psName == artBaseName fn)
        | throw s!"{fn}: not a probe face"
      names := names.push (name, fi)
  let mut consumed := Array.replicate fs.fonts.size 0
  let mut ink : AlphaInk := {}
  for page in pages do
    for run in page.runs do
      let some (_, fi) := names.find? (·.1 == run.face)
        | throw s!"{run.face}: no resource"
      let f := fs.get fi
      let some (_, program, gids) := embedded.find? (fun e => artBaseName e.1 == f.psName)
        | throw s!"{f.psName}: no embedded program"
      let outline := Ink.Src.make program f.isCff f.numGlyphs
      for h : i in [0:run.glyphs.size] do
        let used := consumed[fi]?.getD 0
        let some gid := gids[used]? | throw s!"{f.psName}: missing painted glyph id"
        consumed := consumed.setIfInBounds fi (used + 1)
        if run.isArtifact then continue
        let (x, text) := run.glyphs[i]
        let [scalar] := text.toList | throw s!"unexpected glyph mapping: {text}"
        let some (lo, hi) := outline.yExtentAt gid
          | throw s!"{f.psName}: the embedded outline of {scalar} is unreadable"
        let next := (run.glyphs[i + 1]?.map (·.1)).getD run.x1
        ink := { ink with glyphs := ink.glyphs.push {
          scalar, face := fi, x, y := run.y, advance := next - x, size := run.size
          bottom := run.y + lo * run.size / f.unitsPerEm
          top := run.y + hi * run.size / f.unitsPerEm } }
    for box in page.boxes do
      ink := { ink with bars := ink.bars.push {
        x0 := box.x0, x1 := box.x1, y0 := box.y0, y1 := box.y1 } }
  for (fn, _, gids) in embedded do
    let some fi := fs.fonts.findIdx? (·.psName == artBaseName fn)
      | throw s!"{fn}: not a probe face"
    unless consumed[fi]? == some gids.size do throw s!"{fn}: glyph census differs"
  return ink

private def alphaReadings (fs : Font.FontSet) (body : String) :
    Except String (AlphaInk × AlphaInk) := do
  let (raw, ds) := elabStr (metricDoc body)
  let (doc, ads) := Ir.resolveMathAlphas fs.mathAlphabets "Fira Math" raw
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom fs none doc
  let losses := (ds ++ ads ++ out.diags).filter fun d =>
    d.severity == .error || #["W0012", "W0016", "W0009"].contains d.code
  unless losses.isEmpty do throw s!"unexpected loss: {losses.map (·.code)}"
  let laid ← alphaLaidInk fs geom out
  let pdf := driverPdf fs geom doc out
  let pages ← readArtifact pdf
  let misplaced := artGlyphPlacementOffences (out.pages.flatMap (artLaidGlyphs geom))
    (pages.flatMap artPaintedGlyphs)
  unless misplaced.isEmpty do throw s!"PDF glyph placement: {misplaced}"
  return (laid, ← alphaPaintedInk fs pdf pages)

private def alphaGeometryFonts : IO (Except String Font.FontSet) := do
  let some fs ← serifFacesSet | return .error "the shipped serif/math faces did not load"
  let mut fonts := fs.fonts
  for n in #["OpenSans-Regular.ttf", "OpenSans-Bold.ttf", "OpenSans-Italic.ttf",
      "OpenSans-BoldItalic.ttf", "SourceCodePro-Regular.otf"] do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ n)) with
    | .error e => return .error s!"{n}: {e}"
    | .ok f => fonts := fonts.push f
  return .ok { fs with
    fonts := fonts
    index := #[((0, 400, false), 0), ((0, 700, false), 1),
      ((0, 400, true), 2), ((0, 700, true), 3),
      ((1, 400, false), 5), ((1, 700, false), 6),
      ((1, 400, true), 7), ((1, 700, true), 8), ((2, 400, false), 9)] }

private def alphaNear (a b slack : Sp) : Bool := (a - b).natAbs ≤ slack.toNat

private structure AlphaRoot where
  body : String
  children : Array Nat := #[]
  style : Math.MathStyle := .text false

private structure AlphaRootCase where
  name : String
  source : String
  roots : Array AlphaRoot

private def alphaRootCases : Array AlphaRootCase := #[
  { name := "serif capital", source := "$\\sqrt{\\mathrm{L}}$"
    roots := #[{ body := "L" }] },
  { name := "bold descender and italic digit", source := "$\\sqrt{\\mathbf{Mg}\\mathit{5}}$"
    roots := #[{ body := "Mg5" }] },
  { name := "nested root with subscript"
    source := "$\\sqrt{\\mathrm{L}+\\sqrt{\\mathbf{Mg}_{\\mathit{5}}}}$"
    roots := #[{ body := "L+Mg5", children := #[1] }, { body := "Mg5" }] },
  { name := "root in superscript"
    source := "$x^{\\sqrt{\\mathit{5}\\mathbf{M}_{\\mathrm{q}}}}$"
    roots := #[{ body := "5Mq", style := .script false }] },
  { name := "root around raised and lowered roots"
    source := "$\\sqrt{\\mathrm{M}_{\\sqrt{\\mathit{5}\\mathbf{g}}}^{\\mathrm{Q}}}$"
    roots := #[{ body := "M5gQ", children := #[1] },
      { body := "5g", style := .script false }] },
  { name := "different units per em"
    source := "$\\sqrt{\\mathsf{Hq}+\\sqrt{\\mathrm{L}^{\\mathit{5}}}}$"
    roots := #[{ body := "Hq+L5", children := #[1] }, { body := "L5" }] },
  { name := "display clearance"
    source := "\\[\\sqrt{\\mathsf{Hq}\\mathrm{L}}\\]"
    roots := #[{ body := "HqL", style := .display false }] }]

/-- Text alphabet sizes and advances follow the surrounding text size;
radical bars clear every operand's own font outline, including nested roots
and scripts. Both the shipped layout and native PDF are judged. The PDF
reading uses its font resources, embedded glyph ids/outlines, Tf sizes,
and viewer advances, independently of the layout's extent computation. -/
def mathAlphaGeometryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let .ok fs ← alphaGeometryFonts | failures ref "math alpha geometry: shipped fonts"; return
  let some (_, math, consts) := fs.mathFont?
    | failures ref "math alpha geometry: math constants"; return
  t "math alpha geometry: the probe spans different font units"
    ((fs.get 0).unitsPerEm != (fs.get 5).unitsPerEm)
  let mathSize := (Math.mathSize (pt 10).toNat (fs.get 0).xHeightOptical
    (fs.get 0).unitsPerEm math.xHeightOptical math.unitsPerEm : Sp)
  t "math alpha geometry: text and math sizes differ in the probe" (mathSize != pt 10)
  for c in alphaRootCases do
    match alphaReadings fs c.source with
    | .error e => t s!"math alpha geometry: {c.name}: {e}" false
    | .ok (laid, painted) =>
      for (backend, ink, slack) in #[("layout", laid, 0), ("PDF", painted, artSpellSlack)] do
        let roots := ink.glyphs.filter (·.scalar == '√')
        t s!"math alpha geometry: {c.name}/{backend}: root/bar census"
          (roots.size == c.roots.size && ink.bars.size == c.roots.size)
        for h : i in [0:c.roots.size] do
          let spec := c.roots[i]
          let some root := roots[i]? | t s!"math alpha geometry: {c.name}: missing root" false; continue
          let some bar := ink.bars[i]? | t s!"math alpha geometry: {c.name}: missing bar" false; continue
          let body := ink.glyphs.filter (fun g => spec.body.contains g.scalar)
          t s!"math alpha geometry: {c.name}/{backend}/{i}: operand census"
            (body.size == spec.body.length &&
              spec.body.toList.all (fun ch => body.any (·.scalar == ch)))
          let some first := body[0]? | t s!"math alpha geometry: {c.name}: empty operand" false; continue
          let top := body.foldl (fun a g => max a g.top) first.top
          let bottom := body.foldl (fun a g => min a g.bottom) first.bottom
          let top := spec.children.foldl (fun a j =>
            max a ((roots[j]?.map (·.top)).getD a)) top
          let bottom := spec.children.foldl (fun a j =>
            min a ((roots[j]?.map (·.bottom)).getD a)) bottom
          let gapUnits := match spec.style with
            | .display _ => consts.radicalDisplayStyleVerticalGap
            | _ => consts.radicalVerticalGap
          let gap := gapUnits * root.size / math.unitsPerEm
          t s!"math alpha geometry: {c.name}/{backend}/{i}: bar clears own-face ink"
            (bar.y0 + slack ≥ top + gap)
          t s!"math alpha geometry: {c.name}/{backend}/{i}: surd covers operand depth"
            (root.bottom ≤ bottom + slack)
          t s!"math alpha geometry: {c.name}/{backend}/{i}: surd meets bar at its style size"
            (alphaNear root.top bar.y1 slack &&
              alphaNear root.size (Math.sizeFor consts.scales mathSize spec.style) slack)
          t s!"math alpha geometry: {c.name}/{backend}/{i}: bar covers operand advance"
            (body.all fun g => bar.x0 ≤ g.x + slack && g.x + g.advance ≤ bar.x1 + slack)
  for (ambient, ambientFace, ambientSize) in
      #[("", 0, pt 10), ("\\fontsize{17pt}{22pt}\\selectfont ", 0, pt 17),
        ("\\sffamily\\bfseries\\itshape ", 8, pt 10)] do
    for (cmd, face) in #[("mathrm", 0), ("mathbf", 1), ("mathit", 2), ("mathsf", 5), ("mathtt", 9)] do
      let src := "{" ++ ambient ++ "Z $\\" ++ cmd ++ "{x5}_{\\" ++ cmd ++ "{g}}^{\\" ++
        cmd ++ "{M}^{\\" ++ cmd ++ "{Q}}}\\symup{7}$}"
      let label := s!"math alpha size: {cmd}/{ambientFace}/{ambientSize}"
      match alphaReadings fs src with
      | .error e => t s!"{label}: {e}" false
      | .ok (laid, painted) =>
        let around := fs.get ambientFace
        let symbolSize := (Math.mathSize ambientSize.toNat around.xHeightOptical
          around.unitsPerEm math.xHeightOptical math.unitsPerEm : Sp)
        for (backend, ink, slack) in #[("layout", laid, 0), ("PDF", painted, artSpellSlack)] do
          t s!"{label}/{backend}: scalar census"
            (String.ofList (ink.glyphs.toList.map (·.scalar)) == "Zx5MQg7")
          for g in ink.glyphs do
            let expectedFace := if g.scalar == 'Z' then ambientFace
              else if g.scalar == '7' then 4 else face
            let expectedSize := if g.scalar == '7' then symbolSize
              else if g.scalar == 'M' || g.scalar == 'g' then ambientSize * consts.scales.script / 100
              else if g.scalar == 'Q' then ambientSize * consts.scales.scriptscript / 100
              else ambientSize
            let f := fs.get expectedFace
            let some gid := f.gid g.scalar | t s!"{label}: missing probe scalar" false; continue
            let width := (f.widths[gid]?.getD 0 : Sp) * expectedSize / f.unitsPerEm
            t s!"{label}/{backend}/{g.scalar}: face and ambient style size"
              (g.face == expectedFace && alphaNear g.size expectedSize slack)
            t s!"{label}/{backend}/{g.scalar}: own-face advance at ambient style size"
              (alphaNear g.advance width (if slack == 0 then 0 else slack + expectedSize / 1000))
