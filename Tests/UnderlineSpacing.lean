module

public import Tests.Artifact

public section

open LeanTex.Core
open LeanTex.Core.PdfRead (Obj)

/-- Positive interior spacing of a shipped text line. The closing fill and
line-breaking spaces are absent; authored horizontal spacing is included. -/
private def spacingGaps (line : Layout.LineOut) : Array (Dim.Sp × Dim.Sp) := Id.run do
  let mut x := line.x
  let mut seen := false
  let mut gaps := #[]
  for (seg, i) in line.segs.zipIdx do
    match seg with
    | .run _ _ _ w gs _ _ _ _ _ _ =>
      seen := seen || !gs.isEmpty
      x := x + w
    | .gap w _ | .decoratedGap w _ _ =>
      let later := (line.segs.extract (i + 1) line.segs.size).any fun s => match s with
        | .run _ _ _ _ gs _ _ _ _ _ _ => !gs.isEmpty
        | _ => false
      if seen && later && 0 < w then gaps := gaps.push (x, w)
      x := x + w
    | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return gaps

/-- Actual decoration rectangles in trim coordinates (y down), independent
of the source flag that requested them. -/
private def spacingPaint (line : Layout.LineOut) : Array (Ir.Decoration × Layout.Fill) := Id.run do
  let mut x := line.x
  let mut paint := #[]
  for seg in line.segs do
    match seg with
    | .decoration kind w thickness raise color =>
      paint := paint.push (kind,
        { x := x, y := line.y - raise - thickness, w := w, h := thickness, color := color })
      x := x + w
    | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
      | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return paint

/-- Resolve annotations from their owning pages, including inline dictionaries. -/
private def spacingLinkAnnots (pdf : ByteArray) : Except String (Array Obj) := do
  let es ← PdfRead.objects pdf
  let mut links := #[]
  for e in es.val do
    if PdfCensus.kindOf e.val == .page then
      if let .arr annots := PdfCensus.deref es.val ((e.val.get? "Annots").getD .null) then
        for raw in annots do
          let annot := PdfCensus.deref es.val raw
          if PdfCensus.kindOf annot == .annot "Link" then links := links.push annot
  return links

private def spacingWitness (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (geom : Layout.Geom) (label source control : String) (strike : Bool := false)
    (minLines : Nat := 1) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr source
  let (plain, pds) := elabStr control
  let out := layoutOf fonts doc geom
  let baseline := layoutOf fonts plain geom
  t (label ++ ": diagnostics")
    ((ds ++ pds ++ out.diags ++ baseline.diags).all (·.severity == .note))
  let glyphGeometry (o : Layout.Out) := (shippedBodyGlyphs o).map fun g =>
    (g.page, g.face, g.glyph, g.scalar, g.x, g.y, g.advance, g.size, g.expand,
      g.color, g.leading, g.ground)
  t (label ++ ": decoration preserves glyph geometry and paint")
    (glyphGeometry out == glyphGeometry baseline)
  let lines := (bodyLines out).filter fun l => l.segs.any fun s => match s with
    | .run _ _ _ _ gs _ _ _ _ _ _ => !gs.isEmpty
    | _ => false
  t (label ++ ": text line extent") (lines.size ≥ minLines)
  let paints := (bodyLines out).flatMap spacingPaint
  t (label ++ ": no accidental through-line")
    ((paints.any (·.1 == .lineThrough)) == strike)
  let gaps := lines.flatMap fun l => (spacingGaps l).map fun (x, w) => (l.y, x, w)
  t (label ++ ": nonvacuous interior spacing") (!gaps.isEmpty)
  let pdf := driverPdf fonts geom doc out
  let plainPdf := driverPdf fonts geom plain baseline
  match readArtifact pdf, readArtifact plainPdf with
  | .ok pages, .ok plainPages =>
    t (label ++ ": PDF preserves text and positions")
      (pages.map (fun p => p.runs.map fun r => (r.text, r.face, r.x, r.y, r.w)) ==
        plainPages.map (fun p => p.runs.map fun r => (r.text, r.face, r.x, r.y, r.w)))
    for (y, x, w) in gaps do
      let mid := x + w / 2
      t (label ++ ": Layout.Out underlines space") (paints.any fun (kind, r) =>
        kind == .underline && r.x ≤ mid && mid < r.x + r.w &&
          y < r.y && r.y < y + geom.fontSize / 2)
      let px := geom.bleed + mid
      let py := geom.bleed + geom.pageH - y
      t (label ++ ": emitted PDF underlines space") (pages.any fun p => p.boxes.any fun b =>
        b.kind == "fill" && b.x0 ≤ px && px < b.x1 &&
          py - geom.fontSize / 2 < b.y0 && b.y1 < py)
      if strike then
        t (label ++ ": through-line still covers space") (paints.any fun (kind, r) =>
          kind == .lineThrough && r.x ≤ mid && mid < r.x + r.w && r.y < y)
  | .error e, _ => t (label ++ ": PDF read: " ++ e) false
  | _, .error e => t (label ++ ": control PDF read: " ++ e) false
  if hasStr source "https://example.org/spacing" then
    match spacingLinkAnnots pdf with
    | .ok links =>
      t (label ++ ": emitted link destination survives") (!links.isEmpty && links.all fun e =>
        let action := (e.get? "A").getD .null
        action.get? "URI" == some (.str "(https://example.org/spacing)".toUTF8))
    | .error e => t (label ++ ": PDF links: " ++ e) false

/-- Multiword underline must paint the set space, in native layout and in
the emitted PDF, without changing spacing, line breaks, glyphs or links.
Every phrase is synthetic; the oracle reads shipped rectangles. -/
def underlineSpacingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let geom : Layout.Geom := {}
  let phrase := "Amber Cedar Stone"
  for (label, source, strike) in
      [("link", "\\href{https://example.org/spacing}{" ++ phrase ++ "}", false),
       ("underline", "\\underline{" ++ phrase ++ "}", false),
       ("uline", "\\uline{" ++ phrase ++ "}", false),
       ("underline strike", "\\underline{\\sout{" ++ phrase ++ "}}", true),
       ("strike underline", "\\sout{\\underline{" ++ phrase ++ "}}", true),
       ("strike link", "\\sout{\\href{https://example.org/spacing}{" ++ phrase ++ "}}", true)] do
    spacingWitness ref fonts geom label source phrase strike
  let spaced := "Amber\\hspace{12pt}Cedar\\hspace{8pt}Stone"
  spacingWitness ref fonts geom "authored gaps" ("\\underline{" ++ spaced ++ "}") spaced
  let long := String.intercalate " " (List.replicate 8 phrase)
  let narrow := { geom with pageW := Dim.pt 300, hmargin := Dim.pt 30 }
  spacingWitness ref fonts narrow "broken justified link"
    ("\\href{https://example.org/spacing}{" ++ long ++ "}") long false 3
  let signed := "Amber\\hspace{-2pt}Cedar\\hspace{0pt}Stone Birch"
  spacingWitness ref fonts geom "zero and negative spacing"
    ("\\underline{" ++ signed ++ "}") signed
  let styled := "\\textcolor{blue}{Amber }\\textit{Cedar }{\\large Stone }\\textbf{Birch}"
  match ← serifFacesSet with
  | none => check ref "spacing: shipped style faces load" false
  | some faces =>
    spacingWitness ref faces geom "font color size transitions"
      ("\\underline{" ++ styled ++ "}") styled
  let plain := layoutOf fonts (elabStr phrase).1 geom
  check ref "plain spacing has no decoration" (((bodyLines plain).flatMap spacingPaint).isEmpty)

  -- A shared framefooter containing only an automatic link (no explicit
  -- underline), then the explicit spelling through the same furniture path.
  let wrapper := "\\newenvironment{framefooter}[1]" ++
    "{\\setbeamertemplate{frame footer}{#1}}{\\setbeamertemplate{frame footer}{}}"
  for (label, footer) in
      [("footer link", "\\href{https://example.org/spacing}{" ++ phrase ++ "}"),
       ("footer underline", "\\underline{" ++ phrase ++ "}")] do
    let source := deck169 ("\\theme{moloch}" ++ wrapper)
      ("\\begin{framefooter}{" ++ footer ++ "}\n" ++
       "\\begin{frame}{First}North \\pause East\\end{frame}\n" ++
       "\\begin{frame}{Second}South \\pause West\\end{frame}\n" ++
       "\\end{framefooter}")
    let (doc, ds) := elabStr source
    let geom := Layout.Geom.ofPage doc.page
    let out := layoutOf fonts doc
    check ref (label ++ ": diagnostics")
      ((ds ++ out.diags).all (·.severity == .note))
    check ref (label ++ ": four overlay pages") (out.pages.size == 4)
    match readArtifact (driverPdf fonts geom doc out) with
    | .error e => check ref (label ++ ": PDF read: " ++ e) false
    | .ok pages =>
      check ref (label ++ ": native page count") (pages.size == out.pages.size)
      for (page, i) in out.pages.zipIdx do
        let lines := page.lines.filter fun l => l.furniture && hasStr (lineText l) phrase
        check ref (label ++ ": footer phrase on each page") (lines.size == 1)
        let paint := (page.lines.filter (·.furniture)).flatMap spacingPaint
        for line in lines do
          let gaps := spacingGaps line
          check ref (label ++ ": two word spaces") (gaps.size == 2)
          for (x, w) in gaps do
            let mid := x + w / 2
            check ref (label ++ ": Layout.Out footer underlines space")
              (paint.any fun (kind, r) => kind == .underline && r.x ≤ mid && mid < r.x + r.w &&
                line.y < r.y && r.y < line.y + line.size / 2)
            let px := geom.bleed + mid
            let py := geom.bleed + geom.pageH - line.y
            check ref (label ++ ": emitted PDF footer underlines space")
              ((pages[i]?.map fun p => p.boxes.any fun b => b.kind == "fill" &&
                b.x0 ≤ px && px < b.x1 && py - line.size / 2 < b.y0 && b.y1 < py).getD false)
