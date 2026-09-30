import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj)

private def pdfLinkTargets (pdf : ByteArray) : Except String (Array ByteArray) := do
  let es ← PdfRead.objects pdf
  let mut out : Array ByteArray := #[]
  for e in es.val do
    if PdfCensus.kindOf e.val == .page then
      match PdfCensus.deref es.val ((e.val.get? "Annots").getD .null) with
      | .arr annots =>
        for raw in annots do
          let annot := PdfCensus.deref es.val raw
          if PdfCensus.kindOf annot == .annot "Link" then
            let action := PdfCensus.deref es.val ((annot.get? "A").getD .null)
            if let some (Obj.str target) := action.get? "URI" then
              out := out.push target
      | _ => pure ()
  return out

private def countTag (tag : String) : Html.Node → Nat
  | .text _ | .style _ | .script _ _ => 0
  | .elem t _ kids => (if t == tag then 1 else 0) + kids.foldl (fun n k => n + countTag tag k) 0

mutual

private def pdfFillsOne
    (out : Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)) :
    Pdf.ContentOp → Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)
  | .fill color x y w h => out.push (color, x, y, w, h)
  | .marked _ body => pdfFillsList out body.toList
  | .path _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ => out

private def pdfFillsList
    (out : Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)) :
    List Pdf.ContentOp → Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp)
  | [] => out
  | op :: rest => pdfFillsList (pdfFillsOne out op) rest

end

/-- **A recognized content wrapper consumes its target and preserves a block body.**
Hyperref defines `\hyperlink{target}{text}` and `\hypertarget{target}{text}` as
two-group wrappers (hyperref.sty, `\def\hyperlink` and `\def\hypertarget`).
Their content may be a box: the wrapper's name group is configuration, while
the second group is recursively elaborated through the ordinary minipage and
table paths. The page assertion reads `Layout.Out`; the web assertions read
the typed tree. -/
def recipeLinkWrapperChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\usepackage{hyperref}\n" (
    "\\hypertarget{panel}{\\begin{minipage}{.42\\textwidth}\n" ++
    "Target panel.\\begin{tabular}{ll}Alpha&Beta\\\\Gamma&Delta\\end{tabular}\n" ++
    "\\end{minipage}}\n\n" ++
    "\\hyperlink{panel}{\\begin{minipage}{.42\\textwidth}\n" ++
    "Linked panel.\\begin{tabular}{ll}One&Two\\\\Three&Four\\end{tabular}\n" ++
    "\\end{minipage}}")
  let (doc, ds) := elabStr src
  let cascade := ["W0301", "W0302", "E0336", "E0311"]
  t "internal link wrappers produce no unknown-command or wrapper cascade"
    (ds.all fun d => !cascade.contains d.code)
  let out := layoutOf oneFace doc
  let pageText := " ".intercalate ((allLines out).toList.map lineText)
  t "internal link wrappers preserve both nested minipage and table bodies on the page"
    (["Target panel.", "Alpha", "Delta", "Linked panel.", "One", "Four"].all
      (hasStr pageText ·))
  let anchorBody := "\\begin{minipage}{.42\\textwidth}Anchor position.\\end{minipage}"
  let placed (body : String) :=
    (allLines (layoutOf oneFace (elabStr (dvDoc "" body)).1)).filterMap fun l =>
      if l.segs.isEmpty || l.furniture then none else some (lineText l, l.x, l.y)
  t "a block target adds no page spacing or displacement"
    (placed ("\\hypertarget{spot}{" ++ anchorBody ++ "}") == placed anchorBody)
  t "the linked block reaches Layout.Out as one whole-block rectangle"
    (match out.pages[0]?.bind (·.links[0]?) with
     | some rect =>
       (out.pages[0]?.map (·.links.size == 1)).getD false && rect.target == "#panel" &&
         ((allLines out).filter (fun l =>
           ["Linked panel.", "One", "Two", "Three", "Four"].any (hasStr (lineText l) ·))).all
           fun l => rect.x ≤ l.x && l.x + l.setWidth ≤ rect.x + rect.w &&
             rect.y ≤ l.y && l.y ≤ rect.y + rect.h
     | none => false)
  let trees := doc.body.map (HtmlDoc.blockNode {})
  let hrefs := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let ids := trees.foldl
    (fun acc n => acc ++ attrValuesOf (fun _ => true) "id" n) #[]
  t "the typed HTML tree carries exactly one matching internal link"
    (ids.contains "panel" && hrefs == #["#panel"])
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) oneFace out.pages doc.info
  t "the PDF artifact carries exactly one matching block-link annotation"
    (pdfLinkTargets pdf == .ok #["(#panel)".toUTF8])
  t "the typed HTML tree keeps both nested tables"
    (trees.foldl (fun n tree => n + countTag "table" tree) 0 == 2)
  let (nestedDoc, nestedDs) := elabStr (dvDoc "\\usepackage{hyperref}\n"
    ("\\hyperlink{outer}{\\begin{minipage}{.4\\textwidth}" ++
      "Outer words and \\href{https://example.org}{inner words}.\\end{minipage}}"))
  let nestedTrees := nestedDoc.body.map (HtmlDoc.blockNode {})
  let nestedHrefs := nestedTrees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  t "a nested link keeps the inner link and truthfully refuses only the outer wrapper"
    ((nestedDs.filter (·.code == "W0104")).size == 1 &&
      nestedHrefs.contains "https://example.org" && !nestedHrefs.contains "#outer" &&
      nestedTrees.foldl (fun n tree => n + treeShownOccurs #[tree] "Outer words") 0 == 1)

/-- **A titlepage is one isolated, furniture-free flow page.** Article's
installed class opens a fresh page, applies the empty page style, and opens
another page at the close (`article.cls`, `titlepage`). Its body remains an
ordinary block sequence: explicit infinite glue controls vertical placement.
Assertions read the shipped pages under the document's own flow geometry and
the typed HTML tree. -/
def recipeTitlePageChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc
    "\\page{ width = 420pt, height = 600pt, hmargin = 54pt, vmargin = 48pt }\n"
    ("Lead page.\\begin{titlepage}\nTop marker.\n" ++
      "\\vfill\nBottom marker.\\end{titlepage}Tail page.")
  let (doc, ds) := elabStr src
  let cascade := ["W0302", "E0336", "E0311"]
  t "titlepage is recognized without an unknown-wrapper cascade"
    (ds.all fun d => !cascade.contains d.code)
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  let census := censusOf (coveredColorsOf doc) out
  t "titlepage uses the document's flow geometry"
    (match lineXOf census 1 "Top marker.", lineXOf census 1 "Bottom marker." with
     | some top, some bottom => top == doc.page.hmargin && bottom == doc.page.hmargin
     | _, _ => false)
  t "titlepage opens and closes exactly one physical page"
    (out.pages.size == 3 && pageHas census 0 "Lead page." &&
      pageHas census 1 "Top marker." &&
      pageHas census 1 "Bottom marker." &&
      pageHas census 2 "Tail page.")
  t "titlepage carries no running furniture"
    ((out.pages[1]?.map fun p => p.lines.all (!·.furniture)).getD false)
  t "titlepage keeps its explicit infinite-glue vertical distribution"
    (match lineYOf census 1 "Top marker.",
        lineYOf census 1 "Bottom marker." with
     | some top, some bottom => top < bottom && bottom - top > geom.textHeight / 2
     | _, _ => false)
  let trees := doc.body.map (HtmlDoc.blockNode {})
  t "typed HTML keeps titlepage as one section with its body once"
    (trees.foldl (fun n tree => n + countTag "section" tree) 0 == 1 &&
      trees.foldl (fun n tree => n + treeShownOccurs #[tree] "Top marker.") 0 == 1 &&
      trees.foldl (fun n tree => n + treeShownOccurs #[tree] "Bottom marker.") 0 == 1)

/-- **Paracol's two flows are one typed columns row.** The installed package
sets each column's width from `\columnratio`, gives the final column the
remainder, and makes bare `\switchcolumn` advance cyclically while `[n]`
selects column n (paracol.sty, `\pcol@setcolwidth@r` and
`\pcol@com@switchcolumn`). Repeated switches append to each independent
flow. Assertions read the IR, Layout.Out, and typed HTML. -/
def recipeParacolChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\usepackage{paracol}\n\\columnratio{.35}\n" (
    "\\begin{paracol}{2}\nLeft first.\n" ++
    "\\begin{minipage}{\\columnwidth}Left nested box.\\end{minipage}\n" ++
    "\\switchcolumn\nRight first.\\begin{tabular}{ll}R1&R2\\\\R3&R4\\end{tabular}\n" ++
    "\\switchcolumn[0]\nLeft second.\n\\end{paracol}")
  let (doc, ds) := elabStr src
  let cascade := ["W0103", "W0301", "W0302", "E0336", "E0311"]
  t "paracol's supported two-flow family produces no package or wrapper cascade"
    (ds.all fun d => !cascade.contains d.code)
  let cols := doc.body.findSome? fun b => match b with
    | .columns cs => some cs
    | _ => none
  t "columnratio maps to declared complementary column widths"
    ((cols.map fun cs => cs.map (fun c => c.1.size)) ==
      some #[.frac 350, .frac 650])
  let out := layoutOf oneFace doc
  let census := censusOf (coveredColorsOf doc) out
  t "switchcolumn appends each segment to its selected flow"
    (match lineXOf census 0 "Left first.", lineXOf census 0 "Left second.",
        lineXOf census 0 "Right first." with
     | some l1, some l2, some r => l1 == l2 && l1 < r
     | _, _, _ => false)
  t "nested supported bodies remain structural and ship once"
    (pageOccurs census 0 "Left nested box." == 1 &&
      ["R1", "R2", "R3", "R4"].all (pageHas census 0 ·))
  let trees := doc.body.map (HtmlDoc.blockNode {})
  let styles := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "div") "style" n) #[]
  t "typed HTML projects the same two ratio tracks"
    (styles.any (hasStr · "grid-template-columns: 35% 65%") &&
      trees.foldl (fun n tree => n + countTag "table" tree) 0 == 1)
  let (starDoc, starDs) := elabStr (dvDoc "\\usepackage{paracol}\n"
    "\\begin{paracol}{2}Left.\\switchcolumn*[Spanning words.]Right.\\end{paracol}")
  t "a synchronized switch is one truthful refusal with its text preserved"
    ((starDs.filter (·.code == "W0104")).size == 1 &&
      starDs.all (fun d => !["W0301", "W0302", "E0336"].contains d.code) &&
      ((Ir.blocksText starDoc.body).splitOn "Spanning words.").length == 2)

/-- **A tabularx X column receives the target's remaining width.** The
installed package rewrites X to a paragraph column, repeatedly choosing its
width so the table reaches the first argument (`tabularx.sty`,
`\TX@endtabularx`, `\TX@arith`, and `\tabularxcolumn`). The target is the
enclosing measure when written as `\linewidth`, including inside a
minipage. Assertions read Layout.Out and the typed HTML table. -/
def recipeTabularxChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\usepackage{tabularx}\n" (
    "\\begin{minipage}{.6\\textwidth}\\begin{tabularx}{\\linewidth}{lX}\n" ++
    "Key & Alpha bravo charlie delta echo foxtrot golf hotel india juliet kilo lima.\\\\\n" ++
    "End & Short value.\\end{tabularx}\\end{minipage}")
  let (doc, ds) := elabStr src
  let cascade := ["W0103", "W0301", "W0302", "W0104", "E0336", "E0311"]
  t "tabularx and X produce no package, environment, or column-type cascade"
    (ds.all fun d => !cascade.contains d.code)
  let out := layoutOf oneFace doc
  let census := censusOf (coveredColorsOf doc) out
  t "tabularx preserves its nested table body on the shipped page"
    (["Key", "Alpha", "kilo", "End", "Short value."].all (pageHas census 0 ·) &&
      (ds ++ out.diags).all (·.code != "W0338"))
  t "the X cell wraps at one stable column origin inside the minipage"
    (match lineXOf census 0 "Alpha", lineXOf census 0 "kilo",
        lineYOf census 0 "Alpha", lineYOf census 0 "kilo" with
     | some xa, some xk, some ya, some yk => xa == xk && ya < yk
     | _, _, _, _ => false)
  let tableCols := Ir.foldBlocks (fun acc b => match b with
      | .table cols _ _ _ _ _ => acc.push cols
      | _ => acc) (fun acc _ => acc) #[] doc.body
  t "X reaches the shared table IR as a flexible target-width column"
    ((tableCols[0]?.bind (·[1]?)).map (·.width) ==
      some (.flex (.sized (.ref .lineWidth))))
  let probeCols : Array Ir.ColSpec :=
    #[{ width := .natural, align := .left },
      { width := .flex (.frac 1000), align := .left }]
  t "X receives exactly the target remainder after the natural column and pads"
    (Layout.tableColWidths 10 1000 probeCols #[#[100, 200]] #[] == #[100, 860])
  let trees := doc.body.map (HtmlDoc.blockNode {})
  let tableStyles := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "table") "style" n) #[]
  let colStyles := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "col") "style" n) #[]
  let cellStyles := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "td") "style" n) #[]
  t "typed HTML keeps the nested tabularx and its target/flexible track"
    (trees.foldl (fun n tree => n + countTag "table" tree) 0 == 1 &&
      tableStyles.contains "width: 100%" && colStyles.contains "width: 100%")
  t "typed HTML justifies only the X paragraph cells"
    (cellStyles == #["text-align: justify", "text-align: justify"])

/-- **Strikeout is a shared decoration, not a suppressed package warning.**
Installed ulem fixes text-mode `\sout` at a `0.55ex` bottom and `0.4pt`
thickness from the command-entry face and colour. These checks read the IR,
`Layout.Out`, typed HTML, PDF operators, and accessibility facts. -/
def recipeUlemChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let load := "\\usepackage[normalem]{ulem}\n"
  let src := dvDoc load "Kept before. \\sout{Crossed words.} Kept after."
  let (doc, ds) := elabStr src
  t "normalem ulem and sout have no package or unknown-command loss"
    (ds.all fun d => d.severity == .note && d.code != "W0103" && d.code != "W0301")
  t "sout has a typed line-through IR wrapper"
    ((elabStr "\\sout{x}").1.body ==
      #[.para #[.decorated .lineThrough #[.text "x"]]])
  let bareDs := (elabStr (dvDoc "\\usepackage{ulem}\n" "\\emph{x}")).2
  t "bare ulem keeps one precise emphasis diagnostic"
    ((bareDs.filter (·.code == "W0103")).size == 1 &&
      bareDs.any (fun d => hasStr d.message "changes \\emph") &&
      !bareDs.any (·.code == "W0301"))
  let normalEm := (elabStr (dvDoc load "\\emph{x}")).1.body
  let plainEm := (elabStr (dvDoc "" "\\emph{x}")).1.body
  t "normalem leaves ordinary emphasis unchanged" (normalEm == plainEm)

  let geom : Layout.Geom := {}
  let out := layoutOf oneFace doc geom
  let census := censusOf (coveredColorsOf doc) out
  t "strikeout preserves its text exactly once on one page"
    (out.pages.size == 1 && pageOccurs census 0 "Crossed words." == 1)
  let strikeSegs := (metricDecorationSegs out).filter fun (kind, _, _, _, _) =>
    kind == .lineThrough
  let strikeWidth := strikeSegs.foldl (fun n (_, w, _, _, _) => n + w) (0 : Dim.Sp)
  let sourceWidth := (allLines out).foldl (fun n l =>
    n + l.segs.foldl (fun n s => match s with
      | .run _ _ _ w _ _ _ decorations _ _ _ =>
        if decorations.lineThrough.isSome then n + w else n
      | .decoratedGap w _ _ => n + w
      | .gap .. | .decoration .. | .rule .. | .image .. => n) 0) 0
  let font := oneFace.body
  let expectedRaise := Layout.lineThroughRaise
    (font.xHeight * geom.fontSize / (font.unitsPerEm : Int))
  t "strikeout covers words and interword gaps at the measured font band"
    (!strikeSegs.isEmpty && strikeWidth == sourceWidth &&
      strikeSegs.all fun (_, w, thickness, raise, color) =>
        w > 0 && thickness == Layout.lineThroughThickness &&
          raise == expectedRaise && color == Ir.Color.black)

  let underlineOut := layoutOf oneFace (elabStr "\\underline{aqa}").1 geom
  let underlineSegs := (metricDecorationSegs underlineOut).filter
    fun (kind, _, _, _, _) => kind == .underline
  let underlineWidth := underlineSegs.foldl (fun n (_, w, _, _, _) => n + w) (0 : Dim.Sp)
  let underlineTextWidth := ((bodyLines underlineOut)[0]?.map (·.setWidth)).getD 0
  t "line-through cannot pass by substituting underline geometry"
    (strikeSegs.all (fun (_, _, _, raise, _) => raise > 0) &&
      underlineSegs.all (fun (_, _, _, raise, _) => raise < 0) &&
      0 < underlineWidth && underlineWidth < underlineTextWidth)

  let nestedSrc := dvDoc load
    "\\textcolor{blue}{\\sout{A \\href{https://example.org}{\\textit{B}} \\textcolor{red}{C}}}"
  let (nestedDoc, nestedDs) := elabStr nestedSrc
  let nestedOut := layoutOf oneFace nestedDoc geom
  let runColors := (bodyLines nestedOut).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ color _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then none else some color
    | _ => none
  let strikeColors := (metricDecorationSegs nestedOut).filterMap
    fun (kind, _, _, _, color) => if kind == .lineThrough then some color else none
  t "strike keeps its entry colour while nested style, colour, and link survive"
    (!nestedDs.any (fun d => d.code == "W0103" || d.code == "W0301" || d.severity == .error) &&
      !runColors.isEmpty &&
      runColors.any (· != runColors[0]!) &&
      strikeColors.all (· == runColors[0]!) &&
      (bodyLines nestedOut).any fun l => l.segs.any fun s => match s with
        | .run _ _ (some "https://example.org") _ _ _ _ _ _ _ _ => true
        | _ => false)

  let nestedTrees := nestedDoc.body.map (HtmlDoc.blockNode {})
  let (nestedHtml, _) := HtmlDoc.emit {} nestedDoc
  let facts := HtmlDoc.a11yFacts true false nestedTrees
  t "typed HTML keeps s, link, emphasis, colour, and line-through CSS"
    (nestedTrees.foldl (fun n tree => n + countTag "s" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "a" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "em" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "span" tree) 0 >= 2 &&
      hasStr nestedHtml s!"s \{ text-decoration-line: line-through; text-decoration-thickness: {HtmlDoc.lineThroughThicknessCss};" &&
      facts.hiddenTabStops == 0 && treeShownOccurs nestedTrees "A B C" == 1)

  let expectedPdf : Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let mut expected := #[]
    for page in out.pages do
      for l in page.lines do
        let mut x := geom.bleed + l.x
        for seg in l.segs do
          match seg with
          | .decoration .lineThrough w thickness raise color =>
            expected := expected.push
              (color, x, geom.bleed + geom.pageH - l.y + raise, w, thickness)
            x := x + w
          | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
          | .decoration .underline w _ _ _ | .rule w _ _ _ | .image _ w _ =>
            x := x + w
    return expected
  let pdfFills := (Pdf.pageOps geom oneFace out.pages).flatMap fun ops =>
    pdfFillsList #[] ops.toList
  t "every typed through-line becomes the same PDF fill rule"
    (!expectedPdf.isEmpty && expectedPdf.all pdfFills.contains)
  match pdfLinkTargets (Pdf.write geom oneFace nestedOut.pages) with
  | .error e => failures ref s!"ulem link PDF: {e}"
  | .ok targets =>
    t "a link inside strikeout remains one PDF link annotation"
      (targets == #["(https://example.org)".toUTF8])

  let multiline (body : String) : Layout.Out :=
    layoutOf oneFace (elabStr (dvDoc
      ("\\page{ width = 110pt, height = 400pt, margin = 10pt }\n" ++ load) body)).1
  let multilineOk (multi : Layout.Out) : Bool :=
    let textYs := (bodyLines multi).filterMap fun l => if hasGlyphRun l then some l.y else none
    let strikeYs := (bodyLines multi).filterMap fun l =>
      if l.segs.any (· matches .decoration .lineThrough ..) then some l.y else none
    textYs.size >= 2 && textYs.size == strikeYs.size && textYs.all strikeYs.contains
  t "explicit and automatic multiline bodies draw one through-line per baseline"
    (multilineOk (multiline "\\sout{First line\\\\Second line}") &&
      multilineOk (multiline "\\sout{alpha beta gamma delta epsilon zeta eta theta}"))

  let both := metricDecorationSegs
    (layoutOf oneFace (elabStr "\\underline{\\sout{aqa}}").1 geom)
  t "underline and line-through compose as two typed decoration kinds"
    (both.any (fun (kind, _, _, _, _) => kind == .underline) &&
      both.any (fun (kind, _, _, _, _) => kind == .lineThrough))

  -- Drawn decoration geometry must reach every line path, not only body
  -- paragraphs: a strike inside a footnote (body ink on a note-flagged
  -- line) and inside a running foot (furniture) each paints its
  -- through-line. HTML strikes the same IR node on the note (agreement);
  -- furniture has no HTML counterpart, so its agreement is Layout.Out +
  -- PDF. The through-line reaches the PDF as a fill on every path.
  let throughFills (g : Layout.Geom) (o : Layout.Out) :
      Array (Ir.Color × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let mut expected := #[]
    for page in o.pages do
      for l in page.lines do
        let mut x := g.bleed + l.x
        for seg in l.segs do
          match seg with
          | .decoration .lineThrough w thickness raise color =>
            expected := expected.push
              (color, x, g.bleed + g.pageH - l.y + raise, w, thickness)
            x := x + w
          | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
          | .decoration .underline w _ _ _ | .rule w _ _ _ | .image _ w _ =>
            x := x + w
    return expected
  let paintedInPdf (g : Layout.Geom) (o : Layout.Out) : Bool :=
    let expected := throughFills g o
    let fills := (Pdf.pageOps g oneFace o.pages).flatMap fun ops =>
      pdfFillsList #[] ops.toList
    !expected.isEmpty && expected.all fills.contains

  let fnSrc := dvDoc load "Body claim.\\footnote{Note with \\sout{crossed} words.}"
  let (fnDoc, fnDs) := elabStr fnSrc
  let fnGeom := Layout.Geom.ofPage fnDoc.page
  let fnOut := layoutOf oneFace fnDoc
  let fnNoteStrike := (fnOut.pages.flatMap (·.lines.filter (·.note))).flatMap fun l =>
    l.segs.filterMap fun s => match s with
      | .decoration .lineThrough w _ raise color => some (w, raise, color)
      | _ => none
  t "a strike inside a footnote paints a through-line on the note line"
    (!fnNoteStrike.isEmpty &&
      fnNoteStrike.all (fun (w, raise, _) => w > 0 && raise > 0) &&
      fnDs.all (·.severity != .error))
  t "the footnote through-line becomes a PDF fill" (paintedInPdf fnGeom fnOut)
  let (fnHtml, _) := HtmlDoc.emit {} fnDoc
  t "HTML strikes the same footnote text, kept accessible (PDF and HTML agree)"
    (hasStr fnHtml "<s>" && hasStr fnHtml "crossed")

  let rfSrc := dvDoc "\\runningfoot{p. \\sout{draft} \\pagenumber}" "Body text stands here."
  let (rfDoc, rfDs) := elabStr rfSrc
  let rfGeom := Layout.Geom.ofPage rfDoc.page
  let rfOut := layoutOf oneFace rfDoc
  let rfFurnStrike := (rfOut.pages.flatMap (·.lines.filter (·.furniture))).flatMap fun l =>
    l.segs.filterMap fun s => match s with
      | .decoration .lineThrough w _ raise color => some (w, raise, color)
      | _ => none
  t "a strike inside a running foot paints a through-line on the furniture line"
    (!rfFurnStrike.isEmpty &&
      rfFurnStrike.all (fun (w, raise, _) => w > 0 && raise > 0) &&
      rfDs.all (·.severity != .error))
  t "the running-foot through-line becomes a PDF fill" (paintedInPdf rfGeom rfOut)
