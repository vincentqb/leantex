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

/-- Count anchors nested inside another anchor. An `<a>` descending from an
`<a>` is invalid interactive nesting and a keyboard trap (HTML content model;
WCAG SC 4.1.2): a block link must never emit one, which is what refusing a
nested wrapper secures. -/
private def anchorInAnchor (inside : Bool) : Html.Node → Nat
  | .text _ | .style _ | .script _ _ => 0
  | .elem t _ kids =>
    (if inside && t == "a" then 1 else 0)
      + kids.foldl (fun n k => n + anchorInAnchor (inside || t == "a") k) 0

/-- The text an anchor subtree contributes to its accessible name: every text
leaf below an `<a>`. Content outside every anchor contributes nothing. -/
private def anchorInnerText (inside : Bool) : Html.Node → String
  | .text s => if inside then s else ""
  | .style _ | .script _ _ => ""
  | .elem t _ kids => kids.foldl (fun s k => s ++ anchorInnerText (inside || t == "a") k) ""

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
  -- A multi-paragraph wrapper with text on either side: one authored link
  -- identity spans both paragraphs (never one wrapper per inline leaf), and
  -- the surrounding siblings stay outside the one region, one annotation,
  -- and the one anchor.
  let msrc := dvDoc "\\usepackage{hyperref}\n" (
    "Before the link.\n\n" ++
    "\\hyperlink{multi}{First linked paragraph.\n\n" ++
    "Second linked paragraph.}\n\n" ++
    "After the link.")
  let (mdoc, mds) := elabStr msrc
  let linkBlocks := Ir.foldBlocks (fun n b => n + (if b matches .link _ _ then 1 else 0))
    (fun n _ => n) 0 mdoc.body
  t "a multi-paragraph wrapper is one block link, no unknown-command cascade"
    (mds.all (fun d => !cascade.contains d.code) && linkBlocks == 1)
  let mout := layoutOf oneFace mdoc
  let mLinks := (mout.pages[0]?.map (·.links)).getD #[]
  let mInside (names : List String) (rect : Layout.LinkRect) : Bool :=
    ((allLines mout).filter (fun l => names.any (hasStr (lineText l) ·))).all
      fun l => rect.y ≤ l.y && l.y ≤ rect.y + rect.h
  let mOutside (names : List String) (rect : Layout.LinkRect) : Bool :=
    ((allLines mout).filter (fun l => names.any (hasStr (lineText l) ·))).all
      fun l => l.y < rect.y || l.y > rect.y + rect.h
  t "the multi-paragraph link is one region spanning both paragraphs, not its siblings"
    (match mLinks[0]? with
     | some rect =>
       mLinks.size == 1 && rect.target == "#multi" &&
         mInside ["First linked paragraph.", "Second linked paragraph."] rect &&
         mOutside ["Before the link.", "After the link."] rect
     | none => false)
  let mpdf := Pdf.write (Layout.Geom.ofPage mdoc.page) oneFace mout.pages mdoc.info
  t "the multi-paragraph link is exactly one PDF annotation, siblings carry none"
    (pdfLinkTargets mpdf == .ok #["(#multi)".toUTF8])
  let mtrees := mdoc.body.map (HtmlDoc.blockNode {})
  let mhrefs := mtrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let mAnchorText := mtrees.foldl (fun s n => s ++ anchorInnerText false n) ""
  t "one HTML anchor wraps both linked paragraphs and excludes the surrounding text"
    (mhrefs == #["#multi"] &&
      hasStr mAnchorText "First linked paragraph." && hasStr mAnchorText "Second linked paragraph." &&
      !hasStr mAnchorText "Before the link." && !hasStr mAnchorText "After the link.")
  -- Accessibility: a block link's anchor carries an accessible name (its own
  -- text) and no anchor ever nests inside another — the invalid interactive
  -- nesting the nested-wrapper refusal exists to prevent.
  t "the block link is accessible: a named anchor with no nested interactive anchor"
    (!mAnchorText.isEmpty &&
      mtrees.foldl (fun n tree => n + anchorInAnchor false tree) 0 == 0 &&
      nestedTrees.foldl (fun n tree => n + anchorInAnchor false tree) 0 == 0)

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
  t "typed HTML keeps the nested tabularx and its target/flexible track"
    (trees.foldl (fun n tree => n + countTag "table" tree) 0 == 1 &&
      tableStyles.contains "width: 100%" && colStyles.contains "width: 100%")



mutual
/-- Collect every PDF fill rectangle's colour, width, and height, descending
into marked-content sequences. A through-line lowers to one such fill. -/
private def pdfFillsOne (out : Array (Ir.Color × Dim.Sp × Dim.Sp)) :
    Pdf.ContentOp → Array (Ir.Color × Dim.Sp × Dim.Sp)
  | .fill color _ _ w h => out.push (color, w, h)
  | .marked _ body => pdfFillsList out body.toList
  | .path _ _ _ | .text _ | .image _ _ _ _ _ | .imageMissing _ _ _ _ => out
private def pdfFillsList (out : Array (Ir.Color × Dim.Sp × Dim.Sp)) :
    List Pdf.ContentOp → Array (Ir.Color × Dim.Sp × Dim.Sp)
  | [] => out
  | op :: rest => pdfFillsList (pdfFillsOne out op) rest
end

/-- **Strikeout is a shared decoration, not a suppressed package warning.**
Installed ulem fixes text-mode `\sout` at a `0.55ex` bottom (above the
baseline) and `0.4pt` thickness from the command-entry face and colour, where
`\uline` sits below the baseline. These checks read the IR, `Layout.Out`, the
typed HTML tree, PDF operators, and the accessibility facts — never a dump. -/
def recipeUlemChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let load := "\\usepackage[normalem]{ulem}\n"
  let src := dvDoc load "Kept before. \\sout{Crossed words.} Kept after."
  let (doc, ds) := elabStr src
  t "normalem ulem and sout have no package or unknown-command loss"
    (ds.all fun d => d.code != "W0103" && d.code != "W0301" && d.severity != .error)
  t "sout has a typed line-through IR wrapper"
    ((elabStr "\\sout{x}").1.body == #[.para #[.decorated .lineThrough #[.text "x"]]])
  let bareDs := (elabStr (dvDoc "\\usepackage{ulem}\n" "\\emph{x}")).2
  t "bare ulem keeps one precise emphasis diagnostic, no unknown-command"
    ((bareDs.filter (·.code == "W0103")).size == 1 &&
      bareDs.any (fun d => hasStr d.message "emph") &&
      !bareDs.any (·.code == "W0301"))
  let normalEm := (elabStr (dvDoc load "\\emph{x}")).1.body
  let plainEm := (elabStr (dvDoc "" "\\emph{x}")).1.body
  t "normalem leaves ordinary emphasis unchanged" (normalEm == plainEm)

  let out := layoutOf oneFace doc
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
      | .gap .. | .decoration .. | .rule .. | .image .. | .poly .. => n) 0) 0
  t "strikeout covers words and interword gaps at the shared through-line band"
    (!strikeSegs.isEmpty && strikeWidth == sourceWidth &&
      strikeSegs.all fun (_, w, thickness, raise, color) =>
        w > 0 && thickness == Layout.lineThroughThickness &&
          raise > 0 && color == Ir.Color.black)

  let underlineOut := layoutOf oneFace (elabStr "\\underline{aqa}").1
  let underlineSegs := (metricDecorationSegs underlineOut).filter
    fun (kind, _, _, _, _) => kind == .underline
  t "line-through cannot pass by substituting below-baseline underline geometry"
    (!underlineSegs.isEmpty &&
      strikeSegs.all (fun (_, _, _, raise, _) => raise > 0) &&
      underlineSegs.all (fun (_, _, _, raise, _) => raise < 0))

  let nestedSrc := dvDoc load
    "\\textcolor{blue}{\\sout{A \\href{https://example.org}{\\textit{B}} \\textcolor{red}{C}}}"
  let (nestedDoc, nestedDs) := elabStr nestedSrc
  let nestedOut := layoutOf oneFace nestedDoc
  let runColors := (bodyLines nestedOut).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ color _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then none else some color
    | _ => none
  let strikeColors := (metricDecorationSegs nestedOut).filterMap
    fun (kind, _, _, _, color) => if kind == .lineThrough then some color else none
  t "strike keeps its entry colour while nested style, colour, and link survive"
    (!nestedDs.any (fun d => d.code == "W0103" || d.code == "W0301" || d.severity == .error) &&
      !runColors.isEmpty && runColors.any (· != runColors[0]!) &&
      !strikeColors.isEmpty && strikeColors.all (· == runColors[0]!) &&
      (bodyLines nestedOut).any fun l => l.segs.any fun s => match s with
        | .run _ _ (some "https://example.org") _ _ _ _ _ _ _ _ => true
        | _ => false)

  let nestedTrees := nestedDoc.body.map (HtmlDoc.blockNode {})
  let (nestedHtml, _) := HtmlDoc.emit {} nestedDoc
  let facts := HtmlDoc.a11yFacts true false nestedTrees
  t "typed HTML keeps s, link, emphasis, colour, and derives line-through CSS"
    (nestedTrees.foldl (fun n tree => n + countTag "s" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "a" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "em" tree) 0 == 1 &&
      nestedTrees.foldl (fun n tree => n + countTag "span" tree) 0 >= 2 &&
      hasStr nestedHtml
        "s { text-decoration-line: line-through; text-decoration-thickness: 0.4pt;" &&
      facts.hiddenTabStops == 0 && treeShownOccurs nestedTrees "A B C" == 1)

  let tree := Struct.ofDoc (Layout.pdfView doc)
  let pdfFills := (Pdf.pageOps (Layout.Geom.ofPage doc.page) oneFace out.pages {} tree).flatMap
    fun ops => pdfFillsList #[] ops.toList
  t "every typed through-line becomes one PDF fill rule of its colour, width, and weight"
    (!strikeSegs.isEmpty &&
      strikeSegs.all fun (_, w, thickness, _, color) => pdfFills.contains (color, w, thickness))
  match pdfLinkTargets
      (Pdf.write (Layout.Geom.ofPage nestedDoc.page) oneFace nestedOut.pages nestedDoc.info) with
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

  let both := metricDecorationSegs (layoutOf oneFace (elabStr "\\underline{\\sout{aqa}}").1)
  t "underline and line-through compose as two typed decoration kinds"
    (both.any (fun (kind, _, _, _, _) => kind == .underline) &&
      both.any (fun (kind, _, _, _, _) => kind == .lineThrough))
