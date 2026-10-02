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

/-- How many page objects the PDF carries: the physical page count the
artifact ships. -/
private def pdfPageCount (pdf : ByteArray) : Except String Nat := do
  let es ← PdfRead.objects pdf
  return (es.val.filter fun e => PdfCensus.kindOf e.val == .page).size

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
  -- User-definition precedence: `href`/`link`/`hyperlink`/`hypertarget` are
  -- `renderedBuiltins`, which the block dispatch (like the inline dispatch)
  -- must handle by its literal arm only AFTER `lookupUser` fails. A document
  -- that redefines one with a block-shaped use is the user's command, not
  -- the built-in link: no `#dest` anchor, the redefinition's own output.
  let (rdoc, rds) := elabStr (dvDoc
    "\\usepackage{hyperref}\n\\renewcommand{\\hyperlink}[2]{Redefined lead: #2}\n"
    "\\hyperlink{dest}{Alpha words.\\par Beta words.}")
  let rLinks := Ir.foldBlocks (fun n b => n + (if b matches .link _ _ then 1 else 0))
    (fun n _ => n) 0 rdoc.body
  let rTrees := rdoc.body.map (HtmlDoc.blockNode {})
  let rHrefs := rTrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let rText := " ".intercalate ((allLines (layoutOf oneFace rdoc)).toList.map lineText)
  t "a redefined block link name is the user's command, consulted before the built-in arm"
    (rLinks == 0 && !rHrefs.contains "#dest" &&
      hasStr rText "Redefined lead:" && hasStr rText "Alpha words." && hasStr rText "Beta words." &&
      rds.all (fun d => !cascade.contains d.code))
  -- A `\hfill` run of `\hyperlink`-wrapped minipages is ONE columns row: the
  -- flow-transparent wrapper is read through for the row (width and row
  -- participation from the minipage inside) while the wrapper stays around
  -- the tile's content, so each column is one `.link` to its own target
  -- (`Ir.linkedBoxRow_text`, `Ir.linkedBoxRow_links`). The row stands at the
  -- same baseline and column origins as the unlinked three-minipage row, and
  -- each tile gets one link rectangle over its OWN ink only — not the gutter
  -- or a neighbour (`Layout.Out`), with one `<a>` per tile (typed HTML).
  let linkTiles :=
    "\\hyperlink{ta}{\\begin{minipage}{0.3\\textwidth}Tile Apple.\\begin{tabular}{ll}A&B\\\\C&D\\end{tabular}\\end{minipage}}\\hfill\n" ++
    "\\hyperlink{tb}{\\begin{minipage}{0.3\\textwidth}Tile Berry.\\begin{tabular}{ll}E&F\\\\G&H\\end{tabular}\\end{minipage}}\\hfill\n" ++
    "\\hyperlink{tc}{\\begin{minipage}{0.3\\textwidth}Tile Cherry.\\begin{tabular}{ll}I&J\\\\K&L\\end{tabular}\\end{minipage}}"
  let bareTiles :=
    "\\begin{minipage}{0.3\\textwidth}Tile Apple.\\begin{tabular}{ll}A&B\\\\C&D\\end{tabular}\\end{minipage}\\hfill\n" ++
    "\\begin{minipage}{0.3\\textwidth}Tile Berry.\\begin{tabular}{ll}E&F\\\\G&H\\end{tabular}\\end{minipage}\\hfill\n" ++
    "\\begin{minipage}{0.3\\textwidth}Tile Cherry.\\begin{tabular}{ll}I&J\\\\K&L\\end{tabular}\\end{minipage}"
  let (ldoc, lds) := elabStr (dvDoc "\\usepackage{hyperref}\n" linkTiles)
  let (bdoc, _) := elabStr (dvDoc "\\usepackage{hyperref}\n" bareTiles)
  let lcols := ldoc.body.findSome? fun b => match b with | .columns cs => some cs | _ => none
  t "a hfill run of linked minipages is one columns row of three linked columns"
    (match lcols with
     | some cs => cs.size == 3 &&
         Ir.colLinkTargets cs.toList == [some "#ta", some "#tb", some "#tc"]
     | none => false)
  t "the linked row has three block links and no unknown-command cascade"
    (lds.all (fun d => !cascade.contains d.code) &&
      Ir.foldBlocks (fun n b => n + (if b matches .link _ _ then 1 else 0))
        (fun n _ => n) 0 ldoc.body == 3)
  let lout := layoutOf oneFace ldoc
  let bout := layoutOf oneFace bdoc
  let lineY (o : Layout.Out) (needle : String) : Option Dim.Sp :=
    (allLines o).findSome? fun l => if hasStr (lineText l) needle then some l.y else none
  let lineX (o : Layout.Out) (needle : String) : Option Dim.Sp :=
    (allLines o).findSome? fun l => if hasStr (lineText l) needle then some l.x else none
  t "the three linked tiles stand on the unlinked row's one baseline"
    (match lineY lout "Tile Apple.", lineY lout "Tile Berry.", lineY lout "Tile Cherry.",
         lineY bout "Tile Apple." with
     | some ya, some yb, some yc, some ybare => ya == yb && yb == yc && ya == ybare
     | _, _, _, _ => false)
  t "each linked tile keeps the unlinked row's column origin"
    (lineX lout "Tile Apple." == lineX bout "Tile Apple." &&
      lineX lout "Tile Berry." == lineX bout "Tile Berry." &&
      lineX lout "Tile Cherry." == lineX bout "Tile Cherry.")
  let rects := (lout.pages[0]?.map (·.links)).getD #[]
  let sorted := rects.qsort (fun a b => decide (a.x < b.x))
  let covers (r : Layout.LinkRect) (x : Dim.Sp) : Bool :=
    decide (r.x ≤ x) && decide (x ≤ r.x + r.w)
  t "the hfill linked row ships exactly three disjoint link rectangles with a gutter between"
    (rects.size == 3 &&
      (match sorted[0]?, sorted[1]?, sorted[2]? with
       | some r0, some r1, some r2 =>
         decide (r0.x + r0.w < r1.x) && decide (r1.x + r1.w < r2.x)
       | _, _, _ => false))
  t "each link rectangle covers its own tile's ink and neither the gutter nor a neighbour"
    (match lineX lout "Tile Apple.", lineX lout "Tile Berry.", lineX lout "Tile Cherry.",
         sorted[0]?, sorted[1]?, sorted[2]? with
     | some xa, some xb, some xc, some r0, some r1, some r2 =>
       covers r0 xa && !covers r0 xb && !covers r0 xc &&
       covers r1 xb && !covers r1 xa && !covers r1 xc &&
       covers r2 xc && !covers r2 xa && !covers r2 xb
     | _, _, _, _, _, _ => false)
  t "the three link rectangles carry the three distinct tile targets left to right"
    (sorted.map (·.target) == #["#ta", "#tb", "#tc"])
  let ltrees := ldoc.body.map (HtmlDoc.blockNode {})
  let lhrefs := ltrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  t "the typed HTML row carries one anchor per tile with the three targets"
    (lhrefs == #["#ta", "#tb", "#tc"] &&
      ltrees.foldl (fun n tree => n + countTag "a" tree) 0 == 3)

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

/-- **Array `>{decl}` and `<{decl}` column modifiers set a column's
alignment.** The array package reads a `>{...}` group before a column and a
`<{...}` group after it (array manual §1-2); `\raggedright`, `\raggedleft`,
and `\centering` select the column's horizontal alignment and
`\arraybackslash` is inert inside the group. The common flexible recipe
column `>{\raggedright\arraybackslash}X` must stay a flexible target-width
column whose alignment follows the modifier, and must raise no
unreadable-type (W0104) or short-row (W0337) cascade. An effect the group
carries that the engine does not model is named once. Assertions read the
shared table IR (`Ir.ColSpec`). -/
def recipeColModChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let firstTable := fun (doc : Ir.Doc) =>
    (Ir.foldBlocks (fun acc b => match b with
      | .table cols pl pr _ _ _ => acc.push (cols, pl, pr)
      | _ => acc) (fun acc _ => acc) #[] doc.body)[0]?
  let isFlex := fun (w : Ir.ColWidth) => match w with | .flex _ => true | _ => false
  let cascade := ["W0104", "W0337", "W0338", "W0103", "W0301", "W0302"]
  -- A raggedright X: one flexible, left-aligned column, no cascade.
  let (d1, ds1) := elabStr (dvDoc "\\usepackage{tabularx}\n"
    "\\begin{tabularx}{\\linewidth}{>{\\raggedright\\arraybackslash}X}Key.\\end{tabularx}")
  t "a raggedright X column stays flexible, left-aligned, with no cascade"
    (match firstTable d1 with
     | some (cols, _, _) =>
       cols.size == 1 && cols[0]?.map (·.align) == some .left &&
       ((cols[0]?.map (·.width)).any isFlex) &&
       ds1.all (fun d => !cascade.contains d.code)
     | none => false)
  -- Mixed l then a centring X.
  let (d2, ds2) := elabStr (dvDoc "\\usepackage{tabularx}\n"
    "\\begin{tabularx}{\\linewidth}{l>{\\centering\\arraybackslash}X}A & B.\\end{tabularx}")
  t "a mixed l and centring-X spec yields a natural-left then a flexible-centre column"
    (match firstTable d2 with
     | some (cols, _, _) =>
       cols.size == 2 &&
       cols[0]?.map (·.align) == some .left && cols[0]?.map (·.width) == some .natural &&
       cols[1]?.map (·.align) == some .center && ((cols[1]?.map (·.width)).any isFlex) &&
       ds2.all (fun d => !cascade.contains d.code)
     | none => false)
  -- Raggedleft on a p column.
  let (d3, ds3) := elabStr (dvDoc ""
    "\\begin{tabular}{>{\\raggedleft\\arraybackslash}p{3cm}}x\\end{tabular}")
  t "raggedleft on a p column sets right alignment with no cascade"
    (match firstTable d3 with
     | some (cols, _, _) =>
       cols.size == 1 && cols[0]?.map (·.align) == some .right &&
       ds3.all (fun d => !cascade.contains d.code)
     | none => false)
  -- An unsupported effect is named once; the column still stands.
  let (d4, ds4) := elabStr (dvDoc ""
    "\\begin{tabular}{>{\\bfseries}c}a\\end{tabular}")
  t "an unsupported modifier effect is named once and the column stands"
    (match firstTable d4 with
     | some (cols, _, _) =>
       cols.size == 1 && cols[0]?.map (·.align) == some .center &&
       (ds4.filter (·.code == "W0104")).size == 1 &&
       ds4.all (fun d => d.code != "W0337")
     | none => false)
  -- A post `\arraybackslash` modifier is inert.
  let (d5, ds5) := elabStr (dvDoc ""
    "\\begin{tabular}{c<{\\arraybackslash}}a\\end{tabular}")
  t "a post arraybackslash modifier is inert and raises no cascade"
    (match firstTable d5 with
     | some (cols, _, _) =>
       cols.size == 1 && cols[0]?.map (·.align) == some .center &&
       ds5.all (fun d => !cascade.contains d.code)
     | none => false)
  -- An `@{}` gap after a modified X drops the right pad.
  let (d6, ds6) := elabStr (dvDoc "\\usepackage{tabularx}\n"
    "\\begin{tabularx}{\\linewidth}{>{\\raggedright\\arraybackslash}X@{}}k.\\end{tabularx}")
  t "an @{} gap after a modified X column drops the right pad with no cascade"
    (match firstTable d6 with
     | some (cols, _, padR) =>
       cols.size == 1 && padR == false && ds6.all (fun d => !cascade.contains d.code)
     | none => false)

/-- **The article `titlepage` environment is an isolated flow page.** The
installed class opens a fresh page, applies the empty page style, and opens
another at the close (`classes.dtx`, `\titlepage`). This engine lowers the
environment before the block knot to the `\pagebreak` the flow already names
around the body carried in a group — so there is no unknown-environment
cascade, the body elaborates through the ordinary top-level block paths at
the document's own flow geometry (its left margin, where LuaLaTeX sets
ordinary titlepage text, the author's `\vfill` controlling the vertical
split), a declaration inside ends at the close, and adjacent or boundary
breaks close only a page holding content so no blank page is left. Assertions
read the shipped pages (`Layout.Out`), the IR, the PDF page objects, and the
typed HTML tree. -/
def recipeTitlePageChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page := "\\page{ width = 420pt, height = 600pt, hmargin = 54pt, vmargin = 48pt }\n"
  let cascade := ["W0302", "W0301", "E0336", "E0311"]
  -- Middle: a title page between lead and tail matter — exactly three pages,
  -- the two `\clearpage` boundaries LuaLaTeX's `titlepage` sets.
  let src := dvDoc page
    ("Lead page.\\begin{titlepage}\nTop marker.\n\\vfill\nBottom marker." ++
      "\\end{titlepage}Tail page.")
  let (doc, ds) := elabStr src
  t "titlepage is recognized with no unknown-environment or wrapper cascade"
    (ds.all fun d => !cascade.contains d.code)
  let out := layoutOf oneFace doc
  let census := censusOf (coveredColorsOf doc) out
  t "a title page between matter opens and closes exactly one physical page"
    (out.pages.size == 3 && pageHas census 0 "Lead page." &&
      pageHas census 1 "Top marker." && pageHas census 1 "Bottom marker." &&
      pageHas census 2 "Tail page." &&
      pageOccurs census 1 "Top marker." == 1 && pageOccurs census 2 "Tail page." == 1)
  -- LuaLaTeX sets ordinary titlepage text left-aligned at the text margin,
  -- the author's `\vfill` controlling the vertical split; the markers land at
  -- the document's hmargin with the bottom pushed well below the top.
  t "titlepage body uses the document's own flow geometry (left margin, author vfill)"
    (match lineXOf census 1 "Top marker.", lineXOf census 1 "Bottom marker.",
        lineYOf census 1 "Top marker.", lineYOf census 1 "Bottom marker." with
     | some xt, some xb, some yt, some yb =>
       xt == doc.page.hmargin && xb == doc.page.hmargin && yt < yb &&
         yb - yt > doc.page.height / 3
     | _, _, _, _ => false)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) oneFace out.pages doc.info
  t "the PDF artifact carries exactly the three physical pages"
    (pdfPageCount pdf == .ok 3)
  let (html, _) := HtmlDoc.emit {} doc
  t "typed HTML keeps the title page body as one continuous semantic flow"
    (["Lead page.", "Top marker.", "Bottom marker.", "Tail page."].all (hasStr html ·))
  -- Leading: no blank page before.
  let (fdoc, fds) := elabStr (dvDoc page "\\begin{titlepage}\nTitle only.\\end{titlepage}Body after.")
  let fout := layoutOf oneFace fdoc
  let fcensus := censusOf (coveredColorsOf fdoc) fout
  t "a leading title page leaves no blank page before it"
    (fds.all (fun d => !cascade.contains d.code) && fout.pages.size == 2 &&
      pageHas fcensus 0 "Title only." && pageHas fcensus 1 "Body after.")
  -- Trailing: no blank page after.
  let (ldoc, lds) := elabStr (dvDoc page "Body before.\\begin{titlepage}\nColophon.\\end{titlepage}")
  let lout := layoutOf oneFace ldoc
  let lcensus := censusOf (coveredColorsOf ldoc) lout
  t "a trailing title page leaves no blank page after it"
    (lds.all (fun d => !cascade.contains d.code) && lout.pages.size == 2 &&
      pageHas lcensus 0 "Body before." && pageHas lcensus 1 "Colophon.")
  -- Empty body: adjacent breaks make no blank page; the two sides stay apart.
  let (edoc, eds) := elabStr (dvDoc page "Before.\\begin{titlepage}\\end{titlepage}After.")
  let eout := layoutOf oneFace edoc
  let ecensus := censusOf (coveredColorsOf edoc) eout
  let etrees := edoc.body.map (HtmlDoc.blockNode {})
  t "an empty title page produces no blank page"
    (eds.all (fun d => !cascade.contains d.code) && eout.pages.size == 2 &&
      pageHas ecensus 0 "Before." && pageHas ecensus 1 "After." &&
      etrees.foldl (fun n tree => n + countTag "section" tree) 0 == 0)
  -- Nested block content stays block-shaped on the title page's own page.
  let nsrc := dvDoc page
    ("\\begin{titlepage}\n\\begin{center}Centered head.\\end{center}\n" ++
      "\\begin{itemize}\\item First point.\\item Second point.\\end{itemize}" ++
      "\\end{titlepage}After matter.")
  let (ndoc, nds) := elabStr nsrc
  let nout := layoutOf oneFace ndoc
  let ncensus := censusOf (coveredColorsOf ndoc) nout
  let listBlocks := Ir.foldBlocks
    (fun n b => n + (if b matches .list .. then 1 else 0)) (fun n _ => n) 0 ndoc.body
  t "nested block content inside a title page stays block-shaped on its page"
    (nds.all (fun d => !cascade.contains d.code) && nout.pages.size == 2 &&
      ["Centered head.", "First point.", "Second point."].all (pageHas ncensus 0 ·) &&
      pageHas ncensus 1 "After matter." && listBlocks >= 1 &&
      (match lineYOf ncensus 0 "First point.", lineYOf ncensus 0 "Second point." with
       | some y1, some y2 => y1 < y2
       | _, _ => false))
  -- A declaration inside the title page applies there and is restored after:
  -- the group that carries the body scopes it to the close.
  let (ddoc, _) := elabStr (dvDoc page "\\begin{titlepage}\\Large Big title.\\end{titlepage}Plain tail.")
  let dcensus := censusOf (coveredColorsOf ddoc) (layoutOf oneFace ddoc)
  let (pdoc, _) := elabStr (dvDoc page "Plain tail.")
  let pcensus := censusOf (coveredColorsOf pdoc) (layoutOf oneFace pdoc)
  t "a size declaration inside a title page applies there and is restored after"
    (match lineSizeOf dcensus 0 "Big title.", lineSizeOf dcensus 1 "Plain tail.",
        lineSizeOf pcensus 0 "Plain tail." with
     | some big, some tail, some plain => big > tail && tail == plain
     | _, _, _ => false)



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

  -- Drawn decoration must reach every finalized line path, not only body
  -- paragraphs: a strike inside a footnote (body ink on a note-flagged
  -- line) and inside a running foot (furniture) each paints its
  -- through-line from the one owner (`Layout.decorationRiders`, applied in
  -- `furnishPage`). HTML strikes the same IR node on the note (agreement);
  -- furniture has no HTML counterpart, so its agreement is Layout.Out + PDF.
  let throughOf (ls : Array Layout.LineOut) :
      Array (Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) :=
    ls.flatMap fun l => l.segs.filterMap fun s => match s with
      | .decoration .lineThrough w thickness raise color => some (w, thickness, raise, color)
      | _ => none
  let paintedInPdf (doc2 : Ir.Doc) (o : Layout.Out) : Bool :=
    let tree := Struct.ofDoc (Layout.pdfView doc2)
    let fills := (Pdf.pageOps (Layout.Geom.ofPage doc2.page) oneFace o.pages {} tree).flatMap
      fun ops => pdfFillsList #[] ops.toList
    let through := throughOf (allLines o)
    !through.isEmpty && through.all fun (w, thickness, _, color) => fills.contains (color, w, thickness)

  let fnSrc := dvDoc load "Body claim.\\footnote{Note with \\sout{crossed} words.}"
  let (fnDoc, fnDs) := elabStr fnSrc
  let fnOut := layoutOf oneFace fnDoc
  let fnNoteStrike := throughOf (fnOut.pages.flatMap (·.lines.filter (·.note)))
  t "a strike inside a footnote paints a through-line on the note line"
    (!fnNoteStrike.isEmpty &&
      fnNoteStrike.all (fun (w, _, raise, _) => w > 0 && raise > 0) &&
      fnDs.all (·.severity != .error))
  t "the footnote through-line becomes a PDF fill" (paintedInPdf fnDoc fnOut)
  let (fnHtml, _) := HtmlDoc.emit {} fnDoc
  t "HTML strikes the same footnote text, kept accessible (PDF and HTML agree)"
    (hasStr fnHtml "<s>" && hasStr fnHtml "crossed")

  let rfSrc := dvDoc "\\runningfoot{p. \\sout{draft} \\pagenumber}" "Body text stands here."
  let (rfDoc, rfDs) := elabStr rfSrc
  let rfOut := layoutOf oneFace rfDoc
  let rfFurnStrike := throughOf (rfOut.pages.flatMap (·.lines.filter (·.furniture)))
  t "a strike inside a running foot paints a through-line on the furniture line"
    (!rfFurnStrike.isEmpty &&
      rfFurnStrike.all (fun (w, _, raise, _) => w > 0 && raise > 0) &&
      rfDs.all (·.severity != .error))
  t "the running-foot through-line becomes a PDF fill" (paintedInPdf rfDoc rfOut)

  -- No double paint: the one owner replaced the body paragraph's own
  -- sibling, so the single-line body strike paints exactly one through-line
  -- overlay — a second finalized line carrying the decoration would mean a
  -- duplicate.
  let bodyThrough := (bodyLines out).filter fun l =>
    l.segs.any (· matches .decoration .lineThrough ..)
  t "the body strike paints exactly one through-line overlay (no double paint)"
    (bodyThrough.size == 1)


/-- **A block link's nested text carries the inline link's two affordances;
an image-only body carries none.** An inline link paints its body in the
kind's declared ink (`Styles.linkInk`: `urlcolor` for `\href`, `linkcolor`
for internal `\hyperlink`) and underlines it (`Layout`'s `.link` arm, WCAG
2.2 SC 1.4.1 — never colour alone, never nothing). A block link's nested
text must carry the same, applied once per text-bearing run, so the two
backends read one afforded body. An image-only body has no text to mark, so
it carries no invisible-only decoration: its affordance is the reachable,
named `<a>` wrapping the `<img>`'s own name. These checks read `Layout.Out`,
the typed HTML tree, and the PDF operators — never a dump. -/
def recipeLinkAffordChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let cascade := ["W0301", "W0302", "E0304", "E0336", "E0311"]
  let magenta : Ir.Color := { r := 255, g := 0, b := 255 }
  -- A multi-paragraph `\href` is a block link; under colorlinks its kind is
  -- `url` (magenta). Its nested text must ship magenta and underlined.
  let tsrc := dvDoc "\\usepackage[colorlinks]{hyperref}\n"
    "\\href{https://example.org}{First linked line.\n\nSecond linked line.}"
  let (tdoc, tds) := elabStr tsrc
  t "a text block link elaborates with no unknown-command or wrapper cascade"
    (tds.all fun d => !cascade.contains d.code && d.severity != .error)
  let tout := layoutOf oneFace tdoc
  let linkRunColors := (bodyLines tout).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ color _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then none else some color
    | _ => none
  let underlineSegs := (metricDecorationSegs tout).filter
    fun (kind, _, _, _, _) => kind == .underline
  -- Layout.Out: every glyph run of the link's body is in the kind's ink, and
  -- the body is underlined — the two affordances, together.
  t "PAGE: a text block link paints its nested text in link ink and underlines it"
    (!linkRunColors.isEmpty && linkRunColors.all (· == magenta) && !underlineSegs.isEmpty)
  -- Layout.Out: the block link still ships its one whole-block annotation.
  t "PAGE: the text block link ships one link rectangle to its target"
    (match tout.pages[0]?.bind (·.links[0]?) with
     | some rect => (tout.pages[0]?.map (·.links.size == 1)).getD false &&
         rect.target == "https://example.org"
     | none => false)
  -- PDF: the underline lowers to a fill of the link ink, and the annotation
  -- carries the URL — decoration and annotation agree with the page.
  let tree := Struct.ofDoc (Layout.pdfView tdoc)
  let pdfFills := (Pdf.pageOps (Layout.Geom.ofPage tdoc.page) oneFace tout.pages {} tree).flatMap
    fun ops => pdfFillsList #[] ops.toList
  t "PDF: the underline becomes a fill of the link ink"
    (underlineSegs.all fun (_, w, thickness, _, color) =>
      color == magenta && pdfFills.contains (color, w, thickness))
  let tpdf := Pdf.write (Layout.Geom.ofPage tdoc.page) oneFace tout.pages tdoc.info
  t "PDF: the text block link carries one annotation to its target"
    (pdfLinkTargets tpdf == .ok #["(https://example.org)".toUTF8])
  -- HTML: the same two affordances — the anchor, the underline tag, and the
  -- ink span — on the link's own text, so both backends agree.
  let ttrees := tdoc.body.map (HtmlDoc.blockNode {})
  let threfs := ttrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let (thtml, _) := HtmlDoc.emit {} tdoc
  t "HTML: a text block link carries href, an underline tag, and the ink span"
    (threfs == #["https://example.org"] &&
      ttrees.foldl (fun n tree => n + countTag "u" tree) 0 >= 1 &&
      hasStr thtml (HtmlDoc.cssColor magenta))
  -- An image-only block link: no text to mark, so no invisible-only
  -- decoration — the affordance is the reachable, named anchor.
  let isrc := dvDoc "\\usepackage{graphicx}\n\\usepackage[colorlinks]{hyperref}\n"
    "\\href{https://example.org}{\\begin{center}\\includegraphics[alt={Site logo}]{logo.png}\\end{center}}"
  let (idoc, ids) := elabStr isrc
  t "an image-only block link elaborates with no unknown-command or wrapper cascade"
    (ids.all fun d => !cascade.contains d.code && d.severity != .error)
  let iout := layoutOf oneFace idoc
  let iUnderline := (metricDecorationSegs iout).filter
    fun (kind, _, _, _, _) => kind == .underline
  t "PAGE: an image-only block link carries no underline and one link rectangle"
    (iUnderline.isEmpty &&
      (match iout.pages[0]?.bind (·.links[0]?) with
       | some rect => (iout.pages[0]?.map (·.links.size == 1)).getD false &&
           rect.target == "https://example.org"
       | none => false))
  let itrees := idoc.body.map (HtmlDoc.blockNode {})
  let ihrefs := itrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let ialts := itrees.foldl (fun acc n => acc ++ attrValuesOf (· == "img") "alt" n) #[]
  t "HTML: an image-only block link is a reachable named anchor with no underline"
    (ihrefs == #["https://example.org"] && ialts.contains "Site logo" &&
      itrees.foldl (fun n tree => n + countTag "u" tree) 0 == 0)


/-- **A block link refuses any interactive descendant and keeps the content.**
Wrapping a focusable or anchor-bearing node in an outer link makes invalid
nested interaction (WCAG SC 4.1.2) — an `<a>` inside an `<a>`, or an `<a>`
around a `<pre tabindex="0">` — a keyboard trap. The genuine new gap over the
already-refused nested links/references/citations/footnotes is a
listing/verbatim block, which ships as a focusable `<pre>`. For each,
`Ir.hasInteractiveDescendant` drops the outer wrapper (one W0104, keyed
`link:nested`) while keeping the content; a legitimate block link keeps its
one named, reachable anchor. The backstop fact
`A11yFacts.interactiveInAnchor` is zero in every case. Assertions read
Layout.Out, the typed HTML tree, and the accessibility facts — never a dump. -/
def recipeInteractiveNestingChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let cascade := ["W0301", "W0302", "E0304", "E0336", "E0311"]
  let a11yOf (trees : Array Html.Node) : HtmlDoc.A11yFacts :=
    HtmlDoc.a11yFacts true false trees
  -- The new gap: a block link wrapping a listing. The verbatim ships as a
  -- focusable `<pre>`, so keeping the outer `<a>` would wrap a tab stop — the
  -- case `hasInteractiveDescendant` did not detect before.
  let (vdoc, vds) := elabStr (dvDoc "\\usepackage{hyperref}\n"
    "\\hyperlink{spot}{\\begin{verbatim}\nlisting body here\n\\end{verbatim}}")
  let vtrees := vdoc.body.map (HtmlDoc.blockNode {})
  let vout := layoutOf oneFace vdoc
  let (vhtml, _) := HtmlDoc.emit {} vdoc
  t "a block link wrapping a listing is refused and ships the listing with no outer link"
    ((vds.filter (·.code == "W0104")).size == 1 && vds.all (fun d => !cascade.contains d.code) &&
      vtrees.foldl (fun n tree => n + countTag "a" tree) 0 == 0 &&
      vtrees.foldl (fun n tree => n + countTag "pre" tree) 0 == 1 &&
      hasStr vhtml "listing body here" &&
      (vout.pages[0]?.map (·.links.size)).getD 1 == 0 &&
      (a11yOf vtrees).interactiveInAnchor == 0)
  -- Already refused before this change, re-asserted: a block link wrapping an
  -- anchor-bearing inline (reference, citation, footnote). The inner anchor
  -- survives; only the outer wrapper is dropped, so no anchor nests in
  -- another, the outer target reaches no href, and the content stays.
  let refusedInline (name body content : String) : IO Unit := do
    let (rdoc, rds) := elabStr (dvDoc "\\usepackage{hyperref}\n"
      ("\\hyperlink{spot}{" ++ body ++ "}"))
    let trees := rdoc.body.map (HtmlDoc.blockNode {})
    let hrefs := trees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
    let txt := " ".intercalate ((allLines (layoutOf oneFace rdoc)).toList.map lineText)
    t s!"a block link wrapping a {name} is refused, keeps its content, and nests no anchor"
      ((rds.filter (·.code == "W0104")).size == 1 && rds.all (fun d => !cascade.contains d.code) &&
        hasStr txt content && !hrefs.contains "#spot" &&
        trees.foldl (fun n tree => n + anchorInAnchor false tree) 0 == 0 &&
        (a11yOf trees).interactiveInAnchor == 0)
  refusedInline "reference" "See \\ref{sec:x} here." "here."
  refusedInline "citation" "See \\cite{key} here." "here."
  refusedInline "footnote" "Body text\\footnote{a note}." "Body text"
  -- A legitimate (non-interactive) block link is untouched: one named,
  -- reachable anchor, and no interactive descendant inside it.
  let (gdoc, gds) := elabStr (dvDoc "\\usepackage{hyperref}\n"
    "\\hyperlink{spot}{\\begin{minipage}{.4\\textwidth}Legit panel words.\\end{minipage}}")
  let gtrees := gdoc.body.map (HtmlDoc.blockNode {})
  let ghrefs := gtrees.foldl (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let gName := gtrees.foldl (fun s n => s ++ anchorInnerText false n) ""
  t "a legitimate block link keeps its one named, reachable anchor and no nested interaction"
    ((gds.filter (·.code == "W0104")).size == 0 &&
      ghrefs.size == 1 && (ghrefs[0]?.map (·.startsWith "#")).getD false &&
      ghrefs.all (fun h => HtmlDoc.tabbable "a" #[("href", h)]) &&
      hasStr gName "Legit panel words." &&
      (a11yOf gtrees).interactiveInAnchor == 0 &&
      gtrees.foldl (fun n tree => n + anchorInAnchor false tree) 0 == 0)
