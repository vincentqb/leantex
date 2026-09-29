import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

private def countTag (tag : String) : Html.Node → Nat
  | .text _ | .style _ | .script _ _ => 0
  | .elem t _ kids => (if t == tag then 1 else 0) + kids.foldl (fun n k => n + countTag tag k) 0

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
  t "the linked block reaches Layout.Out as an internal link"
    ((allLines out).any fun l => l.segs.any fun s => match s with
      | .run _ _ (some "#panel") _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
      | _ => false)
  let trees := doc.body.map (HtmlDoc.blockNode {})
  let hrefs := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  let ids := trees.foldl
    (fun acc n => acc ++ attrValuesOf (fun _ => true) "id" n) #[]
  t "the typed HTML tree carries the matching target and internal link"
    (ids.contains "panel" && hrefs.contains "#panel")
  t "the typed HTML tree keeps both nested tables"
    (trees.foldl (fun n tree => n + countTag "table" tree) 0 == 2)

/-- **A titlepage is one isolated, furniture-free flow page.** Article's
installed class opens a fresh page, applies the empty page style, and opens
another page at the close (`article.cls`, `titlepage`). Its body remains an
ordinary block sequence: explicit infinite glue controls vertical placement.
Assertions read the shipped pages and typed HTML tree. -/
def recipeTitlePageChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "" ("Lead page.\\begin{titlepage}\nTop marker.\n" ++
    "\\vfill\nBottom marker.\\end{titlepage}Tail page.")
  let (doc, ds) := elabStr src
  let cascade := ["W0302", "E0336", "E0311"]
  t "titlepage is recognized without an unknown-wrapper cascade"
    (ds.all fun d => !cascade.contains d.code)
  let geom : Layout.Geom := {}
  let out := layoutOf oneFace doc geom
  let census := censusOf (coveredColorsOf doc) out
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
    ((tableCols[0]?.bind (·[1]?)).map (·.width) == some (.flex (.frac 1000)))
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

/-- **Strikeout stays one explicit unsupported boundary until it has shared
geometry.** Installed ulem defines `\sout` by moving an underline to
`ULdepth=-.55ex`, a rule through the glyphs. The current IR has only the
below-baseline `underline` decoration; pretending that is strikeout would
misrender both PDF geometry and HTML semantics. Until a shared strike value
and exhaustive backend/walk arms land, the package and command each fire
once and the command's text remains visible. -/
def recipeUlemRefusalChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\usepackage[normalem]{ulem}\n"
    "Kept before. \\sout{Crossed words.} Kept after."
  let (doc, ds) := elabStr src
  t "ulem and sout each have one truthful diagnostic, with no cascade"
    ((ds.filter (·.code == "W0103")).size == 1 &&
      (ds.filter (·.code == "W0301")).size == 1 &&
      ds.all (·.severity != .error))
  let out := layoutOf oneFace doc
  let census := censusOf (coveredColorsOf doc) out
  t "the unsupported strike boundary preserves its text exactly once"
    (pageOccurs census 0 "Crossed words." == 1)
  let trees := doc.body.map (HtmlDoc.blockNode {})
  t "typed HTML does not claim strike semantics it cannot share with PDF"
    (trees.foldl (fun n tree => n + countTag "s" tree) 0 == 0 &&
      trees.foldl (fun n tree => n + treeShownOccurs #[tree] "Crossed words.") 0 == 1)
