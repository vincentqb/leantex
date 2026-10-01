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

