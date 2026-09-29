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
      | .run _ _ (some "#panel") _ glyphs _ _ _ _ _ => !glyphs.isEmpty
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
