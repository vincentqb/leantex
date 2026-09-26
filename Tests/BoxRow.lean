import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- **Boxes with fill between them share a row.** Two `{minipage}`s with an
`\hfill` between and no paragraph break are LaTeX's side-by-side panels:
the fill takes the measure the boxes leave, so the first box stands at the
margin and the second ends at the measure's right edge, both on one line.
The defect stacked them, each its declared width with the rest of its line
empty, and a frame of two titled panels ran onto a second page. Read off
`Layout.Out` — where the boxes' lines land — and the typed HTML tree, the
other artifact of the same IR value. A paragraph break between the boxes
ends the line, so there they stack, as LaTeX's do. Invented content
throughout. -/
def minipageRowChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let panel (w txt : String) : String :=
    "\\begin{minipage}{" ++ w ++ "}" ++ txt ++ "\\end{minipage}"
  let doc (between : String) : String :=
    dvDoc "" (panel ".45\\textwidth" "Left panel text." ++ between ++
      panel ".45\\textwidth" "Right panel text.")
  let linesOf (src : String) : Array Layout.LineOut :=
    (allLines (layoutOf oneFace (elabStr src).1 geom)).filter
      fun l => !l.furniture && !l.segs.isEmpty
  let lineWith (ls : Array Layout.LineOut) (needle : String) : Option Layout.LineOut :=
    ls.find? fun l => hasStr (lineText l) needle
  let row := linesOf (doc "\\hfill\n")
  match lineWith row "Left", lineWith row "Right" with
  | some l, some r =>
    t "two boxes with a fill between stand on one line" (l.y == r.y)
    t "the first box stands at the margin" (l.x == geom.hmargin)
    t "the second box starts where its declared width ends the measure"
      (decide (r.x ≥ geom.hmargin + geom.textWidth - geom.textWidth * 45 / 100 - 1))
    t "each box keeps its declared width"
      (decide (l.setWidth ≤ geom.textWidth * 45 / 100) &&
        decide (r.setWidth ≤ geom.textWidth * 45 / 100))
  | _, _ => t "the row probe ships both boxes' text" false
  -- A paragraph break between the boxes ends the line: they stack.
  let stacked := linesOf (doc "\n\n\\hfill\n\n")
  t "a paragraph break between two boxes stacks them"
    (match lineWith stacked "Left", lineWith stacked "Right" with
     | some l, some r => decide (l.y < r.y)
     | _, _ => false)
  -- The HTML projection of the same row: one grid of two tracks, each the
  -- declared fraction, the leftover between them.
  let (rowDoc, _) := elabStr (doc "\\hfill\n")
  let isRow : Html.Node → Bool
    | .elem "div" attrs kids =>
      attrs.any (fun a => a.1 == "class" && a.2 == "columns") && kids.size == 2
    | _ => false
  t "the HTML row is one grid holding both boxes"
    (rowDoc.body.any fun b => isRow (HtmlDoc.blockNode {} b))
  -- The frame shape: two titled panels whose widths a document command
  -- spells, side by side under `\centering`. Stacked they are taller than
  -- the frame; side by side they fit it, so the frame is one page and says
  -- nothing about spilling.
  let tall := "One\\\\Two\\\\Three\\\\Four\\\\Five\\\\Six\\\\Seven\\\\Eight\\\\Nine\\\\Ten\\\\Eleven"
  let frameSrc := dvDeck "\\newcommand{\\panelw}{.45\\textwidth}\n"
    ("\\begin{frame}{Panels}\n\\centering\n" ++
     "\\begin{minipage}{\\panelw}\n\\begin{block}{First}\n" ++ tall ++
     "\n\\end{block}\n\\end{minipage}\\hfill\n" ++
     "\\begin{minipage}{\\panelw}\n\\begin{block}{Second}\n" ++ tall ++
     "\n\\end{block}\n\\end{minipage}\n\\end{frame}")
  let (fdoc, fds) := elabStr frameSrc
  let fout := layoutOf oneFace fdoc
  let fls := (allLines fout).filter fun l => !l.furniture && !l.segs.isEmpty
  t "two titled panels in a frame stand side by side"
    (match lineWith fls "First", lineWith fls "Second" with
     | some a, some b => a.y == b.y && decide (a.x < b.x)
     | _, _ => false)
  t "the frame of two side-by-side panels is one page, with no spill named"
    (fout.pages.size == 1 && (fds ++ fout.diags).all (·.code != "W0384"))
