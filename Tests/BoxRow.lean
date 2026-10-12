module

public import Tests.Support

public section

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
  -- Side by side, not stacked: the second title starts on the first's row,
  -- right of it. A painted block's box is as tall as its title's glyphs, so
  -- two titles of different letters stand a fraction of a point apart.
  t "two titled panels in a frame stand side by side"
    (match lineWith fls "First", lineWith fls "Second" with
     | some a, some b => decide ((a.y - b.y).natAbs < (Dim.pt 1).natAbs) && decide (a.x < b.x)
     | _, _ => false)
  t "the frame of two side-by-side panels is one page, with no spill named"
    (fout.pages.size == 1 && (fds ++ fout.diags).all (·.code != "W0384"))


/-- **A row stands its boxes on one baseline** (TeXbook ch. 12; latex.ltx
`\@iiiparbox`: `[t]` puts a box's first baseline on the line, `[b]` its
last, `[c]` its middle; `Ir.BoxPos`, `Layout.B.alignRow`). The defect set
every row top-aligned and noted the option as machinery nothing modelled
(N0102), so a `[b]` pair stood a full line away from where LaTeX puts it. A
picture's `baseline` is the height it stands on the line by
(`Ir.Pic.Picture.rise`): a paragraph of a positioned box and a picture is
one line, the label beside the graph. Read off `Layout.Out` and the typed
HTML tree. Invented content. -/
def boxPosRowChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let two (pos a b : String) : String :=
    dvDoc "" ("\\noindent\n\\parbox" ++ pos ++ "{3cm}{" ++ a ++ "}\\hfill\n\\parbox" ++ pos ++
      "{3cm}{" ++ b ++ "}")
  let tall := "Alpha bravo charlie delta echo foxtrot golf hotel india juliet kilo."
  let linesOf (src : String) : Array Layout.LineOut :=
    (allLines (layoutOf oneFace (elabStr src).1 geom)).filter
      fun l => !l.furniture && !l.segs.isEmpty
  let ys (src : String) (needle : String) : List Dim.Sp :=
    ((linesOf src).filter fun l => hasStr (lineText l) needle).toList.map (·.y)
  let tallYs (src : String) : List Dim.Sp :=
    ((linesOf src).filter fun l => !hasStr (lineText l) "Short").toList.map (·.y)
  -- `[b]`: the one-line box stands on the tall box's last line.
  let bRow := two "[b]" "Short." tall
  t "a [b] row stands each box on its last baseline"
    (match ys bRow "Short", (tallYs bRow).reverse with
     | [s], last :: _ :: _ => s == last
     | _, _ => false)
  -- `[t]` against a first line set larger: top edges would differ from
  -- first baselines, so this is the case the top-aligned row got wrong.
  let tRow := two "[t]" "Short." ("{\\Large Big} " ++ tall)
  t "a [t] row stands each box on its first baseline"
    (match ys tRow "Short", ys tRow "Big" with
     | [s], [b] => s == b
     | _, _ => false)
  -- `[c]`: a one-line box stands halfway down the tall one.
  let cRow := two "[c]" "Short." tall
  t "a [c] row stands each box on its middle"
    (match ys cRow "Short", tallYs cRow with
     | [s], y1 :: rest@(_ :: _) =>
       let yn := rest.getLast?.getD y1
       decide (s - (y1 + yn) / 2 ≤ 1 ∧ (y1 + yn) / 2 - s ≤ 1)
     | _, _ => false)
  t "an honoured box position names nothing"
    (!((elabStr bRow).2.any (·.code == "N0102")) && !((elabStr tRow).2.any (·.code == "N0102")))
  -- beamer's row-wide `[b]` reaches the columns that declare none.
  let cols := dvDeck "" ("\\begin{frame}{Cols}\n\\begin{columns}[b]\n" ++
    "\\begin{column}{.4\\textwidth}Short.\\end{column}\n" ++
    "\\begin{column}{.4\\textwidth}" ++ tall ++ "\\end{column}\n\\end{columns}\n\\end{frame}")
  t "a columns [b] row stands each column on its last baseline"
    (match ys cols "Short", (tallYs cols).reverse with
     | [s], last :: _ :: _ => s == last
     | _, _ => false)
  -- A positioned box, then a picture, one paragraph: one line. Elaborated
  -- as the driver elaborates, with the measurement layout sets labels by,
  -- so the node's `base` is where its label's baseline ships.
  let picLine := dvDoc "" ("\\raggedright\n\n\\parbox[t]{.2\\textwidth}{\\emph{Lab}}\n" ++
    "\\begin{tikzpicture}[baseline={(c.base)}]\n\\node (x) {Nodea};\n" ++
    "\\node (c) [right =of x] {Nodeb};\n\\path (c) edge (x);\n\\end{tikzpicture}\n")
  let elabM (s : String) : Ir.Doc × Array Diag := elabMeasured oneFace s
  let (pd, _) := elabM picLine
  let pls := (allLines (layoutOf oneFace pd)).filter fun l => !l.furniture && !l.segs.isEmpty
  t "a box and a picture on one line: the label stands beside the graph, on its node's baseline"
    (match pls.find? (fun l => hasStr (lineText l) "Lab"), pls.find? (fun l => hasStr (lineText l) "Nodeb") with
     | some lab, some node => lab.y == node.y && decide (lab.x < node.x)
     | _, _ => false)
  -- The HTML projections: the grid's own baseline alignment, and the
  -- declared baseline as the SVG's lift off the line.
  let (bDoc, _) := elabStr bRow
  let bStyles := bDoc.body.foldl (fun acc b => acc ++ attrValuesOf (· == "div") "style" (HtmlDoc.blockNode {} b)) #[]
  t "the HTML row stands [b] boxes on their last baselines"
    ((bStyles.filter (hasStr · "align-self: last baseline")).size == 2)
  let svgStyles := pd.body.foldl (fun acc b => acc ++ attrValuesOf (· == "svg") "style" (HtmlDoc.blockNode {} b)) #[]
  let pStyles := pd.body.foldl (fun acc b => acc ++ attrValuesOf (· == "div") "style" (HtmlDoc.blockNode {} b)) #[]
  t "the HTML picture stands on its declared baseline, beside its box"
    (svgStyles.any (hasStr · "vertical-align: -") &&
      (pStyles.filter (hasStr · "align-self: baseline")).size == 2)
  -- A baseline coordinate's y is read as a path reads a coordinate's
  -- component (TikZ manual §13.2.1): a length where it declares units, a
  -- number of the y vector otherwise, and with no transformation of the
  -- picture's, which pgf reads the coordinate after closing. So `(0,5pt)`
  -- stands the picture on its line as `baseline=5pt` does and `(0,0.2)` as
  -- `baseline=0.2cm`, at `scale=2` too, as lualatex sets them; the defect
  -- read every y as a number of the vector, scaled, and `(0,5pt)` as five of
  -- them. Every height here lies inside the picture's box, which bounds the
  -- rise (`Ir.Pic.Picture.rise`).
  let based (opts : String) : Ir.Doc :=
    (elabM (dvDoc "" ("\\raggedright\n\n\\parbox[t]{.2\\textwidth}{\\emph{Lab}}\n" ++
      "\\begin{tikzpicture}[" ++ opts ++ "]\n\\node (x) {Nodea};\n\\end{tikzpicture}\n"))).1
  let rise (opts : String) : Option Int :=
    let ls := (allLines (layoutOf oneFace (based opts))).filter fun l => !l.furniture && !l.segs.isEmpty
    match ls.find? (fun l => hasStr (lineText l) "Lab"), ls.find? (fun l => hasStr (lineText l) "Nodea") with
    | some lab, some node => some (node.y - lab.y)
    | _, _ => none
  let near (a b : Option Int) : Bool :=
    match a, b with
    | some x, some y => decide (x - y ≤ 2 ∧ y - x ≤ 2)
    | _, _ => false
  t "a baseline coordinate's y in points stands the picture as that length does"
    (near (rise "baseline={(0,5pt)}") (rise "baseline=5pt") &&
      near (rise "baseline={(1,5pt)}") (rise "baseline=5pt"))
  t "a baseline coordinate's unitless y is a number of the y vector"
    (near (rise "baseline={(0,0.2)}") (rise "baseline=0.2cm"))
  t "the picture's scale reaches no baseline coordinate"
    (near (rise "scale=2,baseline={(0,5pt)}") (rise "scale=2,baseline=5pt") &&
      near (rise "scale=2,baseline={(0,0.2)}") (rise "scale=2,baseline=0.2cm"))
  t "the baseline readings stand the picture at different heights"
    (!near (rise "baseline=5pt") (rise "baseline=0.2cm"))
  let lift (opts : String) : Array String :=
    (based opts).body.foldl (fun acc b => acc ++ attrValuesOf (· == "svg") "style" (HtmlDoc.blockNode {} b)) #[]
  t "the HTML picture's lift reads a baseline coordinate as the page does"
    (!(lift "baseline=5pt").isEmpty && lift "baseline={(0,5pt)}" == lift "baseline=5pt" &&
      lift "scale=2,baseline={(0,5pt)}" == lift "scale=2,baseline=5pt")
