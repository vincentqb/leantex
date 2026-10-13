module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private def overlayAttr (attrs : Array (String × String)) (key : String) : String :=
  ((attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- Read the emitted attribute vocabulary, independently of the IR selector:
the stylesheet matches space-separated step numbers, or the older contiguous
start/end attributes. The browser probe also exercises these selectors. -/
private def overlayActive (attrs : Array (String × String)) (k : Nat) : Bool :=
  if attrs.any (·.1 == "data-steps") then
    (overlayAttr attrs "data-steps").splitOn " " |>.contains (toString k)
  else
    let lo := (overlayAttr attrs "data-step").toNat?.getD 1
    let hi := (overlayAttr attrs "data-step-last").toNat?
    lo ≤ k && (hi.map fun u => decide (k ≤ u)).getD true

/-- Does an element show at snap `k`: an alternative where its steps select
it, anything else unless it is `hidden`. -/
private def overlayShown (attrs : Array (String × String)) (k : Nat) : Bool :=
  let classes := (overlayAttr attrs "class").splitOn " "
  if classes.contains "alt-set" then overlayActive attrs k
  else if classes.contains "alt-crisp" then overlayActive attrs k
  else if classes.contains "alt-pending" then !overlayActive attrs k
  else !(attrs.any (·.1 == "hidden"))

mutual

/-- Actual typed HTML text at a snap: the first component is present text,
the second is its uncovered subset. No source or IR is consulted. -/
private def overlayTextOne (k : Nat) (covered : Bool)
    (acc : String × String) : Html.Node → String × String
  | .text s => (acc.1 ++ s, if covered then acc.2 else acc.2 ++ s)
  | .style _ | .script _ _ => acc
  | .elem _ attrs kids =>
    let classes := (overlayAttr attrs "class").splitOn " "
    let shown := overlayShown attrs k
    let covered := covered ||
      ((classes.contains "step" || classes.contains "step-set" ||
        classes.contains "step-end") && !overlayActive attrs k)
    if shown then overlayTextList k covered acc kids.toList else acc

private def overlayTextList (k : Nat) (covered : Bool)
    (acc : String × String) : List Html.Node → String × String
  | [] => acc
  | n :: ns => overlayTextList k covered (overlayTextOne k covered acc n) ns

end

mutual

/-- Count the typed tree's actual paging destinations, including a stepless
frame's own snap. A selector alone cannot create a reachable reveal step. -/
private def overlaySnapsOne (acc : Nat) : Html.Node → Nat
  | .text _ | .style _ | .script _ _ => acc
  | .elem _ attrs kids =>
    overlaySnapsList (acc + if attrs.any (·.1 == "data-snap") then 1 else 0) kids.toList

private def overlaySnapsList (acc : Nat) : List Html.Node → Nat
  | [] => acc
  | n :: ns => overlaySnapsList (overlaySnapsOne acc n) ns

end

private def overlayCount (text needle : String) : Nat :=
  (text.splitOn needle).length - 1

/-- The elements whose box breaks the line, as a browser's default styles
set them. -/
private def renderedBlockTags : List String :=
  ["p", "li", "ul", "ol", "dl", "dt", "dd", "div", "section", "article", "aside", "nav",
   "header", "footer", "h1", "h2", "h3", "h4", "h5", "h6", "table", "thead", "tbody", "tr",
   "td", "th", "caption", "figure", "figcaption", "blockquote", "pre", "details", "summary",
   "hr", "br"]

mutual

/-- The typed tree's text shown at snap `k`, a line break at every block
edge: what `renderedLines` reads as the page a reader is shown. -/
private def overlayRenderedOne (k : Nat) (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    if overlayShown attrs k then
      let edge := if renderedBlockTags.contains tag then "\n" else ""
      overlayRenderedList k (acc ++ edge) kids.toList ++ edge
    else acc

private def overlayRenderedList (k : Nat) (acc : String) : List Html.Node → String
  | [] => acc
  | n :: ns => overlayRenderedList k (overlayRenderedOne k acc n) ns

end

/-- Shown text as a browser sets it under `white-space: normal`: each run of
white space one space, none at a block's edge, and no empty line. -/
private def renderedLines (s : String) : List String :=
  (s.splitOn "\n").filterMap fun line =>
    let words := (line.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)
    if words.isEmpty then none else some (" ".intercalate words)

/-- A shipped segment's marks, apart from the source leaf it stands for. -/
private def segMark : Layout.Seg → String
  | .run f c l w gs sz m d r g _ => reprStr (f, c, l, w, gs, sz, m, d, r, g)
  | s@(.gap ..) | s@(.decoratedGap ..) | s@(.decoration ..) | s@(.rule ..) | s@(.image ..)
  | s@(.poly ..) => reprStr s

/-- What a shipped page paints, read off `Layout.PageOut`, whatever source
leaf each mark stands for: every line's place, size, set width, hang and
expansion, with its segments — a run's face, colour, link, width, glyphs
and their advances, size, metrics, decorations, raise and ground — every
fill, and every picture mark. Two pages with the same marks paint the same
page. -/
private def pageMarks (p : Layout.PageOut) : Array String :=
  p.lines.map (fun l => reprStr (l.x, l.y, l.size, l.setWidth, l.hang, l.expand, l.furniture) ++
      String.join (l.segs.toList.map segMark)) ++
    p.fills.map reprStr ++ (pageInkMarks p).map reprStr

/-- A union selects exactly its numbered steps on both artifacts. Covering
keeps its one body, alternation replaces it with exactly one other body.
Every expectation is over the shipped layout or the emitted typed tree. -/
def overlaySetChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let cases : List (String × List Bool) :=
    [("1,4", [true, false, false, true]),
     ("1-4", [true, true, true, true]),
     ("1,3-4", [true, false, true, true]),
     ("1,4-", [true, false, false, true]),
     ("1-2,4", [true, true, false, true]),
     ("4,1,4", [true, false, false, true]),
     ("1-2,2,4", [true, true, false, true]),
     ("2,4", [false, true, false, true]),
     ("2-3,4-", [false, true, true, true]),
     ("-2,4", [true, true, false, true]),
     ("1,4-", [true, false, false, true, true]),
     ("1,4", [true, false, false, true, false])]
  let sourceWitness (label source : String) (active : List Bool) (alternative : Bool)
      (absent : Bool := false) := do
    let (doc, ds) := elabStr source
    t (label ++ ": numbered spec") (ds.all fun d => d.severity == .note)
    let pages := censusOf (coveredColorsOf doc) (layoutOf fonts doc)
    let (_, tree, _) := HtmlDoc.emitTree {} doc
    t (label ++ ": page count") (pages.size == active.length)
    t (label ++ ": HTML snap count") (overlaySnapsList 0 tree.toList == active.length)
    t (label ++ ": HTML body declared once") (treeOccurs tree "AmberMarker" == 1)
    if alternative then
      t (label ++ ": HTML other declared once") (treeOccurs tree "BlueMarker" == 1)
    for (selected, i) in active.zipIdx do
      let suffix := s!": step {i + 1}"
      let (shown, crisp) := overlayTextList (i + 1) false ("", "") tree.toList
      let copies := if (alternative || absent) && !selected then 0 else 1
      t (label ++ suffix ++ " layout text") (pageOccurs pages i "AmberMarker" == copies)
      t (label ++ suffix ++ " HTML text") (overlayCount shown "AmberMarker" == copies)
      t (label ++ suffix ++ " layout selection")
        (if alternative then pageOccurs pages i "BlueMarker" == (if selected then 0 else 1)
         else if absent then !pageCovered pages i "AmberMarker"
         else pageCovered pages i "AmberMarker" == !selected)
      t (label ++ suffix ++ " HTML selection")
        (overlayCount crisp "AmberMarker" == (if selected then 1 else 0) &&
          (!alternative || overlayCount shown "BlueMarker" == (if selected then 0 else 1)))
  let witness (label body : String) (active : List Bool) (alternative : Bool)
      (absent : Bool := false) :=
    sourceWitness label (deck169Frame
      (body ++ s!"\n\n\\uncover<{active.length}>" ++ "{ClockMarker}")) active alternative absent
  for (spec, active) in cases do
    witness ("uncover " ++ spec) (s!"Lead \\uncover<{spec}>" ++ "{AmberMarker}") active false
    witness ("alt " ++ spec) (s!"Lead \\alt<{spec}>" ++ "{AmberMarker}{BlueMarker}") active true
  let unionSteps := [true, false, false, true]
  -- `\only` is absent where its selector does not select, as beamer's
  -- `\alt<s>{x}{}` is; the others cover, keeping their space.
  for cmd in ["only", "uncover", "visible", "onslide"] do
    let absent := cmd == "only"
    witness (cmd ++ " inline") (s!"Lead \\{cmd}<1,4>" ++ "{AmberMarker}") unionSteps false absent
    witness (cmd ++ " block") (s!"\\{cmd}<1,4>" ++ "{AmberMarker\n\nSecondMarker}")
      unionSteps false absent
    witness (cmd ++ " declaration") (s!"\\{cmd}<1,4>AmberMarker") unionSteps false absent
    witness (cmd ++ " spaced declaration") (s!"\\{cmd}<1,4> AmberMarker") unionSteps false
      absent
  witness "alt block" "\\alt<1,4>{AmberMarker\n\nFirstMarker}{BlueMarker\n\nOtherMarker}"
    unionSteps true
  for env in ["itemize", "enumerate", "description"] do
    witness (env ++ " item") ("\\begin{" ++ env ++ "}\n\\item<1,4> AmberMarker\n\\end{" ++ env ++ "}")
      unionSteps false
  witness "overprint union" ("\\begin{overprint}\n\\onslide<1,4> AmberMarker\n" ++
    "\\onslide<2-3> BlueMarker\n\\end{overprint}") unionSteps true
  witness "nested selectors" "\\uncover<1,3-4>{\\uncover<1-2,4>{AmberMarker}}"
    unionSteps false
  -- A frame's title and subtitle share the extent established by its body.
  -- Each selected title reaches the shipped page once; both source branches
  -- stand once in HTML while only the selected branch is shown at each snap.
  for (spec, active) in
      [("1,4", unionSteps), ("1-4", [true, true, true, true]),
       ("2,4", [false, true, false, true]),
       ("1,3-4", [true, false, true, true]),
       ("1,4-", [true, false, false, true, true])] do
    let title := s!"\\alt<{spec}>" ++ "{AmberMarker}{BlueMarker}"
    witness ("frame title " ++ spec) ("\\frametitle{" ++ title ++ "}\nBodyMarker")
      active true
    witness ("frame subtitle " ++ spec)
      ("\\frametitle{Header}\n\\framesubtitle{" ++ title ++ "}\nBodyMarker")
      active true
    sourceWitness ("frame title argument " ++ spec)
      (deck169Body ("\\begin{frame}{" ++ title ++ "}\nBodyMarker\n\\uncover<" ++
        toString active.length ++ ">{ClockMarker}\n\\end{frame}")) active true
  -- LuaLaTeX gives a title-only <1,4> four pages: the title's endpoints
  -- create the frame's steps even when its body has no overlay.
  for (spec, active) in
      [("1,4", unionSteps), ("1-4", [true, true, true, true]),
       ("2,4", [false, true, false, true]),
       ("1,3-4", [true, false, true, true]),
       ("1,4-", unionSteps), ("1-2,4", [true, true, false, true])] do
    let title := s!"\\alt<{spec}>" ++ "{AmberMarker}{BlueMarker}"
    sourceWitness ("title-only " ++ spec)
      (deck169Frame ("\\frametitle{" ++ title ++ "}\nBodyMarker")) active true
    sourceWitness ("subtitle-only " ++ spec)
      (deck169Frame ("\\frametitle{Header}\n\\framesubtitle{" ++ title ++ "}\nBodyMarker"))
      active true
    sourceWitness ("title argument only " ++ spec)
      (deck169Body ("\\begin{frame}{" ++ title ++ "}\nBodyMarker\n\\end{frame}"))
      active true
  -- HTML furniture inside the sticky stage uses the same finite extent.
  -- Its source branches remain single nodes, including at an open range end.
  for cmd in ["framefoot", "logo"] do
    for (spec, active) in
        [("1,4", unionSteps), ("1-4", [true, true, true, true]),
         ("1,4-", [true, false, false, true, true])] do
      let label := cmd ++ " HTML " ++ spec
      let source := deck169Body
        (s!"\\{cmd}" ++ "{\\alt<" ++ spec ++ ">{AmberMarker}{BlueMarker}}\n" ++
          "\\begin{frame}\nBodyMarker\n\\uncover<" ++ toString active.length ++
          ">{ClockMarker}\n\\end{frame}")
      let (doc, ds) := elabStr source
      t (label ++ ": numbered spec") (ds.all fun d => d.severity == .note)
      let (_, tree, _) := HtmlDoc.emitTree {} doc
      t (label ++ ": one source copy per branch")
        (treeOccurs tree "AmberMarker" == 1 && treeOccurs tree "BlueMarker" == 1)
      for (selected, i) in active.zipIdx do
        let (shown, _) := overlayTextList (i + 1) false ("", "") tree.toList
        t (label ++ s!": step {i + 1} selection")
          (overlayCount shown "AmberMarker" == (if selected then 1 else 0) &&
            overlayCount shown "BlueMarker" == (if selected then 0 else 1))

/-- **`\only` is absent off its steps, and takes no space.** Beamer's
`\only<s>{x}` is `\alt<s>{x}{}` (beamerbaseoverlay.sty): on a step its
selector does not select, the frame is typeset as if `x` were not written,
and TeX keeps the spaces around it. So every step's shipped page is the page
of the frame written with that step's reading — the argument's tokens where
the selector selects, nothing elsewhere — and every snap of the typed tree
shows that reading's text, nothing covered. Read over `Layout.PageOut`
(`pageMarks`) and the emitted tree, for an argument inline, as paragraphs,
in display and inline formulas, as its next token, as a control word with
its groups, in a title, an item and a cell, under unions and nesting, and as
`\onslide*` — and for `\alt` nested at an alternative's opening, whose
display stands in the paragraph the outer alternation opened in, as a
formula's readings chain. The defect it names: `\only` covered its argument
and kept its space, as `\uncover` does, so a frame whose steps swap blocks
by `\only` stood every step at the height of all of them and continued on a
further page where lualatex sets one per step. -/
def overlayOnlyChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf fonts
  let pick (b : Bool) (x : String) : String := if b then x else ""
  let lines (tag : String) (n : Nat) : String :=
    "\n\n".intercalate ((List.range n).map fun i => s!"{tag} block line {i} with words.")
  let cases : List (String × String × Nat × (Nat → String)) :=
    [("inline", "Lead words \\only<2>{Middle} trail words.", 2,
       fun k => "Lead words " ++ (if k == 2 then "Middle" else "{}") ++ " trail words."),
     ("paragraphs",
       "Top paragraph.\n\n\\only<2>{Middle paragraph.\n\nSecond middle.}\n\nBottom paragraph.", 2,
       fun k => "Top paragraph.\n\n" ++ pick (k == 2) "Middle paragraph.\n\nSecond middle.\n\n" ++
         "Bottom paragraph."),
     ("display formula", "Before.\n\\[ a + \\only<2>{b +} c \\]\nAfter.", 2,
       fun k => "Before.\n\\[ a + " ++ pick (k == 2) "b + " ++ "c \\]\nAfter."),
     ("display formula after a break", "Before.\n\n\\[ a + \\only<2>{b +} c \\]\n\nAfter.", 2,
       fun k => "Before.\n\n\\[ a + " ++ pick (k == 2) "b + " ++ "c \\]\n\nAfter."),
     ("display formula union", "Before.\n\\[ x \\only<1,3>{+ y} \\only<2>{- z} \\]\nAfter.", 3,
       fun k => "Before.\n\\[ x " ++ pick (k != 2) "+ y" ++ " " ++ pick (k == 2) "- z" ++
         " \\]\nAfter."),
     ("unnumbered equation", "Before.\n\\begin{equation*} a \\only<2>{+ b} \\end{equation*}\nAfter.",
       2, fun k => "Before.\n\\begin{equation*} a " ++ pick (k == 2) "+ b" ++
         " \\end{equation*}\nAfter."),
     ("inline formula", "Value $x \\only<2>{+ y}$ here.", 2,
       fun k => "Value $x " ++ pick (k == 2) "+ y" ++ "$ here."),
     ("next token", "Lead \\only<2>Word end.", 2,
       fun k => "Lead " ++ (if k == 2 then "Word" else "ord") ++ " end."),
     ("control word", "Lead \\only<2>\\textbf{bold} rest.", 2,
       fun k => "Lead " ++ (if k == 2 then "\\textbf{bold}" else "{bold}") ++ " rest."),
     ("onslide star", "Lead words \\onslide*<2>{Middle} trail words.", 2,
       fun k => "Lead words " ++ (if k == 2 then "Middle" else "{}") ++ " trail words."),
     ("title", "\\frametitle{\\only<2>{Hidden }Shown}\nBody text.", 2,
       fun k => "\\frametitle{" ++ pick (k == 2) "Hidden " ++ "Shown}\nBody text."),
     ("item", "\\begin{itemize}\n\\item One \\only<2>{and more}\n\\item Two\n\\end{itemize}", 2,
       fun k => "\\begin{itemize}\n\\item One " ++ (if k == 2 then "and more" else "{}") ++
         "\n\\item Two\n\\end{itemize}"),
     ("cell", "\\begin{tabular}{ll}\nleft & \\only<2>{wide cell words}\\\\\nnext & row\n" ++
       "\\end{tabular}", 2,
       fun k => "\\begin{tabular}{ll}\nleft & " ++ (if k == 2 then "wide cell words" else "{}") ++
         "\\\\\nnext & row\n\\end{tabular}"),
     ("union", "A \\only<1,3>{First}\\only<2>{Second} tail.", 3,
       fun k => "A " ++ (if k == 2 then "Second" else "First") ++ " tail."),
     ("nested", "Lead \\only<2-3>{outer \\only<3>{inner} done} end.", 3,
       fun k => "Lead " ++ (if k == 1 then "{}" else
         "outer " ++ (if k == 3 then "inner" else "{}") ++ " done") ++ " end."),
     ("swapped blocks", "\\only<1>{" ++ lines "First" 10 ++ "}\\only<2>{" ++ lines "Second" 10 ++ "}",
       2, fun k => lines (if k == 1 then "First" else "Second") 10),
     -- An alternation nested at another's opening stands its display where
     -- the outer one stands it: in the paragraph the text before it opened.
     ("alt nested at an alternative's opening",
       "Before.\n\\alt<1>{\\[ a \\]}{\\alt<2>{\\[ b \\]}{\\[ c \\]}}\nAfter.", 2,
       fun k => "Before.\n\\[ " ++ (if k == 1 then "a" else "b") ++ " \\]\nAfter."),
     ("alt nested before a break",
       "Before.\n\\alt<1>{\\[ a \\]}{\\alt<2>{\\[ b \\]}{\\[ c \\]}}\n\nAfter.", 2,
       fun k => "Before.\n\\[ " ++ (if k == 1 then "a" else "b") ++ " \\]\n\nAfter.")]
  for (label, body, steps, reading) in cases do
    let label := "overlay reading, " ++ label
    let (doc, ds) := elabStr (deck169Frame body)
    let fitted := fittedOf fonts doc
    let out := layoutOf fonts doc
    let (_, tree, hds) := HtmlDoc.emitTree {} doc
    t (label ++ ": no loss") ((ds ++ fitted.out.diags ++ hds).all (·.severity == .note))
    t (label ++ ": one page per step") (fitted.out.pages.size == steps && out.pages.size == steps)
    for k in [1:steps + 1] do
      let (rdoc, _) := elabStr (deck169Frame (reading k))
      let rout := layoutOf fonts rdoc
      let (_, rtree, _) := HtmlDoc.emitTree {} rdoc
      t (label ++ s!": step {k}'s page is its reading's page")
        (rout.pages.size == 1 &&
          (out.pages[k - 1]?.map pageMarks) == (rout.pages[0]?.map pageMarks))
      let (shown, crisp) := overlayTextList k false ("", "") tree.toList
      t (label ++ s!": snap {k} shows its reading's text, nothing covered")
        (renderedLines (overlayRenderedList k "" tree.toList) ==
            renderedLines (overlayRenderedList 1 "" rtree.toList) &&
          crisp == shown)

end Tests
