module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

mutual

/-- The typed HTML text present at a step, and its uncovered subset. -/
private def overlayTextOne (k : Nat) (covered : Bool)
    (acc : String × String) : Html.Node → String × String
  | .text s => (acc.1 ++ s, if covered then acc.2 else acc.2 ++ s)
  | .style _ | .script _ _ => acc
  | .elem _ attrs kids =>
    let classes := (snapAttr attrs "class").splitOn " "
    let shown := snapShows attrs k && !(classes.contains "step-hide" && !snapActive attrs k)
    let covered := covered ||
      ((classes.contains "step" || classes.contains "step-set" ||
        classes.contains "step-end") && !snapActive attrs k)
    if shown then overlayTextList k covered acc kids.toList else acc

private def overlayTextList (k : Nat) (covered : Bool)
    (acc : String × String) : List Html.Node → String × String
  | [] => acc
  | n :: ns => overlayTextList k covered (overlayTextOne k covered acc n) ns

end

mutual

/-- The typed tree's paging destinations, a stepless frame's own included. -/
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

mutual

/-- Does an alternation's pair stand inside another's group (`inGroup`)? -/
private def nestedPairsOne (inGroup : Bool) : Html.Node → Bool
  | .elem _ attrs kids =>
    let cls := (snapAttr attrs "class").splitOn " "
    (inGroup && cls.contains "alt-pair") || nestedPairs (inGroup || cls.contains "alt") kids.toList
  | .text _ | .style _ | .script _ _ => false

private def nestedPairs (inGroup : Bool) : List Html.Node → Bool
  | [] => false
  | n :: rest => nestedPairsOne inGroup n || nestedPairs inGroup rest

end

mutual

/-- Every element carrying class `c`. -/
private def elemsWithClassOne (c : String) (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .elem tag attrs kids =>
    let acc := if ((snapAttr attrs "class").splitOn " ").contains c
      then acc.push (.elem tag attrs kids) else acc
    elemsWithClassList c acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def elemsWithClassList (c : String) (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => elemsWithClassList c (elemsWithClassOne c acc n) rest

end

private def elemsWithClass (nodes : Array Html.Node) (c : String) : Array Html.Node :=
  elemsWithClassList c #[] nodes.toList

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
    if snapShows attrs k then
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

/-- What a shipped page paints, whatever source leaf each mark stands for: its lines with their
segments, its fills and its picture marks. -/
private def pageMarks (p : Layout.PageOut) : Array String :=
  p.lines.map (fun l => reprStr (l.x, l.y, l.size, l.setWidth, l.hang, l.expand, l.furniture) ++
      String.join (l.segs.toList.map segMark)) ++
    p.fills.map reprStr ++ (pageInkMarks p).map reprStr

/-- A union selects exactly its numbered steps on both artifacts; covering keeps its one body and
alternation replaces it with one other. -/
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
  -- `\only` is absent where its selector does not select, as beamer's `\alt<s>{x}{}` is, and
  -- `\visible` invisible there; the others cover.
  for cmd in ["only", "uncover", "visible", "onslide"] do
    let absent := cmd == "only" || cmd == "visible"
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
  -- LuaLaTeX gives a title-only <1,4> four pages: the title's endpoints make the frame's steps.
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

/-- Every step of an `\only` frame ships the page, and every snap shows the text, of the frame
written with that step's reading, the argument's tokens where the selector selects. -/
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
     ("a display inside a paragraph", "Before.\n\\only<2>{\\[ a \\]}\nAfter.", 2,
       fun k => if k == 2 then "Before.\n\\[ a \\]\nAfter." else "Before.\n{}\nAfter."),
     ("two displays swapped", "Before.\n\\only<1>{\\[ a \\]}\\only<2>{\\[ b \\]}\nAfter.", 2,
       fun k => "Before.\n\\[ " ++ (if k == 1 then "a" else "b") ++ " \\]\nAfter."),
     ("a paragraph break inside a paragraph", "Before \\only<2>{text.\n\nNew para} after.", 2,
       fun k => if k == 2 then "Before text.\n\nNew para after." else "Before {} after."),
     ("a list inside a paragraph",
       "Before \\only<2>{\\begin{itemize}\\item x\\end{itemize}} after.", 2,
       fun k => if k == 2 then "Before \\begin{itemize}\\item x\\end{itemize} after."
         else "Before {} after."),
     ("a paragraph opening the frame", "\\only<2>{Head line.}\n\nBody line.", 2,
       fun k => if k == 2 then "Head line.\n\nBody line." else "Body line."),
     ("a paragraph closing the frame", "Body line.\n\n\\only<2>{Tail line.}", 2,
       fun k => if k == 2 then "Body line.\n\nTail line." else "Body line."),
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
     ("frame title", "\\frametitle{\\only<2>{Hidden }Shown}\nBody text.", 2,
       fun k => "\\frametitle{" ++ pick (k == 2) "Hidden " ++ "Shown}\nBody text."),
     ("block title", "\\begin{block}{\\only<2>{New }Heading}Body.\\end{block}", 2,
       fun k => "\\begin{block}{" ++ pick (k == 2) "New " ++ "Heading}Body.\\end{block}"),
     ("caption",
       "\\begin{figure}\\centering Figure body\\caption{Caption \\only<2>{extra} end}\\end{figure}", 2,
       fun k => "\\begin{figure}\\centering Figure body\\caption{Caption " ++
         (if k == 2 then "extra" else "{}") ++ " end}\\end{figure}"),
     ("inline in an item",
       "\\begin{itemize}\n\\item One \\only<2>{and more}\n\\item Two\n\\end{itemize}", 2,
       fun k => "\\begin{itemize}\n\\item One " ++ (if k == 2 then "and more" else "{}") ++
         "\n\\item Two\n\\end{itemize}"),
     ("cell", "\\begin{tabular}{ll}\nleft & \\only<2>{wide cell words}\\\\\nnext & row\n" ++
       "\\end{tabular}", 2,
       fun k => "\\begin{tabular}{ll}\nleft & " ++ (if k == 2 then "wide cell words" else "{}") ++
         "\\\\\nnext & row\n\\end{tabular}"),
     ("an item",
       "\\begin{enumerate}\n\\item Alpha one\n\\only<2>{\\item Beta two}\n\\item Gamma three\n" ++
         "\\end{enumerate}", 2,
       fun k => "\\begin{enumerate}\n\\item Alpha one\n" ++ pick (k == 2) "\\item Beta two\n" ++
         "\\item Gamma three\n\\end{enumerate}"),
     ("a row",
       "\\begin{tabular}{ll}\nDelta & four \\\\\n\\only<2>{Epsilon & five \\\\}\nZeta & six \\\\\n" ++
         "\\end{tabular}", 2,
       fun k => "\\begin{tabular}{ll}\nDelta & four \\\\\n" ++ pick (k == 2) "Epsilon & five \\\\\n" ++
         "Zeta & six \\\\\n\\end{tabular}"),
     ("union", "A \\only<1,3>{First}\\only<2>{Second} tail.", 3,
       fun k => "A " ++ (if k == 2 then "Second" else "First") ++ " tail."),
     ("nested", "Lead \\only<2-3>{outer \\only<3>{inner} done} end.", 3,
       fun k => "Lead " ++ (if k == 1 then "{}" else
         "outer " ++ (if k == 3 then "inner" else "{}") ++ " done") ++ " end."),
     ("swapped blocks", "\\only<1>{" ++ lines "First" 10 ++ "}\\only<2>{" ++ lines "Second" 10 ++ "}",
       2, fun k => lines (if k == 1 then "First" else "Second") 10),
     ("beside a document's own alt", "\\def\\alt#1#2#3{Lost}\nLead \\only<2>{Probe} trail.", 2,
       fun k => "\\def\\alt#1#2#3{Lost}\nLead " ++ (if k == 2 then "Probe" else "{}") ++ " trail."),
     ("a selector inside reaching past the outer one",
       "Top.\n\n\\only<2>{Middle.\n\n\\only<3>{Inner.}}\n\nBottom.", 3,
       fun k => "Top.\n\n" ++ pick (k == 2) "Middle.\n\n" ++ "Bottom."),
     ("a formula's selector reaching past the outer one",
       "Before.\n\\[ a \\only<2-3>{+ b \\only<4>{+ c}} \\]\nAfter.", 4,
       fun k => "Before.\n\\[ a " ++ pick (k == 2 || k == 3) "+ b" ++ " \\]\nAfter."),
     ("after a switch opening its paragraph",
       "\\centering\nAlpha words \\only<2>{\\[ x + y \\]} more words.\n\nNext paragraph here.", 2,
       fun k => "\\centering\nAlpha words " ++ (if k == 2 then "\\[ x + y \\]" else "{}") ++
         " more words.\n\nNext paragraph here."),
     ("in a centred scope",
       "\\begin{center}Lead words \\only<2>{\\[ x \\]} tail words.\\end{center}", 2,
       fun k => "\\begin{center}Lead words " ++ (if k == 2 then "\\[ x \\]" else "{}") ++
         " tail words.\\end{center}"),
     ("after a frame title", "\\frametitle{Probe Title}\n\\only<2>{Head line.}\n\nBody line.", 2,
       fun k => "\\frametitle{Probe Title}\n" ++ pick (k == 2) "Head line.\n\n" ++ "Body line."),
     ("in a block",
       "\\begin{block}{Claim}Claim words \\only<2>{\\[ x \\]} more words.\\end{block}", 2,
       fun k => "\\begin{block}{Claim}Claim words " ++ (if k == 2 then "\\[ x \\]" else "{}") ++
         " more words.\\end{block}"),
     ("beside a document's alternation of paragraphs",
       "\\alt<2->{After one.\n\nAfter two.}{Before.}\n\nBody \\only<2>{more }line.", 2,
       fun k => (if k == 2 then "After one.\n\nAfter two." else "Before.") ++ "\n\nBody " ++
         pick (k == 2) "more " ++ "line.")]
  for (label, body, steps, reading) in cases do
    let label := "only, " ++ label
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
  -- With no snap state — scripting off, the print sheet, the reduced page —
  -- the deck shows step 1's reading, and an argument that reading leaves out
  -- stands too: an alternation never shows nothing over what it says.
  let floor (body : String) : String :=
    let (_, tree, _) := HtmlDoc.emitTree {} (elabStr (deck169Frame body)).1
    shownTextList "" tree.toList
  t "only, with no snap state: an argument step 1 leaves out stands"
    (hasStr (floor "Lead words \\only<2>{Middle} trail words.") "Middle" &&
      hasStr (floor "Lead \\only<2-3>{Later} words.\n\n\\uncover<3>{Third.}") "Later")
  let swap := "\\only<1>{First reading.\n\nFirst more.}\\only<2>{Second reading.\n\nSecond more.}"
  t "only, with no snap state: blocks read per step show the handout, every argument"
    (hasStr (floor swap) "First reading." && hasStr (floor swap) "Second reading." &&
      hasStr (floor "Before.\n\\only<2>{\\[ y \\]}\nAfter words.") "𝑦")
  -- The handout's alternation selects no step: the floor shows its group and
  -- no step page does, which loses no increment; a group neither a step nor
  -- the floor reaches still does.
  t "only, a handout: no alternation group goes unreached"
    (Ir.altUnreachable (elabStr (deck169Frame swap)).1 == 0)
  t "only, beside a handout: a group no step reaches still counts"
    (Ir.altUnreachable (elabStr (deck169Frame
      "\\alt<1->{First words.}{Lost words.}\\only<2>{Later words.}")).1 == 1)
  -- A chain of readings stands its groups side by side, so the sheet's
  -- boundaries read one carrier deep however many readings a frame has.
  let rows := String.join ((List.range 16).map fun i =>
    s!"\\only<{i + 1}->" ++ "{R" ++ toString i ++ " & v \\\\}\n")
  let (_, many, _) := HtmlDoc.emitTree {} (elabStr (deck169Frame
    ("\\begin{tabular}{ll}\n" ++ rows ++ "\\end{tabular}"))).1
  t "only, sixteen readings: no alternation stands inside another's group"
    (!nestedPairs false many.toList && (elemsWithClass many "alt").size ≥ 16)
  -- A theorem's body is a flow of paragraphs, read per step as a frame's is
  -- (the class names the environment it does not define, W0302, and keeps
  -- its body).
  let thm (body : String) : String := deck169Frame ("\\begin{theorem}" ++ body ++ "\\end{theorem}")
  let tout := layoutOf fonts (elabStr (thm "Claim words \\only<2>{\\[ x \\]} more words.")).1
  for k in [1:3] do
    let rout := layoutOf fonts (elabStr (thm ("Claim words " ++
      (if k == 2 then "\\[ x \\]" else "{}") ++ " more words."))).1
    t s!"only, in a theorem: step {k}'s page is its reading's page"
      (tout.pages.size == 2 && (tout.pages[k - 1]?.map pageMarks) == (rout.pages[0]?.map pageMarks))
  -- A document that defines `\only` keeps its meaning.
  let (udoc, _) := elabStr (deck169Frame "\\def\\only#1{[#1]}Lead \\only<2>{later} end.")
  t "only, defined by the document: its own macro, no step"
    ((layoutOf fonts udoc).pages.size == 1 && hasStr (pageTextOf fonts
      (deck169Frame "\\def\\only#1{[#1]}Lead \\only<2>{later} end.")) "[")
  -- Overlays nested at a carrier's opening: the inner carrier's display
  -- stands where the outer carrier stands it, unless a break opens it.
  for (label, body, reading) in
      [("an uncover opening an uncover", "Before.\n\\uncover<1->{\\uncover<2->{\\[ x \\]}}\nAfter.",
         "Before.\n\\[ x \\]\nAfter."),
       ("an uncover opening an uncover on a break",
         "Before.\n\\uncover<1->{\\uncover<2->{\n\n\\[ x \\]}}\nAfter.",
         "Before.\n\n\\[ x \\]\nAfter.")] do
    let out := layoutOf fonts (elabStr (deck169Frame body)).1
    let rout := layoutOf fonts (elabStr (deck169Frame reading)).1
    let place (p : Layout.PageOut) : Array (Dim.Sp × Dim.Sp × String) :=
      p.lines.map fun l => (l.x, l.y, lineText l)
    t s!"nested overlays, {label}: the uncovered step's page is the flat frame's"
      (out.pages.size == 2 && (out.pages[1]?.map pageMarks) == (rout.pages[0]?.map pageMarks))
    t s!"nested overlays, {label}: the covered step stands its lines there too"
      ((out.pages[0]?.map place) == (rout.pages[0]?.map place))

end Tests

namespace Tests

/-- A segment's width where it inks: a run, an image, a rule, a decoration or a decorated gap. -/
private def inkWidth? : Layout.Seg → Option Dim.Sp
  | .run _ _ _ w .. => some w
  | .image _ w _ => some w
  | .rule w .. => some w
  | .decoration _ w .. => some w
  | .decoratedGap w .. => some w
  | .gap .. | .poly .. => none

/-- Does `page` stand every line of `covered`, each segment the same, or where `covered` inks a
gap as wide, and its polygons none? -/
private def standsInkless (page covered : Layout.PageOut) : Bool :=
  page.lines.size == covered.lines.size &&
    (page.lines.zip covered.lines).all fun (a, c) =>
      let segs := c.segs.filter fun s => !(s matches .poly ..)
      (a.x, a.y, a.size, a.setWidth) == (c.x, c.y, c.size, c.setWidth) &&
        a.segs.size == segs.size &&
        (a.segs.zip segs).all fun (x, y) =>
          segMark x == segMark y || (match x, inkWidth? y with
            | .gap w _, some wy => w == wy
            | _, _ => false)

/-- Off its steps `\visible`'s argument is invisible and keeps its space: every such step's page
is the page `\uncover` ships there with the argument's ink gone, a gap as wide in its place, and
every other step's the same page; `\onslide+` is `\visible`. -/
def overlayVisibleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf fonts
  -- label, body with `\CMD` for the command, the argument's words, the words beside it, the
  -- frame's steps and the steps where the argument is hidden
  let cases : List (String × String × List String × List String × Nat × List Nat) :=
    [("inline", "Lead words \\CMD<2>{Hidden phrase} tail words.", ["Hidden", "phrase"],
       ["Lead", "tail"], 2, [1]),
     ("a paragraph", "Top line.\n\n\\CMD<2>{Middle phrase.}\n\nBottom line.",
       ["Middle", "phrase"], ["Top", "Bottom"], 2, [1]),
     ("a list", "\\CMD<2>{\\begin{itemize}\\item Hidden one\\item Hidden two\\end{itemize}}\n\n" ++
       "After the list.", ["Hidden", "one", "two", "•"], ["After", "list"], 2, [1]),
     ("a formula", "Lead words \\CMD<2>{$q^2$} tail words.", ["𝑞"], ["Lead", "tail"], 2, [1]),
     ("a display", "Lead words.\n\\CMD<2>{\\[ q + 2 \\]}\nTail words.", ["𝑞", "+"],
       ["Lead", "Tail"], 2, [1]),
     ("a colour", "Lead words \\CMD<2>{\\textcolor{red}{Red phrase}} tail words.", ["Red", "phrase"],
       ["Lead", "tail"], 2, [1]),
     ("a link", "Lead words \\CMD<2>{\\href{https://example.org}{Link phrase}} tail words.",
       ["Link", "phrase"], ["Lead", "tail"], 2, [1]),
     ("an image", "Lead words \\CMD<2>{\\includegraphics[width=1cm]{absent.png}} tail words.", [],
       ["Lead", "tail"], 2, [1]),
     ("an open selector", "Lead words \\CMD<2->{Hidden phrase} tail \\uncover<3>{words.}",
       ["Hidden", "phrase"], ["Lead", "tail"], 3, [1]),
     ("inside a cover", "\\uncover<3>{Outer \\CMD<2>{Hidden} words}", ["Hidden"], ["Outer", "words"],
       3, [1, 3]),
     ("the rest of its group", "Lead words {\\CMD<2> Hidden phrase} tail words.",
       ["Hidden", "phrase"], ["Lead", "tail"], 2, [1])]
  for (label, body, absent, present, steps, hiddenAt) in cases do
    let label := "visible, " ++ label
    let spell (cmd : String) : String :=
      deck169Frame (("\\" ++ cmd).intercalate (body.splitOn "\\CMD"))
    let vdoc := (elabStr (spell "visible")).1
    let vout := layoutOf fonts vdoc
    let uout := layoutOf fonts (elabStr (spell "uncover")).1
    let pout := layoutOf fonts (elabStr (spell "onslide+")).1
    let census := censusOf (coveredColorsOf vdoc) vout
    t (label ++ ": one page per step") (vout.pages.size == steps && uout.pages.size == steps)
    t (label ++ ": onslide+ is visible") (pout.pages.map pageMarks == vout.pages.map pageMarks)
    for k in [1:steps + 1] do
      match vout.pages[k - 1]?, uout.pages[k - 1]? with
      | some v, some u =>
        if hiddenAt.contains k then
          t (label ++ s!": step {k} stands uncover's page, ink a gap as wide")
            (standsInkless v u)
          t (label ++ s!": step {k} ships none of the argument and all beside it")
            ((census[k - 1]?).any fun page =>
              absent.all (fun w => !hasStr page.text w && !hasStr page.covered w) &&
                present.all (fun w => hasStr page.text w || hasStr page.covered w))
          t (label ++ s!": step {k} ships no image")
            (v.lines.all fun l => l.segs.all fun s => !(s matches .image ..))
        else
          t (label ++ s!": step {k} is uncover's page") (pageMarks v == pageMarks u)
      | _, _ => t (label ++ s!": step {k} ships") false

end Tests
