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

/-- Where the argument a hidden step drops stands on the page that shows it. -/
private inductive ArgRegion where
  /-- The lines strictly between the line holding `above` and the line holding `below`, and the
  fills, pictures and links between their baselines. -/
  | lines (above below : String)
  /-- The segments at the baseline of the line holding both, between the end of the run holding
  `before` and the start of the run holding `after`. -/
  | segs (before after : String)
  | images

private def segText (s : Layout.Seg) : String := String.ofList s.glyphChars

private def lineIdxOf (p : Layout.PageOut) (w : String) : Option Nat :=
  p.lines.findIdx? fun l => hasStr (lineText l) w

/-- Each segment's pen x on its line. -/
private def segPens (l : Layout.LineOut) : Array Dim.Sp :=
  (l.segs.foldl (fun (acc : Array Dim.Sp × Dim.Sp) sg => (acc.1.push acc.2, acc.2 + sg.advance))
    (#[], l.x)).1

/-- Per line, which of the page's segments stand in the argument's region. -/
private def regionMask (p : Layout.PageOut) : ArgRegion → Array (Array Bool)
  | .lines above below =>
    match lineIdxOf p above, lineIdxOf p below with
    | some a, some b => p.lines.mapIdx fun i l => l.segs.map fun _ => a < i && i < b
    | _, _ => p.lines.map fun l => l.segs.map fun _ => false
  | .segs before after =>
    let span? := p.lines.findSome? fun l =>
      match l.segs.findIdx? (fun sg => hasStr (segText sg) before),
          l.segs.findIdx? (fun sg => hasStr (segText sg) after) with
      | some a, some b =>
        let pens := segPens l
        some (l.y, pens.getD a 0 + (l.segs.getD a default).advance, pens.getD b 0)
      | _, _ => none
    p.lines.map fun l => match span? with
      | some (y, x0, x1) =>
        if l.y != y then l.segs.map fun _ => false
        else (segPens l).zipWith (fun x sg => x0 ≤ x && x + sg.advance ≤ x1) l.segs
      | none => l.segs.map fun _ => false
  | .images => p.lines.map fun l => l.segs.map fun s => s matches .image ..

/-- The baselines a `.lines` region stands between. -/
private def regionBand (p : Layout.PageOut) : ArgRegion → Option (Dim.Sp × Dim.Sp)
  | .lines above below => do
    let a ← p.lines[← lineIdxOf p above]?
    let b ← p.lines[← lineIdxOf p below]?
    pure (a.y, b.y)
  | .segs .. | .images => none

private def fillIn (band : Option (Dim.Sp × Dim.Sp)) (f : Layout.Fill) : Bool :=
  band.any fun (top, bot) => top ≤ f.y && f.y + f.h ≤ bot

private def inkIn (band : Option (Dim.Sp × Dim.Sp)) (k : Layout.InkOut) : Bool :=
  band.any fun (top, bot) =>
    top ≤ k.place.dy && k.place.dy ≤ bot && k.claims.all fun b => top ≤ b.1.2 && b.2.2 ≤ bot

private def linkIn (band : Option (Dim.Sp × Dim.Sp)) (r : Layout.LinkRect) : Bool :=
  band.any fun (top, bot) => top ≤ r.y && r.y + r.h ≤ bot

private def segInks : Layout.Seg → Bool
  | .gap .. => false
  | .decoratedGap _ _ d => d.underline.isSome || d.lineThrough.isSome || d.highlight.isSome
  | .run .. | .decoration .. | .rule .. | .image .. | .poly .. => true

private def lineGeom (l : Layout.LineOut) : String :=
  reprStr (l.x, l.y, l.size, l.setWidth, l.hang, l.expand, l.furniture, l.note, l.regionExtent,
    l.lastBase)

private def inkMark (k : Layout.InkOut) : String := reprStr (k.fig, k.place)

/-- Does the hidden step's line stand where the shown one does, segment by segment as wide, the
region's ink a gap and its polygons gone, and everything else as the shown line inks it? -/
private def lineHides (h s : Layout.LineOut) (mask : Array Bool) : Bool :=
  let kept := (s.segs.zip mask).filter fun (sg, inR) => !(inR && sg matches .poly ..)
  lineGeom h == lineGeom s && h.segs.size == kept.size &&
    (h.segs.zip kept).all fun (hs, ss, inR) =>
      if inR && segInks ss then (match hs with | .gap w _ => w == ss.advance | _ => false)
      else segMark hs == segMark ss

/-- The region the shown page inks, so a check over it is not vacuous. -/
private def regionInks (s : Layout.PageOut) (r : ArgRegion) : Bool :=
  let band := regionBand s r
  ((s.lines.zip (regionMask s r)).any fun (l, m) =>
      (l.segs.zip m).any fun (sg, inR) => inR && segInks sg) ||
    s.fills.any (fillIn band) || s.inks.any (inkIn band)

/-- Off its steps `\visible`'s argument keeps its place and ships no ink, the page showing it held
to its every line, segment, fill and picture outside the argument; `\onslide+` is `\visible`. -/
def overlayVisibleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let some serif ← serifFacesSet | t "visible: the serif faces load" false
  let faceSets := [("", ← mathSetOf oneFace), (" in a kerned serif", serif)]
  let above := "Above words."
  let below := "Below words."
  let own (arg : String) : String × String :=
    (above ++ "\n\n\\CMD<2>{" ++ arg ++ "}\n\n" ++ below, above ++ "\n\n" ++ arg ++ "\n\n" ++ below)
  let inl (arg : String) : String × String :=
    ("Lead \\CMD<2>{" ++ arg ++ "} tail words.", "Lead " ++ arg ++ " tail words.")
  let lines := ArgRegion.lines "Above" "Below"
  let segs := ArgRegion.segs "Lead" "tail"
  let titlePage (title : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\theme{default}\n\\title{" ++ title ++
      "}\n\\author{Some Writer}\n\\begin{document}\n\\begin{frame}\n\\titlepage\n\\end{frame}\n" ++
      "\\end{document}"
  let markDeck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\usepackage{xcolor}\n" ++
      "\\palette{ alert = #1C1917 }\n\\definecolor{alertmark}{HTML}{FFEE00}\n\\begin{document}\n" ++
      "\\begin{frame}\n" ++ body ++ "\n\\end{frame}\n\\end{document}"
  -- label, body spelling the command `\CMD`, the body with the argument bare, the argument's
  -- region, the frame's steps and the steps it hides on
  let cases : List (String × (String × String) × ArgRegion × Nat × List Nat) :=
    [("a paragraph", own "Middle phrase.", lines, 2, [1]),
     ("an image alone", own "\\includegraphics[width=2cm]{absent.png}", lines, 2, [1]),
     ("a list", own "\\begin{itemize}\\item Bullet one\\item Bullet two\\end{itemize}", lines, 2, [1]),
     ("a description", own "\\begin{description}\\item[Term] Defining words.\\end{description}",
       lines, 2, [1]),
     ("a ruled table", own "\\begin{tabular}{|l|r|}\\hline Cell a & Cell b\\\\\\hline\\end{tabular}",
       lines, 2, [1]),
     ("a booktabs table",
       own "\\begin{tabular}{ll}\\toprule Head & Head\\\\\\midrule Cell & Cell\\\\\\bottomrule\\end{tabular}",
       lines, 2, [1]),
     ("a numbered equation", own "\\begin{equation} q + r = s \\end{equation}", lines, 2, [1]),
     ("a figure", own
       "\\begin{figure}\\includegraphics[width=2cm]{absent.png}\\caption{Caption words.}\\end{figure}",
       lines, 2, [1]),
     ("a listing", own "\\begin{lstlisting}[language=Python]\ndef f(q):\n    return \"s\"\n\\end{lstlisting}",
       lines, 2, [1]),
     ("a bibliography",
       own "\\begin{thebibliography}{9}\\bibitem{k} Some Writer. \\emph{Some Title}.\\end{thebibliography}",
       lines, 2, [1]),
     ("a shaded picture", own ("\\begin{tikzpicture}\\shade[left color=blue,right color=green] " ++
       "(0,0) rectangle (2,1);\\fill[red] (3,0.5) circle (0.5);\\end{tikzpicture}"), lines, 2, [1]),
     ("a block", own "\\begin{block}{Block title}Block words.\\end{block}", lines, 2, [1]),
     ("a theorem", own "\\begin{theorem}Theorem words.\\end{theorem}", lines, 2, [1]),
     ("an image in a node", own
       "\\begin{tikzpicture}\\node {\\includegraphics[width=1cm]{absent.png}};\\end{tikzpicture}",
       lines, 2, [1]),
     ("a block link", own "\\href{https://example.org}{Para one.\n\nPara two.}", lines, 2, [1]),
     ("inline text", inl "Hidden phrase", segs, 2, [1]),
     ("colour boundaries", inl "AV\\textcolor{red}{AV}\\textcolor{blue}{AVAV}AV", segs, 2, [1]),
     ("ligatures across colours", inl "f\\textcolor{red}{i}f\\textcolor{red}{f}\\textcolor{blue}{l}",
       segs, 2, [1]),
     ("a formula", inl "$\\sqrt{q^2} + \\frac{a}{b}$", segs, 2, [1]),
     ("an inline image", inl "\\includegraphics[height=1ex]{absent.png}", segs, 2, [1]),
     ("a rule", inl "\\rule{1em}{1ex}", segs, 2, [1]),
     ("a link", inl "\\href{https://example.org}{Link phrase}", segs, 2, [1]),
     ("an underline", inl "\\underline{Under phrase}", segs, 2, [1]),
     ("normal type", inl "\\textnormal{Plain phrase} and {\\normalfont plain words}", segs, 2, [1]),
     ("a footnote mark", inl "Noted\\footnote{Note words.}", segs, 2, [1]),
     ("an open selector", ("Lead \\CMD<2->{Hidden phrase} tail \\uncover<3>{words.}",
       "Lead Hidden phrase tail \\uncover<3>{words.}"), segs, 3, [1]),
     ("inside a cover", ("\\uncover<3>{Lead \\CMD<2>{Hidden} tail words.}",
       "\\uncover<3>{Lead Hidden tail words.}"), segs, 3, [1, 3]),
     ("an uncover inside", ("Lead \\CMD<2>{Outer \\uncover<3>{inner} words} tail words.",
       "Lead Outer \\uncover<3>{inner} words tail words."), segs, 3, [1, 3]),
     ("nested", ("Lead \\CMD<2>{Outer \\CMD<2>{inner} words} tail words.",
       "Lead Outer inner words tail words."), segs, 2, [1]),
     ("a block title", ("\\begin{block}{Lead \\CMD<2>{extra} tail}Block words.\\end{block}",
       "\\begin{block}{Lead extra tail}Block words.\\end{block}"), segs, 2, [1]),
     ("a figure caption",
       ("\\begin{figure}\\includegraphics[width=1cm]{absent.png}\\caption{Lead \\CMD<2>{extra} tail}" ++
         "\\end{figure}",
        "\\begin{figure}\\includegraphics[width=1cm]{absent.png}\\caption{Lead extra tail}\\end{figure}"),
       segs, 2, [1]),
     ("a table caption",
       ("\\begin{table}\\caption{Lead \\CMD<2>{extra} tail}\\begin{tabular}{ll} a & b \\\\ \\end{tabular}" ++
         "\\end{table}",
        "\\begin{table}\\caption{Lead extra tail}\\begin{tabular}{ll} a & b \\\\ \\end{tabular}\\end{table}"),
       segs, 2, [1]),
     ("a title page", (titlePage "Lead \\CMD<2>{extra} tail", titlePage "Lead extra tail"), segs, 2, [1]),
     ("columns", own ("\\begin{columns}\\column{.4\\textwidth} Left words.\\column{.4\\textwidth} " ++
       "Right words.\\end{columns}"), lines, 2, [1]),
     ("inside a column",
       ("\\begin{columns}\\column{.4\\textwidth} Lead \\CMD<2>{Hidden} tail.\\column{.4\\textwidth} " ++
         "Right words.\\end{columns}",
        "\\begin{columns}\\column{.4\\textwidth} Lead Hidden tail.\\column{.4\\textwidth} " ++
         "Right words.\\end{columns}"), segs, 2, [1]),
     ("inside a block", ("\\begin{block}{Block title}Lead \\CMD<2>{Hidden} tail words.\\end{block}",
       "\\begin{block}{Block title}Lead Hidden tail words.\\end{block}"), segs, 2, [1]),
     ("an alert's mark", (markDeck "Lead \\CMD<2>{\\alert{Marked phrase}} tail words.",
       markDeck "Lead \\alert{Marked phrase} tail words."), segs, 2, [1])]
  for (faces, fonts) in faceSets do
    for (label, (body, bare), region, steps, hiddenAt) in cases do
      let label := "visible, " ++ label ++ faces
      let doc (b : String) : String := if b.startsWith "\\documentclass" then b else deck169Frame b
      let spell (cmd : String) : String := doc (("\\" ++ cmd).intercalate (body.splitOn "\\CMD"))
      let vis := (fittedOf fonts (elabStr (spell "visible")).1).out
      let plus := (fittedOf fonts (elabStr (spell "onslide+")).1).out
      let shown := (fittedOf fonts (elabStr (doc bare)).1).out
      t (label ++ ": one page per step") (vis.pages.size == steps)
      t (label ++ ": onslide+ ships visible's pages")
        (plus.pages.map pageMarks == vis.pages.map pageMarks &&
          plus.pages.map (·.links) == vis.pages.map (·.links))
      for k in [1:vis.pages.size + 1] do
        let idx := if shown.pages.size == vis.pages.size then k - 1 else 0
        match vis.pages[k - 1]?, shown.pages[idx]? with
        | some h, some s =>
          if hiddenAt.contains k then
            let band := regionBand s region
            let mask := regionMask s region
            t (label ++ s!": step {k}'s argument inks the page showing it") (regionInks s region)
            t (label ++ s!": step {k} stands every line where the page showing the argument does, " ++
                "the argument's ink a gap as wide")
              (h.lines.size == s.lines.size &&
                (h.lines.zip s.lines).zipIdx.all fun ((hl, sl), i) =>
                  lineHides hl sl (mask[i]?.getD #[]))
            t (label ++ s!": step {k} ships that page's fills outside the argument and none inside")
              (h.fills.map reprStr == (s.fills.filter (!fillIn band ·)).map reprStr)
            t (label ++ s!": step {k} ships that page's pictures outside the argument and none inside")
              (h.inks.map inkMark == (s.inks.filter (!inkIn band ·)).map inkMark)
            t (label ++ s!": step {k} ships that page's links outside the argument and none inside")
              (h.links == s.links.filter (!linkIn band ·))
          else
            t (label ++ s!": step {k} is the page showing the argument")
              (pageMarks h == pageMarks s && h.inks.map inkMark == s.inks.map inkMark &&
                h.links == s.links)
        | _, _ => t (label ++ s!": step {k} ships") false
  -- A picture's label lines hide with the picture they label, step by step.
  let labelled := "\\begin{tikzpicture}\\draw (0,0) -- (2,0);\\node at (1,0.5) {Label words};" ++
    "\\end{tikzpicture}"
  for (faces, fonts) in faceSets do
    let out := (fittedOf fonts (elabStr (deck169Frame (above ++ "\n\n\\visible<2>{" ++ labelled ++
      "}\n\n" ++ below))).1).out
    let labels (k : Nat) : Array Layout.LineOut :=
      ((out.pages[k]?.map (·.lines)).getD #[]).filter (·.pictureLabel.isSome)
    t s!"visible, a picture's labels{faces}: both steps place them"
      (out.pages.size == 2 && !(labels 0).isEmpty && !(labels 1).isEmpty)
    t s!"visible, a picture's labels{faces}: hidden on the step hiding the picture, shown on the other"
      ((labels 0).all (·.hidden) && (labels 1).all (!·.hidden))
  -- Outside a frame no step is set, so the argument shows, as beamer's article mode sets it.
  let body := "Lead \\CMD<2>{shown phrase} tail words.\n\n\\CMD<2>{A whole paragraph.}\n\nClosing words."
  let bare := "Lead shown phrase tail words.\n\nA whole paragraph.\n\nClosing words."
  for (faces, fonts) in faceSets do
    let article (b : String) : Layout.Out :=
      (fittedOf fonts (elabStr (dvDoc "\\usepackage{beamerarticle}\n" b)).1).out
    let shown := article bare
    for cmd in ["visible", "onslide+"] do
      let out := article (("\\" ++ cmd).intercalate (body.splitOn "\\CMD"))
      t s!"visible, outside a frame{faces}: {cmd} ships the page showing its argument"
        (out.pages.map pageMarks == shown.pages.map pageMarks &&
          out.pages.map (·.links) == shown.pages.map (·.links))

end Tests
