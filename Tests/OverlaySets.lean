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

mutual

/-- Actual typed HTML text at a snap: the first component is present text,
the second is its uncovered subset. No source or IR is consulted. -/
private def overlayTextOne (k : Nat) (covered : Bool)
    (acc : String × String) : Html.Node → String × String
  | .text s => (acc.1 ++ s, if covered then acc.2 else acc.2 ++ s)
  | .style _ | .script _ _ => acc
  | .elem _ attrs kids =>
    let classes := (overlayAttr attrs "class").splitOn " "
    let shown :=
      if classes.contains "alt-set" then overlayActive attrs k
      else if classes.contains "alt-crisp" then overlayActive attrs k
      else if classes.contains "alt-pending" then !overlayActive attrs k
      else !(attrs.any (·.1 == "hidden"))
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
  let sourceWitness (label source : String) (active : List Bool) (alternative : Bool) := do
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
      let copies := if alternative && !selected then 0 else 1
      t (label ++ suffix ++ " layout text") (pageOccurs pages i "AmberMarker" == copies)
      t (label ++ suffix ++ " HTML text") (overlayCount shown "AmberMarker" == copies)
      t (label ++ suffix ++ " layout selection")
        (if alternative then pageOccurs pages i "BlueMarker" == (if selected then 0 else 1)
         else pageCovered pages i "AmberMarker" == !selected)
      t (label ++ suffix ++ " HTML selection")
        (overlayCount crisp "AmberMarker" == (if selected then 1 else 0) &&
          (!alternative || overlayCount shown "BlueMarker" == (if selected then 0 else 1)))
  let witness (label body : String) (active : List Bool) (alternative : Bool) :=
    sourceWitness label (deck169Frame
      (body ++ s!"\n\n\\uncover<{active.length}>" ++ "{ClockMarker}")) active alternative
  for (spec, active) in cases do
    witness ("uncover " ++ spec) (s!"Lead \\uncover<{spec}>" ++ "{AmberMarker}") active false
    witness ("alt " ++ spec) (s!"Lead \\alt<{spec}>" ++ "{AmberMarker}{BlueMarker}") active true
  let unionSteps := [true, false, false, true]
  for cmd in ["only", "uncover", "visible", "onslide"] do
    witness (cmd ++ " inline") (s!"Lead \\{cmd}<1,4>" ++ "{AmberMarker}") unionSteps false
    witness (cmd ++ " block") (s!"\\{cmd}<1,4>" ++ "{AmberMarker\n\nSecondMarker}")
      unionSteps false
    witness (cmd ++ " declaration") (s!"\\{cmd}<1,4>AmberMarker") unionSteps false
    witness (cmd ++ " spaced declaration") (s!"\\{cmd}<1,4> AmberMarker") unionSteps false
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

end Tests
