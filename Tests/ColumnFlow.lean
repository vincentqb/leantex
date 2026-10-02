import Tests.Support

open LeanTex.Core LeanTex.Core.Dim

private def flowMark (label : String) (i : Nat) : String := s!"{label}{i + 1}."

private def flowText (label : String) (count : Nat) : String :=
  String.join ((List.range count).map fun i => flowMark label i ++ "\\par\n")

private def flowSource (left right : String) (lead : String := "") : String :=
  dvDoc "\\page{width=240pt,height=200pt,hmargin=20pt,vmargin=20pt}\n\\usepackage{paracol}\n"
    (lead ++ "\\begin{paracol}{2}\n" ++ left ++ "\\switchcolumn\n" ++ right ++
      "\\end{paracol}\nAfterflow.")

private def flowPlaces (census : Array CensusPage) (mark : String) : Array (Nat × Sp × Sp) :=
  census.zipIdx.flatMap fun (p, i) => p.lines.filterMap fun l =>
    if !l.furniture && hasStr l.text mark then some (i, l.x, l.y) else none

private def pageBefore (a b : Nat × Sp × Sp) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2.2 < b.2.2)

/-- Each independent flow starts at the row's opening page and baseline,
retains its own pagination, and joins after the later ending flow. Swapping
the columns may change x, never a paragraph's page or baseline. -/
def columnFlowChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for (leftCount, rightCount) in #[(24, 1), (1, 24), (24, 17), (17, 24)] do
    let left := flowText "Left" leftCount
    let right := flowText "Right" rightCount
    let (doc, ds) := elabStr (flowSource left right)
    let out := layoutOf oneFace doc
    let census := censusOf #[] out
    let swapped := censusOf #[] (layoutOf oneFace (elabStr (flowSource right left)).1)
    let name := s!"columns {leftCount}/{rightCount}"
    t s!"{name}: both flows start on page one at the same baseline"
      (match flowPlaces census "Left1.", flowPlaces census "Right1." with
       | #[l], #[r] => l.1 == 0 && r.1 == 0 && l.2.2 == r.2.2 && l.2.1 < r.2.1
       | _, _ => false)
    for (label, count) in #[("Left", leftCount), ("Right", rightCount)] do
      let places := (List.range count).toArray.map fun i =>
        flowPlaces census (flowMark label i)
      t s!"{name}: every {label} paragraph ships once, in order"
        (places.all (·.size == 1) &&
          (places.zip (places.extract 1 places.size)).all fun (a, b) =>
            match a, b with
            | #[p], #[q] => pageBefore p q
            | _, _ => false)
      t s!"{name}: swapping columns preserves {label} page and baseline"
        ((List.range count).all fun i =>
          let mark := flowMark label i
          match flowPlaces census mark, flowPlaces swapped mark with
          | #[a], #[b] => a.1 == b.1 && a.2.2 == b.2.2
          | _, _ => false)
    t s!"{name}: following content stands after both flow ends"
      (match flowPlaces census (flowMark "Left" (leftCount - 1)),
          flowPlaces census (flowMark "Right" (rightCount - 1)),
          flowPlaces census "Afterflow." with
       | #[l], #[r], #[after] => pageBefore l after && pageBefore r after
       | _, _, _ => false)
    let longest := if leftCount ≥ rightCount then left else right
    let alone := censusOf #[] (layoutOf oneFace (elabStr (flowSource longest "")).1)
    t s!"{name}: joining resumes at the longest flow's page and baseline"
      (match flowPlaces census "Afterflow.", flowPlaces alone "Afterflow." with
       | #[a], #[b] => a.1 == b.1 && a.2.2 == b.2.2
       | _, _ => false)
    t s!"{name}: valid flow has no error"
      ((ds ++ out.diags).all fun d => !d.code.startsWith "E")
  let lead := "Priorpage.\\newpage Openingline.\\par\n"
  let out := layoutOf oneFace (elabStr (flowSource (flowText "Left" 24)
    (flowText "Right" 1) lead)).1
  let census := censusOf #[] out
  t "columns opened on a later page preserve prior ink and restart both below the prefix"
    (match flowPlaces census "Priorpage.", flowPlaces census "Openingline.",
        flowPlaces census "Left1.", flowPlaces census "Right1." with
     | #[prior], #[opening], #[l], #[r] =>
       prior.1 == 0 && opening.1 == 1 && l.1 == 1 && r.1 == 1 &&
         opening.2.2 < l.2.2 && l.2.2 == r.2.2
     | _, _, _, _ => false)
  let right := "Rightstart.\\par\n\\begin{tabular}{ll}" ++
    "CellA & CellB\\\\ CellC & CellD\\end{tabular}"
  let nested := censusOf #[] (layoutOf oneFace
    (elabStr (flowSource (flowText "Left" 24) right)).1)
  let alone := censusOf #[] (layoutOf oneFace (elabStr (flowSource "" right)).1)
  t "a table in the shorter flow retains its opening-page row geometry"
    (#["Rightstart.", "CellA", "CellB", "CellC", "CellD"].all fun mark =>
      match flowPlaces nested mark, flowPlaces alone mark with
      | #[a], #[b] => a.1 == 0 && a == b
      | _, _ => false)
