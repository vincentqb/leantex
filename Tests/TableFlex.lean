import Tests.Support

open LeanTex.Core LeanTex.Core.Dim

private def flexRuleWidths (out : Layout.Out) : Array Sp :=
  out.pages.flatMap fun p => p.lines.flatMap fun l =>
    if l.furniture then #[] else l.segs.filterMap fun s => match s with
      | .rule w _ _ _ => some w
      | _ => none

private structure FlexCase where
  name : String
  cols : String
  span : String
  row : String
  count : Nat := 1
  nested : Bool := false
  padR : Bool := true

private def flexCases : Array FlexCase := #[
  { name := "natural span before X", cols := "lX",
    span := "\\multicolumn{1}{l}{Spanmark}", row := "\\Cell & Tail" },
  { name := "natural span after X", cols := "Xl",
    span := "\\multicolumn{1}{l}{Spanmark}", row := "Tail & \\Cell" },
  { name := "two X columns", cols := "lXX", count := 2,
    span := "\\multicolumn{1}{l}{Spanmark}", row := "\\Cell & Mid & Tail" },
  { name := "outer pads removed", cols := "@{}lX@{}", padR := false,
    span := "\\multicolumn{1}{l}{Spanmark}", row := "\\Cell & Tail" },
  { name := "sized span", cols := "lX",
    span := "\\multicolumn{1}{p{64pt}}{Spanmark}", row := "\\Cell & Tail" },
  { name := "span over natural columns", cols := "llX",
    span := "\\multicolumn{2}{l}{Spanmark over two}", row := "\\Cell & Tail" },
  { name := "span ending in X", cols := "lXX", count := 2,
    span := "\\multicolumn{2}{l}{Spanmark over two columns}", row := "\\Cell & Tail" },
  { name := "span from X to natural", cols := "XlX", count := 2,
    span := "\\multicolumn{2}{l}{Spanmark over two columns}", row := "\\Cell & Tail" },
  { name := "full width span", cols := "XX", count := 2,
    span := "\\multicolumn{2}{c}{Spanmark}", row := "\\Cell\\\\ Left & Tail" },
  { name := "nested linewidth", cols := "lX", nested := true,
    span := "\\multicolumn{1}{l}{Spanmark}", row := "\\Cell & Tail" }]

private def flexSource (c : FlexCase) : String :=
  let target := if c.nested then "\\linewidth" else "200pt"
  let body := "\\begin{tabularx}{" ++ target ++ "}{" ++ c.cols ++ "}\n" ++
    "\\toprule\n" ++ c.row.replace "Tail" "x\\hfill Tail" ++
      "\\\\\n\\bottomrule\n\\end{tabularx}"
  dvDoc ("\\usepackage{tabularx,booktabs}\n\\newcommand{\\Cell}{" ++ c.span ++ "}\n")
    (if c.nested then "\\begin{minipage}{200pt}" ++ body ++ "\\end{minipage}" else body)

/-- Feasible spans participate in the X budget. The shipped full rules must
reach the declared target, to the division remainder of fewer than one sp
per X column, with every span's content retained. A macro keeps this guard
independent of Compat's handling of a direct multicolumn in tabularx. -/
def tableFlexChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for c in flexCases do
    let (doc, ds) := elabStr (flexSource c)
    let out := layoutOf oneFace doc
    let widths := flexRuleWidths out
    let census := censusOf #[] out
    t s!"tabularx {c.name}: full rules reach 200pt within the X division remainder"
      (widths.size == 2 &&
        widths.all fun w => pt 200 - ((c.count : Int) - 1) ≤ w && w ≤ pt 200)
    t s!"tabularx {c.name}: span and following cell each ship once"
      ((censusText census |>.splitOn "Spanmark").length == 2 &&
        (censusText census |>.splitOn "Tail").length == 2)
    let lines := (allLines out).filter (!·.furniture)
    let rule := lines.find? fun l => l.segs.any fun s => s matches .rule _ _ _ _
    let runs := lines.flatMap lineRuns
    let right := runs.foldl (fun x r => max x (r.2.2.1 + r.2.2.2)) 0
    let trailing := if c.padR then Ir.tabColSep.sp else 0
    t s!"tabularx {c.name}: last cell reaches the target edge inside its pad"
      (match rule with
       | some l => runs.size > 0 && l.x + pt 200 - ((c.count : Int) - 1) ≤ right + trailing &&
           right + trailing ≤ l.x + pt 200 &&
           runs.all (fun r => l.x ≤ r.2.2.1 && r.2.2.1 + r.2.2.2 ≤ l.x + pt 200)
       | none => false)
    t s!"tabularx {c.name}: valid input has no table or command refusal"
      ((ds ++ out.diags).all fun d =>
        !d.code.startsWith "E" && !#["W0301", "W0302", "W0337", "W0338"].contains d.code)
