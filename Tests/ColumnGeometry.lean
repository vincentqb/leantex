import Tests.Support

open LeanTex.Core LeanTex.Core.Dim

private structure ColumnGeomInk where
  page : Nat
  x : Sp
  y : Sp
  width : Sp

-- A full-line rule exposes the column's assigned measure without depending
-- on word widths, justification, or an IR claim about what reached the page.
private def columnGeomInk (out : Layout.Out) : Array ColumnGeomInk :=
  out.pages.zipIdx.flatMap fun (page, i) => page.lines.filterMap fun line =>
    if line.furniture then none else
    match line.segs with
    | #[.rule w _ _ _] => some ⟨i, line.x, line.y, w⟩
    | _ => none

private def columnGeomProp (style key : String) : Option String :=
  (style.splitOn ";").reverse.findSome? fun decl => do
    let [name, value] := decl.splitOn ":" | none
    if name.trimAscii.toString == key then some value.trimAscii.toString else none

private def columnGeomAtom (s : String) (measure : Sp) : Option Sp := do
  if s == "0" then return 0
  let (number, unit) ←
    if s.endsWith "pt" then some ((s.dropEnd 2).toString, pt 1)
    else if s.endsWith "%" then some ((s.dropEnd 1).toString, measure)
    else none
  let (n, d) ← Decl.parseDecimal number
  if d == 0 then none else
    some (n * unit / ((d : Int) * if s.endsWith "%" then 100 else 1))

-- Read the emitted additive affine CSS, independently of Ir.Track's writer.
-- Unknown units or expressions fail closed rather than being guessed.
private def columnGeomLength (s : String) (measure : Sp) : Option Sp := do
  if !(s.startsWith "calc(" && s.endsWith ")") then
    return ← columnGeomAtom s measure
  let terms := (((s.drop 5).toString.dropEnd 1).toString.splitOn " ").filter (!·.isEmpty)
  let mut total : Sp := 0
  let mut sign : Int := 1
  let mut needTerm := true
  for term in terms do
    if needTerm then
      let value ← columnGeomAtom term measure
      total := total + sign * value
      needTerm := false
    else if term == "+" || term == "-" then
      sign := if term == "-" then -1 else 1
      needTerm := true
    else
      return ← none
  if needTerm then none else some total

private def columnGeomTracks (s : String) : Option (Array String) := do
  let mut depth := 0
  let mut term := ""
  let mut terms := #[]
  for c in s.toList do
    if c == ')' then
      if depth == 0 then return ← none
      depth := depth - 1
    if c.isWhitespace && depth == 0 then
      unless term.isEmpty do
        terms := terms.push term
        term := ""
    else
      term := term.push c
    if c == '(' then depth := depth + 1
  if depth != 0 then return ← none
  return if term.isEmpty then terms else terms.push term

private def columnGeomTrack (s : String) (measure : Sp) : Option (Sp × Int) := do
  let s ←
    if s.startsWith "minmax(" && s.endsWith ")" then do
      let [lower, upper] := ((s.drop 7).toString.dropEnd 1).toString.splitOn "," | none
      if lower.trimAscii.toString != "0" then none else some upper.trimAscii.toString
    else some s
  if s.endsWith "fr" then
    let (n, d) ← Decl.parseDecimal (s.dropEnd 2).toString
    if n ≤ 0 || d == 0 then none else some (0, n * 1000 / d)
  else
    return (← columnGeomLength s measure, 0)

private structure ColumnGeomRow where
  left : Sp
  gap : Sp
  right : Sp
  deriving BEq, Repr

-- The browser's track arithmetic at the PDF's declared measure. Fixed
-- tracks leave their remainder to space-between; fr tracks consume only
-- what remains after the explicit gap and fixed tracks.
private def columnGeomHtml (style : String) (measure : Sp) : Option ColumnGeomRow := do
  if columnGeomProp style "display" != some "grid" then return ← none
  let gap ← columnGeomLength ((columnGeomProp style "column-gap").getD "0pt") measure
  let #[a, b] ← columnGeomTracks (← columnGeomProp style "grid-template-columns") | none
  let (aw, af) ← columnGeomTrack a measure
  let (bw, bf) ← columnGeomTrack b measure
  let remaining := measure - gap - aw - bw
  if gap < 0 || aw < 0 || bw < 0 || remaining < 0 then return ← none
  if af + bf > 0 then
    let left := aw + remaining * af / (af + bf)
    return ⟨left, gap, measure - gap - left⟩
  let justify := (columnGeomProp style "justify-content").getD "normal"
  if justify == "space-between" then return ⟨aw, gap + remaining, bw⟩
  if remaining == 0 || justify == "start" || justify == "normal" then
    return ⟨aw, gap, bw⟩
  none

private def columnGeomStyles (trees : Array Html.Node) : Array String :=
  (trees.foldl (fun acc tree => elemAttrsOne (· == "div") acc tree) #[]).filterMap
    fun (_, attrs) => do
      let cls ← (attrs.find? (·.1 == "class")).map (·.2)
      if !(cls.splitOn " ").contains "columns" then none else
        (attrs.find? (·.1 == "style")).map (·.2)

private def columnGeomSource (measure : Int) (body : String) (pre : String := "") : String :=
  dvDoc ("\\page{width=" ++ toString (measure + 40) ++
    "pt,height=600pt,hmargin=20pt,vmargin=20pt}\n" ++
    "\\usepackage{paracol}\n" ++ pre) body

private def columnGeomRule : String := "\\noindent\\rule{\\linewidth}{1pt}\\par\n"

private def columnGeomPair : String :=
  "\\begin{paracol}{2}\n" ++ columnGeomRule ++ "L.\\par\n\\switchcolumn\n" ++
    columnGeomRule ++ "R.\\par\n\\end{paracol}\n"

private def columnGeomExpected (measure gap : Sp) (quarter : Int) : ColumnGeomRow :=
  let left := (measure - gap) * quarter / 4
  ⟨left, gap, measure - gap - left⟩

private def columnGeomPlaces (out : Layout.Out) (text : String) : Array (Nat × Sp × Sp) :=
  out.pages.zipIdx.flatMap fun (page, i) => page.lines.filterMap fun line =>
    if !line.furniture && (lineText line false).trimAscii.toString == text then
      (lineRuns line)[0]?.map fun (_, _, x, _) => (i, x, line.y)
    else none

private def columnGeomCase (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (name src : String) (measure : Sp) (expected : Array ColumnGeomRow) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr src
  let out := layoutOf fonts doc
  let ink := columnGeomInk out
  let (_, trees, htmlDs) := HtmlDoc.emitTree {} doc
  let styles := columnGeomStyles trees
  let leftGlyphs := columnGeomPlaces out "L."
  let rightGlyphs := columnGeomPlaces out "R."
  t s!"{name}: both measuring rules ship once per row"
    (ink.size == 2 * expected.size)
  t s!"{name}: typed HTML ships every two-column row"
    (styles.size == expected.size)
  t s!"{name}: supported column declarations have no refusal or error"
    ((ds ++ out.diags ++ htmlDs).all fun d =>
      !d.code.startsWith "E" && !["W0104", "W0301", "W0302", "W0012"].contains d.code)
  for (want, i) in expected.zipIdx do
    let label := s!"{name} row {i + 1}"
    let pair := (ink[2 * i]?, ink[2 * i + 1]?)
    t s!"{label}: PDF ratios consume measure minus the exact gutter"
      (match pair with
       | (some a, some b) => a.width == want.left && b.width == want.right &&
           a.width + b.width + want.gap == measure
       | _ => false)
    t s!"{label}: PDF origins leave the declared gutter and fill the measure"
      (match pair with
       | (some a, some b) => a.x == pt 20 && b.x == a.x + a.width + want.gap &&
           b.x + b.width == pt 20 + measure && a.page == b.page && a.y == b.y
       | _ => false)
    t s!"{label}: shipped glyph origins follow the two column edges"
      (leftGlyphs.size == expected.size && rightGlyphs.size == expected.size &&
        match leftGlyphs[i]?, rightGlyphs[i]? with
        | some a, some b => a.2.1 == pt 20 && b.2.1 == pt 20 + want.left + want.gap &&
            a.1 == b.1 && a.2.2 == b.2.2
        | _, _ => false)
    let html := styles[i]?.bind (columnGeomHtml · measure)
    t s!"{label}: typed HTML resolves the same gutter and ratio widths"
      (html == some want)
    t s!"{label}: PDF origins and widths agree with typed HTML"
      (match pair, html with
       | (some a, some b), some h =>
         a.width == h.left && b.width == h.right && b.x - a.x == h.left + h.gap
       | _, _ => false)

private def columnGeomParagraphs (label : String) (count : Nat) : String :=
  String.join ((List.range count).map fun i =>
    columnGeomRule ++ s!"{label}{i + 1}.\\par\n")

private def columnGeomBefore (a b : Nat × Sp × Sp) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2.2 < b.2.2)

/-- The article class sets `\columnsep` to 10pt (article.cls).
Paracol's `\pcol@setcolwidth@r` first subtracts that gap from `\textwidth`,
then applies ratios and gives the last column the remainder. An invented
LuaLaTeX probe at a 200pt measure gives 47.5/142.5pt for ratio .25,
45.5/136.5pt under a locally scoped 18pt gap, and 47.5/142.5pt afterward.
These exact quarters need no rounding tolerance. The guards read shipped
rules and text in Layout.Out, and declarations in HtmlDoc.emitTree. -/
def columnGeometryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let css := "display: grid; column-gap: 10pt; grid-template-columns: "
  let want := columnGeomExpected (pt 200) (pt 10) 1
  t "column geometry CSS reader accepts affine and fractional tracks"
    (columnGeomHtml (css ++ "calc(25% - 2.5pt) calc(75% - 7.5pt)") (pt 200) == some want &&
      columnGeomHtml (css ++ "1fr 3fr") (pt 200) == some want &&
      columnGeomHtml (css ++ "minmax(0, 1fr) minmax(0, 3fr)") (pt 200) == some want)
  t "column geometry CSS reader resolves affine tracks with the implicit zero grid gap"
    (columnGeomHtml ("display: grid; justify-content: space-between; " ++
      "grid-template-columns: calc(25% - 2.5pt) calc(75% - 7.5pt)") (pt 200) == some want)
  t "column geometry CSS reader rejects full-measure percentages plus a gap and unknown units"
    ((columnGeomHtml (css ++ "25% 75%") (pt 200)).isNone &&
      (columnGeomHtml ("display: grid; column-gap: 0.75rem; " ++
        "grid-template-columns: 25% 75%") (pt 200)).isNone &&
      (columnGeomTracks "calc(25% - 2.5pt) calc(75% - 7.5pt").isNone)
  for (ratio, quarter) in #[(".25", 1), (".5", 2), (".75", 3)] do
    for measure in #[200, 360] do
      columnGeomCase ref oneFace s!"paracol default {measure}pt ratio {ratio}"
        (columnGeomSource measure columnGeomPair ("\\columnratio{" ++ ratio ++ "}\n"))
        (pt measure) #[columnGeomExpected (pt measure) (pt 10) quarter]
  for gap in #[0, 18] do
    let body := columnGeomPair ++ "{\\setlength{\\columnsep}{" ++ toString gap ++ "pt}\n" ++
      columnGeomPair ++ "}\n" ++ columnGeomPair
    columnGeomCase ref oneFace s!"paracol scoped {gap}pt"
      (columnGeomSource 200 body "\\columnratio{.25}\n") (pt 200)
      #[want, columnGeomExpected (pt 200) (pt gap) 1, want]
  -- Scope exit restores the values held at entry, regardless of their
  -- declaration source or the order in which local assignments changed them.
  let openGap := columnGeomExpected (pt 200) (pt 18) 1
  let closedGap := columnGeomExpected (pt 200) 0 1
  for nativeInBody in #[false, true] do
    let native := "\\tokens{columnsep=18pt}\n"
    let body := (if nativeInBody then native else "") ++ columnGeomPair ++
      "{\\setlength{\\columnsep}{0pt}\n" ++ columnGeomPair ++ "}\n" ++ columnGeomPair
    columnGeomCase ref oneFace s!"paracol restores native opening gap (body={nativeInBody})"
      (columnGeomSource 200 body
        ("\\columnratio{.25}\n" ++ if nativeInBody then "" else native))
      (pt 200) #[openGap, closedGap, openGap]
  for assignments in #[
      "\\setlength{\\columnsep}{0pt}\\setlength{\\savedgap}{30pt}\n",
      "\\setlength{\\savedgap}{30pt}\\setlength{\\columnsep}{0pt}\n"] do
    let body := columnGeomPair ++ "{" ++ assignments ++ columnGeomPair ++ "}\n" ++
      columnGeomPair ++ "\\setlength{\\columnsep}{\\savedgap}\n" ++ columnGeomPair
    columnGeomCase ref oneFace s!"paracol restores copied opening gap ({assignments.trimAscii})"
      (columnGeomSource 200 body
        ("\\columnratio{.25}\n\\newlength{\\savedgap}\\setlength{\\savedgap}{18pt}\n" ++
          "\\setlength{\\columnsep}{\\savedgap}\n"))
      (pt 200) #[openGap, closedGap, openGap, openGap]
  -- TeX copies a register's value at each executed assignment, including
  -- the class default and reads inside a command definition.
  columnGeomCase ref oneFace "paracol copied class gap"
    (columnGeomSource 200 columnGeomPair
      ("\\columnratio{.25}\n\\setlength{\\columnsep}{2\\columnsep}\n"))
    (pt 200) #[columnGeomExpected (pt 200) (pt 20) 1]
  columnGeomCase ref oneFace "paracol repeated gap macro"
    (columnGeomSource 200 columnGeomPair
      ("\\columnratio{.25}\n\\newcommand{\\doublegap}{\\setlength{\\columnsep}{2\\columnsep}}\n" ++
        "\\doublegap\\doublegap\n"))
    (pt 200) #[columnGeomExpected (pt 200) (pt 40) 1]
  columnGeomCase ref oneFace "paracol saved class gap"
    (columnGeomSource 200 columnGeomPair
      ("\\columnratio{.25}\n\\newlength{\\savedgap}\\setlength{\\savedgap}{\\columnsep}\n" ++
        "\\setlength{\\columnsep}{18pt}\\setlength{\\columnsep}{\\savedgap}\n"))
    (pt 200) #[want]
  -- Unequal flows still revisit their common opening page and join after
  -- the longer flow. Rules on every paragraph witness continuation widths.
  for (leftCount, rightCount) in #[(24, 1), (1, 24), (24, 17), (17, 24)] do
    let body := "\\begin{paracol}{2}\n" ++ columnGeomParagraphs "CL" leftCount ++
      "\\switchcolumn\n" ++ columnGeomParagraphs "CR" rightCount ++
      "\\end{paracol}\nAftergeom."
    let src := dvDoc ("\\page{width=240pt,height=200pt,hmargin=20pt,vmargin=20pt}\n" ++
      "\\usepackage{paracol}\n\\columnratio{.25}\n\\setlength{\\columnsep}{18pt}\n") body
    let (doc, ds) := elabStr src
    let out := layoutOf oneFace doc
    let want := columnGeomExpected (pt 200) (pt 18) 1
    let rightX := pt 20 + want.left + want.gap
    let name := s!"paracol gutter flow {leftCount}/{rightCount}"
    let ink := columnGeomInk out
    t s!"{name}: every continuation retains its assigned width and origin"
      (ink.size == leftCount + rightCount && ink.all fun r =>
        (r.x == pt 20 && r.width == want.left) || (r.x == rightX && r.width == want.right))
    t s!"{name}: both flows start on the same opening page and baseline"
      (match columnGeomPlaces out "CL1.", columnGeomPlaces out "CR1." with
       | #[a], #[b] => a.1 == 0 && b.1 == 0 && a.2.2 == b.2.2
       | _, _ => false)
    for (label, count, x) in #[("CL", leftCount, pt 20), ("CR", rightCount, rightX)] do
      let places := (List.range count).toArray.map fun i =>
        columnGeomPlaces out s!"{label}{i + 1}."
      t s!"{name}: every {label} paragraph ships once in page order"
        (places.all (·.size == 1) &&
          (places.zip (places.extract 1 places.size)).all fun (a, b) =>
            match a, b with
            | #[p], #[q] => columnGeomBefore p q
            | _, _ => false)
      t s!"{name}: {label} text keeps its column origin across pages"
        (places.all fun ps => match ps with | #[p] => p.2.1 == x | _ => false)
      if count == 24 then
        t s!"{name}: the long flow exercises another physical page"
          (match places[0]?, places[count - 1]? with
           | some #[a], some #[b] => a.1 < b.1
           | _, _ => false)
    t s!"{name}: following content resumes after both flow ends"
      (match columnGeomPlaces out s!"CL{leftCount}.", columnGeomPlaces out s!"CR{rightCount}.",
          columnGeomPlaces out "Aftergeom." with
       | #[a], #[b], #[last] => columnGeomBefore a last && columnGeomBefore b last
       | _, _, _ => false)
    t s!"{name}: valid flow has no layout error"
      ((ds ++ out.diags).all fun d => !d.code.startsWith "E")
