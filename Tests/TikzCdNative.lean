module

public import Tests.TikzCd

public section

open LeanTex.Core LeanTex.Cli

/-- **A commutative diagram is drawn by the engine itself.** The invariant
whose absence sent every diagram to lualatex: tikz-cd is a TikZ matrix of
math cells in the `asymmetrical rectangle` shape — centred at the math
axis, so a row's cells share their axis — and arrows drawn after it from
one cell's border to another's, ending in `cm to`, with their labels in
script style at the path's middle, `auto` on the left of the direction
(tikzlibrarycd.code.tex). So a diagram the reader draws whole ships with no
boundary request and no formula floor: its cells' text, its arrows as
paths, its labels beside them, on `Layout.Out` and in the typed HTML. A
diagram with an option the reader cannot draw still goes to the boundary
whole, and with the boundary closed draws natively with the loss named.
Each diagram elaborates as the driver elaborates it, against the label
measurement layout sets with, so a cell's extent is its letters'. Invented
content; geometry read off the page. -/
def tikzcdNativeChecks (ref : IO.Ref (List String)) (mathSet : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\usepackage{tikz-cd}\n"
  let firstPass (src : String) : Ir.Doc × Array Diag := elabMeasured mathSet src
  let page (d : Ir.Doc) : Array CensusPage := censusOf (coveredColorsOf d) (layoutOf mathSet d)
  for (form, body) in cdDisplaysOf cdUpright do
    let (doc, ds) := firstPass (dvDoc pre body)
    let c := page doc
    t s!"diagram natively: {form}: no boundary request, no floor"
      ((Ir.pictureRefs doc).isEmpty && ds.all (·.code != "W0012") && ds.all (·.code != "N0023") &&
        ds.all (·.code != "W0334"))
    t s!"diagram natively: {form}: its cells and labels ship as text, its arrows as paths"
      (["Alpha", "Beta", "Gamma", "f", "g"].all (fun s => hasStr (censusText c) s) &&
        !hasStr (censusText c) "arrow" && (c[0]?.map (·.paths == 4)).getD false)
    t s!"diagram natively: {form}: the HTML holds the drawing, not an image"
      (doc.body.any fun b =>
        let n := HtmlDoc.blockNode {} b
        (elemNodesOne (· == "svg") #[] n).size == 1 &&
          (attrValuesOf (· == "img") "src" n).all (!·.startsWith Ir.picSrcPrefix))
  -- Geometry: one row shares its axis, one column its centre, and each
  -- label stands on the left of its arrow's direction.
  let (doc, _) := firstPass (dvDoc pre ("\\[" ++ cdUpright ++ "\\]"))
  let c := page doc
  let lineOf (s : String) : Option CensusLine :=
    (c[0]?.bind fun p => p.lines.find? fun l => l.text.trimAscii.toString == s)
  let centre (l : CensusLine) : Dim.Sp := l.x + l.width / 2
  t "diagram geometry: a row's cells share their baseline"
    (match lineOf "Alpha", lineOf "Beta" with
     | some a, some b => a.y == b.y && a.x < b.x
     | _, _ => false)
  t "diagram geometry: a column's cells share their centre, the lower row below"
    (match lineOf "Beta", lineOf "Gamma" with
     | some b, some g => decide (centre b - centre g ≤ 2 ∧ centre g - centre b ≤ 2) && b.y < g.y
     | _, _ => false)
  let shafts : Array (Array Ir.Pic.PathSeg) :=
    ((layoutOf mathSet doc).pages.flatMap pageDraws).filterMap fun (g, _, st) =>
      match g, st with
      | .path subs, some s => if s.cap == .butt then some (subpathSegs subs) else none
      | _, _ => none
  t "diagram geometry: the rightward arrow is level, its label above it"
    (match shafts.toList, lineOf "f" with
     | #[.line _ y0 _ y1] :: _, some f => y0 == y1 && f.y < y0
     | _, _ => false)
  t "diagram geometry: the downward arrow is plumb, its label on its right"
    (match shafts.toList, lineOf "g" with
     | _ :: #[.line x0 _ x1 _] :: _, some g => x0 == x1 && g.x > x0
     | _, _ => false)
  -- A wider separation by name sets the cells farther apart.
  let (wide, _) := firstPass (dvDoc pre
    "\\[\\begin{tikzcd}[column sep=large] \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  let (narrow, _) := firstPass (dvDoc pre
    "\\[\\begin{tikzcd}[column sep=tiny] \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  let gap (d : Ir.Doc) : Option Dim.Sp :=
    let c := page d
    match (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == "Alpha")),
          (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == "Beta")) with
    | some a, some b => some (b.x - (a.x + a.width))
    | _, _ => none
  t "diagram separation: a larger column sep by name parts the cells farther"
    (match gap wide, gap narrow with
     | some w, some n => n < w
     | _, _ => false)
  -- A diagram with an arrow key the reader does not draw goes to the
  -- boundary whole, and draws natively, named, where the boundary is closed.
  let lossy := "\\[\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r, hook] & \\mathrm{Beta} \\end{tikzcd}\\]"
  let (routed, routedDs, _) :=
    let (toks, lds) := Lex.lex "t" (dvDoc pre lossy)
    let (raws, pds) := Parse.parse "t" toks
    Elab.runRawsSpanned "t" raws (lds ++ pds)
  t "diagram natively: an arrow key outside the reader sends the diagram to the boundary"
    ((Ir.pictureRefs routed).size == 1 && routedDs.any (·.code == "N0023"))
  let (closed, closedDs) := firstPass (dvDoc ("\\pictures{ tool = none }\n" ++ pre) lossy)
  t "diagram natively: with the boundary closed it draws here and names the key"
    ((Ir.pictureRefs closed).isEmpty && closedDs.any (fun d => d.code == "W0334" && hasStr d.message "hook") &&
      hasStr (censusText (page closed)) "Alpha")
