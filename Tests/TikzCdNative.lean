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
  -- A cell's own node options are named, never set as its mathematics.
  let (opted, optDs) := firstPass (dvDoc ("\\pictures{ tool = none }\n" ++ pre)
    "\\[\\begin{tikzcd} |[red]| \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  t "diagram natively: a cell's |[...]| options are named, never set as its mathematics"
    (optDs.any (fun d => d.code == "W0334" && hasStr d.message "cell options") &&
      hasStr (censusText (page opted)) "Alpha" && !hasStr (censusText (page opted)) "red")
  -- A label in a display the reader draws keeps its anchor, as a formula's
  -- does: the reference lands on the web page and on the PDF's page. The
  -- invariant whose absence shipped the drawing without its labels'
  -- anchors, so every link to them pointed nowhere.
  let labelled := "\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{hyperref}\n" ++
    pre ++ "\\begin{document}\n\\section{One}\nSee \\ref{cd} and \\ref{al}.\n" ++
    "\\[\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\label{cd}\\]\n" ++
    "Then\n\\begin{align*}\\begin{tikzcd} \\mathrm{Gamma} \\arrow[r] & \\mathrm{Delta} " ++
    "\\end{tikzcd}\\label{al}\\end{align*}\nAfter.\n\\end{document}"
  let (ldoc, _) := firstPass labelled
  let (_, lbody, hds) := HtmlDoc.emitTree {} ldoc
  let ids := lbody.flatMap (attrValuesOf (fun _ => true) "id")
  t "diagram natively: a label in its display keeps its anchor on the web page"
    ((Ir.pictureRefs ldoc).isEmpty && ids.contains "cd" && ids.contains "al" &&
      hds.all (·.code != "W0326") && hasStr (censusText (page ldoc)) "Delta")
  let lpages := (layoutOf mathSet ldoc).pages
  t "diagram natively: and on the PDF's page, where its link lands"
    ((Layout.destination? lpages "cd").isSome && (Layout.destination? lpages "al").isSome)
  -- A drawing sets in the size in force where it stands, as a diagram's
  -- cells and a picture's nodes set in the font current at their statement
  -- — the size the boundary's request carries too (`pictureSizeInForce`).
  -- The invariant whose absence drew a diagram under `\large` at the body
  -- size natively and at the large size at the boundary.
  let widthOf (src : String) (word : String) : Option Dim.Sp :=
    let c := page (firstPass src).1
    (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == word)).map (·.width)
  let one := "\\[\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]"
  let node := "\\begin{tikzpicture}\\node {Alpha};\\draw (0,0) -- node {Beta} (2,0);\\end{tikzpicture}"
  for (what, body) in [("a diagram's cells", one), ("a picture's node", node),
      ("a picture's edge label", node)] do
    let word := if what == "a picture's edge label" then "Beta" else "Alpha"
    match widthOf (dvDoc pre body) word, widthOf (dvDoc pre ("{\\large " ++ body ++ "\n}")) word,
        widthOf (dvDoc pre ("{\\small " ++ body ++ "\n}")) word with
    | some w, some wl, some ws =>
      t s!"drawing size: {what} set larger under \\large and smaller under \\small"
        (w * 11 < wl * 10 && ws < w)
    | _, _, _ => t s!"drawing size: {what} ships under each size" false
