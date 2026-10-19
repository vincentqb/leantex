module

public import Tests.TikzCd

public section

open LeanTex.Core LeanTex.Cli

/-- A commutative diagram is drawn by the engine itself. -/
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
  let (doc, _) := firstPass (dvDoc pre ("\\[" ++ cdUpright ++ "\\]"))
  let c := page doc
  let lineOf (s : String) : Option CensusLine :=
    (c[0]?.bind fun p => p.lines.find? fun l => l.text.trimAscii.toString == s)
  let centre (l : CensusLine) : Dim.Length := l.x + l.width / 2
  t "diagram geometry: a row's cells share their baseline"
    (match lineOf "Alpha", lineOf "Beta" with
     | some a, some b => a.y == b.y && a.x < b.x
     | _, _ => false)
  t "diagram geometry: a column's cells share their centre, the lower row below"
    (match lineOf "Beta", lineOf "Gamma" with
     | some b, some g => decide (centre b - centre g ≤ 2 * Dim.Length.quantum ∧ centre g - centre b ≤ 2 * Dim.Length.quantum) && b.y < g.y
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
  let (wide, _) := firstPass (dvDoc pre
    "\\[\\begin{tikzcd}[column sep=large] \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  let (narrow, _) := firstPass (dvDoc pre
    "\\[\\begin{tikzcd}[column sep=tiny] \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  let gap (d : Ir.Doc) : Option Dim.Length :=
    let c := page d
    match (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == "Alpha")),
          (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == "Beta")) with
    | some a, some b => some (b.x - (a.x + a.width))
    | _, _ => none
  t "diagram separation: a larger column sep by name parts the cells farther"
    (match gap wide, gap narrow with
     | some w, some n => n < w
     | _, _ => false)
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
  let (opted, optDs) := firstPass (dvDoc ("\\pictures{ tool = none }\n" ++ pre)
    "\\[\\begin{tikzcd} |[red]| \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]")
  t "diagram natively: a cell's |[...]| options are named, never set as its mathematics"
    (optDs.any (fun d => d.code == "W0334" && hasStr d.message "cell options") &&
      hasStr (censusText (page opted)) "Alpha" && !hasStr (censusText (page opted)) "red")
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
  let diagram := "\\[\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}\\]"
  let around (lead : String) : Option Dim.Length :=
    let c := page (firstPass (dvDoc pre (lead ++ "\n" ++ diagram ++ "\nAfter."))).1
    match (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == lead)),
          (c[0]?.bind fun p => p.lines.find? (·.text.trimAscii.toString == "After.")) with
    | some a, some b => some (b.y - a.y)
    | _, _ => none
  let skips := Ir.displaySkipsFor {} (Dim.pt 10)
  let short := "Short."
  let long := "Words enough to stand past the middle of the measure here."
  t "diagram display: after a long line the long skips, after a short one the short pair"
    (match around long, around short with
     | some l, some sh =>
       l - sh == (skips.above.width.sp - skips.aboveShort.width.sp) +
         (skips.below.width.sp - skips.belowShort.width.sp)
     | _, _ => false)
  let (desc, _) := firstPass (dvDoc ("\\palette{ bg = #202020, fg = #F0F0F0 }\n" ++ pre)
    "\\[\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r, \"f\" description] & \\mathrm{Beta} \\end{tikzcd}\\]")
  let fills := ((layoutOf mathSet desc).pages.flatMap pageDraws).filterMap fun (_, f, _) =>
    f.bind (paintColor? ·.paint)
  t "diagram description: its label's box is tikz-cd's white, whatever the page's ground"
    (fills.contains Ir.Color.white && !((desc.palette.find? "bg").any fills.contains))
  let bare := "\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r] & \\mathrm{Beta} \\end{tikzcd}"
  for (what, body) in [("in a paragraph of its own", "Before.\n\n" ++ bare ++ "\n\nAfter."),
      ("in a center", "Before.\n\n\\begin{center}" ++ bare ++ "\\end{center}\n\nAfter."),
      ("among a paragraph's text", "Before " ++ bare ++ " after.")] do
    let (bdoc, bds) := firstPass (dvDoc pre body)
    let bc := page bdoc
    t s!"diagram block: {what}: drawn by the reader, no unknown environment or reserved character"
      ((Ir.pictureRefs bdoc).isEmpty &&
        bds.all (fun d => !["E0311", "W0302", "W0012", "N0023"].contains d.code) &&
        ["Alpha", "Beta"].all (fun w => hasStr (censusText bc) w) &&
        (bc[0]?.map (·.paths == 2)).getD false)
    if what == "among a paragraph's text" then
      t "diagram block: among a paragraph's text, the break is named"
        (bds.any fun d => d.code == "W0334" && hasStr d.message "inside a paragraph")
  let (sdoc, _) := firstPass (dvDoc pre (short ++ "\n" ++ diagram ++ "\nAfter."))
  t "diagram display: on the web page the display paragraph holds the drawing"
    (sdoc.body.any fun b =>
      let n := HtmlDoc.blockNode {} b
      (attrValuesOf (· == "p") "class" n).contains "display" &&
        (elemNodesOne (· == "svg") #[] n).size == 1)
  let widthOf (src : String) (word : String) : Option Dim.Length :=
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
