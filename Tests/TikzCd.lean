module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-- A three-object diagram in tikz-cd's syntax, with both arrow spellings. -/
def cdDiagram : String :=
  "\\begin{tikzcd} Alpha \\arrow[r, \"f\"] & Beta \\arrow{d}{g} \\\\ & Gamma \\end{tikzcd}"

/-- The three displays a diagram stands alone in: `\[…\]`, `equation*` and an unnumbered
alignment. -/
def cdDisplaysOf (d : String) : List (String × String) :=
  [("a bracket display", "\\[" ++ d ++ "\\]"),
   ("equation*", "\\begin{equation*}" ++ d ++ "\\end{equation*}"),
   ("align*", "\\begin{align*}" ++ d ++ "\\end{align*}")]

/-- The diagram with an arrow key the native reader does not draw (a hooked tail). -/
def cdLossy : String :=
  "\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r, \"f\", hook] & \\mathrm{Beta} \\arrow{d}{g} " ++
    "\\\\ & \\mathrm{Gamma} \\end{tikzcd}"

/-- The diagram with upright cells and labels, whose text a page census reads back as written. -/
def cdUpright : String :=
  "\\begin{tikzcd} \\mathrm{Alpha} \\arrow[r, \"\\mathrm{f}\"] & \\mathrm{Beta} " ++
    "\\arrow{d}{\\mathrm{g}} \\\\ & \\mathrm{Gamma} \\end{tikzcd}"

/-- A commutative diagram standing alone in a display ships a picture, never a placeholder. -/
def tikzcdRouteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\usepackage{tikz-cd}\n"
  let firstPass (src : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let (toks, lds) := Lex.lex "t" src
    let (raws, pds) := Parse.parse "t" toks
    Elab.runRawsSpanned "t" raws (lds ++ pds)
  let shipped (d : Ir.Doc) (imgs : Image.Store := {}) : Array CensusPage :=
    censusOf (coveredColorsOf d) (layoutOf oneFace d (imgs := imgs))
  let picImages (d : Ir.Doc) : Array String := (Ir.imageRefs d).filter (·.startsWith Ir.picSrcPrefix)
  let displayImgs (d : Ir.Doc) : Nat :=
    d.body.foldl (fun n b =>
      let html := HtmlDoc.blockNode {} b
      let displays := (elemNodesList (fun tag => tag == "p") #[] [html]).filter fun e =>
        match e with
        | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "display"
        | _ => false
      n + (displays.foldl (fun acc e =>
        acc ++ (attrValuesOf (· == "img") "src" e).filter (·.startsWith Ir.picSrcPrefix))
        #[]).size) 0
  for (form, body) in cdDisplaysOf cdLossy do
    let (doc, ds, rs) := firstPass (dvDoc pre body)
    let refs := Ir.pictureRefs doc
    t s!"a lone diagram in {form} states one diagram request"
      (refs.size == 1 && doc.pictureSrcs.all (·.2.kind == .cd))
    t s!"its standalone opens the diagram's own environment, in no picture: {form}"
      (refs.all fun (_, w) =>
        hasStr w "\\begin{tikzcd}" && hasStr w "\\end{tikzcd}" &&
        !hasStr w "\\begin{tikzpicture}" && hasStr w "\\usepackage{tikz-cd}")
    t s!"no text floor is named and the package load is not refused: {form}"
      (ds.all (·.code != "W0012") && ds.all (·.code != "W0103") &&
       ds.any fun d => d.code == "N0023" && hasStr d.message "this diagram is drawn by")
    t s!"the diagram is a fallback the driver may withdraw: {form}"
      (rs.fallbacks == refs.map (·.1))
    let img := (picImages doc).getD 0 ""
    let store : Image.Store :=
      { entries := #[{ src := img, info := some ({ pxW := 240, pxH := 120 } : Image.Plan) }] }
    let page := shipped doc store
    t s!"the page ships the boundary's box and none of the diagram's source: {form}"
      ((page[0]?.map fun p => p.images == 1) == some true &&
       !hasStr (censusText page) "Alpha" && !hasStr (censusText page) "tikzcd" &&
       !hasStr (censusText page) "arrow")
    t s!"the HTML display holds the request's image: {form}"
      (displayImgs doc == 1)
  let bracket := "\\[" ++ cdLossy ++ "\\]"
  let (closed, closedDs) := elabStr (dvDoc ("\\pictures{ tool = none }\n" ++ pre) bracket)
  t "with the boundary refused, the diagram draws natively, its loss named"
    (closed.pictureSrcs.isEmpty && closedDs.any (·.code == "W0334") &&
     closedDs.all (·.code != "W0012") && hasStr (censusText (shipped closed)) "Alpha" &&
     ((shipped closed)[0]?.map (·.images == 0)) == some true)
  let (withdrawn, withdrawnDs) := elabStr (dvDoc pre bracket)
  t "a diagram no tool drew is withdrawn to the same native drawing, named"
    (withdrawn.pictureSrcs.isEmpty && withdrawnDs.any (·.code == "W0334") &&
     hasStr (censusText (shipped withdrawn)) "Alpha")
  let (mixed, mixedDs, _) := firstPass (dvDoc pre ("\\[ x + " ++ cdDiagram ++ "\\]"))
  t "a diagram beside other mathematics stays the formula's floor, named"
    ((Ir.pictureRefs mixed).isEmpty && mixedDs.any (·.code == "W0012"))
  -- A numbered alignment owes its number, so it keeps the formula's door.
  let (numbered, numberedDs, _) := firstPass (dvDoc pre
    ("\\begin{align}" ++ cdDiagram ++ "\\end{align}"))
  t "a numbered alignment's diagram keeps the formula's door, named"
    ((Ir.pictureRefs numbered).isEmpty && numberedDs.any (·.code == "W0012"))

/-- A boundary standalone compiles what its document compiled, at the size its picture stands at. -/
def boundaryFidelityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let firstPass (src : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let (toks, lds) := Lex.lex "t" src
    let (raws, pds) := Parse.parse "t" toks
    Elab.runRawsSpanned "t" raws (lds ++ pds)
  let reqOf (src : String) : String :=
    (((Ir.pictureRefs (firstPass src).1)[0]?).map (·.2)).getD ""
  let pre := "\\usepackage{amsmath}\n\\usepackage{tikz-cd}\n"
  let display (body : String) : String := "\\[" ++ body ++ "\\]"
  let ten := reqOf (dvDoc pre (display cdLossy))
  let eleven := reqOf ("\\documentclass[11pt]{article}\n" ++ pre ++
    "\\begin{document}\n" ++ display cdLossy ++ "\n\\end{document}")
  t "a ten-point document's standalone takes no size option"
    (hasStr ten "\\documentclass{standalone}\n\\usepackage{tikz}\n")
  t "an eleven-point document's standalone takes its body size"
    (hasStr eleven "\\documentclass[11pt]{standalone}")
  let largeSrc := dvDoc pre ("{\\large\n" ++ display cdLossy ++ "\n}")
  let large := reqOf largeSrc
  t "a diagram under a size switch is drawn at that size"
    (hasStr large "\\begin{document}\n\\large\n\\begin{tikzcd}")
  t "one diagram at two sizes is two requests"
    (((firstPass largeSrc).1.pictureSrcs.map (·.1)) !=
      ((firstPass (dvDoc pre (display cdLossy))).1.pictureSrcs.map (·.1)))
  t "a body size the class holds no option for is set by its own switch"
    (Ir.pictureSwitch { fontSize := Dim.pt 9 } none ==
      some s!"\\fontsize\{{(Dim.pt 9).toPtString}pt}\{{(Ir.leadingFor (Dim.pt 9)).toPtString}pt}\\selectfont")
  let ops := reqOf (dvDoc (pre ++ "\\DeclareMathOperator{\\gradient}{grad}\n" ++
      "\\newlength{\\thumbside}\\setlength{\\thumbside}{.5in}\n")
    (display "\\begin{tikzcd} A \\arrow[r, \"\\gradient\", hook] & \\parbox{\\thumbside}{B} \\end{tikzcd}"))
  t "an operator the document declared is the standalone's"
    (hasStr ops "\\renewcommand{\\gradient}{\\operatorname{grad}}")
  t "a length the document declared and set is the standalone's, guarded"
    (hasStr ops "\\ifdefined\\thumbside\\else\\newlength{\\thumbside}\\fi\\setlength{\\thumbside}{.5in}")
  let alerted := reqOf ("\\documentclass{beamer}\n" ++ pre ++ "\\begin{document}\n\\begin{frame}\n" ++
    display "\\begin{tikzcd} A \\arrow[r, hook] & \\alert{B} \\end{tikzcd}" ++ "\n\\end{frame}\n\\end{document}")
  t "an alerting slides diagram carries the alert and its colour"
    (hasStr alerted "\\RenewDocumentCommand{\\alert}{d<>m}" && hasStr alerted "\\definecolor{alert}")
  t "an article's standalone carries no alert of beamer's"
    (!hasStr ten "\\alert")
  let inputs := Ir.pictureInputs ("\\includegraphics [keepaspectratio,width=\\thumbside ]" ++
    "{figures/thumb.png}\\includegraphics{plain}\\includegraphicsx{other}" ++
    "\\includegraphics*{figures/thumb.png}\\newcommand\\pic[1]{\\includegraphics{#1}}")
  t "a request's inputs are its \\includegraphics files, once each"
    (inputs == #["figures/thumb.png", "plain"])
