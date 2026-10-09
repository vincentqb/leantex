module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

/-- An invented three-object diagram in tikz-cd's own syntax, both arrow
spellings: the bracket form with a quoted label, and the brace form with a
direction group and a label group. -/
def cdDiagram : String :=
  "\\begin{tikzcd} Alpha \\arrow[r, \"f\"] & Beta \\arrow{d}{g} \\\\ & Gamma \\end{tikzcd}"

/-- The three displays a diagram stands alone in: `\[…\]`, `equation*`, and an
unnumbered alignment — every one the reference talks wrote one in. -/
def cdDisplays : List (String × String) :=
  [("a bracket display", "\\[" ++ cdDiagram ++ "\\]"),
   ("equation*", "\\begin{equation*}" ++ cdDiagram ++ "\\end{equation*}"),
   ("align*", "\\begin{align*}" ++ cdDiagram ++ "\\end{align*}")]

/-- **A commutative diagram standing alone in a display ships a picture.**
The invariant whose absence set every diagram of the reference talks as
its own source text under W0012: a `tikzcd` is TikZ ink set as display
mathematics, so the boundary draws it — one request of the diagram's own
kind, its standalone opening `tikzcd` outside any `tikzpicture` — and the
display ships the boundary's box with no text floor, on the PDF page and
in the HTML display alike. Where no tool draws it, or the document refused
the boundary, the display keeps the floor it had, named: a diagram is never
a placeholder. A diagram beside other mathematics stays the formula's. The
page claims read `Layout.Out` and the typed HTML tree; invented content. -/
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
  for (form, body) in cdDisplays do
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
       ds.any (·.code == "N0023"))
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
  -- Every other door keeps the floor and names it, never a placeholder.
  let bracket := "\\[" ++ cdDiagram ++ "\\]"
  let (closed, closedDs) := elabStr (dvDoc ("\\pictures{ tool = none }\n" ++ pre) bracket)
  t "with the boundary refused, the diagram keeps its text floor, named"
    (closed.pictureSrcs.isEmpty && closedDs.any (·.code == "W0012") &&
     hasStr (censusText (shipped closed)) "Alpha" &&
     ((shipped closed)[0]?.map (·.images == 0)) == some true)
  let (withdrawn, withdrawnDs) := elabStr (dvDoc pre bracket)
  t "a diagram no tool drew is withdrawn to the same floor, named"
    (withdrawn.pictureSrcs.isEmpty && withdrawnDs.any (·.code == "W0012") &&
     hasStr (censusText (shipped withdrawn)) "Alpha")
  let (mixed, mixedDs, _) := firstPass (dvDoc pre ("\\[ x + " ++ cdDiagram ++ "\\]"))
  t "a diagram beside other mathematics stays the formula's floor, named"
    ((Ir.pictureRefs mixed).isEmpty && mixedDs.any (·.code == "W0012"))
  -- A numbered alignment owes its number, so it keeps the formula's door,
  -- named as the formula's floor is.
  let (numbered, numberedDs, _) := firstPass (dvDoc pre
    ("\\begin{align}" ++ cdDiagram ++ "\\end{align}"))
  t "a numbered alignment's diagram keeps the formula's door, named"
    ((Ir.pictureRefs numbered).isEmpty && numberedDs.any (·.code == "W0012"))
