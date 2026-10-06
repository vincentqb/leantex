import Tests.Support

open LeanTex.Core

namespace PictureMathLabels

/-- Invented labels exercise empty nuclei as well as ordinary mathematical
structure. The expected leaves are painted characters, not a linear reading
of the formula: a superscript contributes no parentheses or caret. -/
def mathLabelCases : Array (String × String × String) := #[
  ("Maple$'$", "Maple′", "msup"),
  ("Birch$''$", "Birch′′", "msup"),
  ("Cedar$_r$", "Cedarr", "msub"),
  ("Elm$^{2}$", "Elm2", "msup"),
  ("Ash$\\frac{3}{7}$", "Ash37", "mfrac"),
  ("Pine$\\sqrt{z}$", "Pinez", "msqrt")]

def mathLabelSource (label opts : String) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "\\begin{tikzpicture}\n\\node[" ++ opts ++ "] at (-1,1) {" ++ label ++
  "};\n\\end{tikzpicture}\n\\end{document}"

def pictures (doc : Ir.Doc) : Array Ir.Pic.Picture :=
  Ir.foldBlocks (fun acc b => match b with
    | .picture p => acc.push p
    | _ => acc) (fun acc _ => acc) #[] doc.body

end PictureMathLabels

/-- **Parsed picture mathematics keeps its structure on the shipped page.**
The native page must retain and raise an orphan script after text. The
typed HTML must paint the same letters and a native script, fraction or
radical, without introducing the punctuation of a plaintext serialization.
The label retains the shared measured baseline, every horizontal anchor,
and visible overflow. This guard fails on the structural-text SVG fallback.
It reads `Layout.Out` and the emitted HTML tree, never an IR dump.
Invented content throughout. -/
def pictureMathLabelChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let attr := fun (node : Html.Node) (key : String) =>
    match node with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs key
    | _ => none
  let fs ← mathSetOf oneFace
  t "picture mathematics: the bundled math face loads" fs.math.isSome
  for (label, leaves, schema) in PictureMathLabels.mathLabelCases do
    let (base, ds) := elabMeasured fs (PictureMathLabels.mathLabelSource label "")
    let pics := PictureMathLabels.pictures base
    t s!"picture mathematics: {label} parses one picture without loss"
      (pics.size == 1 &&
        !ds.any fun d => ["W0012", "W0334", "E0333", "W0335"].contains d.code)
    let some original := pics[0]? | continue
    for (side, align) in #[("center", Ir.Pic.LabelAlign.center), ("west", .west),
        ("east", .east), ("north", .north), ("south", .south)] do
      for scale in #[700, 1000, 1600] do
        let pic := { original with shapes := original.shapes.map fun shape =>
          match shape with
          | .label x y content color _ _ => .label x y content color scale align
          | _ => shape }
        let doc := { base with
          body := #[.picture pic], tokens := base.tokens.declare "topskip" {} }
        let geom := Layout.Geom.ofPage doc.page
        let out := layoutOf fs doc
        let cfg : HtmlDoc.Config := {
          fonts := some fs, page := doc.page, labelMetric := Layout.labelMetric geom fs }
        let svgs := #[HtmlDoc.pictureSvg cfg pic]
        let name := s!"picture mathematics: {label}/{side}/{scale}"
        t (name ++ " ships one native label") ((bodyLines out).size == 1)
        for svg in svgs do
          t (name ++ " paints exactly the mathematical leaves")
            (String.ofList (MathMl.nodeChars #[] svg).toList == leaves)
          t (name ++ " preserves its native mathematical schema")
            (!(elemNodesOne (· == schema) #[] svg).isEmpty)
          t (name ++ " never clips the label")
            (attr svg "overflow" == some "visible")
        -- Layout's first run must keep the leading letter. For scripts,
        -- measure the emitted glyphs, not a source spelling or a box guess.
        let glyphs := shippedBodyGlyphs out
        t (name ++ " keeps its first native letter")
          ((glyphs[0]?.map (·.scalar)) == leaves.toList.head?)
        if schema == "msup" then
          let primes := glyphs.filter fun g => g.scalar == '′' || g.scalar == '2'
          let first := glyphs[0]?
          t (name ++ " ships an elevated native superscript")
            (!primes.isEmpty && primes.all fun g =>
              first.any fun f => g.y < f.y && g.size < f.size)
        for shape in pic.shapes do
          match shape with
          | .label x y content color size align =>
            let metric := Layout.labelMetric geom fs
            let emitted := HtmlDoc.pictureKids pic (pic.box metric).1.1
              (pic.box metric).2.2 metric
            let baselines := emitted.filterMap fun n =>
              attr n "y"
            let baseline := (pic.box metric).2.2 -
              Ir.Pic.labelBaseline y align (metric content size)
            t (name ++ " retains the shared alphabetic baseline")
              (baselines.contains baseline.toPtString &&
                (bodyLines out)[0]?.any fun l => l.y - geom.vmargin == baseline)
            -- Give the label a box narrower than its ink: both artifacts
            -- must still retain the whole leading word.
            let small : Ir.Pic.Picture := {
              shapes := #[.label x y content color size align]
              declared := some ((0, 0), (Dim.pt 1, Dim.pt 1)) }
            let narrow := HtmlDoc.pictureSvg cfg small
            t (name ++ " retains ink outside a declared box")
              (attr narrow "overflow" == some "visible" &&
                String.ofList (MathMl.nodeChars #[] narrow).toList == leaves)
          | _ => pure ()
  -- Styling may surround both text and math. The script still owns its
  -- mathematical structure under face resets, nested emphasis and colour.
  for label in #["\\textbf{Maple$'$}", "\\textit{\\emph{Maple}$'$}",
      "\\textbf{\\textnormal{Maple}$'$}", "\\textcolor{red}{Maple$'$}"] do
    let (doc, _) := elabMeasured fs (PictureMathLabels.mathLabelSource label "")
    let cfg : HtmlDoc.Config := {
      fonts := some fs, labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs }
    let svgs := elemNodesList (· == "svg") #[] (HtmlDoc.emitTree cfg doc).2.1.toList
    t s!"picture mathematics: styled label {label} preserves text and the script"
      (svgs.size == 1 && svgs.all fun svg =>
        String.ofList (MathMl.nodeChars #[] svg).toList == "Maple′" &&
          !(elemNodesOne (· == "msup") #[] svg).isEmpty)
