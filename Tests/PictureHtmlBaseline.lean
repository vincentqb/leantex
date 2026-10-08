module

public import Tests.Support

public section

open LeanTex.Core

/-- SVG label baselines and native page baselines project the same measured
IR band, for every alignment, face and size. Browser baseline keywords
previously guessed a second band and put the letters at different heights.
The guards read emitted SVG attributes and `Layout.Out`, including source
nodes split into lines and nodes with a declared text box. Invented content. -/
def pictureHtmlBaselineChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let mut faces := #[("sans", oneFace)]
  match ← serifFacesSet with
  | some fs => faces := faces.push ("serif", fs)
  | none => t "picture baseline: the shipped serif faces load" false
  let alignments : Array (String × Ir.Pic.LabelAlign × String) := #[
    ("center", .center, "middle"), ("west", .west, "start"),
    ("east", .east, "end"), ("south", .south, "middle"), ("north", .north, "middle")]
  let contents : Array (String × Array Ir.Inline) := #[
    ("capitals", #[.text "WAX"]),
    ("descenders", #[.text "gjpqy"]),
    ("bold", #[.styled .bold #[.text "Amber"]]),
    ("italic", #[.styled .italic #[.text "gypsy"]])]
  let geom : Layout.Geom := {}
  for (face, fs) in faces do
    let metric := Layout.labelMetric geom fs
    let cfg : HtmlDoc.Config := { labelMetric := metric }
    for (side, align, anchor) in alignments do
      for scale in #[650, 1000, 1750] do
        for (word, content) in contents do
          for declared in #[none, some ((Dim.pt (-9), Dim.pt (-17)), (Dim.pt 75, Dim.pt 31))] do
            let x := Dim.pt 14
            let y := Dim.pt 11
            let pic : Ir.Pic.Picture := {
              shapes := #[.label x y content Ir.Color.black scale align]
              declared := declared }
            let doc : Ir.Doc := {
              body := #[.picture pic]
              tokens := ({} : Ir.Tokens).declare "topskip" {} }
            let lines := bodyLines (layoutOf fs doc geom)
            let labels := elemAttrsOne (· == "text") #[] (HtmlDoc.pictureSvg cfg pic)
            let name := s!"picture baseline: {face}/{side}/{scale}/{word}/{declared.isSome}"
            t (name ++ " ships one label in each artifact")
              (lines.size == 1 && labels.size == 1)
            let expected := (pic.box metric).2.2 - Ir.Pic.labelBaseline y align (metric content scale)
            t (name ++ " native baseline is the shared IR baseline")
              ((lines[0]?.map (·.y - geom.vmargin)) == some expected)
            t (name ++ " SVG baseline agrees with the native page")
              ((labels[0]?.bind fun (_, attrs) => HtmlDoc.attrOf? attrs "y")
                == (lines[0]?.map fun l => (l.y - geom.vmargin).toPtString))
            t (name ++ " SVG uses an alphabetic baseline")
              ((labels[0]?.bind fun (_, attrs) => HtmlDoc.attrOf? attrs "dominant-baseline")
                == some "alphabetic")
            t (name ++ " retains horizontal anchoring")
              ((labels[0]?.bind fun (_, attrs) => HtmlDoc.attrOf? attrs "text-anchor") == some anchor)
    -- A source node's lines and declared text height/depth have already
    -- been seated by Picture. HTML must preserve every resulting baseline,
    -- including under transform shape, with the driver's same metric.
    for opts in #["", "font=\\bfseries", "font=\\itshape",
        "text height=2ex,text depth=0.5ex"] do
      for alignment in #["center", "left", "right"] do
        for scale in #["1", "1.5"] do
          let src := "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
            "\\begin{tikzpicture}[scale=" ++ scale ++ ",transform shape]\n" ++
            "\\node[align=" ++ alignment ++ (if opts.isEmpty then "" else "," ++ opts) ++
            "] at (0,0) {Amber\\\\gypsy};\n\\end{tikzpicture}\n\\end{document}"
          let (doc, ds) := elabMeasured fs src
          let doc := { doc with tokens := doc.tokens.declare "topskip" {} }
          let g := Layout.Geom.ofPage doc.page
          let cfg : HtmlDoc.Config := { labelMetric := Layout.labelMetric g fs }
          let lines := bodyLines (layoutOf fs doc)
          let labels := elemAttrsList (· == "text") #[]
            (HtmlDoc.emitTree cfg doc).2.1.toList
          let name := s!"picture baseline: source/{face}/{alignment}/{scale}/{opts}"
          t (name ++ " ships both lines without picture losses")
            (lines.size == 2 && labels.size == 2 &&
              !ds.any fun d => ["W0334", "E0333", "W0335"].contains d.code)
          t (name ++ " preserves the source text")
            (lines.map lineText == #["Amber", "gypsy"])
          t (name ++ " SVG lines agree with native page baselines")
            (labels.map (fun (_, attrs) => HtmlDoc.attrOf? attrs "y")
              == lines.map (fun l => some (l.y - g.vmargin).toPtString))
          t (name ++ " SVG lines use alphabetic baselines")
            (labels.all fun (_, attrs) =>
              HtmlDoc.attrOf? attrs "dominant-baseline" == some "alphabetic")
  -- With no font environment the existing zero metric declares no band.
  -- Keep the source anchor exactly, without asking a browser to guess a
  -- different band; measured callers above supply the driver contract.
  for (side, align, _) in alignments do
    let pic : Ir.Pic.Picture := {
      shapes := #[.label (Dim.pt 7) (Dim.pt 3) #[.text "Amber"] Ir.Color.black 1000 align]
      declared := some ((0, 0), (Dim.pt 20, Dim.pt 10)) }
    let labels := elemAttrsOne (· == "text") #[] (HtmlDoc.pictureSvg {} pic)
    t s!"picture baseline: no-font/{side} preserves the anchor"
      ((labels[0]?.bind fun (_, attrs) => HtmlDoc.attrOf? attrs "y")
        == some (Dim.pt 7).toPtString)
    t s!"picture baseline: no-font/{side} uses the declared alphabetic baseline"
      ((labels[0]?.bind fun (_, attrs) => HtmlDoc.attrOf? attrs "dominant-baseline")
        == some "alphabetic")
