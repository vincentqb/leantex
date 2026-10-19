module

public import Tests.Artifact
public import Tests.PictureKeys
public import Tests.Backends

public section

open LeanTex.Core

namespace Tests.GfxRegression

/-- The lines of a page's typed stream. -/
def streamLines (oneFace : Font.FontSet) (doc : Ir.Doc) (out : Layout.Out) : Array String :=
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let geom := Layout.Geom.ofPage doc.page
  ((Pdf.pageOps geom oneFace out.pages {} tree)[0]?.map fun ops =>
    ((Pdf.render ops).splitOn "\n").toArray).getD #[]

/-- The stroked SVG paths of a document's pictures, as their attributes. -/
def strokedPaths (doc : Ir.Doc) : Array (Array (String × String)) :=
  (elemAttrsList (· == "path") #[] (doc.body.toList.map (HtmlDoc.blockNode {}))).filterMap
    fun (_, attrs) =>
      if attrs.any (fun (k, v) => k == "stroke" && v != "none") then some attrs else none

def attr? (attrs : Array (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- A step read back from an artifact, as ink or a label. -/
def stepKind {α : Type} : Gfx.Step α → String
  | .mark _ => "ink"
  | .label _ => "label"

/-- Whether the first list is the second with some elements left out. -/
def subseq : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then subseq as bs else subseq (a :: as) bs

end Tests.GfxRegression

open Tests.GfxRegression in
/-- A placed picture's ink is its page's content: a page holding only a picture ships, what follows
stands below or on the next page, and the page's vertical distribution moves it as a rule of its
size. -/
def gfxContentPageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let draws (out : Layout.Out) (i : Nat) : Nat := ((out.pages[i]?.map pageDraws).map (·.size)).getD 0
  let fills := "\\fill[red] (0,0) rectangle (3,2);\n\\fill[blue] (4,0) rectangle (5,1);"
  let strokes := "\\draw[red, line width=2pt] (0,0) -- (3,2);"
  let article (body : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let pic := tikzPicture
  let deck (body : String) : String :=
    "\\documentclass{beamer}\\pictures{ tool = none }\\begin{document}\n" ++
    "\\begin{frame}{Opening}\nOpening slide text.\n\\end{frame}\n" ++
    "\\begin{frame}\n" ++ pic body ++ "\n\\end{frame}\n" ++
    "\\begin{frame}{Closing}\nClosing slide text.\n\\end{frame}\n\\end{document}"
  for (kind, body, marks) in [("fills", fills, 2), ("strokes", strokes, 1)] do
    let last := layoutOf oneFace (elabStr (article ("An opening paragraph.\n\\newpage\n" ++ pic body))).1
    t s!"a picture of {kind} alone is the document's last page"
      (last.pages.size == 2 && draws last 0 == 0 && draws last 1 == marks)
    let middle := layoutOf oneFace (elabStr (article ("An opening paragraph.\n\\newpage\n" ++ pic body ++
      "\n\\newpage\nA closing paragraph."))).1
    t s!"a picture of {kind} alone between two page breaks is a page of its own"
      (middle.pages.size == 3 && draws middle 0 == 0 && draws middle 1 == marks && draws middle 2 == 0)
    let frames := layoutOf oneFace (elabStr (deck body)).1
    t s!"a frame holding a picture of {kind} alone is a page of its own"
      (frames.pages.size == 3 && draws frames 1 == marks && draws frames 2 == 0)
  let bottomOf (out : Layout.Out) (i : Nat) : Option Dim.Length := do
    let ds := (← out.pages[0]?).inks.flatMap fun k =>
      (pageDraws { inks := #[k] }).map fun (g, _, _) => markExtent g
    let (_, y, _, h) ← ds[i]?
    return y + h
  let after := layoutOf oneFace (elabStr (article (pic fills ++ "\n\nA paragraph after it."))).1
  t "a paragraph after a picture of fills at a page's top stands below it"
    (match bottomOf after 0, after.pages[0]?.bind fun p => (p.lines.filter (!·.furniture))[0]? with
     | some bottom, some l => after.pages.size == 1 && bottom < l.y
     | _, _ => false)
  let twice := layoutOf oneFace
    (elabStr (article (pic "\\fill[red] (0,0) rectangle (3,2);" ++ "\n\n" ++
      pic "\\fill[blue] (0,0) rectangle (3,2);"))).1
  let tops := ((twice.pages[0]?.map pageDraws).getD #[]).map fun (g, _, _) => (markExtent g).2.1
  t "a second picture after a picture of fills stands below it"
    (match bottomOf twice 0, tops[1]? with
     | some bottom, some top => twice.pages.size == 1 && bottom ≤ top
     | _, _ => false)
  let lay (src : String) : Layout.Out := layoutOf oneFace (elabStr src).1
  let picTops (out : Layout.Out) (page : Nat) : Array Dim.Length :=
    ((out.pages[page]?.map pageDraws).getD #[]).map fun (g, _, _) => (markExtent g).2.1
  let ruleTops (out : Layout.Out) (page : Nat) : Array Dim.Length :=
    ((out.pages[page]?.map fun p => p.lines.filter (!·.furniture)).getD #[]).map fun l =>
      l.y - (Layout.segsInk oneFace l.segs).1
  -- pgf's cm (28.45274pt) and TeX's (7227/254pt) differ by 0.56 ppm, about 30sp across a page.
  let near (a b : Array Dim.Length) : Bool :=
    a.size == b.size && (a.zip b).all fun (x, y) => (x - y).abs ≤ 64 * Dim.Length.quantum
  let rule := "\\noindent\\rule{3cm}{2cm}"
  let box := pic "\\fill[red] (0,0) rectangle (3,2);"
  let frameSrc (opt body : String) : String :=
    "\\documentclass{beamer}\\pictures{ tool = none }\\begin{document}\n\\begin{frame}" ++ opt ++
      "\n" ++ body ++ "\n\\end{frame}\n\\end{document}"
  let centred := lay (frameSrc "" box)
  t "a frame holding only a picture centres it where it centres a rule of its size"
    (near (picTops centred 0) (ruleTops (lay (frameSrc "" rule)) 0) &&
      picTops centred 0 != picTops (lay (frameSrc "[t]" box)) 0)
  let sandwich (body : String) : String := article ("\\vspace*{\\fill}\n" ++ body ++ "\n\\vspace*{\\fill}")
  t "fil glue around a picture alone on its page moves it as it moves a rule of its size"
    (near (picTops (lay (sandwich ("\\noindent" ++ box))) 0) (ruleTops (lay (sandwich rule)) 0))
  let flush (body : String) : String :=
    "\\documentclass{article}\\pictures{ tool = none }\\page{ bottom = flush }\\begin{document}\n" ++
      "\n\n\\vspace{0pt plus 80pt}\n".intercalate [body, body, body] ++ "\n\\end{document}"
  t "a flush bottom sets a page of pictures as it sets a page of rules of their size"
    (near (picTops (lay (flush ("\\noindent" ++ pic "\\fill[red] (0,0) rectangle (3,8);"))) 0)
      (ruleTops (lay (flush "\\noindent\\rule{3cm}{8cm}")) 0))
  let crowded := lay (article (pic "\\fill[red] (0,0) rectangle (3,22.6);" ++
    "\n\nA paragraph after a picture that leaves it no room on the page."))
  t "a paragraph a picture leaves no room for opens the next page"
    (crowded.pages.size == 2 && draws crowded 0 == 1 &&
      ((crowded.pages[0]?.map fun p => (p.lines.filter (!·.furniture)).isEmpty).getD false) &&
      ((crowded.pages[1]?.map fun p => !(p.lines.filter (!·.furniture)).isEmpty).getD false))
  let tall := layoutOf oneFace (elabStr (article (pic "\\fill[red] (0,0) rectangle (3,14);" ++
    "\n\n\\begin{figure}[h]\n" ++ pic "\\fill[blue] (0,0) rectangle (3,9);" ++
    "\n\\caption{An invented figure.}\n\\end{figure}"))).1
  t "a float after a picture-only page that it cannot share opens a page of its own"
    (tall.pages.size == 2 && draws tall 0 == 1 && draws tall 1 == 1 &&
      !tall.diags.any (·.code == "W0358"))

open Tests.GfxRegression in
/-- Pictures agree across backends over the page's typed stream, `Layout.Out` and the typed HTML
tree: fill order, subpaths, zero widths, miter limits, zero-size and dashed shapes, and
square-capped dots. -/
def gfxDefectChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let red : Ir.Color := { r := 255, g := 0, b := 0 }
  let (doc1, ds1) := elabStr (picDoc "" ""
    "\\draw (-1,-1) -- (1,1);\n\\fill[red] (-0.5,-0.5) rectangle (0.5,0.5);")
  let out1 := layoutOf oneFace doc1
  t "F1: a picture's rectangle fill is no page fill"
    (ds1.all (·.code != "W0334") && out1.pages.size == 1 &&
      out1.pages.all fun p => p.fills.all fun f => !(f.color == red))
  let ls := streamLines oneFace doc1 out1
  let fig := ls.findIdx? (fun l => l.startsWith "/Figure << /MCID")
  let circle := ls.findIdx? (fun l => l.endsWith " l S Q")
  let fillAt := ls.findIdx? (fun l => hasStr l (red.pdfFill ++ " ") && l.endsWith " re f Q")
  t "F1: the rectangle fill paints in source order inside its picture's Figure sequence"
    (match fig, circle, fillAt with
     | some f, some c, some r =>
       f < c && c < r && ((ls.extract (f + 1) r).all fun l => l != "EMC")
     | _, _, _ => false)
  -- A footer band never splits a picture: fill and stroke stand on one side, in one sequence.
  let ground : Ir.Color := { r := 0xE8, g := 0xED, b := 0xF3 }
  let (docF, _) := elabStr ("\\documentclass{beamer}\\usetheme{moloch}\\pictures{ tool = none }" ++
    "\\definecolor{FootGround}{HTML}{E8EDF3}\\setbeamercolor{footline}{bg=FootGround}" ++
    "\\begin{document}\\begin{frame}{Picture}\n\\begin{tikzpicture}\n" ++
    "\\fill[red] (0,0) rectangle (1,1);\n\\draw (0,0) -- (1,1);\n" ++
    "\\end{tikzpicture}\n\\end{frame}\\end{document}")
  let outF := layoutOf oneFace docF
  let lsF := streamLines oneFace docF outF
  -- The band keeps the exact rider `\definecolor` declared, read off the shipped fill.
  let band := (outF.pages[0]?.bind fun p => p.fills.find? (·.color == ground)).map (·.color.pdfFill)
  let bandAt := band.bind fun b => lsF.findIdx? fun l => hasStr l (b ++ " ") && l.endsWith " re f Q"
  let figAt := lsF.findIdx? fun l => l.startsWith "/Figure << /MCID"
  let fillAtF := lsF.findIdx? fun l => hasStr l (red.pdfFill ++ " ") && l.endsWith " re f Q"
  let strokeAtF := lsF.findIdx? fun l => l.endsWith " l S Q"
  t "F1: a footer band never splits a picture's fill from its stroke"
    (match bandAt, figAt, fillAtF, strokeAtF with
     | some b, some f, some r, some k =>
       f < r && r < k && ((lsF.extract (f + 1) k).all fun l => l != "EMC") &&
         ((b < r && b < k) || (r < b && k < b))
     | _, _, _, _ => false)
  let (doc2, _) := elabStr (picDoc "" "" "\\draw (0,0) -- (1,0) -- (1,1);")
  t "F2: a continuing segment chain is one SVG subpath"
    (match (strokedPaths doc2).toList with
     | [attrs] => ((attr? attrs "d").map fun d => (d.splitOn "M").length == 2).getD false
     | _ => false)
  let ls2 := streamLines oneFace doc2 (layoutOf oneFace doc2)
  t "F2: and one PDF subpath"
    ((ls2.filter fun l => l.endsWith " S Q").all fun l => (l.splitOn " m ").length == 2)
  let (doc3, _) := elabStr (picDoc "" "" "\\draw[line width=0pt] (0,0) -- (1,0);")
  t "F3: a 0pt line width draws the SVG hairline"
    (match (strokedPaths doc3).toList with
     | [attrs] => attr? attrs "stroke-width" == some "1" &&
         attr? attrs "vector-effect" == some "non-scaling-stroke"
     | _ => false)
  t "F3: and the PDF's thinnest line"
    ((streamLines oneFace doc3 (layoutOf oneFace doc3)).any (hasStr · " 0 w "))
  let (doc4, _) := elabStr (picDoc "" ""
    "\\draw (0,0) -- (1,0) -- (1,1);\n\\node[draw] at (3,0) {Box};\n\\node[draw,circle] at (5,0) {O};")
  let stroked := elemAttrsList (fun tag => tag == "path" || tag == "rect" || tag == "circle") #[]
    (doc4.body.toList.map (HtmlDoc.blockNode {}))
  let strokes := stroked.filter fun (_, attrs) => attrs.any fun (k, v) => k == "stroke" && v != "none"
  t "F4: HTML TikZ strokes carry stroke-miterlimit 10"
    (strokes.size == 3 && strokes.all fun (_, attrs) => attr? attrs "stroke-miterlimit" == some "10")
  -- Zero-size and dashed rectangles and circles spell as the path the PDF strokes.
  let shapes (doc : Ir.Doc) : Array (String × Array (String × String)) :=
    (elemAttrsList (fun tag => tag == "path" || tag == "rect" || tag == "circle" || tag == "ellipse") #[]
      (doc.body.toList.map (HtmlDoc.blockNode {}))).filter fun (_, attrs) =>
        attrs.any fun (k, v) => k == "stroke" && v != "none"
  let (docZ, _) := elabStr (picDoc "" "" "\\draw (0,0) rectangle (2,0);\n\\draw (3,0) rectangle (3,1);")
  t s!"zero-size: a stroked rectangle of zero height or width spells the path the PDF strokes ({shapes docZ})"
    ((shapes docZ).size == 2 && (shapes docZ).all fun (tag, attrs) =>
      tag == "path" && ((attr? attrs "d").map fun d => (d.splitOn "L").length == 4).getD false)
  let lsZ := streamLines oneFace docZ (layoutOf oneFace docZ)
  t "zero-size: and the PDF strokes each as its `re`"
    ((lsZ.filter fun l => l.endsWith " re S Q").size == 2)
  let numbers (d : String) : Array Int := (d.splitOn " ").toArray.filterMap fun w =>
    (w.replace "," "").toInt?.orElse fun _ =>
      ((w.replace "," "").splitOn ".")[0]?.bind (·.toInt?)
  let (docD, _) := elabStr (picDoc "" "" "\\draw[dashed] (0,0) rectangle (2,1);")
  t s!"dashed: a dashed rectangle's dashes start where the PDF's do, at its min corner along x ({shapes docD})"
    (match (shapes docD).toList with
     | [("path", attrs)] =>
       match (attr? attrs "d").map numbers with
       | some ns =>
         -- The bottom edge first: SVG's y grows down, so the min corner's y is the largest.
         ns.size ≥ 8 && ns[1]? == ns[3]? && (ns[0]?.getD 0) < (ns[2]?.getD 0) &&
           (ns[5]?.getD 0) < (ns[1]?.getD 0)
       | none => false
     | _ => false)
  let (docC, _) := elabStr (picDoc "" "" "\\node[draw,dashed,circle,minimum size=1cm] at (0,0) {};")
  t s!"dashed: a dashed circle runs counter-clockwise from angle 0, as the PDF's does ({shapes docC})"
    (match (shapes docC).toList with
     | [("path", attrs)] =>
       match (attr? attrs "d").map numbers with
       | some ns => ns.size ≥ 8 && (ns[7]?.getD 0) < (ns[1]?.getD 0)
       | none => false
     | _ => false)
  -- A square-capped dot: PDF paints nothing (ISO 32000-2 §8.5.3.2), SVG a square.
  let dotted : Gfx.Figure Empty :=
    { box := ((0, 0), (Dim.bp 10, Dim.bp 10)), clipToBox := false, outlines := #[], symbols := #[]
      rasters := #[], title := none, losses := #[]
      nodes := #[.draw (.path #[{ start := (Dim.bp 2, Dim.bp 2), segs := #[.line (Dim.bp 2, Dim.bp 2)], closed := false },
          { start := (Dim.bp 4, Dim.bp 4), segs := #[.line (Dim.bp 8, Dim.bp 4)], closed := false }]) none
        (some { paint := .solid red, width := Dim.bp 1, cap := .square, join := .miter, miterLimit := 10
                dash := #[], phase := 0, alpha := Gfx.Alpha.opaque })] }
  let dotSvg := GfxSvg.document (fun _ (e : Empty) => nomatch e) #[] dotted
  t s!"dots: a square-capped dot is left out of the SVG path, which keeps the segment beside it"
    (!hasStr dotSvg "M 2 8 L 2 8" && hasStr dotSvg "M 4 6 L 8 6")
  -- The standalone mode ships the inline SVG's box and marks as a file.
  match doc4.body.toList.filterMap (fun b => match b with | .picture p => some p | _ => none) with
  | [pic] =>
    let viewBox := match HtmlDoc.pictureSvg {} pic with
      | .elem _ attrs _ => attr? attrs "viewBox"
      | _ => none
    let file := HtmlDoc.pictureDocument {} pic
    t "a picture ships as a standalone SVG file with its inline box"
      (file.startsWith "<?xml" && viewBox.any fun v => hasStr file s!"viewBox=\"{v}\"")
  | _ => t "a picture ships as a standalone SVG file with its inline box" false

open Tests.GfxRegression in
/-- The HTML face of the `diagram-strokes` census row: the vector model's strokes on the fixture's
emitted page, read over the typed HTML tree. -/
def gfxStrokeCensusChecks (ref : IO.Ref (List String)) (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  match arts.find? (·.name == "diagram-strokes") with
  | none => t "gfx stroke census: the diagram-strokes fixture is built" false
  | some art =>
    let paths := strokedPaths art.doc
    let subpaths (attrs : Array (String × String)) : Nat × Nat :=
      ((attr? attrs "d").map fun d => ((d.splitOn "M").length - 1, (d.splitOn "L").length - 1)).getD (0, 0)
    t s!"gfx stroke census: three stroked paths ship ({paths.size})" (paths.size == 3)
    t "gfx stroke census: the chain ships as one subpath of two segments"
      ((paths[0]?.map fun a => subpaths a == (1, 2) && attr? a "stroke-dasharray" == none).getD false)
    t "gfx stroke census: the zero line width ships as the SVG hairline"
      ((paths[1]?.map fun a => attr? a "stroke-width" == some "1" &&
        attr? a "vector-effect" == some "non-scaling-stroke").getD false)
    t "gfx stroke census: the dashed chain ships as one dashed subpath of two segments"
      ((paths[2]?.map fun a => subpaths a == (1, 2) && (attr? a "stroke-dasharray").isSome).getD false)
    t "gfx stroke census: every stroke states pgf's miter limit"
      (paths.all fun a => attr? a "stroke-miterlimit" == some "10")

/-- Both artifacts read one picture's marks over the whole corpus, every picture with ink is placed,
and every shipped SVG stroke states pgf's miter limit. -/
def gfxAgreementChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let mut placed := 0
  let mut labelled := 0
  for art in arts do
    let metric := Layout.labelMetric art.geom oneFace art.store
    let pics := Ir.foldBlocks (fun (acc : Array Ir.Pic.Picture) b => match b with
      | .picture p => acc.push p
      | _ => acc) (fun acc _ => acc) #[] art.doc.body
    let svg := pics.filterMap fun pic =>
      let box := pic.box metric
      let ms := GfxSvg.readMarks (HtmlDoc.pictureIso box) (HtmlDoc.pictureTree pic box metric {})
      if ms.isEmpty then none else some ms
    let pdf := art.out.pages.flatMap fun p => p.inks.map fun k =>
      GfxPdf.readMarks ((Pdf.pageIso art.geom).compose k.place)
        (Pdf.inkPaint art.geom Pdf.figureNames (fun _ => none) k)
    placed := placed + pdf.size
    -- Every PDF picture sequence interleaves its labels with its ink as the SVG does.
    let svgSteps := pics.map fun pic =>
      let box := pic.box metric
      (GfxSvg.readSteps (HtmlDoc.pictureIso box) (HtmlDoc.pictureTree pic box metric {})).map
        Tests.GfxRegression.stepKind
    let tree := Struct.ofDoc (Layout.pdfView art.doc)
    -- A picture's sequence stands before the page's text object, an image's after it.
    let pdfSteps := ((Pdf.pageOps art.geom oneFace art.out.pages art.store tree).flatMap fun ops =>
      (ops.toList.takeWhile fun o => !(o matches .text _)).toArray.filterMap fun o => match o with
        | .marked (.content "Figure" _ _) body =>
          some ((GfxPdf.readSteps { flipY := true, dx := 0, dy := 0 } body).map
            Tests.GfxRegression.stepKind)
        | _ => none).filter (!·.isEmpty)
    -- A label the page set no line for paints nothing in the PDF, and nothing is reordered.
    check ref s!"gfx agreement {art.name}: every picture sequence sets its labels among its ink as its SVG does"
      (pdfSteps.all fun s => svgSteps.any fun v =>
        Tests.GfxRegression.subseq s.toList v.toList &&
          s.filter (· == "ink") == v.filter (· == "ink"))
    labelled := labelled + (pdfSteps.filter fun s => s.contains "label" && svgSteps.contains s).size
    let strokes := pics.flatMap fun pic =>
      (elemAttrsList (fun tag => tag == "path" || tag == "rect" || tag == "circle" || tag == "ellipse")
        #[] (HtmlDoc.pictureKids pic (pic.box metric) metric {}).toList).filter fun (_, attrs) =>
          attrs.any fun (k, v) => k == "stroke" && v != "none"
    check ref s!"gfx agreement {art.name}: every shipped picture stroke states pgf's miter limit"
      (strokes.all fun (_, attrs) => Tests.GfxRegression.attr? attrs "stroke-miterlimit" == some "10")
    check ref s!"gfx agreement {art.name}: every placed ink reads back as a picture's SVG marks"
      (pdf.all fun m => svg.contains m)
    check ref s!"gfx agreement {art.name}: every picture with ink is placed"
      (svg.all fun m => pdf.contains m)
  check ref s!"gfx agreement: the corpus placed picture ink ({placed} inks)" (placed > 0)
  check ref s!"gfx agreement: the corpus sets labels among picture ink as its SVG does ({labelled})"
    (labelled > 0)

open Tests.GfxRegression in
/-- A picture's labels paint in the order its statements wrote them, in the PDF as in the HTML. -/
def gfxLabelOrderChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let red : Ir.Color := { r := 255, g := 0, b := 0 }
  let (doc, _) := elabStr (picDoc "" ""
    "\\node at (0,0) {Under};\n\\fill[red] (-0.6,-0.2) rectangle (0.6,0.2);\n\\node at (0,1) {Over};")
  let out := layoutOf oneFace doc
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let geom := Layout.Geom.ofPage doc.page
  let ops := ((Pdf.pageOps geom oneFace out.pages {} tree)[0]?).getD #[]
  let figures := ops.filterMap fun o => match o with
    | .marked (.content "Figure" _ _) body => some body
    | _ => none
  t "label order: the PDF sets the picture's labels in its Figure sequence, on either side of the fill as written"
    (match figures.toList with
     | [body] => (GfxPdf.readSteps { flipY := true, dx := 0, dy := 0 } body).map stepKind ==
         #["label", "ink", "label"]
     | _ => false)
  -- Inside the one Figure sequence: a saved state around a text object, the red fill, another.
  let ls := streamLines oneFace doc out
  let fig := ls.findIdx? (fun l => l.startsWith "/Figure << /MCID")
  let fillAt := ls.findIdx? (fun l => hasStr l (red.pdfFill ++ " ") && l.endsWith " re f Q")
  let bts := (ls.zipIdx.filter (·.1 == "BT")).map (·.2)
  t "label order: the spelled stream paints the first label, the fill, then the second, in one sequence"
    (match fig, fillAt, bts.toList with
     | some f, some r, b1 :: b2 :: _ =>
       f < b1 && b1 < r && r < b2 && ls[b1 - 1]? == some "q" && ls[b2 - 1]? == some "q" &&
         ((ls.extract (f + 1) b2).all fun l => l != "EMC")
     | _, _, _ => false)
  t "label order: the stream's glyph census is the page's, in paint order, every run once"
    (match out.pages[0]? with
     | some p => Pdf.runsOf ops == Pdf.paintRuns p &&
         (Pdf.paintRuns p).length == (Pdf.pageRuns p).length &&
         ((Pdf.paintLines p).filterMap (·.pictureLabel.map (·.key))).take 2 == ["Under", "Over"]
     | none => false)
  match doc.body.toList.filterMap (fun b => match b with | .picture p => some p | _ => none) with
  | [pic] =>
    let box := HtmlDoc.pictureBoxOf {} pic
    let els := HtmlDoc.pictureTree pic box
    t "label order: the SVG paints the same order"
      ((GfxSvg.readSteps (HtmlDoc.pictureIso box) els).map stepKind == #["label", "ink", "label"])
  | _ => t "label order: the document holds one picture" false
