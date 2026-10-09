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

end Tests.GfxRegression

open Tests.GfxRegression in
/-- **The four cross-backend picture defects the vector model closed**,
each asserted over the artifact a reader meets — the page's typed stream
and `Layout.Out`, the typed HTML tree — and each failing before the model
landed. A rectangle fill painted in the page's leading fill block, before
every picture path (F1); an edge's continuing segments each opened with
its own `M` in the SVG, so interior vertices drew caps where the PDF drew
joins (F2); a zero line width painted nothing in the SVG where PDF and pgf
draw the thinnest visible line (F3); SVG strokes left at SVG's miter limit
of 4 where PDF and pgf mitre to 10 (F4). Invented pictures. -/
def gfxDefectChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let red : Ir.Color := { r := 255, g := 0, b := 0 }
  -- F1: the fill paints after the edge the source draws first, inside the
  -- picture's own Figure sequence, and is no page fill.
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
  -- F1 and the furniture: a footer band never splits a picture — its fill
  -- and its stroke stand on one side of the band, inside one Figure
  -- sequence. While picture fills were page fills, the band painted after
  -- the fill and before the stroke, so a picture overflowing into the band
  -- lost its fills under it and kept its strokes over it. Which side the
  -- band paints on is the furniture's own decision: today it paints with
  -- the page's other fills, before the body's ink and text.
  let ground : Ir.Color := { r := 0xE8, g := 0xED, b := 0xF3 }
  let (docF, _) := elabStr ("\\documentclass{beamer}\\usetheme{moloch}\\pictures{ tool = none }" ++
    "\\definecolor{FootGround}{HTML}{E8EDF3}\\setbeamercolor{footline}{bg=FootGround}" ++
    "\\begin{document}\\begin{frame}{Picture}\n\\begin{tikzpicture}\n" ++
    "\\fill[red] (0,0) rectangle (1,1);\n\\draw (0,0) -- (1,1);\n" ++
    "\\end{tikzpicture}\n\\end{frame}\\end{document}")
  let outF := layoutOf oneFace docF
  let lsF := streamLines oneFace docF outF
  -- The band's colour carries the exact rider `\definecolor` declared, so
  -- its spelling is read off the shipped fill, not rebuilt from the screen
  -- value.
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
  -- F2: a chain of continuing segments is one subpath in both artifacts.
  let (doc2, _) := elabStr (picDoc "" "" "\\draw (0,0) -- (1,0) -- (1,1);")
  t "F2: a continuing segment chain is one SVG subpath"
    (match (strokedPaths doc2).toList with
     | [attrs] => ((attr? attrs "d").map fun d => (d.splitOn "M").length == 2).getD false
     | _ => false)
  let ls2 := streamLines oneFace doc2 (layoutOf oneFace doc2)
  t "F2: and one PDF subpath"
    ((ls2.filter fun l => l.endsWith " S Q").all fun l => (l.splitOn " m ").length == 2)
  -- F3: a zero line width is the thinnest visible line in both.
  let (doc3, _) := elabStr (picDoc "" "" "\\draw[line width=0pt] (0,0) -- (1,0);")
  t "F3: a 0pt line width draws the SVG hairline"
    (match (strokedPaths doc3).toList with
     | [attrs] => attr? attrs "stroke-width" == some "1" &&
         attr? attrs "vector-effect" == some "non-scaling-stroke"
     | _ => false)
  t "F3: and the PDF's thinnest line"
    ((streamLines oneFace doc3 (layoutOf oneFace doc3)).any (hasStr · " 0 w "))
  -- F4: every TikZ stroke states pgf's miter limit to the SVG.
  let (doc4, _) := elabStr (picDoc "" ""
    "\\draw (0,0) -- (1,0) -- (1,1);\n\\node[draw] at (3,0) {Box};\n\\node[draw,circle] at (5,0) {O};")
  let stroked := elemAttrsList (fun tag => tag == "path" || tag == "rect" || tag == "circle") #[]
    (doc4.body.toList.map (HtmlDoc.blockNode {}))
  let strokes := stroked.filter fun (_, attrs) => attrs.any fun (k, v) => k == "stroke" && v != "none"
  t "F4: HTML TikZ strokes carry stroke-miterlimit 10"
    (strokes.size == 3 && strokes.all fun (_, attrs) => attr? attrs "stroke-miterlimit" == some "10")
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
/-- **The HTML face of the `diagram-strokes` census row**: the strokes the
vector model made reachable in the SVG ship on the fixture's emitted page,
read over the typed HTML tree — the chain and the dashed chain each one
subpath of two segments, the zero line width the hairline (one CSS pixel
that no transform scales), every stroke at pgf's miter limit. -/
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

/-- **Both artifacts read one picture's marks, over the whole corpus**: the
marks read back from every ink the layout placed (`Pdf.inkPaint`, the
operators `contentOps` writes under the picture's Figure sequence, read with
PDF's meaning) are the marks read back from the typed SVG tree the HTML
backend emits for one of the document's pictures (`HtmlDoc.pictureTree`,
read with SVG's meaning), and every picture with ink is placed; and every
stroke a shipped picture's SVG paints states pgf's miter limit, the census
of that emission. The executable face of `Gfx.picture_marks_agree` on the
shipped pipeline. -/
def gfxAgreementChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let mut placed := 0
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
      GfxPdf.readMarks ((Pdf.pageIso art.geom).compose k.place) (Pdf.inkPaint art.geom Pdf.figureNames k)
    placed := placed + pdf.size
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
