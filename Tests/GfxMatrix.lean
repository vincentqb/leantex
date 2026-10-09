module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.GfxMatrix

def red : Ir.Color := { r := 255, g := 0, b := 0 }
def blue : Ir.Color := { r := 0, g := 0, b := 255 }

def half : Gfx.Alpha := ⟨500, by decide⟩

def fillOf (c : Ir.Color) : Gfx.Fill := { paint := .solid c, rule := .nonzero, alpha := Gfx.Alpha.opaque }

/-- A stroke stating every field away from both formats' initial values. -/
def fancyStroke : Gfx.Stroke :=
  { paint := .solid blue, width := Dim.pt 2, cap := .round, join := .bevel, miterLimit := 4
    dash := #[Dim.pt 2, Dim.pt 1], phase := Dim.pt 1, alpha := half }

def stops : Array Gfx.Stop := #[{ offset := 0, color := red }, { offset := 65536, color := blue }]

def linear : Gfx.Gradient := .linear (0, 0) (Dim.pt 10, 0) stops Gfx.Affine.unit

def radial : Gfx.Gradient := .radial (Dim.pt 5, Dim.pt 5) 0 (Dim.pt 5, Dim.pt 5) (Dim.pt 5) stops
  Gfx.Affine.unit

/-- A rotation by the 3-4-5 angle, then a translation: exact in rationals. -/
def turn : Gfx.Affine := ⟨3 / 5, 4 / 5, -4 / 5, 3 / 5, Dim.pt 10, Dim.pt 20⟩

def square : Gfx.Geom := .rect 0 0 (Dim.pt 10) (Dim.pt 10)

def tri : Gfx.Subpath :=
  { start := (0, 0), segs := #[.line (Dim.pt 10, 0), .cubic (Dim.pt 10, Dim.pt 5) (Dim.pt 5, Dim.pt 10)
      (0, Dim.pt 10)], closed := true }

def figure (nodes : Array (Gfx.Node Empty)) (symbols : Array (Array (Gfx.Node Empty)) := #[])
    (outlines : Array (Array Gfx.Subpath) := #[]) : Gfx.Figure Empty :=
  { box := ((0, 0), (Dim.pt 100, Dim.pt 100)), clipToBox := false, nodes := nodes
    outlines := outlines, symbols := symbols
    rasters := #[{ bytes := ByteArray.empty, jpeg := false, pxW := 1, pxH := 1, smooth := false }]
    title := none, losses := #[] }

/-- The synthetic matrix: every node arm, solid and gradient paints on fill
and stroke, a clip of each rule, an alpha group, a symbol use, an outline
stamp, a raster, ink-free words. -/
def cases : Array (String × Gfx.Figure Empty) := #[
  ("solid fill and a stroke stating every field",
    figure #[.draw square (some (fillOf red)) (some fancyStroke)]),
  ("an ellipse filled and stroked with gradients",
    figure #[.draw (.ellipse (Dim.pt 5) (Dim.pt 5) (Dim.pt 5) (Dim.pt 3))
      (some { paint := .gradient linear, rule := .nonzero, alpha := Gfx.Alpha.opaque })
      (some { fancyStroke with paint := .gradient radial })]),
  ("an even-odd path",
    figure #[.draw (.path #[tri]) (some { fillOf red with rule := .evenOdd }) none]),
  ("a turned group clipped twice",
    figure #[.group turn #[{ geom := square, rule := .nonzero }, { geom := .path #[tri], rule := .evenOdd }]
      Gfx.Alpha.opaque #[.draw square (some (fillOf blue)) none]]),
  ("an alpha group",
    figure #[.group Gfx.Affine.unit #[] half #[.draw square (some (fillOf red)) none,
      .draw (.path #[tri]) none (some (Gfx.strokeOf {}))]]),
  ("a symbol used twice",
    figure #[.use 0 turn, .use 0 Gfx.Affine.unit]
      #[#[.draw square (some (fillOf red)) none,
          .group turn #[] Gfx.Alpha.opaque #[.draw (.path #[tri]) none (some (Gfx.strokeOf {}))]]]),
  ("an outline stamped",
    figure #[.stamp 0 turn (some (fillOf blue)) none] (outlines := #[#[tri]])),
  ("a raster mapped",
    figure #[.image 0 ⟨20, 0, 0, 10, Dim.pt 5, Dim.pt 5⟩]),
  ("ink-free words", figure #[.words "recovered text", .draw square none (some (Gfx.strokeOf {}))])]

def pdfPlace : Gfx.Iso := { flipY := false, dx := Dim.pt 3, dy := Dim.pt 4 }
def svgPlace : Gfx.Iso := { flipY := true, dx := 0, dy := Dim.pt 100 }

def names : GfxPdf.Request → Nat := fun _ => 0

def pdfOps (fig : Gfx.Figure Empty) : Array Pdf.ContentOp :=
  GfxPdf.emit names (fun _ e => nomatch e) pdfPlace fig

def svgTree (fig : Gfx.Figure Empty) : Array GfxSvg.El :=
  GfxSvg.tree (fun _ e => nomatch e) #[{ href := "data:image/png;base64,", smooth := false }] svgPlace fig

def spelled (fig : Gfx.Figure Empty) : Array Html.Node := GfxSvg.spell 7 (svgTree fig)

def attrs (fig : Gfx.Figure Empty) (tag : String) : Array (Array (String × String)) :=
  (elemAttrsList (· == tag) #[] (spelled fig).toList).map (·.2)

def has (a : Array (String × String)) (k v : String) : Bool := a.any (· == (k, v))

end Tests.GfxMatrix

open Tests.GfxMatrix in
/-- **The vector model's two emitters over a synthetic matrix**, asserted
over the typed PDF operators and the typed and spelled SVG trees: each case
reads back to the figure's marks in both formats (`GfxPdf.marks_projects`,
`GfxSvg.marks_projects`, executed), and each spells what its format needs —
the state PDF does not start in, the attributes SVG does not start with,
the resources and definitions a gradient, clip, alpha group, symbol, stamp
and raster name. Invented geometry. -/
def gfxMatrixChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, fig) in cases do
    t s!"gfx matrix {name}: the PDF reads back as the figure's marks"
      (GfxPdf.readMarks pdfPlace (pdfOps fig) == fig.marks)
    t s!"gfx matrix {name}: the SVG reads back as the figure's marks"
      (GfxSvg.readMarks svgPlace (svgTree fig) == fig.marks)
  let some (_, f0) := cases[0]? | t "gfx matrix: cases" false
  let pdf0 := Pdf.render (pdfOps f0)
  t "gfx matrix: PDF states a stroke's cap, join, miter limit, dash and alphas"
    (["1 J ", "2 j ", "4 M ", "[2 1] 1 d ", "/GS1 gs "].all (hasStr pdf0 ·))
  t "gfx matrix: SVG states what differs from its initial values, and not the miter limit 4"
    ((attrs f0 "rect").any fun a => has a "stroke-linecap" "round" && has a "stroke-linejoin" "bevel" &&
      has a "stroke-dasharray" "2 1" && has a "stroke-dashoffset" "1" &&
      has a "stroke-opacity" "0.5" && !(a.any (·.1 == "stroke-miterlimit")))
  let some (_, f1) := cases[1]? | t "gfx matrix: cases" false
  let pdf1 := Pdf.render (pdfOps f1)
  t "gfx matrix: a gradient paints through a shading pattern in PDF"
    (hasStr pdf1 "/Pattern cs /P1 scn" && hasStr pdf1 "/Pattern CS /P1 SCN")
  t "gfx matrix: and through gradient definitions in SVG"
    ((attrs f1 "linearGradient").any (has · "id" "f7~g0") &&
      (attrs f1 "radialGradient").any (has · "id" "f7~g1") &&
      (attrs f1 "ellipse").any fun a => has a "fill" "url(#f7~g0)" && has a "stroke" "url(#f7~g1)")
  let some (_, f2) := cases[2]? | t "gfx matrix: cases" false
  t "gfx matrix: an even-odd fill is f* in PDF and fill-rule in SVG"
    ((Pdf.render (pdfOps f2)).endsWith "f* Q" && (attrs f2 "path").any (has · "fill-rule" "evenodd"))
  let some (_, f3) := cases[3]? | t "gfx matrix: cases" false
  t "gfx matrix: a transformed clipped group is one saved state with its cm and clips"
    (match pdfOps f3 with
     | #[.group (some _) none clips body] => clips.size == 2 && body.size == 1 &&
         hasStr (Pdf.render (pdfOps f3)) "W* n"
     | _ => false)
  t "gfx matrix: and a transformed g around one g per clip, each clipPath in user space"
    ((attrs f3 "clipPath").size == 2 && (attrs f3 "clipPath").all (has · "clipPathUnits" "userSpaceOnUse") &&
      (attrs f3 "g").any (·.any (·.1 == "transform")) &&
      (attrs f3 "g").any (has · "clip-path" "url(#f7~c0)") &&
      (attrs f3 "g").any (has · "clip-path" "url(#f7~c1)"))
  let some (_, f4) := cases[4]? | t "gfx matrix: cases" false
  t "gfx matrix: an alpha group composites as one transparency group form"
    (match pdfOps f4 with
     | #[.group none (some g) #[] #[.xobject none _ .group body]] => g.fill == half && body.size == 2
     | _ => false)
  t "gfx matrix: and as a g with opacity"
    ((attrs f4 "g").any (has · "opacity" "0.5"))
  let some (_, f5) := cases[5]? | t "gfx matrix: cases" false
  t "gfx matrix: a symbol is one form painted per use"
    (match pdfOps f5 with
     | #[.xobject (some _) _ .symbol a, .xobject (some _) _ .symbol b] => a == b && a.size == 2
     | _ => false)
  t "gfx matrix: and one symbol definition each use names"
    ((attrs f5 "symbol").size == 1 && (attrs f5 "use").size == 2 &&
      (attrs f5 "use").all (has · "href" "#f7~s0"))
  let some (_, f6) := cases[6]? | t "gfx matrix: cases" false
  t "gfx matrix: a stamp sets its paints before the outline's form"
    (hasStr (Pdf.render (pdfOps f6)) " /Fm1 Do Q")
  t "gfx matrix: and paints an unpainted outline definition through use"
    ((attrs f6 "path").any (has · "id" "f7~o0") &&
      (attrs f6 "use").any fun a => has a "href" "#f7~o0" && a.any (·.1 == "fill"))
  let some (_, f7) := cases[7]? | t "gfx matrix: cases" false
  t "gfx matrix: a raster paints its image XObject under its matrix"
    ((Pdf.render (pdfOps f7)).endsWith "/Ri1 Do Q")
  t "gfx matrix: and an image of the unit square, flipped into SVG's frame"
    ((attrs f7 "image").any fun a => has a "width" "1" && has a "height" "1" &&
      has a "preserveAspectRatio" "none" && a.any (·.1 == "transform"))
  -- A raster's unit square is one frame unit: both formats' image space.
  t "gfx matrix: a 20 × 10 raster spans 20 pt by 10 pt in the model"
    (f7.geomBox == some ((Dim.pt 5, Dim.pt 5), (Dim.pt 25, Dim.pt 15)))
  t "gfx matrix: and in the PDF, its unit square under the placed matrix"
    (Pdf.render (pdfOps f7) == "q 20 0 0 10 8 9 cm /Ri1 Do Q")
  t "gfx matrix: and in the SVG, its top edge at 85 pt down the 100 pt viewport"
    ((attrs f7 "image").any (has · "transform" "matrix(20 0 0 10 5 85)"))
  t "gfx matrix: a raster no reader may smooth says so to the SVG"
    ((attrs f7 "image").any (has · "image-rendering" "pixelated"))
  let some (_, f8) := cases[8]? | t "gfx matrix: cases" false
  t "gfx matrix: words paint nothing in either format"
    ((pdfOps f8).size == 1 && (svgTree f8).size == 1)
  let doc := GfxSvg.document (fun _ e => nomatch e) #[] f0
  t "gfx matrix: a figure ships as a standalone SVG document"
    (doc.startsWith "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<svg xmlns=\"http://www.w3.org/2000/svg\" \
viewBox=\"0 0 100 100\" width=\"100pt\" height=\"100pt\" overflow=\"visible\">")
  t "gfx matrix: and its children are the inline spelling's"
    (match GfxSvg.documentRoot f0.box f0.clipToBox (GfxSvg.spell 0 (GfxSvg.tree (fun _ e => nomatch e) #[]
        (GfxSvg.documentIso f0.box) f0)) with
     | .elem "svg" _ kids => kids.size == (GfxSvg.spell 0 (svgTree f0)).size
     | _ => false)
