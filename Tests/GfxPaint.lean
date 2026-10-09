module

public import Tests.GfxMatrix
public import Tests.Backends

public section

open LeanTex.Core

namespace Tests.GfxPaint

open Tests.GfxMatrix

def opaqueFill (p : Gfx.Paint) : Gfx.Fill := { paint := p, rule := .nonzero, alpha := Gfx.Alpha.opaque }

/-- A gradient that runs up the page from the figure's origin, and one off
its box's centre: both read differently in a frame the placement flips. -/
def vertical : Gfx.Gradient := .linear (0, 0) (0, Dim.pt 10) stops Gfx.Affine.unit

def offCentre : Gfx.Gradient :=
  .radial (Dim.pt 2, Dim.pt 3) 0 (Dim.pt 2, Dim.pt 3) (Dim.pt 6) stops Gfx.Affine.unit

def atRoot (g : Gfx.Gradient) : Gfx.Figure Empty :=
  figure #[.draw square (some (opaqueFill (.gradient g))) none]

def inGroup (g : Gfx.Gradient) : Gfx.Figure Empty :=
  figure #[.group (Gfx.Affine.translate (Dim.pt 20) (Dim.pt 30)) #[] Gfx.Alpha.opaque
    #[.draw square (some (opaqueFill (.gradient g))) none]]

/-- The SVG an emitter that left a gradient in its own frame wrote: every
`url` paint's frame map back to the gradient's own. -/
def unplacedSvg : GfxSvg.El → GfxSvg.El
  | .shape g a =>
    let back (p : GfxSvg.SPaint) : GfxSvg.SPaint := match p with
      | .url gr => .url (gr.withXf Gfx.Affine.unit)
      | .none => .none
      | .color c => .color c
    .shape g { a with fill := a.fill.map back, stroke := a.stroke.map back }
  | e => e

/-- The PDF an emitter that left a pattern's matrix out of the placement
wrote. -/
def unplacedPdf : Pdf.ContentOp → Pdf.ContentOp
  | .paint fl st gs segs =>
    let back (p : Pdf.PdfPaint) : Pdf.PdfPaint := match p with
      | .pattern r gr => .pattern r (gr.withXf Gfx.Affine.unit)
      | .solid c => .solid c
    .paint (fl.map fun f => { f with paint := back f.paint }) st gs segs
  | o => o

def gradientAttr (fig : Gfx.Figure Empty) (tag key : String) : Option String :=
  ((attrs fig tag)[0]?).bind fun a => (a.find? (·.1 == key)).map (·.2)

mutual

/-- Every value an attribute named `key` takes in a node tree, onto `acc`. -/
def attrValuesOne (key : String) (acc : Array String) : Html.Node → Array String
  | .elem _ as kids =>
    attrValuesList key (acc ++ as.filterMap fun kv => if kv.1 == key then some kv.2 else none)
      kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def attrValuesList (key : String) (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | n :: rest => attrValuesList key (attrValuesOne key acc n) rest

end

def attrValues (key : String) (n : Html.Node) : Array String := attrValuesOne key #[] n

/-- The definitions an `svg` subtree references: `url(#…)` paints and clips,
`#…` hrefs. -/
def refsOf (n : Html.Node) : Array String :=
  let urls := (#["fill", "stroke", "clip-path"].flatMap fun k => attrValues k n).filterMap fun v =>
    if v.startsWith "url(#" then some ((v.drop 5).dropEnd 1).toString else none
  let hrefs := (attrValues "href" n).filterMap fun v =>
    if v.startsWith "#" then some (v.drop 1).toString else none
  urls ++ hrefs

def svgOf (fig : Gfx.Figure Empty) : Html.Node := Html.elem "svg" (GfxSvg.spell 0 (svgTree fig)) #[]

def stampFig (paints : Array (Option Gfx.Fill × Option Gfx.Stroke)) : Gfx.Figure Empty :=
  figure (paints.map fun (fl, st) => .stamp 0 turn fl st) (outlines := #[#[tri]])

def forms (fig : Gfx.Figure Empty) : Array Pdf.FigRes :=
  (Pdf.collectList #[] (pdfOps fig).toList).filter fun r => match r with
    | .form _ _ => true
    | .extG _ _ => false
    | .pattern _ => false
    | .shading _ => false

end Tests.GfxPaint

open Tests.GfxPaint Tests.GfxMatrix in
/-- **A gradient lands in the frame the figure placed it in**, in both
artifacts, and the readers see where it lands. The SVG once spelled a
root-level gradient's points and transform in the figure's y-up frame while
its shape's coordinates were placed into the SVG's y-down one, so a
vertical gradient painted upside down; and both readers copied the typed
gradient back without reading its frame, so `backend_marks_agree` held of
the misplaced SVG. The emitters compose the placement into a gradient's
frame map (`GfxSvg.sPaint`, `GfxPdf.pdfPaint`), and the readers place it
back in the figure frame from what the artifact states — so the same
artifact with the placement left out of the gradient reads as different
marks. Invented geometry. -/
def gfxGradientFrameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "gradient frame: a root gradient's SVG transform carries the placement"
    (gradientAttr (atRoot vertical) "linearGradient" "gradientTransform" == some "matrix(1 0 0 -1 0 100)")
  t "gradient frame: inside a transformed group it is the group's own frame"
    (gradientAttr (inGroup vertical) "linearGradient" "gradientTransform" == some "matrix(1 0 0 1 0 0)")
  t "gradient frame: a root pattern's matrix carries the PDF placement"
    (match pdfOps (atRoot vertical) with
     | #[.paint (some { paint := .pattern _ g, .. }) none none _] =>
       g.xf == Gfx.Affine.translate (Dim.pt 3) (Dim.pt 4)
     | _ => false)
  for (name, fig) in #[("vertical root", atRoot vertical), ("off-centre radial root", atRoot offCentre),
      ("vertical in a group", inGroup vertical), ("radial in a group", inGroup offCentre)] do
    t s!"gradient frame {name}: the SVG reads back as the figure's marks"
      (GfxSvg.readMarks svgPlace (svgTree fig) == fig.marks)
    t s!"gradient frame {name}: the PDF reads back as the figure's marks"
      (GfxPdf.readMarks pdfPlace (pdfOps fig) == fig.marks)
  for (name, fig) in #[("vertical root", atRoot vertical), ("off-centre radial root", atRoot offCentre)] do
    t s!"gradient frame {name}: an SVG gradient left in its own frame reads as other marks"
      (GfxSvg.readMarks svgPlace ((svgTree fig).map unplacedSvg) != fig.marks)
    t s!"gradient frame {name}: a pattern matrix without the placement reads as other marks"
      (GfxPdf.readMarks pdfPlace ((pdfOps fig).map unplacedPdf) != fig.marks)
  t "gradient frame: a mark's gradient stands in the figure frame"
    (match (inGroup vertical).marks with
     | #[.paint _ _ (some { paint := .gradient g, .. }) none _ _] =>
       g.xf == Gfx.Affine.translate (Dim.pt 20) (Dim.pt 30)
     | _ => false)

open Tests.GfxPaint Tests.GfxMatrix in
/-- **Figures on one page never share an id**: every figure spells its
definitions under ordinal 0, and the page numbers each rendered figure that
defines anything apart, in document order (`HtmlDoc.numberFigures`) — so a
second figure's `url(#…)` resolves to its own definition, not the first's.
The ids hold a separator no anchor the document names can (`GfxSvg.idSep`),
and the anchors two overlay alternatives share are never a figure's own.
Invented geometry. -/
def gfxIdChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some (_, grads) := cases[1]? | t "figure ids: cases" false
  let some (_, clips) := cases[3]? | t "figure ids: cases" false
  let some (_, plain) := cases[0]? | t "figure ids: cases" false
  let body := #[svgOf grads, Html.elem "div" #[svgOf clips] #[], svgOf plain, svgOf grads]
  let ids (ns : Array Html.Node) : Array String := ns.flatMap (attrValues "id")
  t "figure ids: unnumbered, two figures share their ids"
    ((ids body).size != (ids body).toList.eraseDups.length)
  let numbered := HtmlDoc.numberFigures body
  t "figure ids: numbered, every id on the page is distinct"
    (!(ids numbered).isEmpty && (ids numbered).size == (ids numbered).toList.eraseDups.length)
  let same (a b : Html.Node) : Bool := Html.render a 0 == Html.render b 0
  t "figure ids: each figure is spelled under its document ordinal"
    (match numbered with
     | #[a, .elem "div" _ #[b], c, d] =>
       same a (Html.elem "svg" (GfxSvg.spell 0 (svgTree grads)) #[]) &&
         same b (Html.elem "svg" (GfxSvg.spell 1 (svgTree clips)) #[]) &&
         same c (svgOf plain) && same d (Html.elem "svg" (GfxSvg.spell 2 (svgTree grads)) #[])
     | _ => false)
  t "figure ids: every reference resolves inside its own figure"
    ((numbered.flatMap fun n => match n with
        | .elem "div" _ kids => kids
        | n => #[n]).all fun svg => (refsOf svg).all fun r => (attrValues "id" svg).contains r)
  t "figure ids: a document's label anchor never spells a figure id"
    (Ir.labelAnchor (GfxSvg.svgId 0 .gradient 0) != GfxSvg.svgId 0 .gradient 0 &&
      (GfxSvg.parseId (Ir.labelAnchor (GfxSvg.svgId 0 .gradient 0))).isNone)
  t "figure ids: an id reads back as its parts"
    (GfxSvg.parseId (GfxSvg.svgId 12 .outline 7) == some (12, .outline, 7) &&
      GfxSvg.parseId "f12-o7" == none && GfxSvg.parseId "fn3" == none)
  let spec : Ir.OverlaySpec := { first := 1, last := some 1 }
  let alts := HtmlDoc.overlayAlternatives "div" 2 spec #[svgOf grads] #[svgOf grads]
  t "figure ids: overlay alternatives hoist no figure definition"
    (alts.all fun n => match n with
      | .elem "span" _ _ => false
      | _ => true)
  t "figure ids: and both alternatives keep their figures' definitions"
    (((HtmlDoc.numberFigures alts).flatMap (attrValues "id")).size == 2 * (ids #[svgOf grads]).size)

open Tests.GfxPaint Tests.GfxMatrix in
/-- **A stamp's form is its outline and operator, never its colour**: an
outline painted red and blue under two matrices is one form, its body a
path and a painting operator with no colour of its own, each instance
setting its colour before the `Do`; a stroked stamp's form is keyed by the
reach its strokes need, which its box clips to; a gradient stamp paints
inline, since a pattern never crosses a form boundary. Each reads back as
its marks. Invented geometry. -/
def gfxStampChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let twoColours := stampFig #[(some (fillOf red), none), (some (fillOf blue), none)]
  t "stamps: one outline in two colours is one form"
    ((forms twoColours).size == 1)
  t "stamps: the form's body is the outline and its operator alone"
    (match forms twoColours with
     | #[.form (.stamp 0) #[.outline (some .nonzero) false _]] => true
     | _ => false)
  t "stamps: each instance sets its own colour before the form paints"
    (match pdfOps twoColours with
     | #[.xobject (some _) _ (.stamp (some (.solid a)) none none) _,
         .xobject (some _) _ (.stamp (some (.solid b)) none none) _] => a == red && b == blue
     | _ => false)
  t "stamps: the form's stream states no colour"
    (match forms twoColours with
     | #[.form _ body] => !hasStr (Pdf.render body) " rg" && (Pdf.render body).endsWith " h f"
     | _ => false)
  let widths := stampFig #[(none, some { Gfx.strokeOf {} with width := Dim.pt 1 }),
    (none, some { Gfx.strokeOf {} with width := Dim.pt 4 })]
  t "stamps: strokes needing different room are different forms"
    ((forms widths).size == 2)
  let graded := stampFig #[(some (opaqueFill (.gradient linear)), none)]
  t "stamps: a gradient stamp paints inline, in no form"
    ((forms graded).isEmpty &&
      match pdfOps graded with
      | #[.group (some _) none #[] #[.paint (some { paint := .pattern _ _, .. }) none none _]] => true
      | _ => false)
  for (name, fig) in #[("two colours", twoColours), ("two widths", widths), ("a gradient", graded)] do
    t s!"stamps {name}: the PDF reads back as the figure's marks"
      (GfxPdf.readMarks pdfPlace (pdfOps fig) == fig.marks)
    t s!"stamps {name}: the SVG reads back as the figure's marks"
      (GfxSvg.readMarks svgPlace (svgTree fig) == fig.marks)

open Tests.GfxMatrix in
/-- **The shared geometry kit**, each piece at the values its definition
names: the four axis directions exact; an endpoint arc's centre on its
chord's midpoint and its pieces' joins on the circle, including when its
radii are scaled up to reach; a rounded rectangle's radii clamped to half
its extents; the quadratic-to-cubic elevation two thirds of the way; a dash
array as both formats read it; a regular polygon's vertices on its circle.
Invented values. -/
def gfxKitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let u := Gfx.Trig.unit
  t "kit: the axis directions are exact"
    (Gfx.Trig.cosSin 0 == (u, 0) && Gfx.Trig.cosSin (Gfx.Trig.pi / 2) == (0, u) &&
      Gfx.Trig.cosSin Gfx.Trig.pi == (-u, 0) && Gfx.Trig.cosSin (-(Gfx.Trig.pi / 2)) == (0, -u))
  let p := Dim.pt 1
  let semi := Gfx.Kit.arcEndpoint (0, 0) p p 0 false true (2 * p, 0)
  t "kit: a semicircle's quarter join is on the circle, below its chord's midpoint"
    (semi.size == 2 && (semi[0]?.map Gfx.Seg.endPt) == some (p, -p))
  t "kit: and it ends exactly where it was declared to"
    ((semi.back?.map Gfx.Seg.endPt) == some (2 * p, 0))
  let other := Gfx.Kit.arcEndpoint (0, 0) p p 0 false false (2 * p, 0)
  t "kit: the other sweep bulges the other way"
    ((other[0]?.map Gfx.Seg.endPt) == some (p, p))
  let reach := Gfx.Kit.arcEndpoint (0, 0) (p / 2) (p / 2) 0 false true (2 * p, 0)
  t "kit: radii too small to reach scale up, the centre at the chord's midpoint"
    (match reach[0]?.map Gfx.Seg.endPt with
     | some (x, y) => (x - p).natAbs ≤ 2 && (y + p).natAbs ≤ 2
     | none => false)
  t "kit: a zero radius is a line, coincident ends draw nothing"
    (Gfx.Kit.arcEndpoint (0, 0) 0 p 0 false true (p, p) == #[.line (p, p)] &&
      (Gfx.Kit.arcEndpoint (p, p) p p 0 false true (p, p)).isEmpty)
  let rr := Gfx.Kit.roundedRect 0 0 (10 * p) (4 * p) (3 * p) (3 * p)
  t "kit: a rounded rectangle clamps its radii to half its extents and closes"
    (rr.closed && rr.start == (3 * p, 0) && rr.segs[1]? == some
      (.cubic (7 * p + (3 * p * 5523 + 5000) / 10000, 0) (10 * p, 2 * p - (2 * p * 5523 + 5000) / 10000)
        (10 * p, 2 * p)) &&
      (rr.segs.back?.map Gfx.Seg.endPt) == some rr.start)
  t "kit: a rounded rectangle with no radius is the rectangle"
    (Gfx.Kit.roundedRect 0 0 p p 0 (p / 2) == Gfx.Kit.rectPath 0 0 p p)
  t "kit: a quadratic elevates two thirds of the way to its control"
    (Gfx.Kit.quadToCubic (0, 0) (3 * p, 3 * p) (6 * p, 0) ==
      .cubic (2 * p, 2 * p) (4 * p, 2 * p) (6 * p, 0))
  t "kit: an odd dash list doubles, a list with no positive entry or a negative one is solid"
    (Gfx.Kit.normDash #[1, 2, 3] == #[1, 2, 3, 1, 2, 3] && Gfx.Kit.normDash #[0, 0] == #[] &&
      Gfx.Kit.normDash #[-1, 2] == #[] && Gfx.Kit.normDash #[2, 1] == #[2, 1])
  let sq := Gfx.Kit.regularPolygon 0 0 (10 * p) 4 0
  t "kit: a regular polygon's vertices stand on its circle"
    (sq.closed && sq.start == (10 * p, 0) &&
      sq.segs.map Gfx.Seg.endPt == #[(0, 10 * p), (-(10 * p), 0), (0, -(10 * p))])

open Tests.GfxMatrix in
/-- **A page's ink paints no raster, and the writer refuses one that
would**: the lowering puts no image node in a picture's ink
(`Gfx.ofPictureIn_imageFree_exact`), and the checked writer refuses a page whose
ink carries one rather than writing a name no resource answers. Invented
geometry. -/
def gfxInkRasterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let some (_, raster) := cases[7]? | t "ink rasters: cases" false
  let some (_, plain) := cases[0]? | t "ink rasters: cases" false
  let page (fig : Gfx.Figure Empty) : Layout.PageOut :=
    { inks := #[{ fig := fig, place := { flipY := true, dx := 0, dy := Dim.pt 100 } }] }
  t "ink rasters: an ink that paints a raster is refused"
    (match Pdf.writeChecked {} oneFace #[page plain, page raster] with
     | .error (.inkRaster 1) => true
     | _ => false)
  t "ink rasters: an ink without one is written"
    (match Pdf.writeChecked {} oneFace #[page plain] with
     | .ok _ => true
     | .error _ => false)

/-- **A copied page's content survives the writer's compression, on every
corpus figure**: each copied form the corpus ships declares `/FlateDecode`
exactly when its stored stream is smaller than the page's content, and its
stream decodes to that content — the shipped half of
`Pdf.copiedForm_inflate_id`. -/
def copiedFormChecks (ref : IO.Ref (List String)) (arts : Array GoldenArt) : IO Unit := do
  let mut seen := 0
  for art in arts do
    let contents := (Pdf.copiedFormContents art.store art.out.pages).filterMap id
    if contents.isEmpty then continue
    match art.objs with
    | .error e => check ref s!"copied forms {art.name}: the file reads back: {e}" false
    | .ok es =>
      let copied := es.filter fun e => e.val.get? "Subtype" == some (.name "Form") &&
        (e.val.get? "Matrix").isSome
      for e in copied do
        seen := seen + 1
        let raw := e.stream.getD ByteArray.empty
        let filtered := e.val.get? "Filter" == some (.name "FlateDecode")
        let decoded := (PdfRead.decodeStream e.val raw).toOption
        check ref s!"copied forms {art.name} {e.num}: the stream decodes to a copied page's content"
          (decoded.any fun d => contents.any (· == d))
        check ref s!"copied forms {art.name} {e.num}: deflated exactly when that is smaller"
          (decoded.any fun d => filtered == (raw.size < d.size) && (filtered || raw == d))
  check ref s!"copied forms: the corpus ships copied pages ({seen})" (seen > 0)
