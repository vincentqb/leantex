/-
The vector model's two emitters, rasterized and compared. Run from the
repository root:

  lake build ScriptsModules && lake env lean --run scripts/gfx-diff.lean --report
  lake env lean --run scripts/gfx-diff.lean --selftest

Each synthetic figure (invented geometry, every node arm the model has
but labels) is emitted twice. The PDF is the document writer's
(`Pdf.write`): one page the figure's size holding it as a placed ink, its
resources the document's figure table (`Pdf.figureTable`) — ExtGStates,
shading patterns, forms. A figure with a raster goes through `figurePdf`
below, a harness writer over the same table, since the document writer
refuses a placed ink that paints a raster (`Pdf.inkRasterPage?`: a page's
ink is a lowered picture, which paints none). Poppler's `pdftoppm`
rasterizes the
file at `rasterDpi`. The SVG is the standalone
document `GfxSvg.document` spells, which Chromium screenshots at the same
scale. The two rasters are compared by ImageMagick's DSSIM at
pdf-oracles' `dssimScale` and `dssimTolerance`, and by the mean Oklab
distance (ΔE_OK, ×100) between them. The raster figure does not smooth:
renderers smooth a scaled raster with different kernels, so only
sample-per-square rendering is a reading two of them share.

`--report` prints both numbers per figure and fails when any figure's
DSSIM exceeds the tolerance. `--selftest` injects a mutant into the SVG
side only — butt caps squared, a clip dropped, y flipped, an alpha
ignored, SVG's own miter limit of 4, a root gradient left in its own frame
— each on a figure that shows it, and fails unless every mutant lands above
the tolerance while its unmutated figure stays within. A
report, never a gate: it needs Poppler, Chromium and ImageMagick, and a
missing tool fails the run with its name.
-/
import LeanTex.Core.PdfFigures
import LeanTex.Core.PdfContent
import LeanTex.Core.Pdf
import LeanTex.Core.GfxSvg
import LeanTex.Core.HtmlResource
import LeanTex.Core.Oklab
import LeanTex.Core.Image
import scripts.RasterJudge
import Tests.Support

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

namespace GfxDiff

def rgbC (r g b : Nat) : Ir.Color := { r := r.toUInt8, g := g.toUInt8, b := b.toUInt8 }

def red : Ir.Color := rgbC 220 30 30
def blue : Ir.Color := rgbC 30 60 200
def green : Ir.Color := rgbC 20 150 60
def black : Ir.Color := rgbC 0 0 0
def amber : Ir.Color := rgbC 240 170 20

def pt (n : Int) : Sp := Dim.pt n

def solid (c : Ir.Color) : Fill := { paint := .solid c, rule := .nonzero, alpha := Alpha.opaque }

def stroke (c : Ir.Color) (w : Sp) : Stroke :=
  { paint := .solid c, width := w, cap := .butt, join := .miter, miterLimit := 10, dash := #[]
    phase := 0, alpha := Alpha.opaque }

def alphaOf (n : Nat) : Alpha := ⟨min n 1000, by omega⟩

def path (start : Pt) (pts : List Pt) (closed : Bool) : Geom :=
  .path #[{ start, segs := (pts.map Seg.line).toArray, closed }]

def figure (w h : Int) (nodes : Array (Node Empty)) (symbols : Array (Array (Node Empty)) := #[])
    (outlines : Array (Array Subpath) := #[]) (rasters : Array Raster := #[]) : Figure Empty :=
  { box := ((0, 0), (pt w, pt h)), clipToBox := false, nodes, outlines, symbols, rasters
    title := none, losses := #[] }

/-- A two-by-two RGB checkerboard as a PNG: signature, IHDR, one IDAT of
unfiltered rows (filter type 0) deflated by the engine's own codec, IEND —
each chunk with its CRC-32 (ISO/IEC 15948 §5.3). -/
def crcTable : Array UInt32 := Id.run do
  let mut t : Array UInt32 := #[]
  for n in [0:256] do
    let mut c : UInt32 := n.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

def crc32 (b : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for x in b.data do
    c := (crcTable[((c ^^^ x.toUInt32) &&& 0xFF).toNat]?.getD 0) ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

def be32 (n : UInt32) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

def chunk (kind : String) (data : ByteArray) : ByteArray :=
  let body := kind.toUTF8 ++ data
  be32 data.size.toUInt32 ++ body ++ be32 (crc32 body)

def checkerPng : ByteArray :=
  let sig : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩
  let ihdr := be32 2 ++ be32 2 ++ ⟨#[8, 2, 0, 0, 0]⟩
  let rows : ByteArray := ⟨#[0, 220, 30, 30, 30, 60, 200, 0, 30, 60, 200, 220, 30, 30]⟩
  sig ++ chunk "IHDR" ihdr ++ chunk "IDAT" (Flate.deflate rows) ++ chunk "IEND" ByteArray.empty

def checker : Raster := { bytes := checkerPng, jpeg := false, pxW := 2, pxH := 2, smooth := false }

/-- A closed wedge, the stamp's outline. -/
def wedge : Subpath :=
  { start := (0, 0), segs := #[.line (pt 80, 0), .line (pt 40, pt 50)], closed := true }

/-- A rotation by the 3-4-5 angle: exact in rationals. -/
def turn (dx dy : Int) : Affine := ⟨3 / 5, 4 / 5, -4 / 5, 3 / 5, pt dx, pt dy⟩

def stops2 : Array Stop := #[{ offset := 0, color := red }, { offset := 65536, color := blue }]

def stops3 : Array Stop :=
  #[{ offset := 0, color := amber }, { offset := 32768, color := green }, { offset := 65536, color := blue }]

/-- The report's figures: every node arm but labels, solid and gradient
paints on fill and stroke, both rules, a clip, an alpha group, symbols, a
stamp, a raster, ink-free words. -/
def cases : Array (String × Figure Empty) := #[
  ("fill and stroke", figure 120 80 #[
    .draw (.rect (pt 10) (pt 10) (pt 60) (pt 40)) (some (solid red))
      (some { stroke blue (pt 4) with join := .round }),
    .draw (path (pt 80, pt 10) [(pt 110, pt 40), (pt 80, pt 70)] false) none
      (some { stroke black (pt 6) with cap := .round, join := .bevel })]),
  ("dash, caps and joins", figure 120 80 #[
    .draw (path (pt 10, pt 20) [(pt 110, pt 20)] false) none
      (some { stroke blue (pt 4) with dash := #[pt 9, pt 4], phase := pt 2 }),
    .draw (path (pt 15, pt 40) [(pt 60, pt 70), (pt 105, pt 40)] false) none
      (some { stroke red (pt 8) with cap := .square, join := .miter, miterLimit := 4 })]),
  ("even-odd and nonzero", figure 120 80 #[
    .draw (.path #[{ start := (pt 10, pt 10), segs := #[.line (pt 50, pt 10), .line (pt 50, pt 50),
        .line (pt 10, pt 50)], closed := true },
      { start := (pt 20, pt 20), segs := #[.line (pt 40, pt 20), .line (pt 40, pt 40),
        .line (pt 20, pt 40)], closed := true }])
      (some { solid green with rule := .evenOdd }) none,
    .draw (.ellipse (pt 85) (pt 40) (pt 25) (pt 18)) (some (solid amber))
      (some (stroke black (pt 2)))]),
  ("cubic curves", figure 120 80 #[
    .draw (.path #[{ start := (pt 10, pt 10), segs := #[.cubic (pt 30, pt 90) (pt 90, pt (-10))
        (pt 110, pt 70)], closed := false }]) none (some (stroke blue (pt 5)))]),
  ("vertical gradient at the root", figure 120 80 #[
    .draw (.rect (pt 10) (pt 10) (pt 100) (pt 60))
      (some { solid red with paint := .gradient (.linear (0, pt 10) (0, pt 70) stops3 Affine.unit) })
      none]),
  ("off-centre radial gradient at the root", figure 120 80 #[
    .draw (.rect (pt 10) (pt 10) (pt 100) (pt 60))
      (some { solid red with paint := .gradient (.radial (pt 30, pt 25) 0 (pt 30, pt 25) (pt 50)
        stops2 Affine.unit) }) none]),
  ("hairline", figure 120 80 #[
    .draw (path (pt 10, pt 20) [(pt 110, pt 20), (pt 110, pt 60)] false) none
      (some (stroke black 0))]),
  ("sharp miter at pgf's limit", figure 120 80 #[
    .draw (path (pt 15, pt 26) [(pt 95, pt 40), (pt 15, pt 54)] false) none
      (some (stroke blue (pt 6)))]),
  ("linear gradient", figure 120 80 #[
    .draw (.rect (pt 10) (pt 10) (pt 100) (pt 60))
      (some { solid red with paint := .gradient (.linear (pt 10, 0) (pt 110, 0) stops3 Affine.unit) })
      (some (stroke black (pt 1)))]),
  ("radial gradient", figure 120 80 #[
    .draw (.ellipse (pt 60) (pt 40) (pt 45) (pt 30))
      (some { solid red with paint := .gradient (.radial (pt 60, pt 40) 0 (pt 60, pt 40) (pt 45)
        stops2 Affine.unit) }) none]),
  ("gradient stroke", figure 120 80 #[
    .draw (path (pt 10, pt 40) [(pt 110, pt 40)] false) none
      (some { stroke black (pt 16) with
        paint := .gradient (.linear (pt 10, 0) (pt 110, 0) stops2 Affine.unit) })]),
  ("clip", figure 120 80 #[
    .group Affine.unit #[{ geom := .ellipse (pt 60) (pt 40) (pt 30) (pt 30), rule := .nonzero }]
      Alpha.opaque #[.draw (.rect (pt 10) (pt 10) (pt 100) (pt 60)) (some (solid blue)) none]]),
  ("turned group", figure 120 80 #[
    .group (turn 60 10) #[] Alpha.opaque
      #[.draw (.rect 0 0 (pt 40) (pt 30)) (some (solid green)) (some (stroke black (pt 2)))]]),
  ("alpha group", figure 120 80 #[
    .draw (.rect (pt 5) (pt 30) (pt 110) (pt 20)) (some (solid amber)) none,
    .group Affine.unit #[] (alphaOf 500)
      #[.draw (.rect (pt 20) (pt 10) (pt 40) (pt 50)) (some (solid blue)) none,
        .draw (.rect (pt 45) (pt 20) (pt 40) (pt 50)) (some (solid red)) none]]),
  ("paint alpha", figure 120 80 #[
    .draw (.rect (pt 5) (pt 30) (pt 110) (pt 20)) (some (solid black)) none,
    .draw (.ellipse (pt 60) (pt 40) (pt 40) (pt 30)) (some { solid red with alpha := alphaOf 400 })
      (some { stroke blue (pt 6) with alpha := alphaOf 700 })]),
  ("symbol uses", figure 120 80 #[.use 0 (Affine.translate (pt 10) (pt 10)),
      .use 0 (turn 90 30)]
    (symbols := #[#[.draw (.rect 0 0 (pt 30) (pt 20)) (some (solid red)) (some (stroke black (pt 2)))]])),
  ("stamp", figure 120 80 #[.stamp 0 (Affine.translate (pt 20) (pt 15)) (some (solid green))
      (some (stroke black (pt 2)))] (outlines := #[#[wedge]])),
  ("one stamp form in two colours", figure 120 80 #[
      .stamp 0 ⟨1 / 2, 0, 0, 1 / 2, pt 5, pt 10⟩ (some (solid red)) none,
      .stamp 0 ⟨1 / 2, 0, 0, 1 / 2, pt 60, pt 40⟩ (some (solid blue)) (some (stroke black (pt 3)))]
    (outlines := #[#[wedge]])),
  ("gradient stamp", figure 120 80 #[.stamp 0 (Affine.translate (pt 20) (pt 15))
      (some { solid red with paint := .gradient (.linear (0, 0) (0, pt 50) stops2 Affine.unit) })
      none] (outlines := #[#[wedge]])),
  ("raster", figure 120 80 #[.image 0 ⟨80, 0, 0, 60, pt 20, pt 10⟩] (rasters := #[checker])),
  ("words", figure 120 80 #[.words "recovered text",
    .draw (.rect (pt 10) (pt 10) (pt 100) (pt 60)) none (some (stroke black (pt 3)))])]

/-! ## The PDF side: a harness writer -/

def ratNum (p q : Int) : String := Dim.ratString p q

def rgbArr (c : Ir.Color) : String :=
  s!"[{ratNum c.r.toNat 255} {ratNum c.g.toNat 255} {ratNum c.b.toNat 255}]"

def interp (c0 c1 : Ir.Color) : String :=
  s!"<< /FunctionType 2 /Domain [0 1] /C0 {rgbArr c0} /C1 {rgbArr c1} /N 1 >>"

/-- A stop list as a PDF function over [0, 1]: the first colour before the
first stop and the last after the last (SVG's padding), one exponential
segment between consecutive distinct offsets, stitched (§7.10.4). -/
def stopsFunction (stops : Array Stop) : String :=
  match stops.toList with
  | [] => interp black black
  | [s] => interp s.color s.color
  | first :: _ =>
    let last := (stops.back?.getD first)
    let pts : List (Nat × Ir.Color) :=
      (if first.offset.val > 0 then [(0, first.color)] else []) ++
        stops.toList.map (fun s => (s.offset.val, s.color)) ++
        (if last.offset.val < 65536 then [(65536, last.color)] else [])
    let segs := (pts.zip (pts.drop 1)).filter fun (a, b) => a.1 < b.1
    match segs with
    | [] => interp first.color first.color
    | [(a, b)] => interp a.2 b.2
    | _ =>
      let fns := " ".intercalate (segs.map fun (a, b) => interp a.2 b.2)
      let bounds := " ".intercalate ((segs.drop 1).map fun (a, _) => ratNum a.1 65536)
      let enc := " ".intercalate (segs.map fun _ => "0 1")
      s!"<< /FunctionType 3 /Domain [0 1] /Functions [{fns}] /Bounds [{bounds}] /Encode [{enc}] >>"

def shadingDict : Gradient → String
  | .linear p0 p1 stops _ =>
    s!"<< /ShadingType 2 /ColorSpace /DeviceRGB /Coords [{p0.1.toPtString} {p0.2.toPtString} \
{p1.1.toPtString} {p1.2.toPtString}] /Function {stopsFunction stops} /Extend [true true] >>"
  | .radial c0 r0 c1 r1 stops _ =>
    s!"<< /ShadingType 3 /ColorSpace /DeviceRGB /Coords [{c0.1.toPtString} {c0.2.toPtString} \
{r0.toPtString} {c1.1.toPtString} {c1.2.toPtString} {r1.toPtString}] /Function {stopsFunction stops} \
/Extend [true true] >>"

/-- A form's /BBox: the document writer's (`Pdf.formBBox`). -/
def bboxOf (kind : Pdf.FormKind) (body : Array Pdf.ContentOp) : String :=
  let (x0, y0, x1, y1) := Pdf.formBBox kind body
  s!"[{x0} {y0} {x1} {y1}]"

def resPrefix : Pdf.FigRes → String
  | .extG _ _ => "GS"
  | .pattern _ => "P"
  | .shading _ => "Sh"
  | .form _ _ => "Fm"

/-- One page of the figure: catalog, page tree, page, one resources
dictionary every stream names, the content, then one object per table
entry and per raster — classic cross-reference table. -/
def figurePdf (fig : Figure Empty) : ByteArray := Id.run do
  let ((x0, y0), (x1, y1)) := fig.box
  let place : Iso := { flipY := false, dx := -x0, dy := -y0 }
  let ix : GfxPdf.Request → Nat := fun r => match r with
    | .raster k => k
    | _ => 0
  let ops0 := GfxPdf.emit ix (fun _ e => nomatch e) place fig
  let t := Pdf.collectList #[] ops0.toList
  let ops := Pdf.nameOps t ops0
  let firstRes := 6
  let rasterBase := firstRes + t.size
  let mut objs : Array String := #[]
  let mut streams : Array (String × ByteArray) := #[]
  let mut entries : Array String := #[]
  for (r, i) in t.zipIdx do
    let id := firstRes + i
    entries := entries.push s!"/{resPrefix r}{i + 1} {id} 0 R"
  let mut rasterEntries : Array String := #[]
  for (_, k) in fig.rasters.zipIdx do
    rasterEntries := rasterEntries.push s!"/Ri{k + 1} {rasterBase + k} 0 R"
  let kindOf (p : String) : Array String := (entries.filter fun e => e.startsWith s!"/{p}")
  let sub (key : String) (es : Array String) : String :=
    if es.isEmpty then "" else s!" /{key} << {" ".intercalate es.toList} >>"
  let resources := "<<" ++ sub "ExtGState" (kindOf "GS") ++ sub "Pattern" (kindOf "P") ++
    sub "Shading" (kindOf "Sh") ++ sub "XObject" ((kindOf "Fm") ++ rasterEntries) ++ " >>"
  let w := (x1 - x0).toPtString
  let h := (y1 - y0).toPtString
  objs := objs.push "<< /Type /Catalog /Pages 2 0 R >>"
  objs := objs.push "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
  objs := objs.push s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {w} {h}] /Resources 4 0 R \
/Contents 5 0 R >>"
  objs := objs.push resources
  streams := streams.push ("", (Pdf.render ops).toUTF8)
  for r in t do
    match Pdf.nameRes t r with
    | .extG a b =>
      objs := objs.push s!"<< /Type /ExtGState /ca {ratNum a.val 1000} /CA {ratNum b.val 1000} >>"
    | .pattern g =>
      objs := objs.push s!"<< /Type /Pattern /PatternType 2 /Shading {shadingDict g} \
/Matrix [{g.xf.operands}] >>"
    | .shading g => objs := objs.push (shadingDict g)
    | .form kind body =>
      let group := match kind with
        | .group => " /Group << /Type /Group /S /Transparency /I true >>"
        | .symbol => ""
        | .stamp _ => ""
      streams := streams.push (s!"/Type /XObject /Subtype /Form /BBox {bboxOf kind body} \
/Resources 4 0 R{group}", (Pdf.render body).toUTF8)
      objs := objs.push ""
  for r in fig.rasters do
    let interp := if r.smooth then " /Interpolate true" else ""
    match Image.decode r.bytes with
    | .ok plan =>
      let cs := match plan.color with
        | .gray => "/DeviceGray"
        | _ => "/DeviceRGB"
      let filter := match plan.filter with
        | .flatePredictor => s!"/Filter /FlateDecode /DecodeParms << /Predictor 15 \
/Colors {plan.color.components} /BitsPerComponent {plan.bitDepth} /Columns {plan.pxW} >>"
        | .dct => "/Filter /DCTDecode"
      streams := streams.push (s!"/Type /XObject /Subtype /Image /Width {plan.pxW} \
/Height {plan.pxH} /ColorSpace {cs} /BitsPerComponent {plan.bitDepth}{interp} {filter}", plan.data)
      objs := objs.push ""
    | .error _ =>
      streams := streams.push ("/Type /XObject /Subtype /Image /Width 1 /Height 1 \
/ColorSpace /DeviceGray /BitsPerComponent 8", ⟨#[255]⟩)
      objs := objs.push ""
  -- Objects in id order: four dictionaries, the content (5), then the
  -- resources, a stream wherever `objs` holds an empty placeholder.
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offs : Array Nat := #[]
  let mut si := 0
  let all : Array String := (objs.extract 0 4).push "" ++ objs.extract 4 objs.size
  for (o, i) in all.zipIdx do
    offs := offs.push out.size
    if o.isEmpty then
      let (d, data) := streams[si]?.getD ("", ByteArray.empty)
      si := si + 1
      out := out ++ s!"{i + 1} 0 obj\n<< {d} /Length {data.size} >>\nstream\n".toUTF8 ++ data ++
        "\nendstream\nendobj\n".toUTF8
    else
      out := out ++ s!"{i + 1} 0 obj\n{o}\nendobj\n".toUTF8
  let xref := out.size
  let pad10 (n : Nat) : String :=
    let s := toString n
    String.ofList (List.replicate (10 - s.length) '0') ++ s
  out := out ++ s!"xref\n0 {all.size + 1}\n0000000000 65535 f \n".toUTF8
  for o in offs do
    out := out ++ s!"{pad10 o} 00000 n \n".toUTF8
  out := out ++ s!"trailer\n<< /Size {all.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8
  return out

/-- The figure through the document writer (`Pdf.writeChecked`): one page
the figure's size holding it as a placed ink, its resources the document's
figure table. An empty file when the writer refuses, which `pdftoppm` then
names. -/
def documentPdf (fs : Font.FontSet) (fig : Figure Empty) : ByteArray :=
  let ((x0, y0), (x1, y1)) := fig.box
  let geom : Layout.Geom := { pageW := x1 - x0, pageH := y1 - y0 }
  let ink : Layout.InkOut := { fig, place := { flipY := true, dx := -x0, dy := y1 }, leaf := none }
  match Pdf.writeChecked geom fs #[{ inks := #[ink] }] with
  | .ok b => b
  | .error _ => ByteArray.empty

/-- The writer a figure is judged through: the document writer, or the
harness writer for a figure that paints a raster, which no page's ink
does. -/
def pdfOf (fs : Font.FontSet) (fig : Figure Empty) : ByteArray × String :=
  if fig.imageFree then (documentPdf fs fig, "document") else (figurePdf fig, "harness")

/-! ## The SVG side -/

/-- The figure as a standalone SVG file (`GfxSvg.document`), its rasters
as data URLs. -/
def figureSvg (fig : Figure Empty) : String :=
  let rasters := fig.rasters.map fun r =>
    { href := (if r.jpeg then "data:image/jpeg;base64," else "data:image/png;base64,") ++
        HtmlResource.base64 r.bytes
      smooth := r.smooth : GfxSvg.RasterRef }
  GfxSvg.document (fun _ e => nomatch e) rasters fig

/-! ## Mutants: the SVG side only -/

mutual

-- conserves: none — a test mutant over figure nodes.
def mapNodesOne (f : Node Empty → Node Empty) : Node Empty → Node Empty
  | .group xf clips alpha kids => f (.group xf clips alpha (mapNodesList f #[] kids.toList))
  | n => f n

def mapNodesList (f : Node Empty → Node Empty) (acc : Array (Node Empty)) :
    List (Node Empty) → Array (Node Empty)
  | [] => acc
  | n :: rest => mapNodesList f (acc.push (mapNodesOne f n)) rest

end

def mapNodes (f : Node Empty → Node Empty) (fig : Figure Empty) : Figure Empty :=
  { fig with nodes := mapNodesList f #[] fig.nodes.toList }

def squareCaps : Node Empty → Node Empty
  | .draw g fl st => .draw g fl (st.map fun s => { s with cap := .square })
  | n => n

def dropClips : Node Empty → Node Empty
  | .group xf _ alpha kids => .group xf #[] alpha kids
  | n => n

def ignoreAlpha : Node Empty → Node Empty
  | .group xf clips _ kids => .group xf clips Alpha.opaque kids
  | n => n

/-- SVG's own miter limit of 4 instead of the figure's, the F4 defect. -/
def svgMiterLimit : Node Empty → Node Empty
  | .draw g fl st => .draw g fl (st.map fun s => { s with miterLimit := 4 })
  | n => n

/-- A gradient left in its own frame at the root, the defect the SVG
emitter once had: the figure's y flipped inside the gradient alone. -/
def flipGradients (fig : Figure Empty) : Figure Empty :=
  let ((_, y0), (_, y1)) := fig.box
  let flip (p : Paint) : Paint := match p with
    | .gradient g => .gradient (g.withXf ((⟨1, 0, 0, -1, 0, y0 + y1⟩ : Affine).compose g.xf))
    | .solid c => .solid c
  mapNodes (fun n => match n with
    | .draw g fl st => .draw g (fl.map fun f => { f with paint := flip f.paint }) st
    | n => n) fig

/-- The figure mirrored top to bottom inside its own box. -/
def flipY (fig : Figure Empty) : Figure Empty :=
  let ((_, y0), (_, y1)) := fig.box
  { fig with nodes := #[.group ⟨1, 0, 0, -1, 0, y0 + y1⟩ #[] Alpha.opaque fig.nodes] }

/-- The selftest's figures, each showing its mutant plainly. -/
def mutants : Array (String × Figure Empty × (Figure Empty → Figure Empty)) := #[
  ("butt caps squared", figure 120 80 #[
    .draw (path (pt 40, pt 40) [(pt 80, pt 40)] false) none (some (stroke black (pt 30)))],
    mapNodes squareCaps),
  ("clip dropped", figure 120 80 #[
    .group Affine.unit #[{ geom := .ellipse (pt 60) (pt 40) (pt 15) (pt 15), rule := .nonzero }]
      Alpha.opaque #[.draw (.rect 0 0 (pt 120) (pt 80)) (some (solid blue)) none]],
    mapNodes dropClips),
  ("y flipped", figure 120 80 #[
    .draw (.rect (pt 10) (pt 45) (pt 100) (pt 30)) (some (solid red)) none,
    .draw (.rect (pt 10) (pt 5) (pt 30) (pt 30)) (some (solid blue)) none],
    flipY),
  ("alpha ignored", figure 120 80 #[
    .group Affine.unit #[] (alphaOf 250)
      #[.draw (.rect (pt 10) (pt 10) (pt 100) (pt 60)) (some (solid black)) none]],
    mapNodes ignoreAlpha),
  ("miter limit at SVG's default", figure 120 80 #[
    .draw (path (pt 15, pt 8) [(pt 75, pt 20), (pt 15, pt 32)] false) none
      (some (stroke blue (pt 14))),
    .draw (path (pt 15, pt 48) [(pt 75, pt 60), (pt 15, pt 72)] false) none
      (some (stroke blue (pt 14)))],
    mapNodes svgMiterLimit),
  ("root gradient in its own frame", figure 120 80 #[
    .draw (.rect (pt 10) (pt 10) (pt 100) (pt 60))
      (some { solid red with paint := .gradient (.linear (0, pt 10) (0, pt 70) stops3 Affine.unit) })
      none],
    flipGradients)]

/-! ## Rasters and their distance -/

def tool (cmd : String) (args : Array String) : IO IO.Process.Output := do
  match ← runTool cmd args with
  | some out =>
    if out.exitCode == 0 then return out
    throw (IO.userError s!"gfx-diff: {cmd} exited {out.exitCode}: {out.stderr}")
  | none => throw (IO.userError s!"gfx-diff: {cmd} is not on PATH")

def popplerPng (dir : System.FilePath) (stem : String) (pdf : ByteArray) : IO String := do
  let file := dir / s!"{stem}.pdf"
  IO.FS.writeBinFile file pdf
  let _ ← tool "pdftoppm" #["-r", toString rasterDpi, "-png", "-singlefile", file.toString,
    (dir / s!"{stem}-pdf").toString]
  return (dir / s!"{stem}-pdf.png").toString

def chromePng (chrome : String) (dir : System.FilePath) (stem : String) (fig : Figure Empty)
    (svg : String) : IO String := do
  let file := dir / s!"{stem}.svg"
  IO.FS.writeFile file svg
  let ((x0, y0), (x1, y1)) := fig.box
  let cssPx (d : Sp) : Nat := ((d.toNat * 96 + 72 * 65536 - 1) / (72 * 65536))
  let out := (dir / s!"{stem}-svg.png").toString
  let _ ← tool chrome #["--headless=new", "--disable-gpu", "--no-sandbox", "--hide-scrollbars",
    s!"--force-device-scale-factor={(rasterDpi.toFloat / 96.0)}",
    s!"--window-size={cssPx (x1 - x0)},{cssPx (y1 - y0)}", s!"--screenshot={out}",
    s!"file://{file}"]
  return out

/-- The mean Oklab distance between two rasters at the reference's size,
×100 (ΔE_OK), from their raw RGB samples. -/
def deltaE (dir : System.FilePath) (tag : String) (a b : String) : IO Float := do
  let some geom ← pngGeometry b | throw (IO.userError s!"gfx-diff: no geometry for {b}")
  let ra := dir / s!"{tag}-a.rgb"
  let rb := dir / s!"{tag}-b.rgb"
  let _ ← tool "magick" #[a, "-alpha", "off", "-resize", geom ++ "!", "-depth", "8", s!"rgb:{ra}"]
  let _ ← tool "magick" #[b, "-alpha", "off", "-depth", "8", s!"rgb:{rb}"]
  let da ← IO.FS.readBinFile ra
  let db ← IO.FS.readBinFile rb
  let n := min da.size db.size / 3
  if n == 0 then return 0
  let mut sum : Float := 0
  for i in [0:n] do
    let px (d : ByteArray) (j : Nat) : Ir.Color :=
      { r := d[3 * j]?.getD 0, g := d[3 * j + 1]?.getD 0, b := d[3 * j + 2]?.getD 0 }
    let ca := px da i
    let cb := px db i
    let la := Oklab.labOf ca
    let lb := Oklab.labOf cb
    let d (x y : Int) : Float := (Float.ofInt (x - y)) / 1e18
    let e := Float.sqrt (d la.L lb.L ^ 2 + d la.a lb.a ^ 2 + d la.b lb.b ^ 2)
    sum := sum + e
  return 100 * sum / n.toFloat

structure Measure where
  dssim : Float
  deltaE : Float
  writer : String

def measure (fs : Font.FontSet) (chrome : String) (dir : System.FilePath) (stem : String)
    (pdfFig svgFig : Figure Empty) : IO Measure := do
  let (pdf, writer) := pdfOf fs pdfFig
  let p ← popplerPng dir stem pdf
  let s ← chromePng chrome dir stem svgFig (figureSvg svgFig)
  let some d ← dssimAgainst dir stem s p | throw (IO.userError s!"gfx-diff: no DSSIM for {stem}")
  return { dssim := d, deltaE := ← deltaE dir stem s p, writer }

def fmt (f : Float) : String := (toString f).take 7 |>.toString

end GfxDiff

open GfxDiff in
def main (args : List String) : IO UInt32 := do
  let some (chrome, version) ← findChrome |
    IO.eprintln "gfx-diff: no Chrome (LEANTEX_CHROME or Playwright's cache)"; return 2
  let some fontData ← findFont |
    IO.eprintln "gfx-diff: no shipped test face (testdata/corpus/fonts)"; return 2
  let .ok font := Font.parse fontData |
    IO.eprintln "gfx-diff: the shipped test face does not parse"; return 2
  let fs := oneFaceOf font
  let dir ← IO.FS.createTempDir
  IO.println s!"gfx-diff: {version}; tolerance DSSIM {dssimTolerance} at {dssimScale}, {rasterDpi} dpi"
  let mut failed := 0
  if args.contains "--selftest" then
    for (name, fig, mutate) in mutants do
      let stem := (name.map fun c => if c.isAlphanum then c else '-')
      let base ← measure fs chrome dir s!"{stem}-base" fig fig
      let mutant ← measure fs chrome dir s!"{stem}-mutant" fig (mutate fig)
      let ok := base.dssim ≤ dssimTolerance && mutant.dssim > dssimTolerance
      IO.println s!"{if ok then "caught" else "MISSED"}  {name}: unmutated DSSIM {fmt base.dssim} \
ΔE {fmt base.deltaE}; mutant DSSIM {fmt mutant.dssim} ΔE {fmt mutant.deltaE}"
      unless ok do failed := failed + 1
  else
    for (name, fig) in cases do
      let stem := (name.map fun c => if c.isAlphanum then c else '-')
      let m ← measure fs chrome dir stem fig fig
      let ok := m.dssim ≤ dssimTolerance
      IO.println s!"{if ok then "within" else "ABOVE "}  {name}: DSSIM {fmt m.dssim} ΔE {fmt m.deltaE} \
({m.writer} writer)"
      unless ok do failed := failed + 1
  IO.println s!"gfx-diff: rasters under {dir}"
  return if failed == 0 then 0 else 1
