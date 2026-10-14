module

public import LeanTex.Cli.Driver
public import LeanTex.Core.LayoutFigure
public import LeanTex.Core.FigureStore
public import Tests.Artifact

public section

/-! The native SVG route through the driver's decision and the PDF writer; only the converter is
simulated. -/

namespace Tests

open LeanTex.Core LeanTex.Cli

/-- A figure with a line of sans text and a rotated mono label. -/
def svgTextFixture : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 200 100\" " ++
   "font-family=\"Example Display, sans-serif\">" ++
   "<rect width=\"200\" height=\"100\" fill=\"#eef\"/>" ++
   "<text x=\"100\" y=\"90\" text-anchor=\"middle\" font-size=\"12\">Invented label</text>" ++
   "<text transform=\"translate(10 50) rotate(-90)\" font-family=\"monospace\">axis</text>" ++
   "</svg>").toUTF8

/-- A figure with a filter, which the engine does not draw. -/
def svgFilterFixture : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"40\" height=\"20\">" ++
   "<!-- an authored comment no converter needs -->" ++
   "<filter id=\"blur\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
   "<rect width=\"40\" height=\"20\" fill=\"red\" filter=\"url(#blur)\"/></svg>").toUTF8

mutual

/-- Every content operator onto `acc`, bodies included. -/
def opsOne (acc : Array Pdf.ContentOp) (o : Pdf.ContentOp) : Array Pdf.ContentOp :=
  match o with
  | .marked _ b | .group _ _ _ b | .xobject _ _ _ b => opsList (acc.push o) b.toList
  | .fill .. | .paint .. | .text _ | .image .. | .imageMissing .. | .shade .. | .outline .. =>
    acc.push o

def opsList (acc : Array Pdf.ContentOp) : List Pdf.ContentOp → Array Pdf.ContentOp
  | [] => acc
  | o :: rest => opsList (opsOne acc o) rest

end

def allOps (ops : Array Pdf.ContentOp) : Array Pdf.ContentOp := opsList #[] ops.toList

/-- A drawn SVG is a native form whose text sets in the document's sans face, with no converter
consulted. -/
def svgNativePdfChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let some sansData ← (some <$> IO.FS.readBinFile "testdata/corpus/fonts/FiraSans-Regular.otf")
    | check ref "native SVG PDF: the shipped sans face reads" false
  let .ok sans := Font.parse sansData | check ref "native SVG PDF: the shipped sans face parses" false
  let body := fonts.body
  -- The body in slot 0, the sans in slot 1: a figure's sans text must take slot 1.
  let fs : Font.FontSet :=
    { fonts := #[body, sans],
      index := #[((0, 400, false), 0), ((1, 400, false), 1), ((2, 400, false), 0)] }
  let f ← Driver.svgFetch "chart.svg" svgTextFixture .first "en" none
  check ref "native SVG PDF: the text figure imports exactly, with no diagnostic"
    (f.vector.isSome && f.diags.isEmpty && f.res.toBool)
  let req : Image.Request := { src := "chart.svg" }
  let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some svgTextFixture) none)
  let imgs := FigureStore.attach { entries := #[en] } #[some f.drawn]
  let (imgs, notes) := FigureStore.settle fs imgs
  check ref "native SVG PDF: a missing family falls to its generic, unreported"
    (notes.isEmpty)
  check ref "native SVG PDF: every glyph of the sans text sets in the sans face"
    (match imgs.shaped[0]? with
      | some (some fig) => fig.labels.any fun (_, r) =>
          r.text == "Invented label" && !r.glyphs.isEmpty && r.glyphs.all (·.1 == 1)
      | _ => false)
  let doc := (elabStr "\\includegraphics[width=200pt,alt={An invented chart}]{chart.svg}").1
  let out := layoutOf fs doc (imgs := imgs)
  check ref "native SVG PDF: the page places the drawn figure by its store entry"
    (out.pages.any fun p => p.lines.any fun l => l.segs.any fun s => match s with
      | .image (some 0) _ _ _ => true
      | _ => false)
  let ops := Pdf.pageOps (Layout.Geom.ofPage doc.page) fs out.pages imgs
  let keep := Pdf.keepFaces fs out.pages imgs.shaped
  let sansRes := keep.findIdx? (· == 1)
  let forms := (ops.flatMap allOps).filterMap fun o => match o with
    | .xobject _ _ .symbol body => some body
    | _ => none
  let texts := (forms.flatMap allOps).filterMap fun o => match o with
    | .text tops => some tops
    | _ => none
  check ref "native SVG PDF: the figure is one symbol form" (forms.size ≥ 1)
  check ref "native SVG PDF: the form sets its text in the sans face's resource with TJ"
    (sansRes.isSome && texts.any fun tops =>
      tops.any (fun t => match t with
        | .font res _ => some res == sansRes
        | _ => false) &&
      tops.any (fun t => match t with
        | .show items => !items.isEmpty
        | _ => false))
  check ref "native SVG PDF: the file keeps the sans face for the figure's glyphs" (keep.contains 1)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fs out.pages {} imgs
  check ref "native SVG PDF: the written file names no image XObject for the figure"
    (!bytesContain pdf "/Subtype /Image")

/-- The route a figure takes depends on its import, never on the host alone. -/
def svgRouteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let calls ← IO.mkRef (#[] : Array ByteArray)
  let pdfPlan : Except PicCache.Outcome Image.Plan :=
    (Image.probe svgCanvasPdf >>= Image.plan {}).mapError .inconclusive
  let fake : ByteArray → Bool → IO (Except PicCache.Outcome Image.Plan) := fun b _ => do
    calls.modify (·.push b)
    return pdfPlan
  let failing : ByteArray → Bool → IO (Except PicCache.Outcome Image.Plan) := fun _ _ =>
    return .error (.refused "rsvg-convert exited 1: an invented failure")
  let withTool ← Driver.svgFetch "a.svg" svgTextFixture .first "en" (some (.always fake))
  let without ← Driver.svgFetch "a.svg" svgTextFixture .first "en" none
  check ref "figure route: a lossless figure never calls the converter" ((← calls.get).isEmpty)
  check ref "figure route: a lossless figure ships one drawing with or without the converter"
    ((withTool.vector.map (·.marks)) == (without.vector.map (·.marks)) && withTool.vector.isSome &&
      withTool.diags.isEmpty && without.diags.isEmpty)
  let converted ← Driver.svgFetch "b.svg" svgFilterFixture .first "en" (some (.always fake))
  let sent ← calls.get
  check ref "figure route: a lossy figure asks the converter once" (sent.size == 1)
  check ref "figure route: the converter receives the canonical parse, not the authored bytes"
    (sent.all fun b => b != svgFilterFixture && !bytesContain b "<!--" &&
      (Xml.parse b).toBool)
  check ref "figure route: the converter's drawing ships, the engine's figure stands down"
    (converted.vector.isNone && converted.res.toBool)
  let subjects (ds : Array Diag) := ds.filterMap (·.subject)
  check ref "figure route: the converted figure names its loss as the reason (N0024)"
    (converted.diags.all (·.code == "N0024") &&
      subjects converted.diags == #["figure:svg:property:filter"])
  let degraded ← Driver.svgFetch "b.svg" svgFilterFixture .first "en" none
  check ref "figure route: with no converter the engine's drawing ships, never a placeholder"
    (degraded.vector.isSome && degraded.res.toBool)
  check ref "figure route: with no converter each loss is W0609 under the converted figure's subjects"
    (degraded.diags.all (·.code == "W0609") && subjects degraded.diags == subjects converted.diags)
  let failed ← Driver.svgFetch "b.svg" svgFilterFixture .first "en" (some (.always failing))
  check ref "figure route: a failed conversion ships the engine's drawing with the loss named"
    (failed.vector.isSome && subjects failed.diags == subjects degraded.diags)
  let absent : Driver.Converter := fun _ _ => pure none
  let missing ← Driver.svgFetch "b.svg" svgFilterFixture .first "en" (some absent)
  check ref "figure route: a declared refusal's help says how to lift it, and not to install"
    (!degraded.diags.isEmpty && degraded.diags.all fun d =>
      d.help.any (hasStr · "convert = none") && !(d.help.any (hasStr · "install")))
  check ref "figure route: a missing converter's help says to install it"
    (subjects missing.diags == subjects degraded.diags &&
      missing.diags.all fun d => d.code == "W0609" && d.help.any (hasStr · "install librsvg"))
  check ref "figure route: a failed converter's own words say why"
    (failed.diags.all fun d => d.detail == some "rsvg-convert exited 1: an invented failure")
  check ref "figure route: a converter's verdict offers acceptance, not an install"
    (!failed.diags.isEmpty && failed.diags.all fun d =>
      d.help.any (hasStr · "\\allow{W0609}") && !(d.help.any (hasStr · "install")))
  calls.set #[]
  let refused ← Driver.svgFetch "c.svg" (svgDocument "<script>alert(1)</script>") .first "en" (some (.always fake))
  check ref "figure route: a refused figure never reaches the converter"
    ((← calls.get).isEmpty && !refused.res.toBool && refused.vector.isNone)
  check ref "figure route: the refusal names the boundary"
    (match refused.res with
      | .error e => hasStr e "SVG resource boundary"
      | .ok _ => false)


/-- A figure whose text forms paint: a translucent caption, a caption in a translucent group, and a
caption a `use` paints. -/
def svgFormTextFixture : ByteArray :=
  ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"300\" height=\"120\" viewBox=\"0 0 300 120\">" ++
   "<rect width=\"300\" height=\"120\" fill=\"#ffffff\"/>" ++
   "<text x=\"10\" y=\"20\" font-size=\"14\" opacity=\"0.6\">Half-seen caption</text>" ++
   "<g opacity=\"0.5\"><rect x=\"10\" y=\"40\" width=\"20\" height=\"20\" fill=\"blue\"/>" ++
   "<text x=\"40\" y=\"55\" font-size=\"14\">Beside a faded square</text></g>" ++
   "<defs><g id=\"tag\"><text x=\"0\" y=\"0\" font-size=\"14\">Inside a reused group</text></g></defs>" ++
   "<use href=\"#tag\" x=\"10\" y=\"95\"/></svg>").toUTF8

/-- Every glyph a figure's form paints stands inside the form's box, read off the written file. -/
def svgFormTextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let f ← Driver.svgFetch "captions.svg" svgFormTextFixture .first "en" none
  check ref "form text: the captions figure imports exactly" (f.vector.isSome && f.diags.isEmpty)
  let req : Image.Request := { src := "captions.svg" }
  let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some svgFormTextFixture) none)
  let imgs := FigureStore.attach { entries := #[en] } #[some f.drawn]
  let imgs := (FigureStore.settle fonts imgs).1
  let doc := (elabStr "\\includegraphics[width=300pt,alt={Three invented captions}]{captions.svg}").1
  let out := layoutOf fonts doc (imgs := imgs)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages {} imgs
  match formGlyphOffences pdf fonts with
  | .error e => check ref s!"form text: the file's forms read back: {e}" false
  | .ok (seen, offences) =>
    check ref s!"form text: every caption glyph is read ({seen})" (seen ≥ 50)
    check ref s!"form text: every glyph stands inside its form's box: {offences.toList.take 3}"
      offences.isEmpty
  -- The judge breaks once: the same file with every form's box emptied clips every glyph.
  match formGlyphOffences pdf fonts (fun _ => #[0, 0, 0, 0]) with
  | .ok (seen, offences) =>
    check ref "form text: an emptied box is an offence for every glyph" (seen ≥ 50 && offences.size == seen)
  | .error e => check ref s!"form text: the emptied file reads back: {e}" false

/-- The host is asked for the converter only when a figure needs it, and once. -/
def svgConverterProbeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let probes ← IO.mkRef 0
  let probe : IO Bool := do
    probes.modify (· + 1)
    return true
  let pdfPlan : Except PicCache.Outcome Image.Plan :=
    (Image.probe svgCanvasPdf >>= Image.plan {}).mapError .inconclusive
  let some convert ← Driver.svgConverterWith probe (fun _ _ => return pdfPlan) true
    | check ref "converter probe: an allowed converter is offered" false
  for _ in [0:3] do
    let _ ← Driver.svgFetch "a.svg" svgTextFixture .first "en" (some convert)
  check ref "converter probe: figures drawn whole never probe the host" ((← probes.get) == 0)
  let _ ← Driver.svgFetch "b.svg" svgFilterFixture .first "en" (some convert)
  let _ ← Driver.svgFetch "c.svg" svgFilterFixture .first "en" (some convert)
  check ref "converter probe: lossy figures probe the host once" ((← probes.get) == 1)
  check ref "converter probe: a refusing document offers no converter"
    ((← Driver.svgConverterWith probe (fun _ _ => return pdfPlan) false).isNone && (← probes.get) == 1)

/-- A character no face covers is a figure loss (W0609), never an error. -/
def svgGlyphGapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let bytes := svgDocument "<text x=\"1\" y=\"10\" font-family=\"sans-serif\">Gap 漢</text>" 60 20
  let doc := (elabStr "\\includegraphics[alt={An invented gap}]{gap.svg}").1
  let req := (Ir.imageRequests doc)[0]!
  let f ← Driver.svgFetch "gap.svg" bytes .first "en" none
  let (store, _) := Image.fulfilRequests #[(req, .decoded "" f.res (some bytes) none (some bytes) none)]
  let store := FigureStore.attach store #[some f.drawn]
  let (_, notes) := Layout.shapeStoreNotesBy fonts store
  let ds := notes.map (·.2)
  check ref s!"SVG glyph gap: the uncovered character is one W0609 under the figure ({ds.map (·.code)})"
    (ds.any fun d => d.code == "W0609" && d.subject == some "figure:svg:font:U+6F22")
  check ref "SVG glyph gap: no error stops the build" (ds.all (·.severity != .error))

/-- A link a figure holds is named once (N0027), whichever route draws the figure. -/
def svgLinkNoteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let bytes := svgDocument ("<rect id=\"x\" width=\"1\" height=\"1\"/>" ++
    "<a href=\"#x\"><rect width=\"9\" height=\"9\" fill=\"red\"/></a>" ++
    "<a href=\"#x\"><rect x=\"10\" width=\"9\" height=\"9\"/></a>")
  let f ← Driver.svgFetch "figures/linked.svg" bytes .first "en" none
  check ref "SVG link note: the figure draws its links' content natively"
    (f.vector.any fun v => v.losses.isEmpty && v.marks.size == 3)
  check ref s!"SVG link note: one N0027 names the links, under its subject ({f.diags.map (·.code)})"
    (f.diags.map (·.code) == #["N0027"] &&
      f.diags.all (·.subject == some "figure:svg:note:a link"))

/-- `\figures{ convert = none }` is the converter's declared refusal: open by default, and nothing
else accepted. -/
def figuresDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref "figures declaration: the converter door is open by default"
    (elabStr "x").1.figureConvert
  let (doc, ds) := elabStr (dvDoc "\\figures{ convert = none }\n" "x")
  check ref "figures declaration: convert = none refuses the converter"
    (!doc.figureConvert && !(ds.any (·.severity == .error)))
  for conv in ["rsvg-convert", "pdftocairo"] do
    let (doc, ds) := elabStr (dvDoc s!"\\figures\{ convert = {conv} }\n" "x")
    check ref s!"figures declaration: the pinned converter {conv} keeps the door open"
      (doc.figureConvert && !(ds.any (·.severity == .error)))
  let (_, ds) := elabStr (dvDoc "\\figures{ convert = magick }\n" "x")
  check ref "figures declaration: an unpinned converter is refused by name"
    (ds.any fun d => d.code == "E0321" && hasStr d.message "magick")
  let (_, ds) := elabStr (dvDoc "\\figures{ colour = none }\n" "x")
  check ref "figures declaration: an unknown key is named" (ds.any fun d => hasStr d.message "colour")


/-- A family the document's roles do not answer is set in the sans face and named once (N0026). -/
def svgFontMatchChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let figure (family : String) : ByteArray :=
    (s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"60\" height=\"20\">" ++
     s!"<text x=\"2\" y=\"15\" font-family=\"{family}\">Label</text>" ++
     s!"<text x=\"30\" y=\"15\" font-family=\"{family}\">Again</text></svg>").toUTF8
  let shapedWith (bytes : ByteArray) : IO (Option (Gfx.Figure Gfx.Shaped) × Array Diag) := do
    let f ← Driver.svgFetch "f.svg" bytes .first "en" none
    let req : Image.Request := { src := "f.svg" }
    let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some bytes) none)
    let (imgs, ds) := FigureStore.settle fonts
      (FigureStore.attach { entries := #[en] } #[some f.drawn])
    return ((imgs.shaped[0]?).join, ds.map (·.2))
  let faces (fig : Option (Gfx.Figure Gfx.Shaped)) : Array Nat :=
    (fig.map fun f => f.labels.flatMap fun (_, r) => r.glyphs.map (·.1)).getD #[]
  let (named, namedDs) ← shapedWith (figure "Example Grotesk")
  let (generic, genericDs) ← shapedWith (figure "sans-serif")
  let own := (fonts.get (fonts.lookup 1 400 false)).family
  let (role, roleDs) ← shapedWith (figure own)
  check ref "svg font match: an unanswered family is reported once, by its subject"
    (namedDs.size == 1 && namedDs.all fun d =>
      d.code == "N0026" && d.subject == some "svg:font:Example Grotesk")
  check ref "svg font match: a generic family and the role's own family report nothing"
    (genericDs.isEmpty && roleDs.isEmpty)
  check ref "svg font match: the three spellings set the same faces"
    (faces named == faces generic && faces generic == faces role && !(faces named).isEmpty)

/-- The XObject names a content stream invokes (`/Name Do`). -/
def doNames (content : ByteArray) : Array String := Id.run do
  let toks := scanContent content
  let mut out : Array String := #[]
  let mut last : Option String := none
  for t in toks do
    match t with
    | .name n => last := some n
    | .op o =>
      if o == "Do" then
        if let some n := last then out := out.push n
      last := none
    | _ => last := none
  return out

/-- Every XObject a file's forms and pages invoke that their resources do not name. -/
def danglingXObjects (pdf : ByteArray) : Except String (Array String) := do
  let es := (← PdfRead.objects pdf).val
  let deref := PdfCensus.deref es
  let mut out : Array String := #[]
  for e in es do
    let isForm := e.val.get? "Subtype" == some (.name "Form")
    let isPage := e.val.get? "Type" == some (.name "Page")
    unless isForm || isPage do continue
    let names : Array String := match deref ((deref ((e.val.get? "Resources").getD .null)).get? "XObject" |>.getD .null) with
      | .dict xs => xs.map (·.1)
      | _ => #[]
    let content ← if isForm then
        match e.decoded with
        | .ok (some d) => pure d
        | _ => throw "a form does not decode"
      else
        match e.val.get? "Contents" with
        | some (.ref n _) =>
          match es.find? (·.num == n) with
          | some c => match c.decoded with
            | .ok (some d) => pure d
            | _ => throw "a page's content does not decode"
          | none => throw "a page names no content"
        | _ => pure ByteArray.empty
    for n in doNames content do
      unless names.contains n do out := out.push n
  return out

/-- A file's image XObjects by width, height and smoothing, and every name a form's content
invokes. -/
def imagesAndFormNames (pdf : ByteArray) : Except String (Array (Nat × Nat × Bool) × Array String) := do
  let es := (← PdfRead.objects pdf).val
  let mut imgs : Array (Nat × Nat × Bool) := #[]
  let mut names : Array String := #[]
  for e in es do
    if e.val.get? "Subtype" == some (.name "Image") then
      let smooth := e.val.get? "Interpolate" == some (.bool true)
      match e.val.get? "Width", e.val.get? "Height" with
      | some (.int w), some (.int h) => imgs := imgs.push (w.toNat, h.toNat, smooth)
      | _, _ => imgs := imgs.push (0, 0, smooth)
    if e.val.get? "Subtype" == some (.name "Form") then
      match e.decoded with
      | .ok (some d) => names := names ++ doNames d
      | _ => pure ()
  return (imgs, names)

/-- A figure's raster is drawn in its own form, as a page's image is. -/
def svgRasterFigureChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let figure (png : String) : ByteArray := svgDocument (width := 40) (height := 40)
    ("<rect width=\"40\" height=\"40\" fill=\"#dddddd\"/>" ++
     s!"<image href=\"data:image/png;base64,{png}\" x=\"5\" y=\"5\" width=\"30\" height=\"30\"/>")
  let bytes := figure (HtmlResource.base64 tinyPng)
  let f ← Driver.svgFetch "raster.svg" bytes .first "en" none
  check ref "raster figure: the import is exact, its raster planned"
    ((f.vector.map fun v => v.rasters.size == 1 && v.losses.isEmpty && !v.marks.isEmpty).getD false &&
      f.plans.size == 1 && f.diags.isEmpty)
  let req : Image.Request := { src := "raster.svg" }
  let (en, _) := Image.fulfilOne req (.decoded "" f.res (some bytes) none (some bytes) none)
  let attached := FigureStore.attach { entries := #[en] } #[some f.drawn]
  check ref "raster figure: the raster's entry follows the request's, owned by the figure"
    (attached.entries.size == 2 && (attached.get? 0).map (·.rasterSlots) == some #[1] &&
      ((attached.get? 1).bind (·.rasterOf)) == some 0 &&
      ((attached.get? 1).bind (·.info)).isSome)
  let imgs := (FigureStore.settle fonts attached).1
  let doc := (elabStr "\\includegraphics[width=80pt,alt={An invented raster figure}]{raster.svg}").1
  let out := layoutOf fonts doc (imgs := imgs)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages {} imgs
  check ref "raster figure: every XObject the file invokes, its resources name"
    (danglingXObjects pdf == .ok #[])
  check ref "raster figure: one image of the PNG's size, smoothed, painted by the figure's form"
    (match imagesAndFormNames pdf with
     | .ok (ims, names) => ims == #[(1, 1, true)] && names.contains "Ri2"
     | .error _ => false)
  let crisp := svgDocument (width := 40) (height := 40)
    (s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" width=\"40\" height=\"40\" " ++
     "image-rendering=\"pixelated\"/>")
  let cf ← Driver.svgFetch "crisp.svg" crisp .first "en" none
  let (cen, _) := Image.fulfilOne { src := "crisp.svg" } (.decoded "" cf.res (some crisp) none (some crisp) none)
  let cimgs := (FigureStore.settle fonts (FigureStore.attach { entries := #[cen] } #[some cf.drawn])).1
  let cdoc := (elabStr "\\includegraphics[width=80pt,alt={An invented crisp raster}]{crisp.svg}").1
  let cpdf := Pdf.write (Layout.Geom.ofPage cdoc.page) fonts (layoutOf fonts cdoc (imgs := cimgs)).pages {} cimgs
  check ref "raster figure: a pixelated raster is not smoothed"
    (match imagesAndFormNames cpdf with
     | .ok (ims, _) => ims == #[(1, 1, false)]
     | .error _ => false)
  let unslotted := (FigureStore.settle fonts
    (FigureStore.attach { entries := #[en] } #[some { f.drawn with plans := #[] }])).1
  let updf := Pdf.write (Layout.Geom.ofPage doc.page) fonts (layoutOf fonts doc (imgs := unslotted)).pages {}
    unslotted
  check ref "raster figure: a raster with no entry is not drawn, and nothing dangles"
    (danglingXObjects updf == .ok #[] &&
      (match imagesAndFormNames updf with
       | .ok (ims, names) => ims.isEmpty && !names.any (·.startsWith "Ri")
       | .error _ => false))
  let (_, body, _) := HtmlDoc.emitTree { imgs } doc
  check ref "raster figure: the page keeps the authored bytes in an image"
    ((elemAttrsList (· == "img") #[] body.toList).size == 1 &&
      (elemAttrsList (· == "svg") #[] body.toList).isEmpty)
  check ref "raster figure: the raster's entry ships no asset; the figure's file carries it"
    ((HtmlDoc.imageAssets imgs).size == 1 &&
      (HtmlDoc.imageResources imgs).map (·.bytes) == #[bytes] &&
      hasStr (String.fromUTF8! bytes) (HtmlResource.base64 tinyPng))
  -- The tiny PNG made interlaced (its header's last byte and checksum), which the planner refuses.
  let interlaced := ((tinyPng.set! 28 1).set! 29 0xE7 |>.set! 30 0x70 |>.set! 31 0x63).set! 32 0x48
  check ref "raster figure: the interlaced PNG probes and does not plan"
    ((Image.probe interlaced).toBool && !(Image.decode interlaced).toBool)
  let refused ← Driver.svgFetch "broken.svg" (figure (HtmlResource.base64 interlaced)) .first "en" none
  check ref "raster figure: a raster the planner refuses is dropped, the drop named"
    ((refused.vector.map fun v => v.rasters.isEmpty && v.losses.contains FigureLoss.rasterLoss &&
        !v.marks.isEmpty).getD false && refused.plans.isEmpty &&
      refused.diags.any fun d => d.code == "W0609" &&
        d.subject == some (FigureLoss.subject "svg" FigureLoss.rasterLoss))
  for (name, img) in [("no reference", "<image width=\"4\" height=\"4\"/>"),
      ("a data source and no reference", "<image src=\"data:image/png;base64," ++
        HtmlResource.base64 tinyPng ++ "\" width=\"4\" height=\"4\"/>")] do
    let f ← Driver.svgFetch "nothing.svg" (svgDocument ("<rect width=\"2\" height=\"2\"/>" ++ img))
      .first "en" none
    check ref s!"raster figure: an image with {name} draws nothing and names no loss ({f.diags.map (·.code)})"
      ((f.vector.map fun v => v.losses.isEmpty && v.rasters.isEmpty).getD false && f.diags.isEmpty)

end Tests
