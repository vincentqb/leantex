module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # Images

The image blocks, one file per the by-phase split: the probe and the
planner, the alpha split, colour-key transparency, and the plan's own
contract (`planChecks`). -/

/-- The colour-key ranges a plan carries, empty when none. -/
def planKey (pl : Image.Plan) : Array Nat :=
  match pl.alpha with
  | .colorKey ks => ks
  | .opaque => #[]
  | .soft _ _ => #[]

/-- The soft-mask plane a plan carries, empty when none. -/
def planSoft (pl : Image.Plan) : ByteArray :=
  match pl.alpha with
  | .soft plane _ => plane
  | .opaque => ByteArray.empty
  | .colorKey _ => ByteArray.empty

/-- The palette an indexed plan carries, empty otherwise. -/
def planPalette (pl : Image.Plan) : ByteArray :=
  match pl.color with
  | .indexed pal => pal
  | .gray => ByteArray.empty
  | .rgb => ByteArray.empty
  | .iccBased _ _ => ByteArray.empty

/-- `splitPredictedAlpha_exact`, executed: over seeded random pixels with a
random filter type per row, for grey+alpha and RGBA at several geometries
(one-pixel rows, one-row images, wide rows), unfiltering the two residual
planes equals projecting the unfiltered pixels, and the split keeps every
row's filter byte. Alongside, the unfilter inverts the forward filter of
every type. -/
def alphaSplitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut s : UInt64 := 0x2545F4914F6CDD1D
  let mut n := 0
  let mut allExact := true
  let mut allKeepFilter := true
  let mut allInvert := true
  let mut sawFilter : Array Bool := Array.replicate 5 false
  for (pxH, w, chs) in [(1, 1, 4), (1, 1, 2), (1, 7, 4), (3, 1, 2), (2, 2, 4), (5, 9, 4),
      (4, 6, 2), (7, 3, 4)] do
    for _ in [0:6] do
      let rowBytes := w * chs
      let mut px := ByteArray.emptyWithCapacity (pxH * rowBytes)
      for _ in [0:pxH * rowBytes] do
        let (v, s') := rand s 256
        s := s'
        px := px.push (UInt8.ofNat v)
      let mut fts : Array Nat := #[]
      for _ in [0:pxH] do
        let (f, s') := rand s 5
        s := s'
        fts := fts.push f
        sawFilter := sawFilter.setIfInBounds f true
      let ft (r : Nat) : Nat := fts[r]?.getD 0
      let raw := pngFilter px pxH rowBytes chs ft
      unless Flate.pngUnfilter raw pxH rowBytes chs == .ok px do allInvert := false
      let (color, alpha) := Image.splitPredictedAlpha raw pxH w chs
      let (colorPx, alphaPx) := Image.splitAlpha px chs
      unless Flate.pngUnfilter color pxH (w * (chs - 1)) (chs - 1) == .ok colorPx &&
          Flate.pngUnfilter alpha pxH w 1 == .ok alphaPx do allExact := false
      for r in [0:pxH] do
        unless color[r * (1 + w * (chs - 1))]? == some (UInt8.ofNat (ft r)) &&
            alpha[r * (1 + w)]? == some (UInt8.ofNat (ft r)) do allKeepFilter := false
      n := n + 1
  t s!"residual split unfilters to the pixel projections ({n} cases)" allExact
  t "residual split keeps every row's filter byte" allKeepFilter
  t "pngUnfilter inverts the forward filter of every type" allInvert
  t "the random rows exercised all five filter types" (sawFilter.all id)

/-- Images: the decoders' verdicts over synthetic bytes and the shipped
fixtures, the sizing contract on placed pages, the placeholder path, the PDF
embedding, and the HTML emit. Decoder totality over truncations and random
bytes is fuzzed deeper in `scripts/img-fuzz.lean` (an oracle, not a
theorem). -/
def imageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Synthetic PNGs through the shared synthesizer (Tests/Support).
  let chunk := pngChunk
  let ihdr := pngIhdr
  let plain := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++ chunk "IDAT" [1, 2, 3] ++
    chunk "IEND" [])
  match Image.decode plain with
  | .error e => failures ref s!"png decode: {e}"
  | .ok inf =>
    t "png dimensions" (inf.pxW == 64 && inf.pxH == 40)
    t "png default density is one pixel per point"
      (inf.dpiX == 72 && inf.width == Dim.pt 64 && inf.height == Dim.pt 40)
    t "png space and depth" (inf.color == .rgb && inf.bitDepth == 8)
    t "png idat survives" (inf.data == bytes [1, 2, 3])
  -- pHYs at 5906 pixels per metre is 150 dpi to the spec's own rounding.
  let physed := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++
    chunk "pHYs" (be32 5906 ++ be32 5906 ++ [1]) ++ chunk "IDAT" [0] ++ chunk "IEND" [])
  t "png pHYs density read"
    (match Image.decode physed with
     | .ok inf => inf.dpiX == 150 && inf.width == Dim.pt 64 * 72 / 150
     | .error _ => false)
  -- Refusals and the decode path, each with its reason: 16-bit alpha and
  -- interlace refuse; 8-bit alpha inflates and splits its filtered rows —
  -- never its pixels — and the alpha plane comes back as an SMask.
  t "png 16-bit alpha refused"
    (match Image.decode (mkPng (chunk "IHDR" (ihdr 8 8 16 6 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "16-bit").length == 2
     | .ok _ => false)
  -- 2×2 RGBA, row 0 filter None, row 1 filter Sub: known planes out.
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++
    [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
    chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" [])
  t "png alpha decodes to colour plus smask, planes filtered and compressed"
    (match Image.decode rgbaPng with
     | .ok inf =>
       inf.color == .rgb && inf.filter == .flatePredictor && !(planSoft inf).isEmpty &&
       ((Flate.inflate inf.data 14).bind fun rows =>
         Flate.pngUnfilter rows 2 6 3) ==
         .ok (bytes [10, 20, 30, 40, 50, 60, 5, 5, 5, 6, 7, 8]) &&
       ((Flate.inflate (planSoft inf) 6).bind fun rows =>
         Flate.pngUnfilter rows 2 2 1) == .ok (bytes [255, 128, 7, 16])
     | .error _ => false)
  -- The planes are the source's residuals under the source's own filters
  -- (None, then Sub), not a re-filtering: the split never saw a pixel.
  t "png alpha planes keep the source rows' filter bytes"
    (match Image.decode rgbaPng with
     | .ok inf =>
       Flate.inflate inf.data 14 == .ok (bytes [0, 10, 20, 30, 40, 50, 60, 1, 5, 5, 5, 1, 2, 3]) &&
       Flate.inflate (planSoft inf) 6 == .ok (bytes [0, 255, 128, 1, 7, 9])
     | .error _ => false)
  -- The inflate under it round-trips its own stored encoder, and reads a
  -- real compressor's stream: rects.png's IDAT is zlib at level 9, and its
  -- unfiltered scanlines are 40 rows of 1+192 bytes.
  t "flate roundtrip on stored blocks"
    (Flate.inflate (Flate.deflateStored rgbaRaw) rgbaRaw.size == .ok rgbaRaw)
  -- The real compressor: `inflate_deflate_id`'s statement, witnessed on
  -- the shapes a block must survive — empty, tiny, a run, a period-3
  -- repetition, text, and the raw plane above (`scripts/flate-fuzz.lean`
  -- is the deep oracle, with a foreign inflater as second judge).
  let rt (b : ByteArray) : Bool := Flate.inflate (Flate.deflate b) b.size == .ok b
  t "deflate roundtrip: empty" (rt ByteArray.empty)
  t "deflate roundtrip: one byte" (rt (bytes [42]))
  t "deflate roundtrip: a run" (rt (ByteArray.mk (Array.replicate 70000 7)))
  t "deflate roundtrip: period 3"
    (rt (ByteArray.mk (Array.ofFn (n := 999) fun i => UInt8.ofNat (i.val % 3))))
  t "deflate roundtrip: text"
    (rt "pack my box with five dozen liquor jugs, again and again and again".toUTF8)
  t "deflate roundtrip: the raw plane" (rt rgbaRaw)
  t "deflate really compresses a run"
    ((Flate.deflate (ByteArray.mk (Array.replicate 70000 7))).size < 1000)
  -- A deflate-compressed IDAT decodes through the dynamic-Huffman path:
  -- the engine reads its own compressor's output inside a PNG too.
  t "png alpha decodes from a deflate-compressed IDAT"
    (match Image.decode (mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
      chunk "IDAT" (Flate.deflate rgbaRaw).toList ++ chunk "IEND" [])) with
     | .ok inf => inf.color == .rgb && !(planSoft inf).isEmpty
     | .error _ => false)
  -- The driver's image-cache serialization inverts exactly
  -- (`decodeBin_encodeBin_id`'s statement, witnessed on a real decode).
  t "image cache serialization round-trips a decoded alpha png"
    (match Image.decode rgbaPng with
     | .ok inf =>
       (match Image.decodeBin (Image.encodeBin inf) with
        | some back =>
          back.pxW == inf.pxW && back.pxH == inf.pxH &&
          back.dpiX == inf.dpiX && back.dpiY == inf.dpiY &&
          back.bitDepth == inf.bitDepth && back.color == inf.color &&
          back.data == inf.data && back.filter == inf.filter && back.alpha == inf.alpha &&
          back.recoded == inf.recoded && back.losses == inf.losses &&
          back.orientation == inf.orientation && back.form.isNone
        | none => false)
     | .error _ => false)
  t "image cache decode rejects foreign bytes"
    ((Image.decodeBin (bytes [1, 2, 3])).isNone &&
     (Image.decodeBin ByteArray.empty).isNone)
  t "image cache decode rejects a truncated entry"
    (match Image.decode rgbaPng with
     | .ok inf =>
       let blob := Image.encodeBin inf
       (Image.decodeBin (blob.extract 0 (blob.size - 1))).isNone
     | .error _ => false)
  t "png interlace refused"
    (match Image.decode (mkPng (chunk "IHDR" (ihdr 8 8 8 2 1) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "interlaced").length == 2
     | .ok _ => false)
  t "png indexed without PLTE refused"
    ((Image.decode (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png indexed with PLTE carries the palette"
    (match Image.decode (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "PLTE" [0, 0, 0, 255, 255, 255] ++ chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .ok inf => (planPalette inf).size == 6 && inf.color == .indexed (planPalette inf)
     | .error _ => false)
  t "png zero size refused"
    ((Image.decode (mkPng (chunk "IHDR" (ihdr 0 8 8 2 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png lying chunk length refused"
    ((Image.decode (mkPng (chunk "IHDR" (ihdr 8 8 8 2 0) ++
      be32 99999 ++ ("IDAT".toList.map fun c => UInt8.ofNat c.toNat) ++ [0]))).isOk
      == false)
  -- A synthetic JPEG: SOI, JFIF APP0 declaring 144 dpi, SOF0 10×20 in three
  -- components, SOS. The scan data never has to exist for the header walk.
  let jfif (unit dx dy : Nat) : List UInt8 :=
    [0xFF, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, UInt8.ofNat unit,
     UInt8.ofNat (dx / 256), UInt8.ofNat (dx % 256),
     UInt8.ofNat (dy / 256), UInt8.ofNat (dy % 256), 0, 0]
  let sof0 (w h ncomp : Nat) : List UInt8 :=
    [0xFF, 0xC0, 0, UInt8.ofNat (8 + 3 * ncomp), 8,
     UInt8.ofNat (h / 256), UInt8.ofNat (h % 256),
     UInt8.ofNat (w / 256), UInt8.ofNat (w % 256), UInt8.ofNat ncomp] ++
     (List.range ncomp).flatMap fun k => [UInt8.ofNat (k + 1), 0x11, 0]
  let jpg := bytes ([0xFF, 0xD8] ++ jfif 1 144 144 ++ sof0 10 20 3 ++ [0xFF, 0xDA])
  match Image.decode jpg with
  | .error e => failures ref s!"jpeg decode: {e}"
  | .ok inf =>
    t "jpeg dimensions" (inf.pxW == 10 && inf.pxH == 20)
    t "jpeg jfif density read" (inf.dpiX == 144 && inf.width == Dim.pt 10 * 72 / 144)
    t "jpeg embeds whole" (inf.data.size == jpg.size)
  t "jpeg cmyk refused"
    (match Image.decode (bytes ([0xFF, 0xD8] ++ sof0 4 4 4 ++ [0xFF, 0xDA])) with
     | .error e => (e.splitOn "CMYK").length == 2
     | .ok _ => false)
  t "jpeg aspect-only density keeps the default"
    (match Image.decode (bytes ([0xFF, 0xD8] ++ jfif 0 1 1 ++ sof0 4 4 1 ++
      [0xFF, 0xDA])) with
     | .ok inf => inf.dpiX == 72 && inf.color == .gray
     | .error _ => false)
  t "decode rejects foreign bytes" ((Image.decode (bytes [0, 1, 2, 3])).isOk == false)
  t "decode rejects empty" ((Image.decode (bytes [])).isOk == false)

  -- The shipped fixtures: what `lake test` sees on every host.
  let pngData ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let jpgData ← IO.FS.readBinFile "testdata/corpus/rects.jpg"
  let alphaData ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  let pngInfo := Image.decode pngData
  let jpgInfo := Image.decode jpgData
  let alphaInfo := Image.decode alphaData
  t "shipped png decodes 64x40 rgb"
    (match pngInfo with
     | .ok inf => inf.filter == .flatePredictor && inf.pxW == 64 && inf.pxH == 40 &&
        inf.color == .rgb && inf.width == Dim.pt 64
     | .error _ => false)
  t "shipped jpeg decodes 64x40"
    (match jpgInfo with
     | .ok inf => inf.filter == .dct && inf.pxW == 64 && inf.pxH == 40 &&
        inf.width == Dim.pt 64
     | .error _ => false)
  -- The RGBA fixture went through a real compressor (zlib level 9), so
  -- decoding it exercises the Huffman paths of the inflater; its alpha
  -- fades 255 down to 15 across the rectangle and vanishes outside it.
  t "shipped alpha png decodes with its mask"
    (match alphaInfo with
     | .ok inf =>
       inf.pxW == 48 && inf.pxH == 32 && inf.color == .rgb && !(planSoft inf).isEmpty &&
       (match (Flate.inflate (planSoft inf) (32 * 49)).bind fun rows =>
          Flate.pngUnfilter rows 32 48 1 with
        | .ok mask => mask.size == 48 * 32 && mask[0]?.getD 1 == 0 &&
            (mask[4 * 48 + 4]?.getD 0) == 255 && (mask[4 * 48 + 43]?.getD 0) == 21
        | .error _ => false)
     | .error _ => false)
  -- Totality over truncations of both, as for fonts: reaching the count is
  -- the property — a panic would take the run down.
  t "png decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (pngData.extract 0 (pngData.size * k / 64))).isOk).length == 64)
  t "jpeg decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (jpgData.extract 0 (jpgData.size * k / 64))).isOk).length == 64)

  let store : Image.Store := { entries := #[
    { src := "rects.png", source := some pngData, info := pngInfo.toOption },
    { src := "rects.jpg", source := some jpgData, info := jpgInfo.toOption },
    { src := "rects-alpha.png", source := some alphaData, info := alphaInfo.toOption }] }
  let geom : Layout.Geom := {}
  let imageSegs (out : Layout.Out) : Array (Option Nat × Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Option Nat × Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        for s in l.segs do
          if let .image idx w h := s then acc := acc.push (idx, w, h)
    return acc
  let layoutSrc (src : String) : Layout.Out :=
    let (doc, _) := Elab.run "t" src
    layoutOf oneFace doc geom none store

  -- Intrinsic: no keys, the box is the file's physical size.
  let outIntrinsic := layoutSrc "\\includegraphics{rects.png}"
  t "layout intrinsic size"
    (imageSegs outIntrinsic == #[(some 0, Dim.pt 64, Dim.pt 40)])
  -- `width = 0.8\textwidth`: the spelling every deck sizes a figure with.
  let outTw := layoutSrc "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let expectW := geom.textWidth * 800 / 1000
  t "layout width fraction of the measure"
    (imageSegs outTw == #[(some 0, expectW, expectW * Dim.pt 40 / Dim.pt 64)])
  let affineSrc := "\\includegraphics[width=0.334\\dimexpr \\textwidth +28mm\\relax]{rects.png}"
  let outAffine := layoutSrc affineSrc
  let affineW := ((geom.textWidth + Dim.mm 28) * 334).tdiv 1000
  t "layout resolves an affine image width against the local measure"
    (imageSegs outAffine == #[(some 0, affineW, affineW * Dim.pt 40 / Dim.pt 64)])
  t "an affine image width emits no length error"
    (!(errCodes affineSrc).contains "E0331")
  let localSrc := "\\begin{minipage}{0.5\\textwidth}" ++
    "\\includegraphics[width=0.5\\dimexpr \\linewidth +10pt\\relax]{rects.png}" ++
    "\\end{minipage}"
  let localW := ((geom.textWidth / 2 + Dim.pt 10) * 1).tdiv 2
  t "linewidth resolves inside its minipage rather than against the page"
    (imageSegs (layoutSrc localSrc) ==
      #[(some 0, localW, localW * Dim.pt 40 / Dim.pt 64)])
  -- Both dimensions declared win exactly.
  let outBoth := layoutSrc "\\includegraphics[width=32pt, height=40pt]{rects.png}"
  t "layout declared size wins"
    (imageSegs outBoth == #[(some 0, Dim.pt 32, Dim.pt 40)])
  -- keepaspectratio fits inside the declared box: width binds (the image is
  -- wider than tall), the height follows the intrinsic ratio.
  let outKeep :=
    layoutSrc "\\includegraphics[width=32pt, height=32pt, keepaspectratio]{rects.jpg}"
  t "layout keepaspect fits the box"
    (imageSegs outKeep == #[(some 1, Dim.pt 32, Dim.pt 32 * 40 / 64)])
  -- The mirror bound, in the poster's own spelling: with `width` and
  -- `totalheight` both given, `keepaspectratio` takes the smaller of the
  -- two scales so neither bound is exceeded (graphicx.sty, the `Gin@iso`
  -- branch of `\Gin@req@sizes`; `resolveSize_keepAspect_fits` is the
  -- engine's statement). Here the height is the binding bound: the width
  -- follows the intrinsic ratio, never the declared 60pt.
  let outKeepH :=
    layoutSrc "\\includegraphics[width=60pt, totalheight=20pt, keepaspectratio]{rects.jpg}"
  t "layout keepaspect picks the binding bound"
    (imageSegs outKeepH == #[(some 1, Dim.pt 20 * 64 / 40, Dim.pt 20)])
  -- A source the store has no entry for is a placeholder box: the document
  -- still compiles, at the requested size.
  let outMissing := layoutSrc "\\includegraphics[width=50pt]{missing.png}"
  t "layout missing image keeps requested width"
    (imageSegs outMissing == #[(none, Dim.pt 50, Dim.pt 50)] &&
     outMissing.pages.size == 1)
  t "layout missing image without a size is an inch square"
    (imageSegs (layoutSrc "\\includegraphics{missing.png}") ==
      #[(none, Dim.inch 1, Dim.inch 1)])

  -- The figure environment: a float standing where written, the caption on
  -- its source side (below here) and the alt of the image it captions.
  let (figDoc, figDiags) := Elab.run "t"
    "\\begin{figure}[t]\\centering\\includegraphics{rects.png}\\caption{A mark}\\end{figure}"
  t "figure elaborates with its placement registered as a note"
    (figDiags.all (·.severity == .note) && figDiags.any (·.code == "N0102"))
  t "figure elaborates to a float carrying its caption"
    (match figDoc.body.toList with
     | [.float .figure _ false inner cap] =>
       match inner.toList with
       | [.para xs] =>
         (xs.any fun x => match x with
           | .image "rects.png" _ alt => alt == .described "A mark"
           | _ => false) &&
         Ir.plainText cap == "A mark"
       | _ => false
     | _ => false)
  t "figure image reaches the page"
    ((imageSegs (layoutOf oneFace figDoc geom none store)).size == 1)
  -- An image in a slide: the frame's page carries it.
  let (slideDoc, _) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\begin{frame}{T}\\includegraphics{rects.png}\\end{frame}\\end{document}"
  let slideGeom := Layout.Geom.ofPage slideDoc.page
  t "slide image reaches the frame page"
    ((imageSegs (layoutOf oneFace slideDoc slideGeom none store)).size == 1)
  -- The deck logo: same image node, placed at the lower-right corner of
  -- every page, its right edge on the margin.
  let (logoDoc, logoDiags) := Elab.run "t"
    "\\documentclass{slides}\\logo{\\includegraphics[height=8pt, alt={A synthetic mark}]{rects.png}}\
\\begin{document}\\begin{frame}{A}x\\end{frame}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declaration elaborates clean" (logoDiags.isEmpty)
  let logoGeom := Layout.Geom.ofPage logoDoc.page
  let logoOut := layoutOf oneFace logoDoc logoGeom none store
  let logoW := Dim.pt 8 * Dim.pt 64 / Dim.pt 40
  t "logo placed on every page at the right margin"
    (logoOut.pages.size == 2 && logoOut.pages.all fun p =>
      p.lines.any fun l =>
        l.x + l.setWidth == logoGeom.pageW - logoGeom.hmargin &&
        l.segs.any fun s => match s with
          | .image _ w h => w == logoW && h == Dim.pt 8
          | _ => false)

  -- The PDF: an XObject per used image, painted by a cm+Do pair; the xref
  -- theorem-test still holds with the new objects in the file.
  let (pdfDoc, _) := Elab.run "t"
    "\\includegraphics{rects.png} and \\includegraphics{rects.jpg} and \
\\includegraphics{rects-alpha.png}"
  let pdfOut := layoutOf oneFace pdfDoc geom none store
  let pdfRaw := Pdf.write geom oneFace pdfOut.pages {} store
  let pdf := pdfText pdfRaw
  t "pdf embeds the png as flate with the predictor"
    (bytesContain pdf "/Subtype /Image" && bytesContain pdf "/FlateDecode" &&
     bytesContain pdf "/Predictor 15")
  t "pdf embeds the jpeg as dct" (bytesContain pdf "/DCTDecode")
  t "pdf gives the alpha image a soft mask" (bytesContain pdf "/SMask")
  t "pdf paints all three images" (bytesContain pdf "/Im1 Do" &&
    bytesContain pdf "/Im2 Do" && bytesContain pdf "/Im3 Do")
  -- The cm matrix must carry the placed size: a Do behind a degenerate
  -- matrix is a blank box that every structural check would miss.
  t "pdf image matrix carries the placed size"
    (bytesContain pdf "q 64 0 0 40 ")
  t "pdf page resources name the xobjects" (bytesContain pdf "/XObject <<")
  match checkXref pdfRaw with
  | .ok n => t "pdf xref valid with images" (n > 0)
  | .error e => failures ref s!"pdf xref with images: {e}"
  -- The raw IDAT bytes must reach the file unchanged: the stream is the
  -- pass-through, not a re-encoding.
  t "pdf carries the png stream verbatim"
    (match pngInfo with
     | .ok inf => containsBytes pdf inf.data
     | .error _ => false)
  -- The placeholder: an outlined box, no image object, a valid file.
  let missOut := layoutOf oneFace
    ((Elab.run "t" "\\includegraphics[width=50pt]{missing.png}").1) geom none store
  let missRaw := Pdf.write geom oneFace missOut.pages {} store
  let missPdf := pdfText missRaw
  t "pdf placeholder draws an outline, embeds nothing"
    (bytesContain missPdf "re S" && !(bytesContain missPdf "/Subtype /Image"))
  match checkXref missRaw with
  | .ok _ => pure ()
  | .error e => failures ref s!"pdf xref with placeholder: {e}"

  -- The HTML: an <img> through the typed tree, intrinsic pixel size as
  -- attributes so the page never reflows, the caption as alt, the requested
  -- fraction as a percentage.
  let hcfg : HtmlDoc.Config := { imgs := store }
  let (_, figTree, _) := HtmlDoc.emitTree hcfg figDoc
  let pngHref ← htmlDataOracle "image/png" pngData
  t "html figure image with alt and intrinsic size"
    (elemAttrsList (· == "img") #[] figTree.toList ==
      #[("img", #[("src", pngHref), ("alt", "A mark"), ("width", "64"), ("height", "40")])])
  let (twDoc, _) := Elab.run "t" "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let (twHtml, _) := HtmlDoc.emit hcfg twDoc
  t "html width fraction becomes a percentage"
    ((twHtml.splitOn "style=\"width: 80%; height: auto\"").length == 2)
  let (affineDoc, _) := Elab.run "t" affineSrc
  let (affineHtml, _) := HtmlDoc.emit hcfg affineDoc
  t "html emits a mixed affine image width as calc"
    (hasStr affineHtml "style=\"width: calc(33.4% + " && hasStr affineHtml "pt); height: auto\"")
  let (missHtml, _) := HtmlDoc.emit hcfg
    ((Elab.run "t" "\\includegraphics{missing.png}").1)
  t "html missing image still emits the img with alt"
    ((missHtml.splitOn "<img src=\"missing.png\"").length == 2)

  -- The surface diagnostics: a length that does not parse, an option the
  -- engine does not model.
  t "includegraphics bad length is E0331"
    (errCodes "\\includegraphics[width=banana]{x.png}" == ["E0331"])
  t "includegraphics em length is E0331"
    (errCodes "\\includegraphics[width=2em]{x.png}" == ["E0331"])
  t "includegraphics unknown option warns W0110"
    (warnCodes "\\includegraphics[angle=45, alt={A box}]{x.png}" == ["W0110"])
  t "includegraphics without a file group is E0304"
    (errCodes "\\includegraphics[width=3cm]" == ["E0304"])
  -- totalheight is height plus depth and an image has no depth: one key.
  t "includegraphics totalheight is height"
    (match (elabStr "\\includegraphics[totalheight=8pt]{x.png}").1.body.toList with
     | [.para xs] => xs.any fun x => match x with
        | .image _ spec _ => spec.height == some (Image.Len.abs (Dim.pt 8))
        | _ => false
     | _ => false)
  -- \logo is a declaration in the body too, and it is stateful there, as
  -- in beamer: a deck scopes a logo to one frame with `\logo{...}` before
  -- it and `\logo{}` after.
  let (bodyLogoDoc, bodyLogoDiags) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\logo{\\includegraphics[height=8pt, alt={A synthetic mark}]{rects.png}}\
\\begin{frame}{A}x\\end{frame}\\logo{}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declared in the body binds" (bodyLogoDiags.isEmpty && bodyLogoDoc.logo.isNone)
  let blOut := layoutOf oneFace bodyLogoDoc (pats := none) (imgs := store)
  let pageHasImage (p : Layout.PageOut) : Bool :=
    p.lines.any fun l => l.segs.any fun s => match s with
      | .image .. => true
      | _ => false
  t "body logo scopes to its frame's page"
    (blOut.pages.size == 2 && pageHasImage blOut.pages[0]! &&
     !pageHasImage blOut.pages[1]!)
  -- A bare graphicx name gains the extension the file on disk has; the
  -- candidate order tries the name as written first, then `.pdf` —
  -- graphicx's own order under pdfTeX.
  t "source candidates try the written name first"
    ((Image.sourceCandidates "figures/plot").take 3 ==
      ["figures/plot", "figures/plot.pdf", "figures/plot.png"])
  t "html embeds the resolved file's bytes for a bare spelling"
    (let store2 : Image.Store := { entries := #[
      { src := "figures/plot", href := "figures/plot.png", source := some pngData,
        info := pngInfo.toOption }] }
     let (_, tree, _) := HtmlDoc.emitTree { imgs := store2 }
       ((Elab.run "t" "\\includegraphics{figures/plot}").1)
     HtmlDoc.imgSrcsList #[] tree.toList == #[pngHref])

/-- Colour-key transparency: a PNG `tRNS` chunk on the pass-through colour
types (greyscale, truecolour, indexed) is either exactly the PDF `/Mask`
ranges in sample units or a refusal the driver names — never an opaque
embed. Every bit depth, the indexed edge cases (interval, prefix, all
opaque, fractional, scattered, over-long), chunk order and duplicates, the
image dictionary, and the cache codec's new field. -/
def colorKeyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let chunk := pngChunk
  let ihdr := pngIhdr
  -- A PNG of colour type `ct` at bit depth `bd`, its PLTE and tRNS as given
  -- (an empty list omits the chunk), IDAT arbitrary.
  let png (bd ct : Nat) (plte trns : List UInt8) (idat : List UInt8 := [0]) : ByteArray :=
    mkPng (chunk "IHDR" (ihdr 4 4 bd ct 0) ++
      (if plte.isEmpty then [] else chunk "PLTE" plte) ++
      (if trns.isEmpty then [] else chunk "tRNS" trns) ++
      chunk "IDAT" idat ++ chunk "IEND" [])
  let keyOf (b : ByteArray) : Option (Array Nat) :=
    match Image.decode b with
    | .ok inf => some (planKey inf)
    | .error _ => none
  let refusedNaming (b : ByteArray) (word : String) : Bool :=
    match Image.decode b with
    | .error e => (e.splitOn word).length == 2
    | .ok _ => false
  -- Greyscale: one two-byte sample, in range for the bit depth.
  t "grey 8-bit key is the sample twice" (keyOf (png 8 0 [] [0, 7]) == some #[7, 7])
  -- 16-bit keys: exact in the pure mapping, refused by the decoder — two of
  -- the four target readers (Poppler, PDFium) paint the keyed pixels.
  t "grey 16-bit key is exact in the mapping"
    (Image.colorKeyRanges .gray 16 (bytes [1, 2]) ByteArray.empty == .ok #[258, 258])
  t "grey 16-bit key refused by the decoder, naming the readers"
    (refusedNaming (png 16 0 [] [1, 2]) "readers")
  t "grey 4-bit key at the top value" (keyOf (png 4 0 [] [0, 15]) == some #[15, 15])
  t "grey 2-bit key" (keyOf (png 2 0 [] [0, 3]) == some #[3, 3])
  t "grey 1-bit key" (keyOf (png 1 0 [] [0, 1]) == some #[1, 1])
  t "grey 4-bit key out of range refused" (refusedNaming (png 4 0 [] [0, 16]) "tRNS")
  t "grey 8-bit key out of range refused" (refusedNaming (png 8 0 [] [1, 0]) "tRNS")
  t "grey key of the wrong length refused"
    (refusedNaming (png 8 0 [] [7]) "tRNS" && refusedNaming (png 8 0 [] [0, 7, 0]) "tRNS")
  -- Truecolour: three two-byte samples.
  t "rgb 8-bit key is each sample twice"
    (keyOf (png 8 2 [] [0, 10, 0, 20, 0, 30]) == some #[10, 10, 20, 20, 30, 30])
  t "rgb 16-bit key is exact in the mapping"
    (Image.colorKeyRanges .rgb 16 (bytes [1, 0, 2, 0, 3, 0]) ByteArray.empty ==
      .ok #[256, 256, 512, 512, 768, 768])
  t "rgb 16-bit key refused by the decoder" (refusedNaming (png 16 2 [] [1, 0, 2, 0, 3, 0]) "16-bit")
  t "rgb 16-bit without a key still passes through"
    (keyOf (png 16 2 [] []) == some #[])
  t "rgb 8-bit key out of range refused" (refusedNaming (png 8 2 [] [1, 0, 0, 0, 0, 0]) "tRNS")
  t "rgb key of the wrong length refused" (refusedNaming (png 8 2 [] [0, 10]) "tRNS")
  -- Indexed: the transparent entries one interval, the rest opaque.
  let pal2 : List UInt8 := [0, 0, 0, 255, 255, 255]
  let pal4 : List UInt8 := pal2 ++ [255, 0, 0, 0, 255, 0]
  t "indexed key on entry 0" (keyOf (png 8 3 pal2 [0, 255]) == some #[0, 0])
  t "indexed key on entry 1" (keyOf (png 8 3 pal2 [255, 0]) == some #[1, 1])
  t "indexed key on an interior interval" (keyOf (png 8 3 pal4 [255, 0, 0, 255]) == some #[1, 2])
  t "indexed key on a prefix interval" (keyOf (png 8 3 pal4 [0, 0]) == some #[0, 1])
  t "indexed key reaching the last entry" (keyOf (png 8 3 pal4 [255, 255, 0, 0]) == some #[2, 3])
  t "indexed all-opaque tRNS is no mask" (keyOf (png 8 3 pal4 [255, 255]) == some #[])
  t "indexed at bit depth 1" (keyOf (png 1 3 pal2 [0]) == some #[0, 0])
  t "indexed at bit depth 2" (keyOf (png 2 3 pal4 [255, 255, 255, 0]) == some #[3, 3])
  t "indexed at bit depth 4" (keyOf (png 4 3 pal4 [0, 255]) == some #[0, 0])
  t "indexed partial alpha refused" (refusedNaming (png 8 3 pal4 [0, 128, 255]) "partial")
  t "indexed scattered transparency refused" (refusedNaming (png 8 3 pal4 [0, 255, 0]) "partial")
  t "indexed tRNS longer than the palette refused"
    (refusedNaming (png 8 3 pal2 [255, 255, 0]) "tRNS")
  t "indexed tRNS beyond the bit depth refused"
    (refusedNaming (png 1 3 pal4 [255, 255, 0]) "tRNS")
  -- Order and multiplicity: one tRNS, after PLTE, before IDAT.
  t "tRNS on an alpha type refused"
    (refusedNaming (mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++ chunk "tRNS" [0, 0, 0, 0, 0, 0] ++
      chunk "IDAT" (Flate.deflateStored (bytes (List.replicate 18 0))).toList ++
      chunk "IEND" [])) "tRNS")
  t "duplicate tRNS refused"
    (refusedNaming (mkPng (chunk "IHDR" (ihdr 4 4 8 0 0) ++ chunk "tRNS" [0, 1] ++
      chunk "tRNS" [0, 2] ++ chunk "IDAT" [0] ++ chunk "IEND" [])) "tRNS")
  t "tRNS after IDAT refused"
    (refusedNaming (mkPng (chunk "IHDR" (ihdr 4 4 8 0 0) ++ chunk "IDAT" [0] ++
      chunk "tRNS" [0, 1] ++ chunk "IEND" [])) "tRNS")
  t "indexed tRNS before PLTE refused"
    (refusedNaming (mkPng (chunk "IHDR" (ihdr 4 4 8 3 0) ++ chunk "tRNS" [0] ++
      chunk "PLTE" pal2 ++ chunk "IDAT" [0] ++ chunk "IEND" [])) "tRNS")
  t "no tRNS is no key" (keyOf (png 8 2 [] []) == some #[])
  -- The pure ranges, exercised beside their theorems on shapes the
  -- decoder cannot reach (a tRNS array with no palette behind it).
  t "colorKeyRanges: empty indexed tRNS is no mask"
    (Image.colorKeyRanges .indexed 8 ByteArray.empty (bytes pal4) == .ok #[])
  t "colorKeyRanges: grey ignores the palette"
    (Image.colorKeyRanges .gray 8 (bytes [0, 9]) (bytes pal4) == .ok #[9, 9])
  -- The PDF: the raster dictionary carries `/Mask` in sample units, the
  -- IDAT still passes through verbatim, and an unkeyed image has no mask.
  let idxPng := png 8 3 pal2 [0, 255] (idat := (Flate.deflateStored (bytes
    (List.replicate 4 [0, 0, 1, 1, 0]).flatten)).toList)
  let rgbPng := png 8 2 [] [0, 10, 0, 20, 0, 30]
    (idat := (Flate.deflateStored (bytes (List.replicate (4 * 13) 0))).toList)
  let plainPng := png 8 2 [] [] (idat := (Flate.deflateStored (bytes
    (List.replicate (4 * 13) 0))).toList)
  let idxInfo := Image.decode idxPng
  let store : Image.Store := { entries := #[
    { src := "key-idx.png", info := idxInfo.toOption },
    { src := "key-rgb.png", info := (Image.decode rgbPng).toOption },
    { src := "plain.png", info := (Image.decode plainPng).toOption }] }
  t "keyed fixtures decode" (store.entries.all (·.info.isSome))
  let geom : Layout.Geom := {}
  let (doc, _) := Elab.run "t"
    "\\includegraphics{key-idx.png} \\includegraphics{key-rgb.png} \\includegraphics{plain.png}"
  let out := layoutOf oneFace doc geom none store
  let pdfRaw := Pdf.write geom oneFace out.pages {} store
  let pdf := pdfText pdfRaw
  t "pdf indexed image carries its colour-key mask" (bytesContain pdf "/Mask [0 0]")
  t "pdf rgb image carries its colour-key mask" (bytesContain pdf "/Mask [10 10 20 20 30 30]")
  t "pdf keyed images stay pass-through"
    (match idxInfo with
     | .ok inf => containsBytes pdf inf.data && bytesContain pdf "/Predictor 15"
     | .error _ => false)
  t "pdf unkeyed image has no mask"
    (bytesContain pdf "/BitsPerComponent 8 /Filter /FlateDecode")
  match checkXref pdfRaw with
  | .ok n => t "pdf xref valid with keyed images" (n > 0)
  | .error e => failures ref s!"pdf xref with keyed images: {e}"
  -- The cache codec: the key rides, the format version moved, and the
  -- old magic is a miss.
  match idxInfo with
  | .error e => failures ref s!"keyed png decode: {e}"
  | .ok inf =>
    let blob := Image.encodeBin inf
    t "image cache serialization round-trips the colour key"
      (match Image.decodeBin blob with
       | some back => planKey back == planKey inf && planKey back == #[0, 0] &&
           back.color == inf.color && back.data == inf.data &&
           planPalette back == bytes pal2 &&
           back.bitDepth == inf.bitDepth && back.pxW == 4 && back.pxH == 4
       | none => false)
    t "image cache magic is LTIMG3" (blob.extract 0 6 == "LTIMG3".toUTF8)
    t "image cache rejects a stale LTIMG1 entry" ((Image.decodeBin (blob.set! 5 49)).isNone)
    t "image cache rejects a stale LTIMG2 entry" ((Image.decodeBin (blob.set! 5 50)).isNone)
    t "image cache rejects a lying key count"
      ((Image.decodeBin (blob.set! 49 (blob[49]! + 1))).isNone)
  -- A wide key (the truecolour ranges) round-trips too.
  t "image cache round-trips a six-range key"
    (match Image.decode rgbPng with
     | .ok inf => (Image.decodeBin (Image.encodeBin inf)).map planKey ==
         some #[10, 10, 20, 20, 30, 30]
     | .error _ => false)


/-- A JPEG header from segments: SOI, the given APP segments, a baseline
SOF0 of the given geometry, and SOS — the scan never has to exist for the
probe. -/
def jpegOf (apps : List UInt8) (w h ncomp : Nat) : ByteArray :=
  let sof0 : List UInt8 :=
    [0xFF, 0xC0, 0, UInt8.ofNat (8 + 3 * ncomp), 8,
     UInt8.ofNat (h / 256), UInt8.ofNat (h % 256),
     UInt8.ofNat (w / 256), UInt8.ofNat (w % 256), UInt8.ofNat ncomp] ++
     (List.range ncomp).flatMap fun k => [UInt8.ofNat (k + 1), 0x11, 0]
  bytes ([0xFF, 0xD8] ++ apps ++ sof0 ++ [0xFF, 0xDA])

/-- One marker segment: `FF m`, then the length (its own two bytes
included), then the payload. -/
def jpegSeg (m : Nat) (payload : List UInt8) : List UInt8 :=
  let len := payload.length + 2
  [0xFF, UInt8.ofNat m, UInt8.ofNat (len / 256), UInt8.ofNat (len % 256)] ++ payload

/-- An APP1 Exif segment carrying one IFD0 entry: orientation `o`, in the
given byte order. -/
def exifApp1 (o : Nat) (bigEndian : Bool) : List UInt8 :=
  let u16 (v : Nat) : List UInt8 :=
    if bigEndian then [UInt8.ofNat (v / 256), UInt8.ofNat (v % 256)]
    else [UInt8.ofNat (v % 256), UInt8.ofNat (v / 256)]
  let u32 (v : Nat) : List UInt8 :=
    if bigEndian then be32 v else (be32 v).reverse
  let tiff := [if bigEndian then [0x4D, 0x4D] else [0x49, 0x49], u16 42, u32 8,
    u16 1, u16 0x0112, u16 3, u32 1, u16 o, u16 0, u32 0].flatten
  jpegSeg 0xE1 ([0x45, 0x78, 0x69, 0x66, 0, 0] ++ tiff)

/-- An APP2 `ICC_PROFILE` piece `seq` of `count`. -/
def iccApp2 (seq count : Nat) (data : List UInt8) : List UInt8 :=
  jpegSeg 0xE2 ([0x49, 0x43, 0x43, 0x5F, 0x50, 0x52, 0x4F, 0x46, 0x49, 0x4C, 0x45, 0] ++
    [UInt8.ofNat seq, UInt8.ofNat count] ++ data)

/-- The probe and the planner: every `Source` fact the plan does not carry
is a ledger entry (`plan_losses_accounts`), the refusals name their
format (`plan_refuses_named`), the cache gate is the planner's
(`recodes_iff`), the parameters key the cache
(`planParams_serialize_inj`), the codec inverts on every constructor, and
the driver turns the ledger into one diagnostic per entry. -/
def planChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let chunk := pngChunk
  let ihdr := pngIhdr
  let idat2 := (Flate.deflateStored (bytes (List.replicate 2 [0, 1, 2, 3, 4, 5, 6]).flatten)).toList
  let profile : List UInt8 := (List.range 40).map fun k => UInt8.ofNat (k * 7 % 256)
  let iccpChunk := chunk "iCCP" ([0x69, 0x63, 0x63, 0, 0] ++ (Flate.deflateStored (bytes profile)).toList)
  let pngIccp := mkPng (chunk "IHDR" (ihdr 2 2 8 2 0) ++ iccpChunk ++ chunk "IDAT" idat2 ++
    chunk "IEND" [])
  let pngPlain := mkPng (chunk "IHDR" (ihdr 2 2 8 2 0) ++ chunk "IDAT" idat2 ++ chunk "IEND" [])
  let pngAncillary := mkPng (chunk "IHDR" (ihdr 2 2 8 2 0) ++ chunk "sRGB" [1] ++
    chunk "gAMA" (be32 45455) ++ chunk "cHRM" ((List.range 8).flatMap fun k => be32 (1000 * (k + 1))) ++
    chunk "IDAT" idat2 ++ chunk "IEND" [])
  let default := Image.PlanParams.default
  let planOf (b : ByteArray) (p : Image.PlanParams := default) : Except String Image.Plan :=
    Image.probe b >>= Image.plan p
  -- Red 1: the profile is read, dropped under the default policy, and the
  -- drop is in the ledger; the IDAT still passes through.
  t "probe reads an iCCP profile as zlib bytes"
    (match Image.probe pngIccp with
     | .ok s => s.iccIsZlib && s.icc == Flate.deflateStored (bytes profile) && s.format == .png
     | .error _ => false)
  t "plan drops the profile under the default policy and says so"
    (match planOf pngIccp with
     | .ok pl => pl.color == .rgb && pl.losses == #[.iccDropped] && pl.data == bytes idat2
     | .error _ => false)
  t "plan carries the profile under the carry policy, no loss"
    (match planOf pngIccp { default with iccPolicy := .carry } with
     | .ok pl => pl.color == .iccBased 3 (Flate.deflateStored (bytes profile)) && pl.losses.isEmpty
     | .error _ => false)
  t "an indexed profile is dropped even under carry, and says so"
    (match planOf (mkPng (chunk "IHDR" (ihdr 2 2 8 3 0) ++ iccpChunk ++
        chunk "PLTE" [0, 0, 0, 255, 255, 255] ++ chunk "IDAT" idat2 ++ chunk "IEND" []))
        { default with iccPolicy := .carry } with
     | .ok pl => pl.color == .indexed (bytes [0, 0, 0, 255, 255, 255]) && pl.losses == #[.iccDropped]
     | .error _ => false)
  t "the ledger names exactly one W0603 for a profiled source"
    (match planOf pngIccp with
     | .ok pl => (Image.lossDiags "figures/a.png" pl).map (·.code) == #["W0603"] &&
         (Image.lossDiags "figures/a.png" pl).all (·.subject == some "figures/a.png")
     | .error _ => false)
  t "a plain PNG has an empty ledger"
    (match planOf pngPlain with
     | .ok pl => pl.losses.isEmpty && (Image.lossDiags "a.png" pl).isEmpty
     | .error _ => false)
  t "probe reads sRGB, gAMA and cHRM as source facts; the plan has no loss for them"
    (match Image.probe pngAncillary, planOf pngAncillary with
     | .ok s, .ok pl => s.srgbIntent == some 1 && s.gamma == some 45455 &&
         s.chrm == some #[1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000] && pl.losses.isEmpty
     | _, _ => false)
  t "a corrupt iCCP (no name) is refused as corrupt"
    (match Image.probe (mkPng (chunk "IHDR" (ihdr 2 2 8 2 0) ++ chunk "iCCP" [0, 0, 1, 2] ++
        chunk "IDAT" idat2 ++ chunk "IEND" [])) with
     | .error e => hasStr e "iCCP"
     | .ok _ => false)
  -- Red 2: orientation, both byte orders, in the ledger and one W0604.
  let jpgExif6 := jpegOf (exifApp1 6 true) 2 1 3
  let jpgExif8le := jpegOf (exifApp1 8 false) 2 1 3
  t "probe reads Exif orientation 6 (big-endian TIFF)"
    (match Image.probe jpgExif6 with
     | .ok s => s.orientation == 6 && s.format == .jpeg && s.colorType == 3 && s.pxW == 2
     | .error _ => false)
  t "probe reads Exif orientation 8 (little-endian TIFF)"
    ((Image.probe jpgExif8le).toOption.map (·.orientation) == some 8)
  t "plan drops the orientation and says so"
    (match planOf jpgExif6 with
     | .ok pl => pl.orientation == 6 && pl.losses == #[.orientationDropped] &&
         pl.filter == .dct && pl.data == jpgExif6
     | .error _ => false)
  t "the ledger names exactly one W0604 with the tag"
    (match planOf jpgExif6 with
     | .ok pl => (Image.lossDiags "p.jpg" pl).map (·.code) == #["W0604"] &&
         (Image.lossDiags "p.jpg" pl).all fun d => d.subject == some "p.jpg" && hasStr d.message "tag 6"
     | .error _ => false)
  t "orientation 1 and an absent tag are no loss"
    ((planOf (jpegOf (exifApp1 1 true) 2 1 3)).toOption.map (·.losses) == some #[] &&
     (planOf (jpegOf [] 2 1 3)).toOption.map (·.losses) == some #[])
  t "an orientation outside 1–8 is the default"
    ((Image.probe (jpegOf (exifApp1 9 true) 2 1 3)).toOption.map (·.orientation) == some 1)
  -- A JPEG profile in two APP2 pieces, out of file order, concatenates in
  -- sequence order; a profiled JPEG with orientation carries two losses.
  let jpgIcc := jpegOf (iccApp2 2 2 [4, 5, 6] ++ iccApp2 1 2 [1, 2, 3] ++ exifApp1 3 true) 2 1 3
  t "probe concatenates APP2 profile pieces in sequence order, raw"
    (match Image.probe jpgIcc with
     | .ok s => s.icc == bytes [1, 2, 3, 4, 5, 6] && !s.iccIsZlib
     | .error _ => false)
  t "a profiled, oriented JPEG carries both losses, in ledger order"
    (match planOf jpgIcc with
     | .ok pl => pl.losses == #[.iccDropped, .orientationDropped] &&
         (Image.lossDiags "p.jpg" pl).map (·.code) == #["W0603", "W0604"]
     | .error _ => false)
  t "carry deflates a raw JPEG profile"
    (match planOf jpgIcc { default with iccPolicy := .carry } with
     | .ok pl => pl.color == .iccBased 3 (Flate.deflate (bytes [1, 2, 3, 4, 5, 6])) &&
         pl.losses == #[.orientationDropped]
     | .error _ => false)
  t "probe reads the APP14 Adobe transform"
    ((Image.probe (jpegOf (jpegSeg 0xEE [0x41, 0x64, 0x6F, 0x62, 0x65, 0, 100, 0, 0, 0, 0, 1])
        2 1 3)).toOption.bind (·.adobeTransform) == some 1)
  -- Red 3: the unembeddable formats are recognised, sized, and refused by name.
  let le24 (n : Nat) : List UInt8 :=
    [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n / 65536 % 256)]
  let webpX := bytes ([0x52, 0x49, 0x46, 0x46] ++ (be32 30).reverse ++ [0x57, 0x45, 0x42, 0x50] ++
    [0x56, 0x50, 0x38, 0x58] ++ (be32 10).reverse ++ [0, 0, 0, 0] ++ le24 (300 - 1) ++ le24 (200 - 1))
  let webpL := bytes ([0x52, 0x49, 0x46, 0x46] ++ (be32 30).reverse ++ [0x57, 0x45, 0x42, 0x50] ++
    [0x56, 0x50, 0x38, 0x4C] ++ (be32 10).reverse ++ [0x2F] ++
    -- 14 bits width-1 = 15, 14 bits height-1 = 9: 15 + 9·2¹⁴, little-endian.
    (be32 (15 + 9 * 16384)).reverse)
  let webp8 := bytes ([0x52, 0x49, 0x46, 0x46] ++ (be32 30).reverse ++ [0x57, 0x45, 0x42, 0x50] ++
    [0x56, 0x50, 0x38, 0x20] ++ (be32 10).reverse ++ [0, 0, 0, 0x9D, 0x01, 0x2A] ++
    [64, 0, 40, 0])
  let refusedNaming (b : ByteArray) (name : String) : Bool :=
    match planOf b with
    | .error e => e.startsWith name
    | .ok _ => false
  t "probe sizes a VP8X WebP"
    ((Image.probe webpX).toOption.map (fun s => (s.format, s.pxW, s.pxH)) == some (.webp, 300, 200))
  t "probe sizes a VP8L WebP"
    ((Image.probe webpL).toOption.map (fun s => (s.pxW, s.pxH)) == some (16, 10))
  t "probe sizes a VP8 WebP"
    ((Image.probe webp8).toOption.map (fun s => (s.pxW, s.pxH)) == some (64, 40))
  t "plan refuses WebP by name" (refusedNaming webpX "WebP" && refusedNaming webpL "WebP")
  let avif := bytes ((be32 20) ++ [0x66, 0x74, 0x79, 0x70, 0x61, 0x76, 0x69, 0x66] ++ be32 0 ++
    [0x6D, 0x69, 0x66, 0x31, 0x61, 0x76, 0x69, 0x66] ++
    be32 20 ++ [0x69, 0x73, 0x70, 0x65] ++ be32 0 ++ be32 640 ++ be32 480)
  t "probe sizes an AVIF from ispe"
    ((Image.probe avif).toOption.map (fun s => (s.format, s.pxW, s.pxH)) == some (.avif, 640, 480))
  t "plan refuses AVIF by name" (refusedNaming avif "AVIF")
  -- JPEG XL: small size header, 8×8 at ratio 1:1 (bits LSB-first: small=1,
  -- ysize_div8_minus_1=0, ratio=1), and a non-small 300×200 header.
  let jxlSmall := bytes [0xFF, 0x0A, 0x41, 0]
  t "probe sizes a small JPEG XL header"
    ((Image.probe jxlSmall).toOption.map (fun s => (s.format, s.pxW, s.pxH)) == some (.jxl, 8, 8))
  -- non-small: bit0 small=0; U32 selector 0 (2 bits) then 9 bits = 199 (h=200);
  -- ratio 0 (3 bits); U32 selector 0 then 9 bits = 299 (w=300).
  let bitsToBytes (bs : List Nat) : List UInt8 := Id.run do
    let mut out : Array UInt8 := #[]
    let mut cur := 0
    let mut n := 0
    for b in bs do
      cur := cur + b * 2 ^ n
      n := n + 1
      if n == 8 then
        out := out.push (UInt8.ofNat cur)
        cur := 0
        n := 0
    if n > 0 then out := out.push (UInt8.ofNat cur)
    return out.toList
  let lsb (v n : Nat) : List Nat := (List.range n).map fun k => v / 2 ^ k % 2
  let jxlBig := bytes ([0xFF, 0x0A] ++ bitsToBytes ([0] ++ lsb 0 2 ++ lsb 199 9 ++ lsb 0 3 ++
    lsb 0 2 ++ lsb 299 9))
  t "probe sizes a non-small JPEG XL header"
    ((Image.probe jxlBig).toOption.map (fun s => (s.pxW, s.pxH)) == some (300, 200))
  let jxlBox := bytes ([0, 0, 0, 0x0C, 0x4A, 0x58, 0x4C, 0x20, 0x0D, 0x0A, 0x87, 0x0A] ++
    be32 12 ++ [0x6A, 0x78, 0x6C, 0x63] ++ [0xFF, 0x0A, 0x41, 0])
  t "probe sizes a JPEG XL container through its jxlc box"
    ((Image.probe jxlBox).toOption.map (fun s => (s.pxW, s.pxH)) == some (8, 8))
  t "plan refuses JPEG XL by name" (refusedNaming jxlSmall "JPEG XL" && refusedNaming jxlBox "JPEG XL")
  let jp2 := bytes ([0, 0, 0, 0x0C, 0x6A, 0x50, 0x20, 0x20, 0x0D, 0x0A, 0x87, 0x0A] ++
    be32 22 ++ [0x69, 0x68, 0x64, 0x72] ++ be32 3 ++ be32 4 ++ [0, 3, 7, 7, 0, 0])
  let j2k := bytes ([0xFF, 0x4F, 0xFF, 0x51, 0, 41, 0, 0] ++ be32 10 ++ be32 6 ++ be32 2 ++ be32 1)
  t "probe sizes a JP2 container from ihdr"
    ((Image.probe jp2).toOption.map (fun s => (s.format, s.pxW, s.pxH)) == some (.jpx, 4, 3))
  t "probe sizes a raw J2K codestream from SIZ"
    ((Image.probe j2k).toOption.map (fun s => (s.format, s.pxW, s.pxH)) == some (.jpx, 8, 5))
  t "plan refuses JPEG 2000 by name under every permission"
    (refusedNaming jp2 "JPEG 2000" && refusedNaming j2k "JPEG 2000" &&
     (match planOf jp2 { default with jpxPermitted := true } with
      | .error e => e.startsWith "JPEG 2000"
      | .ok _ => false))
  t "a foreign signature is still the old refusal"
    (match Image.probe (bytes [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) with
     | .error e => hasStr e "unrecognised signature"
     | .ok _ => false)
  -- Red 4: the gate agrees with the planner on the shipped fixtures and a
  -- synthetic colour type 6; the recoded flag is exactly the alpha arm's.
  let pngData ← IO.FS.readBinFile "testdata/corpus/rects.png"
  let jpgData ← IO.FS.readBinFile "testdata/corpus/rects.jpg"
  let alphaData ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++ [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
    chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" [])
  let agrees (b : ByteArray) : Bool :=
    match Image.probe b with
    | .ok s => (match Image.plan default s with
      | .ok pl => pl.recoded == Image.Plan.recodes default s
      | .error _ => false)
    | .error _ => false
  t "recodes agrees with the planner on every fixture"
    (agrees pngData && agrees jpgData && agrees alphaData && agrees rgbaPng && agrees pngIccp)
  t "only the alpha PNGs recode"
    ((Image.probe alphaData).toOption.map (Image.Plan.recodes default) == some true &&
     (Image.probe rgbaPng).toOption.map (Image.Plan.recodes default) == some true &&
     (Image.probe pngData).toOption.map (Image.Plan.recodes default) == some false &&
     (Image.probe jpgData).toOption.map (Image.Plan.recodes default) == some false)
  t "an interlaced alpha PNG is refused, so the gate's answer never reaches a cache"
    ((planOf (mkPng (chunk "IHDR" (ihdr 2 2 8 6 1) ++
      chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" []))).isOk == false)
  -- The parameters the alpha arm honours.
  t "a forbidden soft mask refuses the alpha PNG by name"
    (match planOf rgbaPng { default with softMaskPermitted := false } with
     | .error e => hasStr e "soft mask"
     | .ok _ => false)
  t "a depth over the declared limit refuses the pass-through"
    (match planOf (mkPng (chunk "IHDR" (ihdr 2 2 16 0 0) ++ chunk "IDAT" idat2 ++ chunk "IEND" []))
        { default with maxBpc := 8 } with
     | .error e => hasStr e "16 bits"
     | .ok _ => false)
  t "the default limit passes 16-bit samples through"
    ((planOf (mkPng (chunk "IHDR" (ihdr 2 2 16 0 0) ++ chunk "IDAT" idat2 ++ chunk "IEND" []))).isOk)
  -- Red 5: the serialization is injective over the parameter product, and
  -- two records differing only in the policy key two cache paths.
  let params : List Image.PlanParams := Id.run do
    let mut out : List Image.PlanParams := []
    for j in [false, true] do
      for sm in [false, true] do
        for bpc in [8, 16, 4294967295] do
          for pol in [Image.IccPolicy.dropWithDiag, .carry] do
            out := { jpxPermitted := j, softMaskPermitted := sm, maxBpc := bpc, iccPolicy := pol } :: out
    return out
  t "params serialize injectively over the product (24 records)"
    (params.length == 24 && params.all fun a => params.all fun b =>
      (a.serialize == b.serialize) == (a == b))
  t "params serialize fixed-width" (params.all fun p => p.serialize.size == 7)
  t "two policies key two cache paths"
    (default.key != ({ default with iccPolicy := .carry } : Image.PlanParams).key &&
     default.key.length == 14)
  -- Red 6: the codec inverts on a plan per alpha and colour constructor;
  -- the older magics are misses.
  let rt (pl : Image.Plan) : Bool :=
    match Image.decodeBin (Image.encodeBin pl) with
    | some back => back.pxW == pl.pxW && back.pxH == pl.pxH && back.dpiX == pl.dpiX &&
        back.dpiY == pl.dpiY && back.bitDepth == pl.bitDepth && back.color == pl.color &&
        back.filter == pl.filter && back.data == pl.data && back.alpha == pl.alpha &&
        back.recoded == pl.recoded && back.losses == pl.losses &&
        back.orientation == pl.orientation && back.form.isNone
    | none => false
  let base : Image.Plan :=
    { pxW := 3, pxH := 2, dpiX := 150, dpiY := 96, bitDepth := 4, data := bytes [9, 8, 7],
      orientation := 6, losses := #[.orientationDropped, .iccDropped] }
  t "codec round-trips every alpha constructor"
    (rt base && rt { base with alpha := .colorKey #[1, 1, 2, 2, 3, 3] } &&
     rt { base with alpha := .soft (bytes [0, 1, 2]) 8, recoded := true })
  t "codec round-trips every colour constructor"
    (rt { base with color := .gray } && rt { base with color := .rgb } &&
     rt { base with color := .indexed (bytes [0, 0, 0, 255, 255, 255]) } &&
     rt { base with color := .iccBased 3 (bytes [1, 2, 3, 4]) } &&
     rt { base with color := .iccBased 1 ByteArray.empty, alpha := .colorKey #[5, 5] })
  t "codec round-trips both filters and an empty ledger"
    (rt { base with filter := .dct, losses := #[] } && rt { base with filter := .flatePredictor })
  let blob := Image.encodeBin base
  t "LTIMG1 and LTIMG2 bytes are misses"
    ((Image.decodeBin (blob.set! 5 49)).isNone && (Image.decodeBin (blob.set! 5 50)).isNone &&
     (Image.decodeBin blob).isSome)
  t "a foreign colour tag is a miss" ((Image.decodeBin (blob.set! 6 9)).isNone)
  t "a foreign loss tag is a miss"
    ((Image.decodeBin (blob.set! 66 7)).isNone)
  -- The driver, end to end: one W0603 and one W0604 per source, the PDF still
  -- built, and the two images embedded pass-through.
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"leantex builds for the plan checks:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode == 0 then
    let dir ← IO.FS.createTempDir
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf"))
    IO.FS.writeBinFile (dir / "profiled.png") pngIccp
    IO.FS.writeBinFile (dir / "oriented.jpg") jpgExif6
    IO.FS.writeBinFile (dir / "plain.png") pngPlain
    IO.FS.writeBinFile (dir / "photo.webp") webpX
    IO.FS.writeFile (dir / "d.tex") "\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n\
\\begin{document}\n\\includegraphics{profiled.png} \\includegraphics{oriented.jpg} \
\\includegraphics{plain.png} \\includegraphics{oriented.jpg} \\includegraphics{photo.webp}\n\
\\end{document}\n"
    let r ← IO.Process.output {
      cmd := ".lake/build/bin/leantex"
      args := #[(dir / "d.tex").toString, "-o", (dir / "out").toString ++ "/"] }
    let log := r.stdout ++ r.stderr
    let count (needle : String) : Nat := (log.splitOn needle).length - 1
    t s!"driver: a profiled PNG is one W0603, an oriented JPEG one W0604, per source: {log}"
      (r.exitCode == 0 && count "[W0603]" == 1 && count "[W0604]" == 1 &&
       hasStr log "profiled.png" && hasStr log "oriented.jpg" && hasStr log "tag 6")
    t "driver: the WebP is refused by name as W0602"
      (count "[W0602]" == 1 && hasStr log "WebP images cannot be embedded")
    let pdf ← IO.FS.readBinFile (dir / "out" / "d.pdf")
    let text := pdfText pdf
    t "driver: the profiled PNG and the oriented JPEG embed pass-through"
      (containsBytes text (bytes idat2) && containsBytes text jpgExif6 &&
       bytesContain text "/DeviceRGB")


/-- Images set in a row, spaced as TeX sets them: a user's frame of two
centred rows, each two images parted by `\hfill`, shipped its images
clumped at the middle of the measure. Over `Layout.Out`, on an invented
frame of the same shape: every image box with its left edge (the line's
origin plus what the line set before it). -/
def imageRowChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pngInfo := Image.decode (← IO.FS.readBinFile "testdata/corpus/rects.png")
  let store : Image.Store := { entries := #[{ src := "rects.png", info := pngInfo.toOption }] }
  let boxes (out : Layout.Out) : Array (Nat × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Nat × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for h : i in [0:out.pages.size] do
      for l in out.pages[i].lines do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .image _ w hh =>
            acc := acc.push (i, x, l.y, w, hh)
            x := x + w
          | .run _ _ _ w _ _ _ _ _ _ _ => x := x + w
          | .gap w _ | .decoratedGap w _ _ => x := x + w
          | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
          | .poly _ _ => pure ()
    return acc
  let img := "\\includegraphics[keepaspectratio,totalheight=.28\\textheight,\
width=.4\\textwidth]{rects.png}%\n"
  let row := "\\begin{center}%\n" ++ img ++ "\\hfill\n" ++ img ++ "\\end{center}\n\n"
  let (doc, _) := Elab.run "t" ("\\documentclass[10pt,aspectratio=169]{beamer}\n\
\\begin{document}\n\\begin{frame}{An invented frame}\n" ++ row ++ row ++
    "A closing line of invented text.\n\\end{frame}\n\\end{document}\n")
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom none store
  let bs := boxes out
  let left := geom.hmargin
  let right := geom.pageW - geom.hmargin
  -- `\centering` puts 0pt plus 1fil in `\leftskip` and `\rightskip`
  -- (`\@flushglue`, latex.ltx) and `\hfill` is 0pt plus 1fill, an order
  -- above them, so the fill takes all of the row's slack: the first image
  -- stands at the measure's left edge, the second ends at its right edge.
  t s!"image rows: one page, four images: {bs.size} on {out.pages.size}"
    (out.pages.size == 1 && bs.size == 4)
  t s!"image rows: each row spans the measure, the fill taking the slack: {bs}"
    (bs.size == 4 && [0, 2].all fun k =>
      match bs[k]?, bs[k + 1]? with
      | some (_, x0, y0, _, _), some (_, x1, y1, w1, _) =>
        x0 == left && x1 + w1 == right && y0 == y1
      | _, _ => false)
  -- beamer's `\textheight` is the paper less `\footheight` and
  -- `\headheight` (beamerbaseframecomponents.sty:178-180): on a frame
  -- page carrying the footline, the text area the page builder already
  -- stands the body in (`Layout.footFloor`, moloch's headline empty). The
  -- invented image is taller than the deck's, so the height binds the
  -- keepaspectratio fit: its box is .28 of that height.
  match out.pages[0]? with
  | some p =>
    match p.footBox with
    | some (bh, bd) =>
      let th := Layout.footFloor geom.pageH Ir.footline.sep bh bd
      t s!"image rows: .28\\textheight is .28 of the frame's text area, {th}: {bs}"
        (bs.size == 4 && bs.all fun (_, _, _, _, hh) => hh == 280 * th / 1000)
    | none => t "image rows: the frame page carries the footline" false
  | none => t "image rows: the frame lays out" false
  -- A logo is furniture of the page, sized by the same `\textheight`.
  let (logoDoc, _) := Elab.run "t" "\\documentclass[10pt,aspectratio=169]{beamer}\n\
\\logo{\\includegraphics[totalheight=.2\\textheight, alt={An invented mark}]{rects.png}}\n\
\\begin{document}\n\\begin{frame}{An invented frame}\nA line of invented text.\n\
\\end{frame}\n\\end{document}\n"
  let logoGeom := Layout.Geom.ofPage logoDoc.page
  let logoOut := layoutOf oneFace logoDoc logoGeom none store
  match logoOut.pages[0]? with
  | some p =>
    match p.footBox with
    | some (bh, bd) =>
      let th := Layout.footFloor logoGeom.pageH Ir.footline.sep bh bd
      t s!"image rows: a logo's .2\\textheight is .2 of the frame's text area, {th}: \
{boxes logoOut}"
        ((boxes logoOut).map (·.2.2.2.2) == #[200 * th / 1000])
    | none => t "image rows: the logo's page carries the footline" false
  | none => t "image rows: the logo's frame lays out" false
  -- The HTML: the row is the container its fractions are stated against,
  -- each image's box is graphicx's fit under the height, never a letterbox,
  -- and a fill row's first group starts at the left as the fill spans the
  -- line. Chromium measured the deck's frame this way (the report's
  -- evidence); the typed tree carries what it read.
  let (html, _) := HtmlDoc.emit { imgs := store } doc
  let rowOpen := "<p class=\"entry entry-pair\" style=\"container-type: inline-size\">"
  t "image rows html: each row declares the container its fractions read"
    ((html.splitOn rowOpen).length == 3)
  t "image rows html: each image is .4 of the row, fitted under its height"
    ((html.splitOn "width: 40%; width: min(40cqi, calc(").length == 5 &&
     (html.splitOn " * 64 / 40)); height: auto").length == 5)
  t "image rows html: no letterboxed image" (!hasStr html "object-fit")
  t "image rows html: a fill row's first group starts at the left"
    (hasStr html ".entry > .group:first-child, .entry-row > .group:first-child { text-align: left; }")
