import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # Images

The image blocks, one file per the by-phase split: the decoders, the
alpha split, and colour-key transparency. -/

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
  match Image.decodePng plain with
  | .error e => failures ref s!"png decode: {e}"
  | .ok inf =>
    t "png dimensions" (inf.pxW == 64 && inf.pxH == 40)
    t "png default density is one pixel per point"
      (inf.dpiX == 72 && inf.width == Dim.pt 64 && inf.height == Dim.pt 40)
    t "png space and depth" (inf.space == .rgb && inf.bitDepth == 8)
    t "png idat survives" (inf.data == bytes [1, 2, 3])
  -- pHYs at 5906 pixels per metre is 150 dpi to the spec's own rounding.
  let physed := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++
    chunk "pHYs" (be32 5906 ++ be32 5906 ++ [1]) ++ chunk "IDAT" [0] ++ chunk "IEND" [])
  t "png pHYs density read"
    (match Image.decodePng physed with
     | .ok inf => inf.dpiX == 150 && inf.width == Dim.pt 64 * 72 / 150
     | .error _ => false)
  -- Refusals and the decode path, each with its reason: 16-bit alpha and
  -- interlace refuse; 8-bit alpha inflates and splits its filtered rows —
  -- never its pixels — and the alpha plane comes back as an SMask.
  t "png 16-bit alpha refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 16 6 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "16-bit").length == 2
     | .ok _ => false)
  -- 2×2 RGBA, row 0 filter None, row 1 filter Sub: known planes out.
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++
    [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
    chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" [])
  t "png alpha decodes to colour plus smask, planes filtered and compressed"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       inf.space == .rgb && inf.predictor && !inf.smask.isEmpty &&
       ((Flate.inflate inf.data 14).bind fun rows =>
         Flate.pngUnfilter rows 2 6 3) ==
         .ok (bytes [10, 20, 30, 40, 50, 60, 5, 5, 5, 6, 7, 8]) &&
       ((Flate.inflate inf.smask 6).bind fun rows =>
         Flate.pngUnfilter rows 2 2 1) == .ok (bytes [255, 128, 7, 16])
     | .error _ => false)
  -- The planes are the source's residuals under the source's own filters
  -- (None, then Sub), not a re-filtering: the split never saw a pixel.
  t "png alpha planes keep the source rows' filter bytes"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       Flate.inflate inf.data 14 == .ok (bytes [0, 10, 20, 30, 40, 50, 60, 1, 5, 5, 5, 1, 2, 3]) &&
       Flate.inflate inf.smask 6 == .ok (bytes [0, 255, 128, 1, 7, 9])
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
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
      chunk "IDAT" (Flate.deflate rgbaRaw).toList ++ chunk "IEND" [])) with
     | .ok inf => inf.space == .rgb && !inf.smask.isEmpty
     | .error _ => false)
  -- The driver's image-cache serialization inverts exactly
  -- (`decodeBin_encodeBin_id`'s statement, witnessed on a real decode).
  t "image cache serialization round-trips a decoded alpha png"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       (match Image.decodeBin (Image.encodeBin inf) with
        | some back =>
          back.format == inf.format && back.pxW == inf.pxW && back.pxH == inf.pxH &&
          back.dpiX == inf.dpiX && back.dpiY == inf.dpiY &&
          back.bitDepth == inf.bitDepth && back.space == inf.space &&
          back.palette == inf.palette && back.data == inf.data &&
          back.predictor == inf.predictor && back.smask == inf.smask &&
          back.form.isNone
        | none => false)
     | .error _ => false)
  t "image cache decode rejects foreign bytes"
    ((Image.decodeBin (bytes [1, 2, 3])).isNone &&
     (Image.decodeBin ByteArray.empty).isNone)
  t "image cache decode rejects a truncated entry"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       let blob := Image.encodeBin inf
       (Image.decodeBin (blob.extract 0 (blob.size - 1))).isNone
     | .error _ => false)
  t "png interlace refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 1) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "interlaced").length == 2
     | .ok _ => false)
  t "png indexed without PLTE refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png indexed with PLTE carries the palette"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "PLTE" [0, 0, 0, 255, 255, 255] ++ chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .ok inf => inf.space == .indexed && inf.palette.size == 6
     | .error _ => false)
  t "png zero size refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 0 8 8 2 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png lying chunk length refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 0) ++
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
  match Image.decodeJpeg jpg with
  | .error e => failures ref s!"jpeg decode: {e}"
  | .ok inf =>
    t "jpeg dimensions" (inf.pxW == 10 && inf.pxH == 20)
    t "jpeg jfif density read" (inf.dpiX == 144 && inf.width == Dim.pt 10 * 72 / 144)
    t "jpeg embeds whole" (inf.data.size == jpg.size)
  t "jpeg cmyk refused"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ sof0 4 4 4 ++ [0xFF, 0xDA])) with
     | .error e => (e.splitOn "CMYK").length == 2
     | .ok _ => false)
  t "jpeg aspect-only density keeps the default"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ jfif 0 1 1 ++ sof0 4 4 1 ++
      [0xFF, 0xDA])) with
     | .ok inf => inf.dpiX == 72 && inf.space == .gray
     | .error _ => false)
  t "decode rejects foreign bytes" ((Image.decode (bytes [0, 1, 2, 3])).isOk == false)
  t "decode rejects empty" ((Image.decode (bytes [])).isOk == false)

  -- The shipped fixtures: what `lake test` sees on every host.
  let pngData ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpgData ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let alphaData ← IO.FS.readBinFile "tests/corpus/rects-alpha.png"
  let pngInfo := Image.decode pngData
  let jpgInfo := Image.decode jpgData
  let alphaInfo := Image.decode alphaData
  t "shipped png decodes 64x40 rgb"
    (match pngInfo with
     | .ok inf => inf.format == .png && inf.pxW == 64 && inf.pxH == 40 &&
        inf.space == .rgb && inf.width == Dim.pt 64
     | .error _ => false)
  t "shipped jpeg decodes 64x40"
    (match jpgInfo with
     | .ok inf => inf.format == .jpeg && inf.pxW == 64 && inf.pxH == 40 &&
        inf.width == Dim.pt 64
     | .error _ => false)
  -- The RGBA fixture went through a real compressor (zlib level 9), so
  -- decoding it exercises the Huffman paths of the inflater; its alpha
  -- fades 255 down to 15 across the rectangle and vanishes outside it.
  t "shipped alpha png decodes with its mask"
    (match alphaInfo with
     | .ok inf =>
       inf.pxW == 48 && inf.pxH == 32 && inf.space == .rgb && !inf.smask.isEmpty &&
       (match (Flate.inflate inf.smask (32 * 49)).bind fun rows =>
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
    { src := "rects.png", info := pngInfo.toOption },
    { src := "rects.jpg", info := jpgInfo.toOption },
    { src := "rects-alpha.png", info := alphaInfo.toOption }] }
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
           | .image "rects.png" _ alt => alt == "A mark"
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
  let (figHtml, _) := HtmlDoc.emit hcfg figDoc
  t "html figure image with alt and intrinsic size"
    ((figHtml.splitOn "<img src=\"rects.png\" alt=\"A mark\" width=\"64\" height=\"40\">").length == 2)
  let (twDoc, _) := Elab.run "t" "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let (twHtml, _) := HtmlDoc.emit hcfg twDoc
  t "html width fraction becomes a percentage"
    ((twHtml.splitOn "style=\"width: 80%; height: auto\"").length == 2)
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
        | .image _ spec _ => spec.height == some { sp := Dim.pt 8 }
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
  t "html names the resolved file, not the bare spelling"
    (let store2 : Image.Store := { entries := #[
      { src := "figures/plot", href := "figures/plot.png", info := pngInfo.toOption }] }
     let (h, _) := HtmlDoc.emit { imgs := store2 }
       ((Elab.run "t" "\\includegraphics{figures/plot}").1)
     (h.splitOn "<img src=\"figures/plot.png\"").length == 2)

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
    match Image.decodePng b with
    | .ok inf => some inf.colorKey
    | .error _ => none
  let refusedNaming (b : ByteArray) (word : String) : Bool :=
    match Image.decodePng b with
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
       | some back => back.colorKey == inf.colorKey && back.colorKey == #[0, 0] &&
           back.palette == inf.palette && back.data == inf.data && back.space == .indexed &&
           back.bitDepth == inf.bitDepth && back.pxW == 4 && back.pxH == 4
       | none => false)
    t "image cache magic is LTIMG2" (blob.extract 0 6 == "LTIMG2".toUTF8)
    t "image cache rejects a stale LTIMG1 entry" ((Image.decodeBin (blob.set! 5 49)).isNone)
    t "image cache rejects a lying key count"
      ((Image.decodeBin (blob.set! 44 (blob[44]! + 1))).isNone)
  -- A wide key (the truecolour ranges) round-trips too.
  t "image cache round-trips a six-range key"
    (match Image.decode rgbPng with
     | .ok inf => (Image.decodeBin (Image.encodeBin inf)).map (·.colorKey) ==
         some #[10, 10, 20, 20, 30, 30]
     | .error _ => false)

