import Tests.Support
import LeanTex.Cli.ImageAssets

open LeanTex.Core

namespace Tests

/-- librsvg supplies a static drawing, not a selected SMIL frame. Reject
non-first posters before invoking any converter. Empty input makes this
guard independent of host tools; a converter error cannot satisfy it. -/
def svgPosterChecks (ref : IO.Ref (List String)) : IO Unit := do
  for page in [PdfRead.PageSelection.last, .number 2] do
    let result ← LeanTex.Cli.ImageAssets.svgPlan .default ByteArray.empty page
    check ref s!"SVG poster {repr page} requires its PDF frame sequence"
      (match result with
        | .error err => hasStr err "selected poster requires a PDF frame sequence"
        | .ok _ => false)

/-- The shared browser-face plan (`HtmlDoc.facePlan`/`applyFacePlan`), and
the regression that matters most: the hermetic store the scoreboard emits
from (`facedStore`) now carries the converted success shape, so hermetic
`emit` links the published converted asset exactly as a successful real
build does — where the raw store, which the hermetic builder used before,
emitted only a placeholder. -/
def facePlanChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let data ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  let info := (Image.decode data).toOption
  t "box.pdf decodes to a vector form" (info.any (·.form.isSome))
  -- A PDF image plans a converted primary of its selected page; a raster
  -- and a boundary picture plan no conversion.
  let pdfEn : Image.Loaded := { src := "box.pdf", info, source := some data }
  t "PDF image plans a converted primary face"
    (HtmlDoc.facePlan pdfEn == .convertedPrimary (.pdfPage .first))
  t "a page-2 PDF plans that page's conversion"
    (HtmlDoc.facePlan { pdfEn with page := .number 2 }
      == .convertedPrimary (.pdfPage (.number 2)))
  t "an animated PDF with a companion plans the moving-companion shape"
    (HtmlDoc.facePlan { pdfEn with animated := true, companion := some "<svg/>".toUTF8 }
      == .animatedWithCompanion (.pdfPage .first))
  t "a boundary picture plans no browser face"
    (HtmlDoc.facePlan { pdfEn with src := Ir.picSrcPrefix ++ "abc" } == .keep)
  -- Without the plan applied, the raw store links the unconverted PDF
  -- itself and publishes no browser asset: the shape the hermetic builder
  -- emitted before — a face no browser decodes.
  let raw : Image.Store := { entries := #[pdfEn] }
  let doc := (elabStr (dvDoc "" "\\includegraphics[alt={A box}]{box.pdf}")).1
  let (_, rawTree, _) := HtmlDoc.emitTree { imgs := raw } doc
  let rawSrcs := rawTree.foldl HtmlDoc.imgSrcsOne #[]
  t "raw PDF store links the unconverted PDF and publishes no asset (pre-fix shape)"
    (rawSrcs == #["box.pdf"] && (HtmlDoc.imageAssets raw).isEmpty)
  -- The shared hermetic executor gives the store the converted success
  -- shape, so hermetic emit links the published converted asset — exactly
  -- the markup, src and asset name a successful real build produces.
  let faced := HtmlDoc.facedStore raw
  let (_, facedTree, ds) := HtmlDoc.emitTree { imgs := faced, assetsDir := "assets" } doc
  let srcs := facedTree.foldl HtmlDoc.imgSrcsOne #[]
  t "faced PDF store publishes the converted browser asset"
    ((HtmlDoc.imageAssets faced).map (·.file) == #["i0-box.svg"])
  t "faced PDF store: typed HTML links the converted asset"
    (srcs == #["assets/i0-box.svg"])
  t "faced PDF store: the converted face carries nonempty stand-in bytes"
    (((faced.get? 0).bind (·.webSvg)).any (!·.isEmpty))
  t "faced PDF store: no PDF-only placeholder diagnostic"
    (!(ds.any (·.code == "W0605")))
  -- applyFacePlan is the one door that sets the face: a failed mandatory
  -- conversion becomes webError, not a published face.
  let failed := HtmlDoc.applyFacePlan pdfEn (.convertedPrimary (.pdfPage .first))
    { bytes := .error "pdftocairo exited 1" }
  t "applyFacePlan records a mandatory conversion failure as webError"
    (failed.webError == some "pdftocairo exited 1" && failed.webSvg.isNone)

/-- The expected converted-image face identities the accounting matches
against are read from the typed `HtmlDoc.browserFaceAssets` projection — the
`.svg` assets of a store. Converted image faces (`isImageFaceName`) and
boundary picture SVGs (`isBoundaryFaceName`) are two disjoint publication
paths: an image face's name is an `i`/`p` `.svg`, a boundary picture's SVG is
`Ir.picHash body ++ ".svg"` — a hex-digit stem, never `i`/`p`, proved by
`HtmlDoc.isImageFaceName_boundary` from `Ir.picHash_chars_mem`. -/
def expectedFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let data ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  let info := (Image.decode data).toOption
  let pdfEn : Image.Loaded := { src := "box.pdf", info, source := some data }
  -- A converted PDF publishes exactly one SVG browser face; the projection
  -- is read from imageAssets, not rebuilt by hand.
  let faced := HtmlDoc.facedStore { entries := #[pdfEn] }
  t "browserFaceAssets projects the one converted SVG face of a PDF"
    ((HtmlDoc.browserFaceAssets faced).map (·.file) == #["i0-box.svg"])
  -- An animated PDF with a valid companion publishes a moving primary and a
  -- static poster — two SVG faces, both captured by the oracle.
  let animated := HtmlDoc.facedStore
    { entries := #[{ pdfEn with animated := true, companion := some "<svg/>".toUTF8 }] }
  t "browserFaceAssets projects both faces of an animated companion"
    ((HtmlDoc.browserFaceAssets animated).map (·.file) == #["i0-box.svg", "p0-box.svg"])
  -- A real PNG raster ships its own bytes under its own name and publishes no
  -- SVG browser face at all — the projection is empty.
  let pngData ← IO.FS.readBinFile "tests/corpus/rects.png"
  let pngInfo := (Image.decode pngData).toOption
  t "the PNG fixture decodes to a raster (no vector form)"
    (pngInfo.any (·.form.isNone))
  let rasterEn : Image.Loaded :=
    { src := "rects.png", info := pngInfo, source := some pngData }
  let rasterStore := HtmlDoc.facedStore { entries := #[rasterEn] }
  t "a raster publishes no SVG browser face"
    (HtmlDoc.browserFaceAssets rasterStore).isEmpty
  t "a raster still ships its own bytes under its own-extension name"
    ((HtmlDoc.imageAssets rasterStore).map (·.file) == #["i0-rects.png"])
  -- The classifier separates image faces from boundary pictures, and rejects
  -- a non-.svg i/p asset name as its docstring promises.
  t "a converted primary name is classified as an image face"
    (HtmlDoc.isImageFaceName (HtmlDoc.imageAssetName 0 "box.svg"))
  t "a static poster name is classified as an image face"
    (HtmlDoc.isImageFaceName (HtmlDoc.imagePosterName 3 pdfEn))
  t "a non-.svg i/p asset name (a raster) is not an image face"
    (!HtmlDoc.isImageFaceName (HtmlDoc.imageAssetName 0 "rects.png") &&
      !HtmlDoc.isImageFaceName "i0-box.pdf" && !HtmlDoc.isImageFaceName "p0-box.png")
  t "a boundary picture's picHash SVG name is a boundary face, not an image face"
    (HtmlDoc.isBoundaryFaceName (Ir.picHash "\\draw (0,0) -- (1,1);" ++ ".svg") &&
      !HtmlDoc.isImageFaceName (Ir.picHash "\\draw (0,0) -- (1,1);" ++ ".svg") &&
      !HtmlDoc.isImageFaceName (Ir.picHash "\\node {label};" ++ ".svg"))
  t "a raster source name is neither an image nor a boundary face"
    (!HtmlDoc.isImageFaceName "photo.png" && !HtmlDoc.isBoundaryFaceName "photo.png")

/-- An SVG's PDF form is its print face, not evidence that the browser
should receive a PDF. The typed page must link a published SVG, with its
text alternative, even though layout reads vector PDF geometry. -/
def svgAssetChecks (ref : IO.Ref (List String)) : IO Unit := do
  facePlanChecks ref
  expectedFaceChecks ref
  svgPosterChecks ref
  let t := check ref
  t "extensionless image lookup includes SVG"
    ((Image.sourceCandidates "diagram").contains "diagram.svg")
  let data ← IO.FS.readBinFile "tests/corpus/figures/box.pdf"
  let info := (Image.decode data).toOption
  t "SVG asset probe has a vector print face" (info.any (·.form.isSome))
  let imgs : Image.Store := { entries := #[{ src := "diagram.svg", info }] }
  let doc := (elabStr "\\includegraphics[alt={A moving square}]{diagram.svg}").1
  let (_, body, diags) := HtmlDoc.emitTree { imgs, assetsDir := "assets" } doc
  let srcs := body.foldl HtmlDoc.imgSrcsOne #[]
  t "SVG print face still publishes the SVG browser asset"
    ((HtmlDoc.imageAssets imgs).map (·.file) == #["i0-diagram.svg"])
  t "typed HTML links the published SVG"
    (srcs == #["assets/i0-diagram.svg"])
  t "SVG browser face has no PDF-only placeholder diagnostic"
    (!(diags.any (·.code == "W0605")))
  -- The native decode can succeed before the mandatory browser poster
  -- conversion fails. Neither a .svg extension nor captured moving bytes
  -- can certify the missing static face.
  let reason := "rsvg-convert exited 19: poster unavailable"
  for (src, href) in [("diagram.svg", ""), ("diagram.pdf", ""), ("diagram", "diagram.svg")] do
    let failed : Image.Store := { entries := #[
      { src, href, info, webSvg := some "<svg/>".toUTF8, webError := some reason }] }
    let source := "\\includegraphics[alt={A moving square}]{" ++ src ++ "}"
    let doc := (elabStr (dvDoc "" source)).1
    let (_, tree, ds) := HtmlDoc.emitTree { imgs := failed } doc
    let nodes := elemAttrsList (fun _ => true) #[] tree.toList
    t s!"failed browser conversion {src}: no source bytes publish"
      (HtmlDoc.imageAssets failed).isEmpty
    t s!"failed browser conversion {src}: no image or media URL ships"
      (!(nodes.any fun (tag, _) => tag == "img" || tag == "source" || tag == "object"))
    t s!"failed browser conversion {src}: a named placeholder ships"
      (nodes.any fun (tag, attrs) => tag == "span" &&
        attrs.contains ("role", "img") &&
        attrs.contains ("aria-label", "A moving square") &&
        attrs.contains ("data-image-src", if href.isEmpty then src else href))
    let facts := HtmlDoc.a11yFacts true false tree
    t s!"failed browser conversion {src}: the accessibility judge counts the placeholder"
      (facts.imgs == 1 && facts.imgsUnnamed == 0)
    let losses := ds.filter (·.code == "W0605")
    t s!"failed browser conversion {src}: its reason is accounted once"
      (losses.size == 1 && losses.any (fun d => hasStr d.message reason))
    let pdfOnly := (elabStr (dvDoc ""
      ("\\begin{ifbackend}{pdf}" ++ source ++ "\\end{ifbackend}"))).1
    let (_, _, hiddenDs) := HtmlDoc.emitTree { imgs := failed } pdfOnly
    t s!"failed browser conversion {src}: an absent HTML include has no loss"
      (!(hiddenDs.any (·.code == "W0605")))

  -- A resolved filename is not a request identity: selected pages,
  -- animation posters and extensionless aliases can share it. The shipped
  -- placeholders must retain the exact entry and its own failure, even
  -- when a different request precedes it in the store or is PDF-only.
  let selected : Image.Store := { entries := #[
    { src := "sequence.pdf", page := .number 1, info, webError := some "page one failed" },
    { src := "sequence.pdf", page := .number 2, info, webError := some "page two failed" },
    { src := "sequence.pdf", page := .number 2, animated := true, info,
      webError := some "animation poster failed" },
    { src := "sequence.pdf", info, webError := some "default page failed" },
    { src := "sequence.pdf", page := .number 3, info },
    { src := "sequence", href := "sequence.pdf", info, webError := some "alias failed" }] }
  let includes := #[
    "\\includegraphics[page=1,alt={First}]{sequence.pdf}",
    "\\includegraphics[page=2,alt={Second}]{sequence.pdf}",
    "\\animategraphics[poster=1,alt={Moving}]{17}{sequence.pdf}{}{}",
    "\\includegraphics[alt={Default}]{sequence.pdf}",
    "\\includegraphics[page=3,alt={Unconverted}]{sequence.pdf}",
    "\\includegraphics[alt={Alias}]{sequence}"]
  let probes : Array (String × String × Array Nat) := #[
    ("later page alone", includes[1]!, #[1]),
    ("repeated page", includes[1]! ++ includes[1]!, #[1, 1]),
    ("two selected pages", includes[1]! ++ includes[0]!, #[1, 0]),
    ("ordinary and animated", includes[1]! ++ includes[2]!, #[1, 2]),
    ("default page", includes[3]!, #[3]),
    ("unconverted page", includes[4]!, #[4]),
    ("resolved alias", includes[1]! ++ includes[5]!, #[1, 5]),
    ("absent earlier request",
      "\\begin{ifbackend}{pdf}" ++ includes[0]! ++ "\\end{ifbackend}" ++ includes[1]!, #[1])]
  for (name, source, indices) in probes do
    let (_, tree, ds) := HtmlDoc.emitTree { imgs := selected } (elabStr (dvDoc "" source)).1
    let marked := (elemAttrsList (fun _ => true) #[] tree.toList).filterMap fun (_, attrs) =>
      (HtmlDoc.attrOf? attrs "data-image-index").bind String.toNat?
    t s!"image failure identity {name}: each emitted use keeps its store entry"
      (marked == indices)
    let unique := indices.foldl (fun acc k =>
      if acc.contains k then acc else acc.push k) #[]
    let losses := ds.filter (·.code == "W0605")
    t s!"image failure identity {name}: each request is named once, in page order"
      (losses.size == unique.size && (unique.zip losses).all fun (k, d) =>
        d.subject == some s!"img:{k}:sequence.pdf" &&
        match selected.entries[k]!.webError with
        | some err => hasStr d.message err
        | none => hasStr d.message "PDF page no browser decodes")
    t s!"image failure identity {name}: distinct losses survive site accounting"
      (losses.size == unique.size && (Diag.tallySites losses).all (·.sites == 1))

end Tests
