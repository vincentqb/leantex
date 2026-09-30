import Tests.Support
import LeanTex.Cli.ImageAssets

open LeanTex.Core

namespace Tests

/-- Exporter doctype identifiers do not declare XML meaning. Actual DTD
declarations, named entity dependencies and parser errors must still fail
the same boundary. -/
def svgDoctypeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let parsed (events : String) := "SAX.startDocument()\n" ++ events ++ "\nSAX.endDocument()\n"
  let inert := "SAX.internalSubset(svg, -//W3C//DTD SVG 1.1//EN, missing.dtd)\n\
    SAX.externalSubset(svg, -//W3C//DTD SVG 1.1//EN, missing.dtd)"
  check ref "SVG doctype identity requests removal without refusing the drawing"
    (LeanTex.Cli.ImageAssets.svgSaxBoundary (parsed inert) == .ok true)
  check ref "SVG without a doctype needs no normalization"
    (LeanTex.Cli.ImageAssets.svgSaxBoundary (parsed "") == .ok false)
  for event in ["entityDecl", "attributeDecl", "elementDecl", "notationDecl",
      "unparsedEntityDecl", "resolveEntity", "getParameterEntity", "getEntity", "reference"] do
    check ref s!"SVG doctype still refuses {event}"
      (LeanTex.Cli.ImageAssets.svgSaxBoundary
        (parsed (inert ++ "\nSAX." ++ event ++ "(probe)"))).toOption.isNone
  for event in ["SAX.error: Entity undefined", "SAX.fatalError: Invalid document"] do
    check ref "SVG doctype never certifies a parser error between document callbacks"
      (LeanTex.Cli.ImageAssets.svgSaxBoundary (parsed event)).toOption.isNone
  for source in ["", inert, "SAX.startDocument()\n" ++ inert,
      inert ++ "\nSAX.endDocument()"] do
    check ref "SVG doctype never certifies an incomplete parse"
      (LeanTex.Cli.ImageAssets.svgSaxBoundary source).toOption.isNone

/-- Adding SVG candidates must not change which existing PDF or raster
source wins an extensionless request. In particular a companion SVG must
not shadow an uppercase PDF that can supply the selected poster. -/
def svgSourcePrecedenceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let candidates := Image.sourceCandidates "sequence"
  for ext in ["pdf", "png", "jpg", "jpeg", "PDF", "PNG", "JPG", "JPEG"] do
    check ref s!"SVG lookup preserves the existing .{ext} source"
      (candidates.find? (fun p => p == "sequence." ++ ext || p == "sequence.svg") ==
        some ("sequence." ++ ext))
  check ref "SVG lookup still accepts both SVG extensions after existing formats"
    (candidates.filter (Image.isSvg ·) == ["sequence.svg", "sequence.SVG"])

/-- Filenames are not URLs. Primary and media-selected image links encode
each filename byte while publication keeps the literal filename. A space
in `srcset` would otherwise be parsed as a descriptor, disabling fallback. -/
def svgAssetUrlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let source := "moving figure,#?%20é.svg"
  let imgs : Image.Store := { entries := #[
    { src := source, info := some { pxW := 20, pxH := 20 },
      webSvg := some "<svg/>".toUTF8, posterSvg := some "<svg/>".toUTF8 }] }
  let assetsDir := "output files/figures#1"
  let doc := (elabStr "\\includegraphics[alt={Moving square}]{image.svg}").1
  -- Use the image's IR value: percent/hash in a filename is not TeX syntax.
  let rename (i : Ir.Inline) : Ir.Inline := match i with
    | .image _ size alt => .image source size alt
    | i => i
  let doc := { doc with body := Ir.mapBlocks rename doc.body }
  let (_, tree, _) := HtmlDoc.emitTree { imgs, assetsDir } doc
  let images := elemAttrsList (· == "img") #[] tree.toList
  let sources := elemAttrsList (· == "source") #[] tree.toList
  let assetPrefix := "output%20files/figures%231/"
  let encoded := "moving%20figure%2C%23%3F%2520%C3%A9.svg"
  let key := Flate.contentKey "<svg/>".toUTF8 ++ "-"
  t "SVG primary URL encodes the asset directory and literal filename"
    (images.any fun (_, attrs) => attrs.contains ("src", assetPrefix ++ "i0-" ++ key ++ encoded))
  t "SVG print and reduced-motion srcset is one encoded URL"
    (sources.any fun (_, attrs) =>
      attrs.contains ("srcset", assetPrefix ++ "p0-" ++ key ++ encoded) &&
      attrs.contains ("media", "print, (prefers-reduced-motion: reduce)"))
  t "SVG URL encoding does not rename published files"
    ((HtmlDoc.imageAssets imgs).map (·.file) ==
      #["i0-" ++ key ++ source, "p0-" ++ key ++ source])
  let facts := HtmlDoc.a11yFacts true false tree
  t "encoded SVG URLs retain the accessible image alternative"
    (images.size == 1 && facts.imgs == 1 && facts.imgsUnnamed == 0 &&
      facts.hiddenTabStops == 0)

/-- A browser may retain a successful but blank image response across
document builds. The typed page must change that URL when its published
bytes change, including an independently selected print poster. Equal
published bytes keep their URL; a clock or an unrelated source does not
participate in the image's cache identity. -/
def imageContentUrlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let blank := "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"20\" height=\"20\"/>".toUTF8
  let drawn := "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"20\" height=\"20\">\
    <rect width=\"20\" height=\"20\" fill=\"red\"/></svg>".toUTF8
  let doc := (elabStr "\\includegraphics[alt={A square}]{chart.svg}").1
  let links (en : Image.Loaded) : Array String × Array String :=
    let (_, tree, _) := HtmlDoc.emitTree
      { imgs := { entries := #[en] }, assetsDir := "assets" } doc
    (tree.foldl HtmlDoc.imgSrcsOne #[],
      (elemAttrsList (· == "source") #[] tree.toList).filterMap fun (_, attrs) =>
        HtmlDoc.attrOf? attrs "srcset")
  let captured : Image.Loaded :=
    { src := "chart.svg", info := some { pxW := 20, pxH := 20 }, source := some blank }
  t "image refresh: changed captured source changes the emitted image URL"
    ((links captured).1 != (links { captured with source := some drawn }).1)
  let converted := { captured with webSvg := some blank }
  let updated := { converted with webSvg := some drawn }
  t "image refresh: changed converted face changes the emitted image URL"
    ((links converted).1 != (links updated).1)
  t "image refresh: captured face wins over a changed original source"
    (links updated == links { updated with source := some drawn })
  let poster := { updated with posterSvg := some blank }
  let posterUpdated := { poster with posterSvg := some drawn }
  t "image refresh: changed poster changes its emitted media URL alone"
    ((links poster).1 == (links posterUpdated).1 &&
      (links poster).2 != (links posterUpdated).2)
  t "image refresh: changed moving face keeps the unchanged poster URL"
    ((links poster).1 != (links { poster with webSvg := some blank }).1 &&
      (links poster).2 == (links { poster with webSvg := some blank }).2)
  for en in [captured, converted, updated, poster, posterUpdated] do
    let emitted := links en
    let assets := HtmlDoc.imageAssets { entries := #[en] }
    t "image refresh: every emitted URL names its literal published file"
      ((emitted.1 ++ emitted.2) ==
        assets.map (fun asset => HtmlDoc.imageAssetHref "assets" asset.file))
    t "image refresh: rebuilding the same captured bytes preserves its URLs"
      (links en == links { en with source := en.source.map (fun bytes => bytes.extract 0 bytes.size) })
  for stem in [String.ofList (List.replicate 216 'a'),
      String.ofList (List.replicate 110 'é'), String.ofList (List.replicate 60 '𝛼')] do
    let en := { posterUpdated with href := stem ++ ".svg" }
    let assets := HtmlDoc.imageAssets { entries := #[en] }
    t "image refresh: long primary and poster names fit a 255-byte filesystem component"
      (assets.all fun asset => asset.file.utf8ByteSize ≤ 255 && asset.file.endsWith ".svg")
    t "image refresh: shortened names still match the typed page's links"
      ((links en).1 ++ (links en).2 ==
        assets.map (fun asset => HtmlDoc.imageAssetHref "assets" asset.file))

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

/-- An SVG's PDF form is its print face, not evidence that the browser
should receive a PDF. The typed page must link a published SVG, with its
text alternative, even though layout reads vector PDF geometry. -/
def svgAssetChecks (ref : IO.Ref (List String)) : IO Unit := do
  svgDoctypeChecks ref
  svgSourcePrecedenceChecks ref
  svgAssetUrlChecks ref
  imageContentUrlChecks ref
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
