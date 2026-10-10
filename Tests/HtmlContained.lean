module

public import Tests.Support
public import LeanTex.Cli.Publication
public import LeanTex.Cli.ImageAssets

public section

open LeanTex.Core LeanTex.Cli.Publication

namespace Tests

/-- Raw style/script payloads owe an HTML raw-text parsing context. Foreign
content and title RCDATA can reinterpret the payload as markup; a void
element discards its children. Refuse those placements rather than certify
the dependency reading of bytes the browser does not read as CSS or script. -/
def htmlContainedRawContextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let close (head body : Array Html.Node) :=
    HtmlResource.close #[] #[] HtmlDoc.deckScript "en" head body
  let escape := "</svg><img src=\"https://remote.invalid/closure.png\">"
  let witness := #[Html.elem "svg" #[Html.Node.style escape]]
  let expected := "<!DOCTYPE html>\n<html lang=\"en\">\n  <head></head>\n  <body>\n" ++
    "    <svg>\n      <style>\n</svg><img src=\"https://remote.invalid/closure.png\">\n" ++
    "      </style>\n    </svg>\n  </body>\n</html>\n"
  t "contained raw context: exact serialized foreign-content witness"
    (Html.document "en" #[] witness == expected)
  t "contained raw context: SVG escape cannot become a closed page"
    (!(close #[] witness).isOk)
  for (name, tag, payload) in [
      ("SVG", "svg", escape),
      ("mixed-case SVG", "SvG", escape),
      ("MathML", "math", "</math><img src=\"https://remote.invalid/closure.png\">"),
      ("title RCDATA", "title", "</title><img src=\"https://remote.invalid/closure.png\">"),
      ("void child", "img", "p { color: red }")] do
    for (kind, node) in [("style", Html.Node.style payload),
        ("JSON data script", Html.Node.script #[("type", "application/ld+json")] payload)] do
      t ("contained raw context: refuses " ++ kind ++ " below " ++ name)
        (!(close #[] #[Html.elem tag #[node]]).isOk)
  for (tag, child) in [("svg", "g"), ("math", "mrow"), ("title", "span")] do
    for node in [Html.Node.style "p { color: red }", Html.Node.script #[] HtmlDoc.deckScript] do
      t ("contained raw context: ordinary descendants cannot reset " ++ tag)
        (!(close #[] #[Html.elem tag #[Html.elem child #[Html.elem "div" #[node]]]]).isOk)
  for tag in ["textarea", "xmp", "iframe", "noembed", "noframes", "noscript", "plaintext"] do
    t ("contained raw context: unsupported text context remains refused: " ++ tag)
      (!(close #[] #[Html.elem tag #[Html.Node.style escape]]).isOk)
  let css := "p { color: rgb(1, 2, 3) }"
  let head := #[Html.Node.style css,
    Html.Node.script #[("type", "application/ld+json")] "{\"name\":\"Contained\"}"]
  let body := #[Html.elem "svg", Html.elem "math", Html.elem "p" #[Html.text "Contained"],
    Html.Node.script #[] HtmlDoc.deckScript]
  match close head body with
  | .error _ => t "contained raw context: head style and body deck script remain supported" false
  | .ok page =>
    t "contained raw context: valid raw payloads survive checked serialization"
      (hasStr page.render css && hasStr page.render HtmlDoc.deckScript &&
        hasStr page.render "{\"name\":\"Contained\"}")
  t "contained raw context: ordinary HTML nesting remains supported"
    ((close #[] #[Html.elem "section" #[Html.elem "div"
      #[Html.Node.style css, Html.Node.script #[] HtmlDoc.deckScript]]]).isOk)
  let quoted := #[Html.elem "svg" #[Html.elem "text" #[Html.text escape]]]
  t "contained raw context: escaped foreign text remains supported"
    ((close #[] quoted).isOk &&
      hasStr (Html.document "en" #[] quoted) "&lt;/svg&gt;&lt;img")

/-- A CSS at-keyword starts at `@`, even beside another token. In particular,
HTML's legacy CSS comment opener must not hide an import from the dependency
policy: the browser ignores the opener and still fetches the stylesheet. -/
def htmlContainedCssAtRuleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let close (head body : Array Html.Node) :=
    HtmlResource.close #[] #[] HtmlDoc.deckScript "en" head body
  let imported := "@import \"https://example.invalid/style.css\";"
  let css := "<!--" ++ imported ++ "-->"
  let tree := #[Html.Node.style css]
  t "contained CSS at-keyword: serialized comment opener preserves the import"
    (hasStr (Html.document "en" tree #[]) ("<style>\n" ++ css ++ "\n"))
  t "contained CSS at-keyword: browser-active legacy comment import is refused"
    (!(close tree #[]).isOk)
  for leading in ["", "<!--", "--", "token", "1", "@media"] do
    for rule in [imported, "@IMPORT 'missing.css';", "@namespace 'missing.svg';"] do
      t ("contained CSS at-keyword: preceding token cannot absorb @: " ++ leading)
        (HtmlResource.cssRequests (leading ++ rule) == HtmlResource.cssRequests rule)
      t ("contained CSS at-keyword: style attribute shares the policy: " ++ leading)
        (!(close #[] #[Html.elem "p" #[] #[("style", leading ++ rule)]]).isOk)
  for css in ["<!--@media screen { p { color: red } }-->",
      "/* <!--@import 'missing.css'; */ p { color: red }",
      "p::before { content: \"<!--@import 'missing.css';\" }"] do
    t "contained CSS at-keyword: supported rules and inert mentions remain accepted"
      ((close #[.style css] #[]).isOk)

/-- Active attribution requests are not rendering resources, and script escape
states can consume following HTML even for JSON or an approved constant.
Admission owes both boundaries independently of the current emitter. -/
def htmlContainedAdmissionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let bytes := svgDocument "<rect width=\"1\" height=\"1\"/>"
  let image : HtmlResource.Embedded := { media := .svg, bytes }
  let close := HtmlResource.close #[image] #[bytes] HtmlDoc.deckScript "en"
  for name in ["attributionsrc", "AtTrIbUtIoNsRc"] do
    for (kind, value) in [("empty", ""), ("single URL", "https://example.invalid/attribution"),
        ("URL list", "https://example.invalid/first https://example.invalid/second"),
        ("captured URL", image.uri)] do
      for (tag, node) in [
          ("img", Html.elem "img" #[] #[("src", image.uri), (name, value)]),
          ("a", Html.elem "a" #[] #[("href", "https://example.invalid/reading"), (name, value)]),
          ("script", Html.Node.script #[("type", "application/ld+json"), (name, value)] "{}")] do
        t ("contained attribution refuses " ++ name ++ " on " ++ tag ++ ": " ++ kind)
          (!(close #[] #[node]).isOk)
  t "contained attribution: similarly named data and inert attributes remain supported"
    ((close #[] #[Html.elem "img" #[] #[("src", image.uri), ("alt", "Captured square"),
      ("data-attributionsrc", "https://example.invalid/attribution"),
      ("title", "attributionsrc <!--<script>"), ("loading", "lazy")]]).isOk)
  let following := #[Html.elem "p" #[Html.text "Following"] #[("id", "following")]]
  for text in ["<!--<script>", "<!--<ScRiPt/>", "<!--", "</ScRiPt >"] do
    let raw := "{\"name\":\"" ++ text ++ "\"}"
    for attrs in [#[], #[("type", "application/ld+json")]] do
      t ("contained script: MIME or constant approval cannot bypass parser control: " ++ text)
        (!(HtmlResource.close #[] #[] raw "en" #[.script attrs raw] following).isOk)
    let escaped := "{\"name\":\"" ++ Html.escapeJson text ++ "\"}"
    match close #[.script #[("type", "application/ld+json")] escaped] following with
    | .error _ => t "contained script: escaped JSON data remains supported" false
    | .ok page =>
      t "contained script: escaped JSON data and following element serialize intact"
        (hasStr page.render escaped && hasStr page.render "<p id=\"following\">Following</p>")
  for text in ["<script>", "1 < 2", "-->"] do
    let raw := "{\"name\":\"" ++ text ++ "\"}"
    t "contained script: harmless raw JSON text remains supported"
      ((close #[.script #[("type", "application/ld+json")] raw] following).isOk)

/-- Prepared closure retains exact captured bytes, rejects unready entries even
among duplicates, and preserves the typed carriers and first refusal. -/
def htmlContainedIndexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let close (resources : Array HtmlResource.Embedded) (checked : Array ByteArray) :=
    HtmlResource.close resources checked HtmlDoc.deckScript "en"
  let image (uri : String) := Html.elem "img" #[] #[("src", uri), ("alt", "Captured square")]
  let captures : Array HtmlResource.Embedded := (Array.range 32).map fun i =>
    { media := .svg, bytes := svgDocument s!"<rect id=\"square-{i}\" width=\"1\" height=\"1\"/>" }
  let checked := captures.map (·.bytes)
  let urls := captures.map (·.uri)
  let invalid : Array HtmlResource.Embedded :=
    #[.png, .jpeg, .ico, .svg, .ttf, .otf].map fun media =>
      { media, bytes := "not an admitted resource".toUTF8 }
  let resources := invalid ++ captures ++ captures
  let head := #[Html.Node.style ("p { background: url(\"" ++ urls[0]! ++ "\") }")]
  let repeated := (Array.range 512).map fun i => urls[i % urls.size]!
  let body := repeated.map image
  match close resources checked head body with
  | .error _ => t "contained index: repeated assets close with duplicates and unused invalid entries" false
  | .ok page =>
    let images := elemAttrsList (· == "img") #[] page.body.toList
    t "contained index: every repeated typed carrier survives in order"
      (images == repeated.map (fun uri => ("img", #[("src", uri), ("alt", "Captured square")])))
    t "contained index: checked serialization is exactly the supplied tree"
      (page.render == Html.document "en" head body)
  for resource in invalid do
    t s!"contained index: an unready {repr resource.media} entry cannot resolve its own URI"
      (!(close resources checked head (body.push (image resource.uri))).isOk)
  for (media, signature) in [
      (HtmlResource.Media.png, bytes [137, 80, 78, 71, 13, 10, 26, 10]),
      (.jpeg, bytes [255, 216, 255]), (.ico, bytes [0, 0, 1, 0]),
      (.ttf, bytes [0, 1, 0, 0]), (.otf, "OTTO".toUTF8)] do
    let resource : HtmlResource.Embedded := { media, bytes := signature ++ "captured".toUTF8 }
    let carrier (uri : String) := match media with
      | .ttf | .otf => Html.Node.style ("@font-face { font-family: Probe; src: url(\"" ++ uri ++ "\"); }")
      | .png | .jpeg | .ico | .svg => image uri
    t s!"contained index: admitted {repr media} signature still resolves"
      ((close #[resource] #[] #[] #[carrier resource.uri]).isOk)
    for n in [:signature.size] do
      let truncated := { resource with bytes := signature.extract 0 n }
      t s!"contained index: truncated {repr media} signature {n} remains refused"
        (!(close #[truncated] #[truncated.bytes] #[] #[carrier truncated.uri]).isOk)
    let changed := { resource with bytes := signature ++ "changed".toUTF8 }
    t s!"contained index: {repr media} readiness cannot stand in for the captured bytes"
      (!(close #[changed] #[] #[] #[carrier resource.uri]).isOk &&
        (close #[changed] #[] #[] #[carrier changed.uri]).isOk)
  let original := captures[0]'(by simp [captures])
  let changed := { original with bytes := svgDocument "<rect width=\"2\" height=\"1\"/>" }
  t "contained index: replacing SVG bytes cannot reuse the old attestation"
    (!(close #[changed] #[original.bytes] #[] #[image changed.uri]).isOk)
  t "contained index: new SVG approval admits only the new captured URI"
    ((close #[changed] #[changed.bytes] #[] #[image changed.uri]).isOk &&
      !(close #[changed] #[changed.bytes] #[] #[image original.uri]).isOk)
  t "contained index: independent closures keep their own capture and approval"
    ((close #[original] #[original.bytes] #[] #[image original.uri]).isOk &&
      !(close #[original] #[changed.bytes] #[] #[image original.uri]).isOk)
  let missing := "first-missing.svg"
  let later := "later-missing.svg"
  let why := "HTML rendering URL " ++ reprStr missing ++ " has no embedded, validated resource"
  for (extraHead, extraBody, expected) in [
      (head, body ++ #[image missing, image later], why),
      (head.push (.style ("p { background: url(" ++ missing ++ ") }")), body.push (image later), why),
      (head, body ++ #[Html.elem "svg" #[Html.elem "use" #[] #[("href", "#bad fragment")]],
        image missing], "unsupported SVG fragment reference " ++ reprStr "#bad fragment"),
      (head, body ++ #[Html.Node.script #[] "unapproved()", image missing],
        "an HTML script is not the constant deck script"),
      (head, body ++ #[Html.elem "svg" #[Html.Node.style "p { color: red }"], image missing],
        "raw HTML style is inside an unsupported parsing context")] do
    match close resources checked extraHead extraBody with
    | .error actual => t "contained index: first refusal retains projection order and exact detail" (actual == expected)
    | .ok _ => t "contained index: an unknown URL or refused context cannot close" false
  t "contained index: an empty tree needs no resource evidence"
    ((close invalid #[] #[] #[]).isOk)

/-- A single HTML file carries the exact captured rendering bytes in its
actual typed carriers. These assertions fail on the sibling-file emitter;
closure of nested SVG/CSS references is a separate, stricter obligation. -/
def htmlContainedChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  htmlContainedRawContextChecks ref
  htmlContainedCssAtRuleChecks ref
  htmlContainedAdmissionChecks ref
  htmlContainedIndexChecks ref
  let t := check ref
  let moving := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let poster := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let body := "\\includegraphics[alt={A captured square}]{figure.svg} " ++
    "\\href{https://example.invalid/reading}{Further reading}"
  let doc := (elabStr body).1
  let imgs : Image.Store := { entries := #[
    { src := "figure.svg", source := some moving, posterSvg := some poster,
      info := some { pxW := 20, pxH := 20 } }] }
  let cfg : HtmlDoc.Config := { imgs, fonts := some fonts, mdHref := some "reading.md" }
  let (head, tree, _) := HtmlDoc.emitTree cfg doc
  let images := elemAttrsList (· == "img") #[] tree.toList
  let sources := elemAttrsList (· == "source") #[] tree.toList
  let expectedMoving ← htmlDataOracle "image/svg+xml" moving
  let expectedPoster ← htmlDataOracle "image/svg+xml" poster
  t "contained HTML: moving image carries captured bytes"
    (images.size == 1 && images.all (fun (_, attrs) =>
      attrs.contains ("src", expectedMoving)))
  t "contained HTML: static media source carries its own captured bytes"
    (sources.size == 1 && sources.all (fun (_, attrs) =>
      attrs.contains ("srcset", expectedPoster) &&
      attrs.contains ("media", "print, (prefers-reduced-motion: reduce)")))
  let converted := { imgs with entries := imgs.entries.map fun en =>
    { en with source := some "replaced original".toUTF8, webSvg := some moving } }
  let (_, convertedTree, _) := HtmlDoc.emitTree { cfg with imgs := converted } doc
  t "contained HTML: converted browser bytes win over original bytes"
    ((elemAttrsList (· == "img") #[] convertedTree.toList).all fun (_, attrs) =>
      attrs.contains ("src", expectedMoving))
  let css := treeCssList "" head.toList
  for ff in HtmlDoc.shipFaces fonts do
    let f := fonts.get ff.index
    let expected ← htmlDataOracle (if f.isCff then "font/otf" else "font/ttf") f.data
    t "contained HTML: font rule carries its resolved face byte for byte"
      (hasStr css ("src: url(\"" ++ expected ++ "\") format(\"" ++ ff.format ++ "\")"))
  let links := elemAttrsList (· == "a") #[] tree.toList
  t "contained HTML: outgoing reading link remains navigation"
    (links.any fun (_, attrs) => attrs.contains ("href", "https://example.invalid/reading"))
  t "contained HTML: markdown alternate remains navigation"
    ((elemAttrsList (· == "link") #[] head.toList).any fun (_, attrs) =>
      attrs.contains ("rel", "alternate") && attrs.contains ("href", "reading.md"))

  let iconDoc := { doc with info := { doc.info with favicon := some "icon.svg" } }
  let iconCfg := { cfg with favicon := some ("icon.svg", { media := .svg, bytes := poster }) }
  let (iconHead, _, _) := HtmlDoc.emitTree iconCfg iconDoc
  t "contained HTML: favicon carries its captured bytes"
    ((elemAttrsList (· == "link") #[] iconHead.toList).any fun (_, attrs) =>
      attrs.contains ("rel", "icon") && attrs.contains ("href", expectedPoster))
  t "contained HTML: captured tree closes with exact SVG attestations"
    ((HtmlDoc.emitClosed iconCfg iconDoc #[moving, poster]).1.isOk)
  t "contained HTML: another SVG's attestation cannot cover these bytes"
    (!(HtmlDoc.emitClosed iconCfg iconDoc #["different bytes".toUTF8]).1.isOk)
  t "contained HTML: missing icon capture cannot publish"
    (!(HtmlDoc.emitClosed cfg iconDoc #[moving, poster]).1.isOk)
  let resource : HtmlResource.Embedded := { media := .svg, bytes := moving }
  let close (head body : Array Html.Node) :=
    HtmlResource.close #[resource] #[moving] HtmlDoc.deckScript "en" head body
  let image := Html.elem "img" #[] #[("src", resource.uri), ("alt", "Captured square")]
  for (name, head, body) in [
      ("remote image", #[], #[Html.elem "img" #[] #[("src", "https://example.invalid/x.png")]]),
      ("fragment image fetch", #[], #[Html.elem "img" #[] #[("src", "#local")]]),
      ("fragment srcset fetch", #[], #[Html.elem "source" #[] #[("srcset", "#local")]]),
      ("fragment-led srcset list", #[], #[Html.elem "source" #[]
        #[("srcset", "#local 1x, https://example.invalid/x.png 2x")]]),
      ("relative stylesheet", #[Html.elem "link" #[] #[("rel", "stylesheet"), ("href", "x.css")]], #[]),
      ("remote icon", #[Html.elem "link" #[] #[("rel", "icon"), ("href", "https://example.invalid/x.ico")]], #[]),
      ("hidden source", #[], #[Html.elem "picture" #[image,
        Html.elem "source" #[] #[("srcset", "missing.svg"), ("media", "print")]]]),
      ("unattested data", #[], #[Html.elem "img" #[] #[("src", "data:image/svg+xml;base64,PHN2Zy8+")]]),
      ("active markup", #[], #[Html.elem "iframe" #[] #[("srcdoc", "<img src='x'>")]]),
      ("script source", #[Html.Node.script #[("src", "https://example.invalid/x.js")] ""], #[]),
      ("new executable script", #[Html.Node.script #[] "fetch('https://example.invalid/x')"], #[]),
      ("event handler", #[], #[Html.elem "p" #[] #[("onclick", "fetch('x')")]]),
      ("raw attribute name", #[], #[Html.elem "p" #[] #[("x\"><img src='missing'>", "")]])] do
    t ("contained gate refuses " ++ name) (!(close head body).isOk)
  for (value, label) in [("missing-figure.png", "missing-figure.png"),
      ("data:image/svg+xml;base64," ++ String.ofList (List.replicate 1024 'A'), "image/svg+xml")] do
    match close #[] #[Html.elem "img" #[] #[("src", value)]] with
    | .error detail =>
      t "contained gate: refusal names the reference without dumping its payload"
        (hasStr detail label && detail.length < 256)
    | .ok _ => t "contained gate: unresolved diagnostic probe must be refused" false
  for (name, css) in [
      ("external url", "p { background: url(https://example.invalid/x.png) }"),
      ("fragment background fetch", "p { background: url(#local) }"),
      ("fragment font fetch", "@font-face { font-family: Probe; src: url(#local) }"),
      ("relative url", "p { background: URL('missing.svg') }"),
      ("import string", "@import 'missing.css';"),
      ("import url", "@import url('missing.css');"),
      ("image-set string", "p { background: image-set('missing.png' 1x) }"),
      ("escaped function", "p { background: u\\72l(missing.png) }"),
      ("external font", "@font-face { font-family: sample; src: local('Sample') }"),
      ("raw text terminator", "</style><img src='missing'>"),
      ("unterminated token", "p { content: 'unterminated }"),
      ("raw newline in string", "p { content: 'open\n'; background: url(missing.png) }")] do
    t ("contained gate refuses CSS " ++ name) (!(close #[.style css] #[image]).isOk)
    t ("contained gate refuses style attribute " ++ name)
      (!(close #[] #[Html.elem "p" #[] #[("style", css)]]).isOk)
  for (name, css) in [
      ("captured URL", "p { background: url(\"" ++ resource.uri ++ "\") }"),
      ("inert URL text", "p::before { content: 'url(missing.png)' }"),
      ("inert comment", "/* @import 'missing.css'; */ p { color: red }"),
      ("quoted escape", "p::before { content: \"a\\\" url(missing.png)\" }"),
      ("generated marker", "p::before { content: \"" ++ HtmlDoc.cssString "a\"\\b" ++ "\" }"),
      ("generated functions", "@supports (color: color-mix(in oklab, red, blue)) { p { color: var(--ink, red) } }")] do
    t ("contained gate accepts CSS " ++ name) ((close #[.style css] #[image]).isOk)
  t "contained gate permits fragment references in SVG reference attributes"
    ((close #[] #[Html.elem "svg" #[
      Html.elem "use" #[] #[("href", "#local")],
      Html.elem "rect" #[] #[("fill", "url(#local)"), ("clip-path", "url(#clip)")]]]).isOk)
  t "contained gate permits navigation, inert metadata and the constant deck script"
    ((close #[Html.Node.script #[("type", "application/ld+json")] "{\"url\":\"https://example.invalid\"}",
      Html.Node.script #[] HtmlDoc.deckScript,
      Html.elem "link" #[] #[("rel", "canonical"), ("href", "https://example.invalid/page")],
      Html.elem "link" #[] #[("rel", "alternate"), ("type", "text/markdown"), ("href", "page.md")]]
      #[image, Html.elem "a" #[Html.text "Reading"] #[("href", "https://example.invalid/reading")]]).isOk)
  for mode in [HtmlDoc.CssMode.own, .bulma, .none] do
    let sheetDoc := { iconDoc with output := { iconDoc.output with stylesheet := some "local.css" } }
    let sheetCfg := { iconCfg with css := mode, stylesheet := some ("local.css", "p { color: red }") }
    let (result, _) := HtmlDoc.emitClosed sheetCfg sheetDoc #[moving, poster]
    t s!"contained HTML: declared local CSS is inline in mode {repr mode}" result.isOk
    if let .ok page := result then
      t "contained HTML: checked publication renders exactly the captured tree"
        (page.render == (HtmlDoc.emit sheetCfg sheetDoc).1)
    t "contained HTML: missing declared CSS cannot publish"
      (!(HtmlDoc.emitClosed { sheetCfg with stylesheet := none } sheetDoc #[moving, poster]).1.isOk)
    t "contained HTML: nested CSS resources cannot publish"
      (!(HtmlDoc.emitClosed { sheetCfg with stylesheet := some ("local.css", "@import 'missing.css';") }
        sheetDoc #[moving, poster]).1.isOk)
  t "contained HTML: Bulma framework request cannot rely on a host stylesheet"
    (!(HtmlDoc.emitClosed { cfg with css := .bulma } doc #[moving, poster]).1.isOk)
  let collection : HtmlResource.Embedded := { media := .ttf, bytes := "ttcf".toUTF8 }
  t "contained gate refuses a collection mislabeled as a standalone font"
    (!(HtmlResource.close #[collection] #[] HtmlDoc.deckScript "en"
      #[.style ("@font-face { font-family: Probe; src: url(\"" ++ collection.uri ++ "\"); }")] #[]).isOk)
  for renderer in ["katex", "mathjax"] do
    t ("contained HTML: remote math boundary is refused: " ++ renderer)
      (!(HtmlDoc.emitClosed { cfg with mathBoundary := some renderer } doc #[moving, poster]).1.isOk)

/-- Capture and publication are separated by deliberate source mutations.
SVG dependency mutations cross the actual CLI validator before the gate. -/
def htmlContainedPublicationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let css := "p { color: rgb(1, 2, 3) }"
    let square := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
    IO.FS.writeFile (dir / "local.css") css
    IO.FS.writeBinFile (dir / "icon.svg") square
    IO.FS.writeBinFile (dir / "figure.svg") square
    let doc := (elabStr "\\includegraphics[alt={Captured square}]{figure.svg}").1
    let captured := { doc with
      output := { doc.output with stylesheet := some "local.css" }
      info := { doc.info with favicon := some "icon.svg" } }
    let cfg : HtmlDoc.Config := { imgs := { entries := #[
      { src := "figure.svg", source := some square, info := some { pxW := 20, pxH := 20 } }] } }
    let output := dir / "output"
    let (result, _) ← prepareHtml (dir / "source.tex").toString cfg captured
    t "contained publication: checked preparation writes no output" (!(← output.pathExists))
    match result with
    | .error why => t ("contained publication: preparation failed: " ++ why) false
    | .ok page =>
      let expected ← htmlDataOracle "image/svg+xml" square
      IO.FS.writeFile (dir / "local.css") "@import 'outside.css';"
      IO.FS.writeFile (dir / "icon.svg") "<svg><image href='outside.png'/></svg>"
      IO.FS.removeFile (dir / "figure.svg")
      let target := output / "page.html"
      let written ← publish none (some (target.toString, page)) none none
      let html ← IO.FS.readFile target
      t "contained publication: writes the checked serialization byte for byte"
        (html == page.render && written == #[target.toString])
      t "contained publication: retains captured stylesheet and image/icon bytes"
        (hasStr html css && !hasStr html "outside.css" && !hasStr html "outside.png" &&
          hasStr html ("src=\"" ++ expected ++ "\"") &&
          hasStr html ("href=\"" ++ expected ++ "\""))
      t "contained publication: one HTML file is the whole output"
        ((← output.readDir).map (·.fileName) == #["page.html"])
    for (name, contents, expected) in [
        ("one leading BOM", "\uFEFF" ++ css, css),
        ("two leading BOMs", "\uFEFF\uFEFF" ++ css, "\uFEFF" ++ css),
        ("interior BOM", "p::before { content: '\uFEFF' }", "p::before { content: '\uFEFF' }")] do
      IO.FS.writeFile (dir / "local.css") contents
      let (result, _) ← prepareHtml (dir / "source.tex").toString cfg
        { doc with output := { doc.output with stylesheet := some "local.css" } }
      t ("contained stylesheet: decoding preserves selector text for " ++ name)
        (match result with
         | .ok page => hasStr page.render ("<style>\n" ++ expected ++ "\n")
         | .error _ => false)
    IO.FS.writeBinFile (dir / "invalid.css") ⟨#[255]⟩
    let invalidCssDoc := { doc with output := { doc.output with stylesheet := some "invalid.css" } }
    let (invalidCss, _) ← prepareHtml (dir / "source.tex").toString cfg invalidCssDoc
    t "contained publication: UTF-8 refusal names the declared stylesheet"
      (match invalidCss with
       | .error why => hasStr why "invalid.css" && hasStr why "UTF-8"
       | .ok _ => false)
    for (name, bytes) in [
        ("image href", svgDocument "<image href=\"outside.png\"/>"),
        ("use href", svgDocument "<use href=\"outside.svg#shape\"/>"),
        ("CSS import", svgDocument "<style>@import 'outside.css';</style>"),
        ("CSS URL", svgDocument "<style>rect { fill: url(outside.svg#paint) }</style>"),
        ("style attribute", svgDocument "<rect style=\"fill:url(outside.svg#paint)\"/>"),
        ("event", svgDocument "<rect onload=\"fetch('outside')\"/>"),
        ("foreignObject", svgDocument "<foreignObject><div>Content</div></foreignObject>"),
        ("external XML entity", ("<!DOCTYPE svg [<!ENTITY x SYSTEM 'outside.txt'>]>" ++
          String.fromUTF8! (svgDocument "<text>&x;</text>")).toUTF8)] do
      let mutated := { cfg with imgs := { entries := cfg.imgs.entries.map fun en =>
        { en with source := some bytes } } }
      let (rejected, _) ← prepareHtml (dir / "source.tex").toString mutated doc
      t ("contained publication: exact SVG validation refuses " ++ name) (!rejected.isOk)

/-- Numeric color presentation attributes, including converter output, must
cross the same exact-byte closure gate as authored SVG. The raster oracle
reads the published carrier and compares it with separately authored colors;
it never treats successful conversion as resource-closure evidence. -/
def htmlContainedSvgColorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let red := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let blue := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let raster (svg : ByteArray) : IO ByteArray := IO.FS.withTempDir fun dir => do
    let input := dir / "input.svg"
    let output := dir / "output.png"
    IO.FS.writeBinFile input svg
    let run ← IO.Process.output { cmd := "rsvg-convert", args := #[
      "--format=png", "--width=20", "--height=20", "--output", output.toString, input.toString] }
    unless run.exitCode == 0 do throw <| IO.userError "the SVG color oracle requires rsvg-convert"
    IO.FS.readBinFile output
  let poster ← LeanTex.Cli.ImageAssets.svgPoster blue
  let converted ← LeanTex.Cli.ImageAssets.pdfSvg svgCanvasPdf .last
  IO.FS.withTempDir fun dir => do
    let doc := (elabStr "\\includegraphics[alt={Captured color square}]{figure.svg}").1
    for (name, result, expected, isPoster) in [
        ("integer RGB", .ok (svgDocument
          "<rect width=\"20\" height=\"20\" fill=\"rgb(255,0,0)\"/>"), red, false),
        ("percentage RGB", .ok (svgDocument
          "<rect width=\"20\" height=\"20\" fill=\"rgb(46.666667%,46.666667%,46.666667%)\"/>"),
          svgDocument "<rect width=\"20\" height=\"20\" fill=\"#777777\"/>", false),
        ("alpha RGBA", .ok (svgDocument
          "<rect width=\"20\" height=\"20\" fill=\"rgba(255,0,0,0.5)\"/>"),
          svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\" fill-opacity=\"0.5\"/>", false),
        ("decoded stroke RGB", .ok (svgDocument
          "<rect width=\"20\" height=\"20\" fill=\"none\" stroke=\"RGB(0,0,&#x32;55)\" stroke-width=\"4\"/>"),
          svgDocument "<rect width=\"20\" height=\"20\" fill=\"none\" stroke=\"blue\" stroke-width=\"4\"/>", false),
        ("rsvg poster", poster, blue, true),
        ("PDF conversion", converted, red, false)] do
      match result with
      | .error why => t ("contained SVG color: conversion failed for " ++ name ++ ": " ++ why) false
      | .ok svg =>
        let cfg : HtmlDoc.Config := { imgs := { entries := #[
          { src := "figure.svg", source := some (if isPoster then blue else svg),
            posterSvg := if isPoster then some svg else none,
            info := some { pxW := 20, pxH := 20 } }] } }
        let (closed, _) ← prepareHtml (dir / "source.tex").toString cfg doc
        match closed with
        | .error why => t ("contained SVG color: preparation failed for " ++ name ++ ": " ++ why) false
        | .ok page =>
          let output := dir / name
          let target := output / "page.html"
          let _ ← publish none (some (target.toString, page)) none none
          let html ← IO.FS.readFile target
          let (_, captured) ← svgPublishedAsset html output
            (if isPoster then "source" else "img") (if isPoster then "srcset" else "src")
          t ("contained SVG color: exact published bytes for " ++ name) (captured == svg)
          t ("contained SVG color: single-file publication for " ++ name)
            (html == page.render && (← output.readDir).map (·.fileName) == #["page.html"])
          let actual ← raster captured
          let wanted ← raster expected
          t ("contained SVG color: independently authored raster for " ++ name)
            (!actual.isEmpty && actual == wanted)
    for (name, body) in [
        ("trailing local URL", "<rect fill=\"rgb(255,0,0) url(#paint)\"/>"),
        ("trailing external URL", "<rect fill=\"rgb(255,0,0) url(outside.svg#paint)\"/>"),
        ("nested variable", "<rect fill=\"rgb(var(--red),0,0)\"/>"),
        ("nested URL", "<rect fill=\"rgb(255,0,url(outside.svg#paint))\"/>"),
        ("decoded trailing URL", "<rect fill=\"rgb(255,0,0) &#x75;rl(outside.svg#paint)\"/>"),
        ("style resource", "<rect style=\"fill:rgb(255,0,0);filter:url(outside.svg#paint)\"/>"),
        ("image resource", "<rect fill=\"rgb(255,0,0)\"/><image href=\"outside.png\"/>")] do
      let cfg : HtmlDoc.Config := { imgs := { entries := #[
        { src := "figure.svg", source := some (svgDocument body),
          info := some { pxW := 20, pxH := 20 } }] } }
      let (closed, _) ← prepareHtml (dir / "source.tex").toString cfg doc
      t ("contained SVG color: refuses " ++ name) (svgBoundaryError closed)

/-- Refusal precedes the CLI's output writes, including best-effort mode.
These cases wrote unresolved pages before checked publication was installed. -/
def htmlContainedCliChecks (ref : IO.Ref (List String)) : IO Unit := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.withTempDir fun dir => do
    for (name, preamble, args) in [
        ("missing CSS", "\\output{ formats = html, stylesheet = \"missing.css\" }", #[]),
        ("nested CSS", "\\output{ formats = html, stylesheet = \"nested.css\" }", #[]),
        ("missing icon", "\\output{ formats = html }\n\\pdfmeta{ favicon = \"missing.svg\" }", #[]),
        ("remote math", "\\output{ formats = html }", #["--math-boundary", "katex"]),
        ("best effort", "\\output{ formats = html, stylesheet = \"missing.css\" }", #["--best-effort"]),
        ("missing framework", "\\output{ formats = html, css = bulma }", #[]),
        ("remote framework", "\\output{ formats = html, css = bulma, stylesheet = \"https://example.invalid/framework.css\" }", #[])] do
      let input := dir / name
      let output := input / "output"
      IO.FS.createDirAll input
      IO.FS.writeFile (input / "nested.css") "@import 'https://example.invalid/nested.css';"
      IO.FS.writeFile (input / "source.tex")
        ("\\documentclass{article}\n" ++ preamble ++
          "\n\\begin{document}\nAn invented resource probe.\\end{document}\n")
      let request : IO.Process.SpawnArgs := {
        cmd := binary.toString, cwd := some input,
        args := #["source.tex", "-o", output.toString ++ "/"] ++ args,
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)] }
      let run ← IO.Process.output request
      check ref ("contained CLI: refuses " ++ name ++ " before creating output")
        (run.exitCode != 0 && hasStr (run.stdout ++ run.stderr) "E0606" && !(← output.pathExists))
      for (probe, resource) in [("missing CSS", "missing.css"), ("missing icon", "missing.svg"),
          ("best effort", "missing.css"), ("remote framework", "https://example.invalid/framework.css")] do
        if name == probe then
          check ref ("contained CLI: refusal names the authored resource for " ++ name)
            (hasStr (run.stdout ++ run.stderr) resource)
      IO.FS.createDirAll output
      IO.FS.writeFile (output / "source.html") "existing artifact"
      let retry ← IO.Process.output request
      check ref ("contained CLI: refusal preserves existing output for " ++ name)
        (retry.exitCode != 0 && hasStr (retry.stdout ++ retry.stderr) "E0606" &&
          (← IO.FS.readFile (output / "source.html")) == "existing artifact" &&
          (← output.readDir).map (·.fileName) == #["source.html"])

/-- The shipped generated syntax must remain in the checked vocabulary.
This is a syntax coverage guard; missing captures still owe publication checks. -/
def htmlContainedCorpusChecks (ref : IO.Ref (List String)) : IO Unit := do
  for name in goldenNames do
    let (doc, _) ← goldenDoc name
    for mode in [HtmlDoc.CssMode.own, .bulma, .none] do
      let (head, body, _) := HtmlDoc.emitTree { css := mode } doc
      let refusals := (HtmlResource.requests head body).filterMap fun
        | .refused why => some why
        | _ => none
      check ref s!"contained corpus syntax: {name} {repr mode}: {repr refusals}" refusals.isEmpty

end Tests
