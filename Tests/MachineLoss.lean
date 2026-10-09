module

public import Tests.Support
public import LeanTex.Cli.Boundary
public import LeanTex.Cli.Publication
public import Lean.Data.Json

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- The opening tags of a page's failed-face placeholders: the spans that
carry `data-image-src`. -/
private def placeholderTags (html : String) : List String :=
  ((html.splitOn "<span ").drop 1).filterMap fun rest =>
    let tag := (rest.splitOn ">").headD ""
    if hasStr tag "data-image-src=" then some tag else none

/-- An attribute's value in one opening tag, as the serializer writes it. -/
private def attrIn (tag name : String) : Option String :=
  match (" " ++ tag).splitOn (" " ++ name ++ "=\"") with
  | _ :: rest :: _ => some ((rest.splitOn "\"").headD "")
  | _ => none

private def labelled (tag : String) : Bool :=
  (attrIn tag "aria-label").any (!·.isEmpty)

/-- A boundary renderer that names its version and draws by copying a
committed PDF beside a log. Shell builtins and `/bin/cp` alone, so a PATH
holding nothing else still runs it. -/
private def fakeRenderer (pdf : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp '" ++ pdf.toString.replace "'" "'\\''" ++ "' pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- One machine the build runs on: which corpus document, whether its PATH
holds the renderer (it never holds a converter or a validator), and the one
loss that machine owes, by code and subject. -/
private structure MachineCase where
  name : String
  fixture : String
  renderer : Bool
  cache : String
  code : String
  subject : String
  placeholders : Nat

/-- **No machine fact removes an artifact.** A reply saying the machine
lacks a tool, or that the tool never finished, may degrade the HTML page and
never refuses it, and each such loss is named once, by its subject. The
defects all refused the page (E0606) and wrote nothing while the PDF shipped
its placeholder: no boundary tool (W0379), a renderer with no converter
(W0378), and no SVG validator for the page's icon. The library half holds
the two pure steps — a faceless boundary picture refuses the unmarked page
and ships the marked one with no new diagnostic, and an omitted face leaves
a page that closes with its losses named — and the CLI half runs the built
binary on machines whose PATH holds no tool, or only a synthetic renderer.
Invented content; the renderer copies a committed fixture. -/
def machineLossChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let (boundaryDoc, _) ← elabFixture "diagram-boundary"
    (← IO.FS.readFile "testdata/corpus/diagram-boundary.tex")
  let requests := Ir.imageRequests boundaryDoc
  let picSrc := ((requests.find? (·.src.startsWith Ir.picSrcPrefix)).map (·.src)).getD ""
  t "machine loss: the boundary fixture states one picture request"
    (!picSrc.isEmpty && (requests.filter (·.src.startsWith Ir.picSrcPrefix)).size == 1)
  let drawn := (Image.probe (← IO.FS.readBinFile "testdata/corpus/figures/box.pdf") >>=
    Image.plan .default).toOption
  t "machine loss: the renderer's committed drawing plans" drawn.isSome
  let fonts := (← findFont).bind fun bytes => (Font.parse bytes).toOption.map oneFaceOf
  t "machine loss: the shipped face loads" fonts.isSome
  let geom := Layout.Geom.ofPage boundaryDoc.page
  for (label, info) in [("no tool", none), ("no converter", drawn)] do
    let store : Image.Store := { entries := requests.map fun req => { toRequest := req, info } }
    let marked := Boundary.markFaceless store
    let pdfOf (fonts : Font.FontSet) (imgs : Image.Store) : ByteArray :=
      Pdf.write geom fonts (layoutOf fonts boundaryDoc geom none imgs).pages {} imgs
    t s!"machine loss {label}: marking leaves the PDF byte for byte"
      (fonts.any fun fonts => pdfOf fonts store == pdfOf fonts marked)
    let (before, beforeDiags) := HtmlDoc.emitClosed { imgs := store } boundaryDoc #[]
    let (after, afterDiags) := HtmlDoc.emitClosed { imgs := marked } boundaryDoc #[]
    t s!"machine loss {label}: a faceless picture refuses the unmarked page" (!before.isOk)
    t s!"machine loss {label}: marking names nothing new"
      (afterDiags.map (·.code) == beforeDiags.map (·.code))
    match after with
    | .error why => t s!"machine loss {label}: the marked page closes: {why}" false
    | .ok page =>
      let tags := placeholderTags page.render
      t s!"machine loss {label}: one labelled placeholder stands for the picture"
        (tags.length == 1 && tags.all fun tag =>
          attrIn tag "data-image-src" == some picSrc && labelled tag)
      t s!"machine loss {label}: no image names the request key"
        (!hasStr page.render (" src=\"" ++ Ir.picSrcPrefix))
  -- Validation that never finished omits a face; nothing is refused.
  let square := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let face := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let icon := svgDocument "<circle cx=\"10\" cy=\"10\" r=\"8\"/>"
  let (pageDoc, _) := elabStr (dvDoc ""
    ("\\includegraphics[alt={An invented square}]{figure.svg}\n\n" ++
      "\\begin{tikzpicture}\n  \\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}"))
  let pageDoc := { pageDoc with info := { pageDoc.info with favicon := some "icon.svg" } }
  let pagePic := ((Ir.imageRequests pageDoc).find? (·.src.startsWith Ir.picSrcPrefix)).map (·.src)
  let cfg : HtmlDoc.Config := {
    imgs := { entries := (Ir.imageRequests pageDoc).map fun req =>
      if req.src.startsWith Ir.picSrcPrefix then { toRequest := req, info := drawn, webSvg := some face }
      else { toRequest := req, info := drawn, source := some square } }
    favicon := some ("icon.svg", { media := .svg, bytes := icon }) }
  let why := "xmllint did not finish"
  let (omittedCfg, omittedDoc, omitDiags) :=
    Publication.omitFaces #[(square, why), (face, why), (icon, why)] cfg pageDoc
  t "machine loss omitted: unchecked faces still refuse the page"
    (!(HtmlDoc.emitClosed cfg pageDoc #[]).1.isOk)
  t "machine loss omitted: the picture is named by W0378 and the icon by W0605, once each"
    (pagePic.isSome && omitDiags.map (fun d => (d.code, d.subject)) ==
      #[("W0378", pagePic), ("W0605", some "icon.svg")])
  t "machine loss omitted: every face carries its reason, and the icon leaves the head"
    (omittedCfg.imgs.entries.all (·.webError == some why) && omittedCfg.favicon.isNone &&
      omittedDoc.info.favicon.isNone)
  match HtmlDoc.emitClosed omittedCfg omittedDoc #[] with
  | (.error why, _) => t s!"machine loss omitted: the page closes: {why}" false
  | (.ok page, diags) =>
    let tags := placeholderTags page.render
    t "machine loss omitted: the image and the picture ship labelled placeholders"
      (tags.length == 2 && tags.all labelled && !hasStr page.render "rel=\"icon\"")
    t "machine loss omitted: the page names the image's face once (W0605)"
      ((diags.filter (·.code == "W0605")).size == 1 &&
        diags.all fun d => d.code != "W0605" || (d.subject.any (hasStr · "figure.svg")))
  -- The built binary on machines that lack tools.
  let binary ← IO.FS.realPath binary
  let corpus ← IO.FS.realPath "testdata/corpus"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    let bare := dir / "bare"
    let tools := dir / "tools"
    IO.FS.createDirAll bare
    IO.FS.createDirAll tools
    IO.FS.writeFile (tools / "lualatex") (fakeRenderer (corpus / "figures" / "box.pdf"))
    IO.setAccessRights (tools / "lualatex") { user := ⟨true, true, true⟩ }
    -- The first two share a cache: the first run's missing tool is remembered
    -- nowhere, so the renderer draws the picture on the second.
    for c in [
        ({ name := "no tool", fixture := "diagram-boundary", renderer := false
           cache := "boundary", code := "W0379", subject := picSrc, placeholders := 1 } :
          MachineCase),
        { name := "no converter", fixture := "diagram-boundary", renderer := true
          cache := "boundary", code := "W0378", subject := picSrc, placeholders := 1 },
        { name := "no validator", fixture := "webpage", renderer := false
          cache := "webpage", code := "W0605", subject := "favicon.svg", placeholders := 0 }] do
      let out := dir / (c.name.replace " " "-") / "page.html"
      let run ← IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #[(corpus / (c.fixture ++ ".tex")).toString, "-o", out.toString, "--porcelain"]
        env := #[("PATH", some (if c.renderer then tools else bare).toString),
          ("XDG_CACHE_HOME", some (dir / ("cache-" ++ c.cache)).toString),
          ("LEANTEX_FONT", some font.toString)] }
      let records := ((run.stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun line =>
        (Lean.Json.parse line).toOption
      let coded (codes : List String) := records.filter fun j =>
        j.getObjValAs? String "event" == .ok "diagnostic" &&
          codes.any fun code => j.getObjValAs? String "code" == .ok code
      t s!"machine loss CLI {c.name}: the build ships (exit {run.exitCode})" (run.exitCode == 0)
      t s!"machine loss CLI {c.name}: no closure refusal" (coded ["E0606"]).isEmpty
      let losses := coded ["W0378", "W0379", "W0605"]
      t s!"machine loss CLI {c.name}: one {c.code}, under its subject, and no other machine loss"
        (losses.length == 1 && losses.all fun j =>
          j.getObjValAs? String "code" == .ok c.code &&
            j.getObjValAs? String "subject" == .ok c.subject)
      match ← (IO.FS.readFile out).toBaseIO with
      | .error _ => t s!"machine loss CLI {c.name}: the HTML page is written" false
      | .ok html =>
        let tags := placeholderTags html
        t s!"machine loss CLI {c.name}: {c.placeholders} labelled placeholders"
          (tags.length == c.placeholders && tags.all labelled)
        t s!"machine loss CLI {c.name}: no image names a request key, and no icon is linked"
          (!hasStr html (" src=\"" ++ Ir.picSrcPrefix) && !hasStr html "rel=\"icon\"")

end Tests
