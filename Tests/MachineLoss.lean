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

/-- A path quoted for `/bin/sh`. -/
private def shQuoted (p : System.FilePath) : String :=
  "'" ++ p.toString.replace "'" "'\\''" ++ "'"

/-- A boundary renderer that names its version and draws by copying a
committed PDF beside a log. Shell builtins and `/bin/cp` alone, so a PATH
holding nothing else still runs it. -/
private def fakeRenderer (pdf : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuoted pdf ++ " pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- A PDF-to-SVG converter that names its version and converts by copying
one SVG to the output it is given (`-svg <input> <output>`). -/
private def fakeConverter (svg : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = -v ]; then\n" ++
  "  printf '%s\\n' 'synthetic converter 1' >&2\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuoted svg ++ " \"$3\" || exit 3\n"

/-- An SVG validator the machine kills before it answers. -/
private def killedValidator : String :=
  "#!/bin/sh\nkill -9 $$\n"

/-- An included SVG figure, by a generated file beside the document.
Invented content. -/
private def includeSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented square follows.\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented square}]{square.svg}\n\\end{document}\n"

/-- A picture the rendered subset draws in part — its frame and its label —
that its rounded corners send to the boundary. Invented content. -/
private def fallbackSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented picture follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\draw[rounded corners] (0,0) rectangle (3,1);\n" ++
  "  \\node at (1.5,0.5) {Mark};\n\\end{tikzpicture}\n\nText follows the picture.\n" ++
  "\\end{document}\n"

/-- One machine the build runs on: the document, the directory its PATH
holds (no tool, a synthetic renderer, a synthetic renderer and converter, or
a validator the machine kills — never one that answers), and the one loss
that machine owes: its code, its subject (`none`: the picture the run itself
declares at the boundary, by its N0023), whether it carries the picture's
source line, and what the page shows in its place — labelled placeholders,
or the rendered subset's inline drawings. -/
private structure MachineCase where
  name : String
  doc : System.FilePath
  path : System.FilePath
  cache : String
  code : String
  subject : Option String
  located : Bool
  placeholders : Nat
  drawings : Nat

/-- **A tool this machine lacks, or a check it could not finish, degrades
the HTML page instead of refusing it**, on the paths fixed here, and each
such loss is named once, under its subject: a boundary picture no tool drew
(W0379); one drawn whose browser face was not converted, or whose face's
check did not finish (W0378, at the picture's span — and where the rendered
subset draws the picture in part, the subset's drawing ships whichever step
failed); an included SVG whose plan a missing or killed validator stopped
(W0602, which names the PDF's placeholder and the page's at once); and a
page icon whose check did not finish (W0605). The defects refused the page
(E0606) and wrote nothing while the PDF shipped its placeholder. One path is
not held here: a boundary render that started and did not finish stays
E0382 and fails the run by design (`boundaryUnfinishedChecks`). The library
half holds the pure steps — a faceless boundary picture, or an include whose
plan stopped, refuses the unmarked page and ships the marked one with no new
diagnostic and the PDF unchanged, and an omitted face leaves a page that
closes with its losses named — and the CLI half runs the built binary.
Invented content; the synthetic tools copy a committed PDF and a generated
SVG. -/
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
  -- An include whose plan the machine stopped: marked, the page ships its
  -- placeholder and names nothing new, and the PDF is the PDF.
  let (includeDoc, _) := elabStr (dvDoc ""
    "\\includegraphics[width=20pt,alt={An invented square}]{square.svg}")
  let includeReqs := Ir.imageRequests includeDoc
  t "machine loss stopped plan: the include states one request" (includeReqs.size == 1)
  let unplannedStore : Image.Store := { entries := includeReqs.map fun req => { toRequest := req } }
  let stoppedStore := Boundary.markUnplanned includeReqs unplannedStore
  let includeGeom := Layout.Geom.ofPage includeDoc.page
  let includePdf (fonts : Font.FontSet) (imgs : Image.Store) : ByteArray :=
    Pdf.write includeGeom fonts (layoutOf fonts includeDoc includeGeom none imgs).pages {} imgs
  t "machine loss stopped plan: marking leaves the PDF byte for byte"
    (fonts.any fun fonts => includePdf fonts unplannedStore == includePdf fonts stoppedStore)
  t "machine loss stopped plan: a request no fact stopped is left as it was"
    ((Boundary.markUnplanned #[] unplannedStore).entries.all (·.webError.isNone))
  let (unmarked, unmarkedDiags) := HtmlDoc.emitClosed { imgs := unplannedStore } includeDoc #[]
  let (marked, markedDiags) := HtmlDoc.emitClosed { imgs := stoppedStore } includeDoc #[]
  t "machine loss stopped plan: an unplanned include refuses the unmarked page" (!unmarked.isOk)
  t "machine loss stopped plan: marking names nothing new"
    (markedDiags.map (·.code) == unmarkedDiags.map (·.code))
  match marked with
  | .error why => t s!"machine loss stopped plan: the marked page closes: {why}" false
  | .ok page =>
    let tags := placeholderTags page.render
    t "machine loss stopped plan: one labelled placeholder stands for the include"
      (tags.length == 1 && tags.all fun tag =>
        attrIn tag "data-image-src" == some "square.svg" && labelled tag)
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
  let fallbackText := fallbackSource (corpus / "fonts")
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    let bare := dir / "bare"
    let renderer := dir / "renderer"
    let converter := dir / "converter"
    let killed := dir / "killed"
    for d in [bare, renderer, converter, killed] do IO.FS.createDirAll d
    IO.FS.writeFile (killed / "xmllint") killedValidator
    IO.setAccessRights (killed / "xmllint") { user := ⟨true, true, true⟩ }
    IO.FS.writeBinFile (dir / "square.svg") square
    let svgInclude := dir / "include.tex"
    IO.FS.writeFile svgInclude (includeSource (corpus / "fonts"))
    IO.FS.writeBinFile (dir / "face.svg") face
    for d in [renderer, converter] do
      IO.FS.writeFile (d / "lualatex") (fakeRenderer (corpus / "figures" / "box.pdf"))
      IO.setAccessRights (d / "lualatex") { user := ⟨true, true, true⟩ }
    IO.FS.writeFile (converter / "pdftocairo") (fakeConverter (dir / "face.svg"))
    IO.setAccessRights (converter / "pdftocairo") { user := ⟨true, true, true⟩ }
    let fallback := dir / "fallback.tex"
    IO.FS.writeFile fallback fallbackText
    let boundary := corpus / "diagram-boundary.tex"
    -- Runs on one document share a cache: a missing tool, and a check that
    -- did not finish, are remembered nowhere, so each next machine asks again.
    for c in [
        ({ name := "no tool", doc := boundary, path := bare, cache := "boundary"
           code := "W0379", subject := some picSrc, located := true, placeholders := 1
           drawings := 0 } : MachineCase),
        { name := "no converter", doc := boundary, path := renderer, cache := "boundary"
          code := "W0378", subject := some picSrc, located := true, placeholders := 1
          drawings := 0 },
        { name := "no face check", doc := boundary, path := converter, cache := "boundary"
          code := "W0378", subject := some picSrc, located := true, placeholders := 1
          drawings := 0 },
        { name := "fallback, no converter", doc := fallback, path := renderer, cache := "fallback"
          code := "W0378", subject := none, located := true, placeholders := 0, drawings := 1 },
        { name := "fallback, no face check", doc := fallback, path := converter
          cache := "fallback", code := "W0378", subject := none, located := true
          placeholders := 0, drawings := 1 },
        { name := "no SVG tools", doc := svgInclude, path := bare, cache := "include"
          code := "W0602", subject := some "square.svg", located := true, placeholders := 1
          drawings := 0 },
        { name := "killed SVG check", doc := svgInclude, path := killed, cache := "include"
          code := "W0602", subject := some "square.svg", located := true, placeholders := 1
          drawings := 0 },
        { name := "no icon check", doc := corpus / "webpage.tex", path := bare, cache := "webpage"
          code := "W0605", subject := some "favicon.svg", located := false, placeholders := 0
          drawings := 0 },
        { name := "killed icon check", doc := corpus / "webpage.tex", path := killed
          cache := "webpage", code := "W0605", subject := some "favicon.svg", located := false
          placeholders := 0, drawings := 0 }] do
      let out := dir / ((c.name.replace " " "-").replace "," "") / "page.html"
      let run ← IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #[c.doc.toString, "-o", out.toString, "--porcelain"]
        env := #[("PATH", some c.path.toString),
          ("XDG_CACHE_HOME", some (dir / ("cache-" ++ c.cache)).toString),
          ("LEANTEX_FONT", some font.toString)] }
      let records := ((run.stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun line =>
        (Lean.Json.parse line).toOption
      let coded (codes : List String) := records.filter fun j =>
        j.getObjValAs? String "event" == .ok "diagnostic" &&
          codes.any fun code => j.getObjValAs? String "code" == .ok code
      t s!"machine loss CLI {c.name}: the build ships (exit {run.exitCode})" (run.exitCode == 0)
      t s!"machine loss CLI {c.name}: no closure refusal" (coded ["E0606"]).isEmpty
      let declared := (coded ["N0023"]).filterMap fun j =>
        (j.getObjValAs? String "subject").toOption.bind fun s =>
          if s.startsWith "picture:boundary:" then
            some (Ir.picSrcPrefix ++ (s.drop "picture:boundary:".length).toString)
          else none
      let subject := c.subject <|> declared.head?
      let losses := coded ["W0378", "W0379", "W0602", "W0605"]
      t s!"machine loss CLI {c.name}: one {c.code}, under its subject, and no other machine loss"
        (subject.isSome && losses.length == 1 && losses.all fun j =>
          j.getObjValAs? String "code" == .ok c.code &&
            (j.getObjValAs? String "subject").toOption == subject)
      t s!"machine loss CLI {c.name}: the loss's reason reads as one clause"
        (losses.all fun j => (j.getObjValAs? String "message").toOption.any (!hasStr · ": ;"))
      let place := if c.located then "at its picture's source line" else "with no source line"
      t s!"machine loss CLI {c.name}: the loss is named {place}"
        (losses.all fun j => (j.getObjValAs? Nat "line").isOk == c.located)
      match ← (IO.FS.readFile out).toBaseIO with
      | .error _ => t s!"machine loss CLI {c.name}: the HTML page is written" false
      | .ok html =>
        let tags := placeholderTags html
        t s!"machine loss CLI {c.name}: {c.placeholders} labelled placeholders"
          (tags.length == c.placeholders && tags.all labelled)
        t s!"machine loss CLI {c.name}: {c.drawings} drawings by the rendered subset"
          ((html.splitOn "<svg").length - 1 == c.drawings)
        t s!"machine loss CLI {c.name}: no image names a request key, and no icon is linked"
          (!hasStr html (" src=\"" ++ Ir.picSrcPrefix) && !hasStr html "rel=\"icon\"")

end Tests
