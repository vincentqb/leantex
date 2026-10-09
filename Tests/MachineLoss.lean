module

public import Tests.Support
public import LeanTex.Cli.Boundary
public import LeanTex.Cli.Publication
public import Lean.Data.Json
public import LeanTex.Cli.RunBounded

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
  "/bin/cp " ++ shQuote pdf.toString ++ " pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- A PDF-to-SVG converter that names its version and converts by copying
one SVG to the output it is given (`-svg <input> <output>`). -/
private def fakeConverter (svg : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = -v ]; then\n" ++
  "  printf '%s\\n' 'synthetic converter 1' >&2\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuote svg.toString ++ " \"$3\" || exit 3\n"

/-- An SVG validator the machine kills before it answers. -/
private def killedValidator : String :=
  "#!/bin/sh\nkill -9 $$\n"

/-- An SVG validator a missing shared library cannot start: every check
counts itself in `calls`, then exits 127 with the dynamic loader's line on
its stderr. A real one could not answer `--version` either; its answer here
stands in for the version memo an earlier build wrote while the library was
still there. -/
private def loaderBroken (calls : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'xmllint: using libxml version 20900' >&2\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "printf '%s\\n' check >> " ++ shQuote calls.toString ++ "\n" ++
  "printf '%s\\n' 'xmllint: error while loading shared libraries: libsynthetic.so.0: \
cannot open shared object file: No such file or directory' >&2\n" ++
  "exit 127\n"

/-- A converter that names its version and is never asked to convert. -/
private def versionOnly (name : String) : String :=
  "#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' '" ++ name ++ " 1'; exit 0; fi\nexit 3\n"

/-- A boundary renderer that names its version and refuses every picture,
saying why in its log. -/
private def refusingRenderer : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "printf '%s\\n' '! Synthetic refusal of an invented picture.' > pic.log\n" ++
  "exit 1\n"

/-- A picture outside the rendered subset whose failed render the document
accepts. Invented content. -/
private def acceptedSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\allow{E0382}\n\\begin{document}\nAn invented shading follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\shade (0,0) rectangle (2,1);\n\\end{tikzpicture}\n\\end{document}\n"

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

/-- The child behind `legacySlotChecks`: a conversion with a synthetic tool
fills its slot; the slot is replaced by one spelled as the v2 variant spells
it, holding the refusal a run that never started read as there; and the next
conversion of the same source must ask the tool again. Exit 0 when it does. -/
private def legacySlotDriver : String :=
  "import LeanTex.Cli.ConvCache\n" ++
  "import LeanTex.Cli.ToolProbe\n" ++
  "open LeanTex.Cli\n" ++
  "def main (args : List String) : IO UInt32 := do\n" ++
  "  let [dir] := args | return 2\n" ++
  "  let tool := dir ++ \"/zz-legacy-tool\"\n" ++
  "  let calls ← IO.mkRef 0\n" ++
  "  let produce : IO (ConvCache.Result × Bool) := do\n" ++
  "    calls.modify (· + 1)\n" ++
  "    return ({ outcome := .drawn, bytes := \"drawn\".toUTF8 }, true)\n" ++
  "  let source := \"an invented source\".toUTF8\n" ++
  "  let recipe := \"zz-legacy-tool <input> <output>\"\n" ++
  "  let first ← ConvCache.cachedResult source recipe #[tool] true produce\n" ++
  "  let convs : System.FilePath := dir ++ \"/cache/leantex/convs\"\n" ++
  "  let answers ← do\n" ++
  "    let entries ← convs.readDir\n" ++
  "    pure (entries.filter (·.fileName.endsWith \".answer\"))\n" ++
  "  let memo ← IO.FS.readFile (convs / (\"tool-\" ++ LeanTex.Core.Flate.contentKey tool.toUTF8 ++ \".ver\"))\n" ++
  "  let some (stamp, version) := PicCache.readVersionMemo memo | return 3\n" ++
  "  let identity := tool ++ \"\\n\" ++ stamp ++ \"\\n\" ++ version\n" ++
  "  let variant := LeanTex.Core.Flate.contentKey (String.intercalate \"\\u0000\"\n" ++
  "    [\"vector-cache-v2\", LeanTex.version, recipe, identity]).toUTF8\n" ++
  "  for e in answers do IO.FS.removeFile e.path\n" ++
  "  IO.FS.writeBinFile (convs / (LeanTex.Core.Flate.contentKey source ++ \"-\" ++ variant ++ \".answer\"))\n" ++
  "    (ConvCache.encode (.error \"zz-legacy-tool exited 127: zz-legacy-tool: error while loading shared libraries\"))\n" ++
  "  let again ← ConvCache.cachedResult source recipe #[tool] true produce\n" ++
  "  IO.println s!\"{answers.size} slot, {← calls.get} conversions\"\n" ++
  "  return if answers.size == 1 && first.outcome == .drawn && again.outcome == .drawn &&\n" ++
  "    (← calls.get) == 2 then 0 else 1\n"

/-- **A slot the v2 variant wrote is never read.** v2 could hold a run that
never started (exit 126 or 127) as the tool's refusal, so the slots moved to
v3: in a child whose cache is its own, a v2 slot holding such a refusal
leaves the next conversion to ask the tool again. -/
def legacySlotChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (lean, leanPath) ← leanChild "legacy slot checks"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    writeScript (dir / "zz-legacy-tool")
      "#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' 'zz-legacy-tool 1'; exit 0; fi\nexit 3\n"
    let driver := dir / "legacy.lean"
    IO.FS.writeFile driver legacySlotDriver
    let result ← RunBounded.runBounded lean.toString #["--run", driver.toString, dir.toString] dir 30000 100
      (env := #[("LEAN_PATH", some leanPath), ("XDG_CACHE_HOME", some (dir / "cache").toString)])
    check ref s!"machine loss: a v2 slot holding a run that never started is not read ({repr result.ran}): {result.out}{result.err}"
      (result.complete && result.ran == .exited 0)

/-- **A tool this machine lacks, or a check it could not finish, degrades
the HTML page instead of refusing it**, on the paths fixed here, and each
such loss is named once, under its subject: a boundary picture no tool drew
(W0379); one drawn whose browser face was not converted, or whose face's
check did not finish (W0378, at the picture's span — and where the rendered
subset draws the picture in part, the subset's drawing ships whichever step
failed); an included SVG whose plan a missing or killed validator stopped
(W0602, which names the PDF's placeholder and the page's at once), a
validator that cannot start among them (exit 127 from a missing library,
remembered nowhere, so the next build asks again); and a page icon whose
check did not finish (W0605). The defects refused the page (E0606) and wrote
nothing while the PDF shipped, and so did a refused render the document
accepts (`\allow{E0382}`), which now ships the page's placeholder too. One
path is not held here: a boundary render that did not finish — killed, a
spawn that raised, or a nonzero exit with no log, a renderer that cannot
start after naming its version among them — stays E0382 and fails the run
by design (`boundaryUnfinishedChecks`). The library
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
    let loader := dir / "loader"
    let refusing := dir / "refusing"
    for d in [bare, renderer, converter, killed, loader, refusing] do IO.FS.createDirAll d
    for (file, body) in [(killed / "xmllint", killedValidator),
        (loader / "xmllint", loaderBroken (loader / "calls")),
        (loader / "rsvg-convert", versionOnly "synthetic converter"),
        (refusing / "lualatex", refusingRenderer)] do
      IO.FS.writeFile file body
      IO.setAccessRights file { user := ⟨true, true, true⟩ }
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
    let build (doc path : System.FilePath) (cache : String) (out : System.FilePath) : IO IO.Process.Output :=
      IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #[doc.toString, "-o", out.toString, "--porcelain"]
        env := #[("PATH", some path.toString),
          ("XDG_CACHE_HOME", some (dir / ("cache-" ++ cache)).toString),
          ("LEANTEX_FONT", some font.toString)] }
    let recordsOf (run : IO.Process.Output) : List Lean.Json :=
      ((run.stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun line => (Lean.Json.parse line).toOption
    let loaderCase : MachineCase :=
      { name := "loader-broken SVG check", doc := svgInclude, path := loader, cache := "loader"
        code := "W0602", subject := some "square.svg", located := true, placeholders := 1
        drawings := 0 }
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
        loaderCase,
        { name := "no icon check", doc := corpus / "webpage.tex", path := bare, cache := "webpage"
          code := "W0605", subject := some "favicon.svg", located := false, placeholders := 0
          drawings := 0 },
        { name := "killed icon check", doc := corpus / "webpage.tex", path := killed
          cache := "webpage", code := "W0605", subject := some "favicon.svg", located := false
          placeholders := 0, drawings := 0 }] do
      let out := dir / ((c.name.replace " " "-").replace "," "") / "page.html"
      let run ← build c.doc c.path c.cache out
      let records := recordsOf run
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
    -- A validator a missing shared library cannot start said nothing of its
    -- own: its run is remembered nowhere, so the next build asks it again.
    let checks : IO Nat := do
      return (((← IO.FS.readFile (loader / "calls")).splitOn "\n").filter (!·.isEmpty)).length
    let before ← checks
    let again ← build loaderCase.doc loaderCase.path loaderCase.cache (dir / "loader-again" / "page.html")
    let after ← checks
    t s!"machine loss CLI loader-broken SVG check: the next build asks the validator again ({before} then {after} checks)"
      (again.exitCode == 0 && before ≥ 1 && after > before)
    -- A refused render the document accepts: the faceless picture's loss is
    -- that E0382, accepted once, and the page ships its placeholder.
    let accepted := dir / "accepted.tex"
    IO.FS.writeFile accepted (acceptedSource (corpus / "fonts"))
    let acceptedOut := dir / "accepted" / "page.html"
    let run ← build accepted refusing "accepted" acceptedOut
    let records := recordsOf run
    let event (j : Lean.Json) := (j.getObjValAs? String "event").toOption
    let acceptedCodes := records.filterMap fun j =>
      if event j == some "accepted" then (j.getObjValAs? (Array Lean.Json) "codes").toOption else none
    let named := records.filterMap fun j =>
      if event j == some "diagnostic" then (j.getObjValAs? String "code").toOption else none
    t s!"machine loss CLI accepted refusal: the build ships (exit {run.exitCode})" (run.exitCode == 0)
    t s!"machine loss CLI accepted refusal: the failed render is accepted once and no machine loss is named ({named})"
      (acceptedCodes.any (·.any fun c => (c.getObjValAs? String "code").toOption == some "E0382" &&
          (c.getObjValAs? Nat "count").toOption == some 1) &&
        !named.any (["E0606", "W0378", "W0379", "W0602", "W0605"].contains ·))
    match ← (IO.FS.readFile acceptedOut).toBaseIO with
    | .error _ => t "machine loss CLI accepted refusal: the HTML page is written" false
    | .ok html =>
      let tags := placeholderTags html
      t "machine loss CLI accepted refusal: one labelled placeholder, and no image names a request key"
        (tags.length == 1 && tags.all labelled && !hasStr html (" src=\"" ++ Ir.picSrcPrefix))
  legacySlotChecks ref

end Tests
