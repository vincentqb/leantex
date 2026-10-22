module

public import Tests.Support
public import LeanTex.Cli.Boundary
public import LeanTex.Cli.Publication
public import Lean.Data.Json
public import LeanTex.Cli.RunBounded

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- A boundary renderer whose terminal output ends in bytes that are not UTF-8. -/
private def noisyRenderer (pdf : System.FilePath) : String :=
  fakeRenderer pdf ++ "printf 'Transcript written on pic.log \\303\\n\\377'\n"

/-- A boundary renderer whose log ends in a split UTF-8 character. -/
private def splitLogRenderer (pdf : System.FilePath) : String :=
  fakeRenderer pdf ++ "printf 'Transcript of an invented run \\303\\n' >> pic.log\n"

private def killedValidator : String :=
  "#!/bin/sh\nkill -9 $$\n"

/-- An SVG validator a missing shared library stops: each check is logged to `calls` and exits 127. -/
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

private def versionOnly (name : String) : String :=
  "#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' '" ++ name ++ " 1'; exit 0; fi\nexit 3\n"

private def refusingRenderer : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "printf '%s\\n' '! Synthetic refusal of an invented picture.' > pic.log\n" ++
  "exit 1\n"

private def refusingConverter : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ] || [ \"$1\" = -v ]; then printf '%s\\n' 'synthetic converter 1'; exit 0; fi\n" ++
  "printf '%s\\n' 'synthetic refusal of an invented figure' >&2\n" ++
  "exit 1\n"

/-- A document with a PDF and an SVG figure, each using a feature the engine does not draw. -/
private def lossyFiguresSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nTwo invented figures follow.\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented chart}]{lossy.pdf}\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented blur}]{lossy.svg}\n\\end{document}\n"

/-- A document including an encrypted PDF figure the importer refuses. -/
private def lockedIncludeSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented figure follows.\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented canvas}]{locked.pdf}\n\\end{document}\n"

/-- A document accepting a failed render by W0382's legacy spelling, E0382. -/
private def acceptedSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\allow{E0382}\n\\begin{document}\nAn invented pattern follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\pattern (0,0) rectangle (2,1);\n\\end{tikzpicture}\n\\end{document}\n"

private def includeSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented square follows.\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented square}]{square.svg}\n\\end{document}\n"

/-- A picture the rendered subset draws in part, sent to the boundary by a pattern fill. -/
private def fallbackSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented picture follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\draw (0,0) rectangle (3,1);\n  \\pattern (0,0) rectangle (1,1);\n" ++
  "  \\node at (1.5,0.5) {Mark};\n\\end{tikzpicture}\n\nText follows the picture.\n" ++
  "\\end{document}\n"

/-- One build machine and the one loss it owes; `subject := none` takes the subject from the run's N0023. -/
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

/-- The child program of `legacySlotChecks`: exits 0 when a v2 slot leaves the next conversion to ask the tool again. -/
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

/-- A conversion slot written by the v2 cache variant is never read. -/
def legacySlotChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (lean, leanPath) ← leanChild "legacy slot checks"
  IO.FS.withTempDir fun dir => do
    let dir ← IO.FS.realPath dir
    writeScript (dir / "zz-legacy-tool")
      "#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' 'zz-legacy-tool 1'; exit 0; fi\nexit 3\n"
    let driver := dir / "legacy.lean"
    IO.FS.writeFile driver legacySlotDriver
    let result ← childRun 900 lean.toString #["--run", driver.toString, dir.toString] dir
      (env := #[("LEAN_PATH", some leanPath), ("XDG_CACHE_HOME", some (dir / "cache").toString)])
    check ref s!"machine loss: a v2 slot holding a run that never started is not read ({repr result.ran}): {result.out}{result.err}"
      (result.complete && result.ran == .exited 0)

/-- A missing tool or an unfinished run degrades the HTML page rather than refusing it, and names its loss once. -/
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
  let square := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let face := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
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
    -- The renderer's PDF is one the importer refuses, so its web face needs the converter.
    IO.FS.writeBinFile (dir / "refused.pdf") encryptedCanvasPdf
    for d in [renderer, converter] do
      IO.FS.writeFile (d / "lualatex") (fakeRenderer (dir / "refused.pdf"))
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
    let wordsOf (j : Lean.Json) : Option String :=
      (j.getObjValAs? String "message").toOption.map fun m =>
        m ++ ((j.getObjValAs? String "detail").toOption.map ("\n" ++ ·)).getD ""
    -- Runs on one document share a cache: nothing a machine lacked may be remembered.
    for c in [
        ({ name := "no tool", doc := boundary, path := bare, cache := "boundary"
           code := "W0379", subject := some picSrc, located := true, placeholders := 1
           drawings := 0 } : MachineCase),
        { name := "no converter", doc := boundary, path := renderer, cache := "boundary"
          code := "W0378", subject := some picSrc, located := true, placeholders := 1
          drawings := 0 },
        { name := "fallback, no converter", doc := fallback, path := renderer, cache := "fallback"
          code := "W0378", subject := none, located := true, placeholders := 0, drawings := 1 }] do
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
      let losses := coded ["W0378", "W0379", "W0602"]
      t s!"machine loss CLI {c.name}: one {c.code}, under its subject, and no other machine loss"
        (subject.isSome && losses.length == 1 && losses.all fun j =>
          j.getObjValAs? String "code" == .ok c.code &&
            (j.getObjValAs? String "subject").toOption == subject)
      t s!"machine loss CLI {c.name}: the loss's reason reads as one clause"
        (losses.all fun j => (wordsOf j).any (!hasStr · ": ;") &&
          (j.getObjValAs? String "detail").toOption.all (!·.trimAscii.isEmpty))
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
    for (name, doc, path, cache, shows) in [
        ("no SVG tools", svgInclude, bare, "include", "<img"),
        ("killed SVG validator", svgInclude, killed, "include", "<img"),
        ("loader-broken SVG validator", svgInclude, loader, "loader", "<img"),
        ("no icon tools", corpus / "webpage.tex", bare, "webpage", "rel=\"icon\""),
        ("killed icon validator", corpus / "webpage.tex", killed, "webpage", "rel=\"icon\""),
        ("no face validator", boundary, converter, "boundary", "<img"),
        ("fallback, no face validator", fallback, converter, "fallback", "<img")] do
      let out := dir / ((name.replace " " "-").replace "," "") / "page.html"
      let run ← build doc path cache out
      let codes := (recordsOf run).filterMap fun j =>
        if j.getObjValAs? String "event" == .ok "diagnostic" then
          (j.getObjValAs? String "code").toOption else none
      t s!"machine native CLI {name}: the build ships (exit {run.exitCode})" (run.exitCode == 0)
      t s!"machine native CLI {name}: no machine loss and no refusal ({codes})"
        (!codes.any (["E0606", "W0378", "W0379", "W0602", "W0609"].contains ·))
      match ← (IO.FS.readFile out).toBaseIO with
      | .error _ => t s!"machine native CLI {name}: the HTML page is written" false
      | .ok html =>
        t s!"machine native CLI {name}: no placeholder, and the page shows its face"
          ((placeholderTags html).isEmpty && hasStr html shows)
    t "machine native CLI: no build asks the SVG validator"
      (!(← (loader / "calls").pathExists))
    -- A PDF figure's loss is the web page's and an SVG figure's the PDF's, so both are built.
    IO.FS.writeBinFile (dir / "lossy.pdf") type1FigurePdf
    IO.FS.writeBinFile (dir / "lossy.svg") (svgDocument
      ("<filter id=\"soft\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
        "<rect width=\"20\" height=\"20\" fill=\"blue\" filter=\"url(#soft)\"/>"))
    let figures := dir / "figures.tex"
    IO.FS.writeFile figures (lossyFiguresSource (corpus / "fonts"))
    let verdict := dir / "verdict"
    IO.FS.createDirAll verdict
    for tool in ["pdftocairo", "rsvg-convert"] do
      IO.FS.writeFile (verdict / tool) refusingConverter
      IO.setAccessRights (verdict / tool) { user := ⟨true, true, true⟩ }
    let lossOf (path : System.FilePath) (cache subject : String) : IO (Option Lean.Json) := do
      let mut found := none
      for ext in ["html", "pdf"] do
        let run ← build figures path cache (dir / ("figures-" ++ cache) / ("page." ++ ext))
        for j in recordsOf run do
          if (j.getObjValAs? String "code").toOption == some "W0609" &&
              (j.getObjValAs? String "subject").toOption == some subject then
            found := some j
      return found
    let helpOf (j : Option Lean.Json) : String :=
      (j.bind fun j => (j.getObjValAs? String "help").toOption).getD ""
    let lineOf (j : Option Lean.Json) : String := (j.bind wordsOf).getD ""
    let pdfAbsent ← lossOf bare "figures-absent" "figure:pdf:font:type1"
    let svgAbsent ← lossOf bare "figures-absent" "figure:svg:property:filter"
    let anyTool (s : String) : String :=
      (s.replace "poppler's pdftocairo" "its converter").replace "librsvg's rsvg-convert" "its converter"
    t s!"figure remedy CLI: no converter gives PDF and SVG figures one install line ({helpOf pdfAbsent} | {helpOf svgAbsent})"
      (pdfAbsent.isSome && svgAbsent.isSome && anyTool (helpOf pdfAbsent) == anyTool (helpOf svgAbsent) &&
        hasStr (helpOf pdfAbsent) "install poppler's pdftocairo")
    t s!"figure remedy CLI: with no converter, neither figure carries a run's words ({lineOf pdfAbsent} | {lineOf svgAbsent})"
      (pdfAbsent.isSome && svgAbsent.isSome && [pdfAbsent, svgAbsent].all fun j =>
        (j.bind fun j => (j.getObjValAs? String "detail").toOption).isNone &&
          !hasStr (lineOf j) "exited" && !hasStr (lineOf j) "could not execute")
    IO.FS.writeBinFile (dir / "locked.pdf") encryptedCanvasPdf
    let lockedDoc := dir / "locked.tex"
    IO.FS.writeFile lockedDoc (lockedIncludeSource (corpus / "fonts"))
    let locked ← build lockedDoc bare "locked" (dir / "locked" / "page.html")
    let faceless := (recordsOf locked).filter fun j =>
      (j.getObjValAs? String "code").toOption == some "W0602"
    t s!"figure remedy CLI: a refused PDF include with no converter names the install ({faceless.map wordsOf})"
      (locked.exitCode == 0 && !faceless.isEmpty && faceless.all fun j =>
        (wordsOf j).any fun w => hasStr w "install 'pdftocairo'" && hasStr w "PATH")
    for subject in ["figure:pdf:font:type1", "figure:svg:property:filter"] do
      let refused ← lossOf verdict ("figures-verdict-" ++ (subject.splitOn ":")[1]!) subject
      t s!"figure remedy CLI: a converter refusing {subject} gives its words, no install advice ({lineOf refused} | {helpOf refused})"
        (refused.isSome && hasStr (lineOf refused) "synthetic refusal" &&
          !hasStr (helpOf refused) "install" && hasStr (helpOf refused) "\\allow{W0609}")
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
    t s!"machine loss CLI accepted refusal: accepted once, no machine loss named ({named})"
      (acceptedCodes.any (·.any fun c => (c.getObjValAs? String "code").toOption == some "W0382" &&
          (c.getObjValAs? Nat "count").toOption == some 1) &&
        !named.any (["E0606", "W0378", "W0379", "W0602"].contains ·))
    match ← (IO.FS.readFile acceptedOut).toBaseIO with
    | .error _ => t "machine loss CLI accepted refusal: the HTML page is written" false
    | .ok html =>
      let tags := placeholderTags html
      t "machine loss CLI accepted refusal: one labelled placeholder, no request-key image"
        (tags.length == 1 && tags.all labelled && !hasStr html (" src=\"" ++ Ir.picSrcPrefix))
    let rootless (doc path : System.FilePath) (cache : String) (out : System.FilePath) :=
      IO.Process.output {
        cmd := binary.toString, cwd := some dir
        args := #[doc.toString, "-o", out.toString, "--porcelain"]
        env := #[("PATH", some path.toString),
          ("XDG_CACHE_HOME", some (dir / ("cache-" ++ cache)).toString),
          ("LEANTEX_FONT", some font.toString), ("TMPDIR", some (dir / "no-such-root").toString)] }
    let codeOf (j : Lean.Json) := (j.getObjValAs? String "code").toOption
    let included ← rootless svgInclude loader "rootless-include" (dir / "rootless-include" / "page.html")
    let namesRoot (j : Lean.Json) := (wordsOf j).any fun m =>
      hasStr m "no-such-root" && hasStr m "(TMPDIR)" && !hasStr m "leantex-"
    t s!"machine loss CLI no scratch root: an SVG include needs none, and draws (exit {included.exitCode})"
      (included.exitCode == 0 && !(recordsOf included).any fun j => codeOf j == some "W0602")
    let asked ← rootless boundary renderer "rootless-version" (dir / "rootless-version" / "page.html")
    t s!"machine loss CLI no scratch root: W0379 names the root the version question lacked (exit {asked.exitCode})"
      (asked.exitCode == 0 && (recordsOf asked).any fun j => codeOf j == some "W0379" && namesRoot j)
    -- Remember the version under a working root, so the next render meets the missing root.
    discard <| build boundary renderer "rootless-picture" (dir / "rootless-warm" / "page.html")
    let unseen := dir / "unseen.tex"
    IO.FS.writeFile unseen ((acceptedSource (corpus / "fonts")).replace "(2,1)" "(3,1)")
    let picture ← rootless unseen renderer "rootless-picture" (dir / "rootless-picture" / "page.html")
    t s!"machine loss CLI no scratch root: an unstartable render is accepted, not a crash (exit {picture.exitCode})"
      (picture.exitCode == 0 && (recordsOf picture).any fun j => event j == some "accepted")
    let noisy := dir / "noisy"
    writeScript (noisy / "lualatex") (noisyRenderer (corpus / "figures" / "box.pdf"))
    let spoke ← build boundary noisy "noisy" (dir / "noisy-out" / "page.html")
    let codes := (recordsOf spoke).filterMap codeOf
    t s!"machine loss CLI renderer writing no UTF-8: drawn, not unfinished (exit {spoke.exitCode}, {codes})"
      (spoke.exitCode == 0 && codes.contains "N0023" && !codes.contains "W0382" && !codes.contains "W0378")
    let splitLog := dir / "split-log"
    writeScript (splitLog / "lualatex") (splitLogRenderer (corpus / "figures" / "box.pdf"))
    let logged ← build boundary splitLog "split-log" (dir / "split-log-out" / "page.html")
    let loggedCodes := (recordsOf logged).filterMap codeOf
    t s!"machine loss CLI renderer whose log is no UTF-8: drawn, not unfinished (exit {logged.exitCode}, {loggedCodes})"
      (logged.exitCode == 0 && loggedCodes.contains "N0023" && !loggedCodes.contains "W0382" &&
        !loggedCodes.contains "W0378")
    let realRoot := dir / "real-root"
    IO.FS.createDirAll realRoot
    symlink realRoot (dir / "linked-root")
    let pwdSays := dir / "pwd-says"
    writeScript (pwdSays / "lualatex") ("#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' " ++
      "'synthetic boundary renderer 1'; exit 0; fi\nprintf '%s\\n' \"$(pwd)/pic.tex: cannot start\" >&2\nexit 127\n")
    let linked ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #[boundary.toString, "-o", (dir / "linked-out" / "page.html").toString, "--porcelain"]
      env := #[("PATH", some pwdSays.toString), ("XDG_CACHE_HOME", some (dir / "cache-linked").toString),
        ("LEANTEX_FONT", some font.toString), ("TMPDIR", some ((dir / "linked-root").toString ++ "/"))] }
    t s!"machine loss CLI linked temporary root: W0382 masks the scratch directory (exit {linked.exitCode})"
      ((recordsOf linked).any fun j => codeOf j == some "W0382" &&
        ((j.getObjValAs? String "help").toOption.any fun h =>
          hasStr h "<scratch>/pic.tex: cannot start" && !hasStr h "leantex-"))
    let pwdLog := dir / "pwd-log"
    writeScript (pwdLog / "lualatex") ("#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' " ++
      "'synthetic boundary renderer 1'; exit 0; fi\nprintf '%s\\n' \"! Synthetic refusal at $(pwd)/pic.tex.\" > pic.log\nexit 1\n")
    let refusedHere ← build boundary pwdLog "pwd-log" (dir / "pwd-log-out" / "page.html")
    let replayedHere ← build boundary pwdLog "pwd-log" (dir / "pwd-log-again" / "page.html")
    let helpOf (run : IO.Process.Output) : List String := (recordsOf run).filterMap fun j =>
      if codeOf j == some "W0382" then (j.getObjValAs? String "help").toOption else none
    t s!"machine loss CLI refusal naming its scratch directory: remembered as <scratch> (exit {refusedHere.exitCode})"
      (match helpOf refusedHere with
        | [h] => hasStr h "<scratch>/pic.tex" && !hasStr h "leantex-" && helpOf replayedHere == [h]
        | _ => false)
    let unversioned := dir / "unversioned"
    writeScript (unversioned / "lualatex") ("#!/bin/sh\nprintf '%s\\n' 'luatex: error while loading " ++
      "shared libraries: libsynthetic.so.0: cannot open shared object file' >&2\nexit 127\n")
    let unloaded ← build boundary unversioned "unversioned" (dir / "unversioned-out" / "page.html")
    t s!"machine loss CLI renderer a loader stops at its version: W0379 carries the loader's words (exit {unloaded.exitCode})"
      (unloaded.exitCode == 0 && (recordsOf unloaded).any fun j => codeOf j == some "W0379" &&
        ((wordsOf j).any (hasStr · "error while loading shared libraries")))
    let hanging := dir / "hanging"
    writeScript (hanging / "lualatex") "#!/bin/sh\nexec /bin/sleep 30\n"
    let slow ← build boundary hanging "hanging" (dir / "hanging-out" / "page.html")
    t s!"machine loss CLI killed version question: W0379 names how the question ended (exit {slow.exitCode})"
      (slow.exitCode == 0 && (recordsOf slow).any fun j => codeOf j == some "W0379" &&
        ((j.getObjValAs? String "detail").toOption.any (hasStr · "version was not read") &&
          (j.getObjValAs? String "detail").toOption.any (hasStr · "no version within")))
    let unloadable := dir / "unloadable"
    writeScript (unloadable / "lualatex") ("#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' 'synthetic boundary renderer 1'; exit 0; fi\n" ++
      "printf 'luatex: error while loading shared libraries: libsynthetic.so.0: cannot open shared object file\\033]0;zz\\007\\n' >&2\nexit 127\n")
    let stopped ← build boundary unloadable "unloadable" (dir / "unloadable-out" / "page.html")
    t s!"machine loss CLI unloadable renderer: W0382 carries the loader's words (exit {stopped.exitCode})"
      ((recordsOf stopped).any fun j => codeOf j == some "W0382" &&
        ((j.getObjValAs? String "help").toOption.any (hasStr · "error while loading shared libraries")))
    let human ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #[boundary.toString, "-o", (dir / "unloadable-human" / "page.html").toString, "-v"]
      env := #[("PATH", some unloadable.toString),
        ("XDG_CACHE_HOME", some (dir / "cache-unloadable-human").toString),
        ("LEANTEX_FONT", some font.toString)] }
    let raw := human.stderr.toList.filter fun c =>
      (c.toNat < 0x20 && c != '\n') || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F)
    t s!"machine loss CLI unloadable renderer: -v prints no raw control character ({raw.length})"
      (hasStr human.stderr "error while loading shared libraries" && raw.isEmpty)
  legacySlotChecks ref

end Tests
