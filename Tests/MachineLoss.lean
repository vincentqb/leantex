module

public import Tests.Support
public import LeanTex.Cli.Boundary
public import LeanTex.Cli.Publication
public import Lean.Data.Json
public import LeanTex.Cli.RunBounded

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- The boundary renderer, its terminal output ending in bytes that are no
UTF-8, as a TeX engine's line breaking can split a character. -/
private def noisyRenderer (pdf : System.FilePath) : String :=
  fakeRenderer pdf ++ "printf 'Transcript written on pic.log \\303\\n\\377'\n"

/-- The boundary renderer, its log ending in a character a line break split. -/
private def splitLogRenderer (pdf : System.FilePath) : String :=
  fakeRenderer pdf ++ "printf 'Transcript of an invented run \\303\\n' >> pic.log\n"

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
  "\\allow{E0382}\n\\begin{document}\nAn invented pattern follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\pattern (0,0) rectangle (2,1);\n\\end{tikzpicture}\n\\end{document}\n"

/-- An included SVG figure, by a generated file beside the document.
Invented content. -/
private def includeSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented square follows.\n\n" ++
  "\\includegraphics[width=20pt,alt={An invented square}]{square.svg}\n\\end{document}\n"

/-- A picture the rendered subset draws in part — its frame and its label —
that a pattern fill sends to the boundary. Invented content. -/
private def fallbackSource (fonts : System.FilePath) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Source Serif Pro\" }\n" ++
  "\\begin{document}\nAn invented picture follows.\n\n" ++
  "\\begin{tikzpicture}\n  \\draw (0,0) rectangle (3,1);\n  \\pattern (0,0) rectangle (1,1);\n" ++
  "  \\node at (1.5,0.5) {Mark};\n\\end{tikzpicture}\n\nText follows the picture.\n" ++
  "\\end{document}\n"

/-- One machine the build runs on: the document, the directory its PATH
holds (no tool, or a synthetic renderer — never one that answers the
picture), and the one loss that machine owes: its code, its subject
(`none`: the picture the run itself declares at the boundary, by its
N0023), whether it carries the picture's source line, and what the page
shows in its place — labelled placeholders, or the rendered subset's inline
drawings. -/
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

/-- **A tool this machine lacks, or a run it could not finish, degrades
the HTML page instead of refusing it**, on the paths fixed here, and each
such loss is named once, under its subject: a boundary picture no tool drew
(W0379); one drawn whose browser face was not converted (W0378, at the
picture's span — and where the rendered subset draws the picture in part,
the subset's drawing ships). The defects refused the page (E0606) and wrote
nothing while the PDF shipped, and so did a refused render the document
accepts (`\allow{E0382}`, the former spelling of W0382), which now ships the
page's placeholder too. A boundary render that did not finish — killed, a
spawn that raised, or a nonzero exit with no log, a renderer that cannot
start after naming its version among them — is W0382 as well, withdrawn
nowhere and remembered nowhere (`boundaryUnfinishedChecks`). An SVG is no
such path: an included SVG, an SVG page icon and a converted face are read
by the engine itself, so on a machine with no SVG tool, or one whose
validator is killed or cannot start, each ships, nothing is named and no
validator is asked. The library half holds the pure step — a faceless
boundary picture refuses the unmarked page and ships the marked one with no
new diagnostic and the PDF unchanged — and the CLI half runs the built
binary. Invented content; the synthetic tools copy a committed PDF and a
generated SVG. -/
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
    -- The renderer's answer is one the engine's importer refuses (an
    -- encrypted file), so its web face is the converter's or none: what a
    -- machine without the converter, or without the face check, loses.
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
    -- A loss's reason is its detail, beside the words it shares with every site.
    let wordsOf (j : Lean.Json) : Option String :=
      (j.getObjValAs? String "message").toOption.map fun m =>
        m ++ ((j.getObjValAs? String "detail").toOption.map ("\n" ++ ·)).getD ""
    -- Runs on one document share a cache: a missing tool, and a check that
    -- did not finish, are remembered nowhere, so each next machine asks again.
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
      let losses := coded ["W0378", "W0379", "W0602", "W0605"]
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
    -- No SVG validator is a tool any more: an included SVG, an SVG page icon
    -- and a boundary picture's converted face are the engine's own reading,
    -- so a machine with no SVG tool, or with one the machine kills or a
    -- missing library stops, ships each and names no loss, and no build asks
    -- a validator.
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
        (!codes.any (["E0606", "W0378", "W0379", "W0602", "W0605", "W0609"].contains ·))
      match ← (IO.FS.readFile out).toBaseIO with
      | .error _ => t s!"machine native CLI {name}: the HTML page is written" false
      | .ok html =>
        t s!"machine native CLI {name}: no placeholder, and the page shows its face"
          ((placeholderTags html).isEmpty && hasStr html shows)
    t "machine native CLI: no build asks the SVG validator"
      (!(← (loader / "calls").pathExists))
    -- A refused render the document accepts under the code's former
    -- spelling: the faceless picture's loss is W0382, accepted once, and the
    -- page ships its placeholder.
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
      (acceptedCodes.any (·.any fun c => (c.getObjValAs? String "code").toOption == some "W0382" &&
          (c.getObjValAs? Nat "count").toOption == some 1) &&
        !named.any (["E0606", "W0378", "W0379", "W0602", "W0605"].contains ·))
    match ← (IO.FS.readFile acceptedOut).toBaseIO with
    | .error _ => t "machine loss CLI accepted refusal: the HTML page is written" false
    | .ok html =>
      let tags := placeholderTags html
      t "machine loss CLI accepted refusal: one labelled placeholder, and no image names a request key"
        (tags.length == 1 && tags.all labelled && !hasStr html (" src=\"" ++ Ir.picSrcPrefix))
    -- A temporary root in which no directory can be made is a fact about
    -- the machine: the converters' and the renderer's scratch directories
    -- cannot be made, so the include degrades and an accepted render ships
    -- its placeholder, where IO.FS.withTempDir ended the process with a
    -- segmentation fault (exit 139).
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
    t s!"machine loss CLI no scratch root: W0379 says the version could not be asked, naming the root (exit {asked.exitCode})"
      (asked.exitCode == 0 && (recordsOf asked).any fun j => codeOf j == some "W0379" && namesRoot j)
    -- The renderer's version is remembered under a root that works, so a
    -- picture no build has drawn meets the missing root at its render.
    discard <| build boundary renderer "rootless-picture" (dir / "rootless-warm" / "page.html")
    let unseen := dir / "unseen.tex"
    IO.FS.writeFile unseen ((acceptedSource (corpus / "fonts")).replace "(2,1)" "(3,1)")
    let picture ← rootless unseen renderer "rootless-picture" (dir / "rootless-picture" / "page.html")
    t s!"machine loss CLI no scratch root: a render that cannot start is accepted, never a crash (exit {picture.exitCode})"
      (picture.exitCode == 0 && (recordsOf picture).any fun j => event j == some "accepted")
    -- A renderer whose terminal output is no UTF-8 still finished, and its
    -- render is read as the plain renderer's is: drawn, its web face the
    -- engine's own reading of it.
    let noisy := dir / "noisy"
    writeScript (noisy / "lualatex") (noisyRenderer (corpus / "figures" / "box.pdf"))
    let spoke ← build boundary noisy "noisy" (dir / "noisy-out" / "page.html")
    let codes := (recordsOf spoke).filterMap codeOf
    t s!"machine loss CLI renderer writing no UTF-8: the render is drawn, not unfinished (exit {spoke.exitCode}, {codes})"
      (spoke.exitCode == 0 && codes.contains "N0023" && !codes.contains "W0382" && !codes.contains "W0378")
    let splitLog := dir / "split-log"
    writeScript (splitLog / "lualatex") (splitLogRenderer (corpus / "figures" / "box.pdf"))
    let logged ← build boundary splitLog "split-log" (dir / "split-log-out" / "page.html")
    let loggedCodes := (recordsOf logged).filterMap codeOf
    t s!"machine loss CLI renderer whose log is no UTF-8: the render is drawn, not unfinished (exit {logged.exitCode}, {loggedCodes})"
      (logged.exitCode == 0 && loggedCodes.contains "N0023" && !loggedCodes.contains "W0382" &&
        !loggedCodes.contains "W0378")
    -- A temporary root spelled through a link and a trailing separator: the
    -- renderer names its working directory by its real path, and that name
    -- is still spelled out of its words.
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
    t s!"machine loss CLI linked temporary root: W0382 spells the scratch directory out of the renderer's words (exit {linked.exitCode})"
      ((recordsOf linked).any fun j => codeOf j == some "W0382" &&
        ((j.getObjValAs? String "help").toOption.any fun h =>
          hasStr h "<scratch>/pic.tex: cannot start" && !hasStr h "leantex-"))
    -- A refusal whose log names the scratch directory: the remembered words,
    -- replayed on every later build, name no random directory.
    let pwdLog := dir / "pwd-log"
    writeScript (pwdLog / "lualatex") ("#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' " ++
      "'synthetic boundary renderer 1'; exit 0; fi\nprintf '%s\\n' \"! Synthetic refusal at $(pwd)/pic.tex.\" > pic.log\nexit 1\n")
    let refusedHere ← build boundary pwdLog "pwd-log" (dir / "pwd-log-out" / "page.html")
    let replayedHere ← build boundary pwdLog "pwd-log" (dir / "pwd-log-again" / "page.html")
    let helpOf (run : IO.Process.Output) : List String := (recordsOf run).filterMap fun j =>
      if codeOf j == some "W0382" then (j.getObjValAs? String "help").toOption else none
    t s!"machine loss CLI refusal naming its scratch directory: the remembered words name <scratch> (exit {refusedHere.exitCode})"
      (match helpOf refusedHere with
        | [h] => hasStr h "<scratch>/pic.tex" && !hasStr h "leantex-" && helpOf replayedHere == [h]
        | _ => false)
    -- A renderer a missing library stops before it can say who it is: W0379
    -- says why in the loader's words.
    let unversioned := dir / "unversioned"
    writeScript (unversioned / "lualatex") ("#!/bin/sh\nprintf '%s\\n' 'luatex: error while loading " ++
      "shared libraries: libsynthetic.so.0: cannot open shared object file' >&2\nexit 127\n")
    let unloaded ← build boundary unversioned "unversioned" (dir / "unversioned-out" / "page.html")
    t s!"machine loss CLI renderer a loader stops at its version: W0379 carries the loader's words (exit {unloaded.exitCode})"
      (unloaded.exitCode == 0 && (recordsOf unloaded).any fun j => codeOf j == some "W0379" &&
        ((wordsOf j).any (hasStr · "error while loading shared libraries")))
    -- A renderer whose version question never ends: the help says so, rather
    -- than only telling the user to install a tool that is there.
    let hanging := dir / "hanging"
    writeScript (hanging / "lualatex") "#!/bin/sh\nexec /bin/sleep 30\n"
    let slow ← build boundary hanging "hanging" (dir / "hanging-out" / "page.html")
    t s!"machine loss CLI killed version question: W0379 names how the question ended (exit {slow.exitCode})"
      (slow.exitCode == 0 && (recordsOf slow).any fun j => codeOf j == some "W0379" &&
        ((j.getObjValAs? String "message").toOption.any (hasStr · "version was not read") &&
          (j.getObjValAs? String "detail").toOption.any (hasStr · "no version within")))
    -- A renderer that names its version and then cannot start the render (a
    -- shared library gone since): it leaves no log, so the attempt is no
    -- verdict, and W0382 says what stopped it in the loader's words.
    let unloadable := dir / "unloadable"
    writeScript (unloadable / "lualatex") ("#!/bin/sh\nif [ \"$1\" = --version ]; then printf '%s\\n' 'synthetic boundary renderer 1'; exit 0; fi\n" ++
      "printf 'luatex: error while loading shared libraries: libsynthetic.so.0: cannot open shared object file\\033]0;zz\\007\\n' >&2\nexit 127\n")
    let stopped ← build boundary unloadable "unloadable" (dir / "unloadable-out" / "page.html")
    t s!"machine loss CLI unloadable renderer: W0382 carries the loader's words (exit {stopped.exitCode})"
      ((recordsOf stopped).any fun j => codeOf j == some "W0382" &&
        ((j.getObjValAs? String "help").toOption.any (hasStr · "error while loading shared libraries")))
    -- The same words on a human -v run, where a phase line repeats them: no
    -- control character the renderer wrote reaches the terminal raw.
    let human ← IO.Process.output {
      cmd := binary.toString, cwd := some dir
      args := #[boundary.toString, "-o", (dir / "unloadable-human" / "page.html").toString, "-v"]
      env := #[("PATH", some unloadable.toString),
        ("XDG_CACHE_HOME", some (dir / "cache-unloadable-human").toString),
        ("LEANTEX_FONT", some font.toString)] }
    let raw := human.stderr.toList.filter fun c =>
      (c.toNat < 0x20 && c != '\n') || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F)
    t s!"machine loss CLI unloadable renderer: a human -v run prints no raw control character ({raw.length})"
      (hasStr human.stderr "error while loading shared libraries" && raw.isEmpty)
  legacySlotChecks ref

end Tests
