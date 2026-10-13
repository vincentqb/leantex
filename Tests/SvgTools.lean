module

public import Tests.Support
public import LeanTex.Cli.ImageAssets
public import LeanTex.Cli.Driver
public import LeanTex.Core.FigureStore

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- The converter's process boundary, simulated: it records each spawn,
insists on receiving the canonical spelling of a parse (never an authored
comment), writes a PDF drawing, and answers with the failure set for it. -/
private def svgToolRunner (calls : IO.Ref (Array String))
    (failure : IO.Ref (Option (Except IO.Error IO.Process.Output))) (writes : IO.Ref Bool)
    (args : IO.Process.SpawnArgs) : IO IO.Process.Output := do
  calls.modify (·.push args.cmd)
  let some input := args.args.back? | throw <| IO.userError "missing captured input"
  let canonical ← IO.FS.readBinFile input
  unless (Xml.parse canonical).toBool && !bytesContain canonical "<!--" do
    throw <| IO.userError "the converter received bytes that are not a canonical parse"
  -- Even a failing converter may leave bytes; its exit still decides.
  if args.cmd == "rsvg-convert" && (← writes.get) then
    let some output := args.args[2]? | throw <| IO.userError "missing output argument"
    IO.FS.writeBinFile (System.FilePath.mk output) svgCanvasPdf
  if let some result ← failure.get then return ← EIO.ofExcept result
  return { exitCode := 0, stderr := "", stdout := "" }

/-- **A figure asks the converter only for what the engine does not draw,
and its answer never decides whether the page has a figure.** An exact
figure runs no tool. A lossy one asks librsvg once, with the canonical
parse: drawn, the converter's drawing ships and N0024 names why it was
asked; missing or failing, the engine's drawing ships with every loss named
(W0609), carrying the tool's own words — the dependency and PATH recovery
when it could not start, the exit and its stderr when it ran — and the
same source draws whole once the tool is back. Only the process boundary
is simulated: the native judge, import, conversion recipe, PDF read,
fulfilment and layout are real. -/
def svgToolChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let still := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let lossy := svgDocument
    ("<!-- an authored comment --><filter id=\"soft\"><feGaussianBlur stdDeviation=\"2\"/></filter>" ++
     "<rect width=\"20\" height=\"20\" fill=\"blue\" filter=\"url(#soft)\"/>")
  let req : Image.Request := { src := "figure.svg" }
  let doc := (elabStr "\\includegraphics[width=20pt,alt={An invented square}]{figure.svg}").1
  let geom := Layout.Geom.ofPage doc.page
  let placed (f : Driver.SvgFetch) (bytes : ByteArray) : Array (Option Nat) :=
    let (en, _) := Image.fulfilOne req (.decoded "" f.res none none (some bytes) none)
    let imgs := (FigureStore.settle fonts
      (FigureStore.attach { entries := #[en] } #[some f.drawn])).1
    let out := layoutOf fonts doc geom none imgs
    out.pages.flatMap fun page => page.lines.flatMap fun line =>
      line.segs.filterMap fun
        | .image idx _ _ => some idx
        | _ => none
  let calls ← IO.mkRef (#[] : Array String)
  let failure ← IO.mkRef (none : Option (Except IO.Error IO.Process.Output))
  let writes ← IO.mkRef true
  let converter : Driver.Converter := Driver.Converter.always fun canonical independent =>
    ImageAssets.canonicalPlan {} canonical independent
      (runTool := some (svgToolRunner calls failure writes))
  let exact ← Driver.svgFetch req.src still .first "en" (some converter)
  check ref "SVG tools: an exact figure asks no tool and ships the engine's drawing"
    ((← calls.get).isEmpty && exact.vector.isSome && exact.diags.isEmpty &&
      placed exact still == #[some 0])
  -- A converter that cannot start: Lean's exec failure, a spawn that raised,
  -- a shared library the loader cannot find (127), and a wrapper whose
  -- command cannot run (126).
  let exited (code : UInt32) (stderr : String) : Except IO.Error IO.Process.Output :=
    .ok { exitCode := code, stdout := "", stderr }
  let unstarted : List (String × Except IO.Error IO.Process.Output) := [
    ("exec failure", exited 255 "could not execute external process 'rsvg-convert'\n"),
    ("exception", .error (IO.Error.noFileOrDirectory "rsvg-convert" 2 "missing executable")),
    ("missing library", exited 127
      "rsvg-convert: error while loading shared libraries: libsynthetic.so.0: cannot open shared object file\n"),
    ("wrapper", exited 126 "/bin/sh: rsvg-convert-real: Permission denied\n")]
  for (shape, missing) in unstarted do
    let label := s!"SVG tools rsvg-convert ({shape})"
    failure.set (some missing)
    calls.set #[]
    let degraded ← Driver.svgFetch req.src lossy .first "en" (some converter)
    check ref (label ++ " asks the converter once, with the canonical parse")
      ((← calls.get) == #["rsvg-convert"])
    check ref (label ++ " ships the engine's drawing, never a placeholder")
      (degraded.vector.isSome && degraded.res.toBool && placed degraded lossy == #[some 0])
    check ref (label ++ " names every loss with the dependency and PATH recovery")
      (!degraded.diags.isEmpty && degraded.diags.all fun d =>
        d.code == "W0609" && hasStr (diagWords d) "rsvg-convert" &&
          hasStr (diagWords d) "brew install librsvg" && hasStr (diagWords d) "PATH")
    check ref (label ++ " does not ask the author to re-export")
      (!degraded.diags.isEmpty && degraded.diags.all fun d =>
        !hasStr (diagWords d) "re-export" && !(d.help.any (hasStr · "re-export")))
    failure.set none
    calls.set #[]
    let restored ← Driver.svgFetch req.src lossy .first "en" (some converter)
    check ref (label ++ " draws the same source whole once the tool is back")
      ((← calls.get) == #["rsvg-convert"] && restored.vector.isNone && restored.res.toBool &&
        !restored.diags.isEmpty && restored.diags.all (·.code == "N0024") &&
        placed restored lossy == #[some 0])
  for (code, stderr) in [
      (19, "bad SVG geometry"),
      (255, "unsupported SVG feature"),
      (19, "could not execute external process 'rsvg-convert'"),
      (255, "could not execute external process 'different-tool'"),
      (255, "could not execute external process 'rsvg-convert'\nconverter context"),
      (255, "")] do
    failure.set (some (.ok { exitCode := code, stdout := "ignored", stderr }))
    let failed ← Driver.svgFetch req.src lossy .first "en" (some converter)
    check ref s!"SVG converter error {code}/{stderr} keeps its evidence without install advice"
      (failed.vector.isSome && !failed.diags.isEmpty && failed.diags.all fun d =>
        d.code == "W0609" && hasStr (diagWords d) s!"rsvg-convert exited {code}: {stderr}" &&
          !hasStr (diagWords d) "brew install")
    -- The remedy follows the answer: an exit the converter chose is its
    -- verdict on the figure, which no install changes; a high exit may be a
    -- run that never finished, whose repair the reason would name.
    let helps := failed.diags.filterMap (·.help)
    if code < 126 then
      check ref s!"SVG converter verdict {code}/{stderr} offers accepting the drawing, never an install ({helps})"
        (!helps.isEmpty && helps.size == failed.diags.size && helps.all fun h =>
          !hasStr h "install" && hasStr h "\\allow{W0609}")
    else
      check ref s!"SVG converter run {code}/{stderr} that may not have finished names its repair conditionally ({helps})"
        (!helps.isEmpty && helps.size == failed.diags.size && helps.all fun h =>
          hasStr h "if the reason says it cannot start" && hasStr h "\\allow{W0609}")
  failure.set (some (.error (IO.Error.resourceExhausted none 24 "open files")))
  let exhausted ← Driver.svgFetch req.src lossy .first "en" (some converter)
  check ref "SVG process resource failure keeps its evidence without install advice"
    (exhausted.vector.isSome && !exhausted.diags.isEmpty && exhausted.diags.all fun d =>
      hasStr (diagWords d) "open files" && !hasStr (diagWords d) "brew install")
  check ref "SVG process resource failure is a run that did not finish, its repair named conditionally"
    (exhausted.diags.all fun d => (d.help.map (hasStr · "if the reason says it cannot start")).getD false)
  -- A bounded run's own error already names the tool it ran.
  failure.set (some (.error (IO.userError "rsvg-convert: incomplete output within the run's budget")))
  let overrun ← Driver.svgFetch req.src lossy .first "en" (some converter)
  check ref "SVG converter overrun names its tool once"
    (!overrun.diags.isEmpty && overrun.diags.all fun d =>
      hasStr (diagWords d) "rsvg-convert: incomplete output" &&
        !hasStr (diagWords d) "rsvg-convert: rsvg-convert:")
  -- A run that exits 0 and writes nothing says so, never a reader's error.
  failure.set none
  writes.set false
  let silent ← Driver.svgFetch req.src lossy .first "en" (some converter)
  writes.set true
  check ref "SVG converter run that wrote nothing says so"
    (!silent.diags.isEmpty && silent.diags.all fun d =>
      hasStr (diagWords d) "rsvg-convert wrote no output" && !hasStr (diagWords d) "no such file")

end Tests
