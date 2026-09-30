import Tests.Support
import LeanTex.Cli.ImageAssets

open LeanTex.Core LeanTex.Cli

namespace Tests

private def svgToolRunner (calls : IO.Ref (Array String)) (tool : String)
    (failure : IO.Ref (Option (Except IO.Error IO.Process.Output)))
    (source : ByteArray) (args : IO.Process.SpawnArgs) : IO IO.Process.Output := do
  calls.modify (·.push args.cmd)
  let some input := args.args.back? | throw <| IO.userError "missing captured input"
  unless (← IO.FS.readBinFile input) == source do
    throw <| IO.userError "conversion changed the captured source"
  -- Even a failing converter may leave bytes; its exit still decides.
  if args.cmd == "rsvg-convert" then
    let some output := args.args[2]? | throw <| IO.userError "missing output argument"
    IO.FS.writeBinFile (System.FilePath.mk output) svgCanvasPdf
  if args.cmd == tool then
    if let some result ← failure.get then return ← EIO.ofExcept result
  return { exitCode := 0, stderr := "", stdout :=
    if args.cmd == "xmllint" then
      if args.args.contains "--sax" then "SAX.startDocument()\nSAX.endDocument()\n"
      else "true"
    else if args.cmd == "xsltproc" then String.fromUTF8! source
    else "" }

/-- Removing any required executable names its dependency and PATH recovery.
Restoring it retries the same captured source and replaces the shipped
placeholder with a PDF form. Only the process boundary is simulated:
temporary files, PDF import, fulfilment, layout and emission are real. -/
def svgToolChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let source := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let req : Image.Request := { src := "figure.svg" }
  let doc := (elabStr "\\includegraphics[width=20pt,alt={An invented square}]{figure.svg}").1
  let geom := Layout.Geom.ofPage doc.page
  let fulfil (result : Except String Image.Plan) :=
    Image.fulfilOne req (.decoded req.src result none none (some source) none)
  let artifact (entry : Image.Loaded) :=
    let imgs : Image.Store := { entries := #[entry] }
    let out := layoutOf fonts doc geom none imgs
    (out, pdfText (Pdf.write geom fonts out.pages {} imgs))
  let imageIndices (out : Layout.Out) :=
    out.pages.flatMap fun page => page.lines.flatMap fun line =>
      line.segs.filterMap fun
        | .image idx _ _ => some idx
        | _ => none
  let healthy := #["xmllint", "xmllint", "xsltproc", "rsvg-convert"]
  for (tool, package, stopped) in [
      ("xmllint", "libxml2", #["xmllint"]),
      ("xsltproc", "libxslt", #["xmllint", "xmllint", "xsltproc"]),
      ("rsvg-convert", "librsvg", healthy)] do
    for thrown in [false, true] do
      let label := s!"SVG tools {tool} (exception={thrown})"
      let missing : Except IO.Error IO.Process.Output :=
        if thrown then .error (IO.Error.noFileOrDirectory tool 2 "missing executable")
        else .ok { exitCode := 255, stdout := ""
                   stderr := s!"could not execute external process '{tool}'\n" }
      let failure ← IO.mkRef (some missing)
      let calls ← IO.mkRef #[]
      let runTool := svgToolRunner calls tool failure source
      let result ← ImageAssets.svgPlan {} source .last (runTool := runTool)
      let (missing, diag) := fulfil result
      let (before, beforePdf) := artifact missing
      check ref (label ++ " stops at the unavailable tool") ((← calls.get) == stopped)
      check ref (label ++ " names the executable and dependency recovery")
        (diag.any fun d => hasStr d.message tool &&
          hasStr d.message ("brew install " ++ package) && hasStr d.message "PATH")
      check ref (label ++ " does not ask the author to re-export")
        (diag.any fun d => !hasStr d.message "re-export" &&
          !(d.help.any (hasStr · "re-export")))
      check ref (label ++ " keeps W0602 and its source subject")
        (diag.any fun d => d.kind == .W0602 && !d.demoted && d.subject == some req.src)
      check ref (label ++ " ships a placeholder, not the failed output")
        ((imageIndices before).size == 1 && missing.info.isNone &&
          bytesContain beforePdf "re S" &&
          !bytesContain beforePdf "/Im1 Do")
      failure.set none
      calls.set #[]
      let restored ← ImageAssets.svgPlan {} source .last (runTool := runTool)
      let (loaded, afterDiag) := fulfil restored
      let (after, afterPdf) := artifact loaded
      check ref (label ++ " retries the same source after tool restoration")
        ((← calls.get) == healthy && afterDiag.isNone)
      check ref (label ++ " restored source ships a form and image paint")
        (imageIndices after == #[some 0] &&
          bytesContain afterPdf "/Subtype /Form" && bytesContain afterPdf "/Im1 Do" &&
          bytesContain afterPdf "0 0 1 rg 0 0 120 80 re f")
  for (code, stderr) in [
      (19, "bad SVG geometry"),
      (255, "unsupported SVG feature"),
      (19, "could not execute external process 'rsvg-convert'"),
      (255, "could not execute external process 'different-tool'"),
      (255, "could not execute external process 'rsvg-convert'\nconverter context"),
      (255, "")] do
    let calls ← IO.mkRef #[]
    let failure ← IO.mkRef (some (.ok { exitCode := code, stdout := "ignored", stderr }))
    let result ← ImageAssets.svgPlan {} source .last
      (runTool := svgToolRunner calls "rsvg-convert" failure source)
    let (_, diag) := fulfil result
    check ref s!"SVG converter error {code}/{stderr} keeps its evidence without install advice"
      (diag.any fun d => hasStr d.message s!"rsvg-convert exited {code}: {stderr}" &&
        !hasStr d.message "brew install" && d.kind == .W0602)
  let calls ← IO.mkRef #[]
  let failure ← IO.mkRef (some (.error (IO.Error.resourceExhausted none 24 "open files")))
  let result ← ImageAssets.svgPlan {} source .last
    (runTool := svgToolRunner calls "rsvg-convert" failure source)
  check ref "SVG process resource failure keeps its evidence without install advice"
    (match result with
      | .error err => hasStr err "open files" && !hasStr err "brew install"
      | .ok _ => false)

end Tests
