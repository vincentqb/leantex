import LeanTex.Core.Image

/-! Vector image IO. Captured SVG bytes remain the browser source. Fresh
conversions return bytes; only the driver decides when to publish them. -/

namespace LeanTex.Cli.ImageAssets

open LeanTex.Core

/-- A deliberately narrow support boundary, evaluated over libxml's parsed
XML, never the source spelling. Only fragment references are supported.
CSS is plain declarations/rules without functions, escapes or at-rules;
presentation attributes admit exactly `url(#ASCII-id)`, without paint-server
fallback syntax such as `url(#id) red`. Transforms and SMIL timing have their
own non-resource function syntax. Animated resource/style assignments,
scripts and foreign objects are refused. This is a refusal boundary, not a
second XML or CSS parser. -/
private def supportedSvg : String :=
  let localUrl := "(starts-with(normalize-space(.),'url(#') and " ++
    "substring(normalize-space(.),string-length(normalize-space(.)),1)=')' and " ++
    "string-length(normalize-space(.))>6 and " ++
    "translate(substring(normalize-space(.),6,string-length(normalize-space(.))-6)," ++
    "'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.:-','')='')"
  let cssSyntax := "(contains(.,'(') or contains(.,'\\') or contains(.,'@'))"
  let unsupported :=
    "//processing-instruction() | " ++
    "//*[local-name()='script' or local-name()='foreignObject'] | " ++
    "//@*[local-name()='base' or starts-with(local-name(),'on')] | " ++
    "//@*[local-name()='href' or local-name()='src'][not(starts-with(normalize-space(.),'#'))] | " ++
    "//*[local-name()='style'][" ++ cssSyntax ++ "] | " ++
    "//@*[not(local-name()='transform' or local-name()='gradientTransform' or " ++
      "local-name()='patternTransform' or local-name()='begin' or local-name()='end')]" ++
      "[" ++ cssSyntax ++ " and not(" ++ localUrl ++ ")] | " ++
    "//@*[local-name()='attributeName'][" ++
      "normalize-space(.)='href' or substring-after(normalize-space(.),':')='href' or " ++
      "normalize-space(.)='src' or substring-after(normalize-space(.),':')='src' or " ++
      "normalize-space(.)='base' or substring-after(normalize-space(.),':')='base' or " ++
      "normalize-space(.)='style' or normalize-space(.)='attributeName' or " ++
      "normalize-space(.)='from' or normalize-space(.)='to' or normalize-space(.)='by' or " ++
      "normalize-space(.)='values' or starts-with(normalize-space(.),'on')]"
  "boolean(/*[local-name()='svg' and namespace-uri()='http://www.w3.org/2000/svg']) and " ++
    "not(" ++ unsupported ++ ")"

private def saxArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--sax", input.toString]

private def xpathArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--xpath", supportedSvg, input.toString]

private def rsvgArgs (format : String) (input output : System.FilePath) : Array String :=
  #["--format=" ++ format, "--output", output.toString, input.toString]

private def pdfSvgArgs (page : String) (input output : System.FilePath) : Array String :=
  #["-svg", "-f", page, "-l", page, input.toString, output.toString]

private def pdfSvgRoot : String := "<svg preserveAspectRatio=\"none\" "

private def commandText (tool : String) (args : Array String) : String :=
  tool ++ " " ++ String.intercalate " " args.toList

/-- The normalized host-tool recipe behind browser vector faces. The
hermetic source key hashes this value, while the browser oracle separately
records the exact output bytes. Every invocation below reads these same
argument builders, so a recipe change invalidates the committed report. -/
def browserFaceContract : String :=
  let input := System.FilePath.mk "<input>"
  let output := System.FilePath.mk "<output>"
  String.intercalate "\n" [
    commandText "xmllint" (saxArgs input),
    commandText "xmllint" (xpathArgs input),
    commandText "rsvg-convert" (rsvgArgs "pdf" input output),
    commandText "rsvg-convert" (rsvgArgs "svg" input output),
    commandText "pdftocairo" (pdfSvgArgs "<page>" input output),
    "pdftocairo root " ++ pdfSvgRoot]

private def runChecked (tool : String) (args : Array String) : IO String := do
  let ran ← IO.Process.output { cmd := tool, args }
  if ran.exitCode != 0 then
    throw <| IO.userError s!"{tool} exited {ran.exitCode}: {ran.stderr.trimAscii.toString}"
  return ran.stdout

/-- SAX reports a DTD before any tree query can hide it. Do not enable
entity substitution, external-DTD loading, XInclude or recovery. Both
passes read the same captured file; namespace aliases and XML character
references are resolved by libxml before the XPath boundary sees them. -/
private def checkSvgFile (input : System.FilePath) : IO Unit := do
  let sax ← runChecked "xmllint" (saxArgs input)
  let dtdEvent := fun raw =>
    let event := raw.trimAscii.toString
    ["internalSubset(", "externalSubset(", "entityDecl("].any fun marker =>
      (event.splitOn marker).length > 1
  if (sax.splitOn "\n").any dtdEvent then
    throw <| IO.userError "SVG resource boundary refuses DTDs and entity declarations"
  unless (sax.splitOn "\n").any (·.trimAscii.toString == "SAX.startDocument()") &&
      (sax.splitOn "\n").any (·.trimAscii.toString == "SAX.endDocument()") do
    throw <| IO.userError "SVG validation received no complete XML parse"
  let result ← runChecked "xmllint" (xpathArgs input)
  unless result.trimAscii.toString == "true" do
    throw <| IO.userError "SVG resource boundary requires fragment-only references and plain CSS; paint servers must be exactly url(#id), without fallback syntax; DTDs, scripts, foreign objects, base URIs, CSS functions/escapes/at-rules and animated resource/style assignments are unsupported"

/-- Convert one captured input. A failed spawn, nonzero exit or absent
output is an error, including when a failed process left an output file.
SVG inputs pass the support boundary before librsvg sees them. -/
private def convert (tool inputExt outputExt : String)
    (args : System.FilePath → System.FilePath → Array String) (bytes : ByteArray) :
    IO (Except String ByteArray) := do
  try
    IO.FS.withTempDir fun dir => do
      let input := dir / ("source." ++ inputExt)
      let output := dir / ("face." ++ outputExt)
      IO.FS.writeBinFile input bytes
      if inputExt == "svg" then checkSvgFile input
      discard <| runChecked tool (args input output)
      let result ← IO.FS.readBinFile output
      if result.isEmpty then throw <| IO.userError s!"{tool} produced an empty image"
      return .ok result
  catch e => return .error s!"{tool}: {e}"

/-- Validate captured SVG bytes before accepting a browser companion. An
error lets the caller fall back to converting its selected PDF page.
Success includes a usable static PDF plan; retain the original bytes for
the browser, preserving animation and source identity. Requires the
installed xmllint and librsvg tools; either failing is an error value. -/
def validateSvg (bytes : ByteArray) (params : Image.PlanParams := .default) :
    IO (Except String Image.Plan) := do
  let pdf ← convert "rsvg-convert" "svg" "pdf" (rsvgArgs "pdf") bytes
  return pdf >>= fun b => Image.probe b >>= Image.plan params

/-- librsvg's static vector reading of a self-contained SVG. The caller
keeps the captured SVG bytes for the browser, including SMIL animation. -/
def svgPlan (params : Image.PlanParams) (bytes : ByteArray)
    (page : PdfRead.PageSelection := .first) :
    IO (Except String Image.Plan) := do
  if page != .first && page != .number 1 then
    return .error "SVG conversion supplies a static first frame; the selected poster requires a PDF frame sequence"
  validateSvg bytes params

/-- Cairo's static SVG face for print and reduced motion. Use `pdfSvg` on
the selected page instead when a companion PDF supplies a chosen frame. -/
def svgPoster (bytes : ByteArray) : IO (Except String ByteArray) := do
  if let .error e := (← validateSvg bytes) then return .error e
  convert "rsvg-convert" "svg" "svg" (rsvgArgs "svg") bytes

/-- Only the converter-owned root changes. The native PDF form stretches
the selected page onto the first frame's canvas; SVG's default `meet`
would instead letterbox its ink inside the same image box. -/
private def stretchPdfSvg (bytes : ByteArray) : Except String ByteArray := do
  let some text := String.fromUTF8? bytes
    | throw "pdftocairo produced non-UTF-8 SVG"
  let [head, body] := text.splitOn "<svg "
    | throw "pdftocairo produced an unexpected SVG root"
  let prolog := head.trimAscii.toString
  unless prolog.isEmpty || prolog == "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" do
    throw "pdftocairo produced an unexpected SVG prolog"
  let header := (body.splitOn ">").headD ""
  unless header != body && (header.splitOn "preserveAspectRatio").length == 1 do
    throw "pdftocairo produced unexpected SVG root attributes"
  return (head ++ pdfSvgRoot ++ body).toUTF8

/-- Poppler reads the physical page selected by the same page-tree
traversal as the native importer, including `last`; `/Count` is never a
substitute for that traversal. -/
def pdfSvg (bytes : ByteArray) (page : PdfRead.PageSelection) :
    IO (Except String ByteArray) := do
  match PdfRead.pageNumber bytes page with
  | .error e => return .error e
  | .ok n =>
    return (← convert "pdftocairo" "pdf" "svg" (pdfSvgArgs (toString n)) bytes) >>= stretchPdfSvg

end LeanTex.Cli.ImageAssets
