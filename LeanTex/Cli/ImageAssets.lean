import LeanTex.Core.Image

/-! Vector image IO. Captured SVG bytes remain the browser source. Fresh
conversions return bytes; only the driver decides when to publish them. -/

namespace LeanTex.Cli.ImageAssets

open LeanTex.Core

/-- A deliberately narrow support boundary, evaluated over libxml's parsed
XML, never the source spelling. Only fragment references are supported.
CSS is plain declarations/rules without functions, escapes or at-rules;
presentation attributes additionally admit exactly `url(#ASCII-id)`.
Transforms and SMIL timing have their own non-resource function syntax.
Animated resource/style assignments, scripts and foreign objects are refused.
This is a refusal boundary, not a second XML or CSS parser. -/
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
  let sax ← runChecked "xmllint" #["--nonet", "--nocatalogs", "--sax", input.toString]
  let events := sax.splitOn "\n"
  if events.any (·.startsWith "SAX.internalSubset(") then
    throw <| IO.userError "SVG resource boundary refuses DTDs and entity declarations"
  unless events.contains "SAX.startDocument()" && events.contains "SAX.endDocument()" do
    throw <| IO.userError "SVG validation received no complete XML parse"
  let result ← runChecked "xmllint"
    #["--nonet", "--nocatalogs", "--xpath", supportedSvg, input.toString]
  unless result.trimAscii.toString == "true" do
    throw <| IO.userError "SVG resource boundary requires fragment-only references and plain CSS; DTDs, scripts, foreign objects, base URIs, CSS functions/escapes/at-rules and animated resource/style assignments are unsupported"

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
  let pdf ← convert "rsvg-convert" "svg" "pdf"
    (fun input output => #["--format=pdf", "--output", output.toString, input.toString]) bytes
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
  convert "rsvg-convert" "svg" "svg"
    (fun input output => #["--format=svg", "--output", output.toString, input.toString]) bytes

/-- Poppler reads the physical page selected by the same page-tree
traversal as the native importer, including `last`; `/Count` is never a
substitute for that traversal. -/
def pdfSvg (bytes : ByteArray) (page : PdfRead.PageSelection) :
    IO (Except String ByteArray) := do
  match PdfRead.pageNumber bytes page with
  | .error e => return .error e
  | .ok n =>
    convert "pdftocairo" "pdf" "svg"
      (fun input output => #["-svg", "-f", toString n, "-l", toString n,
        input.toString, output.toString]) bytes

end LeanTex.Cli.ImageAssets
