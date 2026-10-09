module

public import LeanTex.Core.Image
public import LeanTex.Cli.PicCache
import LeanTex.Core.PdfCensus
import LeanTex.Cli.SvgPoster
import LeanTex.Cli.ConvCache
import LeanTex.Cli.RunBounded

/-! Vector image IO. Captured SVG bytes remain the browser source. Fresh
conversions return bytes; only the driver decides when to publish them. -/

namespace LeanTex.Cli.ImageAssets

open LeanTex.Core

/-- A deliberately narrow support boundary, evaluated over libxml's parsed
XML, never the source spelling. Only fragment references are supported.
CSS is plain declarations/rules without functions, escapes or at-rules.
Color presentation attributes also admit wholly numeric `rgb()`/`rgba()`
(CSS Color, numeric RGB notation); their alphabet cannot name a resource. This checks
resource closure, not the validity of every numeric color spelling. Other
presentation functions are exactly `url(#ASCII-id)`, without paint-server
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
  let color := "translate(normalize-space(.),'RGBA','rgba')"
  let channels := "substring-before(substring-after(" ++ color ++ ",'('),')')"
  let numericColor :=
    "((local-name()='fill' or local-name()='stroke' or local-name()='color' or " ++
      "local-name()='stop-color' or local-name()='flood-color' or local-name()='lighting-color') and " ++
      "(" ++ color ++ "=concat('rgb('," ++ channels ++ ",')') or " ++
        color ++ "=concat('rgba('," ++ channels ++ ",')')) and " ++
      "string-length(" ++ channels ++ ")>0 and " ++
      "translate(" ++ channels ++ ",'0123456789.%eE+-,/ ','')='')"
  let cssSyntax := "(contains(.,'(') or contains(.,'\\') or contains(.,'@'))"
  let unsupported :=
    "//processing-instruction() | " ++
    "//*[local-name()='script' or local-name()='foreignObject'] | " ++
    "//@*[local-name()='base' or starts-with(local-name(),'on')] | " ++
    "//@*[local-name()='href' or local-name()='src'][not(starts-with(normalize-space(.),'#'))] | " ++
    "//*[local-name()='style'][" ++ cssSyntax ++ "] | " ++
    "//@*[not(local-name()='transform' or local-name()='gradientTransform' or " ++
      "local-name()='patternTransform' or local-name()='begin' or local-name()='end')]" ++
      "[" ++ cssSyntax ++ " and not(" ++ localUrl ++ " or " ++ numericColor ++ ")] | " ++
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

-- An unproven font assumption bypasses caching, never conversion. CSS is
-- deliberately conservative here; resource validation remains independent.
private def fontIndependentSvg : String :=
  let lower := "translate(.,'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz')"
  let units := String.intercalate " or " <|
    ["em", "ex", "ch", "ic", "lh", "cap"].map (fun u => s!"contains({lower},'{u}')")
  "not(//*[local-name()='text' or local-name()='tspan' or local-name()='textPath' or " ++
    "local-name()='tref' or starts-with(local-name(),'altGlyph') or " ++
    "local-name()='glyphRef' or starts-with(local-name(),'font') or " ++
    "local-name()='style'][normalize-space(.)!='' or local-name()!='style'] | " ++
    "//@*[starts-with(local-name(),'font') or local-name()='style' or " ++
      "(local-name()='attributeName' and starts-with(normalize-space(.),'font')) or " ++ units ++ "])"

private def fontArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--xpath", fontIndependentSvg, input.toString]

private def dropDtdArgs (input : System.FilePath) : Array String :=
  #["--nonet", "--nocatalogs", "--dropdtd", "--encode", "UTF-8", input.toString]

private def rsvgArgs (format : String) (input output : System.FilePath) : Array String :=
  #["--format=" ++ format, "--output", output.toString, input.toString]

private def terminalArgs (style input : System.FilePath) : Array String :=
  #["--nonet", "--novalid", "--nodtdattr", "--nowrite", "--nomkdir",
    style.toString, input.toString]

private def pdfSvgArgs (page : String) (input output : System.FilePath) : Array String :=
  #["-svg", "-f", page, "-l", page, input.toString, output.toString]

private def pdfSvgRoot : String := "<svg preserveAspectRatio=\"none\" "

private def commandText (tool : String) (args : Array String) : String :=
  tool ++ " " ++ String.intercalate " " args.toList

private inductive Op where
  | svgPdf (terminal : Bool)
  | svgPoster (terminal : Bool)
  | pdfPage (page : Nat)
  | picFace

private structure Spec where
  tool : String
  inputExt : String
  outputExt : String
  args : System.FilePath → System.FilePath → Array String
  terminal : Bool := false
  stretch : Bool := false

private def Op.spec : Op → Spec
  | .svgPdf terminal => ⟨"rsvg-convert", "svg", "pdf", rsvgArgs "pdf", terminal, false⟩
  | .svgPoster terminal => ⟨"rsvg-convert", "svg", "svg", rsvgArgs "svg", terminal, false⟩
  | .pdfPage n => ⟨"pdftocairo", "pdf", "svg", pdfSvgArgs (toString n), false, true⟩
  | .picFace => ⟨"pdftocairo", "pdf", "svg",
      fun input output => #["-svg", input.toString, output.toString], false, false⟩

private def Spec.tools (s : Spec) : Array String :=
  (if s.inputExt == "svg" then #["xmllint"] else #[]) ++
    (if s.terminal then #["xsltproc"] else #[]) ++ #[s.tool]

private def Spec.recipe (s : Spec) : String :=
  let input := System.FilePath.mk "<input>"
  let output := System.FilePath.mk "<output>"
  let validation := if s.inputExt == "svg" then [
    commandText "xmllint" (saxArgs input),
    commandText "xmllint" (xpathArgs input),
    commandText "xmllint" (fontArgs input),
    commandText "xmllint" (dropDtdArgs input)] else []
  let terminal := if s.terminal then [
    commandText "xsltproc" (terminalArgs "<stylesheet>" input), SvgPoster.stylesheet] else []
  String.intercalate "\n" <| validation ++ terminal ++
    [commandText s.tool (s.args input output), if s.stretch then pdfSvgRoot else ""]

/-- The normalized host-tool recipe behind browser vector faces. The
hermetic source key hashes this value, while the browser oracle separately
records the exact output bytes. Every invocation below reads these same
argument builders, so a recipe change invalidates the committed report. -/
public def browserFaceContract : String :=
  String.intercalate "\n" <|
    ([.svgPdf false, .svgPdf true, .svgPoster false, .svgPoster true,
      .pdfPage 1, .picFace] : List Op).map (·.spec.recipe)

private def toolRecovery (tool : String) : String :=
  let formula := match tool with
    | "xmllint" => "libxml2"
    | "xsltproc" => "libxslt"
    | "rsvg-convert" => "librsvg"
    | "pdftocairo" => "poppler"
    | _ => ""
  let install := if formula.isEmpty then s!"install '{tool}'"
    else s!"install '{tool}' (macOS: brew install {formula})"
  install ++ s!" and ensure '{tool}' is executable on the PATH used to run leantex"

private def runChecked (runTool : IO.Process.SpawnArgs → IO IO.Process.Output)
    (tool : String) (args : Array String) : ExceptT PicCache.Outcome IO String := do
  let recovery := toolRecovery tool
  let ran ← match ← liftM ((runTool { cmd := tool, args }).toBaseIO) with
    | .ok out => pure out
    | .error e =>
      let detail := s!"{tool}: {e}"
      throw <| .inconclusive (match e with
        | .noFileOrDirectory .. | .permissionDenied .. => detail ++ "; " ++ recovery
        | _ => detail)
  if ran.exitCode != 0 then
    let stderr := ran.stderr.trimAscii.toString
    -- Lean's POSIX exec failure has this exact exit and stderr pair, and
    -- 127 is what the dynamic loader exits with when a shared library is
    -- missing, and a shell when the command it was asked for is (126 when
    -- that command cannot run). A converter's own exit 255 is not evidence
    -- that it failed to start.
    let unstarted := (ran.exitCode == 255 &&
        stderr == s!"could not execute external process '{tool}'") ||
      ran.exitCode == 126 || ran.exitCode == 127
    let said := if stderr.isEmpty then ran.stdout.trimAscii.toString else stderr
    let detail := s!"{tool} exited {ran.exitCode}" ++ (if said.isEmpty then "" else ": " ++ said) ++
      (if unstarted then "; " ++ recovery else "")
    -- The process API encodes signals as 128 + signal. High exits are
    -- ambiguous even when the child logged before termination, and a run
    -- that never started said nothing of its own, whatever its stderr holds:
    -- neither is a verdict to remember.
    -- premise: none — xmllint (0–11), xsltproc (0–11) and pdftocairo (0–4, 99) document
    -- their exits, none at or above 126, and rsvg-convert documents none and exits 1 or 2
    throw <| if ran.exitCode >= 126 || (stderr.isEmpty && ran.stdout.trimAscii.isEmpty)
      then .inconclusive detail else .refused detail
  return ran.stdout

/-- SAX distinguishes an exporter's doctype identifier from declarations
that can supply outside meaning. True requests removal of that inert
identifier from the converter input; declarations and non-predefined
entity references remain unsupported. Parser error callbacks also refuse.
The caller must first require a successful parser exit. -/
public def svgSaxBoundary (sax : String) : Except String Bool := do
  let events := (sax.splitOn "\n").map (·.trimAscii.toString)
  let has := fun name => events.any (·.startsWith ("SAX." ++ name ++ "("))
  if ["entityDecl", "attributeDecl", "elementDecl", "notationDecl",
      "unparsedEntityDecl", "resolveEntity", "getParameterEntity",
      "getEntity", "reference"].any has then
    throw "SVG resource boundary refuses DTD declarations and external entities"
  if events.any (fun event =>
      event.startsWith "SAX.error:" || event.startsWith "SAX.fatalError:") then
    throw "SVG validation received an XML parser error"
  unless events.contains "SAX.startDocument()" && events.contains "SAX.endDocument()" do
    throw "SVG validation received no complete XML parse"
  return has "internalSubset" || has "externalSubset"

/-- Do not enable entity substitution, external-DTD loading, XInclude or
recovery. Both validation passes read the same captured file. Namespace
aliases and character references reach XPath through libxml. An inert
doctype is removed only from this temporary input, so the converter never
receives it; the authored browser source stays byte-identical. -/
private def checkSvgFile (runTool : IO.Process.SpawnArgs → IO IO.Process.Output)
    (input : System.FilePath) : ExceptT PicCache.Outcome IO Unit := do
  let sax ← runChecked runTool "xmllint" (saxArgs input)
  let events := (sax.splitOn "\n").map (·.trimAscii.toString)
  unless events.contains "SAX.startDocument()" && events.contains "SAX.endDocument()" do
    throw <| .inconclusive "SVG validation received no complete XML parse"
  -- premise: Tests.svgDoctypeChecks — identification events supply no declarations.
  let hasDtd ← match svgSaxBoundary sax with
    | .error err => throw <| .refused err
    | .ok hasDtd => pure hasDtd
  let result ← runChecked runTool "xmllint" (xpathArgs input)
  if result.trimAscii.toString == "false" then
    throw <| .refused "SVG resource boundary requires fragment-only references and plain CSS; color attributes permit numeric rgb()/rgba(), and paint servers must be exactly url(#id) without fallback syntax; DTD declarations, scripts, foreign objects, base URIs, other CSS functions/escapes/at-rules and animated resource/style assignments are unsupported"
  unless result.trimAscii.toString == "true" do
    throw <| .inconclusive "SVG validation received no Boolean result"
  if hasDtd then
    let stripped ← runChecked runTool "xmllint" (dropDtdArgs input)
    if stripped.trimAscii.isEmpty then throw <| .inconclusive "SVG validation produced no XML"
    IO.FS.writeFile input stripped

/-- Only the converter-owned root changes. The native PDF form stretches
the selected page onto the first frame's canvas; SVG's default `meet`
would instead letterbox its ink inside the same image box. -/
private def finishSvg (tool : String) (stretch : Bool) (bytes : ByteArray) :
    Except String ByteArray := do
  let some text := String.fromUTF8? bytes
    | throw s!"{tool} produced non-UTF-8 SVG"
  let [head, body] := text.splitOn "<svg "
    | throw s!"{tool} produced an unexpected SVG root"
  let prolog := head.trimAscii.toString
  unless prolog.isEmpty || prolog == "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" do
    throw s!"{tool} produced an unexpected SVG prolog"
  let [_, tail] := body.splitOn "</svg>"
    | throw s!"{tool} produced no complete SVG"
  unless tail.trimAscii.isEmpty do throw s!"{tool} produced trailing SVG content"
  unless stretch do return bytes
  let header := (body.splitOn ">").headD ""
  unless header != body && (header.splitOn "preserveAspectRatio").length == 1 do
    throw s!"{tool} produced unexpected SVG root attributes"
  return (head ++ pdfSvgRoot ++ body).toUTF8

/-- Convert one captured input. A failed spawn, nonzero exit or absent
output is an error, including when a failed process left an output file.
SVG inputs pass the support boundary before librsvg sees them. -/
private def convertResult (op : Op) (bytes : ByteArray)
    (runner : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO ConvCache.Result := do
  let spec := op.spec
  let eligible := runner.isNone && (spec.inputExt != "pdf" ||
    (PdfCensus.census bytes).toOption.any (·.fontsEmbedded))
  let runTool := runner.getD RunBounded.output
  ConvCache.cachedResult bytes spec.recipe spec.tools eligible do
    let independent ← IO.mkRef true
    let result ← try IO.FS.withTempDir fun dir => do
        let attempt : ExceptT PicCache.Outcome IO ByteArray := do
          let input := dir / ("source." ++ spec.inputExt)
          let output := dir / ("face." ++ spec.outputExt)
          IO.FS.writeBinFile input bytes
          if spec.inputExt == "svg" then
            checkSvgFile runTool input
            if runner.isNone then
              let fontCheck : Except PicCache.Outcome String ←
                liftM (m := IO) (runChecked runTool "xmllint" (fontArgs input)).run
              independent.set (fontCheck.toOption.any (·.trimAscii.toString == "true"))
          if spec.terminal then
            let style := dir / "terminal.xsl"
            IO.FS.writeFile style SvgPoster.stylesheet
            let projected ← runChecked runTool "xsltproc" (terminalArgs style input)
            if projected.trimAscii.isEmpty then throw <| .inconclusive "SVG projection produced no XML"
            IO.FS.writeFile input projected
          discard <| runChecked runTool spec.tool (spec.args input output)
          let result ← IO.FS.readBinFile output
          if result.isEmpty then throw <| .inconclusive s!"{spec.tool} produced an empty image"
          if spec.outputExt == "pdf" then
            if let .error why := Image.probePdf result then throw <| .inconclusive why
          if spec.outputExt == "svg" then
            match finishSvg spec.tool spec.stretch result with
            | .ok svg => return svg
            | .error why => throw <| .inconclusive why
          return result
        let got ← try attempt.run catch e => pure (.error (.inconclusive e.toString))
        let normalize := fun why : String => why.replace dir.toString "<conversion>"
        return match got with
          | .ok data => { outcome := .drawn, bytes := data : ConvCache.Result }
          | .error (.refused why) => { outcome := .refused (normalize why) }
          | .error (.inconclusive why) => { outcome := .inconclusive (normalize why) }
          | .error .drawn => { outcome := .inconclusive "conversion produced no answer" }
      catch e => pure { outcome := .inconclusive e.toString }
    return (result, ← independent.get)

private def convert (op : Op) (bytes : ByteArray)
    (runner : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO (Except String ByteArray) :=
  ConvCache.Result.answer <$> convertResult op bytes runner

/-- Validate captured SVG bytes before accepting a browser companion. An
error lets the caller fall back to converting its selected PDF page.
Success includes a usable static PDF plan; retain the original bytes for
the browser, preserving animation and source identity. Requires the
installed xmllint and librsvg tools; either failing is an error value. -/
public def validateSvg (bytes : ByteArray) (params : Image.PlanParams := .default) :
    IO (Except String Image.Plan) := do
  let pdf ← convert (.svgPdf false) bytes
  return pdf >>= fun b => Image.probe b >>= Image.plan params

/-- `validateSvg`'s judgement with the converter's outcome kept: a check
that never finished stays `inconclusive`, apart from the boundary's own
refusal, so a caller can omit what this machine could not check. -/
public def validateSvgResult (bytes : ByteArray) (params : Image.PlanParams := .default) :
    IO PicCache.Outcome := do
  let r ← convertResult (.svgPdf false) bytes
  if let .inconclusive _ := r.outcome then return r.outcome
  return match r.answer >>= fun b => Image.probe b >>= Image.plan params with
    | .ok _ => .drawn
    | .error why => .refused why

/-- First reads the authored base drawing; last projects the final declared
values of one synchronized animation cycle. Later numbered frames need a sequence. -/
public def svgPosterAtEnd : PdfRead.PageSelection → Except String Bool
  | .first | .number 1 => .ok false
  | .last => .ok true
  | .number _ => .error "a numbered SVG poster requires a PDF frame sequence"

/-- `svgPlan`, with whether a fact about the machine stopped it: a
conversion that never reached an answer — a tool missing, killed or out of
time — says nothing about the bytes. -/
public def svgPlanResult (params : Image.PlanParams) (bytes : ByteArray)
    (page : PdfRead.PageSelection := .first)
    (runTool : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO (Except String Image.Plan × Bool) := do
  match svgPosterAtEnd page with
  | .error err => return (.error err, false)
  | .ok terminal =>
    let r ← convertResult (.svgPdf terminal) bytes runTool
    let unfinished := match r.outcome with
      | .inconclusive _ => true
      | .drawn | .refused _ => false
    return (r.answer >>= fun b => Image.probe b >>= Image.plan params, unfinished)

/-- librsvg's vector reading of a self-contained SVG, optionally after a
terminal-value projection. The caller retains the captured SVG unchanged
for the browser. Unsupported timelines fail rather than paint the base. -/
public def svgPlan (params : Image.PlanParams) (bytes : ByteArray)
    (page : PdfRead.PageSelection := .first)
    (runTool : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO (Except String Image.Plan) :=
  Prod.fst <$> svgPlanResult params bytes page runTool

/-- Cairo's static SVG face for print and reduced motion. Use `pdfSvg` on
the selected page instead when a companion PDF supplies a chosen frame. -/
public def svgPoster (bytes : ByteArray) (page : PdfRead.PageSelection := .first) :
    IO (Except String ByteArray) := do
  match svgPosterAtEnd page with
  | .error err => return .error err
  | .ok terminal => convert (.svgPoster terminal) bytes

/-- Poppler reads the physical page selected by the same page-tree
traversal as the native importer, including `last`; `/Count` is never a
substitute for that traversal. -/
public def pdfSvg (bytes : ByteArray) (page : PdfRead.PageSelection) :
    IO (Except String ByteArray) := do
  match PdfRead.pageNumber bytes page with
  | .error e => return .error e
  | .ok n => convert (.pdfPage n) bytes

public def picFace (bytes : ByteArray) : IO (Except String ByteArray) :=
  convert .picFace bytes

end LeanTex.Cli.ImageAssets
