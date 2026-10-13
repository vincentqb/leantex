module

public import LeanTex.Core.Image
public import LeanTex.Cli.PicCache
public import LeanTex.Core.PdfRead
import LeanTex.Core.PdfCensus
import LeanTex.Core.Xml
import LeanTex.Core.SvgJudge
import LeanTex.Core.SvgPoster
import LeanTex.Cli.ConvCache
import LeanTex.Cli.Host
import LeanTex.Cli.RunBounded

/-! Vector image IO. Captured SVG bytes remain the browser source. Fresh
conversions return bytes; only the driver decides when to publish them. -/

namespace LeanTex.Cli.ImageAssets

open LeanTex.Core

private def rsvgArgs (format : String) (input output : System.FilePath) : Array String :=
  #["--format=" ++ format, "--output", output.toString, input.toString]

private def pdfSvgArgs (page : String) (input output : System.FilePath) : Array String :=
  #["-svg", "-f", page, "-l", page, input.toString, output.toString]

private def pdfSvgRoot : String := "<svg preserveAspectRatio=\"none\" "

private def commandText (tool : String) (args : Array String) : String :=
  tool ++ " " ++ String.intercalate " " args.toList

/-- What a host tool is asked for. An SVG input is always the canonical
spelling of a parse the native judge accepted (`Xml.renderItem`): no second
XML reader, no stylesheet, no authored byte. -/
private inductive Op where
  | pdfPage (page : Nat)
  | picFace
  /-- librsvg's PDF of a figure the engine does not draw whole. -/
  | canonicalPdf
  /-- librsvg's SVG of the pose of such a figure: the still face of one
  that moves. -/
  | canonicalSvg

private structure Spec where
  tool : String
  inputExt : String
  outputExt : String
  args : System.FilePath → System.FilePath → Array String
  stretch : Bool := false

private def Op.spec : Op → Spec
  | .pdfPage n => ⟨"pdftocairo", "pdf", "svg", pdfSvgArgs (toString n), true⟩
  | .picFace => ⟨"pdftocairo", "pdf", "svg",
      fun input output => #["-svg", input.toString, output.toString], false⟩
  | .canonicalPdf => ⟨"rsvg-convert", "svg", "pdf", rsvgArgs "pdf", false⟩
  | .canonicalSvg => ⟨"rsvg-convert", "svg", "svg", rsvgArgs "svg", false⟩

private def Spec.tools (s : Spec) : Array String := #[s.tool]

private def Spec.recipe (s : Spec) : String :=
  let input := System.FilePath.mk "<input>"
  let output := System.FilePath.mk "<output>"
  String.intercalate "\n"
    [commandText s.tool (s.args input output), if s.stretch then pdfSvgRoot else ""]

/-- The normalized host-tool recipe behind browser vector faces. The
hermetic source key hashes this value, while the browser oracle separately
records the exact output bytes. Every invocation below reads these same
argument builders, so a recipe change invalidates the committed report. -/
public def browserFaceContract : String :=
  String.intercalate "\n" <| ([.canonicalSvg, .pdfPage 1, .picFace] : List Op).map (·.spec.recipe)

/-- The recipe of the conversion the native SVG path asks for the PDF:
librsvg's PDF of the canonical spelling, for a figure whose import named a
loss. -/
public def canonicalPdfRecipe : String := Op.canonicalPdf.spec.recipe

private def toolRecovery (tool : String) : String :=
  let formula := match tool with
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
    -- premise: none — pdftocairo (0–4, 99) documents its exits, none at or above 126,
    -- and rsvg-convert documents none and exits 1 or 2
    throw <| if ran.exitCode >= 126 || (stderr.isEmpty && ran.stdout.trimAscii.isEmpty)
      then .inconclusive detail else .refused detail
  return ran.stdout

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
An SVG input is the canonical spelling of a judged parse, and whether its
drawing reads host fonts is the native reader's answer (`fontIndependent`,
from `Svg.fontDependent`): no second reader runs. -/
private def convertResult (op : Op) (bytes : ByteArray)
    (runner : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none)
    (fontIndependent : Bool := true) :
    IO ConvCache.Result := do
  let spec := op.spec
  let eligible := runner.isNone && (spec.inputExt != "pdf" ||
    (PdfCensus.census bytes).toOption.any (·.fontsEmbedded))
  let runTool := runner.getD RunBounded.output
  ConvCache.cachedResult bytes spec.recipe spec.tools eligible do
    let result ← try Host.withScratch fun dir => do
        let attempt : ExceptT PicCache.Outcome IO ByteArray := do
          let input := dir / ("source." ++ spec.inputExt)
          let output := dir / ("face." ++ spec.outputExt)
          IO.FS.writeBinFile input bytes
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
    return (result, spec.inputExt != "svg" || fontIndependent)

private def convert (op : Op) (bytes : ByteArray)
    (runner : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none)
    (fontIndependent : Bool := true) :
    IO (Except String ByteArray) :=
  ConvCache.Result.answer <$> convertResult op bytes runner fontIndependent

/-- **A browser face's check**: the native resource boundary over the bytes
(`Svg.judge`) — no tool reads them, so the check always finishes. A face the
boundary accepts is drawn; one it refuses keeps the boundary's own words. -/
public def validateSvgResult (bytes : ByteArray) : IO PicCache.Outcome :=
  return match Svg.judge bytes with
    | .ok _ => .drawn
    | .error r => .refused r.message

/-- First reads the authored base drawing; last projects the final declared
values of one synchronized animation cycle. Later numbered frames need a sequence. -/
public def svgPosterAtEnd : PdfRead.PageSelection → Except String Bool
  | .first | .number 1 => .ok false
  | .last => .ok true
  | .number _ => .error "a numbered SVG poster requires a PDF frame sequence"

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

/-- **librsvg's drawing of a figure the engine does not draw whole**: the
canonical spelling of the native parse (`Xml.render`, which no DTD, no
comment and no authored byte survives), converted to PDF and read as a
form. The authored bytes never reach the converter. `fontIndependent` is
the native reader's answer to whether the drawing reads host fonts
(`Svg.fontDependent`): a font-dependent answer is never cached. -/
public def canonicalPlan (params : Image.PlanParams) (canonical : ByteArray) (fontIndependent : Bool)
    (runTool : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO (Except String Image.Plan) := do
  let pdf ← convert .canonicalPdf canonical runTool fontIndependent
  return pdf >>= fun b => Image.probe b >>= Image.plan params

/-- **librsvg's still face of a moving figure the engine does not draw
whole**: the pose the page selection asks for (`SvgPoster.pose`), its
canonical spelling converted to SVG — the face print and reduced motion
show. The authored bytes never reach the converter. -/
public def canonicalPoster (bytes : ByteArray) (page : PdfRead.PageSelection := .first)
    (runTool : Option (IO.Process.SpawnArgs → IO IO.Process.Output) := none) :
    IO (Except String ByteArray) := do
  let atEnd ← match svgPosterAtEnd page with
    | .ok t => pure t
    | .error e => return .error e
  match SvgPoster.pose bytes atEnd with
  | .error why => return .error why
  | .ok pose => convert .canonicalSvg (Xml.renderItem pose) runTool (!Svg.fontDependent pose)

end LeanTex.Cli.ImageAssets
