module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.HtmlResource
import LeanTex.Core.Image
import LeanTex.Core.SvgJudge
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.Host
import LeanTex.Cli.World

/-! Capture the resources a checked HTML page owns and publish accepted artifacts.
The executable and its tests share this boundary without sharing an entry point. -/

namespace LeanTex.Cli.Publication

open LeanTex.Core

/-- Where a declared HTML resource named `name` is read, for a document at
`file`: beside the document unless absolute; none for a name that is no
local file. -/
public def localPath? (file name : String) : Option System.FilePath :=
  if name.isEmpty || name.startsWith "//" || name.contains ':' then none
  else
    let path := System.FilePath.mk name
    some (if path.isAbsolute then path else (System.FilePath.mk file).parent.getD "." / path)

private def htmlLocalBytes (file name : String) : IO (Except String ByteArray) := do
  let some path := localPath? file name
    | return .error "a declared HTML resource must name a local file"
  try return .ok (← IO.FS.readBinFile path)
  catch _ => return .error "a declared HTML resource could not be read"

/-- The math renderer a run names (`--math-boundary <file>`), captured as the
script text the page carries inline (`HtmlDoc.mathBoundaryNodes`): a local
regular file, read through the host's one door as a command-line path is,
from the run's directory, whose bytes are UTF-8 text the HTML parser reads
to the script's own end — no `</script` and no `<!--`, in any case, and no
NUL — which the closure gate refuses as well, never escapes. -/
private def captureMathBoundary (name : String) : IO (Except String String) := do
  let shown := HtmlResource.referenceLabel name
  let label := "the math renderer " ++ shown
  if name.isEmpty || name.startsWith "//" || name.contains ':' then
    return .error (label ++ " names no local file; the page carries its script inline")
  let .ok bytes ← Host.runIO (World.ask (.readFile name)) | return .error (label ++ " could not be read")
  let some text := String.fromUTF8? bytes | return .error (label ++ " is not UTF-8")
  let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
  let lower := text.toLower
  if (lower.splitOn "</script").length > 1 || (lower.splitOn "<!--").length > 1 then
    return .error (label ++ " holds '</script' or '<!--', which would end its inline script \
early or keep it from ending")
  if text.contains '\u0000' then return .error (label ++ " holds a NUL, which no page carries")
  if text.trimAscii.isEmpty then return .error (label ++ " holds no script")
  return .ok text

/-- Capture declared local resources once — the document's stylesheet and
icon, and the math renderer the run names, the page's only renderer: one a
caller set in `cfg` is dropped, never shipped past the capture's checks.
The hermetic browser freshness key uses this same snapshot; XML validation
remains the publication boundary's job. -/
public def captureHtmlResources (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc)
    (mathBoundary : Option String := none) :
    IO (Except String HtmlDoc.Config) := do
  let mut cfg := { cfg with mathRenderer := none }
  if let some name := mathBoundary then
    match ← captureMathBoundary name with
    | .ok text => cfg := { cfg with mathRenderer := some text }
    | .error why => return .error why
  if let some name := doc.output.stylesheet then
    let .ok bytes ← htmlLocalBytes file name | return .error (
      "the declared stylesheet " ++ HtmlResource.referenceLabel name ++
        " could not be captured from a local file")
    let some css := String.fromUTF8? bytes | return .error (
      "the declared stylesheet " ++ HtmlResource.referenceLabel name ++ " is not UTF-8")
    let css := if css.startsWith "\uFEFF" then (css.drop 1).toString else css
    cfg := { cfg with stylesheet := some (name, css) }
  if let some name := doc.info.favicon then
    let .ok bytes ← htmlLocalBytes file name | return .error (
      "the declared favicon " ++ HtmlResource.referenceLabel name ++
        " could not be captured from a local file")
    let media := if Image.isSvg name then HtmlResource.Media.svg
      else if ({ media := .png, bytes } : HtmlResource.Embedded).ready #[] then .png
      else if ({ media := .ico, bytes } : HtmlResource.Embedded).ready #[] then .ico
      else .jpeg
    cfg := { cfg with favicon := some (name, { media, bytes }) }
  return .ok cfg

/-- The bytes measured and published are one serialization of the checked
tree. The erased witness retains resource closure without retaining the tree
or its captured resource buffers at runtime; the renderer's text, which the
witness's type names, is kept. -/
public structure HtmlArtifact where
  render : String
  /-- The math renderer the page may carry, beside the deck's constant: the
  one other script element its type admits. -/
  renderer : Option String
  render_exact : ∃ page : HtmlDoc.ClosedPage renderer, render = page.render

public def HtmlArtifact.ofPage {r : Option String} (page : HtmlDoc.ClosedPage r) : HtmlArtifact :=
  { render := page.render, renderer := r, render_exact := ⟨page, rfl⟩ }

/-- Every SVG resource of a page attested by the native judge's resource
boundary (`Svg.judge`), or the first refusal: the bytes are what the page
embeds, so the judge reads exactly what a browser would, and no tool runs,
so every check finishes. Bytes already judged (`checked`) are not judged
again. -/
public def attestSvg (resources : Array HtmlResource.Embedded) (checked : Array ByteArray := #[]) :
    Except String (Array ByteArray) := do
  let mut svgChecked : Array ByteArray := checked
  for resource in resources do
    if resource.media == .svg && !svgChecked.contains resource.bytes then
      match Svg.judge resource.bytes with
      | .ok _ => svgChecked := svgChecked.push resource.bytes
      | .error r => throw ("an embedded SVG failed resource validation: " ++ r.message)
  return svgChecked

/-- Capture local head resources, attest exact SVG bytes through the native
resource boundary (`attestSvg`), then check the tree that publication will
render. No URL is fetched, no tool runs and no output directory exists at
this point. -/
public def prepareHtml (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc)
    (checked : Array ByteArray := #[]) (mathBoundary : Option String := none) :
    IO (Except String HtmlArtifact × Array Diag) := do
  let cfg ← match ← captureHtmlResources file cfg doc mathBoundary with
    | .ok cfg => pure cfg
    | .error why => return (.error why, #[])
  -- premise: nativeFaceClosedChecks — a face the engine drew itself
  -- (`PdfFaces.svgOf`) names only its own fragments and `data:` rasters, and
  -- a converted face the face decision kept passed this very judge there
  -- (`PdfFaces.answerOf`): neither is judged again.
  let svgChecked ← match attestSvg (HtmlDoc.resources cfg) checked with
    | .ok checked => pure checked
    | .error why => return (.error why, #[])
  let (page, diags) := HtmlDoc.emitClosed cfg doc svgChecked
  return (page.map HtmlArtifact.ofPage, diags)

/-- The only artifact write site, after acceptance. An HTML publication
requires a checked tree and writes its own serialization, with no sidecars
or rereads of resources captured before the gate. Each artifact's directory
is made as it is written, and an artifact that cannot be written is E0004
under its path, the others written: what was written, and the losses. -/
public def publish (outDir : Option String) (html : Option (String × HtmlArtifact))
    (md : Option (String × String)) (pdf : Option (String × ByteArray)) :
    IO (Array String × Array Diag) := do
  let mut written : Array String := #[]
  let mut lost : Array Diag := #[]
  if let some o := outDir then
    discard <| (IO.FS.createDirAll o).toBaseIO
  let artifacts := (html.map fun (path, page) => (path, page.render.toUTF8)).toArray ++
    (md.map fun (path, text) => (path, text.toUTF8)).toArray ++ pdf.toArray
  for (path, bytes) in artifacts do
    let write : IO Unit := do
      IO.FS.createDirAll ((System.FilePath.mk path).parent.getD ".")
      IO.FS.writeBinFile path bytes
    match ← write.toBaseIO with
    | .ok () => written := written.push path
    | .error e => lost := lost.push (DriverDiag.outputUnwritable path (Host.describe e))
  return (written, lost)

end LeanTex.Cli.Publication
