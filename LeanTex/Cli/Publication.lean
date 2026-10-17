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

/-! Capture the resources a checked HTML page owns, and publish accepted artifacts. -/

namespace LeanTex.Cli.Publication

open LeanTex.Core

/-- Where a declared HTML resource `name` is read for a document at `file`: beside it
unless absolute, none for a name that is no local file. -/
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

/-- The math renderer a run names, captured as the script text the page carries inline: a
local regular file of UTF-8 text holding no `</script`, `<!--` or NUL. -/
private def captureMathBoundary (name : String) : IO (Except String String) := do
  let shown := HtmlResource.referenceLabel name
  let label := "the math renderer " ++ shown
  if name.isEmpty || name.startsWith "//" || name.contains ':' then
    return .error (label ++ " names no local file; the page carries its script inline")
  let .ok bytes ← Host.runIO (World.ask (.readFile name)) | return .error (label ++ " could not be read")
  let some text := String.fromUTF8? bytes | return .error (label ++ " is not UTF-8")
  let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
  if Html.holdsTerm text "</script" || Html.holdsTerm text "<!--" then
    return .error (label ++ " holds '</script' or '<!--', which would end its inline script \
early or keep it from ending")
  if text.contains '\u0000' then return .error (label ++ " holds a NUL, which no page carries")
  if text.trimAscii.isEmpty then return .error (label ++ " holds no script")
  return .ok text

/-- Capture declared local resources once: the document's stylesheet and icon, and the
math renderer the run names, the page's only renderer. -/
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

/-- One serialization of a checked tree, the bytes measured and published. -/
public structure HtmlArtifact where
  render : String
  /-- The math renderer the page may carry, the one other script element its type
  admits. -/
  renderer : Option String
  render_exact : ∃ page : HtmlDoc.ClosedPage renderer, render = page.render

public def HtmlArtifact.ofPage {r : Option String} (page : HtmlDoc.ClosedPage r) : HtmlArtifact :=
  { render := page.render, renderer := r, render_exact := ⟨page, rfl⟩ }

/-- Every SVG resource of a page attested by the native judge (`Svg.judge`), or the first
refusal; bytes already judged in `checked` are not judged again. -/
public def attestSvg (resources : Array HtmlResource.Embedded) (checked : Array ByteArray := #[]) :
    Except String (Array ByteArray) := do
  let mut svgChecked : Array ByteArray := checked
  for resource in resources do
    if resource.media == .svg && !svgChecked.contains resource.bytes then
      match Svg.judge resource.bytes with
      | .ok _ => svgChecked := svgChecked.push resource.bytes
      | .error r => throw ("an embedded SVG failed resource validation: " ++ r.message)
  return svgChecked

/-- Capture local head resources, attest SVG bytes (`attestSvg`), and check the tree
publication will render; nothing is fetched, run or written. -/
public def prepareHtml (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc)
    (checked : Array ByteArray := #[]) (mathBoundary : Option String := none) :
    IO (Except String HtmlArtifact × Array Diag) := do
  let cfg ← match ← captureHtmlResources file cfg doc mathBoundary with
    | .ok cfg => pure cfg
    | .error why => return (.error why, #[])
  -- premise: nativeFaceClosedChecks — engine-drawn faces skip the judge
  -- premise: htmlContainedSvgColorChecks — a figure's bytes the judge accepted skip it alike
  let svgChecked ← match attestSvg (HtmlDoc.resources cfg) checked with
    | .ok checked => pure checked
    | .error why => return (.error why, #[])
  let (page, diags) := HtmlDoc.emitClosed cfg doc svgChecked
  return (page.map HtmlArtifact.ofPage, diags)

/-- The only artifact write site, after acceptance: each artifact written with its
directory made, an unwritable one E0004 under its path, the others still written. -/
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
