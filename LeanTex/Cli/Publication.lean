module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
import LeanTex.Core.HtmlResource
import LeanTex.Core.Image
import LeanTex.Cli.ImageAssets

/-! Capture the resources a checked HTML page owns and publish accepted artifacts.
The executable and its tests share this boundary without sharing an entry point. -/

namespace LeanTex.Cli.Publication

open LeanTex.Core

private def htmlLocalBytes (file name : String) : IO (Except String ByteArray) := do
  if name.isEmpty || name.startsWith "//" || name.contains ':' then
    return .error "a declared HTML resource must name a local file"
  let path := System.FilePath.mk name
  let path := if path.isAbsolute then path else
    (System.FilePath.mk file).parent.getD "." / path
  try return .ok (← IO.FS.readBinFile path)
  catch _ => return .error "a declared HTML resource could not be read"

/-- Capture declared local resources once. The hermetic browser freshness key
uses this same snapshot; XML validation remains the publication boundary's job. -/
public def captureHtmlResources (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc) :
    IO (Except String HtmlDoc.Config) := do
  let mut cfg := cfg
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
or its captured resource buffers at runtime. -/
public structure HtmlArtifact where
  render : String
  render_exact : ∃ page : HtmlDoc.ClosedPage, render = page.render

public def HtmlArtifact.ofPage (page : HtmlDoc.ClosedPage) : HtmlArtifact :=
  { render := page.render, render_exact := ⟨page, rfl⟩ }

/-- Capture local head resources, attest exact SVG bytes through the existing
parsed-XML/converter boundary, then check the tree that publication will render.
No URL is fetched and no output directory exists at this point. -/
public def prepareHtml (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc) :
    IO (Except String HtmlArtifact × Array Diag) := do
  let cfg ← match ← captureHtmlResources file cfg doc with
    | .ok cfg => pure cfg
    | .error why => return (.error why, #[])
  let mut svgChecked : Array ByteArray := #[]
  for resource in HtmlDoc.resources cfg do
    if resource.media == .svg && !svgChecked.contains resource.bytes then
      match ← ImageAssets.validateSvg resource.bytes with
      | .ok _ => svgChecked := svgChecked.push resource.bytes
      | .error why => return (.error ("an embedded SVG failed resource validation: " ++ why), #[])
  let (page, diags) := HtmlDoc.emitClosed cfg doc svgChecked
  return (page.map HtmlArtifact.ofPage, diags)

/-- The only artifact write site, after acceptance. An HTML publication
requires a checked tree and writes its own serialization, with no sidecars
or rereads of resources captured before the gate. -/
public def publish (outDir : Option String) (html : Option (String × HtmlArtifact))
    (md : Option (String × String)) (pdf : Option (String × ByteArray)) :
    IO (Array String) := do
  let mut written : Array String := #[]
  if let some o := outDir then
    IO.FS.createDirAll o
  if let some (path, page) := html then
    IO.FS.createDirAll ((System.FilePath.mk path).parent.getD ".")
    IO.FS.writeFile path page.render
    written := written.push path
  if let some (path, text) := md then
    IO.FS.writeFile path text
    written := written.push path
  if let some (path, bytes) := pdf then
    IO.FS.writeBinFile path bytes
    written := written.push path
  return written

end LeanTex.Cli.Publication
