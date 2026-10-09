module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Cli.PicCache
import LeanTex.Core.HtmlResource
import LeanTex.Core.Image
import LeanTex.Cli.DriverDiag
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

/-- What publication does with one captured SVG resource. -/
public inductive Verdict where
  | keep
  | refuse
  | omit
  deriving BEq, Repr, DecidableEq

/-- The validator's outcome, read as the page's decision. A drawn check
keeps the resource. The support boundary's own refusal refuses the page:
the bytes cannot be published as checked. A check that never reached an
answer — the tool absent, killed, or unable to start — omits the resource:
a fact about the machine degrades the page and never refuses it. -/
public def svgVerdict : PicCache.Outcome → Verdict
  | .drawn => .keep
  | .refused _ => .refuse
  | .inconclusive _ => .omit

/-- **Only the validator's own refusal refuses a page** (`_exact`). The
defect read a validator that could not start as one that said no: on a
machine without xmllint, a page whose icon is an SVG published nothing. -/
public theorem svgVerdict_refuse_exact (o : PicCache.Outcome) :
    svgVerdict o = .refuse ↔ ∃ w, o = .refused w := by
  cases o <;> simp [svgVerdict]

private def said : PicCache.Outcome → String
  | .drawn => ""
  | .refused w | .inconclusive w => w

/-- Why validation omitted these bytes, when it did. -/
public def omittedWhy (omitted : Array (ByteArray × String)) (r : HtmlResource.Embedded) :
    Option String :=
  if r.media == .svg then (omitted.find? (·.1 == r.bytes)).map (·.2) else none

/-- Why validation omitted one of this image's SVG faces — the page face,
then the print poster — when it did. -/
public def omittedFace (omitted : Array (ByteArray × String)) (en : Image.Loaded) :
    Option String :=
  (HtmlDoc.imageResource? en).bind (omittedWhy omitted) <|>
    (HtmlDoc.imagePosterResource? en).bind (omittedWhy omitted)

private def omitEntry (omitted : Array (ByteArray × String)) (en : Image.Loaded) :
    Image.Loaded × Option Diag :=
  match omittedFace omitted en with
  | some why => ({ en with webError := some why },
      if en.src.startsWith Ir.picSrcPrefix then some (DriverDiag.boundarySvgMissing en.src why)
      else none)
  | none => (en, none)

/-- The page without the SVG resources validation omitted. An image whose
face is omitted takes the failed-face arm, a placeholder that keeps its box
and text alternative, which the page names (W0605); a boundary picture's is
named here, as its failed conversion is (W0378). An omitted icon leaves the
head, named by its path (W0605). -/
public def omitFaces (omitted : Array (ByteArray × String)) (cfg : HtmlDoc.Config)
    (doc : Ir.Doc) : HtmlDoc.Config × Ir.Doc × Array Diag :=
  let marked := cfg.imgs.entries.map (omitEntry omitted)
  let faced := { cfg with imgs := { entries := marked.map (·.1) } }
  let named := marked.filterMap (·.2)
  -- premise: machineLossChecks — the omitted icon is named once, here, and leaves the head
  match cfg.favicon.bind fun (name, icon) => (omittedWhy omitted icon).map (name, ·) with
  | some (name, why) =>
    ({ faced with favicon := none }, { doc with info := { doc.info with favicon := none } },
      named.push (DriverDiag.pageIconOmitted name why))
  | none => (faced, doc, named)

/-- **Nothing omitted, nothing changed** (`_id`). -/
public theorem omitFaces_id (cfg : HtmlDoc.Config) (doc : Ir.Doc) :
    omitFaces #[] cfg doc = (cfg, doc, #[]) := by
  have hwhy : ∀ r, omittedWhy #[] r = none := fun r => by
    unfold omittedWhy
    split <;> rfl
  have hface : ∀ en, omittedFace #[] en = none := fun en => by
    simp [omittedFace, hwhy]
  have hentry : omitEntry #[] = fun en => (en, none) := funext fun en => by
    simp [omitEntry, hface]
  rcases cfg with ⟨⟩
  simp only [omitFaces, hentry]
  rw [Array.filterMap_map]
  simp [hwhy, Array.map_map, Function.comp_def]

/-- **An omitted picture face is named under its picture** (`_named`): the
entry keeps its native plan and takes the reason as its failed face, and a
boundary picture's W0378 carries its image source as the subject. -/
public theorem omitFaces_named (omitted : Array (ByteArray × String)) (cfg : HtmlDoc.Config)
    (doc : Ir.Doc) (k : Nat) (en : Image.Loaded) (why : String)
    (h : cfg.imgs.get? k = some en) (hwhy : omittedFace omitted en = some why) :
    (omitFaces omitted cfg doc).1.imgs.get? k = some { en with webError := some why } ∧
      (en.src.startsWith Ir.picSrcPrefix = true →
        ∃ d ∈ (omitFaces omitted cfg doc).2.2, d.kind = .W0378 ∧ d.subject = some en.src) := by
  have hentry : omitEntry omitted en = ({ en with webError := some why },
      if en.src.startsWith Ir.picSrcPrefix then
        some (DriverDiag.boundarySvgMissing en.src why) else none) := by
    simp [omitEntry, hwhy]
  simp only [Image.Store.get?] at h
  have hmem : omitEntry omitted en ∈ cfg.imgs.entries.map (omitEntry omitted) :=
    Array.mem_map.mpr ⟨en, Array.mem_of_getElem? h, rfl⟩
  constructor
  · unfold omitFaces
    split <;> simp [Image.Store.get?, Array.getElem?_map, h, hentry]
  · intro hsrc
    have hnamed : DriverDiag.boundarySvgMissing en.src why ∈
        (cfg.imgs.entries.map (omitEntry omitted)).filterMap (·.2) :=
      Array.mem_filterMap.mpr ⟨_, hmem, by simp [hentry, hsrc]⟩
    refine ⟨DriverDiag.boundarySvgMissing en.src why, ?_,
      DriverDiag.boundarySvgMissing_subject en.src why⟩
    unfold omitFaces
    split
    · exact Array.mem_push_of_mem _ hnamed
    · exact hnamed

/-- **An image with no omitted face is unchanged** (`_exact`). -/
public theorem omitFaces_kept_exact (omitted : Array (ByteArray × String))
    (cfg : HtmlDoc.Config) (doc : Ir.Doc) (k : Nat) (en : Image.Loaded)
    (h : cfg.imgs.get? k = some en) (hkept : omittedFace omitted en = none) :
    (omitFaces omitted cfg doc).1.imgs.get? k = some en := by
  have hentry : omitEntry omitted en = (en, none) := by simp [omitEntry, hkept]
  simp only [Image.Store.get?] at h
  unfold omitFaces
  split <;> simp [Image.Store.get?, Array.getElem?_map, h, hentry]

/-- **An icon never leaves the head unnamed** (`_named`). -/
public theorem omitFaces_icon_named (omitted : Array (ByteArray × String))
    (cfg : HtmlDoc.Config) (doc : Ir.Doc) (name : String) (icon : HtmlResource.Embedded)
    (h : cfg.favicon = some (name, icon)) (hgone : (omitFaces omitted cfg doc).1.favicon = none) :
    (omitFaces omitted cfg doc).2.1.info.favicon = none ∧
      ∃ d ∈ (omitFaces omitted cfg doc).2.2, d.kind = .W0605 ∧ d.subject = some name := by
  unfold omitFaces at hgone ⊢
  simp only [h, Option.bind_some] at hgone ⊢
  cases hw : omittedWhy omitted icon with
  | none => simp [hw] at hgone
  | some why =>
    simp only [Option.map_some]
    exact ⟨trivial, _, Array.mem_push_self, DriverDiag.pageIconOmitted_subject name why⟩

/-- Capture local head resources, attest exact SVG bytes through the existing
parsed-XML/converter boundary, then check the tree that publication will render.
Each SVG's verdict is `svgVerdict`'s: only the boundary's refusal refuses the
page, and a check that never finished omits the resource (`omitFaces`).
No URL is fetched and no output directory exists at this point. -/
public def prepareHtml (file : String) (cfg : HtmlDoc.Config) (doc : Ir.Doc) :
    IO (Except String HtmlArtifact × Array Diag) := do
  let cfg ← match ← captureHtmlResources file cfg doc with
    | .ok cfg => pure cfg
    | .error why => return (.error why, #[])
  let mut svgChecked : Array ByteArray := #[]
  let mut omitted : Array (ByteArray × String) := #[]
  for resource in HtmlDoc.resources cfg do
    if resource.media == .svg && !svgChecked.contains resource.bytes &&
        !omitted.any (·.1 == resource.bytes) then
      let outcome ← ImageAssets.validateSvgResult resource.bytes
      match svgVerdict outcome with
      | .keep => svgChecked := svgChecked.push resource.bytes
      | .refuse =>
        return (.error ("an embedded SVG failed resource validation: " ++ said outcome), #[])
      | .omit => omitted := omitted.push (resource.bytes, said outcome)
  let (cfg, doc, omitDiags) := omitFaces omitted cfg doc
  let (page, diags) := HtmlDoc.emitClosed cfg doc svgChecked
  return (page.map HtmlArtifact.ofPage, omitDiags ++ diags)

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
