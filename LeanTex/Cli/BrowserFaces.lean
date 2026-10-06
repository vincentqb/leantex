import LeanTex.Core.HtmlDoc
import LeanTex.Cli.Batch
import LeanTex.Cli.ImageAssets

namespace LeanTex.Cli.BrowserFaces

open LeanTex.Core

inductive Conversion where
  | svgPoster (page : PdfRead.PageSelection)
  | pdfPage (page : PdfRead.PageSelection)
  deriving BEq, Repr

/-- The driver's requests, before host conversion. The hermetic oracle
reads the same plan without running a converter. -/
inductive Plan where
  | keep
  | movingSvgWithPoster (conversion : Conversion)
  | convertedPrimary (conversion : Conversion)
  | animatedWithCompanion (conversion : Conversion)
  deriving BEq, Repr

def Conversion.key : Conversion → String
  | .svgPoster page => s!"svg-poster:{reprStr page}"
  | .pdfPage page => s!"pdf-page:{reprStr page}"

def Plan.key : Plan → String
  | .keep => "keep"
  | .movingSvgWithPoster op => "moving:" ++ op.key
  | .convertedPrimary op => "primary:" ++ op.key
  | .animatedWithCompanion op => "companion:" ++ op.key

def Plan.conversion? : Plan → Option Conversion
  | .keep => none
  | .movingSvgWithPoster op | .convertedPrimary op | .animatedWithCompanion op => some op

/-- Select from the captured source and native plan. A previous browser
conversion must not turn a PDF request into an SVG request on a second pass. -/
def plan (en : Image.Loaded) : Plan :=
  if en.src.startsWith Ir.picSrcPrefix then .keep else
  match en.info with
  | none => .keep
  | some info =>
    if info.form.isNone then .keep
    else if Image.isSvg (HtmlDoc.resolvedSrc en) then .movingSvgWithPoster (.svgPoster en.page)
    else if en.source.isNone then .keep
    else if en.animated && en.companion.isSome then .animatedWithCompanion (.pdfPage en.page)
    else .convertedPrimary (.pdfPage en.page)

structure Outcome where
  bytes : Except String ByteArray
  companionOk : Bool := false

def apply (en : Image.Loaded) (p : Plan) (answer : Outcome) : Image.Loaded :=
  match p with
  | .keep => en
  | .movingSvgWithPoster _ =>
    match answer.bytes with
    | .ok bytes =>
      { en with webSvg := en.source.or en.webSvg
                posterSvg := some bytes, webError := none }
    | .error why => { en with posterSvg := none, webError := some why }
  | .convertedPrimary _ | .animatedWithCompanion _ =>
    match answer.bytes with
    | .error why => { en with webSvg := none, posterSvg := none, webError := some why }
    | .ok bytes =>
      let companion := match p with
        | .animatedWithCompanion _ => if answer.companionOk then en.companion else none
        | .keep | .movingSvgWithPoster _ | .convertedPrimary _ => none
      { en with webSvg := some (companion.getD bytes)
                posterSvg := if companion.isSome then some bytes else none
                webError := none }

/-- Browser payloads preserve the native plan that the PDF backend reads. -/
theorem apply_info_exact (en : Image.Loaded) (p : Plan) (answer : Outcome) :
    (apply en p answer).info = en.info := by
  rcases answer with ⟨bytes, companionOk⟩
  cases p <;> cases bytes <;> rfl

/-- Browser payloads preserve the captured first-frame animation canvas. -/
theorem apply_canvas_exact (en : Image.Loaded) (p : Plan) (answer : Outcome) :
    (apply en p answer).canvasSize = en.canvasSize := by
  rcases answer with ⟨bytes, companionOk⟩
  cases p <;> cases bytes <;> rfl

private def Conversion.source? (en : Image.Loaded) : Conversion → Option ByteArray
  | .svgPoster _ => en.source.or en.webSvg
  | .pdfPage _ => en.source

/-- Cache slots begin with the captured source's content fingerprint.
Serialize even different recipes for that fingerprint: filenames and page
spellings are not cache identities, and no hash injectivity is assumed.
Entries without conversion bytes receive their own position key. -/
def sourceKey (source : Option ByteArray) (index : Nat) : Sum Nat String :=
  match source with
  | none => .inl index
  | some bytes => .inr (Flate.contentKey bytes)

theorem sourceKey_contract (a b : ByteArray) (i j : Nat) :
    sourceKey (some a) i = sourceKey (some b) j ↔
      Flate.contentKey a = Flate.contentKey b := by
  simp [sourceKey]

private def mapBySource (limit : Nat) (source : α → Option ByteArray)
    (f : α → IO β) (xs : Array α) : IO (Array β) := do
  -- Hash once per entry, before the partition compares resource keys.
  let keyed := xs.mapIdx fun i x => (sourceKey (source x) i, x)
  Batch.map limit Prod.fst (fun x => f x.2) keyed

private def primarySource? (en : Image.Loaded) : Option ByteArray :=
  (plan en).conversion?.bind (Conversion.source? en)

private inductive Prepared where
  | keep (entry : Image.Loaded)
  | converted (entry : Image.Loaded) (plan : Plan) (bytes : Except String ByteArray)

private def preparePrimary (en : Image.Loaded) : IO Prepared := do
  let p := plan en
  let some conversion := p.conversion? | return .keep en
  let bytes ← match conversion, conversion.source? en with
    | .svgPoster page, some svg => ImageAssets.svgPoster svg page
    | .svgPoster _, none => pure (.error "the SVG source has no captured bytes")
    | .pdfPage page, some pdf => ImageAssets.pdfSvg pdf page
    | .pdfPage _, none => pure (.error "the PDF source has no captured bytes")
  return .converted en p bytes

private def Prepared.companion? : Prepared → Option ByteArray
  | .converted en (.animatedWithCompanion _) (.ok _) => en.companion
  | _ => none

private def Prepared.finish (prepared : Prepared) : IO Image.Loaded := do
  match prepared with
  | .keep en => return en
  | .converted en p bytes =>
    let companionOk ← match prepared.companion? with
      | some svg => Except.isOk <$> ImageAssets.validateSvg svg
      | none => pure false
    return apply en p { bytes, companionOk }

def prepare (en : Image.Loaded) : IO Image.Loaded := do
  (← preparePrimary en).finish

/-- Prepare browser faces with at most `max 1 limit` concurrent requests,
returning them in source order. All primaries finish before companions:
distinct PDF sources can share a companion's validation cache slot.
Both phases use the same content keys as the conversion cache's source
prefix and the ordered, exclusive partition checked by `Batch.plan_exact`,
`Batch.plan_bounded` and `Batch.plan_keys_nodup`. Tool identity memos may
share a path across keys; ConvCache publishes those atomically too. -/
def prepareAll (entries : Array Image.Loaded) (limit : Nat := 4) :
    IO (Array Image.Loaded) := do
  let prepared ← mapBySource limit primarySource? preparePrimary entries
  mapBySource limit Prepared.companion? Prepared.finish prepared

end LeanTex.Cli.BrowserFaces
