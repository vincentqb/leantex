import LeanTex.Core.HtmlDoc
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

def prepare (en : Image.Loaded) : IO Image.Loaded := do
  let p := plan en
  let some conversion := p.conversion? | return en
  let bytes ← match conversion with
    | .svgPoster page =>
      match en.source.or en.webSvg with
      | some svg => ImageAssets.svgPoster svg page
      | none => pure (.error "the SVG source has no captured bytes")
    | .pdfPage page =>
      match en.source with
      | some pdf => ImageAssets.pdfSvg pdf page
      | none => pure (.error "the PDF source has no captured bytes")
  let companionOk ← match p, bytes, en.companion with
    | .animatedWithCompanion _, .ok _, some svg =>
      Except.isOk <$> ImageAssets.validateSvg svg
    | _, _, _ => pure false
  return apply en p { bytes, companionOk }

end LeanTex.Cli.BrowserFaces
