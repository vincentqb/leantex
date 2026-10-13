module

public import LeanTex.Core.Image
public import LeanTex.Core.PdfRead
public import LeanTex.Core.Flate
import LeanTex.Core.Ir
import LeanTex.Core.HtmlDoc
import LeanTex.Core.SvgJudge
import LeanTex.Cli.Batch
import LeanTex.Cli.ImageAssets
public import LeanTex.Cli.PdfFaces

namespace LeanTex.Cli.BrowserFaces

open LeanTex.Core

public inductive Conversion where
  | svgPoster (page : PdfRead.PageSelection)
  | pdfPage (page : PdfRead.PageSelection)
  deriving BEq, Repr

/-- The driver's browser-face requests, before host conversion. -/
public inductive Plan where
  | keep
  | movingSvgWithPoster (conversion : Conversion)
  | convertedPrimary (conversion : Conversion)
  | animatedWithCompanion (conversion : Conversion)
  deriving BEq, Repr

public def Conversion.key : Conversion → String
  | .svgPoster page => s!"svg-poster:{reprStr page}"
  | .pdfPage page => s!"pdf-page:{reprStr page}"

public def Plan.key : Plan → String
  | .keep => "keep"
  | .movingSvgWithPoster op => "moving:" ++ op.key
  | .convertedPrimary op => "primary:" ++ op.key
  | .animatedWithCompanion op => "companion:" ++ op.key

public def Plan.conversion? : Plan → Option Conversion
  | .keep => none
  | .movingSvgWithPoster op | .convertedPrimary op | .animatedWithCompanion op => some op

/-- The browser-face request for an entry, read from its captured source and native plan.
-/
public def plan (en : Image.Loaded) : Plan :=
  if en.src.startsWith Ir.picSrcPrefix then .keep else
  match en.info with
  | none => .keep
  | some info =>
    if info.form.isNone then .keep
    else if Image.isSvg (HtmlDoc.resolvedSrc en) then
      if en.moving && en.vector.isNone then .movingSvgWithPoster (.svgPoster en.page) else .keep
    else if en.source.isNone then .keep
    else if en.animated && en.companion.isSome then .animatedWithCompanion (.pdfPage en.page)
    else .convertedPrimary (.pdfPage en.page)

public structure Outcome where
  bytes : Except String ByteArray
  companionOk : Bool := false
  /-- The words the drawn page says (`PdfFaces.Face.words`). -/
  words : String := ""

public def apply (en : Image.Loaded) (p : Plan) (answer : Outcome) : Image.Loaded :=
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
    | .error why => { en with webSvg := none, posterSvg := none, webWords := "", webError := some why }
    | .ok bytes =>
      let companion := match p with
        | .animatedWithCompanion _ => if answer.companionOk then en.companion else none
        | .keep | .movingSvgWithPoster _ | .convertedPrimary _ => none
      { en with webSvg := some (companion.getD bytes)
                posterSvg := if companion.isSome then some bytes else none
                webWords := if companion.isSome then "" else answer.words
                webError := none }

public theorem apply_info_exact (en : Image.Loaded) (p : Plan) (answer : Outcome) :
    (apply en p answer).info = en.info := by
  rcases answer with ⟨bytes, companionOk, words⟩
  cases p <;> cases bytes <;> rfl

public theorem apply_canvas_exact (en : Image.Loaded) (p : Plan) (answer : Outcome) :
    (apply en p answer).canvasSize = en.canvasSize := by
  rcases answer with ⟨bytes, companionOk, words⟩
  cases p <;> cases bytes <;> rfl

private def Conversion.source? (en : Image.Loaded) : Conversion → Option ByteArray
  | .svgPoster _ => en.source.or en.webSvg
  | .pdfPage _ => en.source

/-- A cache slot's batch key: the captured source's content fingerprint, else the entry's
position. -/
public def sourceKey (source : Option ByteArray) (index : Nat) : Sum Nat String :=
  match source with
  | none => .inl index
  | some bytes => .inr (Flate.contentKey bytes)

public theorem sourceKey_contract (a b : ByteArray) (i j : Nat) :
    sourceKey (some a) i = sourceKey (some b) j ↔
      Flate.contentKey a = Flate.contentKey b := by
  simp [sourceKey]

private def mapBySource (limit : Nat) (source : α → Option ByteArray)
    (f : α → IO β) (xs : Array α) : IO (Array β) := do
  let keyed := xs.mapIdx fun i x => (sourceKey (source x) i, x)
  Batch.map limit Prod.fst (fun x => f x.2) keyed

private def primarySource? (en : Image.Loaded) : Option ByteArray :=
  (plan en).conversion?.bind (Conversion.source? en)

private inductive Prepared where
  | keep (entry : Image.Loaded)
  | converted (entry : Image.Loaded) (plan : Plan) (bytes : Except String ByteArray)
      (diags : Array Diag) (checked : Bool) (route : Option Boundary.Route) (words : String)

/-- A selected PDF page's face, native first; the converter runs only for a page whose
import names a loss. -/
private def preparePrimary (decl : Boundary.Refusal) (door : PdfFaces.Door)
    (en : Image.Loaded) : IO Prepared := do
  let p := plan en
  let some conversion := p.conversion? | return .keep en
  match conversion, conversion.source? en with
  | .svgPoster page, some svg => return .converted en p (← ImageAssets.canonicalPoster svg page) #[] false none ""
  | .svgPoster _, none =>
    return .converted en p (.error "the SVG source has no captured bytes") #[] false none ""
  | .pdfPage page, some pdf =>
    let f ← PdfFaces.face (HtmlDoc.resolvedSrc en) pdf page (door (ImageAssets.pdfSvgAnswer pdf page))
      ImageAssets.validateSvgResult decl (stretch := true) (cache := ← PdfFaces.cacheDir) (checkRefused := false)
    return .converted en p f.bytes f.diags f.checked (some f.route) f.words
  | .pdfPage _, none =>
    return .converted en p (.error "the PDF source has no captured bytes") #[] false none ""

private def Prepared.companion? : Prepared → Option ByteArray
  | .converted en (.animatedWithCompanion _) (.ok _) _ _ _ _ => en.companion
  | _ => none

/-- What one face's preparation leaves: the entry, the diagnostics its route owes, and the
bytes publication need not check again. -/
public structure Finished where
  entry : Image.Loaded
  diags : Array Diag
  checked : Option ByteArray
  route : Option Boundary.Route

private def Prepared.finish (prepared : Prepared) : IO Finished := do
  match prepared with
  | .keep en => return { entry := en, diags := #[], checked := none, route := none }
  | .converted en p bytes diags checked route words =>
    let companionOk := match prepared.companion? with
      | some svg => (Svg.judge svg).toBool
      | none => false
    let entry := apply en p { bytes, companionOk, words }
    let checkedFace := if checked then (match bytes with
      | .ok b => some b
      | .error _ => none) else none
    return { entry, diags, checked := checkedFace, route }

public def prepare (en : Image.Loaded) : IO Image.Loaded := do
  return (← (← preparePrimary .none (← PdfFaces.door) en).finish).entry

/-- Prepare browser faces with at most `max 1 limit` concurrent requests, in source order;
every primary finishes before any companion. -/
public def prepareAllFaces (entries : Array Image.Loaded) (limit : Nat := 4)
    (decl : Boundary.Refusal := .none) (door : Option PdfFaces.Door := none) :
    IO (Array Image.Loaded × Array (String × Diag) × Array ByteArray × PdfFaces.Tally) := do
  let door ← match door with
    | some d => pure d
    | none => PdfFaces.door
  let prepared ← mapBySource limit primarySource? (preparePrimary decl door) entries
  let done ← mapBySource limit Prepared.companion? Prepared.finish prepared
  return (done.map (·.entry), done.flatMap (fun f => f.diags.map (f.entry.src, ·)),
    done.filterMap (·.checked), done.foldl (fun t f => (f.route.map t.add).getD t) {})

/-- `prepareAllFaces`' entries alone. -/
public def prepareAll (entries : Array Image.Loaded) (limit : Nat := 4) :
    IO (Array Image.Loaded) :=
  (·.1) <$> prepareAllFaces entries limit

end LeanTex.Cli.BrowserFaces
