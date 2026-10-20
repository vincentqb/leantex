module

public import LeanTex.Core.Diag
public import LeanTex.Core.PdfGfx
public import LeanTex.Cli.Boundary
import LeanTex.Core.GfxSvg
import LeanTex.Core.HtmlResource
public import LeanTex.Core.FigureLoss
public import LeanTex.Core.FigureFace
import LeanTex.Cli.AtomicFile
import LeanTex.Cli.Engine
import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.ToolProbe
import LeanTex.Cli.ImageAssets

/-! A PDF figure's web face, native first: the engine's drawing when the import names no
loss, else the converter's face where it draws one, else the lossy drawing with each loss
named; import answers are cached by page bytes and engine. -/

namespace LeanTex.Cli.PdfFaces

open LeanTex.Core

/-- The data URI a figure's raster is referenced by. -/
public def rasterHref (r : Gfx.Raster) : String :=
  "data:" ++ (if r.jpeg then "image/jpeg" else "image/png") ++ ";base64," ++ HtmlResource.base64 r.bytes

/-- A figure as a standalone SVG: one definition per glyph, one use per placement, rasters
embedded, stretched onto its box under `stretch`. -/
public def svgOf (fig : Gfx.Figure Gfx.Run) (stretch : Bool := false) : ByteArray :=
  (GfxSvg.document (fun _ (_ : Gfx.Run) => Html.text "")
    (fig.rasters.map fun r => { href := rasterHref r, smooth := r.smooth }) fig stretch).toUTF8

/-- What a face's decision reads of an import: its losses, the engine's drawing and the
figure's words, or why the import refused the page. -/
public def nativeOf (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) : FigureFace.Answer :=
  (PdfGfx.importPage pdf page).map fun imp =>
    { losses := imp.figure.losses, face := svgOf imp.figure stretch, words := imp.figure.said fun _ => "" }

/-- An import read as the boundary's verdict. -/
public def verdictOf : FigureFace.Answer → Boundary.Verdict
  | .ok d => if d.losses.isEmpty then .exact else .lossy d.losses
  | .error why => .refused why

/-- What the external converter answered for a figure's web face: not asked, no converter,
a face kept or left unchecked, a face the check refused, or no face, each with its
words. -/
public inductive Answer where
  | notAsked
  | absent
  | drew (bytes : ByteArray) (checked : Bool)
  | rejected (bytes : ByteArray) (why : String)
  | failed (why : String)
  | unfinished (why : String)

/-- The words an answer that gave no face says why in. -/
public def Answer.said? : Answer → Option String
  | .absent => some (ImageAssets.missingWords FigureLoss.pdfFigures.tool)
  | .failed why | .unfinished why => some why
  | .notAsked | .drew _ _ | .rejected _ _ => none

/-- An answer as the boundary's route reads it; a face the check refused is no drawing. -/
public def Answer.tool : Answer → Boundary.ToolState
  | .notAsked => .notAsked
  | .absent => .failed (ImageAssets.missingWords FigureLoss.pdfFigures.tool)
  | .drew _ _ => .drew
  | .rejected _ why | .failed why | .unfinished why => .failed why

/-- Why an answer leaves the engine's drawing on the page. -/
public def Answer.unconverted : Answer → FigureLoss.Unconverted
  | .absent => .absent
  | .failed why => .failed why
  | .unfinished why => .unfinished why
  | .rejected _ why => .unfit why
  | .notAsked | .drew _ _ => .refused

/-- The converter's answer, checked by `check` where given: none without a converter, else
its face kept, refused or undrawn; an unchecked face is checked at publication. -/
public def answerOf (convert : IO (Option (Except PicCache.Outcome ByteArray)))
    (check : Option (ByteArray → IO PicCache.Outcome)) : IO Answer := do
  match ← convert with
  | none => return .absent
  | some (.error (.refused why)) => return .failed why
  | some (.error o) => return .unfinished (Boundary.undrawnWords o)
  | some (.ok bytes) =>
    match check with
    | none => return .drew bytes false
    | some check =>
      match ← check bytes with
      | .drawn => return .drew bytes true
      | .refused why => return .rejected bytes why
      | .inconclusive why => return .unfinished why

/-- A figure face's converter door: `convert` runs where the host has the converter, and
none answers for a host without it. -/
public abbrev Door := IO (Except PicCache.Outcome ByteArray) → IO (Option (Except PicCache.Outcome ByteArray))

/-- A converter door that asks `probe` once, the first time a face needs the converter,
however many faces ask at once. -/
public def doorWith (probe : IO Bool) : BaseIO Door := do
  let present ← ToolProbe.once probe
  return fun convert => do
    if ← present then some <$> convert else pure none

/-- poppler's pdftocairo behind that door, opened once per build. -/
public def door : BaseIO Door :=
  doorWith (do return (← ToolProbe.onPath FigureLoss.pdfFigures.tool).isSome)

/-- A web face as decided: its bytes or why it has none, its route, the diagnostics owed,
whether the bytes are the engine's drawing or need no check at publication, and the
figure's words. -/
public structure Face where
  bytes : Except String ByteArray
  route : Boundary.Route
  diags : Array Diag
  native : Bool
  checked : Bool
  words : String := ""

/-- A PDF page's web face, decided purely from what the import and the converter answered
(`Boundary.route`). -/
public def decide (src : String) (native : FigureFace.Answer) (answer : Answer)
    (decl : Boundary.Refusal) : Face :=
  match Boundary.route (verdictOf native) answer.tool decl, native, answer with
  | .native, .ok d, _ =>
    { bytes := .ok d.face, route := .native, diags := #[], native := true, checked := true, words := d.words }
  | .tool, .ok d, .drew bytes checked =>
    { bytes := .ok bytes, route := .tool, native := false, checked, words := d.words
      diags := FigureLoss.diags (FigureLoss.pdfConvertedDiag src) d.losses }
  | .nativeWithLoss, .ok d, _ =>
    { bytes := .ok d.face, route := .nativeWithLoss, native := true, checked := true, words := d.words
      diags := FigureLoss.diags (FigureLoss.pdfLostDiag src answer.unconverted) d.losses }
  | .tool, .error _, .drew bytes checked =>
    { bytes := .ok bytes, route := .tool, diags := #[], native := false, checked }
  | r, .error _, .rejected bytes _ =>
    { bytes := .ok bytes, route := r, diags := #[], native := false, checked := false }
  -- Why the import gave no face, then why the converter gave none.
  | r, .error iw, a =>
    { bytes := .error (match a.said? with
        | some w => if w.isEmpty then iw else if iw.isEmpty then w else s!"{iw}; {w}"
        | none => iw), route := r, diags := #[], native := false, checked := false }
  | r, .ok _, _ => { bytes := .error "no web face", route := r, diags := #[], native := false, checked := false }

/-- A page selection as a slot spells it. -/
public def pageKey : PdfRead.PageSelection → String
  | .first => "first"
  | .last => "last"
  | .number n => s!"number {n}"

/-- A face's slot, one per figure page: the page's bytes, page and stretch; a later
engine's answer replaces an earlier one's. -/
public def slotName (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) : String :=
  Flate.contentKey pdf ++ "-" ++
    Flate.contentKey (String.intercalate "\u0000" ["pdf-face-v3", pageKey page, toString stretch]).toUTF8 ++
    ".face"

/-- The key an answer is stored under: format, the page's content key, page, stretch and
the reading engine. -/
public def slotKey (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) (engine : String) :
    Array String :=
  #["pdf-face-v3", Flate.contentKey pdf, pageKey page, toString stretch, engine]

/-- The import's answer through the face cache in `dir`: a slot holding this key answers,
and anything else is read afresh and replaces it. -/
public def nativeCached (dir : Option System.FilePath) (pdf : ByteArray) (page : PdfRead.PageSelection)
    (stretch : Bool) : IO FigureFace.Answer := do
  let fresh := fun (_ : Unit) => nativeOf pdf page stretch
  let some dir := dir | return fresh ()
  let some engine ← Engine.engineId | return fresh ()
  let key := slotKey pdf page stretch engine
  let path := dir / slotName pdf page stretch
  if let some a := (← (IO.FS.readBinFile path).toBaseIO).toOption.bind (FigureFace.lookup key) then return a
  let a := fresh ()
  if FigureFace.storable key a then
    discard <| (do IO.FS.createDirAll dir; AtomicFile.write path (FigureFace.encode key a)).toBaseIO
  return a

/-- The face cache's directory, beside the engine's other caches. -/
public def cacheDir : IO (Option System.FilePath) := do
  return (← FontDiscovery.cacheDir).map (· / "faces")

/-- A PDF page's web face, native first: the import read through the face cache, the
converter run only where the verdict asks it, and the face decided. -/
public def face (src : String) (pdf : ByteArray) (page : PdfRead.PageSelection)
    (convert : IO (Option (Except PicCache.Outcome ByteArray))) (check : ByteArray → IO PicCache.Outcome)
    (decl : Boundary.Refusal := .none) (stretch : Bool := false)
    (cache : Option System.FilePath := none) (checkRefused : Bool := true) : IO Face := do
  let native ← nativeCached cache pdf page stretch
  let v := verdictOf native
  let checking : Option (ByteArray → IO PicCache.Outcome) := match v with
    | .refused _ => if checkRefused then some check else none
    | _ => some check
  let answer ← if v.asksTool decl then answerOf convert checking else pure .notAsked
  return decide src native answer decl

/-- How a build's figure faces were decided: by the engine, exactly or with losses named,
by the converter, or left to a placeholder. -/
public structure Tally where
  native : Nat := 0
  tool : Nat := 0
  lossy : Nat := 0
  refused : Nat := 0
  deriving Inhabited

/-- One face's route counted. -/
public def Tally.add (t : Tally) : Boundary.Route → Tally
  | .native => { t with native := t.native + 1 }
  | .tool => { t with tool := t.tool + 1 }
  | .nativeWithLoss => { t with lossy := t.lossy + 1 }
  | .refused => { t with refused := t.refused + 1 }

/-- Two tallies summed. -/
public def Tally.merge (a b : Tally) : Tally :=
  { native := a.native + b.native, tool := a.tool + b.tool, lossy := a.lossy + b.lossy
    refused := a.refused + b.refused }

/-- The phase line's words for a tally. -/
public def Tally.words (t : Tally) : String :=
  s!"{t.native} native, {t.lossy} native with losses named, {t.tool} by the converter, \
{t.refused} placeholders"

end LeanTex.Cli.PdfFaces

namespace LeanTex.Core.PdfGfx

open LeanTex.Cli

public theorem route_exact (src : String) (svg : ByteArray) (words : String) (decl : Boundary.Refusal) :
    (PdfFaces.verdictOf (.ok { losses := #[], face := svg, words })).asksTool decl = false ∧
      PdfFaces.decide src (.ok { losses := #[], face := svg, words }) .notAsked decl =
        { bytes := .ok svg, route := .native, diags := #[], native := true, checked := true, words } := by
  have hv : PdfFaces.verdictOf (.ok { losses := #[], face := svg, words }) = .exact := by
    simp [PdfFaces.verdictOf]
  refine ⟨by rw [hv]; exact Boundary.asksTool_lossless_exact decl, ?_⟩
  unfold PdfFaces.decide
  rw [hv, Boundary.route_exact]

public theorem import_named (src : String) (losses : Array Gfx.Loss) (svg : ByteArray) (words : String)
    (answer : PdfFaces.Answer) (decl : Boundary.Refusal) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ (PdfFaces.decide src (.ok { losses, face := svg, words }) answer decl).diags,
      d.subject = some (FigureLoss.subject "pdf" l) := by
  have hne : losses.isEmpty = false := by
    cases hl : losses.isEmpty
    · rfl
    · simp [Array.isEmpty_iff] at hl
      simp [hl] at h
  have hv : PdfFaces.verdictOf (.ok { losses, face := svg, words }) = .lossy losses := by
    simp [PdfFaces.verdictOf, hne]
  unfold PdfFaces.decide
  rw [hv]
  rcases Boundary.route_lossy_exact losses answer.tool decl with hr | hr
  · have hd := (Boundary.route_tool_exact _ _ _ hr).1
    rw [hr]
    cases answer with
    | drew bytes c => exact FigureLoss.pdfDiags_named src .refused true losses l h
    | notAsked => simp [PdfFaces.Answer.tool] at hd
    | rejected bytes why => simp [PdfFaces.Answer.tool] at hd
    | failed why => simp [PdfFaces.Answer.tool] at hd
    | unfinished why => simp [PdfFaces.Answer.tool] at hd
    | absent => simp [PdfFaces.Answer.tool] at hd
  · rw [hr]
    exact FigureLoss.pdfDiags_named src answer.unconverted false losses l h

public theorem nativeOf_exact (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool)
    (engine : String)
    (h : FigureFace.Bounded (PdfFaces.slotKey pdf page stretch engine) (PdfFaces.nativeOf pdf page stretch)) :
    FigureFace.lookup (PdfFaces.slotKey pdf page stretch engine)
        (FigureFace.encode (PdfFaces.slotKey pdf page stretch engine) (PdfFaces.nativeOf pdf page stretch)) =
        some (PdfFaces.nativeOf pdf page stretch) ∧
      ∀ pdf' page' stretch' engine', (Flate.contentKey pdf', PdfFaces.pageKey page', toString stretch', engine') ≠
          (Flate.contentKey pdf, PdfFaces.pageKey page, toString stretch, engine) →
        FigureFace.lookup (PdfFaces.slotKey pdf' page' stretch' engine')
          (FigureFace.encode (PdfFaces.slotKey pdf page stretch engine) (PdfFaces.nativeOf pdf page stretch)) =
          none := by
  obtain ⟨hit, miss⟩ := FigureFace.lookup_exact _ _ h
  refine ⟨hit, fun pdf' page' stretch' engine' hne => miss _ ?_⟩
  intro heq
  apply hne
  simp only [PdfFaces.slotKey, List.toArray, Array.mk.injEq, List.cons.injEq] at heq
  obtain ⟨_, h1, h2, h3, h4, _⟩ := heq
  rw [h1, h2, h3, h4]

end LeanTex.Core.PdfGfx
