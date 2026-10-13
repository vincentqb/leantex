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

/-! A PDF figure's web face, native first. The PDF backend embeds a figure's
page verbatim; the browser receives the engine's own drawing of it
(`PdfGfx.importPage`, `GfxSvg.document`) — exact when the import named no
loss, and then no converter runs. A figure whose import named a loss is
handed to the external converter, and where the converter does not draw it
the engine's lossy drawing ships with every loss named (`Boundary.route`
decides; this module runs the decision). The import is a pure function of
the page's bytes, so what the decision reads of it — the losses, the
drawing and its words, or the refusal — is kept in the face cache under
those bytes and the engine that read them (`FigureFace`), and a warm build
reads no page. -/

namespace LeanTex.Cli.PdfFaces

open LeanTex.Core

/-- The data URI a figure's raster is referenced by. -/
public def rasterHref (r : Gfx.Raster) : String :=
  "data:" ++ (if r.jpeg then "image/jpeg" else "image/png") ++ ";base64," ++ HtmlResource.base64 r.bytes

/-- **A figure as a standalone SVG**: its outlines one definition per
glyph, one use per placement, its rasters embedded — closed by
construction, every reference a fragment of its own or a `data:` raster;
stretched onto the box it is shown in where the PDF face is (`stretch`). -/
public def svgOf (fig : Gfx.Figure Gfx.Run) (stretch : Bool := false) : ByteArray :=
  (GfxSvg.document (fun _ (_ : Gfx.Run) => Html.text "")
    (fig.rasters.map fun r => { href := rasterHref r, smooth := r.smooth }) fig stretch).toUTF8

/-- **What a face's decision reads of an import** (`FigureFace.Answer`):
the losses the import named, the engine's drawing, stretched as the face is
shown, and the words the figure says (`Gfx.Figure.said`), or why the import
refused the page. -/
public def nativeOf (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) : FigureFace.Answer :=
  (PdfGfx.importPage pdf page).map fun imp =>
    { losses := imp.figure.losses, face := svgOf imp.figure stretch, words := imp.figure.said fun _ => "" }

/-- An import read as the boundary's verdict. -/
public def verdictOf : FigureFace.Answer → Boundary.Verdict
  | .ok d => if d.losses.isEmpty then .exact else .lossy d.losses
  | .error why => .refused why

/-- What the external converter answered for a figure's web face, read by
the check publication runs on every embedded SVG: not asked; a face — the
check keeps it, or it was not checked here and publication checks it
(`checked`); a face the check refuses, with its words; or no face, the
converter having failed. -/
public inductive Answer where
  | notAsked
  | drew (bytes : ByteArray) (checked : Bool)
  | rejected (bytes : ByteArray) (why : String)
  | failed (why : String)

/-- An answer as the boundary's route reads it: a face the check refused is
no drawing the page can carry. -/
public def Answer.tool : Answer → Boundary.ToolState
  | .notAsked => .notAsked
  | .drew _ _ => .drew
  | .rejected _ why => .failed why
  | .failed why => .failed why

/-- Why an answer leaves the engine's drawing on the page: no face, in the
converter's words; a face the check refused, in the check's; and, where it
was not asked or its drawing was not taken, the document's refusal
(`Boundary.route_tool_exact`). -/
public def Answer.unconverted : Answer → FigureLoss.Unconverted
  | .failed why => .failed why
  | .rejected _ why => .unfit why
  | .notAsked | .drew _ _ => .refused

/-- **The converter's answer, checked** (`ImageAssets.validateSvgResult` in
the driver) where `check` asks it: its face kept, refused with the check's
words, or none where the conversion failed or its check did not finish;
unchecked, its face as it drew it, which publication checks. -/
public def answerOf (convert : IO (Except String ByteArray))
    (check : Option (ByteArray → IO PicCache.Outcome)) : IO Answer := do
  match ← convert with
  | .error why => return .failed why
  | .ok bytes =>
    match check with
    | none => return .drew bytes false
    | some check =>
      match ← check bytes with
      | .drawn => return .drew bytes true
      | .refused why => return .rejected bytes why
      | .inconclusive why => return .failed why

/-- A web face as decided: its bytes or why it has none, the route that
chose it, the diagnostics the choice owes, whether the bytes are the
engine's own drawing, whether they need no check at publication — the
engine's drawing, closed by construction, or a converted face the page's
check already kept here — and the words the figure says, which the page
carries beside the face whoever drew it, as the PDF's form carries them. -/
public structure Face where
  bytes : Except String ByteArray
  route : Boundary.Route
  diags : Array Diag
  native : Bool
  checked : Bool
  words : String := ""

/-- **A PDF page's web face, decided** (`Boundary.route`): the import's
drawing when it is exact, with no converter run; else the converter's face
when the page's check keeps it, the features that sent it there each named;
else — the converter refused by the document, missing, failed, or its face
refused by the check — the import's lossy drawing with each feature it
lacks named, in the converter's own words where it was asked. A page the
importer could not read at all takes the converter's face whole, and one
the check refused stays for publication to refuse. Pure: what the import
and the converter answered are inputs. -/
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
  | r, .error iw, .failed w =>
    { bytes := .error (if w.isEmpty then iw else w), route := r, diags := #[], native := false, checked := false }
  | r, .error iw, _ => { bytes := .error iw, route := r, diags := #[], native := false, checked := false }
  | r, .ok _, _ => { bytes := .error "no web face", route := r, diags := #[], native := false, checked := false }

/-- Whether an answer fits the face cache's format under a key
(`FigureFace.Bounded`). -/
private def storable (key : Array String) (a : FigureFace.Answer) : Bool :=
  let fits (n : Nat) : Bool := n < 256 ^ 4
  fits (FigureFace.body key a).size && fits key.size && key.all (fun k => fits k.toUTF8.size) &&
    match a with
    | .error why => fits why.toUTF8.size
    | .ok d =>
      fits d.losses.size && fits d.face.size && fits d.words.toUTF8.size &&
        d.losses.all fun l => fits (FigureFace.lossName l).toUTF8.size

/-- A face's slot, one per figure: the page's bytes, and the page and
stretch read from them. A later engine's answer replaces an earlier one's
in it, so the cache holds one face per figure page, however often the
engine is rebuilt. -/
public def slotName (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) : String :=
  Flate.contentKey pdf ++ "-" ++
    Flate.contentKey (String.intercalate "\u0000" ["pdf-face-v2", reprStr page, toString stretch]).toUTF8 ++
    ".face"

/-- **The key an answer is stored under**: the format, the page's bytes by
their content key, the page and the stretch, and the engine that read them
— everything the answer is a function of (`nativeOf`). A slot answers a
read only where the key it holds is this one (`FigureFace.lookup_exact`). -/
public def slotKey (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool) (engine : String) :
    Array String :=
  #["pdf-face-v2", Flate.contentKey pdf, reprStr page, toString stretch, engine]

/-- **The import's answer, through the face cache in `dir`** (none: no
cache): a slot holding this very key (`slotKey`) is the answer this engine
gave for these bytes, page and stretch (`FigureFace.lookup_exact`);
anything else — no slot, another engine's, a damaged one — is read afresh
and replaces it, a refusal as much as a drawing: the import is pure, so
there is no unfinished attempt to keep out. -/
public def nativeCached (dir : Option System.FilePath) (pdf : ByteArray) (page : PdfRead.PageSelection)
    (stretch : Bool) : IO FigureFace.Answer := do
  let fresh := fun (_ : Unit) => nativeOf pdf page stretch
  let some dir := dir | return fresh ()
  let some engine ← Engine.engineId | return fresh ()
  let key := slotKey pdf page stretch engine
  let path := dir / slotName pdf page stretch
  if let some a := (← (IO.FS.readBinFile path).toBaseIO).toOption.bind (FigureFace.lookup key) then return a
  let a := fresh ()
  if storable key a then
    discard <| (do IO.FS.createDirAll dir; AtomicFile.write path (FigureFace.encode key a)).toBaseIO
  return a

/-- The face cache's directory, beside the engine's other caches. -/
public def cacheDir : IO (Option System.FilePath) := do
  return (← FontDiscovery.cacheDir).map (· / "faces")

/-- **A PDF page's web face, native first**: the page's import read (through
the face cache in `cache`), the converter run only where the verdict asks
it (`Boundary.Verdict.asksTool`), and the face `decide`s. The converter's
face is checked here where the engine's drawing stands in for a face the
check refuses — the import named a loss — and, for a page the importer
refused, where the caller checks its faces before publication does
(`checkRefused`: the boundary pictures do, an include's faces wait for
publication's check). -/
public def face (src : String) (pdf : ByteArray) (page : PdfRead.PageSelection)
    (convert : IO (Except String ByteArray)) (check : ByteArray → IO PicCache.Outcome)
    (decl : Boundary.Refusal := .none) (stretch : Bool := false)
    (cache : Option System.FilePath := none) (checkRefused : Bool := true) : IO Face := do
  let native ← nativeCached cache pdf page stretch
  let v := verdictOf native
  let checking : Option (ByteArray → IO PicCache.Outcome) := match v with
    | .refused _ => if checkRefused then some check else none
    | _ => some check
  let answer ← if v.asksTool decl then answerOf convert checking else pure .notAsked
  return decide src native answer decl

/-- How a build's figure faces were decided: drawn by the engine, exactly or
with losses named; drawn by the converter; or left to a placeholder. -/
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

/-- **An exact import is the web face, and the converter is never asked**
(`_exact`): a figure whose import names no loss ships the engine's drawing
with no diagnostic, whatever the document declares — so a lossless figure
reads the same on a machine with no converter. -/
public theorem route_exact (src : String) (svg : ByteArray) (words : String) (decl : Boundary.Refusal) :
    (PdfFaces.verdictOf (.ok { losses := #[], face := svg, words })).asksTool decl = false ∧
      PdfFaces.decide src (.ok { losses := #[], face := svg, words }) .notAsked decl =
        { bytes := .ok svg, route := .native, diags := #[], native := true, checked := true, words } := by
  have hv : PdfFaces.verdictOf (.ok { losses := #[], face := svg, words }) = .exact := by
    simp [PdfFaces.verdictOf]
  refine ⟨by rw [hv]; exact Boundary.asksTool_lossless_exact decl, ?_⟩
  unfold PdfFaces.decide
  rw [hv, Boundary.route_exact]

/-- **Every loss an import names reaches the page's diagnostics**
(`_named`): whichever route the face takes — the converter's drawing or the
engine's own — each loss of the figure has a diagnostic whose subject is
its census key. -/
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
  · rw [hr]
    exact FigureLoss.pdfDiags_named src answer.unconverted false losses l h

/-- **The cache answers what the import answers** (`_exact`): a slot that
holds what `nativeCached` stored for these bytes, page and stretch under
an engine reads back, for that engine, as exactly the fresh reading
(`FigureFace.lookup_exact`) — so a warm face is the cold one — and the same
slot read for another engine, another page or stretch, or bytes of another
content key is a miss, read afresh: never a face this reading did not give. -/
public theorem nativeOf_exact (pdf : ByteArray) (page : PdfRead.PageSelection) (stretch : Bool)
    (engine : String)
    (h : FigureFace.Bounded (PdfFaces.slotKey pdf page stretch engine) (PdfFaces.nativeOf pdf page stretch)) :
    FigureFace.lookup (PdfFaces.slotKey pdf page stretch engine)
        (FigureFace.encode (PdfFaces.slotKey pdf page stretch engine) (PdfFaces.nativeOf pdf page stretch)) =
        some (PdfFaces.nativeOf pdf page stretch) ∧
      ∀ pdf' page' stretch' engine', (Flate.contentKey pdf', reprStr page', toString stretch', engine') ≠
          (Flate.contentKey pdf, reprStr page, toString stretch, engine) →
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
