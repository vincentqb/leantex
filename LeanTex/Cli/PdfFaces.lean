module

public import LeanTex.Core.Diag
public import LeanTex.Core.PdfGfx
public import LeanTex.Cli.Boundary
import LeanTex.Core.GfxSvg
import LeanTex.Core.HtmlResource
public import LeanTex.Core.FigureLoss

/-! A PDF figure's web face, native first. The PDF backend embeds a figure's
page verbatim; the browser receives the engine's own drawing of it
(`PdfGfx.importPage`, `GfxSvg.document`) — exact when the import named no
loss, and then no converter runs. A figure whose import named a loss is
handed to the external converter, and where the converter does not draw it
the engine's lossy drawing ships with every loss named (`Boundary.route`
decides; this module runs the decision). -/

namespace LeanTex.Cli.PdfFaces

open LeanTex.Core

/-- The data URI a figure's raster is referenced by. -/
public def rasterHref (r : Gfx.Raster) : String :=
  "data:" ++ (if r.jpeg then "image/jpeg" else "image/png") ++ ";base64," ++ HtmlResource.base64 r.bytes

/-- **A figure as a standalone SVG**: its outlines one definition per
glyph, one use per placement, its rasters embedded — closed by
construction, every reference a fragment of its own or a `data:` raster. -/
public def svgOf (fig : Gfx.Figure Gfx.Run) : ByteArray :=
  (GfxSvg.document (fun _ (_ : Gfx.Run) => Html.text "")
    (fig.rasters.map fun r => { href := rasterHref r, smooth := r.smooth }) fig).toUTF8

/-- An import read as the boundary's verdict. -/
public def verdictOf : Except String PdfGfx.Imported → Boundary.Verdict
  | .ok imp => if imp.figure.losses.isEmpty then .exact else .lossy imp.figure.losses
  | .error why => .refused why

/-- A web face as decided: its bytes or why it has none, the route that
chose it, the diagnostics the choice owes, and whether the bytes are the
engine's own drawing. -/
public structure Face where
  bytes : Except String ByteArray
  route : Boundary.Route
  diags : Array Diag
  native : Bool

/-- **A PDF page's web face, decided** (`Boundary.route`): the import's
drawing when it is exact, with no converter run; else the converter's, the
features that sent it there each named (N0024); else, where the converter
was refused or did not draw, the import's lossy drawing with each feature
it lacks named (W0608); a page the importer could not read at all takes
the converter's answer whole. Pure: what the converter did is an input. -/
public def decide (src : String) (imported : Except String PdfGfx.Imported)
    (tool : Boundary.ToolState) (converted : Except String ByteArray) (decl : Boundary.Refusal) :
    Face :=
  match Boundary.route (verdictOf imported) tool decl, imported with
  | .native, .ok imp => { bytes := .ok (svgOf imp.figure), route := .native, diags := #[], native := true }
  | .tool, .ok imp =>
    { bytes := converted, route := .tool, native := false
      diags := FigureLoss.diags (FigureLoss.pdfConvertedDiag src) imp.figure.losses }
  | .nativeWithLoss, .ok imp =>
    { bytes := .ok (svgOf imp.figure), route := .nativeWithLoss, native := true
      diags := FigureLoss.diags (FigureLoss.pdfLostDiag src) imp.figure.losses }
  | .tool, .error _ => { bytes := converted, route := .tool, diags := #[], native := false }
  | r, _ =>
    let why := match converted, imported with
      | .error w, .error iw => if w == notAsked then iw else w
      | .error w, .ok _ => w
      | .ok _, _ => "no web face"
    { bytes := .error why, route := r, diags := #[], native := false }
where
  notAsked : String := "the converter was not asked"

/-- **A PDF page's web face, native first**: the page imported, the
converter run only where the verdict asks it (`Boundary.Verdict.asksTool`),
and the face `decide`s. -/
public def face (src : String) (pdf : ByteArray) (page : PdfRead.PageSelection)
    (convert : IO (Except String ByteArray)) (decl : Boundary.Refusal := .none) : IO Face := do
  let imported := PdfGfx.importPage pdf page
  let (tool, converted) ← if (verdictOf imported).asksTool decl then do
      match ← convert with
      | .ok bytes => pure (Boundary.ToolState.drew, Except.ok bytes)
      | .error why => pure (.failed why, .error why)
    else pure (.notAsked, .error decide.notAsked)
  return decide src imported tool converted decl

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
public theorem route_exact (src : String) (imp : Imported) (h : imp.figure.losses = #[])
    (decl : Boundary.Refusal) (converted : Except String ByteArray) :
    (PdfFaces.verdictOf (.ok imp)).asksTool decl = false ∧
      PdfFaces.decide src (.ok imp) .notAsked converted decl =
        { bytes := .ok (PdfFaces.svgOf imp.figure), route := .native, diags := #[], native := true } := by
  have hv : PdfFaces.verdictOf (.ok imp) = .exact := by
    simp [PdfFaces.verdictOf, h]
  refine ⟨by rw [hv]; exact Boundary.asksTool_lossless_exact decl, ?_⟩
  unfold PdfFaces.decide
  rw [hv, Boundary.route_exact]

/-- **Every loss an import names reaches the page's diagnostics**
(`_named`): whichever route the face takes — the converter's drawing or the
engine's own — each loss of the figure has a diagnostic whose subject is
its census key. -/
public theorem import_named (src : String) (imp : Imported) (tool : Boundary.ToolState)
    (converted : Except String ByteArray) (decl : Boundary.Refusal) (l : Gfx.Loss)
    (h : l ∈ imp.figure.losses) :
    ∃ d ∈ (PdfFaces.decide src (.ok imp) tool converted decl).diags,
      d.subject = some (FigureLoss.subject "pdf" l) := by
  have hne : imp.figure.losses.isEmpty = false := by
    cases hl : imp.figure.losses.isEmpty
    · rfl
    · simp [Array.isEmpty_iff] at hl
      simp [hl] at h
  have hv : PdfFaces.verdictOf (.ok imp) = .lossy imp.figure.losses := by
    simp [PdfFaces.verdictOf, hne]
  unfold PdfFaces.decide
  rw [hv]
  rcases Boundary.route_lossy_exact imp.figure.losses tool decl with hr | hr
  · rw [hr]
    exact FigureLoss.pdfDiags_named src true imp.figure.losses l h
  · rw [hr]
    exact FigureLoss.pdfDiags_named src false imp.figure.losses l h

end LeanTex.Core.PdfGfx
