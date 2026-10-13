module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Diag

/-!
# A figure's losses, named

An importer answers exact only when every construct it met has the model's
meaning; anything else is a keyed `Gfx.Loss`. This module is how a loss is
named: its feature key, the subject a diagnostic carries it under —
`figure:<kind>:<feature>`, the kind the importer's (`svg`, `pdf`) — and the
diagnostics a drawn figure owes it: W0609 where the engine's drawing ships
without the feature, N0024 where the external converter drew the figure
because of it — one meaning each for either importer, whose converter and
artifacts are its own (`Importer`). One subject per feature, so the census
counts the feature, and the message names the figure.
-/

namespace LeanTex.Core.FigureLoss

open LeanTex.Core LeanTex.Core.Gfx

/-- A loss's feature key: what kind of thing it is, and which. -/
@[expose] public def key : Gfx.Loss → String
  | .element n => "element:" ++ n
  | .attribute n => "attribute:" ++ n
  | .property n => "property:" ++ n
  | .value n => "value:" ++ n
  | .operator n => "operator:" ++ n
  | .resource n => "resource:" ++ n
  | .font k => "font:" ++ k
  | .budget w => "budget:" ++ w

/-- The subject a loss is censused under. -/
@[expose] public def subject (kind : String) (l : Gfx.Loss) : String :=
  s!"figure:{kind}:{key l}"

/-- The words a loss is reported in. -/
@[expose] public def words : Gfx.Loss → String
  | .element n => s!"<{n}> element"
  | .attribute n => s!"'{n}' attribute"
  | .property n => s!"'{n}' property"
  | .value n => s!"'{n}' value"
  | .operator n => s!"'{n}' operator"
  | .resource n => s!"{n} resource"
  | .font k => s!"'{k}' font"
  | .budget w => s!"{w} beyond the reader's budget"

/-- Where the drawing an SVG figure's route chose ships: the PDF always, and
the HTML too when the figure moves — its print and reduced-motion still
face is that drawing — while a still figure's HTML face is its authored
bytes, which the browser draws whole. -/
@[expose] public def shipsIn (moving : Bool) : Option Diag.Output :=
  -- premise: svgOutputScopeChecks — two builds of a still lossy figure, with
  -- and without the converter, ship byte-identical HTML; a moving one's
  -- still face is the engine's drawing, its loss named for the HTML too
  if moving then none else some .pdf

/-- An importer's figures as their diagnostics name them: the subject's
kind, the converter the engine pins for them and its package, and the
artifacts the drawing their route chose ships in. -/
public structure Importer where
  kind : String
  tool : String
  package : String
  output : Option Diag.Output

/-- A PDF figure: its engine drawing is its web face — the PDF carries the
page itself — and poppler's pdftocairo its converter. -/
@[expose] public def pdfFigures : Importer :=
  { kind := "pdf", tool := "pdftocairo", package := "poppler", output := some .html }

/-- An SVG figure: librsvg's rsvg-convert its converter, its drawing
shipping where `shipsIn` says. -/
@[expose] public def svgFigures (moving : Bool) : Importer :=
  { kind := "svg", tool := "rsvg-convert", package := "librsvg", output := shipsIn moving }

/-- Why a figure's drawing is the engine's though the engine lacks a
feature: the document refused the converter; no converter is on this
machine; one was asked and gave no drawing, in its own words; or it drew
one the page cannot carry, in the words of the page's check. -/
public inductive Unconverted where
  | refused
  | absent
  | failed (why : String)
  | unfit (why : String)
  deriving Repr, BEq

/-- **W0609**: a figure's drawing is the engine's, without the feature — no
converter drew the figure whole; where one was asked, its own words, or
the page's check's, say why. The remedy follows the reason: the document's
refusal is the document's to lift; a converter missing, or one that gave
no drawing, is one to install or repair; otherwise the drawing is the
document's to accept. -/
@[expose] public def lostDiag (imp : Importer) (src : String) (why : Unconverted)
    (l : Gfx.Loss) : Diag :=
  Diag.of .W0609
    (s!"figure '{src}' is drawn without its {words l}, which the engine does not draw" ++
      (match why with
       | .failed w | .unfit w => s!" ({w})"
       | .refused | .absent => ""))
    (help := some (match why with
      | .refused => s!"the document's \\figures\{ convert = none } keeps the figure to the \
engine's drawing; remove it to let {imp.tool} draw the figure whole, or accept the loss with \
\\allow\{W0609}"
      | .absent => s!"install {imp.package}'s {imp.tool} to draw the figure whole, or accept the \
loss with \\allow\{W0609}"
      | .failed _ => s!"install or repair {imp.package}'s {imp.tool} to draw the figure whole, or \
accept the loss with \\allow\{W0609}"
      | .unfit _ => "accept the engine's drawing with \\allow{W0609}"))
    (subject := some (subject imp.kind l)) (output := imp.output)

/-- **N0024**: a figure's drawing is the external converter's, because the
engine does not draw the feature. -/
@[expose] public def convertedDiag (imp : Importer) (src : String) (l : Gfx.Loss) : Diag :=
  Diag.of .N0024
    s!"figure '{src}' is drawn by {imp.tool}, because the engine does not draw its {words l}"
    (subject := some (subject imp.kind l)) (output := imp.output)

/-- W0609 for a PDF figure's web face. -/
@[expose] public def pdfLostDiag (src : String) (why : Unconverted) (l : Gfx.Loss) : Diag :=
  lostDiag pdfFigures src why l

/-- N0024 for a PDF figure's web face. -/
@[expose] public def pdfConvertedDiag (src : String) (l : Gfx.Loss) : Diag :=
  convertedDiag pdfFigures src l

/-- W0609 for an SVG figure's drawing. -/
@[expose] public def svgLostDiag (moving : Bool) (src : String) (why : Unconverted)
    (l : Gfx.Loss) : Diag :=
  lostDiag (svgFigures moving) src why l

/-- N0024 for an SVG figure's drawing. -/
@[expose] public def svgConvertedDiag (moving : Bool) (src : String) (l : Gfx.Loss) : Diag :=
  convertedDiag (svgFigures moving) src l

/-- **N0026**: an SVG names a font family the document does not declare,
and no family after it in its list is one the document's roles answer; its
text sets in the document's face `face`. One per family. -/
@[expose] public def svgFontDiag (src family face : String) : Diag :=
  Diag.of .N0026
    s!"'{family}' in figure '{src}' is no family of the document; its text is set in '{face}'"
    (help := some "name a generic family (serif, sans-serif or monospace) last in the SVG's font list, or declare the family in \\fonts")
    (subject := some ("svg:font:" ++ family))

/-- A figure's losses, each named once, as `diag` says it. -/
@[expose] public def diags (diag : Gfx.Loss → Diag) (losses : Array Gfx.Loss) : Array Diag :=
  losses.map diag

/-- **Every loss is named** (`_named`): each loss of the census has a
diagnostic whose subject is its key — the one the census is counted by —
whether the converter drew the figure or the engine did, for either
importer. -/
public theorem diags_named (imp : Importer) (src : String) (why : Unconverted)
    (converted : Bool) (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then convertedDiag imp src else lostDiag imp src why) losses,
      d.subject = some (subject imp.kind l) := by
  refine ⟨(if converted then convertedDiag imp src else lostDiag imp src why) l,
    Array.mem_map_of_mem h, ?_⟩
  cases converted <;> simp [lostDiag, convertedDiag, Diag.of_subject]

/-- **Every loss of a PDF figure is named** (`_named`), whichever route drew
the web face (`diags_named`). -/
public theorem pdfDiags_named (src : String) (why : Unconverted) (converted : Bool)
    (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then pdfConvertedDiag src else pdfLostDiag src why) losses,
      d.subject = some (subject "pdf" l) :=
  diags_named pdfFigures src why converted losses l h

/-- **Every loss of an SVG figure is named** (`_named`), whether the
converter drew the figure or the engine did (`diags_named`). -/
public theorem svgDiags_named (moving : Bool) (src : String) (why : Unconverted)
    (converted : Bool) (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then svgConvertedDiag moving src else svgLostDiag moving src why)
      losses, d.subject = some (subject "svg" l) :=
  diags_named (svgFigures moving) src why converted losses l h

mutual

-- conserves: none — a rewriting that drops a figure's rasters, which the
-- PDF writer cannot yet name inside a figure's form.
/-- One node onto `acc`, its rasters dropped. -/
public def unrasterOne {L : Type} (acc : Array (Gfx.Node L)) : Gfx.Node L → Array (Gfx.Node L)
  | .image _ _ => acc
  | .group xf clips alpha kids => acc.push (.group xf clips alpha (unrasterList #[] kids.toList))
  | .draw g f st => acc.push (.draw g f st)
  | .use k xf => acc.push (.use k xf)
  | .stamp o xf f st => acc.push (.stamp o xf f st)
  | .label l => acc.push (.label l)
  | .words w => acc.push (.words w)

public def unrasterList {L : Type} (acc : Array (Gfx.Node L)) : List (Gfx.Node L) → Array (Gfx.Node L)
  | [] => acc
  | n :: rest => unrasterList (unrasterOne acc n) rest

end

/-- The loss a figure's rasters are, where the drawing that ships cannot
carry them: a raster the image planner refuses (`FigureStore.rasterPlans`). -/
@[expose] public def rasterLoss : Gfx.Loss := .resource "raster in a PDF figure"

/-- **A figure with its rasters dropped and the drop named**: what the
engine's drawing is where a figure's raster cannot be placed — every other
mark stands, and the loss is the figure's own, so a reader of the figure
(the page's inline choice, the route) sees it. A figure with no raster is
itself. -/
public def unrastered {L : Type} (fig : Gfx.Figure L) : Gfx.Figure L :=
  if fig.rasters.isEmpty then fig else
  { fig with nodes := unrasterList #[] fig.nodes.toList
             symbols := fig.symbols.map fun b => unrasterList #[] b.toList
             rasters := #[]
             losses := if fig.losses.contains rasterLoss then fig.losses else fig.losses.push rasterLoss }

/-- Unrastered, a figure holds no raster. -/
public theorem unrastered_rasters {L : Type} (fig : Gfx.Figure L) : (unrastered fig).rasters.size = 0 := by
  unfold unrastered
  split
  · next h => simpa using h
  · rfl

end LeanTex.Core.FigureLoss
