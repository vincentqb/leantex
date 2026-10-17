module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Diag

/-! How a figure's losses are named: each feature's key, its census subject, and the diagnostics a
drawn figure owes it. -/

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
  | .css w => "css:" ++ w

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
  | .css w => s!"CSS {w}"

/-- Where a lossy SVG figure's drawing ships: the PDF always, the HTML too when the figure moves. -/
@[expose] public def shipsIn (moving : Bool) : Option Diag.Output :=
  -- premise: svgOutputScopeChecks — two builds of a still lossy figure compared
  if moving then none else some .pdf

/-- An importer's figures as their diagnostics name them: the subject's kind, the converter and its
package, and where the drawing ships. -/
public structure Importer where
  kind : String
  tool : String
  package : String
  output : Option Diag.Output

/-- A PDF figure: its engine drawing is its web face, poppler's pdftocairo its converter. -/
@[expose] public def pdfFigures : Importer :=
  { kind := "pdf", tool := "pdftocairo", package := "poppler", output := some .html }

/-- An SVG figure: librsvg's rsvg-convert its converter, its drawing
shipping where `shipsIn` says. -/
@[expose] public def svgFigures (moving : Bool) : Importer :=
  { kind := "svg", tool := "rsvg-convert", package := "librsvg", output := shipsIn moving }

/-- Why a figure's drawing is the engine's though the engine lacks a feature: the document refused
the converter, none is installed, or one answered no drawing, did not finish, or drew what the
page cannot carry. -/
public inductive Unconverted where
  | refused
  | absent
  | failed (why : String)
  | unfinished (why : String)
  | unfit (why : String)
  deriving Repr, BEq

/-- The remedy a reason offers: lift the refusal, install the converter, repair or rerun it, or
accept the engine's drawing. -/
public inductive Remedy where
  | lift
  | install
  | repair
  | accept
  deriving Repr, BEq, DecidableEq

/-- Each reason's remedy. -/
@[expose] public def Unconverted.remedy : Unconverted → Remedy
  | .refused => .lift
  | .absent => .install
  | .unfinished _ => .repair
  | .failed _ | .unfit _ => .accept

public theorem remedy_tool_exact (why : Unconverted) :
    (why.remedy = .install ∨ why.remedy = .repair) ↔
      (why = .absent ∨ ∃ w, why = .unfinished w) := by
  cases why <;> simp [Unconverted.remedy]

/-- The words a reason carries beside its line: the converter's, the run's,
or the page's check's, where one was asked. -/
@[expose] public def Unconverted.said : Unconverted → Option String
  | .failed w | .unfinished w | .unfit w => some w
  | .refused | .absent => none

/-- W0609: a figure's drawing is the engine's, without the feature; the reason's remedy is the help. -/
@[expose] public def lostDiag (imp : Importer) (src : String) (why : Unconverted)
    (l : Gfx.Loss) : Diag :=
  Diag.of .W0609
    s!"figure '{src}' is drawn without its {words l}, which the engine does not draw"
    (detail := why.said)
    (help := some (match why.remedy with
      | .lift => s!"the document's \\figures\{ convert = none } keeps the figure to the \
engine's drawing; remove it to let {imp.tool} draw the figure whole, or accept the loss with \
\\allow\{W0609}"
      | .install => s!"install {imp.package}'s {imp.tool} to draw the figure whole, or accept the \
loss with \\allow\{W0609}"
      | .repair => s!"install or repair {imp.package}'s {imp.tool} if the reason says it cannot \
start, rebuild if it was interrupted, or accept the loss with \\allow\{W0609}"
      | .accept => "accept the engine's drawing with \\allow{W0609}"))
    (subject := some (subject imp.kind l)) (output := imp.output)

/-- N0024: a figure's drawing is the external converter's, because the engine does not draw the feature. -/
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

/-- W0609 for a character of an SVG figure no face of the document covers. -/
@[expose] public def svgGlyphDiag (output : Option Diag.Output) (src code : String) : Diag :=
  Diag.of .W0609
    s!"figure '{src}' is drawn without its character U+{code}, which no face of the document covers"
    (help := some "declare a face that covers it in \\fonts, or accept the loss with \\allow{W0609}")
    (subject := some (subject "svg" (.font s!"U+{code}"))) (output := output)

/-- N0026: an SVG names a family the document's roles do not answer and none after it in its list
do; its text sets in the document's face `face`. -/
@[expose] public def svgFontDiag (output : Option Diag.Output) (src family face : String) : Diag :=
  Diag.of .N0026
    s!"'{family}' in figure '{src}' is no family of the document; its text is set in '{face}'"
    (help := some "name a generic family (serif, sans-serif or monospace) last in the SVG's font list, or declare the family in \\fonts")
    (subject := some ("svg:font:" ++ family)) (output := output)

/-- N0027: an SVG figure holds a link its drawing does not carry, named once per figure. -/
@[expose] public def svgNoteDiag (src note : String) : Diag :=
  Diag.of .N0027 s!"figure '{src}' holds {note}, which its drawing does not carry; its content is drawn"
    (subject := some ("figure:svg:note:" ++ note))

/-- A figure's losses, each named once, as `diag` says it. -/
@[expose] public def diags (diag : Gfx.Loss → Diag) (losses : Array Gfx.Loss) : Array Diag :=
  losses.map diag

public theorem diags_named (imp : Importer) (src : String) (why : Unconverted)
    (converted : Bool) (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then convertedDiag imp src else lostDiag imp src why) losses,
      d.subject = some (subject imp.kind l) := by
  refine ⟨(if converted then convertedDiag imp src else lostDiag imp src why) l,
    Array.mem_map_of_mem h, ?_⟩
  cases converted <;> simp [lostDiag, convertedDiag, Diag.of_subject]

public theorem pdfDiags_named (src : String) (why : Unconverted) (converted : Bool)
    (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then pdfConvertedDiag src else pdfLostDiag src why) losses,
      d.subject = some (subject "pdf" l) :=
  diags_named pdfFigures src why converted losses l h

public theorem svgDiags_named (moving : Bool) (src : String) (why : Unconverted)
    (converted : Bool) (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then svgConvertedDiag moving src else svgLostDiag moving src why)
      losses, d.subject = some (subject "svg" l) :=
  diags_named (svgFigures moving) src why converted losses l h

mutual

-- conserves: none — a rewriting that drops a figure's rasters.
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

/-- The loss of a figure's rasters where the drawing that ships cannot carry them. -/
@[expose] public def rasterLoss : Gfx.Loss := .resource "embedded raster"

/-- A figure with its rasters dropped and the drop named as its own loss; a figure without rasters
is itself. -/
public def unrastered {L : Type} (fig : Gfx.Figure L) : Gfx.Figure L :=
  if fig.rasters.isEmpty then fig else
  { fig with nodes := unrasterList #[] fig.nodes.toList
             symbols := fig.symbols.map fun b => unrasterList #[] b.toList
             rasters := #[]
             losses := if fig.losses.contains rasterLoss then fig.losses else fig.losses.push rasterLoss }

public theorem unrastered_rasters {L : Type} (fig : Gfx.Figure L) : (unrastered fig).rasters.size = 0 := by
  unfold unrastered
  split
  · next h => simpa using h
  · rfl

end LeanTex.Core.FigureLoss
