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
because of it. One subject per feature, so the census counts the feature,
and the message names the figure.
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
  | .font k => s!"{k} font"
  | .budget w => s!"{w} beyond the reader's budget"

/-- Why a PDF figure's web face is the engine's drawing though the engine
lacks a feature: the document refused the converter; the converter gave
no face, in its own words; or it drew one the page cannot carry, in the
words of the page's check. -/
public inductive Unconverted where
  | refused
  | noFace (why : String)
  | unfit (why : String)

/-- **W0609**: a PDF figure's web face is the engine's drawing without the
feature — no converter drew the figure whole; where one was asked, the
words say why its answer is not on the page. The remedy follows the
reason: a converter that gave no face is one to install or repair, and
otherwise the drawing is the document's to accept. -/
@[expose] public def pdfLostDiag (src : String) (why : Unconverted) (l : Gfx.Loss) : Diag :=
  Diag.of .W0609
    (s!"figure '{src}' is drawn on the web page without its {words l}, which the engine does not draw" ++
      (match why with
       | .noFace w | .unfit w => s!" ({w})"
       | .refused => ""))
    (help := some (match why with
      | .noFace _ => "install poppler's pdftocairo to draw the figure whole, or accept the engine's \
          drawing with \\allow{W0609}"
      | .refused | .unfit _ => "accept the engine's drawing with \\allow{W0609}"))
    (subject := some (subject "pdf" l)) (output := some .html)

/-- **N0024**: a PDF figure's web face is the external converter's drawing,
because the engine does not draw the feature. -/
@[expose] public def pdfConvertedDiag (src : String) (l : Gfx.Loss) : Diag :=
  Diag.of .N0024
    s!"figure '{src}' is drawn on the web page by pdftocairo, because the engine does not draw its {words l}"
    (subject := some (subject "pdf" l)) (output := some .html)

/-- A figure's losses, each named once, as `diag` says it. -/
@[expose] public def diags (diag : Gfx.Loss → Diag) (losses : Array Gfx.Loss) : Array Diag :=
  losses.map diag

/-- **Every loss of a PDF figure is named** (`_named`): each loss of the
census has a diagnostic whose subject is its key — the one the census is
counted by — whichever route drew the web face. -/
public theorem pdfDiags_named (src : String) (why : Unconverted) (converted : Bool)
    (losses : Array Gfx.Loss) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ diags (if converted then pdfConvertedDiag src else pdfLostDiag src why) losses,
      d.subject = some (subject "pdf" l) := by
  refine ⟨(if converted then pdfConvertedDiag src else pdfLostDiag src why) l,
    Array.mem_map_of_mem h, ?_⟩
  cases converted <;> simp [pdfLostDiag, pdfConvertedDiag, Diag.of_subject]

end LeanTex.Core.FigureLoss
