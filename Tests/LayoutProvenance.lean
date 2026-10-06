import LeanTex.Core.Layout

namespace LeanTex.Tests.LayoutProvenance

open Core Core.Dim Core.Ir Core.Layout Core.Font

private def source (line id : Nat) : Span :=
  { file := "layout-provenance.tex"
    pos := { line, col := 3, origins := [{ id, name := "framefixture" }],
             command := some "\\begin{frame}" } }

/-- Span equality intentionally ignores expansion metadata, so the regression
checks those fields separately as well as the physical source coordinates. -/
private def sameSource (actual : Option Span) (expected : Span) : Bool :=
  match actual with
  | none => false
  | some actual =>
    actual == expected && actual.pos.origins == expected.pos.origins &&
      actual.pos.command == expected.pos.command

/-- Identical frames restart numbering, expand overlays, and spill naturally.
Their diagnostics must still name two distinct opening declarations. -/
def frameSourceChecks (fs : FontSet) : Array (String × Bool) := Id.run do
  let geom : Geom := {
    pageW := pt 220, pageH := pt 120
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let body := (Array.replicate 24 (.para #[.text "Frame body"] : Block)).push
    (.onSteps { first := 2, last := none } #[.para #[.text "Second step"]])
  let frame := Block.frame #[.text "Frame title"] false .top false body
  let doc : Doc := { docClass := .slides, body := #[frame, frame], frameRestart := some 1 }
  let first := source 7 11
  let second := source 73 29
  let out := run geom fs none doc (frameSpans := #[(0, first), (1, second)])
  let spills := out.diags.filter (·.kind == .W0384)
  return #[
    ("frames really expand and spill", out.pages.size > 4),
    ("frame opening 7 survives overlays and spills", spills.any fun d => sameSource d.span first),
    ("frame opening 73 survives overlays and spills", spills.any fun d => sameSource d.span second),
    ("identical messages at distinct declarations stay distinct", spills.size == 2),
    ("every spill names its own opening",
      !spills.isEmpty && spills.all fun d =>
        sameSource d.span first || sameSource d.span second)]

end LeanTex.Tests.LayoutProvenance
