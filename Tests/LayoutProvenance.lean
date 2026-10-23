module

public import LeanTex.Core.Layout
public import Tests.Support

public section

namespace LeanTex.Tests.LayoutProvenance

open Core Core.Dim Core.Ir Core.Layout Core.Font

private def provenanceSpan (line id : Nat) : Span :=
  { file := "layout-provenance.tex"
    pos := { line, col := 3, origins := [{ id, name := "framefixture" }],
             command := some "\\begin{frame}" } }

/-- Identical frames that restart numbering, expand overlays and spill still name two distinct
opening declarations. -/
def frameSourceChecks (fs : FontSet) : Array (String × Bool) := Id.run do
  let geom : Geom := {
    pageW := pt 220, pageH := pt 120
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let body := (Array.replicate 24 (.para #[.text "Frame body"] : Block)).push
    (.onSteps { first := 2, last := none } #[.para #[.text "Second step"]])
  let frame := Block.frame #[.text "Frame title"] false .top false body
  let doc : Doc := { docClass := .slides, body := #[frame, frame], frameRestart := some 1 }
  let first := provenanceSpan 7 11
  let second := provenanceSpan 73 29
  let out := run geom fs none doc (frameSpans := #[(0, first), (1, second)])
  let spills := out.diags.filter (·.kind == .W0384)
  let htmlOnly := Block.only #["html"] #[.para #[.text "Web-only content"]]
  let mixed := { doc with body := #[htmlOnly, frame, htmlOnly, frame] }
  let sites := frameSpansForPdf mixed #[(1, first), (3, second)]
  let filtered := run geom fs none mixed (frameSpans := sites)
  let filteredSpills := filtered.diags.filter (·.kind == .W0384)
  return #[
    ("frames really expand and spill", out.pages.size > 4),
    ("frame opening 7 survives overlays and spills", spills.any fun d => sameSource d.span first),
    ("frame opening 73 survives overlays and spills", spills.any fun d => sameSource d.span second),
    ("identical messages at distinct declarations stay distinct", spills.size == 2),
    ("every spill names its own opening",
      !spills.isEmpty && spills.all fun d =>
        sameSource d.span first || sameSource d.span second),
    ("PDF filtering remaps real body indices",
      sites.size == 2 && sites[0]?.map (·.1) == some 0 &&
        sites[1]?.map (·.1) == some 1),
    ("filtered frames retain their own opening through actual layout",
      filteredSpills.size == 2 &&
        filteredSpills.any (fun d => sameSource d.span first) &&
        filteredSpills.any (fun d => sameSource d.span second))]

/-- Each overflowing line names its own source, a note's generated mark included. -/
def overfullSourceChecks (fs : FontSet) : Array (String × Bool) := Id.run do
  let geom : Geom := {
    pageW := pt 160, pageH := pt 400
    hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
    hyphenate := false, justify := false }
  let first := provenanceSpan 17 31
  let second := provenanceSpan 43 47
  let word := Inline.text ("".pushn 'W' 96)
  let content := #[.located first #[word], .linebreak {}, .located second #[word]]
  let out := run geom fs none { body := #[.para content] }
  let overfull := out.diags.filter (·.kind == .W0005)
  let notes := run geom fs none
    { body := #[.para #[.text "Note", .footnote (some (.arabic 1)) content]] }
  let noteOverfull := notes.diags.filter (·.kind == .W0005)
  let expansion := provenanceSpan 17 79
  let expanded := run geom fs none
    { body := #[.para #[.located first #[word]], .para #[.located expansion #[word]]] }
  let expansionOverfull := expanded.diags.filter (·.kind == .W0005)
  return #[
    ("body really overflows", !overfull.isEmpty),
    ("each body line retains its site", overfull.size == 2 &&
      overfull.any (fun d => sameSource d.span first) &&
      overfull.any (fun d => sameSource d.span second)),
    ("each note line retains its site after the mark", noteOverfull.size == 2 &&
      noteOverfull.any (fun d => sameSource d.span first) &&
      noteOverfull.any (fun d => sameSource d.span second)),
    ("expansions at identical coordinates retain distinct origins", expansionOverfull.size == 2 &&
      expansionOverfull.any (fun d => sameSource d.span first) &&
      expansionOverfull.any (fun d => sameSource d.span expansion))]

end LeanTex.Tests.LayoutProvenance
