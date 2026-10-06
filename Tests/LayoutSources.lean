import Tests.Support
import Tests.LayoutProvenance
import Tests.LayoutContracts

open LeanTex.Core LeanTex.Cli

private def sameOpening (actual : Option Span) (expected : Span) : Bool :=
  actual.any fun a =>
    a == expected && a.pos.origins == expected.pos.origins &&
      a.pos.command == expected.pos.command

/-- Source sites follow the actual document through citation removal and
backend filtering. Two identical frames expose using an ordinal or a stale
block index instead of the opening that produced the overflowing page. -/
def layoutSourceChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  for (name, ok) in LeanTex.Tests.LayoutProvenance.frameSourceChecks fs do
    t ("layout source: " ++ name) ok
  for (name, ok) in LeanTex.Tests.LayoutProvenance.overfullSourceChecks fs do
    t ("layout source: " ++ name) ok
  for (name, ok) in LeanTex.Tests.LayoutContracts.counterexamples fs do
    t ("layout contract: " ++ name) ok
  let body := String.intercalate "\n\n" (List.replicate 24 "Frame body.")
  let frame := "\\begin{frame}{Same frame}\n" ++ body ++ "\n\\end{frame}\n"
  let text := "\\documentclass{beamer}\n\\begin{document}\n\\nocite{*}\n\n" ++
    frame ++ "\\nocite{*}\n\n" ++ frame ++ "\\end{document}\n"
  let file := "citation-frame-sources.tex"
  let raws := (Parse.parse file (Lex.lex file text).1).1
  let prepared := Elab.prepare file raws
  let geom : Layout.Geom := {
    pageW := Dim.pt 220, pageH := Dim.pt 120
    hmargin := Dim.pt 12, vmargin := Dim.pt 12, fontSize := Dim.pt 10
    hyphenate := false, justify := false }
  for withdrawn in [#[], #["unused-picture"]] do
    let (doc, _, sites) := Elab.runPrepared file prepared (picWithdrawn := withdrawn)
    let (resolved, _) := Bib.apply #[] doc
    let remapped := Bib.remapSources doc sites.frames
    let out := Layout.run geom fs none resolved
      (frameSpans := Layout.frameSpansForPdf resolved remapped)
    let spills := (out.diags.map prepared.sourceTriggers.attribute).filter (·.kind == .W0384)
    t "citation removal really changes the top-level block indices"
      (resolved.body.size + 2 == doc.body.size && sites.frames.size == 2)
    t "the source probe really overflows both identical frames"
      (out.pages.size > 2 && spills.size == 2)
    for (_, site) in sites.frames do
      t s!"citation removal preserves opening line {site.pos.line} through actual layout"
        (spills.any fun d => sameOpening d.span site && d.trigger == some "\\begin")
