import Tests.Support

open LeanTex.Core

namespace Tests

/-- The selector's emitted carriers and stylesheet must agree on the same
numbered states. Zero and reversed endpoints cannot use the range fast path:
its CSS enumerates positive, ordered endpoints. Expectations are authored
finite sets, independent of the IR selector evaluator. -/
def overlayContractChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for (spec, selected, other) in
      [("0-", "1 2 3 4", ""), ("0-2", "1 2", "3 4"),
       ("0", "", "1 2 3 4"), ("2-0", "", "1 2 3 4"),
       ("4-2", "", "1 2 3 4"), ("0-,0-", "1 2 3 4", "")] do
    let source := deck169Frame
      (s!"\\uncover<{spec}>" ++ "{InkProbe} " ++
        s!"\\alt<{spec}>" ++ "{PrimaryProbe}{OtherProbe}\n\n\\uncover<4,4>{ClockMarker}")
    let (doc, ds) := elabStr source
    let out := layoutOf fonts doc
    let (head, tree, htmlDs) := HtmlDoc.emitTree {} doc
    let attrs := (elemAttrsList (fun _ => true) #[] tree.toList).map (·.2)
    let rules := artCssBlocks (treeCssList "" head.toList)
    let here := "boundary " ++ spec
    t (here ++ ": clean four-step artifact")
      ((ds ++ out.diags ++ htmlDs).all (·.severity == .note) && out.pages.size == 4)
    t (here ++ ": nonrepresentable selectors use finite CSS carriers")
      (!(attrs.any fun a => (((HtmlDoc.attrOf? a "class").getD "").splitOn " ").any fun c =>
        ["step", "step-end", "alt-crisp", "alt-pending"].contains c))
    t (here ++ ": finite cover membership")
      (attrs.any fun a => HtmlDoc.attrOf? a "class" == some "step-set" &&
        HtmlDoc.attrOf? a "data-steps" == some selected)
    t (here ++ ": finite choice partitions the numbered states")
      ((attrs.filter fun a => (((HtmlDoc.attrOf? a "class").getD "").splitOn " ").contains
        "alt-set").map (fun a => HtmlDoc.attrOf? a "data-steps") == #[some selected, some other])
    t (here ++ ": finite CSS has a reachable numbered track")
      (attrs.any fun a => HtmlDoc.attrOf? a "class" == some "slide-track")
    for k in [1, 2, 3, 4] do
      let track := s!"[data-snapped=\"{k}\"] "
      for selector in
          [s!"html[data-deck-script] {track}.step-set:not([data-steps~=\"{k}\"])",
           track ++ s!".alt-set[data-steps~=\"{k}\"]",
           track ++ s!".alt-set:not([data-steps~=\"{k}\"])"] do
        t (here ++ s!": step {k} emitted stylesheet matches its finite carrier " ++ selector)
          (rules.any fun rule => rule.1 == selector && !rule.2.isEmpty)

end Tests
