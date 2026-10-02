import Tests.OverlayStyles

open LeanTex.Core

namespace Tests

/-- The selector's emitted carriers and stylesheet must agree on the same
numbered states. Zero and reversed endpoints cannot use the range fast path:
its CSS enumerates positive, ordered endpoints. Expectations are authored
finite sets, independent of the IR selector evaluator. -/
private def overlayBoundaryContractChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
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

private def contractDecl (decls key : String) : Option String :=
  (decls.splitOn ";").findSome? fun decl =>
    match decl.splitOn ":" with
    | [k, v] => if k.trimAscii.toString == key then some v.trimAscii.toString else none
    | _ => none

private def contractRule (rules : Array (String × String)) (selector key : String) :
    Option String := do
  let (_, decls) ← rules.find? (·.1 == selector)
  contractDecl decls key

private def contractIsRule (rules : Array (String × String))
    (scope compound key : String) : Option String := do
  let (_, decls) ← rules.find? fun (sel, _) =>
    sel.startsWith (scope ++ ":is(") && hasStr sel compound
  contractDecl decls key

private def contractPercent (value : String) : Option Nat := do
  if !value.endsWith "%" then none else (value.dropEnd 1).toString.toNat?

/-- Read the emitted floor rules at a numbered snap. In particular, a range's
start is reached only if its actual CSS selector names it; zero is not silently
accepted by a second numeric range model. Reduce and print overrides are not
part of this screen reading. -/
private def contractCarrier (rules : Array (String × String)) (k : Nat)
    (attrs : Array (String × String)) : Option (Bool × Nat) := do
  let classes := (styleAttr attrs "class").splitOn " "
  let track := s!".slide-track[data-snapped=\"{k}\"] "
  let snap := s!"[data-snapped=\"{k}\"] "
  let member := ((styleAttr attrs "data-steps").splitOn " ").contains (toString k)
  let start := styleAttr attrs "data-step"
  let last := styleAttr attrs "data-step-last"
  let mut opacity := 100
  if classes.contains "step-set" then
    let value ← contractRule rules
      (s!"html[data-deck-script] {snap}.step-set:not([data-steps~=\"{k}\"])") "opacity"
    let pct ← contractPercent value
    opacity := if member then 100 else pct
  if classes.contains "step" then
    if start != "1" then
      let value ← contractRule rules
        "html[data-deck-script] .step:not([data-step=\"1\"])" "opacity"
      opacity ← contractPercent value
    if let some value := contractIsRule rules track
        (s!".step[data-step=\"{start}\"]") "opacity" then
      opacity ← contractPercent value
  if classes.contains "step-end" then
    if let some value := contractIsRule rules ("html[data-deck-script] " ++ track)
        (s!".step-end[data-step-last=\"{last}\"]") "opacity" then
      opacity ← contractPercent value
  let mut display := if attrs.any (·.1 == "hidden") then "none" else "contents"
  if classes.contains "alt-set" then
    display ← contractRule rules
      (snap ++ if member then s!".alt-set[data-steps~=\"{k}\"]"
        else s!".alt-set:not([data-steps~=\"{k}\"])") "display"
  for c in ["alt-crisp", "alt-pending"] do
    if classes.contains c then
      if let some value := contractIsRule rules track
          (s!".{c}[data-step=\"{start}\"]") "display" then
        display := value
      if let some value := contractIsRule rules ("html " ++ track)
          (s!".{c}[data-step-last=\"{last}\"]") "display" then
        display := value
  if display != "none" && display != "contents" then none
    else some (display != "none", opacity)

private structure ContractLeaf where
  text : String
  opacity : Nat × Nat
  marks : Array (String × String)
  deriving Repr

mutual

private def contractHtmlOne (rules : Array (String × String)) (k : Nat)
    (opacity : Nat × Nat) (marks : Array (String × String)) (acc : Array ContractLeaf) :
    Html.Node → Option (Array ContractLeaf)
  | .text text => some (acc.push { text, opacity, marks })
  | .style _ | .script _ _ => some acc
  | .elem tag attrs kids => do
    let (shown, pct) ← contractCarrier rules k attrs
    if !shown then return acc
    let opacity := if pct == 100 then opacity else (opacity.1 * pct, opacity.2 * 100)
    let classes := (styleAttr attrs "class").splitOn " "
    let style := styleAttr attrs "style"
    let marks :=
      if ["strong", "em", "u", "s", "ul", "ol", "li"].contains tag then
        marks.push (tag, "")
      else if tag == "a" then marks.push (tag, styleAttr attrs "href")
      else if style.startsWith "color:" then marks.push ("color", style)
      else if classes.contains "alert" then marks.push ("alert", "")
      else marks
    contractHtmlList rules k opacity marks acc kids.toList

private def contractHtmlList (rules : Array (String × String)) (k : Nat)
    (opacity : Nat × Nat) (marks : Array (String × String)) (acc : Array ContractLeaf) :
    List Html.Node → Option (Array ContractLeaf)
  | [] => some acc
  | n :: ns => do
    let acc ← contractHtmlOne rules k opacity marks acc n
    contractHtmlList rules k opacity marks acc ns

end

/-- Composition witnesses have authored readings, not an evaluator of overlay
source as their oracle. Layout equality includes color and placement; the HTML
reader multiplies actual carrier opacities instead of reducing them to covered.
This does not claim the PDF's Oklab blend equals HTML's sRGB compositing. -/
def overlayContractChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  overlayBoundaryContractChecks ref fonts
  let t := check ref
  let some faces ← serifFacesSet |
    t "overlay contracts load the shipped serif quartet and math face" false
    return
  let source (body : String) := deck169Frame
    ("BeforeGuard " ++ body ++ " AfterGuard\n\n\\uncover<4,4>{ClockMarker}")
  let rulesOf (text : String) :=
    let (head, _, _) := HtmlDoc.emitTree {} (elabStr text).1
    artCssBlocks (treeCssList "" head.toList)
  let witness (label native : String) (readings : List String) (markers : List String) := do
    let (out, tree, ds) := styleBuild faces (source native)
    t (label ++ ": clean native") (ds.all (·.severity == .note))
    t (label ++ ": four pages") (out.pages.size == 4 && readings.length == 4)
    let rules := rulesOf (source native)
    for (reading, i) in readings.zipIdx do
      let (want, wantTree, wantDs) := styleBuild faces (source reading)
      let page := stylePage out i
      let control := stylePage want i
      let here := label ++ s!": step {i + 1}"
      t (here ++ " clean authored reading") (wantDs.all (·.severity == .note))
      t (here ++ " exact glyph placement and paint")
        (shippedBodyGlyphs page == shippedBodyGlyphs control)
      t (here ++ " exact decoration ink") (metricDecorationSegs page == metricDecorationSegs control)
      let actual := contractHtmlList rules (i + 1) (1, 1) #[] #[] tree.toList
      let expected := contractHtmlList (rulesOf (source reading))
        (i + 1) (1, 1) #[] #[] wantTree.toList
      t (here ++ " readable emitted script-floor CSS") (actual.isSome && expected.isSome)
      let observed := ["BeforeGuard", "AfterGuard", "ClockMarker"] ++ markers
      for marker in observed do
        let glyphs := styleGlyphs control marker
        let copies := styleCopies (source reading) marker
        t (here ++ " authored glyphs for " ++ marker)
          (glyphs.size == (if copies == 0 then 0 else marker.length) &&
            glyphs.all fun g => g.glyph > 0 && g.advance > 0 && g.size > 0)
        t (here ++ " authored multiplicity for " ++ marker)
          (styleCopies (styleText page) marker == copies &&
            styleCopies (styleText control) marker == copies)
        let found := (actual.getD #[]).filter fun leaf => styleCopies leaf.text marker > 0
        let wanted := (expected.getD #[]).filter fun leaf => styleCopies leaf.text marker > 0
        t (here ++ " HTML multiplicity for " ++ marker)
          (found.size == wanted.size && wanted.size == styleCopies (styleText control) marker)
        t (here ++ " HTML modifiers for " ++ marker)
          (found.map (·.marks) == wanted.map (·.marks))
        t (here ++ " HTML script-floor opacity for " ++ marker ++ s!" got {found.map (·.opacity)}")
          (found.size == wanted.size && (found.zip wanted).all fun (a, b) =>
            a.opacity.1 * b.opacity.2 == b.opacity.1 * a.opacity.2)
  let readerSource := source "\\uncover<2,4>{InkProbe}"
  let (_, readerTree, _) := styleBuild fonts readerSource
  let readerRules := rulesOf readerSource
  let changedRules := readerRules.map fun (sel, decls) =>
    (sel, if hasStr sel ".step-set:not" then "opacity: 7%;" else decls)
  let readInk (rules : Array (String × String)) := do
    let leaves ← contractHtmlList rules 1 (1, 1) #[] #[] readerTree.toList
    return (leaves.filter fun leaf => hasStr leaf.text "InkProbe").map (·.opacity)
  t "overlay reader sees an emitted opacity change at the same numbered state"
    ((readInk readerRules).isSome && readInk changedRules == some #[(7, 100)] &&
      readInk readerRules != readInk changedRules)
  t "overlay reader refuses a missing finite opacity rule"
    ((readInk (readerRules.filter fun (sel, _) => !hasStr sel ".step-set:not")).isNone)
  let covered (body : String) := "\\uncover<0,0>{" ++ body ++ "}"
  let paint := "\\textcolor{blue}{\\textbf{\\underline{InkProbe}}}"
  for cmd in ["only", "uncover", "visible", "onslide"] do
    witness ("nested cover " ++ cmd)
      (s!"\\{cmd}<2,4>" ++ "{\\uncover<3,4>{" ++ paint ++ "}}")
      [covered paint, covered paint, covered paint, paint] ["InkProbe"]
  witness "disjoint nested covers"
    ("\\uncover<1,3>{\\visible<2,4>{" ++ paint ++ "}}")
    [covered paint, covered paint, covered paint, covered paint] ["InkProbe"]
  witness "cover outside replacement and modifiers"
    ("\\uncover<2,4>{\\alt<1,3>" ++
      "{\\textbf<2,3>{\\alert<3,4>{\\sout<1,4>{\\textcolor<1,2>{blue}{PrimaryProbe}}}}}" ++
      "{\\underline<1,2>{OtherProbe}}}")
    [covered "\\sout{\\textcolor{blue}{PrimaryProbe}}", "\\underline{OtherProbe}",
      covered "\\textbf{\\alert{PrimaryProbe}}", "OtherProbe"]
    ["PrimaryProbe", "OtherProbe"]
  witness "replacement outside covers"
    ("\\alt<1,3>{\\uncover<2,3>{\\textit{PrimaryProbe}}}" ++
      "{\\visible<1,4>{\\sout{OtherProbe}}}")
    [covered "\\textit{PrimaryProbe}", covered "\\sout{OtherProbe}",
      "\\textit{PrimaryProbe}", "\\sout{OtherProbe}"] ["PrimaryProbe", "OtherProbe"]
  witness "nested positive ranges preserve the outer end"
    ("\\uncover<2-3>{\\visible<3-4>{" ++ paint ++ "}}")
    [covered paint, covered paint, paint, covered paint] ["InkProbe"]
  witness "positive range cover with replacement"
    "\\uncover<2-3>{\\alt<2-3>{PrimaryProbe}{OtherProbe}}"
    [covered "OtherProbe", "PrimaryProbe", "PrimaryProbe", covered "OtherProbe"]
    ["PrimaryProbe", "OtherProbe"]
  let listSource (env item body : String) :=
    "\\begin{" ++ env ++ "}\n\\item" ++ item ++ " " ++ body ++ "\n\\end{" ++ env ++ "}"
  witness "overprint item cover and modifiers"
    ("\\begin{overprint}\n\\onslide<1,3>\n" ++
      listSource "itemize" "<2,3>" "\\textbf<1,3>{PrimaryProbe}" ++
      "\n\\onslide<2,4>\n" ++
      listSource "enumerate" "<2,3>" "\\alert<1,2>{OtherProbe}" ++ "\n\\end{overprint}")
    [listSource "itemize" "<0,0>" "\\textbf{PrimaryProbe}",
      listSource "enumerate" "" "\\alert{OtherProbe}",
      listSource "itemize" "" "\\textbf{PrimaryProbe}",
      listSource "enumerate" "<0,0>" "OtherProbe"] ["PrimaryProbe", "OtherProbe"]
  for (spec, active) in
      [("0-", [true, true, true, true]), ("0-2", [true, true, false, false]),
       ("0", [false, false, false, false]), ("2-0", [false, false, false, false]),
       ("4-2", [false, false, false, false]), ("0-,0-", [true, true, true, true])] do
    witness ("boundary cover " ++ spec) (s!"\\uncover<{spec}>" ++ "{" ++ paint ++ "}")
      (active.map fun selected => if selected then paint else covered paint) ["InkProbe"]
    witness ("boundary choice " ++ spec) (s!"\\alt<{spec}>" ++ "{PrimaryProbe}{OtherProbe}")
      (active.map fun selected => if selected then "PrimaryProbe" else "OtherProbe")
      ["PrimaryProbe", "OtherProbe"]

end Tests
