import Tests.Artifact

open LeanTex.Core

namespace Tests

private def roleLeafGlyphText (out : Layout.Out) (id : Nat) : String :=
  (bodyLines out).foldl (fun s line =>
    line.segs.foldl (fun s seg => match seg with
      | .run _ _ _ _ gs _ _ _ _ _ (.leaf k) =>
        if k == id then gs.foldl (fun s (_, c, _) => s.push c) s else s
      | _ => s) s) ""

/-- Semantic roles can split a word's structure leaves, but do not change
its shaping or legal hyphenation points. Compare the actual shipped glyphs;
also hold each leaf's ink to its own census so joining words cannot erase
the attribution that tagged PDF reads. Styled controls keep their faces. -/
def roleShapingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let artifact (fonts : Font.FontSet) (label : String) (doc : Ir.Doc) (out : Layout.Out)
      (geom : Layout.Geom) : IO Unit := do
    let laid := out.pages.flatMap fun p =>
      artLaidGlyphs geom { p with lines := p.lines.filter (!·.furniture) }
    t (label ++ ": exact artifact-model coordinates")
      ((shippedBodyGlyphs out).map (fun g => g.x + geom.bleed) == laid)
    match readArtifact (driverPdf fonts geom doc out) with
    | .error e => t s!"{label}: PDF reads back: {e}" false
    | .ok pages =>
      let offences := artGlyphPlacementOffences
        (out.pages.flatMap (artLaidGlyphs geom)) (pages.flatMap artPaintedGlyphs)
      t s!"{label}: emitted PDF pen agrees: {offences.toList.take 3}"
        (!laid.isEmpty && pages.size == out.pages.size && offences.isEmpty)
  for (name, xs, text) in (#[
      ("word remainder", #[.role "wordrole" #[.text "A"], .text "B Tail"], "AB Tail"),
      ("adjacent roles", #[.role "one" #[.text "A"], .role "two" #[.text "B"],
        .text "Tail"], "ABTail"),
      ("nested roles", #[.role "outer" #[.text "(",
        .role "inner" #[.text "(X)"], .text ")"], .text "Tail"], "((X))Tail"),
      ("large kern", #[.role "one" #[.text "A"], .role "two" #[.text "V"]], "AV"),
      ("plain leaves", #[.text "A", .text "B", .text "Tail"], "ABTail"),
      ("space boundary", #[.role "one" #[.text "A "], .role "two" #[.text "V"]], "A V")
    ] : Array (String × Array Ir.Inline × String)) do
    let doc : Ir.Doc := { body := #[.para xs] }
    let out := layoutOf fonts doc
    let control := { doc with body := #[.para #[.text text]] }
    let plain := layoutOf fonts control
    t s!"role shaping {name}: exact shipped glyphs"
      (shippedBodyGlyphs out == shippedBodyGlyphs plain)
    t s!"role shaping {name}: no layout loss" (out.diags.isEmpty && plain.diags.isEmpty)
    artifact fonts s!"role shaping {name}" doc out (Layout.Geom.ofPage doc.page)
    artifact fonts s!"role shaping {name} control" control plain (Layout.Geom.ofPage control.page)
    for (id, leaf) in (Struct.ofDoc doc).leaves do
      t s!"role shaping {name}: leaf {id} keeps its ink"
        (roleLeafGlyphText out id == leaf.census.replace " " "")
  let some styleFonts ← serifFacesSet | t "role shaping: serif faces load" false
  let styled : Ir.Doc := { body := #[.para #[
    .role "one" #[.styled .bold #[.text "A"]],
    .role "two" #[.text "V"]]] }
  let control := { styled with body := #[.para #[.styled .bold #[.text "A"], .text "V"]] }
  let bare := { styled with body := #[.para #[.text "AV"]] }
  let out := layoutOf styleFonts styled
  t "role shaping: authored style survives annotation"
    (shippedBodyGlyphs out == shippedBodyGlyphs (layoutOf styleFonts control))
  t "role shaping: authored style still changes the page"
    (shippedBodyGlyphs out != shippedBodyGlyphs (layoutOf styleFonts bare))
  t "role shaping: distinct faces remain distinct"
    (bodyGlyphs out == #[(1, 'A'), (0, 'V')])
  artifact styleFonts "role shaping styled" styled out (Layout.Geom.ofPage styled.page)
  let hyphenated : Ir.Doc := { body := #[.para #[
    .role "one" #[.text "al"], .role "two" #[.text "gorithm"]]] }
  let joined := { hyphenated with body := #[.para #[.text "algorithm"]] }
  let geom : Layout.Geom := {
    pageW := Dim.pt 190, hmargin := Dim.pt 80, expand := false, protrude := false }
  let pats := some (Hyphen.load' "" "al-go-rithm" 2 3)
  let splitOut := Layout.run geom fonts pats hyphenated
  let joinedOut := Layout.run geom fonts pats joined
  t "role shaping: control really hyphenates"
    ((bodyLines joinedOut).size > 1 &&
      (bodyGlyphs joinedOut).any (fun (_, c) => c == '-'))
  t "role shaping: hyphenation crosses semantic boundaries"
    (shippedBodyGlyphs splitOut == shippedBodyGlyphs joinedOut)
  artifact fonts "role shaping hyphenated" hyphenated splitOut geom
  artifact fonts "role shaping hyphenated control" joined joinedOut geom
  -- Expansion rounds whole-word coordinates. Changing the structure leaves
  -- must not restart that rounding, even inside a leaf with several glyphs.
  for (name, parts, hanging) in (#[
      ("scalar leaves", #["A", "B", "T", "a", "i", "l"], false),
      ("long leaves", #["AB", "Tail"], false),
      ("no kern", #["M", "MMMM"], false),
      ("hanging indent", #["A", "B", "Tail"], true)
    ] : Array (String × Array String × Bool)) do
    let body (xs : Array Ir.Inline) : Array Ir.Block :=
      if hanging then #[.list false #[#[.para
        (#[.role Ir.descLabelRole #[.text "Term "]] ++ xs)]]]
      else #[.para xs]
    let mut xs : Array Ir.Inline := #[]
    let mut text := ""
    for _ in [0:20] do
      for part in parts do
        xs := xs.push (.role "semantic" #[.text part])
        text := text ++ part
      xs := xs.push (.text " ")
      text := text ++ " "
    for measure in [300, 400] do
      let doc : Ir.Doc := {
        page := { width := Dim.pt (measure + 40), hmargin := Dim.pt 20,
                  expand := some true, protrude := some false }
        body := body xs }
      let out := layoutOf fonts doc
      let control := { doc with body := body #[.text text] }
      let plain := layoutOf fonts control
      let label := s!"role shaping {name}, measure {measure}"
      t (label ++ ": control really expands")
        ((bodyLines plain).any (·.expand != 0))
      if hanging then
        t (label ++ ": control really hangs")
          (match (bodyLines plain)[0]?, (bodyLines plain)[1]? with
            | some first, some continuation => first.x < continuation.x
            | _, _ => false)
      t (label ++ ": exact expanded glyphs") (shippedBodyGlyphs out == shippedBodyGlyphs plain)
      t (label ++ ": exact line extents")
        ((bodyLines out).map (fun l => (l.x, l.y, l.setWidth, l.expand)) ==
          (bodyLines plain).map (fun l => (l.x, l.y, l.setWidth, l.expand)))
      t (label ++ ": no layout loss") (out.diags.isEmpty && plain.diags.isEmpty)
      artifact fonts label doc out (Layout.Geom.ofPage doc.page)
      artifact fonts (label ++ " control") control plain (Layout.Geom.ofPage control.page)
      for (id, leaf) in (Struct.ofDoc doc).leaves do
        t s!"{label}: leaf {id} keeps its ink"
          (roleLeafGlyphText out id == leaf.census.replace " " "")

end Tests
