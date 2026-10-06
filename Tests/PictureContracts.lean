import Tests.Support

open LeanTex.Core

namespace PictureContracts

private def nodeStmtAt (name : String) (x y : Int) (body : List Picture.Tok := []) :
    Picture.Stmt :=
  .node #[.sym '(', .ident name, .sym ')', .ident "at",
    .sym '(', .num x, .sym ',', .num y, .sym ')', .group body]

private def relative (name target direction : String) : Picture.Stmt :=
  .node #[.sym '[', .ident direction, .sym '=', .ident "of", .ident target, .sym ']',
    .sym '(', .ident name, .sym ')', .group []]

private def cx : Picture.Cx :=
  { pal := {}, math := fun _ _ => (.text "computed", #[]) }

private def labelText (lines : Array Picture.LabelLine) : String :=
  String.join (lines.toList.map fun line => Ir.plainText line.1)

private def boxLe (a b : Ir.Pic.Box) : Bool :=
  b.1.1 ≤ a.1.1 && b.1.2 ≤ a.1.2 && a.2.1 ≤ b.2.1 && a.2.2 ≤ b.2.2

private def nodeBox (g : Picture.NodeGeom) : Ir.Pic.Box :=
  ((g.x - g.a, g.y - g.b), (g.x + g.a, g.y + g.b))

/-- Counterexamples to overbroad contracts: overlapping writes are
ordered, literal punctuation is content, and math elaboration supplies
its own character provenance. These exercise the actual public readers. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let check (name : String) (ok : Bool) :=
    unless ok do ref.modify (name :: ·)
  let a := nodeStmtAt "n" 0 0
  let b := nodeStmtAt "n" 2000 3000
  let ab := Picture.evalFixed cx [a, b]
  let ba := Picture.evalFixed cx [b, a]
  check "picture duplicate names retain the last declaration"
    (ab.nodes.lookup "n" != ba.nodes.lookup "n" &&
      (ab.nodes.lookup "n").map (·.x) == some (cx.toSp 2000) &&
      (ba.nodes.lookup "n").map (·.x) == some 0)
  check "picture literal punctuation is label content"
    (labelText (Picture.nodeLabel cx [] [.sym '[', .ident "x", .sym ']']).1 == "[x]")
  check "picture math content comes from its elaborator"
    (labelText (Picture.nodeLabel cx [] [.math false []]).1 == "computed")
  let inputs := Picture.labelInputList
    [("value", .str "bound"), ("value", .str "shadowed"), ("unused", .str "unreferenced")]
    #[] [.sym '[', .num (-1250), .group [.ctrl "value", .math true []],
      .ctrl "unbound", .other "parser-marker"]
  check "picture source census retains typed tokens and the selected declaration"
    (inputs == #[.literal (.symbol '['), .literal (.number (-1250)),
      .substitution "value" (.str "bound"), .math true []])
  check "picture source census neither echoes controls nor imports unused declarations"
    (Picture.labelSources cx [("unused", .str "unreferenced")]
      [.ctrl "unbound", .other "parser-marker"] == "")
  check "picture empty source does not manufacture the floor"
    (let (ls, ds) := Picture.nodeLabel cx [] []
     labelText ls == "" && ds.isEmpty)
  check "picture generated floor is absent from the independent source census"
    (let ts := [Picture.Tok.ctrl "unbound"]
     let (ls, ds) := Picture.nodeLabel cx [] ts
     Picture.labelSources cx [] ts == "" &&
       labelText ls == Picture.LabelGenerated.nodeFloor.text && !ds.isEmpty)
  let styledCx : Picture.Cx :=
    { cx with
      pal := ({} : Ir.Palette).declare "accent" Ir.Color.black
      argStyles := [("textbf", .bold), ("emph", .emph)] }
  let nested := Picture.nodeLabel styledCx [("value", .str "bound")]
    [.ctrl "textbf", .group [.ident "outer", .space, .ctrl "textcolor",
      .group [.ident "accent"], .group [.ident "inner"], .space, .ctrl "value",
      .space, .math false []]]
  check "picture nested styles preserve body and elaborated math"
    (labelText nested.1 == "outer inner bound computed" && nested.2.isEmpty)
  let discarded := Picture.nodeLabel styledCx []
    [.ident "before", .space, .ctrl "hspace", .sym '*',
      .group [.ident "not-label-content"], .ctrl "emph", .group [.ident "after"]]
  check "picture recovery discards names without discarding readable arguments"
    (labelText discarded.1 == "before after" && !discarded.2.isEmpty)
  let broken := Picture.nodeLabel styledCx [] [.ctrl "textcolor", .group [.ident "accent"]]
  check "picture incomplete color body is named and has its declared floor"
    (labelText broken.1 == Picture.nodeFloorPlaceholder && !broken.2.isEmpty)
  let multiline := Picture.nodeLabel styledCx []
    [.ctrl "textbf", .group [.ident "first", .ctrl "\\", .ident "second"]]
  check "picture styled splice retains both readable lines"
    (multiline.1.size == 2 &&
      multiline.1.toList.map (fun l => Ir.plainText l.1) == ["first", "second"])
  let metric : Ir.Pic.LabelMetric := fun _ _ =>
    { w := 100, height := 40, depth := 10, boxHeight := 35, boxDepth := 8 }
  let measured := Picture.evalFixed { cx with metric } [nodeStmtAt "n" 0 0 [.ident "text"]]
  let p := measured.toPicture
  check "picture measured node emits a label" (p.shapes.size == 1)
  check "picture reserves measured label ink"
    (p.shapes.all fun s => match s with
      | .label x y content _ scale align =>
        boxLe (Ir.Pic.labelTextBox x y align (metric content scale)) (p.box metric)
      | _ => true)
  let tiny := { p with declared := some ((0, 0), (0, 0)) }
  check "picture explicit bounding box remains authoritative"
    (tiny.box metric == (((0, 0), (0, 0)) : Ir.Pic.Box) &&
      p.box metric != tiny.box metric)
  -- The queued node-border claim quantified over an unrelated metric.
  -- Its lookup, emitted-label and equal-anchor hypotheses all hold here.
  let unrelated : Ir.Pic.LabelMetric := fun _ _ =>
    { w := 1000000000, height := 40, depth := 10 }
  match measured.nodes.lookup "n" with
  | some g =>
    check "picture extent requires the metric that resolved the node"
      (measured.shapes.any fun s => match s with
        | .label x y content _ scale align =>
          x == g.x && y == g.y &&
            !boxLe (Ir.Pic.labelInkBox x y align (unrelated content scale)) (nodeBox g)
        | _ => false)
  | none => check "picture extent counterexample emits its node" false
  -- Equal coordinates do not identify which node owns a label: two named
  -- nodes can share an anchor while reserving different measured widths.
  let varying : Ir.Pic.LabelMetric := fun content _ =>
    { w := if Ir.plainText content == "wide" then 1000000000 else 100
      height := 40, depth := 10, boxHeight := 35, boxDepth := 8 }
  let coincident := Picture.evalFixed { cx with metric := varying }
    [node "small" 0 0 [.ident "small"], node "wide" 0 0 [.ident "wide"]]
  match coincident.nodes.lookup "small" with
  | some g =>
    check "picture equal anchors do not establish label ownership"
      (coincident.shapes.any fun s => match s with
        | .label x y content _ scale align =>
          x == g.x && y == g.y && Ir.plainText content == "wide" &&
            !boxLe (Ir.Pic.labelInkBox x y align (varying content scale)) (nodeBox g)
        | _ => false)
  | none => check "picture ownership counterexample emits its node" false
  let directions : Array (String × Picture.Dir) :=
    #[("left", .left), ("right", .right), ("above", .above), ("below", .below),
      ("above left", .aboveLeft), ("above right", .aboveRight),
      ("below left", .belowLeft), ("below right", .belowRight)]
  for (name, dir) in directions do
    let root := nodeStmtAt "root" 3000 (-5000)
    let p := relative "p" "root" name
    let q := nodeStmtAt "q" 7000 9000
    let before := Picture.evalFixed cx [root, p, q]
    let after := Picture.evalFixed cx [root, q, p]
    let forward := Picture.evalFixed cx [p, root, q]
    check s!"picture independent source placements commute: {name}"
      (["root", "p", "q"].all fun n => before.nodes.lookup n == after.nodes.lookup n)
    check s!"picture forward reference resolves: {name}"
      (before.nodes.lookup "p" == forward.nodes.lookup "p")
    match before.nodes.lookup "root", before.nodes.lookup "p" with
    | some g, some placed =>
      let plan : Picture.NodePlan :=
        { name := some "p", placement := .relative dir "root" cx.dist
          shape := { placed with x := 0, y := 0, base := placed.base - placed.y } }
      check s!"picture emission uses the measured placement resolver: {name}"
        ((plan.run [("root", g)]).1.toOption == some placed)
    | _, _ => check s!"picture source placement emits both nodes: {name}" false
  let missing := Picture.evalFixed cx [relative "p" "absent" "right"]
  check "picture missing references stay unregistered and diagnosed"
    (missing.nodes.lookup "p" == none && !missing.diags.isEmpty)
  let dependency := relative "p" "root" "right"
  let old := node "root" 0 0
  let replacement := node "root" 9000 0
  check "picture placements that read the other write are order dependent"
    ((Picture.evalFixed cx [old, dependency, replacement]).nodes.lookup "p" !=
      (Picture.evalFixed cx [old, replacement, dependency]).nodes.lookup "p")

/-- Provenance witnesses must survive actual placement and both artifact
trees. The math callback intentionally supplies text absent from its raw
input, and the substitution supplies text absent from its control name.
The expected page content is written independently of the source census. -/
def provenanceRenderChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let metric := Layout.labelMetric geom fonts
  let measuredCx : Picture.Cx := {
    cx with
    metric
    pal := ({} : Ir.Palette).declare "accent" Ir.Color.black
    argStyles := [("textbf", .bold), ("emph", .emph)]
    math := fun display _ =>
      (.styled .italic #[.text (if display then "[DISPLAY]" else "[math]")], #[]) }
  let cases : Array (String × List Picture.Tok × Array String × Bool) := #[
    ("literal brackets", [.sym '[', .ident "source", .sym ']'], #["[source]"], false),
    ("declared substitution", [.ctrl "textbf", .group [.ctrl "value"]], #["Bound"], false),
    ("arbitrary math output", [.math true [], .space, .math false []],
      #["[DISPLAY] [math]"], false),
    ("nested style and color", [.ctrl "textbf", .group [
      .ident "first", .ctrl "\\", .math false [], .ctrl "textcolor",
      .group [.ident "accent"], .group [.ident "last"]]], #["first", "[math]last"], false),
    ("discarded naming argument", [.ident "kept", .ctrl "ref", .group [.ident "not-shipped"]],
      #["kept"], true),
    ("generated floor", [.ctrl "unbound"], #[Picture.nodeFloorPlaceholder], true),
    ("incomplete color", [.ctrl "textcolor", .group [.ident "accent"]],
      #[Picture.nodeFloorPlaceholder], true),
    ("deliberately invisible", [.ctrl "phantom", .group [.ident "not-shipped"]], #[], false)]
  let alignments : Array (String × Ir.Pic.LabelAlign) :=
    #[("center", .center), ("west", .west), ("east", .east), ("north", .north), ("south", .south)]
  for (name, body, expected, named) in cases do
    let (labels, ds) := Picture.nodeLabel measuredCx [("value", .str "Bound")] body
    t s!"picture provenance: {name} accounts for its loss" ((!ds.isEmpty) == named)
    for (side, align) in alignments do
      for scale in #[650, 1000, 1750] do
        let pic : Ir.Pic.Picture := {
          shapes := Picture.stackLabels (Dim.pt 13) (Dim.pt (-4)) geom.fontSize
            scale Ir.Color.black align labels #[] }
        let doc : Ir.Doc := {
          body := #[.picture pic]
          tokens := ({} : Ir.Tokens).declare "topskip" {} }
        let lines := (bodyLines (layoutOf fonts doc geom)).filter hasGlyphRun
        let html := HtmlDoc.pictureSvg { labelMetric := metric } pic
        let name := s!"picture provenance: {name}/{side}/{scale}"
        t (name ++ " ships the independently expected native lines")
          (lines.map lineText == expected)
        t (name ++ " ships the same visible SVG text")
          (shownTextOne "" html == String.join expected.toList)
        t (name ++ " preserves the SVG line partition")
          ((elemAttrsOne (· == "text") #[] html).size == expected.size)

end PictureContracts
