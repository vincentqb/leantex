import LeanTex.Core.Picture

open LeanTex.Core

namespace PictureContracts

private def nodeStmtAt (name : String) (x y : Int) (body : List Picture.Tok := []) :
    Picture.Stmt :=
  .node #[.sym '(', .ident name, .sym ')', .ident "at",
    .sym '(', .num x, .sym ',', .num y, .sym ')', .group body]

private def cx : Picture.Cx :=
  { pal := {}, math := fun _ _ => (.text "computed", #[]) }

private def labelText (lines : Array Picture.LabelLine) : String :=
  String.join (lines.toList.map fun line => Ir.plainText line.1)

private def boxLe (a b : Ir.Pic.Box) : Bool :=
  b.1.1 ≤ a.1.1 && b.1.2 ≤ a.1.2 && a.2.1 ≤ b.2.1 && a.2.2 ≤ b.2.2

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
    (tiny.box metric == ((0, 0), (0, 0)) &&
      p.box metric != tiny.box metric)

end PictureContracts
