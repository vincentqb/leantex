module

public import LeanTex.Core.Font
import LeanTex.Core.Layout
import LeanTex.Core.HtmlDoc
import LeanTex.Core.BeamerColor
import LeanTex.Core.Elab
import LeanTex.Core.SeedPalette

open LeanTex.Core

namespace Tests.BlockBody

private def ink : Ir.Color := { r := 230, g := 240, b := 250 }
private def ground : Ir.Color := { r := 20, g := 35, b := 50 }

private def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

private def lineText (line : Layout.LineOut) : String :=
  String.ofList (line.segs.toList.flatMap Layout.Seg.glyphChars)

/-- Keep each element's declarations separate: backgrounds do not inherit,
and two declarations on one box do not witness two nested surfaces. -/
private structure HtmlElement where
  tag : String
  styles : String
  bodyBox : Bool

private structure HtmlInk where
  text : String
  ancestors : List HtmlElement -- nearest element first
  bodyBox : Bool := false

private def cssProperty (styles name : String) : Option String :=
  (styles.splitOn ";").foldl (fun value decl =>
    match decl.splitOn ":" with
    | [key, val] => if key.trimAscii.toString == name then some val.trimAscii.toString else value
    | _ => value) none

mutual
  private def htmlInks (ancestors : List HtmlElement) (out : Array HtmlInk) :
      List Html.Node → Array HtmlInk
    | [] => out
    | node :: rest => htmlInks ancestors (htmlInk ancestors out node) rest
  private def htmlInk (ancestors : List HtmlElement) (out : Array HtmlInk) :
      Html.Node → Array HtmlInk
    | .text text => out.push { text, ancestors }
    | .elem tag attrs kids =>
      let own := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      let bodyBox := attrs.contains ("class", "block-body")
      let ancestors := { tag, styles := own, bodyBox : HtmlElement } :: ancestors
      let out := if bodyBox then
          out.push { text := "", ancestors, bodyBox := true }
        else out
      htmlInks ancestors out kids.toList
    | .style _ | .script .. => out
end

/-- Nearest explicit inline colour, in the emitted declaration format.
This reads inline ownership, not the browser's full stylesheet cascade. -/
private def HtmlInk.inlineColor (leaf : HtmlInk) : Option String :=
  leaf.ancestors.findSome? (fun elem => cssProperty elem.styles "color")

private def HtmlInk.bodyProperty (leaf : HtmlInk) (name : String) : Option String :=
  (leaf.ancestors.find? (·.bodyBox)).bind (fun elem => cssProperty elem.styles name)

/-- Epoch paint belongs on the paragraph/pre containing the text. Ancestor
ink alone cannot stand in for it: a normal stylesheet rule on the child
outranks inherited ink. Descendant inline ink must agree too. This contract
does not compute arbitrary selectors or stylesheet `!important` overrides. -/
private def HtmlInk.epochPaint (leaf : HtmlInk) (tag color : String) : Bool :=
  match leaf.ancestors.find? (fun elem => elem.tag == "p" || elem.tag == "pre") with
  | some owner => owner.tag == tag && cssProperty owner.styles "color" == some color &&
    leaf.inlineColor == some color
  | none => false

private def HtmlInk.nestedPaint (leaf : HtmlInk) (outer inner color : String) : Bool :=
  match leaf.ancestors.filter (·.bodyBox) with
  | innerBox :: outerBox :: [] =>
    cssProperty outerBox.styles "background" == some outer &&
    cssProperty innerBox.styles "background" == some inner &&
    leaf.inlineColor == some color
  | _ => false

private def HtmlInk.paddedBand (leaf : HtmlInk) (background padding : String) : Bool :=
  leaf.bodyBox && leaf.bodyProperty "background" == some background &&
    leaf.bodyProperty "padding" == some padding

/-- Break the witnesses themselves: declaration presence cannot substitute
for the owning element or the actual ancestor relationship. -/
private def htmlWitnessChecks (ref : IO.Ref (List String)) : IO Unit := do
  let body (styles : String) (kids : Array Html.Node) : Html.Node :=
    .elem "div" #[("class", "block-body"), ("style", styles)] kids
  let inner := body "background: #223344; color: #ffffff;" #[.text "NESTED"]
  let nestedAccepts (nodes : List Html.Node) :=
    (htmlInks [] #[] nodes).any fun leaf =>
      leaf.text == "NESTED" && leaf.nestedPaint "#ddeeff" "#223344" "#ffffff"
  for (name, nodes, expected) in #[
      ("distinct nested surfaces", [body "background: #ddeeff;" #[inner]], true),
      ("collapsed backgrounds", [body
        "background: #ddeeff; background: #223344; color: #ffffff;" #[.text "NESTED"]], false),
      ("overwritten outer background",
        [body "background: #ddeeff; background: #223344;" #[inner]], false),
      ("sibling surfaces", [body "background: #ddeeff;" #[], inner], false)] do
    check ref ("block body HTML witness: " ++ name) (nestedAccepts nodes == expected)
  let epochAccepts (styles : String) (child : Html.Node) :=
    (htmlInks [] #[] [
      .style "p { color: #004080; }",
      .elem "section" #[("style", "color: #804000;")]
        #[.elem "p" #[("style", styles)] #[child]]]).any fun leaf =>
      leaf.text == "AFTER" && leaf.epochPaint "p" "#804000"
  for (name, styles, child, expected) in #[
      ("owned epoch paint", "color: #804000;", Html.Node.text "AFTER", true),
      ("ancestor-only epoch paint", "", .text "AFTER", false),
      ("overwritten epoch paint", "color: #804000; color: #004080;", .text "AFTER", false),
      ("descendant inline override", "color: #804000;",
        .elem "span" #[("style", "color: #004080;")] #[.text "AFTER"], false)] do
    check ref ("block body HTML witness: " ++ name) (epochAccepts styles child == expected)
  let paddedAccepts (styles : String) :=
    (htmlInks [] #[] [.elem "section"
      #[("style", "background: #223344; padding: 0.5em;")] #[body styles #[]]]).any
      (fun leaf => leaf.paddedBand "#223344" "0.5em")
  for (name, styles, expected) in #[
      ("owned empty band", "background: #223344; padding: 0.5em;", true),
      ("ancestor-only empty band", "", false),
      ("ancestor-only empty background", "padding: 0.5em;", false),
      ("ancestor-only empty padding", "background: #223344;", false)] do
    check ref ("block body HTML witness: " ++ name) (paddedAccepts styles == expected)

private def probe (kind : Ir.TitledKind) (title : Array Ir.Inline) : Ir.Doc :=
  { palette := { entries := #[
      ("fg", Ir.Color.black), ("bg", Ir.Color.white),
      (kind.name ++ "bodyfg", ink), (kind.name ++ "bodybg", ground)] }
    body := #[.titled kind title #[.para #[.text "BODY"]]] }

private def layout (fonts : Font.FontSet) (doc : Ir.Doc) : Layout.Out :=
  Layout.run (Layout.Geom.ofPage doc.page) fonts none doc

private def html (doc : Ir.Doc) : Array HtmlInk :=
  let (_, nodes, _) := HtmlDoc.emitTree {} doc
  htmlInks [] #[] nodes.toList

/-- Exercise the exported source through the real front end and both
artifacts. A correct palette or an isolated IR renderer cannot stand in
for the bindings between them. Footer ink is declared too: changing the
page polarity must not inherit the opening theme's small-text colour. -/
private def generatedSourceChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let dark : Ir.Color := { r := 25, g := 42, b := 61 }
  let accent : Ir.Color := { r := 196, g := 106, b := 119 }
  for (foreground, paper) in [(dark, Ir.Color.white), (Ir.Color.white, dark)] do
    let seeds : SeedPalette.Seeds := ⟨foreground, paper, accent⟩
    let some palette := SeedPalette.generate seeds
      | check ref "generated block source: palette exists" false
        continue
    for env in ["block", "alertblock", "exampleblock"] do
      for title in ["", "TITLE"] do
        let source := "\\documentclass{beamer}" ++
          SeedPalette.beamerDeclarations "sample" seeds palette ++
          "\\setbeamercolor{normal text}{fg=sampleInk,bg=samplePaper}" ++
          "\\setbeamercolor{footline}{fg=sampleMuted,bg=samplePaper}" ++
          "\\begin{document}\\begin{frame}" ++
          "\\begin{" ++ env ++ "}{" ++ title ++ "}BODY\\end{" ++ env ++ "}" ++
          "\\end{frame}\\end{document}"
        let (doc, diags) := Elab.run "generated.tex" source
        let label := s!"generated block {paper.css}/{env}/{title}"
        check ref (label ++ ": clean source") (diags.all (·.severity == .note))
        let out := layout fonts doc
        let body := out.pages.flatMap (·.lines) |>.filter (lineText · == "BODY")
        check ref (label ++ ": content survives once") (body.size == 1)
        check ref (label ++ ": PDF ink and ground")
          (body.any fun line => line.segs.any fun
            | .run _ c _ _ _ _ _ _ _ g _ =>
              c == seeds.ink && g == some palette.colors.surface
            | _ => false)
        check ref (label ++ ": PDF enclosing surface")
          (out.pages.any fun page => page.lines.any fun line =>
            lineText line == "BODY" && page.fills.any fun fill =>
              fill.color == palette.colors.surface && fill.x ≤ line.x &&
              line.x + line.setWidth ≤ fill.x + fill.w &&
              fill.y < line.y && line.y < fill.y + fill.h)
        check ref (label ++ ": HTML ink and surface")
          ((html doc).any fun leaf => leaf.text == "BODY" &&
            leaf.inlineColor == some seeds.ink.css &&
            leaf.bodyProperty "background" == some palette.colors.surface.css)

/-- These four small documents hold the reviewed artifact counterexamples:
epochs must replace inherited concrete ink, nesting owes every inset, empty
paint has area, and padding participates in fitting on every spill page. -/
private def regionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let blue : Ir.Color := { r := 0, g := 64, b := 128 }
  let brown : Ir.Color := { r := 128, g := 64, b := 0 }
  let pale : Ir.Color := { r := 221, g := 238, b := 255 }
  let dark : Ir.Color := { r := 34, g := 51, b := 68 }
  let pal : Ir.Palette := { entries := #[
    ("fg", Ir.Color.black), ("bg", Ir.Color.white), ("blockbodyfg", blue)] }
  let epoch : Ir.Doc := { palette := pal, body := #[.titled .block #[] #[
    .para #[.text "BEFORE"],
    .setPalette { pal with entries := pal.entries.map fun (key, c) =>
      (key, if key == "fg" then brown else c) },
    .para #[.text "AFTER", .math false "x"], .verbatim none "CODE" {}]] }
  let leaves := html epoch
  for (text, tag) in #[("AFTER", "p"), ("x", "p"), ("CODE", "pre")] do
    check ref s!"block body epoch: HTML {text} replaces concrete ink"
      (leaves.any fun leaf => leaf.text == text && leaf.epochPaint tag brown.css)
  check ref "block body epoch: PDF replacement ink"
    ((layout fonts epoch).pages.any fun page => page.lines.any fun line =>
      (lineText line).contains "AFTER" && line.segs.any fun
        | .run _ c _ _ _ _ _ _ _ _ _ => c == brown
        | _ => false)
  let nested : Ir.Doc := {
    palette := { entries := #[
      ("fg", Ir.Color.black), ("bg", Ir.Color.white),
      ("blockbodybg", pale), ("examplebodybg", dark), ("examplebodyfg", Ir.Color.white)] }
    body := #[.titled .block #[] #[.titled .example #[] #[.para #[.text "NESTED"]]]] }
  let pad := Ir.titledPadding.resolve nested.page.fontSize 0
  check ref "block body nested: PDF outer includes inner padding"
    ((layout fonts nested).pages.any fun page => page.fills.any fun outer =>
      outer.color == pale && page.fills.any fun inner =>
        inner.color == dark && outer.x + pad ≤ inner.x &&
        outer.y + pad ≤ inner.y &&
        inner.x + inner.w + pad ≤ outer.x + outer.w &&
        inner.y + inner.h + pad ≤ outer.y + outer.h)
  check ref "block body nested: HTML both surfaces enclose content"
    ((html nested).any fun leaf => leaf.text == "NESTED" &&
      leaf.nestedPaint pale.css dark.css Ir.Color.white.css)
  let empty : Ir.Doc := {
    palette := { entries := #[
      ("fg", Ir.Color.black), ("bg", Ir.Color.white), ("blockbodybg", dark)] }
    body := #[.para #[.text "BEFORE"], .titled .block #[] #[], .para #[.text "AFTER"]] }
  check ref "block body empty: PDF nonzero band between paragraphs"
    ((layout fonts empty).pages.any fun page => page.fills.any fun fill =>
      fill.color == dark && fill.h ≥ 2 * pad &&
        page.lines.any (fun line => lineText line == "BEFORE" && line.y < fill.y) &&
        page.lines.any (fun line => lineText line == "AFTER" && fill.y + fill.h < line.y))
  check ref "block body empty: HTML padded band"
    ((html empty).any fun leaf =>
      leaf.paddedBand dark.css (HtmlDoc.cssLength Ir.titledPadding))
  let spill : Ir.Doc := {
    page := {
      width := Dim.pt 200, height := Dim.pt 100, hmargin := Dim.pt 10
      vmargin := Dim.pt 1, fontSize := Dim.pt 10 }
    palette := { entries := #[
      ("fg", Ir.Color.black), ("bg", Ir.Color.white), ("blockbodybg", pale)] }
    body := #[.titled .block #[] ((List.range 24).map fun i =>
      Ir.Block.para #[.text s!"LINE{i}"]).toArray] }
  let out := layout fonts spill
  check ref "block body spill: every padded fragment is inside the medium"
    (out.pages.size > 1 && out.pages.all fun page =>
      let fills := page.fills.filter (·.color == pale)
      fills.size == 1 && fills.all fun fill =>
        0 ≤ fill.x && 0 ≤ fill.y && fill.x + fill.w ≤ spill.page.width &&
        fill.y + fill.h ≤ spill.page.height)
  check ref "block body spill: every line survives once"
    ((List.range 24).all fun i =>
      (out.pages.flatMap (·.lines) |>.filter (lineText · == s!"LINE{i}")).size == 1)

/-- Filled titled bodies ship their declared ink and an enclosing surface
on both artifacts, for every kind and with or without a title. These are
artifact assertions; resolving a role in the IR alone cannot pass them. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  htmlWitnessChecks ref
  for kind in #[Ir.TitledKind.block, .alert, .example] do
    for title in #[#[], #[Ir.Inline.text "TITLE"]] do
      let doc := probe kind title
      let label := s!"block body {kind.name}/{title.size}"
      let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
      let lines := out.pages.flatMap (·.lines) |>.filter (!·.furniture)
      let body := lines.filter (lineText · == "BODY")
      check ref (label ++ ": content survives") (body.size == 1)
      check ref (label ++ ": PDF body ink and ground")
        (body.any fun line => line.segs.any fun
          | .run _ c _ _ _ _ _ _ _ g _ => c == ink && g == some ground
          | _ => false)
      check ref (label ++ ": PDF fill encloses body")
        (out.pages.any fun page => page.lines.any fun line =>
          lineText line == "BODY" && page.fills.any fun fill =>
            fill.color == ground && fill.x ≤ line.x &&
            line.x + line.setWidth ≤ fill.x + fill.w &&
            fill.y < line.y && line.y < fill.y + fill.h)
      let (_, nodes, _) := HtmlDoc.emitTree {} doc
      let leaves := htmlInks [] #[] nodes.toList
      check ref (label ++ ": HTML body ink and surface")
        (leaves.any fun leaf => leaf.text == "BODY" &&
          leaf.inlineColor == some ink.css &&
          leaf.bodyProperty "background" == some ground.css)
  generatedSourceChecks ref fonts
  regionChecks ref fonts

end Tests.BlockBody
