module

public import LeanTex.Core.Font
import LeanTex.Core.Elab
import LeanTex.Core.Layout
import LeanTex.Core.HtmlDoc
import Tests.LightCss
import Tests.Support

open LeanTex.Core

namespace Tests.BlockFillConditionals

private def ink : Ir.Color := { r := 0x17, g := 0x3B, b := 0x58 }
private def paper : Ir.Color := { r := 0xE8, g := 0xED, b := 0xF3 }

private def source (env pre : String) : String :=
  "\\documentclass{beamer}\\usetheme{moloch}\\usepackage{etoolbox}" ++
    "\\definecolor{ProbeInk}{HTML}{173B58}" ++
    "\\definecolor{ProbePaper}{HTML}{E8EDF3}" ++ pre ++
    "\\begin{document}\\begin{frame}[t]{FRAME}" ++
    "\\begin{" ++ env ++ "}{HEADER}BODYFIRST\\par BODYLAST\\end{" ++ env ++ "}" ++
    "OUTSIDE\\end{frame}\\end{document}"

private structure Artifacts where
  out : Layout.Out
  tree : Array Html.Node
  serialized : String
  diags : Array Diag

private def artifacts (fonts : Font.FontSet) (src : String) : Artifacts :=
  let (doc, ds) := Elab.run "block-fill-conditionals.tex" src
  let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  { out, tree, serialized := Html.document "en" head tree, diags := ds ++ out.diags ++ hds }

private def encloses (fill : Layout.Fill) (line : Layout.LineOut) : Bool :=
  match line.regionExtent with
  | none => false
  | some (above, below) =>
    fill.x ≤ line.x && line.x + line.setWidth ≤ fill.x + fill.w &&
      fill.y ≤ line.y - above && line.y + below ≤ fill.y + fill.h

private def linePaint (line : Layout.LineOut) : Bool :=
  let runs := line.segs.filterMap fun
    | .run _ c _ _ _ _ _ _ _ ground _ => some (c, ground)
    | _ => none
  !runs.isEmpty && runs.all (fun (c, ground) => c == ink && ground == some paper)

/-- Inline declarations and ancestry read from the typed artifact. -/
private structure HtmlInk where
  text : String := ""
  styles : String
  inBody : Bool
  box : Bool := false

mutual
  private def htmlInks (styles : String) (inBody : Bool) (out : Array HtmlInk) :
      List Html.Node → Array HtmlInk
    | [] => out
    | node :: rest => htmlInks styles inBody (htmlInk styles inBody out node) rest
  private def htmlInk (styles : String) (inBody : Bool) (out : Array HtmlInk) :
      Html.Node → Array HtmlInk
    | .text text => out.push { text, styles, inBody }
    | .elem _ attrs kids =>
      let raw := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      -- A style stated through its roles reads as the light screen reads it.
      let own := lightStyle (styleVars raw ++ styleVars styles) raw
      let styles := styles ++ ";" ++ own
      let box := attrs.contains ("class", "block-body")
      let inBody := inBody || box
      let out := if box then out.push { styles, inBody, box := true } else out
      htmlInks styles inBody out kids.toList
    | .style _ | .script .. => out
end

private def bodyPaint (leaf : HtmlInk) : Bool :=
  leaf.inBody && cssProperty leaf.styles "color" == some ink.css &&
    cssProperty leaf.styles "background" == some paper.css

/-- Two paragraphs lie inside one positive-area body surface with their ink and foreground, the
title and the following paragraph outside it, in both artifacts. -/
private def filledChecks (ref : IO.Ref (List String)) (label : String)
    (actual : Artifacts) : IO Unit := do
  let lines := actual.out.pages.flatMap (·.lines)
  let leaves := htmlInks "" false #[] actual.tree.toList
  for text in #["BODYFIRST", "BODYLAST"] do
    let body := lines.filter (lineText · false == text)
    check ref (label ++ ": PDF " ++ text ++ " once, authored ink and ground")
      (body.size == 1 && body.all linePaint)
    let body := leaves.filter (·.text == text)
    check ref (label ++ ": HTML " ++ text ++ " once, inside authored body paint")
      (body.size == 1 && body.all bodyPaint)
  check ref (label ++ ": one PDF surface encloses both complete paragraphs")
    (actual.out.pages.size == 1 && actual.out.pages.any fun page =>
      let fills := page.fills.filter (·.color == paper)
      fills.size == 1 && fills.any fun fill =>
        fill.w > 0 && fill.h > 0 &&
        #["BODYFIRST", "BODYLAST"].all (fun text =>
          page.lines.any fun line => lineText line false == text && encloses fill line) &&
        #["HEADER", "OUTSIDE"].all (fun text =>
          page.lines.any fun line => lineText line false == text &&
            (line.y < fill.y || fill.y + fill.h < line.y)))
  let boxes := leaves.filter (·.box)
  check ref (label ++ ": one typed HTML body box with padding")
    (boxes.size == 1 && boxes.all (fun box => bodyPaint box &&
      cssProperty box.styles "padding" ==
        some s!"0 {HtmlDoc.cssLength Ir.titledPadding} {HtmlDoc.cssLength Ir.titledPadding}"))
  for text in #["HEADER", "OUTSIDE"] do
    let outside := leaves.filter (·.text == text)
    check ref (label ++ ": HTML " ++ text ++ " survives outside body box")
      (outside.size == 1 && outside.all (!·.inBody))

private def compareChecks (ref : IO.Ref (List String)) (label : String)
    (actual control : Artifacts) : IO Unit := do
  check ref (label ++ ": identical Layout.Out pages")
    (reprStr actual.out.pages == reprStr control.out.pages)
  check ref (label ++ ": identical serialized typed HTML")
    (actual.serialized == control.serialized)

/-- Source conditionals keep the selected body declaration through Compat, Elab and both artifacts,
for normal, alert and example blocks. -/
public def blockFillConditionalChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (env, element, role) in #[
      ("block", "block body", "block"),
      ("alertblock", "block body alerted", "alert"),
      ("exampleblock", "block body example", "example")] do
    let declared := "\\setbeamercolor{" ++ element ++ "}{fg=ProbeInk,bg=ProbePaper}"
    let other := "\\setbeamercolor{" ++ element ++ "}{fg=white,bg=black}"
    let native := "\\palette{" ++ role ++ "bodyfg=#173B58," ++ role ++ "bodybg=#E8EDF3}"
    let setter (fill : String) :=
      "\\renewcommand{\\molochset}[1]{\\ifstrequal{#1}{block=fill}{" ++ fill ++ "}{" ++ other ++ "}}"
    let guard := "\\ifdefined\\molochset\\molochset{block=fill}\\else" ++ other ++ "\\fi"
    for (name, pre, controlPre) in #[
        ("redefined moloch setter fill", setter declared ++ guard, declared),
        ("moloch's setter followed by body declaration",
          "\\ifdefined\\molochset\\molochset{block=fill}\\fi" ++ declared,
          "\\molochset{block=fill}" ++ declared),
        ("false directlua followed by native body declaration",
          "\\ifdefined\\directlua\\directlua{unselected}" ++ other ++ "\\fi" ++ native, native),
        ("authored colors override guarded defaults", setter other ++ guard ++ declared, declared)] do
      let label := "block fill conditional " ++ env ++ "/" ++ name
      let actual := artifacts fonts (source env pre)
      let control := artifacts fonts (source env controlPre)
      -- The contrast contract names moloch's teal-on-grey title wherever the setter runs.
      let named (a : Artifacts) := (a.diags.filter (·.severity != .note)).map (·.code)
      let contrast (a : Artifacts) := named a |>.filter fun c => c != "W0315" && c != "W0345"
      check ref (label ++ ": source has no loss") (contrast actual).isEmpty
      check ref (label ++ ": declaration control has no loss") (contrast control).isEmpty
      check ref (label ++ ": the source names what its control names") (named actual == named control)
      compareChecks ref label actual control
      filledChecks ref label actual

  -- Unsupported configuration is an honest no-effect, its whole key list kept out of the artifact.
  let actual := artifacts fonts (source "block" "\\metroset{block=fill}")
  let control := artifacts fonts (source "block" "")
  check ref "block fill conditional metroset: one named loss"
    ((actual.diags.filter (·.severity != .note)).size == 1 &&
      actual.diags.any (fun d => d.kind == .W0104 && d.subject == some "beamer:metroset"))
  check ref "block fill conditional metroset: control has no loss"
    (control.diags.all (·.severity == .note))
  compareChecks ref "block fill conditional metroset refusal" actual control
  check ref "block fill conditional metroset: no body surface invented"
    (!(htmlInks "" false #[] actual.tree.toList).any (·.box) &&
      !(actual.out.pages.any fun page => page.fills.any (·.color == paper)))

end Tests.BlockFillConditionals
