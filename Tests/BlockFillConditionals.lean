module

public import LeanTex.Core.Font
import LeanTex.Core.Elab
import LeanTex.Core.Layout
import LeanTex.Core.HtmlDoc

open LeanTex.Core

namespace Tests.BlockFillConditionals

private def check (ref : IO.Ref (List String)) (label : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (label :: ·)

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

private def lineText (line : Layout.LineOut) : String :=
  String.ofList (line.segs.toList.flatMap Layout.Seg.glyphChars)

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

/-- Read inline declarations and ancestry from the typed artifact. This is
an artifact witness, not another palette resolver or a browser CSS cascade. -/
private structure HtmlInk where
  text : String := ""
  styles : String
  inBody : Bool
  box : Bool := false

private def property (styles name : String) : Option String :=
  (styles.splitOn ";").foldl (fun found declaration =>
    match declaration.splitOn ":" with
    | [key, value] =>
      if key.trimAscii.toString == name then some value.trimAscii.toString else found
    | _ => found) none

mutual
  private def htmlInks (styles : String) (inBody : Bool) (out : Array HtmlInk) :
      List Html.Node → Array HtmlInk
    | [] => out
    | node :: rest => htmlInks styles inBody (htmlInk styles inBody out node) rest
  private def htmlInk (styles : String) (inBody : Bool) (out : Array HtmlInk) :
      Html.Node → Array HtmlInk
    | .text text => out.push { text, styles, inBody }
    | .elem _ attrs kids =>
      let own := (attrs.find? (·.1 == "style")).map (·.2) |>.getD ""
      let styles := styles ++ ";" ++ own
      let box := attrs.contains ("class", "block-body")
      let inBody := inBody || box
      let out := if box then out.push { styles, inBody, box := true } else out
      htmlInks styles inBody out kids.toList
    | .style _ | .script .. => out
end

private def bodyPaint (leaf : HtmlInk) : Bool :=
  leaf.inBody && property leaf.styles "color" == some ink.css &&
    property leaf.styles "background" == some paper.css

/-- Two distinct paragraphs must lie inside the same positive-area body
surface, with their measured ink bounds and authored foreground. The title
and following paragraph stay outside that surface in both artifacts. -/
private def filledChecks (ref : IO.Ref (List String)) (label : String)
    (actual : Artifacts) : IO Unit := do
  let lines := actual.out.pages.flatMap (·.lines)
  let leaves := htmlInks "" false #[] actual.tree.toList
  for text in #["BODYFIRST", "BODYLAST"] do
    let body := lines.filter (lineText · == text)
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
          page.lines.any fun line => lineText line == text && encloses fill line) &&
        #["HEADER", "OUTSIDE"].all (fun text =>
          page.lines.any fun line => lineText line == text &&
            (line.y < fill.y || fill.y + fill.h < line.y)))
  let boxes := leaves.filter (·.box)
  check ref (label ++ ": one typed HTML body box with padding")
    (boxes.size == 1 && boxes.all (fun box => bodyPaint box &&
      property box.styles "padding" == some (HtmlDoc.cssLength Ir.titledPadding)))
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

/-- Source conditionals must retain the selected body declaration through
Compat, Elab and both artifact paths. The positive availability witness
defines a small synthetic `molochset`; it does not claim that selecting the
builtin theme installs the upstream setter. Its literal `block=fill` branch
uses the supported `setbeamercolor` surface. Source overrides use that same
surface; the false `directlua` guard is followed by an unconditional native
palette declaration.

These are finite source/artifact checks for normal, alert and example
blocks, with two body paragraphs. They assert Layout.Out geometry and the
typed HTML tree, not serialized PDF paint, browser rendering or a universal
conditional-execution theorem. -/
public def blockFillConditionalChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (env, element, role) in #[
      ("block", "block body", "block"),
      ("alertblock", "block body alerted", "alert"),
      ("exampleblock", "block body example", "example")] do
    let declared := "\\setbeamercolor{" ++ element ++ "}{fg=ProbeInk,bg=ProbePaper}"
    let other := "\\setbeamercolor{" ++ element ++ "}{fg=white,bg=black}"
    let native := "\\palette{" ++ role ++ "bodyfg=#173B58," ++ role ++ "bodybg=#E8EDF3}"
    let setter (fill : String) :=
      "\\newcommand{\\molochset}[1]{\\ifstrequal{#1}{block=fill}{" ++ fill ++ "}{" ++ other ++ "}}"
    let guard := "\\ifdefined\\molochset\\molochset{block=fill}\\else" ++ other ++ "\\fi"
    for (name, pre, controlPre) in #[
        ("defined moloch fill", setter declared ++ guard, declared),
        ("undefined moloch followed by body declaration",
          "\\ifdefined\\molochset\\molochset{block=fill}\\fi" ++ declared, declared),
        ("false directlua followed by native body declaration",
          "\\ifdefined\\directlua\\directlua{unselected}" ++ other ++ "\\fi" ++ native, native),
        ("authored colors override guarded defaults", setter other ++ guard ++ declared, declared)] do
      let label := "block fill conditional " ++ env ++ "/" ++ name
      let actual := artifacts fonts (source env pre)
      let control := artifacts fonts (source env controlPre)
      check ref (label ++ ": source has no loss") (actual.diags.all (·.severity == .note))
      check ref (label ++ ": declaration control has no loss") (control.diags.all (·.severity == .note))
      compareChecks ref label actual control
      filledChecks ref label actual

  -- Unsupported configuration remains an honest no-effect. Keeping the
  -- whole key list out of the artifact is part of the refusal contract.
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
