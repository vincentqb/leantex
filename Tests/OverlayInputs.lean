module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private def inputBuild (fonts : Font.FontSet) (body : String) :
    Layout.Out × Array Html.Node × Array Diag :=
  let (doc, ds) := elabStr (deck169Frame body)
  let out := layoutOf fonts doc
  let (_, html, hd) := HtmlDoc.emitTree {} doc
  (out, html, ds ++ out.diags ++ hd)

private def inputText (out : Layout.Out) : String :=
  String.ofList ((shippedBodyGlyphs out).toList.map (·.scalar))

private def inputAttrs (html : Array Html.Node) (key : String) : Array String :=
  (elemAttrsList (fun _ => true) #[] html.toList).filterMap fun (_, attrs) =>
    (attrs.find? (·.1 == key)).map (·.2)

private def inputSelectors (html : Array Html.Node) : Array (Array (String × String)) :=
  (elemAttrsList (fun _ => true) #[] html.toList).filterMap fun (_, attrs) =>
    let selected := attrs.filter fun (key, _) =>
      ["data-step", "data-step-last", "data-steps"].contains key
    if selected.isEmpty then none else some selected

/-- Equivalent surface calls must ship the same numbered pages and HTML
selector attributes. The positive text assertion prevents two empty artifacts
from passing; glyph equality also observes covered colour and placement. -/
private def inputEquivalent (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label source canonical : String) (probeCopies : Nat := 3) : IO Unit := do
  -- Fix the frame extent before a source can redefine the clock's name.
  let clock := "\\uncover<3>{ClockMarker}\n\n"
  let (out, html, ds) := inputBuild fonts (clock ++ source)
  let (want, wantHtml, wantDs) := inputBuild fonts (clock ++ canonical)
  check ref (label ++ ": complete artifacts")
    (out.pages.size == 3 && want.pages.size == 3 &&
      ds.all (·.severity == .note) && wantDs.all (·.severity == .note))
  check ref (label ++ ": numbered shipped pages")
    (shippedBodyGlyphs out == shippedBodyGlyphs want &&
      ((inputText out).splitOn "Probe").length == probeCopies + 1)
  check ref (label ++ ": typed HTML selector boundary")
    (inputSelectors html == inputSelectors wantHtml &&
      nodeTextList "" html.toList == nodeTextList "" wantHtml.toList)
  check ref (label ++ ": link and destination identities")
    (inputAttrs html "id" == inputAttrs wantHtml "id" &&
      inputAttrs html "href" == inputAttrs wantHtml "href")

/-- A selected alert has one authored body, hence one note and label effect.
The following note must still be 2. Read the shipped note ink and all HTML
IDs, including hidden alternatives: a selected branch alone cannot certify
that elaboration did not execute its body twice. -/
private def inputAlertEffects (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body := "FirstProbe\\footnote{FirstNote}\\label{input-label}"
  let after := " SecondProbe\\footnote{SecondNote} \\hyperlink{input-label}{LabelLink}"
  for spec in ["2", "1,3"] do
    let (out, html, ds) := inputBuild fonts
      ("\\alert<" ++ spec ++ ">{" ++ body ++ "}" ++ after ++
        "\n\n\\uncover<3>{ClockMarker}")
    let label := "alert body once <" ++ spec ++ ">"
    check ref (label ++ ": no effect loss") (ds.all (·.severity == .note))
    check ref (label ++ ": three numbered pages") (out.pages.size == 3)
    for page in out.pages do
      let one := { out with pages := #[page] }
      let text := inputText one
      check ref (label ++ ": following note keeps number 2")
        ((text.splitOn "FirstProbe1").length == 2 &&
          (text.splitOn "SecondProbe2").length == 2)
      check ref (label ++ ": one shipped body for each note")
        ((text.splitOn "FirstNote").length == 2 &&
          (text.splitOn "SecondNote").length == 2)
    let ids := inputAttrs html "id"
    for id in ["fn1", "fn2", "fnref1", "fnref2", "input-label"] do
      check ref (label ++ ": one full-tree target " ++ id)
        ((ids.filter (· == id)).size == 1)
    check ref (label ++ ": no phantom third note") (!ids.contains "fn3")

/-- The native families share the same cover boundary. In particular the
label of a description item and the title of a block are covered with their
body; prefix and final selector slots produce identical artifacts. -/
private def inputNativeFamilies (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for kind in ["block", "alertblock", "exampleblock"] do
    let bare := "\\begin{" ++ kind ++ "}{Heading}Probe\\end{" ++ kind ++ "}"
    let want := "\\uncover<1,3>{" ++ bare ++ "}"
    inputEquivalent ref fonts (kind ++ " prefix selector")
      ("\\begin{" ++ kind ++ "}< 1 , 3 >{Heading}Probe\\end{" ++ kind ++ "}") want
    inputEquivalent ref fonts (kind ++ " final selector")
      ("\\begin{" ++ kind ++ "}{Heading}< 1 , 3 >Probe\\end{" ++ kind ++ "}") want
  for item in ["\\item<1,3>[Label]Probe", "\\item[Label] < 1 , 3 >Probe"] do
    inputEquivalent ref fonts "description label and body selected together"
      ("\\begin{description}" ++ item ++ "\\end{description}")
      "\\uncover<1,3>{\\begin{description}\\item[Label]Probe\\end{description}}"
  inputEquivalent ref fonts "onslide star prefix"
    "\\onslide*<1,3>{Probe}" "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "onslide star final"
    "\\onslide*{Probe}<1,3>" "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "onslide plus prefix"
    "\\onslide+<1,3>{Probe}" "\\visible<1,3>{Probe}"
  inputEquivalent ref fonts "native let forwarding"
    "\\let\\Pick\\only\\Pick< 1 , 3 >{Probe}" "\\only<1,3>{Probe}"
  for name in ["only", "uncover", "visible", "onslide", "alert", "emph", "textbf"] do
    inputEquivalent ref fonts ("native let freezes " ++ name)
      ("\\let\\Pick\\" ++ name ++ "\\let\\Copy\\Pick\\def\\" ++ name ++
        "#1{Lost}\\Copy<1,3>{Probe}") ("\\" ++ name ++ "<1,3>{Probe}")
  inputEquivalent ref fonts "saved onslide star keeps native dispatch"
    "\\let\\Pick\\onslide\\def\\only#1{Lost}\\Pick*<1,3>{Probe}" "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "saved native wrapper keeps block dispatch"
    "\\let\\Pick\\hyperlink\\def\\hyperlink#1{Lost}\\Pick<1,3>{input-link}{Probe\\par Second}\\hypertarget{input-link}{}"
    "\\hyperlink<1,3>{input-link}{Probe\\par Second}\\hypertarget{input-link}{}" 2

private def inputAttr (attrs : Array (String × String)) (key : String) : String :=
  ((attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- Read the artifact's selector vocabulary; covering carriers remain present.
Only the display-level alternative carriers can remove their descendants. -/
private def inputAltShown (attrs : Array (String × String)) (step : Nat) : Bool :=
  let classes := (inputAttr attrs "class").splitOn " "
  if classes.contains "alt-set" then
    (inputAttr attrs "data-steps").splitOn " " |>.contains (toString step)
  else if classes.contains "alt-crisp" || classes.contains "alt-pending" then
    let lo := (inputAttr attrs "data-step").toNat?.getD 1
    let hi := (inputAttr attrs "data-step-last").toNat?
    let active := lo ≤ step && (hi.map fun n => decide (step ≤ n)).getD true
    if classes.contains "alt-pending" then !active else active
  else !(attrs.any (·.1 == "hidden"))

mutual

private def inputAtOne (step : Nat) (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .elem tag attrs kids =>
    if inputAltShown attrs step then
      acc.push (.elem tag attrs (inputAtList step #[] kids.toList))
    else acc
  | node => acc.push node

private def inputAtList (step : Nat) (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | node :: rest => inputAtList step (inputAtOne step acc node) rest

end

private def inputPageLinks (page : Layout.PageOut) : Array String :=
  page.links.map (·.target) ++ page.lines.flatMap fun line =>
    line.segs.filterMap fun
      | .run _ _ link .. => link
      | _ => none

/-- Beamer's native targets use only (beamerbaseoverlay.sty, lines 631–632):
excluded steps have no body ink, link, or destination. Ordinary only currently
covers in this engine, so it is a reference for the included reading alone;
the independent absence assertions below judge the excluded reading. -/
private def inputNativeTargetRemoval (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  for name in ["hyperlink", "hypertarget"] do
    let target := if name == "hyperlink" then "input-link" else "input-target"
    let dest := if name == "hyperlink" then "input-body" else target
    let href := if name == "hyperlink" then "#input-link" else "https://example.invalid/target"
    let ink := if name == "hyperlink" then "\\label{input-body}Probe"
      else "\\href{https://example.invalid/target}{Probe}"
    let tail := "\n\nAlways\\hypertarget{outside}{}" ++
      if name == "hyperlink" then "\\hypertarget{input-link}{}" else ""
    for block in [false, true] do
      let body := ink ++ if block then "\\par Second" else ""
      let args := "{" ++ target ++ "}{" ++ body ++ "}"
      let bare := "\\" ++ name ++ args
      for spec in ["2", "1,3"] do
        let selector := "< " ++ spec ++ " >"
        let clock := "\\uncover<3>{ClockMarker}\n\n"
        let (want, wantHtml, wantDs) := inputBuild fonts
          (clock ++ "\\only<" ++ spec ++ ">{" ++ bare ++ "}" ++ tail)
        for (slot, call) in [
            ("prefix", "\\" ++ name ++ selector ++ args),
            ("middle", "\\" ++ name ++ "{" ++ target ++ "}" ++ selector ++ "{" ++ body ++ "}"),
            ("final", bare ++ selector)] do
          let (out, html, ds) := inputBuild fonts (clock ++ call ++ tail)
          let label := s!"native {name} {if block then "block" else "inline"} {slot} <{spec}>"
          check ref (label ++ ": complete artifacts")
            (out.pages.size == 3 && want.pages.size == 3 &&
              ds.all (·.severity == .note) && wantDs.all (·.severity == .note))
          check ref (label ++ ": one authored HTML body and destination")
            (treeOccurs html "Probe" == 1 && ((inputAttrs html "id").filter (· == dest)).size == 1)
          for step in [1, 2, 3] do
            let selected := if spec == "2" then step == 2 else step == 1 || step == 3
            let view := inputAtList step #[] html.toList
            let expected := if selected then 1 else 0
            let suffix := s!": step {step}"
            check ref (label ++ suffix ++ " HTML body present exactly when selected")
              (treeOccurs view "Probe" == expected &&
                (!block || treeOccurs view "Second" == expected) && treeOccurs view "Always" == 1)
            check ref (label ++ suffix ++ " HTML link present exactly when selected")
              ((inputAttrs view "href").contains href == selected)
            check ref (label ++ suffix ++ " HTML destination present exactly when selected")
              ((inputAttrs view "id").contains dest == selected &&
                (inputAttrs view "id").contains "outside")
            if let some page := out.pages[step - 1]? then
              let one := { out with pages := #[page] }
              let text := inputText one
              check ref (label ++ suffix ++ " layout body present exactly when selected")
                ((text.splitOn "Probe").length == expected + 1 &&
                  (!block || (text.splitOn "Second").length == expected + 1) &&
                  (text.splitOn "Always").length == 2)
              check ref (label ++ suffix ++ " layout link present exactly when selected")
                ((inputPageLinks page).contains href == selected)
              check ref (label ++ suffix ++ " layout destination present exactly when selected")
                (page.lines.any (fun line => line.anchors.contains dest) == selected &&
                  page.lines.any (fun line => line.anchors.contains "outside"))
              if selected then
                let wantView := inputAtList step #[] wantHtml.toList
                check ref (label ++ suffix ++ " included reading agrees with only")
                  (shippedBodyGlyphs one == shippedBodyGlyphs { want with pages := want.pages.extract (step - 1) step } &&
                    nodeTextList "" view.toList == nodeTextList "" wantView.toList &&
                    inputAttrs view "id" == inputAttrs wantView "id" &&
                    inputAttrs view "href" == inputAttrs wantView "href")

/-- Every new native boundary reads fragments at use, including a titled
body reached through a macro. Refused fragments retain the page and the
state following the call; they cannot execute a definition or flag setter. -/
private def inputNativeFragments (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for kind in ["block", "alertblock", "exampleblock"] do
    let bare := "\\begin{" ++ kind ++ "}{Heading}Probe\\end{" ++ kind ++ "}"
    let want := "\\uncover<1,3>{" ++ bare ++ "}"
    for (slot, call) in [
        ("prefix", "\\begin{" ++ kind ++ "}<\\Step>{Heading}Probe\\end{" ++ kind ++ "}"),
        ("final", "\\begin{" ++ kind ++ "}{Heading}<\\Step>Probe\\end{" ++ kind ++ "}")] do
      inputEquivalent ref fonts (kind ++ " " ++ slot ++ " fragment")
        ("\\def\\Step{1,3}" ++ call) want
      inputEquivalent ref fonts (kind ++ " " ++ slot ++ " fragment reads use state")
        ("\\def\\Step{1}\\def\\Pick{" ++ call ++ "}\\def\\Step{1,3}\\Pick") want
  inputEquivalent ref fonts "onslide star final fragment"
    "\\def\\Step{1,3}\\onslide*{Probe}<\\Step>" "\\only<1,3>{Probe}"
  for (label, call, bare) in [
      ("block prefix", "\\begin{block}<\\Bad>{Heading}Probe\\end{block}",
        "\\begin{block}{Heading}Probe\\end{block}"),
      ("block final", "\\begin{block}{Heading}<\\Bad>Probe\\end{block}",
        "\\begin{block}{Heading}Probe\\end{block}"),
      ("onslide star final", "\\onslide*{Probe}<\\Bad>", "Probe")] do
    for (kind, before, after) in [
        ("definition", "\\def\\Bad{\\gdef\\Sentinel{Lost}2}\\def\\Sentinel{Kept}", " \\Sentinel"),
        ("flag", "\\newif\\ifprobe\\def\\Bad{\\probetrue 2}", " \\ifprobe Lost\\else Kept\\fi"),
        ("cycle", "\\def\\Bad{\\Bad}", " Kept")] do
      let clock := "\n\n\\uncover<3>{ClockMarker}"
      let (out, html, ds) := inputBuild fonts (before ++ call ++ after ++ clock)
      let (want, wantHtml, _) := inputBuild fonts (bare ++ " Kept" ++ clock)
      let label := label ++ " refused " ++ kind ++ " fragment"
      check ref (label ++ ": named without another loss")
        (ds.any (·.code == "W0105") && ds.all (fun d => d.severity == .note || d.code == "W0105"))
      check ref (label ++ ": shipped body and state")
        (out.pages.size == 3 && shippedBodyGlyphs out == shippedBodyGlyphs want)
      check ref (label ++ ": typed HTML body and selector boundary")
        (nodeTextList "" html.toList == nodeTextList "" wantHtml.toList &&
          inputSelectors html == inputSelectors wantHtml)
  for name in ["href", "link"] do
    let (out, html, ds) := inputBuild fonts
      ("\\" ++ name ++ "<1,3>{https://example.invalid}{Probe\\par Second}\n\n\\uncover<3>{ClockMarker}")
    check ref (name ++ ": no new selector slot on a general link")
      (ds.any (·.code == "E0304") &&
        !(inputSelectors html).any (fun attrs => attrs.contains ("data-steps", "1 3")) &&
        ((inputText out).splitOn "Probe").length == 4)

/-- Beamer's newcommand<> wrappers remember the last selector through their
ordinary arguments (beamer@foundspec / beamer@finalspec). Only/alt consume one
selector, and a final slot never skips a space. These guards failed on
f6d3a50 before the review correction. -/
private def inputSelectorWindows (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for name in ["alert", "emph"] do
    let want := "\\" ++ name ++ "<2>{Probe}"
    inputEquivalent ref fonts (name ++ " final selector wins")
      ("\\" ++ name ++ "<1>{Probe}<2>") want
    inputEquivalent ref fonts (name ++ " repeated prefix selector wins")
      ("\\" ++ name ++ "<1><2>{Probe}") want
    inputEquivalent ref fonts (name ++ " final fragment reads use state")
      ("\\def\\Step{1}\\def\\Pick{\\" ++ name ++ "<1>{Probe}<\\Step>}" ++
        "\\def\\Step{2}\\Pick") want
  for (label, source, want) in [
      ("only prefix closes its selector window", "\\only<1>{Probe}<2>", "\\only<1>{Probe}{<2>}"),
      ("only suffix does not skip space", "\\only{Probe} <1,3>", "Probe <1,3>"),
      ("emph suffix does not skip space", "\\emph{Probe} <1,3>", "\\emph{Probe} {<1,3>}"),
      ("font wrapper has no final selector", "\\textbf{Probe}<1,3>", "\\textbf{Probe}{<1,3>}")] do
    inputEquivalent ref fonts label source want

/-- A selector reads a finite graph of parameterless text definitions at the
use. Reusing a dependency is not a cycle. An unread fragment must reach the
unsupported-selector boundary without running its definitions or setters. -/
private def inputSelectorFragments (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let names := (List.range 24).map fun n => "Step" ++ String.ofList (List.replicate n 'x')
  let (defs, first) := names.foldr (fun name (defs, next) =>
    ("\\def\\" ++ name ++ "{" ++ next ++ "}" ++ defs, "\\" ++ name)) ("", "1,3")
  inputEquivalent ref fonts "fragment path follows the binding table"
    (defs ++ "\\only<" ++ first ++ ">{Probe}") "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "fragment dependency can occur twice"
    "\\def\\Leaf{2}\\def\\Pair{\\Leaf,\\Leaf}\\only<\\Pair>{Probe}" "\\only<2,2>{Probe}"
  for (label, source, want) in [
      ("self cycle", "\\def\\Step{\\Step}\\only<\\Step>{Probe}", "Probe"),
      ("mutual cycle", "\\def\\Left{\\Right}\\def\\Right{\\Left}\\only<\\Left>{Probe}", "Probe"),
      ("group fragment", "\\def\\Step{{2}}\\only<\\Step>{Probe}", "Probe"),
      ("argument fragment", "\\def\\Step#1{#1}\\only<\\Step>{Probe}", "Probe"),
      ("definition fragment",
        "\\def\\Bad{\\gdef\\Sentinel{Lost}2}\\def\\Sentinel{Kept}\\only<\\Bad>{Probe} \\Sentinel",
        "Probe Kept"),
      ("flag fragment",
        "\\newif\\ifprobe\\def\\Bad{\\probetrue 2}\\only<\\Bad>{Probe} \\ifprobe Lost\\else Kept\\fi",
        "Probe Kept")] do
    let clock := "\n\n\\uncover<3>{ClockMarker}"
    let (out, _, ds) := inputBuild fonts (source ++ clock)
    let (expected, _, _) := inputBuild fonts (want ++ clock)
    check ref (label ++ ": refused selector named")
      (ds.any (·.code == "W0105") && ds.all (·.severity != .error))
    check ref (label ++ ": refusal preserves shipped body and state")
      (out.pages.size == 3 && inputText out == inputText expected)

/-- Surface-boundary regression entry; standalone callers need only the
shipped one-face font set. Guards were run against e5a5428a before the fix;
this module does not depend on the parallel overlay-contract work. -/
def overlayInputChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  inputAlertEffects ref fonts
  inputSelectorWindows ref fonts
  inputSelectorFragments ref fonts
  inputNativeFamilies ref fonts
  inputNativeFragments ref fonts
  inputNativeTargetRemoval ref fonts
  for command in ["only", "uncover", "visible", "textbf", "textcolor{blue}"] do
    -- textcolor's selector precedes its colour, not its content argument.
    let head := if command == "textcolor{blue}" then "textcolor" else command
    let args := if command == "textcolor{blue}" then "{blue}{Probe}" else "{Probe}"
    inputEquivalent ref fonts ("spaced selector " ++ command)
      ("\\" ++ head ++ "< 1 , 3 >" ++ args)
      ("\\" ++ head ++ "<1,3>" ++ args)
  inputEquivalent ref fonts "spaced interval endpoints"
    "\\only< 1 - 2 >{Probe}" "\\only<1-2>{Probe}"
  inputEquivalent ref fonts "parameter selector fragments"
    "\\newcommand{\\Pick}[1]{\\only<#1>{Probe}}\\Pick{1,3}"
    "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "expanded selector fragments"
    "\\def\\Steps{1,3}\\only<\\Steps>{Probe}" "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "native forwarding boundary"
    "\\def\\Pick{\\only}\\Pick< 1 , 3 >{Probe}" "\\only<1,3>{Probe}"
  inputEquivalent ref fonts "trailing alert selector"
    "\\alert{Probe}<1,3>" "\\alert<1,3>{Probe}"
  for spec in ["+", "beamer:2", "alert@2"] do
    let (out, _, ds) := inputBuild fonts ("\\alert<" ++ spec ++ ">{Probe}")
    check ref ("unsupported selector stays diagnosed " ++ spec)
      (ds.any (·.code == "W0105") &&
        ((inputText out).splitOn "Probe").length == 2)

end Tests
