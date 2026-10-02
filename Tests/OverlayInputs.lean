import Tests.Support

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
    (label source canonical : String) : IO Unit := do
  let clock := "\n\n\\uncover<3>{ClockMarker}"
  let (out, html, ds) := inputBuild fonts (source ++ clock)
  let (want, wantHtml, wantDs) := inputBuild fonts (canonical ++ clock)
  check ref (label ++ ": complete artifacts")
    (out.pages.size == 3 && want.pages.size == 3 &&
      ds.all (·.severity == .note) && wantDs.all (·.severity == .note))
  check ref (label ++ ": numbered shipped pages")
    (shippedBodyGlyphs out == shippedBodyGlyphs want &&
      ((inputText out).splitOn "Probe").length == 4)
  check ref (label ++ ": typed HTML selector boundary")
    (inputSelectors html == inputSelectors wantHtml &&
      nodeTextList "" html.toList == nodeTextList "" wantHtml.toList)

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
