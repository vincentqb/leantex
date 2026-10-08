module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private structure MacroForwardCase where
  label : String
  pre : String
  body : String
  controlPre : String
  controlBody : String
  visible : String
  roles : Array (String × Nat)

/-- Expansion reads arguments from the caller, executes each substituted
occurrence in source order, and owns only the resulting ink. The complete
serialized typed tree observes role ancestry, separators and whitespace;
the shipped glyph census retains exact positions and paint. -/
private def macroForwardArtifacts (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (c : MacroForwardCase) : IO Unit := do
  let source := dvDoc ("\\pagestyle{empty}" ++ c.pre) c.body
  let control := dvDoc ("\\pagestyle{empty}" ++ c.controlPre) c.controlBody
  let (ds, out, html, text) := sourceArtifacts fonts source
  let (cds, cout, chtml, ctext) := sourceArtifacts fonts control
  let t := check ref
  let label := "macro forwarding " ++ c.label
  t (label ++ ": no loss") (ds.all (·.severity == .note))
  t (label ++ ": control has no loss") (cds.all (·.severity == .note))
  t (label ++ ": exact visible HTML") (text == c.visible && ctext == c.visible)
  t (label ++ ": exact typed HTML ownership") (html == chtml)
  t (label ++ ": exact shipped glyphs") (shippedBodyGlyphs out == shippedBodyGlyphs cout)
  t (label ++ ": exact pages and lines")
    (out.pages.size == cout.pages.size &&
      (bodyLines out).map (fun l => (l.x, l.y, lineText l, metricInnerGaps l)) ==
        (bodyLines cout).map (fun l => (l.x, l.y, lineText l, metricInnerGaps l)))
  t (label ++ ": exact painted rules") (metricRuleSegs out == metricRuleSegs cout)
  let (_, tree, _) := HtmlDoc.emitTree {} (elabStr source).1
  let classes := tree.flatMap (attrValuesOf (fun _ => true) "class")
  for (name, expected) in c.roles do
    let count := classes.foldl (fun n value =>
      if (value.splitOn " ").contains (HtmlDoc.roleClass name) then n + 1 else n) 0
    t s!"{label}: {name} has {expected} role sites" (count == expected)
  unless ds.all (·.severity == .note) do
    IO.println s!"{label}: {repr (ds.filter (·.severity != .note))}"

/-- A forwarded call has the same argument/state semantics as its direct
spelling. The stateful repeated-argument expectations are witnessed by
synthetic LuaLaTeX pages: `AX/T/Z` and `AUnset/AB/T/Z`. -/
def macroForwardArgumentsChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let native (name : String) := "\\define\\" ++ name ++ "(a: content){\\a}"
  let variants := #[
    ("direct", "", "\\wordprobe", "wordprobe"),
    ("parameter alias", "\\let\\aliasprobe\\wordprobe", "\\aliasprobe", "aliasprobe"),
    ("zero-argument forward", "\\def\\zeroprobe{\\wordprobe}", "\\zeroprobe", "wordprobe"),
    ("forward alias", "\\def\\zeroprobe{\\wordprobe}\\let\\aliasprobe\\zeroprobe",
      "\\aliasprobe", "wordprobe"),
    ("forward chain", "\\def\\zeroprobe{\\wordprobe}\\def\\chainprobe{\\zeroprobe}",
      "\\chainprobe", "wordprobe")]
  for (label, definitions, call, role) in variants do
    let roles := #[(role, 1), ("zeroprobe", 0), ("chainprobe", 0)]
    macroForwardArtifacts ref fonts {
      label := label ++ " changes following state"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[1]{#1\\choiceprobetrue}" ++
        definitions
      body := "A" ++ call ++ "{X}/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native role
      controlBody := "A\\" ++ role ++ "{X}/T/Z"
      visible := "AX/T/Z", roles }
    macroForwardArtifacts ref fonts {
      label := label ++ " repeats stateful argument in order"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[1]{" ++
        "\\ifchoiceprobe Set\\else Unset\\fi/#1#1}" ++ definitions
      body := "A" ++ call ++ "{\\ifchoiceprobe B\\else A\\fi\\choiceprobetrue}" ++
        "/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native role
      controlBody := "A\\" ++ role ++ "{Unset/AB}/T/Z"
      visible := "AUnset/AB/T/Z", roles }

  for c in (#[
    { label := "forward leaves bare-word remainder outside"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[1]{#1\\choiceprobetrue}" ++
        "\\def\\zeroprobe{\\wordprobe}"
      body := "A\\zeroprobe XY/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native "wordprobe", controlBody := "A\\wordprobe{X}Y/T/Z"
      visible := "AXY/T/Z", roles := #[("wordprobe", 1), ("zeroprobe", 0)] },
    { label := "forward consumes two following arguments"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[2]{#1/#2\\choiceprobetrue}" ++
        "\\def\\zeroprobe{\\wordprobe}"
      body := "A\\zeroprobe{X}{Y}/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native "wordprobe", controlBody := "A\\wordprobe{X/Y}/T/Z"
      visible := "AX/Y/T/Z", roles := #[("wordprobe", 1), ("zeroprobe", 0)] },
    { label := "forward reads explicit optional argument"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[2][D]{#1/#2\\choiceprobetrue}" ++
        "\\def\\zeroprobe{\\wordprobe}"
      body := "A\\zeroprobe[Q]{X}/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native "wordprobe", controlBody := "A\\wordprobe{Q/X}/T/Z"
      visible := "AQ/X/T/Z", roles := #[("wordprobe", 1), ("zeroprobe", 0)] },
    { label := "forward selects optional default"
      pre := "\\newif\\ifchoiceprobe\\newcommand\\wordprobe[2][D]{#1/#2\\choiceprobetrue}" ++
        "\\def\\zeroprobe{\\wordprobe}"
      body := "A\\zeroprobe{X}/\\ifchoiceprobe T\\else F\\fi/Z"
      controlPre := native "wordprobe", controlBody := "A\\wordprobe{D/X}/T/Z"
      visible := "AD/X/T/Z", roles := #[("wordprobe", 1), ("zeroprobe", 0)] },
    { label := "parameterized forward owns consumed group only"
      pre := "\\newcommand\\wordprobe[1]{#1}\\newcommand\\outerprobe[1]{\\wordprobe}"
      body := "A\\outerprobe{unused}{X}/Z"
      controlPre := native "wordprobe" ++ native "outerprobe"
      controlBody := "A\\outerprobe{\\wordprobe{X}}/Z"
      visible := "AX/Z", roles := #[("wordprobe", 1), ("outerprobe", 1)] },
    { label := "parameterized forward leaves bare-word remainder outside"
      pre := "\\newcommand\\wordprobe[1]{#1}\\newcommand\\outerprobe[1]{\\wordprobe}"
      body := "A\\outerprobe{unused}XY/Z"
      controlPre := native "wordprobe" ++ native "outerprobe"
      controlBody := "A\\outerprobe{\\wordprobe{X}}Y/Z"
      visible := "AXY/Z", roles := #[("wordprobe", 1), ("outerprobe", 1)] }
    ] : Array MacroForwardCase) do
    macroForwardArtifacts ref fonts c

  -- Settlement is speculative; a malformed actual use must still account
  -- for its unread arguments.
  let missing := dvDoc
    "\\newcommand\\wordprobe[1]{#1}\\def\\zeroprobe{\\wordprobe}"
    "\\zeroprobe"
  check ref "macro forwarding missing actual argument remains diagnosed"
    ((elabStr missing).2.any fun d =>
      d.code == "W0104" && d.subject == some "cond:arguments:wordprobe")

/-- Settling a reusable zero-argument replacement must leave each
parameterized child's role fresh at every use, without owning the wrapper.
Includes the forwarding checks, so the suite has one entry point. -/
def macroForwardingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  macroForwardArgumentsChecks ref fonts
  let native (name : String) := "\\define\\" ++ name ++ "(a: content){\\a}"
  let wrappers := #[
    ("complete zero-argument definition", "\\def\\zeroprobe{\\wordprobe{X}}", "\\zeroprobe"),
    ("complete zero-argument alias", "\\def\\zeroprobe{\\wordprobe{X}}\\let\\aliasprobe\\zeroprobe",
      "\\aliasprobe"),
    ("native zero-argument wrapper", "\\define\\zeroprobe(){\\wordprobe{X}}", "\\zeroprobe"),
    ("settled builtin replacement", "\\renewcommand\\maketitle{\\wordprobe{X}}", "\\maketitle")]
  for (label, definition, call) in wrappers do
    for (spacing, separator) in #[("separated", "/"), ("adjacent", "")] do
      macroForwardArtifacts ref fonts {
        label := label ++ " " ++ spacing
        pre := "\\newcommand\\wordprobe[1]{#1}" ++ definition
        body := "A" ++ call ++ separator ++ call ++ "/Z"
        controlPre := native "wordprobe"
        controlBody := "A\\wordprobe{X}" ++ separator ++ "\\wordprobe{X}/Z"
        visible := "AX" ++ separator ++ "X/Z"
        roles := #[("wordprobe", 2), ("zeroprobe", 0), ("aliasprobe", 0), ("maketitle", 0)] }
  macroForwardArtifacts ref fonts {
    label := "settled builtin keeps styled child identity"
    pre := "\\newcommand\\wordprobe[1]{\\textbf{#1}}" ++
      "\\renewcommand\\maketitle{\\wordprobe{X}}"
    body := "A\\maketitle\\maketitle/Z"
    controlPre := native "wordprobe"
    controlBody := "A\\wordprobe{\\textbf{X}}\\wordprobe{\\textbf{X}}/Z"
    visible := "AXX/Z", roles := #[("wordprobe", 2), ("maketitle", 0)] }

  -- Builtin refusals still keep native ink.
  for (label, replacement) in #[
      ("empty", ""), ("unknown", "\\begingroup\\unreadprobe\\endgroup")] do
    let pre := "\\title{Title}\\author{Author}\\date{}"
    let (ds, out, html, _) := sourceArtifacts fonts
      (dvDoc (pre ++ "\\renewcommand\\maketitle{" ++ replacement ++ "}") "\\maketitle/Z")
    let (_, cout, chtml, _) := sourceArtifacts fonts (dvDoc pre "\\maketitle/Z")
    check ref s!"macro forwarding {label} builtin replacement remains refused"
      (ds.any (·.code == "W0361") && ds.all (fun d => d.severity == .note || d.code == "W0361"))
    check ref s!"macro forwarding {label} builtin refusal preserves both artifacts"
      (html == chtml && shippedBodyGlyphs out == shippedBodyGlyphs cout)

end Tests
