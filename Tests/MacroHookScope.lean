import Tests.Support

open LeanTex.Core

namespace Tests

-- These nine expectations are pinned independently to LuaLaTeX's emitted
-- PDF text by scripts/macro-defaults-oracle.lean --case hook-scope.
private def macroHookScopeCases : Array (String × String × String × String) := #[
  ("begin-hook-flag",
    r"\newif\ifprobeFlag\AtBeginDocument{\probeFlagtrue}",
    r"\ifprobeFlag T\else F\fi", "T"),
  ("begin-hook-flag-timing",
    r"\newif\ifprobeFlag\AtBeginDocument{\probeFlagtrue}" ++
      r"\ifprobeFlag\def\probeBefore{BAD}\else\def\probeBefore{OK}\fi",
    r"\probeBefore/\ifprobeFlag T\else F\fi", "OK/T"),
  ("end-hook-flag-timing",
    r"\usepackage{etoolbox}\newif\ifprobeFlag\AtEndPreamble{\probeFlagtrue}" ++
      r"\ifprobeFlag\def\probeBefore{BAD}\else\def\probeBefore{OK}\fi",
    r"\probeBefore/\ifprobeFlag T\else F\fi", "OK/T"),
  ("begin-hook-optional-binding",
    r"\AtBeginDocument{\newcommand{\probe}[1][D]{(#1)}}",
    r"\probe/\probe[E]/\probe[]", "(D)/(E)/()"),
  ("begin-hook-flag-read",
    r"\newif\ifprobeFlag\AtBeginDocument{\ifprobeFlag T\else F\fi}\probeFlagtrue",
    "/T", "T/T"),
  ("hook-phase-order",
    r"\usepackage{etoolbox}\newif\ifprobeFlag" ++
      r"\AtBeginDocument{\ifprobeFlag T\else F\fi\probeFlagfalse}" ++
      r"\AtEndPreamble{\probeFlagtrue}",
    r"/\ifprobeFlag T\else F\fi", "T/F"),
  ("brace-flag",
    r"\newif\ifprobeFlag",
    r"{\probeFlagtrue\ifprobeFlag T\else F\fi}/\ifprobeFlag T\else F\fi", "T/F"),
  ("begingroup-flag",
    r"\newif\ifprobeFlag",
    r"\begingroup\probeFlagtrue\ifprobeFlag T\else F\fi" ++
      r"\endgroup/\ifprobeFlag T\else F\fi", "T/F"),
  ("bgroup-flag",
    r"\newif\ifprobeFlag",
    r"\bgroup\probeFlagtrue\ifprobeFlag T\else F\fi\egroup/\ifprobeFlag T\else F\fi", "T/F")
]

-- The argument delimiters do not execute as a group. Only an additional
-- group in the replacement retains local scope. The external oracle pins
-- these same seven expectations for all four direct/alias definition forms.
private def requiredArgumentScopeCases : Array (String × String × String × String) :=
  #["def", "newcommand"].flatMap fun kind => #[false, true].flatMap fun alias =>
    let route := kind ++ if alias then "-alias" else ""
    let call := if alias then r"\aliasprobe" else r"\passprobe"
    let define (replacement : String) :=
      r"\newif\ifchoiceprobe\def\wordprobe{Old}\def\newwordprobe{New}" ++
      (if kind == "def" then r"\def\passprobe#1{" else r"\newcommand{\passprobe}[1]{") ++
      replacement ++ "}" ++ (if alias then r"\let\aliasprobe\passprobe" else "")
    let probe (label replacement body expected : String) :=
      ("required-argument-" ++ route ++ "-" ++ label, define replacement, body, expected)
    #[
      probe "identity-flag" "#1"
        (call ++ r"{\choiceprobetrue}\ifchoiceprobe Set\else Unset\fi") "Set",
      probe "identity-let" "#1"
        (call ++ r"{\let\wordprobe\newwordprobe}\wordprobe") "New",
      probe "unused" "Kept"
        (call ++ r"{\choiceprobetrue\let\wordprobe\newwordprobe" ++
          r"\ifchoiceprobe WrongSet\else WrongUnset\fi}/" ++
          r"\ifchoiceprobe Set\else Unset\fi/\wordprobe") "Kept/Unset/Old",
      probe "repeated" "#1#1"
        (r"\ifchoiceprobe Set\else Unset\fi/" ++ call ++
          r"{\ifchoiceprobe B\else A\fi\choiceprobetrue}/" ++
          r"\ifchoiceprobe Set\else Unset\fi") "Unset/AB/Set",
      probe "repeated-order" r"\ifchoiceprobe Set\else Unset\fi/#1#1"
        (call ++ r"{\ifchoiceprobe B\else A\fi\choiceprobetrue}/" ++
          r"\ifchoiceprobe Set\else Unset\fi") "Unset/AB/Set",
      probe "grouped-flag" "#1"
        (call ++ r"{{\choiceprobetrue\ifchoiceprobe Set\else Unset\fi}}/" ++
          r"\ifchoiceprobe Set\else Unset\fi") "Set/Unset",
      probe "grouped-let" "#1"
        (call ++ r"{{\let\wordprobe\newwordprobe\wordprobe}}/\wordprobe") "New/Old"
    ]

private def copiedHelperCases : Array (String × String × String × String) :=
  #[false, true].flatMap fun optional => #[false, true].map fun grouped =>
    let setup := r"\newif\ifprobeFlag\def\helperprobe#1{\probeFlagfalse#1}" ++
      (if optional then r"\newcommand{\sourceprobe}[1][\helperprobe{}]{#1}"
       else r"\def\sourceprobe#1{\helperprobe{#1}}") ++
      r"\def\helperprobe#1{\probeFlagtrue#1}"
    let call := if optional then r"\aliasprobe" else r"\aliasprobe{}"
    let selected := r"\ifprobeFlag T\else F\fi"
    ("copied-helper-" ++ (if optional then "optional" else "required") ++
        (if grouped then "-local" else "-top"),
      setup ++ (if grouped then r"\def\passprobe#1{#1}" else r"\let\aliasprobe\sourceprobe"),
      if grouped then r"\passprobe{{\let\aliasprobe\sourceprobe" ++ call ++ selected ++ "}}/" ++ selected
      else call ++ selected,
      if grouped then "T/F" else "T")

/-- Deferred hooks read and change the state at execution, while actual
TeX groups restore local flags without splitting the surrounding paragraph.
Required macro arguments execute after substitution, not during scanning.
Compare complete laid-out pages and serialized typed HTML against literal
documents: page/line boundaries, positioning, attributes and whitespace
remain visible. Positive controls prevent matching two empty artifacts. -/
def macroHookScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let article (pre body : String) := dvDoc (r"\pagestyle{empty}" ++ pre) body
  let artifacts := sourceArtifacts fonts
  let probes := macroHookScopeCases ++ requiredArgumentScopeCases ++ copiedHelperCases
  for (label, pre, body, expected) in probes do
    let name := "macro hook scope " ++ label
    let (controlDs, controlOut, controlHtml, controlText) := artifacts (article "" expected)
    let (ds, out, html, _) := artifacts (article pre body)
    t (name ++ ": literal control has no loss") (controlDs.all (·.severity == .note))
    t (name ++ ": literal control ships exactly one body line")
      ((bodyLines controlOut).map (fun l => (lineText l).trimAscii.toString) == #[expected])
    t (name ++ ": literal control has the expected visible HTML")
      (controlText.trimAscii.toString == expected)
    t (name ++ ": no loss") (ds.all (·.severity == .note))
    t (name ++ ": Layout.Out equals the literal document")
      (reprStr out.pages == reprStr controlOut.pages)
    t (name ++ ": typed HTML equals the literal document") (html == controlHtml)
  let (_, joinedOut, joinedHtml, joinedText) := artifacts (article "" "T/F")
  let (_, splitOut, splitHtml, splitText) := artifacts (article "" r"T/\par F")
  t "macro hook scope comparison: same concatenated text does not hide a paragraph break"
    (joinedText == splitText &&
      String.join ((bodyLines joinedOut).toList.map (lineText · false)) ==
        String.join ((bodyLines splitOut).toList.map (lineText · false)) &&
      reprStr joinedOut.pages != reprStr splitOut.pages && joinedHtml != splitHtml)
  let (_, spacedOut, spacedHtml, _) := artifacts (article "" "T/ F")
  t "macro hook scope comparison: an interior space changes both artifacts"
    (reprStr joinedOut.pages != reprStr spacedOut.pages && joinedHtml != spacedHtml)

end Tests
