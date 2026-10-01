import Tests.Support

open LeanTex.Core

namespace Tests

/-- Undelimited arguments are substituted before a live replacement text is
run (TeXbook chapter 20). Each case compares all shipped text and the typed
HTML's visible text with its literal control, including text after the call.
The definitions themselves never install the names in their bodies. -/
def macroArgumentChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let ink (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let page (label pre body expected : String) : IO Unit := do
    let source := dvDoc pre body
    let (doc, ds) := elabStr source
    let (_, tree, hds) := HtmlDoc.emitTree {} doc
    let control := dvDoc "" expected
    let (_, expectedTree, _) := HtmlDoc.emitTree {} (elabStr control).1
    t s!"macro arguments {label}: no loss" ((ds ++ hds).all (·.severity == .note))
    t s!"macro arguments {label}: shipped layout"
      (ink (allTextOf fonts source) == ink (allTextOf fonts control))
    t s!"macro arguments {label}: typed HTML"
      (ink (shownTextList "" tree.toList) == ink (shownTextList "" expectedTree.toList))
  for (label, definer) in #[
      ("def", "\\def\\installerprobe#1"),
      ("gdef", "\\gdef\\installerprobe#1"),
      ("newcommand", "\\newcommand{\\installerprobe}[1]"),
      ("providecommand", "\\providecommand{\\installerprobe}[1]")] do
    let install := definer ++ "{\\def\\installedprobe{#1}}"
    page (label ++ " unused") install
      "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail" "Absent Tail"
    page (label ++ " invoked") install
      ("\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} " ++
        "\\installerprobe{Installed}\\ifdefined\\installedprobe Present\\else Missing\\fi{} " ++
        "\\installedprobe{} Tail") "Absent Present Installed Tail"
    page (label ++ " provision")
      (install ++ "\\providecommand{\\installedprobe}{Provided}")
      "\\installedprobe{} Tail" "Provided Tail"
    page (label ++ " replacement")
      (install ++ "\\providecommand{\\installedprobe}{Provided}\\installerprobe{Installed}")
      "\\installedprobe{} Tail" "Installed Tail"
    page (label ++ " token") install
      "\\installerprobe XY\\installedprobe{} Tail" "YX Tail"
    page (label ++ " skipped") install
      "\\iffalse\\installerprobe{Installed}\\fi\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail"
      "Absent Tail"
  page "name argument" "\\def\\installerprobe#1#2{\\def#1{#2}}"
    "\\installerprobe\\installedprobe{Installed}\\ifdefined\\installedprobe Present\\else Missing\\fi{} \\installedprobe{} Tail"
    "Present Installed Tail"
  page "parameter followed by a digit" "\\def\\installerprobe#1{\\def\\installedprobe{#10}}"
    "\\installerprobe{Value}\\installedprobe{} Tail" "Value0 Tail"
  page "nested parameter" "\\def\\installerprobe#1{\\def\\installedprobe##1{#1##1}}"
    "\\installerprobe{First}\\installedprobe{Second} Tail" "FirstSecond Tail"
  page "nullary nested parameter" "\\def\\installerprobe{\\def\\installedprobe##1{##1}}"
    "\\installerprobe\\installedprobe{Installed} Tail" "Installed Tail"
  page "conditional arguments" "\\newcommand\\branchprobe[1]{\\ifnum#1=1 One\\else Other\\fi}"
    "\\branchprobe{1} \\branchprobe{2} Tail" "One Other Tail"
  for definer in #["newcommand", "providecommand"] do
    let install := "\\" ++ definer ++ "\\installerprobe[0]{\\def\\installedprobe{Installed}}"
    page (definer ++ " explicit zero arity unused") install
      "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail" "Absent Tail"
    page (definer ++ " explicit zero arity invoked") install
      ("\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} \\installerprobe" ++
        "\\ifdefined\\installedprobe Present\\else Missing\\fi{} \\installedprobe{} Tail")
      "Absent Present Installed Tail"
  -- LuaLaTeX takes Different for significant replacement spaces (also
  -- inside groups) and for a paragraph versus a space. Positions, runs of
  -- source whitespace and whitespace ending a control word do not count.
  -- Read the chosen branch from both artifacts: trimming their whitespace
  -- cannot hide a wrong comparison of whitespace in the stored definitions.
  for (label, left, right, expected) in #[
      ("ifx leading space", " #1", "#1", "Different"),
      ("ifx trailing space", "#1 ", "#1", "Different"),
      ("ifx group leading space", "{ #1}", "{#1}", "Different"),
      ("ifx group trailing space", "{#1 }", "{#1}", "Different"),
      ("ifx paragraph versus space", "#1\n\nX", "#1 X", "Different"),
      ("ifx equal tokens at different positions", "#1", "#1", "Same"),
      ("ifx equal space runs", " #1 ", "   #1   ", "Same"),
      ("ifx ignored control word space", "\\tokenprobe #1", "\\tokenprobe#1", "Same"),
      ("ifx control word boundary", "\\tokenprobe X#1", "\\tokenprobeX#1", "Different"),
      ("ifx control symbol space", "\\! #1", "\\!#1", "Different")] do
    page label ("\\def\\firstprobe#1{" ++ left ++ "}\\def\\secondprobe#1{" ++ right ++ "}")
      "\\ifx\\firstprobe\\secondprobe Same\\else Different\\fi{} Tail" (expected ++ " Tail")
  -- Binding can split a run of character tokens across Raw.word nodes.
  -- LuaLaTeX still compares the installed text with literal ab as Equal.
  page "ifx expanded adjacent words"
    ("\\def\\installerprobe#1{\\def\\firstprobe{a#1}}" ++
      "\\installerprobe{b}\\def\\secondprobe{ab}")
    "\\ifx\\firstprobe\\secondprobe Equal\\else Different\\fi{} Tail" "Equal Tail"
  page "argument spaces" "\\def\\branchprobe#1{\\ifnum#1=12 Hit\\else Miss\\fi}"
    "\\branchprobe   {12} Tail" "Hit Tail"
  page "definition control word space" "\\def\\branchprobe #1{\\ifnum#1=12 Hit\\else Miss\\fi}"
    "\\branchprobe{12} Tail" "Hit Tail"
  page "argument newline" "\\def\\branchprobe#1#2{\\ifnum#1=1 #2\\else Miss\\fi}"
    "\\branchprobe 1\n{Hit} Tail" "Hit Tail"
  -- Significant parameter spaces are delimiters (TeXbook chapter 20).
  -- LuaLaTeX ships Hit Tail for each call below. Our declared boundary is
  -- whole-definition refusal, W0357, with the call's arguments preserved:
  -- neither the conditional nor a nested definition may execute. A nested
  -- body belongs to that one refusal, never an additional W0104.
  let refused (label pre body expected : String) (called : Bool) : IO Unit := do
    let source := dvDoc pre body
    let (doc, ds) := elabStr source
    let (_, tree, hds) := HtmlDoc.emitTree {} doc
    let control := dvDoc "" expected
    let (_, expectedTree, _) := HtmlDoc.emitTree {} (elabStr control).1
    let losses := (ds ++ hds).filter (·.severity != .note)
    t s!"macro arguments {label}: one W0357"
      ((losses.filter (·.code == "W0357")).size == 1)
    t s!"macro arguments {label}: no secondary loss"
      (losses.all fun d => d.code == "W0357" || (called && d.code == "W0301"))
    t s!"macro arguments {label}: refused shipped layout"
      (ink (allTextOf fonts source) == ink (allTextOf fonts control))
    t s!"macro arguments {label}: refused typed HTML"
      (ink (shownTextList "" tree.toList) == ink (shownTextList "" expectedTree.toList))
  for (label, params, replacement, call, expected) in #[
      ("delimiter space", "#1 ", "\\ifnum#1=12 Hit\\else Miss\\fi", "\\branchprobe12 Tail", "12 Tail"),
      ("delimiter tab", "#1\t", "\\ifnum#1=12 Hit\\else Miss\\fi", "\\branchprobe12 Tail", "12 Tail"),
      ("delimiter newline", "#1\n", "\\ifnum#1=12 Hit\\else Miss\\fi", "\\branchprobe12 Tail", "12 Tail"),
      ("delimiter between parameters", "#1 #2", "\\ifnum#1=12 #2\\else Miss\\fi",
        "\\branchprobe12 {Hit} Tail", "12 Hit Tail")] do
    let pre := "\\def\\branchprobe" ++ params ++ "{" ++ replacement ++ "}"
    refused (label ++ " unused") pre "Tail" "Tail" false
    refused (label ++ " invoked") pre call expected true
  let delimitedInstall := "\\def\\installerprobe#1!{\\def\\installedprobe{#1}}"
  refused "delimited nested definition unused" delimitedInstall
    "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail" "Absent Tail" false
  -- LuaLaTeX ships Present Tail; refusal must leave installedprobe absent.
  refused "delimited nested definition invoked" delimitedInstall
    "\\installerprobe Value!\\ifdefined\\installedprobe Present\\else Missing\\fi{} Tail"
    "Value Missing Tail" true
  -- A parameterized numeric macro is not a constant. The conditional
  -- reader must not consume its body without the argument TeX would read.
  let unknown := dvDoc "" "\\def\\numberprobe#1{1}\\ifnum\\numberprobe=1 Bad\\else Other\\fi"
  t "macro arguments: a numeric macro with unbound arguments stays unread"
    ((elabStr unknown).2.all (·.code != "N0114"))

end Tests
