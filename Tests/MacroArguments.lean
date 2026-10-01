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
  -- A parameterized numeric macro is not a constant. The conditional
  -- reader must not consume its body without the argument TeX would read.
  let unknown := dvDoc "" "\\def\\numberprobe#1{1}\\ifnum\\numberprobe=1 Bad\\else Other\\fi"
  t "macro arguments: a numeric macro with unbound arguments stays unread"
    ((elabStr unknown).2.all (·.code != "N0114"))

end Tests
