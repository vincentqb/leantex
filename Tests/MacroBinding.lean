module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- A definition stores its replacement text. Only invoking it installs
the definitions that text contains (TeXbook, chapters 20 and 24).
The witnesses read shipped layout and typed HTML, including a provision
between storing an installer and invoking it. -/
def macroBindingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let installers : Array (String × String) := #[
    ("def", "\\def\\installerprobe"),
    ("gdef", "\\gdef\\installerprobe"),
    ("newcommand", "\\newcommand{\\installerprobe}"),
    ("providecommand", "\\providecommand{\\installerprobe}")]
  let ink (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let page (label pre body expected : String) : IO Unit := do
    let (doc, ds) := elabStr (dvDoc pre body)
    let (control, controlDs) := elabStr (dvDoc "" expected)
    let out := layoutOf fonts doc
    let expectedOut := layoutOf fonts control
    let (_, tree, hds) := HtmlDoc.emitTree {} doc
    let (_, controlTree, _) := HtmlDoc.emitTree {} control
    t s!"macro binding {label}: no loss"
      ((ds ++ hds ++ controlDs).all (·.severity == .note))
    t s!"macro binding {label}: shipped layout"
      (ink (String.join ((allLines out).toList.map lineText)) ==
        ink (String.join ((allLines expectedOut).toList.map lineText)))
    t s!"macro binding {label}: typed HTML"
      (ink (shownTextList "" tree.toList) == ink (shownTextList "" controlTree.toList))
  for (label, definer) in installers do
    let install := definer ++ "{\\def\\installedprobe{Installed}}"
    page (label ++ " unused") install
      "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail" "Absent Tail"
    page (label ++ " invoked") install
      ("\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} " ++
        "\\installerprobe\\ifdefined\\installedprobe Present\\else Missing\\fi{} Tail")
      "Absent Present Tail"
    page (label ++ " fresh provision")
      (install ++ "\\providecommand{\\installedprobe}{Provided}")
      "\\installedprobe{} Tail" "Provided Tail"
    page (label ++ " active replacement")
      (install ++ "\\providecommand{\\installedprobe}{Provided}\\installerprobe")
      "\\installedprobe{} Tail" "Installed Tail"
    page (label ++ " skipped use") install
      ("\\iffalse\\installerprobe\\fi" ++
        "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail")
      "Absent Tail"

end Tests
