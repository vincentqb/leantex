module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- A definition stores its replacement text; only invoking it installs the definitions that text
contains. -/
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
  -- A name is looked up when its caller expands, as TeX does, whichever was defined first.
  page "forward reference"
    "\\newcommand{\\fwdA}{[\\fwdB]}\\newcommand{\\fwdB}{B\\fwdC}\\newcommand{\\fwdC}{c}"
    "\\fwdA{} $\\fwdA$" "[Bc] $[Bc]$"
  page "use-time redefinition"
    "\\newcommand{\\useX}{1}\\newcommand{\\useY}{\\useX}\\renewcommand{\\useX}{2}" "\\useY" "2"
  page "environment halves"
    "\\newenvironment{fwdenv}{(\\fwdD}{\\fwdD)}\\newcommand{\\fwdD}{d}"
    "\\begin{fwdenv}in\\end{fwdenv}" "(dind)"
  page "environment halves in a call"
    ("\\newcommand{\\fwdG}{\\begin{fwdby}x\\end{fwdby}}\\newcommand{\\fwdH}{h}" ++
      "\\newenvironment{fwdby}{[\\fwdH}{]}") "\\fwdG" "[hx]"
  page "environment halves see a redefinition"
    ("\\newcommand{\\fwdQ}{q}\\newenvironment{fwdbx}{[\\fwdQ}{]}" ++
      "\\newcommand{\\fwdC}{\\begin{fwdbx}x\\end{fwdbx}}\\renewcommand{\\fwdQ}{r}") "\\fwdC" "[rx]"
  page "body definition" "\\newcommand{\\fwdF}{[\\fwdE]}" "\\newcommand{\\fwdE}{e}\\fwdF" "[e]"
  let (_, ds) := elabStr (dvDoc "\\newcommand{\\recA}{a\\recB}\\newcommand{\\recB}{b\\recA}" "\\recA")
  t "macro binding mutual recursion stops, named once"
    ((ds.filter (·.code == "W0301")).size == 1)

end Tests
