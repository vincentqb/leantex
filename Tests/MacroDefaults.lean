import Tests.Support

open LeanTex.Core

namespace Tests

/-- LaTeX's optional first argument is selected and substituted before a
replacement text runs. Definitions and defaults remain inert until use;
an explicit empty argument differs from an omitted one. The witnesses read
both artifacts, including the source after each call. -/
def macroDefaultChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let page (label pre body expected : String) : IO Unit :=
    sourceTextChecks ref fonts s!"macro defaults {label}"
      (dvDoc pre body) (dvDoc "" expected)
  for (label, definer) in #[
      ("newcommand", "\\newcommand\\installerprobe"),
      ("newcommand star", "\\newcommand*\\installerprobe"),
      ("providecommand", "\\providecommand\\installerprobe"),
      ("renewcommand", "\\newcommand\\installerprobe{}\\renewcommand\\installerprobe")] do
    let install := definer ++ "[1][Default]{\\def\\installedprobe{#1}}"
    page (label ++ " unused") install
      "\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail" "Absent Tail"
    page (label ++ " default") install
      "\\installerprobe\\installedprobe{} Tail" "Default Tail"
    page (label ++ " explicit") install
      "\\installerprobe[Explicit]\\installedprobe{} Tail" "Explicit Tail"
    page (label ++ " empty") install
      "\\installerprobe[]\\ifdefined\\installedprobe Present\\else Missing\\fi{} \\installedprobe{} Tail"
      "Present Tail"
    page (label ++ " grouped closing bracket") install
      "\\installerprobe[{A]B}]\\installedprobe{} Tail" "A]B Tail"
    page (label ++ " skipped") install
      "\\iffalse\\installerprobe\\fi\\ifdefined\\installedprobe Leaked\\else Absent\\fi{} Tail"
      "Absent Tail"
    let pair := definer ++ "[2][Default]{\\def\\installedprobe{#1#2}}"
    page (label ++ " required with default") pair
      "\\installerprobe{Required}\\installedprobe{} Tail" "DefaultRequired Tail"
    page (label ++ " single token tail") pair
      "\\installerprobe[X]YZ\\installedprobe{} Tail" "ZXY Tail"
  page "ordinary text" "\\newcommand\\textprobe[2][Default]{#1 #2}"
    "\\textprobe{Required} \\textprobe[Explicit]{Required} \\textprobe[]{Required} Tail"
    "Default Required Explicit Required Required Tail"
  page "ordinary wrapper"
    "\\newcommand\\textprobe[2][Default]{#1 #2}\\newcommand\\wrapperprobe[1]{\\textprobe{#1}}"
    "\\wrapperprobe{Required} Tail" "Default Required Tail"
  page "conditional default" "\\newcommand\\branchprobe[1][1]{\\ifnum#1=1 One\\else Other\\fi}"
    "\\branchprobe{} \\branchprobe[2] Tail" "One Other Tail"
  let flag := "\\newif\\ifchoiceprobe\\newcommand\\chooseprobe[1][\\choiceprobetrue]{#1}"
  page "default flag unused" flag "\\ifchoiceprobe Leaked\\else Unset\\fi{} Tail" "Unset Tail"
  page "default flag used" flag
    "\\chooseprobe\\ifchoiceprobe Set\\else Missing\\fi{} Tail" "Set Tail"
  page "default flag overridden" flag
    "\\chooseprobe[\\choiceprobefalse]\\ifchoiceprobe Wrong\\else Unset\\fi{} Tail" "Unset Tail"
  page "provision keeps meaning"
    ("\\newcommand\\textprobe[1][First]{#1}" ++
      "\\providecommand\\textprobe[1][\\def\\leakedprobe{Leak}]{Discarded}")
    "\\textprobe\\ifdefined\\leakedprobe Leaked\\else Absent\\fi{} Tail" "First Absent Tail"
  page "scoped definition"
    "\\newcommand\\textprobe[1][Outer]{#1}"
    "{\\renewcommand\\textprobe[1][Inner]{#1}\\textprobe{}} \\textprobe{} Tail"
    "Inner Outer Tail"
  page "let optional alias"
    "\\newcommand\\textprobe[1][Default]{#1}\\let\\aliasprobe\\textprobe"
    "\\aliasprobe{} \\aliasprobe[Explicit] Tail" "Default Explicit Tail"
  for (label, definition, use, expected) in #[
      ("plain", "\\def\\textprobe{Old}", "\\aliasprobe", "Old"),
      ("required", "\\def\\textprobe#1{Old#1}", "\\aliasprobe{X}", "OldX"),
      ("newcommand", "\\newcommand\\textprobe[1]{Old#1}", "\\aliasprobe{X}", "OldX")] do
    page ("let copies " ++ label)
      (definition ++ "\\let\\aliasprobe = \\textprobe")
      (use ++ "\\def\\textprobe{New}/" ++ use ++ "{} Tail")
      (expected ++ "/" ++ expected ++ " Tail")
  page "let alias chain"
    "\\def\\textprobe#1{Old#1}\\let\\middleprobe\\textprobe\\let\\aliasprobe\\middleprobe"
    "\\def\\middleprobe{New}\\aliasprobe{X} Tail" "OldX Tail"
  page "scoped flag and meaning"
    "\\newif\\ifchoiceprobe\\def\\textprobe{Outer}\\def\\sameprobe{Outer}"
    ("{\\choiceprobetrue\\def\\textprobe{Inner}\\def\\localprobe{}" ++
      "\\ifchoiceprobe T\\else F\\fi/\\ifx\\textprobe\\sameprobe Same\\else Different\\fi}/" ++
      "\\ifchoiceprobe T\\else F\\fi/\\ifx\\textprobe\\sameprobe Same\\else Different\\fi/" ++
      "\\ifdefined\\localprobe Leaked\\else Absent\\fi")
    "T/Different/F/Same/Absent"
  page "global definition outlives nested groups" ""
    "{\\def\\textprobe{Local}{\\gdef\\textprobe{Global}}}\\ifdefined\\textprobe\\textprobe\\else Missing\\fi"
    "Global"
  page "ifx optional wrappers name their command"
    "\\newcommand\\firstprobe[1][Default]{#1}\\newcommand\\secondprobe[1][Default]{#1}"
    "\\ifx\\firstprobe\\secondprobe Same\\else Different\\fi{} Tail" "Different Tail"
  page "ifx let preserves wrapper"
    "\\newcommand\\firstprobe[1][Default]{#1}\\let\\secondprobe\\firstprobe"
    "\\ifx\\firstprobe\\secondprobe Same\\else Different\\fi{} Tail" "Same Tail"
  let alias := "\\newcommand\\textprobe[1][D]{O#1}\\let\\aliasprobe\\textprobe"
  page "alias follows scoped helper" alias
    "\\textprobe/{\\renewcommand\\textprobe[1][E]{N#1}\\textprobe/\\aliasprobe}/\\textprobe/\\aliasprobe"
    "OD/NE/ND/OD/OD"
  for (label, renewal, expected) in #[
      ("body", "\\renewcommand\\textprobe[1][D]{N#1}", "ND"),
      ("arity", "\\renewcommand\\textprobe[2][D]{N(#1:#2)}", "N(D:Q)"),
      ("star", "\\renewcommand*\\textprobe[1][D]{N#1}", "ND")] do
    page ("ifx wrapper ignores helper " ++ label) alias
      (renewal ++ "\\ifx\\textprobe\\aliasprobe Same\\else Different\\fi/\\aliasprobe" ++
        (if label == "arity" then " Q" else ""))
      ("Same/" ++ expected)
  page "alias keeps default" alias
    "\\renewcommand\\textprobe[1][E]{N#1}\\ifx\\textprobe\\aliasprobe Same\\else Different\\fi/\\textprobe/\\aliasprobe"
    "Different/NE/ND"
  page "plain renewal preserves optional helper" alias
    "\\renewcommand\\textprobe[1]{N#1}\\textprobe{X}/\\aliasprobe" "NX/OD"
  page "ifx default group identity" alias
    ("\\renewcommand\\textprobe[1][{D}]{N#1}\\ifx\\textprobe\\aliasprobe Same\\else Different\\fi/" ++
      "\\renewcommand\\textprobe[1][{{D}}]{N#1}\\ifx\\textprobe\\aliasprobe Same\\else Different\\fi")
    "Same/Different"
  page "one optional argument group stripped"
    ("\\newif\\ifchoiceprobe" ++
      "\\newcommand\\firstprobe[1][{\\choiceprobetrue}]{#1}" ++
      "\\newcommand\\secondprobe[1][{{\\choiceprobetrue}}]{#1}")
    ("\\firstprobe\\ifchoiceprobe T\\else F\\fi/\\choiceprobefalse" ++
      "\\secondprobe\\ifchoiceprobe T\\else F\\fi/" ++
      "\\firstprobe[{\\choiceprobetrue}]\\ifchoiceprobe T\\else F\\fi/\\choiceprobefalse" ++
      "\\firstprobe[{{\\choiceprobetrue}}]\\ifchoiceprobe T\\else F\\fi")
    "T/F/T/F"
  page "selected argument executes at each substitution"
    ("\\newif\\ifchoiceprobe" ++
      "\\newcommand\\textprobe[1][\\ifchoiceprobe B\\else A\\fi\\choiceprobetrue]{#1#1}")
    "\\textprobe/\\ifchoiceprobe T\\else F\\fi" "AB/T"
  page "unused default stays inert"
    "\\newif\\ifchoiceprobe\\newcommand\\textprobe[1][\\choiceprobetrue]{OK}"
    "\\textprobe/\\ifchoiceprobe T\\else F\\fi" "OK/F"
  page "substitution preserves order"
    ("\\newif\\ifchoiceprobe" ++
      "\\newcommand\\textprobe[1][\\choiceprobetrue]{\\ifchoiceprobe T\\else F\\fi#1\\ifchoiceprobe T\\else F\\fi}")
    "\\textprobe" "FT"

end Tests
