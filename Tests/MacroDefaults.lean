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

/-- A deferred call observes the state at its execution phase. Settlement,
refusal recovery and delimiter recovery must preserve that same boundary.
LaTeX's opening ignore-space scan stops at a nonexpandable command, even
when compatibility later removes that command. These guards compare both
complete artifacts with controls, including their internal whitespace. -/
def macroPhaseChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let article (pre body : String) := dvDoc (r"\pagestyle{empty}" ++ pre) body
  let same (label source control : String) (losses : List String := []) : IO Unit := do
    let (ds, out, html, _) := sourceArtifacts fonts source
    let (cds, cout, chtml, ctext) := sourceArtifacts fonts control
    let named (ds : Array Diag) :=
      ds.all (fun d => d.severity == .note || losses.contains d.code)
    t (label ++ ": source has only the declared losses") (named ds)
    t (label ++ ": control has only the declared losses") (named cds)
    for code in losses do
      t (label ++ ": names " ++ code) (ds.any (·.code == code))
    t (label ++ ": control ships visible content")
      (!(bodyLines cout).isEmpty && !ctext.trimAscii.isEmpty)
    t (label ++ ": complete PDF layout agrees") (reprStr out.pages == reprStr cout.pages)
    t (label ++ ": complete typed HTML agrees") (html == chtml)
  for (label, test, after, expected) in #[
      ("class true", r"\IfClassLoadedTF{article}{Chosen}{Other}", "", "Chosen"),
      ("class false", r"\IfClassLoadedTF{book}{Chosen}{Other}", "", "Other"),
      ("class false-only", r"\IfClassLoadedF{book}{Chosen}", "", "Chosen"),
      ("package later", r"\IfPackageLoadedTF{amsmath}{Chosen}{Other}",
        r"\usepackage{amsmath}", "Chosen"),
      ("package absent", r"\IfPackageLoadedTF{amsmath}{Chosen}{Other}", "", "Other")] do
    let pre (body : String) := r"\title{Fallback}\renewcommand{\maketitle}{" ++ body ++ "}" ++ after
    same ("macro phase builtin " ++ label)
      (article (pre test) r"\maketitle Tail") (article (pre expected) r"\maketitle Tail")
  for hook in ["AtBeginDocument", "AtEndPreamble"] do
    let flag := r"\newif\ifscopeprobe"
    let read := r"\ifscopeprobe Leaked\else Scoped\fi{} Tail"
    same ("macro phase refused body " ++ hook)
      (article flag ("\\" ++ hook ++ r"{\scopeprobetrue}" ++ read))
      (article flag (r"{\scopeprobetrue}" ++ read)) ["W0340"]
    same ("macro phase refused nested " ++ hook)
      (article (flag ++ r"\AtBeginDocument{\" ++ hook ++ r"{\scopeprobetrue}" ++ read ++ "}") "/End")
      (article (flag ++ r"\AtBeginDocument{{\scopeprobetrue}" ++ read ++ "}") "/End") ["W0340"]
  let pair := r"\def\pairprobe#1,#2\relax{#1}"
  same "macro phase deferred delimited call"
    (article (pair ++ r"\AtBeginDocument{Lead \pairprobe A,B\relax{} Tail.}") "End.")
    (article (pair ++ r"\AtBeginDocument{Lead \pairprobe{A}{B}{} Tail.}") "End.")
    ["W0357", "W0301"]
  let first := r"\def\scanprobe#1.{#1}"
  let later := r"\def\scanprobe#1;{#1}"
  same "macro phase deferred last preamble signature"
    (article (first ++ r"\AtBeginDocument{Lead \scanprobe A; Tail.}" ++ later) "End.")
    (article (first ++ r"\AtBeginDocument{Lead \scanprobe{A} Tail.}" ++ later) "End.")
    ["W0357", "W0301"]
  let endDef := r"\usepackage{etoolbox}\AtEndPreamble{" ++ later ++ "}"
  same "macro phase signature defined in end hook"
    (article (endDef ++ r"\AtBeginDocument{Lead \scanprobe A; Tail.}") "End.")
    (article (endDef ++ r"\AtBeginDocument{Lead \scanprobe{A} Tail.}") "End.")
    ["W0357", "W0301"]
  same "macro phase later body signature stays later"
    (article (later ++ r"\AtBeginDocument{Lead \scanprobe A; Tail.}") (first ++ "End."))
    (article (later ++ r"\AtBeginDocument{Lead \scanprobe{A} Tail.}") (first ++ "End."))
    ["W0357", "W0301"]
  for (label, pre, body, expected) in #[
      ("opening newline", r"\AtBeginDocument{T}", "/T", "T/T"),
      ("hook owns trailing space", r"\AtBeginDocument{T }", "/T", "T /T"),
      ("empty group stops scan", r"\AtBeginDocument{T}", "{} /T", "T /T"),
      ("logging command stops scan", r"\AtBeginDocument{T}",
        r"\PackageInfo{probe}{log} /T", "T /T"),
      ("logging warning stops scan", r"\AtBeginDocument{T}",
        r"\PackageWarningNoLine{probe}{log} /T", "T /T"),
      ("macro expands to space", r"\AtBeginDocument{T}\def\spaceprobe{ }",
        r"\spaceprobe/T", "T/T"),
      ("macro expands to barrier",
        r"\AtBeginDocument{T}\def\barrierprobe{\PackageInfo{probe}{log} }",
        r"\barrierprobe/T", "T /T"),
      ("selected empty branch stays transparent", r"\AtBeginDocument{T}",
        r"\IfClassLoadedTF{article}{}{Hidden} /T", "T/T"),
      ("paragraph stops scan", r"\AtBeginDocument{T}", r"\par/T", "T\\par/T")] do
    same ("macro phase whitespace " ++ label) (article pre body) (article "" expected)

end Tests
