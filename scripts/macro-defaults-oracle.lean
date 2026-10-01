import Lean

/-!
External optional-first-argument oracle. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/macro-defaults-oracle.lean --selftest
  lake env lean --run scripts/macro-defaults-oracle.lean --report --keep

The default mode fails on any difference. --report permits measured engine
differences, but NEVER a missing/failed/drifted reference or an observation
fault. --reference-only checks the reference pins without needing leantex.
--case NAME selects names containing NAME; --engine PATH selects a binary.
All sources, PDFs, logs and caches live in a fresh temporary directory;
--keep retains it for inspection. Each child is a fixed executable/argv
invocation with a timeout, never a shell. Requires LuaLaTeX, kpsewhich,
Poppler pdftotext and GNU timeout. This is an external report, not a tier.

Invariant: a match requires two successful builds, two successfully read
PDFs, and the entire extracted text of EACH equal to the fixed expectation.
A failed observation has no text, even if a failed build left a PDF. Only
CRLF, form feeds and outer whitespace are normalized; interior whitespace,
glyph order, extra ink and missing ink remain significant. This reading is
blind to pagination, outer whitespace, geometry and font appearance, not
to the spaces inside a parenthesized argument. --selftest breaks the
observation contract and the declared text normalization in both directions.

Source basis: latex.ltx, \@star@or@long, \@xargdef, \@testopt,
\@protected@testopt, \@yargdef, \@yargd@f, \renew@command,
\provide@command and \@ifnextchar (TeX Live 2026). The optional outer macro
contains its own name, the hidden helper's name and the unexpanded default.
It is non-long in both star modes. The helper owns the body, arity and
longness. Therefore distinct optional names are not \ifx, while a \let
alias preserves the old default but calls the same, possibly renewed,
helper. Body/arity/star changes alone do not change the wrapper's identity.
A sole brace group is stripped when a delimited argument is captured,
including the default at definition time. An ungrouped [ does not nest.

All documents are invented. Expectations come from kernel source and real
LuaLaTeX PDFs, independently of Compat or the native parser. Each successful
case compares real PDF text from both CLIs, with the repository's Fira Sans
and Fira Math faces. Wrapper \meaning pins and intentional paragraph-scan
errors are explicitly reference-only: no PDF equivalence is claimed for
an error, and a generic failed reference cannot satisfy an error pin.

The hook-scope cases also pin deferred execution: hook registration does
not execute its payload; begin-document and end-preamble payloads change
the state the body reads. Actual braces, \begingroup and \bgroup restore
local flags without inserting a paragraph break. End-preamble hooks run
before begin-document hooks even when registered later. Run just these nine
cases with --case hook-scope.

The required-argument cases distinguish an argument's delimiting braces
from an actual group in the substituted text. Flag setters and \let run
only where the replacement uses the argument; an unused argument is inert,
and a repeated argument executes again in the state its first use left.
An extra pair of explicit braces remains a local scope. Run the seven cases
for each of direct \def, direct \newcommand and their \let aliases with
--case required-argument.

The forwarded-argument cases require a replacement's trailing call to read
its caller's operand, through direct, \let, zero-argument and chained calls.
Repeated stateful substitution pins the order before, during and after the
call. An incomplete grouped call is reference-only, pinned to its exact
argument-scan error. Run these nine cases with --case forwarded-argument.

The opening-space cases pin LaTeX's final \ignorespaces expansion scan.
A nonexpandable token stops it even when compatibility later removes that
token as log-only. Run these eight cases with --case phase-space.
-/

namespace MacroDefaultsOracle

inductive Expected where
  | text (value : String)
  | reject (needle : String)
  deriving BEq, Repr

structure Probe where
  name : String
  setup : String
  body : String
  expected : Expected
  engine : Bool := true
  logs : Array String := #[]
  math : Bool := false
  deriving Repr

private def textCase (name setup body expected : String) : Probe :=
  { name, setup, body, expected := .text expected }

private def family (kind : String) : Array Probe := Id.run do
  let seed := if kind == "renewcommand" then r"\newcommand{\probe}{OLD}" else ""
  let define (signature body : String) :=
    seed ++ "\\" ++ kind ++ r"{\probe}" ++ signature ++ "{" ++ body ++ "}"
  return #[
    textCase (kind ++ "-values")
      (define "[2][D]" "(#1:#2)")
      r"\probe{A}/\probe[E]{B}/\probe[]{C}" "(D:A)/(E:B)/(:C)",
    textCase (kind ++ "-flag")
      (r"\newif\ifprobeFlag\probeFlagfalse" ++ define r"[1][\probeFlagtrue]" "#1")
      r"\ifprobeFlag T\else F\fi/\probe[]\ifprobeFlag T\else F\fi/\probe\ifprobeFlag T\else F\fi"
      "F/F/T",
    textCase (kind ++ "-definition")
      (r"\def\probeWord{OLD}" ++ define r"[1][\def\probeWord{NEW}]" "#1")
      r"\probeWord/\probe[]\probeWord/\probe\probeWord" "OLD/OLD/NEW",
    textCase (kind ++ "-conditional")
      (r"\newif\ifprobeFlag\probeFlagfalse" ++
        define r"[1][\ifprobeFlag T\else F\fi]" "(#1)")
      r"\probe/\probeFlagtrue\probe/\probe[X]/\probe[]" "(F)/(T)/(X)/()",
    textCase (kind ++ "-late-binding")
      (r"\def\probeWord{OLD}" ++ define r"[1][\probeWord]" "(#1)" ++
        r"\def\probeWord{NEW}")
      r"\probe/\probe[X]" "(NEW)/(X)",
    textCase (kind ++ "-unused-undefined")
      (define r"[1][\probeNeverBound]" "(#1)")
      r"\probe[X]/\probe[]" "(X)/()"
  ]

-- The stored default and the explicit delimited actual undergo the same
-- single-group stripping. Pins include spaces and braces verbatim.
private def rawGroupCases : Array Probe :=
  (#[
    ("bare", "D", "D", "D"),
    ("one", "{D}", "D", "D"),
    ("two", "{{D}}", "{D}", "D"),
    ("space-inside", "{ D }", " D ", " D "),
    ("space-outside", " {D} ", " {D} ", " D "),
    ("two-space-inside", "{{ D }}", "{ D }", " D "),
    ("empty", "", "", "")
  ] : Array (String × String × String × String)).map fun (name, written, captured, shown) =>
    { name := "raw-group-" ++ name
      setup := r"\newcommand{\probe}[2][" ++ written ++
        r"]{\typeout{ARG-#2=\detokenize{#1}}(#1)}\typeout{WRAPPER=\meaning\probe}"
      body := r"\probe{DEFAULT}/\probe[" ++ written ++ "]{EXPLICIT}"
      expected := .text ("(" ++ shown ++ ")/(" ++ shown ++ ")")
      engine := false
      logs := #[
        r"WRAPPER=macro:->\@protected@testopt \probe \\probe {" ++ captured ++ "}",
        "ARG-DEFAULT=" ++ captured, "ARG-EXPLICIT=" ++ captured] }

-- Independently measured LuaLaTeX PDF text; the hermetic artifact guards
-- in Tests.MacroHookScope use literal expected documents for these cases.
private def hookScopeCases : Array Probe := #[
  textCase "hook-scope-begin-hook-flag"
    r"\newif\ifprobeFlag\AtBeginDocument{\probeFlagtrue}"
    r"\ifprobeFlag T\else F\fi" "T",
  textCase "hook-scope-begin-hook-flag-timing"
    (r"\newif\ifprobeFlag\AtBeginDocument{\probeFlagtrue}" ++
      r"\ifprobeFlag\def\probeBefore{BAD}\else\def\probeBefore{OK}\fi")
    r"\probeBefore/\ifprobeFlag T\else F\fi" "OK/T",
  textCase "hook-scope-end-hook-flag-timing"
    (r"\usepackage{etoolbox}\newif\ifprobeFlag\AtEndPreamble{\probeFlagtrue}" ++
      r"\ifprobeFlag\def\probeBefore{BAD}\else\def\probeBefore{OK}\fi")
    r"\probeBefore/\ifprobeFlag T\else F\fi" "OK/T",
  textCase "hook-scope-begin-hook-optional-binding"
    r"\AtBeginDocument{\newcommand{\probe}[1][D]{(#1)}}"
    r"\probe/\probe[E]/\probe[]" "(D)/(E)/()",
  textCase "hook-scope-begin-hook-flag-read"
    r"\newif\ifprobeFlag\AtBeginDocument{\ifprobeFlag T\else F\fi}\probeFlagtrue"
    "/T" "T/T",
  textCase "hook-scope-hook-phase-order"
    (r"\usepackage{etoolbox}\newif\ifprobeFlag" ++
      r"\AtBeginDocument{\ifprobeFlag T\else F\fi\probeFlagfalse}" ++
      r"\AtEndPreamble{\probeFlagtrue}")
    r"/\ifprobeFlag T\else F\fi" "T/F",
  textCase "hook-scope-brace-flag"
    r"\newif\ifprobeFlag"
    r"{\probeFlagtrue\ifprobeFlag T\else F\fi}/\ifprobeFlag T\else F\fi" "T/F",
  textCase "hook-scope-begingroup-flag"
    r"\newif\ifprobeFlag"
    (r"\begingroup\probeFlagtrue\ifprobeFlag T\else F\fi" ++
      r"\endgroup/\ifprobeFlag T\else F\fi") "T/F",
  textCase "hook-scope-bgroup-flag"
    r"\newif\ifprobeFlag"
    r"\bgroup\probeFlagtrue\ifprobeFlag T\else F\fi\egroup/\ifprobeFlag T\else F\fi" "T/F"
]

private def requiredArgumentFamily (kind : String) (alias : Bool) : Array Probe :=
  let route := kind ++ if alias then "-alias" else ""
  let call := if alias then r"\aliasprobe" else r"\passprobe"
  let define (replacement : String) :=
    r"\newif\ifchoiceprobe\def\wordprobe{Old}\def\newwordprobe{New}" ++
    (if kind == "def" then r"\def\passprobe#1{" else r"\newcommand{\passprobe}[1]{") ++
    replacement ++ "}" ++ (if alias then r"\let\aliasprobe\passprobe" else "")
  let probe (label replacement body expected : String) :=
    textCase ("required-argument-" ++ route ++ "-" ++ label) (define replacement) body expected
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

private def forwardedArgumentCases : Array Probe :=
  let define (replacement : String) :=
    r"\newif\ifchoiceprobe\newcommand\wordprobe[1]{" ++ replacement ++ "}"
  let variants := (#[
    ("direct", "", r"\wordprobe"),
    ("let", r"\let\aliasprobe\wordprobe", r"\aliasprobe"),
    ("zero", r"\def\zeroprobe{\wordprobe}", r"\zeroprobe"),
    ("chain", r"\def\zeroprobe{\wordprobe}\def\outerprobe{\zeroprobe}", r"\outerprobe")
  ] : Array (String × String × String)).flatMap fun (route, forwarding, call) => #[
    textCase ("forwarded-argument-" ++ route ++ "-state")
      (define r"#1\choiceprobetrue" ++ forwarding)
      ("A" ++ call ++ r"{X}/\ifchoiceprobe T\else F\fi/Z") "AX/T/Z",
    textCase ("forwarded-argument-" ++ route ++ "-source-order")
      (define r"\ifchoiceprobe Set\else Unset\fi/#1#1" ++ forwarding)
      ("A" ++ call ++ r"{\ifchoiceprobe B\else A\fi\choiceprobetrue}/" ++
        r"\ifchoiceprobe T\else F\fi/Z") "AUnset/AB/T/Z"
  ]
  variants.push {
    name := "forwarded-argument-incomplete-rejected"
    setup := define r"#1\choiceprobetrue" ++ r"\def\zeroprobe{\wordprobe}"
    body := r"A{\zeroprobe}/Z"
    expected := .reject r"Argument of \wordprobe has an extra }."
    engine := false }

private def phaseCases : Array Probe := #[
  textCase "phase-space-opening-newline" r"\AtBeginDocument{T}" "/T" "T/T",
  textCase "phase-space-hook-trailing" r"\AtBeginDocument{T }" "/T" "T /T",
  textCase "phase-space-empty-group" r"\AtBeginDocument{T}" "{} /T" "T /T",
  textCase "phase-space-log-barrier" r"\AtBeginDocument{T}"
    r"\PackageInfo{probe}{log} /T" "T /T",
  textCase "phase-space-warning-barrier" r"\AtBeginDocument{T}"
    r"\PackageWarningNoLine{probe}{log} /T" "T /T",
  textCase "phase-space-macro-space" r"\AtBeginDocument{T}\def\spaceprobe{ }"
    r"\spaceprobe/T" "T/T",
  textCase "phase-space-macro-barrier"
    r"\AtBeginDocument{T}\def\barrierprobe{\PackageInfo{probe}{log} }"
    r"\barrierprobe/T" "T /T",
  textCase "phase-space-empty-selected-branch" r"\AtBeginDocument{T}"
    r"\IfClassLoadedTF{article}{}{Hidden} /T" "T/T"
]

private def copiedHelperCases : Array Probe :=
  #[false, true].flatMap fun optional => #[false, true].map fun grouped =>
    let setup := r"\newif\ifprobeFlag\def\helperprobe#1{\probeFlagfalse#1}" ++
      (if optional then r"\newcommand{\sourceprobe}[1][\helperprobe{}]{#1}"
       else r"\def\sourceprobe#1{\helperprobe{#1}}") ++
      r"\def\helperprobe#1{\probeFlagtrue#1}"
    let call := if optional then r"\aliasprobe" else r"\aliasprobe{}"
    let selected := r"\ifprobeFlag T\else F\fi"
    textCase ("copied-helper-" ++ (if optional then "optional" else "required") ++
        (if grouped then "-local" else "-top"))
      (setup ++ (if grouped then r"\def\passprobe#1{#1}" else r"\let\aliasprobe\sourceprobe"))
      (if grouped then r"\passprobe{{\let\aliasprobe\sourceprobe" ++ call ++ selected ++ "}}/" ++ selected
       else call ++ selected)
      (if grouped then "T/F" else "T")

private def cases : Array Probe :=
  phaseCases ++ copiedHelperCases ++ forwardedArgumentCases ++
  requiredArgumentFamily "def" false ++ requiredArgumentFamily "def" true ++
  requiredArgumentFamily "newcommand" false ++ requiredArgumentFamily "newcommand" true ++
  hookScopeCases ++ rawGroupCases ++ family "newcommand" ++
  family "renewcommand" ++ family "providecommand" ++ #[
    textCase "provide-existing-optional"
      (r"\newif\ifprobeFlag\probeFlagfalse\newcommand{\probe}[1][OLD]{(#1)}" ++
        r"\providecommand{\probe}[1][\probeFlagtrue]{BAD#1}")
      r"\ifprobeFlag T\else F\fi/\probe/\probe[X]" "F/(OLD)/(X)",
    textCase "provide-existing-plain"
      r"\newcommand{\probe}{OLD}\providecommand{\probe}[2][\probeNeverBound]{BAD#1#2}"
      r"\probe" "OLD",
    textCase "unused-parameter"
      r"\newif\ifprobeFlag\probeFlagfalse\newcommand{\probe}[1][\probeFlagtrue]{OK}"
      r"\ifprobeFlag T\else F\fi/\probe/\ifprobeFlag T\else F\fi" "F/OK/F",
    textCase "repeated-parameter"
      (r"\newif\ifprobeFlag\probeFlagfalse" ++
        r"\newcommand{\probe}[1][\ifprobeFlag B\else A\fi\probeFlagtrue]{#1#1}")
      r"\ifprobeFlag T\else F\fi/\probe/\ifprobeFlag T\else F\fi" "F/AB/T",
    textCase "body-execution-order"
      (r"\newif\ifprobeFlag\probeFlagfalse" ++
        r"\newcommand{\probe}[1][\probeFlagtrue]{\ifprobeFlag T\else F\fi#1\ifprobeFlag T\else F\fi}")
      r"\probe" "FT",
    textCase "grouped-close"
      r"\newcommand{\probe}[2][{A]B}]{(#1:#2)}"
      r"\probe{X}/\probe[{C]D}]{Y}" "(A]B:X)/(C]D:Y)",
    textCase "ungrouped-open-does-not-nest"
      r"\newcommand{\probe}[2][D]{(#1:#2)}"
      r"\probe[H[I]T" "(H[I:T)",
    textCase "spaces"
      r"\newcommand{\probe}[2][ A ]{(#1:#2)}"
      r"\probe{B}/\probe[ C ]{D}/\probe[{ E }]{F}/\probe {G}/\probe[H] IJ"
      "( A :B)/( C :D)/( E :F)/( A :G)/(H:I)J",
    textCase "lookahead-skips-spaces-without-expansion"
      r"\newcommand{\probe}[1][D]{(#1)}\def\probeOption{[E]}\let\?\probe"
      r"\probe\probeOption/\?   [X]/\probe\space[Y]" "(D)[E]/(X)/(D) [Y]",
    textCase "mandatory-single-tokens"
      r"\newcommand{\probe}[3][D]{(#1:#2:#3)}"
      r"\probe AB/\probe[E]CD/\probe[]{Q}R" "(D:A:B)/(E:C:D)/(:Q:R)",
    textCase "mandatory-group-and-control"
      r"\def\probeWord{MN}\newcommand{\probe}[3][D]{(#1:#2:#3)}"
      r"\probe{AB}\probeWord/\probe[E]\probeWord{CD}" "(D:AB:MN)/(E:MN:CD)",
    textCase "empty-default-and-mandatory"
      r"\newcommand{\probe}[2][]{(#1:#2)}"
      r"\probe{}/\probe[X]{}/\probe[]Q" "(:)/(X:)/(:Q)",
    textCase "group-stripping-default-and-explicit"
      (r"\newif\ifprobeFlag\probeFlagfalse" ++
        r"\newcommand{\probe}[1][{\probeFlagtrue}]{#1}" ++
        r"\newcommand{\probeTwo}[1][{{\probeFlagtrue}}]{#1}")
      (r"\probe\ifprobeFlag T\else F\fi/\probeFlagfalse" ++
        r"\probeTwo\ifprobeFlag T\else F\fi/" ++
        r"\probe[{\probeFlagtrue}]\ifprobeFlag T\else F\fi/\probeFlagfalse" ++
        r"\probe[{{\probeFlagtrue}}]\ifprobeFlag T\else F\fi")
      "T/F/T/F",
    textCase "call-scope"
      r"\def\probeWord{OLD}\newcommand{\probe}[1][\def\probeWord{NEW}]{#1}"
      r"\probeWord/{\probe\probeWord}/\probeWord" "OLD/NEW/OLD",
    textCase "definition-scope-and-alias"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\probe/{\renewcommand{\probe}[1][E]{N#1}\probe/\probeAlias}/\probe/\probeAlias"
      "OD/NE/ND/OD/OD",
    textCase "ifx-distinct-optional"
      r"\newcommand{\probeA}[1][D]{(#1)}\newcommand{\probeB}[1][D]{(#1)}\let\probeAlias\probeA"
      r"\ifx\probeA\probeB SAME\else DIFF\fi/\ifx\probeA\probeAlias SAME\else DIFF\fi"
      "DIFF/SAME",
    textCase "ifx-distinct-plain-control"
      r"\newcommand{\probeA}[1]{(#1)}\newcommand{\probeB}[1]{(#1)}"
      r"\ifx\probeA\probeB SAME\else DIFF\fi" "SAME",
    textCase "ifx-body-renew-alias"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\renewcommand{\probe}[1][D]{N#1}\ifx\probe\probeAlias SAME\else DIFF\fi/\probeAlias"
      "SAME/ND",
    textCase "ifx-arity-renew-alias"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\renewcommand{\probe}[2][D]{N(#1:#2)}\ifx\probe\probeAlias SAME\else DIFF\fi/\probeAlias Q"
      "SAME/N(D:Q)",
    textCase "ifx-star-renew-alias"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\renewcommand*{\probe}[1][D]{N#1}\ifx\probe\probeAlias SAME\else DIFF\fi/\probeAlias"
      "SAME/ND",
    textCase "ifx-default-renew-alias"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\renewcommand{\probe}[1][E]{N#1}\ifx\probe\probeAlias SAME\else DIFF\fi/\probe/\probeAlias"
      "DIFF/NE/ND",
    textCase "ifx-default-token-identity"
      r"\def\probeWord{D}\newcommand{\probe}[1][\probeWord]{(#1)}\let\probeAlias\probe"
      r"\renewcommand{\probe}[1][D]{(#1)}\ifx\probe\probeAlias SAME\else DIFF\fi/\probe/\probeAlias"
      "DIFF/(D)/(D)",
    textCase "ifx-default-group-identity"
      r"\newcommand{\probe}[1][D]{(#1)}\let\probeAlias\probe"
      (r"\renewcommand{\probe}[1][{D}]{(#1)}\ifx\probe\probeAlias SAME\else DIFF\fi/" ++
        r"\renewcommand{\probe}[1][{{D}}]{(#1)}\ifx\probe\probeAlias SAME\else DIFF\fi")
      "SAME/DIFF",
    textCase "ifx-default-space-identity"
      r"\newcommand{\probe}[1][D]{(#1)}\let\probeAlias\probe"
      r"\renewcommand{\probe}[1][ D]{(#1)}\ifx\probe\probeAlias SAME\else DIFF\fi/\probe/\probeAlias"
      "DIFF/( D)/(D)",
    textCase "plain-renew-preserves-alias-helper"
      r"\newcommand{\probe}[1][D]{O#1}\let\probeAlias\probe"
      r"\renewcommand{\probe}[1]{N#1}\probe{X}/\probeAlias" "NX/OD",
    textCase "long-explicit-and-mandatory-paragraph"
      r"\newcommand{\probe}[2][D]{OK}"
      r"A\probe[X\par Y]{Z}/\probe{X\par Y}Z" "AOK/OKZ",
    textCase "long-default-paragraph"
      r"\newcommand{\probe}[1][X\par Y]{OK}" r"A\probe Z" "AOKZ",
    textCase "star-default-paragraph-inert"
      r"\newcommand*{\probe}[1][X\par Y]{OK}" r"A\probe[X]Z" "AOKZ",
    textCase "alias-follows-renewed-long-helper"
      r"\newcommand*{\probe}[1][D]{OLD}\let\probeAlias\probe\renewcommand{\probe}[1][D]{OK}"
      r"A\probeAlias[X\par Y]Z" "AOKZ",
    { name := "star-explicit-paragraph-rejected"
      setup := r"\newcommand*{\probe}[1][D]{OK}"
      body := r"A\probe[X\par Y]Z"
      expected := .reject r"Paragraph ended before \\probe was complete."
      engine := false },
    { name := "star-default-paragraph-rejected"
      setup := r"\newcommand*{\probe}[1][X\par Y]{OK}"
      body := r"A\probe Z"
      expected := .reject r"Paragraph ended before \\probe was complete."
      engine := false },
    { name := "star-mandatory-paragraph-rejected"
      setup := r"\newcommand*{\probe}[2][D]{OK}"
      body := r"A\probe[X]{Y\par Z}Q"
      expected := .reject r"Paragraph ended before \\probe was complete."
      engine := false },
    { name := "alias-follows-renewed-star-helper"
      setup := r"\newcommand{\probe}[1][D]{OLD}\let\probeAlias\probe\renewcommand*{\probe}[1][D]{OK}"
      body := r"A\probeAlias[X\par Y]Z"
      expected := .reject r"Paragraph ended before \\probe was complete."
      engine := false },
    { name := "wrapper-meaning"
      setup :=
        r"\newcommand{\probeA}[2][D]{(#1:#2)}\newcommand*{\probeStar}[2][D]{(#1:#2)}" ++
        r"\expandafter\let\expandafter\probeInner\csname\string\probeA\endcsname" ++
        r"\expandafter\let\expandafter\probeInnerStar\csname\string\probeStar\endcsname" ++
        r"\typeout{OUTER-A=\meaning\probeA}\typeout{OUTER-STAR=\meaning\probeStar}" ++
        r"\typeout{INNER-A=\meaning\probeInner}\typeout{INNER-STAR=\meaning\probeInnerStar}"
      body := "OK"
      expected := .text "OK"
      engine := false
      logs := #[
        r"OUTER-A=macro:->\@protected@testopt \probeA \\probeA {D}",
        r"OUTER-STAR=macro:->\@protected@testopt \probeStar \\probeStar {D}",
        r"INNER-A=\long macro:[#1]#2->(#1:#2)",
        r"INNER-STAR=macro:[#1]#2->(#1:#2)"] },
    { (textCase "math-values" r"\newcommand{\probe}[1][7]{#1}"
        r"A$\probe$B/A$\probe[8]$B/A$\probe[]$B" "A7B/A8B/AB") with math := true }
  ]

inductive Observation where
  | pdf (text log : String)
  | rejected (exit : UInt32) (log : String) (pdfExists : Bool)
  | fault (message : String)
  deriving BEq, Repr

private def normalize (text : String) : String :=
  ((text.replace "\r\n" "\n").replace "\x0c" "").trimAscii.toString

private def contains (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

private def pinnedLog (log : String) (pins : Array String) : Bool :=
  pins.all fun pin =>
    ((log.replace "\r\n" "\n").splitOn "\n").count pin == 1

private def accepts (p : Probe) (o : Observation) : Bool :=
  match p.expected, o with
  | .text wanted, .pdf actual log => normalize actual == wanted && pinnedLog log p.logs
  | .reject needle, .rejected exit log false =>
    exit != 0 && exit < 124 && contains log needle && pinnedLog log p.logs
  | _, _ => false

private def pdfsAgree (p : Probe) (reference engine : Observation) : Bool :=
  match p.expected, reference, engine with
  | .text _, .pdf _ _, .pdf _ _ => accepts p reference && accepts { p with logs := #[] } engine
  | _, _, _ => false

private def observe (exit : UInt32) (log : String) (pdfExists : Bool)
    (extraction : Option (UInt32 × String)) : Observation :=
  if exit >= 124 then .fault s!"process/timeout failure (exit {exit})"
  else if exit != 0 then .rejected exit log pdfExists
  else if !pdfExists then .fault "successful build produced no PDF"
  else match extraction with
    | none => .fault "PDF was not extracted"
    | some (0, text) => .pdf text log
    | some (code, _) => .fault s!"pdftotext failed (exit {code})"

private def resultCode (referenceFailures faults differences : Nat) (reportOnly : Bool) : UInt32 :=
  if referenceFailures > 0 || faults > 0 then 2
  else if differences > 0 && !reportOnly then 1 else 0

private def selftest : IO UInt32 := do
  let mut failures : Array String := #[]
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do IO.eprintln s!"FAIL {name}"
  let p := textCase "contract" "" "" "( A )"
  let good := Observation.pdf "( A )\n\n\x0c" ""
  let tests : Array (String × Bool) := #[
    ("exact full text", accepts p good),
    ("extractor boundaries ignored", normalize "\r\n( A )\r\n\x0c" == normalize "( A )"),
    ("raw reading sees ignored boundaries", "\r\n( A )\r\n\x0c" != "( A )"),
    ("page partition ignored", normalize "A\x0cB" == normalize "AB"),
    ("raw reading sees page partition", "A\x0cB" != "AB"),
    ("interior spaces kept", !accepts p (.pdf "(A)" "")),
    ("interior line breaks kept", !accepts p (.pdf "(\nA )" "")),
    ("glyph order kept", normalize "AB" != normalize "BA"),
    ("extra ink kept", !accepts p (.pdf "( A )EXTRA" "")),
    ("missing ink kept", !accepts p (.pdf "" "")),
    ("good observations match", pdfsAgree p good good),
    ("same wrong answer is not a match", !pdfsAgree p (.pdf "BAD" "") (.pdf "BAD" "")),
    ("two faults are not a match", !pdfsAgree p (.fault "missing") (.fault "missing")),
    ("stale PDF after failure is not text",
      observe 1 "failed" true (some (0, "( A )")) == .rejected 1 "failed" true),
    ("missing PDF is a fault", observe 0 "" false none == .fault "successful build produced no PDF"),
    ("missing extraction is a fault", observe 0 "" true none == .fault "PDF was not extracted"),
    ("failed extractor cannot supply text",
      observe 0 "" true (some (1, "( A )")) == .fault "pdftotext failed (exit 1)"),
    ("successful extraction supplies text", observe 0 "" true (some (0, "( A )")) == .pdf "( A )" ""),
    ("empty extraction is observable", accepts (textCase "empty" "" "" "") (.pdf "\n\x0c" "")),
    ("empty expectation cannot accept absence",
      !accepts (textCase "empty" "" "" "") (observe 0 "" false none)),
    ("one exact log line", pinnedLog "PREFIX\nPIN\nEND\n" #["PIN"]),
    ("missing log line", !pinnedLog "" #["PIN"]),
    ("substring is not log line", !pinnedLog "PIN EXTRA\n" #["PIN"]),
    ("duplicate log line", !pinnedLog "PIN\nPIN\n" #["PIN"]),
    ("missing meaning pin prevents a match",
      !pdfsAgree { p with logs := #["PIN"] } good good),
    ("clean run passes", resultCode 0 0 0 false == 0),
    ("difference fails default mode", resultCode 0 0 1 false == 1),
    ("report permits measured difference", resultCode 0 0 1 true == 0),
    ("report cannot forgive reference failure", resultCode 1 0 0 true == 2),
    ("report cannot forgive observation fault", resultCode 0 1 0 true == 2),
    ("reference pins required even beside differences", resultCode 1 0 1 true == 2),
    ("matrix names unique", (cases.toList.map (·.name)).eraseDups.length == cases.size),
    ("matrix nonempty", !cases.isEmpty)
  ]
  for (name, ok) in tests do
    check name ok
    unless ok do failures := failures.push name
  let rejection : Probe := { p with expected := .reject "KNOWN", engine := false }
  for (name, ok) in #[
      ("specific rejection", accepts rejection (observe 1 "KNOWN" false none)),
      ("other rejection refused", !accepts rejection (observe 1 "OTHER" false none)),
      ("success with error-looking log refused", !accepts rejection (.pdf "" "KNOWN")),
      ("failed spawn refused", !accepts rejection (observe 127 "KNOWN" false none)),
      ("timeout refused", !accepts rejection (observe 124 "KNOWN" false none)),
      ("failed reference with PDF refused", !accepts rejection (observe 1 "KNOWN" true none)),
      ("rejections never claim PDF equivalence",
        !pdfsAgree rejection (.rejected 1 "KNOWN" false) (.rejected 1 "KNOWN" false))] do
    check name ok
    unless ok do failures := failures.push name
  IO.println s!"macro defaults selftest: {tests.size + 7} checks, {failures.size} failures"
  return if failures.isEmpty then 0 else 1

structure Options where
  report : Bool := false
  referenceOnly : Bool := false
  keep : Bool := false
  engine : System.FilePath := ".lake/build/bin/leantex"
  select : String := ""

private def options : List String → Options → Except String Options
  | [], o => .ok o
  | "--report" :: rest, o => options rest { o with report := true }
  | "--reference-only" :: rest, o => options rest { o with referenceOnly := true }
  | "--keep" :: rest, o => options rest { o with keep := true }
  | "--engine" :: path :: rest, o => options rest { o with engine := path }
  | "--case" :: name :: rest, o => options rest { o with select := name }
  | _, _ => .error "usage: macro-defaults-oracle.lean [--selftest | --report] \
[--reference-only] [--case NAME] [--engine PATH] [--keep]"

private def source (p : Probe) (reference : Bool) : String :=
  "\\documentclass{article}\n" ++
  (if reference then
    "\\usepackage{fontspec}\n\\setmainfont{FiraSans-Regular.otf}[Path=../fonts/]\n" ++
    (if p.math then
      "\\usepackage{unicode-math}\n\\setmathfont{FiraMath-Regular.otf}[Path=../fonts/]\n"
     else "")
   else "\\fonts{dir=\"../fonts\", body=\"Fira Sans\", math=\"Fira Math\"}\n") ++
  "\\pagestyle{empty}\n" ++ p.setup ++ "\n\\begin{document}\n" ++
  p.body ++ "\n\\end{document}\n"

private def run (cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String)) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := "timeout", args := #["--kill-after=2s", "30s", cmd] ++ args,
    cwd := some cwd, env }

private def build (p : Probe) (reference : Bool) (binary root : System.FilePath)
    (env : Array (String × Option String)) : IO Observation := do
  let dir := root / p.name
  let stem := if reference then "reference" else "engine"
  let pdf := dir / (stem ++ ".pdf")
  try
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / (stem ++ ".tex")) (source p reference)
    let out ← if reference then
      run "lualatex"
        #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "reference.tex"] dir env
      else run binary.toString #["engine.tex", "-o", "engine.pdf"] dir env
    IO.FS.writeFile (dir / (stem ++ ".stdout")) out.stdout
    IO.FS.writeFile (dir / (stem ++ ".stderr")) out.stderr
    let hasPdf ← pdf.pathExists
    let mut extraction := none
    if out.exitCode == 0 && hasPdf then
      let text ← run "pdftotext" #["-enc", "UTF-8", pdf.toString, "-"] dir env
      IO.FS.writeFile (dir / (stem ++ ".txt")) text.stdout
      IO.FS.writeFile (dir / (stem ++ ".extract.stderr")) text.stderr
      extraction := some (text.exitCode, text.stdout)
    return observe out.exitCode (out.stdout ++ out.stderr) hasPdf extraction
  catch e =>
    return .fault e.toString

private def describe : Observation → String
  | .pdf text _ => s!"pdf={repr (normalize text)}"
  | .rejected code _ pdf => s!"rejected(exit={code}, pdf={pdf})"
  | .fault message => s!"fault={repr message}"

private def isFault : Observation → Bool
  | .fault _ => true
  | .pdf _ _ | .rejected _ _ _ => false

private def report (o : Options) (root : System.FilePath) : IO UInt32 := do
  let selected := cases.filter fun p => o.select.isEmpty || contains p.name o.select
  if selected.isEmpty then throw <| IO.userError s!"no case names contain {repr o.select}"
  let cache := root / "cache"
  IO.FS.createDirAll cache
  IO.FS.createDirAll (root / "fonts")
  for font in #["FiraSans-Regular.otf", "FiraMath-Regular.otf"] do
    IO.FS.writeBinFile (root / "fonts" / font)
      (← IO.FS.readBinFile (System.FilePath.mk "tests/corpus/fonts" / font))
  let env := #[("TEXMFCACHE", some cache.toString), ("TEXMFVAR", some cache.toString),
    ("XDG_CACHE_HOME", some cache.toString), ("LEANTEX_FONT", none),
    ("max_print_line", some "1000")]
  let version ← run "lualatex" #["--version"] root env
  unless version.exitCode == 0 do throw <| IO.userError "lualatex --version failed"
  IO.println ((version.stdout.splitOn "\n").headD "")
  let kernel ← run "kpsewhich" #["latex.ltx"] root env
  unless kernel.exitCode == 0 && !kernel.stdout.trimAscii.isEmpty do
    throw <| IO.userError "kpsewhich could not locate latex.ltx"
  let kernelPath := System.FilePath.mk kernel.stdout.trimAscii.toString
  let kernelText ← IO.FS.readFile kernelPath
  unless contains kernelText r"\long\def\@xargdef" &&
      contains kernelText r"\def\@protected@testopt" do
    throw <| IO.userError "latex.ltx lacks the kernel definitions this oracle measures"
  IO.println s!"kernel: {kernelPath}"
  let extractor ← run "pdftotext" #["-v"] root env
  unless extractor.exitCode == 0 do throw <| IO.userError "pdftotext -v failed"
  let binary ← if o.referenceOnly then pure o.engine else IO.FS.realPath o.engine
  unless o.referenceOnly do
    let engineVersion ← run binary.toString #["--version"] root env
    unless engineVersion.exitCode == 0 do throw <| IO.userError "leantex --version failed"
    IO.println s!"engine: {binary}; {engineVersion.stdout.trimAscii}"
  let mut referenceFailures := 0
  let mut compared := 0
  let mut differences := 0
  let mut faults := 0
  for p in selected do
    let reference ← build p true binary root env
    if !accepts p reference then
      referenceFailures := referenceFailures + 1
      IO.println s!"REF-FAIL {p.name}: expected={repr p.expected}; {describe reference}"
      match reference with
      | .pdf _ log | .rejected _ log _ =>
        IO.println s!"  reference log tail: {repr (String.ofList (log.toList.drop (log.length - 1600)))}"
      | .fault _ => pure ()
    else if o.referenceOnly || !p.engine then
      IO.println s!"REF-OK {p.name}: {describe reference}; reference-only"
      for pin in p.logs do IO.println s!"  {pin}"
    else
      let engine ← build p false binary root env
      compared := compared + 1
      let same := pdfsAgree p reference engine
      unless same do differences := differences + 1
      if isFault engine then faults := faults + 1
      IO.println s!"{if same then "MATCH" else "DIFF"} {p.name}: \
reference {describe reference}; engine {describe engine}"
  IO.println s!"macro defaults: {selected.size} references, {referenceFailures} reference failures; \
{compared} engine cases, {differences} differences, {faults} engine observation faults"
  return resultCode referenceFailures faults differences o.report

def main (args : List String) : IO UInt32 := do
  if args == ["--selftest"] then return ← selftest
  match options args {} with
  | .error usage => IO.eprintln usage; return 2
  | .ok o =>
    try
      let root ← IO.FS.createTempDir
      IO.println s!"macro defaults artifacts: {root}{if o.keep then " (retained)" else ""}"
      try report o root finally
        unless o.keep do IO.FS.removeDirAll root
    catch e =>
      IO.eprintln s!"macro defaults observation failure: {e}"
      return 2

end MacroDefaultsOracle

def main := MacroDefaultsOracle.main
