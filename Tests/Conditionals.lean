import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The heads the accounting row ranges over: every `\if…` primitive of
TeX82's table (`Compat.texPrimitives`) and e-TeX's three. Spelled from the
table rather than listed, so a head the table gains is a probe this block
owes. -/
def condProbeHeads : List String :=
  (Compat.texPrimitives.toList.filter (·.startsWith "if")) ++
    ["ifdefined", "ifcsname", "iffontchar"]

/-- One probe per head: what follows the head so TeX reads a complete test,
and which branch TeX takes (`none` where the answer is TeX's run-time state,
a mode or a register this engine does not keep). The `\ifcase` row's case 0
is its own text, so the probe's first case is not the one taken. -/
def condProbeArgs : List (String × String × Option Bool) :=
  [("if", "aa ", none), ("ifcase", "1 Zero\\or ", some true), ("ifcat", "aa ", none),
   ("ifdim", "1pt<2pt ", none), ("ifeof", "1 ", none), ("iffalse", " ", some false),
   ("ifhbox", "0 ", none), ("ifhmode", " ", none), ("ifinner", " ", none),
   ("ifmmode", " ", none), ("ifnum", "1=1 ", some true), ("ifodd", "3 ", some true),
   ("iftrue", " ", some true), ("ifvbox", "0 ", none), ("ifvmode", " ", none),
   ("ifvoid", "0 ", none), ("ifx", "\\relax\\relax ", some true),
   ("ifdefined", "\\probeundefined ", some false), ("ifcsname", "relax\\endcsname ", none),
   ("iffontchar", "\\font`a ", none)]

/-- **Every conditional is accounted for.** A TeX conditional the engine
meets is either decided — its branch named, the other branch gone — or
refused by name; it is never resolved in silence. The defect this pins:
inside a picture, `\ifnum` over a document macro was computed from the last
definition the whole document made, with no diagnostic at all, so three
renderings of one picture under three macro states drew the same branch.

Asserted structurally, two builds apart: wrapping content in a conditional
adds at least one diagnostic that carries a subject (the census key a
reader and a tally can look up) to what the unwrapped content emits, in
running text and in a picture alike, and a decided head ships exactly the
branch TeX takes. Exhaustive over the heads TeX defines: a head with no
probe row fails here. Invented content throughout. -/
def condAccountingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let keyed (ds : Array Diag) : Nat := (ds.filter (·.subject.isSome)).size
  let text (src : String) : String := censusText (censusOfSrc oneFace src)
  let picOf (body : String) : String :=
    dvDoc "" ("\\begin{tikzpicture}\n" ++ body ++ "\\end{tikzpicture}")
  let thenNode := "\\node at (0,0) {Then};\n"
  let otherNode := "\\node at (0,0) {Other};\n"
  for h in condProbeHeads do
    match condProbeArgs.find? (·.1 == h) with
    | none => t s!"conditional head '\\{h}' has a probe row" false
    | some (_, args, taken) =>
      let bodySrc := dvDoc "" ("\\" ++ h ++ args ++ "Then\\else Other\\fi")
      let bodyCtl := dvDoc "" "Then"
      t s!"'\\{h}' in running text is decided or refused by name"
        (decide (keyed (elabStr bodySrc).2 > keyed (elabStr bodyCtl).2))
      let picSrc := picOf ("\\" ++ h ++ args ++ thenNode ++ "\\else\n" ++ otherNode ++ "\\fi\n")
      let picCtl := picOf thenNode
      t s!"'\\{h}' in a picture is decided or refused by name"
        (decide (keyed (elabStr picSrc).2 > keyed (elabStr picCtl).2))
      if let some v := taken then
        let (keep, drop) := if v then ("Then", "Other") else ("Other", "Then")
        let bt := text bodySrc
        let pt := text picSrc
        t s!"'\\{h}' in running text ships the branch TeX takes, and only it"
          (hasStr bt keep && !hasStr bt drop)
        t s!"'\\{h}' in a picture ships the branch TeX takes, and only it"
          (hasStr pt keep && !hasStr pt drop)
  -- A document's own `\newif` flag is a conditional head too.
  let flagSrc := dvDoc "\\newif\\ifprobe\n" "\\ifprobe Then\\else Other\\fi"
  t "a declared flag's conditional is decided by name"
    (decide (keyed (elabStr flagSrc).2 >
      keyed (elabStr (dvDoc "\\newif\\ifprobe\n" "Other")).2))

/-- **A picture honours the macro state at its own site.** Two renderings of
one picture source under different definitions draw what those definitions
decide: TeX reads a macro where it is expanded, and `\def` inside an
environment ends with it. The deck-shaped probe: three sibling environments
each define the state a picture's `\ifnum` and `\ifdefined` read, and the
last one leaves the stage different — the defect drew the last stage's
branch in all three, because the picture's macro table was the whole
document's, last definition winning. Read off the shipped page census:
which branch ran is visible only as ink. Invented content throughout. -/
def picStateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let shipped := censusOfSrc oneFace
  let pic :=
    "\\begin{tikzpicture}\n\\ifnum\\stage=1\n\\node at (0,0) {Small};\n" ++
    "\\ifdefined\\cut\\else\n\\node at (2,0) {Edge};\n\\fi\n" ++
    "\\else\n\\node at (0,0) {Large};\n\\fi\n\\end{tikzpicture}\n"
  let src := dvDoc ""
    ("\\begin{center}\\def\\stage{1}\\def\\cut{}\n" ++ pic ++ "\\end{center}\n\n" ++
     "\\begin{center}\\def\\stage{1}\n" ++ pic ++ "\\end{center}\n\n" ++
     "\\begin{center}\\def\\stage{2}\n" ++ pic ++ "\\end{center}\n")
  let c := shipped src
  t "each picture draws the stage its own site defines"
    (pageOccurs c 0 "Small" == 2 && pageOccurs c 0 "Large" == 1)
  t "a definition made inside an environment ends with it"
    (pageOccurs c 0 "Edge" == 1)
  let (_, ds) := elabStr src
  t "every decision the pictures' state made is a keyed note"
    ((ds.filter fun d => d.code == "N0114" && d.subject.isNone).isEmpty &&
      (ds.filter (·.code == "N0114")).size ≥ 5)
  -- Running text reads the same scoped state.
  let scopeTxt := censusText (shipped (dvDoc ""
    "\\begin{center}\\def\\flag{}Inner\\end{center}\n\n\\ifdefined\\flag Leaked\\else Scoped\\fi"))
  t "a definition inside an environment is not visible after it"
    (hasStr scopeTxt "Scoped" && !hasStr scopeTxt "Leaked")
  -- A global definition escapes its environment, as TeX's `\gdef` does.
  let globalTxt := censusText (shipped (dvDoc ""
    "\\begin{center}\\gdef\\flag{}Inner\\end{center}\n\n\\ifdefined\\flag Kept\\else Lost\\fi"))
  t "a global definition outlives its environment"
    (hasStr globalTxt "Kept" && !hasStr globalTxt "Lost")
  -- The boundary's identity is the picture's bytes, so a branch the state
  -- decides must be decided before the bytes are taken: two sites of one
  -- source under two states are two requests, never one cached answer.
  let bpic :=
    "\\begin{tikzpicture}\\ifnum\\mode=1 \\draw (0,0) circle (1);\\else " ++
    "\\draw (0,0) circle (2);\\fi\\end{tikzpicture}"
  let (bdoc, _) := elabStr (dvDoc "" ("\\def\\mode{1}\n" ++ bpic ++ "\n\n\\def\\mode{2}\n" ++ bpic))
  t "two states of one boundary picture are two requests"
    (bdoc.pictureSrcs.size == 2)


/-- **`\ifx` compares the meaning TeX compares.** Two macros are `\ifx`-equal
when their replacement texts and their prefixes agree (TeXbook chapter 20),
and LaTeX's `\newcommand` is `\long` only when it takes arguments and is not
starred: `\meaning` reads `macro:->x` for a parameterless `\newcommand` and a
`\def` alike (measured against LaTeX2e 2025-11-01). The defect read every
unstarred `\newcommand` as `\long`, so the common string switch — a
`\newcommand` holding a word compared against a `\def` of the same word —
shipped the wrong branch with a note. A robust command's meaning names the
command itself, so two of them with one body are different meanings: the
engine cannot say so from the text and refuses the test by name. Read off
the shipped census. Invented content throughout. -/
def ifxMeaningChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let text (body : String) : String := censusText (censusOfSrc oneFace (dvDoc "" body))
  let ships (body keep drop : String) : Bool :=
    let s := text body
    hasStr s keep && !hasStr s drop
  let test (a b : String) : String := a ++ b ++ "\\ifx\\probeA\\probeB Same\\else Differ\\fi"
  t "a parameterless newcommand and a def of one text are ifx-equal"
    (ships (test "\\def\\probeA{x}" "\\newcommand\\probeB{x}") "Same" "Differ")
  t "the string switch: a newcommand word equals a def of the same word"
    (ships ("\\newcommand{\\probeMode}{draft}\\def\\probeWord{draft}" ++
      "\\ifx\\probeMode\\probeWord DraftBranch\\else FinalBranch\\fi")
      "DraftBranch" "FinalBranch")
  t "a long def differs from a parameterless newcommand of the same text"
    (ships (test "\\long\\def\\probeA{x}" "\\newcommand\\probeB{x}") "Differ" "Same")
  t "a starred newcommand equals a def of the same text"
    (ships (test "\\def\\probeA{x}" "\\newcommand*\\probeB{x}") "Same" "Differ")
  t "a protected def differs from a def of the same text"
    (ships (test "\\protected\\def\\probeA{x}" "\\def\\probeB{x}") "Differ" "Same")
  let robust := test "\\DeclareRobustCommand\\probeA{x}" "\\DeclareRobustCommand\\probeB{x}"
  t "two robust commands of one text are not read as equal, and the test is refused by name"
    (!hasStr (text robust) "Same" && (elabStr (dvDoc "" robust)).2.any (·.code == "W0104"))


/-- **A conditional in a macro's text is decided where the macro is used.**
TeX expands a macro where it is used, so a conditional in its text reads the
state in force at the use, and a macro used under two states takes two
branches. The defect decided the conditional where the macro was defined:
`\def\n{1}\def\show{\ifnum\n=1 One\else Two\fi}\def\n{2}\show` shipped "One"
(TeX: "Two") with a note, where the base had named the loss. A use the engine
cannot decide is refused by name, never decided at the definition: a macro
with parameters is expanded by the elaborator, which has no conditionals.
Read off the shipped census and the structured diagnostics. Invented
content throughout. -/
def macroUseChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let text (pre body : String) : String := censusText (censusOfSrc oneFace (dvDoc pre body))
  let occurs (s needle : String) : Nat := (s.splitOn needle).length - 1
  let ships (body keep drop : String) : Bool :=
    let s := text "" body
    hasStr s keep && !hasStr s drop
  let showDef := "\\def\\probeShow{\\ifnum\\probeN=1 One\\else Two\\fi}"
  t "a def's conditional reads the value in force where the macro is used"
    (ships ("\\def\\probeN{1}" ++ showDef ++ "\\def\\probeN{2}\\probeShow") "Two" "One")
  t "a newcommand's conditional reads the value in force where the macro is used"
    (ships ("\\newcommand{\\probeN}{1}" ++
      "\\newcommand{\\probeShow}{\\ifnum\\probeN=1 One\\else Two\\fi}" ++
      "\\renewcommand{\\probeN}{2}\\probeShow") "Two" "One")
  t "a macro's ifdefined sees a name defined after the macro and before its use"
    (ships ("\\newcommand{\\probeShow}{\\ifdefined\\probeLater Defined\\else Undefined\\fi}" ++
      "\\def\\probeLater{}\\probeShow") "Defined" "Undefined")
  let twice := text "" (showDef ++ "\\def\\probeN{1}\\probeShow\n\n\\def\\probeN{2}\\probeShow")
  t "one macro used under two states ships each state's branch"
    (occurs twice "One" == 1 && occurs twice "Two" == 1)
  let flag := text "\\newif\\ifprobe\n"
    ("\\newcommand\\probeShow{\\ifprobe On\\else Off\\fi}\\probeShow\n\n\\probetrue\\probeShow")
  t "a flag's test in a macro reads the flag where the macro is used"
    (occurs flag "Off" == 1 && occurs flag "On" == 1)
  t "a macro that sets a flag sets it where it is used"
    (ships ("\\newif\\ifprobe\\newcommand\\probeOn{\\probetrue}" ++
      "\\ifprobe Early\\fi\\probeOn\\ifprobe Late\\fi") "Late" "Early")
  t "a definition a macro makes takes effect where the macro is used"
    (ships ("\\newcommand\\probeSet{\\def\\probeMode{2}}\\def\\probeMode{1}\\probeSet" ++
      "\\ifnum\\probeMode=1 One\\else Two\\fi") "Two" "One")
  t "a macro used through another macro is decided at the outer use"
    (ships ("\\def\\probeInner{\\ifnum\\probeN=1 One\\else Two\\fi}" ++
      "\\def\\probeOuter{\\probeInner}\\def\\probeN{1}\\def\\probeN{2}\\probeOuter") "Two" "One")
  let (_, useDs) := elabStr (dvDoc "" (showDef ++ "\\def\\probeN{2}\\probeShow"))
  t "the decision at the use is a keyed note"
    (useDs.any fun d => d.code == "N0114" && d.subject.isSome)
  -- Never decided at the definition: with parameters the use is the
  -- elaborator's, so the text's conditional is refused by name there, and
  -- no branch is chosen from the state the definition was made in.
  let argSrc := dvDoc "" ("\\def\\probeN{2}\\newcommand\\probeShow[1]{\\ifnum\\probeN=1 #1\\fi}" ++
    "\\def\\probeN{1}\\probeShow{Arg}")
  let (_, argDs) := elabStr argSrc
  t "a conditional in a macro with parameters is refused by name, not decided where it is defined"
    (argDs.any (fun d => d.code == "W0104" && d.subject.isSome) &&
      argDs.all (·.code != "N0114"))
  -- A picture written as a macro draws the state at each use.
  let fig := "\\newcommand{\\probeFig}{\\begin{tikzpicture}\\ifnum\\probeStage=1 " ++
    "\\node at (0,0) {Small};\\else \\node at (0,0) {Large};\\fi\\end{tikzpicture}}\n"
  let figs := text fig "\\def\\probeStage{1}\\probeFig\n\n\\def\\probeStage{2}\\probeFig"
  t "a picture written as a macro draws the state in force at each use"
    (occurs figs "Small" == 1 && occurs figs "Large" == 1)
