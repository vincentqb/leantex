module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- Lengths print as their base-unit counts in failure messages. -/
private instance : ToString Dim.Length := ⟨reprStr⟩

/-- The heads the accounting row ranges over: every `\if…` primitive of TeX82's table
(`Compat.texPrimitives`) and e-TeX's three. -/
def condProbeHeads : List String :=
  (Compat.texPrimitives.toList.filter (·.startsWith "if")) ++
    ["ifdefined", "ifcsname", "iffontchar"]

/-- One probe per head: what completes TeX's test, and which branch TeX takes (`none` where the
answer is run-time state this engine does not keep). -/
def condProbeArgs : List (String × String × Option Bool) :=
  [("if", "aa ", none), ("ifcase", "1 Zero\\or ", some true), ("ifcat", "aa ", none),
   ("ifdim", "1pt<2pt ", none), ("ifeof", "1 ", none), ("iffalse", " ", some false),
   ("ifhbox", "0 ", none), ("ifhmode", " ", none), ("ifinner", " ", none),
   ("ifmmode", " ", some false), ("ifnum", "1=1 ", some true), ("ifodd", "3 ", some true),
   ("iftrue", " ", some true), ("ifvbox", "0 ", none), ("ifvmode", " ", none),
   ("ifvoid", "0 ", none), ("ifx", "\\relax\\relax ", some true),
   ("ifdefined", "\\probeundefined ", some false), ("ifcsname", "relax\\endcsname ", none),
   ("iffontchar", "\\font`a ", none)]

/-- Where a picture's statements answer differently from running text: the four mode tests, since
pgf sets a picture in a horizontal box. -/
def condPicTaken : List (String × Bool) :=
  [("ifhmode", true), ("ifinner", true), ("ifmmode", false), ("ifvmode", false)]

/-- `\ifmmode` reads by the mode its text sets in: the text branch in text and in a formula's text
argument, the math branch in a formula; one the text leaves open stays as written; and its
source reads back as TeX spells the conditional. -/
def modeReadingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "\\usepackage{amsmath}\n\\newcommand{\\mm}[1]{\\ifmmode 7#1\\else 8#1\\fi}\n"
    "Aaa \\mm{1} and $\\mm{2}$ and $\\text{\\mm{3}}$ and \\ensuremath{\\mm{4}}."
  let text := censusText (censusOfSrc oneFace src)
  t s!"ifmmode: text takes the text branch, a formula the math branch, its text argument the text ({text})"
    (hasStr text "81" && hasStr text "72" && hasStr text "83" && hasStr text "74" &&
      !hasStr text "71" && !hasStr text "82" && !hasStr text "73")
  let raws := (Parse.parse "m.tex" (Lex.lex "m.tex" "\\ifmmode a\\else b\\fi \\ifmmode c").1).1
  t s!"ifmmode: a closed conditional reads back as written, an open one stays ({Parse.rawSrc raws})"
    (raws.any (· matches .env _ _ _) && Parse.rawSrc raws == "\\ifmmode a\\else b\\fi \\ifmmode c")

/-- Every conditional is accounted for, decided with its branch named or refused by name: wrapping
content in one adds a subjected diagnostic, and a decided head ships TeX's branch. -/
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
        t s!"'\\{h}' in running text ships the branch TeX takes, and only it"
          (hasStr bt keep && !hasStr bt drop)
      if let some v := (condPicTaken.lookup h).orElse fun _ => taken then
        let (keep, drop) := if v then ("Then", "Other") else ("Other", "Then")
        let pt := text picSrc
        t s!"'\\{h}' in a picture ships the branch TeX takes, and only it"
          (hasStr pt keep && !hasStr pt drop)
  -- A document's own `\newif` flag is a conditional head too.
  let flagSrc := dvDoc "\\newif\\ifprobe\n" "\\ifprobe Then\\else Other\\fi"
  t "a declared flag's conditional is decided by name"
    (decide (keyed (elabStr flagSrc).2 >
      keyed (elabStr (dvDoc "\\newif\\ifprobe\n" "Other")).2))
  modeReadingChecks ref oneFace

/-- A picture honours the macro state at its own site, read off the shipped page census. -/
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
  let scopeTxt := censusText (shipped (dvDoc ""
    "\\begin{center}\\def\\flag{}Inner\\end{center}\n\n\\ifdefined\\flag Leaked\\else Scoped\\fi"))
  t "a definition inside an environment is not visible after it"
    (hasStr scopeTxt "Scoped" && !hasStr scopeTxt "Leaked")
  -- A global definition escapes its environment, as TeX's `\gdef` does.
  let globalTxt := censusText (shipped (dvDoc ""
    "\\begin{center}\\gdef\\flag{}Inner\\end{center}\n\n\\ifdefined\\flag Kept\\else Lost\\fi"))
  t "a global definition outlives its environment"
    (hasStr globalTxt "Kept" && !hasStr globalTxt "Lost")
  -- A branch is decided before the boundary's bytes are taken, so two states are two requests.
  let bpic :=
    "\\begin{tikzpicture}\\ifnum\\mode=1 \\draw (0,0) parabola (1,1);\\else " ++
    "\\draw (0,0) parabola (2,2);\\fi\\end{tikzpicture}"
  let (bdoc, _) := elabStr (dvDoc "" ("\\def\\mode{1}\n" ++ bpic ++ "\n\n\\def\\mode{2}\n" ++ bpic))
  t "two states of one boundary picture are two requests"
    (bdoc.pictureSrcs.size == 2)

/-- `\ifx` compares the meaning TeX compares: replacement texts and prefixes, a parameterless
`\newcommand` not `\long`, and two robust commands refused by name. -/
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

/-- A conditional in a macro's text is decided where the macro is used, after its required arguments
are bound, or refused by name. -/
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
  let argSrc := dvDoc "" ("\\def\\probeN{2}\\newcommand\\probeShow[1]{\\ifnum\\probeN=1 #1\\fi}" ++
    "\\def\\probeN{1}\\probeShow{Arg}")
  let (_, argDs) := elabStr argSrc
  t "a conditional in a macro with parameters is decided after binding at the use"
    (argDs.all (·.code != "W0104") && argDs.any (·.code == "N0114") &&
      hasStr (censusText (censusOfSrc oneFace argSrc)) "Arg")
  let fig := "\\newcommand{\\probeFig}{\\begin{tikzpicture}\\ifnum\\probeStage=1 " ++
    "\\node at (0,0) {Small};\\else \\node at (0,0) {Large};\\fi\\end{tikzpicture}}\n"
  let figs := text fig "\\def\\probeStage{1}\\probeFig\n\n\\def\\probeStage{2}\\probeFig"
  t "a picture written as a macro draws the state in force at each use"
    (occurs figs "Small" == 1 && occurs figs "Large" == 1)

private def macroLengthOps : List String :=
  ["newlength", "setlength", "addtolength", "advance", "multiply", "divide"]

private def macroLengthExecuted (source : String) : Compat.Executed :=
  let raws := (Parse.parse "length-live.tex" (Lex.lex "length-live.tex" source).1).1
  Elab.executeInputs (m := Id) (fun _ context => pure (none, context))
    "length-live.tex" raws

-- Only executed top-level controls count: a definition's stored operands remain groups.
private def topMacroLengthOps (raws : Array Parse.Raw) : Array String :=
  raws.filterMap fun r => match r with
    | .ctrl name _ => if macroLengthOps.contains name then some name else none
    | _ => none

private def topMacroLengthUses (raws : Array Parse.Raw) : Array String :=
  raws.filterMap fun r => match r with
    | .ctrl name _ => if ["doublegap", "copygap", "wrappergap"].contains name
        then some name else none
    | _ => none

/-- A macro's length mutations reach the scoped rewrite once per executed use, in source order,
operands readable; dormant definitions and skipped branches contribute none. -/
def macroLengthExecutionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let setup := "\\newlength{\\probegap}\\setlength{\\probegap}{10pt}\n"
  let rule := "Leadword\\rule{\\probegap}{1pt}Tailword."
  let bad (ds : Array Diag) := ds.filter (·.severity != .note)
  let html (doc : Ir.Doc) :=
    let (head, tree, _) := HtmlDoc.emitTree {} doc
    Html.document "en" head tree
  for (label, operation, width) in [
      ("setlength", "\\setlength{\\probegap}{2\\probegap}", Dim.pt 40),
      ("addtolength", "\\addtolength{\\probegap}{\\probegap}", Dim.pt 40),
      ("advance", "\\advance\\probegap by 10pt", Dim.pt 30),
      ("multiply", "\\multiply\\probegap by 2", Dim.pt 40),
      ("divide", "\\divide\\probegap by 2", Dim.pt 5 / 2)] do
    let definition := "\\newcommand{\\doublegap}{" ++ operation ++ "}\n"
    let repeated := operation ++ "\n" ++ operation ++ "\n"
    let source := dvDoc (setup ++ definition ++ "\\doublegap\\doublegap\n") rule
    let control := dvDoc (setup ++ repeated) rule
    let actual := macroLengthExecuted source
    let direct := macroLengthExecuted control
    t s!"{label}: both use-time mutations reach the executor output in order"
      (topMacroLengthOps actual.raws == topMacroLengthOps direct.raws &&
        (topMacroLengthUses actual.raws).isEmpty)
    let (doc, ds) := elabStr source
    let (want, wantDs) := elabStr control
    let out := layoutOf fonts doc
    let wantOut := layoutOf fonts want
    t s!"{label}: repeated macro and direct calls have no loss"
      ((bad ds).isEmpty && (bad wantDs).isEmpty)
    t s!"{label}: direct control ships the calculated rule width"
      ((metricRuleSegs wantOut).map (·.1) == #[width])
    t s!"{label}: repeated reads ship the calculated rule width"
      ((metricRuleSegs out).map (·.1) == #[width])
    t s!"{label}: macro and direct calls ship identical rule geometry"
      (metricRuleSegs out == metricRuleSegs wantOut)
    t s!"{label}: macro and direct calls ship the same typed HTML"
      (html doc == html want)
  let operation := "\\setlength{\\probegap}{2\\probegap}"
  let definition := "\\newcommand{\\doublegap}{" ++ operation ++ "}\n"
  for (label, extra, use) in [
      ("copied meaning", "\\let\\copygap\\doublegap", "\\copygap\\copygap"),
      ("zero-argument forwarder", "\\newcommand{\\wrappergap}{\\doublegap}",
        "\\wrappergap\\wrappergap")] do
    let actual := macroLengthExecuted
      (dvDoc (setup ++ definition ++ extra ++ "\n" ++ use ++ "\n") rule)
    let direct := macroLengthExecuted (dvDoc (setup ++ operation ++ operation) rule)
    t s!"{label}: forwarding retains both executed length mutations"
      (topMacroLengthOps actual.raws == topMacroLengthOps direct.raws &&
        (topMacroLengthUses actual.raws).isEmpty)
  for (label, use) in [("unused", ""), ("skipped", "\\iffalse\\doublegap\\fi")] do
    let actual := macroLengthExecuted (dvDoc (setup ++ definition ++ use) rule)
    let direct := macroLengthExecuted (dvDoc setup rule)
    t s!"{label}: no dormant length mutation reaches the rewrite"
      (topMacroLengthOps actual.raws == topMacroLengthOps direct.raws)
  let declaration := "\\newlength{\\probegap}"
  let actual := macroLengthExecuted (dvDoc
    ("\\newcommand{\\makegap}{" ++ declaration ++ "}\\makegap") "Visibleword.")
  let direct := macroLengthExecuted (dvDoc declaration "Visibleword.")
  t "newlength: declaration reaches the rewrite at its macro use"
    (topMacroLengthOps actual.raws == topMacroLengthOps direct.raws)
  -- Column geometry reads the assignments later, so expansion must keep both use-time operands.
  let gap := "\\setlength{\\columnsep}{2\\columnsep}"
  let actual := macroLengthExecuted (dvDoc
    ("\\newcommand{\\doublegap}{" ++ gap ++ "}\\doublegap\\doublegap") "Visibleword.")
  t "columnsep: the exact failing source emits two unreduced assignments"
    (topMacroLengthOps actual.raws == #["setlength", "setlength"] &&
      (topMacroLengthUses actual.raws).isEmpty)

/-- A picture's macro-dependent values are the ones in force at its own site, for the walk and the
boundary alike, and a name with different texts at different sites is named. -/
def picSiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let occurs (s needle : String) : Nat := (s.splitOn needle).length - 1
  let pic (body : String) : String :=
    "\\begin{tikzpicture}\n" ++ body ++ "\\end{tikzpicture}\n"
  let strokes (pre body : String) : Array (Option Gfx.Paint) :=
    ((layoutOf oneFace (elabStr (dvDoc ("\\pictures{ tool = none }\n" ++ pre) (pic body))).1).pages[0]?.map
      fun p => (pageDraws p).map fun d => d.2.2.map (·.paint)).getD #[]
  let line := "\\draw (0,0) -- (2,0);\n"
  let red := strokes "" "\\draw[red] (0,0) -- (1,0);\n"
  let blue := strokes "" "\\draw[blue] (0,0) -- (1,0);\n"
  let installed := strokes ("\\newcommand{\\useasboundingbox}{\\draw[red]}\n" ++
      "\\newcommand{\\scoped}{\\draw[blue] (0,2) -- (3,2);}\n")
    ("\\useasboundingbox (0,0) rectangle (3,1);\n\\scoped \\draw (0,0) -- (1,1);\n" ++ line)
  t "a document's definitions of commands TikZ installs in every picture do not reach one"
    (!red.isEmpty && !blue.isEmpty && (strokes "" line).all installed.contains &&
      installed.all fun p => !red.contains p && !blue.contains p)
  let nodeText := censusText (censusOfSrc oneFace (dvDoc
    ("\\pictures{ tool = none }\n\\newcommand{\\pic}{Picx}\n\\newcommand{\\graph}[1]{Gr#1}\n" ++
      "\\newcommand{\\matrix}{Mfirst}\n\\renewcommand{\\matrix}{Msecond}\n")
    (pic "\\node at (0,0) {Ub[\\pic] Uc[\\graph{y}] Ud[\\matrix]};\n" ++
      "\n\\renewcommand{\\pic}{Picy}\n" ++ pic "\\node at (0,0) {Ue[\\pic]};\n")))
  t "a document's definitions of commands TikZ installs reach a node's text, where TikZ restores them"
    (hasStr nodeText "Ub[Picx]" && hasStr nodeText "Uc[Gry]" && hasStr nodeText "Ud[Msecond]" &&
      hasStr nodeText "Ue[Picy]")
  let (rdoc, _) := elabStr (dvDoc "\\newcommand{\\matrix}{Mfirst}\n\\renewcommand{\\matrix}{Msecond}\n"
    "\\begin{tikzpicture}\\draw (0,0) parabola (1,1) node {Uf[\\matrix]};\\end{tikzpicture}")
  t "a boundary picture's node text carries the definition in force where the picture stands"
    (rdoc.pictureSrcs.any fun p => hasStr p.2.body "Uf[Msecond]")
  let provided := censusText (censusOfSrc oneFace (dvDoc
    ("\\usepackage{tikz}\n\\pictures{ tool = none }\n\\providecommand{\\pgfmathsetmacro}[2]{\\def#1{#2}}\n" ++
      "\\providecommand{\\foreach}{}\n")
    (pic ("\\pgfmathsetmacro{\\va}{2*3}\\node at (0,0) {Pa[\\va]};\n" ++
      "\\foreach \\x in {1,2} {\\node at (\\x,1) {Pb[\\x]};}\n"))))
  t "a document's \\providecommand of a command pgf defines when it loads leaves pgf's"
    (hasStr provided "Pa[6.0]" && hasStr provided "Pb[1]" && hasStr provided "Pb[2]")
  let unloaded := censusText (censusOfSrc oneFace (dvDoc
    "\\providecommand{\\foreach}{Fz}\n\\providecommand{\\pgfmathsetmacro}[2]{Sm[#1][#2]}\n"
    "Text \\foreach{} here \\pgfmathsetmacro{a}{b}."))
  t "with no pgf package loaded, a document's \\providecommand of pgf's commands defines them"
    (hasStr unloaded "Fz" && hasStr unloaded "Sm[a][b]")
  t "a document's redefinition of a command TikZ does not install reaches its picture"
    (strokes "\\renewcommand{\\textcolor}[2]{#2}\n" ("\\textcolor{red}{" ++ line ++ "}\n") ==
      strokes "" line && strokes "" ("\\textcolor{red}{" ++ line ++ "}\n") != strokes "" line)
  let label := pic "\\node at (0,0) {\\probeLabel};\n"
  let labels := censusText (censusOfSrc oneFace (dvDoc "\\newcommand\\probeLabel{Early}\n"
    (label ++ "\n\\renewcommand\\probeLabel{Late}\n" ++ label)))
  t "a label macro redefined between two pictures draws each site's text"
    (occurs labels "Early" == 1 && occurs labels "Late" == 1)
  let lateSrc := dvDoc ""
    (pic ("\\ifnum\\probeLate=1 \\node at (0,0) {Small};\\else \\node at (0,0) {Large};\\fi\n") ++
      "\n\\def\\probeLate{1}\n")
  let (_, lateDs) := elabStr lateSrc
  t "a picture's test is not computed from a definition made after the picture"
    (lateDs.all (·.code != "N0114") && lateDs.any fun d => d.code == "W0334" && d.subject.isSome)
  let wrapPic := pic "\\node at (0,0) {\\probeWrap{x}};\n"
  let wrapSrc := dvDoc "\\newcommand\\probeWrap[1]{A#1}\n"
    (wrapPic ++ "\n\\renewcommand\\probeWrap[1]{B#1}\n" ++ wrapPic)
  let wrapped := censusText (censusOfSrc oneFace wrapSrc)
  t "a parameterized label redefined between pictures draws each site's text"
    (occurs wrapped "Ax" == 1 && occurs wrapped "Bx" == 1 &&
      (elabStr wrapSrc).2.all (·.severity == .note))
  let bpic := "\\begin{tikzpicture}\\draw (0,0) parabola (1,1) node {\\probeLabel};\\end{tikzpicture}"
  let (bdoc, _) := elabStr (dvDoc "\\newcommand\\probeLabel{Early}\n"
    (bpic ++ "\n\n\\renewcommand\\probeLabel{Late}\n" ++ bpic))
  t "two sites of one boundary picture under two label texts are two requests, each its own text"
    (bdoc.pictureSrcs.size == 2 &&
      bdoc.pictureSrcs.any (fun p => hasStr p.2.body "Early") &&
      bdoc.pictureSrcs.any (fun p => hasStr p.2.body "Late"))

/-- A picture's labels set the characters lualatex sets: a number written in a label or a list as
written, and a pgfmath value as pgfmath spells it. -/
def picNumberTextChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pic (body : String) : String := "\\begin{tikzpicture}\n" ++ body ++ "\\end{tikzpicture}\n\n"
  let sets : List (String × String × String) :=
    [("pgfmathsetmacro", "2*3", "6.0"), ("pgfmathsetmacro", "2.50", "2.50"),
     ("pgfmathsetmacro", "-2", "-2.0"), ("pgfmathsetmacro", "(2.50)", "2.50"),
     ("pgfmathsetmacro", "+2.50", "2.50"), ("pgfmathsetmacro", "0.5*4", "2.0"),
     ("pgfmathsetmacro", "10/4", "2.5"), ("pgfmathsetmacro", "max(2.50,1)", "2.5"),
     ("pgfmathsetmacro", "min(1,2)", "1.0"), ("pgfmathsetmacro", "2<3", "1"),
     ("pgfmathsetmacro", "3<2", "0"), ("pgfmathsetmacro", "ifthenelse(1,2,3)", "2"),
     ("pgfmathsetmacro", "2", "2"), ("pgfmathsetmacro", "02", "02"),
     ("pgfmathsetmacro", "-0", "0.0"), ("pgfmathsetmacro", "2pt", "2.0"),
     ("pgfmathsetmacro", "0-2", "-2.0"), ("pgfmathsetmacro", "100*100", "10000.0"),
     ("pgfmathtruncatemacro", "-2.7", "-2"), ("pgfmathtruncatemacro", "2.50", "2"),
     ("pgfmathsetlengthmacro", "2", "2.0pt"), ("pgfmathsetlengthmacro", "2.50", "2.5pt"),
     ("pgfmathsetlengthmacro", "2pt*2", "4.0pt"), ("pgfmathsetmacro", "(02)", "2"),
     ("pgfmathsetmacro", "+02", "2"), ("pgfmathsetmacro", " 02", "2"),
     ("pgfmathsetmacro", "(007)", "7"), ("pgfmathsetmacro", "(00)", "0"),
     ("pgfmathsetmacro", "ifthenelse(1,02,3)", "2"), ("pgfmathsetmacro", "(010)", "8"),
     ("pgfmathsetmacro", "010*1", "8.0"), ("pgfmathsetmacro", "2.", "2.")]
  let tag (k : Nat) : String :=
    "K" ++ String.singleton (Char.ofNat (97 + k / 26)) ++ String.singleton (Char.ofNat (97 + k % 26))
  let setPics := String.join (sets.zipIdx.map fun ((cmd, expr, _), k) =>
    pic ("\\" ++ cmd ++ "{\\v}{" ++ expr ++ "}\n\\node at (0,0) {" ++ tag k ++ "[\\v]};\n"))
  let listPics :=
    pic "\\foreach \\x in {-1,2*3,1.0,2.50} {\\node at (0,0) {La[\\x]};}\n" ++
    pic "\\foreach \\x in {1.0,1.5,...,3.0} {\\node at (\\x,0) {Lb[\\x]};}\n" ++
    pic "\\foreach \\x in {1,...,3} {\\pgfmathsetmacro{\\y}{\\x*2}\\node at (\\x,0) {Lc[\\y]};}\n" ++
    pic "\\foreach \\x in {2.50} {\\pgfmathsetmacro{\\y}{\\x}\\node at (0,0) {Ld[\\y]};}\n" ++
    pic "\\node at (0,0) {Le[2.50] Le[007] Le[1,000] Le[3.0] Le[.5] Le[3.14159] Le[0.0001]};\n" ++
    pic "\\foreach \\x in {1pt,2.5cm} {\\node at (0,0) {Lf[\\x]};}\n" ++
    pic "\\foreach \\x in {1pt} {\\pgfmathsetlengthmacro{\\y}{\\x}\\node at (0,0) {Lg[\\y]};}\n" ++
    pic "\\foreach \\x in {1pt} {\\pgfmathsetmacro{\\y}{\\x}\\node at (0,0) {Lh[\\y]};}\n" ++
    pic "\\foreach \\x in {2*3,(1),+2,-1} {\\pgfmathsetmacro{\\y}{\\x}\\node at (0,0) {Li[\\y]};}\n" ++
    pic "\\foreach \\x in {2*3} {\\pgfmathsetmacro{\\y}{ifthenelse(1,\\x,0)}\\node at (0,0) {Lj[\\y]};}\n" ++
    pic "\\pgfmathtruncatemacro{\\a}{-2.7}\\pgfmathsetmacro{\\b}{\\a}\\node at (0,0) {Lk[\\b]};\n" ++
    pic "\\foreach \\x in {-1} {\\pgfmathsetmacro{\\y}{(\\x)}\\node at (0,0) {Ll[\\y]};}\n" ++
    pic "\\foreach \\x in {-2,...,0} {\\pgfmathsetmacro{\\y}{\\x}\\node at (\\x,0) {Lm[\\y]};}\n" ++
    pic "\\pgfmathsetmacro{\\va}{010}\\pgfmathsetmacro{\\vb}{\\va*1}\\node at (0,0) {Ln[\\va][\\vb]};\n" ++
    pic "\\foreach \\x in {1 + 1} {\\node at (0,0) {Lo[\\x]};}\n" ++
    pic "\\foreach \\x/\\y in {1 / 2, 3/ 4 } {\\node at (\\x,0) {Lq[\\x][\\y]};}\n"
  let text := censusText (censusOfSrc oneFace (dvDoc "\\pictures{ tool = none }\n" (setPics ++ listPics)))
  for ((cmd, expr, want), k) in sets.zipIdx do
    t s!"a label sets '\\{cmd}' of '{expr}' as pgfmath spells it, {want}"
      (hasStr text (tag k ++ "[" ++ want ++ "]"))
  for (label, want) in [("La", "-1"), ("La", "2*3"), ("La", "1.0"), ("La", "2.50"),
      ("Lb", "1.0"), ("Lb", "1.5"), ("Lb", "2"), ("Lb", "2.5"), ("Lb", "3"),
      ("Lc", "2.0"), ("Lc", "4.0"), ("Lc", "6.0"), ("Ld", "2.50"),
      ("Le", "2.50"), ("Le", "007"), ("Le", "1,000"), ("Le", "3.0"), ("Le", ".5"),
      ("Le", "3.14159"), ("Le", "0.0001"), ("Lf", "1pt"), ("Lf", "2.5cm"), ("Lg", "1.0pt"),
      ("Lh", "1.0"), ("Li", "6.0"), ("Li", "1"), ("Li", "2"), ("Li", "-1.0"), ("Lj", "6.0"),
      ("Lk", "-2.0"), ("Ll", "-1.0"), ("Lm", "-2.0"), ("Lm", "-1.0"), ("Lm", "0"),
      ("Ln", "010][8.0"), ("Lo", "1 + 1"), ("Lq", "1 ][ 2"), ("Lq", "3][ 4 ")] do
    t s!"a label sets {want} where lualatex sets it" (hasStr text (label ++ "[" ++ want ++ "]"))
  t "a dimension's points are spelled as TeX's \\the spells them"
    (([1864679, 131072, 21845, 6554, -1, 0, 65535, 98304, 13108, -6554, 1073741823, 1, 32768,
        100] : List Int).map (Picture.texPoints ∘ Dim.Length.ofSp) ==
      ["28.45274", "2.0", "0.33333", "0.1", "-0.00002", "0.0", "0.99998", "1.5", "0.20001",
        "-0.1", "16383.99998", "0.00002", "0.5", "0.00153"])

/-- A definition no use reaches is decided against the state at the preamble's end and named as the
definition's. -/
def settleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let venue (after : String) : String :=
    "\\documentclass{article}\\title{T}\\author{A. Name}" ++
    "\\newif\\ifprobeanon\\probeanonfalse" ++
    "\\renewcommand{\\maketitle}{\\begingroup\\@maketitle\\endgroup}" ++
    "\\providecommand{\\@maketitle}{}" ++
    "\\renewcommand{\\@maketitle}{\\vbox{\\centering{\\Large\\bf \\@title\\par}" ++
    "\\ifprobeanon\\else\\begin{tabular}[t]{c}\\bf\\rule{\\z@}{24\\p@}\\@author" ++
    "\\end{tabular}\\fi\\vskip 0.3in \\@minus 0.1in}}" ++ after ++
    "\\begin{document}\\maketitle Body.\\end{document}"
  let styled (doc : Ir.Doc) : Bool :=
    inTitleBlock doc fun b => match b with
      | .para #[.strut h, .styled .bold _] => h == Ir.titleAuthorStrut
      | _ => false
  let (keptDoc, keptDs) := elabStr (venue "")
  t "a flag's branch in a text the engine reads at the preamble's end is kept, not taken out"
    (styled keptDoc)
  t "that decision is a keyed note"
    (keptDs.any fun d => d.code == "N0114" && d.subject.isSome && hasStr d.message "preamble")
  let (lateDoc, _) := elabStr (venue "\\probeanontrue")
  t "it reads the state at the preamble's end, not where the definition was made"
    (!styled lateDoc)
  -- Settling reads a text without running it: its flags stay undeclared and unset.
  let (_, declDs) := elabStr ("\\documentclass{article}" ++
    "\\newcommand\\probeDecl{\\newif\\ifprobelate}\\newif\\ifprobeon" ++
    "\\newcommand\\probeSet{\\probeontrue}" ++
    "\\begin{document}\\ifprobeon On\\else Off\\fi\\end{document}")
  t "a flag a settled text declares or sets is neither declared nor set by the settling"
    (declDs.all fun d => !(d.code == "N0114" &&
      (hasStr d.message "ifprobelate" || hasStr d.message "probeontrue" ||
        hasStr d.message "is true here")))
