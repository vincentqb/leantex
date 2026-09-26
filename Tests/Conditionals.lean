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
  let shipped (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
  let text (src : String) : String := censusText (shipped src)
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
  let shipped (src : String) : Array CensusPage :=
    let (doc, _) := elabStr src
    censusOf (coveredColorsOf doc) (layoutOf oneFace doc)
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
