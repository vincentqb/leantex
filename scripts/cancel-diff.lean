/-
LuaLaTeX (cancel.sty over FiraMath) against leantex placement for `\cancel`/`\cancelto` over an
invented matrix: room within [0.40, 2.50], the value right of and above the strike.
Usage: lake build leantex ScriptsModules && lake env lean --run scripts/cancel-diff.lean [--report | --selftest]
-/
import LeanTex
import scripts.ToolDump

open LeanTex.Core

/-- A Poppler word box, coordinates in micro-points (1/72 in ÷ 1e6). -/
structure WordBox where
  text : String
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving Repr, BEq, Inhabited

/-- Every non-empty word box in a Poppler `-bbox` dump; cancel.sty's rules surface as
empty words and are dropped. -/
def parseWords (xml : String) : Array WordBox := Id.run do
  let mut out : Array WordBox := #[]
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<word " then
      match (attrOf line "xMin").bind microPt, (attrOf line "yMin").bind microPt,
          (attrOf line "xMax").bind microPt, (attrOf line "yMax").bind microPt with
      | some x0, some y0, some x1, some y1 =>
        let t := wordText line
        unless t.isEmpty do out := out.push { text := t, x0, y0, x1, y1 }
      | _, _, _, _ => pure ()
  return out

/-- The mathematical-italic scalar an ASCII letter maps to in math mode (italic h at
U+210E); a digit stays itself. -/
def mathItalic (c : Char) : String :=
  let u := c.toNat
  if c == 'h' then "ℎ"
  else if 'a'.toNat ≤ u && u ≤ 'z'.toNat then
    String.singleton (Char.ofNat (0x1D44E + (u - 'a'.toNat)))
  else if 'A'.toNat ≤ u && u ≤ 'Z'.toNat then
    String.singleton (Char.ofNat (0x1D434 + (u - 'A'.toNat)))
  else String.singleton c

def mathItalicStr (s : String) : String :=
  String.join (s.toList.map mathItalic)

/-- One case of the invented matrix: the struck source and its expected Poppler text, the
neighbour, the `\cancelto` value, display style and thick rules. -/
structure Case where
  label : String
  cmd : String
  struck : String
  struckWord : String
  neighbour : String
  value : Option String
  display : Bool
  thick : Bool
  deriving Inhabited

def mkCase (label cmd struck struckWord neighbour : String) (value : Option String)
    (display thick : Bool := false) : Case :=
  { label, cmd, struck, struckWord, neighbour, value, display, thick }

/-- Every cancellation flavour over narrow, wide and tall struck content, then display and
thick-rule variants of the wide arrow. -/
def cases : List Case :=
  let shapes := [("narrow", "v", mathItalicStr "v"),
    ("wide", "abcd", mathItalicStr "abcd"), ("tall", "\\int", "∫")]
  ["cancel", "bcancel", "xcancel", "cancelto"].flatMap (fun cmd =>
    shapes.map fun (label, struck, word) =>
      mkCase s!"{cmd}-{label}" cmd struck word "Z"
        (if cmd == "cancelto" then some "7" else none)) ++
  [ mkCase "display" "cancelto" "abcd" (mathItalicStr "abcd") "Z" (some "7") true
  , mkCase "thick" "cancelto" "abcd" (mathItalicStr "abcd") "Z" (some "7") false true ]

def bodyOf (c : Case) : String :=
  let mark := match c.value with
    | some v => s!"\\{c.cmd}\{{v}}\{{c.struck}}"
    | none => s!"\\{c.cmd}\{{c.struck}}"
  -- A `\quad` keeps the neighbour a separate word; it cancels in the room difference.
  let inner := s!"{mark}\\quad {c.neighbour}"
  if c.display then s!"\\[ {inner} \\]" else s!"$ {inner} $"

def optStr (c : Case) (room : Bool) : String :=
  String.intercalate "," ((if room then ["makeroom"] else ["overlap"]) ++
    (if c.thick then ["thicklines"] else []))

/-- The LuaLaTeX source: unicode-math over the corpus FiraMath face, cancel with the
case's options, the mark in pure red. -/
def luaSource (fontDir : String) (c : Case) (room : Bool) : String :=
  "\\documentclass{article}\n\\usepackage{fontspec}\n\\usepackage{unicode-math}\n" ++
  s!"\\setmainfont\{FiraSans-Regular.otf}[Path={fontDir}/]\n" ++
  s!"\\setmathfont\{FiraMath-Regular.otf}[Path={fontDir}/]\n" ++
  "\\usepackage{xcolor}\n" ++
  s!"\\usepackage[{optStr c room}]\{cancel}\n" ++
  "\\definecolor{markink}{HTML}{FF0000}\n" ++
  "\\renewcommand{\\CancelColor}{\\color{markink}}\n" ++
  "\\pagestyle{empty}\n\\begin{document}\n" ++ bodyOf c ++ "\n\\end{document}\n"

/-- The leantex source: the same FiraMath face through `\fonts`, the same
cancel options and mark colour. -/
def leanSource (fontDir : String) (c : Case) (room : Bool) : String :=
  "\\documentclass{article}\n" ++
  s!"\\fonts\{ dir = \"{fontDir}\", body = \"Fira Sans\", math = \"Fira Math\" }\n" ++
  "\\usepackage{xcolor}\n" ++
  s!"\\usepackage[{optStr c room}]\{cancel}\n" ++
  "\\definecolor{markink}{HTML}{FF0000}\n" ++
  "\\renewcommand{\\CancelColor}{\\color{markink}}\n" ++
  "\\begin{document}\n" ++ bodyOf c ++ "\n\\end{document}\n"

def runTool (cmd : String) (args : Array String) (cwd : System.FilePath) :
    IO IO.Process.Output := do
  IO.Process.output { cmd, args, cwd }

/-- The three glyph boxes a case exposes: the struck content, the value (`\cancelto`), and
the following atom; `none` when Poppler could not isolate exactly the expected words. -/
structure Boxes where
  struck : WordBox
  neighbour : WordBox
  value : Option WordBox
  deriving Repr, Inhabited

def isolate (c : Case) (words : Array WordBox) : Option Boxes := do
  -- Exact glyph text ignores the arrowhead, the page number and empty mark words.
  let unique (text : String) : Option WordBox :=
    match (words.filter (·.text == text)).toList with
    | [w] => some w
    | _ => none
  let struck ← unique c.struckWord
  let neighbour ← unique (mathItalicStr c.neighbour)
  match c.value with
  | some v =>
    let value ← unique v
    return { struck, neighbour, value := some value }
  | none => return { struck, neighbour, value := none }

/-- Whether two reserved advances agree in micro-points: within the ratio band for a
positive reference, within cancel.sty v2.2's 2pt line extension for a zero one. -/
def roomAgreement (reference engine : Int) : Bool :=
  0 ≤ reference && 0 ≤ engine &&
    if reference == 0 then engine ≤ 2000000
    else 400 * reference ≤ 1000 * engine && 1000 * engine ≤ 2500 * reference

def selftest : IO UInt32 := do
  let xml := "<page>\n<word xMin=\"1.000000\" yMin=\"5.000000\" xMax=\"3.000000\" \
yMax=\"7.000000\">𝑎𝑏</word>\n<word xMin=\"4.000000\" yMin=\"5.000000\" xMax=\"5.000000\" \
yMax=\"7.000000\">𝑍</word>\n<word xMin=\"3.200000\" yMin=\"2.000000\" xMax=\"3.800000\" \
yMax=\"3.000000\">7</word>\n<word xMin=\"1.500000\" yMin=\"5.500000\" xMax=\"2.500000\" \
yMax=\"6.500000\"></word>\n</page>"
  let ws := parseWords xml
  let expected : Array WordBox :=
    #[{ text := "𝑎𝑏", x0 := 1000000, y0 := 5000000, x1 := 3000000, y1 := 7000000 },
      { text := "𝑍", x0 := 4000000, y0 := 5000000, x1 := 5000000, y1 := 7000000 },
      { text := "7", x0 := 3200000, y0 := 2000000, x1 := 3800000, y1 := 3000000 }]
  let wsOk := ws == expected
  let c := mkCase "t" "cancelto" "ab" "𝑎𝑏" "Z" (some "7")
  let iso := isolate c ws
  let isoOk := match iso with
    | some b => b.struck.text == "𝑎𝑏" && b.neighbour.text == "𝑍" &&
        (b.value.map (·.text)) == some "7"
    | none => false
  -- Each expected glyph word must appear exactly once; unrelated words are irrelevant.
  let missingOk := ws.all fun w => (isolate c (ws.filter (·.text != w.text))).isNone
  let uniqueOk := ws.all fun w => (isolate c (ws.push w)).isNone
  let unrelatedOk := (isolate c (ws.push { text := ":", x0 := 0, y0 := 0, x1 := 1, y1 := 1 })).isSome
  let escapedOk := wordText "<word>&amp;lt; &lt; &gt; &amp;</word>" == "&lt; < > &"
  -- Unicode's italic h lives in Letterlike Symbols, not the plane-1 run.
  let mapOk := mathItalic 'a' == "𝑎" && mathItalic 'h' == "ℎ" &&
    mathItalic 'Z' == "𝑍" && mathItalic '7' == "7"
  let roomOk := roomAgreement 0 0 && roomAgreement 0 2000000 &&
    !roomAgreement 0 2000001 && !roomAgreement 0 (-1) &&
    !roomAgreement (-1) 0 && !roomAgreement 1000000 0 &&
    roomAgreement 1000000 400000 && roomAgreement 1000000 2500000 &&
    !roomAgreement 1000000 399999 && !roomAgreement 1000000 2500001
  if wsOk && isoOk && missingOk && uniqueOk && unrelatedOk && escapedOk && mapOk && roomOk then
    IO.println "cancel-diff --selftest: all passed"
    return 0
  IO.eprintln s!"cancel-diff --selftest: FAIL words={wsOk} isolate={isoOk} missing={missingOk} unique={uniqueOk} unrelated={unrelatedOk} escaped={escapedOk} map={mapOk} room={roomOk}"
  return 1

/-- A ratio `a / b` in per-mille, or none when `b` is zero. -/
def ratioMille (a b : Int) : Option Int :=
  if b == 0 then none else some (a * 1000 / b)

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  let reportOnly := args.contains "--report"
  let root ← IO.currentDir
  let leantex := root / ".lake" / "build" / "bin" / "leantex"
  unless ← leantex.pathExists do
    IO.eprintln "cancel-diff: build leantex first (lake build leantex)"
    return 2
  let work := root / ".lake" / "cancel-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let fontDir := (root / "testdata" / "corpus" / "fonts").toString
  for (cmd, probe) in [("lualatex", #["--version"]), ("pdftotext", #["-v"])] do
    if (← toolVersion cmd probe root) == "unavailable" then
      IO.eprintln s!"cancel-diff: {cmd} not available — untested"
      return 2
  IO.println "cancel-diff: cancellation placement, LuaLaTeX (cancel.sty) vs leantex"
  IO.println "  shared face: FiraMath / Fira Sans (repository corpus)"
  IO.println "  room: [0.40, 2.50] × positive reference; 0–2pt when reference adds none"
  IO.println s!"  lualatex: {← toolVersion "lualatex" #["--version"] root}"
  IO.println s!"  poppler:  {← toolVersion "pdftotext" #["-v"] root}"

  let measure (tag : String) (c : Case) (room : Bool)
      (src : String) (buildLua : Bool) : IO (Option Boxes) := do
    let stem := s!"{c.label}-{if room then "mk" else "ov"}-{tag}"
    let dir := work / stem
    IO.FS.createDirAll dir
    let tex := dir / "m.tex"
    IO.FS.writeFile tex src
    let pdf := dir / "m.pdf"
    if buildLua then
      let a := #["-interaction=nonstopmode", "-halt-on-error",
        s!"-output-directory={dir}", tex.toString]
      let _ ← runTool "lualatex" a root
      let r ← runTool "lualatex" a root
      if r.exitCode != 0 then return none
    else
      let r ← runTool leantex.toString #[tex.toString, "-o", pdf.toString] root
      if r.exitCode != 0 then return none
    let bbox := dir / "m.bbox"
    let r ← runTool "pdftotext" #["-bbox", pdf.toString, bbox.toString] root
    if r.exitCode != 0 then return none
    return isolate c (parseWords (← IO.FS.readFile bbox))

  let mut failed := false
  let mut cross := 0
  let mut crossFail := 0
  for c in cases do
    IO.println s!"\n{c.label}  (\\{c.cmd}, struck={c.struck}, {if c.display then "display" else "text"}{if c.thick then ", thick" else ""})"
    let build (buildLua : Bool) (room : Bool) : IO (Option Boxes) :=
      measure (if buildLua then "lua" else "lean") c room
        ((if buildLua then luaSource else leanSource) fontDir c room) buildLua
    let engines := [("lualatex", true), ("leantex", false)]
    let mut effects : List (String × Int) := []
    let mut rises : List (String × Int) := []
    let mut dxs : List (String × Int) := []
    for (ename, isLua) in engines do
      let mk ← build isLua true
      let ov ← build isLua false
      match mk, ov with
      | some mb, some ob =>
        let gapMk := mb.neighbour.x0 - mb.struck.x0
        let gapOv := ob.neighbour.x0 - ob.struck.x0
        let g1 := gapMk ≥ gapOv
        unless g1 do failed := true
        effects := effects ++ [(ename, gapMk - gapOv)]
        IO.println s!"  {ename}: neighbour gap makeroom {pointMicro gapMk} pt, overlap {pointMicro gapOv} pt [G1 room {if g1 then "PASS" else "FAIL"}]"
        match mb.value with
        | some v =>
          let dx := v.x0 - mb.struck.x1
          let rise := mb.struck.y0 - v.y0
          let g2 := dx > 0
          let g3 := rise > 0
          unless g2 && g3 do failed := true
          dxs := dxs ++ [(ename, dx)]
          rises := rises ++ [(ename, rise)]
          IO.println s!"    value dx {pointMicro dx} pt [G2 right {if g2 then "PASS" else "FAIL"}], rise {pointMicro rise} pt [G3 above {if g3 then "PASS" else "FAIL"}]"
        | none => pure ()
      | _, _ =>
        failed := true
        IO.println s!"  {ename}: could not isolate struck/neighbour/value boxes [FAIL]"
    match effects.lookup "lualatex", effects.lookup "leantex" with
    | some l, some e =>
      cross := cross + 1
      let ok := roomAgreement l e
      unless ok do crossFail := crossFail + 1
      let comparison := match ratioMille e l with
        | some r => s!"{r}‰ [400, 2500]"
        | none => s!"{pointMicro e} pt [0, 2]"
      IO.println s!"    room agreement: {comparison} [{if ok then "PASS" else "FAIL"}]"
    | _, _ => pure ()
    -- Value rise and dx are evidence only: the engines choose different slopes.
    let ratioLine (name : String) (m : List (String × Int)) : IO Unit := do
      match m.lookup "lualatex", m.lookup "leantex" with
      | some l, some e =>
        match ratioMille e l with
        | some r =>
          IO.println s!"    {name} leantex/lualatex = {r}‰ (evidence)"
        | none => IO.println s!"    {name}: lualatex baseline zero (evidence)"
      | _, _ => pure ()
    ratioLine "value rise" rises
    ratioLine "value dx" dxs
  IO.println s!"\ncancel-diff: {cross} gated room comparisons, {crossFail} out of band"
  if reportOnly then
    IO.println "cancel-diff: report only (no gate)"
    return 0
  if failed || crossFail > 0 then
    IO.eprintln "cancel-diff: FAIL"
    return 1
  IO.println "cancel-diff: PASS"
  return 0
