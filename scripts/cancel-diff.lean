/-
External cancellation-geometry placement differential. Run from the repo root:

  lake build leantex
  lake env lean --run scripts/cancel-diff.lean            # build + measure + gate
  lake env lean --run scripts/cancel-diff.lean --report   # measure, print, never fail
  lake env lean --run scripts/cancel-diff.lean --selftest  # parser self-check

This is a report and deeper oracle, never a `lake test` gate: it needs a TeX
installation and writes only under `.lake/cancel-diff/`. Run it when the
cancellation geometry (`Math.cancelGeom` and the marks it lays) changes.

It builds an invented matrix of `\cancel`/`\cancelto` cases — narrow, wide
and tall struck content, text and display style, thin and thick rules, room
reserved (`makeroom`) and overlapping, with and without a value — with both
LuaLaTeX (cancel.sty over unicode-math/FiraMath) and leantex (the same
FiraMath face), and asks Poppler `pdftotext -bbox` for the bounding boxes of
the struck content, the value and the following atom. From those boxes it
measures the placements the two engines must agree on in direction, and
prints every magnitude with the cross-engine ratio as evidence.

The struck content and the neighbour are separate math words, so Poppler
isolates each; the value is the digit 7, kept upright. Gated invariants,
both required of BOTH engines:

  G1  room reserved   the neighbour sits further right under makeroom than
                      under overlap (the reserved box holds the mark before
                      the next atom); the makeroom−overlap advance is held
                      to the band cross-engine
  G2  value to the right of the struck box            (\cancelto)
  G3  value above the struck baseline                 (\cancelto)

The cross-engine tolerance is a magnitude band [0.40, 2.50] on the room the
mark reserves (the neighbour's makeroom−overlap advance) — a box quantity
both engines derive from the struck ink and the same overbar clearance. It
catches a gross divergence (a mark reserving no room, an order-of-magnitude
misplacement) while tolerating the honest per-engine metric difference.

The value's rise and rightward offset are printed as evidence, NOT gated on
magnitude: leantex sets the `\cancelto` value as the struck subformula's
superscript (TeX's rule 18, `Math.cancelto_value_between`), while cancel.sty
sets it at the arrow tip, so the two agree in direction (G2, G3) but not in
scale by design — leantex's value sits lower and closer than cancel.sty's.
Poppler word boxes read each writer's font descriptor differently; the raw
boxes are evidence, not an identity. No private fixtures: the fonts are the
repository's own corpus faces and every struck symbol is invented.
-/
import LeanTex

open LeanTex.Core

/-- A Poppler word box, coordinates in micro-points (1/72 in ÷ 1e6). -/
structure WordBox where
  text : String
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving Repr, BEq, Inhabited

def attrOf (line attr : String) : Option String := do
  let after ← (line.splitOn (attr ++ "=\""))[1]?
  (after.splitOn "\"").head?

/-- A decimal string of points to micro-points. -/
def microPt (s : String) : Option Int := do
  let (mantissa, scale) ← Decl.parseDecimal s
  return mantissa * 1000000 / (scale : Int)

/-- The text between `>` and `</word>`, entities decoded. -/
def wordText (line : String) : String :=
  let after := String.intercalate ">" ((line.splitOn ">").drop 1)
  let body := (after.splitOn "</word>").headD ""
  (((body.replace "&amp;" "&").replace "&lt;" "<").replace "&gt;" ">").trimAscii.toString

/-- Every non-empty word box in a Poppler `-bbox` dump. cancel.sty's rules
surface as empty-text word boxes; those are dropped, since the differential
compares glyph placement, not each engine's mark encoding. -/
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

def pointMicro (v : Int) : String :=
  let sign := if v < 0 then "-" else ""
  let n := v.natAbs
  let frac := toString (n % 1000000)
  s!"{sign}{n / 1000000}.{String.ofList (List.replicate (6 - frac.length) '0')}{frac}"

/-- The mathematical-italic scalar an ASCII letter maps to in math mode,
matching leantex's elaboration and unicode-math: `a`–`z` at U+1D44E, `A`–`Z`
at U+1D434 (with the six holes the plane leaves filled from the Letterlike
block — none used here). A digit stays itself. -/
def mathItalic (c : Char) : String :=
  let u := c.toNat
  if 'a'.toNat ≤ u && u ≤ 'z'.toNat then
    String.singleton (Char.ofNat (0x1D44E + (u - 'a'.toNat)))
  else if 'A'.toNat ≤ u && u ≤ 'Z'.toNat then
    String.singleton (Char.ofNat (0x1D434 + (u - 'A'.toNat)))
  else String.singleton c

def mathItalicStr (s : String) : String :=
  String.join (s.toList.map mathItalic)

/-- One case of the invented matrix. `struck` is the ASCII struck content
(mapped to math italic for word matching); `neighbour` the following atom;
`value` the `\cancelto` target (`none` for a plain strike); `display`
whether the math is set in display style; `opts` the cancel.sty options. -/
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

/-- The matrix: one axis moved at a time off a wide `\cancelto` base. `∫`
gives a tall, narrow struck box; `abcd` a short, wide one; `v` a small one. -/
def cases : List Case :=
  [ mkCase "narrow"  "cancelto" "v"      (mathItalicStr "v")    "Z" (some "7")
  , mkCase "wide"    "cancelto" "abcd"   (mathItalicStr "abcd") "Z" (some "7")
  , mkCase "tall"    "cancelto" "\\int"  "∫"                    "Z" (some "7")
  , mkCase "display" "cancelto" "abcd"   (mathItalicStr "abcd") "Z" (some "7") true
  , mkCase "thick"   "cancelto" "abcd"   (mathItalicStr "abcd") "Z" (some "7") false true
  , mkCase "cancel"  "cancel"   "abcd"   (mathItalicStr "abcd") "Z" none
  , mkCase "bcancel" "bcancel"  "abcd"   (mathItalicStr "abcd") "Z" none
  , mkCase "xcancel" "xcancel"  "abcd"   (mathItalicStr "abcd") "Z" none ]

def bodyOf (c : Case) : String :=
  let mark := match c.value with
    | some v => s!"\\{c.cmd}\{{v}}\{{c.struck}}"
    | none => s!"\\{c.cmd}\{{c.struck}}"
  -- A `\quad` before the neighbour keeps it a separate Poppler word even
  -- under overlap (which otherwise collapses the mark's advance and merges
  -- the struck glyphs with the neighbour). The same fixed space sits in
  -- both room variants, so it cancels in the makeroom−overlap difference.
  let inner := s!"{mark}\\quad {c.neighbour}"
  if c.display then s!"\\[ {inner} \\]" else s!"$ {inner} $"

def optStr (c : Case) (room : Bool) : String :=
  String.intercalate "," ((if room then ["makeroom"] else ["overlap"]) ++
    (if c.thick then ["thicklines"] else []))

/-- The LuaLaTeX source: unicode-math over the corpus FiraMath face, cancel
in the case's options, the mark drawn in a pure red the report never needs
but that pins the mark's ink to one colour across engines. -/
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

def version (cmd : String) (args : Array String) (cwd : System.FilePath) : IO String := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    if out.exitCode == 0 then return ((out.stdout ++ out.stderr).splitOn "\n").headD "?"
    return "unavailable"
  catch _ => return "unavailable"

/-- The three glyph boxes a case exposes: the struck content, the value
(`\cancelto`), and the following atom. `none` when Poppler could not isolate
exactly the expected words. -/
structure Boxes where
  struck : WordBox
  neighbour : WordBox
  value : Option WordBox
  deriving Repr, Inhabited

def isolate (c : Case) (words : Array WordBox) : Option Boxes := do
  -- Match by exact glyph text: this ignores cancel.sty's arrowhead (a `:`
  -- glyph), the engine's page number, and the mark rules (empty words).
  let struck ← words.find? (·.text == c.struckWord)
  let neighbour ← words.find? (·.text == mathItalicStr c.neighbour)
  match c.value with
  | some v =>
    let value ← words.find? (·.text == v)
    return { struck, neighbour, value := some value }
  | none => return { struck, neighbour, value := none }

def selftest : IO UInt32 := do
  let xml := "<page>\n<word xMin=\"1.000000\" yMin=\"5.000000\" xMax=\"3.000000\" \
yMax=\"7.000000\">ab</word>\n<word xMin=\"4.000000\" yMin=\"5.000000\" xMax=\"5.000000\" \
yMax=\"7.000000\">Z</word>\n<word xMin=\"3.200000\" yMin=\"2.000000\" xMax=\"3.800000\" \
yMax=\"3.000000\">7</word>\n<word xMin=\"1.500000\" yMin=\"5.500000\" xMax=\"2.500000\" \
yMax=\"6.500000\"></word>\n</page>"
  let ws := parseWords xml
  let expected : Array WordBox :=
    #[{ text := "ab", x0 := 1000000, y0 := 5000000, x1 := 3000000, y1 := 7000000 },
      { text := "Z", x0 := 4000000, y0 := 5000000, x1 := 5000000, y1 := 7000000 },
      { text := "7", x0 := 3200000, y0 := 2000000, x1 := 3800000, y1 := 3000000 }]
  let wsOk := ws == expected
  let c := mkCase "t" "cancelto" "ab" "ab" "Z" (some "7")
  let iso := isolate c ws
  let isoOk := match iso with
    | some b => b.struck.text == "ab" && b.neighbour.text == "Z" &&
        (b.value.map (·.text)) == some "7"
    | none => false
  -- The math-italic mapping matches leantex elaboration on a known letter.
  let mapOk := mathItalic 'a' == "𝑎" && mathItalic 'Z' == "𝑍" && mathItalic '7' == "7"
  if wsOk && isoOk && mapOk then
    IO.println "cancel-diff --selftest: all passed"
    return 0
  IO.eprintln s!"cancel-diff --selftest: FAIL words={wsOk} isolate={isoOk} map={mapOk}"
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
  let fontDir := (root / "tests" / "corpus" / "fonts").toString
  for (cmd, probe) in [("lualatex", #["--version"]), ("pdftotext", #["-v"])] do
    if (← version cmd probe root) == "unavailable" then
      IO.eprintln s!"cancel-diff: {cmd} not available — untested"
      return 2
  IO.println "cancel-diff: cancellation placement, LuaLaTeX (cancel.sty) vs leantex"
  IO.println "  shared face: FiraMath / Fira Sans (repository corpus)"
  IO.println "  cross-engine magnitude band: [0.40, 2.50]; direction gated exactly"
  IO.println s!"  lualatex: {← version "lualatex" #["--version"] root}"
  IO.println s!"  poppler:  {← version "pdftotext" #["-v"] root}"

  -- Build one source with an engine and return its isolated boxes.
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
    -- Gap of the neighbour from the struck origin, per engine, both rooms.
    let build (buildLua : Bool) (room : Bool) : IO (Option Boxes) :=
      measure (if buildLua then "lua" else "lean") c room
        ((if buildLua then luaSource else leanSource) fontDir c room) buildLua
    let engines := [("lualatex", true), ("leantex", false)]
    let mut effects : List (String × Int) := []   -- room-reservation effect, per engine
    let mut rises : List (String × Int) := []      -- value rise, per engine
    let mut dxs : List (String × Int) := []         -- value dx, per engine
    for (ename, isLua) in engines do
      let mk ← build isLua true
      let ov ← build isLua false
      match mk, ov with
      | some mb, some ob =>
        let gapMk := mb.neighbour.x0 - mb.struck.x0
        let gapOv := ob.neighbour.x0 - ob.struck.x0
        let g1 := gapMk > gapOv
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
    -- The reserved-room band is gated cross-engine. The value's rise and dx
    -- are printed as evidence only: leantex sets the value as a superscript,
    -- cancel.sty at the arrow tip, so they agree in direction, not scale.
    let ratioLine (name : String) (m : List (String × Int)) : IO (Option Bool) := do
      match m.lookup "lualatex", m.lookup "leantex" with
      | some l, some e =>
        match ratioMille e l with
        | some r =>
          let ok := 400 ≤ r && r ≤ 2500
          IO.println s!"    {name} leantex/lualatex = {r}‰{if name == "room effect" then s!" [{if ok then "in band" else "OUT OF BAND"}]" else " (evidence)"}"
          return some ok
        | none => IO.println s!"    {name}: lualatex baseline zero — skipped"; return none
      | _, _ => return none
    match ← ratioLine "room effect" effects with
    | some ok => cross := cross + 1; unless ok do crossFail := crossFail + 1
    | none => pure ()
    let _ ← ratioLine "value rise" rises
    let _ ← ratioLine "value dx" dxs
  IO.println s!"\ncancel-diff: {cross} gated room-effect ratios, {crossFail} out of band"
  if reportOnly then
    IO.println "cancel-diff: report only (no gate)"
    return 0
  if failed || crossFail > 0 then
    IO.eprintln "cancel-diff: FAIL"
    return 1
  IO.println "cancel-diff: PASS"
  return 0
