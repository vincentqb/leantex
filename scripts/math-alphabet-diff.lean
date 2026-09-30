/-
External math-alphabet differential. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/math-alphabet-diff.lean
  lake env lean --run scripts/math-alphabet-diff.lean --selftest

This is a report, never a hermetic gate. It writes only below
`.lake/math-alphabet-diff`, sets each legacy alphabet explicitly to its
unicode-math `sym` source, and compares LuaLaTeX with leantex over two math
faces and eight alphabets. Ghostscript reads each PDF's painted scalar,
font, advance, and point size; no IR dump or source spelling is an
observation.
-/
import LeanTex

open LeanTex.Core

structure GlyphFact where
  scalar : String
  font : String
  advance : Int
  sizeMilli : Int
  deriving Repr, BEq, Inhabited

structure FaceCase where
  label : String
  path : String
  deriving Repr, Inhabited

def alphabetCases : List (String × String) :=
  [("bb", "mathbb"), ("cal", "mathcal"), ("frak", "mathfrak"),
   ("bf", "mathbf"), ("it", "mathit"), ("sf", "mathsf"),
   ("tt", "mathtt"), ("rm", "mathrm")]

def attrOf (line attr : String) : Option String := do
  let after ← ((line.splitOn (attr ++ "=\"")).drop 1).head?
  (after.splitOn "\"").head?

def normalizedFont (s : String) : String :=
  match s.splitOn "+" with
  | [_prefix, rest] => rest
  | _ => s

def hexDigit : Char → Option Nat
  | c =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
    else none

def hexNatGo (n : Nat) : List Char → Option Nat
  | [] => some n
  | c :: rest => do
    let d ← hexDigit c
    hexNatGo (n * 16 + d) rest

def codeUnit (s : String) : Option Nat :=
  if s.startsWith "&#x" && s.endsWith ";" then
    hexNatGo 0 ((s.drop 3).dropEnd 1).toString.toList
  else s.toList.head?.map (·.toNat)

def scalarOfUnits (units : Array Nat) : Option Char :=
  match units.toList with
  | [hi, lo] =>
    if 0xD800 ≤ hi && hi ≤ 0xDBFF && 0xDC00 ≤ lo && lo ≤ 0xDFFF then
      some (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)))
    else none
  | [u] => some (Char.ofNat u)
  | _ => none

def milli (s : String) : Option Int := do
  let (mantissa, scale) ← Decl.parseDecimal s
  pure (mantissa * 1000 / (scale : Int))

def bboxWidth (s : String) : Option Int := do
  let parts := s.splitOn " "
  let x0 ← parts[0]?.bind String.toInt?
  let x1 ← parts[2]?.bind String.toInt?
  pure (x1 - x0)

def parseGlyphs (xml : String) : Array GlyphFact := Id.run do
  let mut out : Array GlyphFact := #[]
  let mut font := ""
  let mut advance := 0
  let mut sizeMilli := 0
  let mut units : Array Nat := #[]
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<span " then
      font := normalizedFont ((attrOf line "font").getD "")
      advance := (attrOf line "bbox").bind bboxWidth |>.getD 0
      sizeMilli := (attrOf line "size").bind milli |>.getD 0
      units := #[]
    else if line.startsWith "<char " then
      if let some u := (attrOf line "c").bind codeUnit then units := units.push u
    else if line == "</span>" then
      if let some c := scalarOfUnits units then
        out := out.push { scalar := String.ofList [c], font, advance, sizeMilli }
      units := #[]
  return out

def formulaGlyph (facts : Array GlyphFact) : Option GlyphFact :=
  facts[0]?

def firstLine (s : String) : String :=
  ((s.splitOn "\n").headD "unknown").trimAscii.toString

def runTool (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO IO.Process.Output := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"{cmd} exited {out.exitCode}: {(out.stdout ++ out.stderr).trimAscii.toString}")
  return out

def version (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    if out.exitCode == 0 then return some (firstLine (out.stdout ++ out.stderr))
    return none
  catch _ => return none

def texSource (bodyFontDir : String) (face : FaceCase) (cmd : String) : String :=
  let p := System.FilePath.mk face.path
  let dir := (p.parent.getD ".").toString
  let file := p.fileName.getD face.path
  "\\documentclass{article}\n" ++
  "\\usepackage{fontspec}\n" ++
  "\\usepackage[mathrm=sym,mathit=sym,mathbf=sym,mathsf=sym,mathtt=sym]{unicode-math}\n" ++
  s!"\\setmainfont\{OpenSans-Regular.ttf}[Path={bodyFontDir}/]\n" ++
  s!"\\setmathfont[Scale=MatchLowercase]\{{file}}[Path={dir}/]\n" ++
  "\\pagestyle{empty}\n\\begin{document}\n$\\" ++ cmd ++
  "{O}$\n\\end{document}\n"

def extract (root work : System.FilePath) (tag : String)
    (pdf : System.FilePath) : IO (Option GlyphFact) := do
  let xml := work / s!"{tag}.xml"
  let _ ← runTool "gs" #["-q", "-dNOPAUSE", "-dBATCH", "-r720",
    "-sDEVICE=txtwrite", "-dTextFormat=0", s!"-sOutputFile={xml}", pdf.toString] root
  return formulaGlyph (parseGlyphs (← IO.FS.readFile xml))

def selftest : IO UInt32 := do
  let sample := "<span bbox=\"1 2 9 12\" font=\"ABCDEF+FiraMath-Regular\" size=\"10.000\">\n" ++
    "<char bbox=\"1 2 9 12\" c=\"&#xd835;\"/>\n" ++
    "<char bbox=\"9 2 9 12\" c=\"&#xdc42;\"/>\n</span>"
  let want : Array GlyphFact :=
    #[{ scalar := "𝑂", font := "FiraMath-Regular", advance := 8, sizeMilli := 10000 }]
  if parseGlyphs sample == want then
    IO.println "math-alphabet-diff --selftest: all passed"
    return 0
  IO.eprintln s!"math-alphabet-diff --selftest: FAIL {repr (parseGlyphs sample)}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  let root ← IO.currentDir
  let bin := root / ".lake" / "build" / "bin" / "leantex"
  unless ← bin.pathExists do
    IO.eprintln "math-alphabet-diff: build leantex first"
    return 2
  let some luaVersion ← version "lualatex" #["--version"] root
    | IO.eprintln "math-alphabet-diff: lualatex unavailable — untested"; return 2
  let some gsVersion ← version "gs" #["--version"] root
    | IO.eprintln "math-alphabet-diff: ghostscript unavailable — untested"; return 2
  let lm ← runTool "kpsewhich" #["latinmodern-math.otf"] root
  let lmPath := lm.stdout.trimAscii.toString
  if lmPath.isEmpty then
    IO.eprintln "math-alphabet-diff: latinmodern-math.otf unavailable — multi-face matrix untested"
    return 2
  let fira ← IO.FS.realPath (root / "tests" / "corpus" / "fonts" / "FiraMath-Regular.otf")
  let faces : List FaceCase :=
    [{ label := "Fira Math", path := fira.toString },
     { label := "Latin Modern Math", path := lmPath }]
  let work := root / ".lake" / "math-alphabet-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let bodyFontDir := (root / "tests" / "corpus" / "fonts").toString
  IO.println "math-alphabet-diff: LuaLaTeX/leantex symbol-source matrix"
  IO.println s!"  lualatex: {luaVersion}"
  IO.println s!"  ghostscript: {gsVersion}"
  IO.println "face\talphabet\tref-scalar\tengine-scalar\tref-font\tengine-font\tref-advance\tengine-advance\tref-size\tengine-size\tresult"
  let mut failed := false
  for face in faces do
    for (alphabet, cmd) in alphabetCases do
      let stem := (face.label.replace " " "-").toLower ++ "-" ++ alphabet
      let src := work / s!"{stem}.tex"
      IO.FS.writeFile src (texSource bodyFontDir face cmd)
      let _ ← runTool "lualatex"
        #["-halt-on-error", "-interaction=batchmode", s!"-output-directory={work}", src.toString] root
      let refPdf := work / s!"{stem}.pdf"
      let enginePdf := work / s!"{stem}-engine.pdf"
      let _ ← runTool bin.toString #[src.toString, "-o", enginePdf.toString, "-q"] root
      let refFact ← extract root work (stem ++ "-ref") refPdf
      let engineFact ← extract root work (stem ++ "-engine") enginePdf
      match refFact, engineFact with
      | some r, some e =>
        -- LuaTeX's TeX-point scale and the PDF-point layout differ by
        -- 72/72.27; at these 10–12 pt sizes that is below 0.05 pt.
        let close := (r.advance - e.advance).natAbs ≤ 2 &&
          (r.sizeMilli - e.sizeMilli).natAbs ≤ 50
        let ok := r.scalar == e.scalar && r.font == e.font && close
        unless ok do failed := true
        IO.println s!"{face.label}\t{alphabet}\t{r.scalar}\t{e.scalar}\t{r.font}\t{e.font}\t{r.advance}\t{e.advance}\t{r.sizeMilli}\t{e.sizeMilli}\t{if ok then "PASS" else "DIFF"}"
      | _, _ =>
        failed := true
        IO.println s!"{face.label}\t{alphabet}\t?\t?\t?\t?\t?\t?\t?\t?\tMISSING"
  if failed then
    IO.eprintln "math-alphabet-diff: DIFF"
    return 1
  IO.println "math-alphabet-diff: PASS"
  return 0
