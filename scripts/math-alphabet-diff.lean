/-
External math-alphabet differential. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/math-alphabet-diff.lean
  lake env lean --run scripts/math-alphabet-diff.lean --selftest

This is a report, never a hermetic gate. It writes only below
`.lake/math-alphabet-diff`, sets each legacy alphabet explicitly to its
unicode-math `sym` source, and compares LuaLaTeX with leantex over four math
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

/-- One differential row: a math body set under a chosen source policy.
`scalarOnly` marks the text-slot cases where LuaLaTeX legitimately paints
from a text family the engine does not model — the scalar must still agree,
the font divergence is recorded, not failed. -/
structure Case where
  label : String
  body : String
  sym : Bool := true
  scalarOnly : Bool := false
  deriving Repr, Inhabited

/-- The widened matrix: per-range anchors, Letterlike holes, nested
alphabet stacks, `\boldsymbol`, and both unicode-math source policies. The
single-letter sym anchors kept from the original narrow matrix stand first;
the categories after them are what the reviewer's blocking findings turn
on. Every body is one painted formula so `formulaGlyph` reads it. -/
def cases : List Case :=
  -- sym-source single-letter anchors (the original narrow matrix)
  [ { label := "bb O", body := "\\mathbb{O}" },
    { label := "cal O", body := "\\mathcal{O}" },
    { label := "frak O", body := "\\mathfrak{O}" },
    { label := "bf O", body := "\\mathbf{O}" },
    { label := "it O", body := "\\mathit{O}" },
    { label := "sf O", body := "\\mathsf{O}", scalarOnly := true },
    { label := "tt O", body := "\\mathtt{O}" },
    { label := "rm O", body := "\\mathrm{O}" },
    -- per-range anchors: upper, lower, digit, Greek upper/lower, misc
    { label := "bf lower a", body := "\\mathbf{a}" },
    { label := "bf digit 5", body := "\\mathbf{5}" },
    { label := "bf Greek up", body := "\\mathbf{\\Gamma}" },
    { label := "bb digit 5", body := "\\mathbb{5}" },
    { label := "bb lower k", body := "\\mathbb{k}" },
    { label := "sf digit 5", body := "\\mathsf{5}", scalarOnly := true },
    { label := "tt digit 5", body := "\\mathtt{5}" },
    { label := "it lower x", body := "\\mathit{x}" },
    { label := "it Greek low", body := "\\mathit{\\gamma}" },
    { label := "it Greek up", body := "\\mathit{\\Gamma}" },
    { label := "up Greek up", body := "\\symup{\\Gamma}" },
    { label := "bfup Greek low", body := "\\symbfup{\\gamma}" },
    { label := "bfup nabla", body := "\\symbfup{\\nabla}" },
    -- Letterlike holes
    { label := "bb hole R", body := "\\mathbb{R}" },
    { label := "bb hole Z", body := "\\mathbb{Z}" },
    { label := "cal hole L", body := "\\mathcal{L}" },
    { label := "cal hole B", body := "\\mathcal{B}" },
    { label := "frak hole C", body := "\\mathfrak{C}" },
    { label := "frak hole H", body := "\\mathfrak{H}" },
    -- nested alphabet stacks: innermost that covers the range wins
    { label := "bf(cal A)", body := "\\mathbf{\\mathcal{A}}" },
    { label := "bb(cal A)", body := "\\mathbb{\\mathcal{A}}" },
    { label := "bf(cal 5)", body := "\\mathbf{\\mathcal{5}}" },
    { label := "bf(frak 5)", body := "\\mathbf{\\mathfrak{5}}" },
    { label := "bf(frak Z)", body := "\\mathbf{\\mathfrak{Z}}" },
    { label := "cal(bf A)", body := "\\mathcal{\\mathbf{A}}" },
    -- \boldsymbol: bold, variables staying italic
    { label := "bsym O", body := "\\boldsymbol{O}" },
    { label := "bsym 5", body := "\\boldsymbol{5}" },
    { label := "bsym alpha", body := "\\boldsymbol{\\alpha}" },
    { label := "bsym Gamma", body := "\\boldsymbol{\\Gamma}" },
    { label := "bsym(cal A)", body := "\\boldsymbol{\\mathcal{A}}" },
    -- default (text-sourced) policy. Phase 2 keeps the source scalar in the
    -- SELECTED MATH FACE when that face does not cover the alphabet — never a
    -- Unicode math scalar an unrelated host face would then satisfy
    -- per-character (Fira lacks sans: `\mathsf{R}` stays in FiraMath, not a
    -- host). LuaLaTeX paints the source scalar from a text family the engine
    -- does not yet model; that text-slot projection is phase 3, so these rows
    -- stay `scalarOnly` and their font divergence is recorded, not failed.
    { label := "text sf R", body := "\\mathsf{R}", sym := false, scalarOnly := true },
    { label := "text rm d", body := "\\mathrm{d}", sym := false, scalarOnly := true },
    { label := "text bf x", body := "\\mathbf{x}", sym := false, scalarOnly := true },
    { label := "text it y", body := "\\mathit{y}", sym := false, scalarOnly := true },
    { label := "text tt k", body := "\\mathtt{k}", sym := false, scalarOnly := true } ]

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

def preambleFor (sym : Bool) : String :=
  if sym then
    "\\usepackage[mathrm=sym,mathit=sym,mathbf=sym,mathsf=sym,mathtt=sym]{unicode-math}\n"
  else "\\usepackage{unicode-math}\n"

def texSource (bodyFontDir : String) (face : FaceCase) (c : Case) : String :=
  let p := System.FilePath.mk face.path
  let dir := (p.parent.getD ".").toString
  let file := p.fileName.getD face.path
  "\\documentclass{article}\n" ++
  "\\usepackage{fontspec}\n" ++
  preambleFor c.sym ++
  s!"\\setmainfont\{OpenSans-Regular.ttf}[Path={bodyFontDir}/]\n" ++
  s!"\\setmathfont[Scale=MatchLowercase]\{{file}}[Path={dir}/]\n" ++
  "\\pagestyle{empty}\n\\begin{document}\n$" ++ c.body ++
  "$\n\\end{document}\n"

/-- A filesystem-safe stem: letters and digits kept, everything else a dash. -/
def slug (s : String) : String :=
  String.ofList (s.toList.map fun ch =>
    if ('a' ≤ ch && ch ≤ 'z') || ('A' ≤ ch && ch ≤ 'Z') || ('0' ≤ ch && ch ≤ '9')
    then ch else '-')

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
  -- A single BMP scalar from a text family: the shape a text-sourced row
  -- reads once phase 2 keeps the source letter (`\mathsf{R}` → 'R') rather
  -- than a surrogate-pair math scalar. Exercises the non-surrogate
  -- `scalarOfUnits`/`codeUnit` path and font-prefix normalization.
  let bmp := "<span bbox=\"0 0 10 12\" font=\"XYZABC+LMSans10-Regular\" size=\"10.000\">\n" ++
    "<char bbox=\"0 0 10 12\" c=\"&#x0052;\"/>\n</span>"
  let wantBmp : Array GlyphFact :=
    #[{ scalar := "R", font := "LMSans10-Regular", advance := 10, sizeMilli := 10000 }]
  if parseGlyphs sample == want && parseGlyphs bmp == wantBmp then
    IO.println "math-alphabet-diff --selftest: all passed"
    return 0
  IO.eprintln s!"math-alphabet-diff --selftest: FAIL {repr (parseGlyphs sample)} {repr (parseGlyphs bmp)}"
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
  let fira ← IO.FS.realPath (root / "tests" / "corpus" / "fonts" / "FiraMath-Regular.otf")
  let required : List (String × String) :=
    [("Latin Modern Math", "latinmodern-math.otf"),
     ("TeX Gyre Pagella Math", "texgyrepagella-math.otf"),
     ("STIX Two Math", "STIXTwoMath-Regular.otf")]
  let mut faces : Array FaceCase := #[{ label := "Fira Math", path := fira.toString }]
  for (label, file) in required do
    let found ← try
      let out ← IO.Process.output { cmd := "kpsewhich", args := #[file], cwd := root }
      if out.exitCode == 0 then pure out.stdout.trimAscii.toString else pure ""
    catch _ => pure ""
    if found.isEmpty then
      IO.eprintln s!"math-alphabet-diff: {file} unavailable — four-face matrix untested"
      return 2
    faces := faces.push { label, path := found }
  let work := root / ".lake" / "math-alphabet-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let bodyFontDir := (root / "tests" / "corpus" / "fonts").toString
  IO.println "math-alphabet-diff: LuaLaTeX/leantex alphabet matrix"
  IO.println s!"  lualatex: {luaVersion}"
  IO.println s!"  ghostscript: {gsVersion}"
  IO.println "face\tcase\tsrc\tref-scalar\tengine-scalar\tref-font\tengine-font\tref-adv\tengine-adv\tresult"
  let mut failed := false
  for face in faces do
    for c in cases do
      let stem := slug face.label ++ "-" ++ slug c.label
      let src := work / s!"{stem}.tex"
      IO.FS.writeFile src (texSource bodyFontDir face c)
      let _ ← runTool "lualatex"
        #["-halt-on-error", "-interaction=batchmode", s!"-output-directory={work}", src.toString] root
      let refPdf := work / s!"{stem}.pdf"
      let enginePdf := work / s!"{stem}-engine.pdf"
      let _ ← runTool bin.toString #[src.toString, "-o", enginePdf.toString, "-q"] root
      let refFact ← extract root work (stem ++ "-ref") refPdf
      let engineFact ← extract root work (stem ++ "-engine") enginePdf
      let srcTag := if c.sym then "sym" else "text"
      match refFact, engineFact with
      | some r, some e =>
        -- LuaTeX's TeX-point scale and the PDF-point layout differ by
        -- 72/72.27; at these 10–12 pt sizes that is below 0.05 pt.
        let close := (r.advance - e.advance).natAbs ≤ 2 &&
          (r.sizeMilli - e.sizeMilli).natAbs ≤ 50
        let scalarOk := r.scalar == e.scalar
        -- Text-slot cases: the scalar must survive (no host glyph, no
        -- Unicode-alphanumeric remap the math face then lacks); LuaLaTeX's
        -- text family and the engine's math face differ by design.
        let ok := if c.scalarOnly then scalarOk else scalarOk && r.font == e.font && close
        unless ok do failed := true
        let mark :=
          if ok then (if c.scalarOnly && r.font != e.font then "PASS(text)" else "PASS")
          else "DIFF"
        IO.println s!"{face.label}\t{c.label}\t{srcTag}\t{r.scalar}\t{e.scalar}\t{r.font}\t{e.font}\t{r.advance}\t{e.advance}\t{mark}"
      | _, _ =>
        failed := true
        IO.println s!"{face.label}\t{c.label}\t{srcTag}\t?\t?\t?\t?\t?\t?\tMISSING"
  if failed then
    IO.eprintln "math-alphabet-diff: DIFF"
    return 1
  IO.println "math-alphabet-diff: PASS"
  return 0
