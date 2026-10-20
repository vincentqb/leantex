/-
The cancellation probe the cancel-diff oracle measures and the cancel tier judges: invented cases
over the corpus Fira faces, their LaTeX and leantex sources, the anchors read off a colour-coded
raster, and the tolerances the tier states.
-/
import scripts.Board

namespace CancelProbe

/-- One invented case: its label, the formula's source and whether it is a display. -/
structure Case where
  label : String
  formula : String
  display : Bool
  deriving Inhabited

/-- Every slope class of `\cancel` and `\cancelto`, narrow, wide and tall operands, inline and
display, a sum with a limit, an integral with both limits and a fraction. -/
def cases : List Case :=
  let v := "\\textcolor{probeval}"
  [ ⟨"cancel-narrow", "\\cancel{v}", false⟩
  , ⟨"cancel-wide", "\\cancel{a+b+c+d}", false⟩
  , ⟨"cancel-tall", "\\cancel{\\frac{x}{y}}", true⟩
  , ⟨"bcancel-narrow", "\\bcancel{p}", false⟩
  , ⟨"xcancel-pair", "\\xcancel{q r}", false⟩
  , ⟨"to-narrow", s!"\\cancelto\{{v}\{0}}\{x}", false⟩
  , ⟨"to-wide", s!"\\cancelto\{{v}\{0}}\{a+b}", false⟩
  , ⟨"to-integral", s!"\\cancelto\{{v}\{\\infty}}\{\\int_0^1 t}", false⟩
  , ⟨"to-fraction", s!"\\cancelto\{{v}\{0}}\{\\frac\{r}\{s}}", true⟩
  , ⟨"to-sum", s!"\\cancelto\{{v}\{0}}\{\\sum_\{n} c_n (z_n - w)}", true⟩ ]

/-- The two package options a case is set under. -/
def rooms : List (String × String) := [("mk", "makeroom"), ("ov", "overlap")]

/-- A case's formula in math delimiters. -/
def mathOf (c : Case) : String :=
  if c.display then s!"\\[ {c.formula} \\]" else s!"${c.formula}$"

/-- The preamble lines both engines share: a small page, the strike in pure red, values in pure
blue. -/
def colours (opt : String) : String :=
  "\\usepackage[paperwidth=4in,paperheight=2in,margin=0.4in]{geometry}\n" ++
  "\\usepackage{xcolor}\n" ++
  s!"\\usepackage[{opt}]\{cancel}\n" ++
  "\\definecolor{probemark}{HTML}{FF0000}\n\\definecolor{probeval}{HTML}{0000FF}\n" ++
  "\\renewcommand{\\CancelColor}{\\color{probemark}}\n"

/-- One case per page. -/
def body : String :=
  String.intercalate "\n\\newpage\n" (cases.map mathOf) ++ "\n"

/-- The LuaLaTeX source: unicode-math over the corpus faces. -/
def luaSource (fontDir opt : String) : String :=
  "\\documentclass{article}\n\\usepackage{fontspec}\n\\usepackage{unicode-math}\n" ++
  s!"\\setmainfont\{FiraSans-Regular.otf}[Path={fontDir}/]\n" ++
  s!"\\setmathfont\{FiraMath-Regular.otf}[Path={fontDir}/]\n" ++ colours opt ++
  "\\pagestyle{empty}\n\\begin{document}\n" ++ body ++ "\\end{document}\n"

/-- The leantex source: the same faces through `\fonts`. -/
def leanSource (fontDir opt : String) : String :=
  "\\documentclass{article}\n" ++
  s!"\\fonts\{ dir = \"{fontDir}\", body = \"Fira Sans\", math = \"Fira Math\" }\n" ++
  colours opt ++ "\\pagestyle{empty}\n\\begin{document}\n" ++ body ++ "\\end{document}\n"

/-- Where both the oracle and the tier build leantex's probe, so its bytes do not depend on a
temporary path. -/
def probeDir : System.FilePath := ".lake" / "cancel-probe"

/-- The corpus faces from `probeDir`. -/
def probeFonts : String := "../../testdata/corpus/fonts"

/-- Ink boxes in raster pixels, `(left, top, right, bottom)` with y downward. -/
structure Ink where
  left : Int
  top : Int
  right : Int
  bottom : Int
  deriving Repr, BEq, Inhabited

/-- One case's measured boxes: the strike (red), the value (blue) and the struck operand (black),
with the em in pixels. -/
structure Boxes where
  em : Int
  mark : Ink
  value : Option Ink
  operand : Ink
  deriving Repr, Inhabited

/-- The anchors a case is judged by, in thousandths of an em: the strike's ink edges from the
operand's, and the value's left and bottom from the operand's right and bottom. -/
structure Anchors where
  left : Int
  bottom : Int
  right : Int
  top : Int
  valueX : Option Int
  valueY : Option Int
  deriving Repr, BEq, Inhabited

def Boxes.anchors (b : Boxes) : Anchors :=
  let m (px : Int) := px * 1000 / max 1 b.em
  { left := m (b.mark.left - b.operand.left), bottom := m (b.operand.bottom - b.mark.bottom)
    right := m (b.mark.right - b.operand.right), top := m (b.operand.top - b.mark.top)
    valueX := b.value.map fun v => m (v.left - b.operand.right)
    valueY := b.value.map fun v => m (b.operand.bottom - v.bottom) }

def Anchors.values (a : Anchors) : List (Option Int) :=
  [some a.left, some a.bottom, some a.right, some a.top, a.valueX, a.valueY]

/-- The largest anchor difference, `none` when one side measured a value the other did not. -/
def Anchors.gap (a b : Anchors) : Option Int :=
  (a.values.zip b.values).foldlM (fun worst (x, y) =>
    match x, y with
    | some x, some y => some (max worst (x - y).natAbs)
    | none, none => some worst
    | _, _ => none) 0

/-- The stated tolerances, thousandths of an em: leantex's PDF against LuaLaTeX's sets the same
faces, so a tenth of an em is the visible bar at reading distance; the browser's page against
leantex's PDF also carries the browser's own layout of the operand. -/
def pdfTolerance : Nat := 100
def htmlTolerance : Nat := 100

def engines : List String := ["lualatex", "pdf", "html"]

/-- An oracle row: `<case>-<room> <engine> <left> <bottom> <right> <top> <valueX|-> <valueY|->`. -/
def renderRow (label engine : String) (a : Anchors) : String :=
  let o (v : Option Int) := (v.map toString).getD "-"
  s!"{label} {engine} {a.left} {a.bottom} {a.right} {a.top} {o a.valueX} {o a.valueY}"

def parseRow (line : String) : Option (String × String × Anchors) := do
  let toks := (line.splitOn " ").filter (!·.isEmpty)
  let [label, engine, l, b, r, t, vx, vy] := toks | none
  let opt (s : String) : Option (Option Int) := if s == "-" then some none else s.toInt?.map some
  return (label, engine,
    { left := ← l.toInt?, bottom := ← b.toInt?, right := ← r.toInt?, top := ← t.toInt?
      valueX := ← opt vx, valueY := ← opt vy })

def oraclePath : String := "testdata/oracles/cancel-anchors.txt"

/-- Every row of an oracle file, and the unique value of a top-level `name:` line. -/
def readOracle (text : String) : Array (String × String × Anchors) :=
  ((text.splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" || (l.splitOn ": ").length > 1 then none else parseRow l).toArray

def oracleValue (text name : String) : Option String :=
  match (text.splitOn "\n").filterMap (fun raw =>
      let l := raw.trimAscii.toString
      if l.startsWith (name ++ ": ") then some (l.drop (name.length + 2)).toString else none) with
  | [v] => some v
  | _ => none

/-- Per case, whether `engine` is within `tol` of `against`; a case either side lacks counts as
a row that fails. -/
def judge (rows : Array (String × String × Anchors)) (engine against : String) (tol : Nat) :
    Nat × Nat := Id.run do
  let labels := rows.foldl (fun acc (l, _, _) => if acc.contains l then acc else acc.push l) #[]
  let mut pass := 0
  for l in labels do
    let find (e : String) := (rows.find? fun (l', e', _) => l' == l && e' == e).map (·.2.2)
    if let (some a, some b) := (find engine, find against) then
      if (a.gap b).any (· ≤ (tol : Int)) then pass := pass + 1
  return (pass, labels.size)

/-- The freshness key: this tree's leantex HTML and PDF of the probe, built from `probeDir`. -/
def buildKey (leantex : System.FilePath) : IO (Except String String) := do
  IO.FS.createDirAll probeDir
  let mut blobs : Array (String × ByteArray) := #[]
  for (tag, opt) in rooms do
    let tex := probeDir / s!"lean-{tag}.tex"
    IO.FS.writeFile tex (leanSource probeFonts opt)
    for ext in ["html", "pdf"] do
      let out := probeDir / s!"lean-{tag}.{ext}"
      let r ← IO.Process.output
        { cmd := leantex.toString, args := #[tex.fileName.getD "", "-o", out.fileName.getD "", "-q"]
          cwd := probeDir }
      if r.exitCode != 0 then
        return .error s!"leantex exited {r.exitCode} on {tex}: {r.stderr.trimAscii}"
      blobs := blobs.push (s!"{tag}.{ext}", ← IO.FS.readBinFile out)
  return .ok (Scoreboard.contentKey blobs)

end CancelProbe
