/- TeX's own words for the causes lualatex also reports, read from its logs on invented probes.
Usage: lake build leantex TestsModules &&
  lake env lean --run scripts/textexts.lean [--write | --check] -/
import Tests.Diag

namespace TexTexts

/-- One cause: the row key, the code that reports it, the probe's body, and the names the text
carries, each becoming a slot in order. -/
structure Probe where
  key : String
  code : String
  body : String
  names : List String := []
  /-- A warning is read from its `Warning:` or `Overfull` log line, an error from its `! ` line. -/
  warning : Bool := false
  preamble : String := ""

def probes : List Probe := [
  { key := "brace", code := "E0202", body := "Kilo}" },
  { key := "tab", code := "E0311", body := "Kilo & lima" },
  { key := "math", code := "E0311", body := "Kilo ^ lima" },
  { key := "itemMissing", code := "E0310",
    body := "\\begin{itemize}\nKilo\n\\item lima\n\\end{itemize}" },
  { key := "preambleText", code := "E0313", preamble := "Kilo\n", body := "lima" },
  { key := "envMismatch", code := "E0205", names := ["itemize", "enumerate"],
    body := "\\begin{itemize}\n\\item Kilo\n\\end{enumerate}" },
  { key := "envUnclosed", code := "E0205", names := ["itemize", "document"],
    body := "\\begin{itemize}\n\\item Kilo\n" },
  { key := "inputMissing", code := "E0502", names := ["zzabsent.tex"],
    body := "\\input{zzabsent}" },
  { key := "nesting", code := "W0010",
    body := String.join ((List.range 5).map fun _ => "\\begin{itemize}\\item Kilo\n") ++
      String.join ((List.range 5).map fun _ => "\\end{itemize}\n") },
  { key := "preambleOnly", code := "W0340", body := "Kilo\n\n\\usepackage{xcolor}\n\nlima" },
  { key := "extraTab", code := "W0337",
    body := "\\begin{tabular}{ll}\nKilo & lima & mike \\\\\n\\end{tabular}" },
  { key := "citation", code := "W0351", names := ["zzghost"], warning := true,
    body := "Kilo \\cite{zzghost}." },
  { key := "reference", code := "W0349", names := ["zznowhere"], warning := true,
    body := "Kilo \\ref{zznowhere}." },
  { key := "labelTwice", code := "W0350", names := ["zztwice"], warning := true,
    body := "\\section{Kilo}\\label{zztwice}\\label{zztwice}" }]

def contains (s needle : String) : Bool := (s.splitOn needle).length > 1

def probeSource (p : Probe) : String :=
  "\\documentclass{article}\n" ++ p.preamble ++ "\\begin{document}\n" ++ p.body ++
    "\n\\end{document}\n"

/-- The text after a leading run of digits, dots and the unit, or `none` when none leads. -/
def afterNumber (s : String) (unit : String) : Option String :=
  let digits := s.toList.takeWhile fun c => c.isDigit || c == '.'
  if digits.isEmpty then none
  else
    let rest := (s.drop digits.length).toString
    if rest.startsWith unit then some (rest.drop unit.length).toString else none

/-- `s` with every `marker` followed by a number and `unit` removed. -/
def cutNumbered (s marker unit : String) : String :=
  match s.splitOn marker with
  | [] => s
  | first :: rest => rest.foldl (fun acc part =>
      match afterNumber part unit with
      | some after => acc ++ after
      | none => acc ++ marker ++ part) first

/-- TeX's text without the particulars it puts in: its line and page, a measure, a final period. -/
def cutParticulars (s : String) : String :=
  let s := cutNumbered s " on input line " ""
  let s := cutNumbered s " on page " ""
  let s := cutNumbered s " by " "pt"
  let s := match s.splitOn " (" with
    | head :: _ :: _ => if contains s "pt too " then head else s
    | _ => s
  let s := if s.endsWith "." then (s.dropEnd 1).toString else s
  s.trimAscii.toString

/-- The probe's names as slots `#1`, `#2`, in order, each standing exactly once in the text. -/
def slotted (s : String) (names : List String) : Except String String :=
  (names.zipIdx).foldlM (init := s) fun acc (n, i) =>
    if (acc.splitOn n).length == 2 then pure (acc.replace n s!"#{i + 1}")
    else throw s!"the name '{n}' stands other than once in '{s}'"

/-- The cause's line in lualatex's log: the first `! ` line for an error, the first warning line
naming the probe's first name (or any, when it names none) for a warning, its prefix dropped, and
whether LaTeX, not the engine, raised it. -/
def logText (log : String) (warning : Bool) (names : List String) : Option (String × Bool) :=
  let ls := (log.replace "\r\n" "\n").splitOn "\n"
  let names (l : String) : Bool := names.head?.all (contains l ·)
  if warning then
    ls.findSome? fun l =>
      if l.startsWith "LaTeX Warning: " && names l then
        some ((l.drop "LaTeX Warning: ".length).toString, true)
      else none
  else
    ls.findSome? fun l =>
      if l.startsWith "! LaTeX Error: " then some ((l.drop "! LaTeX Error: ".length).toString, true)
      else if l.startsWith "! " then some ((l.drop 2).toString, false)
      else none

structure Row where
  key : String
  code : String
  text : String
  source : String
  /-- Whether lualatex stopped with an error on the probe. -/
  failed : Bool

def runIn (dir : System.FilePath) (cmd : String) (args : Array String) :
    IO IO.Process.Output :=
  IO.Process.output { cmd := cmd, args := args, cwd := some dir, stdin := .null
                      env := #[("max_print_line", some "1000")] }

/-- A text's runs of letters. -/
def words (s : String) : List String :=
  let (out, cur) := s.toList.foldl (init := (([] : List String), "")) fun (out, cur) c =>
    if c.isAlpha then (out, cur.push c) else if cur.isEmpty then (out, cur) else (cur :: out, "")
  (if cur.isEmpty then out else cur :: out).reverse

/-- The words of a row's text outside its slots, four letters or more. -/
def fixedWords (text : String) : List String :=
  let parts : List (String × Nat) := (text.splitOn "#").zipIdx
  let fixed : List String := parts.map fun pi =>
    if pi.2 == 0 then pi.1 else String.ofList (pi.1.toList.dropWhile Char.isDigit)
  (words (String.join fixed)).filter (·.length ≥ 4)

/-- Does `l` hold `w` as a whole word. -/
def holdsWord (l w : String) : Bool := (words l).contains w

/-- The `latex.ltx` line where a row's words stand, read with the two lines after it since its
messages wrap, or the engine for a primitive's. -/
def sourceOf (ltx : Option (System.FilePath × Array String)) (engine text : String) :
    Option String :=
  let words := fixedWords text
  match ltx with
  | some (path, lines) =>
    let window (i : Nat) := " ".intercalate ((List.range 3).map fun k => lines[i + k]?.getD "")
    let first := words.headD ""
    let found := (List.range lines.size).find? fun i =>
      holdsWord (lines[i]?.getD "") first && words.length ≥ 2 &&
        words.all (holdsWord (window i) ·)
    found.map fun i => s!"{path.fileName.getD "latex.ltx"}:{i + 1}, {engine}"
  | none => none

/-- The commands `latex.ltx` declares `\\@onlypreamble`, by name; a declaration it cannot read
stops the run. -/
def onlyPreamble (ltx : Option (System.FilePath × Array String)) : Except String (List String) :=
  match ltx with
  | some (_, lines) => lines.toList.filterMapM fun l =>
      match l.trimAscii.toString.dropPrefix? "\\@onlypreamble" with
      | some rest =>
        let rest := String.ofList (rest.toString.toList.dropWhile (· == ' '))
        let name := String.ofList ((rest.drop 1).toString.toList.takeWhile fun c =>
          c.isAlpha || c == '@' || c == '_' || c == ':')
        if rest.startsWith "\\" && !name.isEmpty then pure (some name)
        else throw s!"unread \\@onlypreamble line: {l}"
      | none => pure none
  | none => pure []

def generate (root : System.FilePath) : IO (Array Row × List String) := do
  let first := ((← IO.Process.output { cmd := "lualatex", args := #["--version"] }).stdout.splitOn
    "\n").headD "lualatex"
  let version := ((first.dropPrefix? "This is ").map (·.toString)).getD first
  let ltxPath :=
    (← IO.Process.output { cmd := "kpsewhich", args := #["latex.ltx"] }).stdout.trimAscii
  let ltx ← if ltxPath.isEmpty then pure none else do
    let p : System.FilePath := ltxPath.toString
    pure (some (p, ((← IO.FS.readFile p).splitOn "\n").toArray))
  let mut rows := #[]
  for p in probes do
    let dir := root / p.key
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "t.tex") (probeSource p)
    let tex := runIn dir "lualatex"
      #["-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "t.tex"]
    -- A warning LaTeX reads from the .aux file, as a twice-defined label, needs the second run.
    let o ← if p.warning then do let _ ← tex; tex else tex
    let log ← if ← (dir / "t.log").pathExists then IO.FS.readFile (dir / "t.log") else pure ""
    let some (raw, latex) := logText log p.warning p.names
      | throw (IO.userError
          s!"textexts: probe {p.key} logged no {if p.warning then "warning" else "error"}")
    let text ← match slotted (cutParticulars raw) p.names with
      | .ok t => pure t
      | .error e => throw (IO.userError s!"textexts: probe {p.key}: {e}")
    if (fixedWords text).isEmpty then
      throw (IO.userError s!"textexts: probe {p.key}'s text '{text}' has no fixed word")
    let source ← if !latex then pure version else match sourceOf ltx version text with
      | some s => pure s
      | none => throw (IO.userError s!"textexts: probe {p.key}: no latex.ltx line raises '{text}'")
    rows := rows.push { key := p.key, code := p.code, text, source, failed := o.exitCode != 0 }
  match onlyPreamble ltx with
  | .ok names => return (rows, names)
  | .error e => throw (IO.userError s!"textexts: {e}")

def quote (s : String) : String := (Lean.Json.str s).compress

def render (rows : Array Row) (preamble : List String) : String :=
  let keys := rows.toList.map (·.key)
  let row (r : Row) : String :=
    s!"  | .{r.key} =>\n    \{ key := {quote r.key}, code := .{r.code},\n" ++
    s!"      text := {quote r.text},\n" ++
    s!"      source := {quote r.source} }\n"
  "module\n\npublic import LeanTex.Core.Diag\n\n" ++
  "/-! Generated by scripts/textexts.lean from lualatex's logs and latex.ltx. -/\n\n" ++
  "namespace LeanTex.Core\n\n" ++
  "public inductive TexKey where\n" ++ String.join (keys.map (s!"  | {·}\n")) ++
  "  deriving Repr, BEq, DecidableEq\n\n" ++
  "public def TexKey.row : TexKey → TexText\n" ++ String.join (rows.toList.map row) ++ "\n" ++
  "public def TexText.rows : List TexText :=\n  [" ++
    ", ".intercalate (keys.map (s!"TexKey.row .{·}")) ++ "]\n\n" ++
  "public def TexText.preambleOnly : List String :=\n  [" ++
    ",\n   ".intercalate (preamble.map quote) ++ "]\n\n" ++
  "end LeanTex.Core\n"

def dataPath : System.FilePath := "LeanTex/Core/TexTextData.lean"

/-- leantex's messages for the row's code on the row's probe. -/
def leantexSays (root : System.FilePath) (p : Probe) : IO (Array String) := do
  let dir := root / p.key / "leantex"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "t.tex") (probeSource p)
  let bin ← IO.FS.realPath ".lake/build/bin/leantex"
  let o ← runIn dir bin.toString #["t.tex", "-o", "t.pdf", "--porcelain", "--best-effort"]
  return ((o.stdout.splitOn "\n").filterMap fun l => (Lean.Json.parse l).toOption.bind fun j =>
    if (j.getObjValAs? String "code").toOption == some p.code then
      (j.getObjValAs? String "message").toOption
    else none).toArray

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := ".lake/textexts"
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll root
  let (rows, preamble) ← generate root
  let text := render rows preamble
  if args.contains "--write" then
    IO.FS.writeFile dataPath text
    IO.println s!"textexts: wrote {rows.size} rows to {dataPath}"
    return 0
  let mut faults := 0
  let committed := LeanTex.Core.TexText.rows.map fun r => (r.key, r.code.code, r.text)
  if committed != rows.toList.map (fun r => (r.key, r.code, r.text)) ||
      LeanTex.Core.TexText.preambleOnly != preamble then
    IO.println "textexts: the committed table differs from lualatex's words (run --write)"
    faults := faults + 1
  else
    let unsourced (t : String) : List String :=
      (t.splitOn "\n").filter fun l => !(l.trimAscii.toString.startsWith "source := ")
    if unsourced (← IO.FS.readFile dataPath) != unsourced text then
      IO.println "textexts: the committed table is not the generator's (run --write)"
      faults := faults + 1
    else if (← IO.FS.readFile dataPath) != text then
      IO.println "textexts: the table's sources name another TeX installation; its words agree"
  for (p, r) in probes.zip rows.toList do
    if r.code.startsWith "E" && !r.failed then
      IO.println s!"textexts: {r.key} {r.code} is an error lualatex accepts"
      faults := faults + 1
    let said ← leantexSays root p
    let want := ({ key := r.key, code := .E0001, text := r.text, source := "" } :
      LeanTex.Core.TexText).fill p.names
    if said.any (· == want) then
      IO.println s!"textexts: {r.key} {r.code} says '{want}'"
    else
      IO.println s!"textexts: {r.key} {r.code} does not say '{want}': {said.toList}"
      faults := faults + 1
  return if faults == 0 then 0 else 1

end TexTexts

def main (args : List String) : IO UInt32 := TexTexts.main args
