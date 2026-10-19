/- The cause oracle: error witnesses and context mutants, each leantex error judged by lualatex.
Usage: lake build leantex TestsModules && lake env lean --run scripts/diag-oracle.lean [--witnesses]
  [--mutants] [--only <code>...] [--lualatex <path>] [--jobs <j>] [--keep] [--selftest] -/
import Tests.DiagAudit

open LeanTex.Core

namespace DiagOracle

/-- Codes a wrapped twin changes the meaning of, since their cause is the end of input. -/
def endOfInput : List DiagCode := [.E0101, .E0102]

/-- leantex-native constructs TeX never reads; a witness writing one is not TeX's to judge. -/
def nativeSpellings : List String :=
  ["\\define", "\\page", "\\palette", "\\style", "\\allow", "\\assert", "\\pictures",
   "\\fonts", "\\theme", "\\runninghead", "\\runningfoot", "{ifbackend}", "\\pdfmeta"]

/-- The causes allowed to stop the writer (PRINCIPLES.md § Always ship). -/
def fatal : List DiagCode := [.E0001, .E0004, .E0330, .E0401, .E0402, .E0404, .E0501, .E0502]

/-- leantex's class name to the LaTeX class judging it. -/
def classMap : List (String × String) :=
  [("article", "article"), ("report", "report"), ("book", "book"), ("slides", "beamer"),
   ("beamer", "beamer")]

/-- Packages whose commands leantex supplies without a load, loaded for TeX only. -/
def prelude : String :=
  "\\usepackage{graphicx}\\usepackage{xcolor}\\usepackage{amsmath}\\usepackage{booktabs}" ++
  "\\usepackage{fontawesome5}"

/-- TeX log lines naming a defect TeX repaired and shipped. -/
def recoveryMarks : List String :=
  ["\\end occurred inside a group", "\\end occurred when", "LaTeX Warning: Reference",
   "LaTeX Warning: Citation", "Missing character:"]

def sentinel : String := "Kqzv"

def contains (s needle : String) : Bool := (s.splitOn needle).length > 1

def lines (s : String) : List String := (s.replace "\r\n" "\n").splitOn "\n"

def codeOf? (s : String) : Option DiagCode := DiagCode.all.find? (·.code == s)

structure Case where
  id : String
  kind : String
  code : Option DiagCode := none
  lean : String
  tex : String
  seed : Option String := none
  sentinel : Bool := false
  excluded : Option String := none

/-- The class a source declares, or `none` for a classless body. -/
def declaredClass? (src : String) : Option String :=
  (lines src).findSome? fun l =>
    if l.startsWith "\\documentclass" then
      match (l.splitOn "{").getLast? with
      | some rest => some ((rest.splitOn "}").headD "").trimAscii.toString
      | none => none
    else none

/-- `src` with the class mapped and the prelude appended on its `\documentclass` line, so every
other line keeps its number. -/
def texTwin (src : String) : Option String := do
  let cls ← declaredClass? src
  let mapped ← (classMap.find? (·.1 == cls)).map (·.2)
  let fix (l : String) : String :=
    if l.startsWith "\\documentclass" then
      l.replace ("{" ++ cls ++ "}") ("{" ++ mapped ++ "}") ++ prelude
    else l
  return "\n".intercalate ((lines src).map fix)

def wrapBody (src : String) : String :=
  if contains src "\\documentclass" then src
  else "\\documentclass{article}\n\\begin{document}\n" ++ src ++ "\n\\end{document}\n"

/-- Each error code's witness sources as the suite writes them, with the surface each is read in. -/
def witnessSources (fonts : Font.FontSet) (c : DiagCode) : Array (String × String) :=
  (diagWitnessWith { sourceOnly := true } fonts fonts fonts (fun _ => #[]) c).filterMap fun d =>
    match d.subject with
    | some s =>
      if s == witnessSource "tex" then some ("tex", d.message)
      else if s == witnessSource "md" then some ("md", d.message) else none
    | none => none

def auditWord? (c : DiagCode) : Option String :=
  (DiagAudit.registry.find? (·.code == c)).bind fun r =>
    if r.verdict == .refusal || r.verdict == .divergence then some r.verdict.word else none

def witnessCases (fonts : Font.FontSet) (only : List String) : Array Case := Id.run do
  let mut out := #[]
  for c in DiagCode.all do
    unless c.code.startsWith "E" do continue
    unless only.isEmpty || only.contains c.code do continue
    let srcs := witnessSources fonts c
    if srcs.isEmpty then
      out := out.push { id := c.code, kind := "witness", code := c, lean := "", tex := "",
                        excluded := some "driver, probe or layout witness" }
      continue
    let mut i := 0
    for (surface, raw) in srcs do
      i := i + 1
      let id := if srcs.size == 1 then c.code else s!"{c.code}.{i}"
      let src := wrapBody raw
      let why? : Option String :=
        if surface == "md" then some "markdown surface"
        else if endOfInput.contains c then some "end-of-input cause"
        else if nativeSpellings.any (contains raw ·) then some "native surface"
        else if (texTwin src).isNone then some "no mapped class"
        else none
      out := out.push { id, kind := "witness", code := c, lean := src,
                        tex := (texTwin src).getD "", excluded := why? }
  return out

/-- Block environments, each a context mutant's payload. -/
def blocks : List (String × String) :=
  [("minipage-inline", "\\begin{minipage}{3cm}" ++ sentinel ++ " text.\\end{minipage}"),
   ("minipage", "\\begin{minipage}{3cm}\n" ++ sentinel ++ " text.\n\\end{minipage}"),
   ("itemize", "\\begin{itemize}\n\\item " ++ sentinel ++ " text.\n\\end{itemize}"),
   ("enumerate", "\\begin{enumerate}\n\\item " ++ sentinel ++ " text.\n\\end{enumerate}"),
   ("description",
     "\\begin{description}\n\\item[Term] " ++ sentinel ++ " text.\n\\end{description}"),
   ("center", "\\begin{center}\n" ++ sentinel ++ " text.\n\\end{center}"),
   ("quote", "\\begin{quote}\n" ++ sentinel ++ " text.\n\\end{quote}"),
   ("tabular", "\\begin{tabular}{ll}\n" ++ sentinel ++ " & b\\\\\n\\end{tabular}"),
   ("verbatim", "\\begin{verbatim}\n" ++ sentinel ++ " text.\n\\end{verbatim}")]

/-- Context operators: a preamble line and the wrapping of a block. -/
def wrappers : List (String × String × (String → String)) :=
  [("raisebox", "", fun b => "A \\raisebox{2pt}{" ++ b ++ "} b."),
   ("fbox", "", fun b => "A \\fbox{" ++ b ++ "} b."),
   ("parbox", "", fun b => "A \\parbox{6cm}{" ++ b ++ "} b."),
   ("cell-l", "", fun b => "\\begin{tabular}{l}\n" ++ b ++ "\n\\end{tabular}"),
   ("cell-p", "", fun b => "\\begin{tabular}{p{6cm}}\n" ++ b ++ "\n\\end{tabular}"),
   ("macro-arg", "\\newcommand{\\wrapper}[1]{#1}\n", fun b => "\\wrapper{" ++ b ++ "}"),
   ("textbf-arg", "", fun b => "\\textbf{" ++ b ++ "}"),
   ("footnote-arg", "", fun b => "a\\footnote{" ++ b ++ "}")]

def framed (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\nPlaceholder text.\n\n" ++ body ++
    "\n\nMore placeholder text.\n\\end{document}\n"

def mutantCases : Array Case := Id.run do
  let mut out := #[]
  for (bname, b) in blocks do
    let seed := framed "" b
    out := out.push { id := "seed." ++ bname, kind := "seed", lean := seed,
                      tex := (texTwin seed).getD "", sentinel := contains b sentinel }
    for (wname, pre, wrap) in wrappers do
      let src := framed pre (wrap b)
      out := out.push {
        id := s!"{wname}.{bname}", kind := "mutant", lean := src, tex := (texTwin src).getD "",
        seed := some ("seed." ++ bname), sentinel := contains b sentinel }
  return out

structure LDiag where
  code : String
  line : Nat
  message : String
  deriving Repr, BEq

inductive Obs (α : Type) where
  | ran (value : α)
  | inconclusive (why : String)
  | untested

structure LRun where
  diags : Array LDiag
  text : Option String

structure TRun where
  exit : UInt32
  error : Option String := none
  errLine : Option Nat := none
  opener : Option Nat := none
  recovery : Option String := none
  text : Option String := none
  deriving Repr, BEq

def TRun.accepted (t : TRun) : Bool := t.exit == 0 && t.error.isNone

/-- The digits starting `s`, as a number. -/
def leadingNat? (s : String) : Option Nat :=
  let ds := s.toList.takeWhile Char.isDigit
  if ds.isEmpty then none else (String.ofList ds).toNat?

/-- TeX's first error, its `l.N` line, the opener line its message names, and a recovery line. -/
def parseLog (exit : UInt32) (log : String) : TRun := Id.run do
  let ls := lines log
  let mut error := none
  let mut errLine := none
  let mut opener := none
  for l in ls do
    if error.isNone && l.startsWith "! " then
      error := some (l.drop 2).toString
      match l.splitOn "on input line " with
      | _ :: rest :: _ => opener := leadingNat? rest
      | _ => pure ()
    else if error.isSome && errLine.isNone && l.startsWith "l." then
      errLine := leadingNat? (l.drop 2).toString
  let recovery := ls.find? fun l => recoveryMarks.any (contains l ·)
  return { exit, error, errLine, opener, recovery }

/-- A cascade naming a construct present in the source, as `expected '\end{document}'` when it is
there. -/
def spurious (src : String) (d : LDiag) : Bool :=
  ["expected '", "without matching '"].any fun lead =>
    match d.message.splitOn lead with
    | _ :: rest :: _ =>
      let named := (rest.splitOn "'").headD ""
      named.startsWith "\\" && contains src named
    | _ => false

structure Env where
  root : System.FilePath
  repo : System.FilePath
  leantex : System.FilePath
  lualatex : Option System.FilePath
  texVersion : String := ""
  budgetMs : Nat := 30000
  keep : Bool := false

def timeoutArgs (ms : Nat) : Array String :=
  let milli := String.ofList ((toString (1000 + ms % 1000)).toList.drop 1)
  #["--kill-after=2s", s!"{ms / 1000}.{milli}s"]

def run (cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String)) (ms : Nat) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := "/usr/bin/timeout", args := timeoutArgs ms ++ #[cmd] ++ args, cwd := some cwd, env,
    stdin := .null }

def pdfText (pdf : System.FilePath) (cwd : System.FilePath) : IO (Option String) := do
  unless ← pdf.pathExists do return none
  let o ← run "pdftotext" #["-enc", "UTF-8", pdf.toString, "-"] cwd #[] 30000
  return if o.exitCode == 0 then some o.stdout else none

def writeCase (dir : System.FilePath) (src : String) (repo : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "t.tex") src
  let png ← IO.FS.readBinFile (repo / "testdata" / "corpus" / "rects.png")
  for n in ["x.png", "logo.png"] do IO.FS.writeBinFile (dir / n) png

def parsePorcelain (out : String) : Option (Array LDiag) := Id.run do
  let mut ds := #[]
  let mut summary := false
  for l in lines out do
    match Lean.Json.parse l with
    | .error _ => pure ()
    | .ok j =>
      match j.getObjValAs? String "event" with
      | .ok "diagnostic" =>
        let code := (j.getObjValAs? String "code").toOption.getD ""
        let line := (j.getObjValAs? Nat "line").toOption.getD 0
        let message := (j.getObjValAs? String "message").toOption.getD ""
        ds := ds.push { code, line, message }
      | .ok "summary" => summary := true
      | _ => pure ()
  return if summary then some ds else none

def runLeantex (e : Env) (dir : System.FilePath) (src : String) : IO (Obs LRun) := do
  let d := dir / "leantex"
  writeCase d src e.repo
  let o ← run e.leantex.toString #["t.tex", "-o", "t.pdf", "--porcelain", "--best-effort",
      "--font-dir", (e.repo / "testdata" / "corpus" / "fonts").toString] d
    #[("HOME", some (e.root / "home").toString), ("LEANTEX_FONT", none)] (2 * e.budgetMs)
  IO.FS.writeFile (d / "porcelain.jsonl") o.stdout
  if o.exitCode ≥ 124 then return .inconclusive s!"leantex exit {o.exitCode}"
  match parsePorcelain o.stdout with
  | none => return .inconclusive "leantex wrote no summary"
  | some ds => return .ran { diags := ds, text := ← pdfText (d / "t.pdf") d }

def texEnv (e : Env) (lualatex : System.FilePath) : Array (String × Option String) :=
  let var := (e.root / s!"texmf-{hash e.texVersion}").toString
  #[("PATH", some ((lualatex.parent.getD ".").toString ++ ":/usr/bin:/bin")),
    ("TEXMFVAR", some var), ("TEXMFCACHE", some var), ("XDG_CACHE_HOME", some var),
    ("max_print_line", some "1000")]

def encodeT (t : TRun) : String :=
  s!"{t.exit}\n{t.error.getD ""}\n{t.errLine.getD 0}\n{t.opener.getD 0}\n{t.recovery.getD ""}\n" ++
    match t.text with | some s => "1\n" ++ s | none => "0\n"

def decodeT (s : String) : Option TRun :=
  match s.splitOn "\n" with
  | exit :: error :: l :: op :: rec :: has :: text =>
    let nz (n : Nat) := if n == 0 then none else some n
    let ne (x : String) := if x.isEmpty then none else some x
    some {
      exit := (exit.toNat?.getD 1).toUInt32, error := ne error, errLine := nz (l.toNat?.getD 0),
      opener := nz (op.toNat?.getD 0), recovery := ne rec,
      text := if has == "1" then some ("\n".intercalate text) else none }
  | _ => none

def runTex (e : Env) (dir : System.FilePath) (src : String) : IO (Obs TRun) := do
  let some lualatex := e.lualatex | return .untested
  let cache := e.root / "cache" / s!"{hash (src ++ "\x00" ++ e.texVersion)}.tex"
  if ← cache.pathExists then
    if let some t := decodeT (← IO.FS.readFile cache) then return .ran t
  let d := dir / "lualatex"
  writeCase d src e.repo
  let o ← run lualatex.toString #["-interaction=nonstopmode", "-halt-on-error",
    "-no-shell-escape", "t.tex"] d (texEnv e lualatex) e.budgetMs
  if o.exitCode ≥ 124 then return .inconclusive s!"lualatex exit {o.exitCode}"
  let logPath := d / "t.log"
  let log ← if ← logPath.pathExists then IO.FS.readFile logPath else pure o.stdout
  let t := parseLog o.exitCode log
  let text ← if t.accepted then pdfText (d / "t.pdf") d else pure none
  let t := { t with text }
  IO.FS.createDirAll (e.root / "cache")
  IO.FS.writeFile cache (encodeT t)
  return .ran t

structure Row where
  id : String
  kind : String
  code : String
  verdict : String
  leanLine : Nat := 0
  texLine : Nat := 0
  texError : String := ""
  message : String := ""

def Row.tsv (r : Row) : String :=
  let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
  "\t".intercalate [r.id, r.kind, r.code, r.verdict, toString r.leanLine, toString r.texLine,
    clean r.texError, clean r.message]

def isError (d : LDiag) : Bool := d.code.startsWith "E"
def isWarning (d : LDiag) : Bool := d.code.startsWith "W"

/-- The verdict rows of one case, the seed's observations given for a mutant. -/
def judge (c : Case) (l : Obs LRun) (t : Obs TRun) (seed : Option (Obs LRun × Obs TRun)) :
    Array Row := Id.run do
  let row (code verdict : String) : Row := { id := c.id, kind := c.kind, code, verdict }
  let codeName := (c.code.map (·.code)).getD "-"
  if let some why := c.excluded then return #[row codeName s!"excluded {why}"]
  match l, t with
  | .untested, _ | _, .untested => return #[row codeName "untested"]
  | .inconclusive why, _ | _, .inconclusive why =>
    return #[{ row codeName "inconclusive" with message := why }]
  | .ran lr, .ran tr =>
    let mut considered := lr.diags.filter isError
    if c.kind != "witness" then
      match seed with
      | some (.ran sl, .ran st) =>
        if !st.accepted || sl.diags.any (fun d => isError d || isWarning d) then
          return #[{ row codeName "confounded" with
            texError := st.error.getD "", message := "the top-level twin is not clean" }]
        let inSeed (d : LDiag) := sl.diags.any fun s => s.code == d.code && s.message == d.message
        considered := lr.diags.filter fun d => (isError d || isWarning d) && !inSeed d
      | some _ => return #[row codeName "inconclusive"]
      | none => pure ()
    let spur := considered.filter (spurious c.lean)
    let rest := (considered.filter (!spurious c.lean ·)).qsort (·.line < ·.line)
    let first := (rest[0]?.map (·.line)).getD 0
    let texLine := (tr.errLine.getD 0)
    let mut rows := #[]
    for d in rest do
      let verdict :=
        if d.line != first then "cascade"
        else if tr.accepted then (if tr.recovery.isSome then "tex-ships" else "false-cause")
        else if some d.line == tr.errLine || some d.line == tr.opener then "confirmed"
        else if tr.errLine.isNone && tr.opener.isNone then "unlocated"
        else "elsewhere"
      let texError := (if tr.accepted then tr.recovery else tr.error).getD ""
      rows := rows.push { row d.code verdict with
        leanLine := d.line, texLine, texError, message := d.message }
    for d in spur do
      rows := rows.push { row d.code "cascade-spurious" with
        leanLine := d.line, texLine, message := d.message }
    if rest.isEmpty && !tr.accepted then
      rows := rows.push { row codeName "missed" with texLine, texError := tr.error.getD "" }
    if c.kind == "mutant" && tr.accepted then
      unless considered.isEmpty do
        rows := rows.push { row "-" "transparency" with
          message := " ".intercalate (considered.map (·.code)).toList }
      if c.sentinel then
        let inTex := (tr.text.map (contains · sentinel)).getD false
        let inLean := (lr.text.map (contains · sentinel)).getD false
        if inTex != inLean then
          rows := rows.push { row "-" "sentinel" with
            message := s!"lualatex shows it: {inTex}; leantex shows it: {inLean}" }
    if c.kind == "witness" && rows.isEmpty then rows := rows.push (row codeName "not-fired")
    return rows.map fun r => match (codeOf? r.code).bind auditWord? with
      | some w => { r with verdict := "audit:" ++ w }
      | none => r

def parMap (jobs : Nat) (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let mut out := #[]
  let mut i := 0
  while i < xs.size do
    let chunk := xs.extract i (i + max jobs 1)
    let tasks ← chunk.mapM fun x => IO.asTask (f x) .dedicated
    for task in tasks do out := out.push (← IO.ofExcept (← IO.wait task))
    i := i + max jobs 1
  return out

def observe (e : Env) (c : Case) : IO (Obs LRun × Obs TRun) := do
  if c.excluded.isSome then return (.untested, .untested)
  let dir := e.root / "run" / c.id
  let l ← runLeantex e dir c.lean
  let t ← runTex e dir c.tex
  return (l, t)

/-- Every case observed and judged, a mutant against its seed's observations. -/
def judgeAll (e : Env) (jobs : Nat) (cases : Array Case) : IO (Array Row × Array LDiag) := do
  let obs ← parMap jobs cases (observe e)
  let seeds := (cases.zip obs).filter (·.1.kind == "seed") |>.map fun (c, o) => (c.id, o)
  let mut rows := #[]
  let mut emitted := #[]
  for (c, (l, t)) in cases.zip obs do
    let seed := c.seed.bind fun s => (seeds.find? (·.1 == s)).map (·.2)
    let rs := judge c l t seed
    rows := rows ++ rs
    if let .ran lr := l then emitted := emitted ++ lr.diags
    if e.keep && rs.any (·.verdict == "false-cause") then
      IO.FS.createDirAll (e.root / "cases" / c.id)
      IO.FS.writeFile (e.root / "cases" / c.id / "leantex.tex") c.lean
      IO.FS.writeFile (e.root / "cases" / c.id / "lualatex.tex") c.tex
  let runDir := e.root / "run"
  if ← runDir.pathExists then IO.FS.removeDirAll runDir
  return (rows, emitted)

def resolve (cmd : String) : IO (Option System.FilePath) := do
  let path := (← IO.getEnv "PATH").getD ""
  for dir in path.splitOn ":" do
    let p := System.FilePath.mk dir / cmd
    if ← p.pathExists then return some p
  return none

/-- The premises the verdicts read: TeX meets a closed stdin, and starts with the reduced PATH. -/
def premises (e : Env) : IO (Array String) := do
  let some lualatex := e.lualatex | return #[]
  let mut failed := #[]
  let version ← run lualatex.toString #["--version"] e.root (texEnv e lualatex) e.budgetMs
  unless version.exitCode == 0 do failed := failed.push "pathKept: lualatex did not start"
  let dir := e.root / "premise"
  writeCase dir "\\documentclass{article}\n\\begin{document}\nx\n" e.repo
  let o ← run lualatex.toString #["-interaction=nonstopmode", "t.tex"] dir (texEnv e lualatex)
    e.budgetMs
  unless o.exitCode != 0 && o.exitCode < 124 do
    failed := failed.push s!"stdinClosed: an unfinished body exited {o.exitCode}"
  IO.FS.removeDirAll dir
  return failed

def setup (repo : System.FilePath) (lualatex? : Option String) (keep : Bool) : IO Env := do
  let root := repo / ".lake" / "diag-oracle"
  IO.FS.createDirAll (root / "home")
  let lualatex ← match lualatex? with
    | some p => do
      let path := System.FilePath.mk p
      pure (if ← path.pathExists then some path else none)
    | none => resolve "lualatex"
  let leantex ← IO.FS.realPath (repo / ".lake" / "build" / "bin" / "leantex")
  let e : Env := { root, repo, leantex, lualatex, keep }
  match lualatex with
  | none => return e
  | some p =>
    let v ← run p.toString #["--version"] root (texEnv e p) 30000
    return { e with texVersion := ((lines v.stdout).headD "").trimAscii.toString }

def summary (rows : Array Row) (emitted : Array LDiag) : Array String := Id.run do
  let mut out := #[]
  let codes := (rows.map (·.code)).toList.eraseDups
  for code in codes do
    let vs := (rows.filter (·.code == code)).map (·.verdict)
    let counts := vs.toList.eraseDups.map fun v => s!"{v} {vs.toList.count v}"
    out := out.push s!"summary\t{code}\t{", ".intercalate counts}"
  for code in (emitted.map (·.code)).toList.eraseDups do
    if let some c := codeOf? code then
      if c.loss == .dropped && !fatal.contains c then
        out := out.push s!"error-not-fatal\t{code}\t{(emitted.filter (·.code == code)).size}"
  return out

structure Options where
  witnesses : Bool := false
  mutants : Bool := false
  only : List String := []
  lualatex : Option String := none
  jobs : Option Nat := none
  keep : Bool := false
  selftest : Bool := false

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--witnesses" :: r, o => parse r { o with witnesses := true }
  | "--mutants" :: r, o => parse r { o with mutants := true }
  | "--keep" :: r, o => parse r { o with keep := true }
  | "--selftest" :: r, o => parse r { o with selftest := true }
  | "--lualatex" :: p :: r, o => parse r { o with lualatex := some p }
  | "--jobs" :: j :: r, o => match j.toNat? with
    | some n => parse r { o with jobs := some n }
    | none => .error s!"--jobs needs a number, not '{j}'"
  | "--only" :: r, o => parse r o
  | a :: r, o =>
    if (codeOf? a).isSome then parse r { o with only := o.only ++ [a] }
    else .error s!"unknown argument '{a}'"

def defaultJobs : IO Nat := do
  let cores := ((lines (← IO.FS.readFile "/proc/cpuinfo")).filter (·.startsWith "processor")).length
  let mem ← IO.FS.readFile "/proc/meminfo"
  let kib := ((lines mem).findSome? fun l =>
    if l.startsWith "MemAvailable:" then
      (((l.drop "MemAvailable:".length).toString.trimAscii.toString.splitOn " ").headD "").toNat?
    else none).getD 0
  return min 16 (min (max 1 cores) (max 1 (kib / 700000)))

def has (rows : Array Row) (id code verdict : String) : Bool :=
  rows.any fun r => r.id == id && r.code == code && r.verdict == verdict

def selftest (repo : System.FilePath) (lualatex? : Option String) : IO UInt32 := do
  let mut fails := #[]
  let unclosed := "LaTeX Error: \\begin{itemize} on input line 3 ended by \\end{document}."
  let pure' := [
    ("log: first error, its line and opener",
      parseLog 1 ("x\n! " ++ unclosed ++ "\n\nl.7 \\end{document}\n! Later.\nl.9 x\n") ==
        { exit := 1, error := some unclosed, errLine := some 7, opener := some 3 }),
    ("log: a recovery line is read",
      (parseLog 0 "(\\end occurred inside a group at level 1)\n").recovery.isSome),
    ("log: a clean log accepts", (parseLog 0 "Output written on t.pdf\n").accepted),
    ("spurious: a named construct present", spurious "\\end{document}"
      { code := "E0201", line := 2, message := "unclosed: expected '\\end{document}'" }),
    ("spurious: a brace is never a construct", !spurious "}"
      { code := "E0201", line := 3, message := "unclosed: expected '}'" }),
    ("cache: a run round-trips", decodeT (encodeT { exit := 0, text := some "a\nb" }) ==
      some { exit := 0, text := some "a\nb" }),
    ("class map keeps every line",
      (texTwin "\\documentclass{slides}\nx").map (lines · |>.length) == some 2)]
  for (name, ok) in pure' do unless ok do fails := fails.push name
  let e ← setup repo lualatex? false
  let gone ← setup repo (some "/nonexistent") false
  let a := wrapBody "a}"
  let dir := gone.root / "run" / "u"
  let probe : Case := { id := "u", kind := "witness", code := DiagCode.E0202, lean := a, tex := a }
  let untested := judge probe (← runLeantex gone dir a) (← runTex gone dir a) none
  unless has untested "u" "E0202" "untested" do
    fails := fails.push "--lualatex /nonexistent: untested"
  if e.lualatex.isNone then
    IO.println s!"diag-oracle selftest: lualatex untested; {pure'.length + 1} checks, \
{fails.size} failures"
    return if fails.isEmpty then 0 else 1
  let wrapped := "raisebox.minipage-inline"
  let mini := mutantCases.filter fun c => c.id == "seed.minipage-inline" || c.id == wrapped
  let brace := wrapBody "{a"
  let twin (src : String) : String := (texTwin src).getD ""
  let witness (id : String) (code : DiagCode) (src : String) : Case :=
    { id, kind := "witness", code, lean := src, tex := twin src }
  let cases := mini ++ #[witness "a" .E0202 a, witness "brace" .E0201 brace,
    { id := "seed.broken", kind := "seed", lean := framed "" "a}", tex := twin (framed "" "a}") },
    { id := "broken", kind := "mutant", lean := framed "" "\\fbox{a}",
      tex := twin (framed "" "\\fbox{a}"), seed := some "seed.broken" }]
  let (rows, _) ← judgeAll e 4 cases
  let (late, _) ← judgeAll { e with budgetMs := 1 } 1 #[witness "late" .E0202 (a ++ "%late")]
  for (name, ok) in [
      ("a} is confirmed", has rows "a" "E0202" "confirmed"),
      ("the minipage mutant's W0302 is a false cause", has rows wrapped "W0302" "false-cause"),
      ("the minipage mutant's E0336 is a false cause", has rows wrapped "E0336" "false-cause"),
      ("the minipage mutant breaks transparency", has rows wrapped "-" "transparency"),
      ("{a ships in TeX", has rows "brace" "E0201" "tex-ships"),
      ("{a's E0205 is a spurious cascade", has rows "brace" "E0205" "cascade-spurious"),
      ("a broken twin confounds", has rows "broken" "-" "confounded"),
      ("a 1 ms budget is inconclusive", has late "late" "E0202" "inconclusive")] do
    unless ok do fails := fails.push name
  for f in fails do IO.eprintln s!"FAIL {f}"
  for r in rows ++ late do IO.println r.tsv
  IO.println s!"diag-oracle selftest: {pure'.length + 9} checks, {fails.size} failures"
  return if fails.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  match parse args {} with
  | .error msg => IO.eprintln s!"diag-oracle: {msg}"; return 3
  | .ok o =>
    let repo ← IO.currentDir
    if o.selftest then return ← selftest repo o.lualatex
    let e ← setup repo o.lualatex o.keep
    if e.lualatex.isNone then
      IO.println "diag-oracle: lualatex untested"
      return 0
    let failed ← premises e
    unless failed.isEmpty do
      for f in failed do IO.eprintln s!"diag-oracle premise failed: {f}"
      return 2
    let both := !o.witnesses && !o.mutants
    let fonts := (← shippedFira).getD { fonts := #[] }
    let cases := (if both || o.witnesses then witnessCases fonts o.only else #[]) ++
      (if both || o.mutants then mutantCases else #[])
    let jobs ← match o.jobs with | some j => pure j | none => defaultJobs
    IO.println s!"diag-oracle: {e.texVersion}; {cases.size} cases, {jobs} jobs"
    let (rows, emitted) ← judgeAll e jobs cases
    IO.println "id\tkind\tcode\tverdict\tleantex line\tTeX line\tTeX error or recovery\tmessage"
    for r in rows do IO.println r.tsv
    let sum := summary rows emitted
    for s in sum do IO.println s
    IO.FS.writeFile (e.root / "report.tsv")
      ("\n".intercalate ((rows.map (·.tsv)) ++ sum).toList ++ "\n")
    return 0

end DiagOracle

def main (args : List String) : IO UInt32 := DiagOracle.main args
