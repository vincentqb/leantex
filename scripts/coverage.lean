/-
Documented-command coverage: how much of LaTeX does this engine answer?

  lake env lean --run scripts/coverage.lean                  regenerate the scoreboard, then check it
  lake env lean --run scripts/coverage.lean --check [path]    check the checked-in scoreboard only
  lake env lean --run scripts/coverage.lean --selftest        the checker and the verdict rule, hand-written
  lake env lean --run scripts/coverage.lean --report          the per-item detail and the drift audit
  lake env lean --run scripts/coverage.lean --denominator <latex2e.texi> <probe.tsv>
                                                             rebuild tests/coverage/latex2e-index.txt

The number is a measurement, never a list. Every verdict comes from running
the engine's own dispatch over a probe of the command (`Elab.run`), so the
published figure cannot drift from what the engine does: a command the
dispatch stops recognising becomes `unknown` on the next run. Three
verdicts, and they are the compat-index's own vocabulary: `impl` (no
W0301/W0302 — the engine recognised it), `refuse` (recognised and a loss
named by a code), `unknown` (W0301/W0302 — nothing knows this name).

The denominator has two halves, and neither is chosen here.

*Kernel.* `tests/coverage/latex2e-index.txt`: the command names indexed by
the LaTeX2e unofficial reference manual (`@findex`, `@ftable` items, and
`@node` headings that name a command), each confirmed by lualatex to be a
control sequence LaTeX actually defines, and each classified by the meaning
lualatex gives it. Regenerating that file needs the manual and lualatex and
so is a separate mode; `--check` reads only the committed file.

*Packages.* `tests/compat-index/<pkg>.txt`, unchanged: each file is already
one package's documented command list sourced to a manual section, one row
per command with its verdict. The rows are the denominator and the `impl`
rows the numerator, so a package's coverage is data someone reviewed.

Exclusions, all stated and all derived:

  * math-mode symbol commands — the names lualatex reports as `math_given`
    (`\mathchardef`-style: `\alpha`, `\Gamma`, `\leq`). They are a font
    table, not a dispatch surface; counting them would inflate both halves
    of the fraction with the same work. This is flashtex's exclusion, taken
    for the same reason and computed rather than listed.
  * names the manual indexes that lualatex does not define under
    `article`/`book` with amsmath and amssymb — index entries for
    environments, file extensions, counters, and commands a package
    provides. A command that a package provides is counted in that
    package's half or not at all, never twice.
  * environments. The manual indexes them as `@findex <name> environment`;
    this extraction keeps `\name` tokens only, so `itemize` never enters the
    command denominator. An environment surface is the compat-index's job.

The scoreboard is `tests/scoreboard/coverage.tsv` in the autonomy loop's
one format: `#` provenance lines (data, never gated), then `item<TAB>count`
rows, sorted and unique, higher better. Items are manual chapters and
package names; the value is the `impl` count. A value that drops, or a
baselined item that disappears, is a regression.
-/
import LeanTex

open LeanTex.Core

def denomPath : String := "tests/coverage/latex2e-index.txt"
def tsvPath : String := "tests/scoreboard/coverage.tsv"
def compatDir : System.FilePath := "tests/compat-index"

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

-- ## The kernel denominator, as committed data

/-- One kernel row: the command, the manual chapter that documents it, and
the meaning lualatex gives it (the class the exclusion rule reads). -/
structure KRow where
  name : String
  chapter : String
  cls : String
deriving Inhabited, BEq

/-- Commands whose lualatex meaning is a math symbol — excluded, by the
engine's own report rather than by a list kept here. -/
def mathClass : String := "math_given"

def KRow.counted (r : KRow) : Bool := r.cls != mathClass

/-- Split on the first tab, keeping the rest whole. -/
def tabs (line : String) : Array String :=
  (line.splitOn "\t").toArray.map (·.trimAscii.toString)

def parseDenom (text : String) : Except String (Array KRow) := do
  let mut rows : Array KRow := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let f := tabs line
    if f.size != 3 then
      throw s!"denominator: want three tab-separated fields, got {f.size}: {line}"
    rows := rows.push { name := f[0]!, chapter := f[1]!, cls := f[2]! }
  if rows.isEmpty then throw "denominator: no rows"
  return rows

-- ## The verdict, measured

inductive Verdict where
  | impl
  | refuse (code : String)
  | unknown
deriving Inhabited, BEq

def Verdict.isImpl : Verdict → Bool
  | .impl => true
  | _ => false

def Verdict.tag : Verdict → String
  | .impl => "impl"
  | .refuse c => "refuse:" ++ c
  | .unknown => "unknown"

/-- The unknown-command codes: the engine saw a name nothing knows. Any
other code means the dispatch recognised the command and named what it
could not do with it. -/
def unknownCodes : List String := ["W0301", "W0302"]

/-- One probe's verdict, read from the diagnostics the engine produced.
`impl` is the absence of an unknown-command code *and* of any other loss —
so a command the engine rewrites with a note counts as implemented, and one
it refuses is separated from one it never heard of. -/
def verdictOf (ds : Array Diag) : Verdict :=
  if ds.any (fun d => unknownCodes.contains d.code) then .unknown
  else
    match ds.find? (fun d => d.severity == .warning || d.severity == .error) with
    | some d => .refuse d.code
    | none => .impl

/-- Best of two verdicts: recognised beats unknown, clean beats refused.
The probe tries a command in several argument shapes because the
denominator carries names and not signatures; taking the best is one
uniform rule, where a per-command shape table would be a hand list. -/
def Verdict.best (a b : Verdict) : Verdict :=
  match a, b with
  | .impl, _ => .impl
  | _, .impl => .impl
  | .refuse c, _ => .refuse c
  | _, .refuse c => .refuse c
  | .unknown, .unknown => .unknown

/-- The argument shapes every command is tried in, in order: no argument,
one group, two, an option and a group, and the three definer shapes whose
first argument is a control sequence rather than text (`\newcommand` and
its family read a name there, and a text group is not one). The family is
uniform — no per-command signature table — and adding a shape can only move
a name from `unknown` toward recognised, so the count cannot be inflated by
a shape that happens to fit. -/
def shapes (name : String) : Array String :=
  #["\\" ++ name,
    "\\" ++ name ++ "{x}",
    "\\" ++ name ++ "{x}{y}",
    "\\" ++ name ++ "[o]{x}",
    "\\" ++ name ++ "{\\zzprobe}",
    "\\" ++ name ++ "{\\zzprobe}{y}",
    "\\" ++ name ++ "{\\zzprobe}[1]{y}"]

/-- Both places a command can stand. LaTeX allows `\newcommand` in either,
and the engine answers the preamble spelling (a rewrite into `\define`)
while the body spelling is unknown — so probing one place only would
publish a number that depends on where the probe happened to look. -/
def wrap (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

def wrapPre (pre : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nx\n\\end{document}"

/-- Probe one command name through the engine's real dispatch, in every
shape and both places, and keep the best verdict. -/
def probe (name : String) : Verdict := Id.run do
  let mut best : Verdict := .unknown
  for src in shapes name do
    for doc in [wrap src, wrapPre src] do
      let ds := (Elab.run "coverage" doc).2
      best := Verdict.best best (verdictOf ds)
      if best.isImpl then return best
  return best

-- ## The package half, from the compat index

/-- One package's rows: its name, the number of commands it documents, and
how many of them are `impl`. `inert:` rows are recognised commands that
legitimately move no ink, so they count as implemented — the index already
carries the reason, reviewed, in the row. -/
structure PRow where
  pkg : String
  documented : Nat
  impl : Nat
deriving Inhabited, BEq

def annotationOf (line : String) : Option String :=
  let place := ((line.splitOn " ").headD "")
  let rest := (line.drop place.length).toString.trimAscii.toString
  let ann := ((rest.splitOn " ").headD "")
  if ann.isEmpty then none else some ann

def callOf (line : String) : String :=
  let place := ((line.splitOn " ").headD "")
  let rest := (line.drop place.length).toString.trimAscii.toString
  let ann := ((rest.splitOn " ").headD "")
  (rest.drop ann.length).toString.trimAscii.toString

def readPackages : IO (Array PRow) := do
  let mut rows : Array PRow := #[]
  let names := (← compatDir.readDir).map (·.fileName) |>.qsort (· < ·)
  for entry in names do
    unless entry.endsWith ".txt" do continue
    let pkg := (entry.dropEnd ".txt".length).toString
    let content ← IO.FS.readFile (compatDir / entry)
    let mut documented := 0
    let mut impl := 0
    for line in content.splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      match annotationOf line with
      | none => pure ()
      | some ann =>
        documented := documented + 1
        if ann == "impl" || ann.startsWith "inert:" then impl := impl + 1
    rows := rows.push { pkg, documented, impl }
  return rows

-- ## The scoreboard file

structure Board where
  provenance : Array String
  rows : Array (String × Nat)
deriving Inhabited

def parseBoard (text : String) : Except String Board := do
  let mut provenance : Array String := #[]
  let mut rows : Array (String × Nat) := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "#" then
      provenance := provenance.push line
      continue
    let f := tabs line
    if f.size != 2 then throw s!"scoreboard: want item<TAB>count, got: {line}"
    match f[1]!.toNat? with
    | none => throw s!"scoreboard: not an integer: {line}"
    | some n => rows := rows.push (f[0]!, n)
  if rows.isEmpty then throw "scoreboard: no rows"
  let keys := rows.map (·.1)
  let sorted := keys.qsort (· < ·)
  if keys != sorted then throw "scoreboard: rows are not sorted"
  for i in [1:keys.size] do
    if keys[i]! == keys[i - 1]! then throw s!"scoreboard: duplicate item: {keys[i]!}"
  return { provenance, rows }

def renderBoard (b : Board) : String :=
  let head := b.provenance.foldl (fun acc l => acc ++ l ++ "\n") ""
  b.rows.foldl (fun acc (k, n) => acc ++ k ++ "\t" ++ toString n ++ "\n") head

/-- The scoreboard a run computes: kernel chapters and packages, each with
its `impl` count. -/
def computeRows (kernel : Array KRow) (pkgs : Array PRow) : Array (String × Nat) := Id.run do
  let mut chapters : Array (String × Nat) := #[]
  for r in kernel do
    unless r.counted do continue
    unless (probe r.name).isImpl do continue
    let key := "kernel/" ++ r.chapter
    match chapters.findIdx? (fun p => p.1 == key) with
    | some i => chapters := chapters.set! i (key, chapters[i]!.2 + 1)
    | none => chapters := chapters.push (key, 1)
  -- Every counted chapter appears, so a chapter falling to zero is a
  -- regression and not a retirement.
  for r in kernel do
    unless r.counted do continue
    let key := "kernel/" ++ r.chapter
    unless chapters.any (fun p => p.1 == key) do chapters := chapters.push (key, 0)
  let mut out := chapters
  for p in pkgs do
    out := out.push ("pkg/" ++ p.pkg, p.impl)
  return out.qsort (fun a b => a.1 < b.1)

structure Totals where
  kImpl : Nat
  kRefuse : Nat
  kUnknown : Nat
  kExcluded : Nat
  pImpl : Nat
  pDoc : Nat
deriving Inhabited

def Totals.num (t : Totals) : Nat := t.kImpl + t.pImpl
def Totals.den (t : Totals) : Nat := t.kImpl + t.kRefuse + t.kUnknown + t.pDoc

/-- Percent with one decimal, as an integer count of tenths. -/
def tenths (num den : Nat) : Nat := if den == 0 then 0 else (num * 1000 + den / 2) / den

def totalsOf (kernel : Array KRow) (pkgs : Array PRow) : Totals := Id.run do
  let mut t : Totals := { kImpl := 0, kRefuse := 0, kUnknown := 0, kExcluded := 0,
                          pImpl := 0, pDoc := 0 }
  for r in kernel do
    if !r.counted then t := { t with kExcluded := t.kExcluded + 1 }
    else match probe r.name with
      | .impl => t := { t with kImpl := t.kImpl + 1 }
      | .refuse _ => t := { t with kRefuse := t.kRefuse + 1 }
      | .unknown => t := { t with kUnknown := t.kUnknown + 1 }
  for p in pkgs do
    t := { t with pImpl := t.pImpl + p.impl, pDoc := t.pDoc + p.documented }
  return t

def pct (num den : Nat) : String :=
  let t := tenths num den
  toString (t / 10) ++ "." ++ toString (t % 10) ++ "%"

-- ## Modes

def loadKernel : IO (Array KRow) := do
  unless (← System.FilePath.pathExists denomPath) do
    throw (IO.userError s!"coverage: {denomPath} is missing — run --denominator")
  match parseDenom (← IO.FS.readFile denomPath) with
  | .error e => throw (IO.userError ("coverage: " ++ e))
  | .ok rows => return rows

def checkFile (path : String) : IO UInt32 := do
  unless (← System.FilePath.pathExists path) do
    return (← die 3 s!"coverage: {path} is missing — regenerate it")
  let kernel ← loadKernel
  let pkgs ← readPackages
  match parseBoard (← IO.FS.readFile path) with
  | .error e => die 3 ("coverage: " ++ e)
  | .ok board => do
    let want := computeRows kernel pkgs
    let mut bad : Array String := #[]
    for (k, n) in board.rows do
      match want.find? (fun p => p.1 == k) with
      | none => bad := bad.push s!"{k}: baselined item has disappeared"
      | some (_, m) =>
        if m < n then bad := bad.push s!"{k}: {n} → {m} is a regression"
    for (k, m) in want do
      unless board.rows.any (fun p => p.1 == k) do
        bad := bad.push s!"{k}: {m} implemented, not in the baseline — regenerate"
    if bad.isEmpty then
      let t := totalsOf kernel pkgs
      IO.println s!"coverage: ok — {t.num}/{t.den} ({pct t.num t.den})"
      return 0
    else
      for b in bad do IO.eprintln ("coverage: " ++ b)
      return 1

def provenanceLines (t : Totals) : IO (Array String) := do
  let date := (← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }).stdout
  return #[
    "# documented-command coverage: the impl count per kernel chapter and per package.",
    "# kernel denominator: tests/coverage/latex2e-index.txt (its own provenance line).",
    "# package denominator: tests/compat-index/*.txt rows, unchanged.",
    s!"# kernel: {t.kImpl} impl, {t.kRefuse} refused, {t.kUnknown} unknown, \
{t.kExcluded} excluded as math-mode symbols.",
    s!"# packages: {t.pImpl} impl of {t.pDoc} documented.",
    s!"# total: {t.num}/{t.den} = {pct t.num t.den}",
    "# date: " ++ date.trimAscii.toString]

def regenerate : IO UInt32 := do
  let kernel ← loadKernel
  let pkgs ← readPackages
  let t := totalsOf kernel pkgs
  let board : Board := { provenance := ← provenanceLines t, rows := computeRows kernel pkgs }
  IO.FS.createDirAll "tests/scoreboard"
  IO.FS.writeFile tsvPath (renderBoard board)
  IO.println s!"coverage: wrote {tsvPath}"
  checkFile tsvPath

/-- The per-item detail, and the audit the number cannot show: where the
measured verdict and the compat-index's reviewed verdict disagree. A
disagreement is a finding either way — the index claims an `impl` the
dispatch no longer recognises, or it records a refusal the engine has since
implemented. -/
def report : IO UInt32 := do
  let kernel ← loadKernel
  let pkgs ← readPackages
  let t := totalsOf kernel pkgs
  IO.println s!"kernel  {t.kImpl} impl / {t.kRefuse} refuse / {t.kUnknown} unknown \
({t.kExcluded} excluded)"
  IO.println s!"package {t.pImpl} impl / {t.pDoc} documented"
  IO.println s!"total   {t.num}/{t.den} = {pct t.num t.den}"
  IO.println ""
  IO.println "-- kernel chapters, worst first (unknown, refused, impl)"
  let mut chs : Array (String × Nat × Nat × Nat) := #[]
  for r in kernel do
    unless r.counted do continue
    let v := probe r.name
    let idx := chs.findIdx? (fun c => c.1 == r.chapter)
    let (u, f, i) := match idx with
      | some j => (chs[j]!.2.1, chs[j]!.2.2.1, chs[j]!.2.2.2)
      | none => (0, 0, 0)
    let bumped := match v with
      | .unknown => (r.chapter, u + 1, f, i)
      | .refuse _ => (r.chapter, u, f + 1, i)
      | .impl => (r.chapter, u, f, i + 1)
    match idx with
    | some j => chs := chs.set! j bumped
    | none => chs := chs.push bumped
  for c in chs.qsort (fun a b => a.2.1 > b.2.1) do
    IO.println s!"  {c.2.1}\t{c.2.2.1}\t{c.2.2.2}\t{c.1}"
  IO.println ""
  IO.println "-- unknown kernel commands, by chapter"
  for c in chs.qsort (fun a b => a.1 < b.1) do
    let names := kernel.filterMap fun r =>
      if r.counted && r.chapter == c.1 && (probe r.name) == .unknown then some r.name else none
    unless names.isEmpty do
      IO.println s!"  {c.1}: {String.intercalate " " names.toList}"
  IO.println ""
  IO.println "-- compat-index disagreements (index verdict vs measured)"
  let mut disagree := 0
  for entry in (← compatDir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless entry.endsWith ".txt" do continue
    let pkg := (entry.dropEnd ".txt".length).toString
    let content ← IO.FS.readFile (compatDir / entry)
    for line in content.splitOn "\n" do
      let line := line.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      match annotationOf line with
      | none => pure ()
      | some ann =>
        let call := callOf line
        -- Only single-command rows are comparable: a row that is a whole
        -- environment or several commands has no one name to probe.
        if call.startsWith "\\" && !(call.any (· == '{')) && !(call.any (· == ' ')) then
          let name := (call.drop 1).toString
          let v := probe name
          -- The index's vocabulary and this measurement's must be lined up
          -- before a difference means anything: `refuse:W0301` *is*
          -- `unknown` (W0301 is the unknown-command code, so a row naming
          -- it agrees with an unknown measurement), and a row naming a
          -- note code records a rewrite, which is implemented. Without
          -- this, 37 rows read as disagreements and every one of them was
          -- this script's own vocabulary, not a finding.
          let want :=
            if ann == "impl" || ann.startsWith "inert:" then "impl"
            else if ann.startsWith "refuse:" then
              let code := (ann.drop "refuse:".length).toString
              if unknownCodes.contains code then "unknown"
              else if code.startsWith "N" then "impl"
              else "refuse"
            else "?"
          let got := match v with
            | .impl => "impl"
            | .refuse _ => "refuse"
            | .unknown => "unknown"
          unless want == got do
            disagree := disagree + 1
            IO.println s!"  {pkg}\t{call}\tindex:{ann}\tmeasured:{v.tag}"
  IO.println s!"-- {disagree} disagreement(s)"
  return 0

/-- Rebuild the kernel denominator from the reference manual and a lualatex
probe of every candidate name. Both inputs are external, so this mode is
never part of a gate: `--check` reads the committed file only.

The probe file is what lualatex writes for the candidate list — one row
`name<TAB>defined<TAB>meaning<TAB>index` — so the confirmation and the
classification are lualatex's answers, not ours. -/
def denominator (texi probeFile : String) : IO UInt32 := do
  let src ← IO.FS.readFile texi
  let mut chapter := "About this document"
  let mut found : Array (String × String) := #[]
  let mut inFtable := false
  for line in src.splitOn "\n" do
    if line.startsWith "@chapter " then chapter := (line.drop 9).toString.trimAscii.toString
    else if line.startsWith "@appendix " then chapter := (line.drop 10).toString.trimAscii.toString
    if line.startsWith "@ftable" then inFtable := true
    else if line.startsWith "@end ftable" then inFtable := false
    let harvest := line.startsWith "@findex" || line.startsWith "@node"
      || (inFtable && line.startsWith "@item")
    unless harvest do continue
    -- Every `\name` token on the line: a control word, or a single
    -- non-letter control symbol.
    let cs := line.toList
    let mut i := 0
    let arr := cs.toArray
    while i < arr.size do
      if arr[i]! == '\\' && i + 1 < arr.size then
        let c := arr[i + 1]!
        if c.isAlpha then
          let mut j := i + 1
          while j < arr.size && arr[j]!.isAlpha do j := j + 1
          let name := String.ofList (arr.toList.drop (i + 1) |>.take (j - i - 1))
          found := found.push (name, chapter)
          i := j
        else if !c.isWhitespace && c != '{' && c != '}' && c != '@' then
          found := found.push (String.singleton c, chapter)
          i := i + 2
        else i := i + 2
      else i := i + 1
  let probeText ← IO.FS.readFile probeFile
  let mut meaning : Array (String × String) := #[]
  for line in probeText.splitOn "\n" do
    let f := tabs line
    if f.size < 3 then continue
    if f[1]! == "true" then meaning := meaning.push (f[0]!, f[2]!)
  let mut rows : Array KRow := #[]
  for (name, ch) in found do
    if rows.any (fun r => r.name == name) then continue
    match meaning.find? (fun m => m.1 == name) with
    | none => continue
    | some (_, cls) => rows := rows.push { name, chapter := ch, cls }
  let sorted := rows.qsort (fun a b => a.name < b.name)
  let uniqueCands := found.foldl (fun (acc : Array String) (p : String × String) =>
    if acc.contains p.1 then acc else acc.push p.1) #[]
  let sha := (← IO.Process.output { cmd := "sha256sum", args := #[texi] }).stdout
  let shaField := ((sha.splitOn " ").headD "").trimAscii.toString
  let id := ((← IO.FS.readFile texi).splitOn "\n").find? (·.startsWith "@c $Id:")
  let luaVer := (← IO.Process.output { cmd := "lualatex", args := #["--version"] }).stdout
  let head :=
    "# The kernel command denominator: every command name the LaTeX2e unofficial\n\
     # reference manual indexes (@findex, @ftable items, @node headings), confirmed\n\
     # by lualatex to be a control sequence LaTeX defines, and classified by the\n\
     # meaning lualatex reports. Fields: name, manual chapter, lualatex meaning.\n\
     # A `math_given` row is a math-mode symbol command and is excluded from the\n\
     # count; it is kept here so the exclusion is visible and countable.\n\
     # Regenerate with scripts/coverage.lean --denominator; never hand-edit.\n" ++
    s!"# manual: latex2e-help-texinfo latex2e.texi, sha256 {shaField}\n" ++
    s!"# manual-id: {(id.getD "unknown").trimAscii.toString}\n" ++
    s!"# confirmed-by: {((luaVer.splitOn "\n").headD "").trimAscii.toString}\n" ++
    s!"# confirmed-under: \\documentclass\{article} and \{book}, amsmath + amssymb\n" ++
    s!"# candidates: {uniqueCands.size} indexed names, {sorted.size} confirmed defined\n"
  let body := sorted.foldl
    (fun acc r => acc ++ r.name ++ "\t" ++ r.chapter ++ "\t" ++ r.cls ++ "\n") head
  IO.FS.createDirAll "tests/coverage"
  IO.FS.writeFile denomPath body
  IO.println s!"coverage: wrote {denomPath} with {sorted.size} confirmed names \
({uniqueCands.size} indexed names in the manual)"
  return 0

-- ## Selftest

def selftest : IO UInt32 := do
  let ref ← IO.mkRef (#[] : Array String)
  let expect (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (·.push name)
  -- The verdict rule, on diagnostics the engine really produces.
  expect "a known command is impl" ((probe "textbf").isImpl)
  expect "an invented name is unknown" (probe "zzfakecommandzz" == .unknown)
  expect "best prefers impl over unknown" (Verdict.best .unknown .impl == .impl)
  expect "best prefers refuse over unknown"
    (Verdict.best .unknown (.refuse "W0399") == .refuse "W0399")
  expect "unknown only when nothing recognised" (Verdict.best .unknown .unknown == .unknown)
  -- The exclusion is read from the class, not a list.
  expect "a math symbol row is excluded"
    (!(KRow.counted { name := "alpha", chapter := "Math formulas", cls := mathClass }))
  expect "a macro row is counted"
    (KRow.counted { name := "textbf", chapter := "Fonts", cls := "call" })
  -- The scoreboard parser refuses what a hand edit produces.
  expect "unsorted rows are refused"
    ((parseBoard "b\t1\na\t2\n").toOption.isNone)
  expect "duplicate items are refused"
    ((parseBoard "a\t1\na\t2\n").toOption.isNone)
  expect "a non-integer value is refused"
    ((parseBoard "a\tmany\n").toOption.isNone)
  expect "an empty board is refused" ((parseBoard "# only provenance\n").toOption.isNone)
  expect "a good board parses"
    (match parseBoard "# p\na\t1\nb\t2\n" with
     | .ok b => b.rows == #[("a", 1), ("b", 2)] && b.provenance == #["# p"]
     | .error _ => false)
  expect "render round-trips"
    (match parseBoard (renderBoard { provenance := #["# p"], rows := #[("a", 1)] }) with
     | .ok b => b.rows == #[("a", 1)]
     | .error _ => false)
  expect "the denominator parser wants three fields"
    ((parseDenom "a\tb\n").toOption.isNone)
  expect "the denominator parser reads a row"
    (match parseDenom "# h\nx\tFonts\tcall\n" with
     | .ok rs => rs == #[{ name := "x", chapter := "Fonts", cls := "call" }]
     | .error _ => false)
  expect "tenths rounds" (tenths 1 3 == 333 && tenths 2 3 == 667 && tenths 1 2 == 500)
  expect "pct renders" (pct 605 1314 == "46.0%")
  let bad ← ref.get
  if bad.isEmpty then
    IO.println "coverage: selftest ok"
    return 0
  else
    for b in bad do IO.eprintln ("coverage: selftest failed: " ++ b)
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => regenerate
  | ["--check"] => checkFile tsvPath
  | ["--check", path] => checkFile path
  | ["--selftest"] => selftest
  | ["--report"] => report
  | ["--denominator", texi, probeFile] => denominator texi probeFile
  | _ => die 3 "usage: coverage [--check [path] | --selftest | --report | \
--denominator <latex2e.texi> <probe.tsv>]"
