/-
The parity ladder's regenerator: the only thing in this repository that
invokes the reference engine. Run from the repository root:

  lake build ParityLib
  lake env lean --run scripts/parity-regen.lean --selftest
  lake env lean --run scripts/parity-regen.lean            # only missing ones
  lake env lean --run scripts/parity-regen.lean --force     # all of them
  lake env lean --run scripts/parity-regen.lean --force prose

A committed reference is byte-immutable by default: a fixture that already
has one is skipped, so a run of this script cannot quietly move the thing
the ladder measures against. `--force` regenerates and reports the delta —
the old content key against the new, and the page count either way — so a
reference that moved says so in the output that moved it.

Each reference is compiled repeatedly until the bytes stop changing *and*
the engine stops asking for a rerun. Two passes are not always enough; a
cross-reference or a table of contents settles on the third. A reference
still moving after the last pass is not a reference: it is refused, because
a fixed point nobody reached is a byte string the next rebuild will not
reproduce.

The engine reads the reference source where it stands and writes every
output into a fresh scratch directory (`-output-directory`), and a result is
copied into the tree only once it is a verdict. So nothing is written on an
abort, the engine's side files never touch `tests/parity`, and a source that
ships no page cannot pass off the PDF a previous run left beside it.

The reference is a function of its inputs and nothing else. Three things
make that true, and the two-directory check in `--selftest` is what says so:

* `SOURCE_DATE_EPOCH=0` and `FORCE_SOURCE_DATE=1`, so the file does not
  carry today's date;
* a **content-derived trailer `/ID`**, injected on the command line rather
  than written into the source. LuaTeX's default `/ID` is
  MD5(timestamp ‖ cwd ‖ output name), so the same inputs built in another
  directory differ in 60 bytes and every committed reference carries a
  fingerprint of the directory that produced it. `\pdfvariable trailerid`
  replaces it with the reference source's own content key. It goes on the
  command line because a key of a file cannot be written inside that file;
  the invocation is recorded in the sidecar's `argv`, so it is as visible as
  a line in the source would be;
* `-recorder`, whose `.fls` lists every file the engine read. Each in-repo
  input is pinned in the sidecar by content key — the shipped font included,
  which nothing pinned before, so a font update could leave the engine on a
  new face and the reference on an old one with no stale report.

A reference engine not on PATH is a fact about the machine: the script says
so and exits 0 without writing. It never records a fixture as failing to
compile on that evidence. `compiles: no` means the engine ran, refused, and
left a log saying so in one of TeX's own error spellings — the
verdict/machine-fault distinction `LeanTex.Cli.PicCache` already states as
values, reused here rather than re-decided. A kill, a failed spawn, and a
nonzero exit that left no error line are machine faults: they abort the
regeneration, and nothing is written.
-/
import scripts.ParityCore
import LeanTex.Cli.PicCache

open LeanTex.Core LeanTex.Cli Parity

/-- The reference engine. `-halt-on-error` is the whole of the build level
on the reference side: a document that limps past an error is not a
reference. -/
def refEngine : String := "lualatex"

/-- The trailer `/ID` a reference carries: its own reference source's
content key, twice (the original and the updated identifier of a file that
has never been updated). 32 hex digits, which is the size PDF asks for. -/
def trailerId (key : String) : String :=
  s!"\\pdfvariable trailerid\{[<{key}> <{key}>]}"

/-- The invocation, given the reference source's content key and the
directory the outputs go to. `-jobname` is required because the argument is
no longer a file name: with `\input` first, the engine would name its output
`texput`. -/
def refArgs (stem key outDir : String) : Array String :=
  #["-halt-on-error", "-interaction=nonstopmode", "-file-line-error", "-recorder",
    s!"-output-directory={outDir}", s!"-jobname={stem}.ref",
    trailerId key ++ s!"\\input\{{stem}.ref.tex}"]

/-- How a sidecar spells the output directory: a fresh one every run, so
its name is not part of the invocation anybody could reproduce. -/
def scratchName : String := "<scratch>"

def haveTool (name : String) : IO Bool := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  return out.exitCode == 0

/-- The engine's own version line, recorded so a reference regenerated
under a different install is visible as such. -/
def engineVersion : IO String := do
  let out ← IO.Process.output { cmd := refEngine, args := #["--version"] }
  return ((out.stdout.splitOn "\n").head?.getD "").trimAscii.toString

/-- The LaTeX format the run loaded, from the log's own `LaTeX2e <date>`
line. The binary's version says nothing about it: the same `lualatex` with a
newer format lays out differently, and `engine:` alone would call that the
same reference. -/
def formatLine (log : String) : String :=
  (((log.splitOn "\n").find? fun l => l.startsWith "LaTeX2e <").getD "").trimAscii.toString

/-- How many overfull boxes the reference engine reported. Recorded rather
than acted on: an overfull box on the reference side is a fact about the
pairing worth seeing when a geometry level later disagrees. -/
def overfullCount (log : String) : Nat :=
  ((log.splitOn "\n").filter fun l => l.startsWith "Overfull" || l.startsWith "! Overfull").length

/-- Does this line open one of LaTeX's warnings? The kernel's warning macros
write exactly these heads: `LaTeX Warning:`, `LaTeX <kind> Warning:`,
`Package <name> Warning:`, `Class <name> Warning:`. A package's version
banner (`Package: <name> <date> …`) is not one, which is the whole of the
difference between rerunfilecheck saying who it is and asking for a pass. -/
def warningHead (l : String) : Bool :=
  match l.splitOn " " with
  | "LaTeX" :: "Warning:" :: _ => true
  | "LaTeX" :: _ :: "Warning:" :: _ => true
  | "Package" :: _ :: "Warning:" :: _ => true
  | "Class" :: _ :: "Warning:" :: _ => true
  | _ => false

/-- Does this line say "rerun" as a word, in any case? A word, because the
package that most often asks is named `rerunfilecheck`, and its name is not
a request. -/
def mentionsRerun (l : String) : Bool := Id.run do
  let parts := (l.toLower.splitOn "rerun").toArray
  for i in [1:parts.size] do
    let before := (parts[i - 1]!.toList.getLast?).getD ' '
    let after := (parts[i]!.toList.head?).getD ' '
    if !before.isAlpha && !after.isAlpha then return true
  return false

/-- Does the engine want another pass? Asked of LaTeX's warnings, which are
where a rerun is requested: every warning is its own paragraph, a blank line
before and after, with a package's continuation lines prefixed by its name.
A warning paragraph that says "rerun" is a request.

Fails closed: a document whose warnings say "rerun" on every pass never
settles, and a reference that never settles is refused — which is the right
answer about a document whose engine keeps asking for another pass. -/
def wantsRerun (log : String) : Bool := Id.run do
  let mut inWarning := false
  for raw in log.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then
      inWarning := false
      continue
    if warningHead l then inWarning := true
    if inWarning && mentionsRerun l then return true
  return false

/-- TeX's trailer on every halt. Under `-halt-on-error` each refusal ends in
it, whatever spelling the error itself took. -/
def fatalTrailer : String := "==> Fatal error occurred"

/-- `<file>:<line>: <message>`: how `-file-line-error` spells an error. The
file part is a path (it holds a `.` or a `/` and no space), the line part is
digits, and the message follows a space. -/
def fileLineError (l : String) : Bool :=
  match l.splitOn ":" with
  | file :: line :: rest :: _ =>
    !file.isEmpty && !file.any Char.isWhitespace && (file.any (· == '.') || file.any (· == '/'))
      && !line.isEmpty && line.all Char.isDigit && rest.startsWith " "
  | _ => false

/-- The engine's own refusal, if it left one: the first of TeX's error lines
in the log that is not the halt trailer, or the trailer when it is the only
one. Two spellings count, both of them TeX's, captured from real runs under
this file's argv: the classic `! <message>` (a missing file and an
`Emergency stop` keep it) and `-file-line-error`'s `<file>:<line>:
<message>` (an undefined command, a missing `$`, `\PackageError`,
`\ClassError`, `\errmessage`). Its absence is what separates a document the
engine refused from a run the machine broke: a kill leaves a log that stops
mid-line and says neither. -/
def refusalLine (log : String) : Option String :=
  let errs := ((log.splitOn "\n").map (·.trimAscii.toString)).filter fun l =>
    l.startsWith "!" || fileLineError l
  let isTrailer (l : String) : Bool := (l.splitOn fatalTrailer).length > 1
  match errs.find? (!isTrailer ·) with
  | some l => some l
  | none => errs.head?

/-- One reference compile read as a verdict, through the cached-external-
answer policy the driver already states: the engine's exit, whether a PDF
landed, and whether it left an error line. `.refused` is a `compiles: no`
worth committing; `.inconclusive` is a machine fault and is committed
nowhere. -/
def refOutcome (code : UInt32) (drew : Bool) (log : String) : PicCache.Outcome :=
  PicCache.outcome (.exited code.toNat) drew
    (match refusalLine log with
     | some l => .says l
     | none => .absent)

/-- The prose the fixture declares about its own pairing, from its
`% parity:` line. A fixture with no such line has not said what its
reference is for, which is a fixture the ladder will not regenerate. -/
def claimOf (src : String) : Option String :=
  ((src.splitOn "\n").find? (·.startsWith "% parity: ")).map fun l =>
    (l.drop 10).trimAscii.toString

/-- The in-repo files the run read, from `-recorder`'s `.fls`: the relative
`INPUT` lines, deduplicated, with the engine's own litter dropped. An
absolute path is a file of this host's TeX install (or of the scratch
output directory), which `engine:` and `format:` already identify; a
relative one is a file of this repository, which only a content key
identifies. -/
def inputsOf (fls : String) : List String :=
  ((fls.splitOn "\n").filterMap fun raw =>
    let l := raw.trimAscii.toString
    if !l.startsWith "INPUT " then none
    else
      let p := (l.drop 6).trimAscii.toString
      if p.startsWith "/" then none
      else if refLitter.any (fun e => p.endsWith e) then none
      else some p).eraseDups

/-- The in-repo files a reference *names*, which `-recorder` alone does not
pin.

Measured 2026-09-25: with a cold luaotfload cache the `.fls` lists
`../corpus/fonts/OpenSans-Regular.ttf`; with a warm one it lists
`…/luatex-cache/generic/fonts/otl/opensans-regular.luc` under this host's
TeX tree, and the shipped face — the file *both* engines read, and the one
whose drift would move the reference and not the engine — goes unpinned.
So the `.fls` is not a stable answer to "which of this repository's files
did this run read", and the shipped fonts are found by name instead. -/
def namedInputs (refSrc : String) (fontNames : List String) : List String :=
  (fontNames.filter fun f => (refSrc.splitOn f).length > 1).map
    fun f => "../corpus/fonts/" ++ f

structure Pass where
  bytes : ByteArray
  log : String
  fls : String
  exitCode : UInt32
  passes : Nat
  /-- Did the bytes stop moving? A reference that never settles is not one. -/
  settled : Bool
  deriving Inhabited

/-- Compile one reference to a fixed point: the source read from `srcDir`,
every output written to `outDir`. Both are arguments so `--selftest` can
build the same source somewhere else and compare the bytes. -/
def compileRef (srcDir outDir : System.FilePath) (stem key : String) : IO Pass := do
  let mut prev : ByteArray := .empty
  let mut log := ""
  let mut code : UInt32 := 0
  let pdf := outDir / (stem ++ ".ref.pdf")
  let read (ext : String) : IO String := do
    let p := outDir / (stem ++ ext)
    if ← p.pathExists then IO.FS.readFile p else pure ""
  for pass in [1:6] do
    let child ← IO.Process.output
      { cmd := refEngine, args := refArgs stem key outDir.toString, cwd := some srcDir
        env := #[("SOURCE_DATE_EPOCH", some "0"), ("FORCE_SOURCE_DATE", some "1")] }
    code := child.exitCode
    let logText ← read ".ref.log"
    log := if logText.isEmpty then child.stdout else logText
    if code != 0 then
      return { bytes := .empty, log := log, fls := ← read ".ref.fls"
               exitCode := code, passes := pass, settled := true }
    let bytes ← if ← pdf.pathExists then IO.FS.readBinFile pdf else pure .empty
    if bytes == prev && !wantsRerun log then
      return { bytes := bytes, log := log, fls := ← read ".ref.fls"
               exitCode := code, passes := pass, settled := true }
    prev := bytes
  return { bytes := prev, log := log, fls := ← read ".ref.fls"
           exitCode := code, passes := 5, settled := false }

/-- How many pages the reference carries, read from its bytes by the
engine's own reader — the same reading the gate performs, so the recorded
count and the judged count cannot come apart. -/
def refPages (bytes : ByteArray) : Except String Nat :=
  (readArtifact bytes).map (·.size)

/-- Lay out, under `root`, what a reference reads: its source at
`tests/parity/`, and the shipped fonts at the relative path a reference
names them by. Returns the source directory. -/
def stage (root : System.FilePath) (stem src : String) : IO System.FilePath := do
  let dir := root / "tests" / "parity"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / (stem ++ ".ref.tex")) src
  let fonts := root / "tests" / "corpus" / "fonts"
  IO.FS.createDirAll fonts
  for e in ← System.FilePath.readDir testFonts do
    if e.fileName.endsWith ".ttf" || e.fileName.endsWith ".otf" then
      IO.FS.writeBinFile (fonts / e.fileName) (← IO.FS.readBinFile e.path)
  return dir

/-- One source compiled in a scratch tree, and read as a verdict. A PDF of
`stale` bytes is planted beside the source first when given, so a run that
ships no page is seen not to adopt it. -/
def buildScratch (stem src : String) (stale : Option ByteArray := none) :
    IO (Pass × PicCache.Outcome) := do
  let root ← IO.FS.createTempDir
  try
    let dir ← stage root stem src
    if let some b := stale then IO.FS.writeBinFile (dir / (stem ++ ".ref.pdf")) b
    let out := root / "out"
    IO.FS.createDirAll out
    let r ← compileRef dir out stem (srcKeyOf src)
    return (r, refOutcome r.exitCode (!r.bytes.isEmpty) r.log)
  finally
    IO.FS.removeDirAll root

/-- **The reference is a function of its inputs, not of where it was
built.** The check that says so: one source compiled in two directories at
different depths, byte for byte — and, when this host is the one the
sidecar records (the same `engine:` and `format:`), against the committed
bytes too. Not a claim a docstring can carry — the defect it replaces was a
`byte-identical` sentence that held in exactly one directory, because LuaTeX
hashes the working directory into `/ID`. `.ok` says which comparisons were
made. -/
def twoDirectoryRebuild (stem : String) : IO (Except String String) := do
  let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
  let key := srcKeyOf src
  let root : System.FilePath := ← IO.FS.createTempDir
  try
    let mut keys : Array String := #[]
    let mut format := ""
    for sub in ["a", "b/deeper/still"] do
      let dir ← stage (root / sub) stem src
      let out := root / sub / "out"
      IO.FS.createDirAll out
      let r ← compileRef dir out stem key
      unless r.settled && r.exitCode == 0 && !r.bytes.isEmpty do
        return .error s!"the rebuild in {sub} did not settle (exit {r.exitCode})"
      keys := keys.push (Flate.contentKey r.bytes)
      format := formatLine r.log
    unless keys[0]? == keys[1]? do
      return .error s!"two rebuilds of {stem} differ: {keys[0]?.getD "?"} against {keys[1]?.getD "?"}"
    let side ← match Sidecar.parse (← IO.FS.readFile
        (System.FilePath.mk parityDir / (stem ++ ".ref.txt"))) with
      | .ok s => pure s
      | .error e => return .error s!"the committed sidecar of {stem} is unreadable: {e}"
    let engine ← engineVersion
    unless side.engine == engine && side.format == format do
      return .ok s!"{stem} rebuilt identically in two directories; not compared with the \
committed bytes, which another install built ({side.engine}, {side.format})"
    unless keys[0]? == some side.pdfKey do
      return .error s!"a rebuild of {stem} is not the committed reference: \
{keys[0]?.getD "?"} against {side.pdfKey}"
    return .ok s!"{stem} rebuilt identically in two directories, and matches the committed bytes"
  finally
    IO.FS.removeDirAll root

/-- A `.tex` source that `\input`s nothing and ships the one construct. -/
def oneConstruct (preamble body : String) : String :=
  s!"\\documentclass\{article}\n{preamble}\n\\begin\{document}\n{body}\n\\end\{document}\n"

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  unless overfullCount "Overfull \\hbox (1pt too wide)\nfoo\nOverfull \\vbox" == 2 do
    bad := bad.push "overfullCount"
  unless overfullCount "nothing here" == 0 do bad := bad.push "overfullCount zero"
  unless claimOf "% parity: a floor probe\n\\documentclass{article}" == some "a floor probe" do
    bad := bad.push s!"claimOf: {repr (claimOf "% parity: a floor probe\n")}"
  unless claimOf "\\documentclass{article}" == none do bad := bad.push "claimOf absent"
  unless formatLine "This is LuaHBTeX\nLaTeX2e <2025-11-01>\nmore" == "LaTeX2e <2025-11-01>" do
    bad := bad.push s!"formatLine: {formatLine "LaTeX2e <2025-11-01>"}"
  unless formatLine "no format here" == "" do bad := bad.push "formatLine absent"
  unless trailerId "AB" == "\\pdfvariable trailerid{[<AB> <AB>]}" do
    bad := bad.push s!"trailerId: {trailerId "AB"}"
  unless (refArgs "prose" "AB" "/o").contains "-jobname=prose.ref" do
    bad := bad.push "refArgs names the job, or the output is texput"
  unless (refArgs "prose" "AB" "/o").contains "-recorder" do
    bad := bad.push "refArgs asks for the input list"
  unless (refArgs "prose" "AB" "/o").contains "-output-directory=/o" do
    bad := bad.push "refArgs writes its outputs where it is told"
  -- The refusal reading, on lines captured verbatim from lualatex (LuaHBTeX
  -- 1.24.0, TeX Live 2026) under this file's own argv, one construct per
  -- document: each error line with the halt trailer that run ended on.
  let trailerAt (f : String) : String :=
    s!"./{f}.ref.tex:4:  ==> Fatal error occurred, no output PDF file produced!"
  let captured : List (String × String × String) :=
    [("an undefined command", "./undefcs.ref.tex:4: Undefined control sequence.", trailerAt "undefcs"),
     ("a missing $", "./missingdollar.ref.tex:4: Missing $ inserted.", trailerAt "missingdollar"),
     ("\\PackageError", "./pkgerror.ref.tex:4: Package demo Error: a package refuses.",
      trailerAt "pkgerror"),
     ("\\ClassError", "./classerror.ref.tex:4: Class demo Error: a class refuses.",
      trailerAt "classerror"),
     ("\\errmessage", "./errmessage.ref.tex:4: a plain refusal.", trailerAt "errmessage"),
     ("a missing package",
      "! LaTeX Error: File `a-package-that-does-not-exist-anywhere.sty' not found.",
      "./missingpkg.ref.tex:3:  ==> Fatal error occurred, no output PDF file produced!"),
     ("no \\end{document}", "! Emergency stop.",
      "!  ==> Fatal error occurred, no output PDF file produced!")]
  for (what, errLine, trailer) in captured do
    let log := s!"This is LuaHBTeX, Version 1.24.0\nLaTeX Font Info:    ... okay on input line 3.\n\
{errLine}\nl.4 ...\n\nHere is how much of LuaTeX's memory you used:\n{trailer}\n"
    unless refOutcome 1 false log == .refused errLine do
      bad := bad.push s!"a refusal ({what}) read as {repr (refOutcome 1 false log)}"
    unless refOutcome 1 false s!"This is LuaHBTeX\n{trailer}\n" == .refused trailer do
      bad := bad.push s!"a halt trailer alone ({what}) was not read as a refusal"
  -- A kill leaves a log that stops mid-line, with no error in it (captured:
  -- a run killed after three seconds, exit 137).
  let killed := "LaTeX Font Info:    ... okay on input line 3.\n\
LaTeX Font Info:    Checking defaults for T1/cmr/m/n on input line 3.\n\
LaTeX Font Info:    ... okay on input line 3.\nLaTeX Font Info:    Checking defa"
  unless refOutcome 137 false killed == .inconclusive "exit code 137" do
    bad := bad.push s!"a killed run was read as a verdict: {repr (refOutcome 137 false killed)}"
  unless PicCache.remembers (refOutcome 137 false killed) == none do
    bad := bad.push "a machine fault would be committed"
  unless refOutcome 0 true "fine" == .drawn do bad := bad.push "refOutcome drawn"
  unless refOutcome 0 false "warning  (pdf backend): no pages of output." ==
      .refused "no PDF was produced" do
    bad := bad.push "a run that shipped no page was not read as producing no reference"
  unless !fileLineError "LaTeX Font Info:    ... okay on input line 3." do
    bad := bad.push "an info line read as an error"
  unless !fileLineError "Package: rerunfilecheck 2025-06-21 v1.11 Rerun checks" do
    bad := bad.push "a package banner read as an error"
  -- The rerun reading, on captured lines: the kernel's request, a package's
  -- request on its continuation line, and the two lines that must not read
  -- as one — rerunfilecheck's banner, and its all-clear on a settled pass.
  let kernelRerun :=
    "\nLaTeX Warning: Label(s) may have changed. Rerun to get cross-references right.\n\n"
  let outlines := "\nPackage rerunfilecheck Warning: File `hyper.ref.out' has changed.\n\
(rerunfilecheck)                Rerun to get outlines right\n\
(rerunfilecheck)                or use package `bookmark'.\n\n"
  let banner := "(/texmf-dist/tex/latex/rerunfilecheck/rerunfilecheck.sty\n\
Package: rerunfilecheck 2025-06-21 v1.11 Rerun checks for auxiliary files (HO)\n"
  let settledPass := "\nPackage rerunfilecheck Info: File `hyper.ref.out' has not changed.\n\
(rerunfilecheck)             Checksum: D41D8CD98F00B204E9800998ECF8427E;0.\n"
  unless wantsRerun kernelRerun do bad := bad.push "the kernel's rerun request was missed"
  unless wantsRerun outlines do bad := bad.push "a package's rerun request was missed"
  unless !wantsRerun banner do bad := bad.push "rerunfilecheck's banner read as a rerun request"
  unless !wantsRerun (banner ++ settledPass) do
    bad := bad.push "a settled hyperref pass read as asking for another"
  unless !wantsRerun ("\nLaTeX Warning: There were undefined references.\n\n" ++ banner) do
    bad := bad.push "a warning paragraph ran on past its blank line"
  unless !wantsRerun "\nPackage rerunfilecheck Warning: a warning about something else.\n\n" do
    bad := bad.push "a package named rerun-something read as asking for a rerun"
  unless wantsRerun "\nPackage biblatex Warning: Please (re)run Biber on the file:\n\
(biblatex)                bibl.ref\n(biblatex)                and rerun LaTeX afterwards.\n\n" do
    bad := bad.push "a lower-case rerun request on a continuation line was missed"
  -- The input list: relative inputs pinned, this host's TeX tree and the
  -- scratch output directory not, the engine's own litter not.
  unless inputsOf "INPUT ./prose.ref.tex\nINPUT /usr/share/texmf/base.sty\n\
INPUT ../corpus/fonts/OpenSans-Regular.ttf\nINPUT ./prose.ref.aux\nINPUT /tmp/x/prose.ref.aux\n\
OUTPUT ./prose.ref.pdf\n"
      == ["./prose.ref.tex", "../corpus/fonts/OpenSans-Regular.ttf"] do
    bad := bad.push s!"inputsOf: {repr (inputsOf "INPUT ./prose.ref.tex\n")}"
  unless namedInputs "\\setmainfont{OpenSans-Regular.ttf}[Path=../corpus/fonts/]"
      ["OpenSans-Regular.ttf", "FiraMath-Regular.otf"]
      == ["../corpus/fonts/OpenSans-Regular.ttf"] do
    bad := bad.push s!"namedInputs: {repr (namedInputs "OpenSans-Regular.ttf" ["OpenSans-Regular.ttf"])}"
  unless namedInputs "\\documentclass{article}" ["OpenSans-Regular.ttf"] == [] do
    bad := bad.push "namedInputs pinned a font nothing names"
  let s : Sidecar :=
    { fixture := "x", compiles := true, pdfKey := "abc", pdfSize := 12
      srcKey := "d", srcBodyKey := "d2", refSrcKey := "e", engine := "eng 1"
      format := "LaTeX2e <2025-11-01>"
      argv := "a b", inputs := "./x.ref.tex=1 ../corpus/fonts/f.ttf=2"
      pages := 3, overfull := 0, provenance := "a claim with: a colon" }
  match Sidecar.parse s.render with
  | .error e => bad := bad.push s!"sidecar round trip: {e}"
  | .ok r =>
    unless r.fixture == s.fixture && r.compiles && r.pdfKey == s.pdfKey
        && r.pdfSize == s.pdfSize && r.pages == s.pages && r.format == s.format
        && r.inputs == s.inputs && r.provenance == s.provenance do
      bad := bad.push s!"sidecar round trip differs: {repr r}"
  match Sidecar.parse "fixture: x\n" with
  | .error _ => pure ()
  | .ok _ => bad := bad.push "a sidecar missing every other line parsed"
  -- A sidecar whose values are empty must still round trip. It is not a
  -- hypothetical: the fixture whose reference refuses to compile has no
  -- artifact, so its `pdf-key` is empty, and a renderer that writes
  -- "pdf-key: " against a parser that trims the line then demands the space
  -- produces a sidecar nothing can read. The draft did exactly that, and the
  -- denominator probe is what found it.
  let bare : Sidecar :=
    { fixture := "refuses", compiles := false, pdfKey := "", pdfSize := 0
      srcKey := "a", srcBodyKey := "a2", refSrcKey := "b", engine := "eng", format := ""
      argv := "-x f.tex"
      inputs := "", pages := 0, overfull := 0, provenance := "the denominator probe" }
  match Sidecar.parse bare.render with
  | .error e => bad := bad.push s!"a sidecar with an empty value did not round trip: {e}"
  | .ok r =>
    unless r.pdfKey == "" && !r.compiles && r.pages == 0 && r.provenance == bare.provenance do
      bad := bad.push s!"sidecar with an empty value round tripped wrong: {repr r}"
  -- Then the tool itself, when it is installed: each reading above against a
  -- run made now, so a TeX that changes how it spells an error or a rerun
  -- fails here rather than in a regeneration.
  if ← haveTool refEngine then
    let (r, o) ← buildScratch "undefcs" (oneConstruct "" "Text. \\undefinedcommandnobodydefined")
    unless o == .refused "./undefcs.ref.tex:4: Undefined control sequence." do
      bad := bad.push s!"live: an undefined command read as {repr o} (exit {r.exitCode})"
    let (r, o) ← buildScratch "hyper" (oneConstruct "\\usepackage{hyperref}" "Text.")
    unless o == .drawn && r.settled do
      bad := bad.push s!"live: a hyperref document did not settle ({r.passes} passes, {repr o})"
    let (r, o) ← buildScratch "labels" (oneConstruct "" "\\section{One}\\label{s}See~\\ref{s}.")
    unless o == .drawn && r.settled && 2 ≤ r.passes do
      bad := bad.push s!"live: a cross-reference did not settle on a later pass \
({r.passes} passes, {repr o})"
    -- A source that ships no page, compiled beside the PDF a previous run
    -- left: the verdict is that there is no reference, never the old bytes.
    let (r, o) ← buildScratch "nopage" (oneConstruct "" "") (some "%PDF-stale".toUTF8)
    unless o == .refused "no PDF was produced" && r.bytes.isEmpty do
      bad := bad.push s!"live: a source that ships no page read as {repr o}"
    match ← twoDirectoryRebuild "prose" with
    | .error why => bad := bad.push s!"the reference is not directory-independent: {why}"
    | .ok what => IO.println s!"parity-regen --selftest: {what}"
  else
    IO.println s!"parity-regen --selftest: {refEngine} not installed — \
the live checks and the two-directory rebuild were skipped, not passed"
  if bad.isEmpty then
    IO.println "parity-regen --selftest: all passed"
    return 0
  for b in bad do IO.eprintln s!"FAIL {b}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  unless ← haveTool refEngine do
    IO.println s!"parity-regen: {refEngine} not on PATH — nothing regenerated (never a failure)"
    return 0
  let force := args.contains "--force"
  let only := args.filter fun a => !a.startsWith "--"
  let version ← engineVersion
  let dir := System.FilePath.mk parityDir
  let mut wrote : Nat := 0
  let mut skipped : Nat := 0
  for stem in ← parityNames do
    if !only.isEmpty && !only.contains stem then continue
    let sidecarPath := dir / (stem ++ ".ref.txt")
    let pdfPath := dir / (stem ++ ".ref.pdf")
    let had ← sidecarPath.pathExists
    if had && !force then
      skipped := skipped + 1
      continue
    let oldKey ← if ← pdfPath.pathExists then
        pure (Flate.contentKey (← IO.FS.readBinFile pdfPath))
      else pure ""
    let src ← IO.FS.readFile (dir / (stem ++ ".tex"))
    let refSrcPath := dir / (stem ++ ".ref.tex")
    unless ← refSrcPath.pathExists do
      IO.eprintln s!"parity-regen {stem}: no reference source beside it"
      return 1
    let refSrc ← IO.FS.readFile refSrcPath
    let some claim := claimOf src
      | do IO.eprintln s!"parity-regen {stem}: the fixture declares no '% parity:' claim"
           return 1
    let refSrcKey := srcKeyOf refSrc
    let out ← IO.FS.createTempDir
    let r ← try compileRef dir out stem refSrcKey finally IO.FS.removeDirAll out
    let outcome := refOutcome r.exitCode (!r.bytes.isEmpty) r.log
    match outcome with
    | .inconclusive says =>
      IO.eprintln s!"parity-regen {stem}: the attempt reached no verdict — {says}"
      IO.eprintln "  Nothing is written: a machine fault must not be committed as a refusal."
      return 1
    | _ => pure ()
    unless r.settled do
      IO.eprintln s!"parity-regen {stem}: the reference was still moving after {r.passes} passes"
      IO.eprintln "  Nothing is written: a byte string nobody reached a fixed point for is not a reference."
      return 1
    let compiles := outcome == .drawn
    let pages ← if compiles then
        match refPages r.bytes with
        | .ok n => pure n
        | .error e => do
            IO.eprintln s!"parity-regen {stem}: the reference compiled but is unreadable: {e}"
            return 1
      else pure 0
    let mut pinned : Array String := #[]
    let mut fontNames : List String := []
    for e in ← System.FilePath.readDir testFonts do
      if e.fileName.endsWith ".ttf" || e.fileName.endsWith ".otf" then
        fontNames := fontNames ++ [e.fileName]
    for p in (inputsOf r.fls ++ namedInputs refSrc fontNames).eraseDups do
      let path := dir / p
      if ← path.pathExists then
        pinned := pinned.push s!"{p}={Flate.contentKey (← IO.FS.readBinFile path)}"
    let sidecar : Sidecar :=
      { fixture := stem, compiles := compiles
        pdfKey := if compiles then Flate.contentKey r.bytes else ""
        pdfSize := r.bytes.size
        srcKey := srcKeyOf src
        srcBodyKey := srcBodyKeyOf src
        refSrcKey := refSrcKey
        engine := version
        format := formatLine r.log
        argv := String.intercalate " " ((refArgs stem refSrcKey scratchName).toList)
        inputs := String.intercalate " " pinned.toList
        pages := pages, overfull := overfullCount r.log
        provenance := claim }
    -- The verdict is in; only now does anything reach the tree. A refusal
    -- removes the reference a previous verdict left, since this source no
    -- longer produces one.
    if compiles then IO.FS.writeBinFile pdfPath r.bytes
    else if ← pdfPath.pathExists then IO.FS.removeFile pdfPath
    IO.FS.writeFile sidecarPath sidecar.render
    wrote := wrote + 1
    if compiles then
      let moved := !oldKey.isEmpty && oldKey != sidecar.pdfKey
      IO.println s!"parity-regen {stem}: {pages} pages, {r.passes} pass(es), \
{sidecar.overfull} overfull, {pinned.size} input(s) pinned, key {sidecar.pdfKey}\
{if moved then s!" (was {oldKey} — the reference moved)" else ""}"
    else
      IO.println s!"parity-regen {stem}: the reference engine refused it (compiles: no)\
{if oldKey.isEmpty then "" else s!" — the reference it had ({oldKey}) is removed"}"
      match outcome with
      | .refused says => IO.println s!"   {says}"
      | _ => pure ()
  IO.println s!"parity-regen: {wrote} written, {skipped} left alone \
(committed references are immutable without --force)"
  return 0
