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
left a log saying so with a `!` error line — the verdict/machine-fault
distinction `LeanTex.Cli.PicCache` already states as values, reused here
rather than re-decided. A kill, a failed spawn, and a nonzero exit that left
no error line are machine faults: they abort the regeneration, and nothing
is written.
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

/-- The invocation, given the reference source's content key. `-jobname` is
required because the argument is no longer a file name: with `\input` first,
the engine would name its output `texput`. -/
def refArgs (stem key : String) : Array String :=
  #["-halt-on-error", "-interaction=nonstopmode", "-file-line-error", "-recorder",
    s!"-jobname={stem}.ref", trailerId key ++ s!"\\input\{{stem}.ref.tex}"]

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

/-- Does the engine want another pass? -/
def wantsRerun (log : String) : Bool :=
  (log.splitOn "Rerun").length > 1

/-- The engine's own refusal, if it left one: the first `!` line of the
log, which is how TeX spells an error under `-file-line-error`. Its absence
is what separates a document the engine refused from a run the machine
broke — a missing package leaves `! LaTeX Error: File … not found.`, a kill
leaves nothing. -/
def refusalLine (log : String) : Option String :=
  ((log.splitOn "\n").find? fun l =>
    l.startsWith "!" || (l.splitOn ": !").length > 1).map (·.trimAscii.toString)

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
absolute path is a file of this host's TeX install, which `engine:` and
`format:` already identify; a relative one is a file of this repository,
which only a content key identifies. -/
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

/-- Compile one reference to a fixed point, in a named directory: the
directory is an argument so `--selftest` can build the same source twice
somewhere else and compare the bytes. -/
def compileRef (dir : System.FilePath) (stem key : String) : IO Pass := do
  let mut prev : ByteArray := .empty
  let mut log := ""
  let mut code : UInt32 := 0
  let pdf := dir / (stem ++ ".ref.pdf")
  let read (ext : String) : IO String := do
    let p := dir / (stem ++ ext)
    if ← p.pathExists then IO.FS.readFile p else pure ""
  for pass in [1:6] do
    let child ← IO.Process.output
      { cmd := refEngine, args := refArgs stem key, cwd := some dir
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

def sweep (dir : System.FilePath) (stem : String) : IO Unit := do
  for ext in refLitter do
    let p := dir / (stem ++ ext)
    if ← p.pathExists then IO.FS.removeFile p

/-- How many pages the reference carries, read from its bytes by the
engine's own reader — the same reading the gate performs, so the recorded
count and the judged count cannot come apart. -/
def refPages (bytes : ByteArray) : Except String Nat :=
  (readArtifact bytes).map (·.size)

/-- **The reference is a function of its inputs, not of where it was
built.** The check that says so: one source compiled in two directories at
different depths, byte for byte. Not a claim a docstring can carry — the
defect it replaces was a `byte-identical` sentence that held in exactly one
directory, because LuaTeX hashes the working directory into `/ID`. Skipped,
reported as skipped, when the engine is not installed. -/
def twoDirectoryRebuild (stem : String) : IO (Option String) := do
  unless ← haveTool refEngine do return none
  let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
  let key := srcKeyOf src
  let root : System.FilePath := ← IO.FS.createTempDir
  let mut keys : Array String := #[]
  for sub in ["a", "b/deeper/still"] do
    let dir := root / sub / "tests" / "parity"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / (stem ++ ".ref.tex")) src
    let fonts := root / sub / "tests" / "corpus" / "fonts"
    IO.FS.createDirAll fonts
    for e in ← System.FilePath.readDir testFonts do
      if e.fileName.endsWith ".ttf" || e.fileName.endsWith ".otf" then
        IO.FS.writeBinFile (fonts / e.fileName) (← IO.FS.readBinFile e.path)
    let r ← compileRef dir stem key
    unless r.settled && r.exitCode == 0 && !r.bytes.isEmpty do
      return some s!"the rebuild in {sub} did not settle (exit {r.exitCode})"
    keys := keys.push (Flate.contentKey r.bytes)
  IO.FS.removeDirAll root
  if keys[0]? == keys[1]? then return none
  return some s!"two rebuilds of {stem} differ: {keys[0]?.getD "?"} against {keys[1]?.getD "?"}"

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  unless overfullCount "Overfull \\hbox (1pt too wide)\nfoo\nOverfull \\vbox" == 2 do
    bad := bad.push "overfullCount"
  unless overfullCount "nothing here" == 0 do bad := bad.push "overfullCount zero"
  unless wantsRerun "LaTeX Warning: Label(s) may have changed. Rerun to get" do
    bad := bad.push "wantsRerun"
  unless !wantsRerun "all settled" do bad := bad.push "wantsRerun negative"
  unless claimOf "% parity: a floor probe\n\\documentclass{article}" == some "a floor probe" do
    bad := bad.push s!"claimOf: {repr (claimOf "% parity: a floor probe\n")}"
  unless claimOf "\\documentclass{article}" == none do bad := bad.push "claimOf absent"
  unless formatLine "This is LuaHBTeX\nLaTeX2e <2025-11-01>\nmore" == "LaTeX2e <2025-11-01>" do
    bad := bad.push s!"formatLine: {formatLine "LaTeX2e <2025-11-01>"}"
  unless formatLine "no format here" == "" do bad := bad.push "formatLine absent"
  unless trailerId "AB" == "\\pdfvariable trailerid{[<AB> <AB>]}" do
    bad := bad.push s!"trailerId: {trailerId "AB"}"
  unless (refArgs "prose" "AB").contains "-jobname=prose.ref" do
    bad := bad.push "refArgs names the job, or the output is texput"
  unless (refArgs "prose" "AB").contains "-recorder" do
    bad := bad.push "refArgs asks for the input list"
  -- The verdict, through the driver's own policy. Each arm broken once: the
  -- engine's refusal is committed, and every machine fault is not.
  unless refOutcome 1 false "./x.tex:3: ! LaTeX Error: File `nope.sty' not found."
      == .refused "./x.tex:3: ! LaTeX Error: File `nope.sty' not found." do
    bad := bad.push s!"refOutcome refusal: {repr (refOutcome 1 false "! nope")}"
  unless refOutcome 1 false "killed before it said anything" == .inconclusive "exit code 1" do
    bad := bad.push s!"a nonzero exit with no error line was read as a verdict: \
{repr (refOutcome 1 false "killed")}"
  unless refOutcome 0 true "fine" == .drawn do bad := bad.push "refOutcome drawn"
  unless PicCache.remembers (refOutcome 1 false "no error line here") == none do
    bad := bad.push "a machine fault would be committed"
  -- The input list: relative inputs pinned, this host's TeX tree not, the
  -- engine's own litter not.
  unless inputsOf "INPUT ./prose.ref.tex\nINPUT /usr/share/texmf/base.sty\n\
INPUT ../corpus/fonts/OpenSans-Regular.ttf\nINPUT ./prose.ref.aux\nOUTPUT ./prose.ref.pdf\n"
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
  -- And the reproducibility claim itself, measured rather than asserted.
  match ← twoDirectoryRebuild "prose" with
  | some why => bad := bad.push s!"the reference is not directory-independent: {why}"
  | none =>
    if ← haveTool refEngine then
      IO.println "parity-regen --selftest: prose rebuilt identically in two directories"
    else
      IO.println s!"parity-regen --selftest: {refEngine} not installed — \
the two-directory rebuild was skipped, not passed"
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
    let r ← compileRef dir stem refSrcKey
    let outcome := refOutcome r.exitCode (!r.bytes.isEmpty) r.log
    let fls := r.fls
    sweep dir stem
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
    for p in (inputsOf fls ++ namedInputs refSrc fontNames).eraseDups do
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
        argv := String.intercalate " " ((refArgs stem refSrcKey).toList)
        inputs := String.intercalate " " pinned.toList
        pages := pages, overfull := overfullCount r.log
        provenance := claim }
    IO.FS.writeFile sidecarPath sidecar.render
    wrote := wrote + 1
    if compiles then
      let moved := !oldKey.isEmpty && oldKey != sidecar.pdfKey
      IO.println s!"parity-regen {stem}: {pages} pages, {r.passes} pass(es), \
{sidecar.overfull} overfull, {pinned.size} input(s) pinned, key {sidecar.pdfKey}\
{if moved then s!" (was {oldKey} — the reference moved)" else ""}"
    else
      IO.println s!"parity-regen {stem}: the reference engine refused it (compiles: no)"
      match outcome with
      | .refused says => IO.println s!"   {says}"
      | _ => pure ()
  IO.println s!"parity-regen: {wrote} written, {skipped} left alone \
(committed references are immutable without --force)"
  return 0
