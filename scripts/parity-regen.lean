/-
The parity ladder's regenerator: the only thing in this repository that
invokes the reference engine. Run from the repository root:

  lake build TestsModules
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
cross-reference or a table of contents settles on the third.

`SOURCE_DATE_EPOCH=0` and `FORCE_SOURCE_DATE=1` are set for every pass, so
the reference does not carry today's date and a regeneration that changed
nothing produces the same bytes.

A reference engine not on PATH is a fact about the machine: the script says
so and exits 0 without writing. It never records a fixture as failing to
compile on that evidence — `compiles: no` means the engine ran and refused.
-/
import scripts.ParityCore

open LeanTex.Core LeanTex.Cli Parity

/-- The reference engine and the flags it is invoked with. `-halt-on-error`
is the whole of the build rung on the reference side: a document that limps
past an error is not a reference. -/
def refEngine : String := "lualatex"

def refArgs (stem : String) : Array String :=
  #["-halt-on-error", "-interaction=nonstopmode", "-file-line-error", stem ++ ".ref.tex"]

def haveTool (name : String) : IO Bool := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  return out.exitCode == 0

/-- The engine's own version line, recorded so a reference regenerated
under a different install is visible as such. -/
def engineVersion : IO String := do
  let out ← IO.Process.output { cmd := refEngine, args := #["--version"] }
  return ((out.stdout.splitOn "\n").head?.getD "").trimAscii.toString

/-- How many overfull boxes the reference engine reported. Recorded rather
than acted on: an overfull box on the reference side is a fact about the
pairing worth seeing when a geometry rung later disagrees. -/
def overfullCount (log : String) : Nat :=
  ((log.splitOn "\n").filter fun l => l.startsWith "Overfull" || l.startsWith "! Overfull").length

/-- Does the engine want another pass? -/
def wantsRerun (log : String) : Bool :=
  (log.splitOn "Rerun").length > 1

/-- The prose the fixture declares about its own pairing, from its
`% parity:` line. A fixture with no such line has not said what its
reference is for, which is a fixture the ladder will not regenerate. -/
def claimOf (src : String) : Option String :=
  ((src.splitOn "\n").find? (·.startsWith "% parity: ")).map fun l =>
    (l.drop 10).trimAscii.toString

structure Pass where
  bytes : ByteArray
  log : String
  exitCode : UInt32
  passes : Nat
  deriving Inhabited

/-- Compile one reference to a fixed point. -/
def compileRef (stem : String) : IO Pass := do
  let mut prev : ByteArray := .empty
  let mut log := ""
  let mut code : UInt32 := 0
  let pdf := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
  for pass in [1:6] do
    let child ← IO.Process.output
      { cmd := refEngine, args := refArgs stem, cwd := some (System.FilePath.mk parityDir)
        env := #[("SOURCE_DATE_EPOCH", some "0"), ("FORCE_SOURCE_DATE", some "1")] }
    code := child.exitCode
    let logPath := System.FilePath.mk parityDir / (stem ++ ".ref.log")
    log ← if ← logPath.pathExists then IO.FS.readFile logPath else pure child.stdout
    if code != 0 then
      return { bytes := .empty, log := log, exitCode := code, passes := pass }
    let bytes ← if ← pdf.pathExists then IO.FS.readBinFile pdf else pure .empty
    if bytes == prev && !wantsRerun log then
      return { bytes := bytes, log := log, exitCode := code, passes := pass }
    prev := bytes
  return { bytes := prev, log := log, exitCode := code, passes := 5 }

/-- The side files the reference engine leaves behind. None of them is a
reference, and a committed one would be noise the ladder never reads. -/
def refLitter : List String := [".ref.aux", ".ref.log", ".ref.out", ".ref.toc", ".ref.nav", ".ref.snm"]

def sweep (stem : String) : IO Unit := do
  for ext in refLitter do
    let p := System.FilePath.mk parityDir / (stem ++ ext)
    if ← p.pathExists then IO.FS.removeFile p

/-- How many pages the reference carries, read from its bytes by the
engine's own reader — the same reading the gate performs, so the recorded
count and the judged count cannot come apart. -/
def refPages (bytes : ByteArray) : Except String Nat :=
  (readArtifact bytes).map (·.size)

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
  let s : Sidecar :=
    { fixture := "x", compiles := true, pdfKey := "abc", pdfSize := 12
      srcKey := "d", refSrcKey := "e", engine := "eng 1", argv := "a b"
      pages := 3, overfull := 0, provenance := "a claim with: a colon" }
  match Sidecar.parse s.render with
  | .error e => bad := bad.push s!"sidecar round trip: {e}"
  | .ok r =>
    unless r.fixture == s.fixture && r.compiles && r.pdfKey == s.pdfKey
        && r.pdfSize == s.pdfSize && r.pages == s.pages
        && r.provenance == s.provenance do
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
      srcKey := "a", refSrcKey := "b", engine := "eng", argv := "-x f.tex"
      pages := 0, overfull := 0, provenance := "the denominator probe" }
  match Sidecar.parse bare.render with
  | .error e => bad := bad.push s!"a sidecar with an empty value did not round trip: {e}"
  | .ok r =>
    unless r.pdfKey == "" && !r.compiles && r.pages == 0 && r.provenance == bare.provenance do
      bad := bad.push s!"sidecar with an empty value round tripped wrong: {repr r}"
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
  let mut wrote : Nat := 0
  let mut skipped : Nat := 0
  for stem in ← parityNames do
    if !only.isEmpty && !only.contains stem then continue
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    let pdfPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let had ← sidecarPath.pathExists
    if had && !force then
      skipped := skipped + 1
      continue
    let oldKey ← if ← pdfPath.pathExists then
        pure (Flate.contentKey (← IO.FS.readBinFile pdfPath))
      else pure ""
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrcPath := System.FilePath.mk parityDir / (stem ++ ".ref.tex")
    unless ← refSrcPath.pathExists do
      IO.eprintln s!"parity-regen {stem}: no reference source beside it"
      return 1
    let refSrc ← IO.FS.readFile refSrcPath
    let some claim := claimOf src
      | do IO.eprintln s!"parity-regen {stem}: the fixture declares no '% parity:' claim"
           return 1
    let r ← compileRef stem
    sweep stem
    let compiles := r.exitCode == 0 && !r.bytes.isEmpty
    let pages ← if compiles then
        match refPages r.bytes with
        | .ok n => pure n
        | .error e => do
            IO.eprintln s!"parity-regen {stem}: the reference compiled but is unreadable: {e}"
            return 1
      else pure 0
    let sidecar : Sidecar :=
      { fixture := stem, compiles := compiles
        pdfKey := if compiles then Flate.contentKey r.bytes else ""
        pdfSize := r.bytes.size
        srcKey := Flate.contentKey src.toUTF8
        refSrcKey := Flate.contentKey refSrc.toUTF8
        engine := version
        argv := String.intercalate " " ((refArgs stem).toList)
        pages := pages, overfull := overfullCount r.log
        provenance := claim }
    IO.FS.writeFile sidecarPath sidecar.render
    wrote := wrote + 1
    if compiles then
      let moved := !oldKey.isEmpty && oldKey != sidecar.pdfKey
      IO.println s!"parity-regen {stem}: {pages} pages, {r.passes} pass(es), \
{sidecar.overfull} overfull, key {sidecar.pdfKey}\
{if moved then s!" (was {oldKey} — the reference moved)" else ""}"
    else
      IO.println s!"parity-regen {stem}: the reference engine refused it (compiles: no)"
      IO.println s!"   {(((r.log.splitOn "\n").filter fun l => l.startsWith "!").head?).getD ""}"
  IO.println s!"parity-regen: {wrote} written, {skipped} left alone \
(committed references are immutable without --force)"
  return 0
