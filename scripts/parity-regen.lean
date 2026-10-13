/-
The parity ladder's regenerator, the only invoker of the reference engine: each lualatex
reference compiled to a reproducible fixed point, committed only as a verdict.
Usage: lake build ScriptsModules && lake env lean --run scripts/parity-regen.lean [--selftest | --force [fixture]]
-/
import scripts.ParityCore
import LeanTex.Cli.PicCache

open LeanTex.Core LeanTex.Cli Parity

/-- The reference engine; `-halt-on-error` is the whole build level on the reference
side. -/
def refEngine : String := "lualatex"

/-- The trailer `/ID` a reference carries: its reference source's content key, twice, 32
hex digits. -/
def trailerId (key : String) : String :=
  s!"\\pdfvariable trailerid\{[<{key}> <{key}>]}"

/-- The invocation, given the reference source's content key and the output directory;
`-jobname` names the output since the argument is no file name. -/
def refArgs (stem key outDir : String) : Array String :=
  #["-halt-on-error", "-interaction=nonstopmode", "-file-line-error", "-recorder",
    s!"-output-directory={outDir}", s!"-jobname={stem}.ref",
    trailerId key ++ s!"\\input\{{stem}.ref.tex}"]

/-- How a sidecar spells the fresh output directory. -/
def scratchName : String := "<scratch>"

def haveTool (name : String) : IO Bool := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  return out.exitCode == 0

/-- The engine's own version line, recorded. -/
def engineVersion : IO String := do
  let out ← IO.Process.output { cmd := refEngine, args := #["--version"] }
  return ((out.stdout.splitOn "\n").head?.getD "").trimAscii.toString

/-- The LaTeX format the run loaded, from the log's `LaTeX2e <date>` line. -/
def formatLine (log : String) : String :=
  (((log.splitOn "\n").find? fun l => l.startsWith "LaTeX2e <").getD "").trimAscii.toString

/-- How many overfull boxes the reference engine reported, recorded and not acted on. -/
def overfullCount (log : String) : Nat :=
  ((log.splitOn "\n").filter fun l => l.startsWith "Overfull" || l.startsWith "! Overfull").length

/-- Whether a line opens one of LaTeX's warnings: `LaTeX Warning:`, `LaTeX <kind>
Warning:`, `Package <name> Warning:` or `Class <name> Warning:`. -/
def warningHead (l : String) : Bool :=
  match l.splitOn " " with
  | "LaTeX" :: "Warning:" :: _ => true
  | "LaTeX" :: _ :: "Warning:" :: _ => true
  | "Package" :: _ :: "Warning:" :: _ => true
  | "Class" :: _ :: "Warning:" :: _ => true
  | _ => false

/-- Whether a line says "rerun" as a word, in any case, so the package name
`rerunfilecheck` is no request. -/
def mentionsRerun (l : String) : Bool := Id.run do
  let parts := (l.toLower.splitOn "rerun").toArray
  for i in [1:parts.size] do
    let before := (parts[i - 1]!.toList.getLast?).getD ' '
    let after := (parts[i]!.toList.head?).getD ' '
    if !before.isAlpha && !after.isAlpha then return true
  return false

/-- Whether the engine wants another pass: a LaTeX warning paragraph that says "rerun"; a
document that asks on every pass never settles and is refused. -/
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

/-- TeX's trailer on every halt under `-halt-on-error`. -/
def fatalTrailer : String := "==> Fatal error occurred"

/-- `<file>:<line>: <message>`, how `-file-line-error` spells an error. -/
def fileLineError (l : String) : Bool :=
  match l.splitOn ":" with
  | file :: line :: rest :: _ =>
    !file.isEmpty && !file.any Char.isWhitespace && (file.any (· == '.') || file.any (· == '/'))
      && !line.isEmpty && line.all Char.isDigit && rest.startsWith " "
  | _ => false

/-- The engine's own refusal: the first of TeX's error lines (`! <message>` or
`<file>:<line>: <message>`) other than the halt trailer, or the trailer alone; a killed
run leaves neither. -/
def refusalLine (log : String) : Option String :=
  let errs := ((log.splitOn "\n").map (·.trimAscii.toString)).filter fun l =>
    l.startsWith "!" || fileLineError l
  let isTrailer (l : String) : Bool := (l.splitOn fatalTrailer).length > 1
  match errs.find? (!isTrailer ·) with
  | some l => some l
  | none => errs.head?

/-- One reference compile read as a verdict through `PicCache.outcome`: `.refused` is a
`compiles: no` worth committing, `.inconclusive` a machine fault committed nowhere. -/
def refOutcome (code : UInt32) (drew : Bool) (log : String) : PicCache.Outcome :=
  PicCache.outcome (.exited code.toNat) drew
    (match refusalLine log with
     | some l => .says l
     | none => .absent)

/-- The prose a fixture declares about its pairing, from its `% parity:` line; a fixture
with none is not regenerated. -/
def claimOf (src : String) : Option String :=
  ((src.splitOn "\n").find? (·.startsWith "% parity: ")).map fun l =>
    (l.drop 10).trimAscii.toString

/-- The in-repo files the run read, from `-recorder`'s `.fls`: the relative `INPUT` lines,
deduplicated, the engine's litter dropped. -/
def inputsOf (fls : String) : List String :=
  ((fls.splitOn "\n").filterMap fun raw =>
    let l := raw.trimAscii.toString
    if !l.startsWith "INPUT " then none
    else
      let p := (l.drop 6).trimAscii.toString
      if p.startsWith "/" then none
      else if refLitter.any (fun e => p.endsWith e) then none
      else some p).eraseDups

/-- The shipped fonts a reference names, found by name since a warm luaotfload cache hides
them from the `.fls`. -/
def namedInputs (refSrc : String) (fontNames : List String) : List String :=
  (fontNames.filter fun f => (refSrc.splitOn f).length > 1).map
    fun f => "../corpus/fonts/" ++ f

structure Pass where
  bytes : ByteArray
  log : String
  fls : String
  exitCode : UInt32
  passes : Nat
  /-- Whether the bytes stopped moving: a reference that never settles is not one. -/
  settled : Bool
  deriving Inhabited

/-- Compile one reference to a fixed point, reading its source from `srcDir` and writing
every output to `outDir`. -/
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

/-- How many pages the reference carries, read by the engine's own reader as the gate
reads them. -/
def refPages (bytes : ByteArray) : Except String Nat :=
  (readArtifact bytes).map (·.size)

/-- Lay out under `root` what a reference reads: its source at `testdata/parity/` and the
shipped fonts where the reference names them. -/
def stage (root : System.FilePath) (stem src : String) : IO System.FilePath := do
  let dir := root / "testdata" / "parity"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / (stem ++ ".ref.tex")) src
  let fonts := root / "testdata" / "corpus" / "fonts"
  IO.FS.createDirAll fonts
  for e in ← System.FilePath.readDir testFonts do
    if e.fileName.endsWith ".ttf" || e.fileName.endsWith ".otf" then
      IO.FS.writeBinFile (fonts / e.fileName) (← IO.FS.readBinFile e.path)
  return dir

/-- One source compiled in a scratch tree and read as a verdict; a planted stale PDF shows
that a run shipping no page does not adopt it. -/
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

/-- The reference is a function of its inputs, not of where it was built: one source
compiled in two directories at different depths, byte for byte, and against the committed
bytes on the host the sidecar records. -/
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
  -- The refusal reading, on lines captured from LuaHBTeX 1.24.0 (TeX Live 2026).
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
  -- A kill leaves a log that stops mid-line with no error in it.
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
  -- The rerun reading: the kernel's and a package's requests, and two lines that are none.
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
  -- The input list: relative inputs pinned; the TeX tree, scratch and litter not.
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
  -- A sidecar whose values are empty still round trips, as the refusing fixture's does.
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
  -- Each reading against a run made now, where the tool is installed.
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
    -- A source shipping no page has no reference, whatever PDF stands beside it.
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
    -- Only a verdict reaches the tree; a refusal removes the reference a previous verdict left.
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
