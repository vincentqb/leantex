/- The exporter's oracle: runs `lake exe leantex-export` in a scratch project requiring export/ on
each invented file in testdata/codedoc/lean; `--selftest` holds the committed facts to what it writes
and leantex's reader to every layout's, and `--check` holds them to their sources, running no Lean. -/
import LeanTex

open LeanTex.Core LeanTex.Cli

def fixtureDir : String := "testdata/codedoc/lean"
def keysPath : String := "testdata/codedoc/lean/answers.tsv"

/-- The exporter's sources, whose content key a facts file's row names. -/
def exporterFiles : List String :=
  ["export/LeantexExport/Program.lean", "export/LeantexExport/Header.lean", "export/Main.lean"]

def exporterKey : IO String := do
  let mut text := ""
  for f in exporterFiles do text := text ++ (← IO.FS.readFile f) ++ "\u0000"
  return Flate.contentKey text.toUTF8

/-- The fixtures, by name, with their bytes. -/
def fixtures : IO (Array (String × ByteArray)) := do
  let mut out := #[]
  for e in ← System.FilePath.readDir fixtureDir do
    if e.fileName.endsWith ".lean" then out := out.push (e.fileName, ← IO.FS.readBinFile e.path)
  return out.qsort (·.1 < ·.1)

def stem (name : String) : String := (name.dropEnd ".lean".length).toString

def factsPath (name : String) : String := s!"{fixtureDir}/{stem name}.facts"

def moduleOf (name : String) : String := ".".intercalate ((s!"{fixtureDir}/{stem name}").splitOn "/")

/-- The row a fixture's facts are kept under: the exporter, the file and the Lean that answered. -/
def row (key name : String) (bytes : ByteArray) (lean : String) : String :=
  s!"{name}\t{key}\t{Flate.contentKey bytes}\t{lean}"

/-- A scratch project requiring the exporter in export/, holding every fixture. -/
def scratch (dir : System.FilePath) : IO (Array (String × ByteArray)) := do
  let repo ← IO.FS.realPath (← IO.currentDir)
  IO.FS.writeFile (dir / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
  IO.FS.writeFile (dir / "lakefile.toml") ("name = \"oracle\"\n\n[[require]]\n" ++
    s!"name = \"leantex-export\"\npath = \"{repo / "export"}\"\n")
  IO.FS.createDirAll (dir / fixtureDir)
  let fs ← fixtures
  for (name, bytes) in fs do IO.FS.writeBinFile (dir / fixtureDir / name) bytes
  return fs

/-- The exporter run in a scratch project on `args`, as from a shell outside any Lake
environment, or why it failed. -/
def exportIn (dir : System.FilePath) (args : Array String) : IO (Except String Unit) := do
  let ran ← IO.Process.output {
    cmd := "lake", args := #["exe", "leantex-export"] ++ args, cwd := dir
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
  if ran.exitCode != 0 then
    return .error s!"lake exe leantex-export exited with {ran.exitCode}\n{ran.stdout}{ran.stderr}"
  return .ok ()

/-- Every fixture's facts as the exporter writes them now, in a scratch project requiring it. -/
def runExporter : IO (Except String (Array (String × ByteArray))) :=
  IO.FS.withTempDir fun dir => do
    let fs ← scratch dir
    match ← exportIn dir (fs.map (moduleOf ·.1)) with
    | .error why => return .error why
    | .ok () =>
      let mut out := #[]
      for (name, _) in fs do
        out := out.push (name, ← IO.FS.readBinFile
          (dir / ".lake/build/leantex" / s!"{fixtureDir}/{stem name}.facts"))
      return .ok out

/-- Whether leantex's own reader finds a file's facts where the exporter wrote them, lined up. -/
def readBack (file : System.FilePath) : IO (Option LeanFacts.Facts) := do
  let text := (Encoding.readMarkdown file.toString (← IO.FS.readBinFile file)).text
  let (facts, ds, _) ← Host.runIO (LeanFactsFile.factsFor file.toString text none)
  return if ds.isEmpty then facts else none

/-- A fact file's records with its module named nowhere, to compare two exports of one text. -/
def unnamed (f : LeanFacts.Facts) : LeanFacts.Facts :=
  { f with decls := f.decls.map fun d => { d with moduleName := "" } }

/-- The layouts leantex must find an export in: a fixture with CRLF line ends, a module named
`Main` beside the exporter's own, and a nested package's file, each read back through leantex. -/
def layouts : IO (Array String) :=
  IO.FS.withTempDir fun dir => do
    let fs ← scratch dir
    let mut faults := #[]
    let some (name, bytes) := fs[0]? | return #["no fixture"]
    let lf := (String.fromUTF8? bytes).getD ""
    IO.FS.writeFile (dir / fixtureDir / "crlfCopy.lean") (lf.replace "\n" "\r\n")
    IO.FS.writeFile (dir / "Main.lean") "theorem main_true : True := trivial\n"
    IO.FS.createDirAll (dir / "sub/Sub")
    IO.FS.writeFile (dir / "sub/lakefile.toml") "name = \"sub\"\n"
    IO.FS.writeFile (dir / "sub/Sub/Thing.lean") "theorem thing : 1 = 1 := rfl\n"
    let args := #[moduleOf name, s!"{fixtureDir}/crlfCopy.lean", "Main", "sub/Sub/Thing.lean"]
    if let .error why ← exportIn dir args then return #[why]
    let real ← IO.FS.realPath dir
    let original ← readBack (real / fixtureDir / name)
    match original, ← readBack (real / fixtureDir / "crlfCopy.lean") with
    | some a, some b =>
      unless unnamed a == unnamed b do
        faults := faults.push "a CRLF copy's facts differ from its LF original's"
    | _, _ => faults := faults.push "a fixture or its CRLF copy has no facts leantex reads lined up"
    match ← readBack (real / "Main.lean") with
    | some f =>
      unless f.decls.map (·.name) == #["main_true"] && f.decls.all (·.moduleName == "Main") do
        faults := faults.push "the module Main exported another file than the project's"
    | none => faults := faults.push "the project's Main has no facts leantex reads lined up"
    if (← readBack (real / "sub/Sub/Thing.lean")).isNone then
      faults := faults.push "a nested package's file has no facts where leantex reads them"
    return faults

def check : IO UInt32 := do
  let key ← exporterKey
  let rows := ((← IO.FS.readFile keysPath).splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  let mut faults := #[]
  for (name, bytes) in ← fixtures do
    match LeanFacts.decode (← IO.FS.readFile (factsPath name)) with
    | .ok f =>
      unless rows.contains (row key name bytes f.lean) do
        faults := faults.push s!"{name}: its facts were not written by this exporter of this file; regenerate"
      unless LeanFacts.alignedWith f ((String.fromUTF8? bytes).getD "") do
        faults := faults.push s!"{name}: its facts no longer line up with it; regenerate"
    | .error why => faults := faults.push s!"{name}: its facts do not read: {why}"
  for f in faults do IO.eprintln s!"leanexport: {f}"
  if faults.isEmpty then
    IO.println "leanexport --check: ok"
    return 0
  return 1

def regenerate : IO UInt32 := do
  let key ← exporterKey
  match ← runExporter with
  | .error why => IO.eprintln s!"leanexport: {why}"; return 1
  | .ok written =>
    let mut rows : Array String := #[]
    for (name, facts) in written do
      IO.FS.writeBinFile (factsPath name) facts
      let lean := match (String.fromUTF8? facts).map LeanFacts.decode with
        | some (.ok f) => f.lean
        | _ => ""
      rows := rows.push (row key name (← IO.FS.readBinFile s!"{fixtureDir}/{name}") lean)
      IO.println s!"leanexport: {name}: {facts.size} bytes of facts"
    IO.FS.writeFile keysPath ("# Each fixture's facts, as the exporter in export/ wrote them: case, \
exporter key, file key, the Lean that answered. Written only by scripts/leanexport.lean.\n" ++
      rows.foldl (fun s r => s ++ r ++ "\n") "")
    return 0

def selftest : IO UInt32 := do
  match ← runExporter with
  | .error why => IO.eprintln s!"leanexport --selftest: {why}"; return 1
  | .ok written =>
    let mut status : UInt32 := 0
    for (name, facts) in written do
      if facts != (← IO.FS.readBinFile (factsPath name)) then
        IO.eprintln s!"leanexport --selftest: {name}: the exporter writes other facts than the committed ones"
        status := 1
    for fault in ← layouts do
      IO.eprintln s!"leanexport --selftest: {fault}"
      status := 1
    if status == 0 then
      IO.println s!"leanexport --selftest: {written.size} facts files as committed, and every layout read back"
    return status

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--check"] => check
  | ["--selftest"] => selftest
  | [] => regenerate
  | _ => do IO.eprintln "usage: leanexport [--check | --selftest]"; return 2
