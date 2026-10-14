/- The Lean export's committed answers: `lake env lean --run scripts/leanexport.lean` asks Lean
again, through the export the engine ships, for every invented file in testdata/codedoc/lean;
`--check` holds each committed answer to the export and the file it was asked for. -/
import LeanTex

open LeanTex.Core LeanTex.Cli

def fixtureDir : String := "testdata/codedoc/lean"
def keysPath : String := "testdata/codedoc/lean/answers.tsv"

/-- The fixtures, by name, with their text and bytes. -/
def fixtures : IO (Array (String × String × ByteArray)) := do
  let mut out := #[]
  for e in ← System.FilePath.readDir fixtureDir do
    if e.fileName.endsWith ".lean" then
      let bytes ← IO.FS.readBinFile e.path
      out := out.push (e.fileName, (Encoding.readMarkdown e.path.toString bytes).text, bytes)
  return out.qsort (·.1 < ·.1)

/-- The export a fixture is asked through, and the row its answer is kept under: the export, the
file and the Lean that answered. -/
def row (name text : String) (bytes : ByteArray) (lean : String) : Option String :=
  (Code.leanImports? text).map fun imports =>
    s!"{name}\t{Flate.contentKey (LeanExport.source imports).toUTF8}\t{Flate.contentKey bytes}\t{lean}"

def answerPath (name : String) : String :=
  s!"{fixtureDir}/{(name.dropEnd ".lean".length).toString}.answer"

def check : IO UInt32 := do
  let rows := ((← IO.FS.readFile keysPath).splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
  let mut faults := #[]
  for (name, text, bytes) in ← fixtures do
    let lean := match LeanFacts.decode (← IO.FS.readFile (answerPath name)) with
      | .ok f => f.lean
      | .error _ => ""
    match row name text bytes lean with
    | none => faults := faults.push s!"{name}: a prelude file has no answer"
    | some r =>
      unless rows.contains r do
        faults := faults.push s!"{name}: its answer was not asked through this export of this file; regenerate"
      match LeanFacts.decode (← IO.FS.readFile (answerPath name)) with
      | .ok _ => pure ()
      | .error why => faults := faults.push s!"{name}: its answer does not read: {why}"
  for f in faults do IO.eprintln s!"leanexport: {f}"
  if faults.isEmpty then
    IO.println "leanexport --check: ok"
    return 0
  return 1

def regenerate : IO UInt32 := do
  let root := (← IO.currentDir).toString
  let mut rows : Array String := #[]
  for (name, text, bytes) in ← fixtures do
    let some imports := Code.leanImports? text
      | IO.eprintln s!"leanexport: {name}: a prelude file has no answer"; return 1
    let abs := s!"{root}/{fixtureDir}/{name}"
    let got ← Host.runIO (World.ToolPath.probe "lake"
      (LeanExport.callAt root abs (LeanExport.moduleOf root abs) (LeanExport.source imports) bytes))
    let some (_, ended) := got | IO.eprintln "leanexport: no `lake` on PATH"; return 1
    let result := LeanExport.resultOf ended
    match result.outcome with
    | .drawn =>
      IO.FS.writeBinFile (answerPath name) result.bytes
      let lean := match (String.fromUTF8? result.bytes).map LeanFacts.decode with
        | some (.ok f) => f.lean
        | _ => ""
      match row name text bytes lean with
      | some r => rows := rows.push r
      | none => pure ()
      IO.println s!"leanexport: {name}: answered ({result.bytes.size} bytes)"
    | .refused why | .inconclusive why =>
      IO.eprintln s!"leanexport: {name}: no answer: {why}"
      return 1
  IO.FS.writeFile keysPath ("# Each fixture's answer, as the export the engine ships asked Lean for it: \
case, export key, file key, the Lean that answered. Written only by scripts/leanexport.lean.\n" ++
    rows.foldl (fun s r => s ++ r ++ "\n") "")
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--check"] => check
  | [] => regenerate
  | _ => do IO.eprintln "usage: leanexport [--check]"; return 2
