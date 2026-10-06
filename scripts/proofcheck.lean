import Lean

namespace ProofCheck

/-- Hidden build metadata and fixture bytes are not maintained Lean modules.
Every other source directory is discovered, including newly added libraries. -/
def sourcePath (parts : List String) : Bool :=
  parts.all (!·.startsWith ".") &&
    parts.head? != some "tests" && parts.head? != some "testdata"

/-- Source files, not umbrella imports or a fixed library list, define the
verification boundary. Unregistered modules consequently fail their Lake build.
Do not follow links outside the source tree. -/
def sources (root : System.FilePath) : IO (Array System.FilePath) := do
  let root ← IO.FS.realPath root
  let relative := fun (path : System.FilePath) =>
    path.normalize.components.drop root.normalize.components.length
  let paths ← root.walkDir fun path => do
    return (← path.symlinkMetadata).type == .dir && sourcePath (relative path)
  let mut found := #[]
  for path in paths do
    let parts := relative path
    if sourcePath parts && path.extension == some "lean" &&
        parts != ["lakefile.lean"] then
      unless (← path.symlinkMetadata).type == .file do
        throw <| IO.userError s!"proof audit: source is not a regular file: {path}"
      found := found.push ⟨String.intercalate "/" parts⟩
  return found.qsort (fun a b => a.toString < b.toString)

def moduleName (file : System.FilePath) : String :=
  (file.withExtension "").toString.replace "/" "."

def importName (name : String) : String :=
  String.intercalate "." ((name.splitOn ".").map fun part => "«" ++ part ++ "»")

def wrapper (names : Array String) : String :=
  "import scripts.ProofAudit\n" ++
  String.join (names.toList.map fun name => "import " ++ importName name ++ "\n") ++
  "#audit_proofs [" ++ String.intercalate ", " (names.toList.map reprStr) ++ "]\n"

def compile (file : System.FilePath) (extra : Array String := #[])
    (search : Option System.FilePath := none) : IO IO.Process.Output := do
  let env ← match search with
    | none => pure #[]
    | some path =>
      pure #[("LEAN_PATH", some (path.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""))]
  IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-E", "hasSorry"] ++ extra ++ #[file.toString], env }

def checkGroup (dir : System.FilePath) (index : Nat) (names : Array String) : IO Bool := do
  let file := dir / s!"Audit{index}.lean"
  IO.FS.writeFile file (wrapper names)
  let out ← compile file
  if out.exitCode != 0 then
    IO.eprint (out.stdout ++ out.stderr)
    return false
  return true

/-- Scripts and executable roots can declare the same global `main`; audit
them in separate compiler environments. Library modules share one environment. -/
def groups (files : Array System.FilePath) : Array (Array String) := Id.run do
  let mut library := #[]
  let mut isolated := #[]
  for file in files do
    let name := moduleName file
    if name.startsWith "LeanTex." || name.startsWith "Tests." || name == "LeanTex" then
      library := library.push name
    else
      isolated := isolated.push #[name]
  return #[library] ++ isolated

def verify : IO UInt32 := do
  let files ← sources "."
  if files.isEmpty then
    throw <| IO.userError "proof audit: no source modules found"
  let targets := files.map fun file => "+" ++ importName (moduleName file) ++ ":olean"
  let built ← IO.Process.output { cmd := "lake", args := #["build", "--wfail"] ++ targets }
  if built.exitCode != 0 then
    IO.eprint (built.stdout ++ built.stderr)
    return built.exitCode
  IO.FS.withTempDir fun dir => do
    let mut passed := true
    for batch in (groups files).zipIdx do
      if !(← checkGroup dir batch.2 batch.1) then passed := false
    if passed then
      IO.println s!"proof audit: {files.size} source modules; no unfinished proofs or project axioms"
    return if passed then 0 else 1

/-- Exercise the compiler and the compiled audit independently. A suppressed
compiler warning cannot certify a proof; unused private declarations count too. -/
def selftest : IO UInt32 := IO.FS.withTempDir fun dir => do
  let mut failures : Array String := #[]
  let expect (label : String) (okay : Bool) : StateT (Array String) IO Unit :=
    unless okay do modify (·.push label)
  let probe (name body : String) : IO IO.Process.Output := do
    let file := dir / (name ++ ".lean")
    IO.FS.writeFile file body
    compile file #["-R", dir.toString, "-o", (dir / (name ++ ".olean")).toString] (some dir)
  let hole := "sor" ++ "ry"
  let valid ← probe "Valid" "module\npublic theorem identity (n : Nat) : n = n := rfl\n"
  (_, failures) ← (expect "valid proof rejected by the compiler" (valid.exitCode == 0)).run failures
  let visible ← probe "Visible" s!"module\npublic theorem hole : False := by {hole}\n"
  (_, failures) ← (expect "hasSorry did not reject an unfinished proof"
    (visible.exitCode != 0 &&
      (visible.stdout ++ visible.stderr).contains ("declaration uses `" ++ hole ++ "`"))).run failures
  let warning := "warn." ++ hole
  let hidden ← probe "Hidden"
    s!"module\nset_option {warning} false\nprivate theorem unused : False := by {hole}\n"
  (_, failures) ← (expect "hidden-proof mutation did not compile" (hidden.exitCode == 0)).run failures
  let foreign ← probe "Foreign" "module\nprivate axiom invented : False\n"
  (_, failures) ← (expect "unexpected-axiom mutation did not compile" (foreign.exitCode == 0)).run failures
  let foundation ← probe "Foundation" "module
public theorem byChoice {α : Sort u} (h : Nonempty α) : Nonempty α :=
  ⟨Classical.choice h⟩
public theorem byPropext (p q : Prop) (h : p ↔ q) : p = q := propext h
public theorem byQuotient {α : Sort u} {r : α → α → Prop} {a b : α}
    (h : r a b) : Quot.mk r a = Quot.mk r b := Quot.sound h
"
  (_, failures) ← (expect "foundation fixture did not compile"
    (foundation.exitCode == 0)).run failures
  let bridge ← probe "Bridge" s!"module
set_option {warning} false
private theorem hidden : False := by {hole}
public theorem exported : False := hidden
"
  (_, failures) ← (expect "transitive-hole fixture did not compile"
    (bridge.exitCode == 0)).run failures
  let consumer ← probe "Consumer" "module
import Bridge
public theorem dependent : False := exported
"
  (_, failures) ← (expect "transitive-hole consumer did not compile"
    (consumer.exitCode == 0)).run failures
  let axiomBridge ← probe "AxiomBridge" "module
private axiom inventedBoundary : False
public theorem exportedBoundary : False := inventedBoundary
"
  (_, failures) ← (expect "transitive-axiom fixture did not compile"
    (axiomBridge.exitCode == 0)).run failures
  let axiomConsumer ← probe "AxiomConsumer" "module
import AxiomBridge
public theorem dependentBoundary : False := exportedBoundary
"
  (_, failures) ← (expect "transitive-axiom consumer did not compile"
    (axiomConsumer.exitCode == 0)).run failures
  for (label, imports, manifest, okay) in [
      ("valid compiled proof", #["Valid"], #["Valid"], true),
      ("accepted logical foundation", #["Foundation"], #["Foundation"], true),
      ("unused private unfinished proof", #["Hidden"], #["Hidden"], false),
      ("unused private project axiom", #["Foreign"], #["Foreign"], false),
      ("transitive unfinished proof", #["Consumer"], #["Consumer"], false),
      ("transitive project axiom", #["AxiomConsumer"], #["AxiomConsumer"], false),
      ("empty manifest", #["Valid"], #[], false),
      ("duplicate manifest", #["Valid"], #["Valid", "Valid"], false),
      ("missing module", #["Valid"], #["Unimported"], false)] do
    let file := dir / "Audit.lean"
    let source := "import scripts.ProofAudit\n" ++
      String.join (imports.toList.map fun name => "import " ++ importName name ++ "\n") ++
      "#audit_proofs [" ++ String.intercalate ", " (manifest.toList.map reprStr) ++ "]\n"
    IO.FS.writeFile file source
    let out ← compile file #["-R", dir.toString] (some dir)
    (_, failures) ← (expect label ((out.exitCode == 0) == okay)).run failures
    if (out.exitCode == 0) != okay then IO.eprint (out.stdout ++ out.stderr)
  let sourceRoot := dir / "discovery"
  for name in ["LeanTex", "Tests", "scripts", "NewLibrary", "tests", "testdata", ".lake"] do
    IO.FS.createDirAll (sourceRoot / name)
  for name in ["LeanTex.lean", "LeanTex/Unimported.lean", "Tests/Private.lean",
      "scripts/tool.lean", "Obligations.lean", "NewLibrary/Unregistered.lean",
      "tests/fixture.lean", "testdata/fixture.lean", ".lake/Generated.lean"] do
    IO.FS.writeFile (sourceRoot / name) ""
  let discovered ← sources sourceRoot
  (_, failures) ← (expect "source discovery omitted an unimported module"
    ((discovered.map moduleName) ==
      #["LeanTex", "LeanTex.Unimported", "NewLibrary.Unregistered",
        "Obligations", "Tests.Private", "scripts.tool"])).run failures
  let regrouped := (groups discovered).foldl (· ++ ·) #[]
  (_, failures) ← (expect "audit grouping lost or duplicated a source"
    (regrouped.size == discovered.size &&
      (discovered.map moduleName).all regrouped.contains)).run failures
  let fromRelative ← sources "."
  let fromAbsolute ← sources (← IO.currentDir)
  (_, failures) ← (expect "relative source root changes module names"
    (fromRelative == fromAbsolute &&
      fromRelative.all (fun file => !(moduleName file).isEmpty))).run failures
  for failure in failures do IO.eprintln ("proof audit selftest: " ++ failure)
  if failures.isEmpty then IO.println "proof audit selftest: all passed"
  return if failures.isEmpty then 0 else 1

end ProofCheck

def main (args : List String) : IO UInt32 :=
  if args == ["--selftest"] then ProofCheck.selftest
  else if args.isEmpty || args == ["--check"] then ProofCheck.verify
  else do
    IO.eprintln "usage: proofcheck [--check | --selftest]"
    return 2
