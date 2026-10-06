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

def auditCommand (root : System.FilePath) (names manifest : Array String) : String :=
  "#audit_proofs [" ++ String.intercalate ", " (names.toList.map reprStr) ++ "] from " ++
  reprStr root.toString ++ " manifest [" ++
  String.intercalate ", " (manifest.toList.map reprStr) ++ "]\n"

def wrapper (root : System.FilePath) (names manifest : Array String) : String :=
  "import scripts.ProofAudit\n" ++
  String.join (names.toList.map fun name => "import " ++ importName name ++ "\n") ++
  auditCommand root names manifest

def compile (file : System.FilePath) (extra : Array String := #[])
    (search : Option System.FilePath := none) : IO IO.Process.Output := do
  let env ← match search with
    | none => pure #[]
    | some path =>
      pure #[("LEAN_PATH", some (path.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""))]
  IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-E", "hasSorry"] ++ extra ++ #[file.toString], env }

def checkGroup (dir : System.FilePath) (index : Nat)
    (names manifest : Array String) : IO Bool := do
  let file := dir / s!"Audit{index}.lean"
  IO.FS.writeFile file (wrapper (← IO.currentDir) names manifest)
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
      if !(← checkGroup dir batch.2 batch.1 (files.map moduleName)) then passed := false
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
  let allFixtures := #["Valid", "Visible", "Hidden", "Foreign", "Foundation",
    "Bridge", "Consumer", "AxiomBridge", "AxiomConsumer", "Unimported"]
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
      auditCommand dir manifest allFixtures
    IO.FS.writeFile file source
    let out ← compile file #["-R", dir.toString] (some dir)
    (_, failures) ← (expect label ((out.exitCode == 0) == okay)).run failures
    if (out.exitCode == 0) != okay then IO.eprint (out.stdout ++ out.stderr)
  let modernAudit := dir / "ModernAudit.lean"
  IO.FS.writeFile modernAudit ("module\n" ++ wrapper dir #["Hidden"] allFixtures)
  let modernOut ← compile modernAudit #["-R", dir.toString] (some dir)
  (_, failures) ← (expect "modern audit wrapper can hide private declarations"
    (modernOut.exitCode != 0 &&
      (modernOut.stdout ++ modernOut.stderr).contains "legacy audit wrapper")).run failures
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
  -- An imported module omitted by discovery still belongs to this project.
  -- Nothing in the root refers to these declarations: reachability is not enough.
  for layout in ["hidden", "linked"] do
    for (kind, body) in [
        ("valid", "public theorem unused : True := True.intro\n"),
        ("private-hole", s!"set_option {warning} false\nprivate theorem unused : False := by admit\n"),
        ("public-hole", s!"set_option {warning} false\npublic theorem unused : False := by admit\n"),
        ("private-axiom", "private axiom invented : False\n")] do
      let root := dir / (layout ++ "-" ++ kind)
      let src := root / "src"
      let lib := root / "lib"
      IO.FS.createDirAll (src / "Project")
      IO.FS.createDirAll (src / "testdata")
      let (hiddenPath, hiddenName) ← if layout == "hidden" then do
          IO.FS.createDirAll (src / "Project" / ".hidden")
          pure ("Project/.hidden/Hidden", "Project.«.hidden».Hidden")
        else do
          let linked ← IO.Process.output {
            cmd := "ln", args := #["-s", "../testdata", (src / "Project" / "Linked").toString] }
          unless linked.exitCode == 0 do throw <| IO.userError linked.stderr
          pure ("Project/Linked/Hidden", "Project.Linked.Hidden")
      let hiddenFile := src / (hiddenPath ++ ".lean")
      let hiddenObject := lib / (hiddenPath ++ ".olean")
      IO.FS.createDirAll hiddenObject.parent.get!
      IO.FS.writeFile hiddenFile ("module\n" ++ body)
      IO.FS.writeFile (src / "Project.lean")
        s!"module\nimport {hiddenName}\npublic theorem retained : True := True.intro\n"
      let hiddenBuild ← compile hiddenFile
        #["-R", src.toString, "-o", hiddenObject.toString] (some lib)
      let rootBuild ← compile (src / "Project.lean")
        #["-R", src.toString, "-o", (lib / "Project.olean").toString] (some lib)
      let discovered ← sources src
      let label := layout ++ " " ++ kind
      (_, failures) ← (expect (label ++ ": mutation did not compile")
        (hiddenBuild.exitCode == 0 && rootBuild.exitCode == 0)).run failures
      (_, failures) ← (expect (label ++ ": discovery fixture changed")
        (discovered.map moduleName == #["Project"])).run failures
      let audit := root / "Audit.lean"
      IO.FS.writeFile audit (wrapper src (discovered.map moduleName) (discovered.map moduleName))
      let out ← compile audit #["-R", root.toString] (some lib)
      (_, failures) ← (expect (label ++ ": omitted imported module escaped")
        (out.exitCode != 0 &&
          (out.stdout ++ out.stderr).contains "is missing from the source manifest")).run failures
      -- The same import is legal once discovery accounts for it. Its proof
      -- obligations are then checked in its own batch, including private ones.
      if layout == "linked" then
        let complete := #["Project", hiddenName]
        IO.FS.writeFile audit (wrapper src #["Project"] complete)
        let rootOut ← compile audit #["-R", root.toString] (some lib)
        (_, failures) ← (expect (label ++ ": a covered dependency was rejected")
          (rootOut.exitCode == 0)).run failures
        IO.FS.writeFile audit (wrapper src #[hiddenName] complete)
        let leafOut ← compile audit #["-R", root.toString] (some lib)
        (_, failures) ← (expect (label ++ ": the dependency's own batch missed its proof")
          ((leafOut.exitCode == 0) == (kind == "valid"))).run failures
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
