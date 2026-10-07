import scripts.ProofSources
import scripts.ProofAudit
import LeanTex.Cli.Batch

namespace ProofCheck

open ProofSources

def auditCommand (root : System.FilePath) (names manifest : Array String) : String :=
  "#audit_proofs [" ++ String.intercalate ", " (names.toList.map (reprStr ∘ importName)) ++ "] from " ++
  reprStr root.toString ++ " with [" ++
  String.intercalate ", " (manifest.toList.map (reprStr ∘ importName)) ++ "]\n"

def wrapper (root : System.FilePath) (names manifest : Array String) : String :=
  "import scripts.ProofAudit\n" ++
  String.join (names.toList.map fun name => "import " ++ importName name ++ "\n") ++
  auditCommand root names manifest

/-- Lake chooses the platform's native library name. Loading a compiler plugin
registers the linter without adding imports to the module being checked. -/
def sourcePlugin : IO System.FilePath := do
  let target := "+scripts.ProofAudit:dynlib"
  let built ← IO.Process.output { cmd := "lake", args := #["build", "--wfail", target] }
  unless built.exitCode == 0 do
    throw <| IO.userError (built.stdout ++ built.stderr)
  let queried ← IO.Process.output { cmd := "lake", args := #["query", target] }
  unless queried.exitCode == 0 do
    throw <| IO.userError (queried.stdout ++ queried.stderr)
  let path := System.FilePath.mk queried.stdout.trimAscii.toString
  unless ← path.pathExists do
    throw <| IO.userError s!"proof audit: compiler plugin was not built: {path}"
  return path

def compile (file : System.FilePath) (extra : Array String := #[])
    (search : Option System.FilePath := none) : IO IO.Process.Output := do
  let env ← match search with
    | none => pure #[]
    | some path =>
      pure #[("LEAN_PATH", some (path.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""))]
  IO.Process.output {
    cmd := "lake", args := #["env", "lean", "-E", "hasSorry"] ++ extra ++ #[file.toString], env }

def checkGroup (dir : System.FilePath) (index : Nat)
    (names manifest : Array String) : IO IO.Process.Output := do
  let file := dir / s!"Audit{index}.lean"
  IO.FS.writeFile file (wrapper (← IO.currentDir) names manifest)
  compile file

/-- A successful compiler exit is insufficient if its audit did not finish. -/
def requireSourceAudit (source : System.FilePath) (out : IO.Process.Output) :
    IO.Process.Output :=
  if out.exitCode != 0 || (out.stdout.splitOn "\n").any (fun line =>
      line.startsWith s!"proof audit: {source}: " &&
      line.endsWith " anonymous examples checked before discard") then out
  else
    { out with
      exitCode := 1
      stderr := out.stderr ++ s!"proof audit: {source}: compiler audit receipt is missing\n" }

def checkSource (plugin source : System.FilePath) (extra : Array String := #[])
    (search : Option System.FilePath := none) : IO IO.Process.Output := do
  return requireSourceAudit source (← compile source
    (#["--plugin=" ++ plugin.toString] ++ extra) search)

/-- Compiler audits read already-built dependencies and own distinct temporary
wrappers. Keep at most two compilers resident: source elaboration can be large.
The shared executor joins every started process and retains source order. -/
def auditBatch (jobs : Array α) (run : Nat → α → IO IO.Process.Output) :
    IO (Array IO.Process.Output) :=
  LeanTex.Cli.Batch.map 2 Prod.snd (fun (job, index) => run index job) jobs.zipIdx

def verify : IO UInt32 := do
  let files ← sources "."
  if files.isEmpty then
    throw <| IO.userError "proof audit: no source modules found"
  let targets := files.map fun file => "+" ++ importName (moduleName file) ++ ":olean"
  let built ← IO.Process.output { cmd := "lake", args := #["build", "--wfail"] ++ targets }
  if built.exitCode != 0 then
    IO.eprint (built.stdout ++ built.stderr)
    return built.exitCode
  let plugin ← sourcePlugin
  IO.FS.withTempDir fun dir => do
    let manifest := files.map moduleName
    let compiled ← auditBatch (groups files) fun index names =>
      checkGroup dir index names manifest
    let elaborated ← auditBatch files fun _ file => checkSource plugin file
    let mut passed := true
    for results in #[compiled, elaborated] do
      for out in results do
        if out.exitCode != 0 then
          IO.eprint (out.stdout ++ out.stderr)
          passed := false
    if passed then
      IO.println s!"proof audit: {files.size} source modules; no unfinished proofs or project axioms"
    return if passed then 0 else 1

/-- Exercise the compiler and the compiled audit independently. A suppressed
compiler warning cannot certify a proof; unused private declarations count too. -/
def selftest : IO UInt32 := IO.FS.withTempDir fun dir => do
  let plugin ← sourcePlugin
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
  let hyphenated ← probe "Hyphenated-Module"
    "module\npublic theorem hyphenatedIdentity (n : Nat) : n = n := rfl\n"
  (_, failures) ← (expect "hyphenated module fixture did not compile"
    (hyphenated.exitCode == 0)).run failures
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
  let allFixtures := #["Valid", "Hyphenated-Module", "Visible", "Hidden", "Foreign", "Foundation",
    "Bridge", "Consumer", "AxiomBridge", "AxiomConsumer", "Unimported"]
  for (label, imports, manifest, okay) in [
      ("valid compiled proof", #["Valid"], #["Valid"], true),
      ("hyphenated compiled module", #["Valid", "Hyphenated-Module"],
        #["Valid", "Hyphenated-Module"], true),
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
  -- A failed compiler is an audit result, not an exception that skips the
  -- remaining sources. Exercise real compiler jobs through the same executor.
  let batchCases := #[("Valid", true), ("Hidden", false), ("Foundation", true)]
  let batched ← auditBatch batchCases fun index (name, _) => do
    let file := dir / s!"BatchAudit{index}.lean"
    IO.FS.writeFile file (wrapper dir #[name] allFixtures)
    compile file #["-R", dir.toString] (some dir)
  (_, failures) ← (expect "parallel audits lost, reordered, or skipped compiler results"
    (batched.map (·.exitCode == 0) == batchCases.map Prod.snd)).run failures
  (_, failures) ← (expect "parallel audit hid an unused private unfinished proof"
    (batched.any fun out => out.exitCode != 0 &&
      (out.stdout ++ out.stderr).contains "sorryAx")).run failures
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
      "scripts/tool.lean", "ExtraProofs.lean", "NewLibrary/Unregistered.lean",
      "tests/Unimported.lean", "testdata/fixture.lean", ".lake/Generated.lean"] do
    IO.FS.writeFile (sourceRoot / name) ""
  let discovered ← sources sourceRoot
  (_, failures) ← (expect "source discovery omitted an unimported module"
    ((discovered.map moduleName) ==
      #["ExtraProofs", "LeanTex", "LeanTex.Unimported", "NewLibrary.Unregistered",
        "Tests.Private", "scripts.tool", "tests.Unimported"])).run failures
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
  -- Anonymous proofs have no declarations in their compiled modules. They must
  -- be checked in the frontend's saved environment before that environment goes
  -- away, independently of both hasSorry and diagnostic suppression.
  let anonymousCases := #[
    ("ordinary", "example : 1 = 1 := rfl\nexample : 2 + 2 = 4 := by decide\n",
      true, "2 anonymous examples checked before discard"),
    ("ordinary-term", "example : Nat := 3\n",
      true, "1 anonymous examples checked before discard"),
    ("identifier", "def manifest : Nat := 3\nexample : manifest = 3 := rfl\n",
      true, "1 anonymous examples checked before discard"),
    ("foundation", "noncomputable example {α : Sort u} (h : Nonempty α) : α := Classical.choice h\n",
      true, "1 anonymous examples checked before discard"),
    ("admitted", s!"set_option {warning} false\nexample : False := by admit\n",
      false, "depends on [sorryAx]"),
    ("native", "example : 1 = 1 := by native_decide\n",
      false, "native_decide"),
    ("scoped", s!"set_option {warning} false in\nexample : False := by admit\n",
      false, "depends on [sorryAx]"),
    ("repeated", s!"set_option {warning} false\nexample : True := True.intro\nexample : False := by admit\n",
      false, "depends on [sorryAx]"),
    ("macro", s!"set_option {warning} false\nmacro \"lost_proof\" : command => `(example : False := by admit)\nlost_proof\n",
      false, "depends on [sorryAx]"),
    ("quoted", "macro \"unused_proof\" : command => `(example : False := by admit)\ndef sample : String := \"example : False := by admit\"\n/- example : False := by admit -/\n",
      true, "0 anonymous examples checked before discard"),
    ("mutual", "mutual\nexample : True := True.intro\nend\n",
      false, "give it a theorem or definition name"),
    ("macro-mutual", "macro \"mutual_proof\" : command => `(mutual\nexample : True := True.intro\nend)\nmutual_proof\n",
      false, "give it a theorem or definition name"),
    ("guarded", s!"set_option {warning} false\n#guard_msgs in\nexample : False := by admit\n",
      false, "depends on [sorryAx]"),
    ("guarded-drop", s!"set_option {warning} false\n#guard_msgs (drop all) in\nexample : False := by admit\n",
      false, "anonymous proof audit failed"),
    ("guarded-missing-snapshot", "#guard_msgs (drop all) in\nmutual\nexample : True := True.intro\nend\n",
      false, "anonymous proof audit failed"),
    ("guarded-nonproof-error", "#guard_msgs (drop all) in\n#check Missing\nexample : True := True.intro\n",
      true, "1 anonymous examples checked before discard"),
    ("early-exit", "example : True := True.intro\n#exit\nexample : False := by admit\n",
      false, "compiler audit receipt is missing")]
  for modern in [false, true] do
    for (label, body, okay, diagnostic) in anonymousCases do
      let source := dir / "Anonymous.lean"
      IO.FS.writeFile source ((if modern then "module\n" else "") ++ "import Lean\n" ++ body)
      let built ← compile source #["-R", dir.toString] (some dir)
      let label := s!"{if modern then "modern" else "legacy"} anonymous {label}"
      (_, failures) ← (expect (label ++ ": mutation did not compile")
        (built.exitCode == 0)).run failures
      if built.exitCode != 0 then IO.eprint (built.stdout ++ built.stderr)
      let out ← checkSource plugin source #["-R", dir.toString] (some dir)
      (_, failures) ← (expect label
        ((out.exitCode == 0) == okay && (out.stdout ++ out.stderr).contains diagnostic)).run failures
      if (out.exitCode == 0) != okay || !(out.stdout ++ out.stderr).contains diagnostic then
        IO.eprint (out.stdout ++ out.stderr)
  -- The audit's implementation imports must not become imports of the source.
  -- In particular, an interface guard must have the same answer under audit.
  let isolated := dir / "Isolated.lean"
  IO.FS.writeFile isolated "module

/-- error: Unknown identifier `Std.HashSet` -/
#guard_msgs in
#check Std.HashSet

example (n : Nat) : n = n := rfl
"
  let built ← compile isolated #["-R", dir.toString] (some dir)
  (_, failures) ← (expect "isolated source fixture did not compile"
    (built.exitCode == 0)).run failures
  if built.exitCode != 0 then IO.eprint (built.stdout ++ built.stderr)
  (_, failures) ← (expect "a compiler run without the audit plugin was accepted"
    ((requireSourceAudit isolated built).exitCode != 0)).run failures
  let out ← checkSource plugin isolated #["-R", dir.toString] (some dir)
  (_, failures) ← (expect "auditor exposed its implementation imports to the source"
    (out.exitCode == 0 &&
      (out.stdout ++ out.stderr).contains "1 anonymous examples checked before discard")).run failures
  if out.exitCode != 0 then IO.eprint (out.stdout ++ out.stderr)
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
