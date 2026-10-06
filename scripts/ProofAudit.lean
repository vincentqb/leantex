module

public meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
meta import Lean.Util.Path

open Lean Elab Command

/-- The lexical source path also counts: a link into a fixture directory must
not hide a module that the compiler actually imported into the project. -/
meta def projectModule (root : System.FilePath) (name : Name) : IO Bool := do
  if ← (modToFilePath root name "lean").pathExists then return true
  let object := (← IO.currentDir) / (← findOLean name)
  let buildRoot := root / ".lake" / "build" / "lib" / "lean"
  if buildRoot.normalize.components.isPrefixOf object.normalize.components then return true
  if ← buildRoot.pathExists then
    let buildRoot ← IO.FS.realPath buildRoot
    return buildRoot.normalize.components.isPrefixOf (← IO.FS.realPath object).normalize.components
  return false

/-- Audit the compiled declarations of an explicit source manifest, including
private and unused declarations. The compiler loads the complete environment;
checking only exported theorem names would miss private unfinished proofs.

The batch may be smaller than the manifest because executable roots can have
conflicting names. Every imported project module must still be in that manifest.

The accepted foundation is Lean's quotient soundness, classical choice, and
propositional extensionality. Any additional assumption must be an explicit
hypothesis of a contract, with its external interpretation checked separately. -/
elab "#audit_proofs" "[" modules:str,* "]" "from" root:str
    "manifest" "[" manifest:str,* "]" : command => do
  let expected := modules.getElems.map (·.getString.toName)
  if expected.isEmpty then
    throwError "proof audit: an empty source manifest is not verification"
  let env ← getEnv
  if env.header.isModule then
    throwError "proof audit: use a legacy audit wrapper without `module`; modern imports hide private declarations"
  let root ← IO.FS.realPath root.getString
  let mut covered : NameSet := {}
  for entry in manifest.getElems do
    let name := entry.getString.toName
    if covered.contains name then
      throwError "proof audit: duplicate source manifest module {name}"
    covered := covered.insert name
  for name in env.header.moduleNames do
    if !covered.contains name && (← projectModule root name) then
      throwError "proof audit: imported project module {name} is missing from the source manifest; move hidden or linked sources into a maintained directory and register their Lake target"
  let mut seen : NameSet := {}
  let mut count : Nat := 0
  let mut failures : Nat := 0
  for name in expected do
    if seen.contains name then
      throwError "proof audit: duplicate module {name}"
    seen := seen.insert name
    unless covered.contains name do
      throwError "proof audit: batch module {name} is missing from the source manifest"
    let some idx := env.header.moduleNames.findIdx? (· == name)
      | throwError "proof audit: module {name} was not imported"
    let some data := env.header.moduleData[idx]?
      | throwError "proof audit: imported module {name} has no declaration data"
    for decl in data.constNames do
      if (env.checked.get.find? decl).isNone then
        throwError "proof audit: {name}: declaration {decl} has no kernel information"
      let axioms ← liftCoreM (collectAxioms decl)
      let unexpected := axioms.filter fun ax =>
        !#[`Quot.sound, `Classical.choice, `propext].contains ax
      if !unexpected.isEmpty then
        logError m!"proof audit: {name}: {decl} depends on {unexpected}"
        failures := failures + 1
      count := count + 1
  if failures == 0 then
    logInfo m!"proof audit: {expected.size} modules, {count} declarations checked"
