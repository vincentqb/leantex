module

public meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Lean Elab Command

/-- Audit the compiled declarations of an explicit source manifest, including
private and unused declarations. The compiler loads the complete environment;
checking only exported theorem names would miss private unfinished proofs.

The accepted foundation is Lean's quotient soundness, classical choice, and
propositional extensionality. Any additional assumption must be an explicit
hypothesis of a contract, with its external interpretation checked separately. -/
elab "#audit_proofs" "[" modules:str,* "]" : command => do
  let expected := modules.getElems.map (·.getString.toName)
  if expected.isEmpty then
    throwError "proof audit: an empty source manifest is not verification"
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut count : Nat := 0
  let mut failures : Nat := 0
  for name in expected do
    if seen.contains name then
      throwError "proof audit: duplicate module {name}"
    seen := seen.insert name
    let some idx := env.header.moduleNames.findIdx? (· == name)
      | throwError "proof audit: module {name} was not imported"
    let some data := env.header.moduleData[idx]?
      | throwError "proof audit: imported module {name} has no declaration data"
    for decl in data.constNames do
      let axioms ← liftCoreM (collectAxioms decl)
      let unexpected := axioms.filter fun ax =>
        !#[`Quot.sound, `Classical.choice, `propext].contains ax
      if !unexpected.isEmpty then
        logError m!"proof audit: {name}: {decl} depends on {unexpected}"
        failures := failures + 1
      count := count + 1
  if failures == 0 then
    logInfo m!"proof audit: {expected.size} modules, {count} declarations checked"
