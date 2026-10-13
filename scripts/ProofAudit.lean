module

public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils
meta import Lean.Util.CollectAxioms
meta import Lean.Util.Path

open Lean Elab Command

/-- Whether a module is the project's, by its lexical source path too, so a link into a
fixture directory cannot hide one. -/
meta def projectModule (root : System.FilePath) (name : Name) : IO Bool := do
  if ← (modToFilePath root name "lean").pathExists then return true
  let object := (← IO.currentDir) / (← findOLean name)
  let buildRoot := root / ".lake" / "build" / "lib" / "lean"
  if buildRoot.normalize.components.isPrefixOf object.normalize.components then return true
  if ← buildRoot.pathExists then
    let buildRoot ← IO.FS.realPath buildRoot
    return buildRoot.normalize.components.isPrefixOf (← IO.FS.realPath object).normalize.components
  return false

meta def unexpectedAxioms (axioms : Array Name) : Array Name :=
  axioms.filter fun ax => !#[`Quot.sound, `Classical.choice, `propext].contains ax

/-- The `example` commands of a parse, not words in comments, strings or syntax
quotations. -/
meta def parsedExamples (stx : Syntax) : Array Syntax :=
  let visit (node : Syntax) : StateM (Array Syntax) (Option Syntax) := do
    if node.isQuot then return some node
    if node.isOfKind ``Parser.Command.example then
      modify (·.push node)
      return some node
    return none
  ((stx.replaceM visit).run #[]).2

/-- The kernel environment the frontend saved for an example before discarding it, one
snapshot per command. -/
meta def exampleSnapshot (ctx : ContextInfo) (tree : InfoTree) :
    IO (Option (Name × Environment)) :=
  (InfoTree.context (.commandCtx ctx.toCommandContextInfo) tree).foldInfoM
    (init := none) fun inner _ found => do
      if found.isSome then return found
      let some name := inner.parentDecl? | return none
      let .str _ "_example" := (privateToUserName name).eraseMacroScopes | return none
      unless (inner.env.checked.get.find? name).isSome do return none
      return some (name, inner.env)

/-- Audit a command's anonymous examples from their saved kernel environments, macro
expansions included; a missing snapshot is a refusal. -/
meta def auditExamples (command : Syntax) : CommandElabM Nat := do
  let path ← getFileName
  let fileMap ← getFileMap
  let mut expected := parsedExamples command
  let mut observed : Array Syntax := #[]
  let mut count := 0
  for tree in (← getInfoState).trees do
    let commands := tree.foldInfoTree (init := #[]) fun ctx node found =>
      match node with
      | .node (.ofCommandInfo info) _ =>
        found.push (ctx, node, info.stx)
      | _ => found
    for (ctx, node, command) in commands do
      expected := expected ++ parsedExamples command
      unless command.isOfKind ``Parser.Command.declaration &&
          command[1].isOfKind ``Parser.Command.example do continue
      let stx := command[1]
      observed := observed.push stx
      let pos := fileMap.toPosition (stx.getPos?.getD 0)
      let some (name, snapshot) ← exampleSnapshot ctx node
        | throwError "proof audit: {path}:{pos.line}:{pos.column}: anonymous example has no checked kernel snapshot; give it a theorem or definition name so the compiled audit can verify it"
      -- Include auxiliaries even when the resulting example never uses them.
      let decls := snapshot.constants.map₂.toList.map (·.1) |>.filter (name.isPrefixOf ·)
      unless decls.contains name do
        throwError "proof audit: {path}:{pos.line}:{pos.column}: anonymous example is missing from its kernel snapshot; give it a theorem or definition name"
      for decl in decls do
        unless (snapshot.checked.get.find? decl).isSome do
          throwError "proof audit: {path}:{pos.line}:{pos.column}: anonymous auxiliary {decl} has no kernel information"
        let (axioms, _) ← (collectAxioms decl : CoreM (Array Name)).toIO
          { fileName := path, fileMap } { env := snapshot }
        let unexpected := unexpectedAxioms axioms
        unless unexpected.isEmpty do
          throwError "proof audit: {path}:{pos.line}:{pos.column}: anonymous example {decl} depends on {unexpected}"
      count := count + 1
  for stx in expected do
    unless observed.any (·.eqWithInfo stx) do
      let pos := fileMap.toPosition (stx.getPos?.getD 0)
      throwError "proof audit: {path}:{pos.line}:{pos.column}: anonymous example was not audited before discard; give it a theorem or definition name (including examples nested in mutual or diagnostic commands)"
  return count

/-- Registered as a native compiler plugin, so the audit adds no imports to the source; a
failed audit stays failed, and only end-of-file issues a success receipt. -/
meta initialize
  discard <| registerStatefulLinter (τ := Unit) (some 0 : Option Nat)
    (post := fun stx previous _ _ _ => do
      let current ← try
          pure (some (← auditExamples stx))
        catch ex =>
          logException ex
          pure none
      let checked := previous.bind fun count => current.map (count + ·)
      if stx.isOfKind ``Parser.Command.eoi then
        match checked with
        | some count =>
          logInfo m!"proof audit: {← getFileName}: {count} anonymous examples checked before discard"
        | none =>
          logError m!"proof audit: {← getFileName}: anonymous proof audit failed"
      return checked)

/-- Audit the compiled declarations of an explicit source manifest, private and unused
ones included, against the accepted foundation: quotient soundness, classical choice and
propositional extensionality. -/
elab "#audit_proofs" "[" modules:str,* "]" "from" root:str
    "with" "[" manifest:str,* "]" : command => do
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
      let unexpected := unexpectedAxioms axioms
      if !unexpected.isEmpty then
        logError m!"proof audit: {name}: {decl} depends on {unexpected}"
        failures := failures + 1
      count := count + 1
  if failures == 0 then
    logInfo m!"proof audit: {expected.size} modules, {count} declarations checked"
