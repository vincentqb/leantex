module

public import Lean

namespace CiteEnv

open Lean

public section

structure Site where
  moduleName : String
  file : String
  line : Nat
  ns : Name
  subject : String
  text : String
  deriving FromJson, ToJson

structure Query where
  moduleName : String
  ns : Name
  token : String
  deriving BEq, Hashable, FromJson, ToJson

inductive Verdict where
  | scope
  | tree
  | phantom
  deriving BEq, Inhabited, FromJson, ToJson, Repr

structure Request where
  modules : Array String
  paths : Array String
  collect : Bool := false
  queries : Array Query := #[]
  deriving FromJson, ToJson

structure Response where
  modules : Array String
  sites : Array Site := #[]
  verdicts : Array Verdict := #[]
  deriving FromJson, ToJson

def moduleFile (name : String) : String := name.replace "." "/" ++ ".lean"

/-- Inventory paths contain raw module components, including dashed script
names. Construct those components directly; String.toName parses identifiers
and rejects these names unless each component is quoted. -/
def toModuleName (name : String) : Name :=
  (name.splitOn ".").foldl Name.str .anonymous

def requireCompiled (modules : Array String) : IO Unit := do
  for name in modules do
    let compiled ← try
      (← findOLean (toModuleName name)).pathExists
    catch _ => pure false
    unless compiled do
      let quoted := String.intercalate "." ((name.splitOn ".").map ("«" ++ · ++ "»"))
      throw <| IO.userError s!"cites: no compiled {moduleFile name}. \
        Build every maintained source first: lake build '+{quoted}:olean'"

/-- Import private declarations and server metadata without executing project
initializers. Alias extension state is not initialized in this mode, but its
persisted entries remain available. -/
def load (modules : Array String) : IO Environment := do
  requireCompiled modules
  let env ← importModules (modules.map fun name => { module := toModuleName name }) {}
    (loadExts := false) (level := .private)
  let mut aliases := getAliasState env
  for i in [:env.header.moduleNames.size] do
    for entry in aliasExtension.getModuleEntries env i (level := .private) do
      aliases := addAliasEntry aliases entry
  return aliasExtension.setState env aliases.switch

def moduleIndices (env : Environment) (modules : Array String) :
    IO (Array (Nat × String)) := do
  let mut out := #[]
  for name in modules do
    let some i := env.header.moduleNames.findIdx? (· == toModuleName name)
      | throw <| IO.userError s!"cites: import omitted maintained module {name}"
    out := out.push (i, name)
  return out

/-- Only compiled docstrings count. Keep the kernel name for metadata lookup,
and the user name for the report and the declaration's namespace. -/
def sites (env : Environment) (modules : Array String) : IO (Array Site) := do
  let mut out := #[]
  for (i, name) in ← moduleIndices env modules do
    let file := moduleFile name
    for doc in (getModuleDoc? env (toModuleName name)).getD #[] do
      out := out.push {
        moduleName := name, file, line := doc.declarationRange.pos.line
        ns := .anonymous, subject := "the module docstring", text := doc.doc }
    for kernelName in env.header.moduleData[i]!.constNames do
      if let some doc ← findDocString? env kernelName then
        let userName := privateToUserName kernelName
        let range := declRangeExt.find? (level := .server) env kernelName
          <|> declRangeExt.find? (level := .exported) env kernelName
        out := out.push {
          moduleName := name, file, line := (range.map (·.range.pos.line)).getD 0
          ns := userName.getPrefix, subject := s!"`{userName}`", text := doc }
  return out

abbrev NameIndex := Std.HashMap String (Array (String × Name))

def indexName (idx : NameIndex) (moduleName : String) (name : Name) : NameIndex :=
  match privateToUserName name with
  | .str ns short =>
    let origins := idx[short]?.getD #[]
    if origins.contains (moduleName, ns) then idx
    else idx.insert short (origins.push (moduleName, ns))
  | _ => idx

def shortIndex (env : Environment) (modules : Array String) : IO NameIndex := do
  let mut idx := {}
  for (i, name) in ← moduleIndices env modules do
    for n in env.header.moduleData[i]!.constNames do
      idx := indexName idx name n
    for (aliasName, _) in aliasExtension.getModuleEntries env i (level := .private) do
      idx := indexName idx name aliasName
  return idx

/-- Restoring the declaring module lets Lean resolve its private names itself.
A resolver answer with projection suffixes is not a declaration, and reserved
names count only after the compiler has actually created their constants. -/
def resolvesIn (env : Environment) (moduleName : String) (ns : Name)
    (opens : List OpenDecl) (token : String) : Bool :=
  (ResolveName.resolveGlobalName (env.setMainModule (toModuleName moduleName)) {}
    ns opens token.toName).any fun (name, projections) =>
      projections.isEmpty && (env.checked.get.find? name).isSome

def verdict (env : Environment) (idx : NameIndex) (q : Query) : Verdict :=
  if resolvesIn env q.moduleName q.ns [.simple `Obligations []] q.token then .scope
  else if (idx[(q.token.splitOn ".").getLast!]?.getD #[]).any fun (m, ns) =>
      resolvesIn env m ns [] q.token then .tree
  else .phantom

/-- Each worker owns one imported environment. Its process exits before the next
batch starts, releasing Lean's imported memory regions as well as the values. -/
def run (request : Request) : IO Response := do
  searchPathRef.set (request.paths.toList.map System.FilePath.mk)
  let env ← load request.modules
  let docs ← if request.collect then sites env request.modules else pure #[]
  let idx ← shortIndex env request.modules
  return {
    modules := request.modules, sites := docs
    verdicts := request.queries.map (verdict env idx) }

end
end CiteEnv
