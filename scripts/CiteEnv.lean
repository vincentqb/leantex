module

public import Lean

namespace CiteEnv

open Lean

-- Kernel names travel as component kind and bytes, leaf first, which identifiers cannot carry.
inductive NamePart where
  | str (value : String)
  | num (value : Nat)
  deriving FromJson, ToJson

def nameParts : Name → List NamePart
  | .anonymous => []
  | .str parent value => .str value :: nameParts parent
  | .num parent value => .num value :: nameParts parent

def partsName : List NamePart → Name
  | [] => .anonymous
  | .str value :: parent => .str (partsName parent) value
  | .num value :: parent => .num (partsName parent) value

theorem nameParts_roundtrip_exact (name : Name) :
    partsName (nameParts name) = name := by
  induction name <;> simp_all [nameParts, partsName]

local instance : ToJson Name where
  toJson name := toJson (nameParts name)

local instance : FromJson Name where
  fromJson? json := partsName <$> (fromJson? json : Except String (List NamePart))

public structure Site where
  moduleName : String
  file : String
  line : Nat
  ns : Name
  subject : String
  text : String
  deriving FromJson, ToJson

public structure Query where
  moduleName : String
  ns : Name
  token : String
  deriving BEq, Hashable, FromJson, ToJson

public inductive Verdict where
  | scope
  | tree
  | phantom
  deriving BEq, Inhabited, FromJson, ToJson, Repr

/-- A batch's work: the docstrings to collect, the queries to judge, and the
queries whose resolved declarations are wanted by name, not only by verdict. -/
public structure Request where
  modules : Array String
  paths : Array String
  collect : Bool := false
  queries : Array Query := #[]
  named : Array Query := #[]
  deriving FromJson, ToJson

/-- A declaration a named query resolves to, and whether it forms types: an inductive,
structure, class, constructor, or a definition whose result is a sort. -/
public structure Resolved where
  name : Name
  typeFormer : Bool
  deriving BEq, Inhabited, FromJson, ToJson

public structure Response where
  modules : Array String
  sites : Array Site := #[]
  verdicts : Array Verdict := #[]
  named : Array (Array Resolved) := #[]
  deriving FromJson, ToJson

public def moduleFile (name : String) : String := name.replace "." "/" ++ ".lean"

/-- A module name from raw inventory components, dashed script names included, which
`String.toName` would reject. -/
def toModuleName (name : String) : Name :=
  (name.splitOn ".").foldl Name.str .anonymous

public def requireCompiled (modules : Array String) : IO Unit := do
  for name in modules do
    let compiled ← try
      (← findOLean (toModuleName name)).pathExists
    catch _ => pure false
    unless compiled do
      let quoted := String.intercalate "." ((name.splitOn ".").map ("«" ++ · ++ "»"))
      throw <| IO.userError s!"cites: no compiled {moduleFile name}. \
        Build every maintained source first: lake build '+{quoted}:olean'"

/-- Import private declarations and server metadata without running project initializers.
-/
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

/-- The compiled docstring sites of `modules`, by kernel name for lookup and by user name
for the report. -/
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

/-- The complete declarations a token names from a module and namespace; a
projection-suffixed answer is no declaration, and reserved names count only once created.
-/
def resolvedIn (env : Environment) (moduleName : String) (ns : Name)
    (opens : List OpenDecl) (token : String) : List Name :=
  ((ResolveName.resolveGlobalName (env.setMainModule (toModuleName moduleName)) {}
    ns opens token.toName).filter fun (name, projections) =>
      projections.isEmpty && (env.checked.get.find? name).isSome).map (·.1)

def resolvesIn (env : Environment) (moduleName : String) (ns : Name)
    (opens : List OpenDecl) (token : String) : Bool :=
  !(resolvedIn env moduleName ns opens token).isEmpty

/-- The places a token's last component is declared: where the tree tier
resolves it from. -/
def origins (idx : NameIndex) (token : String) : Array (String × Name) :=
  idx[(token.splitOn ".").getLast!]?.getD #[]

def verdict (env : Environment) (idx : NameIndex) (q : Query) : Verdict :=
  if resolvesIn env q.moduleName q.ns [] q.token then .scope
  else if (origins idx q.token).any fun (m, ns) => resolvesIn env m ns [] q.token then .tree
  else .phantom

/-- Every declaration a query's token names through either tier, each once. -/
def resolutions (env : Environment) (idx : NameIndex) (q : Query) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for n in resolvedIn env q.moduleName q.ns [] q.token do
    unless out.contains n do out := out.push n
  for (m, ns) in origins idx q.token do
    for n in resolvedIn env m ns [] q.token do
      unless out.contains n do out := out.push n
  return out

def resolvedOf (env : Environment) (n : Name) : Resolved :=
  { name := n, typeFormer := match env.checked.get.find? n with
      | some (.ctorInfo _) => true
      | some info => info.type.getForallBody.isSort
      | none => false }

/-- One batch in its own worker process, which exits before the next starts, releasing the
imported environment. -/
public def run (request : Request) : IO Response := do
  searchPathRef.set (request.paths.toList.map System.FilePath.mk)
  let env ← load request.modules
  let docs ← if request.collect then sites env request.modules else pure #[]
  let idx ← shortIndex env request.modules
  return {
    modules := request.modules, sites := docs
    verdicts := request.queries.map (verdict env idx)
    named := request.named.map fun q => (resolutions env idx q).map (resolvedOf env) }

end CiteEnv
