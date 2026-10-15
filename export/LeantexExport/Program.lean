/-! The export the exporter hands the project's own `lean`: it elaborates a file command by
command and writes each declaration the file writes by name, with its spans and type, and each
command's span and text. -/

namespace LeantexExport

/-- The export, run as `lean` elaborates a file: it elaborates the bytes `LEANTEX_LEAN_SOURCE`
holds as the file `LEANTEX_LEAN_FILE`, command by command, then writes to `LEANTEX_LEAN_ANSWER`
each declaration it wrote by name, with its spans and type, and each command's span and text. -/
def program : String := r#"open Lean Elab Command

namespace LeantexExport

def binderCode : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

def jstr (s : String) : String := (Json.str s).compress

/-- A constant's name as its source spells it. -/
def shown (n : Name) : Name := (privateToUserName? n).getD n

structure Emitted where
  nodes : Array String := #[]
  consts : NameSet := {}
  over : Bool := false

abbrev EmitM := StateT Emitted MetaM

def cap : Nat := 20000

def full : EmitM Bool := do
  if (← get).nodes.size ≥ cap then
    modify fun e => { e with over := true }
    return true
  return false

def push (node : String) : EmitM Nat := do
  if ← full then return 0
  modify fun e => { e with nodes := e.nodes.push node }
  return (← get).nodes.size - 1

/-- A type's nodes in post-order, each binder's type also checked for being a proposition under the
binders `xs` it stands inside. -/
def emit : Expr → Array Expr → EmitM Nat
  | .bvar i, _ => push s!"[\"bvar\",{i}]"
  | .fvar _, _ => push "[\"other\",\"fvar\"]"
  | .mvar _, _ => push "[\"other\",\"mvar\"]"
  | .sort l, _ => push s!"[\"sort\",{jstr (toString l)}]"
  | .const n _, _ => do
    modify fun e => { e with consts := e.consts.insert n }
    push s!"[\"const\",{jstr (shown n).toString}]"
  | .app f a, xs => do
    if ← full then return 0
    let i ← emit f xs
    let j ← emit a xs
    push s!"[\"app\",{i},{j}]"
  | .lam n t b bi, xs => do
    if ← full then return 0
    let i ← emit t xs
    let j ← Meta.withLocalDecl n bi (t.instantiateRev xs) fun x => emit b (xs.push x)
    push s!"[\"lam\",{jstr n.eraseMacroScopes.toString},\"{binderCode bi}\",{i},{j}]"
  | .forallE n t b bi, xs => do
    if ← full then return 0
    let i ← emit t xs
    let ty := t.instantiateRev xs
    let prop ← try Meta.isProp ty catch _ => pure false
    let j ← Meta.withLocalDecl n bi ty fun x => emit b (xs.push x)
    push s!"[\"pi\",{jstr n.eraseMacroScopes.toString},\"{binderCode bi}\",{i},{j},{if prop then 1 else 0}]"
  | .letE n t v b _, xs => do
    if ← full then return 0
    let i ← emit t xs
    let j ← emit v xs
    let k ← Meta.withLetDecl n (t.instantiateRev xs) (v.instantiateRev xs) fun x => emit b (xs.push x)
    push s!"[\"let\",{jstr n.eraseMacroScopes.toString},{i},{j},{k}]"
  | .lit (.natVal n), _ => push s!"[\"nat\",{jstr (toString n)}]"
  | .lit (.strVal s), _ => push s!"[\"str\",{jstr s}]"
  | .proj s i b, xs => do
    if ← full then return 0
    let j ← emit b xs
    push s!"[\"proj\",{jstr (shown s).toString},{i},{j}]"
  | .mdata _ b, xs => emit b xs

def mask (acc : String) : Expr → String
  | .forallE _ _ b bi => mask (acc ++ binderCode bi) b
  | .mdata _ b => mask acc b
  | _ => acc

def kindOf (env : Environment) (n : Name) : ConstantInfo → Option String
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => if Meta.isInstanceCore env n || env.isProjectionFn n then none else some "def"
  | .opaqueInfo _ => if Meta.isInstanceCore env n then none else some "def"
  | .axiomInfo _ => some "axiom"
  | _ => none

/-- A declaration a command writes by name: its kind, its name as written, where that name and
the declaration stand, where the command that writes it opens, and its signature's and value's
spans. -/
structure Written where
  kind : String
  name : Name
  id : Position
  range : Position × Position
  head : Position
  sig : Option (Position × Position)
  val : Option (Position × Position)

def spanOf (fm : FileMap) (stx : Syntax) : Option (Position × Position) := do
  let a ← stx.getPos?
  let b ← stx.getTailPos?
  return (fm.toPosition a, fm.toPosition b)

/-- The child of one of `kinds`, among a node's arguments and those of its optional parts. -/
def childOf (stx : Syntax) (kinds : List Name) : Option Syntax :=
  let direct := stx.getArgs.toList
  let nested := direct.flatMap fun a => if a.getKind == nullKind then a.getArgs.toList else []
  (direct ++ nested).find? fun a => kinds.contains a.getKind

def keyword (k : SyntaxNodeKind) : Option String :=
  if k == ``Lean.Parser.Command.theorem then some "theorem"
  else if k == ``Lean.Parser.Command.definition || k == ``Lean.Parser.Command.abbrev ||
      k == ``Lean.Parser.Command.opaque then some "def"
  else if k == ``Lean.Parser.Command.axiom then some "axiom"
  else none

/-- The declarations a command writes, through `mutual` and `… in`, each opening where the
outermost `… in` around it does. -/
def writtenIn (fm : FileMap) (cmd : Syntax) : Array Written := Id.run do
  let mut todo : Array (Syntax × Option Position) := #[(cmd, none)]
  let mut out := #[]
  for _ in [0:4096] do
    let some (stx, head) := todo.back? | break
    todo := todo.pop
    let k := stx.getKind
    if k == ``Lean.Parser.Command.mutual then todo := todo ++ stx[1].getArgs.map fun a => (a, none)
    else if k == ``Lean.Parser.Command.in then
      todo := todo.push (stx[2], head <|> stx.getPos?.map fm.toPosition)
    else if k == ``Lean.Parser.Command.declaration then
      let decl := stx[1]
      if let some kw := keyword decl.getKind then
        if let some id := childOf decl [``Lean.Parser.Command.declId] then
          if let (some p, some r) := (id.getPos?, spanOf fm stx) then
            let sig := (childOf decl [``Lean.Parser.Command.declSig,
              ``Lean.Parser.Command.optDeclSig]).bind (spanOf fm)
            let val := (childOf decl [``Lean.Parser.Command.declValSimple,
              ``Lean.Parser.Command.declValEqns, ``Lean.Parser.Command.whereStructInst]).bind (spanOf fm)
            let w : Written :=
              { kind := kw, name := id[0].getId, id := fm.toPosition p, range := r
                head := head.getD r.1, sig, val }
            out := out.push w
  return out

/-- Whether a constant's name ends with what its declaration writes, `_root_.` aside. -/
def namedBy (n written : Name) : Bool :=
  let w := (written.componentsRev.filter (· != `_root_))
  !w.isEmpty && n.componentsRev.take w.length == w

def posText (p : Position) : String := s!"{p.line},{p.column}"

/-- The text between two positions of a source whose lines are `lines`. -/
def between (lines : Array (List Char)) (a b : Position) : String := Id.run do
  let mut out := ""
  for l in [a.line:b.line + 1] do
    let cs := lines[l - 1]?.getD []
    let cs := if l == b.line then cs.take b.column else cs
    let cs := if l == a.line then cs.drop a.column else cs
    out := cs.foldl String.push out
    if l != b.line then out := out.push '\n'
  return out

def spanText : Option (Position × Position) → String
  | some (a, b) => s!"[{posText a},{posText b}]"
  | none => "null"

end LeantexExport

open LeantexExport in
run_cmd do
  let some file ← (IO.getEnv "LEANTEX_LEAN_FILE" : IO (Option String))
    | throwError "leantex export: LEANTEX_LEAN_FILE names no file"
  let some source ← (IO.getEnv "LEANTEX_LEAN_SOURCE" : IO (Option String))
    | throwError "leantex export: LEANTEX_LEAN_SOURCE names no file"
  let some answer ← (IO.getEnv "LEANTEX_LEAN_ANSWER" : IO (Option String))
    | throwError "leantex export: LEANTEX_LEAN_ANSWER names no file"
  let moduleName := ((← (IO.getEnv "LEANTEX_LEAN_MODULE" : IO (Option String))).getD "")
  -- A file the machine cannot read or write is no verdict on the file: the run stops apart.
  let input ← match ← (IO.FS.readFile source).toBaseIO with
    | .ok text => pure text
    | .error _ => IO.Process.exit 127
  -- Lean reads the source with its line ends made `\n`, and so do the positions it gives.
  let ictx := Parser.mkInputContext input file
  let text := ictx.inputString
  let textLines : Array (List Char) := (text.splitOn "\n").toArray.map String.toList
  let (header, st0, _) ← Parser.parseHeader ictx
  let saved := (← get).messages
  let savedScopes := (← get).scopes
  let opts := (← getScope).opts
  modify fun s => { s with scopes := [{ header := "", opts }] }
  let (errors, writtens, read) ← withReader (fun ctx => { ctx with fileName := file, fileMap := ictx.fileMap }) do
    let mut st := st0
    let mut errors := 0
    let mut writtens : Array Written := #[]
    let mut read : Array (Position × Position) := (spanOf ictx.fileMap header).toArray
    for _ in [0:text.utf8ByteSize + 1] do
      if st.pos.byteIdx ≥ text.utf8ByteSize then break
      let scope ← getScope
      let pmctx : Parser.ParserModuleContext :=
        { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
          openDecls := scope.openDecls }
      let begin := st.pos
      let recovering := st.recovering
      let (cmd, st', msgs) := Parser.parseCommand ictx pmctx st {}
      st := st'
      let failed := msgs.toList.any (·.severity == .error)
      let span := spanOf ictx.fileMap cmd
      -- A command a parse error cuts short, and the text the next skips, are quoted whole.
      if failed || recovering then
        let stop := match span, failed with
          | some (_, b), false => b
          | _, _ => ictx.fileMap.toPosition st'.pos
        read := read.push (ictx.fileMap.toPosition begin, stop)
      else if cmd.getKind != ``Lean.Parser.Command.moduleDoc then
        if let some r := span then read := read.push r
      if cmd.getKind == ``Lean.Parser.Command.eoi then break
      errors := errors + (msgs.toList.filter (·.severity == .error)).length
      if cmd.getKind == ``Lean.Parser.Command.exit then break
      writtens := writtens ++ writtenIn ictx.fileMap cmd
      modify fun s => { s with messages := {} }
      elabCommandTopLevel cmd
      errors := errors + ((← get).messages.toList.filter (·.severity == .error)).length
    return (errors, writtens, read)
  modify fun s => { s with messages := saved, scopes := savedScopes }
  let env ← getEnv
  let mut lines : Array String :=
    #[s!"\{\"leantex-lean-export\":3,\"lean\":{jstr Lean.versionString},\"errors\":{errors}}"]
  let mut consts : NameSet := {}
  let mut decls := 0
  let mut seen : Array Position := #[]
  let mine := env.constants.map₂.toList.toArray.qsort fun a b => a.1.toString < b.1.toString
  for (name, info) in mine do
    if (`LeantexExport).isPrefixOf name then continue
    let some ranges := declRangeExt.find? env name | continue
    seen := seen.push ranges.selectionRange.pos
    let user := shown name
    if user.isInternal then continue
    let some kind := kindOf env name info | continue
    let some w := writtens.find? fun w => w.id == ranges.selectionRange.pos && namedBy user w.name
      | continue
    let doc ← findDocString? env name
    let (_, e) ← liftTermElabM <| (emit info.type #[]).run {}
    let prop ← liftTermElabM <| try Meta.isProp info.type catch _ => pure false
    let type := if e.over then "null" else s!"[{",".intercalate e.nodes.toList}]"
    unless e.over do consts := e.consts.foldl (fun acc c => acc.insert c) consts
    let proved ← if info matches .thmInfo _ then
        do pure !(← collectAxioms name).contains ``sorryAx
      else pure true
    lines := lines.push (s!"\{\"name\":{jstr user.toString},\"module\":{jstr moduleName}," ++
      s!"\"kind\":\"{kind}\",\"range\":{spanText (some w.range)},\"head\":[{posText w.head}]," ++
      s!"\"signature\":{spanText w.sig},\"proof\":{spanText w.val},\"proved\":{proved}," ++
      s!"\"prop\":{prop}," ++
      s!"\"doc\":{(doc.map jstr).getD "null"}," ++
      s!"\"type\":{type}}")
    decls := decls + 1
  for w in writtens do
    unless seen.contains w.id do
      lines := lines.push (s!"\{\"failed\":{jstr w.name.toString},\"kind\":\"{w.kind}\"," ++
        s!"\"range\":{spanText (some w.range)},\"head\":[{posText w.head}],\"proof\":{spanText w.val}}")
  for c in consts.toList do
    if let some ci := env.find? c then
      lines := lines.push s!"\{\"const\":{jstr (shown c).toString},\"binders\":\"{mask "" ci.type}\"}"
  for (a, b) in read do
    lines := lines.push s!"\{\"command\":{spanText (some (a, b))},\"text\":{jstr (between textLines a b)}}"
  lines := lines.push s!"\{\"leantex-lean-export-end\":{decls}}"
  match ← (IO.FS.writeFile answer ("\n".intercalate lines.toList ++ "\n")).toBaseIO with
  | .ok () => pure ()
  | .error _ => IO.Process.exit 127
"#

/-- The export for one file: Lean's frontend and the file's own imports, then the program. -/
def source (imports : Array String) : String :=
  let header := imports.foldl (fun s m => s ++ s!"import {m}\n") "import Lean.Elab.Frontend\n"
  header ++ program

end LeantexExport
