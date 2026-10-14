module

public import LeanTex.Cli.World
public import LeanTex.Core.LeanFacts
public import LeanTex.Core.Diag
public import LeanTex.Cli.ConvCache
import LeanTex.Core.CodeDoc
import LeanTex.Core.Flate
import Lean.Data.Json

/-! Lean's answer for a Lean file: a constant export program run under the file's own project,
its whole answer kept under a content key, a refusal Lean wrote kept beside it, and an attempt
that did not finish, or a machine that could not run it, asked again. -/

namespace LeanTex.Cli.LeanExport

open LeanTex.Core LeanTex.Cli.World

/-- The export, run as `lean` elaborates a file: it elaborates the bytes `LEANTEX_LEAN_SOURCE`
holds as the file `LEANTEX_LEAN_FILE`, command by command, then writes each declaration it wrote by
name, with its spans and type, to `LEANTEX_LEAN_ANSWER`. -/
public def program : String := r#"open Lean Elab Command

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
  let ictx := Parser.mkInputContext input file
  let (_, st0, _) ← Parser.parseHeader ictx
  let saved := (← get).messages
  let savedScopes := (← get).scopes
  let opts := (← getScope).opts
  modify fun s => { s with scopes := [{ header := "", opts }] }
  let (errors, writtens) ← withReader (fun ctx => { ctx with fileName := file, fileMap := ictx.fileMap }) do
    let mut st := st0
    let mut errors := 0
    let mut writtens : Array Written := #[]
    for _ in [0:input.utf8ByteSize + 1] do
      if st.pos.byteIdx ≥ input.utf8ByteSize then break
      let scope ← getScope
      let pmctx : Parser.ParserModuleContext :=
        { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
          openDecls := scope.openDecls }
      let (cmd, st', msgs) := Parser.parseCommand ictx pmctx st {}
      st := st'
      errors := errors + (msgs.toList.filter (·.severity == .error)).length
      if cmd.getKind == ``Lean.Parser.Command.exit then break
      writtens := writtens ++ writtenIn ictx.fileMap cmd
      modify fun s => { s with messages := {} }
      elabCommandTopLevel cmd
      errors := errors + ((← get).messages.toList.filter (·.severity == .error)).length
    return (errors, writtens)
  modify fun s => { s with messages := saved, scopes := savedScopes }
  let env ← getEnv
  let mut lines : Array String :=
    #[s!"\{\"leantex-lean-export\":1,\"lean\":{jstr Lean.versionString},\"errors\":{errors}}"]
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
    let type := if e.over then "null" else s!"[{",".intercalate e.nodes.toList}]"
    unless e.over do consts := e.consts.foldl (fun acc c => acc.insert c) consts
    let proved ← if info matches .thmInfo _ then
        do pure !(← collectAxioms name).contains ``sorryAx
      else pure true
    lines := lines.push (s!"\{\"name\":{jstr user.toString},\"module\":{jstr moduleName}," ++
      s!"\"kind\":\"{kind}\",\"range\":{spanText (some w.range)},\"head\":[{posText w.head}]," ++
      s!"\"signature\":{spanText w.sig},\"proof\":{spanText w.val},\"proved\":{proved}," ++
      s!"\"doc\":{(doc.map jstr).getD "null"}," ++
      s!"\"type\":{type}}")
    decls := decls + 1
  for w in writtens do
    unless seen.contains w.id do
      lines := lines.push (s!"\{\"failed\":{jstr w.name.toString},\"kind\":\"{w.kind}\"," ++
        s!"\"range\":{spanText (some w.range)},\"head\":[{posText w.head}]}")
  for c in consts.toList do
    if let some ci := env.find? c then
      lines := lines.push s!"\{\"const\":{jstr (shown c).toString},\"binders\":\"{mask "" ci.type}\"}"
  lines := lines.push s!"\{\"leantex-lean-export-end\":{decls}}"
  match ← (IO.FS.writeFile answer ("\n".intercalate lines.toList ++ "\n")).toBaseIO with
  | .ok () => pure ()
  | .error _ => IO.Process.exit 127
"#

/-- The program for one file: Lean's frontend and the file's own imports, then the export. -/
public def source (imports : Array String) : String :=
  let header := imports.foldl (fun s m => s ++ s!"import {m}\n") "import Lean.Elab.Frontend\n"
  header ++ program

/-- How long Lean may take over one file, and over saying which Lean it is, and how long either
has to stop. -/
public def budgetMs : Nat := 240000
public def versionBudgetMs : Nat := 30000
public def graceMs : Nat := 2000

/-- The directories from a path's own up to the root, nearest first. -/
private def ancestors (path : String) : List String :=
  let parts := (path.splitOn "/").filter (!·.isEmpty)
  let dir := parts.dropLast
  (List.range (dir.length + 1)).reverse.map fun k => "/" ++ "/".intercalate (dir.take k)

/-- The first directory among `dirs` that holds a regular file named one of `names`. -/
private def findUp (names : List String) : List String → Prog (Option String)
  | [] => .pure none
  | d :: rest => do
    for n in names do
      if ToolPath.isFile (← ask (.stat (ToolPath.join d n))) then return some d
    findUp names rest

/-- A file's bytes, or none. -/
private def bytesOf (path : String) : Prog (Option ByteArray) :=
  .ask (.readFile path) fun r => .pure r.toOption

/-- The Lake trace of a module the file imports, from the project's build or a package's. -/
private def traceOf (root : String) (packages : List String) (m : String) :
    Prog (Option ByteArray) := do
  let rel := m.replace "." "/" ++ ".trace"
  let dirs := (ToolPath.join root ".lake/build/lib/lean") ::
    packages.map fun p => ToolPath.join root s!".lake/packages/{p}/.lake/build/lib/lean"
  match ← findUp [rel] dirs with
  | some d => bytesOf (ToolPath.join d rel)
  | none => pure none

/-- Whether a module is the toolchain's own, which the toolchain's identity pins. -/
private def toolchainModule (m : String) : Bool :=
  ["Init", "Std", "Lean", "Lake"].any fun r => m == r || m.startsWith (r ++ ".")

/-- The cache slot one key takes under the user's cache directory, none without one. -/
private def slotOf (key : String) : Prog (Option String) := do
  let base ← match ← ask (.env "XDG_CACHE_HOME") with
    | some d => if d.isEmpty then pure none else pure (some d)
    | none => pure none
  let base ← match base with
    | some d => pure (some d)
    | none => (·.map (ToolPath.join · ".cache")) <$> ask (.env "HOME")
  match base with
  | none => pure none
  | some b =>
    let dir := ToolPath.join b "leantex/lean"
    match ← ask (.createDirAll dir) with
    | .ok () => pure (some (ToolPath.join dir (key ++ ".answer")))
    | .error _ => pure none

/-- Lean's own words for a run of the export that failed in the export: its first error placed
in `<scratch>/export.lean`, without that place. -/
public def exportSaid? (log : String) : Option String :=
  let lines := ((log.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty)
  lines.findSome? fun l =>
    if l.startsWith "<scratch>/export.lean:" then match l.splitOn "error: " with
      | _ :: rest@(_ :: _) =>
        let said := "error: ".intercalate rest
        some (if said.length > PicCache.saidLimit then (said.take PicCache.saidLimit).toString ++ "…"
          else said)
      | _ => none
    else none

/-- Whether an answer reads whole. -/
public def answerReads (bytes : ByteArray) : Bool :=
  ((String.fromUTF8? bytes).map fun t => (LeanFacts.decode t).toOption.isSome).getD false

/-- One attempt read as the export's answer: the answer it wrote, when it exited cleanly and the
answer reads; else Lean's refusal of the export itself in its own words; else no verdict. -/
public def resultOf (e : Ended) : ConvCache.Result :=
  match e.ran with
  | .exited c =>
    if c == 0 then
      match (e.outputs.find? (·.1 == "answer.jsonl")).bind (·.2) with
      | some bytes => if answerReads bytes then { outcome := .drawn, bytes }
        else { outcome := .inconclusive "Lean wrote an answer that does not read" }
      | none => { outcome := .inconclusive "Lean exited cleanly with no answer" }
    else if 126 ≤ c then { outcome := .inconclusive s!"Lean stopped with exit {c}" }
    else match exportSaid? (e.out ++ "\n" ++ e.err) with
      | some said => { outcome := .refused said }
      | none => { outcome := .inconclusive s!"Lean exited {c} with no answer" }
  | .overran s => { outcome := .inconclusive s!"Lean gave no answer within {s} s and was stopped" }
  | .unstarted why => { outcome := .inconclusive why }

/-- An answer is kept exactly when the export exited cleanly and wrote one that reads. -/
public theorem answer_kept_exact (e : Ended) (bytes : ByteArray) :
    (resultOf e).outcome = .drawn ∧ (resultOf e).bytes = bytes ↔
      e.ran = .exited 0 ∧ (e.outputs.find? (·.1 == "answer.jsonl")).bind (·.2) = some bytes ∧
        answerReads bytes = true := by
  unfold resultOf
  rcases e with ⟨ran, out, err, complete, outputs⟩
  cases ran with
  | exited c =>
    by_cases hc : c = 0
    · subst hc
      simp only [BEq.rfl, ite_true]
      cases hb : (outputs.find? (·.1 == "answer.jsonl")).bind (·.2) with
      | none => simp
      | some b =>
        by_cases hr : answerReads b = true
        · simp only [hr, ite_true]
          simp only [Option.some.injEq, true_and]
          exact ⟨fun h => ⟨h, h ▸ hr⟩, fun h => h.1⟩
        · simp [hr]
          intro h
          subst h
          simpa using hr
    · have h0 : (c == 0) = false := by simpa using hc
      simp only [h0, Bool.false_eq_true, ite_false]
      split
      · simp [hc]
      · split <;> simp [hc]
  | overran s => simp
  | unstarted why => simp

/-- A stopped run, one that never started, or an exit the machine forced, is asked again, never
kept. -/
public theorem unfinished_retried_exact (e : Ended)
    (hr : (∃ s, e.ran = .overran s) ∨ (∃ why, e.ran = .unstarted why) ∨
      ∃ c, 126 ≤ c ∧ e.ran = .exited c) :
    (resultOf e).record? = none := by
  rcases hr with ⟨s, hs⟩ | ⟨w, hw⟩ | ⟨c, hc, hx⟩
  · simp only [resultOf, hs]; exact ConvCache.inconclusive_retried_exact _ _
  · simp only [resultOf, hw]; exact ConvCache.inconclusive_retried_exact _ _
  · have h0 : (c == 0) = false := by simp; omega
    simp only [resultOf, hx, h0, hc, Bool.false_eq_true, ite_false, ite_true]
    exact ConvCache.inconclusive_retried_exact _ _

/-- A failed exit that left no error of the export's own in Lean's words is asked again. -/
public theorem silent_retried_exact (e : Ended) (c : Nat) (hc : c ≠ 0)
    (hx : e.ran = .exited c) (hs : exportSaid? (e.out ++ "\n" ++ e.err) = none) :
    (resultOf e).record? = none := by
  have h0 : (c == 0) = false := by simpa using hc
  simp only [resultOf, hx, h0, hs, Bool.false_eq_true, ite_false]
  split <;> exact ConvCache.inconclusive_retried_exact _ _

/-- The note a file whose statements Lean gave none of carries, once. -/
public def unread (file why : String) : Diag :=
  Diag.of .W0414 s!"Lean gave no statements for '{file}': {why}; its code is set without them"
    (some ⟨file, {}⟩) (subject := some s!"lean:{file}")

/-- What a result gives the page: Lean's answer, or the loss it names. -/
public def settle (file : String) (r : ConvCache.Result) : Option LeanFacts.Facts × Array Diag :=
  match r.answer with
  | .ok bytes =>
    match (String.fromUTF8? bytes).map LeanFacts.decode with
    | some (.ok facts) => (some facts, #[])
    | some (.error why) => (none, #[unread file s!"its answer does not read: {why}"])
    | none => (none, #[unread file "its answer is not UTF-8"])
  | .error why => (none, #[unread file why])

/-- The run that asks Lean about one file, from the file's project root: the file's bytes as
read, so the answer is of the bytes its key names. -/
public def callAt (root abs moduleName : String) (src : String) (bytes : ByteArray) (exe : String) :
    ToolCall :=
  { tool := exe, args := #["env", "lean", "-DElab.async=false", "<scratch>/export.lean"]
    inputs := #[("export.lean", src.toUTF8), ("source.lean", bytes)], outputs := #["answer.jsonl"]
    budgetMs, graceMs, captureLimit := 1048576
    env := #[("LEANTEX_LEAN_FILE", some abs), ("LEANTEX_LEAN_SOURCE", some "<scratch>/source.lean"),
      ("LEANTEX_LEAN_MODULE", some moduleName),
      ("LEANTEX_LEAN_ANSWER", some "<scratch>/answer.jsonl")]
    cwd := some root }

/-- The run that asks the project's Lean which it is. -/
public def versionAt (root exe : String) : ToolCall :=
  { tool := exe, args := #["env", "lean", "--version"], budgetMs := versionBudgetMs, graceMs
    captureLimit := 65536, cwd := some root }

/-- The key a file's answer is kept under: the export, the file's bytes, the path and module the
answer records, the Lean the project runs, its manifest and lakefile, and the Lake trace of each
module it imports from the project or its packages. -/
public def keyOf (src lean place : String) (pinned : Array (String × ByteArray))
    (bytes : ByteArray) : String :=
  let parts := pinned.foldl (fun s (name, b) =>
    s ++ "\u0000" ++ name ++ "\u0000" ++ Flate.contentKey b) ""
  Flate.contentKey (("lean-export-v1\u0000" ++ src ++ "\u0000" ++ lean ++ "\u0000" ++ place ++
    parts).toUTF8 ++ bytes)

/-- Whether a lakefile requires a package: a `require` command, or a `[[require]]` table. -/
public def requiresPackages (lakefile : String) : Bool :=
  (lakefile.splitOn "\n").any fun l =>
    let t := l.trimAscii.toString
    t.startsWith "require " || t.startsWith "[[require]]"

/-- The packages a project's manifest names that are not where it puts them, and with no manifest,
the lakefile's requirement, which Lake would fetch. -/
private def unfetched (root : String) (manifest : Option ByteArray) : Prog (List String) := do
  let some b := manifest | do
    for name in ["lakefile.lean", "lakefile.toml"] do
      if let some text := (← bytesOf (ToolPath.join root name)).bind String.fromUTF8? then
        if requiresPackages text then return [s!"the packages {name} requires"]
    return []
  let some text := String.fromUTF8? b | return []
  let .ok json := Lean.Json.parse text | return []
  let dir := (json.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let names := ((json.getObjValAs? (Array Lean.Json) "packages").toOption.getD #[]).filterMap
    fun p => (p.getObjValAs? String "name").toOption
  let mut missing := []
  for n in names do
    match ← ask (.stat (ToolPath.join root s!"{dir}/{n}")) with
    | .ok st => if st.kind != .dir then missing := missing ++ [n]
    | .error _ => missing := missing ++ [n]
  return missing

/-- A module's name from its file's place under the project root. -/
public def moduleOf (root abs : String) : String :=
  let rel := if abs.startsWith (root ++ "/") then (abs.drop (root.length + 1)).toString else abs
  let stem := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
  ".".intercalate (stem.splitOn "/")

/-- What Lean says about a Lean file, asked of the file's own project or remembered once that
project's Lean answers who it is, with the loss it names when Lean gives no answer. -/
public def factsFor (file : String) (bytes : ByteArray) (text : String) :
    Prog (Option LeanFacts.Facts × Array Diag) := do
  let some imports := Code.leanImports? text
    | return (none, #[unread file "a prelude file elaborates without Init, which the export needs"])
  let joined := match ← ask .cwd with
    | .ok d => if file.startsWith "/" then file else ToolPath.join d file
    | .error _ => file
  let abs := match ← ask (.stat joined) with
    | .ok st => st.real
    | .error _ => joined
  let dirs := ancestors abs
  let root := (← findUp ["lakefile.lean", "lakefile.toml"] dirs).getD (dirs.headD "/")
  let manifest ← bytesOf (ToolPath.join root "lake-manifest.json")
  let missing ← unfetched root manifest
  unless missing.isEmpty do
    return (none, #[unread file s!"its project's packages {", ".intercalate missing} are not fetched"])
  let moduleName := moduleOf root abs
  let some (_, said) ← ToolPath.probe "lake" (versionAt root)
    | return (none, #[unread file "no `lake` is on PATH to ask"])
  let lean := ((said.out.splitOn "\n").headD "").trimAscii.toString
  unless said.ran == .exited 0 && !lean.isEmpty do
    return (none, #[unread file s!"`lake env lean --version` gave no version"])
  let packages ← match ← ask (.listDir (ToolPath.join root ".lake/packages")) with
    | .ok entries => pure (entries.toList.filter (·.2 == .dir) |>.map (·.1))
    | .error _ => pure []
  let mut pinned : Array (String × ByteArray) := #[]
  let mut keyed := true
  for name in ["lake-manifest.json", "lakefile.lean", "lakefile.toml"] do
    if let some b ← bytesOf (ToolPath.join root name) then pinned := pinned.push (name, b)
  for m in imports do
    unless toolchainModule m do
      match ← traceOf root packages m with
      | some b => pinned := pinned.push (m, b)
      | none => keyed := false
  let src := source imports
  let slot ← if keyed then slotOf (keyOf src lean s!"{abs}\u0000{moduleName}" pinned bytes)
    else pure none
  if let some path := slot then
    if let some answer := (← bytesOf path).bind ConvCache.decode then
      let replayed := ConvCache.Result.replay answer
      -- A kept answer this reader no longer reads is no answer: Lean is asked again.
      if replayed.outcome != .drawn || answerReads replayed.bytes then
        return settle file replayed
  let some (_, ended) ← ToolPath.probe "lake" (callAt root abs moduleName src bytes)
    | return (none, #[unread file "no `lake` is on PATH to ask"])
  let result := resultOf ended
  if let some path := slot then
    if let some answer := result.record? then
      discard <| ask (.writeAtomic path (ConvCache.encode answer))
  return settle file result

end LeanTex.Cli.LeanExport
