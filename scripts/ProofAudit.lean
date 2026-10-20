module

public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.PreDefinition.Structural.Eqns
public meta import Lean.Elab.PreDefinition.WF.Eqns
meta import Lean.Util.CollectAxioms
meta import Lean.Util.Path
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Compiler.ExternAttr

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

/-- The modules that define the engine's base unit, the only ones that may spell a count of it. -/
meta def baseUnitModules : Array Name := #[`LeanTex.Core.Dim, `LeanTex.Core.DimSpell]

/-- A numeral as it elaborates: a raw literal or `OfNat.ofNat`, possibly negated or cast. -/
meta def numeral? (e : Expr) : Option Int :=
  let nat? (e : Expr) : Option Nat := match e.consumeMData with
    | .lit (.natVal n) => some n
    | e => if e.isAppOfArity ``OfNat.ofNat 3 then
        match (e.getArg! 1).consumeMData with
        | .lit (.natVal n) => some n
        | _ => none
      else none
  let e := e.consumeMData
  let e := if e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``NatCast.natCast 3 ||
      e.isAppOfArity ``Int.cast 3 || e.isAppOfArity ``IntCast.intCast 3 then e.getArg! 2
    else if e.isAppOfArity ``Int.ofNat 1 then e.getArg! 0 else e
  match nat? e with
  | some n => some n
  | none =>
    if e.isAppOfArity ``Neg.neg 3 then (nat? (e.getArg! 2)).map fun n => -(n : Int)
    else if e.isAppOfArity ``Int.negSucc 1 then (nat? (e.getArg! 0)).map fun n => -((n : Int) + 1)
    else none

/-- Whether an expression reads a length's base-unit count, through casts, `toNat` and `natAbs`;
`exact` counts its rational image too. -/
meta def readsUnits (exact : Bool) (e : Expr) : Bool :=
  let peel (e : Expr) : Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``Int.cast 3 || e.isAppOfArity ``IntCast.intCast 3 ||
        e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``NatCast.natCast 3 then
      (e.getArg! 2).consumeMData
    else if e.isAppOfArity ``Int.toNat 1 || e.isAppOfArity ``Int.natAbs 1 then
      (e.getArg! 0).consumeMData
    else e
  let e := peel (peel e)
  e.isAppOfArity `LeanTex.Core.Dim.Length.units 1 ||
    (exact && e.isAppOfArity `LeanTex.Core.Dim.Length.toRat 1)

/-- Whether an expression is a closed count made of numerals and arithmetic alone. -/
meta def numericConstant (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasFVar && !e.hasMVar && e.getUsedConstants.all fun c =>
    c.getRoot == `Int || c.getRoot == `Nat || c.getRoot == `Rat ||
      #[``OfNat.ofNat, ``Neg.neg, ``HMul.hMul, ``HAdd.hAdd, ``HSub.hSub, ``HDiv.hDiv, ``HMod.hMod,
        ``Mul.mul, ``Add.add, ``Sub.sub, ``Div.div, ``NatCast.natCast, ``IntCast.intCast].contains c ||
      (match c with
       | .str _ s => s.startsWith "inst"
       | _ => false)

/-- An expression with each project constant of type Int, Nat or Rat naming a count read as its
value, through four names, so `def bpCount : Nat := (bp 1).units.toNat` meets the audit as its spelling. -/
meta def unfoldCounts (env : Environment) (e : Expr) : Expr := Id.run do
  let project (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some i => !(env.header.moduleNames[i.toNat]?).any fun m => [`Init, `Std, `Lean].contains m.getRoot
    | none => true
  let named (c : Name) : Option Expr :=
    if !project c || c == `LeanTex.Core.Dim.unitsPerInch then none else
    match env.find? c with
    | some (.defnInfo d) =>
      if !(#[``Int, ``Nat, ``Rat].any d.type.isConstOf) || d.value.hasLooseBVars then none
      else if numericConstant d.value || (d.value.find? (readsUnits true ·)).isSome ||
          d.value.getUsedConstants.any project then some d.value
      else none
    | _ => none
  let mut e := e
  for _ in [0:4] do
    let next := e.replace fun sub => match sub with
      | .const c _ => named c
      | _ => none
    if next == e then break
    e := next
  return e

/-- What a subterm spells of a count of the base unit, which Dim alone defines: the base itself, a
length built from a closed count, a large multiple of the quantum, or a base-unit count or a large
scale of its rational image against a numeral other than 0 and ±1. -/
meta def baseLiteral (e : Expr) : Option String :=
  let carries (x : Expr) := (x.find? fun s => (numeral? s).any (·.natAbs ≥ 32768)).isSome
  let large (x : Expr) := match numeral? x with
    | some n => n.natAbs ≥ 32768
    | none => numericConstant x && carries x
  let hit (sub : Expr) : Option String :=
    if sub.isConstOf `LeanTex.Core.Dim.unitsPerInch then some "the base unit itself"
    else if (#[`LeanTex.Core.Dim.Length.ofUnits, `LeanTex.Core.Dim.Length.ofRatFloor,
        `LeanTex.Core.Dim.Length.ofRatCeil, `LeanTex.Core.Dim.Length.ofRatRound].any
          (sub.isAppOfArity · 1)) &&
        (numericConstant (sub.getArg! 0) || carries (sub.getArg! 0)) then
      some "a length built from a count of base units"
    else if sub.isAppOfArity `LeanTex.Core.Dim.Length.ofRatio 3 &&
        (sub.getArg! 0).consumeMData.isConstOf `LeanTex.Core.Dim.Length.quantum then
      some "a length built from a count of quanta"
    else
      let args := sub.getAppArgs
      let scaling := #[(``HMul.hMul, 6), (``HDiv.hDiv, 6), (``HMod.hMod, 6)]
      let compare := #[(``HAdd.hAdd, 6), (``HSub.hSub, 6), (``LE.le, 4), (``LT.lt, 4), (``GE.ge, 4),
        (``GT.gt, 4), (``Eq, 3), (``Ne, 3), (``BEq.beq, 4), (``bne, 4), (``Max.max, 4), (``Min.min, 4)]
      let full (ops : Array (Name × Nat)) := ops.any fun (n, k) => sub.isAppOfArity n k
      if !(full scaling || full compare) then none else
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let quantum (x : Expr) := x.consumeMData.isConstOf `LeanTex.Core.Dim.Length.quantum
      let big (x : Expr) := match numeral? x with
        | some n => n.natAbs ≥ 2
        | none => numericConstant x
      let scaled := full scaling
      if sub.isAppOf ``HMul.hMul && ((quantum a && large b) || (quantum b && large a)) then
        some "a large multiple of the quantum"
      else if (readsUnits false a && big b) || (readsUnits false b && big a) then
        some "a base-unit count against a numeral"
      else if (readsUnits true a && (if scaled then large b else big b)) ||
          (readsUnits true b && (if scaled then large a else big a)) then
        some "a rational base-unit count against a numeral"
      else none
  (e.find? fun sub => (hit sub).isSome).bind hit

/-- Whether a definition of the given arity binds a `let` before a function it returns. -/
meta def letBeforeLambda (arity : Nat) (value : Expr) : Bool :=
  let (params, body) := lambdas value
  match lets body with
  | (0, _) => false
  | (_, rest) => rest.isLambda || params < arity
where
  lambdas : Expr → Nat × Expr
    | .lam _ _ body _ => let (n, e) := lambdas body; (n + 1, e)
    | .mdata _ e => lambdas e
    | e => (0, e)
  lets : Expr → Nat × Expr
    | .letE _ _ _ body _ => let (n, e) := lets body; (n + 1, e)
    | .mdata _ e => lets e
    | e => (0, e)

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

/-- For each argument of an application spine, right to left, whether it fills a slot of a
recursive call that `dead` marks. -/
meta def spineSlots (dead : NameMap (Array Bool)) (e : Expr) : List Bool :=
  let n := e.getAppNumArgs
  match e.getAppFn with
  | .const g _ => match dead.find? g with
    | some slots => ((List.range n).map fun j => slots.getD j false).reverse
    | none => List.replicate n false
  | _ => List.replicate n false

/-- Whether `e` reads `x` anywhere but in the slots `dead` marks on recursive calls, given the
marks of the spine an argument is peeled from. -/
meta def readsOutside (dead : NameMap (Array Bool)) (x : FVarId) :
    Expr → Option (List Bool) → Bool
  | e@(.app f a), some (d :: rest) =>
    e.hasFVar && ((!d && readsOutside dead x a none) || readsOutside dead x f (some rest))
  | e@(.app f a), some [] => e.hasFVar && (readsOutside dead x a none || readsOutside dead x f none)
  | e@(.app f a), none => e.hasFVar && match spineSlots dead e with
    | d :: rest => (!d && readsOutside dead x a none) || readsOutside dead x f (some rest)
    | [] => readsOutside dead x a none || readsOutside dead x f none
  | e@(.lam _ t b _), _ | e@(.forallE _ t b _), _ =>
    e.hasFVar && (readsOutside dead x t none || readsOutside dead x b none)
  | e@(.letE _ t v b _), _ =>
    e.hasFVar && (readsOutside dead x t none || readsOutside dead x v none ||
      readsOutside dead x b none)
  | .mdata _ b, _ | .proj _ _ b, _ => readsOutside dead x b none
  | .fvar y, _ => y == x
  | _, _ => false

/-- Per discriminant of a matcher and per alternative, the field the alternative's pattern binds
the discriminant to, read off the alternative's type; `none` for a discriminant some pattern
inspects. -/
meta def matchAliases (m : Name) (info : Meta.MatcherInfo) :
    MetaM (Array (Option (Array (Option Nat)))) := do
  Meta.forallTelescope (← getConstInfo m).type fun xs _ => do
    let first := info.numParams + 1 + info.numDiscrs
    let mut per : Array (Option (Array (Option Nat))) := Array.replicate info.numDiscrs (some #[])
    for (alt, i) in info.altInfos.zipIdx do
      let fields := alt.numFields + (if alt.hasUnitThunk then 1 else 0)
      let row ← Meta.forallBoundedTelescope (← Meta.inferType (xs.getD (first + i) default)) fields
        fun ys rest => Meta.forallTelescope rest fun _ res => do
          let pats := res.getAppArgs
          return (Array.range info.numDiscrs).map fun j =>
            let pat := pats.getD j default
            if pat.isFVar then (ys.findIdx? (· == pat)).map some else none
      per := (per.zip row).map fun
        | (some acc, some t) => some (acc.push t)
        | _ => none
    return per

/-- Whether `body` reads `x` outside the slots `marks` makes dead, a root match that binds `x`
only to variables passing it to the alternatives that bind it. -/
meta def readsThrough (marks : NameMap (Array Bool)) (x : FVarId) (body : Expr) : MetaM Bool := do
  let body := body.consumeMData
  let some m := body.getAppFn.constName? | return readsOutside marks x body none
  let some info ← Meta.getMatcherInfo? m | return readsOutside marks x body none
  let args := body.getAppArgs
  let np := info.numParams
  let nd := info.numDiscrs
  let na := info.altInfos.size
  if args.size < np + 1 + nd + na then return readsOutside marks x body none
  let js := (List.range nd).filter fun j => args.getD (np + 1 + j) default == .fvar x
  if js.isEmpty then return readsOutside marks x body none
  let aliases ← try matchAliases m info catch _ => return true
  if js.any fun j => (aliases.getD j none).isNone then return true
  let mut read := false
  for (a, k) in args.zipIdx do
    if np + 1 ≤ k && k < np + 1 + nd && js.contains (k - np - 1) then continue
    if np + 1 + nd ≤ k && k < np + 1 + nd + na then
      let i := k - np - 1 - nd
      let alt := info.altInfos.getD i default
      let fields := alt.numFields + (if alt.hasUnitThunk then 1 else 0)
      let viaAlt ← Meta.lambdaBoundedTelescope a fields fun ys altBody => do
        let bound := js.filterMap fun j => (((aliases.getD j none).getD #[]).getD i none).bind
          fun t => (ys.getD t default).fvarId?
        return readsOutside marks x altBody none || bound.any (readsOutside marks · altBody none)
      read := read || viaAlt
    else read := read || readsOutside marks x a none
  return read

/-- A recursive declaration's block: every name defined with it and their bodies before
the recursion was compiled away. -/
meta def recursiveBlock (env : Environment) (decl : Name) : Option (Array Name × Array Expr) :=
  let value (n : Name) : Option Expr :=
    ((Elab.Structural.eqnInfoExt.find? env n).map (·.value)).orElse fun _ =>
      (Elab.WF.eqnInfoExt.find? env n).map (·.value)
  let names := ((Elab.Structural.eqnInfoExt.find? env decl).map (·.declNames)).orElse fun _ =>
    (Elab.WF.eqnInfoExt.find? env decl).map (·.declNames)
  names.bind fun names => (names.mapM value).map (names, ·)

/-- The data parameters of a recursive block that nothing reads but its own recursive calls,
each as its declaration, position and name: the greatest set closed under passing. -/
meta def threadedParams (names : Array Name) (bodies : Array Expr) :
    MetaM (Array (Name × Nat × Name)) := do
  let arities ← bodies.mapM fun v => Meta.lambdaTelescope v fun xs _ => pure xs.size
  let mut dead : NameMap (Array Bool) := {}
  for (n, k) in names.zip arities do dead := dead.insert n (Array.replicate k true)
  for _ in [0:arities.foldl (· + ·) 1] do
    let mut changed := false
    for (n, v) in names.zip bodies do
      let before := (dead.find? n).getD #[]
      let marks := dead
      let after ← Meta.lambdaTelescope v fun xs body => do
        let types ← xs.mapM Meta.inferType
        let result ← Meta.inferType body
        let mut slots := before
        for (x, i) in xs.zipIdx do
          let some id := x.fvarId? | continue
          if slots.getD i false then
            let live := (← Meta.isProp (types.getD i x)) ||
              (types.extract (i + 1) types.size).any (·.containsFVar id) ||
              result.containsFVar id || (← readsThrough marks id body)
            if live then slots := slots.setIfInBounds i false
        return slots
      if after != before then
        dead := dead.insert n after
        changed := true
    unless changed do break
  let mut out := #[]
  for (n, v) in names.zip bodies do
    let users ← Meta.lambdaTelescope v fun xs _ => xs.mapM fun x => return (← Meta.getFVarLocalDecl x).userName
    for (b, i) in ((dead.find? n).getD #[]).zipIdx do
      if b then out := out.push (n, i, users.getD i .anonymous)
  return out

/-- The library loops the binary may reach, whose own value the scan does not read: the host's
file-system walks and file reads, which the `toolchain-loops` premise holds to end. -/
meta def worldLoops : Array Name := #[`IO.FS.createDirAll, `IO.FS.removeDirAll,
  `IO.FS.Handle.readBinToEndInto.loop]

/-- The library functions the project may call that loop through `WellFounded.extrinsicFix` over
iterators they build themselves, which the `toolchain-loops` premise holds finite. -/
meta def iteratorEntries : Array Name := #[`String.foldl,
  `String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep,
  `String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorLoopIdSearchStep,
  `String.toNat?, `String.toNat!, `String.toInt?,
  `System.FilePath.parent, `System.FilePath.fileName, `System.FilePath.fileStem,
  `System.FilePath.extension, `System.FilePath.withExtension, `System.FilePath.components,
  `System.FilePath.isAbsolute, `System.FilePath.isRelative, `System.FilePath.instDiv,
  `System.FilePath.instHDivString, `IO.FS.DirEntry.path, `Array.mergeSort]

/-- The project constants that may loop until interrupted: the watch mode, which rebuilds on every
change, each rebuild a call the scan reads. -/
meta def unendingLoops : Array Name := #[`LeanTex.Cli.Driver.watch]

/-- Whether a constant is a `partial` definition's opaque stand-in. -/
meta def isPartialConst (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.opaqueInfo _) => (env.find? (n ++ `_unsafe_rec)).isSome ||
      (Compiler.getImplementedBy? env n).any (· == n ++ `_unsafe_rec)
  | _ => false

/-- Whether a constant is the project's: declared in one of its modules, or named in its
namespace. -/
meta def projectConst (env : Environment) (n : Name) : Bool :=
  let inModule := (env.getModuleIdxFor? n).any fun i =>
    let m := env.header.moduleNames[i.toNat]?.getD .anonymous
    m.getRoot == `LeanTex || m == `Main
  inModule || (privateToUserName n).getRoot == `LeanTex

/-- The constants a root's values reach, those of them with no value to read, and each offence:
the constant at fault, the project constant reaching it and the library function it enters by. -/
meta def partialReach (env : Environment) (root : Name) :
    Nat × Nat × Array (Name × Name × Name) := Id.run do
  let user := privateToUserName
  let project (n : Name) := n == root || projectConst env n
  let mut seen : NameSet := {}
  let mut succ : NameMap (Array Name) := {}
  let mut stack : Array Name := #[root]
  let mut found : Array (Name × Name × Name) := #[]
  let mut prims := 0
  while h : 0 < stack.size do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if worldLoops.contains (user n) then continue
    if project n && ((Compiler.getImplementedBy? env n).isSome || isExtern env n) then
      found := found.push (n, n, n)
    let value? := match env.find? n with
      | some (.defnInfo d) => some d.value
      | some (.opaqueInfo o) => if isPartialConst env n then none else some o.value
      | _ => none
    match env.find? n with
    | some (.opaqueInfo _) => unless isPartialConst env n do prims := prims + 1
    | some (.axiomInfo _) => pure ()
    | _ => if isExtern env n then prims := prims + 1
    if let some v := value? then
      let cs := v.getUsedConstants
      succ := succ.insert n cs
      for c in cs do
        unless seen.contains c do stack := stack.push c
  let mut pred : NameMap (Array Name) := {}
  for (n, cs) in succ do
    for c in cs do pred := pred.insert c (((pred.find? c).getD #[]).push n)
  for p in seen do
    unless isPartialConst env p && !worldLoops.contains (user p) do continue
    if project p then
      let callers := ((pred.find? p).getD #[]).filter project
      for x in (if callers.isEmpty then #[p] else callers) do found := found.push (p, x, p)
      continue
    let mut lib : NameSet := ({} : NameSet).insert p
    let mut queue : Array Name := #[p]
    while h : 0 < queue.size do
      let y := queue[queue.size - 1]
      queue := queue.pop
      for x in (pred.find? y).getD #[] do
        if project x then
          let looping := unendingLoops.contains (user x) && user p == `repeatM.impl
          let iterating := user p == `WellFounded.opaqueFix && iteratorEntries.contains (user y)
          unless looping || iterating do found := found.push (p, x, y)
        else if !lib.contains x then
          lib := lib.insert x
          queue := queue.push x
  return (seen.size, prims, found)

/-- `#audit_reach r`: no partial constant is reachable from `r`'s definition but through the
world, iterator and unending loops named above, and no project constant it reaches runs other
code than its value. -/
elab "#audit_reach " root:ident : command => do
  let env ← getEnv
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let (count, prims, found) := partialReach env name
  for (n, near, entry) in found do
    if isPartialConst env n then
      let (who, what) := (privateToUserName near, privateToUserName n)
      let via := if entry == n then m!"" else m!" through {privateToUserName entry}"
      logError m!"partial reach: {who} reaches {what}{via}, a partial definition; recurse \
structurally or on a measure instead, and derive a nested or mutual type's equality with \
`deriving_structural_beq`"
    else
      logError m!"partial reach: {privateToUserName n} runs other code than its definition"
  if found.isEmpty then
    logInfo m!"partial reach: {count} constants from {privateToUserName name}, none partial, \
{prims} of them runtime primitives the lean-runtime premise runs"

/-- Audit the compiled declarations of an explicit source manifest, private and unused
ones included, against the accepted foundation (quotient soundness, classical choice and
propositional extensionality) and for a `let` bound before a returned function. -/
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
  let mut threaded : NameSet := {}
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
      let numbered (s pre : String) : Bool :=
        s.startsWith pre && !(s.drop pre.length).toString.isEmpty &&
          (s.drop pre.length).toString.all Char.isDigit
      let fieldDefault := match privateToUserName decl with
        | .str _ s => s == "_default"
        | _ => false
      let body := match privateToUserName decl with
        | .str _ s => s == "_unary" || s == "_mutual"
        | _ => false
      let generated := ((privateToUserName decl).isInternalDetail && !fieldDefault && !body) || match decl with
        | .str _ s => numbered s "eq_" || s == "eq_def" || s == "splitter" || numbered s "match_"
        | _ => false
      if !baseUnitModules.contains name && !generated then
        if let some info := env.find? decl then
          let spelled := (baseLiteral (unfoldCounts env info.type)).orElse fun _ => match info with
            | .defnInfo d => baseLiteral (unfoldCounts env d.value)
            | .thmInfo t =>
              if (t.value.find? (·.isConstOf `LeanTex.Core.Dim.unitsPerInch)).isSome then
                some "the base unit itself, read in a proof"
              else none
            | _ => none
          if let some what := spelled then
            logError m!"proof audit: {name}: {decl} spells a count of the base unit, {what}; \
build the length with Dim's unit constructors and read it through Dim's conversions"
            failures := failures + 1
      if let some (.defnInfo d) := env.find? decl then
        let arity ← liftTermElabM <| withCurrHeartbeats <| Meta.withReducible <|
          Meta.forallTelescopeReducing d.type fun xs _ => pure xs.size
        if !isNoncomputable env decl && letBeforeLambda arity d.value then
          logError m!"proof audit: {name}: {decl} binds a let before the function it returns, \
so the let runs on every call; return what it binds as a structure"
          failures := failures + 1
      if let some (block, bodies) := recursiveBlock env decl then
        unless threaded.contains decl do
          for m in block do threaded := threaded.insert m
          for (d, i, x) in ← liftTermElabM (withCurrHeartbeats (threadedParams block bodies)) do
            logError m!"proof audit: {name}: {privateToUserName d} passes its parameter \
{x.eraseMacroScopes} (#{i + 1}) only to its own recursive calls; nothing reads it"
            failures := failures + 1
      count := count + 1
  if failures == 0 then
    logInfo m!"proof audit: {expected.size} modules, {count} declarations checked"
