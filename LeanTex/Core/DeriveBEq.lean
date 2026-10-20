module

public meta import Lean.Elab.Command
public meta import Lean.PrettyPrinter.Delaborator.Basic

open Lean Elab Command Meta

public section

namespace LeanTex.Core.DeriveBEq

/-- Whether an expression names a type of the family. -/
meta def mentions (fam : Array Name) (e : Expr) : Bool :=
  (e.find? fun s => s.isConst && fam.contains s.constName!).isSome

/-- Whether an expression is an inductive type's application. -/
meta def inductiveApp? (e : Expr) : MetaM (Option InductiveVal) := do
  let .const c _ := e.getAppFn | return none
  match (← getEnv).find? c with
  | some (.inductInfo v) => return if v.numIndices == 0 then some v else none
  | _ => return none

/-- A field type as the inductive application its definitions unfold to. -/
meta def inductiveHead (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if (← inductiveApp? e).isSome then return e
  let e ← whnfD e
  if (← inductiveApp? e).isSome then return e
  throwError "structural BEq: {e} is not an inductive type without indices"

/-- The name of the comparison of the `k`th type, the family's own first. -/
meta def auxName (base : Name) (k : Nat) : Name :=
  if k == 0 then base ++ `beq else base ++ .mkSimple s!"beq_{k}"

/-- The match arms comparing two values of `ty` constructor by constructor; a field whose type holds
the family calls that type's comparison, added to `targets` when new, and a proof is not read. -/
meta def arms (fam : Array Name) (base : Name) (targets : Array Expr) (ty : Expr) :
    MetaM (Array (TSyntax ``Parser.Term.matchAlt) × Array Expr) := do
  let some ind ← inductiveApp? ty | throwError "structural BEq: {ty} is not an inductive type"
  let .const _ us := ty.getAppFn | throwError "structural BEq: {ty} has no constant head"
  let params := ty.getAppArgs
  let mut targets := targets
  let mut out := #[]
  for ctor in ind.ctors do
    let info ← getConstInfoCtor ctor
    let cty ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) params
    let (alt, ts) ← forallTelescope cty fun xs _ => do
      let mut ts := targets
      let mut pa : Array Term := #[]
      let mut pb : Array Term := #[]
      let mut tests : Array Term := #[]
      for h : i in [0:xs.size] do
        let x := xs[i]
        let fty ← inferType x
        if ← isProp fty then
          pa := pa.push (← `(_))
          pb := pb.push (← `(_))
          continue
        for y in xs.extract (i + 1) xs.size do
          if (← inferType y).containsFVar x.fvarId! then
            throwError "structural BEq: {ctor} has a field its later fields depend on"
        let a := mkIdent (.mkSimple s!"a{i}")
        let b := mkIdent (.mkSimple s!"b{i}")
        pa := pa.push a
        pb := pb.push b
        if !mentions fam fty then
          tests := tests.push (← `($a == $b))
        else
          let fty ← inductiveHead fty
          let k ← match ts.findIdx? (· == fty) with
            | some k => pure k
            | none => do
              ts := ts.push fty
              pure (ts.size - 1)
          let f := mkIdent (auxName base k)
          tests := tests.push (← `($f $a $b))
      let holes : Array Term ← (List.replicate params.size ()).toArray.mapM fun _ => `(_)
      let c := mkCIdent ctor
      let body ← match tests.toList with
        | [] => `(true)
        | t :: rest => rest.foldlM (fun acc t => `($acc && $t)) t
      let alt ← `(Parser.Term.matchAltExpr| | @$c $holes* $pa*, @$c $holes* $pb* => $body)
      return (alt, ts)
    targets := ts
    out := out.push alt
  if ind.ctors.length > 1 then
    out := out.push (← `(Parser.Term.matchAltExpr| | _, _ => false))
  return (out, targets)

/-- `deriving_structural_beq T`: a `BEq` instance for the inductive `T`, nested through containers
or mutual, by structural recursion where `deriving BEq` leaves an opaque one. -/
syntax (name := derivingStructuralBEq) "deriving_structural_beq " ident : command

@[command_elab derivingStructuralBEq]
meta def elabDerivingStructuralBEq : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ind ← getConstInfoInduct name
  let fam := ind.all.toArray
  for n in fam do
    let v ← getConstInfoInduct n
    unless v.numIndices == 0 && v.levelParams.isEmpty do
      throwError "structural BEq: {n} takes indices or universes"
  let instOf (n : Name) : Name := n.getPrefix ++ .mkSimple ("instBEq" ++ n.getString!)
  let base := instOf name
  let pub := (← getEnv).header.isModule && !isPrivateName name
  let cmds ← liftTermElabM <| forallBoundedTelescope ind.type ind.numParams fun ps _ => do
    let delab (e : Expr) : TermElabM Term :=
      withOptions (fun o => o.setBool `pp.fullNames true) (PrettyPrinter.delab e)
    let mut binders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
    for p in ps do
      let n := mkIdent (← p.fvarId!.getUserName)
      let t ← delab (← inferType p)
      binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| {$n : $t}))
      binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| [BEq $n]))
    let mut targets : Array Expr := fam.map fun n => mkAppN (mkConst n) ps
    let mut defs : Array (TSyntax `command) := #[]
    let mut k := 0
    while h : k < targets.size do
      let ty := targets[k]
      let (alts, ts) ← arms fam base targets ty
      targets := ts
      let tySyn ← delab ty
      let f := mkIdent (`_root_ ++ auxName base k)
      let body ← `(match x, y with $alts:matchAlt*)
      let body ← if ty.getAppFn.isConstOf ``Array then `(x.size == y.size && $body) else pure body
      let d ← if pub then
          `(command| public def $f $binders:bracketedBinder* (x y : $tySyn) : Bool := $body
              termination_by structural x)
        else
          `(command| def $f $binders:bracketedBinder* (x y : $tySyn) : Bool := $body
              termination_by structural x)
      defs := defs.push d
      k := k + 1
    let mut insts : Array (TSyntax `command) := #[]
    for h : j in [0:fam.size] do
      let i := mkIdent (`_root_ ++ instOf fam[j])
      let t ← delab (mkAppN (mkConst fam[j]) ps)
      let f := mkIdent (auxName base j)
      insts := insts.push (← if pub then
          `(command| public instance $i:ident $binders:bracketedBinder* : BEq $t := ⟨$f⟩)
        else `(command| instance $i:ident $binders:bracketedBinder* : BEq $t := ⟨$f⟩))
    let block ← `(command| mutual
        $defs:command*
      end)
    return #[block] ++ insts
  for c in cmds do elabCommand c

end LeanTex.Core.DeriveBEq
end
