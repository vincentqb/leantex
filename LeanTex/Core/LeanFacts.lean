module

import Lean.Data.Json

/-! # What Lean says about a Lean file

The answer Lean's own export gives for one file: each declaration it elaborated, by name, kind,
source range and type, in a small schema read whole or refused whole. -/

namespace LeanTex.Core.LeanFacts

open Lean (Json)

/-- A binder's kind, as Lean elaborates it. -/
public inductive Binder where
  | explicit
  | implicit
  | strict
  | inst
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a term applies its arguments to. -/
public inductive Head where
  | const (name : String)
  | bvar (index : Nat)
  | sort (level : String)
  | nat (n : Nat)
  | str (s : String)
  | other (what : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A Lean type in the export's schema, each application flattened to its head and arguments, and
each binder of a `∀` marked when its type is a proposition. -/
public inductive Term where
  | apps (head : Head) (args : List Term)
  | applied (fn : Term) (args : List Term)
  | pi (name : String) (binder : Binder) (prop : Bool) (type body : Term)
  | lam (name : String) (binder : Binder) (type body : Term)
  | letE (name : String) (type value body : Term)
  | proj (struct : String) (index : Nat) (e : Term)
  deriving Repr, BEq, Inhabited

/-- The kinds of declaration whose statement a page sets. -/
public inductive Kind where
  | theorem
  | definition
  | axiom
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One declaration: its name, kind, source range (lines from one, columns in characters from
zero) and type, `none` where the type is larger than an answer carries. -/
public structure Decl where
  name : String
  kind : Kind
  start : Nat × Nat
  stop : Nat × Nat
  type : Option Term
  /-- Where the command that writes it opens: its own start, or the outermost `… in` before it. -/
  head : Nat × Nat := start
  /-- The module the declaration belongs to, the spans of its signature and of its value, and
  whether its value rests on no `sorryAx`. -/
  moduleName : String := ""
  signature : Option ((Nat × Nat) × (Nat × Nat)) := none
  proof : Option ((Nat × Nat) × (Nat × Nat)) := none
  proved : Bool := true
  /-- Whether its type is a proposition. -/
  prop : Bool
  deriving Repr, BEq, Inhabited

/-- A declaration the file writes by name that Lean added nothing for: its name as written, its
kind, its range, where the command that writes it opens, and its value's span. -/
public structure Failed where
  name : String
  kind : Kind
  start : Nat × Nat
  stop : Nat × Nat
  head : Nat × Nat := start
  proof : Option ((Nat × Nat) × (Nat × Nat)) := none
  deriving Repr, BEq, Inhabited

/-- An answer: the Lean that gave it, the errors its elaboration logged, the declarations, those
that failed, and the leading binders of every constant their types name. -/
public structure Facts where
  lean : String
  errors : Nat
  decls : Array Decl
  binders : Array (String × Array Binder)
  failed : Array Failed := #[]
  deriving Repr, BEq, Inhabited

/-- The schema's version, which an answer's first line names. -/
public def schemaVersion : Nat := 2

/-- The most bytes an answer may hold, and the most nodes one type may. -/
public def maxAnswerBytes : Nat := 16 * 1024 * 1024
public def maxTypeNodes : Nat := 20000

/-- A binder's kind from its letter. -/
public def binderOf? : Char → Option Binder
  | 'd' => some .explicit
  | 'i' => some .implicit
  | 's' => some .strict
  | 'c' => some .inst
  | _ => none

private def applyTo (f a : Term) : Term :=
  match f with
  | .apps h args => .apps h (args ++ [a])
  | .applied g args => .applied g (args ++ [a])
  | .pi .. | .lam .. | .letE .. | .proj .. => .applied f [a]

private def take (built : Array (Option Term)) (i : Nat) :
    Except String (Term × Array (Option Term)) :=
  match built[i]? with
  | some (some t) => .ok (t, built.set! i none)
  | some none => .error "a node is read twice"
  | none => .error "a node reads one not before it"

private def natOf (j : Json) : Except String Nat :=
  match j with
  | .num n =>
    if n.exponent == 0 && n.mantissa ≥ 0 then .ok n.mantissa.toNat
    else .error "a number is no natural number"
  | _ => .error "a number is missing"

private def node (built : Array (Option Term)) (j : Json) :
    Except String (Term × Array (Option Term)) := do
  let arr ← j.getArr?
  let str (k : Nat) : Except String String := (arr[k]?.getD .null).getStr?
  let idx (k : Nat) : Except String Nat := natOf (arr[k]?.getD .null)
  let binder (k : Nat) : Except String Binder := do
    match (← str k).toList with
    | [c] => match binderOf? c with
      | some b => pure b
      | none => throw "an unknown binder"
    | _ => throw "an unknown binder"
  match ← str 0 with
  | "bvar" => return (.apps (.bvar (← idx 1)) [], built)
  | "const" => return (.apps (.const (← str 1)) [], built)
  | "sort" => return (.apps (.sort (← str 1)) [], built)
  | "nat" =>
    let some n := (← str 1).toNat? | throw "a numeral is no natural number"
    return (.apps (.nat n) [], built)
  | "str" => return (.apps (.str (← str 1)) [], built)
  | "other" => return (.apps (.other (← str 1)) [], built)
  | "app" =>
    let (f, built) ← take built (← idx 1)
    let (a, built) ← take built (← idx 2)
    return (applyTo f a, built)
  | "pi" =>
    let (t, built) ← take built (← idx 3)
    let (body, built) ← take built (← idx 4)
    let prop ← match ← idx 5 with
      | 0 => pure false
      | 1 => pure true
      | _ => throw "a binder's mark is neither 0 nor 1"
    return (.pi (← str 1) (← binder 2) prop t body, built)
  | "lam" =>
    let (t, built) ← take built (← idx 3)
    let (body, built) ← take built (← idx 4)
    return (.lam (← str 1) (← binder 2) t body, built)
  | "let" =>
    let (t, built) ← take built (← idx 2)
    let (v, built) ← take built (← idx 3)
    let (body, built) ← take built (← idx 4)
    return (.letE (← str 1) t v body, built)
  | "proj" =>
    let (e, built) ← take built (← idx 3)
    return (.proj (← str 1) (← idx 2) e, built)
  | k => throw s!"an unknown node '{k}'"

/-- A type from its post-order nodes: a tree whose every node but the last is read once. -/
private def termOf (nodes : Array Json) : Except String Term := do
  if nodes.size > maxTypeNodes then throw "a type larger than an answer may carry"
  let mut built : Array (Option Term) := #[]
  for j in nodes do
    let (t, b) ← node built j
    built := b.push (some t)
  let some (some root) := built.back? | throw "a type with no node"
  unless built.pop.all Option.isNone do throw "a node no other reads"
  return root

private def pairOf (arr : Array Json) (k : Nat) : Except String (Nat × Nat) := do
  return (← natOf (arr[k]?.getD .null), ← natOf (arr[k + 1]?.getD .null))

private def kindOf? : String → Option Kind
  | "theorem" => some .theorem
  | "def" => some .definition
  | "axiom" => some .axiom
  | _ => none

/-- A span from its four numbers, or none for a `null`. -/
private def spanOf (j : Json) : Except String (Option ((Nat × Nat) × (Nat × Nat))) := do
  match j with
  | .null => return none
  | _ =>
    let arr ← j.getArr?
    let a ← pairOf arr 0
    let b ← pairOf arr 2
    return some (a, b)

/-- One record line: a declaration, one that failed, or a constant's binders. -/
private def record (facts : Facts) (j : Json) : Except String Facts := do
  match j.getObjValAs? String "const", j.getObjValAs? String "failed" with
  | .ok c, _ =>
    let mask ← j.getObjValAs? String "binders"
    let bs ← mask.toList.mapM fun ch => match binderOf? ch with
      | some b => Except.ok b
      | none => Except.error "an unknown binder"
    return { facts with binders := facts.binders.push (c, bs.toArray) }
  | .error _, .ok name =>
    let some kind := kindOf? (← j.getObjValAs? String "kind") | throw "an unknown kind"
    let range ← j.getObjValAs? (Array Json) "range"
    let start ← pairOf range 0
    let stop ← pairOf range 2
    let head ← pairOf (← j.getObjValAs? (Array Json) "head") 0
    let proof ← spanOf (j.getObjValD "proof")
    return { facts with failed := facts.failed.push { name, kind, start, stop, head, proof } }
  | .error _, .error _ =>
    let some kind := kindOf? (← j.getObjValAs? String "kind") | throw "an unknown kind"
    let range ← j.getObjValAs? (Array Json) "range"
    let type ← match j.getObjValD "type" with
      | .null => pure none
      | t => some <$> (termOf (← t.getArr?))
    let name ← j.getObjValAs? String "name"
    let start ← pairOf range 0
    let stop ← pairOf range 2
    let head ← pairOf (← j.getObjValAs? (Array Json) "head") 0
    let moduleName ← j.getObjValAs? String "module"
    let signature ← spanOf (j.getObjValD "signature")
    let proof ← spanOf (j.getObjValD "proof")
    let proved ← j.getObjValAs? Bool "proved"
    let prop ← j.getObjValAs? Bool "prop"
    let decl : Decl :=
      { name, kind, start, stop, type, head, moduleName, signature, proof, proved, prop }
    return { facts with decls := facts.decls.push decl }

/-- An answer, whole or refused whole. -/
public def decode (body : String) : Except String Facts := do
  if body.utf8ByteSize > maxAnswerBytes then throw "an answer larger than an answer may be"
  let lines := (body.splitOn "\n").filter (!·.isEmpty)
  let some head := lines.head? | throw "an empty answer"
  let h ← Json.parse head
  if (← h.getObjValAs? Nat "leantex-lean-export") != schemaVersion then
    throw "an answer in another schema"
  let lean ← h.getObjValAs? String "lean"
  let errors ← h.getObjValAs? Nat "errors"
  let mut facts : Facts := { lean, errors, decls := #[], binders := #[] }
  let some last := lines.getLast? | throw "an empty answer"
  if lines.length < 2 then throw "an answer with no end"
  let count ← (← Json.parse last).getObjValAs? Nat "leantex-lean-export-end"
  for line in (lines.drop 1).dropLast do
    facts ← record facts (← Json.parse line)
  if facts.decls.size != count then throw "an answer that does not hold the declarations it counts"
  return facts

/-- Whether a term names a constant anywhere in it. -/
public def Term.names (c : String) : Term → Bool
  | .apps h args => (match h with
      | .const n => n == c
      | .bvar _ | .sort _ | .nat _ | .str _ | .other _ => false) || namesList c args
  | .applied f args => f.names c || namesList c args
  | .pi _ _ _ t b => t.names c || b.names c
  | .lam _ _ t b => t.names c || b.names c
  | .letE _ t v b => t.names c || v.names c || b.names c
  | .proj _ _ e => e.names c
where
  namesList (c : String) : List Term → Bool
    | [] => false
    | t :: rest => t.names c || namesList c rest

/-- Whether Lean elaborated the type without standing in for an error: it names no `sorryAx`. -/
public def Term.elaborated (t : Term) : Bool := !t.names "sorryAx"

/-- Whether `Membership.mem` takes its collection first, as it does from Lean 4.12 on. -/
public def Facts.collectionFirst (f : Facts) : Bool :=
  match (f.lean.splitOn ".").map String.toNat? with
  | some major :: some minor :: _ => major > 4 || (major == 4 && minor ≥ 12)
  | _ => true

/-- Whether a binder shows: only an explicit one does. -/
@[expose] public def Binder.shows : Binder → Bool
  | .explicit => true
  | .implicit | .strict | .inst => false

/-- Whether a term reads the variable bound `k` binders up. -/
public def Term.reads (k : Nat) : Term → Bool
  | .apps h args => (match h with
      | .bvar i => i == k
      | .const _ | .sort _ | .nat _ | .str _ | .other _ => false) || readsList k args
  | .applied f args => f.reads k || readsList k args
  | .pi _ _ _ t b => t.reads k || b.reads (k + 1)
  | .lam _ _ t b => t.reads k || b.reads (k + 1)
  | .letE _ t v b => t.reads k || v.reads k || b.reads (k + 1)
  | .proj _ _ e => e.reads k
where
  readsList (k : Nat) : List Term → Bool
    | [] => false
    | t :: rest => t.reads k || readsList k rest

/-- The constants a term names, in order of first mention. -/
public def Term.consts (acc : Array String) : Term → Array String
  | .apps h args =>
    let acc := match h with
      | .const n => if acc.contains n then acc else acc.push n
      | .bvar _ | .sort _ | .nat _ | .str _ | .other _ => acc
    constsList acc args
  | .applied f args => constsList (f.consts acc) args
  | .pi _ _ _ t b => b.consts (t.consts acc)
  | .lam _ _ t b => b.consts (t.consts acc)
  | .letE _ t v b => b.consts (v.consts (t.consts acc))
  | .proj _ _ e => e.consts acc
where
  constsList (acc : Array String) : List Term → Array String
    | [] => acc
    | t :: rest => constsList (t.consts acc) rest

/-- The label a declaration's kind sets before its name. -/
public def Kind.label : Kind → String
  | .theorem => "Theorem"
  | .definition => "Definition"
  | .axiom => "Axiom"

end LeanTex.Core.LeanFacts
