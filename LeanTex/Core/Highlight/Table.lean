module

public import LeanTex.Core.Highlight.Regex
public import Std.Data.HashSet
import LeanTex.Core.PygmentsLexData

/-! Pygments' `RegexLexer` over a lexer's exported rule table (pygments/lexer.py; BSD-licensed:
testdata/highlight/LICENSE-Pygments); a run of transitions reading nothing takes the fallback at a
stack it held before, where Pygments never ends, or past the square of the states plus one. -/
namespace LeanTex.Core.Highlight.Table

open Regex

/-- What a group of a match writes: nothing, a token, or its text lexed again from a stack, top
last, as `using(this)` does. -/
public inductive GroupAct where
  | skip
  | token (ty : String)
  | relex (stack : List Nat)
  deriving Repr, Inhabited

/-- What a match writes. -/
public inductive Action where
  | none
  | token (ty : String)
  | groups (acts : Array GroupAct)
  | relex (stack : List Nat)
  deriving Repr, Inhabited

/-- One transition step: pop up to `n` states, keeping the root; push the top again; push a state. -/
public inductive Op where
  | pop (n : Nat)
  | dup
  | push (state : Nat)
  deriving Repr, Inhabited

public structure Rule where
  pattern : Nat
  action : Action
  next : Array Op
  deriving Inhabited

/-- A lexer's patterns, its states' rules, its root, and the names its lexing retypes from `Name` to
`Keyword.Type` afterwards. -/
public structure Lexer where
  patterns : Array Pattern
  states : Array (Array Rule)
  root : Nat
  retype : Std.HashSet String

namespace Decode

private def stack? (s : String) : Option (List Nat) :=
  (s.splitOn "/").mapM (·.toNat?)

private def groupAct? (s : String) : Option GroupAct :=
  match s.front with
  | '-' => some .skip
  | 't' => some (.token (s.drop 1).toString)
  | 'u' => (stack? (s.drop 1).toString).map .relex
  | _ => none

private def action? (s : String) : Option Action :=
  let rest := (s.drop 1).toString
  match s.front with
  | '-' => some .none
  | 't' => some (.token rest)
  | 'g' => ((rest.splitOn ";").mapM groupAct?).map fun acts => .groups acts.toArray
  | 'u' => (stack? rest).map .relex
  | _ => none

private def op? (s : String) : Option Op :=
  let rest := (s.drop 1).toString
  match s.front with
  | 'p' => rest.toNat?.map .pop
  | 'd' => some .dup
  | 's' => rest.toNat?.map .push
  | _ => none

private def next? (s : String) : Option (Array Op) :=
  if s == "-" then some #[] else ((s.splitOn ",").mapM op?).map (·.toArray)

/-- A lexer from its table's lines; `none` where a line does not read. -/
public def lexer? (rules : String) (retype : Array String) : Option Lexer := do
  let lines := rules.splitOn "\n"
  let head ← lines.head?
  let (count, root) ← match head.splitOn " " with
    | ["lexer", n, r, _] => some (← n.toNat?, ← r.toNat?)
    | _ => none
  let mut patterns : Array Pattern := #[]
  let mut states : Array (Array Rule) := #[]
  for line in lines.drop 1 do
    match line.splitOn " " with
    | "p" :: g :: code => patterns := patterns.push (← decode? (" ".intercalate code) (← g.toNat?))
    | ["state", _] => states := states.push #[]
    | ["r", p, a, n] =>
      let rule : Rule := { pattern := ← p.toNat?, action := ← action? a, next := ← next? n }
      if states.isEmpty then failure
      states := states.modify (states.size - 1) (·.push rule)
    | _ => failure
  if states.size != count || root ≥ count then failure
  let inRange (n : Nat) : Bool := n < count
  let opOk : Op → Bool
    | .push st => inRange st
    | .pop _ | .dup => true
  let actOk : Action → Bool
    | .relex stack => stack.all inRange
    | .groups acts => acts.all fun
      | .relex stack => stack.all inRange
      | .skip | .token _ => true
    | .none | .token _ => true
  unless states.all (·.all fun r => r.pattern < patterns.size && r.next.all opOk && actOk r.action) do
    failure
  return { patterns, states, root, retype := retype.foldl (·.insert ·) {} }

end Decode

/-- `n` pops, the root kept. -/
private def popN {σ : Type} (m : Machine σ) : Nat → Machine σ
  | 0 => m
  | n + 1 => popN m.pop n

private def apply (m : Machine Nat) : Op → Machine Nat
  | .pop n => popN m n
  | .dup => m.dup
  | .push st => m.push st

/-- The first rule of `rules` matching at `pos`: the rule, its end and its groups. -/
private def firstMatch (lx : Lexer) (rules : Array Rule) (s : Src) (pos : Nat) :
    Option (Rule × Res) := Id.run do
  for r in rules do
    if let some p := lx.patterns[r.pattern]? then
      if let some res := p.matchAt s pos then return some (r, res)
  return none

/-- A token at `[a, b)`, written unless empty. -/
private def put (out : Array Raw) (a b : Nat) (ty : String) : Array Raw :=
  if a < b then out.push ⟨a, b, ty⟩ else out

/-- `[a, b)` lexed again from `stack`, its tokens placed at `a`. -/
private def relexed (s : Src) (sub : Src → List Nat → Array Raw) (out : Array Raw) (a b : Nat)
    (stack : List Nat) : Array Raw :=
  (sub ⟨s.chars.extract a b⟩ stack.reverse).foldl (init := out) fun o r =>
    o.push ⟨r.start + a, r.stop + a, r.kind⟩

/-- The tokens a match writes. -/
private def written (s : Src) (sub : Src → List Nat → Array Raw) (out : Array Raw) (pos : Nat)
    (res : Res) : Action → Array Raw
  | .none => out
  | .token ty => put out pos res.1 ty
  | .relex stack => relexed s sub out pos res.1 stack
  | .groups acts => Id.run do
    let mut o := out
    for act in acts, g in [1:acts.size + 1] do
      if let some (some (a, b)) := res.2[g]? then
        match act with
        | .skip => pure ()
        | .token ty => o := put o a b ty
        | .relex stack => o := relexed s sub o a b stack
    return o

/-- One step: rules tried until one reads a scalar or pops below where the step began, else the
fallback at a stack the step held before or past its bound. -/
private def step (lx : Lexer) (sub : Src → List Nat → Array Raw) (s : Src) (m : Machine Nat) :
    Machine Nat := Id.run do
  let mut cur := m
  let mut held : Array (List Nat) := #[m.stack]
  for _ in [0:(lx.states.size + 1) * (lx.states.size + 1)] do
    let rules := lx.states.getD (cur.top?.getD lx.root) #[]
    match firstMatch lx rules s cur.pos with
    | none => return cur.fallback s lx.root
    | some (r, res) =>
      let out := written s sub cur.out cur.pos res r.action
      let next := r.next.foldl apply { cur with out, pos := res.1 }
      if next.pos > m.pos || next.depth < m.depth then return next
      if held.contains next.stack then return next.fallback s lx.root
      held := held.push next.stack
      cur := next
  return cur.fallback s lx.root

/-- The raw stream from `stack`, top first, before the retyping. -/
public def lexFrom (lx : Lexer) (stack : List Nat) (s : Src) : Array Raw :=
  driveFrom lx.root stack (step lx fun sub st =>
    if _h : sub.size < s.size then lexFrom lx st sub
    else if sub.size == 0 then #[] else #[⟨0, sub.size, Ty.text⟩]) s
termination_by s.size

/-- The lexer's whole stream, each `Name` its retyping names a `Keyword.Type`. -/
public def lex (lx : Lexer) (s : Src) : Array Raw :=
  (lexFrom lx [lx.root] s).map fun r =>
    if r.kind == Ty.name && lx.retype.contains (String.ofList (s.chars.extract r.start r.stop).toList)
    then { r with kind := Ty.keywordType } else r

/-- The table lexers, decoded on first use. -/
private def decoded (_ : Unit) : Array (Option Lexer) :=
  PygmentsLexData.tableRules.mapIdx fun i rules =>
    Decode.lexer? rules (PygmentsLexData.tableRetypes.getD i #[])

private def tables : Thunk (Array (Option Lexer)) := Thunk.mk decoded

/-- Table lexer `i`, `none` where its table does not decode. -/
public def lexer? (i : Nat) : Option Lexer := tables.get.getD i none

end LeanTex.Core.Highlight.Table
