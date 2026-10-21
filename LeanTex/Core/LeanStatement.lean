module

public import LeanTex.Core.LeanFacts
public import LeanTex.Core.LeanNotation
public import LeanTex.Core.Parse

/-! # A Lean statement as mathematics

A declaration's elaborated type through the one notation table, a line free to break inside it. -/

namespace LeanTex.Core.LeanStatement

open LeanTex.Core.Parse LeanTex.Core.LeanFacts LeanTex.Core.LeanNotation

/-- What the renderer reads a constant by: its leading binders, the one its field notation reads
the receiver from, and the name it shows as. -/
public structure Lookup where
  binders : String → Option (Array Binder)
  field : String → Option Nat := fun _ => none
  shown : String → String
  collectionFirst : Bool

/-- A rendered term: its mathematics, its precedence, the binder group it opens with, and the
formulas it sets as where a line may break after each operator of its top-level chain. -/
public structure Rendered where
  math : Array Math
  prec : Nat
  /-- The names, the type and the rest of a leading `∀ names : type, rest`. -/
  group : Option (Array (Array Math) × Array Math × Array Math) := none
  /-- The formulas, none for a term that sets as one. -/
  chain : List (Array Math) := []
  /-- Its elements, where it is a list literal. -/
  elems : Option (List (Array Math)) := none
  deriving Inhabited

/-- The precedence of an atom or anything delimited. -/
public def atomPrec : Nat := 100

/-- The precedence of an application `f x`, tighter than any operator's. -/
public def appPrec : Nat := 90

private def subscriptDigit? (c : Char) : Option Char :=
  if 0x2080 ≤ c.val && c.val ≤ 0x2089 then some (Char.ofNat (c.toNat - 0x2080 + '0'.toNat)) else none

/-- Whether mathematics sets a name's character as written: ASCII letters and digits, Greek, and
a few marks. -/
private def plain (c : Char) : Bool :=
  c.isAlphanum || (0x0391 ≤ c.val && c.val ≤ 0x03C9) || c == '\'' || c == '.' || c == '!' ||
    c == '?'

/-- The control that spells a character TeX reserves: in mathematics, only the underscore a name
may hold; in text, every one, as a text symbol where it has a name. -/
private def reserved? (text : Bool) (c : Char) : Option MathCtrl :=
  match text, c with
  | false, '_' => some .underscore
  | false, _ => none
  | true, '_' => some .textunderscore
  | true, '{' => some .textbraceleft
  | true, '}' => some .textbraceright
  | true, '$' => some .textdollar
  | true, '~' => some .tilde
  | true, '^' => some .caret
  | true, '\\' => some .backslash
  | true, '#' => some .hash
  | true, '%' => some .percent
  | true, '&' => some .amp
  | true, _ => none

/-- A name's or a text's characters: each run of other characters a word, each one TeX reserves a
control. -/
private def spelled (text : Bool) (cs : List Char) : Array Math := Id.run do
  let mut out : Array Math := #[]
  let mut cur := ""
  for c in cs do
    match reserved? text c with
    | some k =>
      unless cur.isEmpty do out := out.push (.word cur)
      cur := ""
      out := out.push (.ctrl k)
    | none => cur := cur.push c
  unless cur.isEmpty do out := out.push (.word cur)
  return out

/-- A name as what sets as written and its trailing subscript digits, when the rest is plain. -/
private def nameParts? (s : String) : Option (List Char × List Char) :=
  let cs := s.toList
  let subs := (cs.reverse.takeWhile fun c => (subscriptDigit? c).isSome).reverse
  let base := cs.take (cs.length - subs.length)
  if !base.isEmpty && base.all fun c => plain c || c == '_' then
    some (base, subs.filterMap subscriptDigit?)
  else none

private def withSubscript (base : Array Math) (digits : List Char) : Array Math :=
  if digits.isEmpty then base else base.push (.sub [.word (String.ofList digits)])

/-- A name set as text, for one mathematics cannot spell. -/
private def textName (s : String) : Array Math := #[.ctrl .text, .arg (spelled true s.toList).toList]

/-- A bound variable's name as one italic word of the text face, its trailing subscript digits a
subscript. -/
public def varMath (s : String) : Array Math :=
  match nameParts? s with
  | some (base, subs) => withSubscript #[.ctrl .mathit, .arg (spelled false base).toList] subs
  | none => textName s

/-- The alphabet a constant's name sets in. -/
public def constFace : MathCtrl := .mathrm

/-- A constant's name as one upright word of the text face. -/
public def opMath (s : String) : Array Math :=
  match nameParts? s with
  | some (base, subs) => withSubscript #[.ctrl constFace, .arg (spelled false base).toList] subs
  | none => textName s

private def glyphMath : Glyph → Array Math
  | .ctrl c => #[.ctrl c]
  | .word w => #[.word w]
  | .bb l => #[.ctrl .mathbb, .arg [.word l]]
  | .numeral => #[]

private def atom (math : Array Math) : Rendered := { math, prec := atomPrec }

private def paren (r : Rendered) (min : Nat) : Array Math :=
  if r.prec ≥ min then r.math else ((#[.word "("] : Array Math) ++ r.math).push (.word ")")

/-- An operator a formula ends on, spaced as an operator against an empty operand. -/
private def opEnd (g : Array Math) : Array Math := g.push (.arg [])

/-- Formulas with `tail` after the last. -/
private def endWith (tail : Array Math) : List (Array Math) → List (Array Math)
  | [] => [tail]
  | [x] => [x ++ tail]
  | x :: rest => x :: endWith tail rest

/-- Formulas between `opening` and `closing`, the one before the first and the other after the
last. -/
private def bracketed (opening closing : String) : List (Array Math) → List (Array Math)
  | [] => [#[.word opening, .word closing]]
  | x :: rest => endWith #[.word closing] ((#[.word opening] ++ x) :: rest)

/-- The formulas a rendered term sets as where it stands at precedence `min`: its chain, in
parentheses where it needs them there, else itself. -/
private def piecesAt (r : Rendered) (min : Nat) : List (Array Math) :=
  if r.chain.isEmpty then [paren r min]
  else if r.prec ≥ min then r.chain else bracketed "(" ")" r.chain

/-- A binary operator's formulas: its left side's, the operator ending the last, then its right
side's. -/
private def chainOf (left : List (Array Math)) (g : Array Math) (right : List (Array Math)) :
    List (Array Math) :=
  (endWith (opEnd g) left).append right

/-- A hypothesis its conclusion names: `(h : P)`. -/
private def named (n : String) (r : Rendered) : Array Math :=
  ((((#[.word "("] : Array Math) ++ varMath n).push (.word ":")).append r.math).push (.word ")")

/-- Items joined by commas, each appended to `acc`. -/
private def commaJoin (acc : Array Math) : List (Array Math) → Array Math
  | [] => acc
  | [x] => acc ++ x
  | x :: rest => commaJoin ((acc ++ x).push (.word ",")) rest

/-- Formulas each but the last ending on a space. -/
private def spaced : List (Array Math) → List (Array Math)
  | [] => []
  | [x] => [x]
  | x :: rest => x.push (.ctrl .space) :: spaced rest

/-- A head applied to its shown arguments by juxtaposition, `f a b`, each compound argument
parenthesized, a line free to break after each space. -/
private def applied (head : Array Math) (args : List Rendered) : Rendered :=
  if args.isEmpty then atom head
  else
    let parts := args.map (paren · atomPrec)
    { math := parts.foldl (fun acc a => (acc.push (.ctrl .space)).append a) head, prec := appPrec
      chain := spaced (head :: parts) }

/-- A universe level as Lean spells it, parenthesized where it has more than one word. -/
private def levelMath (level : String) : Array Math :=
  if !level.contains ' ' then (if level.all Char.isDigit then opMath level else varMath level)
  else if level.startsWith "(" && level.endsWith ")" then textName level
  else ((#[.word "("] : Array Math) ++ textName level).push (.word ")")

/-- The level one below `level`, where Lean spells it `ℓ + k` with `k` at least one. -/
private def below? (level : String) : Option String :=
  match level.splitOn " + " with
  | [base, k] =>
    match k.toNat? with
    | some 1 => some base
    | some (m + 2) => some s!"{base} + {m + 1}"
    | _ => none
  | _ => none

/-- A sort as Lean shows it: `Prop`, `Type ℓ` for a level one above `ℓ`, else `Sort ℓ`. -/
private def sortMath (level : String) : Array Math :=
  match level.toNat?, below? level with
  | some 0, _ => opMath "Prop"
  | some 1, _ => opMath "Type"
  | some (n + 1), _ => ((opMath "Type").push (.ctrl .space)).append (opMath (toString n))
  | none, some b => ((opMath "Type").push (.ctrl .space)).append (levelMath b)
  | none, none => ((opMath "Sort").push (.ctrl .space)).append (levelMath level)

/-- The explicit arguments among a constant's arguments, by its leading binders. -/
public def shownArgs {β : Type} (lk : Lookup) (c : String) (args : List β) : List β :=
  match lk.binders c with
  | some bs => (args.zipIdx.filter fun (_, k) => (bs[k]?.map Binder.shows).getD true).map (·.1)
  | none => args

/-- The explicit arguments among a constant's arguments but the one at `i`. -/
public def otherArgs {β : Type} (lk : Lookup) (c : String) (i : Nat) (args : List β) : List β :=
  let shows (k : Nat) : Bool := match lk.binders c with
    | some bs => (bs[k]?.map Binder.shows).getD true
    | none => true
  (args.zipIdx.filter fun (_, k) => k != i && shows k).map (·.1)

/-- A constant's field notation on its receiver, `x.f`, the field its name's last part. -/
private def fieldHead (recv : Rendered) (c : String) : Array Math :=
  ((paren recv atomPrec).push (.word ".")).append (opMath ((c.splitOn ".").getLastD c))

/-- An operand's formulas beside an operator: its chain where it is an operator's, an application
whole. -/
private def sidePieces (r : Rendered) (min : Nat) : List (Array Math) :=
  if r.prec == appPrec then [paren r min] else piecesAt r min

/-- A binder group `∀ names : type,`. -/
public def forallHead (names : Array (Array Math)) (type : Array Math) : Array Math :=
  ((commaJoin #[.ctrl .forAll] names.toList).push (.word ":")).append type |>.push (.word ",")

/-- `a ⋆ b` from its two sides and glyph. -/
private def around (left : Array Math) (g : Glyph) (right : Array Math) : Array Math :=
  (left.append (glyphMath g)).append right

mutual

/-- A term as mathematics under the bound names `ctx`, innermost first. -/
public def render (lk : Lookup) (ctx : List String) : Term → Rendered
  | .apps h args =>
    match renderBinder? lk ctx h args with
    | some r => r
    | none => renderApps lk ctx h (renderList lk ctx #[] args).toList
  | .applied f args => applied (paren (render lk ctx f) atomPrec) (renderList lk ctx #[] args).toList
  | .pi n b prop t body =>
    let inner := render lk (n :: ctx) body
    let after := sidePieces inner 25
    if b == .inst || !body.reads 0 then
      let hyp := render lk ctx t
      { math := around (paren hyp 26) (.ctrl .to) (paren inner 25), prec := 25
        chain := chainOf (sidePieces hyp 26) #[.ctrl .to] after }
    else if prop then
      let hyp := named n (render lk ctx t)
      { math := (hyp.push (.ctrl .to)).append (paren inner 25), prec := 25
        chain := chainOf [hyp] #[.ctrl .to] after }
    else
      let ty := paren (render lk ctx t) 51
      let me := varMath n
      let fresh : Rendered :=
        { math := (forallHead #[me] ty).append inner.math, prec := 0,
          group := some (#[me], ty, inner.math) }
      match inner.group with
      | some (names, ty', rest) =>
        if ty' == ty then
          { math := (forallHead (#[me] ++ names) ty).append rest, prec := 0
            group := some (#[me] ++ names, ty, rest) }
        else fresh
      | none => fresh
  | .lam n _ _ body =>
    let bound := if body.reads 0 then varMath n else #[.ctrl .underscore]
    { math := (bound.push (.ctrl .mapsto)).append (render lk (n :: ctx) body).math, prec := 0 }
  | .letE n _ v body =>
    let value := (render lk ctx v).math
    let rest := (render lk (n :: ctx) body).math
    { math := ((((opMath "let").append (varMath n)).push (.word ":")).push (.word "=")
        |>.append value |>.push (.word ";") |>.append rest), prec := 0 }
  | .proj _ i e => atom (((paren (render lk ctx e) atomPrec).push (.word ".")).append
      (opMath (toString (i + 1))))

public def renderList (lk : Lookup) (ctx : List String) (acc : Array Rendered) :
    List Term → Array Rendered
  | [] => acc
  | t :: rest => renderList lk ctx (acc.push (render lk ctx t)) rest

/-- A list literal `[a, b]` of the elements of a list's constructors applied to their explicit
arguments, a line free to break after each comma. -/
private def listLit (c : String) (shown : List Rendered) : Option Rendered :=
  let lit (es : List (Array Math)) : Rendered :=
    { math := (commaJoin #[.word "["] es).push (.word "]"), prec := atomPrec, elems := some es
      chain := bracketed "[" "]" (es.zipIdx.map fun (e, i) =>
        if i + 1 < es.length then e.push (.word ",") else e) }
  match c, shown with
  | "List.nil", [] => some (lit [])
  | "List.cons", [x, xs] => xs.elems.map fun es => lit (x.math :: es)
  | _, _ => none

/-- A binder notation `⋆ x : T, P` over its last argument, when that is `fun x : T => P`. -/
public def renderBinder? (lk : Lookup) (ctx : List String) (h : Head) :
    List Term → Option Rendered
  | [] => none
  | [.lam n _ t body] =>
    match h with
    | .const c =>
      match shownOf c with
      | .notation g .binder =>
        let ty := paren (render lk ctx t) 51
        let rest := (render lk (n :: ctx) body).math
        some { math := ((glyphMath g).append (varMath n) |>.push (.word ":") |>.append ty
          |>.push (.word ",") |>.append rest), prec := 0 }
      | .notation _ _ | .name _ => none
    | .bvar _ | .sort _ | .nat _ | .str _ | .other _ => none
  | [_] => none
  | _ :: rest => renderBinder? lk ctx h rest

/-- A head applied to its rendered arguments, through the head's notation when it has one. -/
public def renderApps (lk : Lookup) (ctx : List String) (h : Head) (args : List Rendered) :
    Rendered :=
  match h with
  | .bvar i => applied (varMath (ctx[i]?.getD "?")) args
  | .sort l => applied (sortMath l) args
  | .nat n => applied (opMath (toString n)) args
  | .str s => applied (textName s.quote) args
  | .other w => applied (opMath w) args
  | .const c =>
    let shown := shownArgs lk c args
    match listLit c shown with
    | some r => r
    | none =>
    match shownOf c, shown with
    | .notation g (.infix p a), [x, y] =>
      let (l, r) := match a with
        | .left => (p, p + 1)
        | .right => (p + 1, p)
        | .none => (p + 1, p + 1)
      { math := around (paren x l) g (paren y r), prec := p
        chain := chainOf (sidePieces x l) (glyphMath g) (sidePieces y r) }
    | .notation g (.swapped p), [first, second] =>
      let (coll, elem) := if lk.collectionFirst then (first, second) else (second, first)
      { math := around (paren elem (p + 1)) g (paren coll (p + 1)), prec := p
        chain := chainOf (sidePieces elem (p + 1)) (glyphMath g) (sidePieces coll (p + 1)) }
    | .notation g (.prefix p), [x] => { math := (glyphMath g).append (paren x (p + 1)), prec := p }
    | .notation _ .power, [x, y] =>
      { math := (paren x atomPrec).push (.sup y.math.toList), prec := 75 }
    | .notation g .constant, [] => atom (glyphMath g)
    | .notation _ .numeral, [x] => x
    | .notation _ _, _ => applied (opMath (lk.shown c)) shown
    | .name _, _ =>
      match lk.field c with
      | some i =>
        match args[i]? with
        | some recv => applied (fieldHead recv c) (otherArgs lk c i args)
        | none => applied (opMath (lk.shown c)) shown
      | none => applied (opMath (lk.shown c)) shown

end

/-- A term's formulas where it stands alone, a line free to break between them. -/
public def formulasOf (lk : Lookup) (ctx : List String) (t : Term) : List (Array Math) :=
  piecesAt (render lk ctx t) 0

/-- A binder's type as one formula, parenthesized as a binder sets it. -/
public def boundOf (lk : Lookup) (ctx : List String) (t : Term) : Array Math :=
  paren (render lk ctx t) 51

/-- A piece of a statement's top level: one quantified variable and its type, a quantifier's head,
which a word space follows, or a formula, which a line may break after. -/
public inductive Chunk where
  | binder (name type : Array Math)
  | head (math : Array Math)
  | formula (math : Array Math)
  deriving Inhabited

/-- A statement's top level: its quantifiers, each hypothesis an implication, a proposition's or an
instance's binder takes, an existential's head, then its conclusion's formulas, a looser connective
after an arrow parenthesized; on the `spine` an implicit binder the rest reads hides. -/
public def chunksOf (lk : Lookup) (ctx : List String) (afterArrow spine : Bool) : Term → List Chunk
  | .pi n b prop ty body =>
    let hyp := render lk ctx ty
    if prop && body.reads 0 then
      .formula (opEnd ((named n hyp).push (.ctrl .to))) :: chunksOf lk (n :: ctx) true spine body
    else if spine && !prop && (b == .implicit || b == .strict) && body.reads 0 then
      chunksOf lk (n :: ctx) afterArrow spine body
    else if prop || b == .inst || !body.reads 0 then
      let rest := chunksOf lk (n :: ctx) true spine body
      ((endWith (opEnd #[.ctrl .to]) (sidePieces hyp 26)).map Chunk.formula).append rest
    else .binder (varMath n) (paren hyp 51) :: chunksOf lk (n :: ctx) false spine body
  | .apps (.const c) [ty, .lam n b dom body] =>
    match shownOf c with
    | .notation g .binder =>
      let opening := (((glyphMath g).append (varMath n)).push (.word ":")).append
        (paren (render lk ctx dom) 51) |>.push (.word ",")
      .head opening :: chunksOf lk (n :: ctx) false false body
    | .notation _ _ | .name _ =>
      let t := Term.apps (.const c) [ty, .lam n b dom body]
      (piecesAt (render lk ctx t) (if afterArrow then 25 else 0)).map Chunk.formula
  | t => (piecesAt (render lk ctx t) (if afterArrow then 25 else 0)).map Chunk.formula

/-- A group's formulas: `∀` and each name but the last with its comma, a line free to break after
each, then the last name `: T,`, which a word space follows. -/
private def groupFormulas (names : Array (Array Math)) (type : Array Math) :
    Array (Array Math × Bool) :=
  names.zipIdx.map fun (n, i) =>
    let lead : Array Math := if i == 0 then #[.ctrl .forAll] else #[]
    if i + 1 == names.size then ((((lead ++ n).push (.word ":")).append type).push (.word ","), true)
    else (opEnd ((lead ++ n).push (.word ",")), false)

/-- A statement's chunks as formulas after `acc`, each with whether a word space follows it:
consecutive quantified variables of one type as one group `∀ a, b : T,`. -/
public def mergeBinders (acc : Array (Array Math × Bool)) : List Chunk → Array (Array Math × Bool)
  | [] => acc
  | .formula m :: rest => mergeBinders (acc.push (m, false)) rest
  | .head m :: rest => mergeBinders (acc.push (m, true)) rest
  | .binder n t :: rest =>
    let same := rest.takeWhile fun
      | .binder _ t' => t' == t
      | .head _ | .formula _ => false
    let names := #[n] ++ (same.filterMap fun
      | .binder n' _ => some n'
      | .head _ | .formula _ => none).toArray
    mergeBinders (acc ++ groupFormulas names t) (rest.drop same.length)
termination_by l => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- The namespaces a declaration stands in, innermost first, each with its trailing dot. -/
private def enclosing (decl : String) : List String :=
  let parts := (decl.splitOn ".").dropLast
  (List.range parts.length).reverse.map fun k => String.intercalate "." (parts.take (k + 1)) ++ "."

/-- A constant's name inside a declaration: without the innermost namespace of the declaration's
that prefixes it. -/
private def relative (decl c : String) : String :=
  match (enclosing decl).find? (c.startsWith ·) with
  | some ns => (c.drop ns.length).toString
  | none => c

/-- The names a statement's constants show as: each relative to the declaration, unless two
would show alike, when both keep their full names. -/
public def shownNames (decl : String) (consts : Array String) (c : String) : String :=
  let r := relative decl c
  if consts.any fun d => d != c && (relative decl d == r || d == r) then c else r

/-- What a declaration's statement reads its constants by, from the file's facts. -/
public def lookupOf (facts : Facts) (d : Decl) (type : Term) : Lookup :=
  { binders := fun c => (facts.binders.find? (·.1 == c)).map (·.2)
    field := fun c => (facts.fields.find? (·.1 == c)).map (·.2)
    shown := shownNames d.name (type.consts #[])
    collectionFirst := facts.collectionFirst }

/-- A formula without the space it ends on, and whether it ended on one. -/
public def unspaced (m : Array Math) : Array Math × Bool :=
  if m.back? == some (.ctrl .space) then (m.pop, true) else (m, false)

/-- A declaration's statement as formulas, each with whether a word space, rather than a bare
break, follows it: a declaration whose type is no proposition opens on its name and a colon. -/
public def statementMath (facts : Facts) (d : Decl) (type : Term) : Array (Array Math × Bool) :=
  let lk := lookupOf facts d type
  let opening : Array (Array Math × Bool) := if d.prop then #[] else
    #[((opMath ((d.name.splitOn ".").getLastD d.name)).push (.word ":"), true)]
  (mergeBinders opening (chunksOf lk [] false true type)).map fun (m, spaced) =>
    ((unspaced m).1, spaced || (unspaced m).2)

mutual

/-- One piece of mathematics as the surface's raws, after `acc`. -/
@[expose] public def Math.pushRaws (pos : Pos) (acc : Array Raw) : Math → Array Raw
  | .word s => acc.push (.word s pos)
  | .ctrl c => acc.push (.ctrl c.name pos)
  | .arg body => acc.push (.group (Math.listRaws pos #[] body) pos)
  | .sup body => (acc.push (.sym '^' pos)).push (.group (Math.listRaws pos #[] body) pos)
  | .sub body => (acc.push (.sym '_' pos)).push (.group (Math.listRaws pos #[] body) pos)

@[expose] public def Math.listRaws (pos : Pos) (acc : Array Raw) : List Math → Array Raw
  | [] => acc
  | m :: rest => Math.listRaws pos (Math.pushRaws pos acc m) rest

end

end LeanTex.Core.LeanStatement
