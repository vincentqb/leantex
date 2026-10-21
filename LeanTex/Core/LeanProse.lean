module

public import LeanTex.Core.LeanStatement

/-! # A Lean statement in words

A controlled English whose parser reads its renderer back, and a declaration's type said in it. -/

namespace LeanTex.Core.LeanProse

open LeanTex.Core

/-- A binder group: the names it binds and what bounds them, a type, or the relation a binder
predicate such as `x ∈ S` writes, which shows the name itself. -/
public structure Group (α : Type) where
  names : List α
  bound : α
  pred : Bool
  deriving BEq, Repr

/-- A token: a word, an opaque leaf (a formula) the grammar never inspects, a binder group, a
block's bounds, which a page sets as lines indented one step deeper than the line before, or a list
item's start, which a page sets as a numbered item. -/
public inductive Tok (α : Type) where
  | w (s : String)
  | leaf (a : α)
  | bind (g : Group α)
  | indent
  | dedent
  | item
  deriving BEq, Repr

/-- A template part: a word, or the slot `#k` of the `k`-th argument, counted from 1. -/
public inductive Part where
  | word (s : String)
  | slot (k : Nat)
  deriving DecidableEq, Repr

public structure Template where
  parts : List Part
  deriving DecidableEq, Repr

/-- A term: a leaf, or a phrase template applied to leaves. -/
public inductive Term (α : Type) where
  | leaf (a : α)
  | phrase (t : Template) (args : List α)
  deriving BEq, Repr

/-- A quantifier's groups, the first and any more, as in "every x : T" or "all x : T and y ∈ S". -/
public structure Binder (α : Type) where
  first : Group α
  more : List (Group α)
  deriving BEq, Repr

public inductive Stmt (α : Type) where
  | all (b : Binder α) (body : Stmt α)
  | ex (b : Binder α) (body : Stmt α)
  | imp (hyp concl : Stmt α)
  | conj (a b : Stmt α)
  | disj (a b : Stmt α)
  | iff (a b : Stmt α)
  | tfae (items : Stmt α)
  | neg (a : Stmt α)
  | rel (t : Template) (args : List (Term α))
  | atom (x : α)
  deriving BEq, Repr

/-- Relation templates, which open with a slot, and phrase templates, which open with a word. -/
public structure Lexicon where
  rels : List Template
  phrases : List Template
  deriving Repr

/-- A leaf: a formula, as the pieces a line may break between. -/
public abbrev Leaf := List (Array LeanNotation.Math)

/-- The templates statements are said through, each with the constant it says. -/
public structure Table where
  rels : List (String × Template)
  phrases : List (String × Template)
  deriving Repr, Inhabited

/-- Why a statement is not said in words. -/
public inductive Unsaid where
  /-- A hypothesis the rest of the statement names. -/
  | named (name : String)
  /-- A local definition. -/
  | local (name : String)
  /-- A function where a proposition stands. -/
  | function
  /-- A declaration whose type is no proposition. -/
  | notProp
  deriving Repr, BEq, Inhabited

/-- Why a phrase a directive declares is refused. -/
public inductive Refusal where
  /-- It names no constant a statement names. -/
  | unknown
  /-- It names more than one constant. -/
  | ambiguous
  /-- Its constant has a phrase already. -/
  | twice
  /-- It is no template the grammar reads. -/
  | shape
  /-- Its slots are not its constant's explicit arguments, by their counts. -/
  | arity (slots args : Nat)
  /-- Its words open as another template's do. -/
  | clash
  /-- It names a connective or a quantifier, which the grammar says in its own words. -/
  | connective
  /-- No sentence the page sets uses it. -/
  | unused
  /-- The page says no statement in words, on a Lean file or another. -/
  | unshown (lean : Bool)
  deriving Repr, BEq, Inhabited

/-- What taking a directive's phrases gathers: the table, the constants given a phrase, each
refused phrase and why, and each taken one by name with its template. -/
public structure Declared where
  table : Table
  taken : List String
  refused : Array (String × Refusal)
  phrases : Array (String × Template)
  deriving Repr, Inhabited

/-- The words a list of parts opens with. -/
private def lead : List Part → List String
  | .word s :: ps => s :: lead ps
  | _ => []

private def slotsOf : List Part → List Nat
  | [] => []
  | .word _ :: ps => slotsOf ps
  | .slot k :: ps => k :: slotsOf ps

namespace Template

public def slots (t : Template) : List Nat := slotsOf t.parts

public def arity (t : Template) : Nat := t.slots.length

/-- The slots are `#1` to `#n`, each once. -/
public def wf (t : Template) : Bool :=
  (List.range' 1 t.arity).all t.slots.contains && t.slots.all fun k => 1 ≤ k && k ≤ t.arity

/-- The words after a relation's opening slot, which select the relation. -/
public def relLead (t : Template) : List String :=
  match t.parts with
  | .slot _ :: ps => lead ps
  | _ => []

/-- Reads space-separated words and slots `#k`. -/
public def ofString (s : String) : Template :=
  ⟨(s.splitOn " ").filterMap fun x => if x.isEmpty then none else some (match x.toList with
    | '#' :: ds => ((String.ofList ds).toNat?).elim (.word x) .slot
    | _ => .word x)⟩

end Template

/-- The words that may follow an operand, so no relation's lead begins with one. -/
private def stops : List String := ["and", "or", ",", "if", "."]

/-- Whether a word closes a clause and sets inside a block it follows: a comma or a full stop. -/
private def closing (s : String) : Bool := s == "," || s == "."

/-- The words an equivalence set as a list of its two sides opens with, one token. -/
public def equivWords : String := "the following are equivalent"

/-- The token a list of three or more equivalent statements opens with, set as `equivWords` say. -/
public def tfaeKey : String := "the following are equivalent:3"

/-- The words that open a statement or an operand, so no phrase begins with one. -/
private def opens : List String := ["for", "there", "if", equivWords, tfaeKey, "both", "either", "it"]

private def isRel (t : Template) : Bool :=
  match t.parts with
  | .slot _ :: ps => match lead ps with
    | s :: _ => !stops.contains s
    | [] => false
  | _ => false

private def isPhrase (t : Template) : Bool :=
  match t.parts with
  | .word s :: _ => !opens.contains s && !(equivWords.splitOn " ").isPrefixOf (lead t.parts)
  | _ => false

/-- No list is a prefix of another, equal ones included. -/
private def prefixFree : List (List String) → Bool
  | [] => true
  | a :: l => l.all (fun b => !a.isPrefixOf b && !b.isPrefixOf a) && prefixFree l

/-- Every template is well formed and of its kind, and the leads of each kind are prefix-free. -/
public def Lexicon.wf (lex : Lexicon) : Bool :=
  lex.rels.all (fun t => t.wf && isRel t) && lex.phrases.all (fun t => t.wf && isPhrase t) &&
    prefixFree (lex.rels.map Template.relLead) && prefixFree (lex.phrases.map (lead ·.parts))

variable {α : Type}

/-- A phrase's template is the lexicon's, with as many arguments as slots. -/
public def Term.ok (lex : Lexicon) : Term α → Bool
  | .leaf _ => true
  | .phrase p args => lex.phrases.contains p && args.length == p.arity

/-- Every template used is the lexicon's, with as many arguments as slots, and a list of equivalent
statements three or more. -/
public def Stmt.ok (lex : Lexicon) : Stmt α → Bool
  | .all _ s | .ex _ s | .neg s => s.ok lex
  | .imp a b | .conj a b | .disj a b | .iff a b => a.ok lex && b.ok lex
  | .tfae s => s.ok lex && (s matches .conj _ (.conj ..))
  | .rel t args => lex.rels.contains t && args.length == t.arity && args.all (·.ok lex)
  | .atom _ => true

/-- Words before `rest`. -/
private def wordsTo (l : List String) (rest : List (Tok α)) : List (Tok α) :=
  l.foldr (fun s r => .w s :: r) rest

/-- The `k`-th argument, counted from 1. -/
private def arg? {β : Type} (args : List β) : Nat → Option β
  | 0 => none
  | k + 1 => args[k]?

/-- A template's tokens before `rest`, each slot filled with its argument's. -/
private def fillTo {β : Type} (f : β → List (Tok α) → List (Tok α)) (args : List β) :
    List Part → List (Tok α) → List (Tok α)
  | [], rest => rest
  | .word s :: ps, rest => .w s :: fillTo f args ps rest
  | .slot k :: ps, rest => match arg? args k with
    | some x => f x (fillTo f args ps rest)
    | none => fillTo f args ps rest

/-- A term's tokens before `rest`. -/
public def Term.renderTo : Term α → List (Tok α) → List (Tok α)
  | .leaf a, rest => .leaf a :: rest
  | .phrase t args, rest => fillTo (fun a r => .leaf a :: r) args t.parts rest

public def Term.render (x : Term α) : List (Tok α) := x.renderTo []

/-- Binder groups before `rest`: one, or several with commas between and "and" before the last. -/
private def groupToks : Group α → List (Group α) → List (Tok α) → List (Tok α)
  | g, [], rest => .bind g :: rest
  | g, [h], rest => .bind g :: .w "and" :: .bind h :: rest
  | g, h :: k :: r, rest => .bind g :: .w "," :: groupToks h (k :: r) rest

/-- A binder's tokens before `rest`. -/
private def Binder.renderTo (b : Binder α) (rest : List (Tok α)) : List (Tok α) :=
  groupToks b.first b.more rest

/-- Whether a quantifier binds more than one name, so its words are plural. -/
public def Binder.many (b : Binder α) : Bool := !b.more.isEmpty || 2 ≤ b.first.names.length

/-- Whether a template's words hold one a connective splits a sentence at. -/
private def Template.splits (t : Template) : Bool :=
  t.parts.any fun
    | .word w => ["and", "or", "if", "then", "both", "either"].contains w
    | .slot _ => false

private def Term.splits : Term α → Bool
  | .leaf _ => false
  | .phrase t _ => t.splits

/-- How loosely a statement binds: 0 atomic, 1 delimited by its own words, 2 the rest, a relation
whose words hold a connective's among them. -/
public def Stmt.prec : Stmt α → Nat
  | .rel t args => if t.splits || args.any Term.splits then 2 else 0
  | .atom _ => 0
  | .neg _ | .conj .. | .disj .. => 1
  | .all .. | .ex .. | .imp .. | .iff .. | .tfae _ => 2

private def Stmt.isImp : Stmt α → Bool
  | .imp .. => true
  | .all .. | .ex .. | .conj .. | .disj .. | .iff .. | .tfae _ | .neg _ | .rel .. | .atom _ => false

private def Stmt.isIff : Stmt α → Bool
  | .iff .. => true
  | .all .. | .ex .. | .imp .. | .conj .. | .disj .. | .tfae _ | .neg _ | .rel .. | .atom _ => false

/-- Whether a conjunction a scope holds sets inline, "A and B": both its sides are atomic. -/
public def inline (a b : Stmt α) : Bool := a.prec == 0 && b.prec == 0

/-- Whether a statement a scope holds sets as a list of items: a conjunction not set inline. -/
public def Stmt.isList : Stmt α → Bool
  | .conj a b => !inline a b
  | .all .. | .ex .. | .imp .. | .disj .. | .iff .. | .tfae _ | .neg _ | .rel .. | .atom _ => false

/-- What may follow a statement, ending its extent: the end, a block's end, a list item's start, the
closing word a block sets inside it, or the full stop. -/
private def followsStmt : List (Tok α) → Bool
  | [] | .dedent :: _ | .item :: _ => true
  | .w s :: rest => match rest with
    | [] => s == "."
    | .dedent :: _ => closing s
    | .w _ :: _ | .leaf _ :: _ | .bind _ :: _ | .indent :: _ | .item :: _ => false
  | .leaf _ :: _ | .bind _ :: _ | .indent :: _ => false

/-- What may follow an operand: what may follow a statement, or a word in `stops`. -/
private def followsOpnd : List (Tok α) → Bool
  | [] | .dedent :: _ | .item :: _ => true
  | .w s :: _ => stops.contains s
  | .leaf _ :: _ | .bind _ :: _ | .indent :: _ => false

/-- Tokens `f` before `rest` as a block, a closing word `rest` opens with set inside it. -/
private def blockWith (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) : List (Tok α) :=
  match rest with
  | .w s :: r => if closing s then .indent :: f (.w s :: .dedent :: r) else .indent :: f (.dedent :: rest)
  | [] | .leaf _ :: _ | .bind _ :: _ | .indent :: _ | .dedent :: _ | .item :: _ =>
    .indent :: f (.dedent :: rest)

/-- An operand's tokens `f` before `rest`: bare up to precedence `k`, or where nothing follows it in
its extent and it is no equivalence, else a block. -/
private def wrapWith (k : Nat) (s : Stmt α) (f : List (Tok α) → List (Tok α))
    (rest : List (Tok α)) : List (Tok α) :=
  if s.prec ≤ k || (!s.isIff && followsStmt rest) then f rest else blockWith f rest

/-- How loosely an equivalence's left side may bind and stand bare: a conjunction, its "both"
opening it, else atomic, so "it is not the case that" or "either" never reads as covering it. -/
public def Stmt.leftK : Stmt α → Nat
  | .conj .. => 1
  | .all .. | .ex .. | .imp .. | .disj .. | .iff .. | .tfae _ | .neg _ | .rel .. | .atom _ => 0

/-- An equivalence's right side: a block where its left side is one and it is no atom, the two
standing alike, else an operand. -/
private def iffRight (a b : Stmt α) (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) :
    List (Tok α) :=
  if a.leftK < a.prec && 0 < b.prec then blockWith f rest else wrapWith 1 b f rest

/-- What follows a hypothesis: the next one of a curried implication, or its conclusion. -/
private def chainWith (c : Stmt α) (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) :
    List (Tok α) :=
  if c.isImp then .w "and" :: (f rest).tail else .w "," :: .w "then" :: f rest

/-- A quantifier's opening words: singular before one name, plural before several. -/
private def allWords (b : Binder α) : List String :=
  ["for", if b.many then "all" else "every"]

private def exWords (b : Binder α) : List String :=
  ["there", if b.many then "are" else "is"]

/-- Where a statement stands: an operand its words delimit, a scope running to its extent's end, a
lead (the sentence or an item), a list's items from one on, or a scope inside an operand. -/
private inductive Place where
  | operand
  | scope
  | lead
  | item
  | inner
  deriving DecidableEq

/-- Where a statement at `p` sets its scopes: inside an operand, inner ones. -/
private def Place.sub : Place → Place
  | .operand | .inner => .inner
  | .scope | .lead | .item => .scope

/-- The word that closes a quantifier's groups before its body at `q`: a colon before a list, else
a comma. -/
private def sepWord (q : Place) (s : Stmt α) : String := if q = .scope ∧ s.isList then ":" else ","

/-- Tokens opening with a list item's mark where the place is a list's items. -/
private def mark (p : Place) (t : List (Tok α)) : List (Tok α) := if p = .item then .item :: t else t

/-- An equivalence's tokens `fa` and `fb` before `rest`, a block where a scope holds it, so its "if
and only if" never reads as ending the scope. -/
private def iffTo (p : Place) (a b : Stmt α) (fa fb : List (Tok α) → List (Tok α))
    (rest : List (Tok α)) : List (Tok α) :=
  let body := fun r => wrapWith a.leftK a fa (wordsTo ["if", "and", "only", "if"] (iffRight a b fb r))
  if p = .scope ∨ p = .inner then blockWith body rest else body rest

/-- A statement's tokens before `rest`, where it stands at `p`: a conjunction a scope, a lead or an
inner scope holds inline where both sides are atomic, else as a list where no operand holds it, its
items each a lead, and by "both … and" where one does. -/
private def renderTo : Place → Stmt α → List (Tok α) → List (Tok α)
  | p, .all b s, rest =>
    mark p (wordsTo (allWords b) (b.renderTo (.w (sepWord p.sub s) :: renderTo p.sub s rest)))
  | p, .ex b s, rest =>
    mark p (wordsTo (exWords b) (b.renderTo (.w "such" :: .w "that" :: renderTo p.sub s rest)))
  | p, .imp h c, rest =>
    mark p (.w "if" :: wrapWith (if c.isImp then 0 else 1) h (renderTo .operand h)
      (chainWith c (renderTo p.sub c) rest))
  | .operand, .conj a b, rest =>
    .w "both" :: wrapWith 0 a (renderTo .operand a) (.w "and" :: wrapWith 1 b (renderTo .operand b) rest)
  | .item, .conj a b, rest => .item :: renderTo .lead a (renderTo .item b rest)
  | .inner, .conj a b, rest =>
    if inline a b then renderTo .operand a (.w "and" :: renderTo .operand b rest)
    else .w "both" :: wrapWith 0 a (renderTo .operand a)
      (.w "and" :: wrapWith 1 b (renderTo .operand b) rest)
  | _, .conj a b, rest =>
    if inline a b then renderTo .operand a (.w "and" :: renderTo .operand b rest)
    else .indent :: .item :: renderTo .lead a (renderTo .item b (.dedent :: rest))
  | p, .disj a b, rest =>
    mark p (.w "either" :: wrapWith 0 a (renderTo .operand a) (.w "or" :: wrapWith 1 b (renderTo .operand b) rest))
  | p, .iff a b, rest =>
    if p ≠ .operand ∧ p ≠ .inner ∧ a.leftK < a.prec then
      mark p (.w equivWords :: .w ":" :: .indent :: .item ::
        renderTo .lead a (.item :: renderTo .lead b (.dedent :: rest)))
    else mark p (iffTo p a b (renderTo .operand a) (renderTo .operand b) rest)
  | p, .tfae s, rest => mark p (.w tfaeKey :: .w ":" :: .indent :: renderTo .item s (.dedent :: rest))
  | p, .neg a, rest =>
    mark p (wordsTo ["it", "is", "not", "the", "case", "that"] (wrapWith 1 a (renderTo .operand a) rest))
  | p, .rel t args, rest => mark p (fillTo Term.renderTo args t.parts rest)
  | p, .atom x, rest => mark p (.leaf x :: rest)

/-- A statement's sentence: its tokens, closed by a full stop. -/
public def render (s : Stmt α) : List (Tok α) := renderTo .lead s [.w "."]

/-- Whether a token sets against the one before it, with no space: a comma, a colon or a full stop
does. -/
public def Tok.joins : Tok α → Bool
  | .w s => s == "," || s == ":" || s == "."
  | .leaf _ | .bind _ | .indent | .dedent | .item => false

/-- Binder groups: one, or two or more, "and" before the last. -/
private def parseGroups : List (Tok α) → Option (Group α × List (Group α) × List (Tok α))
  | .bind g :: .w "and" :: .bind h :: r => some (g, [h], r)
  | .bind g :: .w "," :: r@(.bind _ :: _) => (parseGroups r).map fun (y, ys, r') => (g, y :: ys, r')
  | .bind g :: r => some (g, [], r)
  | _ => none

private def parseBinder (t : List (Tok α)) : Option (Binder α × List (Tok α)) :=
  (parseGroups t).map fun (g, gs, r) => (⟨g, gs⟩, r)

private def startsWith : List String → List (Tok α) → Bool
  | [], _ => true
  | s :: l, .w s' :: t => s == s' && startsWith l t
  | _ :: _, _ => false

/-- Matches a template's parts, pairing each slot's index with its item. -/
private def matchParts {β : Type} (item : List (Tok α) → Option (β × List (Tok α))) :
    List Part → List (Tok α) → Option (List (Nat × β) × List (Tok α))
  | [], t => some ([], t)
  | .word s :: ps, .w s' :: t => if s = s' then matchParts item ps t else none
  | .word _ :: _, _ => none
  | .slot k :: ps, t => (item t).bind fun (x, t') =>
    (matchParts item ps t').map fun (xs, r) => ((k, x) :: xs, r)

private def gather {β : Type} (g : Nat → Option β) : List Nat → Option (List β)
  | [] => some []
  | k :: ks => match g k, gather g ks with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- A template's arguments in order, from the items its slots matched. -/
private def collect {β : Type} (t : Template) (pairs : List (Nat × β)) : Option (List β) :=
  gather (pairs.lookup ·) (List.range' 1 t.arity)

private def parseLeaf : List (Tok α) → Option (α × List (Tok α))
  | .leaf a :: r => some (a, r)
  | _ => none

/-- A phrase opening with its lead's words after `s`, its slots' leaves after them. -/
private def phraseTail (p : Template) (r : List (Tok α)) : Option (Term α × List (Tok α)) :=
  match p.parts with
  | .word _ :: ps => (matchParts parseLeaf ps r).bind fun (pairs, r') =>
    (collect p pairs).map fun args => (.phrase p args, r')
  | _ => none

public def Term.parse (lex : Lexicon) : List (Tok α) → Option (Term α × List (Tok α))
  | .leaf a :: r => some (.leaf a, r)
  | .w s :: r => (lex.phrases.find? fun p => startsWith (lead p.parts) (.w s :: r)).bind
      fun p => phraseTail p r
  | .bind _ :: _ => none
  | .indent :: _ => none
  | .dedent :: _ => none
  | .item :: _ => none
  | [] => none

/-- The rest of a relation whose opening slot holds `x`. -/
private def relTail (lex : Lexicon) (t : Template) (x : Term α) (r : List (Tok α)) :
    Option (Stmt α × List (Tok α)) :=
  match t.parts with
  | .slot k :: ps => (matchParts (Term.parse lex) ps r).bind fun (pairs, r') =>
    (collect t ((k, x) :: pairs)).map fun args => (.rel t args, r')
  | _ => none

/-- A relation, chosen by the words after its first term, or else a leaf alone. -/
private def parseAtomic (lex : Lexicon) (t : List (Tok α)) : Option (Stmt α × List (Tok α)) :=
  (Term.parse lex t).bind fun (x, r) =>
    match lex.rels.find? (fun tp => startsWith tp.relLead r) with
    | some tp => relTail lex tp x r
    | none => match x with
      | .leaf a => some (.atom a, r)
      | .phrase .. => none

private theorem parseGroups_len (t : List (Tok α)) : ∀ {r : List (Tok α)} {g : Group α}
    {gs : List (Group α)}, parseGroups t = some (g, gs, r) → r.length < t.length := by
  fun_induction parseGroups t <;> intro r g gs h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [List.length_cons]; omega
  · rename_i ih
    obtain ⟨⟨y, ys, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, -, rfl⟩ := h2
    have := ih h1
    simp only [List.length_cons] at this ⊢; omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp
  · simp at h

private theorem parseBinder_len {t r : List (Tok α)} {b : Binder α}
    (h : parseBinder t = some (b, r)) : r.length < t.length := by
  unfold parseBinder at h
  obtain ⟨⟨g, gs, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  exact parseGroups_len t h1
private theorem matchParts_len {β : Type} {item : List (Tok α) → Option (β × List (Tok α))}
    (hi : ∀ t x r, item t = some (x, r) → r.length ≤ t.length) :
    ∀ (ps : List Part) (t : List (Tok α)) {pairs r},
      matchParts item ps t = some (pairs, r) → r.length ≤ t.length
  | [], t, _, _, h => by simp [matchParts] at h; exact h.2 ▸ Nat.le_refl _
  | .word _ :: _, [], _, _, h => by simp [matchParts] at h
  | .word _ :: _, .leaf _ :: _, _, _, h => by simp [matchParts] at h
  | .word s :: ps, .w s' :: t, _, _, h => by
    simp only [matchParts] at h
    split at h
    · have := matchParts_len hi ps t h; simp; omega
    · simp at h
  | .slot _ :: ps, t, _, _, h => by
    simp only [matchParts] at h
    obtain ⟨⟨x, t'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only at h2
    obtain ⟨⟨xs, r'⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at h4
    obtain ⟨-, rfl⟩ := h4
    have := matchParts_len hi ps _ h3
    have := hi _ _ _ h1
    omega

private theorem phraseTail_len {p : Template} {r r' : List (Tok α)} {x : Term α}
    (h : phraseTail p r = some (x, r')) : r'.length ≤ r.length := by
  unfold phraseTail at h
  split at h
  · obtain ⟨⟨pairs, r''⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, -, h3⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at h3
    obtain ⟨-, rfl⟩ := h3
    exact matchParts_len (fun t x r h => by unfold parseLeaf at h; split at h <;> simp_all) _ _ h1
  · simp at h

private theorem Term.parse_len {lex : Lexicon} {t r : List (Tok α)} {x : Term α}
    (h : Term.parse lex t = some (x, r)) : r.length < t.length := by
  unfold Term.parse at h
  split at h
  · simp at h; simp [← h.2]
  · obtain ⟨p, -, h2⟩ := Option.bind_eq_some_iff.mp h
    have := phraseTail_len h2
    simp; omega
  all_goals simp at h

private theorem relTail_len {lex : Lexicon} {tp : Template} {x : Term α} {r r' : List (Tok α)}
    {s : Stmt α} (h : relTail lex tp x r = some (s, r')) : r'.length ≤ r.length := by
  unfold relTail at h
  split at h
  · obtain ⟨⟨pairs, r''⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, -, h3⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at h3
    obtain ⟨-, rfl⟩ := h3
    exact matchParts_len (fun t x r h => Nat.le_of_lt (Term.parse_len h)) _ _ h1
  · simp at h

private theorem parseAtomic_len {lex : Lexicon} {t r : List (Tok α)} {s : Stmt α}
    (h : parseAtomic lex t = some (s, r)) : r.length < t.length := by
  unfold parseAtomic at h
  obtain ⟨⟨x, r'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  have := Term.parse_len h1
  simp only at h2
  cases hf : lex.rels.find? (fun tp => startsWith tp.relLead r') with
  | some tp => rw [hf] at h2; have := relTail_len h2; omega
  | none =>
    rw [hf] at h2
    cases x with
    | leaf a =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h2; obtain ⟨-, rfl⟩ := h2; exact this
    | phrase _ _ => simp at h2

/-- Whether tokens open with a word that opens a statement: a quantifier's, an existential's, "if"
or a listed equivalence's. -/
private def opensStmt : List (Tok α) → Bool
  | .w s :: _ => s == "for" || s == "there" || s == "if" || s == equivWords || s == tfaeKey
  | [] | .leaf _ :: _ | .bind _ :: _ | .indent :: _ | .dedent :: _ | .item :: _ => false

/-- A parse with its remainder, shorter than the input. -/
private abbrev Parsed (α β : Type) (t : List (Tok α)) :=
  Option (β × {r : List (Tok α) // r.length < t.length})

mutual
/-- A statement a quantifier, an existential or "if" opens. -/
private def parseOpened (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match t with
  | .w "for" :: .w q :: t =>
    if q = "every" ∨ q = "all" then
      match h : parseBinder t with
      | some (b, .w s :: r) =>
        if s = "," ∨ s = ":" then (parseStmt lex r).map fun (s, r') =>
          (.all b s, ⟨r'.1, by
            have h1 := parseBinder_len h; have h2 := r'.2
            simp only [List.length_cons] at h1 h2 ⊢; omega⟩)
        else none
      | _ => none
    else none
  | .w "there" :: .w q :: t =>
    if q = "is" ∨ q = "are" then
      match h : parseBinder t with
      | some (b, .w "such" :: .w "that" :: r) => (parseStmt lex r).map fun (s, r') =>
        (.ex b s, ⟨r'.1, by
          have h1 := parseBinder_len h; have h2 := r'.2
          simp only [List.length_cons] at h1 h2 ⊢; omega⟩)
      | _ => none
    else none
  | .w "if" :: t => (parseHyps lex t).map fun (s, r) =>
    (s, ⟨r.1, by have h1 := r.2; simp only [List.length_cons] at h1 ⊢; omega⟩)
  | .w k :: .w ":" :: .indent :: .item :: t =>
    if k = equivWords then
      match parseStmt lex t with
      | some (a, ⟨.item :: r, h⟩) => match parseStmt lex r with
        | some (b, ⟨.dedent :: r', h'⟩) =>
          some (.iff a b, ⟨r', by simp only [List.length_cons] at h h' ⊢; omega⟩)
        | _ => none
      | _ => none
    else if k = tfaeKey then
      match parseSpine lex (.item :: t) with
      | some (s, ⟨.dedent :: r, h⟩) =>
        some (.tfae s, ⟨r, by simp only [List.length_cons] at h ⊢; omega⟩)
      | _ => none
    else none
  | _ => none
termination_by 3 * t.length
decreasing_by
  all_goals try simp only [List.length_cons] at *
  all_goals first
    | omega
    | (have := parseBinder_len h; simp only [List.length_cons] at this; omega)

/-- A statement: one an opening word opens, else an operand, then an equivalence's right side or
an inline conjunction's rest. -/
private def parseStmt (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  if opensStmt t then parseOpened lex t else
    let o := parseOperand lex t
    match o with
    | some (a, ⟨.w "if" :: .w "and" :: .w "only" :: .w "if" :: r, h⟩) =>
      (parseOperand lex r).map fun (b, r') =>
        (.iff a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1; omega⟩)
    | some (a, ⟨.w "and" :: r, h⟩) =>
      (parseStmt lex r).map fun (b, r') =>
        (.conj a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1; omega⟩)
    | _ => o
termination_by 3 * t.length + 2
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)

/-- The hypotheses after "if", then the conclusion. -/
private def parseHyps (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match parseOperand lex t with
  | some (h, ⟨.w "and" :: r, hr⟩) => (parseHyps lex r).map fun (c, r') =>
    (.imp h c, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at hr h1; omega⟩)
  | some (h, ⟨.w "," :: .w "then" :: r, hr⟩) => (parseStmt lex r).map fun (c, r') =>
    (.imp h c, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at hr h1; omega⟩)
  | _ => none
termination_by 3 * t.length + 2
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)

/-- A list's items from one on, each a mark, then a statement. -/
private def parseSpine (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match t with
  | .item :: t => match parseStmt lex t with
    | some (a, ⟨.item :: r, h⟩) => (parseSpine lex (.item :: r)).map fun (b, r') =>
      (.conj a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1 ⊢; omega⟩)
    | o => o.map fun (a, r) => (a, ⟨r.1, by have := r.2; simp only [List.length_cons]; omega⟩)
  | _ => none
termination_by 3 * t.length
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)

private def parseOperand (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match t with
  | .indent :: .item :: t => match parseSpine lex (.item :: t) with
    | some (s, ⟨.dedent :: r, h⟩) => some (s, ⟨r, by simp at h ⊢; omega⟩)
    | _ => none
  | .indent :: t => match parseStmt lex t with
    | some (s, ⟨.dedent :: r, h⟩) => some (s, ⟨r, by simp at h ⊢; omega⟩)
    | some (s, ⟨.w p :: .dedent :: r, h⟩) =>
      if closing p then some (s, ⟨.w p :: r, by simp at h ⊢; omega⟩) else none
    | _ => none
  | .w "both" :: t => match parseOperand lex t with
    | some (a, ⟨.w "and" :: r, h⟩) => (parseOperand lex r).map fun (b, r') =>
      (.conj a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1 ⊢; omega⟩)
    | _ => none
  | .w "either" :: t => match parseOperand lex t with
    | some (a, ⟨.w "or" :: r, h⟩) => (parseOperand lex r).map fun (b, r') =>
      (.disj a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1 ⊢; omega⟩)
    | _ => none
  | .w "it" :: .w "is" :: .w "not" :: .w "the" :: .w "case" :: .w "that" :: t =>
    (parseOperand lex t).map fun (a, r) =>
      (.neg a, ⟨r.1, by have h1 := r.2; simp only [List.length_cons] at h1 ⊢; omega⟩)
  | t => if opensStmt t then parseOpened lex t else match h : parseAtomic lex t with
    | some (s, r) => some (s, ⟨r, parseAtomic_len h⟩)
    | _ => none
termination_by 3 * t.length + 1
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)
end

/-- A sentence's statement: the tokens of one statement, then its full stop. -/
public def parse (lex : Lexicon) (t : List (Tok α)) : Option (Stmt α) :=
  match parseStmt lex t with
  | some (s, ⟨[.w "."], _⟩) => some s
  | _ => none

/-- The slot indices and arguments a template's parts carry. -/
private def pairsOf {β : Type} (args : List β) : List Part → List (Nat × β)
  | [] => []
  | .word _ :: ps => pairsOf args ps
  | .slot k :: ps => match arg? args k with
    | some x => (k, x) :: pairsOf args ps
    | none => pairsOf args ps

private def forget {β : Type} {t : List (Tok α)} (o : Parsed α β t) : Option (β × List (Tok α)) :=
  o.map fun p => (p.1, p.2.1)

private theorem forget_eq {β : Type} {t : List (Tok α)} {o : Parsed α β t} {x : β}
    {r : List (Tok α)} : forget o = some (x, r) ↔ ∃ h, o = some (x, ⟨r, h⟩) := by
  cases o with
  | none => simp [forget]
  | some p =>
    obtain ⟨y, r', h'⟩ := p
    simp only [forget, Option.map_some, Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2 ▸ h', h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩

private theorem startsWith_fillTo {β : Type} (f : β → List (Tok α) → List (Tok α)) (args : List β)
    (ps : List Part) (rest : List (Tok α)) :
    startsWith (lead ps) (fillTo f args ps rest) = true := by
  induction ps with
  | nil => simp [lead, startsWith]
  | cons p ps ih => cases p <;> simp [lead, fillTo, startsWith, ih]

private theorem startsWith_prefix : ∀ (a b : List String) (t : List (Tok α)),
    startsWith a t = true → startsWith b t = true → a.isPrefixOf b = true ∨ b.isPrefixOf a = true
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | x :: a, y :: b, .w s :: t, ha, hb => by
    simp only [startsWith, Bool.and_eq_true, beq_iff_eq] at ha hb
    obtain ⟨rfl, ha⟩ := ha
    obtain ⟨rfl, hb⟩ := hb
    simpa [List.isPrefixOf] using startsWith_prefix a b t ha hb
  | _ :: _, _ :: _, .leaf _ :: _, ha, _ => by simp [startsWith] at ha
  | _ :: _, _ :: _, [], ha, _ => by simp [startsWith] at ha

private theorem prefixFree_split :
    ∀ (l₁ : List (List String)) (b : List String) (l₂ : List (List String)),
    prefixFree (l₁ ++ b :: l₂) = true → ∀ a ∈ l₁, a.isPrefixOf b = false ∧ b.isPrefixOf a = false
  | [], _, _, _, a, ha => by simp at ha
  | c :: l₁, b, l₂, h, a, ha => by
    simp only [List.cons_append, prefixFree, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · simpa using h.1 b (by simp)
    · exact prefixFree_split l₁ b l₂ h.2 a ha

/-- Among templates with prefix-free keys, one whose key opens the input is the one found. -/
private theorem find_unique {key : Template → List String} {L : List Template} {p : Template}
    {t : List (Tok α)} (hpf : prefixFree (L.map key) = true) (hp : p ∈ L)
    (ht : startsWith (key p) t = true) : L.find? (fun q => startsWith (key q) t) = some p := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hp
  have hsplit := prefixFree_split (pre.map key) (key p) (post.map key) (by simpa using hpf)
  have hnone : pre.find? (fun q => startsWith (key q) t) = none := by
    rw [List.find?_eq_none]
    intro q hq hqt
    have := hsplit (key q) (List.mem_map_of_mem hq)
    rcases startsWith_prefix _ _ t hqt ht with h | h <;> simp_all
  simp [List.find?_append, hnone, ht]

private theorem arg?_mem {β : Type} {args : List β} {k : Nat} {x : β} (h : arg? args k = some x) :
    x ∈ args := by
  cases k with
  | zero => simp [arg?] at h
  | succ k => exact List.mem_of_getElem? h

private theorem matchParts_fillTo {β : Type} {item : List (Tok α) → Option (β × List (Tok α))}
    {f : β → List (Tok α) → List (Tok α)} {args : List β}
    (hi : ∀ x ∈ args, ∀ more, item (f x more) = some (x, more)) (rest : List (Tok α)) :
    ∀ ps : List Part, (∀ k ∈ slotsOf ps, (arg? args k).isSome) →
      matchParts item ps (fillTo f args ps rest) = some (pairsOf args ps, rest)
  | [], _ => by simp [fillTo, matchParts, pairsOf]
  | .word s :: ps, hk => by
    simp only [fillTo, matchParts, ↓reduceIte, pairsOf]
    exact matchParts_fillTo hi rest ps (by simpa [slotsOf] using hk)
  | .slot k :: ps, hk => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hk k (by simp [slotsOf]))
    have ih := matchParts_fillTo hi rest ps (fun j hj => hk j (by simp [slotsOf, hj]))
    simp [fillTo, hx, matchParts, hi x (arg?_mem hx), ih, pairsOf]

private theorem lookup_pairsOf {β : Type} {args : List β} (k : Nat) :
    ∀ ps : List Part, (∀ j ∈ slotsOf ps, (arg? args j).isSome) → k ∈ slotsOf ps →
      (pairsOf args ps).lookup k = arg? args k
  | [], _, hk => by simp [slotsOf] at hk
  | .word _ :: ps, hj, hk => by
    simp only [slotsOf] at hj hk
    simpa [pairsOf] using lookup_pairsOf k ps hj hk
  | .slot j :: ps, hj, hk => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hj j (by simp [slotsOf]))
    simp only [pairsOf, hx, List.lookup_cons]
    by_cases hkj : k = j
    · subst hkj; simp [hx]
    · simp only [slotsOf, List.mem_cons, hkj, false_or] at hk
      have hb : (k == j) = false := by simpa using hkj
      simp [hb, lookup_pairsOf k ps (fun i hi => hj i (by simp [slotsOf, hi])) hk]

private theorem gather_congr {β : Type} {g g' : Nat → Option β} :
    ∀ ks : List Nat, (∀ k ∈ ks, g k = g' k) → gather g ks = gather g' ks
  | [], _ => rfl
  | k :: ks, h => by
    simp only [gather, h k (by simp), gather_congr ks (fun j hj => h j (by simp [hj]))]

private theorem gather_arg? {β : Type} : ∀ (l pre : List β),
    gather (arg? (pre ++ l)) (List.range' (pre.length + 1) l.length) = some l
  | [], _ => by simp [gather]
  | x :: l, pre => by
    have ih := gather_arg? l (pre ++ [x])
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] at ih
    simp [List.range'_succ, gather, arg?, ih]

private theorem wf_isSome {β : Type} {t : Template} (ht : t.wf = true) {args : List β}
    (hl : args.length = t.arity) : ∀ k ∈ t.slots, (arg? args k).isSome := by
  simp only [Template.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  intro k hk
  have := ht.2 k hk
  cases k with
  | zero => omega
  | succ k => simp [arg?]; omega

private theorem collect_pairsOf {β : Type} {t : Template} (ht : t.wf = true) {args : List β}
    (hl : args.length = t.arity) : collect t (pairsOf args t.parts) = some args := by
  have hj := wf_isSome ht hl
  simp only [Template.wf, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at ht
  unfold collect
  rw [gather_congr _ (fun k hk => lookup_pairsOf k t.parts hj (ht.1 k hk)), ← hl]
  simpa using gather_arg? args []

private theorem wf_parts {lex : Lexicon} (h : lex.wf = true) :
    (∀ t ∈ lex.rels, t.wf = true ∧ isRel t = true) ∧
      (∀ t ∈ lex.phrases, t.wf = true ∧ isPhrase t = true) ∧
      prefixFree (lex.rels.map Template.relLead) = true ∧
      prefixFree (lex.phrases.map (lead ·.parts)) = true := by
  simp only [Lexicon.wf, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem isPhrase_parts {t : Template} (h : isPhrase t = true) :
    ∃ s ps, t.parts = .word s :: ps ∧ s ∉ opens := by
  unfold isPhrase at h
  split at h
  · rename_i s ps heq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨s, ps, heq, by simpa using h.1⟩
  · simp at h

private theorem isRel_parts {t : Template} (h : isRel t = true) :
    ∃ k s l ps, t.parts = .slot k :: ps ∧ lead ps = s :: l ∧ s ∉ stops := by
  unfold isRel at h
  split at h
  · rename_i k ps heq
    split at h
    · rename_i s l hl; exact ⟨k, s, l, ps, heq, hl, by simpa using h⟩
    · simp at h
  · simp at h

/-- A term's tokens, followed by anything, read back as the term and what follows. -/
public theorem Term.parse_render_exact {lex : Lexicon} (hlex : lex.wf = true) {x : Term α}
    (hx : x.ok lex = true) (more : List (Tok α)) :
    Term.parse lex (x.renderTo more) = some (x, more) := by
  cases x with
  | leaf a => simp [Term.renderTo, Term.parse]
  | phrase p args =>
    simp only [Term.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hx
    obtain ⟨-, hphr, -, hpf⟩ := wf_parts hlex
    obtain ⟨hwf, hisp⟩ := hphr p hx.1
    obtain ⟨s, ps, hps, -⟩ := isPhrase_parts hisp
    have hk := wf_isSome hwf hx.2
    simp only [Template.slots, hps, slotsOf] at hk
    have hfind := find_unique (key := (lead ·.parts)) hpf hx.1
      (t := .w s :: fillTo (fun a r => .leaf a :: r) args ps more)
      (by simp [hps, lead, startsWith, startsWith_fillTo])
    have hm := matchParts_fillTo (item := parseLeaf) (f := fun a r => Tok.leaf a :: r)
      (args := args) (fun x _ more => by simp [parseLeaf]) more ps hk
    have hc := collect_pairsOf hwf hx.2
    simp only [hps, pairsOf] at hc
    simp only [Term.renderTo, hps, fillTo, Term.parse, hfind, Option.bind_some, phraseTail, hm,
      hc, Option.map_some]

public theorem Term.render_inj {lex : Lexicon} (hlex : lex.wf = true) {x y : Term α}
    (hx : x.ok lex = true) (hy : y.ok lex = true) (h : x.render = y.render) : x = y := by
  have := Term.parse_render_exact hlex hx []
  rw [show x.renderTo [] = y.renderTo [] from h, Term.parse_render_exact hlex hy []] at this
  simpa using this.symm

private theorem groupToks_head (g : Group α) (gs : List (Group α)) (rest : List (Tok α)) :
    ∃ r, groupToks g gs rest = .bind g :: r := by
  match gs with
  | [] => exact ⟨rest, rfl⟩
  | [_] => exact ⟨_, rfl⟩
  | _ :: _ :: _ => exact ⟨_, rfl⟩

private theorem parseGroups_last (g : Group α) (s : String) (r : List (Tok α)) (hs : s ≠ "and")
    (hr : ∀ g' r', r ≠ .bind g' :: r') :
    parseGroups (.bind g :: .w s :: r) = some (g, [], .w s :: r) := by
  unfold parseGroups
  split
  · rename_i heq
    simp only [List.cons.injEq, Tok.w.injEq, Tok.bind.injEq] at heq
    exact absurd heq.2.1 hs
  · rename_i heq
    simp only [List.cons.injEq, Tok.w.injEq, Tok.bind.injEq] at heq
    obtain ⟨-, -, rfl⟩ := heq
    exact absurd rfl (hr _ _)
  · rename_i heq
    simp only [List.cons.injEq, Tok.bind.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  · rename_i hne
    exact absurd rfl (hne g (.w s :: r))

private theorem parseGroups_groupToks (s : String) (r : List (Tok α)) (hs : s ≠ "and")
    (hr : ∀ g' r', r ≠ .bind g' :: r') :
    ∀ (g : Group α) (gs : List (Group α)),
      parseGroups (groupToks g gs (.w s :: r)) = some (g, gs, .w s :: r)
  | g, [] => parseGroups_last g s r hs hr
  | g, [h] => by simp [groupToks, parseGroups]
  | g, h :: k :: rest => by
    have ih := parseGroups_groupToks s r hs hr h (k :: rest)
    obtain ⟨t, ht⟩ := groupToks_head h (k :: rest) (.w s :: r)
    show parseGroups (.bind g :: .w "," :: groupToks h (k :: rest) (.w s :: r)) = _
    rw [ht] at ih ⊢
    rw [parseGroups.eq_2, ih]
    rfl

private theorem parseBinder_render (b : Binder α) (s : String) (r : List (Tok α))
    (hs : s ≠ "and") (hr : ∀ g' r', r ≠ .bind g' :: r') :
    parseBinder (b.renderTo (.w s :: r)) = some (b, .w s :: r) := by
  simp [parseBinder, Binder.renderTo, parseGroups_groupToks s r hs hr]

private theorem notMem_kw {w : String} (h : w ∉ opens) :
    w ∉ ["for", "there", "if", equivWords, tfaeKey] :=
  fun hm => h (List.subset_def.mp (by simp [opens]) hm)

private theorem notMem_op {w : String} (h : w ∉ opens) : w ∉ ["both", "either", "it"] :=
  fun hm => h (List.subset_def.mp (by simp [opens]) hm)

private theorem mark_of {p : Place} (hp : p ≠ .item) (t : List (Tok α)) : mark p t = t := by
  simp [mark, hp]

/-- A relation's tokens open with a leaf or with a word no statement or operand opens with. -/
private theorem rel_head {lex : Lexicon} (hlex : lex.wf = true) {t : Template}
    {args : List (Term α)} (hs : (Stmt.rel t args).ok lex = true) (rest : List (Tok α)) :
    ∃ x r, fillTo Term.renderTo args t.parts rest = x :: r ∧
      ((∃ a, x = .leaf a) ∨ ∃ w, x = .w w ∧ w ∉ opens) := by
  obtain ⟨hrels, hphr, -, -⟩ := wf_parts hlex
  simp only [Stmt.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨ht, hl⟩, hargs⟩ := hs
  obtain ⟨hwf, hrel⟩ := hrels t ht
  obtain ⟨k, -, -, ps, hps, -, -⟩ := isRel_parts hrel
  have hk := wf_isSome hwf hl
  simp only [Template.slots, hps, slotsOf, List.mem_cons, forall_eq_or_imp] at hk
  obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hk.1
  have hx := hargs x₀ (arg?_mem hx₀)
  simp only [hps, fillTo, hx₀]
  cases x₀ with
  | leaf a => exact ⟨_, _, rfl, Or.inl ⟨a, rfl⟩⟩
  | phrase p qs =>
    simp only [Term.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hx
    obtain ⟨s, ps', hps', hs'⟩ := isPhrase_parts (hphr p hx.1).2
    simp only [Term.renderTo, hps', fillTo]
    exact ⟨_, _, rfl, Or.inr ⟨s, rfl, hs'⟩⟩

private theorem blockWith_head (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) :
    ∃ r, blockWith f rest = .indent :: r := by
  unfold blockWith
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  all_goals exact ⟨_, rfl⟩

/-- What a statement's tokens open with where it stands but among a list's items: a word, a leaf or
a block's start, never a group or an item's mark. -/
private def plainHead : List (Tok α) → Bool
  | .w _ :: _ | .leaf _ :: _ | .indent :: _ => true
  | [] | .bind _ :: _ | .dedent :: _ | .item :: _ => false

private theorem renderTo_head {lex : Lexicon} (hlex : lex.wf = true) (s : Stmt α)
    (hs : s.ok lex = true) : ∀ p rest, p ≠ .item → plainHead (renderTo p s rest) = true := by
  induction s with
  | all b body _ => intro p rest hp; simp [renderTo, mark_of hp, wordsTo, allWords, plainHead]
  | ex b body _ => intro p rest hp; simp [renderTo, mark_of hp, wordsTo, exWords, plainHead]
  | imp h c _ _ => intro p rest hp; simp [renderTo, mark_of hp, plainHead]
  | conj a b iha _ =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    intro p rest hp
    cases p with
    | operand => rfl
    | item => exact absurd rfl hp
    | scope | lead | inner =>
      simp only [renderTo]
      split
      · exact iha hs.1 .operand _ (by decide)
      · rfl
  | disj a b _ _ => intro p rest hp; simp [renderTo, mark_of hp, plainHead]
  | iff a b iha _ =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    intro p rest hp
    simp only [renderTo, mark_of hp]
    split
    · rfl
    · simp only [iffTo]
      split
      · obtain ⟨r, hr⟩ := blockWith_head _ rest; rw [hr]; rfl
      · unfold wrapWith
        split
        · exact iha hs.1 .operand _ (by decide)
        · obtain ⟨r, hr⟩ := blockWith_head _ _; rw [hr]; rfl
  | tfae _ _ => intro p rest hp; simp [renderTo, mark_of hp, plainHead]
  | neg a _ => intro p rest hp; simp [renderTo, mark_of hp, wordsTo, plainHead]
  | rel t args =>
    intro p rest hp
    obtain ⟨x, r, hx, hh⟩ := rel_head hlex hs rest
    simp only [renderTo, mark_of hp, hx]
    rcases hh with ⟨a, rfl⟩ | ⟨w, rfl, -⟩ <;> rfl
  | atom x => intro p rest hp; simp [renderTo, mark_of hp, plainHead]

private theorem plainHead_bind {t : List (Tok α)} (h : plainHead t = true) :
    ∀ g r, t ≠ .bind g :: r := by
  intro g r ht; subst ht; simp [plainHead] at h

private theorem plainHead_item {t : List (Tok α)} (h : plainHead t = true) :
    ∀ r, t ≠ .item :: r := by
  intro r ht; subst ht; simp [plainHead] at h

/-- A relation's tokens open with a leaf or with a word no statement or operand opens with. -/
private theorem render_rel_head {lex : Lexicon} (hlex : lex.wf = true) {t : Template}
    {args : List (Term α)} (hs : (Stmt.rel t args).ok lex = true) (p : Place) (hp : p ≠ .item)
    (rest : List (Tok α)) :
    ∀ w r, renderTo p (.rel t args) rest = .w w :: r → w ∉ opens := by
  obtain ⟨x, r, hx, hh⟩ := rel_head hlex hs rest
  intro w r' h
  simp only [renderTo, mark_of hp, hx, List.cons.injEq] at h
  rcases hh with ⟨a, rfl⟩ | ⟨w', rfl, hw⟩
  · simp at h
  · simp only [Tok.w.injEq] at h; exact h.1 ▸ hw

private theorem parseAtomic_rel {lex : Lexicon} (hlex : lex.wf = true) {t : Template}
    {args : List (Term α)} (hs : (Stmt.rel t args).ok lex = true) (rest : List (Tok α)) :
    parseAtomic lex (fillTo Term.renderTo args t.parts rest) = some (.rel t args, rest) := by
  obtain ⟨hrels, -, hpf, -⟩ := wf_parts hlex
  simp only [Stmt.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨ht, hl⟩, hargs⟩ := hs
  obtain ⟨hwf, hrel⟩ := hrels t ht
  obtain ⟨k, -, -, ps, hps, -, -⟩ := isRel_parts hrel
  have hk := wf_isSome hwf hl
  simp only [Template.slots, hps, slotsOf, List.mem_cons, forall_eq_or_imp] at hk
  obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hk.1
  have hterm : ∀ x ∈ args, ∀ more, Term.parse lex (x.renderTo more) = some (x, more) :=
    fun x hx more => Term.parse_render_exact hlex (hargs x hx) more
  have hfind := find_unique (key := Template.relLead) hpf ht
    (t := fillTo Term.renderTo args ps rest) (by simp [Template.relLead, hps, startsWith_fillTo])
  have hc := collect_pairsOf hwf hl
  simp only [hps, pairsOf, hx₀] at hc
  simp only [hps, fillTo, hx₀, parseAtomic, hterm x₀ (arg?_mem hx₀), Option.bind_some,
    hfind, relTail, matchParts_fillTo hterm rest ps hk.2, hc, Option.map_some]

private theorem parseAtomic_atom {lex : Lexicon} (hlex : lex.wf = true) (x : α)
    {rest : List (Tok α)} (hr : followsOpnd rest = true) :
    parseAtomic lex (.leaf x :: rest) = some (.atom x, rest) := by
  obtain ⟨hrels, -, -, -⟩ := wf_parts hlex
  have hnone : lex.rels.find? (fun tp => startsWith tp.relLead rest) = none := by
    rw [List.find?_eq_none]
    intro tp htp hst
    obtain ⟨k, s, l, ps, hps, hlead, hs⟩ := isRel_parts (hrels tp htp).2
    simp only [Template.relLead, hps, hlead] at hst
    match rest, hr, hst with
    | [], _, hst => simp [startsWith] at hst
    | .dedent :: _, _, hst => simp [startsWith] at hst
    | .item :: _, _, hst => simp [startsWith] at hst
    | .w s' :: _, hr, hst =>
      simp only [startsWith, Bool.and_eq_true, beq_iff_eq] at hst
      simp only [followsOpnd, List.contains_iff_mem] at hr
      exact hs (hst.1 ▸ hr)
  simp [parseAtomic, Term.parse, hnone]

private theorem followsOpnd_of {r : List (Tok α)} (h : followsStmt r = true) :
    followsOpnd r = true := by
  match r, h with
  | [], _ => rfl
  | .dedent :: _, _ => rfl
  | .item :: _, _ => rfl
  | .w s :: [], h =>
    simp only [followsStmt, beq_iff_eq] at h
    subst h; simp [followsOpnd, stops]
  | .w s :: .dedent :: _, h =>
    simp only [followsStmt, closing, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl <;> simp [followsOpnd, stops]

/-- Tokens whose first word opens no statement, or that open on no word, open no statement. -/
private theorem opensStmt_of_head {t : List (Tok α)}
    (h : ∀ w r, t = .w w :: r → w ∉ ["for", "there", "if", equivWords, tfaeKey]) :
    opensStmt t = false := by
  match t, h with
  | [], _ => rfl
  | .leaf _ :: _, _ => rfl
  | .bind _ :: _, _ => rfl
  | .indent :: _, _ => rfl
  | .dedent :: _, _ => rfl
  | .item :: _, _ => rfl
  | .w w :: r, h =>
    have hw := h w r rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    simp [opensStmt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2]

private theorem parseStmt_opened {lex : Lexicon} {t : List (Tok α)} (h : opensStmt t = true) :
    parseStmt lex t = parseOpened lex t := by
  rw [parseStmt.eq_1, ite_eq_left h]

private theorem parseOperand_opened {lex : Lexicon} {t : List (Tok α)} (h : opensStmt t = true) :
    parseOperand lex t = parseOpened lex t := by
  match t, h with
  | .w w :: r, h =>
    have hw : w = "for" ∨ w = "there" ∨ w = "if" ∨ w = equivWords ∨ w = tfaeKey := by
      simp only [opensStmt, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((h | h) | h) | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rw [parseOperand.eq_6 lex _ (fun _ ht => by simp at ht) (fun _ ht => by simp at ht)
      (fun _ ht => by
        simp only [List.cons.injEq, Tok.w.injEq] at ht; rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp [equivWords, tfaeKey] at ht)
      (fun _ ht => by
        simp only [List.cons.injEq, Tok.w.injEq] at ht; rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp [equivWords, tfaeKey] at ht)
      (fun _ ht => by
        simp only [List.cons.injEq, Tok.w.injEq] at ht; rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp [equivWords, tfaeKey] at ht),
      ite_eq_left h]

private theorem parseOpened_if {lex : Lexicon} (t : List (Tok α)) :
    forget (parseOpened lex (.w "if" :: t)) = forget (parseHyps lex t) := by
  rw [parseOpened.eq_3]
  cases parseHyps lex t with
  | none => rfl
  | some p => obtain ⟨s, r, h⟩ := p; rfl

private theorem followsStmt_and (r : List (Tok α)) : followsStmt (.w "and" :: r) = false := by
  cases r with
  | nil => rfl
  | cons x _ => cases x <;> rfl

private theorem parseStmt_op {lex : Lexicon} {t rest : List (Tok α)} {s : Stmt α}
    (hkw : opensStmt t = false)
    (ho : forget (parseOperand lex t) = some (s, rest)) (hr : followsStmt rest = true) :
    forget (parseStmt lex t) = some (s, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp ho
  rw [parseStmt.eq_1, ite_eq_right (by simp [hkw])]
  simp only [e]
  split
  · rename_i a r h' heq
    simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    simp [followsStmt] at hr
  · rename_i a r h' heq
    simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rw [followsStmt_and] at hr; cases hr
  · rfl

/-- An operand, "and", then a statement read back as the inline conjunction of the two. -/
private theorem parseStmt_and {lex : Lexicon} {t r rest : List (Tok α)} {a b : Stmt α}
    (hkw : opensStmt t = false) (ho : forget (parseOperand lex t) = some (a, .w "and" :: r))
    (hb : forget (parseStmt lex r) = some (b, rest)) :
    forget (parseStmt lex t) = some (.conj a b, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp ho
  obtain ⟨h2, e2⟩ := forget_eq.mp hb
  rw [parseStmt.eq_1, ite_eq_right (by simp [hkw])]
  simp only [e]
  rw [e2]; rfl

private theorem parseOperand_atomic {lex : Lexicon} {t : List (Tok α)}
    (hi : ∀ r, t ≠ .indent :: r) (h : ∀ w r, t = .w w :: r → w ∉ ["both", "either", "it"])
    (hkw : opensStmt t = false) :
    forget (parseOperand lex t) = parseAtomic lex t := by
  rw [parseOperand.eq_6 lex t (fun _ ht => hi _ ht) (fun _ ht => hi _ ht)
    (fun _ ht => h _ _ ht (by simp))
    (fun _ ht => h _ _ ht (by simp)) (fun _ ht => h _ _ ht (by simp)), ite_eq_right (by simp [hkw])]
  split
  · rename_i s r heq; simp [forget, heq]
  · rename_i hne
    cases hp : parseAtomic lex t with
    | none => rfl
    | some p => exact (hne p.1 p.2 hp).elim

private theorem wrap_head {lex : Lexicon} (hlex : lex.wf = true) {a : Stmt α}
    (ha : a.ok lex = true) (k : Nat) (hk : k ≤ 1) (X : List (Tok α)) (hX : followsStmt X = false) :
    opensStmt (wrapWith k a (renderTo .operand a) X) = false := by
  unfold wrapWith
  by_cases hp : a.prec ≤ k
  · rw [ite_eq_left (by simp [hp])]
    cases a with
    | rel t args =>
      exact opensStmt_of_head fun w r h =>
        notMem_kw (render_rel_head hlex ha .operand (by decide) X w r h)
    | atom x => rfl
    | conj _ _ | disj _ _ | neg _ => simp [renderTo, mark, wordsTo, opensStmt, equivWords, tfaeKey]
    | _ => simp only [Stmt.prec] at hp; omega
  · rw [ite_eq_right (by simp [hp, hX])]
    obtain ⟨r, hr⟩ := blockWith_head (renderTo .operand a) X
    rw [hr]; rfl

/-- A statement's tokens as a block read back as an operand, a closing word after it read after the
block. -/
private theorem block_of {lex : Lexicon} (hlex : lex.wf = true) {s : Stmt α} (hs : s.ok lex = true)
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest)) (rest : List (Tok α)) :
    forget (parseOperand lex (blockWith (renderTo .operand s) rest)) = some (s, rest) := by
  have hni : ∀ X, ∀ r, renderTo .operand s X ≠ .item :: r := fun X =>
    plainHead_item (renderTo_head hlex s hs .operand X (by decide))
  have plain : forget (parseOperand lex (.indent :: renderTo .operand s (.dedent :: rest))) =
      some (s, rest) := by
    obtain ⟨h, e⟩ := forget_eq.mp (hS (.dedent :: rest) rfl)
    rw [parseOperand.eq_2 lex _ (fun _ ht => hni _ _ ht), e]; rfl
  match rest with
  | .w p :: r =>
    by_cases hc : closing p = true
    · rw [blockWith, ite_eq_left hc]
      obtain ⟨h, e⟩ := forget_eq.mp (hS (.w p :: .dedent :: r) (by simp [followsStmt, hc]))
      rw [parseOperand.eq_2 lex _ (fun _ ht => hni _ _ ht), e]
      simp [hc, forget]
    · rw [blockWith, ite_eq_right hc]
      exact plain
  | [] => exact plain
  | .leaf _ :: _ => exact plain
  | .bind _ :: _ => exact plain
  | .indent :: _ => exact plain
  | .dedent :: _ => exact plain
  | .item :: _ => exact plain

/-- An operand reads back at every wrapping level up to 1: bare, bare at its extent's end, or as a
block. -/
private theorem wrap_of {lex : Lexicon} (hlex : lex.wf = true) {s : Stmt α} (hs : s.ok lex = true)
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest))
    (hB : s.prec ≤ 1 → ∀ rest, followsOpnd rest = true →
      forget (parseOperand lex (renderTo .operand s rest)) = some (s, rest))
    (hO : s.isIff = false → ∀ rest, followsStmt rest = true →
      forget (parseOperand lex (renderTo .operand s rest)) = some (s, rest)) :
    ∀ k rest, k ≤ 1 → followsOpnd rest = true →
      forget (parseOperand lex (wrapWith k s (renderTo .operand s) rest)) = some (s, rest) := by
  intro k rest hk hr
  unfold wrapWith
  by_cases hp : s.prec ≤ k
  · rw [ite_eq_left (by simp [hp])]; exact hB (by omega) rest hr
  · by_cases hb : s.isIff = false ∧ followsStmt rest = true
    · rw [ite_eq_left (by simp [hb.1, hb.2])]; exact hO hb.1 rest hb.2
    · rw [ite_eq_right (by
        simp only [Bool.or_eq_true, decide_eq_true_eq, hp, false_or, Bool.and_eq_true,
          Bool.not_eq_true']
        exact hb)]
      exact block_of hlex hs hS rest

/-- An equivalence's right side reads back, alike its left or as an operand. -/
private theorem iffRight_of {lex : Lexicon} (hlex : lex.wf = true) {a s : Stmt α}
    (hs : s.ok lex = true)
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest))
    (hW : ∀ k rest, k ≤ 1 → followsOpnd rest = true →
      forget (parseOperand lex (wrapWith k s (renderTo .operand s) rest)) = some (s, rest))
    (rest : List (Tok α)) (hr : followsOpnd rest = true) :
    forget (parseOperand lex (iffRight a s (renderTo .operand s) rest)) = some (s, rest) := by
  unfold iffRight
  by_cases hb : (a.leftK < a.prec && 0 < s.prec) = true
  · rw [ite_eq_left hb]; exact block_of hlex hs hS rest
  · rw [ite_eq_right hb]; exact hW 1 rest (by decide) hr

private theorem stmt_of {lex : Lexicon} {s : Stmt α}
    (hkw : ∀ rest, opensStmt (renderTo .operand s rest) = false)
    (hB : ∀ rest, followsOpnd rest = true →
      forget (parseOperand lex (renderTo .operand s rest)) = some (s, rest)) :
    ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest) :=
  fun rest hr => parseStmt_op (hkw rest) (hB rest (followsOpnd_of hr)) hr

/-- A statement a quantifier, an existential or "if" opens reads back as a statement and, before a
continuation ending its extent, as an operand. -/
private theorem opened_of {lex : Lexicon} {s : Stmt α}
    (hop : ∀ rest, opensStmt (renderTo .operand s rest) = true)
    (hP : ∀ rest, followsStmt rest = true →
      forget (parseOpened lex (renderTo .operand s rest)) = some (s, rest)) :
    (∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest)) ∧
    (∀ rest, followsStmt rest = true →
      forget (parseOperand lex (renderTo .operand s rest)) = some (s, rest)) :=
  ⟨fun rest hr => by rw [parseStmt_opened (hop rest)]; exact hP rest hr,
   fun rest hr => by rw [parseOperand_opened (hop rest)]; exact hP rest hr⟩

private theorem quant_all {lex : Lexicon} (b : Binder α) {body : Stmt α} {rest : List (Tok α)}
    (p : Place) (hp : p ≠ .item)
    (hhead : plainHead (renderTo p.sub body rest) = true)
    (e1 : ∃ h, parseStmt lex (renderTo p.sub body rest) = some (body, ⟨rest, h⟩)) :
    forget (parseOpened lex (renderTo p (.all b body) rest)) = some (.all b body, rest) := by
  obtain ⟨h1, e1⟩ := e1
  have hq : ∀ q, q = (if b.many then "all" else "every") → q = "every" ∨ q = "all" := by
    intro q hq; subst hq; cases b.many <;> simp
  have hsep : ∀ s, s = sepWord p.sub body → (s = "," ∨ s = ":") ∧ s ≠ "and" := by
    intro s hs; subst hs; unfold sepWord; split <;> simp
  have ht : renderTo p (.all b body) rest =
      .w "for" :: .w (if b.many then "all" else "every") ::
      b.renderTo (.w (sepWord p.sub body) :: renderTo p.sub body rest) := by
    simp [renderTo, mark, hp, wordsTo, allWords]
  rw [ht, parseOpened.eq_1, ite_eq_left (hq _ rfl)]
  have hb := parseBinder_render b (sepWord p.sub body) (renderTo p.sub body rest) (hsep _ rfl).2
    (plainHead_bind hhead)
  split
  · rename_i b' s r heq
    rw [hb] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Tok.w.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rw [ite_eq_left (hsep _ rfl).1, e1]; rfl
  · rename_i hne
    exact (hne b _ _ hb).elim

private theorem quant_ex {lex : Lexicon} (b : Binder α) {body : Stmt α} {rest : List (Tok α)}
    (p : Place) (hp : p ≠ .item)
    (e1 : ∃ h, parseStmt lex (renderTo p.sub body rest) = some (body, ⟨rest, h⟩)) :
    forget (parseOpened lex (renderTo p (.ex b body) rest)) = some (.ex b body, rest) := by
  obtain ⟨h1, e1⟩ := e1
  have hq : ∀ q, q = (if b.many then "are" else "is") → q = "is" ∨ q = "are" := by
    intro q hq; subst hq; cases b.many <;> simp
  have hb := parseBinder_render b "such" (.w "that" :: renderTo p.sub body rest) (by decide)
    (fun _ _ h => by simp at h)
  have ht : renderTo p (.ex b body) rest = .w "there" ::
      .w (if b.many then "are" else "is") ::
      b.renderTo (.w "such" :: .w "that" :: renderTo p.sub body rest) := by
    simp [renderTo, mark, hp, wordsTo, exWords]
  rw [ht, parseOpened.eq_2, ite_eq_left (hq _ rfl)]
  split
  · rename_i heq
    rw [hb] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, -, -, rfl⟩ := heq
    rw [e1]; rfl
  · rename_i hne; exact (hne b _ hb).elim

/-- A statement's tokens among a list's items where it is no conjunction: its mark, then its
tokens at a lead. -/
private theorem item_eq {s : Stmt α} (hc : ∀ a b, s ≠ .conj a b) (rest : List (Tok α)) :
    renderTo .item s rest = .item :: renderTo .lead s rest := by
  cases s with
  | conj a b => exact absurd rfl (hc a b)
  | iff a b =>
    by_cases h : a.leftK < a.prec
    · simp [renderTo, mark, h]
    · simp [renderTo, mark, h, iffTo]
  | _ => simp [renderTo, mark, Place.sub]

/-- The last item of a list reads back, its statement before what follows the list. -/
private theorem spine_last {lex : Lexicon} {s : Stmt α} {rest : List (Tok α)} {t : List (Tok α)}
    (hr : ∀ r, rest ≠ .item :: r) (hS : forget (parseStmt lex t) = some (s, rest)) :
    forget (parseSpine lex (.item :: t)) = some (s, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp hS
  rw [parseSpine.eq_1]
  split
  · rename_i a r h' heq
    rw [e] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
    exact absurd heq.2 (hr r)
  · rename_i o hne
    rw [e]; rfl

/-- An item, then more items, read back as their conjunction. -/
private theorem spine_cons {lex : Lexicon} {a b : Stmt α} {rest r : List (Tok α)}
    {t : List (Tok α)} (ha : forget (parseStmt lex t) = some (a, .item :: r))
    (hb : forget (parseSpine lex (.item :: r)) = some (b, rest)) :
    forget (parseSpine lex (.item :: t)) = some (.conj a b, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp ha
  obtain ⟨h2, e2⟩ := forget_eq.mp hb
  rw [parseSpine.eq_1]
  simp only [e]
  rw [e2]; rfl

/-- Every way a statement stands reads back: an operand's tokens as a statement, in an inner
scope, at a lead, in a scope, among a list's items before what ends the list, and wrapped as an
operand. -/
private structure Reads (lex : Lexicon) (s : Stmt α) : Prop where
  operand : ∀ rest, followsStmt rest = true →
    forget (parseStmt lex (renderTo .operand s rest)) = some (s, rest)
  inner : ∀ rest, followsStmt rest = true →
    forget (parseStmt lex (renderTo .inner s rest)) = some (s, rest)
  lead : ∀ rest, followsStmt rest = true →
    forget (parseStmt lex (renderTo .lead s rest)) = some (s, rest)
  scope : ∀ rest, followsStmt rest = true →
    forget (parseStmt lex (renderTo .scope s rest)) = some (s, rest)
  item : ∀ rest, followsStmt rest = true → (∀ r, rest ≠ .item :: r) →
    forget (parseSpine lex (renderTo .item s rest)) = some (s, rest)
  wrap : ∀ k rest, k ≤ 1 → followsOpnd rest = true →
    forget (parseOperand lex (wrapWith k s (renderTo .operand s) rest)) = some (s, rest)

/-- A statement no conjunction reads back among a list's items as it reads at a lead. -/
private theorem item_of {lex : Lexicon} {s : Stmt α} (hc : ∀ a b, s ≠ .conj a b)
    (hL : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo .lead s rest)) = some (s, rest)) :
    ∀ rest, followsStmt rest = true → (∀ r, rest ≠ .item :: r) →
      forget (parseSpine lex (renderTo .item s rest)) = some (s, rest) :=
  fun rest hr hi => by rw [item_eq hc]; exact spine_last hi (hL rest hr)

/-- Parsing a statement's tokens, wherever it stands, before a continuation in its follow set
returns the statement and the continuation. -/
private theorem reads {lex : Lexicon} (hlex : lex.wf = true) (s : Stmt α)
    (hs : s.ok lex = true) : Reads lex s := by
  induction s with
  | all b body ih =>
    have rb := ih hs
    have hop : ∀ p rest, p ≠ .item → opensStmt (renderTo p (.all b body) rest) = true :=
      fun p rest hp => by simp [renderTo, mark, hp, wordsTo, allWords, opensStmt]
    have hP : ∀ p, p ≠ .item →
        (∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p.sub body rest)) = some (body, rest)) →
        ∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p (.all b body) rest)) = some (.all b body, rest) :=
      fun p hp hb rest hr => by
        rw [parseStmt_opened (hop p rest hp)]
        exact quant_all b p hp (renderTo_head hlex body hs _ rest (by cases p <;> simp [Place.sub] at hp ⊢))
          (forget_eq.mp (hb rest hr))
    have hO := hP .operand (by decide) rb.inner
    have hL := hP .lead (by decide) rb.scope
    have hOp : ∀ rest, followsStmt rest = true →
        forget (parseOperand lex (renderTo .operand (.all b body) rest)) = some (.all b body, rest) :=
      fun rest hr => by
        have := hO rest hr
        rw [parseStmt_opened (hop .operand rest (by decide))] at this
        rw [parseOperand_opened (hop .operand rest (by decide))]
        exact this
    exact { operand := hO, inner := hP .inner (by decide) rb.inner, lead := hL
            scope := hP .scope (by decide) rb.scope
            item := item_of (fun _ _ h => by cases h) hL
            wrap := wrap_of hlex hs hO (fun h => by simp [Stmt.prec] at h) (fun _ => hOp) }
  | ex b body ih =>
    have rb := ih hs
    have hop : ∀ p rest, p ≠ .item → opensStmt (renderTo p (.ex b body) rest) = true :=
      fun p rest hp => by simp [renderTo, mark, hp, wordsTo, exWords, opensStmt]
    have hP : ∀ p, p ≠ .item →
        (∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p.sub body rest)) = some (body, rest)) →
        ∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p (.ex b body) rest)) = some (.ex b body, rest) :=
      fun p hp hb rest hr => by
        rw [parseStmt_opened (hop p rest hp)]
        exact quant_ex b p hp (forget_eq.mp (hb rest hr))
    have hO := hP .operand (by decide) rb.inner
    have hL := hP .lead (by decide) rb.scope
    have hOp : ∀ rest, followsStmt rest = true →
        forget (parseOperand lex (renderTo .operand (.ex b body) rest)) = some (.ex b body, rest) :=
      fun rest hr => by
        have := hO rest hr
        rw [parseStmt_opened (hop .operand rest (by decide))] at this
        rw [parseOperand_opened (hop .operand rest (by decide))]
        exact this
    exact { operand := hO, inner := hP .inner (by decide) rb.inner, lead := hL
            scope := hP .scope (by decide) rb.scope
            item := item_of (fun _ _ h => by cases h) hL
            wrap := wrap_of hlex hs hO (fun h => by simp [Stmt.prec] at h) (fun _ => hOp) }
  | imp h c ihh ihc =>
    have hs' := hs
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have rh := ihh hs.1
    have rc := ihc hs.2
    have hop : ∀ p rest, p ≠ .item → opensStmt (renderTo p (.imp h c) rest) = true :=
      fun p rest hp => by simp [renderTo, mark, hp, opensStmt]
    have hP : ∀ p, p ≠ .item →
        (∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p.sub c rest)) = some (c, rest)) →
        ∀ rest, followsStmt rest = true →
          forget (parseOpened lex (renderTo p (.imp h c) rest)) = some (.imp h c, rest) := by
      intro p hp hcS rest hr
      cases hc : c.isImp with
      | true =>
        cases c with
        | imp h' c' =>
          let Y := wrapWith (if c'.isImp then 0 else 1) h' (renderTo .operand h')
            (chainWith c' (renderTo p.sub.sub c') rest)
          have hsub : p.sub.sub = p.sub := by cases p <;> rfl
          have hc1 := hcS rest hr
          rw [show renderTo p.sub (.imp h' c') rest = .w "if" :: Y from by
              cases p <;> simp [renderTo, mark, Y, Place.sub],
            parseStmt_opened (rfl : opensStmt (.w "if" :: Y) = true), parseOpened_if] at hc1
          obtain ⟨h2, e2⟩ := forget_eq.mp hc1
          obtain ⟨h1, e1⟩ := forget_eq.mp (rh.wrap 0 (.w "and" :: Y) (by decide)
            (by simp [followsOpnd, stops]))
          have ht : renderTo p (.imp h (.imp h' c')) rest =
              .w "if" :: wrapWith 0 h (renderTo .operand h) (.w "and" :: Y) := by
            cases p <;> simp_all [renderTo, mark, chainWith, Stmt.isImp, Y, Place.sub]
          rw [ht, parseOpened_if, parseHyps.eq_1, e1]
          simp only
          rw [e2]; rfl
        | _ => simp [Stmt.isImp] at hc
      | false =>
        obtain ⟨h2, e2⟩ := forget_eq.mp (hcS rest hr)
        obtain ⟨h1, e1⟩ := forget_eq.mp (rh.wrap 1
          (.w "," :: .w "then" :: renderTo p.sub c rest) (by decide)
          (by simp [followsOpnd, stops]))
        have ht : renderTo p (.imp h c) rest = .w "if" ::
            wrapWith 1 h (renderTo .operand h) (.w "," :: .w "then" :: renderTo p.sub c rest) := by
          simp [renderTo, mark, hp, chainWith, hc]
        rw [ht, parseOpened_if, parseHyps.eq_1, e1]
        simp only
        rw [e2]; rfl
    have hS : ∀ p, p ≠ .item →
        (∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p.sub c rest)) = some (c, rest)) →
        ∀ rest, followsStmt rest = true →
          forget (parseStmt lex (renderTo p (.imp h c) rest)) = some (.imp h c, rest) :=
      fun p hp hcS rest hr => by rw [parseStmt_opened (hop p rest hp)]; exact hP p hp hcS rest hr
    have hO := hS .operand (by decide) rc.inner
    have hL := hS .lead (by decide) rc.scope
    have hOp : ∀ rest, followsStmt rest = true →
        forget (parseOperand lex (renderTo .operand (.imp h c) rest)) = some (.imp h c, rest) :=
      fun rest hr => by
        rw [parseOperand_opened (hop .operand rest (by decide))]
        exact hP .operand (by decide) rc.inner rest hr
    exact { operand := hO, inner := hS .inner (by decide) rc.inner, lead := hL
            scope := hS .scope (by decide) rc.scope
            item := item_of (fun _ _ h => by cases h) hL
            wrap := wrap_of hlex hs' hO (fun h => by simp [Stmt.prec] at h) (fun _ => hOp) }
  | conj a b iha ihb =>
    have hs' := hs
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have ra := iha hs.1
    have rb := ihb hs.2
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo .operand (.conj a b) rest)) = some (.conj a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp (rb.wrap 1 rest (by decide) hr)
      obtain ⟨h1, e1⟩ := forget_eq.mp (ra.wrap 0 (.w "and" :: wrapWith 1 b (renderTo .operand b) rest)
        (by decide) (by simp [followsOpnd, stops]))
      have ht : renderTo .operand (.conj a b) rest = .w "both" ::
          wrapWith 0 a (renderTo .operand a) (.w "and" :: wrapWith 1 b (renderTo .operand b) rest) :=
        rfl
      rw [ht, parseOperand.eq_3, e1]
      simp only
      rw [e2]; rfl
    have hO := stmt_of (fun rest => rfl) hB
    have hI : ∀ rest, followsStmt rest = true → (∀ r, rest ≠ .item :: r) →
        forget (parseSpine lex (renderTo .item (.conj a b) rest)) = some (.conj a b, rest) := by
      intro rest hr hi
      obtain ⟨r, hr'⟩ : ∃ r, renderTo .item b rest = .item :: r := by
        cases b
        case iff => simp only [renderTo, mark]; split <;> exact ⟨_, rfl⟩
        all_goals simp [renderTo, mark]
      have e1 := ra.lead (renderTo .item b rest) (by rw [hr']; rfl)
      rw [hr'] at e1
      have e2 := rb.item rest hr hi
      rw [hr'] at e2
      show forget (parseSpine lex (.item :: renderTo .lead a (renderTo .item b rest))) = _
      rw [hr']
      exact spine_cons e1 e2
    have hIn : inline a b = true → ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo .operand a (.w "and" :: renderTo .operand b rest))) =
          some (.conj a b, rest) := by
      intro hin rest hr
      have hpa : a.prec = 0 := by simp [inline] at hin; exact hin.1
      have hX : followsOpnd (.w "and" :: renderTo .operand b rest) = true := by
        simp [followsOpnd, stops]
      have e1 := ra.wrap 0 _ (by decide) hX
      rw [show wrapWith 0 a (renderTo .operand a) (.w "and" :: renderTo .operand b rest) =
        renderTo .operand a (.w "and" :: renderTo .operand b rest) by
          simp [wrapWith, hpa]] at e1
      have hkw : opensStmt (renderTo .operand a (.w "and" :: renderTo .operand b rest)) = false := by
        have := wrap_head hlex hs.1 0 (by decide) (.w "and" :: renderTo .operand b rest)
          (followsStmt_and _)
        simpa [wrapWith, hpa] using this
      exact parseStmt_and hkw e1 (rb.operand rest hr)
    have hL : ∀ p, p = .scope ∨ p = .lead → ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo p (.conj a b) rest)) = some (.conj a b, rest) := by
      intro p hp rest hr
      by_cases hin : inline a b = true
      · have ht : renderTo p (.conj a b) rest =
            renderTo .operand a (.w "and" :: renderTo .operand b rest) := by
          rcases hp with rfl | rfl <;> simp [renderTo, hin]
        rw [ht]; exact hIn hin rest hr
      · have ht : renderTo p (.conj a b) rest =
            .indent :: .item :: renderTo .lead a (renderTo .item b (.dedent :: rest)) := by
          rcases hp with rfl | rfl <;> simp [renderTo, hin]
        rw [ht]
        have e0 : forget (parseSpine lex
            (.item :: renderTo .lead a (renderTo .item b (.dedent :: rest)))) =
            some (.conj a b, .dedent :: rest) := hI (.dedent :: rest) rfl (fun _ h => by cases h)
        obtain ⟨h1, e1⟩ := forget_eq.mp e0
        refine parseStmt_op rfl ?_ hr
        rw [parseOperand.eq_1, e1]; rfl
    have hInner : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo .inner (.conj a b) rest)) = some (.conj a b, rest) := by
      intro rest hr
      by_cases hin : inline a b = true
      · have ht : renderTo .inner (.conj a b) rest =
            renderTo .operand a (.w "and" :: renderTo .operand b rest) := by
          simp [renderTo, hin]
        rw [ht]; exact hIn hin rest hr
      · have ht : renderTo .inner (.conj a b) rest = renderTo .operand (.conj a b) rest := by
          simp [renderTo, hin]
        rw [ht]; exact hO rest hr
    exact { operand := hO, inner := hInner, lead := hL .lead (Or.inr rfl)
            scope := hL .scope (Or.inl rfl), item := hI
            wrap := wrap_of hlex hs' hO (fun _ => hB) (fun _ rest hr => hB rest (followsOpnd_of hr)) }
  | disj a b iha ihb =>
    have hs' := hs
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo .operand (.disj a b) rest)) = some (.disj a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp ((ihb hs.2).wrap 1 rest (by decide) hr)
      obtain ⟨h1, e1⟩ := forget_eq.mp ((iha hs.1).wrap 0
        (.w "or" :: wrapWith 1 b (renderTo .operand b) rest) (by decide) (by simp [followsOpnd, stops]))
      have ht : renderTo .operand (.disj a b) rest = .w "either" ::
          wrapWith 0 a (renderTo .operand a) (.w "or" :: wrapWith 1 b (renderTo .operand b) rest) :=
        rfl
      rw [ht, parseOperand.eq_4, e1]
      simp only
      rw [e2]; rfl
    have hO := stmt_of (fun rest => rfl) hB
    have same : ∀ p, p ≠ .item → ∀ rest,
        renderTo p (.disj a b) rest = renderTo .operand (.disj a b) rest :=
      fun p hp rest => by simp [renderTo, mark, hp]
    exact { operand := hO, inner := fun rest hr => by rw [same .inner (by decide)]; exact hO rest hr
            lead := fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr
            scope := fun rest hr => by rw [same .scope (by decide)]; exact hO rest hr
            item := item_of (fun _ _ h => by cases h)
              (fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr)
            wrap := wrap_of hlex hs' hO (fun _ => hB) (fun _ rest hr => hB rest (followsOpnd_of hr)) }
  | iff a b iha ihb =>
    have hs' := hs
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have ra := iha hs.1
    have rb := ihb hs.2
    have hO : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo .operand (.iff a b) rest)) = some (.iff a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp
        (iffRight_of (a := a) hlex hs.2 rb.operand rb.wrap rest (followsOpnd_of hr))
      let X : List (Tok α) :=
        .w "if" :: .w "and" :: .w "only" :: .w "if" :: iffRight a b (renderTo .operand b) rest
      obtain ⟨h1, e1⟩ :=
        forget_eq.mp (ra.wrap a.leftK X
          (by cases a <;> simp [Stmt.leftK]) (by simp [X, followsOpnd, stops]))
      have ht : renderTo .operand (.iff a b) rest = wrapWith a.leftK a (renderTo .operand a) X := by
        simp [renderTo, mark, iffTo, wordsTo, X]
      have hkw := wrap_head hlex hs.1 a.leftK
        (by cases a <;> simp [Stmt.leftK]) X (by simp [X, followsStmt])
      rw [ht, parseStmt.eq_1, ite_eq_right (by simp [hkw])]
      simp only [e1, X]
      rw [e2]; rfl
    have hList : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (.w equivWords :: .w ":" :: .indent :: .item ::
          renderTo .lead a (.item :: renderTo .lead b (.dedent :: rest)))) = some (.iff a b, rest) := by
      intro rest _
      obtain ⟨h1, e1⟩ := forget_eq.mp (ra.lead (.item :: renderTo .lead b (.dedent :: rest)) rfl)
      obtain ⟨h2, e2⟩ := forget_eq.mp (rb.lead (.dedent :: rest) rfl)
      rw [parseStmt_opened (by simp [opensStmt]), parseOpened.eq_4 lex _ _ (by simp [equivWords])
        (by simp [equivWords]) (by simp [equivWords]), ite_eq_left (rfl : equivWords = equivWords), e1]
      simp only
      rw [e2]
      rfl
    have hS : ∀ p, p = .scope ∨ p = .inner → ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo p (.iff a b) rest)) = some (.iff a b, rest) := by
      intro p hp rest hr
      by_cases hl : p = .scope ∧ a.leftK < a.prec
      · have ht : renderTo p (.iff a b) rest = .w equivWords :: .w ":" :: .indent :: .item ::
            renderTo .lead a (.item :: renderTo .lead b (.dedent :: rest)) := by
          obtain ⟨rfl, hl⟩ := hl
          simp [renderTo, mark, hl]
        rw [ht]; exact hList rest hr
      · have hn : ¬ (p ≠ .operand ∧ p ≠ .inner ∧ a.leftK < a.prec) := by
          rcases hp with rfl | rfl
          · exact fun h => hl ⟨rfl, h.2.2⟩
          · exact fun h => h.2.1 rfl
        have ht : renderTo p (.iff a b) rest = blockWith (renderTo .operand (.iff a b)) rest := by
          rw [renderTo, ite_eq_right hn]
          rcases hp with rfl | rfl <;> simp [mark, iffTo, renderTo]
        rw [ht]
        obtain ⟨r, hr'⟩ := blockWith_head (renderTo .operand (.iff a b)) rest
        exact parseStmt_op (by rw [hr']; rfl) (block_of hlex hs' hO rest) hr
    have hL : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo .lead (.iff a b) rest)) = some (.iff a b, rest) :=
      fun rest hr => by
        by_cases hl : a.leftK < a.prec
        · rw [show renderTo .lead (.iff a b) rest = .w equivWords :: .w ":" :: .indent :: .item ::
              renderTo .lead a (.item :: renderTo .lead b (.dedent :: rest)) by
            simp [renderTo, mark, hl]]
          exact hList rest hr
        · rw [show renderTo .lead (.iff a b) rest = renderTo .operand (.iff a b) rest by
            simp [renderTo, mark, iffTo, hl]]
          exact hO rest hr
    exact { operand := hO, inner := hS .inner (Or.inr rfl), lead := hL
            scope := hS .scope (Or.inl rfl), item := item_of (fun _ _ h => by cases h) hL
            wrap := wrap_of hlex hs' hO (fun h => by simp [Stmt.prec] at h)
              (fun h => by simp [Stmt.isIff] at h) }
  | tfae s ih =>
    have hs' := hs
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    obtain ⟨a, b, rfl⟩ : ∃ a b, s = .conj a b := by
      cases s with
      | conj a b => exact ⟨a, b, rfl⟩
      | _ => simp at hs
    have rs := ih hs.1
    have hop : ∀ p rest, p ≠ .item → opensStmt (renderTo p (.tfae (.conj a b)) rest) = true :=
      fun p rest hp => by simp [renderTo, mark, hp, opensStmt]
    have hP : ∀ p, p ≠ .item → ∀ rest, followsStmt rest = true →
        forget (parseOpened lex (renderTo p (.tfae (.conj a b)) rest)) =
          some (.tfae (.conj a b), rest) := by
      intro p hp rest _
      have e0 := rs.item (.dedent :: rest) rfl (fun _ h => by cases h)
      have ht : renderTo p (.tfae (.conj a b)) rest = .w tfaeKey :: .w ":" :: .indent :: .item ::
          renderTo .lead a (renderTo .item b (.dedent :: rest)) := by
        simp [renderTo, mark, hp]
      have he : renderTo .item (.conj a b) (.dedent :: rest) =
          .item :: renderTo .lead a (renderTo .item b (.dedent :: rest)) := by simp [renderTo]
      rw [he] at e0
      obtain ⟨h1, e1⟩ := forget_eq.mp e0
      rw [ht, parseOpened.eq_4 lex _ _ (by simp [tfaeKey]) (by simp [tfaeKey])
        (by simp [tfaeKey]), ite_eq_right (by simp [tfaeKey, equivWords]),
        ite_eq_left (rfl : tfaeKey = tfaeKey), e1]
      rfl
    have hS : ∀ p, p ≠ .item → ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo p (.tfae (.conj a b)) rest)) =
          some (.tfae (.conj a b), rest) :=
      fun p hp rest hr => by rw [parseStmt_opened (hop p rest hp)]; exact hP p hp rest hr
    have hO := hS .operand (by decide)
    have hL := hS .lead (by decide)
    have hOp : ∀ rest, followsStmt rest = true →
        forget (parseOperand lex (renderTo .operand (.tfae (.conj a b)) rest)) =
          some (.tfae (.conj a b), rest) :=
      fun rest hr => by
        rw [parseOperand_opened (hop .operand rest (by decide))]
        exact hP .operand (by decide) rest hr
    exact { operand := hO, inner := hS .inner (by decide), lead := hL
            scope := hS .scope (by decide)
            item := item_of (fun _ _ h => by cases h) hL
            wrap := wrap_of hlex hs' hO (fun h => by simp [Stmt.prec] at h) (fun _ => hOp) }
  | neg a iha =>
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo .operand (.neg a) rest)) = some (.neg a, rest) := by
      intro rest hr
      obtain ⟨h1, e1⟩ := forget_eq.mp ((iha hs).wrap 1 rest (by decide) hr)
      have ht : renderTo .operand (.neg a) rest = .w "it" :: .w "is" :: .w "not" :: .w "the" ::
          .w "case" :: .w "that" :: wrapWith 1 a (renderTo .operand a) rest := rfl
      rw [ht, parseOperand.eq_5, e1]; rfl
    have hO := stmt_of (fun rest => rfl) hB
    have same : ∀ p, p ≠ .item → ∀ rest,
        renderTo p (.neg a) rest = renderTo .operand (.neg a) rest :=
      fun p hp rest => by simp [renderTo, mark, hp]
    exact { operand := hO, inner := fun rest hr => by rw [same .inner (by decide)]; exact hO rest hr
            lead := fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr
            scope := fun rest hr => by rw [same .scope (by decide)]; exact hO rest hr
            item := item_of (fun _ _ h => by cases h)
              (fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr)
            wrap := wrap_of hlex hs hO (fun _ => hB) (fun _ rest hr => hB rest (followsOpnd_of hr)) }
  | rel t args =>
    have hkw : ∀ rest, opensStmt (renderTo .operand (.rel t args) rest) = false := fun rest =>
      opensStmt_of_head fun w r h => notMem_kw (render_rel_head hlex hs .operand (by decide) rest w r h)
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo .operand (.rel t args) rest)) = some (.rel t args, rest) := by
      intro rest _
      have he : renderTo .operand (.rel t args) rest = fillTo Term.renderTo args t.parts rest := rfl
      have hi : ∀ r, renderTo .operand (.rel t args) rest ≠ .indent :: r := fun r h => by
        have := parseAtomic_rel hlex hs rest
        rw [← he, h] at this
        simp [parseAtomic, Term.parse] at this
      rw [parseOperand_atomic hi (fun w r h => notMem_op (render_rel_head hlex hs .operand (by decide)
        rest w r h)) (hkw rest), he, parseAtomic_rel hlex hs]
    have hO := stmt_of hkw hB
    have same : ∀ p, p ≠ .item → ∀ rest,
        renderTo p (.rel t args) rest = renderTo .operand (.rel t args) rest :=
      fun p hp rest => by simp [renderTo, mark, hp]
    exact { operand := hO, inner := fun rest hr => by rw [same .inner (by decide)]; exact hO rest hr
            lead := fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr
            scope := fun rest hr => by rw [same .scope (by decide)]; exact hO rest hr
            item := item_of (fun _ _ h => by cases h)
              (fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr)
            wrap := wrap_of hlex hs hO (fun _ => hB) (fun _ rest hr => hB rest (followsOpnd_of hr)) }
  | atom x =>
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo .operand (.atom x) rest)) = some (.atom x, rest) := by
      intro rest hr
      have ht : renderTo .operand (.atom x) rest = .leaf x :: rest := rfl
      rw [ht, parseOperand_atomic (by simp) (by simp) rfl, parseAtomic_atom hlex x hr]
    have hO := stmt_of (fun rest => rfl) hB
    have same : ∀ p, p ≠ .item → ∀ rest,
        renderTo p (.atom x) rest = renderTo .operand (.atom x) rest :=
      fun p hp rest => by simp [renderTo, mark, hp]
    exact { operand := hO, inner := fun rest hr => by rw [same .inner (by decide)]; exact hO rest hr
            lead := fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr
            scope := fun rest hr => by rw [same .scope (by decide)]; exact hO rest hr
            item := item_of (fun _ _ h => by cases h)
              (fun rest hr => by rw [same .lead (by decide)]; exact hO rest hr)
            wrap := wrap_of hlex hs hO (fun _ => hB) (fun _ rest hr => hB rest (followsOpnd_of hr)) }

/-- A statement's tokens read back as the statement, for a well-formed lexicon whose templates it
uses with their arities. -/
public theorem parse_render_exact {lex : Lexicon} (hlex : lex.wf = true) (s : Stmt α)
    (hs : s.ok lex = true) : parse lex (render s) = some s := by
  obtain ⟨h, e⟩ := forget_eq.mp ((reads hlex s hs).lead [.w "."] rfl)
  rw [render, parse, e]
  rfl

public theorem render_inj {lex : Lexicon} (hlex : lex.wf = true) {s s' : Stmt α}
    (hs : s.ok lex = true) (hs' : s'.ok lex = true) (h : render s = render s') : s = s' := by
  have := parse_render_exact hlex s hs
  rw [h, parse_render_exact hlex s' hs'] at this
  exact (Option.some.inj this).symm

/-! ## Statements from a file's facts -/

public def Table.lexicon (tb : Table) : Lexicon := ⟨tb.rels.map (·.2), tb.phrases.map (·.2)⟩

/-- The symbols a relation's words may be, each as the formula it sets as. -/
public def relGlyph? : String → Option (Array LeanNotation.Math)
  | "=" => some #[.word "="]
  | "≠" => some #[.ctrl .neq]
  | "<" => some #[.word "<"]
  | "≤" => some #[.ctrl .leq]
  | ">" => some #[.word ">"]
  | "≥" => some #[.ctrl .geq]
  | "∣" => some #[.ctrl .mid]
  | "∈" => some #[.ctrl .mem]
  | _ => none

/-- The relations the core table says, by their symbols: equality, order, divisibility and
membership, whose collection Lean passes first from 4.12 on. -/
public def coreRels (collectionFirst : Bool) : List (String × Template) :=
  [("Eq", ⟨[.slot 1, .word "=", .slot 2]⟩),
   ("Ne", ⟨[.slot 1, .word "≠", .slot 2]⟩),
   ("LT.lt", ⟨[.slot 1, .word "<", .slot 2]⟩),
   ("LE.le", ⟨[.slot 1, .word "≤", .slot 2]⟩),
   ("GT.gt", ⟨[.slot 1, .word ">", .slot 2]⟩),
   ("GE.ge", ⟨[.slot 1, .word "≥", .slot 2]⟩),
   ("Dvd.dvd", ⟨[.slot 1, .word "∣", .slot 2]⟩),
   ("Membership.mem", if collectionFirst then ⟨[.slot 2, .word "∈", .slot 1]⟩
     else ⟨[.slot 1, .word "∈", .slot 2]⟩)]

public def coreTable (collectionFirst : Bool) : Table := ⟨coreRels collectionFirst, []⟩

/-- Whether a template's words are all symbols, so a relation through it is a formula. -/
public def Template.symbolic (t : Template) : Bool :=
  t.parts.all fun
    | .word w => (relGlyph? w).isSome
    | .slot _ => true

/-- The relations a binder predicate may write, as `∀ x ∈ S, P` writes `∀ x, x ∈ S → P`. -/
public def predRels : List String := ["Membership.mem", "LT.lt", "LE.le", "GT.gt", "GE.ge", "Ne"]

/-- Whether a binder predicate through `c` fixes its name's type: a collection's members, or a side
naming a variable in scope, of `depth` names, where a numeral alone would leave it open. -/
public def predTyped (c : String) (depth : Nat) (side : LeanFacts.Term) : Bool :=
  c == "Membership.mem" || (List.range' 1 depth).any side.reads

section
variable (lk : LeanStatement.Lookup) (tb : Table)

/-- A term as a formula. -/
public def leafOf (ctx : List String) (t : LeanFacts.Term) : Leaf :=
  LeanStatement.formulasOf lk ctx t

/-- A bound name as a formula. -/
public def nameLeaf (n : String) : Leaf := [LeanStatement.varMath n]

/-- The group binding `n` by its type `t`, `n : t`. -/
public def typedGroup (ctx : List String) (n : String) (t : LeanFacts.Term) : Group Leaf :=
  ⟨[nameLeaf n], [LeanStatement.boundOf lk ctx t], false⟩

/-- The group a binder predicate writes for the name `n` it binds: its hypothesis `hyp`, as
`n ∈ S`, where that relates `n` alone to a side that does not name it. -/
public def predGroup? (ctx : List String) (n : String) (hyp : LeanFacts.Term) : Option (Group Leaf) :=
  match hyp with
  | .apps (.const c) args =>
    if predRels.contains c then
      match LeanStatement.shownArgs lk c args with
      | [x, y] =>
        let (left, right) := if c == "Membership.mem" && lk.collectionFirst then (y, x) else (x, y)
        if left == .apps (.bvar 0) [] && !right.reads 0 && predTyped c ctx.length right then
          some ⟨[nameLeaf n], leafOf lk (n :: ctx) hyp, true⟩
        else none
      | _ => none
    else none
  | _ => none

/-- A term as a relation's argument: its constant's phrase where one applies to its explicit
arguments, else its formula. -/
public def termOf (ctx : List String) (t : LeanFacts.Term) : Term Leaf :=
  match t with
  | .apps (.const c) args =>
    match tb.phrases.lookup c with
    | some p =>
      let shown := LeanStatement.shownArgs lk c args
      if shown.length == p.arity then .phrase p (shown.map (leafOf lk ctx))
      else .leaf (leafOf lk ctx t)
    | none => .leaf (leafOf lk ctx t)
  | _ => .leaf (leafOf lk ctx t)

/-- Whether a term is a phrase's. -/
public def Term.isPhrase {β : Type} : Term β → Bool
  | .phrase .. => true
  | .leaf _ => false

/-- A proposition no connective or quantifier opens: its constant's relation where one applies to
its explicit arguments and words say it or an argument's phrase, else its formula. -/
public def atomOf (ctx : List String) (t : LeanFacts.Term) : Stmt Leaf :=
  match t with
  | .apps (.const c) args =>
    match tb.rels.lookup c with
    | some r =>
      let shown := LeanStatement.shownArgs lk c args
      let terms := shown.map (termOf lk tb ctx)
      if shown.length == r.arity && (!r.symbolic || terms.any Term.isPhrase) then .rel r terms
      else .atom (leafOf lk ctx t)
    | none => .atom (leafOf lk ctx t)
  | _ => .atom (leafOf lk ctx t)

end

/-- Whether a quantifier's groups bind a name group `g` binds. -/
public def Group.clashes (g : Group Leaf) (b : Binder Leaf) : Bool :=
  (b.first :: b.more).any fun h => h.names.any g.names.contains

/-- Group `g` before a quantifier's groups: joined into its first where both bind by one type, else a
group of its own. -/
public def Group.before (g : Group Leaf) (b : Binder Leaf) : Binder Leaf :=
  if !g.pred && !b.first.pred && g.bound == b.first.bound then
    ⟨{ g with names := g.names ++ b.first.names }, b.more⟩
  else ⟨g, b.first :: b.more⟩

/-- `∀ g, body`, a quantifier just inside it joining its groups after `g` unless it binds a name
`g` does. -/
public def forAll (g : Group Leaf) : Stmt Leaf → Stmt Leaf
  | .all b rest => if g.clashes b then .all ⟨g, []⟩ (.all b rest) else .all (g.before b) rest
  | s => .all ⟨g, []⟩ s

/-- `∃ g, body`, an existential just inside it joining its groups after `g` unless it binds a name
`g` does. -/
public def thereIs (g : Group Leaf) : Stmt Leaf → Stmt Leaf
  | .ex b rest => if g.clashes b then .ex ⟨g, []⟩ (.ex b rest) else .ex (g.before b) rest
  | s => .ex ⟨g, []⟩ s

/-- Two results joined, or the first reason either gives. -/
public def both {β γ δ : Type} (a : Except Unsaid β) (b : Except Unsaid γ) (f : β → γ → δ) :
    Except Unsaid δ :=
  match a, b with
  | .ok x, .ok y => .ok (f x y)
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-- A conjunction's spine over statements, the first outermost. -/
public def spineOf : Stmt Leaf → List (Stmt Leaf) → Stmt Leaf
  | x, [] => x
  | x, y :: ys => .conj x (spineOf y ys)

/-- Whether a statement is a conjunction, which a list's spine would take for more items. -/
public def isConjStmt (s : Stmt Leaf) : Bool := s matches .conj ..

/-- Equivalent statements in their order, the conjunctions moved first where one would end it. -/
public def tfaeOrder (items : List (Stmt Leaf)) : List (Stmt Leaf) :=
  if (items.getLast?.map isConjStmt).getD false then
    items.filter isConjStmt ++ items.filter (!isConjStmt ·)
  else items

/-- Three or more statements said as equivalent, the last no conjunction. -/
public def tfaeOf (items : List (Stmt Leaf)) : Option (Stmt Leaf) :=
  match tfaeOrder items with
  | x :: y :: z :: zs =>
    if ((tfaeOrder items).getLast?.map isConjStmt).getD true then none
    else some (.tfae (spineOf x (y :: z :: zs)))
  | _ => none

/-- Statements said as equivalent: two as an equivalence, more as a list, else `d`. -/
public def listedOf (items : List (Stmt Leaf)) (d : Stmt Leaf) : Stmt Leaf :=
  match items with
  | [a, b] => .iff a b
  | _ => (tfaeOf items).getD d

/-- Whether a term is a list literal, its constructors down to its end. -/
public def isListLit : LeanFacts.Term → Bool
  | .apps (.const "List.cons") [_, _, xs] => isListLit xs
  | .apps (.const "List.nil") [_] => true
  | _ => false

/-- The items a list literal's statements say, its conjunction spine's left sides. -/
public def itemsOf : Stmt Leaf → List (Stmt Leaf)
  | .conj x rest => x :: itemsOf rest
  | _ => []

/-- A proposition said in words, or why it cannot be: a proposition's or an instance's binder a
hypothesis, a binder predicate's its group, any other a quantifier but where `top` hides it. -/
public def stmtOf (lk : LeanStatement.Lookup) (tb : Table) (top : Bool) (ctx : List String) :
    LeanFacts.Term → Except Unsaid (Stmt Leaf)
  | .pi n b prop ty body =>
    if prop then
      if body.reads 0 then .error (.named n)
      else both (stmtOf lk tb false ctx ty) (stmtOf lk tb top (n :: ctx) body) .imp
    else if top && (b == .implicit || b == .strict) && body.reads 0 then
      stmtOf lk tb top (n :: ctx) body
    else if b == .inst then both (stmtOf lk tb false ctx ty) (stmtOf lk tb top (n :: ctx) body) .imp
    else match _hb : body with
      | .pi h _ true hyp rest =>
        match predGroup? lk ctx n hyp, rest.reads 0 with
        | some g, false => (stmtOf lk tb top (h :: n :: ctx) rest).map (forAll g)
        | _, _ => (stmtOf lk tb top (n :: ctx) body).map (forAll (typedGroup lk ctx n ty))
      | _ => (stmtOf lk tb top (n :: ctx) body).map (forAll (typedGroup lk ctx n ty))
  | .apps (.const "Exists") [_, .lam n _ dom body] =>
    match _hb : body with
    | .apps (.const "And") [hyp, rest] =>
      match predGroup? lk ctx n hyp with
      | some g => (stmtOf lk tb false (n :: ctx) rest).map (thereIs g)
      | none => (stmtOf lk tb false (n :: ctx) body).map (thereIs (typedGroup lk ctx n dom))
    | _ => (stmtOf lk tb false (n :: ctx) body).map (thereIs (typedGroup lk ctx n dom))
  | .apps (.const "And") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .conj
  | .apps (.const "Or") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .disj
  | .apps (.const "Iff") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .iff
  | t@(.apps (.const "List.TFAE") [l]) =>
    if top && isListLit l then
      (stmtOf lk tb false ctx l).map fun sp => listedOf (itemsOf sp) (atomOf lk tb ctx t)
    else .ok (atomOf lk tb ctx t)
  | .apps (.const "List.cons") [_, x, xs] => both (stmtOf lk tb false ctx x) (stmtOf lk tb false ctx xs) .conj
  | .apps (.const "Not") [a] => (stmtOf lk tb false ctx a).map .neg
  | .letE n .. => .error (.local n)
  | .lam .. => .error .function
  | t => .ok (atomOf lk tb ctx t)
termination_by t => sizeOf t

/-- The templates a statement says, after `acc`. -/
public def Stmt.templates (acc : Array Template) : Stmt α → Array Template
  | .all _ s | .ex _ s | .neg s => s.templates acc
  | .imp a b | .conj a b | .disj a b | .iff a b => b.templates (a.templates acc)
  | .tfae s => s.templates acc
  | .rel t args => args.foldl (fun acc x => match x with
      | .phrase p _ => acc.push p
      | .leaf _ => acc) (acc.push t)
  | .atom _ => acc

/-- A declaration's statement said in words, or why it cannot be: only a proposition is. -/
public def proseOf (facts : LeanFacts.Facts) (tb : Table) (d : LeanFacts.Decl)
    (type : LeanFacts.Term) : Except Unsaid (Stmt Leaf) :=
  if d.prop then stmtOf (LeanStatement.lookupOf facts d type) tb true [] type else .error .notProp

/-- The constants a declared name names: itself, else each whose name ends with it. -/
private def namedBy (facts : LeanFacts.Facts) (name : String) : List String :=
  let cs := facts.binders.toList.map (·.1)
  if cs.contains name then [name] else (cs.filter (·.endsWith ("." ++ name))).eraseDups

/-- A table with constant `c` said through `t` for its kind, after the rest. -/
public def Table.with (tb : Table) (c : String) (t : Template) : Table :=
  if isRel t then ⟨tb.rels.filter (·.1 != c) ++ [(c, t)], tb.phrases⟩
  else ⟨tb.rels, tb.phrases.filter (·.1 != c) ++ [(c, t)]⟩

/-- The constants the grammar says in its own words. -/
public def connectives : List String := ["Exists", "And", "Or", "Iff", "Not"]

/-- Whether no word of a template holds a comma, colon, parenthesis, brace or quote, or is a full
stop. -/
private def plainWords (t : Template) : Bool :=
  t.parts.all fun
    | .word w => w != "." &&
      !w.any fun c => c == ',' || c == ':' || c == '(' || c == ')' || c == '{' || c == '}' || c == '"'
    | .slot _ => true

/-- The constant a declared phrase names and its template, or why it is refused before a table
is consulted. -/
private def accept (facts : LeanFacts.Facts) (taken : List String) (name text : String) :
    Except Refusal (String × Template) :=
  match namedBy facts name with
  | [] => .error .unknown
  | [c] =>
    let t := Template.ofString text
    let args := ((facts.binders.find? (·.1 == c)).map fun e =>
      e.2.toList.countP LeanFacts.Binder.shows).getD 0
    if taken.contains c then .error .twice
    else if connectives.contains c then .error .connective
    else if !(t.wf && (isRel t || isPhrase t) && plainWords t) then .error .shape
    else if t.arity != args then .error (.arity t.arity args)
    else .ok (c, t)
  | _ :: _ :: _ => .error .ambiguous

/-- One declared phrase taken into a table with the constant it says and its template, or why it
is refused. -/
public def Table.declare (facts : LeanFacts.Facts) (taken : List String) (tb : Table)
    (name text : String) : Except Refusal (String × Template × Table) :=
  match accept facts taken name text with
  | .ok (c, t) => if (tb.with c t).lexicon.wf then .ok (c, t, tb.with c t) else .error .clash
  | .error r => .error r

/-- One declared phrase taken into a table, or refused with why. -/
private def declareStep (facts : LeanFacts.Facts) (acc : Declared) (e : String × String) :
    Declared :=
  match acc.table.declare facts acc.taken e.1 e.2 with
  | .ok (c, t, tb) =>
    { acc with table := tb, taken := c :: acc.taken, phrases := acc.phrases.push (e.1, t) }
  | .error r => { acc with refused := acc.refused.push (e.1, r) }

/-- What a page says its statements through: the core table, then each declared phrase it takes,
with each refused one and why. -/
public def tableFor (facts : LeanFacts.Facts) (declared : List (String × String)) : Declared :=
  declared.foldl (declareStep facts) ⟨coreTable facts.collectionFirst, [], #[], #[]⟩

private theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {c : String} {v : β},
    l.lookup c = some v → v ∈ l.map (·.2)
  | [], _, _, h => by simp at h
  | (k, w) :: rest, c, v, h => by
    simp only [List.lookup_cons] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

private theorem termOf_ok (lk : LeanStatement.Lookup) (tb : Table) (ctx : List String)
    (t : LeanFacts.Term) : (termOf lk tb ctx t).ok tb.lexicon = true := by
  unfold termOf
  split
  · split
    · rename_i p hp
      dsimp only
      split
      · rename_i hl
        simp only [Term.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq]
        exact ⟨lookup_mem hp, by simpa using hl⟩
      · rfl
    · rfl
  · rfl

private theorem atomOf_ok (lk : LeanStatement.Lookup) (tb : Table) (ctx : List String)
    (t : LeanFacts.Term) : (atomOf lk tb ctx t).ok tb.lexicon = true := by
  unfold atomOf
  split
  · split
    · rename_i r hr
      dsimp only
      split
      · rename_i hl
        simp only [Bool.and_eq_true] at hl
        simp only [Stmt.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true]
        refine ⟨⟨lookup_mem hr, by simpa using hl.1⟩, ?_⟩
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
        exact termOf_ok lk tb ctx a
      · rfl
    · rfl
  · rfl

private theorem forAll_ok (lex : Lexicon) (g : Group Leaf) (s : Stmt Leaf) :
    (forAll g s).ok lex = s.ok lex := by
  unfold forAll
  split
  · split <;> rfl
  · rfl

private theorem thereIs_ok (lex : Lexicon) (g : Group Leaf) (s : Stmt Leaf) :
    (thereIs g s).ok lex = s.ok lex := by
  unfold thereIs
  split
  · split <;> rfl
  · rfl

private theorem both_ok {β γ δ : Type} {a : Except Unsaid β} {b : Except Unsaid γ}
    {f : β → γ → δ} {s : δ} (h : both a b f = .ok s) :
    ∃ x y, a = .ok x ∧ b = .ok y ∧ s = f x y := by
  unfold both at h
  split at h
  · rename_i x y
    exact ⟨x, y, rfl, rfl, by simpa using h.symm⟩
  · simp at h
  · simp at h

private theorem map_ok {β γ : Type} {e : Except Unsaid β} {f : β → γ} {s : γ}
    (h : e.map f = .ok s) : ∃ x, e = .ok x ∧ s = f x := by
  cases e with
  | error _ => simp [Except.map] at h
  | ok x => exact ⟨x, rfl, by simpa [Except.map] using h.symm⟩

private theorem itemsOf_ok (lex : Lexicon) : ∀ {sp : Stmt Leaf}, sp.ok lex = true →
    ∀ x ∈ itemsOf sp, x.ok lex = true
  | .conj a b, h, x, hx => by
    simp only [Stmt.ok, Bool.and_eq_true] at h
    simp only [itemsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact itemsOf_ok lex h.2 x hx
  | .all .., _, _, hx | .ex .., _, _, hx | .imp .., _, _, hx | .disj .., _, _, hx
  | .iff .., _, _, hx | .tfae .., _, _, hx | .neg .., _, _, hx | .rel .., _, _, hx
  | .atom .., _, _, hx => by simp [itemsOf] at hx

private theorem spineOf_ok (lex : Lexicon) : ∀ (x : Stmt Leaf) (ys : List (Stmt Leaf)),
    x.ok lex = true → (∀ y ∈ ys, y.ok lex = true) → (spineOf x ys).ok lex = true
  | _, [], hx, _ => hx
  | x, y :: ys, hx, hy => by
    simp only [spineOf, Stmt.ok, Bool.and_eq_true]
    exact ⟨hx, spineOf_ok lex y ys (hy y (by simp)) (fun z hz => hy z (by simp [hz]))⟩

private theorem tfaeOf_ok (lex : Lexicon) {items : List (Stmt Leaf)}
    (h : ∀ x ∈ items, x.ok lex = true) {r : Stmt Leaf} (hr : tfaeOf items = some r) :
    r.ok lex = true := by
  have hmem : ∀ x ∈ tfaeOrder items, x.ok lex = true := by
    intro x hx
    unfold tfaeOrder at hx
    split at hx
    · simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | hx
      · exact h x hx.1
      · exact h x hx.1
    · exact h x hx
  unfold tfaeOf at hr
  split at hr
  next _ a b c cs heq =>
    split at hr
    · cases hr
    · simp only [Option.some.injEq] at hr
      subst hr
      simp only [Stmt.ok, spineOf, Bool.and_eq_true]
      refine ⟨⟨hmem a (by simp [heq]), hmem b (by simp [heq]),
        spineOf_ok lex c cs (hmem c (by simp [heq])) ?_⟩, trivial⟩
      intro z hz; exact hmem z (by simp [heq, hz])
  · cases hr

private theorem listed_ok (lex : Lexicon) {sp : Stmt Leaf} (h : sp.ok lex = true)
    {d : Stmt Leaf} (hd : d.ok lex = true) : (listedOf (itemsOf sp) d).ok lex = true := by
  have hi := itemsOf_ok lex h
  unfold listedOf
  split
  · rename_i a b heq
    simp only [Stmt.ok, Bool.and_eq_true]
    exact ⟨hi a (by simp [heq]), hi b (by simp [heq])⟩
  · cases hr : tfaeOf (itemsOf sp) with
    | none => exact hd
    | some r => exact tfaeOf_ok lex hi hr

/-- Every template a statement said in words uses is its table's, with as many arguments as
slots. -/
public theorem stmtOf_mem (lk : LeanStatement.Lookup) (tb : Table) (top : Bool)
    (ctx : List String) (t : LeanFacts.Term) {s : Stmt Leaf} (h : stmtOf lk tb top ctx t = .ok s) :
    s.ok tb.lexicon = true := by
  fun_induction stmtOf lk tb top ctx t generalizing s
  all_goals first
    | (cases h; done)
    | (rename_i ih2 ih1
       obtain ⟨x, y, hx, hy, rfl⟩ := both_ok h
       simp only [Stmt.ok, Bool.and_eq_true]
       exact ⟨ih2 hx, ih1 hy⟩)
    | (rename_i ih1
       obtain ⟨x, hx, rfl⟩ := map_ok h
       first
         | exact listed_ok _ (ih1 hx) (atomOf_ok lk tb _ _)
         | (rw [forAll_ok]; exact ih1 hx)
         | (rw [thereIs_ok]; exact ih1 hx)
         | (simp only [Stmt.ok]; exact ih1 hx))
    | (rename_i ih1; exact ih1 h)
    | (simp only [Except.ok.injEq] at h; subst h; exact atomOf_ok lk tb _ _)

/-- The words a declaration's statement is said in read back as that statement, through a table
whose lexicon is well formed. -/
public theorem proseOf_parse_exact {facts : LeanFacts.Facts} {tb : Table} {d : LeanFacts.Decl}
    {type : LeanFacts.Term} {s : Stmt Leaf} (htb : tb.lexicon.wf = true)
    (h : proseOf facts tb d type = .ok s) : parse tb.lexicon (render s) = some s := by
  unfold proseOf at h
  split at h
  · exact parse_render_exact htb s (stmtOf_mem _ tb true [] type h)
  · cases h

end LeanTex.Core.LeanProse
