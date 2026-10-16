module

public import LeanTex.Core.LeanStatement

/-! # A Lean statement in words

A controlled English whose parser reads its renderer back, and a declaration's type said in it. -/

namespace LeanTex.Core.LeanProse

open LeanTex.Core

/-- A token: a word, an opaque leaf (a formula or a bound name) the grammar never inspects, or a
block's bounds, which a page sets as lines indented one step deeper than the line before. -/
public inductive Tok (α : Type) where
  | w (s : String)
  | leaf (a : α)
  | indent
  | dedent
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

/-- A binder's noun, its bound names, the first and any more, and an optional domain, as in "every
element x of S". -/
public structure Binder (α : Type) where
  noun : List String
  name : α
  more : List α
  dom : Option α
  deriving BEq, Repr

public inductive Stmt (α : Type) where
  | all (b : Binder α) (body : Stmt α)
  | ex (b : Binder α) (body : Stmt α)
  | imp (hyp concl : Stmt α)
  | conj (a b : Stmt α)
  | disj (a b : Stmt α)
  | iff (a b : Stmt α)
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

/-- What a binder ranges over: its noun in the singular and the plural, and the domain it names. -/
public structure Noun where
  one : List String
  many : List String
  dom : Option Leaf
  deriving Repr, BEq, Inhabited

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
private def stops : List String := ["and", "or", ",", "if"]

/-- The words that open a statement or an operand, so no phrase begins with one. -/
private def opens : List String := ["for", "there", "if", "both", "either", "it"]

private def isRel (t : Template) : Bool :=
  match t.parts with
  | .slot _ :: ps => match lead ps with
    | s :: _ => !stops.contains s
    | [] => false
  | _ => false

private def isPhrase (t : Template) : Bool :=
  match t.parts with
  | .word s :: _ => !opens.contains s
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

/-- Every template used is the lexicon's, with as many arguments as slots. -/
public def Stmt.ok (lex : Lexicon) : Stmt α → Bool
  | .all _ s | .ex _ s | .neg s => s.ok lex
  | .imp a b | .conj a b | .disj a b | .iff a b => a.ok lex && b.ok lex
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

/-- Bound names before `rest`: one, or several with commas between and "and" before the last. -/
private def nameToks : α → List α → List (Tok α) → List (Tok α)
  | x, [], rest => .leaf x :: rest
  | x, [y], rest => .leaf x :: .w "and" :: .leaf y :: rest
  | x, y :: z :: r, rest => .leaf x :: .w "," :: nameToks y (z :: r) rest

/-- A domain's tokens before `rest`: after "of", or after "in" when the binder has no noun. -/
private def domToks (noun : List String) : Option α → List (Tok α) → List (Tok α)
  | some d, rest => .w (if noun.isEmpty then "in" else "of") :: .leaf d :: rest
  | none, rest => rest

/-- A binder's tokens before `rest`. -/
private def Binder.renderTo (b : Binder α) (rest : List (Tok α)) : List (Tok α) :=
  wordsTo b.noun (nameToks b.name b.more (domToks b.noun b.dom rest))

/-- The indefinite article before a noun, or "some" before none. -/
private def article : List String → String
  | s :: _ => if s.toList.head?.any ("aeiou".toList.contains ·.toLower) then "an" else "a"
  | [] => "some"

/-- Whether a template's words hold one a connective splits a sentence at. -/
private def Template.splits (t : Template) : Bool :=
  t.parts.any fun
    | .word w => w == "and" || w == "or" || w == "if"
    | .slot _ => false

private def Term.splits : Term α → Bool
  | .leaf _ => false
  | .phrase t _ => t.splits

/-- How loosely a statement binds: 0 atomic, 1 delimited by its own words, 2 the rest, a relation
whose words hold a connective's among them. -/
private def Stmt.prec : Stmt α → Nat
  | .rel t args => if t.splits || args.any Term.splits then 2 else 0
  | .atom _ => 0
  | .neg _ | .conj .. | .disj .. => 1
  | .all .. | .ex .. | .imp .. | .iff .. => 2

private def Stmt.isImp : Stmt α → Bool
  | .imp .. => true
  | .all .. | .ex .. | .conj .. | .disj .. | .iff .. | .neg _ | .rel .. | .atom _ => false

private def Stmt.isIff : Stmt α → Bool
  | .iff .. => true
  | .all .. | .ex .. | .imp .. | .conj .. | .disj .. | .neg _ | .rel .. | .atom _ => false

/-- Tokens `f` before `rest` as a block. -/
private def blockWith (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) : List (Tok α) :=
  .indent :: f (.dedent :: rest)

/-- An operand's tokens `f` before `rest`, bare up to precedence `k`, else a block. -/
private def wrapWith (k : Nat) (s : Stmt α) (f : List (Tok α) → List (Tok α))
    (rest : List (Tok α)) : List (Tok α) :=
  if s.prec ≤ k then f rest else blockWith f rest

/-- A quantifier's body or a conclusion, which runs to its scope's end: a block where its "if and
only if" would otherwise read as ending that scope. -/
private def scopeWith (s : Stmt α) (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) :
    List (Tok α) :=
  if s.isIff then blockWith f rest else f rest

/-- What follows a hypothesis: the next one of a curried implication, or its conclusion. -/
private def chainWith (c : Stmt α) (f : List (Tok α) → List (Tok α)) (rest : List (Tok α)) :
    List (Tok α) :=
  if c.isImp then .w "and" :: (f rest).tail else .w "," :: .w "then" :: f rest

/-- A quantifier's opening words: singular before one name, plural before several. -/
private def allWords (b : Binder α) : List String :=
  ["for", if b.more.isEmpty then "every" else "all"]

private def exWords (b : Binder α) : List String :=
  if b.more.isEmpty then ["there", "is", article b.noun] else ["there", "are"]

/-- A statement's tokens before `rest`. -/
private def renderTo : Stmt α → List (Tok α) → List (Tok α)
  | .all b s, rest => wordsTo (allWords b) (b.renderTo (.w "," :: scopeWith s (renderTo s) rest))
  | .ex b s, rest =>
    wordsTo (exWords b) (b.renderTo (.w "such" :: .w "that" :: scopeWith s (renderTo s) rest))
  | .imp h c, rest =>
    .w "if" :: wrapWith (if c.isImp then 0 else 1) h (renderTo h)
      (chainWith c (scopeWith c (renderTo c)) rest)
  | .conj a b, rest =>
    .w "both" :: wrapWith 0 a (renderTo a) (.w "and" :: wrapWith 1 b (renderTo b) rest)
  | .disj a b, rest =>
    .w "either" :: wrapWith 0 a (renderTo a) (.w "or" :: wrapWith 1 b (renderTo b) rest)
  | .iff a b, rest =>
    wrapWith 0 a (renderTo a) (wordsTo ["if", "and", "only", "if"] (wrapWith 1 b (renderTo b) rest))
  | .neg a, rest =>
    wordsTo ["it", "is", "not", "the", "case", "that"] (wrapWith 1 a (renderTo a) rest)
  | .rel t args, rest => fillTo Term.renderTo args t.parts rest
  | .atom x, rest => .leaf x :: rest

public def render (s : Stmt α) : List (Tok α) := renderTo s []

/-- Whether a token sets against the one before it, with no space: a comma or a full stop does. -/
public def Tok.joins : Tok α → Bool
  | .w s => s == "," || s == "."
  | .leaf _ | .indent | .dedent => false

/-- A comma or full stop after blocks moved inside the last of them, where a page sets it: at the end
of that block's last line. -/
public def closeIn : List (Tok α) → List (Tok α)
  | .dedent :: rest => match closeIn rest with
    | .w s :: r => if s == "," || s == "." then .w s :: .dedent :: r else .dedent :: .w s :: r
    | r => .dedent :: r
  | t :: rest => t :: closeIn rest
  | [] => []

/-- A sentence's lines, each with its depth and its tokens, a block's lines one deeper than the line
before it. -/
public def layoutLines (l : List (Tok α)) : Array (Nat × List (Tok α)) :=
  let flush (acc : Nat × Array (Tok α) × Array (Nat × List (Tok α))) :=
    if acc.2.1.isEmpty then acc.2.2 else acc.2.2.push (acc.1, acc.2.1.toList)
  let step (acc : Nat × Array (Tok α) × Array (Nat × List (Tok α))) (t : Tok α) :=
    match t with
    | .indent => (acc.1 + 1, #[], flush acc)
    | .dedent => (acc.1 - 1, #[], flush acc)
    | .w _ | .leaf _ => (acc.1, acc.2.1.push t, acc.2.2)
  flush (l.foldl step (0, #[], #[]))

/-- One line's tokens as text, a space between two but where they join. -/
public def lineText (f : α → String) (l : List (Tok α)) : String :=
  (l.foldl (fun (acc : String × Bool) t =>
    let text := match t with
      | .w s => s
      | .leaf a => f a
      | .indent | .dedent => ""
    ((if acc.2 || t.joins then acc.1 else acc.1.push ' ') ++ text, false)) ("", true)).1

/-- The tokens as text in their lines, four spaces of indent for each step of depth. -/
public def showToks (f : α → String) (l : List (Tok α)) : String :=
  "\n".intercalate ((layoutLines (closeIn l)).toList.map fun (d, ts) =>
    String.ofList (List.replicate (4 * d) ' ') ++ lineText f ts)

private def spanWords : List (Tok α) → List String × List (Tok α)
  | .w s :: t => let p := spanWords t; (s :: p.1, p.2)
  | t => ([], t)

/-- Two or more bound names, "and" before the last. -/
private def parseNames : List (Tok α) → Option (α × List α × List (Tok α))
  | .leaf x :: .w "and" :: .leaf y :: r => some (x, [y], r)
  | .leaf x :: .w "," :: r => (parseNames r).map fun (y, ys, r') => (x, y :: ys, r')
  | _ => none

/-- One bound name, or two or more when `many`. -/
private def parseNamed (many : Bool) (t : List (Tok α)) : Option (α × List α × List (Tok α)) :=
  if many then parseNames t else match t with
    | .leaf x :: r => some (x, [], r)
    | _ => none

private def parseDom : List (Tok α) → Option α × List (Tok α)
  | .w "of" :: .leaf d :: r => (some d, r)
  | .w "in" :: .leaf d :: r => (some d, r)
  | t => (none, t)

private def parseBinder (many : Bool) (t : List (Tok α)) : Option (Binder α × List (Tok α)) :=
  (parseNamed many (spanWords t).2).map fun (x, xs, r) =>
    (⟨(spanWords t).1, x, xs, (parseDom r).1⟩, (parseDom r).2)

private def isArticle (s : String) : Bool := s == "a" || s == "an" || s == "some"

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
  | .indent :: _ => none
  | .dedent :: _ => none
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

private theorem spanWords_len (t : List (Tok α)) : (spanWords t).2.length ≤ t.length := by
  induction t with
  | nil => simp [spanWords]
  | cons x t ih => cases x <;> simp [spanWords]; omega

private theorem parseNames_len (t : List (Tok α)) : ∀ {r : List (Tok α)} {x : α} {xs : List α},
    parseNames t = some (x, xs, r) → r.length < t.length := by
  fun_induction parseNames t <;> intro r x xs h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [List.length_cons]; omega
  · rename_i ih
    obtain ⟨⟨y, ys, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, -, rfl⟩ := h2
    have := ih h1
    simp; omega
  · simp at h

private theorem parseNamed_len (many : Bool) (t : List (Tok α)) {r : List (Tok α)} {x : α}
    {xs : List α} (h : parseNamed many t = some (x, xs, r)) : r.length < t.length := by
  unfold parseNamed at h
  split at h
  · exact parseNames_len t h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      simp
    · simp at h

private theorem parseDom_len (t : List (Tok α)) : (parseDom t).2.length ≤ t.length := by
  unfold parseDom
  split <;> simp <;> omega

private theorem parseBinder_len {many : Bool} {t r : List (Tok α)} {b : Binder α}
    (h : parseBinder many t = some (b, r)) : r.length < t.length := by
  unfold parseBinder at h
  obtain ⟨⟨x, xs, r'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  have := parseNamed_len many _ h1
  have := spanWords_len t
  have := parseDom_len r'
  omega

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

/-- A parse with its remainder, shorter than the input. -/
private abbrev Parsed (α β : Type) (t : List (Tok α)) :=
  Option (β × {r : List (Tok α) // r.length < t.length})

mutual
private def parseStmt (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match t with
  | .w "for" :: .w q :: t =>
    if q = "every" ∨ q = "all" then
      match h : parseBinder (decide (q = "all")) t with
      | some (b, .w "," :: r) => (parseStmt lex r).map fun (s, r') =>
        (.all b s, ⟨r'.1, by
          have h1 := parseBinder_len h; have h2 := r'.2
          simp only [List.length_cons] at h1 h2 ⊢; omega⟩)
      | _ => none
    else none
  | .w "there" :: .w "is" :: .w a :: t =>
    if isArticle a then
      match h : parseBinder false t with
      | some (b, .w "such" :: .w "that" :: r) => (parseStmt lex r).map fun (s, r') =>
        (.ex b s, ⟨r'.1, by
          have h1 := parseBinder_len h; have h2 := r'.2
          simp only [List.length_cons] at h1 h2 ⊢; omega⟩)
      | _ => none
    else none
  | .w "there" :: .w "are" :: t =>
    match h : parseBinder true t with
    | some (b, .w "such" :: .w "that" :: r) => (parseStmt lex r).map fun (s, r') =>
      (.ex b s, ⟨r'.1, by
        have h1 := parseBinder_len h; have h2 := r'.2
        simp only [List.length_cons] at h1 h2 ⊢; omega⟩)
    | _ => none
  | .w "if" :: t => (parseHyps lex t).map fun (s, r) =>
    (s, ⟨r.1, by have h1 := r.2; simp only [List.length_cons] at h1 ⊢; omega⟩)
  | t =>
    let o := parseOperand lex t
    match o with
    | some (a, ⟨.w "if" :: .w "and" :: .w "only" :: .w "if" :: r, h⟩) =>
      (parseOperand lex r).map fun (b, r') =>
        (.iff a b, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at h h1; omega⟩)
    | _ => o
termination_by 2 * t.length + 1
decreasing_by
  all_goals try simp only [List.length_cons] at *
  all_goals first
    | omega
    | (have := parseBinder_len h; simp only [List.length_cons] at this; omega)

/-- The hypotheses after "if", then the conclusion. -/
private def parseHyps (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match parseOperand lex t with
  | some (h, ⟨.w "and" :: r, hr⟩) => (parseHyps lex r).map fun (c, r') =>
    (.imp h c, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at hr h1; omega⟩)
  | some (h, ⟨.w "," :: .w "then" :: r, hr⟩) => (parseStmt lex r).map fun (c, r') =>
    (.imp h c, ⟨r'.1, by have h1 := r'.2; simp only [List.length_cons] at hr h1; omega⟩)
  | _ => none
termination_by 2 * t.length + 1
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)

private def parseOperand (lex : Lexicon) (t : List (Tok α)) : Parsed α (Stmt α) t :=
  match t with
  | .indent :: t => match parseStmt lex t with
    | some (s, ⟨.dedent :: r, h⟩) => some (s, ⟨r, by simp at h ⊢; omega⟩)
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
  | t => match h : parseAtomic lex t with
    | some (s, r) => some (s, ⟨r, parseAtomic_len h⟩)
    | _ => none
termination_by 2 * t.length
decreasing_by all_goals ((try simp only [List.length_cons] at *); omega)
end

public def parse (lex : Lexicon) (t : List (Tok α)) : Option (Stmt α) :=
  match parseStmt lex t with
  | some (s, ⟨[], _⟩) => some s
  | _ => none


/-- A continuation that may follow a statement: the end, or a block's end. -/
private def followsStmt : List (Tok α) → Bool
  | [] | .dedent :: _ => true
  | .w _ :: _ | .leaf _ :: _ | .indent :: _ => false

/-- A continuation that may follow an operand: the end, a block's end, or a word in `stops`. -/
private def followsOpnd : List (Tok α) → Bool
  | [] | .dedent :: _ => true
  | .w s :: _ => stops.contains s
  | .leaf _ :: _ | .indent :: _ => false

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
  · rename_i s ps heq; exact ⟨s, ps, heq, by simpa using h⟩
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

private theorem spanWords_wordsTo (n : List String) (x : α) (r : List (Tok α)) :
    spanWords (wordsTo n (.leaf x :: r)) = (n, .leaf x :: r) := by
  induction n with
  | nil => rfl
  | cons s n ih =>
    show spanWords (.w s :: wordsTo n (.leaf x :: r)) = (s :: n, .leaf x :: r)
    simp only [spanWords, ih]

private theorem nameToks_head (x : α) (xs : List α) (rest : List (Tok α)) :
    ∃ r, nameToks x xs rest = .leaf x :: r := by
  match xs with
  | [] => exact ⟨rest, rfl⟩
  | [_] => exact ⟨_, rfl⟩
  | _ :: _ :: _ => exact ⟨_, rfl⟩

private theorem parseNames_nameToks : ∀ (x : α) (xs : List α) (rest : List (Tok α)), xs ≠ [] →
    parseNames (nameToks x xs rest) = some (x, xs, rest)
  | _, [], _, h => (h rfl).elim
  | x, [y], rest, _ => by simp [nameToks, parseNames]
  | x, y :: z :: r, rest, _ => by
    have ih := parseNames_nameToks y (z :: r) rest (by simp)
    simp only [nameToks]
    rw [parseNames, ih]
    rfl

private theorem parseDom_domToks (noun : List String) (d : Option α) (s : String) (r : List (Tok α))
    (hs : s ∉ ["of", "in"]) : parseDom (domToks noun d (.w s :: r)) = (d, .w s :: r) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  cases d with
  | none => simp [domToks, parseDom, hs]
  | some d => by_cases hn : noun.isEmpty <;> simp [domToks, parseDom, hn]

private theorem parseBinder_render (b : Binder α) (s : String) (r : List (Tok α))
    (hs : s ∉ ["of", "in"]) :
    parseBinder (!b.more.isEmpty) (b.renderTo (.w s :: r)) = some (b, .w s :: r) := by
  obtain ⟨n, x, xs, d⟩ := b
  obtain ⟨tail, ht⟩ := nameToks_head x xs (domToks n d (.w s :: r))
  have hspan : spanWords (Binder.renderTo ⟨n, x, xs, d⟩ (.w s :: r)) =
      (n, nameToks x xs (domToks n d (.w s :: r))) := by
    simp only [Binder.renderTo]
    rw [ht, spanWords_wordsTo]
  have hnamed : parseNamed (!xs.isEmpty) (nameToks x xs (domToks n d (.w s :: r))) =
      some (x, xs, domToks n d (.w s :: r)) := by
    cases xs with
    | nil => simp [parseNamed, nameToks]
    | cons y ys => simp [parseNamed, parseNames_nameToks x (y :: ys) _ (by simp)]
  simp only [parseBinder, hspan, hnamed, Option.map_some, parseDom_domToks n d s r hs]

private theorem notMem_kw {w : String} (h : w ∉ opens) : w ∉ ["for", "there", "if"] :=
  fun hm => h (List.subset_def.mp (by simp [opens]) hm)

private theorem notMem_op {w : String} (h : w ∉ opens) : w ∉ ["both", "either", "it"] :=
  fun hm => h (List.subset_def.mp (by simp [opens]) hm)

/-- A relation's tokens open with a leaf or with a word no statement or operand opens with. -/
private theorem render_rel_head {lex : Lexicon} (hlex : lex.wf = true) {t : Template}
    {args : List (Term α)} (hs : (Stmt.rel t args).ok lex = true) (rest : List (Tok α)) :
    ∀ w r, renderTo (.rel t args) rest = .w w :: r → w ∉ opens := by
  obtain ⟨hrels, hphr, -, -⟩ := wf_parts hlex
  simp only [Stmt.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨ht, hl⟩, hargs⟩ := hs
  obtain ⟨hwf, hrel⟩ := hrels t ht
  obtain ⟨k, -, -, ps, hps, -, -⟩ := isRel_parts hrel
  have hk := wf_isSome hwf hl
  simp only [Template.slots, hps, slotsOf, List.mem_cons, forall_eq_or_imp] at hk
  obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hk.1
  intro w r h
  simp only [renderTo, hps, fillTo, hx₀] at h
  have hx := hargs x₀ (arg?_mem hx₀)
  cases x₀ with
  | leaf a => simp [Term.renderTo] at h
  | phrase p qs =>
    simp only [Term.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hx
    obtain ⟨s, ps', hps', hs'⟩ := isPhrase_parts (hphr p hx.1).2
    simp only [Term.renderTo, hps', fillTo, List.cons.injEq, Tok.w.injEq] at h
    exact h.1 ▸ hs'

private theorem parseAtomic_rel {lex : Lexicon} (hlex : lex.wf = true) {t : Template}
    {args : List (Term α)} (hs : (Stmt.rel t args).ok lex = true) (rest : List (Tok α)) :
    parseAtomic lex (renderTo (.rel t args) rest) = some (.rel t args, rest) := by
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
  simp only [renderTo, hps, fillTo, hx₀, parseAtomic, hterm x₀ (arg?_mem hx₀), Option.bind_some,
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

private theorem isArticle_article (n : List String) : isArticle (article n) = true := by
  unfold article
  split
  · split <;> rfl
  · rfl

private theorem parseStmt_if {lex : Lexicon} (t : List (Tok α)) :
    forget (parseStmt lex (.w "if" :: t)) = forget (parseHyps lex t) := by
  rw [parseStmt.eq_4]
  cases parseHyps lex t with
  | none => rfl
  | some p => obtain ⟨s, r, h⟩ := p; rfl

private theorem parseStmt_op {lex : Lexicon} {t rest : List (Tok α)} {s : Stmt α}
    (hkw : ∀ w r, t = .w w :: r → w ∉ ["for", "there", "if"])
    (ho : forget (parseOperand lex t) = some (s, rest)) (hr : followsStmt rest = true) :
    forget (parseStmt lex t) = some (s, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp ho
  rw [parseStmt.eq_5 lex t (fun _ _ ht => hkw _ _ ht (by simp))
    (fun _ _ ht => hkw _ _ ht (by simp)) (fun _ ht => hkw _ _ ht (by simp))
    (fun _ ht => hkw _ _ ht (by simp)), e]
  match rest, hr, h with
  | [], _, _ => rfl
  | .dedent :: _, _, _ => rfl

private theorem parseOperand_atomic {lex : Lexicon} {t : List (Tok α)}
    (hi : ∀ r, t ≠ .indent :: r) (h : ∀ w r, t = .w w :: r → w ∉ ["both", "either", "it"]) :
    forget (parseOperand lex t) = parseAtomic lex t := by
  rw [parseOperand.eq_5 lex t (fun _ ht => hi _ ht) (fun _ ht => h _ _ ht (by simp))
    (fun _ ht => h _ _ ht (by simp)) (fun _ ht => h _ _ ht (by simp))]
  split
  · rename_i s r heq; simp [forget, heq]
  · rename_i hne
    cases hp : parseAtomic lex t with
    | none => rfl
    | some p => exact (hne p.1 p.2 hp).elim

private theorem wrap0_head {lex : Lexicon} (hlex : lex.wf = true) {a : Stmt α}
    (ha : a.ok lex = true) (X : List (Tok α)) :
    ∀ w r, wrapWith 0 a (renderTo a) X = .w w :: r → w ∉ ["for", "there", "if"] := by
  intro w r h
  unfold wrapWith at h
  by_cases hp : a.prec ≤ 0
  · rw [ite_eq_left hp] at h
    cases a with
    | rel t args => exact notMem_kw (render_rel_head hlex ha X w r h)
    | atom x => simp [renderTo] at h
    | _ => simp [Stmt.prec] at hp
  · rw [ite_eq_right hp, blockWith] at h
    simp at h

/-- A statement's tokens as a block read back as an operand. -/
private theorem block_of {lex : Lexicon} {s : Stmt α}
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo s rest)) = some (s, rest)) (rest : List (Tok α)) :
    forget (parseOperand lex (blockWith (renderTo s) rest)) = some (s, rest) := by
  obtain ⟨h, e⟩ := forget_eq.mp (hS (.dedent :: rest) rfl)
  rw [blockWith, parseOperand.eq_1, e]
  rfl

/-- An operand reads back at every wrapping level up to 1, bare or as a block. -/
private theorem wrap_of {lex : Lexicon} {s : Stmt α}
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo s rest)) = some (s, rest))
    (hB : s.prec ≤ 1 → ∀ rest, followsOpnd rest = true →
      forget (parseOperand lex (renderTo s rest)) = some (s, rest)) :
    ∀ k rest, k ≤ 1 → followsOpnd rest = true →
      forget (parseOperand lex (wrapWith k s (renderTo s) rest)) = some (s, rest) := by
  intro k rest hk hr
  unfold wrapWith
  by_cases hp : s.prec ≤ k
  · rw [ite_eq_left hp]; exact hB (by omega) rest hr
  · rw [ite_eq_right hp]; exact block_of hS rest

/-- A scope reads back, bare or as a block, before a continuation a statement may stand before. -/
private theorem scope_of {lex : Lexicon} {s : Stmt α}
    (hS : ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo s rest)) = some (s, rest)) (rest : List (Tok α))
    (hr : followsStmt rest = true) :
    forget (parseStmt lex (scopeWith s (renderTo s) rest)) = some (s, rest) := by
  unfold scopeWith
  by_cases hi : s.isIff = true
  · rw [ite_eq_left hi]
    exact parseStmt_op (fun w r ht => by simp [blockWith] at ht) (block_of hS rest) hr
  · rw [ite_eq_right hi]; exact hS rest hr

private theorem stmt_of {lex : Lexicon} {s : Stmt α}
    (hkw : ∀ rest w r, renderTo s rest = .w w :: r → w ∉ ["for", "there", "if"])
    (hB : ∀ rest, followsOpnd rest = true →
      forget (parseOperand lex (renderTo s rest)) = some (s, rest)) :
    ∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo s rest)) = some (s, rest) :=
  fun rest hr => parseStmt_op (hkw rest) (hB rest (followsOpnd_of hr)) hr

private theorem quant_all {lex : Lexicon} (b : Binder α) {body : Stmt α} {rest : List (Tok α)}
    (e1 : ∃ h, parseStmt lex (scopeWith body (renderTo body) rest) = some (body, ⟨rest, h⟩)) :
    forget (parseStmt lex (renderTo (.all b body) rest)) = some (.all b body, rest) := by
  obtain ⟨h1, e1⟩ := e1
  have hq : ∀ q, q = (if b.more.isEmpty then "every" else "all") →
      (q = "every" ∨ q = "all") ∧ decide (q = "all") = !b.more.isEmpty := by
    intro q hq; subst hq; cases b.more.isEmpty <;> decide
  obtain ⟨hor, hdec⟩ := hq _ rfl
  have ht : renderTo (.all b body) rest =
      .w "for" :: .w (if b.more.isEmpty then "every" else "all") ::
      b.renderTo (.w "," :: scopeWith body (renderTo body) rest) := by
    simp [renderTo, wordsTo, allWords]
  rw [ht, parseStmt.eq_1, ite_eq_left hor]
  split
  · rename_i heq
    rw [hdec, parseBinder_render b "," _ (by decide)] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, -, rfl⟩ := heq
    rw [e1]; rfl
  · rename_i hne
    exact (hne b _ (by rw [hdec]; exact parseBinder_render b "," _ (by decide))).elim

private theorem quant_ex {lex : Lexicon} (b : Binder α) {body : Stmt α} {rest : List (Tok α)}
    (e1 : ∃ h, parseStmt lex (scopeWith body (renderTo body) rest) = some (body, ⟨rest, h⟩)) :
    forget (parseStmt lex (renderTo (.ex b body) rest)) = some (.ex b body, rest) := by
  obtain ⟨h1, e1⟩ := e1
  have hb := parseBinder_render b "such" (.w "that" :: scopeWith body (renderTo body) rest) (by decide)
  cases hm : b.more.isEmpty with
  | true =>
    have ht : renderTo (.ex b body) rest = .w "there" :: .w "is" :: .w (article b.noun) ::
        b.renderTo (.w "such" :: .w "that" :: scopeWith body (renderTo body) rest) := by
      simp [renderTo, wordsTo, exWords, hm]
    rw [hm, Bool.not_true] at hb
    rw [ht, parseStmt.eq_2, ite_eq_left (isArticle_article b.noun)]
    split
    · rename_i heq
      rw [hb] at heq
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
      obtain ⟨rfl, -, -, rfl⟩ := heq
      rw [e1]; rfl
    · rename_i hne; exact (hne b _ hb).elim
  | false =>
    have ht : renderTo (.ex b body) rest = .w "there" :: .w "are" ::
        b.renderTo (.w "such" :: .w "that" :: scopeWith body (renderTo body) rest) := by
      simp [renderTo, wordsTo, exWords, hm]
    rw [hm, Bool.not_false] at hb
    rw [ht, parseStmt.eq_3]
    split
    · rename_i heq
      rw [hb] at heq
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
      obtain ⟨rfl, -, -, rfl⟩ := heq
      rw [e1]; rfl
    · rename_i hne; exact (hne b _ hb).elim

/-- Parsing a statement's tokens, or an operand's, before a continuation in its follow set returns
the statement and the continuation. -/
private theorem parseStmt_render_exact {lex : Lexicon} (hlex : lex.wf = true) (s : Stmt α)
    (hs : s.ok lex = true) :
    (∀ rest, followsStmt rest = true →
      forget (parseStmt lex (renderTo s rest)) = some (s, rest)) ∧
    (∀ k rest, k ≤ 1 → followsOpnd rest = true →
      forget (parseOperand lex (wrapWith k s (renderTo s) rest)) = some (s, rest)) := by
  induction s with
  | all b body ih =>
    have hS : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo (.all b body) rest)) = some (.all b body, rest) :=
      fun rest hr => quant_all b (forget_eq.mp (scope_of (ih hs).1 rest hr))
    exact ⟨hS, wrap_of hS (fun h => by simp [Stmt.prec] at h)⟩
  | ex b body ih =>
    have hS : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo (.ex b body) rest)) = some (.ex b body, rest) :=
      fun rest hr => quant_ex b (forget_eq.mp (scope_of (ih hs).1 rest hr))
    exact ⟨hS, wrap_of hS (fun h => by simp [Stmt.prec] at h)⟩
  | imp h c ihh ihc =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have hS : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo (.imp h c) rest)) = some (.imp h c, rest) := by
      intro rest hr
      cases hc : c.isImp with
      | true =>
        cases c with
        | imp h' c' =>
          let Y := wrapWith (if c'.isImp then 0 else 1) h' (renderTo h')
            (chainWith c' (scopeWith c' (renderTo c')) rest)
          have hc1 := (ihc hs.2).1 rest hr
          rw [show renderTo (.imp h' c') rest = .w "if" :: Y from rfl, parseStmt_if] at hc1
          obtain ⟨h2, e2⟩ := forget_eq.mp hc1
          obtain ⟨h1, e1⟩ := forget_eq.mp ((ihh hs.1).2 0 (.w "and" :: Y) (by decide)
            (by simp [followsOpnd, stops]))
          have ht : renderTo (.imp h (.imp h' c')) rest =
              .w "if" :: wrapWith 0 h (renderTo h) (.w "and" :: Y) := by
            simp [renderTo, chainWith, scopeWith, Stmt.isImp, Stmt.isIff, Y]
          rw [ht, parseStmt_if, parseHyps.eq_1, e1]
          simp only
          rw [e2]; rfl
        | _ => simp [Stmt.isImp] at hc
      | false =>
        obtain ⟨h2, e2⟩ := forget_eq.mp (scope_of (ihc hs.2).1 rest hr)
        obtain ⟨h1, e1⟩ := forget_eq.mp ((ihh hs.1).2 1
          (.w "," :: .w "then" :: scopeWith c (renderTo c) rest) (by decide)
          (by simp [followsOpnd, stops]))
        have ht : renderTo (.imp h c) rest = .w "if" ::
            wrapWith 1 h (renderTo h) (.w "," :: .w "then" :: scopeWith c (renderTo c) rest) := by
          simp [renderTo, chainWith, hc]
        rw [ht, parseStmt_if, parseHyps.eq_1, e1]
        simp only
        rw [e2]; rfl
    exact ⟨hS, wrap_of hS (fun h => by simp [Stmt.prec] at h)⟩
  | conj a b iha ihb =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo (.conj a b) rest)) = some (.conj a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp ((ihb hs.2).2 1 rest (by decide) hr)
      obtain ⟨h1, e1⟩ := forget_eq.mp ((iha hs.1).2 0 (.w "and" :: wrapWith 1 b (renderTo b) rest)
        (by decide) (by simp [followsOpnd, stops]))
      have ht : renderTo (.conj a b) rest =
          .w "both" :: wrapWith 0 a (renderTo a) (.w "and" :: wrapWith 1 b (renderTo b) rest) := rfl
      rw [ht, parseOperand.eq_2, e1]
      simp only
      rw [e2]; rfl
    have hS := stmt_of (fun rest w r h => by
      simp only [renderTo, List.cons.injEq, Tok.w.injEq] at h
      rw [← h.1]; decide) hB
    exact ⟨hS, wrap_of hS (fun _ => hB)⟩
  | disj a b iha ihb =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo (.disj a b) rest)) = some (.disj a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp ((ihb hs.2).2 1 rest (by decide) hr)
      obtain ⟨h1, e1⟩ := forget_eq.mp ((iha hs.1).2 0 (.w "or" :: wrapWith 1 b (renderTo b) rest)
        (by decide) (by simp [followsOpnd, stops]))
      have ht : renderTo (.disj a b) rest =
          .w "either" :: wrapWith 0 a (renderTo a) (.w "or" :: wrapWith 1 b (renderTo b) rest) :=
        rfl
      rw [ht, parseOperand.eq_3, e1]
      simp only
      rw [e2]; rfl
    have hS := stmt_of (fun rest w r h => by
      simp only [renderTo, List.cons.injEq, Tok.w.injEq] at h
      rw [← h.1]; decide) hB
    exact ⟨hS, wrap_of hS (fun _ => hB)⟩
  | iff a b iha ihb =>
    simp only [Stmt.ok, Bool.and_eq_true] at hs
    have hS : ∀ rest, followsStmt rest = true →
        forget (parseStmt lex (renderTo (.iff a b) rest)) = some (.iff a b, rest) := by
      intro rest hr
      obtain ⟨h2, e2⟩ := forget_eq.mp ((ihb hs.2).2 1 rest (by decide) (followsOpnd_of hr))
      let X : List (Tok α) :=
        .w "if" :: .w "and" :: .w "only" :: .w "if" :: wrapWith 1 b (renderTo b) rest
      obtain ⟨h1, e1⟩ :=
        forget_eq.mp ((iha hs.1).2 0 X (by decide) (by simp [X, followsOpnd, stops]))
      have ht : renderTo (.iff a b) rest = wrapWith 0 a (renderTo a) X := rfl
      have hkw := wrap0_head hlex hs.1 X
      rw [ht, parseStmt.eq_5 lex _ (fun _ _ h' => hkw _ _ h' (by simp))
        (fun _ _ h' => hkw _ _ h' (by simp)) (fun _ h' => hkw _ _ h' (by simp))
        (fun _ h' => hkw _ _ h' (by simp)), e1]
      simp only [X]
      rw [e2]; rfl
    exact ⟨hS, wrap_of hS (fun h => by simp [Stmt.prec] at h)⟩
  | neg a iha =>
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo (.neg a) rest)) = some (.neg a, rest) := by
      intro rest hr
      obtain ⟨h1, e1⟩ := forget_eq.mp ((iha hs).2 1 rest (by decide) hr)
      have ht : renderTo (.neg a) rest = .w "it" :: .w "is" :: .w "not" :: .w "the" ::
          .w "case" :: .w "that" :: wrapWith 1 a (renderTo a) rest := rfl
      rw [ht, parseOperand.eq_4, e1]; rfl
    have hS := stmt_of (fun rest w r h => by
      simp only [renderTo, wordsTo, List.foldr_cons, List.foldr_nil, List.cons.injEq,
        Tok.w.injEq] at h
      rw [← h.1]; decide) hB
    exact ⟨hS, wrap_of hS (fun _ => hB)⟩
  | rel t args =>
    have hhead := render_rel_head hlex hs
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo (.rel t args) rest)) = some (.rel t args, rest) := by
      intro rest _
      have hi : ∀ r, renderTo (.rel t args) rest ≠ .indent :: r := fun r h => by
        have := parseAtomic_rel hlex hs rest
        rw [h] at this
        simp [parseAtomic, Term.parse] at this
      rw [parseOperand_atomic hi (fun w r h => notMem_op (hhead rest w r h)),
        parseAtomic_rel hlex hs]
    have hS := stmt_of (fun rest w r h => notMem_kw (hhead rest w r h)) hB
    exact ⟨hS, wrap_of hS (fun _ => hB)⟩
  | atom x =>
    have hB : ∀ rest, followsOpnd rest = true →
        forget (parseOperand lex (renderTo (.atom x) rest)) = some (.atom x, rest) := by
      intro rest hr
      have ht : renderTo (.atom x) rest = .leaf x :: rest := rfl
      rw [ht, parseOperand_atomic (by simp) (by simp), parseAtomic_atom hlex x hr]
    have hS := stmt_of (fun rest w r h => by simp [renderTo] at h) hB
    exact ⟨hS, wrap_of hS (fun _ => hB)⟩

/-- A statement's tokens read back as the statement, for a well-formed lexicon whose templates it
uses with their arities. -/
public theorem parse_render_exact {lex : Lexicon} (hlex : lex.wf = true) (s : Stmt α)
    (hs : s.ok lex = true) : parse lex (render s) = some s := by
  obtain ⟨h, e⟩ := forget_eq.mp ((parseStmt_render_exact hlex s hs).1 [] rfl)
  rw [render, parse, e]

public theorem render_inj {lex : Lexicon} (hlex : lex.wf = true) {s s' : Stmt α}
    (hs : s.ok lex = true) (hs' : s'.ok lex = true) (h : render s = render s') : s = s' := by
  have := parse_render_exact hlex s hs
  rw [h, parse_render_exact hlex s' hs'] at this
  exact (Option.some.inj this).symm

/-! ## Statements from a file's facts -/

public def Table.lexicon (tb : Table) : Lexicon := ⟨tb.rels.map (·.2), tb.phrases.map (·.2)⟩

/-- The relations the core table says: equality, order, divisibility and membership, whose
collection Lean passes first from 4.12 on. -/
public def coreRels (collectionFirst : Bool) : List (String × Template) :=
  [("Eq", ⟨[.slot 1, .word "is", .word "equal", .word "to", .slot 2]⟩),
   ("Ne", ⟨[.slot 1, .word "is", .word "not", .word "equal", .word "to", .slot 2]⟩),
   ("LT.lt", ⟨[.slot 1, .word "is", .word "less", .word "than", .slot 2]⟩),
   ("LE.le", ⟨[.slot 1, .word "is", .word "at", .word "most", .slot 2]⟩),
   ("GT.gt", ⟨[.slot 1, .word "is", .word "greater", .word "than", .slot 2]⟩),
   ("GE.ge", ⟨[.slot 1, .word "is", .word "at", .word "least", .slot 2]⟩),
   ("Dvd.dvd", ⟨[.slot 1, .word "divides", .slot 2]⟩),
   ("Membership.mem", if collectionFirst
     then ⟨[.slot 2, .word "is", .word "an", .word "element", .word "of", .slot 1]⟩
     else ⟨[.slot 1, .word "is", .word "an", .word "element", .word "of", .slot 2]⟩)]

public def coreTable (collectionFirst : Bool) : Table := ⟨coreRels collectionFirst, []⟩

/-- The number sets a binder names by their nouns, singular and plural. -/
public def numberNouns : List (String × List String × List String) :=
  [("Nat", ["natural", "number"], ["natural", "numbers"]),
   ("Int", ["integer"], ["integers"]),
   ("Rat", ["rational", "number"], ["rational", "numbers"]),
   ("Real", ["real", "number"], ["real", "numbers"]),
   ("Complex", ["complex", "number"], ["complex", "numbers"])]

section
variable (lk : LeanStatement.Lookup) (tb : Table)

/-- A term as a formula. -/
public def leafOf (ctx : List String) (t : LeanFacts.Term) : Leaf :=
  LeanStatement.formulasOf lk ctx t

/-- A bound name as a formula. -/
public def nameLeaf (n : String) : Leaf := [LeanStatement.varMath n]

/-- The noun a binder of a type takes: a number set's, a proposition's or a type's, else an
element of the type. -/
public def nounOf (ctx : List String) (t : LeanFacts.Term) : Noun :=
  let number : Option (String × List String × List String) := match t with
    | .apps (.const c) [] => numberNouns.find? (·.1 == c)
    | _ => none
  match number, t with
  | some (_, one, many), _ => ⟨one, many, none⟩
  | none, .apps (.sort "0") [] => ⟨["proposition"], ["propositions"], none⟩
  | none, .apps (.sort "1") [] => ⟨["type"], ["types"], none⟩
  | none, _ => ⟨["element"], ["elements"], some (leafOf lk ctx t)⟩

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

/-- A proposition no connective or quantifier opens: its constant's relation where one applies to
its explicit arguments, else its formula. -/
public def atomOf (ctx : List String) (t : LeanFacts.Term) : Stmt Leaf :=
  match t with
  | .apps (.const c) args =>
    match tb.rels.lookup c with
    | some r =>
      let shown := LeanStatement.shownArgs lk c args
      if shown.length == r.arity then .rel r (shown.map (termOf lk tb ctx))
      else .atom (leafOf lk ctx t)
    | none => .atom (leafOf lk ctx t)
  | _ => .atom (leafOf lk ctx t)

end

/-- Whether a binder ranges over a noun, in the number its names take, none of them `x`. -/
public def Noun.joins (n : Noun) (x : Leaf) (b : Binder Leaf) : Bool :=
  b.dom == n.dom && b.noun == (if b.more.isEmpty then n.one else n.many) && b.name != x &&
    !b.more.contains x

/-- `∀ x, body`, the names of a quantifier over the same noun just inside it joining `x`. -/
public def forAll (n : Noun) (x : Leaf) : Stmt Leaf → Stmt Leaf
  | .all b rest =>
    if n.joins x b then .all ⟨n.many, x, b.name :: b.more, n.dom⟩ rest
    else .all ⟨n.one, x, [], n.dom⟩ (.all b rest)
  | s => .all ⟨n.one, x, [], n.dom⟩ s

/-- `∃ x, body`, the names of an existential over the same noun just inside it joining `x`. -/
public def thereIs (n : Noun) (x : Leaf) : Stmt Leaf → Stmt Leaf
  | .ex b rest =>
    if n.joins x b then .ex ⟨n.many, x, b.name :: b.more, n.dom⟩ rest
    else .ex ⟨n.one, x, [], n.dom⟩ (.ex b rest)
  | s => .ex ⟨n.one, x, [], n.dom⟩ s

/-- Two results joined, or the first reason either gives. -/
public def both {β γ δ : Type} (a : Except Unsaid β) (b : Except Unsaid γ) (f : β → γ → δ) :
    Except Unsaid δ :=
  match a, b with
  | .ok x, .ok y => .ok (f x y)
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-- A proposition said in words, or why it cannot be: a binder whose type is a proposition as a
hypothesis, an instance one too, and any other as a quantifier, but for the implicit binders of
the statement's top, under `top`, that the rest reads, which hide. -/
public def stmtOf (lk : LeanStatement.Lookup) (tb : Table) (top : Bool) (ctx : List String) :
    LeanFacts.Term → Except Unsaid (Stmt Leaf)
  | .pi n b prop ty body =>
    if prop then
      if body.reads 0 then .error (.named n)
      else both (stmtOf lk tb false ctx ty) (stmtOf lk tb top (n :: ctx) body) .imp
    else if top && (b == .implicit || b == .strict) && body.reads 0 then
      stmtOf lk tb top (n :: ctx) body
    else if b == .inst then both (stmtOf lk tb false ctx ty) (stmtOf lk tb top (n :: ctx) body) .imp
    else (stmtOf lk tb top (n :: ctx) body).map (forAll (nounOf lk ctx ty) (nameLeaf n))
  | .apps (.const "Exists") [_, .lam n _ dom body] =>
    (stmtOf lk tb false (n :: ctx) body).map (thereIs (nounOf lk ctx dom) (nameLeaf n))
  | .apps (.const "And") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .conj
  | .apps (.const "Or") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .disj
  | .apps (.const "Iff") [a, b] => both (stmtOf lk tb false ctx a) (stmtOf lk tb false ctx b) .iff
  | .apps (.const "Not") [a] => (stmtOf lk tb false ctx a).map .neg
  | .letE n .. => .error (.local n)
  | .lam .. => .error .function
  | t => .ok (atomOf lk tb ctx t)

/-- The templates a statement says, after `acc`. -/
public def Stmt.templates (acc : Array Template) : Stmt α → Array Template
  | .all _ s | .ex _ s | .neg s => s.templates acc
  | .imp a b | .conj a b | .disj a b | .iff a b => b.templates (a.templates acc)
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

/-- Whether a template's words hold no comma, parenthesis, brace or quote. -/
private def plainWords (t : Template) : Bool :=
  t.parts.all fun
    | .word w => !w.any fun c => c == ',' || c == '(' || c == ')' || c == '{' || c == '}' || c == '"'
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
        simp only [Stmt.ok, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, List.all_eq_true]
        refine ⟨⟨lookup_mem hr, by simpa using hl⟩, ?_⟩
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
        exact termOf_ok lk tb ctx a
      · rfl
    · rfl
  · rfl

private theorem forAll_ok (lex : Lexicon) (n : Noun) (x : Leaf) (s : Stmt Leaf) :
    (forAll n x s).ok lex = s.ok lex := by
  unfold forAll
  split
  · split <;> rfl
  · rfl

private theorem thereIs_ok (lex : Lexicon) (n : Noun) (x : Leaf) (s : Stmt Leaf) :
    (thereIs n x s).ok lex = s.ok lex := by
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
