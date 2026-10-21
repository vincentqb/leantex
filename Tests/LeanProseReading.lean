module

public import Tests.Artifact
public import Tests.LeanProse

public section

open LeanTex.Core LeanTex.Core.LeanProse Prose

/-! Invented statements read back from every artifact, by indentation, list marks or scope marks, by
two readers sharing no grammar with the renderer: one weighing every reading, one running scopes to
block ends. -/

namespace Tests.LeanProseReading

/-- What a reader sees of a sentence: words, and each formula by its text. -/
inductive Item where
  | word (s : String)
  | leaf (s : String)
  deriving BEq, Repr, Inhabited

/-- A sentence as its layout shows it: items, blocks, and numbered lists of items. -/
inductive Piece where
  | item (i : Item)
  | block (body : List Piece)
  | list (items : List (List Piece))
  deriving BEq, Repr, Inhabited

mutual
def pieceSize : Piece → Nat
  | .item _ => 1
  | .block b => 1 + seqSize b
  | .list is => 1 + itemsSize is
def seqSize : List Piece → Nat
  | [] => 0
  | p :: ps => pieceSize p + seqSize ps
def itemsSize : List (List Piece) → Nat
  | [] => 0
  | i :: is => 1 + seqSize i + itemsSize is
end

theorem seqSize_lt_of_mem {i : List Piece} : ∀ {is : List (List Piece)}, i ∈ is →
    seqSize i < itemsSize is
  | [], h => by simp at h
  | j :: js, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [itemsSize]; omega
    · have := seqSize_lt_of_mem h; simp only [itemsSize]; omega

def word (w : String) : Piece := .item (.word w)

/-- A block's pieces closed into the pieces around it, a comma or full stop ending it, which the
page sets inside the block it closes, standing after it. -/
def closeInto (outer : Array Piece) (inner : Array Piece) : Array Piece :=
  match inner.back? with
  | some (.item (.word w)) =>
    if w == "," || w == "." then (outer.push (.block inner.pop.toList)).push (word w)
    else outer.push (.block inner.toList)
  | _ => outer.push (.block inner.toList)

/-- The innermost open block closed into the one around it. -/
def closeTop : List (Array Piece) → List (Array Piece)
  | inner :: outer :: rest => closeInto outer inner :: rest
  | stack => stack

/-- Pieces without the full stop closing them. -/
def unstopped (l : List Piece) : List Piece :=
  match l.getLast? with
  | some (.item (.word ".")) => l.dropLast
  | _ => l

/-- The sentence once every block is closed, its full stop dropped. -/
def closeAll (stack : List (Array Piece)) : List Piece :=
  let closed := (List.range (stack.length - 1)).foldl (fun s _ => closeTop s) stack
  match closed with
  | [top] => unstopped top.toList
  | _ => []

/-- Lines with their depths as indentation shows them: a deeper line opens blocks, a shallower one
closes them. -/
def nest (lines : List (Nat × List Item)) : List Piece :=
  let step (stack : List (Array Piece)) (line : Nat × List Item) : List (Array Piece) :=
    let stack := (List.range (stack.length - 1 - line.1)).foldl (fun s _ => closeTop s) stack
    let stack := (List.range (line.1 - (stack.length - 1))).foldl (fun s _ => #[] :: s) stack
    match stack with
    | top :: rest => (top ++ line.2.toArray.map Piece.item) :: rest
    | [] => [line.2.toArray.map Piece.item]
  closeAll (lines.foldl step [#[]])

/-- Items with scope marks as a sentence: an opening parenthesis opens a block, a closing one closes
it. -/
def byMarks (items : List Item) : List Piece :=
  let step (stack : List (Array Piece)) (i : Item) : List (Array Piece) :=
    match i with
    | .word "(" => #[] :: stack
    | .word ")" => closeTop stack
    | _ => match stack with
      | top :: rest => top.push (.item i) :: rest
      | [] => [#[.item i]]
  closeAll (items.foldl step [#[]])

/-- Pieces whose first word, past any marks and into the blocks they open with, opens a sentence,
in lower case. -/
def lowered : List Piece → List Piece
  | .item (.word "(") :: rest => .item (.word "(") :: lowered rest
  | .item (.word w) :: rest => .item (.word w.decapitalize) :: rest
  | .block b :: rest => .block (lowered b) :: rest
  | l => l
termination_by l => seqSize l
decreasing_by all_goals (simp only [seqSize, pieceSize]; omega)

/-- The vocabulary a reader knows: the relations and phrases a page says. -/
structure Vocab where
  rels : List Template
  phrases : List Template

/-- What follows the words `ws` that `l` opens with. -/
def afterWords : List String → List Piece → Option (List Piece)
  | [], l => some l
  | w :: ws, .item (.word w') :: l => if w == w' then afterWords ws l else none
  | _ :: _, _ => none

/-- `l` around each of its top-level runs of the words `ws`. -/
def wordSplits (ws : List String) (acc : Array Piece) : List Piece →
    List (List Piece × List Piece)
  | [] => []
  | p :: rest =>
    let here := match afterWords ws (p :: rest) with
      | some r => [(acc.toList, r)]
      | none => []
    here ++ wordSplits ws (acc.push p) rest

/-- A binder group read off its formula at its first colon or relation: names before a colon and
the type after it, or a binder predicate's relation, its one name before the symbol. -/
def groupOf? (s : String) : Option (Group String) :=
  let cs := s.toList
  match cs.findIdx? (fun c => c == ':' || "∈<≤>≥≠".contains c) with
  | some i =>
    let before := (String.ofList (cs.take i)).trimAscii.toString
    if cs[i]? == some ':' then
      some ⟨(before.splitOn ",").map (·.trimAscii.toString),
        (String.ofList (cs.drop (i + 1))).trimAscii.toString, false⟩
    else some ⟨[before], s, true⟩
  | none => none

/-- Two or more groups, "and" before the last. -/
def groupList : List Piece → Option (Group String × List (Group String) × List Piece)
  | .item (.leaf x) :: .item (.word "and") :: .item (.leaf y) :: r =>
    match groupOf? x, groupOf? y with
    | some g, some h => some (g, [h], r)
    | _, _ => none
  | .item (.leaf x) :: .item (.word ",") :: r =>
    match groupOf? x, groupList r with
    | some g, some (h, hs, r') => some (g, h :: hs, r')
    | _, _ => none
  | _ => none

/-- A quantifier's groups: several, else one. -/
def readGroups (l : List Piece) : Option (Binder String × List Piece) :=
  match groupList l with
  | some (g, gs, r) => some (⟨g, gs⟩, r)
  | none => match l with
    | .item (.leaf x) :: r => (groupOf? x).map fun g => (⟨g, []⟩, r)
    | _ => none

/-- A quantifier's binder and the body after its comma or colon, or an existential's after "such
that". -/
def quantified (l : List Piece) : Option (Bool × Binder String × List Piece) :=
  match l with
  | .item (.word "for") :: .item (.word q) :: rest =>
    if q == "every" || q == "all" then
      match readGroups rest with
      | some (bd, .item (.word s) :: body) => if s == "," || s == ":" then some (true, bd, body) else none
      | _ => none
    else none
  | .item (.word "there") :: .item (.word q) :: rest =>
    if q == "is" || q == "are" then
      match readGroups rest with
      | some (bd, .item (.word "such") :: .item (.word "that") :: body) => some (false, bd, body)
      | _ => none
    else none
  | _ => none

def quantOf (all : Bool) (bd : Binder String) (s : Stmt String) : Stmt String :=
  if all then .all bd s else .ex bd s

/-- The arguments a template's slots took, in slot order. -/
def ordered {β : Type} (t : Template) (pairs : List (Nat × β)) : Option (List β) :=
  (List.range' 1 t.arity).mapM (pairs.lookup ·)

/-- A template's words and leaf slots opening `is`, with what follows. -/
def leafSlots : List Part → List Item → Option (List (Nat × String) × List Item)
  | [], is => some ([], is)
  | .word w :: ps, .word w' :: is => if w == w' then leafSlots ps is else none
  | .slot k :: ps, .leaf x :: is => (leafSlots ps is).map fun (pr, r) => ((k, x) :: pr, r)
  | _, _ => none

/-- Every term `is` opens with: a leaf, or a phrase over leaves, with what follows. -/
def termsAt (vc : Vocab) (is : List Item) : List (Term String × List Item) :=
  let leaf := match is with
    | .leaf x :: rest => [(Term.leaf x, rest)]
    | _ => []
  leaf ++ vc.phrases.filterMap fun p => (leafSlots p.parts is).bind fun (pairs, rest) =>
    (ordered p pairs).map fun args => (.phrase p args, rest)

/-- Every way a relation's parts read a prefix of `is`, each slot's term with its index, with what
follows. -/
def prefixParts (vc : Vocab) : List Part → List Item → List (List (Nat × Term String) × List Item)
  | [], is => [([], is)]
  | .word w :: ps, .word w' :: is => if w == w' then prefixParts vc ps is else []
  | .word _ :: _, _ => []
  | .slot k :: ps, is =>
    (termsAt vc is).flatMap fun (t, rest) =>
      (prefixParts vc ps rest).map fun (pairs, r) => ((k, t) :: pairs, r)

/-- Every relation or lone formula opening `is`, with what follows. -/
def atomsAt (vc : Vocab) (is : List Item) : List (Stmt String × List Item) :=
  let rels := vc.rels.flatMap fun t =>
    (prefixParts vc t.parts is).filterMap fun (pairs, r) => (ordered t pairs).map (.rel t ·, r)
  let lone := match is with
    | .leaf x :: r => [(Stmt.atom x, r)]
    | _ => []
  rels ++ lone

/-- A list's leading items. -/
def leadItems : List Piece → List Item
  | .item i :: rest => i :: leadItems rest
  | _ => []

/-- The items of a list of items alone. -/
def onlyItems (l : List Piece) : Option (List Item) :=
  l.mapM fun
    | .item i => some i
    | .block _ | .list _ => none

/-- Whether a reading may stand as an operand's pieces: an equivalence only as a block. -/
def unblocked (l : List Piece) (s : Stmt String) : Bool :=
  match l with
  | [.block _] => true
  | _ => !(s matches .iff ..)

/-- Whether a reading is a lone formula or a relation whose words a sentence's connectives never
split, which an inline "and" may join. -/
def plainAtom : Stmt String → Bool
  | .atom _ => true
  | .rel t args =>
    let joins (p : Template) := p.parts.any fun
      | .word w => ["and", "or", "if", "then", "both", "either"].contains w
      | .slot _ => false
    !joins t && args.all fun
      | .phrase p _ => !joins p
      | .leaf _ => true
  | _ => false

def chainOf : List (Stmt String) → Stmt String → Stmt String
  | [], c => c
  | h :: hs, c => .imp h (chainOf hs c)

/-- A list's items as their conjunction, the last item innermost. -/
def conjChain : Stmt String → List (Stmt String) → Stmt String
  | x, [] => x
  | x, y :: ys => .conj x (conjChain y ys)

/-- Every choice of one reading from each list, at most two. -/
def combos : List (List (Stmt String)) → List (List (Stmt String))
  | [] => [[]]
  | r :: rs => (r.flatMap fun x => (combos rs).map (x :: ·)).take 2

/-- A list's readings: its items' readings joined, two items at least. -/
def listReadings (rs : List (List (Stmt String))) : List (Stmt String) :=
  if rs.length < 2 then [] else
    (combos rs).filterMap fun
      | x :: xs => some (conjChain x xs)
      | [] => none

/-! ## A reader weighing every reading

Every reading the words allow, at most two: a block as what it holds, a list as its items'
conjunction, every connective's every split weighed, and in a scope two atoms joined by "and". -/

mutual

def readsN (vc : Vocab) (scope : Bool) (l : List Piece) : List (Stmt String) :=
  let lone : List (Stmt String) := match _hl : l with
    | [.block b] => if _h : seqSize b < seqSize l then readsN vc true b else []
    | [.list items] => listReadings (items.attach.map fun ⟨i, _⟩ =>
        if _h : seqSize i < seqSize l then readsN vc true i else [])
    | _ => []
  let iffs := (wordSplits ["if", "and", "only", "if"] #[] l).flatMap fun (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        ((readsN vc false a).filter (unblocked a)).flatMap fun x =>
          ((readsN vc false b).filter (unblocked b)).map (.iff x ·)
      else []
    else []
  let inlines := if !scope then [] else (wordSplits ["and"] #[] l).flatMap fun (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        ((readsN vc false a).filter plainAtom).flatMap fun x =>
          ((readsN vc false b).filter plainAtom).map (.conj x ·)
      else []
    else []
  let quants := match quantified l with
    | some (all, bd, body) =>
      if _h : seqSize body < seqSize l then (readsN vc true body).map (quantOf all bd) else []
    | none => []
  let opened : List (Stmt String) := match _hl : l with
    | .item (.word "if") :: rest =>
      (wordSplits [",", "then"] #[] rest).flatMap fun (hyps, concl) =>
        if _h1 : seqSize hyps < seqSize l then
          if _h2 : seqSize concl < seqSize l then
            (hypsN vc hyps).flatMap fun hs => (readsN vc true concl).map (chainOf hs ·)
          else []
        else []
    | .item (.word "both") :: rest =>
      (wordSplits ["and"] #[] rest).flatMap fun (a, b) =>
        if _h1 : seqSize a < seqSize l then
          if _h2 : seqSize b < seqSize l then
            ((readsN vc false a).filter (unblocked a)).flatMap fun x =>
              ((readsN vc false b).filter (unblocked b)).map (.conj x ·)
          else []
        else []
    | .item (.word "either") :: rest =>
      (wordSplits ["or"] #[] rest).flatMap fun (a, b) =>
        if _h1 : seqSize a < seqSize l then
          if _h2 : seqSize b < seqSize l then
            ((readsN vc false a).filter (unblocked a)).flatMap fun x =>
              ((readsN vc false b).filter (unblocked b)).map (.disj x ·)
          else []
        else []
    | .item (.word "it") :: .item (.word "is") :: .item (.word "not") :: .item (.word "the") ::
        .item (.word "case") :: .item (.word "that") :: rest =>
      if _h : seqSize rest < seqSize l then
        ((readsN vc false rest).filter (unblocked rest)).map .neg else []
    | [.item (.word "the"), .item (.word "following"), .item (.word "are"),
        .item (.word "equivalent"), .item (.word ":"), .list items] =>
      let rs := listReadings (items.attach.map fun ⟨i, _⟩ =>
        if _h : seqSize i < seqSize l then readsN vc true i else [])
      if items.length == 2 then rs.filterMap fun
        | .conj a b => some (.iff a b)
        | _ => none
      else rs.map .tfae
    | _ => []
  let atoms := match onlyItems l with
    | some is => (atomsAt vc is).filterMap fun (s, r) => if r.isEmpty then some s else none
    | none => []
  (lone ++ iffs ++ inlines ++ quants ++ opened ++ atoms).take 2
termination_by (seqSize l, 0)
decreasing_by all_goals (subst_vars; apply Prod.Lex.left; assumption)

/-- Every way a curried implication's hypotheses read, "and" between two. -/
def hypsN (vc : Vocab) (l : List Piece) : List (List (Stmt String)) :=
  let one := (readsN vc false l).map ([·])
  let more := (wordSplits ["and"] #[] l).flatMap fun (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        (readsN vc false a).flatMap fun x => (hypsN vc b).map (x :: ·)
      else []
    else []
  (one ++ more).take 2
termination_by (seqSize l, 1)
decreasing_by all_goals (subst_vars; first | (apply Prod.Lex.left; assumption) | (apply Prod.Lex.right; omega))

end

/-! ## A reader running each scope to its block's end

One reading, left to right: a block or a list one unit, a scope to its block's end, the longest
relation, an equivalence joining two clauses, and in a scope "and" joining two atoms. -/

mutual

def unitG (vc : Vocab) (l : List Piece) : Option (Stmt String × List Piece) :=
  match _hl : l with
  | .block b :: r =>
    if _h : seqSize b < seqSize l then
      match stmtG vc true b with
      | some (s, []) => some (s, r)
      | _ => none
    else none
  | .list items :: r =>
    let read := items.attach.mapM fun ⟨i, _⟩ =>
      if _h : seqSize i < seqSize l then
        match stmtG vc true i with
        | some (s, []) => some s
        | _ => none
      else none
    match read with
    | some (x :: y :: ys) => some (conjChain x (y :: ys), r)
    | _ => none
  | .item (.word "if") :: rest =>
    if _h : seqSize rest < seqSize l then
      match hypsG vc rest with
      | some (hs, concl) =>
        if _h2 : seqSize concl < seqSize l then
          match stmtG vc true concl with
          | some (c, []) => some (chainOf hs c, [])
          | _ => none
        else none
      | none => none
    else none
  | .item (.word "both") :: rest =>
    if _h : seqSize rest < seqSize l then
      match unitG vc rest with
      | some (a, .item (.word "and") :: r) =>
        if _h2 : seqSize r < seqSize l then (unitG vc r).map fun (b, r') => (.conj a b, r')
        else none
      | _ => none
    else none
  | .item (.word "either") :: rest =>
    if _h : seqSize rest < seqSize l then
      match unitG vc rest with
      | some (a, .item (.word "or") :: r) =>
        if _h2 : seqSize r < seqSize l then (unitG vc r).map fun (b, r') => (.disj a b, r')
        else none
      | _ => none
    else none
  | .item (.word "it") :: .item (.word "is") :: .item (.word "not") :: .item (.word "the") ::
      .item (.word "case") :: .item (.word "that") :: rest =>
    if _h : seqSize rest < seqSize l then (unitG vc rest).map fun (a, r) => (.neg a, r) else none
  | .item (.word "the") :: .item (.word "following") :: .item (.word "are") ::
      .item (.word "equivalent") :: .item (.word ":") :: .list items :: r =>
    let read := items.attach.mapM fun ⟨i, _⟩ =>
      if _h : seqSize i < seqSize l then
        match stmtG vc true i with
        | some (s, []) => some s
        | _ => none
      else none
    match read with
    | some [x, y] => some (.iff x y, r)
    | some (x :: y :: ys) => some (.tfae (conjChain x (y :: ys)), r)
    | _ => none
  | _ =>
    match quantified l with
    | some (all, bd, body) =>
      if _h : seqSize body < seqSize l then
        match stmtG vc true body with
        | some (s, []) => some (quantOf all bd s, [])
        | _ => none
      else none
    | none =>
      let is := leadItems l
      let found := atomsAt vc is
      match (found.map (·.2.length)).min? with
      | some least =>
        match found.filter (·.2.length == least) with
        | [(s, r)] => some (s, l.drop (is.length - r.length))
        | _ => none
      | none => none
termination_by (seqSize l, 0)
decreasing_by all_goals (subst_vars; apply Prod.Lex.left; assumption)

def stmtG (vc : Vocab) (scope : Bool) (l : List Piece) : Option (Stmt String × List Piece) :=
  match unitG vc l with
  | some (s, r) =>
    match afterWords ["if", "and", "only", "if"] r, afterWords ["and"] r with
    | some r', _ =>
      if _h : seqSize r' < seqSize l then (stmtG vc false r').map fun (t, r'') => (.iff s t, r'')
      else none
    | none, some r' =>
      if scope && plainAtom s then
        if _h : seqSize r' < seqSize l then
          match stmtG vc false r' with
          | some (t, []) => if plainAtom t then some (.conj s t, []) else none
          | _ => none
        else none
      else some (s, r)
    | none, none => some (s, r)
  | none => none
termination_by (seqSize l, 1)
decreasing_by all_goals (subst_vars; first | (apply Prod.Lex.left; assumption) | (apply Prod.Lex.right; omega))

/-- A curried implication's hypotheses, each a unit, "and" between two, and what follows its
", then". -/
def hypsG (vc : Vocab) (l : List Piece) : Option (List (Stmt String) × List Piece) :=
  match unitG vc l with
  | some (h, .item (.word ",") :: .item (.word "then") :: concl) => some ([h], concl)
  | some (h, .item (.word "and") :: r) =>
    if _h : seqSize r < seqSize l then (hypsG vc r).map fun (hs, c) => (h :: hs, c) else none
  | _ => none
termination_by (seqSize l, 1)
decreasing_by all_goals (subst_vars; first | (apply Prod.Lex.left; assumption) | (apply Prod.Lex.right; omega))

end

/-- The one reading that reads the whole sentence. -/
def readG (vc : Vocab) (l : List Piece) : Option (Stmt String) :=
  match stmtG vc true l with
  | some (s, []) => some s
  | _ => none

/-! ## Lines from each artifact -/

/-- A formula letter in mathematical italic as its plain letter. -/
def plainChar (c : Char) : Char :=
  let n := c.toNat
  if 0x1D44E ≤ n && n ≤ 0x1D467 then Char.ofNat (n - 0x1D44E + 'a'.toNat)
  else if 0x1D434 ≤ n && n ≤ 0x1D44D then Char.ofNat (n - 0x1D434 + 'A'.toNat)
  else if n == 0x210E then 'h'
  else c

def plainName (s : String) : String := String.ofList (s.toList.map plainChar)

/-- A word with its closing comma, colon or full stop apart. -/
def punct (w : String) : List Item :=
  if w.length > 1 && (w.endsWith "," || w.endsWith "." || w.endsWith ":") then
    [.word (w.dropEnd 1).toString, .word (w.takeEnd 1).toString]
  else [.word w]

/-- The symbols a relation's words may be, each with its spellings: as a glyph, and as a twin's
formula spells it. -/
def relSymbols : List (String × String) :=
  [("=", "="), ("≠", "≠"), ("\\neq", "≠"), ("<", "<"), ("≤", "≤"), ("\\leq", "≤"), (">", ">"),
   ("≥", "≥"), ("\\geq", "≥"), ("∣", "∣"), ("\\mid", "∣"), ("∈", "∈"), ("\\in", "∈")]

/-- A formula's pieces as a reader reads them: an empty group's braces aside, a piece that is a
relation's symbol a word, and one a relation's symbol ends that symbol's piece and the word after
it. -/
def relSplit (piece : String) : List Item :=
  let p := (piece.replace "{}" "").trimAscii.toString
  match relSymbols.find? (p.endsWith ·.1) with
  | some (spelled, sym) =>
    if p == spelled then [.word sym]
    else [.leaf (p.dropEnd spelled.length).toString.trimAscii.toString, .word sym]
  | none => if p.isEmpty then [] else [.leaf p]

/-- A line's items with each run of formula pieces one formula, a space between its pieces, and
each relation's symbol a formula ends on a word after it. -/
def joinLeaves (items : List Item) : List Item :=
  let joined := (items.foldl (fun (acc : Array Item) it => match acc.back?, it with
    | some (.leaf a), .leaf b => acc.pop.push (.leaf (a ++ " " ++ b))
    | _, _ => acc.push it) #[]).toList
  let split := joined.flatMap fun
    | .leaf x => (x.splitOn " ").flatMap relSplit
    | .word w => [.word w]
  (split.foldl (fun (acc : Array Item) it => match acc.back?, it with
    | some (.leaf a), .leaf b => acc.pop.push (.leaf (a ++ " " ++ b))
    | _, _ => acc.push it) #[]).toList

/-- A line's items as a reader reads them: each word's closing punctuation apart, each formula's
pieces one formula. -/
def normal (items : List Item) : List Item :=
  joinLeaves (items.flatMap fun
    | .word w => punct w
    | .leaf x => [.leaf x])

/-- A line's items past its statement's head: through the word closing its parenthesis. -/
def dropHead (items : List Item) : List Item :=
  match items.findIdx? (fun | .word w => w.endsWith ")." | .leaf _ => false) with
  | some i => items.drop (i + 1)
  | none => items

/-- Whether a word is a list item's number: `1.`, `(a)`, `ii.` or `B.`. -/
def isLabel (w : String) : Bool :=
  (w.length ≥ 2 && w.endsWith "." && ((w.dropEnd 1).all Char.isDigit ||
      (w.dropEnd 1).all (fun c => c == 'i' || c == 'v' || c == 'x') || (w.dropEnd 1).all Char.isUpper)) ||
    (w.length ≥ 3 && w.startsWith "(" && w.endsWith ")" && ((w.drop 1).dropEnd 1).all Char.isLower)

/-- A laid-out line as a reader sees it: where it starts, the numbers opening it, each with where
its item's text starts, where its items start, and its items. -/
structure PLine where
  x : Int
  labels : List (String × Int)
  contentX : Int
  items : List Item
  deriving Inhabited

/-- What a reader holds open: the statement's text or an item's, starting at `x`; a block starting
at `x`; or a list whose items' text starts at `x`. -/
inductive RKind where
  | run
  | block
  | list
  deriving BEq, Repr, Inhabited

structure RFrame where
  kind : RKind
  x : Int
  acc : Array Piece
  items : Array (List Piece)
  deriving Inhabited

/-- The innermost frame closed into the one around it: an item into its list, its full stop
dropped; a block into its text; a list into its text. -/
def closeFrame (inner outer : RFrame) : RFrame :=
  match inner.kind with
  | .run => { outer with items := outer.items.push (lowered (unstopped inner.acc.toList)) }
  | .block => { outer with acc := closeInto outer.acc inner.acc }
  | .list => { outer with acc := outer.acc.push (.list inner.items.toList) }

def closeFrames : List RFrame → List RFrame
  | inner :: outer :: rest => closeFrame inner outer :: rest
  | stack => stack

/-- Frames closed while the innermost stands right of `x`, past the tolerance `tol`. -/
def closeRightOf (x tol : Int) (stack : List RFrame) : List RFrame :=
  (List.range stack.length).foldl (fun s _ => match s with
    | f :: _ :: _ => if f.x > x + tol then closeFrames s else s
    | _ => s) stack

/-- A line's items onto the frames: continuing the innermost where they start at its text, else
opening a block, and a block for each step past the first where they start deeper still. -/
def placeItems (tol step : Int) (x : Int) (items : List Item) (stack : List RFrame) : List RFrame :=
  let stack := closeRightOf x tol stack
  match stack with
  | f :: rest =>
    if (f.x - x).natAbs ≤ tol.toNat && f.kind != RKind.list then
      { f with acc := f.acc ++ items.toArray.map Piece.item } :: rest
    else
      let steps := if step ≤ 0 then 1 else max 1 ((x - f.x + step / 2) / step).toNat
      let opened := (List.range (steps - 1)).map fun i =>
        RFrame.mk .block (f.x + step * (Int.ofNat (steps - 1 - i))) #[] #[]
      RFrame.mk .block x (items.toArray.map Piece.item) #[] :: opened ++ f :: rest
  | [] => [RFrame.mk .run x (items.toArray.map Piece.item) #[]]

/-- A list item's number onto the frames: the item before it in its list closed, or a list opened,
then the item's own run, its text starting at `textX`. -/
def openLabel (tol textX : Int) (stack : List RFrame) : List RFrame :=
  let stack := closeRightOf textX tol stack
  let stack := match stack with
    | f :: g :: rest =>
      if f.kind == RKind.run && g.kind == RKind.list && (f.x - textX).natAbs ≤ tol.toNat then
        closeFrame f g :: rest
      else stack
    | _ => stack
  let stack := match stack with
    | f :: _ => if f.kind == RKind.list && (f.x - textX).natAbs ≤ tol.toNat then stack
      else RFrame.mk .list textX #[] #[] :: stack
    | [] => [RFrame.mk .list textX #[] #[]]
  RFrame.mk .run textX #[] #[] :: stack

/-- A statement's lines as pieces, by where each starts: a line at its frame's text continues it,
one further right opens a block, each number opening a line opens a list's item, and a line further
left closes what it is left of; each item's first word, and the statement's, in lower case. -/
def framePieces (tol step : Int) (lines : List PLine) : List Piece :=
  match lines with
  | [] => []
  | first :: _ =>
    let start : List RFrame := [RFrame.mk .run first.x #[] #[]]
    let step1 (stack : List RFrame) (l : PLine) : List RFrame :=
      let stack := l.labels.foldl (fun s (_, tx) => openLabel tol tx s) stack
      if l.items.isEmpty then stack else placeItems tol step l.contentX l.items stack
    let closed := lines.foldl step1 start
    let top := (List.range closed.length).foldl (fun s _ => closeFrames s) closed
    match top with
    | [f] => unstopped (lowered f.acc.toList)
    | _ => []

/-- A line's opening numbers, and its items after them. -/
def splitLabels : List Item → List String × List Item
  | .word w :: rest =>
    if isLabel w then let r := splitLabels rest; (w :: r.1, r.2) else ([], .word w :: rest)
  | items => ([], items)

/-- A shipped line's items: each word between gaps, each run of formula glyphs one leaf. -/
def pdfItems (mathIdx : Nat) (l : Layout.LineOut) : List Item :=
  let flush (acc : Array Item × String × Bool) : Array Item :=
    if acc.2.1.isEmpty then acc.1
    else acc.1.push (if acc.2.2 then .leaf (plainName acc.2.1) else .word acc.2.1)
  let step (acc : Array Item × String × Bool) (seg : Layout.Seg) : Array Item × String × Bool :=
    match seg with
    | .run idx _ _ _ glyphs .. =>
      let text := String.ofList (glyphs.toList.map (·.2.1))
      let math := idx == mathIdx
      if acc.2.1.isEmpty || acc.2.2 == math then (acc.1, acc.2.1 ++ text, math)
      else (flush acc, text, math)
    | .gap .. | .decoratedGap .. => (flush acc, "", false)
    | .decoration .. | .rule .. | .image .. | .poly .. => acc
  (flush (l.segs.foldl step (#[], "", false))).toList

/-- Where each glyph run of a line ends, and where the run after it starts. -/
def runEdges (l : Layout.LineOut) : List (Int × Int) :=
  let r := l.segs.foldl (fun (acc : Dim.Length × Array (Int × Int) × Option Int) seg =>
    match seg with
    | .run _ _ _ w .. =>
      let out := match acc.2.2 with
        | some e => acc.2.1.push (e, acc.1.units)
        | none => acc.2.1
      (acc.1 + w, out, some (acc.1 + w).units)
    | .gap w _ | .decoratedGap w _ _ => (acc.1 + w, acc.2.1, acc.2.2)
    | .decoration .. | .rule .. | .image .. | .poly .. => acc) (l.x, #[], none)
  r.2.1.toList

/-- A shipped line as a reader sees it: each number opening it with its item's text start, where
its label's end and the list's label separation `sep` put it, and its items after them. -/
def pdfLine (mathIdx : Nat) (head : Bool) (sep : Int) (l : Layout.LineOut) : PLine :=
  let raw := pdfItems mathIdx l
  let (labels, rest) := splitLabels (if head then dropHead raw else raw)
  let edges := runEdges l
  let ends := (edges.take labels.length).map (·.1)
  let content := ((edges[labels.length - 1]?).map (·.2)).getD l.x.units
  ⟨l.x.units, labels.zip (ends.map (· + sep)), if labels.isEmpty then l.x.units else content,
    normal rest⟩

/-- The narrowest space after a list item's number on a page: its lists' label separation. -/
def labelSep (mathIdx : Nat) (lines : Array Layout.LineOut) : Int :=
  let gaps := lines.toList.filterMap fun l =>
    match (splitLabels (pdfItems mathIdx l)).1, runEdges l with
    | _ :: _, (e, n) :: _ => some (n - e)
    | _, _ => none
  gaps.foldl min (gaps.headD 0)

/-- The statements of a page: each from a line opening on a theorem's head to the next. -/
def pdfParas (mathIdx : Nat) (step : Dim.Length) (lines : Array Layout.LineOut) :
    Array (List Piece) := Id.run do
  let sep := labelSep mathIdx lines
  let mut out : Array (List Piece) := #[]
  let mut cur : Array PLine := #[]
  for l in lines do
    let head := (lineText l).startsWith "Theorem ("
    if head then
      unless cur.isEmpty do out := out.push (framePieces (step / 4).units step.units cur.toList)
      cur := #[]
    cur := cur.push (pdfLine mathIdx head sep l)
  unless cur.isEmpty do out := out.push (framePieces (step / 4).units step.units cur.toList)
  return out

/-- A text's words, white space between them. -/
def rawWords (s : String) : Array Item :=
  ((s.split fun c => c == ' ' || c == '\n').toList.filter (!·.isEmpty)).toArray.map
    fun w => .word w.toString

def classOf (attrs : Array (String × String)) : String :=
  ((attrs.find? (·.1 == "class")).map (·.2)).getD ""

mutual
/-- A web line's items: its text's words, each formula's text one leaf, and, where `marks`, each
hidden scope mark's parentheses. -/
def htmlItemsOne (marks : Bool) : Html.Node → Array Item → Array Item
  | .text s, acc => (rawWords s).foldl Array.push acc
  | .elem tag attrs kids, acc =>
    if tag == "math" then acc.push (.leaf (plainName (nodeTextList "" kids.toList)))
    else if classOf attrs == "lines-mark" then
      if marks then
        (nodeTextList "" kids.toList).toList.foldl (fun a c => a.push (.word c.toString)) acc
      else acc
    else htmlItemsList marks kids.toList acc
  | .style _, acc | .script _ _, acc => acc
def htmlItemsList (marks : Bool) : List Html.Node → Array Item → Array Item
  | [], acc => acc
  | n :: rest, acc => htmlItemsList marks rest (htmlItemsOne marks n acc)
end

mutual
/-- A laid-out paragraph's lines as the page shows them, each with its depth: a line one, a scope
one step in. -/
def htmlLinesOne (depth : Nat) : Html.Node → Array (Nat × List Item) → Array (Nat × List Item)
  | .elem tag attrs kids, acc =>
    if tag == "span" && classOf attrs == "lines-line" then
      acc.push (depth, (htmlItemsList false kids.toList #[]).toList)
    else if tag == "span" && classOf attrs == "lines-scope" then
      htmlLinesList (depth + 1) kids.toList acc
    else acc
  | .text _, acc | .style _, acc | .script _ _, acc => acc
def htmlLinesList (depth : Nat) : List Html.Node → Array (Nat × List Item) →
    Array (Nat × List Item)
  | [], acc => acc
  | n :: rest, acc => htmlLinesList depth rest (htmlLinesOne depth n acc)
end

/-- A laid-out paragraph as pieces: by its lines' depths, or, where `spoken`, by its words and
marks as assistive technology reads them, the indentation unseen. -/
def htmlLaid (spoken head : Bool) (kids : List Html.Node) : List Piece :=
  let first (items : List Item) : List Item := if head then dropHead items else items
  if spoken then byMarks (normal (first (htmlItemsList true kids #[]).toList))
  else
    let lines := (htmlLinesList 0 kids #[]).toList
    match lines with
    | (d, items) :: rest => nest ((d, normal (first items)) :: rest.map fun (d, i) => (d, normal i))
    | [] => []

/-- What a reader of a statement's web content holds: the pieces read, the text of the run being
read, and whether the statement's head still stands to be dropped. -/
abbrev WebAcc := Array Piece × Array Item × Bool

/-- A web reader's pieces, its open run read. -/
def WebAcc.pieces (st : WebAcc) : List Piece :=
  (st.1 ++ (normal st.2.1.toList).toArray.map Piece.item).toList

mutual
/-- A statement's or a list item's content, node by node. -/
def webList (spoken : Bool) : List Html.Node → WebAcc → WebAcc
  | [], st => st
  | n :: rest, st => webList spoken rest (webNode spoken n st)
/-- One node of a statement's content: a laid-out paragraph, a numbered list, or text of the run. -/
def webNode (spoken : Bool) : Html.Node → WebAcc → WebAcc
  | .elem tag attrs kids, st =>
    if tag == "p" && classOf attrs == "lines" then
      (st.pieces.toArray ++ (htmlLaid spoken st.2.2 kids.toList).toArray, #[], false)
    else if tag == "ol" then
      (st.pieces.toArray.push (.list (webItems spoken #[] kids.toList).toList), #[], false)
    else (st.1, htmlItemsOne spoken (.elem tag attrs kids) st.2.1, st.2.2)
  | other, st => (st.1, htmlItemsOne spoken other st.2.1, st.2.2)
/-- A numbered list's items as pieces after `acc`, each item's first word in lower case. -/
def webItems (spoken : Bool) (acc : Array (List Piece)) : List Html.Node → Array (List Piece)
  | [] => acc
  | n :: rest => webItems spoken (webItem spoken acc n) rest
def webItem (spoken : Bool) (acc : Array (List Piece)) : Html.Node → Array (List Piece)
  | .elem tag _ kids =>
    if tag == "li" then acc.push (lowered (unstopped (webList spoken kids.toList (#[], #[], false)).pieces))
    else acc
  | _ => acc
end

mutual
/-- Every statement of a web page, in order, as pieces. -/
def htmlParasOne (spoken : Bool) : Html.Node → Array (List Piece) → Array (List Piece)
  | .elem tag attrs kids, acc =>
    if tag == "div" && (classOf attrs).startsWith "ragged" then
      acc.push (lowered (unstopped (webList spoken kids.toList (#[], #[], true)).pieces))
    else htmlParasList spoken kids.toList acc
  | .text _, acc | .style _, acc | .script _ _, acc => acc
def htmlParasList (spoken : Bool) : List Html.Node → Array (List Piece) → Array (List Piece)
  | [], acc => acc
  | n :: rest, acc => htmlParasList spoken rest (htmlParasOne spoken n acc)
end

/-- A twin line's items: its words, each `$…$` one leaf. -/
def twinItems (s : String) : List Item := Id.run do
  let mut out : Array Item := #[]
  let mut word := ""
  let mut math := false
  for c in s.toList do
    if c == '$' then
      if math then
        out := out.push (.leaf word)
        word := ""
        math := false
      else
        unless word.isEmpty do out := out.push (.word word)
        word := ""
        math := true
    else if !math && (c == ' ' || c == '\n') then
      unless word.isEmpty do out := out.push (.word word)
      word := ""
    else word := word.push c
  unless word.isEmpty do out := out.push (if math then .leaf word else .word word)
  return out.toList

/-- A twin line's depth: its pairs of em and en spaces. -/
def twinDepth (s : String) : Nat × String :=
  let rec go (cs : List Char) (n : Nat) : Nat × List Char :=
    match cs with
    | ' ' :: ' ' :: rest => go rest (n + 1)
    | _ => (n, cs)
  let r := go s.toList 0
  (r.1, String.ofList r.2)

/-- A twin line's numbers opening it, each with the column its item's text starts at, and the rest
of the line. -/
def twinLabels (col : Nat) (cs : List Char) : List (String × Int) × Nat × List Char :=
  let w := cs.takeWhile (· != ' ')
  if h : isLabel (String.ofList w) && w.length < cs.length then
    let r := twinLabels (col + w.length + 1) (cs.drop (w.length + 1))
    ((String.ofList w, Int.ofNat (col + w.length + 1)) :: r.1, r.2)
  else ([], col, cs)
termination_by cs.length
decreasing_by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.length_drop]
  omega

/-- A twin line as a reader sees it: its indent in spaces, the numbers after it, and each step of
em and en spaces a hundred columns past where its text starts. -/
def twinLine (head : Bool) (line : String) : PLine :=
  let spaces := (line.toList.takeWhile (· == ' ')).length
  let (labels, col, after) := twinLabels spaces (line.toList.drop spaces)
  let (d, rest) := twinDepth (String.ofList after)
  let raw := twinItems rest
  let items := normal (if head then dropHead raw else raw)
  ⟨Int.ofNat spaces, labels, Int.ofNat col + 100 * d, items⟩

/-- The statements of a twin: each from its theorem's paragraph through the list after it, lines
split at hard breaks. -/
def twinParas (md : String) : Array (List Piece) := Id.run do
  let blocks := md.splitOn "\n\n"
  let mut out : Array (List Piece) := #[]
  let mut cur : Array PLine := #[]
  let mut open_ := false
  for b in blocks do
    if b.startsWith "**Theorem** (" then
      if open_ then out := out.push (framePieces 0 100 cur.toList)
      cur := #[]
      open_ := true
      let lines := b.splitOn "\\\n"
      for (line, i) in lines.zipIdx do
        cur := cur.push (twinLine (i == 0) line)
    else if open_ && (b.trimAsciiStart.toString.take 1).all Char.isDigit && !b.isEmpty then
      for line in (b.splitOn "\n") do
        let part := if line.endsWith "\\" then (line.dropEnd 1).toString else line
        cur := cur.push (twinLine false part)
    else if open_ then
      out := out.push (framePieces 0 100 cur.toList)
      cur := #[]
      open_ := false
  if open_ then out := out.push (framePieces 0 100 cur.toList)
  return out

/-- The scope marks a line's replacement text sets around its words: the parentheses opening it,
those closing it, and the words between. -/
def marksOf (text : String) : Nat × Nat × String :=
  let opens := (text.toList.takeWhile (· == '(')).length
  let rest := text.toList.drop opens
  let closes := (rest.reverse.takeWhile (· == ')')).length
  (opens, closes, String.ofList (rest.take (rest.length - closes)))

/-- The tagged file's laid-out paragraphs: each `P` holding only its lines' `Span`s, each line's
replacement text where it has one. -/
def taggedParas (es : Array ReadElem) : Array (List (Option String)) :=
  let byNum (n : Nat) : Option ReadElem := es.find? (·.num == n)
  es.filterMap fun e =>
    if e.s != "P" || e.kids.isEmpty || !e.mcids.isEmpty then none else
    let kids := e.kids.toList.filterMap byNum
    if kids.length == e.kids.size && kids.all (·.s == "Span") then some (kids.map (·.actualText))
    else none

/-- The tagged file's lists, each as its items' count. -/
def taggedLists (es : Array ReadElem) : Array Nat :=
  let byNum (n : Nat) : Option ReadElem := es.find? (·.num == n)
  es.filterMap fun e =>
    if e.s != "L" then none else
    some (e.kids.toList.filterMap byNum |>.filter (·.s == "LI")).length

/-- A page's lines as a laid-out paragraph's: a line wrapping stays at its depth, and two lines of
one paragraph never share one. -/
def depthRuns (lines : List (Nat × List Item)) : List (Nat × List Item) :=
  (lines.foldl (fun (acc : Array (Nat × List Item)) (d, items) => match acc.back? with
    | some (d', prev) => if d == d' then acc.pop.push (d, prev ++ items) else acc.push (d, items)
    | none => acc.push (d, items)) #[]).toList

/-- A tagged paragraph as assistive technology reads it: each line's words as the page sets them,
between the parentheses its replacement text adds; none where a replacement's words are not the
line's. -/
def spokenPara (texts : List (Option String)) (lines : List (Nat × List Item)) :
    Option (List Piece) :=
  let runs := depthRuns lines
  if runs.length != texts.length then none else
  let squash (s : String) : String := String.ofList (s.toList.filter (!·.isWhitespace))
  let itemText (items : List Item) : String := squash (String.join (items.map fun
    | .word w => w
    | .leaf x => x))
  ((texts.zip runs).foldlM (m := Option) (fun (acc : List Item) (tr : Option String × Nat × List Item) =>
    let (t, (_, items)) := tr
    match t with
    | none => some (acc ++ items)
    | some text =>
      let (o, c, core) := marksOf text
      if plainName (squash core) != itemText items then none
      else some (acc ++ List.replicate o (Item.word "(") ++ items ++ List.replicate c (Item.word ")")))
    []).map fun items => lowered (byMarks items)

/-- A list-free page's laid-out paragraphs, each line with its depth and items as the reader
normalizes them. -/
def pdfLaid (mathIdx : Nat) (step : Dim.Length) (lines : Array Layout.LineOut) :
    Array (List (Nat × List Item)) := Id.run do
  let mut out : Array (List (Nat × List Item)) := #[]
  let mut cur : Array (Nat × List Item) := #[]
  let mut x0 : Dim.Length := 0
  for l in lines do
    let head := (lineText l).startsWith "Theorem ("
    if head then
      unless cur.isEmpty do out := out.push cur.toList
      cur := #[]
      x0 := l.x
    let raw := pdfItems mathIdx l
    let depth := ((l.x - x0 + step / 2) / step).toNat
    cur := cur.push (depth, normal (if head then dropHead raw else raw))
  unless cur.isEmpty do out := out.push cur.toList
  return out

/-! ## Invented statements -/

def L (s : String) : Leaf := wordLeaf s

/-- The table invented statements are said through: the core table's relations and four declared
phrases, two holding a connective's word. -/
def tb (_ : Unit) : Table :=
  (tableFor (factsWith #[("Tide.height", #[.explicit, .explicit]),
      ("Tide.Calm", #[.explicit]), ("Tide.Between", #[.explicit, .explicit, .explicit]),
      ("Tide.gap", #[.explicit, .explicit])])
    [("Tide.height", "the height after #2 steps of #1"), ("Calm", "#1 is calm"),
     ("Between", "#1 lies between #2 and #3"), ("gap", "the gap between #1 and #2")]).table

def relT (c : String) : Template := ((tb ()).rels.lookup c).getD ⟨[]⟩

/-- A formula, as a relation between formulas sets. -/
def P (s : String) : Stmt Leaf := .atom (L s)

def lt (a b : String) : Stmt Leaf := P s!"{a}<{b}"
def le (a b : String) : Stmt Leaf := P s!"{a}≤{b}"
def eq (a b : String) : Stmt Leaf := P s!"{a}={b}"
def dvd (a b : String) : Stmt Leaf := P s!"{a}|{b}"
def calm (a : String) : Stmt Leaf := .rel (relT "Tide.Calm") [.leaf (L a)]

def heightOf (a b : String) : Term Leaf :=
  .phrase (((tb ()).phrases.lookup "Tide.height").getD ⟨[]⟩) [L a, L b]

def gapOf (a b : String) : Term Leaf :=
  .phrase (((tb ()).phrases.lookup "Tide.gap").getD ⟨[]⟩) [L a, L b]

def between (a b c : String) : Stmt Leaf :=
  .rel (relT "Tide.Between") [.leaf (L a), .leaf (L b), .leaf (L c)]

/-- Names bound by one type. -/
def grp (names : List String) (t : String) : Group Leaf := ⟨names.map L, L t, false⟩

def nat (x : String) : Binder Leaf := ⟨grp [x] "N", []⟩
def nats (x : String) (ys : List String) : Binder Leaf := ⟨grp (x :: ys) "N", []⟩
def elt (x T : String) : Binder Leaf := ⟨grp [x] T, []⟩
def prop (p : String) : Binder Leaf := ⟨grp [p] "Prop", []⟩
def props (p : String) (qs : List String) : Binder Leaf := ⟨grp (p :: qs) "Prop", []⟩
def ty (a : String) : Binder Leaf := ⟨grp [a] "Type", []⟩
/-- A binder predicate's group, `x ∈ S`. -/
def mem (x S : String) : Binder Leaf := ⟨⟨[L x], L s!"{x}∈{S}", true⟩, []⟩
/-- A binder predicate's group bounding its name, `x < n`. -/
def below (x n : String) : Binder Leaf := ⟨⟨[L x], L s!"{x}<{n}", true⟩, []⟩
/-- A quantifier over several groups. -/
def groups (gs : List (List String × String)) : Binder Leaf :=
  match gs.map fun (ns, t) => grp ns t with
  | g :: more => ⟨g, more⟩
  | [] => ⟨grp ["x"] "N", []⟩

/-- Invented statements, each named by what its scopes and lists do. -/
def corpus : List (String × Stmt Leaf) :=
  [("a quantifier inside a quantifier", .all (nat "x") (.ex (nat "y") (lt "x" "y"))),
   ("an existential over a universal", .ex (nat "x") (.all (nat "y") (le "y" "x"))),
   ("quantifiers over two types", .all (ty "A") (.all (elt "a" "A") (eq "a" "a"))),
   ("one quantifier over three groups",
     .all (groups [(["A"], "Type"), (["a", "b"], "A"), (["n"], "N")]) (eq "a" "b")),
   ("a plural quantifier over an inline conjunction",
     .all (nats "x" ["y"]) (.ex (nat "z") (.conj (le "x" "z") (le "y" "z")))),
   ("three quantifiers deep", .all (ty "A") (.all (elt "a" "A") (.ex (elt "b" "A") (eq "a" "b")))),
   ("a binder predicate", .all (mem "x" "S") (.ex (mem "y" "S") (lt "x" "y"))),
   ("an order binder predicate", .all (nat "n") (.all (below "k" "n") (.ex (below "j" "k") (le "j" "k")))),
   ("a group whose type holds a colon and a comma",
     .all (groups [(["f"], "(n:N,F(n))"), (["g"], "(N→N)")]) (eq "f" "g")),
   ("an existential whose body is a conditional",
     .ex (nat "x") (.all (nat "y") (.imp (lt "y" "x") (.ex (nat "z") (lt "y" "z"))))),
   ("a curried implication", .imp (le "x" "y") (.imp (le "y" "z") (le "x" "z"))),
   ("three curried hypotheses", .imp (P "P") (.imp (P "Q") (.imp (P "R") (P "S")))),
   ("an implication as a hypothesis", .imp (.imp (P "P") (P "Q")) (P "R")),
   ("a quantifier as a hypothesis", .imp (.all (nat "x") (le "x" "y")) (P "Q")),
   ("an existential as a hypothesis", .imp (.ex (nat "x") (lt "y" "x")) (P "Q")),
   ("implications nested in hypotheses", .imp (.imp (.imp (P "P") (P "Q")) (P "R")) (P "S")),
   ("a quantifier among curried hypotheses",
     .imp (P "P") (.imp (.all (nat "x") (lt "x" "y")) (P "Q"))),
   ("a quantifier opening curried hypotheses",
     .imp (.all (nat "x") (lt "x" "y")) (.imp (P "P") (P "Q"))),
   ("a conjunction as the one hypothesis", .imp (.conj (P "P") (P "Q")) (P "R")),
   ("a conjunction among curried hypotheses", .imp (P "P") (.imp (.conj (P "Q") (P "R")) (P "S"))),
   ("a conjunction as the last curried hypothesis",
     .imp (P "P") (.imp (P "Q") (.imp (.conj (P "R") (P "S")) (P "T")))),
   ("a conjunction closing on a quantifier as a hypothesis",
     .imp (.conj (P "P") (.all (nat "x") (le "x" "x"))) (P "Q")),
   ("a list inside a hypothesis's quantifier stands as both and",
     .imp (.all (nat "x") (.conj (.all (nat "y") (lt "x" "y")) (P "Q"))) (P "R")),
   ("a negated quantifier as a hypothesis", .imp (.neg (.all (nat "x") (le "x" "y"))) (P "Q")),
   ("a disjunction as a conclusion", .imp (P "P") (.disj (P "Q") (P "R"))),
   ("an equivalence whose left side a quantifier opens lists its two sides",
     .iff (.all (nat "x") (le "x" "x")) (P "Q")),
   ("three equivalent statements, listed",
     .tfae (.conj (lt "x" "y") (.conj (.all (nat "z") (le "z" "z")) (P "Q")))),
   ("a quantifier over three equivalent statements",
     .all (nat "n") (.tfae (.conj (eq "n" "n") (.conj (P "P") (.ex (nat "m") (lt "n" "m")))))),
   ("an equivalence whose left side is a conjunction sets it bare",
     .iff (.conj (P "P") (P "Q")) (P "R")),
   ("an equivalence whose left side is a negation lists its sides",
     .iff (.neg (P "P")) (P "Q")),
   ("an equivalence whose left side is a disjunction lists its sides",
     .iff (.disj (P "P") (P "Q")) (P "R")),
   ("a negated equivalence keeps its block", .neg (.iff (P "P") (P "Q"))),
   ("a list item holding an equivalence of a conjunction opens on its words",
     .conj (.iff (.conj (P "P") (P "Q")) (P "R")) (.all (nat "x") (le "x" "x"))),
   ("a list item holding an equivalence a quantifier opens lists its sides",
     .conj (.iff (.all (nat "x") (le "x" "y")) (P "Q")) (.ex (nat "z") (eq "z" "z"))),
   ("a scope holding an equivalence an existential opens lists its sides",
     .all (nat "y") (.iff (.ex (nat "x") (lt "x" "y")) (P "Q"))),
   ("a conjunction of quantified statements, a list",
     .conj (.all (nat "x") (le "x" "x")) (.ex (nat "y") (eq "y" "y"))),
   ("a quantifier over a list holding a quantifier",
     .all (nat "x") (.conj (le "x" "y") (.all (nat "z") (lt "z" "x")))),
   ("a list opening on an existential", .conj (.ex (nat "x") (eq "x" "y")) (P "R")),
   ("a list closing on a quantifier", .conj (P "P") (.all (nat "x") (le "x" "x"))),
   ("three clauses, the second of two",
     .all (nat "c") (.conj (le "c" "d") (.conj (.all (nat "k")
       (.conj (.all (nat "m") (lt "m" "k")) (.ex (nat "n") (lt "k" "n")))) (eq "c" "c")))),
   ("a list whose first item is a conjunction",
     .conj (.conj (P "P") (P "Q")) (.all (nat "x") (le "x" "x"))),
   ("a list as a conclusion", .imp (P "P") (.conj (.all (nat "x") (le "x" "x")) (P "Q"))),
   ("a list under an existential", .ex (nat "x") (.conj (.all (nat "y") (le "y" "x")) (P "Q"))),
   ("a disjunction of quantified statements",
     .disj (.all (nat "x") (le "x" "x")) (.all (nat "y") (lt "y" "y"))),
   ("a list holding a conditional first", .conj (.imp (P "P") (P "Q")) (P "R")),
   ("a negated quantifier", .neg (.all (nat "x") (lt "x" "y"))),
   ("a negated conjunction holding a negation", .neg (.conj (P "P") (.neg (P "Q")))),
   ("a double negation", .neg (.neg (P "P"))),
   ("a negated existential under a quantifier", .all (nat "x") (.neg (.ex (nat "y") (lt "y" "x")))),
   ("a negated implication", .neg (.imp (P "P") (P "Q"))),
   ("a list opening on a negation", .conj (.neg (P "P")) (P "Q")),
   ("an equivalence of conjunctions", .iff (.conj (P "P") (P "Q")) (.conj (P "Q") (P "P"))),
   ("a quantified equivalence of conjunctions",
     .all (props "p" ["q"]) (.iff (.conj (P "p") (P "q")) (.conj (P "q") (P "p")))),
   ("an equivalence holding one", .all (prop "p") (.iff (P "p") (.iff (P "p") (P "q")))),
   ("an equivalence as a conclusion", .imp (P "P") (.iff (P "Q") (P "R"))),
   ("an equivalence opening on a quantifier", .iff (.all (nat "x") (le "x" "x")) (P "Q")),
   ("an equivalence under an existential", .ex (nat "x") (.iff (eq "x" "y") (P "R"))),
   ("a negated equivalence", .neg (.iff (P "P") (P "Q"))),
   ("an equivalence of equivalences", .iff (.iff (P "P") (P "Q")) (P "R")),
   ("an equivalence closing a list", .conj (P "P") (.iff (P "Q") (P "R"))),
   ("an equivalence as a hypothesis", .imp (.iff (P "P") (P "Q")) (P "R")),
   ("a phrase in a quantified equation",
     .all (nats "a" ["n"]) (.rel (relT "Eq") [heightOf "a" "n", heightOf "n" "a"])),
   ("a declared relation in a conditional", .all (nat "x") (.imp (calm "x") (.ex (nat "y") (calm "y")))),
   ("an epsilon and delta",
     .all (nat "e") (.imp (lt "o" "e") (.ex (nat "d")
       (.conj (lt "o" "d") (.all (nat "x") (.imp (lt "x" "d") (lt "x" "e"))))))),
   ("two conditional hypotheses",
     .imp (.all (nat "x") (.ex (nat "y") (lt "x" "y"))) (.imp (.ex (nat "z") (eq "z" "z")) (P "R"))),
   ("divisibility under two quantifiers",
     .all (nats "a" ["b", "c"]) (.imp (dvd "a" "b") (.imp (dvd "b" "c") (dvd "a" "c")))),
   ("a relation holding 'and' opening a list", .conj (between "a" "b" "c") (P "Q")),
   ("a relation holding 'and' closing a list", .conj (P "Q") (between "a" "b" "c")),
   ("a relation holding 'and' as a curried hypothesis",
     .imp (between "x" "a" "b") (.imp (P "Q") (P "R"))),
   ("a relation holding 'and' as the last curried hypothesis",
     .imp (P "Q") (.imp (between "x" "a" "b") (P "R"))),
   ("a relation holding 'and' as the one hypothesis", .imp (between "x" "a" "b") (P "R")),
   ("a relation holding 'and' under a quantifier", .all (nat "x") (between "x" "a" "b")),
   ("a relation holding 'and' in an equivalence", .iff (between "x" "a" "b") (P "Q")),
   ("a relation holding 'and' negated", .neg (between "x" "a" "b")),
   ("a term holding 'and' in a disjunction",
     .disj (.rel (relT "LT.lt") [gapOf "a" "b", .leaf (L "c")]) (P "Q")),
   ("a term holding 'and' in a conjunction's hypothesis",
     .imp (.conj (P "P") (.rel (relT "Eq") [gapOf "a" "b", gapOf "b" "a"])) (P "R"))]

/-- `n` random statements of depth at most four over the invented table. -/
def randoms (n : Nat) : List (Stmt Leaf) :=
  ((List.range n).foldl (fun (acc : Array (Stmt Leaf) × UInt64) _ =>
    let (st, s) := randStmt (tb ()) 4 acc.2
    (acc.1.push st, s)) (#[], 0x2545F4914F6CDD1D)).1.toList

def termMap {α β : Type} (f : α → β) : Term α → Term β
  | .leaf a => .leaf (f a)
  | .phrase t args => .phrase t (args.map f)

def groupMap {α β : Type} (f : α → β) (g : Group α) : Group β :=
  ⟨g.names.map f, f g.bound, g.pred⟩

def binderMap {α β : Type} (f : α → β) (b : Binder α) : Binder β :=
  ⟨groupMap f b.first, b.more.map (groupMap f)⟩

/-- A statement with each leaf as `f` names it. -/
def stmtMap {α β : Type} (f : α → β) : Stmt α → Stmt β
  | .all b s => .all (binderMap f b) (stmtMap f s)
  | .ex b s => .ex (binderMap f b) (stmtMap f s)
  | .imp a b => .imp (stmtMap f a) (stmtMap f b)
  | .conj a b => .conj (stmtMap f a) (stmtMap f b)
  | .disj a b => .disj (stmtMap f a) (stmtMap f b)
  | .iff a b => .iff (stmtMap f a) (stmtMap f b)
  | .tfae s => .tfae (stmtMap f s)
  | .neg a => .neg (stmtMap f a)
  | .rel t args => .rel t (args.map (termMap f))
  | .atom x => .atom (f x)

/-- Whether a statement's sentence sets a list. -/
def hasList (s : Stmt Leaf) : Bool := (render s).contains .item

/-- A page setting each statement in words, the `i`-th as theorem `s<i>`. -/
def pageOf (stmts : List (Stmt Leaf)) : Ir.Doc × Array Diag :=
  let paras := stmts.toArray.mapIdx fun i st =>
    Code.wordsRaws (theoremAt s!"s{i}" (i + 1) (selfEq 0)) st {}
  let raws : Array Parse.Raw := #[.ctrl "title" {}, .group #[.word "Readings" {}] {},
    .env "document" (paras.foldl (· ++ ·) #[]) {}]
  Elab.runRaws "readings.lean" raws

/-- Whether both readers take a sentence for exactly the statement. -/
def readsBack (vc : Vocab) (want : Stmt String) (l : List Piece) : Bool :=
  readsN vc true l == [want] && readG vc l == some want

/-- Each statement's reading off an artifact's paragraphs, by position: the failures, labelled. -/
def failuresOf (vc : Vocab) (labels : List String) (want : List (Stmt String))
    (paras : Array (List Piece)) : List String :=
  (labels.zip want).zipIdx.filterMap fun ((label, w), i) =>
    match paras[i]? with
    | none => some s!"{label}: no paragraph"
    | some l =>
      if readsBack vc w l then none
      else some s!"{label}: {(readsN vc true l).length} readings, {repr (readG vc l)}, {(toString (repr l)).take 1500}"

/-! ## Each block set at its scope's margin -/

/-- Every block of a sentence, each as the sentence with that block's lines set at the margin of the
lines around it; a list's items each in turn. -/
def flattenings : List Piece → List (List Piece)
  | [] => []
  | .item i :: rest => (flattenings rest).map (.item i :: ·)
  | .block b :: rest =>
    (b ++ rest) :: (flattenings b).map (fun b' => .block b' :: rest) ++
      (flattenings rest).map (.block b :: ·)
  | .list items :: rest =>
    (items.attach.zipIdx.flatMap fun (⟨i, _⟩, k) =>
      (flattenings i).map fun i' => .list (items.set k i') :: rest) ++
      (flattenings rest).map (.list items :: ·)
termination_by l => seqSize l
decreasing_by
  all_goals simp only [seqSize, pieceSize]
  all_goals first
    | omega
    | (have := seqSize_lt_of_mem ‹_›; omega)

/-- What a block bounds, as a reader sees it: an equivalence it holds, or whose left side it is
and could otherwise run on past; a scope its first words open; or neither. -/
inductive Bound where
  | equivalence
  | scope
  | neither
  deriving BEq, Repr, Inhabited

def iffWords : List String := ["if", "and", "only", "if"]

/-- Every block of a sentence with what it bounds, in the order `flattenings` takes them; `prev`
holds what stands before, nearest first. -/
def bounds (vc : Vocab) (prev : List Piece) : List Piece → List Bound
  | [] => []
  | .item i :: rest => bounds vc (.item i :: prev) rest
  | .block b :: rest =>
    let after := prev.take 4 == iffWords.reverse.map word
    let before := (afterWords iffWords rest).isSome
    let holds := !(wordSplits iffWords #[] b).isEmpty
    let atomic := match onlyItems b with
      | some is => (atomsAt vc is).any (·.2.isEmpty)
      | none => false
    let opens := match b with
      | .item (.word w) :: _ => w == "for" || w == "there" || w == "if"
      | _ => false
    let kind := if holds then Bound.equivalence else if after then .neither
      else if before && !atomic then .equivalence else if opens then .scope else .neither
    kind :: bounds vc [] b ++ bounds vc (.block b :: prev) rest
  | .list items :: rest =>
    items.attach.flatMap (fun ⟨i, _⟩ => bounds vc [] i) ++ bounds vc (.list items :: prev) rest
termination_by l => seqSize l
decreasing_by
  all_goals simp only [seqSize, pieceSize]
  all_goals first
    | omega
    | (have := seqSize_lt_of_mem ‹_›; omega)

/-- Each list a sentence sets, nested ones too, by its items' count, after `acc`. -/
def listsOf (acc : Array Nat) : List Piece → Array Nat
  | [] => acc
  | .item _ :: rest => listsOf acc rest
  | .block b :: rest => listsOf (listsOf acc b) rest
  | .list items :: rest =>
    listsOf (items.attach.foldl (fun a ⟨i, _⟩ => listsOf a i) (acc.push items.length)) rest
termination_by l => seqSize l
decreasing_by
  all_goals simp only [seqSize, pieceSize]
  all_goals first
    | omega
    | (have := seqSize_lt_of_mem ‹_›; omega)

def readingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let vc : Vocab := ⟨(tb ()).rels.map (·.2), (tb ()).phrases.map (·.2)⟩
  let rnd := randoms 300
  let stmts := corpus.map (·.2) ++ rnd
  let labels := corpus.map (·.1) ++ (List.range rnd.length).map (s!"random {·}")
  let want := stmts.map (stmtMap leafWord)
  let (doc, _) := pageOf stmts
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "reading: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "reading: the mono face loads" false
  let fonts ← mathSetOf (slotPairOf 2 text mono)
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fonts doc
  let step := Ir.linesStep.resolve geom.fontSize 0
  let mathIdx := fonts.math.getD 0
  let page := pdfParas mathIdx step (bodyLines out)
  let nodes := (docNodesOf doc).toList
  let web := htmlParasList false nodes #[]
  let webSpoken := htmlParasList true nodes #[]
  let sheet := (HtmlDoc.emit {} doc).1
  t "reading: the web page's stylesheet sets each line a block, each scope a step in and each mark out of sight"
    (hasStr sheet ".lines-line, .lines-scope { display: block; }" &&
      hasStr sheet s!".lines-scope \{ padding-inline-start: {HtmlDoc.cssLength Ir.linesStep}; }" &&
      hasStr sheet s!".lines-mark \{ {HtmlDoc.visuallyHidden} }")
  let twin := twinParas (MarkdownDoc.emit doc)
  t s!"reading: some invented statements set lists and some none ({(stmts.filter hasList).length} of {stmts.length})"
    ((stmts.filter hasList).length > 10 && (stmts.filter (!hasList ·)).length > 10)
  for (what, paras) in [("the page", page), ("the web page", web), ("the twin", twin),
      ("the web page as assistive technology reads it", webSpoken)] do
    let failed := failuresOf vc labels want paras
    t s!"reading: every invented statement reads back from {what}, by both readers ({failed.take 3})"
      (paras.size == stmts.length && failed.isEmpty)
  -- The tagged file: each list a list of its items, and each list-free statement as spoken.
  let pdfOf (d : Ir.Doc) (o : Layout.Out) : Array ReadElem :=
    let pdf := driverPdf fonts (Layout.Geom.ofPage d.page) d o
    match PdfRead.objects pdf, PdfRead.trailer pdf with
    | .ok es, .ok trailer =>
      let es := es.val
      match (PdfCensus.catalogOf es trailer).get? "StructTreeRoot" with
      | some (.ref r _) => match es.find? (·.num == r) with
        | some root => readStructTree es root.val
        | none => #[]
      | _ => #[]
    | _, _ => #[]
  let wantLists := (page.foldl listsOf #[]).size
  let taggedL := taggedLists (pdfOf doc out)
  t s!"reading: the tagged file holds each list the page sets as an L of its items ({taggedL.size} of {wantLists})"
    (taggedL.size ≥ wantLists && wantLists > 0 && taggedL.all (· ≥ 2))
  let flat := stmts.filter (!hasList ·)
  let flatWant := flat.map (stmtMap leafWord)
  let flatLabels := (labels.zip stmts).filterMap fun (l, s) => if hasList s then none else some l
  let (flatDoc, _) := pageOf flat
  let flatOut := layoutOf fonts flatDoc
  let flatLines := pdfLaid mathIdx step (bodyLines flatOut)
  let tagged := taggedParas (pdfOf flatDoc flatOut)
  t s!"reading: the tagged file holds each laid-out paragraph as one P of its lines' Spans ({tagged.size} of {flat.length})"
    (tagged.size == flat.length)
  let spokenPdf := (tagged.zip flatLines).filterMap fun (texts, lines) => spokenPara texts lines
  t s!"reading: each line's replacement text in the tagged file says the line's words between its marks ({spokenPdf.size} of {tagged.size})"
    (spokenPdf.size == tagged.size)
  let failed := failuresOf vc flatLabels flatWant spokenPdf
  t s!"reading: every list-free invented statement reads back from the tagged file as assistive technology reads it, by both readers ({failed.take 3})"
    (spokenPdf.size == flat.length && failed.isEmpty)
  -- Planted: each block of an invented statement set at the margin of the lines around it.
  let census := (corpus.zip page.toList).foldl (fun (acc : Array (String × Bound × Bool))
      ((label, st), l) =>
    let w := stmtMap leafWord st
    ((flattenings l).zip (bounds vc [] l)).foldl (fun acc (flat, b) =>
      acc.push (label, b, readsBack vc w flat)) acc) #[]
  let kept (b : Bound) := census.filter fun (_, k, r) => k == b && r
  let named (rows : Array (String × Bound × Bool)) := (rows.map (·.1)).toList.eraseDups
  let count (b : Bound) := (census.filter (·.2.1 == b)).size
  t s!"reading: set at its margin, a block bounding an equivalence leaves a reader reading its sentence otherwise ({count .equivalence} blocks; {named (kept .equivalence)})"
    (0 < count .equivalence && (kept .equivalence).isEmpty)
  t s!"reading: set at its margin, a block a scope opens leaves a reader reading its sentence otherwise ({count .scope} blocks; {named (kept .scope)})"
    (0 < count .scope && (kept .scope).isEmpty)
  t s!"reading: a block bounding neither is for the eye, both readers reading its sentence without it ({count .neither} blocks; {named (census.filter fun (_, k, r) => k == .neither && !r)})"
    (0 < count .neither && census.all fun (_, k, r) => k != .neither || r)
  -- Three clauses, the second of two, at a wide and a narrow measure: each item's number hangs
  -- left of its text, each line an item wraps onto starts where that text does, a clause of two a
  -- list one level in, and no line ends on an opening parenthesis or a connective.
  let some three := (corpus.find? (·.1 == "three clauses, the second of two")).map (·.2)
    | t "reading: the three-clause statement stands in the corpus" false
  let (threeDoc, _) := pageOf [three]
  for (what, margin) in [("wide", threeDoc.page.hmargin),
      ("narrow", threeDoc.page.hmargin + threeDoc.page.width / 5)] do
    let d := { threeDoc with page := { threeDoc.page with hmargin := margin } }
    let ls := bodyLines (layoutOf fonts d)
    let sep := labelSep mathIdx ls
    let pl := ls.toList.map (pdfLine mathIdx false sep)
    let labels := pl.flatMap (·.labels.map (·.1))
    let texts := pl.flatMap (·.labels.map (·.2))
    let tol := (step / 4).units.toNat
    let near (a b : Int) : Bool := (a - b).natAbs ≤ tol
    let after := (pl.dropWhile (·.labels.isEmpty))
    let wrapped := after.filter (·.labels.isEmpty)
    t s!"reading: {what}, the three clauses number 1 to 3 and the second's two (a) and (b), each number left of its item's text ({labels})"
      (labels == ["1.", "2.", "(a)", "(b)", "3."] &&
        pl.all fun l => l.labels.all fun (_, tx) => l.x < tx)
    t s!"reading: {what}, each line an item wraps onto starts where an item's text does, never at the margin ({wrapped.length} lines)"
      ((what == "wide" || !wrapped.isEmpty) && wrapped.all fun l => texts.any (near l.contentX ·))
    let inks := ls.toList.map fun l => (lineText l).trimAscii.toString
    t s!"reading: {what}, no line ends on an opening parenthesis or a connective ({inks})"
      (inks.all fun s => !s.endsWith "(" && !s.endsWith " and" && !s.endsWith " both" &&
        !s.endsWith " or" && !s.startsWith "and " && s != "and")
    let web := htmlParasList false (docNodesOf d).toList #[]
    t s!"reading: {what}, the web page sets the three clauses as one list, the second holding a list of two"
      (web.size == 1 && (web.toList.headD []).any fun
        | .list [_, i2, _] => i2.any fun
          | .list [_, _] => true
          | _ => false
        | _ => false)

end Tests.LeanProseReading
