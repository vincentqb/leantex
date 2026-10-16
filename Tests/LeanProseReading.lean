module

public import Tests.LeanProse

public section

open LeanTex.Core LeanTex.Core.LeanProse

/-! Invented statements read back from the page, the web page and the markdown twin by a reader
sharing no grammar with the renderer, which takes a scope's extent from indentation alone. -/

namespace Tests.LeanProseReading

/-- What a reader sees of a sentence: words, and each formula by its text. -/
inductive Item where
  | word (s : String)
  | leaf (s : String)
  deriving BEq, Repr, Inhabited

/-- A sentence as indentation shows it: items, and blocks a step in. -/
inductive Piece where
  | item (i : Item)
  | block (body : List Piece)
  deriving BEq, Repr, Inhabited

mutual
def pieceSize : Piece → Nat
  | .item _ => 1
  | .block b => 1 + seqSize b
def seqSize : List Piece → Nat
  | [] => 0
  | p :: ps => pieceSize p + seqSize ps
end

/-- The innermost open block closed into the one around it, a comma or full stop ending it standing
after it. -/
def closeTop : List (Array Piece) → List (Array Piece)
  | inner :: outer :: rest =>
    match inner.back? with
    | some (.item (.word w)) =>
      if w == "," || w == "." then
        ((outer.push (.block inner.pop.toList)).push (.item (.word w))) :: rest
      else (outer.push (.block inner.toList)) :: rest
    | _ => (outer.push (.block inner.toList)) :: rest
  | stack => stack

/-- Lines with their depths as indentation shows them: a deeper line opens blocks, a shallower one
closes them, and the sentence's full stop is dropped. -/
def nest (lines : List (Nat × List Item)) : List Piece :=
  let step (stack : List (Array Piece)) (line : Nat × List Item) : List (Array Piece) :=
    let stack := (List.range (stack.length - 1 - line.1)).foldl (fun s _ => closeTop s) stack
    let stack := (List.range (line.1 - (stack.length - 1))).foldl (fun s _ => #[] :: s) stack
    match stack with
    | top :: rest => (top ++ line.2.toArray.map Piece.item) :: rest
    | [] => [line.2.toArray.map Piece.item]
  let done := lines.foldl step [#[]]
  let closed := (List.range (done.length - 1)).foldl (fun s _ => closeTop s) done
  let top := match closed with
    | [top] => top.toList
    | _ => []
  match top.getLast? with
  | some (.item (.word ".")) => top.dropLast
  | _ => top

/-- The vocabulary a reader knows: the relations and phrases a page says. -/
structure Vocab where
  rels : List Template
  phrases : List Template

/-- What follows the words `ws` that `l` opens with. -/
def afterWords : List String → List Piece → Option (List Piece)
  | [], l => some l
  | w :: ws, .item (.word w') :: l => if w == w' then afterWords ws l else none
  | _ :: _, _ => none

/-- `l` around the first of its top-level runs of the words `ws`. -/
def splitWords (ws : List String) (acc : Array Piece) : List Piece →
    Option (List Piece × List Piece)
  | [] => none
  | p :: rest =>
    match afterWords ws (p :: rest) with
    | some r => some (acc.toList, r)
    | none => splitWords ws (acc.push p) rest

/-- `l` around the first word `closer` at its top level no `opener` before it claims, each opener
claiming the next closer. -/
def splitPaired (opener closer : String) (n : Nat) (acc : Array Piece) : List Piece →
    Option (List Piece × List Piece)
  | [] => none
  | p :: rest =>
    match p with
    | .item (.word w) =>
      if w == closer then
        if n == 0 then some (acc.toList, rest) else splitPaired opener closer (n - 1) (acc.push p) rest
      else if w == opener then splitPaired opener closer (n + 1) (acc.push p) rest
      else splitPaired opener closer n (acc.push p) rest
    | .item (.leaf _) | .block _ => splitPaired opener closer n (acc.push p) rest

/-- A binder's noun: the words before its first name. -/
def nounWords : List Piece → List String × List Piece
  | .item (.word w) :: rest => let r := nounWords rest; (w :: r.1, r.2)
  | l => ([], l)

/-- Two or more names, "and" before the last. -/
def nameList : List Piece → Option (String × List String × List Piece)
  | .item (.leaf x) :: .item (.word "and") :: .item (.leaf y) :: r => some (x, [y], r)
  | .item (.leaf x) :: .item (.word ",") :: r => (nameList r).map fun (y, ys, r') => (x, y :: ys, r')
  | _ => none

/-- A binder: its noun, its names, several where `many`, and a domain after "of" or "in". -/
def readBinder (many : Bool) (l : List Piece) : Option (Binder String × List Piece) :=
  let (noun, r) := nounWords l
  let names : Option (String × List String × List Piece) := if many then nameList r else
    match r with
    | .item (.leaf x) :: r' => some (x, [], r')
    | _ => none
  names.map fun (x, xs, r') => match r' with
    | .item (.word d) :: .item (.leaf v) :: r'' =>
      if d == "of" || d == "in" then (⟨noun, x, xs, some v⟩, r'') else (⟨noun, x, xs, none⟩, r')
    | _ => (⟨noun, x, xs, none⟩, r')

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

/-- Every way a relation's parts read the whole of `is`, each slot's term with its index. -/
def matchParts (vc : Vocab) : List Part → List Item → List (List (Nat × Term String))
  | [], [] => [[]]
  | [], _ :: _ => []
  | .word w :: ps, .word w' :: is => if w == w' then matchParts vc ps is else []
  | .word _ :: _, _ => []
  | .slot k :: ps, is =>
    (termsAt vc is).flatMap fun (t, rest) => (matchParts vc ps rest).map ((k, t) :: ·)

/-- A run of items no connective splits: the one relation reading it, else a formula alone. -/
def readAtomic (vc : Vocab) (l : List Piece) : Option (Stmt String) :=
  let items := l.filterMap fun
    | .item i => some i
    | .block _ => none
  if items.length != l.length then none else
  let found := vc.rels.flatMap fun t =>
    (matchParts vc t.parts items).filterMap fun pairs => (ordered t pairs).map (.rel t)
  match found, items with
  | [s], _ => some s
  | [], [.leaf x] => some (.atom x)
  | _, _ => none

def quantWords (q : String) : Bool := q == "every" || q == "all"

/-- A sentence's statement: a block is one operand; a top-level "if and only if" splits it; else its
opening words name its connective, each operand but the last ends at the first word closing it at
the top level, and the last runs to the end. -/
def read (vc : Vocab) (l : List Piece) : Option (Stmt String) :=
  match _hl : l with
  | [.block b] => if _h : seqSize b < seqSize l then read vc b else none
  | _ =>
  match splitWords ["if", "and", "only", "if"] #[] l with
  | some (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        match read vc a, read vc b with
        | some x, some y => some (.iff x y)
        | _, _ => none
      else none
    else none
  | none =>
  match _hm : l with
  | .item (.word "for") :: .item (.word q) :: rest =>
    if quantWords q then
      match readBinder (q == "all") rest with
      | some (bd, .item (.word ",") :: body) =>
        if _h : seqSize body < seqSize l then (read vc body).map (.all bd) else none
      | _ => none
    else none
  | .item (.word "there") :: .item (.word "is") :: .item (.word _) :: rest =>
    match readBinder false rest with
    | some (bd, .item (.word "such") :: .item (.word "that") :: body) =>
      if _h : seqSize body < seqSize l then (read vc body).map (.ex bd) else none
    | _ => none
  | .item (.word "there") :: .item (.word "are") :: rest =>
    match readBinder true rest with
    | some (bd, .item (.word "such") :: .item (.word "that") :: body) =>
      if _h : seqSize body < seqSize l then (read vc body).map (.ex bd) else none
    | _ => none
  | .item (.word "if") :: rest =>
    match splitWords [",", "then"] #[] rest with
    | some (hyps, concl) =>
      match splitPaired "both" "and" 0 #[] hyps with
      | some (h1, more) =>
        let chain := .item (.word "if") :: more ++ .item (.word ",") :: .item (.word "then") :: concl
        if _hh : seqSize h1 < seqSize l then
          if _hc : seqSize chain < seqSize l then
            match read vc h1, read vc chain with
            | some x, some y => some (.imp x y)
            | _, _ => none
          else none
        else none
      | none =>
        if _hh : seqSize hyps < seqSize l then
          if _hc : seqSize concl < seqSize l then
            match read vc hyps, read vc concl with
            | some x, some y => some (.imp x y)
            | _, _ => none
          else none
        else none
    | none => none
  | .item (.word "both") :: rest =>
    match splitPaired "both" "and" 0 #[] rest with
    | some (a, b) =>
      if _h1 : seqSize a < seqSize l then
        if _h2 : seqSize b < seqSize l then
          match read vc a, read vc b with
          | some x, some y => some (.conj x y)
          | _, _ => none
        else none
      else none
    | none => none
  | .item (.word "either") :: rest =>
    match splitPaired "either" "or" 0 #[] rest with
    | some (a, b) =>
      if _h1 : seqSize a < seqSize l then
        if _h2 : seqSize b < seqSize l then
          match read vc a, read vc b with
          | some x, some y => some (.disj x y)
          | _, _ => none
        else none
      else none
    | none => none
  | .item (.word "it") :: .item (.word "is") :: .item (.word "not") :: .item (.word "the") ::
      .item (.word "case") :: .item (.word "that") :: rest =>
    if _h : seqSize rest < seqSize l then (read vc rest).map .neg else none
  | _ => readAtomic vc l
termination_by seqSize l
decreasing_by all_goals (subst_vars; assumption)

/-! ## Lines from each artifact -/

/-- A formula letter in mathematical italic as its plain letter. -/
def plainChar (c : Char) : Char :=
  let n := c.toNat
  if 0x1D44E ≤ n && n ≤ 0x1D467 then Char.ofNat (n - 0x1D44E + 'a'.toNat)
  else if 0x1D434 ≤ n && n ≤ 0x1D44D then Char.ofNat (n - 0x1D434 + 'A'.toNat)
  else if n == 0x210E then 'h'
  else c

def plainName (s : String) : String := String.ofList (s.toList.map plainChar)

/-- A word with its closing comma or full stop apart. -/
def punct (w : String) : List Item :=
  if w.length > 1 && (w.endsWith "," || w.endsWith ".") then
    [.word (w.dropEnd 1).toString, .word (w.takeEnd 1).toString]
  else [.word w]

/-- A line's items with each run of formula pieces one formula, a space between its pieces. -/
def joinLeaves (items : List Item) : List Item :=
  (items.foldl (fun (acc : Array Item) it => match acc.back?, it with
    | some (.leaf a), .leaf b => acc.pop.push (.leaf (a ++ " " ++ b))
    | _, _ => acc.push it) #[]).toList

/-- A sentence's lines as a reader reads them: its head through its closing parenthesis aside, each
word's closing comma or full stop apart, each formula's pieces one formula, and its opening word in
lower case. -/
def finish (lines : List (Nat × List Item)) : List (Nat × List Item) :=
  let dropHead (items : List Item) : List Item :=
    match items.findIdx? (fun | .word w => w.endsWith ")." | .leaf _ => false) with
    | some i => items.drop (i + 1)
    | none => items
  let lines := match lines with
    | (d, items) :: rest => (d, dropHead items) :: rest
    | [] => []
  let lines := lines.map fun (d, items) => (d, joinLeaves (items.flatMap fun
    | .word w => punct w
    | .leaf x => [.leaf x]))
  let lower (items : List Item) : List Item := match items with
    | .word w :: rest => .word (w.decapitalize) :: rest
    | _ => items
  match lines.span (·.2.isEmpty) with
  | (empty, (d, items) :: rest) => empty ++ (d, lower items) :: rest
  | (empty, []) => empty

/-- A text's words, white space between them. -/
def rawWords (s : String) : Array Item :=
  ((s.split fun c => c == ' ' || c == '\n').toList.filter (!·.isEmpty)).toArray.map
    fun w => .word w.toString

def classOf (attrs : Array (String × String)) : String :=
  ((attrs.find? (·.1 == "class")).map (·.2)).getD ""

mutual
/-- A web line's items: its text's words, each formula's text one leaf. -/
def htmlItemsOne : Html.Node → Array Item → Array Item
  | .text s, acc => (rawWords s).foldl Array.push acc
  | .elem tag _ kids, acc =>
    if tag == "math" then acc.push (.leaf (plainName (nodeTextList "" kids.toList)))
    else htmlItemsList kids.toList acc
  | .style _, acc | .script _ _, acc => acc
def htmlItemsList : List Html.Node → Array Item → Array Item
  | [], acc => acc
  | n :: rest, acc => htmlItemsList rest (htmlItemsOne n acc)
end

mutual
/-- A laid-out paragraph's lines, each with its depth: a line one, a scope one step in. -/
def htmlLinesOne (depth : Nat) : Html.Node → Array (Nat × List Item) → Array (Nat × List Item)
  | .elem tag attrs kids, acc =>
    if tag == "span" && classOf attrs == "lines-line" then
      acc.push (depth, (htmlItemsList kids.toList #[]).toList)
    else if tag == "span" && classOf attrs == "lines-scope" then
      htmlLinesList (depth + 1) kids.toList acc
    else acc
  | .text _, acc | .style _, acc | .script _ _, acc => acc
def htmlLinesList (depth : Nat) : List Html.Node → Array (Nat × List Item) →
    Array (Nat × List Item)
  | [], acc => acc
  | n :: rest, acc => htmlLinesList depth rest (htmlLinesOne depth n acc)
end

mutual
/-- Every laid-out paragraph of a web page, in order. -/
def htmlParasOne : Html.Node → Array (List (Nat × List Item)) → Array (List (Nat × List Item))
  | .elem tag attrs kids, acc =>
    if tag == "p" && classOf attrs == "lines" then
      acc.push (htmlLinesList 0 kids.toList #[]).toList
    else htmlParasList kids.toList acc
  | .text _, acc | .style _, acc | .script _ _, acc => acc
def htmlParasList : List Html.Node → Array (List (Nat × List Item)) →
    Array (List (Nat × List Item))
  | [], acc => acc
  | n :: rest, acc => htmlParasList rest (htmlParasOne n acc)
end

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

/-- The laid-out paragraphs of a page: each from a line opening on a theorem's head to the next, each
line's depth its indent over the first's in steps of `step`. -/
def pdfParas (mathIdx : Nat) (step : Int) (lines : Array Layout.LineOut) :
    Array (List (Nat × List Item)) := Id.run do
  let mut out : Array (List (Nat × List Item)) := #[]
  let mut cur : Array (Nat × List Item) := #[]
  let mut x0 : Int := 0
  for l in lines do
    if (lineText l).startsWith "Theorem (" then
      unless cur.isEmpty do out := out.push cur.toList
      cur := #[]
      x0 := l.x
    let depth := ((l.x - x0 + step / 2) / step).toNat
    cur := cur.push (depth, pdfItems mathIdx l)
  unless cur.isEmpty do out := out.push cur.toList
  return out

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

/-- The laid-out paragraphs of a twin: each theorem's paragraph, its lines split at hard breaks. -/
def twinParas (md : String) : Array (List (Nat × List Item)) :=
  ((md.splitOn "\n\n").filter (·.startsWith "**Theorem** (")).toArray.map fun para =>
    (para.splitOn "\\\n").map fun line =>
      let (d, rest) := twinDepth line
      (d, twinItems rest)

/-! ## Invented statements -/

def L (s : String) : Leaf := Tests.LeanProse.wordLeaf s

/-- The table invented statements are said through: the core table's relations and four declared
phrases, two holding a connective's word. -/
def tb (_ : Unit) : Table :=
  (tableFor (Tests.LeanProse.factsWith #[("Tide.height", #[.explicit, .explicit]),
      ("Tide.Calm", #[.explicit]), ("Tide.Between", #[.explicit, .explicit, .explicit]),
      ("Tide.gap", #[.explicit, .explicit])])
    [("Tide.height", "the height after #2 steps of #1"), ("Calm", "#1 is calm"),
     ("Between", "#1 lies between #2 and #3"), ("gap", "the gap between #1 and #2")]).table

def relT (c : String) : Template := ((tb ()).rels.lookup c).getD ⟨[]⟩

def rel2 (c a b : String) : Stmt Leaf := .rel (relT c) [.leaf (L a), .leaf (L b)]

def lt (a b : String) : Stmt Leaf := rel2 "LT.lt" a b
def le (a b : String) : Stmt Leaf := rel2 "LE.le" a b
def eq (a b : String) : Stmt Leaf := rel2 "Eq" a b
def dvd (a b : String) : Stmt Leaf := rel2 "Dvd.dvd" a b
def calm (a : String) : Stmt Leaf := .rel (relT "Tide.Calm") [.leaf (L a)]
def P (s : String) : Stmt Leaf := .atom (L s)

def heightOf (a b : String) : Term Leaf :=
  .phrase (((tb ()).phrases.lookup "Tide.height").getD ⟨[]⟩) [L a, L b]

def gapOf (a b : String) : Term Leaf :=
  .phrase (((tb ()).phrases.lookup "Tide.gap").getD ⟨[]⟩) [L a, L b]

def between (a b c : String) : Stmt Leaf :=
  .rel (relT "Tide.Between") [.leaf (L a), .leaf (L b), .leaf (L c)]

def nat (x : String) : Binder Leaf := ⟨["natural", "number"], L x, [], none⟩
def nats (x : String) (ys : List String) : Binder Leaf := ⟨["natural", "numbers"], L x, ys.map L, none⟩
def elt (x T : String) : Binder Leaf := ⟨["element"], L x, [], some (L T)⟩
def prop (p : String) : Binder Leaf := ⟨["proposition"], L p, [], none⟩
def props (p : String) (qs : List String) : Binder Leaf :=
  ⟨["propositions"], L p, qs.map L, none⟩
def ty (a : String) : Binder Leaf := ⟨["type"], L a, [], none⟩

/-- Invented statements, each named by what its scopes do. -/
def corpus : List (String × Stmt Leaf) :=
  [("a quantifier inside a quantifier", .all (nat "x") (.ex (nat "y") (lt "x" "y"))),
   ("an existential over a universal", .ex (nat "x") (.all (nat "y") (le "y" "x"))),
   ("quantifiers over two nouns", .all (ty "A") (.all (elt "a" "A") (eq "a" "a"))),
   ("a plural quantifier over a conjunction",
     .all (nats "x" ["y"]) (.ex (nat "z") (.conj (le "x" "z") (le "y" "z")))),
   ("three quantifiers deep", .all (ty "A") (.all (elt "a" "A") (.ex (elt "b" "A") (eq "a" "b")))),
   ("an existential whose body is a conditional",
     .ex (nat "x") (.all (nat "y") (.imp (lt "y" "x") (.ex (nat "z") (lt "y" "z"))))),
   ("a curried implication", .imp (le "x" "y") (.imp (le "y" "z") (le "x" "z"))),
   ("three curried hypotheses", .imp (P "P") (.imp (P "Q") (.imp (P "R") (P "S")))),
   ("an implication as a hypothesis", .imp (.imp (P "P") (P "Q")) (P "R")),
   ("a quantifier as a hypothesis", .imp (.all (nat "x") (le "x" "y")) (P "Q")),
   ("implications nested in hypotheses", .imp (.imp (.imp (P "P") (P "Q")) (P "R")) (P "S")),
   ("a quantifier among curried hypotheses",
     .imp (P "P") (.imp (.all (nat "x") (lt "x" "y")) (P "Q"))),
   ("a conjunction as the one hypothesis", .imp (.conj (P "P") (P "Q")) (P "R")),
   ("a conjunction among curried hypotheses", .imp (P "P") (.imp (.conj (P "Q") (P "R")) (P "S"))),
   ("a conjunction as the last curried hypothesis",
     .imp (P "P") (.imp (P "Q") (.imp (.conj (P "R") (P "S")) (P "T")))),
   ("a disjunction as a conclusion", .imp (P "P") (.disj (P "Q") (P "R"))),
   ("a conjunction of quantified statements",
     .conj (.all (nat "x") (le "x" "x")) (.ex (nat "y") (eq "y" "y"))),
   ("a quantifier over a conjunction holding a quantifier",
     .all (nat "x") (.conj (le "x" "y") (.all (nat "z") (lt "z" "x")))),
   ("a conjunction opening on an existential", .conj (.ex (nat "x") (eq "x" "y")) (P "R")),
   ("a conjunction closing on a quantifier", .conj (P "P") (.all (nat "x") (le "x" "x"))),
   ("a disjunction of quantified statements",
     .disj (.all (nat "x") (le "x" "x")) (.all (nat "y") (lt "y" "y"))),
   ("a conjunction holding a conditional first", .conj (.imp (P "P") (P "Q")) (P "R")),
   ("a negated quantifier", .neg (.all (nat "x") (lt "x" "y"))),
   ("a negated conjunction holding a negation", .neg (.conj (P "P") (.neg (P "Q")))),
   ("a double negation", .neg (.neg (P "P"))),
   ("a negated existential under a quantifier", .all (nat "x") (.neg (.ex (nat "y") (lt "y" "x")))),
   ("a negated implication", .neg (.imp (P "P") (P "Q"))),
   ("a negation opening a conjunction", .conj (.neg (P "P")) (P "Q")),
   ("an equivalence of conjunctions", .iff (.conj (P "P") (P "Q")) (.conj (P "Q") (P "P"))),
   ("a quantified equivalence of conjunctions",
     .all (props "p" ["q"]) (.iff (.conj (P "p") (P "q")) (.conj (P "q") (P "p")))),
   ("an equivalence holding one", .all (prop "p") (.iff (P "p") (.iff (P "p") (P "q")))),
   ("an equivalence as a conclusion", .imp (P "P") (.iff (P "Q") (P "R"))),
   ("an equivalence opening on a quantifier", .iff (.all (nat "x") (le "x" "x")) (P "Q")),
   ("an equivalence under an existential", .ex (nat "x") (.iff (eq "x" "y") (P "R"))),
   ("a negated equivalence", .neg (.iff (P "P") (P "Q"))),
   ("an equivalence of equivalences", .iff (.iff (P "P") (P "Q")) (P "R")),
   ("an equivalence closing a conjunction", .conj (P "P") (.iff (P "Q") (P "R"))),
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
   ("a relation holding 'and' opening a conjunction", .conj (between "a" "b" "c") (P "Q")),
   ("a relation holding 'and' closing a conjunction", .conj (P "Q") (between "a" "b" "c")),
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

/-- A random one-letter leaf. -/
def randLeaf (s : UInt64) : Leaf × UInt64 :=
  let letters := ["a", "b", "c", "d", "k", "m", "n", "u", "v", "w"]
  let (k, s) := rand s letters.length
  (L (letters.getD k "a"), s)

/-- A random term: a leaf, or a declared phrase over leaves. -/
def randTerm (s : UInt64) : Term Leaf × UInt64 :=
  let (k, s) := rand s 6
  let (a, s) := randLeaf s
  let (b, s) := randLeaf s
  match k with
  | 0 => (.phrase (((tb ()).phrases.lookup "Tide.height").getD ⟨[]⟩) [a, b], s)
  | 1 => (.phrase (((tb ()).phrases.lookup "Tide.gap").getD ⟨[]⟩) [a, b], s)
  | _ => (.leaf a, s)

/-- A random binder over one to three one-letter names. -/
def randBinder (s : UInt64) : Binder Leaf × UInt64 :=
  let (k, s) := rand s 4
  let (more, s) := rand s 3
  let (x, s) := randLeaf s
  let (ys, s) := (List.range more).foldl (fun (acc : List Leaf × UInt64) _ =>
    let (y, s) := randLeaf acc.2
    (acc.1 ++ [y], s)) ([], s)
  let pick (one many : List String) : List String := if more == 0 then one else many
  match k with
  | 0 => (⟨pick ["natural", "number"] ["natural", "numbers"], x, ys, none⟩, s)
  | 1 => (⟨pick ["proposition"] ["propositions"], x, ys, none⟩, s)
  | 2 => (⟨pick ["type"] ["types"], x, ys, none⟩, s)
  | _ => (⟨pick ["element"] ["elements"], x, ys, some (L "T")⟩, s)

/-- A random statement of depth at most `d` over the core table's relations and the declared
phrase and relation. -/
def randStmt : Nat → UInt64 → Stmt Leaf × UInt64
  | 0, s =>
    let rels := (tb ()).rels
    let (k, s) := rand s (rels.length + 1)
    match rels[k]? with
    | some (_, r) =>
      let (args, s) := (List.range r.arity).foldl (fun (acc : List (Term Leaf) × UInt64) _ =>
        let (x, s) := randTerm acc.2
        (acc.1 ++ [x], s)) ([], s)
      (.rel r args, s)
    | none => let (a, s) := randLeaf s; (.atom a, s)
  | d + 1, s =>
    let (k, s) := rand s 9
    let (a, s) := randStmt d s
    let (b, s) := randStmt d s
    let (q, s) := randBinder s
    match k with
    | 0 => (.all q a, s)
    | 1 => (.ex q a, s)
    | 2 => (.imp a b, s)
    | 3 => (.conj a b, s)
    | 4 => (.disj a b, s)
    | 5 => (.iff a b, s)
    | 6 => (.neg a, s)
    | _ => (a, s)

/-- `n` random statements of depth at most four. -/
def randoms (n : Nat) : List (Stmt Leaf) :=
  ((List.range n).foldl (fun (acc : Array (Stmt Leaf) × UInt64) _ =>
    let (st, s) := randStmt 4 acc.2
    (acc.1.push st, s)) (#[], 0x2545F4914F6CDD1D)).1.toList

def termMap {α β : Type} (f : α → β) : Term α → Term β
  | .leaf a => .leaf (f a)
  | .phrase t args => .phrase t (args.map f)

def binderMap {α β : Type} (f : α → β) (b : Binder α) : Binder β :=
  ⟨b.noun, f b.name, b.more.map f, b.dom.map f⟩

/-- A statement with each leaf as `f` names it. -/
def stmtMap {α β : Type} (f : α → β) : Stmt α → Stmt β
  | .all b s => .all (binderMap f b) (stmtMap f s)
  | .ex b s => .ex (binderMap f b) (stmtMap f s)
  | .imp a b => .imp (stmtMap f a) (stmtMap f b)
  | .conj a b => .conj (stmtMap f a) (stmtMap f b)
  | .disj a b => .disj (stmtMap f a) (stmtMap f b)
  | .iff a b => .iff (stmtMap f a) (stmtMap f b)
  | .neg a => .neg (stmtMap f a)
  | .rel t args => .rel t (args.map (termMap f))
  | .atom x => .atom (f x)

/-- A page setting each statement in words, the `i`-th as theorem `s<i>`. -/
def pageOf (stmts : List (Stmt Leaf)) : Ir.Doc × Array Diag :=
  let paras := stmts.toArray.mapIdx fun i st =>
    Code.wordsRaws (Tests.LeanProse.theoremAt s!"s{i}" (i + 1) (Tests.LeanProse.selfEq 0)) st {}
  let raws : Array Parse.Raw := #[.ctrl "title" {}, .group #[.word "Readings" {}] {},
    .env "document" (paras.foldl (· ++ ·) #[]) {}]
  Elab.runRaws "readings.lean" raws

/-- Each statement's reading off each artifact's paragraphs, by position: the failures, labelled. -/
def failuresOf (vc : Vocab) (labels : List String) (want : List (Stmt String))
    (paras : Array (List (Nat × List Item))) : List String :=
  (labels.zip want).zipIdx.filterMap fun ((label, w), i) =>
    match paras[i]? with
    | none => some s!"{label}: no paragraph"
    | some lines =>
      let got := read vc (nest (finish lines))
      if got == some w then none else some s!"{label}: {repr got}"

def readingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let vc : Vocab := ⟨(tb ()).rels.map (·.2), (tb ()).phrases.map (·.2)⟩
  let rnd := randoms 300
  let stmts := corpus.map (·.2) ++ rnd
  let labels := corpus.map (·.1) ++ (List.range rnd.length).map (s!"random {·}")
  let want := stmts.map (stmtMap Tests.LeanProse.leafWord)
  let (doc, _) := pageOf stmts
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "reading: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "reading: the mono face loads" false
  let fonts ← mathSetOf (slotPairOf 2 text mono)
  let geom := Layout.Geom.ofPage doc.page
  let step := Ir.linesStep.resolve geom.fontSize 0
  let pdf := pdfParas (fonts.math.getD 0) step (bodyLines (layoutOf fonts doc))
  let html := htmlParasList (docNodesOf doc).toList #[]
  let sheet := (HtmlDoc.emit {} doc).1
  t "reading: the web page's stylesheet sets each line a block of its own and each scope a step in"
    (hasStr sheet ".lines-line, .lines-scope { display: block; }" &&
      hasStr sheet s!".lines-scope \{ padding-inline-start: {HtmlDoc.cssLength Ir.linesStep}; }")
  let twin := twinParas (MarkdownDoc.emit doc)
  for (what, paras) in [("the page", pdf), ("the web page", html), ("the twin", twin)] do
    let failed := failuresOf vc labels want paras
    t s!"reading: every invented statement reads back from {what}'s lines ({failed.take 3})"
      (paras.size == stmts.length && failed.isEmpty)
  -- Planted: the same lines all at the margin lose the scopes their blocks bound.
  let flat := pdf.map (·.map fun (_, items) => (0, items))
  let misread := (failuresOf vc labels want flat).filterMap fun f => (f.splitOn ":").head?
  let bound := ["an equivalence holding one", "an equivalence as a conclusion",
    "an equivalence under an existential", "an equivalence closing a conjunction",
    "a quantified equivalence of conjunctions", "a negated equivalence"]
  t s!"reading: set at the margin, the statements whose blocks bound an 'if and only if' read otherwise ({misread.length} of {stmts.length}: {bound.filter (!misread.contains ·)})"
    (bound.all misread.contains)

end Tests.LeanProseReading
