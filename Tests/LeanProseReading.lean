module

public import Tests.Artifact
public import Tests.LeanProse

public section

open LeanTex.Core LeanTex.Core.LeanProse Prose

/-! Invented statements read back from every artifact, by indentation or by marks, by two readers
sharing no grammar with the renderer: one weighing every reading, one running scopes to block ends. -/

namespace Tests.LeanProseReading

/-- What a reader sees of a sentence: words, and each formula by its text. -/
inductive Item where
  | word (s : String)
  | leaf (s : String)
  deriving BEq, Repr, Inhabited

/-- A sentence as its layout shows it: items, and blocks. -/
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

def word (w : String) : Piece := .item (.word w)

/-- The innermost open block closed into the one around it, a comma or full stop ending it, which
the page sets inside the block it closes, standing after it. -/
def closeTop : List (Array Piece) → List (Array Piece)
  | inner :: outer :: rest =>
    match inner.back? with
    | some (.item (.word w)) =>
      if w == "," || w == "." then ((outer.push (.block inner.pop.toList)).push (word w)) :: rest
      else (outer.push (.block inner.toList)) :: rest
    | _ => (outer.push (.block inner.toList)) :: rest
  | stack => stack

/-- The sentence once every block is closed, its full stop dropped. -/
def closeAll (stack : List (Array Piece)) : List Piece :=
  let closed := (List.range (stack.length - 1)).foldl (fun s _ => closeTop s) stack
  let top := match closed with
    | [top] => top.toList
    | _ => []
  match top.getLast? with
  | some (.item (.word ".")) => top.dropLast
  | _ => top

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

/-- A quantifier's binder and the body after its comma, or an existential's after "such that". -/
def quantified (l : List Piece) : Option (Bool × Binder String × List Piece) :=
  match l with
  | .item (.word "for") :: .item (.word q) :: rest =>
    if q == "every" || q == "all" then
      match readBinder (q == "all") rest with
      | some (bd, .item (.word ",") :: body) => some (true, bd, body)
      | _ => none
    else none
  | .item (.word "there") :: .item (.word "is") :: .item (.word _) :: rest =>
    match readBinder false rest with
    | some (bd, .item (.word "such") :: .item (.word "that") :: body) => some (false, bd, body)
    | _ => none
  | .item (.word "there") :: .item (.word "are") :: rest =>
    match readBinder true rest with
    | some (bd, .item (.word "such") :: .item (.word "that") :: body) => some (false, bd, body)
    | _ => none
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
    | .block _ => none

def chainOf : List (Stmt String) → Stmt String → Stmt String
  | [], c => c
  | h :: hs, c => .imp h (chainOf hs c)

/-! ## A reader weighing every reading

Every reading the words allow of the whole of a list, at most two: a block reads as what it holds,
and every connective's every split is weighed, its operands read in turn. -/

mutual

def readsN (vc : Vocab) (l : List Piece) : List (Stmt String) :=
  let lone : List (Stmt String) := match _hl : l with
    | [.block b] => if _h : seqSize b < seqSize l then readsN vc b else []
    | _ => []
  let iffs := (wordSplits ["if", "and", "only", "if"] #[] l).flatMap fun (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        (readsN vc a).flatMap fun x => (readsN vc b).map (.iff x ·)
      else []
    else []
  let quants := match quantified l with
    | some (all, bd, body) =>
      if _h : seqSize body < seqSize l then (readsN vc body).map (quantOf all bd) else []
    | none => []
  let opened : List (Stmt String) := match _hl : l with
    | .item (.word "if") :: rest =>
      (wordSplits [",", "then"] #[] rest).flatMap fun (hyps, concl) =>
        if _h1 : seqSize hyps < seqSize l then
          if _h2 : seqSize concl < seqSize l then
            (hypsN vc hyps).flatMap fun hs => (readsN vc concl).map (chainOf hs ·)
          else []
        else []
    | .item (.word "both") :: rest =>
      (wordSplits ["and"] #[] rest).flatMap fun (a, b) =>
        if _h1 : seqSize a < seqSize l then
          if _h2 : seqSize b < seqSize l then
            (readsN vc a).flatMap fun x => (readsN vc b).map (.conj x ·)
          else []
        else []
    | .item (.word "either") :: rest =>
      (wordSplits ["or"] #[] rest).flatMap fun (a, b) =>
        if _h1 : seqSize a < seqSize l then
          if _h2 : seqSize b < seqSize l then
            (readsN vc a).flatMap fun x => (readsN vc b).map (.disj x ·)
          else []
        else []
    | .item (.word "it") :: .item (.word "is") :: .item (.word "not") :: .item (.word "the") ::
        .item (.word "case") :: .item (.word "that") :: rest =>
      if _h : seqSize rest < seqSize l then (readsN vc rest).map .neg else []
    | _ => []
  let atoms := match onlyItems l with
    | some is => (atomsAt vc is).filterMap fun (s, r) => if r.isEmpty then some s else none
    | none => []
  (lone ++ iffs ++ quants ++ opened ++ atoms).take 2
termination_by (seqSize l, 0)
decreasing_by all_goals (subst_vars; apply Prod.Lex.left; assumption)

/-- Every way a curried implication's hypotheses read, "and" between two. -/
def hypsN (vc : Vocab) (l : List Piece) : List (List (Stmt String)) :=
  let one := (readsN vc l).map ([·])
  let more := (wordSplits ["and"] #[] l).flatMap fun (a, b) =>
    if _h1 : seqSize a < seqSize l then
      if _h2 : seqSize b < seqSize l then
        (readsN vc a).flatMap fun x => (hypsN vc b).map (x :: ·)
      else []
    else []
  (one ++ more).take 2
termination_by (seqSize l, 1)
decreasing_by all_goals (subst_vars; first | (apply Prod.Lex.left; assumption) | (apply Prod.Lex.right; omega))

end

/-! ## A reader running each scope to its block's end

One reading, left to right: a block one unit, a prefix scope to its block's end, a clause to its
last word, the longest relation, and an equivalence joining the clauses around it. -/

mutual

def unitG (vc : Vocab) (l : List Piece) : Option (Stmt String × List Piece) :=
  match _hl : l with
  | .block b :: r =>
    if _h : seqSize b < seqSize l then
      match stmtG vc b with
      | some (s, []) => some (s, r)
      | _ => none
    else none
  | .item (.word "if") :: rest =>
    if _h : seqSize rest < seqSize l then
      match hypsG vc rest with
      | some (hs, concl) =>
        if _h2 : seqSize concl < seqSize l then
          match stmtG vc concl with
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
  | _ =>
    match quantified l with
    | some (all, bd, body) =>
      if _h : seqSize body < seqSize l then
        match stmtG vc body with
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

def stmtG (vc : Vocab) (l : List Piece) : Option (Stmt String × List Piece) :=
  match unitG vc l with
  | some (s, r) =>
    match afterWords ["if", "and", "only", "if"] r with
    | some r' =>
      if _h : seqSize r' < seqSize l then (stmtG vc r').map fun (t, r'') => (.iff s t, r'')
      else none
    | none => some (s, r)
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
  match stmtG vc l with
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
word's closing comma or full stop apart, each formula's pieces one formula, and its opening word,
past any marks, in lower case. -/
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
  match lines.span (fun l => (l.2.filter (· != .word "(")).isEmpty) with
  | (empty, (d, items) :: rest) =>
    let marks := items.takeWhile (· == .word "(")
    empty ++ (d, marks ++ lower (items.drop marks.length)) :: rest
  | (empty, []) => empty

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

mutual
/-- Every laid-out paragraph of a web page, in order: its lines with their depths, or, where
`spoken`, its words and marks as assistive technology reads them, the indentation unseen. -/
def htmlParasOne (spoken : Bool) : Html.Node → Array (List (Nat × List Item)) →
    Array (List (Nat × List Item))
  | .elem tag attrs kids, acc =>
    if tag == "p" && classOf attrs == "lines" then
      if spoken then acc.push [(0, (htmlItemsList true kids.toList #[]).toList)]
      else acc.push (htmlLinesList 0 kids.toList #[]).toList
    else htmlParasList spoken kids.toList acc
  | .text _, acc | .style _, acc | .script _ _, acc => acc
def htmlParasList (spoken : Bool) : List Html.Node → Array (List (Nat × List Item)) →
    Array (List (Nat × List Item))
  | [], acc => acc
  | n :: rest, acc => htmlParasList spoken rest (htmlParasOne spoken n acc)
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
    | '\u2003' :: '\u2002' :: rest => go rest (n + 1)
    | _ => (n, cs)
  let r := go s.toList 0
  (r.1, String.ofList r.2)

/-- The laid-out paragraphs of a twin: each theorem's paragraph, its lines split at hard breaks. -/
def twinParas (md : String) : Array (List (Nat × List Item)) :=
  ((md.splitOn "\n\n").filter (·.startsWith "**Theorem** (")).toArray.map fun para =>
    (para.splitOn "\\\n").map fun line =>
      let (d, rest) := twinDepth line
      (d, twinItems rest)

/-- A page's lines as a laid-out paragraph's: a line wrapping stays at its depth, and two lines of
one paragraph never share one. -/
def depthRuns (lines : List (Nat × List Item)) : List (Nat × List Item) :=
  (lines.foldl (fun (acc : Array (Nat × List Item)) (d, items) => match acc.back? with
    | some (d', prev) => if d == d' then acc.pop.push (d, prev ++ items) else acc.push (d, items)
    | none => acc.push (d, items)) #[]).toList

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

/-- A tagged paragraph as assistive technology reads it: each line's words as the page sets them,
between the parentheses its replacement text adds; none where a replacement's words are not the
line's. -/
def spokenPara (texts : List (Option String)) (lines : List (Nat × List Item)) :
    Option (List (Nat × List Item)) :=
  let runs := depthRuns lines
  if runs.length != texts.length then none else
  let squash (s : String) : String := String.ofList (s.toList.filter (!·.isWhitespace))
  let itemText (items : List Item) : String := squash (String.join (items.map fun
    | .word w => w
    | .leaf x => x))
  (texts.zip runs).foldlM (fun (acc : List (Nat × List Item)) (t, (_, items)) =>
    match t with
    | none => some (acc ++ [(0, items)])
    | some text =>
      let (o, c, core) := marksOf text
      if plainName (squash core) != itemText items then none
      else some (acc ++ [(0, List.replicate o (.word "(") ++ items ++ List.replicate c (.word ")"))]))
    []

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
   ("a negated quantifier as a hypothesis", .imp (.neg (.all (nat "x") (le "x" "y"))) (P "Q")),
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

/-- `n` random statements of depth at most four over the invented table. -/
def randoms (n : Nat) : List (Stmt Leaf) :=
  ((List.range n).foldl (fun (acc : Array (Stmt Leaf) × UInt64) _ =>
    let (st, s) := randStmt (tb ()) 4 acc.2
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
    Code.wordsRaws (theoremAt s!"s{i}" (i + 1) (selfEq 0)) st {}
  let raws : Array Parse.Raw := #[.ctrl "title" {}, .group #[.word "Readings" {}] {},
    .env "document" (paras.foldl (· ++ ·) #[]) {}]
  Elab.runRaws "readings.lean" raws

/-- Whether both readers take a sentence for exactly the statement. -/
def readsBack (vc : Vocab) (want : Stmt String) (l : List Piece) : Bool :=
  readsN vc l == [want] && readG vc l == some want

/-- Each statement's reading off an artifact's paragraphs, by position: the failures, labelled. -/
def failuresOf (vc : Vocab) (labels : List String) (want : List (Stmt String))
    (paras : Array (List Piece)) : List String :=
  (labels.zip want).zipIdx.filterMap fun ((label, w), i) =>
    match paras[i]? with
    | none => some s!"{label}: no paragraph"
    | some l =>
      if readsBack vc w l then none
      else some s!"{label}: {(readsN vc l).length} readings, {repr (readG vc l)}"

/-! ## Each block set at its scope's margin -/

/-- Every block of a sentence, each as the sentence with that block's lines set at the margin of the
lines around it. -/
def flattenings : List Piece → List (List Piece)
  | [] => []
  | .item i :: rest => (flattenings rest).map (.item i :: ·)
  | .block b :: rest =>
    (b ++ rest) :: (flattenings b).map (fun b' => .block b' :: rest) ++
      (flattenings rest).map (.block b :: ·)
termination_by l => seqSize l
decreasing_by all_goals (simp only [seqSize, pieceSize]; omega)

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
termination_by l => seqSize l
decreasing_by all_goals (simp only [seqSize, pieceSize]; omega)

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
  let pageLines := pdfParas (fonts.math.getD 0) step (bodyLines out)
  let page := pageLines.map (nest ∘ finish)
  let nodes := (docNodesOf doc).toList
  let web := (htmlParasList false nodes #[]).map (nest ∘ finish)
  let webSpoken := (htmlParasList true nodes #[]).map fun ls => byMarks ((finish ls).flatMap (·.2))
  let sheet := (HtmlDoc.emit {} doc).1
  t "reading: the web page's stylesheet sets each line a block, each scope a step in and each mark out of sight"
    (hasStr sheet ".lines-line, .lines-scope { display: block; }" &&
      hasStr sheet s!".lines-scope \{ padding-inline-start: {HtmlDoc.cssLength Ir.linesStep}; }" &&
      hasStr sheet s!".lines-mark \{ {HtmlDoc.visuallyHidden} }")
  let twin := (twinParas (MarkdownDoc.emit doc)).map (nest ∘ finish)
  let pdf := driverPdf fonts geom doc out
  let elems := match PdfRead.objects pdf, PdfRead.trailer pdf with
    | .ok es, .ok trailer =>
      let es := es.val
      match (PdfCensus.catalogOf es trailer).get? "StructTreeRoot" with
      | some (.ref r _) => match es.find? (·.num == r) with
        | some root => readStructTree es root.val
        | none => #[]
      | _ => #[]
    | _, _ => #[]
  let tagged := taggedParas elems
  t s!"reading: the tagged file holds each laid-out paragraph as one P of its lines' Spans ({tagged.size} of {stmts.length})"
    (tagged.size == stmts.length)
  let spokenPdf := (tagged.zip pageLines).filterMap fun (texts, lines) =>
    (spokenPara texts lines).map fun ls => byMarks ((finish ls).flatMap (·.2))
  t s!"reading: each line's replacement text in the tagged file says the line's words between its marks ({spokenPdf.size} of {tagged.size})"
    (spokenPdf.size == tagged.size)
  for (what, paras) in [("the page", page), ("the web page", web), ("the twin", twin),
      ("the web page as assistive technology reads it", webSpoken),
      ("the tagged file as assistive technology reads it", spokenPdf)] do
    let failed := failuresOf vc labels want paras
    t s!"reading: every invented statement reads back from {what}, by both readers ({failed.take 3})"
      (paras.size == stmts.length && failed.isEmpty)
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
    (kept .equivalence).isEmpty
  t s!"reading: set at its margin, a block a scope opens leaves a reader reading its sentence otherwise ({count .scope} blocks; {named (kept .scope)})"
    (kept .scope).isEmpty
  t s!"reading: a block bounding neither is for the eye, both readers reading its sentence without it ({count .neither} blocks; {named (census.filter fun (_, k, r) => k == .neither && !r)})"
    (census.all fun (_, k, r) => k != .neither || r)

end Tests.LeanProseReading
