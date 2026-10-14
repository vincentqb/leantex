module

public import Std.Data.HashMap
import Std.Data.HashSet
import LeanTex.Core.KeyVal

/-! The CSS an SVG file states (SVG 2 §6): declarations, a selector subset, and the cascade
of CSS Cascading 4 §6 over them. -/

namespace LeanTex.Core.Css

/-- One declaration: its lower-case property, its trimmed value without comments, and its importance. -/
public structure Decl where
  prop : String
  value : String
  important : Bool
  deriving Repr, BEq, Inhabited

/-- What a text says that this reader does not read: a refused spelling, or one outside the subset. -/
public inductive Problem where
  | refused (what : String)
  | unsupported (what : String)
  deriving Repr, BEq, Inhabited

public inductive Combinator where
  | descendant
  | child
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A compound selector: an optional type (`none` for `*` or no type), classes and ids, all required. -/
public structure Compound where
  type : Option String
  classes : Array String
  ids : Array String
  deriving Repr, BEq, Inhabited

/-- A complex selector, left to right; its last compound is the subject. -/
public structure Selector where
  head : Compound
  rest : Array (Combinator × Compound)
  deriving Repr, BEq, Inhabited

public structure Rule where
  selectors : Array Selector
  decls : Array Decl
  deriving Repr, BEq, Inhabited

@[expose] public def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- A line end (CSS Syntax 3 §3.3): line feed, carriage return or form feed. -/
@[expose] public def isLineEnd (c : Char) : Bool := c == '\n' || c == '\r' || c == '\x0c'

/-- CSS text onto `acc` as atoms (CSS Syntax 3 §4.3.5, §4.3.7): a string through its closing quote,
a line end or the text's end, escapes included, or an escape, a backslash and its next character,
is one atom, and any other character stands alone. -/
def atomsGo (acc : Array (List Char)) :
    Option (Char × Array Char) → List Char → Array (List Char)
  | none, [] => acc
  | none, '\\' :: c :: rest => atomsGo (acc.push ['\\', c]) none rest
  | none, c :: rest =>
    if c == '"' || c == '\'' then atomsGo acc (some (c, #[c])) rest
    else atomsGo (acc.push [c]) none rest
  | some (_, cur), [] => acc.push cur.toList
  | some (q, cur), '\\' :: c :: rest => atomsGo acc (some (q, (cur.push '\\').push c)) rest
  | some (q, cur), c :: rest =>
    if c == q || isLineEnd c then atomsGo (acc.push (cur.push c).toList) none rest
    else atomsGo acc (some (q, cur.push c)) rest

/-- CSS text as its atoms. -/
def atoms (s : String) : List (List Char) := (atomsGo #[] none s.toList).toList

/-- An atom opening a block (CSS Syntax 3 §5.5.9). -/
def opensBlock (a : List Char) : Bool := a == ['('] || a == ['['] || a == ['{']

/-- An atom closing a block. -/
def closesBlock (a : List Char) : Bool := a == [')'] || a == [']'] || a == ['}']

/-- A piece's atoms as its text. -/
def pieceText (piece : Array (List Char)) : String :=
  piece.foldl (fun t a => a.foldl String.push t) ""

/-- CSS text cut at each `sep` outside blocks, strings and escapes, each piece as written: a
comma-separated list's items (CSS Syntax 3 §5.4.10), or a block's declarations at `;`. -/
public def splitList (sep : Char) (s : String) : Array String :=
  (KeyVal.splitTopAt opensBlock closesBlock (· == [sep]) (atoms s)).map pieceText

/-- `s` with its comments removed: `/* … */`, an unterminated one to the end. -/
public def stripComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut quote : Option Char := none
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD ' '
    match quote with
    | some q =>
      out := out.push c
      if c == q || isLineEnd c then quote := none
      i := i + 1
    | none =>
      if c == '/' && cs[i + 1]? == some '*' then
        let mut j := i + 2
        for _ in [0:cs.size + 1] do
          if j + 1 ≥ cs.size then
            j := cs.size
            break
          if cs[j]? == some '*' && cs[j + 1]? == some '/' then
            j := j + 2
            break
          j := j + 1
        out := out.push ' '
        i := j
      else
        if c == '"' || c == '\'' then quote := some c
        out := out.push c
        i := i + 1
  return out

/-- A character a fragment identifier in `url(#…)` may hold. -/
@[expose] public def idChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'

/-- A character a numeric colour function's channels may hold. -/
@[expose] public def channelChar (c : Char) : Bool :=
  c.isDigit || c == '.' || c == '%' || c == 'e' || c == 'E' || c == '+' || c == '-' ||
    c == ',' || c == '/' || c == ' '

/-- Whether a call is one this reader admits: a fragment `url(#id)` or a numeric `rgb()`/`rgba()`. -/
public def admitsCall (name arg : String) : Bool :=
  let n := name.toLower
  if n == "url" then
    let a := arg.trimAscii.toString
    let a := if a.length ≥ 2 && (a.startsWith "\"" && a.endsWith "\"" || a.startsWith "'" && a.endsWith "'")
      then ((a.drop 1).dropEnd 1).toString else a
    a.startsWith "#" && a.length > 1 && (a.drop 1).all idChar
  else if n == "rgb" || n == "rgba" then
    !arg.isEmpty && arg.all channelChar
  else false

/-- The first spelling this reader refuses: an escape or an at-sign anywhere, an unterminated
string, or a function outside strings that is nested, unterminated or not admitted. -/
public def refusedIn (s : String) : Option String := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  let mut quote : Option Char := none
  let mut ident := ""
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD ' '
    if c == '\\' then return some "an escape"
    if c == '@' then return some "an at-rule"
    match quote with
    | some q =>
      if c == q || isLineEnd c then quote := none
      i := i + 1
    | none =>
      if c == '"' || c == '\'' then
        quote := some c
        ident := ""
        i := i + 1
      else if c == '(' then
        let mut j := i + 1
        let mut arg := ""
        let mut closed := false
        for _ in [0:cs.size + 1] do
          if j ≥ cs.size then break
          if cs[j]? == some ')' then
            closed := true
            break
          if cs[j]? == some '(' then return some s!"a nested function in {ident}()"
          arg := arg.push (cs[j]?.getD ' ')
          j := j + 1
        if !closed then return some s!"an unterminated {ident}()"
        if !admitsCall ident arg then return some s!"the function {ident}()"
        ident := ""
        i := j + 1
      else
        if c.isAlphanum || c == '-' || c == '_' then ident := ident.push c else ident := ""
        i := i + 1
  if quote.isSome then return some "an unterminated string"
  return none

/-- Whether a string in `s` is broken by a line end (CSS Syntax 3 §4.3.5). -/
@[expose] public def brokenString (s : String) : Bool := Id.run do
  let mut quote : Option Char := none
  for c in s.toList do
    match quote with
    | some q =>
      if c == q then quote := none
      else if isLineEnd c then return true
    | none => if c == '"' || c == '\'' then quote := some c
  return false

/-- The offset of the first `stop` from `i` outside a string, or `cs.size`. -/
public def scanTo (cs : Array Char) (stop : Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut quote : Option Char := none
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := cs[j]?.getD ' '
    match quote with
    | some q =>
      if c == q || isLineEnd c then quote := none
    | none =>
      if c == stop then break
      if c == '"' || c == '\'' then quote := some c
    j := j + 1
  return j

/-- A declaration's value without its trailing `!important`, and whether it held one (CSS Syntax 3
§5.5.6). -/
public def importance (value : String) : String × Bool :=
  if !value.contains '!' then (value, false) else
  let parts := splitList '!' value
  match parts.back? with
  | some imp =>
    if parts.size ≥ 2 && imp.trimAscii.toString.toLower == "important" then
      (("!".intercalate parts.pop.toList).trimAscii.toString, true)
    else (value, false)
  | none => (value, false)

/-- A declaration block's declarations in order; a malformed one is unsupported, a refused spelling refused. -/
public def parseDecls (text : String) : Except Problem (Array Decl) := do
  let text := stripComments text
  if let some what := refusedIn text then throw (.refused what)
  let mut out : Array Decl := #[]
  for part in splitList ';' text do
    let p := part.trimAscii.toString
    if p.isEmpty then continue
    if brokenString part then throw (.unsupported s!"the declaration '{p}', whose string a line end breaks")
    match p.splitOn ":" with
    | prop :: rest@(_ :: _) =>
      let prop := prop.trimAscii.toString.toLower
      let (value, important) := importance (":".intercalate rest).trimAscii.toString
      if prop.isEmpty || !prop.all (fun c => c.isAlphanum || c == '-') then
        throw (.unsupported s!"the declaration '{p}'")
      out := out.push { prop, value, important }
    | _ => throw (.unsupported s!"the declaration '{p}'")
  return out

/-- A character of a CSS identifier: a letter, digit, `-`, `_` or non-ASCII. -/
@[expose] public def identChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c.toNat ≥ 128

/-- One compound selector's text, unless it is outside the subset. -/
public def parseCompound (s : String) : Option Compound := do
  let cs := s.toList
  let typeChars := cs.takeWhile (fun c => identChar c || c == '*')
  let typ := String.ofList typeChars
  let mut rest := cs.drop typeChars.length
  let type : Option String ← if typ.isEmpty || typ == "*" then pure none
    else if typ.all identChar then pure (some typ) else failure
  let mut classes : Array String := #[]
  let mut ids : Array String := #[]
  for _ in [0:cs.length + 1] do
    match rest with
    | [] => break
    | '.' :: more =>
      let name := more.takeWhile identChar
      if name.isEmpty then failure
      classes := classes.push (String.ofList name)
      rest := more.drop name.length
    | '#' :: more =>
      let name := more.takeWhile identChar
      if name.isEmpty then failure
      ids := ids.push (String.ofList name)
      rest := more.drop name.length
    | _ => failure
  if type.isNone && classes.isEmpty && ids.isEmpty && typ != "*" then failure
  return { type, classes, ids }

/-- One complex selector's text: compounds joined by white space (descendant) or `>` (child); one
outside the subset is named whole. -/
public def parseSelector (s : String) : Except String Selector := do
  let outside := s!"the selector '{s}'"
  let spaced := (s.replace ">" " > ").trimAscii.toString
  let words := (spaced.split isWs).toList.map (·.toString) |>.filter (!·.isEmpty)
  match words with
  | [] => throw "an empty selector"
  | first :: more =>
    let some head := parseCompound first | throw outside
    let mut rest : Array (Combinator × Compound) := #[]
    let mut pending := Combinator.descendant
    for w in more do
      if w == ">" then pending := .child
      else
        let some c := parseCompound w | throw outside
        rest := rest.push (pending, c)
        pending := .descendant
    if pending == .child then throw outside
    return { head, rest }

/-- How specific a selector is (Selectors 4 §16): its ids, classes, types. -/
@[expose] public def Selector.specificity (sel : Selector) : Nat × Nat × Nat :=
  let all := #[sel.head] ++ sel.rest.map (·.2)
  (all.foldl (fun n c => n + c.ids.size) 0, all.foldl (fun n c => n + c.classes.size) 0,
    all.foldl (fun n c => n + (if c.type.isSome then 1 else 0)) 0)

/-- A style sheet's rules in order, those outside the subset dropped and named; a refused
spelling refuses the sheet. -/
public def parseSheet (text : String) : Except String (Array Rule × Array String) := do
  let text := stripComments text
  if let some what := refusedIn text then throw what
  let cs := text.toList.toArray
  let n := cs.size
  let slice (a b : Nat) : String := String.ofList (cs.extract a b).toList
  let mut rules : Array Rule := #[]
  let mut dropped : Array String := #[]
  let mut i := 0
  for _ in [0:n + 1] do
    let mut j := i
    for _ in [0:n + 1] do
      if j < n && isWs (cs[j]?.getD ' ') then j := j + 1 else break
    if n ≤ j then break
    let o := scanTo cs '{' i
    if n ≤ o then
      dropped := dropped.push s!"the text '{(slice i n).trimAscii}'"
      break
    let c := scanTo cs '}' (o + 1)
    if n ≤ c then
      dropped := dropped.push "an unterminated rule"
      break
    let sels := (splitList ',' (slice i o)).map (·.trimAscii.toString)
    match sels.mapM parseSelector, parseDecls (slice (o + 1) c) with
    | .ok sels, .ok ds => rules := rules.push { selectors := sels, decls := ds }
    | .error why, _ => dropped := dropped.push why
    | _, .error (.unsupported why) => dropped := dropped.push why
    | _, .error (.refused why) => throw why
    i := c + 1
  return (rules, dropped)

/-- What a selector reads of an element: its type, classes and id. -/
public structure Subject where
  type : String
  classes : Array String
  id : Option String
  deriving Repr, BEq, Inhabited

@[expose] public def Compound.matches (c : Compound) (e : Subject) : Bool :=
  c.type.all (· == e.type) && c.classes.all (e.classes.contains ·) &&
    c.ids.all (some · == e.id)

/-- Whether the remaining compounds match the ancestors `up`, innermost first. -/
public def matchUp (parts : List (Combinator × Compound)) (up : List Subject) : Bool :=
  match parts with
  | [] => true
  | (comb, c) :: more =>
    match comb with
    | .child =>
      match up with
      | p :: ps => c.matches p && matchUp more ps
      | [] => false
    | .descendant => tryAll c more up
where
  tryAll (c : Compound) (more : List (Combinator × Compound)) : List Subject → Bool
    | [] => false
    | p :: ps => (c.matches p && matchUp more ps) || tryAll c more ps

/-- Does `sel` match the element `e` whose ancestors, innermost first, are
`up`? -/
public def Selector.matches (sel : Selector) (e : Subject) (up : List Subject) : Bool :=
  let comps := #[sel.head] ++ sel.rest.map (·.2)
  let combs := sel.rest.map (·.1)
  match comps.back? with
  | none => false
  | some subject =>
    let pairs := (combs.zip comps.pop).toList.reverse
    subject.matches e && matchUp pairs up

/-- What a compound requires of an element first: an id, else a class, else a type; `none` when universal. -/
@[expose] public def Compound.key (c : Compound) : Option (Nat × String) :=
  match c.ids[0]? with
  | some i => some (0, i)
  | none =>
    match c.classes[0]? with
    | some c => some (1, c)
    | none => c.type.map ((2 : Nat), ·)

/-- The key a selector's subject compound requires (`Compound.key`). -/
@[expose] public def Selector.key (sel : Selector) : Option (Nat × String) :=
  ((sel.rest.back?.map (·.2)).getD sel.head).key

/-- The key the compound nearest the subject requires of an ancestor, if the selector has one. -/
@[expose] public def Selector.upKey (sel : Selector) : Option (Nat × String) :=
  if sel.rest.isEmpty then none
  else ((sel.rest.pop.back?.map (·.2)).getD sel.head).key

/-- Every key an element offers a compound: its id, its classes, its type. -/
@[expose] public def Subject.keys (e : Subject) : Array (Nat × String) :=
  (e.id.map ((0 : Nat), ·)).toArray ++ e.classes.map ((1 : Nat), ·) ++ #[(2, e.type)]

/-- A sheet's rules with each selector filed under the keys it requires, so an element meets only
the selectors it can match. -/
public structure RuleIndex where
  rules : Array Rule
  /-- Each rule's first declaration's index in source order. -/
  offsets : Array Nat
  /-- Selectors with no keyed ancestor compound, by their subject's key. -/
  byKey : Std.HashMap (Nat × String) (Array (Nat × Nat))
  /-- Selectors by their subject's key and the key of the compound nearest it. -/
  byPair : Std.HashMap ((Nat × String) × (Nat × String)) (Array (Nat × Nat))
  universal : Array (Nat × Nat)
  deriving Inhabited

public def RuleIndex.ofRules (rules : Array Rule) : RuleIndex := Id.run do
  let mut offsets : Array Nat := #[]
  let mut total := 0
  let mut byKey : Std.HashMap (Nat × String) (Array (Nat × Nat)) := {}
  let mut byPair : Std.HashMap ((Nat × String) × (Nat × String)) (Array (Nat × Nat)) := {}
  let mut universal : Array (Nat × Nat) := #[]
  for h : i in [0:rules.size] do
    let r := rules[i]
    offsets := offsets.push total
    total := total + r.decls.size
    for h2 : j in [0:r.selectors.size] do
      let sel := r.selectors[j]
      match sel.key, sel.upKey with
      | some k, some u => byPair := byPair.insert (k, u) ((byPair.getD (k, u) #[]).push (i, j))
      | some k, none => byKey := byKey.insert k ((byKey.getD k #[]).push (i, j))
      | none, _ => universal := universal.push (i, j)
  return { rules, offsets, byKey, byPair, universal }

/-- The selectors an element below `up` can match: under its keys, under its keys and an
ancestor's, and the universal ones. -/
public def RuleIndex.candidates (ix : RuleIndex) (e : Subject) (up : List Subject) :
    Array (Nat × Nat) := Id.run do
  let keys := e.keys
  let mut out : Array (Nat × Nat) := keys.foldl (fun acc k => acc ++ ix.byKey.getD k #[]) #[]
  if !ix.byPair.isEmpty then
    let mut ups : Std.HashSet (Nat × String) := {}
    for a in up do
      for k in a.keys do ups := ups.insert k
    let upKeys := ups.toArray
    for k in keys do
      for u in upKeys do
        out := out ++ ix.byPair.getD (k, u) #[]
  return out ++ ix.universal

/-- A declaration's place in the cascade (CSS Cascading 4 §6.1): importance, level, specificity,
source order; the greater key wins. -/
public structure Key where
  important : Bool
  level : Nat
  spec : Nat × Nat × Nat
  order : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Lexicographic order on lists of naturals: the first differing entry
decides, and a proper prefix is below. -/
@[expose] public def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- A key's entries in the order the cascade reads them. -/
@[expose] public def Key.toList (k : Key) : List Nat :=
  [if k.important then 1 else 0, k.level, k.spec.1, k.spec.2.1, k.spec.2.2, k.order]

/-- The cascade's order on keys: lexicographic, importance first. -/
@[expose] public def Key.lt (a b : Key) : Bool := lexLt a.toList b.toList

/-- The best of the candidates onto the best so far; a candidate wins only with a greater key. -/
public def winnerList (best : Option (Key × String)) : List (Key × String) → Option (Key × String)
  | [] => best
  | c :: rest =>
    winnerList (match best with
      | none => some c
      | some b => if Key.lt b.1 c.1 then some c else some b) rest

/-- The cascaded value: the declaration whose key is greatest. -/
@[expose] public def cascade (cands : Array (Key × String)) : Option String :=
  (winnerList none cands.toList).map (·.2)

public theorem lexLt_irrefl : ∀ l : List Nat, lexLt l l = false
  | [] => rfl
  | a :: as => by simp [lexLt, lexLt_irrefl as]

public theorem lexLt_trans : ∀ a b c : List Nat,
    lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans xs ys zs h1 h2⟩

public theorem lexLt_not_trans : ∀ a b c : List Nat, a.length = b.length → b.length = c.length →
    lexLt a b = false → lexLt b c = false → lexLt a c = false
  | [], [], [], _, _, _, _ => rfl
  | [], [], _ :: _, _, h, _, _ => by simp at h
  | [], _ :: _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp at h
  | x :: xs, y :: ys, z :: zs, l1, l2, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at l1 l2
    simp only [lexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt,
      Bool.and_eq_false_imp, beq_iff_eq] at h1 h2 ⊢
    refine ⟨by omega, fun hxz => ?_⟩
    have hxy : x = y := by omega
    have hyz : y = z := by omega
    exact lexLt_not_trans xs ys zs l1 l2 (h1.2 hxy) (h2.2 hyz)

@[simp] public theorem Key.toList_length (k : Key) : k.toList.length = 6 := rfl

private def winnerStep (best : Option (Key × String)) (c : Key × String) : Option (Key × String) :=
  match best with
  | none => some c
  | some b => if Key.lt b.1 c.1 then some c else some b

private theorem winnerList_cons (best : Option (Key × String)) (c : Key × String)
    (rest : List (Key × String)) : winnerList best (c :: rest) = winnerList (winnerStep best c) rest := by
  cases best <;> rfl

private theorem winnerList_mem (best : Option (Key × String)) (cs : List (Key × String))
    (w : Key × String) (h : winnerList best cs = some w) : best = some w ∨ w ∈ cs := by
  induction cs generalizing best with
  | nil => exact Or.inl h
  | cons c rest ih =>
    rw [winnerList_cons] at h
    rcases ih _ h with hs | hm
    · cases best with
      | none => simp only [winnerStep, Option.some.injEq] at hs; subst hs; simp
      | some b =>
        simp only [winnerStep] at hs
        split at hs
        · simp only [Option.some.injEq] at hs; subst hs; simp
        · exact Or.inl hs
    · exact Or.inr (List.mem_cons_of_mem _ hm)

private theorem winnerList_max (best : Option (Key × String)) (cs : List (Key × String))
    (w : Key × String) (h : winnerList best cs = some w) :
    (∀ c ∈ cs, Key.lt w.1 c.1 = false) ∧ (∀ b, best = some b → Key.lt w.1 b.1 = false) := by
  induction cs generalizing best with
  | nil =>
    refine ⟨by simp, fun b hb => ?_⟩
    simp only [winnerList] at h
    rw [h] at hb
    cases hb
    exact lexLt_irrefl _
  | cons c rest ih =>
    rw [winnerList_cons] at h
    obtain ⟨hrest, hnext⟩ := ih _ h
    cases best with
    | none =>
      exact ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnext x rfl
        · exact hrest x hx, fun _ hb => by cases hb⟩
    | some b =>
      by_cases hlt : Key.lt b.1 c.1 = true
      · have hwc := hnext c (by simp [winnerStep, hlt])
        refine ⟨fun x hx => ?_, fun b' hb => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hwc
          · exact hrest x hx
        · cases hb
          cases hwb : Key.lt w.1 b.1
          · rfl
          · exact absurd (lexLt_trans _ _ _ hwb hlt) (by simp [Key.lt] at hwc ⊢; exact hwc)
      · have hlt' : Key.lt b.1 c.1 = false := by simpa using hlt
        have hwb := hnext b (by simp [winnerStep, hlt'])
        refine ⟨fun x hx => ?_, fun b' hb => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact lexLt_not_trans _ _ _ (by simp) (by simp) hwb hlt'
          · exact hrest x hx
        · cases hb; exact hwb

public theorem cascade_exact (cands : Array (Key × String)) (v : String) (h : cascade cands = some v) :
    ∃ k, (k, v) ∈ cands ∧ ∀ c ∈ cands, Key.lt k c.1 = false := by
  unfold cascade at h
  cases hw : winnerList none cands.toList with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨w.1, ?_, fun c hc => (winnerList_max none _ w hw).1 c (by simpa using hc)⟩
    rcases winnerList_mem none _ w hw with h0 | hm
    · cases h0
    · simpa using hm

private theorem flatten_intercalate (a : List Char) :
    ∀ segs : List (List (List Char)),
      ([a].intercalate segs).flatten = a.intercalate (segs.map List.flatten)
  | [] => by simp
  | [x] => by simp [List.intercalate_singleton]
  | x :: y :: rest => by
    rw [List.intercalate_cons_cons, List.map_cons, List.map_cons, List.intercalate_cons_cons,
      ← List.map_cons, ← flatten_intercalate a (y :: rest)]
    simp

private theorem atomsGo_flatten (acc : Array (List Char)) (st : Option (Char × Array Char))
    (l : List Char) :
    (atomsGo acc st l).toList.flatten =
      acc.toList.flatten ++ ((st.map (·.2.toList)).getD []) ++ l := by
  fun_induction atomsGo acc st l <;> simp_all

/-- Joined, the atoms of a text are the text. -/
private theorem atoms_flatten (s : String) : (atoms s).flatten = s.toList := by
  simp [atoms, atomsGo_flatten]

private theorem notEsc {c : Char} {rest : List Char} (h : c ≠ '\\' ∨ rest = []) :
    ∀ (c' : Char) (r : List Char), c = '\\' → rest = c' :: r → False := by
  intro c' r hc hr
  rcases h with h | h
  · exact h hc
  · simp [h] at hr

/-- String text after quote `q` that ends its string at its last character, whatever follows. -/
private def Ends (q : Char) (b : List Char) : Prop :=
  ∀ acc cur rest, atomsGo acc (some (q, cur)) (b ++ rest) =
    atomsGo (acc.push (cur.toList ++ b)) none rest

/-- String text after quote `q` that only the text's end ends. -/
private def Runs (q : Char) (b : List Char) : Prop :=
  ∀ acc cur, atomsGo acc (some (q, cur)) b = acc.push (cur.toList ++ b)

/-- A string's text either ends it at a closing quote or a line end, or runs to the text's end. -/
private theorem strRun (q : Char) (hq : q ≠ '\\') :
    ∀ l : List Char, (∃ b r, l = b ++ r ∧ Ends q b) ∨ Runs q l
  | [] => .inr fun acc cur => by simp [atomsGo.eq_4]
  | c :: rest =>
    if hc : c = '\\' then
      match rest with
      | [] => .inr fun acc cur => by
          subst hc
          rw [atomsGo.eq_6 _ _ _ _ _ (notEsc (.inr rfl))]
          have hne : ('\\' == q || isLineEnd '\\') = false := by
            simp only [isLineEnd, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
            exact ⟨fun h => hq h.symm, by decide⟩
          simp [hne, atomsGo.eq_4]
      | d :: r =>
        match strRun q hq r with
        | .inl ⟨b, r', hr, hb⟩ =>
          .inl ⟨'\\' :: d :: b, r', by simp [hc, hr], fun acc cur rest' => by
            simp only [List.cons_append]
            rw [atomsGo.eq_5, hb]
            simp⟩
        | .inr hr => .inr fun acc cur => by
            subst hc
            rw [atomsGo.eq_5, hr]
            simp
    else
      if hcl : (c == q || isLineEnd c) = true then
        .inl ⟨[c], rest, rfl, fun acc cur rest' => by
          rw [List.cons_append, List.nil_append, atomsGo.eq_6 _ _ _ _ _ (notEsc (.inl hc))]
          simp [hcl]⟩
      else
        match strRun q hq rest with
        | .inl ⟨b, r', hr, hb⟩ => .inl ⟨c :: b, r', by simp [hr], fun acc cur rest' => by
            rw [List.cons_append, atomsGo.eq_6 _ _ _ _ _ (notEsc (.inl hc))]
            simp only [hcl, Bool.false_eq_true, ↓reduceIte]
            rw [hb]
            simp⟩
        | .inr hr => .inr fun acc cur => by
            rw [atomsGo.eq_6 _ _ _ _ _ (notEsc (.inl hc))]
            simp only [hcl, Bool.false_eq_true, ↓reduceIte]
            rw [hr]
            simp

/-- An atom its own last character ends: an escape, a character standing alone, or a string the
reader closed. -/
private def Whole (a : List Char) : Prop :=
  (∃ x, a = ['\\', x]) ∨ (∃ c, a = [c] ∧ c ≠ '\\' ∧ c ≠ '"' ∧ c ≠ '\'') ∨
    (∃ q b, a = q :: b ∧ (q = '"' ∨ q = '\'') ∧ Ends q b)

/-- An atom only the text's end ends: a lone backslash, or a string still open. -/
private def Open (a : List Char) : Prop :=
  a = ['\\'] ∨ (∃ q b, a = q :: b ∧ (q = '"' ∨ q = '\'') ∧ Runs q b)

/-- Atoms as the reader makes them: each whole but the last, which may be open. -/
private def Made : List (List Char) → Prop
  | [] => True
  | [a] => Whole a ∨ Open a
  | a :: b :: rest => Whole a ∧ Made (b :: rest)

private theorem quote_ne {q : Char} (h : q = '"' ∨ q = '\'') : q ≠ '\\' := by
  rcases h with rfl | rfl <;> decide

private theorem whole_reads (acc : Array (List Char)) (a tail : List Char) (h : Whole a) :
    atomsGo acc none (a ++ tail) = atomsGo (acc.push a) none tail := by
  rcases h with ⟨x, rfl⟩ | ⟨c, rfl, hb, hd, hs⟩ | ⟨q, b, rfl, hq, hend⟩
  · simp [atomsGo.eq_2]
  · rw [List.cons_append, List.nil_append, atomsGo.eq_3 _ _ _ (notEsc (.inl hb))]
    simp [hd, hs]
  · rw [List.cons_append, atomsGo.eq_3 _ _ _ (notEsc (.inl (quote_ne hq)))]
    have hq' : (q == '"' || q == '\'') = true := by rcases hq with rfl | rfl <;> rfl
    simp only [hq', ↓reduceIte]
    rw [hend]
    simp

private theorem open_reads (acc : Array (List Char)) (a : List Char) (h : Open a) :
    atomsGo acc none a = acc.push a := by
  rcases h with rfl | ⟨q, b, rfl, hq, hruns⟩
  · rw [atomsGo.eq_3 _ _ _ (notEsc (.inr rfl))]
    simp [atomsGo.eq_1]
  · rw [atomsGo.eq_3 _ _ _ (notEsc (.inl (quote_ne hq)))]
    have hq' : (q == '"' || q == '\'') = true := by rcases hq with rfl | rfl <;> rfl
    simp only [hq', ↓reduceIte]
    rw [hruns]
    simp

/-- Atoms as the reader makes them read back as themselves. -/
private theorem made_reads (acc : Array (List Char)) :
    ∀ L : List (List Char), Made L → atomsGo acc none L.flatten = acc ++ L.toArray
  | [], _ => by simp [atomsGo.eq_1]
  | [a], h => by
    rcases h with hw | ho
    · simpa [atomsGo.eq_1] using whole_reads acc a [] hw
    · simpa using open_reads acc a ho
  | a :: b :: rest, h => by
    obtain ⟨hw, hrest⟩ := h
    rw [List.flatten_cons, whole_reads acc a _ hw, made_reads (acc.push a) (b :: rest) hrest]
    simp

private theorem made_cons (a : List Char) (L : List (List Char)) (ha : Whole a) (h : Made L) :
    Made (a :: L) := by
  cases L with
  | nil => exact .inl ha
  | cons b rest => exact ⟨ha, h⟩

private theorem made_append :
    ∀ A L : List (List Char), (∀ a ∈ A, Whole a) → Made L → Made (A ++ L)
  | [], _, _, h => h
  | a :: A, L, hA, h =>
    made_cons a (A ++ L) (hA a (by simp)) (made_append A L (fun x hx => hA x (by simp [hx])) h)

/-- The reader's atoms are as it makes them. -/
private theorem atomsGo_made (l : List Char) (acc : Array (List Char))
    (hacc : ∀ a ∈ acc.toList, Whole a) : Made (atomsGo acc none l).toList := by
  match l with
  | [] =>
    rw [atomsGo.eq_1]
    simpa using made_append acc.toList [] hacc trivial
  | c :: rest =>
    if hc : c = '\\' then
      subst hc
      match rest with
      | [] =>
        rw [atomsGo.eq_3 _ _ _ (notEsc (.inr rfl))]
        simp only [show ('\\' == '"' || '\\' == '\'') = false by decide, Bool.false_eq_true,
          ↓reduceIte, atomsGo.eq_1, Array.toList_push]
        exact made_append acc.toList [['\\']] hacc (.inr (.inl rfl))
      | d :: r =>
        rw [atomsGo.eq_2]
        exact atomsGo_made r _ (by
          intro a ha
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact hacc a ha
          · exact .inl ⟨d, rfl⟩)
    else
      rw [atomsGo.eq_3 _ _ _ (notEsc (.inl hc))]
      if hq : (c == '"' || c == '\'') = true then
        simp only [hq, ↓reduceIte]
        have hq2 : c = '"' ∨ c = '\'' := by simpa using hq
        rcases strRun c (quote_ne hq2) rest with ⟨b, r, rfl, hb⟩ | hruns
        · rw [hb]
          exact atomsGo_made r _ (by
            intro a ha
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
            rcases ha with ha | rfl
            · exact hacc a ha
            · exact .inr (.inr ⟨c, b, by simp, hq2, hb⟩))
        · rw [hruns]
          simpa using made_append acc.toList [[c] ++ rest] hacc
            (.inr (.inr ⟨c, rest, by simp, hq2, hruns⟩))
      else
        simp only [hq, Bool.false_eq_true, ↓reduceIte]
        have hq2 : c ≠ '"' ∧ c ≠ '\'' := by simpa using hq
        exact atomsGo_made rest _ (by
          intro a ha
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | rfl
          · exact hacc a ha
          · exact .inr (.inl ⟨c, rfl, hc, hq2.1, hq2.2⟩))
termination_by l.length
decreasing_by all_goals simp_all <;> omega

private theorem made_prefix : ∀ l1 l2 : List (List Char), Made (l1 ++ l2) → Made l1
  | [], _, _ => trivial
  | [a], l2, h => by
    cases l2 with
    | nil => simpa using h
    | cons b r => exact .inl h.1
  | a :: b :: l1, l2, h => ⟨h.1, made_prefix (b :: l1) l2 h.2⟩

private theorem made_suffix : ∀ l1 l2 : List (List Char), Made (l1 ++ l2) → Made l2
  | [], _, h => h
  | a :: l1, l2, h => by
    apply made_suffix l1 l2
    rw [List.cons_append] at h
    cases hl : (l1 ++ l2) with
    | nil => trivial
    | cons b r =>
      rw [hl] at h
      exact h.2

private theorem made_intercalate (sep : List (List Char)) :
    ∀ L : List (List (List Char)), Made (sep.intercalate L) → ∀ p ∈ L, Made p
  | [], _ => by simp
  | [p], h => by simpa [List.intercalate_singleton] using h
  | p :: q :: rest, h => by
    rw [List.intercalate_cons_cons, List.append_assoc] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact made_prefix _ _ h
    · have h' := made_suffix _ _ (made_suffix _ _ h)
      exact made_intercalate sep (q :: rest) h' x (by simpa using hx)

private theorem foldl_push (a : List Char) (t : String) :
    (a.foldl String.push t).toList = t.toList ++ a := by
  induction a generalizing t with
  | nil => simp
  | cons c rest ih => simp [ih, String.toList_push]

private theorem pieceText_eq (piece : Array (List Char)) :
    pieceText piece = String.ofList (piece.toList.flatMap id) := by
  apply String.toList_inj.mp
  have h : ∀ (l : List (List Char)) (t : String),
      (l.foldl (fun t a => a.foldl String.push t) t).toList = t.toList ++ l.flatten := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih => intro t; simp [ih, foldl_push]
  simp [pieceText, ← Array.foldl_toList, h]

/-- Joined at `sep`, the pieces `splitList` cuts are the text it cut. -/
public theorem splitList_join_id (sep : Char) (s : String) :
    [sep].intercalate ((splitList sep s).toList.map String.toList) = s.toList := by
  have h := KeyVal.splitTopAt_join_id opensBlock closesBlock [sep] (atoms s)
  have hf := congrArg List.flatten h
  rw [flatten_intercalate, atoms_flatten] at hf
  simp only [splitList, pieceText_eq, Array.toList_map, List.map_map, Function.comp_def,
    String.toList_ofList, List.flatMap_id]
  simpa [List.map_map, Function.comp_def] using hf

/-- A piece `splitList` cuts holds no `sep` outside blocks, strings and escapes: cut again, it is
itself. -/
public theorem splitList_fixed_point (sep : Char) (s : String) :
    ∀ p ∈ (splitList sep s).toList, splitList sep p = #[p] := by
  intro p hp
  simp only [splitList, pieceText_eq, Array.toList_map, List.mem_map] at hp
  obtain ⟨piece, hpiece, rfl⟩ := hp
  have hjoin := KeyVal.splitTopAt_join_id opensBlock closesBlock [sep] (atoms s)
  have hmade : Made piece.toList := by
    refine made_intercalate [[sep]] _ ?_ piece.toList (List.mem_map_of_mem hpiece)
    rw [hjoin]
    exact atomsGo_made s.toList #[] (by simp)
  have hre : atoms (String.ofList (piece.toList.flatMap id)) = piece.toList := by
    simp only [atoms, String.toList_ofList, List.flatMap_id]
    rw [made_reads #[] piece.toList hmade]
    simp
  simp only [splitList, hre]
  rw [KeyVal.splitTopAt_fixed_point _ _ _ _ piece hpiece]
  simp [pieceText_eq]

end LeanTex.Core.Css
