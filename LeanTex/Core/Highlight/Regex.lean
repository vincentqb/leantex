module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.Hex

/-! Python `re` patterns as the generator exports a table lexer's (pygments/lexer.py; BSD-licensed:
testdata/highlight/LICENSE-Pygments): parsed by Python's own `re` parser into postfix codes, and
matched here by backtracking in `re`'s priority order. -/
namespace LeanTex.Core.Highlight.Regex

/-- One member of a character set. -/
public inductive Member where
  | char (c : Char)
  | range (lo hi : Char)
  | word
  | notWord
  | digit
  | notDigit
  | space
  | notSpace
  deriving Repr, BEq, Inhabited

public def Member.holds (c : Char) : Member → Bool
  | .char d => c == d
  | .range lo hi => lo ≤ c && c ≤ hi
  | .word => wordChar c
  | .notWord => !wordChar c
  | .digit => digitChar c
  | .notDigit => !digitChar c
  | .space => spaceChar c
  | .notSpace => !spaceChar c

/-- A pattern: `alt` tries its left branch first, a greedy repeat one more iteration first and a
lazy one the rest of the pattern first. -/
public inductive Node where
  | empty
  | str (cs : Array Char)
  | notChar (c : Char)
  | set (neg : Bool) (ms : Array Member)
  /-- `.`, a line feed too where `newline`. -/
  | any (newline : Bool)
  /-- `^` under `re.MULTILINE`. -/
  | lineStart
  /-- `$` under `re.MULTILINE`. -/
  | lineEnd
  /-- `\A`. -/
  | textStart
  /-- `\Z`. -/
  | textEnd
  /-- `$` without `re.MULTILINE`: the end, or before a line feed ending the text. -/
  | finalEnd
  /-- `\b` where `holds`, else `\B`. -/
  | boundary (holds : Bool)
  | cat (a b : Node)
  | alt (a b : Node)
  | group (i : Nat) (body : Node)
  | star (body : Node) (greedy : Bool)
  /-- A star of a body that reads exactly one scalar and captures nothing, matched without
  recursing per scalar. -/
  | run (body : Node) (greedy : Bool)
  /-- A lookahead, else a lookbehind of `width` scalars; `neg` for the negative forms. -/
  | look (ahead neg : Bool) (width : Nat) (body : Node)
  | backref (i : Nat)
  deriving Repr, Inhabited

/-- Each group's span, by its number. -/
public abbrev Caps := Array (Option (Nat × Nat))

/-- A match's end and its groups. -/
public abbrev Res := Nat × Caps

/-- Whether the `n` scalars at `i` repeat the ones at `a`. -/
private def same (s : Src) (i a n : Nat) : Bool := Id.run do
  if i + n > s.size then return false
  for k in [0:n] do
    if s.chars[i + k]? != s.chars[a + k]? then return false
  return true

/-- The first way `r` matches at `i` whose continuation `k` succeeds. -/
public def go (s : Src) (r : Node) (i : Nat) (caps : Caps) (k : Nat → Caps → Option Res) :
    Option Res :=
  match r with
  | .empty => k i caps
  | .str cs => if s.lit i cs then k (i + cs.size) caps else none
  | .notChar c => if s.sat i (· != c) then k (i + 1) caps else none
  | .set neg ms => if s.sat i (fun c => ms.any (·.holds c) != neg) then k (i + 1) caps else none
  | .any nl => if s.sat i (fun c => nl || c != '\n') then k (i + 1) caps else none
  | .lineStart => if s.lineStart i then k i caps else none
  | .lineEnd => if i ≥ s.size || s.is i '\n' then k i caps else none
  | .textStart => if i == 0 then k i caps else none
  | .textEnd => if i ≥ s.size then k i caps else none
  | .finalEnd => if i ≥ s.size || (i + 1 == s.size && s.is i '\n') then k i caps else none
  | .boundary b => if s.boundary i == b then k i caps else none
  | .cat a b => go s a i caps fun j c => go s b j c k
  | .alt a b =>
    match go s a i caps k with
    | some x => some x
    | none => go s b i caps k
  | .group g body => go s body i caps fun j c => k j (c.setIfInBounds g (some (i, j)))
  | .star body greedy =>
    let again : Nat → Caps → Option Res := fun j c =>
      if _h : i < j ∧ j ≤ s.size then go s (.star body greedy) j c k else k j c
    if greedy then
      match go s body i caps again with
      | some x => some x
      | none => k i caps
    else
      match k i caps with
      | some x => some x
      | none => go s body i caps again
  | .run body greedy => Id.run do
    let reads (p : Nat) : Bool :=
      (go s body p caps fun j _ => if j == p + 1 then some (j, caps) else none).isSome
    if greedy then
      let mut stop := s.size
      for p in [i:s.size] do
        if !reads p then
          stop := p
          break
      for d in [0:stop + 1 - i] do
        if let some x := k (stop - d) caps then return some x
      return none
    else
      for p in [i:s.size + 1] do
        if let some x := k p caps then return some x
        if !reads p then return none
      return none
  | .look true neg _ body =>
    match (go s body i caps fun _ c => some (i, c)), neg with
    | some (_, c), false => k i c
    | none, true => k i caps
    | _, _ => none
  | .look false neg w body =>
    let hit := if w ≤ i then go s body (i - w) caps fun j c => if j == i then some (j, c) else none
      else none
    match hit, neg with
    | some (_, c), false => k i c
    | none, true => k i caps
    | _, _ => none
  | .backref g =>
    match caps[g]? with
    | some (some (a, b)) => if same s i a (b - a) then k (i + (b - a)) caps else none
    | _ => none
termination_by (sizeOf r, s.size + 1 - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

/-- What the first scalar a node reads must satisfy, `none` where it may read none first or the
node reads no scalar by a class. -/
private def firstTest : Node → Option (Char → Bool)
  | .str cs => cs[0]?.map fun c => (· == c)
  | .notChar c => some (· != c)
  | .set neg ms => some fun c => ms.any (·.holds c) != neg
  | .any nl => some fun c => nl || c != '\n'
  | .cat a b =>
    match firstTest a with
    | some p => some p
    | none => if transparent a then firstTest b else none
  | .alt a b => do
    let p ← firstTest a
    let q ← firstTest b
    some fun c => p c || q c
  | .group _ body => firstTest body
  | .empty | .lineStart | .lineEnd | .textStart | .textEnd | .finalEnd | .boundary _ | .star ..
  | .run .. | .look .. | .backref _ => none
where
  /-- Whether a node reads nothing, whatever it asserts. -/
  transparent : Node → Bool
    | .empty | .lineStart | .lineEnd | .textStart | .textEnd | .finalEnd | .boundary _ | .look .. =>
      true
    | .cat a b => transparent a && transparent b
    | .str cs => cs.isEmpty
    | .notChar _ | .set .. | .any _ | .alt .. | .group .. | .star .. | .run .. | .backref _ => false

/-- A pattern, its group count, and what the first scalar of any match must satisfy where every
match reads one. -/
public structure Pattern where
  node : Node
  groups : Nat
  first : Option (Char → Bool)
  deriving Inhabited

/-- Where `re.match` ends a match of the pattern at `i`, and its groups. -/
public def Pattern.matchAt (p : Pattern) (s : Src) (i : Nat) : Option Res :=
  if p.first.all (s.sat i ·) then
    go s p.node i (Array.replicate (p.groups + 1) none) fun j c => some (j, c)
  else none

/-! ## Decoding -/

/-- Whether a node captures nothing. -/
private def captureFree : Node → Bool
  | .group .. | .backref _ => false
  | .cat a b | .alt a b => captureFree a && captureFree b
  | .star b _ | .run b _ | .look _ _ _ b => captureFree b
  | .empty | .str _ | .notChar _ | .set .. | .any _ | .lineStart | .lineEnd | .textStart
  | .textEnd | .finalEnd | .boundary _ => true

/-- Whether a node reads no scalar. -/
private def zeroWidth : Node → Bool
  | .empty | .lineStart | .lineEnd | .textStart | .textEnd | .finalEnd | .boundary _ => true
  | .look _ _ _ b => captureFree b
  | .cat a b | .alt a b => zeroWidth a && zeroWidth b
  | .str cs => cs.isEmpty
  | .notChar _ | .set .. | .any _ | .group .. | .star .. | .run .. | .backref _ => false

/-- Whether a node reads exactly one scalar and captures nothing. -/
private def oneScalar : Node → Bool
  | .str cs => cs.size == 1
  | .notChar _ | .set .. | .any _ => true
  | .cat a b => (oneScalar a && zeroWidth b) || (zeroWidth a && oneScalar b)
  | .alt a b => oneScalar a && oneScalar b
  | .empty | .lineStart | .lineEnd | .textStart | .textEnd | .finalEnd | .boundary _ | .group ..
  | .star .. | .run .. | .look .. | .backref _ => false

private def starOf (body : Node) (greedy : Bool) : Node :=
  if oneScalar body then .run body greedy else .star body greedy

/-- The largest count a repeat's bounds may spell, beyond which a pattern does not decode. -/
private def repeatBound : Nat := 64

/-- `body{lo,hi}`, `hi` absent for no bound, as concatenations, nested options and a star. -/
private def repeatOf (body : Node) (lo : Nat) (hi : Option Nat) (greedy : Bool) : Node :=
  let opt (n : Node) : Node := if greedy then .alt (.cat body n) .empty else .alt .empty (.cat body n)
  let tail := match hi with
    | none => starOf body greedy
    | some h => (List.range (h - lo)).foldl (fun n _ => opt n) .empty
  (List.range lo).foldr (fun _ n => .cat body n) tail

private def hexChar? (s : String) : Option Char :=
  (Hex.value? s.toList).bind fun v => if v < 0x110000 then some (Char.ofNat v) else none

private def member? (s : String) : Option Member :=
  match s with
  | "w" => some .word
  | "W" => some .notWord
  | "d" => some .digit
  | "D" => some .notDigit
  | "s" => some .space
  | "S" => some .notSpace
  | _ =>
    match s.splitOn "-" with
    | [c] => (hexChar? c).map .char
    | [a, b] => do some (.range (← hexChar? a) (← hexChar? b))
    | _ => none

private def bounds? (s : String) : Option (Nat × Option Nat) :=
  match s.splitOn ":" with
  | [a, "-"] => a.toNat?.map (·, none)
  | [a, b] => do some (← a.toNat?, some (← b.toNat?))
  | _ => none

/-- One postfix code applied to the stack of nodes decoded so far. -/
private def step (stack : List Node) (t : String) : Option (List Node) :=
  let rest := (t.drop 1).toString
  let push (n : Node) : Option (List Node) := some (n :: stack)
  let unary (f : Node → Option Node) : Option (List Node) :=
    match stack with
    | a :: more => (f a).map (· :: more)
    | [] => none
  let binary (f : Node → Node → Node) : Option (List Node) :=
    match stack with
    | b :: a :: more => some (f a b :: more)
    | _ => none
  match t.front with
  | 'c' => (hexChar? rest).bind fun c => push (.str #[c])
  | 'l' => ((rest.splitOn ".").mapM hexChar?).bind fun cs => push (.str cs.toArray)
  | 'n' => (hexChar? rest).bind fun c => push (.notChar c)
  | '.' => push (.any false)
  | ',' => push (.any true)
  | '[' =>
    let neg := rest.startsWith "^"
    let body := if neg then (rest.drop 1).toString else rest
    (((if body.isEmpty then [] else body.splitOn ",").mapM member?)).bind fun ms =>
      push (.set neg ms.toArray)
  | '^' => push .lineStart
  | '$' => push .lineEnd
  | 'A' => push .textStart
  | 'Z' => push .textEnd
  | 'z' => push .finalEnd
  | 'b' => push (.boundary true)
  | 'B' => push (.boundary false)
  | 'e' => push .empty
  | '+' => binary .cat
  | '|' => binary .alt
  | 'g' => rest.toNat?.bind fun g => unary fun a => some (.group g a)
  | '*' | '?' => (bounds? rest).bind fun (lo, hi) =>
    let over := match hi with
      | some h => decide (h > repeatBound) || decide (h < lo)
      | none => false
    if decide (lo > repeatBound) || over then none
    else unary fun a => some (repeatOf a lo hi (t.front == '*'))
  | '>' => unary fun a => some (.look true false 0 a)
  | '!' => unary fun a => some (.look true true 0 a)
  | '<' => rest.toNat?.bind fun w => unary fun a => some (.look false false w a)
  | '~' => rest.toNat?.bind fun w => unary fun a => some (.look false true w a)
  | 'r' => rest.toNat?.bind fun g => push (.backref g)
  | _ => none

/-- A pattern from its postfix codes, one space between each; `none` unless they leave one node. -/
public def decode? (code : String) (groups : Nat) : Option Pattern :=
  match (code.splitOn " ").foldlM step [] with
  | some [n] => some ⟨n, groups, firstTest n⟩
  | _ => none

end LeanTex.Core.Highlight.Regex
