module

public import LeanTex.Core.CaseFold

public section

namespace LeanTex.Core.Jtex

/-! The jtex template language MyST's LaTeX templates are written in: nunjucks 3.2.4 under jtex's
configuration (blocks `[# #]`, variables `[- -]`, comments `%# #%`, `trimBlocks`, no escaping, the
`len` filter), over the subset the templates use, refusing what lies outside it. -/

/-- A template value, as the JSON nunjucks reads, with JavaScript's undefined for what a lookup
misses and a typed splice standing for content the caller sets. -/
inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (items : List Value)
  | obj (fields : List (String × Value))
  | splice (name : String)
  deriving Repr, Inhabited, BEq

/-- A text's length in UTF-16 units, as JavaScript counts it. -/
def utf16Len (s : String) : Nat :=
  s.foldl (fun n c => n + if c.val > 0xFFFF then 2 else 1) 0

/-- A value's member `key` as JavaScript reads it: an object's field, an array's or a text's item
or `length`, undefined otherwise. -/
def Value.get (v : Value) (key : String) : Value :=
  match v, key.toNat? with
  | .obj fields, _ => ((fields.find? (·.1 == key)).map (·.2)).getD .undef
  | .arr items, some i => items.getD i .undef
  | .arr items, none => if key == "length" then .num items.length else .undef
  | .str s, some i => match s.toList[i]? with
    | some c => .str c.toString
    | none => .undef
  | .str s, none => if key == "length" then .num (utf16Len s) else .undef
  | _, _ => .undef

/-- JavaScript's truthiness, which nunjucks's `if` reads: an empty array or object is true. -/
def Value.truthy : Value → Bool
  | .undef | .null => false
  | .bool b => b
  | .num n => n != 0
  | .str s => !s.isEmpty
  | .arr _ | .obj _ | .splice _ => true

mutual

/-- A value as JavaScript's `String` prints it, nunjucks printing undefined and null as nothing. -/
def Value.show : Value → String
  | .undef | .null => ""
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => s
  | .arr items => Value.showList "" items
  | .obj _ => "[object Object]"
  | .splice _ => ""

/-- The items printed after `acc`, a comma after each but the last. -/
def Value.showList (acc : String) : List Value → String
  | [] => acc
  | v :: rest => Value.showList (acc ++ v.show ++ (if rest.isEmpty then "" else ",")) rest

end

/-- The characters JavaScript's `\s` and `trim` read as white space. -/
def jsSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' ||
    c.val == 0xA0 || c.val == 0x1680 || (0x2000 ≤ c.val && c.val ≤ 0x200A) || c.val == 0x2028 ||
    c.val == 0x2029 || c.val == 0x202F || c.val == 0x205F || c.val == 0x3000 || c.val == 0xFEFF

/-- A text as JavaScript's `Number` reads it over integers, none for NaN or a fraction. -/
def numberOf (s : String) : Option Int :=
  let t := ((s.dropWhile jsSpace).copy.dropEndWhile jsSpace).copy
  if t.isEmpty then some 0 else
  let (neg, body) := if t.startsWith "-" then (true, (t.drop 1).copy)
    else if t.startsWith "+" then (false, (t.drop 1).copy) else (false, t)
  if body.isEmpty || !body.all Char.isDigit then none else
    body.toNat?.map fun n => if neg then -(n : Int) else n

/-- A value as JavaScript's `ToPrimitive` leaves it: an array or object as its text. -/
def Value.prim : Value → Value
  | .arr items => .str (Value.showList "" items)
  | .obj _ => .str "[object Object]"
  | .undef => .undef
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
  | .splice n => .splice n

/-- A primitive as JavaScript's `ToNumber` reads it, none for NaN. -/
def Value.number : Value → Option Int
  | .null => some 0
  | .bool b => some (if b then 1 else 0)
  | .num n => some n
  | .str s => numberOf s
  | _ => none

/-- JavaScript's loose equality: undefined and null alike, booleans as numbers, an array or object
against a primitive as its text, a text against a number as its number, two arrays or objects never. -/
def Value.looseEq (a b : Value) : Bool :=
  let nullish (v : Value) := v matches .undef | .null
  if nullish a || nullish b then nullish a && nullish b else
  let objy (v : Value) := v matches .arr _ | .obj _ | .splice _
  if objy a && objy b then false else
  let num (v : Value) : Value := if let .bool x := v then .num (if x then 1 else 0) else v
  match num a.prim, num b.prim with
  | .num m, .num n => m == n
  | .str s, .str t => s == t
  | .num m, .str t => numberOf t == some m
  | .str s, .num n => numberOf s == some n
  | _, _ => false

/-- JavaScript's relational comparison: two texts by their characters, else both as numbers, NaN
answering false; `f` reads the sign of the first's difference from the second. -/
def Value.compare (a b : Value) (f : Int → Bool) : Bool :=
  match a.prim, b.prim with
  | .str s, .str t => f (if s < t then -1 else if s == t then 0 else 1)
  | x, y => match x.number, y.number with
    | some m, some n => f (m - n)
    | _, _ => false

/-- A filter's argument: a literal or a variable's path. -/
inductive Arg where
  | lit (v : Value)
  | path (p : List String)
  deriving Repr, Inhabited, BEq

/-- A comparison operator. -/
inductive Cmp where
  | eq | ne | lt | gt | le | ge
  deriving Repr, Inhabited, BEq

/-- An expression of the subset: a literal, a variable's path, `not`, `and`, `or`, a comparison and a
filter applied with literal or path arguments. -/
inductive Expr where
  | lit (v : Value)
  | path (p : List String)
  | not (e : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | cmp (op : Cmp) (a b : Expr)
  | filter (e : Expr) (name : String) (args : List Arg)
  deriving Repr, Inhabited, BEq

/-- A template node: text, a printed expression, an `if` chain, a `for` loop over a sequence, and a
`set`. -/
inductive Node where
  | text (s : String)
  | out (e : Expr)
  | cond (branches : List (Expr × List Node)) (otherwise : List Node)
  | loop (var : String) (seq : Expr) (body : List Node) (otherwise : List Node)
  | set (var : String) (e : Expr)
  deriving Repr, Inhabited

/-- One piece of a rendered template: the template's own text, a value the document chose, or the
content a splice value names. -/
inductive Piece where
  | text (s : String)
  | value (s : String)
  | splice (name : String)
  deriving Repr, Inhabited, BEq

/-- A token of a template: text, a block tag's or a variable's inner source with whether a `-`
strips the whitespace before it and after it, and a comment with its two strips. -/
inductive Tok where
  | data (s : String)
  | block (src : String) (lstrip rstrip : Bool)
  | var (src : String) (lstrip rstrip : Bool)
  | comment (lstrip rstrip : Bool)
  deriving Repr, Inhabited, BEq

/-- Whether `pat` stands in `cs` at `i`. -/
private def at? (cs : Array Char) (i : Nat) (pat : String) : Bool :=
  pat.toList.zipIdx.all fun (c, k) => cs[i + k]? == some c

/-- The index of the first `pat` at or past `i`, outside a quoted string where `code`. -/
private def findTag (cs : Array Char) (i : Nat) (pat : String) (code : Bool) : Option Nat := Id.run do
  let mut quote : Option Char := none
  let mut k := i
  for _ in [i:cs.size] do
    if k ≥ cs.size then break
    let c := cs.getD k ' '
    match quote with
    | some q =>
      if c == '\\' then k := k + 2; continue
      if c == q then quote := none
    | none =>
      if code && (c == '"' || c == '\'') then quote := some c
      else if at? cs k pat then return some k
    k := k + 1
  return none

/-- A template's tokens under jtex's tags: `[# #]` blocks, `[- -]` variables, `%# #%` comments, a
`-` beside a tag stripping the whitespace on its side, and `trimBlocks`' newline after a block tag
dropped; an unclosed tag or a comment's end in text is an error. -/
def lex (src : String) : Except String (Array Tok) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array Tok := #[]
  let mut buf := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if at? cs i "#%" then return .error s!"a comment's end with no comment open at character {i}"
    let opens := [("[#", 0), ("[-", 1), ("%#", 2)].find? fun (t, _) => at? cs i t
    match opens with
    | none => buf := buf.push (cs.getD i ' '); i := i + 1
    | some (t, kind) =>
      unless buf.isEmpty do out := out.push (.data buf)
      buf := ""
      let close := if kind == 0 then "#]" else if kind == 1 then "-]" else "#%"
      let start := i + 2
      let lstrip := cs[start]? == some '-' && !(kind == 1 && at? cs start "-]")
      let some e := findTag cs (if lstrip then start + 1 else start) close (kind != 2)
        | return .error s!"an unclosed '{t}' at character {i}"
      let rstrip := e > start && cs[e - 1]? == some '-' && kind != 1 || (kind == 1 && e > start + 1 &&
        cs[e - 1]? == some '-')
      let innerEnd := if rstrip then e - 1 else e
      let inner := String.ofList (cs.extract (if lstrip then start + 1 else start) innerEnd).toList
      out := out.push (match kind with
        | 0 => .block inner.trimAscii.toString lstrip rstrip
        | 1 => .var inner.trimAscii.toString lstrip rstrip
        | _ => .comment lstrip rstrip)
      i := e + 2
      -- trimBlocks: one newline after a block tag
      if kind == 0 then
        if cs[i]? == some '\n' then i := i + 1
        else if cs[i]? == some '\r' && cs[i + 1]? == some '\n' then i := i + 2
  unless buf.isEmpty do out := out.push (.data buf)
  return .ok out

/-- Whether a token strips the whitespace before it, and after it. -/
private def Tok.strips : Tok → Bool × Bool
  | .data _ => (false, false)
  | .block _ l r | .var _ l r | .comment l r => (l, r)

/-- The tokens with each text's whitespace, as JavaScript's `\s` reads it, stripped where the tag
before or after it asks. -/
def stripped (toks : Array Tok) : Array Tok :=
  toks.zipIdx.map fun (t, k) => match t with
    | .data s =>
      let before := k > 0 && (toks[k - 1]?.map (·.strips.2)).getD false
      let after := (toks[k + 1]?.map (·.strips.1)).getD false
      let s := if before then (s.dropWhile jsSpace).copy else s
      .data (if after then (s.dropEndWhile jsSpace).copy else s)
    | .block src l r => .block src l r
    | .var src l r => .var src l r
    | .comment l r => .comment l r

/-- A token of an expression: a name, a string or a number, or punctuation. -/
inductive ETok where
  | name (s : String)
  | str (s : String)
  | num (n : Int)
  | punct (s : String)
  deriving Repr, Inhabited, BEq

/-- An expression's tokens, a string's `\n`, `\t` and `\r` read as nunjucks reads them and any other
escaped character as itself; a character outside the subset is an error. -/
def elex (src : String) : Except String (Array ETok) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array ETok := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs.getD i ' '
    if jsSpace c then i := i + 1; continue
    if c.isAlpha || c == '_' then
      let mut j := i
      for _ in [i:cs.size] do
        let d := cs.getD j ' '
        if d.isAlphanum || d == '_' then j := j + 1 else break
      out := out.push (.name (String.ofList (cs.extract i j).toList))
      i := j
    else if c.isDigit then
      let mut j := i
      for _ in [i:cs.size] do
        if (cs.getD j ' ').isDigit then j := j + 1 else break
      if cs[j]? == some '.' && (cs[j + 1]?.any Char.isDigit) then
        return .error "a fractional number, outside the subset"
      out := out.push (.num ((String.ofList (cs.extract i j).toList).toNat?.getD 0))
      i := j
    else if c == '"' || c == '\'' then
      let mut j := i + 1
      let mut v := ""
      let mut closed := false
      for _ in [i:cs.size] do
        if j ≥ cs.size then break
        let d := cs.getD j ' '
        if d == '\\' then
          v := v.push (match cs.getD (j + 1) ' ' with
            | 'n' => '\n'
            | 't' => '\t'
            | 'r' => '\r'
            | e => e)
          j := j + 2
          continue
        if d == c then closed := true; j := j + 1; break
        v := v.push d
        j := j + 1
      unless closed do return .error "an unclosed string"
      out := out.push (.str v)
      i := j
    else
      let two := String.ofList [c, cs.getD (i + 1) ' ']
      if ["==", "!=", "<=", ">="].contains two then out := out.push (.punct two); i := i + 2
      else if "|.,()[]<>".toList.contains c then out := out.push (.punct (String.singleton c)); i := i + 1
      else return .error s!"an unread character '{c}'"
  return .ok out

/-- An operator awaiting its operands: a binary one with its precedence, `not`, or a parenthesis. -/
private inductive Op where
  | bin (name : String) (prec : Nat)
  | not
  | paren
  deriving BEq, Inhabited

private def Op.prec : Op → Nat
  | .bin _ p => p
  | .not => 6
  | .paren => 0

/-- The operands with `op` applied to the last of them; none where too few stand. -/
private def apply (vals : Array Expr) (op : Op) : Option (Array Expr) :=
  match op with
  | .not => vals.back?.map fun e => vals.pop.push (.not e)
  | .bin name _ =>
    match vals.back?, vals.pop.back? with
    | some b, some a =>
      let e : Option Expr := match name with
        | "and" => some (.and a b)
        | "or" => some (.or a b)
        | "==" => some (.cmp .eq a b)
        | "!=" => some (.cmp .ne a b)
        | "<" => some (.cmp .lt a b)
        | ">" => some (.cmp .gt a b)
        | "<=" => some (.cmp .le a b)
        | ">=" => some (.cmp .ge a b)
        | _ => none
      e.map fun e => vals.pop.pop.push e
    | _, _ => none
  | .paren => none

/-- The keywords nunjucks 3.2.4 reads as literals. -/
private def keyword : String → Option Value
  | "true" => some (.bool true)
  | "false" => some (.bool false)
  | "none" | "null" => some .null
  | _ => none

/-- A literal or a path where a filter's argument stands, and the index past it. -/
private def argAt (ts : Array ETok) (i : Nat) : Option (Arg × Nat) := Id.run do
  match ts[i]? with
  | some (.str s) => return some (.lit (.str s), i + 1)
  | some (.num n) => return some (.lit (.num n), i + 1)
  | some (.name n) =>
    if let some v := keyword n then return some (.lit v, i + 1)
    if n == "not" || n == "and" || n == "or" || n == "in" || n == "is" then return none
    let mut p := #[n]
    let mut j := i + 1
    for _ in [i:ts.size] do
      match ts[j]?, ts[j + 1]?, ts[j + 2]? with
      | some (.punct "."), some (.name m), _ => p := p.push m; j := j + 2
      | some (.punct "["), some (.str s), some (.punct "]") => p := p.push s; j := j + 3
      | some (.punct "["), some (.num m), some (.punct "]") => p := p.push (toString m); j := j + 3
      | _, _, _ => break
    return some (.path p.toList, j)
  | _ => return none

/-- An expression of the subset from its tokens, as the JavaScript nunjucks compiles it to binds:
`or` below `and` below equality below order below `not`, filters and paths binding tightest, `not`
only where an operand may start; none outside the subset. -/
def parseExpr (ts : Array ETok) : Option Expr := Id.run do
  let mut vals : Array Expr := #[]
  let mut ops : Array Op := #[]
  let mut i := 0
  -- whether an operand may stand next, rather than an operator
  let mut operand := true
  let binPrec : String → Option Nat
    | "or" => some 1
    | "and" => some 2
    | "==" | "!=" => some 4
    | "<" | ">" | "<=" | ">=" => some 5
    | _ => none
  for _ in [0:ts.size + 1] do
    if i ≥ ts.size then break
    let binary : Option String := match ts[i]? with
      | some (.name n) => if (binPrec n).isSome then some n else none
      | some (.punct o) => if (binPrec o).isSome then some o else none
      | _ => none
    if let some o := binary then
      if operand then return none
      let p := (binPrec o).getD 0
      for _ in [0:ops.size] do
        match ops.back? with
        | some op => if op != .paren && op.prec ≥ p then
                       let some v := apply vals op | return none
                       vals := v; ops := ops.pop
                     else break
        | none => break
      ops := ops.push (.bin o p); i := i + 1; operand := true
      continue
    match ts[i]? with
    | some (.name "not") =>
      -- nunjucks reads `not` only where a test starts: first, or after `(`, `and`, `or` or `not`
      let starts := i == 0 || [ETok.punct "(", .name "and", .name "or", .name "not"].contains (ts.getD (i - 1) (.punct ""))
      if !operand || !starts then return none
      ops := ops.push .not; i := i + 1
    | some (.punct "(") =>
      if !operand then return none
      ops := ops.push .paren; i := i + 1
    | some (.punct ")") =>
      if operand then return none
      for _ in [0:ops.size] do
        match ops.back? with
        | some .paren => break
        | some o => let some v := apply vals o | return none
                    vals := v; ops := ops.pop
        | none => return none
      unless ops.back? == some .paren do return none
      ops := ops.pop; i := i + 1
    | some (.punct "|") =>
      if operand then return none
      let some (.name f) := ts[i + 1]? | return none
      let mut args : Array Arg := #[]
      let mut k := i + 2
      if ts[k]? == some (.punct "(") then
        k := k + 1
        if ts[k]? == some (.punct ")") then k := k + 1 else
        for _ in [0:ts.size] do
          let some (a, j) := argAt ts k | return none
          args := args.push a
          match ts[j]? with
          | some (.punct ",") => k := j + 1
          | some (.punct ")") => k := j + 1; break
          | _ => return none
      let some e := vals.back? | return none
      vals := vals.pop.push (.filter e f args.toList); i := k
    | some _ =>
      if !operand then return none
      let some (a, j) := argAt ts i | return none
      vals := vals.push (match a with
        | .lit v => .lit v
        | .path p => .path p)
      i := j; operand := false
    | none => break
  if operand then return none
  for _ in [0:ops.size] do
    match ops.back? with
    | some o => let some v := apply vals o | return none
                vals := v; ops := ops.pop
    | none => break
  return if vals.size == 1 then vals[0]? else none

/-- A variable bound in a frame: its value, and whether it holds only the template's own text. -/
structure Binding where
  name : String
  value : Value
  own : Bool
  deriving Inhabited

/-- The variables in scope: nunjucks' frames, a loop's innermost first, over the template's context. -/
structure Scope where
  frames : List (List Binding) := [[]]
  context : Value := .obj []

/-- The binding a frame holds for `n`, innermost first. -/
def Scope.find? (sc : Scope) (n : String) : Option Binding :=
  sc.frames.findSome? fun f => f.find? (·.name == n)

/-- A path's value: its first name a frame's or the context's, each next name a member. -/
def Scope.lookup (sc : Scope) : List String → Value
  | [] => .undef
  | n :: rest =>
    let base := ((sc.find? n).map (·.value)).getD (sc.context.get n)
    rest.foldl Value.get base

/-- The scope with `name` bound in the innermost frame. -/
def Scope.bind (sc : Scope) (name : String) (v : Value) (own : Bool := false) : Scope :=
  match sc.frames with
  | f :: fs => { sc with frames := ({ name, value := v, own } :: f.filter (·.name != name)) :: fs }
  | [] => { sc with frames := [[{ name, value := v, own }]] }

/-- The scope after `set name`: the innermost frame holding `name` rebinds it, as nunjucks' write
resolves up, else the innermost frame binds it. -/
def Scope.assign (sc : Scope) (name : String) (v : Value) (own : Bool) : Scope :=
  if sc.frames.any (·.any (·.name == name)) then
    let rec go : List (List Binding) → List (List Binding)
      | [] => []
      | f :: fs => if f.any (·.name == name) then
          f.map (fun b => if b.name == name then { name, value := v, own } else b) :: fs
        else f :: go fs
    { sc with frames := go sc.frames }
  else sc.bind name v own

/-- An argument's value. -/
def Arg.eval (sc : Scope) : Arg → Value
  | .lit v => v
  | .path p => sc.lookup p

/-- A text in lower case as JavaScript's `toLowerCase` sets it: a character with an upper case
mapping is lower already, any other its single folded form, `İ` its two. -/
def lowerText (s : String) : String :=
  s.foldl (fun out c =>
    if CaseFold.upperChar c != #[c] then out.push c
    else if c == 'İ' then out ++ "i̇"
    else match CaseFold.foldChar c with
      | #[d] => out.push d
      | _ => out.push c) ""

/-- A filter of the subset applied, as nunjucks 3.2.4 applies it: `join` with its separator and an
item's attribute, `length`, jtex's `len`, `first`, `lower` and `upper`; the reason where nunjucks
throws or the filter is outside the subset. -/
def filterApply (name : String) (v : Value) (args : List Value) : Except String Value :=
  let text (v : Value) : Option String := match v with
    | .undef | .null | .bool false => some ""
    | .str s => some s
    | _ => none
  match name, v with
  | "join", .arr items =>
    let sep := match args.head? with
      | some (.undef) | none => ""
      | some s => s.prim.show
    let items := match args[1]? with
      | some attr => if attr.truthy then items.map fun (x : Value) => x.get attr.prim.show else items
      | none => items
    .ok (.str (sep.intercalate (items.map fun (x : Value) => x.show)))
  | "join", _ => .error "join over no array"
  | "length", .arr items => .ok (.num items.length)
  | "length", .str s => .ok (.num (utf16Len s))
  | "length", .obj fs => .ok (.num fs.length)
  | "length", .undef | "length", .null | "length", .bool false => .ok (.num 0)
  | "length", _ => .ok .undef
  | "len", .arr items => .ok (.num items.length)
  | "len", .str s => .ok (.num (utf16Len s))
  | "len", .undef | "len", .null => .error "len of no value"
  | "len", _ => .ok .undef
  | "first", .arr items => .ok (items.head?.getD .undef)
  | "first", .str s => .ok (match s.toList.head? with
    | some c => .str c.toString
    | none => .undef)
  | "first", .undef | "first", .null => .error "first of no value"
  | "first", _ => .ok .undef
  | "lower", v => match text v with
    | some s => .ok (.str (lowerText s))
    | none => .error "lower of no text"
  | "upper", v => match text v with
    | some s => .ok (.str (CaseFold.upper s))
    | none => .error "upper of no text"
  | n, _ => .error s!"the filter '{n}', outside the subset"

/-- An expression's value; what nunjucks throws on is an error. -/
def Expr.eval (sc : Scope) : Expr → Except String Value
  | .lit v => .ok v
  | .path p => .ok (sc.lookup p)
  | .not e => do return .bool !(← e.eval sc).truthy
  | .and a b => do
    let x ← a.eval sc
    if !x.truthy then return x else b.eval sc
  | .or a b => do
    let x ← a.eval sc
    if x.truthy then return x else b.eval sc
  | .cmp op a b => do
    let x ← a.eval sc
    let y ← b.eval sc
    return .bool (match op with
      | .eq => x.looseEq y
      | .ne => !x.looseEq y
      | .lt => x.compare y (· < 0)
      | .gt => x.compare y (· > 0)
      | .le => x.compare y (· ≤ 0)
      | .ge => x.compare y (· ≥ 0))
  | .filter e name args => do
    filterApply name (← e.eval sc) (args.map (·.eval sc))

/-- A value printed after `out`: a splice as itself, an array its items apart by commas, nothing for
undefined or null, any other as a value the document chose. -/
def piecesInto (out : Array Piece) (v : Value) : Array Piece :=
  match v with
  | .splice n => out.push (.splice n)
  | .arr items => items.attach.zipIdx.foldl (init := out) fun out (⟨x, _⟩, k) =>
      piecesInto (if k == 0 then out else out.push (.text ",")) x
  | .undef | .null => out
  | .bool _ | .num _ | .str _ | .obj _ => out.push (.value v.show)
decreasing_by
  rename_i h
  have := List.sizeOf_lt_of_mem h
  simp_all
  omega

/-- Whether an expression holds only the template's own text: a string literal, or a variable a
`set` bound to one. -/
def Expr.own (sc : Scope) : Expr → Bool
  | .lit (.str _) => true
  | .path [n] => (sc.find? n).any (·.own)
  | _ => false

/-- A printed expression's pieces: the template's own text as text, a join's items each as printed
with its separator the template's where it writes it, and any other value by `piecesInto`. -/
def printed (sc : Scope) (e : Expr) : Except String (Array Piece) := do
  if e.own sc then return #[.text (← e.eval sc).show]
  match e with
  | .filter inner "join" args =>
    match ← inner.eval sc with
    | .arr items =>
      let vals := args.map (·.eval sc)
      let sep : Array Piece := match args.head?, vals.head? with
        | some (.lit (.str s)), _ => #[.text s]
        | _, some Value.undef => #[]
        | _, none => #[]
        | _, some s => #[.value s.prim.show]
      let items := match vals[1]? with
        | some attr => if attr.truthy then items.map fun (x : Value) => x.get attr.prim.show else items
        | none => items
      return items.zipIdx.foldl (init := #[]) fun out (x, k) =>
        piecesInto (if k == 0 then out else out.append sep) x
    | _ => throw "join over no array"
  | _ => return piecesInto #[] (← e.eval sc)

/-- A statement tag's words: its keyword and the rest of its source. -/
private def tagWords (src : String) : String × String :=
  let t := src.trimAscii.toString
  let kw := (t.takeWhile fun c => !c.isWhitespace).toString
  (kw, (t.drop kw.length).toString.trimAscii.toString)

/-- Whether a text is one name a variable takes. -/
private def isName (s : String) : Bool :=
  !s.isEmpty && (s.front.isAlpha || s.front == '_') && s.all (fun c => c.isAlphanum || c == '_') &&
    (keyword s).isNone && !["not", "and", "or", "in", "is"].contains s

/-- An open block of the template being parsed: an `if` chain's branches so far and the branch being
read, or a `for` loop's variable and sequence. -/
private inductive Frame where
  | cond (done : Array (Expr × List Node)) (test : Option Expr) (nodes : Array Node)
  | loop (var : String) (seq : Expr) (body : Option (List Node)) (nodes : Array Node)

/-- A template's nodes from its stripped tokens: `if`/`elif`/`else`/`endif`, `for x in e`/`else`/
`endfor` and `set x = e` blocks, variables and text; a tag outside the subset, trailing words after
a closing tag or an unbalanced block is an error. -/
def parseNodes (toks : Array Tok) : Except String (List Node) := Id.run do
  let mut stack : Array Frame := #[]
  let mut top : Array Node := #[]
  let expr (src : String) : Except String Expr :=
    match elex src with
    | .ok ts => match parseExpr ts with
      | some e => .ok e
      | none => .error s!"an expression outside the subset: '{src}'"
    | .error e => .error e
  for t in toks do
    match t with
    | .data s => top := top.push (.text s)
    | .comment _ _ => pure ()
    | .var src _ _ =>
      match expr src with
      | .ok e => top := top.push (.out e)
      | .error e => return .error e
    | .block src _ _ =>
      let (kw, rest) := tagWords src
      if ["else", "endif", "endfor"].contains kw && !rest.isEmpty then
        return .error s!"words after '{kw}': '{rest}'"
      match kw with
      | "if" =>
        match expr rest with
        | .ok e => stack := stack.push (.cond #[] (some e) top); top := #[]
        | .error e => return .error e
      | "elif" =>
        match stack.back?, expr rest with
        | some (.cond done (some test) outer), .ok e =>
          stack := stack.pop.push (.cond (done.push (test, top.toList)) (some e) outer); top := #[]
        | _, .error e => return .error e
        | _, _ => return .error "an elif outside an if"
      | "else" =>
        match stack.back? with
        | some (.cond done (some test) outer) =>
          stack := stack.pop.push (.cond (done.push (test, top.toList)) none outer); top := #[]
        | some (.loop v e none outer) => stack := stack.pop.push (.loop v e (some top.toList) outer); top := #[]
        | _ => return .error "an else outside an if or a for"
      | "endif" =>
        match stack.back? with
        | some (.cond done test outer) =>
          let node := match test with
            | some e => Node.cond (done.push (e, top.toList)).toList []
            | none => Node.cond done.toList top.toList
          stack := stack.pop; top := outer.push node
        | _ => return .error "an endif outside an if"
      | "for" =>
        match rest.splitOn " in " with
        | [v, seqSrc] =>
          let v := v.trimAscii.toString
          unless isName v do return .error s!"a for over '{v}', not one name"
          match expr seqSrc with
          | .ok e => stack := stack.push (.loop v e none top); top := #[]
          | .error err => return .error err
        | _ => return .error s!"a for outside the subset: '{src}'"
      | "endfor" =>
        match stack.back? with
        | some (.loop v e body outer) =>
          let node := match body with
            | some b => Node.loop v e b top.toList
            | none => Node.loop v e top.toList []
          stack := stack.pop; top := outer.push node
        | _ => return .error "an endfor outside a for"
      | "set" =>
        match rest.splitOn "=" with
        | v :: vals@(_ :: _) =>
          let v := v.trimAscii.toString
          unless isName v do return .error s!"a set of '{v}', not one name"
          match expr ("=".intercalate vals) with
          | .ok e => top := top.push (.set v e)
          | .error err => return .error err
        | _ => return .error s!"a set outside the subset: '{src}'"
      | _ => return .error s!"a tag outside the subset: '{kw}'"
  unless stack.isEmpty do return .error "a block left open"
  return .ok top.toList

/-- A loop's `loop` object at item `i` of `n`. -/
def loopValue (i n : Nat) : Value :=
  .obj [("index", .num (i + 1)), ("index0", .num i), ("first", .bool (i == 0)),
    ("last", .bool (i + 1 == n)), ("length", .num n), ("revindex", .num (n - i)),
    ("revindex0", .num (n - i - 1))]

mutual

/-- The pieces nodes render to after `out` under a scope, with the scope their `set`s leave. -/
def renderNodes (sc : Scope) (out : Array Piece) : List Node → Except String (Array Piece × Scope)
  | [] => .ok (out, sc)
  | n :: rest => do
    let (out, sc) ← renderNode sc out n
    renderNodes sc out rest
termination_by l => sizeOf l

def renderNode (sc : Scope) (out : Array Piece) : Node → Except String (Array Piece × Scope)
  | .text s => .ok (out.push (.text s), sc)
  | .out e => do return (out ++ (← printed sc e), sc)
  | .set v e => do
    let x ← e.eval sc
    return (out, sc.assign v x (e.own sc))
  | .cond branches otherwise => renderBranches sc out otherwise branches
  | .loop v seq body otherwise => do
    let items ← match ← seq.eval sc with
      | .arr items => pure items
      | .str s => pure (s.toList.map fun (c : Char) => Value.str c.toString)
      | .splice n => throw s!"a loop over the typed content '{n}'"
      | _ => pure []
    let mut out := out
    let mut inner : Scope := { sc with frames := [] :: sc.frames }
    if items.isEmpty then
      let (o, after) ← renderNodes inner out otherwise
      out := o
      inner := after
    for (item, i) in items.zipIdx do
      let (o, after) ← renderNodes ((inner.bind "loop" (loopValue i items.length)).bind v item) out body
      out := o
      inner := after
    return (out, { inner with frames := inner.frames.drop 1 })
termination_by n => sizeOf n

def renderBranches (sc : Scope) (out : Array Piece) (otherwise : List Node) :
    List (Expr × List Node) → Except String (Array Piece × Scope)
  | [] => renderNodes sc out otherwise
  | (test, body) :: rest => do
    if (← test.eval sc).truthy then renderNodes sc out body
    else renderBranches sc out otherwise rest
termination_by bs => sizeOf otherwise + sizeOf bs

end

/-- A jtex template rendered over its context, `.splice` values standing for typed content. -/
def render (template : String) (context : Value) : Except String (Array Piece) := do
  let toks ← lex template
  let nodes ← parseNodes (stripped toks)
  let (out, _) ← renderNodes { context } #[] nodes
  return out

/-- The pieces as nunjucks prints them, each splice its name between `⟦` and `⟧`. -/
def Piece.spelled : Piece → String
  | .text s | .value s => s
  | .splice n => "⟦" ++ n ++ "⟧"

/-- The characters TeX reads as other than themselves in running text, and the line ends that would
end an argument's paragraph. -/
def texSpecials : List Char := ['\\', '{', '}', '$', '&', '#', '^', '_', '%', '~', '\n', '\r']

/-- The spellings a special character takes: each a control TeX reads as setting that character, or
a space for a line end. -/
def escapeSpellings : List String :=
  ["\\textbackslash{}", "\\{", "\\}", "\\$", "\\&", "\\#", "\\textasciicircum{}", "\\_", "\\%",
   "\\textasciitilde{}", " "]

/-- A character as running text spells it: a special one as the control that sets it. -/
def escapeChar (c : Char) : String :=
  match c with
  | '\\' => "\\textbackslash{}"
  | '{' => "\\{"
  | '}' => "\\}"
  | '$' => "\\$"
  | '&' => "\\&"
  | '#' => "\\#"
  | '^' => "\\textasciicircum{}"
  | '_' => "\\_"
  | '%' => "\\%"
  | '~' => "\\textasciitilde{}"
  | '\n' | '\r' => " "
  | c => c.toString

/-- A value the document chose, as TeX source: each character's spelling in order. -/
def escapeTex (s : String) : String := String.join (s.toList.map escapeChar)

/-- A special character spells one of the escape spellings. -/
theorem escapeChar_special (c : Char) (h : c ∈ texSpecials) : escapeChar c ∈ escapeSpellings := by
  simp only [texSpecials, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Any other character spells itself. -/
theorem escapeChar_plain (c : Char) (h : c ∉ texSpecials) : escapeChar c = c.toString := by
  simp only [texSpecials, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold escapeChar
  split <;> simp_all

/-- The pieces as TeX source, each value escaped and each splice given by `splice`. -/
def Piece.tex (splice : String → String) : Piece → String
  | .text s => s
  | .value s => escapeTex s
  | .splice n => splice n

end LeanTex.Core.Jtex
