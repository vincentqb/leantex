module

public section

namespace LeanTex.Core.Jtex

/-! The jtex template language MyST's LaTeX templates are written in: nunjucks 3.2.4 under jtex's
configuration (blocks `[# #]`, variables `[- -]`, comments `%# #%`, `trimBlocks`, no escaping, the
`len` filter), over the subset the templates use. -/

/-- A template value, as the JSON nunjucks reads: null, a boolean, a number, a string, an array or
an object of keys in order. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (items : List Value)
  | obj (fields : List (String × Value))
  deriving Repr, Inhabited, BEq

/-- An object's value under `key`, null where it holds none. -/
def Value.get (v : Value) (key : String) : Value :=
  match v with
  | .obj fields => ((fields.find? (·.1 == key)).map (·.2)).getD .null
  | _ => .null

/-- JavaScript's truthiness, which nunjucks's `if` reads: an empty array or object is true. -/
def Value.truthy : Value → Bool
  | .null => false
  | .bool b => b
  | .num n => n != 0
  | .str s => !s.isEmpty
  | .arr _ | .obj _ => true

mutual

/-- A value as nunjucks prints it: null as nothing, an array as JavaScript joins it. -/
def Value.show : Value → String
  | .null => ""
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => s
  | .arr items => Value.showList "" items
  | .obj _ => "[object Object]"

/-- The items printed after `acc`, a comma after each but the last. -/
def Value.showList (acc : String) : List Value → String
  | [] => acc
  | v :: rest => Value.showList (acc ++ v.show ++ (if rest.isEmpty then "" else ",")) rest

end

/-- JavaScript's loose equality over the values a template compares. -/
def Value.looseEq : Value → Value → Bool
  | .null, .null => true
  | .str a, .str b => a == b
  | .num a, .num b => a == b
  | .bool a, .bool b => a == b
  | .num a, .str b => toString a == b
  | .str a, .num b => a == toString b
  | .bool a, .num b => (if a then 1 else 0) == b
  | .num a, .bool b => a == (if b then 1 else 0)
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
content a reserved name splices in typed. -/
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
dropped; an unclosed tag is an error. -/
def lex (src : String) : Except String (Array Tok) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array Tok := #[]
  let mut buf := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
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

/-- The tokens with each text's whitespace stripped where the tag before or after it asks. -/
def stripped (toks : Array Tok) : Array Tok :=
  toks.zipIdx.map fun (t, k) => match t with
    | .data s =>
      let before := k > 0 && (toks[k - 1]?.map (·.strips.2)).getD false
      let after := (toks[k + 1]?.map (·.strips.1)).getD false
      let s := if before then (s.dropWhile Char.isWhitespace).copy else s
      .data (if after then (s.dropEndWhile Char.isWhitespace).copy else s)
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

/-- An expression's tokens; a character outside the subset is an error. -/
def elex (src : String) : Except String (Array ETok) := Id.run do
  let cs := src.toList.toArray
  let mut out : Array ETok := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs.getD i ' '
    if c.isWhitespace then i := i + 1; continue
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
      out := out.push (.num ((String.ofList (cs.extract i j).toList).toInt?.getD 0))
      i := j
    else if c == '"' || c == '\'' then
      let mut j := i + 1
      let mut v := ""
      let mut closed := false
      for _ in [i:cs.size] do
        let d := cs.getD j ' '
        if j ≥ cs.size then break
        if d == '\\' then v := v.push (cs.getD (j + 1) ' '); j := j + 2; continue
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
      let e : Expr := match name with
        | "and" => .and a b
        | "or" => .or a b
        | "==" => .cmp .eq a b
        | "!=" => .cmp .ne a b
        | "<" => .cmp .lt a b
        | ">" => .cmp .gt a b
        | "<=" => .cmp .le a b
        | _ => .cmp .ge a b
      some (vals.pop.pop.push e)
    | _, _ => none
  | .paren => none

/-- A literal or a path where a filter's argument stands, and the index past it. -/
private def argAt (ts : Array ETok) (i : Nat) : Option (Arg × Nat) := Id.run do
  match ts[i]? with
  | some (.str s) => return some (.lit (.str s), i + 1)
  | some (.num n) => return some (.lit (.num n), i + 1)
  | some (.name n) =>
    let mut p := #[n]
    let mut j := i + 1
    for _ in [i:ts.size] do
      match ts[j]?, ts[j + 1]? with
      | some (.punct "."), some (.name m) => p := p.push m; j := j + 2
      | _, _ => break
    return some (.path p.toList, j)
  | _ => return none

/-- An expression of the subset from its tokens, as the JavaScript nunjucks compiles it to binds:
`or` below `and` below equality below order below `not`, filters and paths binding tightest; none
outside the subset. -/
def parseExpr (ts : Array ETok) : Option Expr := Id.run do
  let mut vals : Array Expr := #[]
  let mut ops : Array Op := #[]
  let mut i := 0
  let binPrec : String → Option Nat
    | "or" => some 1
    | "and" => some 2
    | "==" | "!=" => some 4
    | "<" | ">" | "<=" | ">=" => some 5
    | _ => none
  for _ in [0:ts.size + 1] do
    if i ≥ ts.size then break
    match ts[i]? with
    | some (.name "not") => ops := ops.push .not; i := i + 1
    | some (.name n) =>
      if let some p := binPrec n then
        for _ in [0:ops.size] do
          match ops.back? with
          | some o => if o != .paren && o.prec ≥ p then
                        let some v := apply vals o | return none
                        vals := v; ops := ops.pop
                      else break
          | none => break
        ops := ops.push (.bin n p); i := i + 1
      else
        let lit : Option Value := match n with
          | "true" | "True" => some (.bool true)
          | "false" | "False" => some (.bool false)
          | "none" | "None" | "null" => some .null
          | _ => none
        match lit with
        | some v => vals := vals.push (.lit v); i := i + 1
        | none =>
          let some (.path p, j) := argAt ts i | return none
          let mut path := p
          let mut k := j
          -- a subscript by a literal: `a["b"]` or `a[0]`
          for _ in [0:ts.size] do
            match ts[k]?, ts[k + 1]?, ts[k + 2]? with
            | some (.punct "["), some (.str s), some (.punct "]") => path := path ++ [s]; k := k + 3
            | some (.punct "["), some (.num m), some (.punct "]") => path := path ++ [toString m]; k := k + 3
            | some (.punct "."), some (.name m), _ => path := path ++ [m]; k := k + 2
            | _, _, _ => break
          vals := vals.push (.path path); i := k
    | some (.str s) => vals := vals.push (.lit (.str s)); i := i + 1
    | some (.num n) => vals := vals.push (.lit (.num n)); i := i + 1
    | some (.punct "(") => ops := ops.push .paren; i := i + 1
    | some (.punct ")") =>
      for _ in [0:ops.size] do
        match ops.back? with
        | some .paren => break
        | some o => let some v := apply vals o | return none
                    vals := v; ops := ops.pop
        | none => return none
      unless ops.back? == some .paren do return none
      ops := ops.pop; i := i + 1
    | some (.punct "|") =>
      let some (.name f) := ts[i + 1]? | return none
      let mut args : Array Arg := #[]
      let mut k := i + 2
      if ts[k]? == some (.punct "(") then
        k := k + 1
        for _ in [0:ts.size] do
          if ts[k]? == some (.punct ")") then k := k + 1; break
          let some (a, j) := argAt ts k | return none
          args := args.push a
          k := if ts[j]? == some (.punct ",") then j + 1 else j
      let some e := vals.back? | return none
      vals := vals.pop.push (.filter e f args.toList); i := k
    | some (.punct o) =>
      let some p := binPrec o | return none
      for _ in [0:ops.size] do
        match ops.back? with
        | some op => if op != .paren && op.prec ≥ p then
                       let some v := apply vals op | return none
                       vals := v; ops := ops.pop
                     else break
        | none => break
      ops := ops.push (.bin o p); i := i + 1
    | none => break
  for _ in [0:ops.size] do
    match ops.back? with
    | some o => let some v := apply vals o | return none
                vals := v; ops := ops.pop
    | none => break
  return if vals.size == 1 then vals[0]? else none

/-- The variables in scope: nunjucks' frames, a loop's innermost first, over the template's context. -/
structure Scope where
  frames : List (List (String × Value)) := [[]]
  context : Value := .obj []

/-- A path's value: its first name a frame's or the context's, each next name a field, or an
array's item by its index. -/
def Scope.lookup (sc : Scope) : List String → Value
  | [] => .null
  | n :: rest =>
    let base := ((sc.frames.findSome? fun f => (f.find? (·.1 == n)).map (·.2)).getD (sc.context.get n))
    rest.foldl (fun v k => match v, k.toNat? with
      | .arr items, some i => items.getD i .null
      | v, _ => v.get k) base

/-- The scope with `name` bound in the innermost frame. -/
def Scope.bind (sc : Scope) (name : String) (v : Value) : Scope :=
  match sc.frames with
  | f :: fs => { sc with frames := ((name, v) :: f.filter (·.1 != name)) :: fs }
  | [] => { sc with frames := [[(name, v)]] }

/-- The scope after `set name`: the innermost frame holding `name` rebinds it, as nunjucks' write
resolves up, else the innermost frame binds it. -/
def Scope.assign (sc : Scope) (name : String) (v : Value) : Scope :=
  if sc.frames.any (·.any (·.1 == name)) then
    let rec go : List (List (String × Value)) → List (List (String × Value))
      | [] => []
      | f :: fs => if f.any (·.1 == name) then f.map (fun b => if b.1 == name then (name, v) else b) :: fs
        else f :: go fs
    { sc with frames := go sc.frames }
  else sc.bind name v

/-- An argument's value. -/
def Arg.eval (sc : Scope) : Arg → Value
  | .lit v => v
  | .path p => sc.lookup p

/-- A filter of the subset applied: `join` with its separator and an item's attribute, `length`,
jtex's `len`, `first`, `lower` and `upper`; none for another. -/
def filterApply (name : String) (v : Value) (args : List Value) : Option Value :=
  match name, v with
  | "join", .arr items =>
    let sep := match args.head? with
      | some (.str s) => s
      | _ => ""
    let items := match args[1]? with
      | some (.str attr) => items.map fun (v : Value) => v.get attr
      | _ => items
    some (.str (sep.intercalate (items.map fun (v : Value) => v.show)))
  | "length", .arr items | "len", .arr items => some (.num items.length)
  | "length", .str s | "len", .str s => some (.num s.length)
  | "length", .obj fs => some (.num fs.length)
  | "length", .null | "len", .null => some (.num 0)
  | "first", .arr items => some (items.head?.getD .null)
  | "first", .str s => some (.str (s.take 1).copy)
  | "lower", v => some (.str v.show.toLower)
  | "upper", v => some (.str v.show.toUpper)
  | _, _ => none

/-- An expression's value; a filter outside the subset is an error naming it. -/
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
    let num (v : Value) : Option Int := match v with
      | .num n => some n
      | .str s => s.toInt?
      | .bool b => some (if b then 1 else 0)
      | _ => none
    let ord (f : Int → Int → Bool) : Bool := match num x, num y with
      | some m, some n => f m n
      | _, _ => match x, y with
        | .str s, .str t => f (if s < t then -1 else if s == t then 0 else 1) 0
        | _, _ => false
    return .bool (match op with
      | .eq => x.looseEq y
      | .ne => !x.looseEq y
      | .lt => ord (· < ·)
      | .gt => ord (· > ·)
      | .le => ord (· ≤ ·)
      | .ge => ord (· ≥ ·))
  | .filter e name args => do
    let v ← e.eval sc
    match filterApply name v (args.map (·.eval sc)) with
    | some r => return r
    | none => throw s!"the filter '{name}' on this value"

/-- A statement tag's words: its keyword and the rest of its source. -/
private def tagWords (src : String) : String × String :=
  let t := src.trimAscii.toString
  let kw := (t.takeWhile fun c => !c.isWhitespace).toString
  (kw, (t.drop kw.length).toString.trimAscii.toString)

/-- An open block of the template being parsed: an `if` chain's branches so far and the branch being
read, or a `for` loop's variable and sequence. -/
private inductive Frame where
  | cond (done : List (Expr × List Node)) (test : Option Expr) (nodes : Array Node)
  | loop (var : String) (seq : Expr) (body : Option (List Node)) (nodes : Array Node)

/-- A template's nodes from its stripped tokens: `if`/`elif`/`else`/`endif`, `for x in e`/`else`/
`endfor` and `set x = e` blocks, variables and text; a tag outside the subset or an unbalanced block
is an error. -/
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
      match kw with
      | "if" =>
        match expr rest with
        | .ok e => stack := stack.push (.cond [] (some e) top); top := #[]
        | .error e => return .error e
      | "elif" =>
        match stack.back?, expr rest with
        | some (.cond done (some test) outer), .ok e =>
          stack := stack.pop.push (.cond (done ++ [(test, top.toList)]) (some e) outer); top := #[]
        | _, .error e => return .error e
        | _, _ => return .error "an elif outside an if"
      | "else" =>
        match stack.back? with
        | some (.cond done (some test) outer) =>
          stack := stack.pop.push (.cond (done ++ [(test, top.toList)]) none outer); top := #[]
        | some (.loop v e none outer) => stack := stack.pop.push (.loop v e (some top.toList) outer); top := #[]
        | _ => return .error "an else outside an if or a for"
      | "endif" =>
        match stack.back? with
        | some (.cond done test outer) =>
          let node := match test with
            | some e => Node.cond (done ++ [(e, top.toList)]) []
            | none => Node.cond done top.toList
          stack := stack.pop; top := outer.push node
        | _ => return .error "an endif outside an if"
      | "for" =>
        match rest.splitOn " in " with
        | [v, seqSrc] =>
          match expr seqSrc with
          | .ok e => stack := stack.push (.loop v.trimAscii.toString e none top); top := #[]
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
          match expr ("=".intercalate vals) with
          | .ok e => top := top.push (.set v.trimAscii.toString e)
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

/-- The pieces nodes render to after `out` under a scope, with the scope their `set`s leave; a name
in `splices` printed is a typed splice. -/
def renderNodes (splices : List String) (sc : Scope) (out : Array Piece) :
    List Node → Except String (Array Piece × Scope)
  | [] => .ok (out, sc)
  | n :: rest => do
    let (out, sc) ← renderNode splices sc out n
    renderNodes splices sc out rest
termination_by l => sizeOf l

def renderNode (splices : List String) (sc : Scope) (out : Array Piece) :
    Node → Except String (Array Piece × Scope)
  | .text s => .ok (out.push (.text s), sc)
  | .out e =>
    match e with
    | .path [n] => if splices.contains n then .ok (out.push (.splice n), sc) else
        do return (out.push (.value (← e.eval sc).show), sc)
    | _ => do return (out.push (.value (← e.eval sc).show), sc)
  | .set v e => do
    let x ← e.eval sc
    return (out, sc.assign v x)
  | .cond branches otherwise => renderBranches splices sc out otherwise branches
  | .loop v seq body otherwise => do
    let items := match ← seq.eval sc with
      | .arr items => items
      | .str s => s.toList.map fun (c : Char) => Value.str c.toString
      | _ => []
    if items.isEmpty then renderNodes splices sc out otherwise else
    let mut out := out
    let mut inner : Scope := { sc with frames := [] :: sc.frames }
    for (item, i) in items.zipIdx do
      let (o, after) ← renderNodes splices ((inner.bind "loop" (loopValue i items.length)).bind v item) out body
      out := o
      inner := after
    return (out, { inner with frames := inner.frames.drop 1 })
termination_by n => sizeOf n

def renderBranches (splices : List String) (sc : Scope) (out : Array Piece) (otherwise : List Node) :
    List (Expr × List Node) → Except String (Array Piece × Scope)
  | [] => renderNodes splices sc out otherwise
  | (test, body) :: rest => do
    if (← test.eval sc).truthy then renderNodes splices sc out body
    else renderBranches splices sc out otherwise rest
termination_by bs => sizeOf otherwise + sizeOf bs

end

/-- A jtex template rendered over its context, the names in `splices` set as typed splices. -/
def render (template : String) (context : Value) (splices : List String := []) :
    Except String (Array Piece) := do
  let toks ← lex template
  let nodes ← parseNodes (stripped toks)
  let (out, _) ← renderNodes splices { context } #[] nodes
  return out

/-- The pieces as nunjucks prints them, each splice its name between `⟦` and `⟧`. -/
def Piece.spelled : Piece → String
  | .text s | .value s => s
  | .splice n => "⟦" ++ n ++ "⟧"

/-- The characters TeX reads as other than themselves in running text. -/
def texSpecials : List Char := ['\\', '{', '}', '$', '&', '#', '^', '_', '%', '~']

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
  | c => c.toString

/-- A value the document chose, as TeX source setting its characters. -/
def escapeTex (s : String) : String := String.join (s.toList.map escapeChar)

/-- A special character never spells itself: each is escaped. -/
theorem escapeChar_special (c : Char) (h : c ∈ texSpecials) : escapeChar c ≠ c.toString := by
  simp only [texSpecials, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Any other character spells itself. -/
theorem escapeChar_plain (c : Char) (h : c ∉ texSpecials) : escapeChar c = c.toString := by
  simp only [texSpecials, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold escapeChar
  split <;> simp_all

/-- The pieces as TeX source, each value escaped and each splice given by `splice`. -/
def Piece.tex (splice : String → String) : Piece → String
  | .text s => s
  | .value s => escapeTex s
  | .splice n => splice n

end LeanTex.Core.Jtex
