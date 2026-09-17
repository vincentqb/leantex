import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Decl

/-!
The rendered `tikzpicture` subset: a coordinate system with `scale=`,
`\fill ... rectangle` with a colour expression, `\node[...] at (x,y) {text}`,
`\foreach` over a literal list (the `{a,...,b}` range and the `\x/\y` pair
form included), and `\pgfmathsetmacro`/`\pgfmathtruncatemacro` with the
arithmetic those need (`+ - * /`, `<`/`>`, parens, `max`/`min`,
`ifthenelse` with `"..."` string branches). The subset is scoped to what
one real diagram needs (PLAN M8, the tikz slice): everything is evaluated
here, at elaboration — loops unrolled, expressions reduced, colours
resolved through the document palette, `scale=` applied — so the IR
carries concrete shapes (`Ir.Pic.Shape`) and the backends never see the
source.

The boundary is named, never silent: a construct outside the subset is
W0334 (pending — the graphics story continues in M8) naming the construct;
an expression, range, or colour inside the subset that cannot evaluate is
E0333 naming it, and only its shape is lost. `\foreach` is total by
construction: the range's count is decided before its values exist
(`rangeCount`/`range`, with `range_size`/`range_get` the enumeration
facts), so a range that would not terminate is a diagnostic, not a hang.

Colour mixes reuse `Palette.resolve` (xcolor's `!` chains) and numbers
reuse `Decl.parseDecimal`: the evaluator here adds only the arithmetic
layer neither has.
-/

namespace LeanTex.Core.Picture

open LeanTex.Core LeanTex.Core.Dim

/-- A diagnostic the picture walk raises: code and message; the elaborator
adds the environment's position. -/
abbrev PDiag := DiagCode × String

/-- One micro-token of picture source. The lexer's words run punctuation
together (`++(0.92,0.92);` is one word), so `ofRaws` re-splits them into
numbers, identifiers, and single symbols; braces arrive pre-matched as
groups from `Parse.Raw`. -/
inductive Tok where
  | ctrl (name : String)
  | ident (s : String)
  /-- A number literal, in thousandths (`Decl.parseDecimal`, exact to the
  milli the subset's arithmetic works in). -/
  | num (milli : Int)
  | sym (c : Char)
  | space
  | group (body : List Tok)
  /-- Source the subset cannot even tokenise into itself (math, a nested
  environment, verbatim): named so the diagnostic can say what stood
  here. -/
  | other (what : String)
  deriving Repr, BEq, Inhabited

/-- Split one lexer word into micro-tokens: digit runs (with `.`) become
numbers, letter runs identifiers, everything else single symbols. A `.`
starts a number only when a digit follows, so `...` stays three symbols. -/
private def splitWord (acc : Array Tok) (s : String) : Array Tok := Id.run do
  let cs := s.toList.toArray
  let mut out := acc
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c.isDigit || (c == '.' && (cs[i+1]?.any Char.isDigit)) then
        let mut j := i + 1
        for _ in [i+1:cs.size] do
          if h2 : j < cs.size then
            if cs[j].isDigit || cs[j] == '.' then j := j + 1 else break
          else break
        -- Trailing dots belong to a following `...`, not the number.
        let mut k := j
        for _ in [0:j - i] do
          if k > i + 1 && cs[k-1]? == some '.' && !((cs[k]?).any Char.isDigit) then
            k := k - 1
          else break
        let lit := String.ofList (cs.toList.drop i |>.take (k - i))
        match Decl.parseDecimal lit with
        | some (m, sc) => out := out.push (.num (m * 1000 / sc))
        | none => out := out.push (.other s!"number '{lit}'")
        i := k
      else if c.isAlpha then
        let mut j := i + 1
        for _ in [i+1:cs.size] do
          if h2 : j < cs.size then
            if cs[j].isAlpha then j := j + 1 else break
          else break
        out := out.push (.ident (String.ofList (cs.toList.drop i |>.take (j - i))))
        i := j
      else
        out := out.push (.sym c)
        i := i + 1
    else
      break
  return out

mutual

/-- `Parse.Raw` to picture micro-tokens; groups keep their tree. -/
def ofRawList (acc : Array Tok) : List Parse.Raw → Array Tok
  | [] => acc
  | r :: rest => ofRawList (ofRawOne acc r) rest

def ofRawOne (acc : Array Tok) : Parse.Raw → Array Tok
  | .word s _ => splitWord acc s
  | .space => acc.push .space
  | .par _ => acc.push .space
  | .ctrl n _ => acc.push (.ctrl n)
  | .sym c _ => acc.push (.sym c)
  | .group body _ => acc.push (.group (ofRawList #[] body.toList).toList)
  | .math _ _ _ => acc.push (.other "math")
  | .env n _ _ => acc.push (.other s!"environment '{n}'")
  | .verb _ _ => acc.push (.other "verbatim")

end

def ofRaws (raws : Array Parse.Raw) : Array Tok :=
  ofRawList #[] raws.toList

-- Expression evaluation: pgfmath's arithmetic over milli fixed point.

/-- A `\foreach` binding's value: a number in milli, or the raw text of a
list item that is not one (a label like `alpha`). -/
inductive Val where
  | num (m : Int)
  | str (s : String)
  deriving Repr, BEq, Inhabited

/-- Render a milli value the way pgf prints a macro: an integer without a
point, otherwise up to three decimals. -/
def milliString (m : Int) : String :=
  let neg := m < 0
  let n := m.natAbs
  let ip := n / 1000
  let fr := n % 1000
  let sign := if neg then "-" else ""
  if fr == 0 then s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (3 - frs.length)) ++ frs
    s!"{sign}{ip}.{(frs.dropEndWhile (· == '0')).toString}"

def Val.text : Val → String
  | .num m => milliString m
  | .str s => s

/-- A token named for a diagnostic. -/
private def tokText : Tok → String
  | .ctrl n => s!"'\\{n}'"
  | .ident s => s!"'{s}'"
  | .num m => s!"'{milliString m}'"
  | .sym c => s!"'{c}'"
  | .space => "a space"
  | .group _ => "'{...}'"
  | .other what => what

/-- One RPN element of a parsed expression. -/
private inductive Rp where
  | push (v : Val)
  | neg
  | add | sub | mul | div
  | lt | gt
  | fmax | fmin | fite
  deriving Repr, BEq

/-- Operator precedence for the shunting yard; `neg` binds tightest,
comparisons loosest (pgfmath's ordering). -/
private def prec : Rp → Nat
  | .neg => 4
  | .mul | .div => 3
  | .add | .sub => 2
  | .lt | .gt => 1
  | _ => 0

/-- Evaluate an expression's micro-tokens against the macro environment:
shunting-yard to RPN, then a stack evaluation — two flat passes, total by
construction. Values are numbers in milli or strings (`"black"`, an
`ifthenelse` branch); arithmetic on a string names it. Every failure names
what stopped it. -/
def evalExpr (env : List (String × Val)) (toks : Array Tok) : Except String Val := Id.run do
  -- To RPN. `expectOperand` distinguishes unary minus from subtraction.
  let mut out : Array Rp := #[]
  let mut ops : Array Rp := #[]  -- operators and '(' markers (calls double as markers)
  let mut marks : Array Bool := #[]  -- per '(': is it a function call
  let mut expectOperand := true
  let mut i := 0
  let flushTo (out : Array Rp) (ops : Array Rp) (p : Nat) : Array Rp × Array Rp := Id.run do
    let mut out := out
    let mut ops := ops
    for _ in [0:ops.size] do
      match ops.back? with
      | some op =>
        if prec op ≥ p && op != .fmax && op != .fmin && op != .fite then
          out := out.push op
          ops := ops.pop
        else break
      | none => break
    return (out, ops)
  for _ in [0:toks.size + 1] do
    if h : i < toks.size then
      let t := toks[i]
      i := i + 1
      match t with
      | .space => pure ()
      | .num m =>
        out := out.push (.push (.num m))
        expectOperand := false
      | .ctrl name =>
        match env.lookup name with
        | some v =>
          out := out.push (.push v)
          expectOperand := false
        | none => return .error s!"unknown macro '\\{name}'"
      | .ident "max" | .ident "min" | .ident "ifthenelse" =>
        let f := if t == .ident "max" then Rp.fmax
          else if t == .ident "min" then Rp.fmin else Rp.fite
        match toks[i]? with
        | some (.sym '(') =>
          i := i + 1
          ops := ops.push f
          marks := marks.push true
          expectOperand := true
        | _ => return .error s!"{tokText t} needs '(...)'"
      | .ident name => return .error s!"unknown function or name '{name}'"
      | .sym '"' =>
        -- A pgfmath string literal: one word between quotes.
        match toks[i]?, toks[i+1]? with
        | some (.ident s), some (.sym '"') =>
          i := i + 2
          out := out.push (.push (.str s))
          expectOperand := false
        | _, _ => return .error "an unreadable \"...\" string"
      | .sym '(' =>
        ops := ops.push .fmax  -- placeholder marker; marks says it is bare
        marks := marks.push false
        expectOperand := true
      | .sym ')' =>
        let (o2, p2) := flushTo out ops 1
        out := o2
        ops := p2
        match ops.back?, marks.back? with
        | some f, some isCall =>
          ops := ops.pop
          marks := marks.pop
          if isCall then out := out.push f
          expectOperand := false
        | _, _ => return .error "unmatched ')'"
      | .sym ',' =>
        -- Argument separator: flush to the enclosing call marker.
        let (o2, p2) := flushTo out ops 1
        out := o2
        ops := p2
        expectOperand := true
      | .sym '-' =>
        if expectOperand then
          ops := ops.push .neg
        else
          let (o2, p2) := flushTo out ops 2
          out := o2
          ops := p2.push .sub
          expectOperand := true
      | .sym '+' =>
        if expectOperand then pure ()  -- unary plus
        else
          let (o2, p2) := flushTo out ops 2
          out := o2
          ops := p2.push .add
          expectOperand := true
      | .sym '*' =>
        let (o2, p2) := flushTo out ops 3
        out := o2
        ops := p2.push .mul
        expectOperand := true
      | .sym '/' =>
        let (o2, p2) := flushTo out ops 3
        out := o2
        ops := p2.push .div
        expectOperand := true
      | .sym '<' =>
        let (o2, p2) := flushTo out ops 1
        out := o2
        ops := p2.push .lt
        expectOperand := true
      | .sym '>' =>
        let (o2, p2) := flushTo out ops 1
        out := o2
        ops := p2.push .gt
        expectOperand := true
      | .sym c => return .error s!"'{c}' in an expression"
      | .group _ => return .error "'{...}' in an expression"
      | .other what => return .error s!"{what} in an expression"
  let (o2, p2) := flushTo out ops 1
  out := o2
  for op in p2.reverse do
    if op == .fmax || op == .fmin || op == .fite then
      return .error "unclosed '('"
    out := out.push op
  -- Evaluate the RPN. Arithmetic wants numbers; a string operand names
  -- itself. `ifthenelse` is pgfmath's: a nonzero condition picks the
  -- second argument, zero the third, and the branches may be strings.
  let mut stack : Array Val := #[]
  let num (v : Val) : Except String Int :=
    match v with
    | .num m => .ok m
    | .str s => .error s!"'{s}' where a number is needed"
  for r in out do
    match r with
    | .push v => stack := stack.push v
    | .neg =>
      match stack.back? with
      | some a =>
        match num a with
        | .ok m => stack := stack.pop.push (.num (-m))
        | .error e => return .error e
      | none => return .error "misplaced '-'"
    | .fite =>
      match stack.back?, stack.pop.back?, stack.pop.pop.back? with
      | some no, some yes, some c =>
        let stack' := stack.pop.pop.pop
        match num c with
        | .ok m => stack := stack'.push (if m != 0 then yes else no)
        | .error e => return .error e
      | _, _, _ => return .error "'ifthenelse' needs (condition, value, value)"
    | op =>
      match stack.back? with
      | some bv =>
        match stack.pop.back? with
        | some av =>
          let stack' := stack.pop.pop
          match num av, num bv with
          | .ok a, .ok b =>
            match op with
            | .add => stack := stack'.push (.num (a + b))
            | .sub => stack := stack'.push (.num (a - b))
            | .mul => stack := stack'.push (.num (a * b / 1000))
            | .fmax => stack := stack'.push (.num (max a b))
            | .fmin => stack := stack'.push (.num (min a b))
            | .lt => stack := stack'.push (.num (if a < b then 1000 else 0))
            | .gt => stack := stack'.push (.num (if a > b then 1000 else 0))
            | .div =>
              if b == 0 then return .error "division by zero"
              else stack := stack'.push (.num (a * 1000 / b))
            | _ => return .error "malformed expression"
          | .error e, _ | _, .error e => return .error e
        | none => return .error "operator missing an operand"
      | none => return .error "operator missing an operand"
  match stack.toList with
  | [v] => return .ok v
  | [] => return .error "empty expression"
  | _ => return .error "malformed expression"

/-- An expression in a place that needs a number: a coordinate, a scale. -/
def evalNum (env : List (String × Val)) (toks : Array Tok) : Except String Int :=
  match evalExpr env toks with
  | .ok (.num m) => .ok m
  | .ok (.str s) => .error s!"'{s}' where a number is needed"
  | .error e => .error e

-- `\foreach` ranges: the count is decided before the values exist.

/-- How many values `{a,...,b}` (step `step`) enumerates: `none` when the
step is zero or walks away from the bound — the range that would never
terminate is a diagnostic, not a hang. -/
def rangeCount (a step b : Int) : Option Nat :=
  if step > 0 && a ≤ b then some (((b - a) / step).toNat + 1)
  else if step < 0 && b ≤ a then some (((a - b) / (-step)).toNat + 1)
  else none

/-- The enumerated values, indexed off the count: total by construction. -/
def range (a step b : Int) : Option (Array Int) :=
  (rangeCount a step b).map fun n => (Array.range n).map fun i => a + step * Int.ofNat i

/-- The enumeration is exactly its count long. -/
theorem range_size (a step b : Int) (n : Nat) (h : rangeCount a step b = some n) :
    (range a step b).map (·.size) = some n := by
  simp [range, h]

/-- The k-th value is `a + step·k`: the range enumerates its arithmetic
progression exactly, no value skipped or invented. -/
theorem range_get (a step b : Int) (xs : Array Int) (hx : range a step b = some xs)
    (i : Nat) (h : i < xs.size) : xs[i] = a + step * i := by
  simp only [range, Option.map_eq_some_iff] at hx
  obtain ⟨n, _, hmap⟩ := hx
  subst hmap
  simp

/-- The brief's instance: `{a,...,b}` in whole units (milli ×1000, the
default step) enumerates `b − a + 1` values. -/
theorem range_unit_size (a b : Int) (hab : a ≤ b) :
    (range (1000 * a) 1000 (1000 * b)).map (·.size) = some ((b - a).toNat + 1) := by
  have hc : rangeCount (1000 * a) 1000 (1000 * b) = some ((b - a).toNat + 1) := by
    have hcond : (decide ((1000:Int) > 0) && decide ((1000:Int) * a ≤ 1000 * b)) = true := by
      simp [hab]
    simp only [rangeCount, hcond, Option.some.injEq, ite_true]
    omega
  exact range_size _ _ _ _ hc

-- Statements.

/-- One parsed picture statement. `fill` and `node` keep their token
slices — coordinates and options are evaluated per loop iteration, where
the bindings live. -/
inductive Stmt where
  | fill (toks : Array Tok)
  | node (toks : Array Tok)
  /-- `\pgfmathsetmacro`, and `\pgfmathtruncatemacro` when `trunc`. -/
  | set (name : String) (expr : Array Tok) (trunc : Bool)
  | foreach (vars : Array String) (list : Array Tok) (body : List Stmt)
  deriving Repr, Inhabited

/-- What the statement machine is in the middle of. -/
private inductive Mode where
  | top
  /-- Collecting a `\fill`/`\node` statement's tokens to its `;`. -/
  | stmt (isFill : Bool) (acc : Array Tok)
  /-- After `\pgfmathsetmacro` (or the truncating form), expecting `{\name}`. -/
  | sname (trunc : Bool)
  /-- After `{\name}`, expecting the `{expr}` group. -/
  | sexpr (name : String) (trunc : Bool)
  /-- After `\foreach`, collecting `\x` or `\x/\y` until `in`. -/
  | fvars (vars : Array String)
  /-- After `in`, expecting the `{list}` group. -/
  | flist (vars : Array String)
  /-- After the list, expecting the body: a group, a nested `\foreach`,
  or one `;`-terminated statement. -/
  | fbody (vars : Array String) (list : Array Tok)
  /-- Recovering from a construct outside the subset: to the next `;`. -/
  | skip
  deriving Repr, Inhabited

private structure PSt where
  out : Array Stmt := #[]
  bad : Array PDiag := #[]
  /-- Enclosing `\foreach` headers whose body is the statement being
  built, innermost last. -/
  pending : Array (Array String × Array Tok) := #[]
  mode : Mode := .top

/-- Close one finished statement: wrap it in every pending `\foreach`
header (an unbraced body is one statement), emit, reset. -/
private def PSt.finish (st : PSt) (s : Stmt) : PSt := Id.run do
  let mut s := s
  let mut pending := st.pending
  for _ in [0:st.pending.size] do
    match pending.back? with
    | some (vars, list) =>
      s := .foreach vars list [s]
      pending := pending.pop
    | none => break
  return { st with out := st.out.push s, pending := #[], mode := .top }

private def PSt.diag (st : PSt) (code : DiagCode) (msg : String) : PSt :=
  if st.bad.any (·.2 == msg) then st
  else { st with bad := st.bad.push (code, msg) }

private def PSt.outside (st : PSt) (what : String) : PSt :=
  st.diag .W0334 s!"{what} is outside the rendered picture subset; not drawn"

/-- One non-recursive machine step: every case except a `\foreach` body
group, which `parseToks` handles so the recursion into the group subtree
stays structural. -/
private def step (t : Tok) (st : PSt) : PSt :=
  match st.mode with
  | .top =>
    match t with
    | .ctrl "fill" => { st with mode := .stmt true #[] }
    | .ctrl "node" => { st with mode := .stmt false #[] }
    | .ctrl "foreach" => { st with mode := .fvars #[] }
    | .ctrl "pgfmathsetmacro" => { st with mode := .sname false }
    | .ctrl "pgfmathtruncatemacro" => { st with mode := .sname true }
    | .ctrl name => { (st.outside s!"'\\{name}'") with mode := .skip }
    | .sym ';' | .space => st
    | .other what => { (st.outside what) with mode := .skip }
    | .ident s => { (st.outside s!"'{s}'") with mode := .skip }
    | .num _ => { (st.outside "a bare number") with mode := .skip }
    | .sym c => { (st.outside s!"'{c}'") with mode := .skip }
    | .group _ => { (st.outside "'{...}'") with mode := .skip }
  | .stmt isFill acc =>
    match t with
    | .sym ';' => st.finish (if isFill then .fill acc else .node acc)
    | _ => { st with mode := .stmt isFill (acc.push t) }
  | .sname trunc =>
    match t with
    | .space => st
    | .group g =>
      match g.filter (· != .space) with
      | [.ctrl name] => { st with mode := .sexpr name trunc }
      | _ => { st.diag .E0333 "'\\pgfmathsetmacro' needs '{\\name}' first" with mode := .top }
    | _ =>
      { st.diag .E0333 "'\\pgfmathsetmacro' needs '{\\name}' first" with mode := .top }
  | .sexpr name trunc =>
    match t with
    | .space => st
    | .group g => st.finish (.set name g.toArray trunc)
    | _ =>
      { st.diag .E0333 s!"'\\pgfmathsetmacro' of '\\{name}' needs an expression group"
        with mode := .top }
  | .fvars vars =>
    match t with
    | .ctrl v => { st with mode := .fvars (vars.push v) }
    | .sym '/' | .space => st
    | .ident "in" => { st with mode := .flist vars }
    | _ =>
      { (st.outside "this '\\foreach' variable list")
        with mode := .skip, pending := #[] }
  | .flist vars =>
    match t with
    | .space => st
    | .group l => { st with mode := .fbody vars l.toArray }
    | _ =>
      { (st.outside "a '\\foreach' without a '{...}' list")
        with mode := .skip, pending := #[] }
  | .fbody vars list =>
    match t with
    | .space => st
    | .ctrl "foreach" =>
      { st with pending := st.pending.push (vars, list), mode := .fvars #[] }
    | .ctrl "fill" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt true #[] }
    | .ctrl "node" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt false #[] }
    -- `.group` never reaches here: `parseToks` owns that arm.
    | _ =>
      { (st.outside "this '\\foreach' body")
        with mode := .skip, pending := #[] }
  | .skip =>
    match t with
    | .sym ';' => { st with mode := .top }
    | _ => st

mutual

/-- Parse micro-tokens into statements: one fold, the only recursion into
pre-matched group subtrees (a `\foreach` body), so totality is structural.
Anything outside the subset is named (W0334) and skipped to the next `;` —
never silently dropped, and never able to take the rest of the picture
with it. -/
def parseList : List Tok → PSt → PSt
  | [], st =>
    match st.mode with
    | .top => st
    | .skip => { st with mode := .top, pending := #[] }
    | .stmt isFill _ =>
      { st.diag .E0333
          s!"'\\{if isFill then "fill" else "node"}' misses its ';'; the shape is not drawn"
        with mode := .top, pending := #[] }
    | _ =>
      { st.diag .E0333 "a picture statement ends mid-construct; it is not drawn"
        with mode := .top, pending := #[] }
  | t :: rest, st => parseList rest (parseTok t st)

def parseTok (t : Tok) (st : PSt) : PSt :=
  match st.mode, t with
  | .fbody vars list, .group g =>
    let sub := parseList g {}
    { st with bad := st.bad ++ sub.bad }.finish (.foreach vars list sub.out.toList)
  | _, _ => step t st

end

/-- Evaluation context: the document palette (colour names resolve against
it) and the picture's `scale=`, per mille. -/
structure Cx where
  pal : Ir.Palette
  scale : Int := 1000

/-- Picture milli-units to sp: one TikZ unit is 1 cm, times the declared
scale. One multiplication, one rounding division. -/
def Cx.toSp (cx : Cx) (m : Int) : Sp :=
  m * cx.scale * Dim.mm 10 / 1000000

/-- Split on a separator symbol at zero paren depth (groups are subtrees,
so only `(`/`)` count). -/
private def splitTop (toks : Array Tok) (sep : Char) : Array (Array Tok) := Id.run do
  let mut out : Array (Array Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth := 0
  for t in toks do
    match t with
    | .sym '(' => depth := depth + 1; cur := cur.push t
    | .sym ')' => depth := depth - 1; cur := cur.push t
    | .sym c =>
      if c == sep && depth == 0 then
        out := out.push cur
        cur := #[]
      else cur := cur.push t
    | _ => cur := cur.push t
  return out.push cur

/-- Substitute macros into a colour spelling and hand it to
`Palette.resolve`, the engine's one `!`-mix parser. A computed percentage
rounds to the whole percent xcolor's grammar takes. -/
private def evalColor (cx : Cx) (env : List (String × Val)) (toks : Array Tok) :
    Except String Ir.Color := Id.run do
  let pct (m : Int) : Except String String :=
    if m < 0 then .error s!"'{milliString m}' is not a percentage"
    else .ok (toString ((m + 500) / 1000))
  let mut s := ""
  for t in toks do
    match t with
    | .space => pure ()
    | .ident n => s := s ++ n
    | .sym '!' => s := s ++ "!"
    | .num m =>
      match pct m with
      | .ok p => s := s ++ p
      | .error e => return .error e
    | .ctrl n =>
      match env.lookup n with
      | some (.num m) =>
        match pct m with
        | .ok p => s := s ++ p
        | .error e => return .error e
      | some (.str v) => s := s ++ v
      | none => return .error s!"unknown macro '\\{n}' in a colour"
    | t => return .error s!"{tokText t} in a colour"
  match cx.pal.resolve s with
  | some c => return .ok c
  | none => return .error s!"colour '{s}' does not resolve against the palette"

/-- Read `(x, y)` at index `i`: the two expression slices and the index
past the closing paren. Parens nest (`max(...)` inside a coordinate). -/
private def readCoord (toks : Array Tok) (i : Nat) :
    Except String ((Array Tok × Array Tok) × Nat) := Id.run do
  unless toks[i]? == some (.sym '(') do
    return .error s!"expected a '(x, y)' coordinate, found \
{((toks[i]?).map tokText).getD "the end"}"
  let mut depth := 1
  let mut j := i + 1
  let mut inner : Array Tok := #[]
  for _ in [i+1:toks.size + 1] do
    if h : j < toks.size then
      match toks[j] with
      | .sym '(' => depth := depth + 1; inner := inner.push toks[j]; j := j + 1
      | .sym ')' =>
        depth := depth - 1
        if depth == 0 then break
        inner := inner.push toks[j]
        j := j + 1
      | t => inner := inner.push t; j := j + 1
    else break
  unless depth == 0 do
    return .error "a coordinate misses its ')'"
  match (splitTop inner ',').toList with
  | [xs, ys] => return .ok ((xs, ys), j + 1)
  | _ => return .error "a coordinate needs exactly 'x, y'"

/-- Shapes and named losses, accumulated across the unrolled walk. A
diagnostic dedupes on its message: one construct looped over forty times
is one problem, not forty. -/
structure Ev where
  shapes : Array Ir.Pic.Shape := #[]
  diags : Array PDiag := #[]

def Ev.diag (ev : Ev) (d : PDiag) : Ev :=
  if ev.diags.any (·.2 == d.2) then ev else { ev with diags := ev.diags.push d }

/-- `\fill[colour] (x,y) rectangle ++(dx,dy);` — the one drawing shape of
the subset (`++` relative, or a second absolute corner). The rectangle is
stored corner-sorted, so the IR shape always has non-negative extents. -/
private def evalFill (cx : Cx) (env : List (String × Val)) (toks : Array Tok) :
    Except PDiag Ir.Pic.Shape := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut color := Ir.Color.black
  if ts[0]? == some (.sym '[') then
    let mut j := 1
    let mut inner : Array Tok := #[]
    for _ in [1:ts.size + 1] do
      if h : j < ts.size then
        if ts[j] == .sym ']' then break
        inner := inner.push ts[j]
        j := j + 1
      else break
    unless ts[j]? == some (.sym ']') do
      return .error (.E0333, "'\\fill' options miss their ']'; the shape is not drawn")
    match evalColor cx env inner with
    | .ok c => color := c
    | .error e => return .error (.E0333, s!"{e}; the shape is not drawn")
    i := j + 1
  let c1 ← match readCoord ts i with
    | .ok v => pure v
    | .error e => return .error (.E0333, s!"in '\\fill', {e}; the shape is not drawn")
  let ((x1s, y1s), i1) := c1
  i := i1
  unless ts[i]? == some (.ident "rectangle") do
    return .error (.W0334, s!"'\\fill' with \
{((ts[i]?).map tokText).getD "no shape operation"} is outside the rendered picture \
subset; the shape is not drawn")
  i := i + 1
  let mut relative := false
  if ts[i]? == some (.sym '+') && ts[i+1]? == some (.sym '+') then
    relative := true
    i := i + 2
  let c2 ← match readCoord ts i with
    | .ok v => pure v
    | .error e => return .error (.E0333, s!"in '\\fill', {e}; the shape is not drawn")
  let ((x2s, y2s), i2) := c2
  if h : i2 < ts.size then
    return .error (.W0334, s!"'\\fill' continues with {tokText ts[i2]}, outside the \
rendered picture subset; the shape is not drawn")
  let vals ← match evalNum env x1s, evalNum env y1s, evalNum env x2s, evalNum env y2s with
    | .ok a, .ok b, .ok c, .ok d => pure (a, b, c, d)
    | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e =>
      return .error (.E0333, s!"in '\\fill', {e}; the shape is not drawn")
  let (x1m, y1m, x2m, y2m) := vals
  let (x2m, y2m) := if relative then (x1m + x2m, y1m + y2m) else (x2m, y2m)
  let (x1, y1) := (cx.toSp x1m, cx.toSp y1m)
  let (x2, y2) := (cx.toSp x2m, cx.toSp y2m)
  return .ok (.rect (min x1 x2) (min y1 y2) (max x1 x2 - min x1 x2)
    (max y1 y2 - min y1 y2) color)

/-- A node body's text: words, numbers, and bound macros; anything else is
outside the subset and names itself. -/
private def textOf (env : List (String × Val)) (toks : List Tok) :
    Except String String := Id.run do
  let mut s := ""
  for t in toks do
    match t with
    | .ident w => s := s ++ w
    | .num m => s := s ++ milliString m
    | .space => s := s.push ' '
    | .sym c => s := s.push c
    | .ctrl n =>
      match env.lookup n with
      | some v => s := s ++ v.text
      | none => return .error s!"unknown macro '\\{n}'"
    | t => return .error (tokText t)
  return .ok s.trimAscii.toString

/-- `\node[font=\small, text=colour] at (x,y) {text};` — a centred label.
An option outside the subset loses only itself (named); a node without
`at` or a readable body loses the node. -/
private def evalNode (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) : Ev := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut color := Ir.Color.black
  let mut scale : Nat := 1000
  let mut ev := ev
  if ts[0]? == some (.sym '[') then
    let mut j := 1
    let mut inner : Array Tok := #[]
    for _ in [1:ts.size + 1] do
      if h : j < ts.size then
        if ts[j] == .sym ']' then break
        inner := inner.push ts[j]
        j := j + 1
      else break
    unless ts[j]? == some (.sym ']') do
      return ev.diag (.E0333, "'\\node' options miss their ']'; the node is not drawn")
    for opt in splitTop inner ',' do
      match opt.toList with
      | .ident "font" :: .sym '=' :: .ctrl size :: [] =>
        match Ir.sizeScale.lookup size with
        | some k => scale := k
        | none =>
          ev := ev.diag (.W0334, s!"node option 'font=\\{size}' is outside the \
rendered picture subset; the option is dropped")
      | .ident "text" :: .sym '=' :: rest =>
        match evalColor cx env rest.toArray with
        | .ok c => color := c
        | .error e => ev := ev.diag (.E0333, s!"in '\\node', {e}; the colour is dropped")
      | [] => pure ()
      | o :: _ =>
        ev := ev.diag (.W0334, s!"node option {tokText o} is outside the rendered \
picture subset; the option is dropped")
    i := j + 1
  unless ts[i]? == some (.ident "at") do
    return ev.diag (.W0334, "a '\\node' without 'at (x, y)' is outside the rendered \
picture subset; the node is not drawn")
  i := i + 1
  match readCoord ts i with
  | .error e => return ev.diag (.E0333, s!"in '\\node', {e}; the node is not drawn")
  | .ok ((xs, ys), i2) =>
    match ts[i2]? with
    | some (.group body) =>
      match evalNum env xs, evalNum env ys, textOf env body with
      | .ok xm, .ok ym, .ok text =>
        if h : i2 + 1 < ts.size then
          return ev.diag (.W0334, s!"'\\node' continues with {tokText ts[i2+1]}, \
outside the rendered picture subset; the node is not drawn")
        let shape := Ir.Pic.Shape.label (cx.toSp xm) (cx.toSp ym) text color scale
        return { ev with shapes := ev.shapes.push shape }
      | .error e, _, _ | _, .error e, _ =>
        return ev.diag (.E0333, s!"in '\\node', {e}; the node is not drawn")
      | _, _, .error e =>
        return ev.diag (.W0334, s!"{e} in a node body is outside the rendered \
picture subset; the node is not drawn")
    | _ =>
      return ev.diag (.E0333, "'\\node' needs a '{text}' body; the node is not drawn")

/-- One `\foreach` list item: values (`1`, `2/3`, a word), or the `...`
range marker. -/
private inductive Item where
  | vals (vs : Array Val)
  | dots
  deriving Repr, BEq

/-- Read the literal list: items split on `,`, `...` recognised, `/` the
pair form; a non-numeric single word rides as text. -/
private def readItems (env : List (String × Val)) (toks : Array Tok) :
    Except String (Array Item) := Id.run do
  let mut out : Array Item := #[]
  for part in splitTop toks ',' do
    let part := part.filter (· != .space)
    if part == #[.sym '.', .sym '.', .sym '.'] then
      out := out.push .dots
    else if part.isEmpty then
      pure ()
    else
      let mut vs : Array Val := #[]
      for sub in splitTop part '/' do
        match evalExpr env sub with
        | .ok v => vs := vs.push v
        | .error e =>
          match sub.toList.filter (· != .space) with
          | [.ident w] => vs := vs.push (.str w)
          | _ => return .error e
      out := out.push (.vals vs)
  return .ok out

/-- Unroll the list, ranges expanded through `range` — count first, values
indexed off it, so termination is by construction and a range that walks
away from its bound is named instead of spun. -/
private def expandItems (items : Array Item) : Except String (Array (Array Val)) := Id.run do
  let mut out : Array (Array Val) := #[]
  let mut i := 0
  for _ in [0:items.size + 1] do
    if h : i < items.size then
      match items[i] with
      | .vals vs =>
        out := out.push vs
        i := i + 1
      | .dots =>
        let prev ← match out.back? with
          | some #[Val.num a] => pure a
          | _ => return .error "'...' needs a number before it"
        let bound ← match items[i+1]? with
          | some (.vals #[Val.num b]) => pure b
          | _ => return .error "'...' needs a number bound after it"
        let step ← if out.size ≥ 2 then
            match out[out.size - 2]? with
            | some #[Val.num p2] =>
              if prev - p2 == 0 then
                return .error "a '...' range with a zero step never reaches its bound"
              else pure (prev - p2)
            | _ => pure (if bound ≥ prev then (1000 : Int) else -1000)
          else pure (if bound ≥ prev then (1000 : Int) else -1000)
        if prev == bound then
          i := i + 2
        else
          match range (prev + step) step bound with
          | some vals =>
            for v in vals do
              out := out.push #[.num v]
            i := i + 2
          | none =>
            return .error s!"the range '{milliString prev}, ..., {milliString bound}' \
(step {milliString step}) never reaches its bound"
    else break
  return .ok out

/-- Bind the `\x/\y` variables to one item; pgf repeats the last given
part when the item is shorter than the variable list. -/
private def bindVars (vars : Array String) (item : Array Val)
    (env : List (String × Val)) : List (String × Val) := Id.run do
  let mut out := env
  let last := item.back?.getD (.num 0)
  for k in [0:vars.size] do
    if h : k < vars.size then
      out := (vars[k], (item[k]?).getD last) :: out
  return out

mutual

/-- Evaluate statements in order, threading the macro environment: a
`\pgfmathsetmacro` binds for the statements after it in its own scope. -/
def evalList (cx : Cx) : List Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | [], env, ev => (env, ev)
  | s :: rest, env, ev =>
    let (env2, ev2) := evalOne cx s env ev
    evalList cx rest env2 ev2
termination_by xs _ _ => (sizeOf xs, 0)

def evalOne (cx : Cx) : Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | .fill toks, env, ev =>
    match evalFill cx env toks with
    | .ok shape => (env, { ev with shapes := ev.shapes.push shape })
    | .error d => (env, ev.diag d)
  | .node toks, env, ev => (env, evalNode cx env toks ev)
  | .set name expr trunc, env, ev =>
    match evalExpr env expr with
    | .ok (.num m) =>
      -- The truncating form floors toward zero to a whole unit, as
      -- `\pgfmathtruncatemacro` does.
      let m := if trunc then
          (if m ≥ 0 then m / 1000 * 1000 else -((-m) / 1000 * 1000))
        else m
      ((name, Val.num m) :: env, ev)
    | .ok (.str s) =>
      if trunc then
        (env, ev.diag (.E0333, s!"in '\\pgfmathtruncatemacro' of '\\{name}', '{s}' \
where a number is needed; the macro is not set"))
      else ((name, Val.str s) :: env, ev)
    | .error e =>
      (env, ev.diag (.E0333, s!"in '\\pgfmathsetmacro' of '\\{name}', {e}; the macro \
is not set"))
  | .foreach vars list body, env, ev =>
    match readItems env list with
    | .error e => (env, ev.diag (.E0333, s!"in a '\\foreach' list, {e}"))
    | .ok items =>
      match expandItems items with
      | .error e => (env, ev.diag (.E0333, s!"in a '\\foreach' list, {e}"))
      | .ok expanded =>
        -- The loop's bindings are scoped to its body: the environment
        -- given back is the caller's own.
        (env, evalForeach cx vars body expanded.toList env ev)
termination_by s _ _ => (sizeOf s, 0)

/-- One body evaluation per item: the recursion is on the item list, the
body a fixed subterm of its `\foreach`, so the unrolling is bounded by the
expanded list — which `range` bounded before any value existed. -/
def evalForeach (cx : Cx) (vars : Array String) (body : List Stmt) :
    List (Array Val) → List (String × Val) → Ev → Ev
  | [], _, ev => ev
  | item :: rest, env, ev =>
    let (_, ev2) := evalList cx body (bindVars vars item env) ev
    evalForeach cx vars body rest env ev2
termination_by items _ _ => (sizeOf body, items.length + 1)

end

/-- Elaborate one `tikzpicture` body: the leading `[scale=...]` option
block, the statements, then the unrolled evaluation. Everything the
subset cannot render is a named diagnostic beside the shapes that did. -/
def elabPicture (pal : Ir.Palette) (raws : Array Parse.Raw) :
    Ir.Pic.Picture × Array PDiag := Id.run do
  let toks := ofRaws raws
  let mut scale : Int := 1000
  let mut diags : Array PDiag := #[]
  let mut i := 0
  for _ in [0:toks.size] do
    if toks[i]? == some .space then i := i + 1 else break
  if toks[i]? == some (.sym '[') then
    let mut j := i + 1
    let mut inner : Array Tok := #[]
    for _ in [i+1:toks.size + 1] do
      if h : j < toks.size then
        if toks[j] == .sym ']' then break
        inner := inner.push toks[j]
        j := j + 1
      else break
    if toks[j]? == some (.sym ']') then
      i := j + 1
      for opt in splitTop inner ',' do
        match opt.toList.filter (· != .space) with
        | .ident "scale" :: .sym '=' :: rest =>
          match evalNum [] rest.toArray with
          | .ok m =>
            if m ≤ 0 then
              diags := diags.push (.E0333, "'scale' must be positive; it is ignored")
            else scale := m
          | .error e => diags := diags.push (.E0333, s!"in 'scale=', {e}; it is ignored")
        | [] => pure ()
        | o :: _ =>
          diags := diags.push (.W0334, s!"picture option {tokText o} is outside the \
rendered picture subset; the option is dropped")
    else
      diags := diags.push (.E0333, "the picture's options miss their ']'")
  let st := parseList (toks.toList.drop i) {}
  let cx : Cx := { pal := pal, scale := scale }
  let (_, ev) := evalList cx st.out.toList [] {}
  let all := st.bad ++ ev.diags
  -- One message, once: the parse and eval sides dedupe among themselves;
  -- this joins them under the same rule.
  let mut seen : Array String := #[]
  let mut out : Array PDiag := #[]
  for d in all do
    unless seen.contains d.2 do
      seen := seen.push d.2
      out := out.push d
  return ({ shapes := ev.shapes }, out)

end LeanTex.Core.Picture

