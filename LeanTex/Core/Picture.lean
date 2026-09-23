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
  /-- A math span (`$X$` in a node body): carried whole and elaborated by
  the hook the elaborator provides (`Cx.math`) — the picture walk owns no
  math parser. -/
  | math (display : Bool) (body : List Parse.Raw)
  /-- Source the subset cannot even tokenise into itself (a nested
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
  | .math d body _ => acc.push (.math d body.toList)
  | .env n _ _ => acc.push (.other s!"environment '{n}'")
  | .verb _ _ _ => acc.push (.other "verbatim")

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
  | .math _ _ => "math"
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
      | .math _ _ => return .error "math in an expression"
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
  | draw (toks : Array Tok)
  /-- `\pgfmathsetmacro`, and `\pgfmathtruncatemacro` when `trunc`. -/
  | set (name : String) (expr : Array Tok) (trunc : Bool)
  | foreach (vars : Array String) (list : Array Tok) (body : List Stmt)
  deriving Repr, Inhabited

/-- The `;`-terminated statement kinds the machine collects. -/
private inductive StKind where
  | fill
  | node
  | draw
  deriving Repr, BEq, Inhabited

private def StKind.name : StKind → String
  | .fill => "fill"
  | .node => "node"
  | .draw => "draw"

/-- What the statement machine is in the middle of. -/
private inductive Mode where
  | top
  /-- Collecting a `\fill`/`\node`/`\draw` statement's tokens to its `;`. -/
  | stmt (kind : StKind) (acc : Array Tok)
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
    | .ctrl "fill" => { st with mode := .stmt .fill #[] }
    | .ctrl "node" => { st with mode := .stmt .node #[] }
    | .ctrl "draw" => { st with mode := .stmt .draw #[] }
    | .ctrl "foreach" => { st with mode := .fvars #[] }
    | .ctrl "pgfmathsetmacro" => { st with mode := .sname false }
    | .ctrl "pgfmathtruncatemacro" => { st with mode := .sname true }
    | .ctrl name => { (st.outside s!"'\\{name}'") with mode := .skip }
    | .sym ';' | .space => st
    | .other what => { (st.outside what) with mode := .skip }
    | .math _ _ => { (st.outside "math") with mode := .skip }
    | .ident s => { (st.outside s!"'{s}'") with mode := .skip }
    | .num _ => { (st.outside "a bare number") with mode := .skip }
    | .sym c => { (st.outside s!"'{c}'") with mode := .skip }
    | .group _ => { (st.outside "'{...}'") with mode := .skip }
  | .stmt kind acc =>
    match t with
    | .sym ';' => st.finish (match kind with
        | .fill => .fill acc
        | .node => .node acc
        | .draw => .draw acc)
    | _ => { st with mode := .stmt kind (acc.push t) }
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
      { st with pending := st.pending.push (vars, list), mode := .stmt .fill #[] }
    | .ctrl "node" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .node #[] }
    | .ctrl "draw" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .draw #[] }
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
    | .stmt kind _ =>
      { st.diag .E0333
          s!"'\\{kind.name}' misses its ';'; the shape is not drawn"
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
it), the picture's `scale=`, per mille, the named option bundles its
`name/.style={...}` options declared, and whether `transform shape` opted
the nodes into the scale (pgf manual §25.4: transformations do not apply
to nodes unless `transform shape` is given). -/
structure Cx where
  pal : Ir.Palette
  scale : Int := 1000
  styles : List (String × Array Tok) := []
  transformShape : Bool := false
  /-- The picture-level option entries its contents inherit: what a style
  named in `\begin{tikzpicture}[...]` expanded to, already split into
  entries. Every path and node reads them before its own
  (`inheritOpts`). -/
  opts : Array (Array Tok) := #[]
  /-- What `every node/.style={...}` declared, split into entries: pgf runs
  it inside the node's own scope, so it stands between the picture's
  entries and the node's bracket (`mergeOpts`). -/
  everyNode : Array (Array Tok) := #[]
  /-- What `every path/.style={...}` declared: the same level for a path. -/
  everyPath : Array (Array Tok) := #[]
  /-- How a math span in a node body elaborates: provided by the
  elaborator, so `{$X$}` renders through the same math layer a
  paragraph's does — the picture walk owns no math parser. The result is
  the inline plus any losses the elaboration names. -/
  math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag

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

/-- A style body read once, at the definition: its entries as written, with
a reference to a bundle *already defined* spliced in place of its name.

**Expansion is at the definition, never at the use.** pgf's own model is
textual — a style's body is re-read as keys where the style is applied —
and a body that names another style would then have to be expanded again,
with no bound on the depth and no bound at all on a body that names
itself. So the splice happens here, once, and a use site expands exactly
one level whatever the nesting depth. A style that names itself, or any
cycle of styles, therefore finds nothing to splice and keeps its own name
as a literal key — which the option loop that reads it then names as a key
outside the subset (W0334), never silently dropped and never chased. No
fuel, no fixed point: the recursion does not exist. -/
def expandBody (styles : List (String × Array Tok)) (g : List Tok) :
    Array Tok := Id.run do
  let mut expanded : Array Tok := #[]
  for part in splitTop (g.toArray.filter (· != .space)) ',' do
    unless expanded.isEmpty do expanded := expanded.push (.sym ',')
    match part.toList with
    | [.ident m] =>
      match styles.lookup m with
      | some bundle => expanded := expanded ++ bundle
      | none => expanded := expanded ++ part
    | _ => expanded := expanded ++ part
  return expanded

/-- Fold one `name/.style={...}` definition into the bundles already read,
newest first, so an inner definition shadows an outer one of the same name
(pgf scopes keys; a picture's own `[...]` is inside the document's
`\tikzset`). The body is read by `expandBody`, which is where the
termination property lives. -/
def addStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  (n, expandBody styles g) :: styles

/-- Fold one `name/.append style={...}` definition in: pgf's own reading is
that the keys are *added* to the bundle of that name rather than replacing
it, so the prior body stands and the new entries follow it. Where both
bodies set a key the option loops assign — a colour, a dash, a shape — the
appended value is the one read last and stands; the `minimum` family is the
exception this subset carries, since it accumulates by maximum within one
bracket and a style body is one bracket, so appending a *smaller* minimum
leaves the larger one standing.

Termination is the same property `expandBody` has, for the same reason: the
new entries are spliced against the bundles *already defined*, once, at the
definition. Appending is one concatenation on top of that splice, so a use
site still expands exactly one level. A style appending to itself
(`a/.append style={a}`) therefore resolves the reference to the body `a`
already had — a finite array — and yields that body twice over; nothing is
chased, and the option loop reads the same keys it read before. Appending
to a name nothing defined defines it, which is the reading that applies the
keys the document asked for. -/
def appendStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  let added := expandBody styles g
  match styles.lookup n with
  | some prior =>
    if added.isEmpty then styles
    else if prior.isEmpty then (n, added) :: styles
    else (n, prior.push (.sym ',') ++ added) :: styles
  | none => (n, added) :: styles

/-- Where a declared arrow tip is kept: one bundle environment carries the
definitions, because the elaborator hands the reader one list, and a tip is
not an option bundle — so its slot is a name no key list can spell (a key
path is idents, joined by single spaces). -/
def tipKey (n : String) : String := ".tip " ++ n

/-- Fold one `name/.tip={...}` declaration in. The body is kept as written
and never re-read as keys: it is an arrow-tip construction, not an option
bundle, so there is nothing here to expand and nothing to chase. -/
def declareTip (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  (tipKey n, g.toArray) :: styles

/-- The name of the `every node` level, and of the `every path` level: the
two key paths the option loops read (pgf manual §12.4.1 — every X is
executed inside the X's own scope). -/
def everyNodeKey : String := "every node"
def everyPathKey : String := "every path"

/-- Split a token list at the first occurrence of a symbol, keeping neither
side's separator. -/
private def splitSym (c : Char) : List Tok → Option (List Tok × List Tok)
  | [] => none
  | t :: rest =>
    if t == .sym c then some ([], rest)
    else (splitSym c rest).map fun (pre, post) => (t :: pre, post)

/-- A run of idents read as one key path, joined the way pgf spells it, so
`every node` is one name and not two keys. -/
private def identPath : List Tok → Option String
  | [.ident n] => some n
  | .ident n :: rest => (identPath rest).map fun s => n ++ " " ++ s
  | _ => none

/-- A key path this reader can honour: a single word, which an option
bracket can apply by name, or one of the two `every X` levels the option
loops read. Any other path (`every label`, a two-word name no bracket can
spell) is left unread, so the line that wrote it names the loss — storing a
bundle nothing will ever look up would drop it in silence. -/
private def readableKey (n : String) : Bool :=
  n == everyNodeKey || n == everyPathKey || !n.contains ' '

/-- One definition entry as a key path, a handler name, and the handler's
group: `every node/.style={draw}` reads as `every node`, `style`, `draw`. -/
private def readDef (entry : List Tok) : Option (String × String × List Tok) := do
  let (path, rest) ← splitSym '/' entry
  let name ← identPath path
  match rest with
  | .sym '.' :: hrest =>
    let (hpath, body) ← splitSym '=' hrest
    let handler ← identPath hpath
    match body with
    | [.group g] => some (name, handler, g)
    | _ => none
  | _ => none

/-- Fold one definition entry into the bundles, or refuse it: `none` where
the entry is not a definition at all, or names a handler or a key path
outside the subset. The one router both a document's `\tikzset` and a
picture's own bracket go through, so the two cannot differ about what a
definition means. -/
def readOneDef (styles : List (String × Array Tok)) (entry : List Tok) :
    Option (List (String × Array Tok)) :=
  match readDef entry with
  | some (n, "style", g) =>
    if readableKey n then some (addStyle styles n g) else none
  | some (n, "append style", g) =>
    if readableKey n then some (appendStyle styles n g) else none
  | some (n, "tip", g) =>
    if readableKey n then some (declareTip styles n g) else none
  | _ => none

/-- The tip name an arrow spec ends in, where the spec is one this subset
draws: `-name`, `-{name}`, or `->`. A declared tip draws the engine's own
arrow head, the way `latex` already does — pgf manual §16 names many tip
kinds and this subset has one head to draw them with, so the substitution
is the established one, not a new claim. -/
def tipName : List Tok → Option String
  | [.group g] => identPath (g.filter (· != .space))
  | ts => identPath ts

def arrowTipName : List Tok → Option String
  | [.sym '-', .sym '>'] => some ">"
  | [.sym '-', t] => tipName [t]
  | _ => none

/-- Does a name draw as this subset's arrow head? A tip the document
declared with `/.tip`, or one of the two built-in kinds the plain head has
always stood in for (`latex`, pgf manual §16.3; `>` is the shorthand
itself). Anything else stays outside the subset and is named. -/
def drawsAsArrow (styles : List (String × Array Tok)) (n : String) : Bool :=
  n == ">" || n == "latex" || (styles.lookup (tipKey n)).isSome

/-- Read a `\tikzset` key list: every definition entry this reader knows
folds into the bundles, in source order so a later definition may name an
earlier one. Every other entry comes back unread — `/.tip`, `/.append
style`, a bare key — for the caller to name at the line that wrote it,
which is where such a diagnostic belongs: the line is the document's, not
any one picture's. -/
def readStyleList (styles : List (String × Array Tok)) (toks : Array Tok) :
    List (String × Array Tok) × Array (Array Tok) := Id.run do
  let mut styles := styles
  let mut unread : Array (Array Tok) := #[]
  for entry in splitTop toks ',' do
    let e := entry.toList.filter (· != .space)
    match readOneDef styles e with
    | some s => styles := s
    | none =>
      match e with
      | [] => pure ()
      | other => unread := unread.push other.toArray
  return (styles, unread)

/-- The bundles a document's `\tikzset` lines define, folded in source
order: what every picture in it starts from. -/
def documentStyles (sets : Array (Array Tok)) : List (String × Array Tok) := Id.run do
  let mut styles : List (String × Array Tok) := []
  for keys in sets do
    styles := (readStyleList styles keys).1
  return styles

/-- What one `\tikzset` key list leaves unread, named for a diagnostic at
the line that wrote it. The elaborator's one caller; the fold the pictures
read is `documentStyles`. -/
def unreadKeys (styles : List (String × Array Tok)) (keys : Array Tok) : Array String :=
  (readStyleList styles keys).2.filterMap fun e => (e[0]?).map tokText

/-- Split an option bracket into entries and expand a declared bundle's
name one level into the bundle's own entries. One level is all a use site
needs: `addStyle` spliced any nested bundle in at the definition. -/
def expandOpts (styles : List (String × Array Tok)) (inner : Array Tok) :
    Array (Array Tok) := Id.run do
  let mut opts : Array (Array Tok) := #[]
  for opt in splitTop (inner.filter (· != .space)) ',' do
    match opt.toList with
    | [.ident n] =>
      match styles.lookup n with
      | some bundle => opts := opts ++ splitTop bundle ','
      | none => opts := opts.push opt
    | _ => opts := opts.push opt
  return opts

/-- The key an option entry sets: its tokens up to the `=`, so `draw` and
`draw=red` name one key as they do in pgf, and `minimum size=8mm` names
`minimum size`. -/
def optKey (opt : Array Tok) : String := Id.run do
  let mut s := ""
  for t in opt do
    if t == .sym '=' then break
    unless t == .space do s := s ++ tokText t
  return s

/-- Merge the picture's inherited entries with a path's or node's own.

**The inner setting wins, exactly.** The inherited entries come first, and
an inherited entry whose key the inner bracket also names is dropped
rather than merely overwritten — so `\begin{tikzpicture}[thin]` with
`\draw[thick]` strokes thick, pgf's rule, and it holds for every key
including those this subset accumulates rather than assigns: a `minimum
size` takes a maximum *within* one bracket, so an inherited one left in
place would beat a smaller inner one. Keys whose names differ compose
exactly as they would written in one bracket, the picture's first.

The two facts are `inherit_inner_exact` and `inherit_covers`; they are of
this reader, not of either artifact, because a picture's keys are consumed
here and never reach the IR. -/
def inheritOpts (outer inner : Array (Array Tok)) : Array (Array Tok) :=
  let names := inner.map optKey
  outer.filter (fun o => !names.contains (optKey o)) ++ inner

/-- Precedence: an entry in the merge whose key some inner entry also names
is the inner bracket's own. -/
theorem inherit_inner_exact {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner)
    (hk : ∃ e ∈ inner, optKey e = optKey o) : o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨_, hp⟩ | h
  · obtain ⟨e, he, hek⟩ := hk
    simp at hp
    exact absurd hek (hp e he)
  · exact h

/-- Nothing the inner bracket said is lost to the merge. -/
theorem inherit_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ inner) : o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append]
  exact Or.inr h

/-- The merge invents nothing: every entry came from one of the two sides. -/
theorem inherit_mem {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner) : o ∈ outer ∨ o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨h, _⟩ | h
  · exact Or.inl h
  · exact Or.inr h

/-- The three levels one bracket's entries are read under, outermost first.

**picture < every X < the bracket's own.** pgf sets a picture's keys in the
picture's scope; an `every node`/`every path` style is executed inside the
node's or path's own scope, which is *inside* the picture's; and the
bracket's own keys are read there too, after it. So `every X` beats what the
picture set and loses to what the X itself says — and because each level is
an `inheritOpts`, a key a later level names is *dropped* from the earlier
one rather than merely preceded by it: the `minimum` family accumulates by
maximum within one bracket, so a surviving outer `minimum size=9mm` would
beat an inner `4mm` and draw the opposite of what the document says.

`merge_own_exact` and `merge_every_exact` are the two boundaries,
`merge_covers` that nothing the bracket said is lost. -/
def mergeOpts (picture every own : Array (Array Tok)) : Array (Array Tok) :=
  inheritOpts (inheritOpts picture every) own

/-- Precedence, innermost level: an entry whose key the bracket's own also
names is the bracket's own. -/
theorem merge_own_exact {picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts picture every own)
    (hk : ∃ e ∈ own, optKey e = optKey o) : o ∈ own :=
  inherit_inner_exact hm hk

/-- Precedence, middle level: an entry whose key `every X` names and the
bracket's own does not is the `every X` style's. -/
theorem merge_every_exact {picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts picture every own)
    (hk : ∃ e ∈ every, optKey e = optKey o)
    (ho : ¬ ∃ e ∈ own, optKey e = optKey o) : o ∈ every := by
  rcases inherit_mem hm with h | h
  · exact inherit_inner_exact h hk
  · exact absurd ⟨o, h, rfl⟩ ho

/-- Nothing the bracket's own entries said is lost to either level. -/
theorem merge_covers {picture every own : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ own) : o ∈ mergeOpts picture every own :=
  inherit_covers h

/-- Nothing the outer level said is lost where no inner entry names its
key: the level survives the filter, not only the append. -/
theorem inherit_outer_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ outer) (hk : ∀ e ∈ inner, optKey e ≠ optKey o) :
    o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter]
  refine Or.inl ⟨h, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Array.contains_eq_mem,
    decide_eq_false_iff_not, Array.mem_map, not_exists, not_and]
  exact fun e he => hk e he

/-- Precedence, outermost level: what the picture set reaches the merge
where neither later level names its key. Without this the picture's entries
could be dropped wholesale and the two boundary facts would still hold. -/
theorem merge_picture_covers {picture every own : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ picture) (he : ∀ e ∈ every, optKey e ≠ optKey o)
    (ho : ∀ e ∈ own, optKey e ≠ optKey o) :
    o ∈ mergeOpts picture every own :=
  inherit_outer_covers (inherit_outer_covers h he) ho

/-- A picture-level key outside the subset, named at the bracket that
wrote it. -/
private def outsideOpt (o : Tok) : PDiag :=
  (.W0334, s!"picture option {tokText o} is outside the \
rendered picture subset; the option is dropped")

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

-- Border anchoring: where an edge meets a node's outline — pgf's
-- `\pgfpointshapeborder`, in closed form per shape.

/-- Integer square root of an `Int` (callers pass sums of squares). -/
def isqrt (n : Int) : Int := (Nat.sqrt n.toNat : Nat)

/-- Where the ray from a rectangle's centre `(cx, cy)` (half-extents
`a`, `b`) toward `(qx, qy)` crosses its border — `\pgfpointshapeborder`
for the rectangle shape (pgf manual, Nodes and Shapes), as algebra: the
dominant axis (`|dy|·a ≤ |dx|·b`) decides which edge, that coordinate is
exact, and the other rounds one exact rational (`rectBorder_exact`). A
ray with no direction answers the centre. -/
def rectBorder (cx cy a b qx qy : Int) : Int × Int :=
  let dx := qx - cx
  let dy := qy - cy
  let adx : Int := dx.natAbs
  let ady : Int := dy.natAbs
  if dx = 0 ∧ dy = 0 then (cx, cy)
  else if ady * a ≤ adx * b then
    ((if dx > 0 then cx + a else cx - a), cy + dy * a / adx)
  else
    (cx + dx * b / ady, if dy > 0 then cy + b else cy - b)

/-- Division bound: `x ≤ c·q` gives `x/c ≤ q` (positive `c`). -/
private theorem ediv_le_of_le_mul {x c q : Int} (hc : 0 < c) (h : x ≤ c * q) :
    x / c ≤ q := by
  have h2 := Int.ediv_le_ediv hc h
  rwa [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hc)] at h2

/-- Division bound: `c·q ≤ x` gives `q ≤ x/c` (positive `c`). -/
private theorem le_ediv_of_mul_le {x c q : Int} (hc : 0 < c) (h : c * q ≤ x) :
    q ≤ x / c := by
  have h2 := Int.ediv_le_ediv hc h
  rwa [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hc)] at h2

/-- An edge between two nodes starts and ends on their borders — the
rectangle half: the anchor lands **on** the border (the dominant
coordinate sits exactly on an edge; a directionless ray answers the
centre) and never outside it (both coordinates stay within the
extents). Sourced at `rectBorder`; the one division is exact on the
dominant axis and a single rounding on the other. -/
theorem rectBorder_exact (cx cy a b qx qy : Int) (ha : 0 < a) (hb : 0 < b) :
    ((rectBorder cx cy a b qx qy).1 = cx - a ∨ (rectBorder cx cy a b qx qy).1 = cx + a ∨
     (rectBorder cx cy a b qx qy).2 = cy - b ∨ (rectBorder cx cy a b qx qy).2 = cy + b ∨
     (qx = cx ∧ qy = cy)) ∧
    cx - a ≤ (rectBorder cx cy a b qx qy).1 ∧ (rectBorder cx cy a b qx qy).1 ≤ cx + a ∧
    cy - b ≤ (rectBorder cx cy a b qx qy).2 ∧ (rectBorder cx cy a b qx qy).2 ≤ cy + b := by
  simp only [rectBorder]
  split
  · next hz =>
    dsimp only
    exact ⟨.inr (.inr (.inr (.inr (by omega)))), by omega, by omega, by omega, by omega⟩
  · next hz =>
    split
    · next hle =>
      dsimp only
      -- The vertical-edge branch: dx ≠ 0 (a zero dx with a nonzero dy
      -- fails the branch test, since ady·a ≥ a > 0).
      have hdx : qx - cx ≠ 0 := by
        intro h0
        rw [h0] at hle
        simp only [Int.natAbs_zero, Int.natCast_zero, Int.zero_mul] at hle
        have h1 : (1 : Int) * a ≤ ((qy - cy).natAbs : Int) * a :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        rw [Int.one_mul] at h1
        omega
      have hpos : (0 : Int) < ((qx - cx).natAbs : Int) := by omega
      have hup : (qy - cy) * a ≤ ((qx - cx).natAbs : Int) * b := by
        have h1 : (qy - cy) * a ≤ ((qy - cy).natAbs : Int) * a :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        omega
      have hlo : ((qx - cx).natAbs : Int) * (-b) ≤ (qy - cy) * a := by
        have h1 : (-(qy - cy)) * a ≤ ((qy - cy).natAbs : Int) * a :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        have h2 : ((qx - cx).natAbs : Int) * (-b)
            = -(((qx - cx).natAbs : Int) * b) := by
          rw [Int.mul_neg]
        rw [Int.neg_mul] at h1
        omega
      have hy1 := ediv_le_of_le_mul hpos hup
      have hy2 := le_ediv_of_mul_le hpos hlo
      constructor
      · split
        · exact .inr (.inl rfl)
        · exact .inl rfl
      · refine ⟨?_, ?_, by omega, by omega⟩ <;> split <;> omega
    · next hgt =>
      dsimp only
      -- The horizontal-edge branch: dy ≠ 0 (both-zero was the first
      -- branch, and dy = 0 with dx ≠ 0 satisfies the vertical test).
      have hdy : qy - cy ≠ 0 := by
        intro h0
        rw [h0] at hgt
        simp only [Int.natAbs_zero, Int.natCast_zero, Int.zero_mul] at hgt
        have h1 : (0 : Int) ≤ ((qx - cx).natAbs : Int) * b :=
          Int.mul_nonneg (by omega) (by omega)
        omega
      have hpos : (0 : Int) < ((qy - cy).natAbs : Int) := by omega
      have hup : (qx - cx) * b ≤ ((qy - cy).natAbs : Int) * a := by
        have h1 : (qx - cx) * b ≤ ((qx - cx).natAbs : Int) * b :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        omega
      have hlo : ((qy - cy).natAbs : Int) * (-a) ≤ (qx - cx) * b := by
        have h1 : (-(qx - cx)) * b ≤ ((qx - cx).natAbs : Int) * b :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        have h2 : ((qy - cy).natAbs : Int) * (-a)
            = -(((qy - cy).natAbs : Int) * a) := by
          rw [Int.mul_neg]
        rw [Int.neg_mul] at h1
        omega
      have hx1 := ediv_le_of_le_mul hpos hup
      have hx2 := le_ediv_of_mul_le hpos hlo
      constructor
      · split
        · exact .inr (.inr (.inr (.inl rfl)))
        · exact .inr (.inr (.inl rfl))
      · refine ⟨by omega, by omega, ?_, ?_⟩ <;> split <;> omega

/-- Where the ray from a circle's centre toward `(qx, qy)` meets its
border: `c + r·d/‖d‖`, the normalisation through one integer square
root — `\pgfpointshapeborder` for the circle shape. A ray with no
direction answers the centre. -/
def circleBorder (cx cy r qx qy : Int) : Int × Int :=
  let dx := qx - cx
  let dy := qy - cy
  let n := isqrt (dx * dx + dy * dy)
  if n = 0 then (cx, cy)
  else (cx + r * dx / n, cy + r * dy / n)

/-- An edge between two nodes starts and ends on their borders — the
circle half, stated as the rounding bound it is (not `_exact`, said at
review): each component of `p − c` is the exact rational `r·d_i/‖d‖`
rounded once (within one `n`-th, where `n = ⌊√‖d‖²⌋` and
`n² ≤ ‖d‖² < (n+1)²`), so the anchor misses `‖p − c‖ = r` by at most one
sp per axis plus the square root's own step. The squared-distance
corollary follows by squaring these bounds; that squaring is nonlinear
algebra the statement deliberately stops short of — the per-axis bound
is what the renderer's ±1 sp claim rests on. -/
theorem circleBorder_step (cx cy r qx qy : Int)
    (hn : isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) ≠ 0) :
    isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
        * ((circleBorder cx cy r qx qy).1 - cx) ≤ r * (qx - cx) ∧
    r * (qx - cx) < isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
        * ((circleBorder cx cy r qx qy).1 - cx)
      + isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) ∧
    isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
        * ((circleBorder cx cy r qx qy).2 - cy) ≤ r * (qy - cy) ∧
    r * (qy - cy) < isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
        * ((circleBorder cx cy r qx qy).2 - cy)
      + isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) ∧
    isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
        * isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
      ≤ (qx - cx) * (qx - cx) + (qy - cy) * (qy - cy) := by
  have h0 : 0 ≤ isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) := by
    unfold isqrt
    omega
  have hpos : 0 < isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) := by
    omega
  have hp : circleBorder cx cy r qx qy
      = (cx + r * (qx - cx) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)),
         cy + r * (qy - cy) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))) := by
    simp only [circleBorder]
    split
    · next h => exact absurd h hn
    · rfl
  have hsq : isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
      * isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
      ≤ (qx - cx) * (qx - cx) + (qy - cy) * (qy - cy) := by
    have h1 := Int.natAbs_mul_self (a := qx - cx)
    have h2 := Int.natAbs_mul_self (a := qy - cy)
    have hs := Nat.sqrt_le ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)).toNat
    unfold isqrt
    rw [← Int.natCast_mul]
    omega
  have hx := Int.emod_def (r * (qx - cx))
    (isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)))
  have hxm := Int.emod_nonneg (r * (qx - cx)) (by omega :
    isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) ≠ 0)
  have hxl := Int.emod_lt_of_pos (r * (qx - cx)) hpos
  have hy := Int.emod_def (r * (qy - cy))
    (isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)))
  have hym := Int.emod_nonneg (r * (qy - cy)) (by omega :
    isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) ≠ 0)
  have hyl := Int.emod_lt_of_pos (r * (qy - cy)) hpos
  rw [hp]
  dsimp only
  have e1 : cx + r * (qx - cx) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
      - cx = r * (qx - cx) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) := by
    omega
  have e2 : cy + r * (qy - cy) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy))
      - cy = r * (qy - cy) / isqrt ((qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)) := by
    omega
  rw [e1, e2]
  exact ⟨by omega, by omega, by omega, by omega, hsq⟩

/-- A named node's anchoring geometry: centre and border half-extents (a
circle's radius twice). What an edge's `(name)` endpoint resolves to. -/
structure NodeGeom where
  x : Sp
  y : Sp
  a : Sp := 0
  b : Sp := 0
  circle : Bool := false
  deriving Repr, BEq, Inhabited

/-- Shapes and named losses, accumulated across the unrolled walk. A
diagnostic dedupes on its message: one construct looped over forty times
is one problem, not forty. -/
structure Ev where
  shapes : Array Ir.Pic.Shape := #[]
  diags : Array PDiag := #[]
  /-- Named nodes seen so far, latest first: what a `\draw` endpoint's
  `(name)` resolves against. -/
  nodes : List (String × NodeGeom) := []
  /-- Did some path or node read the picture's inherited options? If
  nothing did, the picture's own bracket names them rather than dropping
  them: `\fill`'s bracket is a colour spelling, not a key list, so a
  picture of nothing but fills reads no keys at all. -/
  readOpts : Bool := false

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

/-- A node body's content: words, numbers, and bound macros become text,
a math span elaborates through `Cx.math`; anything else is outside the
subset and names itself. Leading and trailing space trims, as the braces'
inner space does in TeX. -/
private def contentOf (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    Except String (Array Ir.Inline × Array PDiag) := Id.run do
  let mut out : Array Ir.Inline := #[]
  let mut diags : Array PDiag := #[]
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
    | .math d body =>
      unless s.isEmpty do
        out := out.push (.text s)
        s := ""
      let (inl, ds) := cx.math d body.toArray
      out := out.push inl
      diags := diags ++ ds
    | t => return .error (tokText t)
  unless s.isEmpty do
    out := out.push (.text s)
  let trimL (s : String) : String := String.ofList (s.toList.dropWhile (· == ' '))
  let trimR (s : String) : String :=
    String.ofList ((s.toList.reverse.dropWhile (· == ' ')).reverse)
  let n := out.size
  out := out.mapIdx fun i inl =>
    if let .text f := inl then
      .text (if i + 1 == n then trimR (if i == 0 then trimL f else f)
             else if i == 0 then trimL f else f)
    else inl
  return .ok (out.filter (· != .text ""), diags)

/-- A dimension literal in a node option (`8mm`, `2pt`), in sp. Only the
physical units: a font-relative unit (`em`, `ex`) needs the node's face,
which is layout's question, so it stays outside the subset by name. -/
private def readDim (toks : List Tok) : Except String Sp :=
  match toks with
  | [.num m, .ident u] =>
    match u with
    | "mm" => .ok (m * Dim.mm 10 / 10000)
    | "cm" => .ok (m * Dim.mm 10 / 1000)
    | "pt" => .ok (m * Dim.pt 1 / 1000)
    | "in" => .ok (m * Dim.inch 1 / 1000)
    | u => .error s!"the unit '{u}' is outside the rendered picture subset"
  | _ => .error "a length like '8mm' is needed"

/-- `\node[circle, draw, minimum size=8mm] at (x,y) {$X$};` — a centred
label, its optional outline, optionally named (`\node (u) at ...`; the
name is parsed and dropped: only an edge could consume it, and edges are
outside the subset). An option outside the subset loses only itself
(named); a node without `at` or a readable body loses the node. An option
naming a declared style bundle expands to the bundle's own options, so a
loss inside a bundle is named by its real spelling, never by the
bundle's. -/
private def evalNode (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) : Ev := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut color := Ir.Color.black
  -- `transform shape` opts the node into the picture's scale (pgf manual
  -- §25.4); `font=` then sets its size relative to that.
  let factor : Nat := if cx.transformShape && cx.scale > 0 then cx.scale.toNat else 1000
  let mut scale : Nat := factor
  let mut ev := ev
  -- The node's outline, gathered from its options: shape kind (pgf's
  -- default node shape is a rectangle), whether it draws and/or fills,
  -- how it strokes, and the declared minimum extents.
  let mut isCircle := false
  let mut draw : Option (Option Ir.Color) := none
  let mut fillCol : Option Ir.Color := none
  let mut dash : Ir.Pic.Dash := .solid
  let mut thick := false
  let mut minW : Sp := 0
  let mut minH : Sp := 0
  let mut own : Array (Array Tok) := #[]
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
    own := expandOpts cx.styles inner
    i := j + 1
  ev := { ev with readOpts := true }
  for opt in mergeOpts cx.opts cx.everyNode own do
    match opt.toList with
    | .ident "font" :: .sym '=' :: .ctrl size :: [] =>
      match Ir.sizeScale.lookup size with
      | some k => scale := k * factor / 1000
      | none =>
        ev := ev.diag (.W0334, s!"node option 'font=\\{size}' is outside the \
rendered picture subset; the option is dropped")
    | .ident "text" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => color := c
      | .error e => ev := ev.diag (.E0333, s!"in '\\node', {e}; the colour is dropped")
    | [.ident "circle"] => isCircle := true
    | [.ident "rectangle"] => isCircle := false
    | [.ident "draw"] => draw := some none
    | .ident "draw" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => draw := some (some c)
      | .error e => ev := ev.diag (.E0333, s!"in '\\node', {e}; the colour is dropped")
    | .ident "fill" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => fillCol := some c
      | .error e => ev := ev.diag (.E0333, s!"in '\\node', {e}; the colour is dropped")
    | [.ident "dashed"] => dash := .dashed
    | [.ident "dotted"] | [.ident "densely", .ident "dotted"] => dash := .dotted
    | [.ident "thick"] => thick := true
    | .ident "minimum" :: .ident "size" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => minW := max minW d; minH := max minH d
      | .error e => ev := ev.diag (.W0334, s!"in 'minimum size', {e}; the option \
is dropped")
    | .ident "minimum" :: .ident "width" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => minW := max minW d
      | .error e => ev := ev.diag (.W0334, s!"in 'minimum width', {e}; the option \
is dropped")
    | .ident "minimum" :: .ident "height" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => minH := max minH d
      | .error e => ev := ev.diag (.W0334, s!"in 'minimum height', {e}; the option \
is dropped")
    -- `inner sep` is inert under minimum-only sizing: the outline is the
    -- declared minimum (see the emission note below), which already
    -- dominates the body plus its sep in the class this subset renders.
    | .ident "inner" :: .ident "sep" :: .sym '=' :: _ => pure ()
    | [] => pure ()
    | o :: _ =>
      ev := ev.diag (.W0334, s!"node option {tokText o} is outside the rendered \
picture subset; the option is dropped")
  -- A `(name)` before `at` names the node for edges to reference. It is
  -- recognised only when `at` follows, so a coordinate standing where the
  -- name would does not read as one.
  let mut nodeName : Option String := none
  if ts[i]? == some (.sym '(') then
    let mut j := i + 1
    let mut nm := ""
    for _ in [i+1:ts.size + 1] do
      if h : j < ts.size then
        if ts[j] == .sym ')' || ts[j] == .sym '(' then break
        nm := nm ++ (match ts[j] with
          | .ident s => s
          | .num m => milliString m
          | .sym c => String.singleton c
          | _ => "")
        j := j + 1
      else break
    if ts[j]? == some (.sym ')') && ts[j+1]? == some (.ident "at") then
      i := j + 1
      nodeName := some nm
  unless ts[i]? == some (.ident "at") do
    return ev.diag (.W0334, "a '\\node' without 'at (x, y)' is outside the rendered \
picture subset; the node is not drawn")
  i := i + 1
  match readCoord ts i with
  | .error e => return ev.diag (.E0333, s!"in '\\node', {e}; the node is not drawn")
  | .ok ((xs, ys), i2) =>
    match ts[i2]? with
    | some (.group body) =>
      match evalNum env xs, evalNum env ys, contentOf cx env body with
      | .ok xm, .ok ym, .ok (content, mdiags) =>
        if h : i2 + 1 < ts.size then
          return ev.diag (.W0334, s!"'\\node' continues with {tokText ts[i2+1]}, \
outside the rendered picture subset; the node is not drawn")
        ev := mdiags.foldl Ev.diag ev
        let sx := cx.toSp xm
        let sy := cx.toSp ym
        let dimF (d : Sp) : Sp :=
          if cx.transformShape then d * cx.scale / 1000 else d
        -- A named node registers its anchoring geometry whether or not
        -- its border draws: pgf anchors edges on the shape's border even
        -- when the path itself is never painted.
        if let some nm := nodeName then
          let geom : NodeGeom :=
            if isCircle then
              let r := dimF (max minW minH) / 2
              { x := sx, y := sy, a := r, b := r, circle := true }
            else
              { x := sx, y := sy, a := dimF minW / 2, b := dimF minH / 2 }
          ev := { ev with nodes := (nm, geom) :: ev.nodes }
        -- The node's outline, before its label so the fill paints under
        -- the text. Extent is the declared minimum: pgf manual §"Shapes"
        -- has extent = max(minimum, text extent + 2·inner sep) per axis,
        -- and the minimum is the whole answer when it dominates the
        -- body — the case this subset renders; a body wider than its
        -- declared minimum stands proud of the border. pgf draws a
        -- node's path only when `draw` or `fill` asks it to. Minimums
        -- scale with the picture only under `transform shape` (§25.4);
        -- the line width is graphic state and never scales.
        if draw.isSome || fillCol.isSome then
          let stroke : Option Ir.Pic.Stroke := draw.map fun c =>
            { color := c.getD Ir.Color.black
              width := if thick then Ir.Pic.thickWidth else Ir.Pic.thinWidth
              dash := dash }
          if isCircle then
            let r := dimF (max minW minH) / 2
            if r > 0 then
              ev := { ev with shapes := ev.shapes.push (.circle sx sy r stroke fillCol) }
            else
              ev := ev.diag (.W0334, "a drawn 'circle' without a 'minimum size' \
is outside the rendered picture subset (the body's own extent is not measured \
here); its outline is not drawn")
          else
            let w := dimF minW
            let h := dimF minH
            if w > 0 && h > 0 then
              let fr := Ir.Pic.Shape.frame (sx - w / 2) (sy - h / 2) w h stroke fillCol
              ev := { ev with shapes := ev.shapes.push fr }
            else
              ev := ev.diag (.W0334, "a drawn node without 'minimum width' and \
'minimum height' (or 'minimum size') is outside the rendered picture subset \
(the body's own extent is not measured here); its outline is not drawn")
        let shape := Ir.Pic.Shape.label sx sy content color scale .center
        return { ev with shapes := ev.shapes.push shape }
      | .error e, _, _ | _, .error e, _ =>
        return ev.diag (.E0333, s!"in '\\node', {e}; the node is not drawn")
      | _, _, .error e =>
        return ev.diag (.W0334, s!"{e} in a node body is outside the rendered \
picture subset; the node is not drawn")
    | _ =>
      return ev.diag (.E0333, "'\\node' needs a '{text}' body; the node is not drawn")

/-- Sine of whole degrees 0–90 in milli, ⌊1000·sin d° + ½⌋: what the
`to[out=, in=]` control points read. Any integer degree folds in by the
circle's symmetries (`sinDeg`); whole-degree milli precision is below
one part in two thousand of any control distance. -/
private def sinTable : Array Int :=
  #[0, 17, 35, 52, 70, 87, 105, 122, 139, 156, 174, 191, 208, 225, 242,
    259, 276, 292, 309, 326, 342, 358, 375, 391, 407, 423, 438, 454, 469,
    485, 500, 515, 530, 545, 559, 574, 588, 602, 616, 629, 643, 656, 669,
    682, 695, 707, 719, 731, 743, 755, 766, 777, 788, 799, 809, 819, 829,
    839, 848, 857, 866, 875, 883, 891, 899, 906, 914, 921, 927, 934, 940,
    946, 951, 956, 961, 966, 970, 974, 978, 982, 985, 988, 990, 993, 995,
    996, 998, 999, 999, 1000, 1000]

private def sinDeg (d : Int) : Int :=
  let d := ((d % 360) + 360) % 360
  let (sign, d) := if d ≤ 180 then ((1 : Int), d) else (-1, d - 180)
  let d := if d ≤ 90 then d else 180 - d
  sign * ((sinTable[d.toNat]?).getD 0)

private def cosDeg (d : Int) : Int := sinDeg (d + 90)

/-- An endpoint of a `\draw` path: a named node, whose border anchors the
segment, or a bare coordinate. -/
private inductive Anchor where
  | node (g : NodeGeom)
  | point (x y : Sp)

private def Anchor.center : Anchor → Sp × Sp
  | .node g => (g.x, g.y)
  | .point x y => (x, y)

/-- Where a segment toward `q` leaves this anchor: the border for a node
with extents (`circleBorder`/`rectBorder`), the point itself otherwise. -/
private def Anchor.toward (a : Anchor) (q : Sp × Sp) : Sp × Sp :=
  match a with
  | .point x y => (x, y)
  | .node g =>
    if g.a ≤ 0 || g.b ≤ 0 then (g.x, g.y)
    else if g.circle then circleBorder g.x g.y g.a q.1 q.2
    else rectBorder g.x g.y g.a g.b q.1 q.2

/-- The `latex`/`->` arrow tip as a filled triangle, plus the point the
stroked line shortens to. Extents are pgf's own declaration
(pgflibraryarrows, the `latex` tip): the unit is 0.28 pt + 0.3·line
width, the apex 9 units ahead of the anchor with the back corners 3
behind at ±3.75 — drawn tip 12 units long; the straight sides stand in
for the declared curved outline, a stated approximation. -/
private def tipAt (x y dx dy width : Sp) : Option (Ir.Pic.Tip × Sp × Sp) :=
  let n := isqrt (dx * dx + dy * dy)
  if n == 0 then none
  else
    let unitA := Dim.pt 28 / 100 + width * 3 / 10
    let len := 12 * unitA
    let half := unitA * 15 / 4
    let bx := x - len * dx / n
    let byy := y - len * dy / n
    let ox := (-dy) * half / n
    let oy := dx * half / n
    some ({ x1 := x, y1 := y
            x2 := bx + ox, y2 := byy + oy
            x3 := bx - ox, y3 := byy - oy }, bx, byy)

/-- Where a segment leaving in direction `deg` (degrees) exits this
anchor: the border along the declared tangent, for a node with extents. -/
private def Anchor.towardDir (a : Anchor) (deg : Int) : Sp × Sp :=
  let c := a.center
  a.toward (c.1 + cosDeg deg, c.2 + sinDeg deg)

/-- A `to[out=α, in=β]` control point: `dist` along the declared angle
`deg` from the endpoint — the To-Path library's rule (pgf manual, "To
Paths": control points sit on the departure and arrival tangents). The
angle reads the milli sine table, one rounding division per axis. -/
private def curveControl (px py dist deg : Int) : Int × Int :=
  (px + dist * cosDeg deg / 1000, py + dist * sinDeg deg / 1000)

/-- The curve leaves and arrives along its declared angles: a cubic
Bézier's endpoint tangents are its control offsets — `B′(0) = 3(c₁ − p)`
and `B′(1) = 3(q − c₂)`, the derivative of the ISO 32000-2 §8.5.2.2
(PDF `c`) / SVG `C` cubic — and the offset `curveControl` builds is
`dist·(cos deg, sin deg)` in milli, each axis rounded once (within one
thousandth of `dist`, under the sine table's own stated precision).
One statement covers both ends: `evalDraw` builds `c₂` from the arrival
point by the same function, the in-angle pointing back along the
arrival tangent as pgf's `in=` does. The endpoints themselves anchor on
node borders through `Anchor.towardDir`, which is `rectBorder_exact` /
`circleBorder_step` — reused, not restated. Rounding-bound shape, as
`circleBorder_step` (said at review). -/
private theorem curveControl_tangent (px py dist deg : Int) :
    1000 * ((curveControl px py dist deg).1 - px) ≤ dist * cosDeg deg ∧
    dist * cosDeg deg < 1000 * ((curveControl px py dist deg).1 - px) + 1000 ∧
    1000 * ((curveControl px py dist deg).2 - py) ≤ dist * sinDeg deg ∧
    dist * sinDeg deg < 1000 * ((curveControl px py dist deg).2 - py) + 1000 := by
  simp only [curveControl]
  generalize dist * cosDeg deg = d
  generalize dist * sinDeg deg = e
  omega

/-- One path operation between two endpoints: pgf manual §14.13 (to
paths) — `--` and a bare `to` are the straight line, `to[out=α, in=β]`
the cubic whose control points sit 0.3915·‖d‖ along the departure and
arrival tangents (the To-Path library's own factor, at looseness 1). -/
private inductive DrawOp where
  | straight
  | curve (outA inA : Int)

/-- `\draw[opts] (a) -- (b) to[out=α,in=β] (c) ...;` — a stroked edge
chain between named nodes and coordinates, border-anchored at named
endpoints (along the declared tangent for a curve). Options: `thick`,
`dashed`/`dotted` (and the densely form), an arrow spec (`->`/`-latex`,
both the triangle tip), a colour, and declared style bundles; an in-path
`node[...] {...}` is an edge label at the segment's midpoint. Anything
else outside the subset loses only itself where an option, and the edge
by name where a path operation. -/
private def evalDraw (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) : Ev := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut ev := ev
  let mut color := Ir.Color.black
  let mut dash : Ir.Pic.Dash := .solid
  let mut thick := false
  let mut arrow := false
  let mut own : Array (Array Tok) := #[]
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
      return ev.diag (.E0333, "'\\draw' options miss their ']'; the edge is not drawn")
    own := expandOpts cx.styles inner
    i := j + 1
  ev := { ev with readOpts := true }
  for opt in mergeOpts cx.opts cx.everyPath own do
    match arrowTipName opt.toList with
    | some tip =>
      if drawsAsArrow cx.styles tip then arrow := true
      else
        ev := ev.diag (.W0334, s!"arrow tip '{tip}' is outside the rendered \
picture subset; the edge is drawn without a head")
    | none =>
    match opt.toList with
    | [.ident "thick"] => thick := true
    | [.ident "dashed"] => dash := .dashed
    | [.ident "dotted"] | [.ident "densely", .ident "dotted"] => dash := .dotted
    -- `>=<tip>` names which head the `->` shorthand draws; a declared tip
    -- draws this subset's own head, so the key changes no shape here.
    | .sym '>' :: .sym '=' :: rest =>
      match tipName rest with
      | some tip =>
        unless drawsAsArrow cx.styles tip do
          ev := ev.diag (.W0334, s!"arrow tip '{tip}' is outside the rendered \
picture subset; the edge is drawn without a head")
      | none =>
        ev := ev.diag (.W0334, "'>=' without a tip name is outside the rendered \
picture subset; the option is dropped")
    -- `draw=<colour>` and a bare colour both set the stroke, as in pgf
    | .ident "draw" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => color := c
      | .error e =>
        ev := ev.diag (.E0333, s!"in '\\draw', {e}; the colour is dropped")
    | [] => pure ()
    | o :: rest =>
      -- A remaining option is a colour spelling, or names itself.
      match evalColor cx env opt with
      | .ok c => color := c
      | .error _ =>
        let _ := rest
        ev := ev.diag (.W0334, s!"draw option {tokText o} is outside the \
rendered picture subset; the option is dropped")
  -- The endpoint chain: `(name|x,y)` separated by `--`.
  let readAnchor (i : Nat) : Except PDiag (Anchor × Nat) := Id.run do
    unless ts[i]? == some (.sym '(') do
      return .error (.E0333, s!"in '\\draw', expected a '(...)' endpoint, found \
{((ts[i]?).map tokText).getD "the end"}; the edge is not drawn")
    let mut depth := 1
    let mut j := i + 1
    let mut inner : Array Tok := #[]
    for _ in [i+1:ts.size + 1] do
      if h : j < ts.size then
        match ts[j] with
        | .sym '(' => depth := depth + 1; inner := inner.push ts[j]; j := j + 1
        | .sym ')' =>
          depth := depth - 1
          if depth == 0 then break
          inner := inner.push ts[j]
          j := j + 1
        | t => inner := inner.push t; j := j + 1
      else break
    unless depth == 0 do
      return .error (.E0333, "in '\\draw', an endpoint misses its ')'; the edge \
is not drawn")
    match (splitTop inner ',').toList with
    | [xs, ys] =>
      match evalNum env xs, evalNum env ys with
      | .ok xm, .ok ym => return .ok (.point (cx.toSp xm) (cx.toSp ym), j + 1)
      | .error e, _ | _, .error e =>
        return .error (.E0333, s!"in '\\draw', {e}; the edge is not drawn")
    | _ =>
      let mut nm := ""
      for t in inner do
        nm := nm ++ (match t with
          | .ident s => s
          | .num m => milliString m
          | .sym c => String.singleton c
          | _ => "")
      match ev.nodes.lookup nm with
      | some g => return .ok (.node g, j + 1)
      | none =>
        return .error (.E0333, s!"in '\\draw', no node is named '{nm}'; the edge \
is not drawn")
  let mut pts : Array Anchor := #[]
  let mut ops : Array (DrawOp × Option (Array Ir.Inline × Ir.Color × Nat × Ir.Pic.LabelAlign)) := #[]
  match readAnchor i with
  | .error d => return ev.diag d
  | .ok (a, i2) =>
    pts := pts.push a
    i := i2
  let factor : Nat := if cx.transformShape && cx.scale > 0 then cx.scale.toNat else 1000
  for _ in [0:ts.size + 1] do
    if h : i < ts.size then
      -- the path operation: `--`, or `to` with its optional tangents
      let mut op := DrawOp.straight
      if ts[i]? == some (.sym '-') && ts[i+1]? == some (.sym '-') then
        i := i + 2
      else if ts[i]? == some (.ident "to") then
        i := i + 1
        if ts[i]? == some (.sym '[') then
          let mut j := i + 1
          let mut inner : Array Tok := #[]
          for _ in [i+1:ts.size + 1] do
            if h2 : j < ts.size then
              if ts[j] == .sym ']' then break
              inner := inner.push ts[j]
              j := j + 1
            else break
          unless ts[j]? == some (.sym ']') do
            return ev.diag (.E0333, "'to' options miss their ']'; the edge is \
not drawn")
          i := j + 1
          let mut outA : Option Int := none
          let mut inA : Option Int := none
          for opt in splitTop inner ',' do
            match opt.toList with
            | .ident "out" :: .sym '=' :: rest =>
              match evalNum env rest.toArray with
              | .ok m => outA := some ((m + 500) / 1000)
              | .error e =>
                return ev.diag (.E0333, s!"in 'out=', {e}; the edge is not drawn")
            | .ident "in" :: .sym '=' :: rest =>
              match evalNum env rest.toArray with
              | .ok m => inA := some ((m + 500) / 1000)
              | .error e =>
                return ev.diag (.E0333, s!"in 'in=', {e}; the edge is not drawn")
            | [] => pure ()
            | o :: _ =>
              ev := ev.diag (.W0334, s!"'to' option {tokText o} is outside the \
rendered picture subset; the option is dropped")
          match outA, inA with
          | some oA, some iA => op := .curve oA iA
          | none, none => pure ()  -- pgf's default to path is the straight line
          | _, _ =>
            ev := ev.diag (.W0334, "a 'to' with only one of 'out='/'in=' is \
outside the rendered picture subset; it is drawn as a straight line")
      else
        return ev.diag (.W0334, s!"'\\draw' continues with {tokText ts[i]}, \
outside the rendered picture subset; the edge is not drawn")
      -- an in-path `node[...] {...}`: an edge label at the segment's
      -- midpoint; a placement option (`right`, …) loses only itself
      let mut mid : Option (Array Ir.Inline × Ir.Color × Nat × Ir.Pic.LabelAlign) := none
      if ts[i]? == some (.ident "node") then
        i := i + 1
        -- An edge label reads its own bracket alone: neither the picture's
        -- entries nor an `every node` style reaches it, so a declared one
        -- is named here rather than dropped in silence.
        unless cx.everyNode.isEmpty do
          ev := ev.diag (.W0334, "an 'every node' key on an edge label is outside \
the rendered picture subset; the keys are dropped")
        let mut mcolor := Ir.Color.black
        let mut mscale : Nat := factor
        let mut malign := Ir.Pic.LabelAlign.center
        if ts[i]? == some (.sym '[') then
          let mut j := i + 1
          let mut inner : Array Tok := #[]
          for _ in [i+1:ts.size + 1] do
            if h2 : j < ts.size then
              if ts[j] == .sym ']' then break
              inner := inner.push ts[j]
              j := j + 1
            else break
          unless ts[j]? == some (.sym ']') do
            return ev.diag (.E0333, "an edge node's options miss their ']'; the \
edge is not drawn")
          i := j + 1
          for opt in splitTop inner ',' do
            match opt.toList with
            | .ident "font" :: .sym '=' :: .ctrl size :: [] =>
              match Ir.sizeScale.lookup size with
              | some k => mscale := k * factor / 1000
              | none =>
                ev := ev.diag (.W0334, s!"node option 'font=\\{size}' is outside \
the rendered picture subset; the option is dropped")
            | .ident "text" :: .sym '=' :: rest =>
              match evalColor cx env rest.toArray with
              | .ok c => mcolor := c
              | .error e =>
                ev := ev.diag (.E0333, s!"in an edge node, {e}; the colour is \
dropped")
            -- placement: pgf §17.5.2 — `right` is anchor=west, the label
            -- standing right of the point, and so around
            | [.ident "right"] => malign := .west
            | [.ident "left"] => malign := .east
            | [.ident "above"] => malign := .south
            | [.ident "below"] => malign := .north
            | [] => pure ()
            | o :: _ =>
              ev := ev.diag (.W0334, s!"edge node option {tokText o} is outside \
the rendered picture subset; the option is dropped")
        match ts[i]? with
        | some (.group body) =>
          match contentOf cx env body with
          | .ok (content, mdiags) =>
            ev := mdiags.foldl Ev.diag ev
            mid := some (content, mcolor, mscale, malign)
            i := i + 1
          | .error e =>
            return ev.diag (.W0334, s!"{e} in an edge label is outside the \
rendered picture subset; the edge is not drawn")
        | _ =>
          return ev.diag (.E0333, "an edge 'node' needs a '{text}' body; the \
edge is not drawn")
      match readAnchor i with
      | .error d => return ev.diag d
      | .ok (a, i2) =>
        pts := pts.push a
        ops := ops.push (op, mid)
        i := i2
    else break
  unless pts.size ≥ 2 do
    return ev.diag (.E0333, "'\\draw' needs two endpoints; the edge is not drawn")
  let stroke : Ir.Pic.Stroke :=
    { color := color
      width := if thick then Ir.Pic.thickWidth else Ir.Pic.thinWidth
      dash := dash }
  let mut segs : Array Ir.Pic.PathSeg := #[]
  let mut tip : Option Ir.Pic.Tip := none
  let mut labels : Array Ir.Pic.Shape := #[]
  for k in [0:ops.size] do
    match pts[k]?, pts[k+1]?, ops[k]? with
    | some a, some c, some (op, mid) =>
      let last := k + 1 == ops.size
      match op with
      | .straight =>
        let p1 := a.toward c.center
        let p2 := c.toward a.center
        if last && arrow then
          match tipAt p2.1 p2.2 (p2.1 - p1.1) (p2.2 - p1.2) stroke.width with
          | some (t, bx, byy) =>
            segs := segs.push (.line p1.1 p1.2 bx byy)
            tip := some t
          | none => segs := segs.push (.line p1.1 p1.2 p2.1 p2.2)
        else
          segs := segs.push (.line p1.1 p1.2 p2.1 p2.2)
        if let some (content, mc, msc, mal) := mid then
          labels := labels.push (.label ((p1.1 + p2.1) / 2) ((p1.2 + p2.2) / 2)
            content mc msc mal)
      | .curve oA iA =>
        let p1 := a.towardDir oA
        let p2 := c.towardDir iA
        let ddx := p2.1 - p1.1
        let ddy := p2.2 - p1.2
        -- control distance 0.3915·‖d‖: the To-Path library's factor
        let dist := isqrt (ddx * ddx + ddy * ddy) * 3915 / 10000
        let c1 := curveControl p1.1 p1.2 dist oA
        let c2 := curveControl p2.1 p2.2 dist iA
        segs := segs.push (.cubic p1.1 p1.2 c1.1 c1.2 c2.1 c2.2 p2.1 p2.2)
        if last && arrow then
          -- the tip rides the arrival tangent; the curve keeps its
          -- endpoint and the filled tip covers its last reach
          tip := (tipAt p2.1 p2.2 (p2.1 - c2.1) (p2.2 - c2.2) stroke.width).map (·.1)
        if let some (content, mc, msc, mal) := mid then
          -- B(½) = (p1 + 3c1 + 3c2 + p2)/8, the Bézier midpoint
          labels := labels.push (.label
            ((p1.1 + 3 * c1.1 + 3 * c2.1 + p2.1) / 8)
            ((p1.2 + 3 * c1.2 + 3 * c2.2 + p2.2) / 8) content mc msc mal)
    | _, _, _ => pure ()
  let withEdge := ev.shapes.push (.edge segs stroke tip)
  return { ev with shapes := withEdge ++ labels }

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

def evalOne (cx : Cx) : Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | .fill toks, env, ev =>
    match evalFill cx env toks with
    | .ok shape =>
      -- `\fill`'s bracket is a colour spelling, not a key list, so no
      -- option loop runs here and an `every path` style cannot reach it.
      -- Named rather than dropped in silence: pgf would apply those keys.
      let ev := if cx.everyPath.isEmpty then ev else
        ev.diag (.W0334, "an 'every path' key on a '\\fill' is outside the \
rendered picture subset; the keys are dropped")
      (env, { ev with shapes := ev.shapes.push shape })
    | .error d => (env, ev.diag d)
  | .node toks, env, ev => (env, evalNode cx env toks ev)
  | .draw toks, env, ev => (env, evalDraw cx env toks ev)
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

/-- One body evaluation per item: the recursion is on the item list, the
body a fixed subterm of its `\foreach`, so the unrolling is bounded by the
expanded list — which `range` bounded before any value existed. -/
def evalForeach (cx : Cx) (vars : Array String) (body : List Stmt) :
    List (Array Val) → List (String × Val) → Ev → Ev
  | [], _, ev => ev
  | item :: rest, env, ev =>
    let (_, ev2) := evalList cx body (bindVars vars item env) ev
    evalForeach cx vars body rest env ev2

end

/-- Elaborate one `tikzpicture` body: the leading `[scale=...]` option
block, the statements, then the unrolled evaluation. Everything the
subset cannot render is a named diagnostic beside the shapes that did.
`sets` carries the document's `\tikzset` key lists in source order
(`Compat.tikzsetKeys`), whose `/.style` definitions every picture starts
from — a style reaches its picture wherever the author wrote it — and the
picture's own `[...]` definitions shadow them.

A style *applied* in the picture's own bracket reaches the contents:
pgf sets those keys in the picture's scope, so every path and node reads
them before its own, and a key set in both takes the inner value
(`inheritOpts`). An `every node`/`every path` style is the third level
between them: pgf executes it inside the node's or path's own scope, so it
beats what the picture set and loses to the bracket's own (`mergeOpts`).
An `every X` this subset has no loop for stays unread and is named at the
line that declared it. -/
def elabPicture (pal : Ir.Palette) (raws : Array Parse.Raw)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag :=
      fun d rs => (.math d (Parse.rawSrc rs), #[]))
    (sets : Array (Array Parse.Raw) := #[]) :
    Ir.Pic.Picture × Array PDiag := Id.run do
  let toks := ofRaws raws
  let mut scale : Int := 1000
  let mut styles := documentStyles (sets.map fun keys => ofRaws keys)
  let mut transformShape := false
  let mut inherited : Array (Array Tok) := #[]
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
        let entry := opt.toList.filter (· != .space)
        -- A definition goes through the one router the document's
        -- `\tikzset` lines go through, so a picture's own definition and a
        -- document-level one cannot differ in what they mean. Consed on
        -- top, so a picture's own definition shadows the document's of
        -- that name.
        match readOneDef styles entry with
        | some s => styles := s
        | none =>
        match entry with
        | .ident "scale" :: .sym '=' :: rest =>
          match evalNum [] rest.toArray with
          | .ok m =>
            if m ≤ 0 then
              diags := diags.push (.E0333, "'scale' must be positive; it is ignored")
            else scale := m
          | .error e => diags := diags.push (.E0333, s!"in 'scale=', {e}; it is ignored")
        -- `transform shape`: nodes take the picture's scale (pgf manual
        -- §25.4, "transformations do not apply to nodes" without it).
        | [.ident "transform", .ident "shape"] => transformShape := true
        -- A bare name that resolves is a style applied to the picture
        -- itself: pgf sets it in the picture's scope, so its options are
        -- what the contents inherit (`Cx.opts`, merged by `mergeOpts`).
        -- A name that resolves to nothing is a key, and is named here.
        | [.ident n] =>
          match styles.lookup n with
          | some bundle => inherited := inherited ++ splitTop bundle ','
          | none => diags := diags.push (outsideOpt (.ident n))
        | [] => pure ()
        | o :: _ =>
          diags := diags.push (outsideOpt o)
    else
      diags := diags.push (.E0333, "the picture's options miss their ']'")
  let st := parseList (toks.toList.drop i) {}
  let everyOf (n : String) : Array (Array Tok) :=
    match styles.lookup n with
    | some bundle => (splitTop bundle ',').filter fun e => !e.isEmpty
    | none => #[]
  let cx : Cx := { pal := pal, scale := scale
                   styles := styles, transformShape := transformShape
                   opts := inherited
                   everyNode := everyOf everyNodeKey
                   everyPath := everyOf everyPathKey
                   math := math }
  let (_, ev) := evalList cx st.out.toList [] {}
  -- Nothing in the picture reads keys (a picture of nothing but `\fill`,
  -- whose bracket is a colour spelling), so the inherited entries reached
  -- no loop that could name them. Naming them here keeps the standing
  -- rule: a key the subset does not use is never silently dropped.
  let mut unread : Array PDiag := #[]
  unless ev.readOpts do
    for opt in inherited do
      match opt.toList with
      | [] => pure ()
      | o :: _ =>
        unread := unread.push (.W0334, s!"picture option {tokText o} reached no path \
or node; the option is dropped")
  let all := diags ++ st.bad ++ ev.diags ++ unread
  -- One message, once: the parse and eval sides dedupe among themselves;
  -- this joins them under the same rule.
  let mut seen : Array String := #[]
  let mut out : Array PDiag := #[]
  for d in all do
    unless seen.contains d.2 do
      seen := seen.push d.2
      out := out.push d
  return ({ shapes := ev.shapes }, out)

/-- The stand-in for a picture whose every construct was refused: one
outlined box carrying the diagnostic code, following the image precedent
(an image that did not load renders as an outlined placeholder of its
requested size; W0601). The size is the image default — 1 in square —
because no honest extent is known, and the outline colour is the image
placeholder's own grey, so the two failure modes read alike. -/
def placeholder (code : String) : Ir.Pic.Picture :=
  let side := Dim.inch 1     -- the image-request default when nothing loads
  let th := Dim.pt 3 / 4     -- the image placeholder's 0.75 pt outline
  let grey : Ir.Color := { r := 158, g := 158, b := 168 }  -- its 0.62 0.62 0.66 RG stroke
  { shapes := #[
      .rect 0 0 side th grey,
      .rect 0 (side - th) side th grey,
      .rect 0 0 th side grey,
      .rect (side - th) 0 th side grey,
      .label (side / 2) (side / 2) #[.text code] grey 1000 .center] }

end LeanTex.Core.Picture

