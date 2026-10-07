module

public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.Loop

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
public abbrev PDiag := DiagCode × String

/-- **Does the native drawing lose something the document declared?** A
content loss is one whose floor is not inert (`Loss.floor`): `dropped`,
`pending` and `degraded` — a shape, a construct or a formula TikZ itself
would draw. A `standard`, `config` or `info` diagnostic names a decision or
a standard the declaration already meets, so the boundary would draw the
same page and routing there would only trade the engine's ink for an
opaque box. -/
public def namesLoss (ds : Array PDiag) : Bool :=
  ds.any fun d => d.1.floor != .inert

/-- One micro-token of picture source. The lexer's words run punctuation
together (`++(0.92,0.92);` is one word), so `ofRaws` re-splits them into
numbers, identifiers, and single symbols; braces arrive pre-matched as
groups from `Parse.Raw`. -/
public inductive Tok where
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
private def ofRawList (acc : Array Tok) : List Parse.Raw → Array Tok
  | [] => acc
  | r :: rest => ofRawList (ofRawOne acc r) rest

private def ofRawOne (acc : Array Tok) : Parse.Raw → Array Tok
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

public def ofRaws (raws : Array Parse.Raw) : Array Tok :=
  ofRawList #[] raws.toList

-- Expression evaluation: pgfmath's arithmetic over milli fixed point.

/-- A `\foreach` binding's value: a number in milli, or the raw text of a
list item that is not one (a label like `alpha`). -/
public inductive Val where
  | num (m : Int)
  | str (s : String)
  deriving Repr, BEq, Inhabited

/-- Render a milli value the way pgf prints a macro: an integer without a
point, otherwise up to three decimals. -/
public def milliString (m : Int) : String :=
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

public def Val.text : Val → String
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
private def evalExpr (env : List (String × Val)) (toks : Array Tok) : Except String Val := Id.run do
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
private def evalNum (env : List (String × Val)) (toks : Array Tok) : Except String Int :=
  match evalExpr env toks with
  | .ok (.num m) => .ok m
  | .ok (.str s) => .error s!"'{s}' where a number is needed"
  | .error e => .error e

-- `\foreach` ranges: the count is decided before the values exist.

/-- How many values `{a,...,b}` (step `step`) enumerates: `none` when the
step is zero or walks away from the bound — the range that would never
terminate is a diagnostic, not a hang. -/
public def rangeCount (a step b : Int) : Option Nat :=
  if step > 0 && a ≤ b then some (((b - a) / step).toNat + 1)
  else if step < 0 && b ≤ a then some (((a - b) / (-step)).toNat + 1)
  else none

/-- The enumerated values, indexed off the count: total by construction. -/
public def range (a step b : Int) : Option (Array Int) :=
  (rangeCount a step b).map fun n => (Array.range n).map fun i => a + step * Int.ofNat i

/-- The enumeration is exactly its count long. -/
public theorem range_size (a step b : Int) (n : Nat) (h : rangeCount a step b = some n) :
    (range a step b).map (·.size) = some n := by
  simp [range, h]

/-- The k-th value is `a + step·k`: the range enumerates its arithmetic
progression exactly, no value skipped or invented. -/
public theorem range_get (a step b : Int) (xs : Array Int) (hx : range a step b = some xs)
    (i : Nat) (h : i < xs.size) : xs[i] = a + step * i := by
  simp only [range, Option.map_eq_some_iff] at hx
  obtain ⟨n, _, hmap⟩ := hx
  subst hmap
  simp

/-- The brief's instance: `{a,...,b}` in whole units (milli ×1000, the
default step) enumerates `b − a + 1` values. -/
public theorem range_unit_size (a b : Int) (hab : a ≤ b) :
    (range (1000 * a) 1000 (1000 * b)).map (·.size) = some ((b - a).toNat + 1) := by
  have hc : rangeCount (1000 * a) 1000 (1000 * b) = some ((b - a).toNat + 1) := by
    have hcond : (decide ((1000:Int) > 0) && decide ((1000:Int) * a ≤ 1000 * b)) = true := by
      simp [hab]
    simp only [rangeCount, hcond, Option.some.injEq, ite_true]
    omega
  exact range_size _ _ _ _ hc

-- Statements.

/-- How a TeX conditional's test is read. Every control word beginning
`if` is a conditional opener — TeX's own convention, and what `\newif`
builds on (TeXbook chapter 20) — but only the arithmetic tests carry a
shape this walk can compute:

* `num` is `\ifnum`/`\ifdim`, the ⟨number⟩⟨relation⟩⟨number⟩ form, and the
  `\foreach`-counter idiom;
* `always` is `\iftrue`/`\iffalse`, whose value is the primitive itself;
* `opaque` is every other test — `\ifdefined`, `\ifx`, `\ifcase`, a mode
  test. Their answers are facts about TeX's own state or about a control
  sequence table this walk does not have, so evaluating them would be
  *guessing*, and a guessed branch is wrong ink rather than missing ink.
  They are refused by name, and both branches stay separate so nothing the
  document did not ask for is drawn.
-/
public inductive CondKind where
  | num (name : String)
  | always (v : Bool)
  | mode (name : String) (v : Bool)
  | opaque (name : String)
  deriving Repr, BEq, Inhabited

/-- The answer a mode test gives at a picture's statements: pgf builds the
picture in a horizontal box (`\pgfpicture` sets it with `\hbox`), so there
TeX is in restricted horizontal mode — `\ifhmode` and `\ifinner` hold,
`\ifvmode` and `\ifmmode` fail, whatever mode the picture stands in
(measured against lualatex). -/
private def pictureMode (n : String) : Option Bool :=
  if n == "ifhmode" || n == "ifinner" then some true
  else if n == "ifvmode" || n == "ifmmode" then some false
  else none

/-- The conditional a control word opens, or `none` where it opens none.
Keyed on the `if` prefix rather than on a list of primitives, because
`\newif` lets a document mint `\ifmyflag` and a closed list cannot hold
those — the same closed-list lesson the boundary's macro closure records. -/
private def condKindOf (n : String) : Option CondKind :=
  if n == "ifnum" || n == "ifdim" then some (.num n)
  else if n == "iftrue" then some (.always true)
  else if n == "iffalse" then some (.always false)
  else if let some v := pictureMode n then some (.mode n v)
  else if n.startsWith "if" && n.length > 2 then some (.opaque n)
  else none

/-- Does the head take no test at all? `\iftrue`/`\iffalse` are their own
value and the four mode tests read TeX's state (TeXbook chapter 20), so
the branch begins with the very next token: collecting a test up to a
space would swallow the branch's first statement, since TeX drops the
space after a control word before this walk sees it. -/
private def condTakesNoTest (n : String) : Bool :=
  n == "iftrue" || n == "iffalse" || n == "ifmmode" || n == "ifhmode" ||
    n == "ifvmode" || n == "ifinner"

/-- One parsed picture statement. `fill` and `node` keep their tokenslices — coordinates and options are evaluated per loop iteration, where
the bindings live. -/
public inductive Stmt where
  | fill (toks : Array Tok)
  | node (toks : Array Tok)
  | draw (toks : Array Tok)
  /-- `\path (a) edge (b);` — a path whose operations draw only where one
  asks: pgf's `every edge` carries `draw`, so an `edge` operation strokes
  where a bare `\path ... -- ...` paints nothing. -/
  | path (toks : Array Tok)
  /-- `\useasboundingbox (a) rectangle (b);` — pgf's `\path[use as bounding
  box]`: a size declaration, not a drawing. The rectangle is the picture's
  box from here on (pgf manual §15.8). -/
  | bbox (toks : Array Tok)
  /-- `\pgfmathsetmacro`, and `\pgfmathtruncatemacro` when `trunc`. -/
  | set (name : String) (expr : Array Tok) (trunc : Bool)
  | foreach (vars : Array String) (list : Array Tok) (body : List Stmt)
  /-- `\ifnum <num><rel><num> ... \else ... \fi` and its siblings — TeX's
  conditionals. The test's tokens are kept for evaluation, because a macro
  it names is bound while the statements run and not while they are parsed;
  `kind` says which test this is, because only the arithmetic ones are
  computable here. -/
  | cond (kind : CondKind) (test : Array Tok) (thenS : List Stmt) (elseS : List Stmt)
  deriving Repr, Inhabited

/-- The `;`-terminated statement kinds the machine collects. -/
private inductive StKind where
  | fill
  | node
  | draw
  | path
  | bbox
  deriving Repr, BEq, Inhabited

private def StKind.name : StKind → String
  | .fill => "fill"
  | .node => "node"
  | .draw => "draw"
  | .path => "path"
  | .bbox => "useasboundingbox"

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
  /-- After a conditional opener, collecting the test's tokens. TeX
  terminates a ⟨number⟩ with one optional space, and the second number of
  an arithmetic test is the last thing the test contains — so that test
  ends at the first space standing after a relation and at least one token
  of its right side. A document must write that space for TeX itself, so
  this is the rule and not an approximation of one. Every other test ends
  at its first space, which is what a document writes for the same
  reason. -/
  | icond (kind : CondKind) (test : Array Tok) (sawRel : Bool)
  deriving Repr, Inhabited

/-- One conditional whose branch is being collected: which test it is, the
test's tokens, the statements the branch has taken so far, the statements
the `then` branch took once `\else` has been seen, and whether it has. -/
private structure CondFrame where
  kind : CondKind
  test : Array Tok
  taken : Array Stmt := #[]
  thenS : Array Stmt := #[]
  inElse : Bool := false
  deriving Repr, Inhabited

private structure PSt where
  out : Array Stmt := #[]
  bad : Array PDiag := #[]
  /-- Enclosing `\foreach` headers whose body is the statement being
  built, innermost last. -/
  pending : Array (Array String × Array Tok) := #[]
  /-- Enclosing `\ifnum`s whose branch is being collected, innermost last.
  A finished statement goes to the innermost frame's current branch rather
  than to `out`, which is what makes the two branches separate answers
  instead of one run of statements the evaluator cannot tell apart. -/
  conds : Array CondFrame := #[]
  mode : Mode := .top

/-- A `\draw`/`\path` statement's subpaths. A path ends at its last
coordinate, so a `(` standing where an *operation* would begin starts a new
subpath: `\path (a) edge (b) (c) edge (d);` is two paths, and that is how a
pgf author writes several edges of one diagram in a single statement (pgf
manual §14, the path operations). Split here, at the statement machine, so
each subpath reaches the evaluator as the single chain it already reads; the
option bracket belongs to the statement, so it rides on every slice.

One slice always comes back, so a statement with no boundary in it is
unchanged — and a malformed one still reaches the evaluator, which names
it. -/
private def subpaths (acc : Array Tok) : Array (Array Tok) := Id.run do
  -- The leading option bracket, which every subpath inherits.
  let mut head := 0
  for _ in [0:acc.size + 1] do
    if acc[head]? == some .space then head := head + 1 else break
  let mut pre : Array Tok := #[]
  if acc[head]? == some (.sym '[') then
    let mut j := head
    for _ in [head:acc.size + 1] do
      if h : j < acc.size then
        pre := pre.push acc[j]
        j := j + 1
        if acc[j - 1]? == some (.sym ']') then break
      else break
    head := j
  let mut slices : Array (Array Tok) := #[]
  let mut cur : Array Tok := #[]
  -- Whether the last token that was not a space closed a group at the
  -- outer level: only there does a following `(` begin a coordinate rather
  -- than continue one.
  let mut depth := 0
  let mut closed := false
  for k in [head:acc.size] do
    if h : k < acc.size then
      let t := acc[k]
      if t == .sym '(' && closed && depth == 0 then
        slices := slices.push cur
        cur := #[t]
        depth := 1
        closed := false
      else
        cur := cur.push t
        match t with
        | .sym '(' =>
          depth := depth + 1
          closed := false
        | .sym ')' =>
          depth := depth - 1
          closed := depth == 0
        | .space => pure ()
        | _ => closed := false
  slices := slices.push cur
  -- A path may legally *end* at a coordinate: it moves the current point
  -- and draws nothing (pgf manual §14, the move-to). The split turns such a
  -- tail into its own slice, and a slice of one coordinate is what the
  -- evaluator refuses for want of a second endpoint — so dropping the tail
  -- here is the difference between a no-op and a fatal error on a legal
  -- statement. Only a *tail among several*: a statement that is nothing but
  -- a coordinate is still the evaluator's to name, and if every slice is a
  -- move the whole statement goes through unchanged.
  let moveOnly (s : Array Tok) : Bool := Id.run do
    let ts := s.filter (· != .space)
    unless ts[0]? == some (.sym '(') do return false
    let mut depth := 0
    for k in [0:ts.size] do
      if h : k < ts.size then
        match ts[k] with
        | .sym '(' => depth := depth + 1
        | .sym ')' =>
          depth := depth - 1
          if depth == 0 then return k + 1 == ts.size
        | _ => pure ()
    return false
  let kept := if slices.size ≤ 1 then slices else slices.filter (!moveOnly ·)
  let drawn := if kept.isEmpty then slices else kept
  let out := drawn.filterMap fun s =>
    if s.isEmpty then none else some (s.foldl Array.push pre)
  return if out.isEmpty then #[acc] else out

/-- Where a finished statement goes: the innermost `\ifnum` frame's current
branch if one is open, otherwise the picture's own statement list. One sink,
so a statement cannot reach `out` from inside a branch — which is the whole
of what keeps a conditional's two sides apart. -/
private def PSt.emit (st : PSt) (ss : List Stmt) : PSt :=
  match st.conds.back? with
  | none => { st with out := ss.foldl Array.push st.out }
  | some f =>
    let f2 : CondFrame := { f with taken := ss.foldl Array.push f.taken }
    { st with conds := st.conds.pop.push f2 }

/-- Close one finished statement: wrap it in every pending `\foreach`
header (an unbraced body is one statement), emit, reset. -/
private def PSt.finishMany (st : PSt) (ss : List Stmt) : PSt := Id.run do
  let mut ss := ss
  let mut pending := st.pending
  for _ in [0:st.pending.size] do
    match pending.back? with
    | some (vars, list) =>
      ss := [.foreach vars list ss]
      pending := pending.pop
    | none => break
  return { (st.emit ss) with pending := #[], mode := .top }

private def PSt.finish (st : PSt) (s : Stmt) : PSt := st.finishMany [s]

private def PSt.diag (st : PSt) (code : DiagCode) (msg : String) : PSt :=
  if st.bad.any (·.2 == msg) then st
  else { st with bad := st.bad.push (code, msg) }

private def PSt.outside (st : PSt) (what : String) : PSt :=
  st.diag .W0334 s!"{what} is outside the rendered picture subset; not drawn"

/-- `\else` on the open frame: the statements collected so far are the
`then` branch's, and what follows is the `else` branch's. A second `\else`
is the document's error and is named. -/
private def PSt.elseHere (st : PSt) : PSt :=
  match st.conds.back? with
  | none => (st.outside "an '\\else' with no conditional open")
  | some f =>
    if f.inElse then st.diag .E0333 "a second '\\else' in one conditional; the \
conditional is not drawn"
    else
      let f2 : CondFrame := { f with thenS := f.taken, taken := #[], inElse := true }
      { st with conds := st.conds.pop.push f2 }

/-- `\fi`: close the innermost frame and emit the conditional as one
statement into whatever sink encloses it. -/
private def PSt.fiHere (st : PSt) : PSt :=
  match st.conds.back? with
  | none => (st.outside "a '\\fi' with no conditional open")
  | some f =>
    let thenS := if f.inElse then f.thenS else f.taken
    let elseS := if f.inElse then f.taken else #[]
    let st := { st with conds := st.conds.pop }
    st.finishMany [.cond f.kind f.test thenS.toList elseS.toList]

/-- Close every conditional still open at the end of the body: an
unbalanced `\fi` is the document's error, and the statements its branches
collected may not simply vanish. Each open frame becomes its conditional,
innermost first, so nothing a branch read is stranded in the parser. -/
private def PSt.drain (st : PSt) : PSt := Id.run do
  let mut st := st
  for _ in [0:st.conds.size] do
    if st.conds.isEmpty then break
    st := { st.fiHere with mode := .top }
  if st.conds.isEmpty then return st
  return st.diag .E0333 "a conditional in this picture is never closed by \
'\\fi'; its statements are not drawn"

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
    | .ctrl "path" => { st with mode := .stmt .path #[] }
    | .ctrl "useasboundingbox" => { st with mode := .stmt .bbox #[] }
    | .ctrl "foreach" => { st with mode := .fvars #[] }
    | .ctrl "pgfmathsetmacro" => { st with mode := .sname false }
    | .ctrl "pgfmathtruncatemacro" => { st with mode := .sname true }
    | .ctrl "else" => st.elseHere
    | .ctrl "fi" => st.fiHere
    | .ctrl name =>
      match condKindOf name with
      | some k =>
        if condTakesNoTest name then
          { st with conds := st.conds.push { kind := k, test := #[] }, mode := .top }
        else { st with mode := .icond k #[] false }
      | none => { (st.outside s!"'\\{name}'") with mode := .skip }
    | .sym ';' | .space => st
    | .other what => { (st.outside what) with mode := .skip }
    | .math _ _ => { (st.outside "math") with mode := .skip }
    | .ident s => { (st.outside s!"'{s}'") with mode := .skip }
    | .num _ => { (st.outside "a bare number") with mode := .skip }
    | .sym c => { (st.outside s!"'{c}'") with mode := .skip }
    | .group _ => { (st.outside "'{...}'") with mode := .skip }
  | .stmt kind acc =>
    match t with
    | .sym ';' => match kind with
        | .fill => st.finish (.fill acc)
        | .node => st.finish (.node acc)
        | .draw => st.finishMany ((subpaths acc).toList.map Stmt.draw)
        | .path => st.finishMany ((subpaths acc).toList.map Stmt.path)
        | .bbox => st.finish (.bbox acc)
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
    | .ctrl "path" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .path #[] }
    | .ctrl name =>
      match condKindOf name with
      | some k =>
        if condTakesNoTest name then
          { st with pending := st.pending.push (vars, list),
                    conds := st.conds.push { kind := k, test := #[] }, mode := .top }
        else
          { st with pending := st.pending.push (vars, list), mode := .icond k #[] false }
      | none =>
        { (st.outside "this '\\foreach' body")
          with mode := .skip, pending := #[] }
    -- `.group` never reaches here: `parseToks` owns that arm.
    | _ =>
      { (st.outside "this '\\foreach' body")
        with mode := .skip, pending := #[] }
  | .skip =>
    match t with
    | .sym ';' => { st with mode := .top }
    | _ => st
  | .icond kind test sawRel =>
    let close (st : PSt) : PSt :=
      { st with conds := st.conds.push { kind := kind, test := test }, mode := .top }
    -- An arithmetic test ends at the space TeX's own ⟨number⟩ scan needs;
    -- every other test ends at its first space, which is what a document
    -- writes for the same reason.
    let ready : Bool :=
      match kind with
      | .num _ =>
        sawRel && !test.isEmpty && test.back? != some (.sym '<') &&
          test.back? != some (.sym '>') && test.back? != some (.sym '=')
      | _ => true
    match t with
    | .sym c =>
      if c == '<' || c == '>' || c == '=' then
        { st with mode := .icond kind (test.push t) true }
      else { st with mode := .icond kind (test.push t) sawRel }
    | .space => if ready then close st else st
    -- `\else` or `\fi` immediately: a test with no branch at all.
    | .ctrl "else" => (close st).elseHere
    | .ctrl "fi" => (close st).fiHere
    | _ => { st with mode := .icond kind (test.push t) sawRel }

mutual

/-- Parse micro-tokens into statements: one fold, the only recursion into
pre-matched group subtrees (a `\foreach` body), so totality is structural.
Anything outside the subset is named (W0334) and skipped to the next `;` —
never silently dropped, and never able to take the rest of the picture
with it. -/
private def parseList : List Tok → PSt → PSt
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

private def parseTok (t : Tok) (st : PSt) : PSt :=
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
public structure Cx where
  pal : Ir.Palette
  scale : Int := 1000
  styles : List (String × Array Tok) := []
  transformShape : Bool := false
  /-- What the document's `\tikzset` lines set for every picture in it
  (`documentOpts`): the outermost bracket every statement inherits, so a
  key declared once in the preamble — an arrow tip is the motivating one —
  is read where the statement's own bracket declared nothing. The picture's
  own entries and the statement's own both beat it (`mergeOpts`). -/
  global : Array (Array Tok) := #[]
  /-- The picture-level option entries its contents inherit: what a style
  named in `\begin{tikzpicture}[...]` expanded to, and the keys that
  bracket set itself, already split into entries. Every path and node reads
  them before its own (`inheritOpts`). -/
  opts : Array (Array Tok) := #[]
  /-- What `every node/.style={...}` declared, split into entries: pgf runs
  it inside the node's own scope, so it stands between the picture's
  entries and the node's bracket (`mergeOpts`). -/
  everyNode : Array (Array Tok) := #[]
  /-- What `every path/.style={...}` declared: the same level for a path. -/
  everyPath : Array (Array Tok) := #[]
  /-- What `every text node part/.style={...}` declared: the keys every
  node's text reads, at the level of `every node`. -/
  everyText : Array (Array Tok) := #[]
  /-- `node distance`: the separation a relative placement (`right=of a`)
  puts between the two node centres, vertical then horizontal, as pgf
  spells the pair. pgf's `positioning` library measures *border* to
  border; this subset does not measure a node body's extent at all (see
  the emission note in `evalNode`), so centre to centre is the only
  separation it can define — a stated approximation, exact where the two
  nodes carry the same declared extent. Default 1 cm, pgf's own. -/
  dist : Sp × Sp := (Dim.mm 10, Dim.mm 10)
  /-- Did the *parse* name a construct outside the subset? A declaration
  the parse skipped is gone before evaluation begins, so a name that then
  resolves to nothing traces to that gap rather than to the document. Read
  at the one place a name is resolved, beside `Ev.gapped`. -/
  parseGap : Bool := false
  /-- How a math span in a node body elaborates: provided by the
  elaborator, so `{$X$}` renders through the same math layer a
  paragraph's does — the picture walk owns no math parser. The result is
  the inline plus any losses the elaboration names. -/
  math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag
  /-- The one-argument text commands and the style each names
  (`\textbf` bold, `\emph` emphasis, …): the elaborator's own table, handed
  down as `math` is, so a text command in a node body means what it means
  in a paragraph — the picture walk owns no font-axis table, and a second
  one here would drift from the first. -/
  argStyles : List (String × Ir.Style) := []
  /-- The size ladder in force for the document (`Ir.PageSpec.scale`): what
  a size switch in a node's `font=` or at a label line's start means, per
  mille of the body — the same step the document's paragraphs set it at,
  including a venue's read-out redefinition. -/
  ladder : List (String × Nat) := Ir.sizeScale
  /-- The font declarations and the style each names (`\bfseries` bold,
  `\itshape` italic, …): the elaborator's own table, as `argStyles` is, so
  a `font=` switch means what the same declaration does in a paragraph. -/
  declStyles : List (String × Ir.Style) := []
  /-- The document's body size, passed by the elaborator: the dimension
  font for relative separation and the size `nodeLineLead` scales. -/
  bodySize : Sp := Ir.baseFontSize
  /-- How a label's content measures at a per-mille size: the face,
  arriving as a function because the walk has none of its own. The driver
  resolves it and the elaborator passes it down; the default answers
  nothing, which is the pre-face behaviour (a node's extent is its declared
  minimum alone). -/
  metric : Ir.Pic.LabelMetric := fun _ _ => {}

/-- Picture milli-units to sp: one TikZ unit is 1 cm, times the declared
scale. One multiplication, one rounding division. -/
public def Cx.toSp (cx : Cx) (m : Int) : Sp :=
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
private def expandBody (styles : List (String × Array Tok)) (g : List Tok) :
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
private def addStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
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
private def appendStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
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
private def tipKey (n : String) : String := ".tip " ++ n

/-- Fold one `name/.tip={...}` declaration in. The body is kept as written
and never re-read as keys: it is an arrow-tip construction, not an option
bundle, so there is nothing here to expand and nothing to chase. -/
private def declareTip (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  (tipKey n, g.toArray) :: styles

/-- The name of the `every node` level, and of the `every path` level: the
two key paths the option loops read (pgf manual §12.4.1 — every X is
executed inside the X's own scope). -/
private def everyNodeKey : String := "every node"
private def everyPathKey : String := "every path"
/-- The style the text part of every node runs (tikz.code.tex): the keys a
node's text reads, such as `align=`. -/
private def everyTextKey : String := "every text node part"

/-- Is this token that symbol? A structural match rather than `==`, which
for a recursive inductive's derived `BEq` is compiled by well-founded
recursion and reduces for nothing — so a statement about where a run splits
could not be proved through it. The predicate is the factorization the
proof asked for, and it decides exactly what the comparison did. -/
private def isSym (c : Char) : Tok → Bool
  | .sym d => d == c
  | _ => false

/-- Split a token list at the first occurrence of a symbol, keeping neither
side's separator. -/
private def splitSym (c : Char) : List Tok → Option (List Tok × List Tok)
  | [] => none
  | t :: rest =>
    if isSym c t then some ([], rest)
    else (splitSym c rest).map fun (pre, post) => (t :: pre, post)

/-- `splitSym` at a separator the run before it does not contain: the split
is exactly that run and the rest. -/
private theorem splitSym_append (c : Char) : ∀ (q r : List Tok),
    (∀ t ∈ q, isSym c t = false) → splitSym c (q ++ (.sym c :: r)) = some (q, r)
  | [], r, _ => by simp [splitSym, isSym]
  | t :: q, r, h => by
    have ht : isSym c t = false := h t (List.mem_cons_self ..)
    have hq : ∀ u ∈ q, isSym c u = false := fun u hu => h u (List.mem_cons_of_mem _ hu)
    simp only [List.cons_append, splitSym, ht, Bool.false_eq_true,
      splitSym_append c q r hq, Option.map_some, ite_false]

/-- A run of idents read as one name, joined the way pgf spells it. An
*arrow tip*'s name only: a tip is not a key path (`tipKey`), so its
spelling is deliberately the narrow one — the tip vocabulary pgf's
`arrows` libraries declare is identifiers, and admitting more would turn a
malformed spec into a plausible tip name. Key paths read through
`keyName`. -/
private def identPath : List Tok → Option String
  | [.ident n] => some n
  | .ident n :: rest => (identPath rest).map fun s => n ++ " " ++ s
  | _ => none

/-- Is this token's text a run of key-name *word* characters? `splitWord`
takes letter runs and digit runs greedily, so two word tokens can only be
adjacent across a space the entry filter removed — which is how `keyName`
puts the space back. -/
private def wordTok : Tok → Bool
  | .ident _ => true
  | .num _ => true
  | _ => false

/-- One token's own characters as a key name spells them, or `none` where
the token is not part of a name at all.

pgf's key-name grammar (manual §87.2, "The Key Tree"): a key is a path,
`/` separates its components, `.` introduces a handler, `,` separates
entries in a list and `=` starts a value. **Every other character is the
name's** — which is why `-`, `:`, `@` and digits belong to it, and why a
grammar written as "a run of identifiers" is not the grammar but a guess
about it. A group, a math span, a control word and unreadable source are
not characters and end a name here. -/
private def keyTokText : Tok → Option String
  | .ident s => some s
  | .num m => some (milliString m)
  | .space => some " "
  | .sym c => if c == '/' || c == ',' || c == '=' then none else some (String.singleton c)
  | .ctrl _ | .group _ | .math _ _ | .other _ => none

/-- A key path's name, in pgf's own grammar: every token's characters, with
the space restored between two adjacent word tokens (an entry's spaces are
filtered before it is read, so `every node` and `every  node` arrive here
alike) and the surrounding space stripped, as pgfkeys strips it.

**One reader for both ends.** A name is stored under this and looked up
under this — `readDef` for the declaration, `expandOpts` for the use,
`keyPath` for the vocabularies the option loops match against — which is
what `styleName_agree` pins. The defect that made it one function was a
name cut at its first hyphen: stored under nothing, named as a dropped key
under its first component, and unfound at every bracket that used it. -/
public def keyName (ts : List Tok) : Option String := Id.run do
  let mut out := ""
  let mut prevWord := false
  for t in ts do
    match keyTokText t with
    | none => return none
    | some s =>
      if prevWord && wordTok t then out := out ++ " "
      out := out ++ s
      prevWord := wordTok t
  let name := out.trimAscii.toString
  return if name.isEmpty then none else some name

/-- A key path this reader can honour: a single word, which an option
bracket can apply by name, or one of the three `every X` levels the option
loops read. Any other path (`every label`, a two-word name no bracket can
spell) is left unread, so the line that wrote it names the loss — storing a
bundle nothing will ever look up would drop it in silence. -/
private def readableKey (n : String) : Bool :=
  n == everyNodeKey || n == everyPathKey || n == everyTextKey || !n.contains ' '

/-- One definition entry as a key path, a handler name, and the handler's
group: `every node/.style={draw}` reads as `every node`, `style`, `draw`. -/
private def readDef (entry : List Tok) : Option (String × String × List Tok) := do
  let (path, rest) ← splitSym '/' entry
  let name ← keyName path
  match rest with
  | .sym '.' :: hrest =>
    let (hpath, body) ← splitSym '=' hrest
    let handler ← keyName hpath
    match body with
    | [.group g] => some (name, handler, g)
    | _ => none
  | _ => none

/-- Fold one definition entry into the bundles, or refuse it: `none` where
the entry is not a definition at all, or names a handler or a key path
outside the subset. The one router both a document's `\tikzset` and a
picture's own bracket go through, so the two cannot differ about what a
definition means. -/
private def readOneDef (styles : List (String × Array Tok)) (entry : List Tok) :
    Option (List (String × Array Tok)) :=
  match readDef entry with
  | some (n, "style", g) =>
    if readableKey n then some (addStyle styles n g) else none
  | some (n, "append style", g) =>
    if readableKey n then some (appendStyle styles n g) else none
  | some (n, "tip", g) =>
    if readableKey n then some (declareTip styles n g) else none
  | _ => none

/-- **The name a definition stores is the name a use looks up.** One reader
answers both ends of a bundle's life, so a key name the document writes is
the key name the walk reads — for every name pgf's grammar admits, not for
an enumerated few.

This is the declaration side, stated where it is computable: the name
`readDef` keys a `/.style` entry on is exactly `keyName` of the entry's
path, whatever characters that path is spelled with. The use side is
`expandOpts`, which looks the bundle up under `keyName` of the entry's own
tokens *by construction* — one line of its body, and a reader that gave it
a pattern of its own instead would have to delete this docstring to do it.
That half is checked rather than proved (`pictureHyphenKeyChecks`, read off
`Layout.Out`): the pipeline between the two runs a comma split and a space
filter over a token array, and stating their composition needs an invariant
carried through two `Id.run` loops that the fact itself never mentions —
the factorization is noted and not taken here.

The hypotheses are pgf's own grammar restated (manual §87.2): a name
carries no path separator, and a handler's own path no value separator.
They restrict nothing this reader accepts — `keyName` answers `none` on
either character regardless — they are what lets the two splits be
computed. The handler rides as a token run rather than a literal, because
the conclusion is about the *name* and holds whichever handler follows it —
whichever handler *reads*, which is the third hypothesis: an entry whose
handler is not a name is no definition, and this says nothing about it.

The defect it closes: `-` is an ordinary key-name character, the reader
admitted identifier runs only, and a declaration written `edge-muted` was
stored under nothing, reported as a dropped key `edge`, and found by no
bracket that used it. Nineteen uses of four such names in one figure read
as one dropped key. -/
private theorem styleName_agree (p handler g : List Tok)
    (hp : ∀ t ∈ p, isSym '/' t = false)
    (hh : ∀ t ∈ handler, isSym '=' t = false)
    (hs : (keyName handler).isSome) :
    (readDef (p ++ (.sym '/' :: .sym '.' :: (handler ++ (.sym '=' :: [.group g]))))).map
        (fun d => d.1) = keyName p := by
  cases hk : keyName handler
  · simp [hk] at hs
  · cases h : keyName p <;>
      simp [readDef, splitSym_append '/' p _ hp, splitSym_append '=' handler _ hh, h, hk]

/-- The tip name an arrow spec ends in, where the spec is one this subset
draws: `-name`, `-{name}`, or `->`. A declared tip draws the engine's own
arrow head, the way `latex` already does — pgf manual §16 names many tip
kinds and this subset has one head to draw them with, so the substitution
is the established one, not a new claim. -/
private def tipName : List Tok → Option String
  | [.group g] => identPath (g.filter (· != .space))
  | ts => identPath ts

private def arrowTipName : List Tok → Option String
  | [.sym '-', .sym '>'] => some ">"
  | [.sym '-', t] => tipName [t]
  | _ => none

/-- Does a name draw as this subset's arrow head? A tip the document
declared with `/.tip`, or one of the built-in kinds the plain head has
always stood in for: `latex` (pgf manual §16.3, the `arrows` library) and
`Latex`, which is `arrows.meta`'s spelling of that same tip — one shape
under two library names, so admitting it claims no new substitution. `>` is
the shorthand itself. Anything else stays outside the subset and is named,
which is what keeps a genuinely different tip kind a visible loss rather
than a silent head of the wrong shape. -/
private def drawsAsArrow (styles : List (String × Array Tok)) (n : String) : Bool :=
  n == ">" || n == "latex" || n == "Latex" || (styles.lookup (tipKey n)).isSome

/-- Read a `\tikzset` key list: every definition entry this reader knows
folds into the bundles, in source order so a later definition may name an
earlier one. Every other entry comes back unread — `/.tip`, `/.append
style`, a bare key — for the caller to name at the line that wrote it,
which is where such a diagnostic belongs: the line is the document's, not
any one picture's. -/
public def readStyleList (styles : List (String × Array Tok)) (toks : Array Tok) :
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
@[expose] public def documentStyles (sets : Array (Array Tok)) : List (String × Array Tok) := Id.run do
  let mut styles : List (String × Array Tok) := []
  for keys in sets do
    styles := (readStyleList styles keys).1
  return styles

/-- The name before an entry's `=`, in pgf's key-name grammar: what
`unreadKeys` and the placement reader both name an entry by. The same
reader the declaration stores under (`keyName`), so a vocabulary match and
a bundle lookup cannot disagree about what an entry is called. -/
private def keyPath (toks : List Tok) : String :=
  (keyName (toks.takeWhile (· != .sym '='))).getD ""

/-- The keys this subset reads outside a style definition, so a `\tikzset`
line that sets one is read rather than named as dropped. -/
private def engineKeyNames : List String := ["node distance"]

/-- Does this entry set a key the engine reads? -/
private def setsEngineKey (entry : Array Tok) : Bool :=
  engineKeyNames.contains (keyPath entry.toList)

/-- Split an option bracket into entries and expand a declared bundle's
name one level into the bundle's own entries. One level is all a use site
needs: `addStyle` spliced any nested bundle in at the definition.

The name is read with `keyName`, the one reader a definition is stored
under, so every name pgf's grammar admits is looked up whole. An entry
carrying a value is no bundle use — `keyName` stops at the `=` and answers
`none` — so a key and a bundle of the same name cannot be confused. -/
private def expandOpts (styles : List (String × Array Tok)) (inner : Array Tok) :
    Array (Array Tok) := Id.run do
  let mut opts : Array (Array Tok) := #[]
  for opt in splitTop (inner.filter (· != .space)) ',' do
    match (keyName opt.toList).bind fun n => styles.lookup n with
    | some bundle => opts := opts ++ splitTop bundle ','
    | none => opts := opts.push opt
  return opts

/-- The key an option entry sets: its tokens up to the `=`, so `draw` and
`draw=red` name one key as they do in pgf, and `minimum size=8mm` names
`minimum size`. -/
public def optKey (opt : Array Tok) : String := Id.run do
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
public def inheritOpts (outer inner : Array (Array Tok)) : Array (Array Tok) :=
  let names := inner.map optKey
  outer.filter (fun o => !names.contains (optKey o)) ++ inner

/-- Precedence: an entry in the merge whose key some inner entry also names
is the inner bracket's own. -/
public theorem inherit_inner_exact {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner)
    (hk : ∃ e ∈ inner, optKey e = optKey o) : o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨_, hp⟩ | h
  · obtain ⟨e, he, hek⟩ := hk
    simp at hp
    exact absurd hek (hp e he)
  · exact h

/-- Nothing the inner bracket said is lost to the merge. -/
public theorem inherit_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ inner) : o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append]
  exact Or.inr h

/-- The merge invents nothing: every entry came from one of the two sides. -/
public theorem inherit_mem {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner) : o ∈ outer ∨ o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨h, _⟩ | h
  · exact Or.inl h
  · exact Or.inr h

/-- The four levels one bracket's entries are read under, outermost first.

**document < picture < every X < the bracket's own.** pgf executes a
`\tikzset` key list in the scope it stands in, so a key set once in the
preamble is set for every picture; a picture's keys are set in the
picture's scope, inside that; an `every node`/`every path` style is
executed inside the node's or path's own scope, which is inside the
picture's; and the bracket's own keys are read there too, after it. So each
level beats the ones outside it and loses to the ones inside — and because
each is an `inheritOpts`, a key a later level names is *dropped* from the
earlier one rather than merely preceded by it: the `minimum` family
accumulates by maximum within one bracket, so a surviving document-level
`minimum size=12mm` would beat an inner `4mm` and draw the opposite of what
the node says.

`merge_own_exact`, `merge_every_exact` and `merge_picture_exact` are the
three boundaries, `merge_covers` that nothing the bracket said is lost, and
`merge_global_covers` that a key set once for the document reaches a
bracket that renamed nothing. -/
public def mergeOpts (global picture every own : Array (Array Tok)) : Array (Array Tok) :=
  inheritOpts (inheritOpts (inheritOpts global picture) every) own

/-- Precedence, innermost level: an entry whose key the bracket's own also
names is the bracket's own. -/
public theorem merge_own_exact {global picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts global picture every own)
    (hk : ∃ e ∈ own, optKey e = optKey o) : o ∈ own :=
  inherit_inner_exact hm hk

/-- Precedence, third level: an entry whose key `every X` names and the
bracket's own does not is the `every X` style's. -/
public theorem merge_every_exact {global picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts global picture every own)
    (hk : ∃ e ∈ every, optKey e = optKey o)
    (ho : ¬ ∃ e ∈ own, optKey e = optKey o) : o ∈ every := by
  rcases inherit_mem hm with h | h
  · exact inherit_inner_exact h hk
  · exact absurd ⟨o, h, rfl⟩ ho

/-- Precedence, second level: an entry whose key the picture names and
neither inner level does is the picture's, not the document's. Without this
the outermost level could shadow the picture's own and the boundaries
further in would not notice. -/
public theorem merge_picture_exact {global picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts global picture every own)
    (hk : ∃ e ∈ picture, optKey e = optKey o)
    (he : ¬ ∃ e ∈ every, optKey e = optKey o)
    (ho : ¬ ∃ e ∈ own, optKey e = optKey o) : o ∈ picture := by
  rcases inherit_mem hm with h | h
  · rcases inherit_mem h with h2 | h2
    · exact inherit_inner_exact h2 hk
    · exact absurd ⟨o, h2, rfl⟩ he
  · exact absurd ⟨o, h, rfl⟩ ho

/-- Nothing the bracket's own entries said is lost to any outer level. -/
public theorem merge_covers {global picture every own : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ own) : o ∈ mergeOpts global picture every own :=
  inherit_covers h

/-- Nothing the outer level said is lost where no inner entry names its
key: the level survives the filter, not only the append. -/
public theorem inherit_outer_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ outer) (hk : ∀ e ∈ inner, optKey e ≠ optKey o) :
    o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter]
  refine Or.inl ⟨h, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Array.contains_eq_mem,
    decide_eq_false_iff_not, Array.mem_map, not_exists, not_and]
  exact fun e he => hk e he

/-- Precedence, third level from the outside: what the picture set reaches
the merge where neither later level names its key. Without this the
picture's entries could be dropped wholesale and the boundary facts would
still hold. -/
public theorem merge_picture_covers {global picture every own : Array (Array Tok)}
    {o : Array Tok}
    (h : o ∈ picture) (he : ∀ e ∈ every, optKey e ≠ optKey o)
    (ho : ∀ e ∈ own, optKey e ≠ optKey o) :
    o ∈ mergeOpts global picture every own :=
  inherit_outer_covers (inherit_outer_covers (inherit_covers h) he) ho

/-- **A key the document set for every picture is set on this bracket.** The
outermost level reaches the merge wherever no level inside it names that
key — so an arrow tip declared once in the preamble is read at an edge that
carries no bracket of its own, exactly as if the edge had carried it. The
statement the arrowhead defect needed: before it the entry was dropped
between the `\tikzset` line and the picture, and every edge relying on it
was drawn headless. -/
public theorem merge_global_covers {global picture every own : Array (Array Tok)}
    {o : Array Tok}
    (h : o ∈ global) (hp : ∀ e ∈ picture, optKey e ≠ optKey o)
    (he : ∀ e ∈ every, optKey e ≠ optKey o)
    (ho : ∀ e ∈ own, optKey e ≠ optKey o) :
    o ∈ mergeOpts global picture every own :=
  inherit_outer_covers (inherit_outer_covers (inherit_outer_covers h hp) he) ho

/-- An option entry named for a diagnostic: its whole key, as pgf reads
`key=value` (`text width`, not `text`), else its first token. The first
token alone reported three different dropped keys as one supported-looking
`'text'`, one site where there were three. -/
private def optName (opt : List Tok) : String :=
  let key := keyPath opt
  if key.isEmpty then (opt.head?.map tokText).getD "an empty option" else s!"'{key}'"

/-- A picture-level key outside the subset, named at the bracket that
wrote it. -/
private def outsideOpt (opt : List Tok) : PDiag :=
  (.W0334, s!"picture option {optName opt} is outside the \
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
public def isqrt (n : Int) : Int := (Nat.sqrt n.toNat : Nat)

/-- Where the ray from a rectangle's centre `(cx, cy)` (half-extents
`a`, `b`) toward `(qx, qy)` crosses its border — `\pgfpointshapeborder`
for the rectangle shape (pgf manual, Nodes and Shapes), as algebra: the
dominant axis (`|dy|·a ≤ |dx|·b`) decides which edge, that coordinate is
exact, and the other rounds one exact rational (`rectBorder_exact`). A
ray with no direction answers the centre. -/
public def rectBorder (cx cy a b qx qy : Int) : Int × Int :=
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
public theorem rectBorder_exact (cx cy a b qx qy : Int) (ha : 0 < a) (hb : 0 < b) :
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
public def circleBorder (cx cy r qx qy : Int) : Int × Int :=
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
public theorem circleBorder_step (cx cy r qx qy : Int)
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

/-- `inner sep`'s default, in ten-thousandths of an em: pgf's `0.3333em`
(TikZ manual §17.2.2, the `inner sep`/`inner xsep`/`inner ysep` keys). -/
private def innerSepDefault : Int := 3333

/-- One inner sep at this em. -/
public def innerSep (em : Sp) : Sp := em * innerSepDefault / 10000

/-- **A drawn node's outline is the shape pgf draws**, for a node that does
not declare its whole extent (pgfmoduleshapes.code.tex, the `rectangle`
shape's `\northeast` and the `circle` shape's `\radius`): centred on the
text box, and per axis the text box plus two inner seps, or the declared
minimum where that is larger — a circle's radius is the length of the
vector from the text box's centre to its corner one inner sep out, or half
the larger minimum. The glyph box `lo`–`hi` is relative to the node's
centre `sy`. Returns the outline's centre height and its width and height
(a circle's are both its diameter), so a governing minimum is met to the
sp. -/
public def nodeOutline (circle : Bool) (minW minH sy textHalfW lo hi sepX sepY : Sp) :
    Sp × Sp × Sp :=
  let mid := sy + (lo + hi) / 2
  let tx := textHalfW + sepX
  let ty := (hi - lo) / 2 + sepY
  if circle then
    let d := max (max minW minH) (2 * isqrt (tx * tx + ty * ty))
    (mid, d, d)
  else (mid, max minW (2 * tx), max minH (2 * ty))

/-- **The outline covers the letters, one inner sep out** (`_covers`): the
drawn rectangle is centred on the text box and at least the text box plus
two inner seps on each axis — the room pgf gives a node's text, whatever
minimum it declares — and a governing minimum is its size exactly. -/
public theorem nodeOutline_covers (minW minH sy textHalfW lo hi sepX sepY : Int) :
    (nodeOutline false minW minH sy textHalfW lo hi sepX sepY).1 = sy + (lo + hi) / 2 ∧
      2 * (textHalfW + sepX) ≤ (nodeOutline false minW minH sy textHalfW lo hi sepX sepY).2.1 ∧
      2 * ((hi - lo) / 2 + sepY) ≤ (nodeOutline false minW minH sy textHalfW lo hi sepX sepY).2.2 ∧
      minW ≤ (nodeOutline false minW minH sy textHalfW lo hi sepX sepY).2.1 ∧
      minH ≤ (nodeOutline false minW minH sy textHalfW lo hi sepX sepY).2.2 := by
  simp only [nodeOutline, Bool.false_eq_true, ↓reduceIte, true_and]
  have step : ∀ mW mH t u : Int, 2 * t ≤ max mW (2 * t) ∧ 2 * u ≤ max mH (2 * u) ∧
      mW ≤ max mW (2 * t) ∧ mH ≤ max mH (2 * u) := by
    intros; omega
  exact step minW minH (textHalfW + sepX) ((hi - lo) / 2 + sepY)

/-- **Where pgf seats a node's text box**: centred on the node
(pgfmoduleshapes.code.tex, the `rectangle` and `circle` shapes' `center`
anchor, `.5\wd` across and `.5\ht − .5\dp` up from the box's origin, which
`\pgfmultipartnode` shifts onto the node's coordinate). A box of height `ht`
and depth `dp` stands with its baseline `(ht − dp)/2` below the node, so it
spans `dp` below that baseline and `ht` above it. Returns the baseline and
the box's lower and upper edges, relative to the node's position. -/
public def textSeat (ht dp : Sp) : Sp × Sp × Sp :=
  let b := -((ht - dp) / 2)
  (b, b - dp, b + ht)

/-- **A drawn outline stands on its node, whatever its letters** (`_exact`):
the outline of a text box pgf seats is centred on the node's own position,
to the scaled point, for every height and depth the box can have. A node's
frame, the anchors on it and the edges from them therefore follow the node
and never its glyphs. The defect centred each outline on its letters' box
instead, so `g` stood 2 bp above `A` at one declared height and a
`right=of` chain climbed by the difference at every step. -/
public theorem nodeOutline_seat_exact (circle : Bool) (minW minH sy textHalfW ht dp sepX sepY : Int) :
    (nodeOutline circle minW minH sy textHalfW (textSeat ht dp).2.1 (textSeat ht dp).2.2
      sepX sepY).1 = sy := by
  have step : ∀ s h d : Int, s + ((-((h - d) / 2) - d) + (-((h - d) / 2) + h)) / 2 = s := by
    intro s h d; omega
  cases circle <;> exact step sy ht dp

/-- **A node's border half-extent: its text, plus one inner sep, or the
declared minimum where that is larger.** pgf manual §17.2.2 — a node's
border is its text *plus* `inner sep`, and §17.5.2's anchors sit on the
border, not on the letters. One site, so the extent an anchor resolves
against and the extent a relative placement measures are the same number. -/
public def borderHalf (decl ink sep : Sp) : Sp := max decl (ink + sep)

/-- **The border stands between the letters and one inner sep beyond
them.** The registered `_between` shape, and the tighter sibling of
`anchorPoint_between`: that one says every anchor is inside the box the node
registered; this says the box the node registers is strictly outside the box
its label inks, by the sep and no more. Composed at `g.a := borderHalf …`,
an anchor lies between the ink and the border — which is pgf's own reading.

The strict lower bound is what the defect failed: the extent was
`max decl ink`, the ink itself, so every anchor sat one inner sep inside
where pgf puts it and an edge drawn to a node's `west` started inside the
label's first letter. Spelled over bare `Int` binders, since `omega` does
not read an `Sp`-typed structure field. -/
public theorem borderHalf_between (decl ink sep : Sp) (hd : decl ≤ ink + sep)
    (hs : 0 < sep) : ink < borderHalf decl ink sep ∧ borderHalf decl ink sep ≤ ink + sep := by
  have step : ∀ d i s : Int, d ≤ i + s → 0 < s → i < max d (i + s) ∧ max d (i + s) ≤ i + s := by
    intro d i s h1 h2; omega
  exact step decl ink sep hd hs

/-- A named node's anchoring geometry: centre and border half-extents (a
circle's radius twice). What an edge's `(name)` endpoint resolves to. -/
public structure NodeGeom where
  x : Sp
  y : Sp
  a : Sp := 0
  b : Sp := 0
  circle : Bool := false
  /-- Where this node's own text baseline stands, in the picture's
  coordinates: what the `base` family of anchors reads. Nodes centre their
  label, so the baseline sits below the centre by half the measured ink
  less its depth — `Ir.labelBaseline`, the one site that says so, read
  rather than restated here. The default is the centre, which is what a
  node whose body measured nothing has. -/
  base : Sp := 0
  deriving Repr, BEq, Inhabited

/-- A named anchor on a node's border: `(n.west)` and its siblings, pgf's
core positioning vocabulary. The set *and* each one's position are the
`rectangle` shape's own `\anchor` declarations (pgf,
`pgfmoduleshapes.code.tex`, `\pgfdeclareshape{rectangle}`): `center`,
`base`, `mid`, the four sides, the four corners, and `base`/`mid` paired
with `east` and `west`.

`mid` sits half an ex above the baseline and an ex is the face's, which
this walk cannot ask for (the same missing measurement `Cx.metric` names) —
so the `mid` family is not a constructor here and is named where it is
written. -/
public inductive NodeAnchor where
  | center
  | north | south | east | west
  | northEast | northWest | southEast | southWest
  | base | baseEast | baseWest
  deriving Repr, BEq, Inhabited

/-- The anchor a spelling names, keyed on pgf's own name with its spaces
removed. An endpoint's tokens are space-filtered before its name is joined,
so `south west` — pgf's declared spelling — and `southwest` arrive here as
the same string, and one table answers both. -/
private def nodeAnchorOf : String → Option NodeAnchor
  | "center" => some .center
  | "north" => some .north
  | "south" => some .south
  | "east" => some .east
  | "west" => some .west
  | "northeast" => some .northEast
  | "northwest" => some .northWest
  | "southeast" => some .southEast
  | "southwest" => some .southWest
  | "base" => some .base
  | "baseeast" => some .baseEast
  | "basewest" => some .baseWest
  | _ => none

/-- Milli cosine of 45°, ⌊1000·cos 45° + ½⌋ = 707: where a circle's corner
anchors stand. pgf's `circle` shape puts `north east` on the *circle* at
45° (`\pgfdeclareshape{circle}`), not on the bounding box's corner, so a
corner is the radius times this on each axis. -/
private def diag45 : Int := 707

/-- The horizontal reach of a corner anchor: a rectangle's corner is its
own border, a circle's the point on the circle at 45°. -/
public def NodeGeom.cornerA (g : NodeGeom) : Sp :=
  if g.circle then g.a * diag45 / 1000 else g.a

/-- The vertical reach of a corner anchor. -/
public def NodeGeom.cornerB (g : NodeGeom) : Sp :=
  if g.circle then g.b * diag45 / 1000 else g.b

/-- The baseline the `base` family stands on, held inside the node's own
extent. The clamp is inert wherever the extent covers the label's ink —
which is what `Ir.Pic.nodeExtent_covers` says of the number `evalNode`
registers — and a guard where a metric answers a descender deeper than the
node's own border: an anchor may not name a point outside the box every
relative placement measures from. -/
public def NodeGeom.baseY (g : NodeGeom) : Sp :=
  max (g.y - g.b) (min (g.y + g.b) g.base)

/-- Where a named anchor stands. Arithmetic on the centre and the
half-extents the node registered, arm by arm so each position reads off the
declaration it came from rather than off an offset table. -/
public def NodeGeom.anchorPoint (g : NodeGeom) : NodeAnchor → Sp × Sp
  | .center => (g.x, g.y)
  | .north => (g.x, g.y + g.b)
  | .south => (g.x, g.y - g.b)
  | .east => (g.x + g.a, g.y)
  | .west => (g.x - g.a, g.y)
  | .northEast => (g.x + g.cornerA, g.y + g.cornerB)
  | .northWest => (g.x - g.cornerA, g.y + g.cornerB)
  | .southEast => (g.x + g.cornerA, g.y - g.cornerB)
  | .southWest => (g.x - g.cornerA, g.y - g.cornerB)
  | .base => (g.x, g.baseY)
  | .baseEast => (g.x + g.a, g.baseY)
  | .baseWest => (g.x - g.a, g.baseY)

/-- Each corner is exactly its two sides, on a node whose corners are its
own border: the pairing rather than four coordinates restated, so a sign
error in the table is one failing conjunct. `offset_corners_exact` is the
same shape one level up, over the relative-placement vocabulary. -/
public theorem anchorPoint_corners_exact (g : NodeGeom) (h : g.circle = false) :
    g.anchorPoint .northEast = ((g.anchorPoint .east).1, (g.anchorPoint .north).2) ∧
    g.anchorPoint .northWest = ((g.anchorPoint .west).1, (g.anchorPoint .north).2) ∧
    g.anchorPoint .southEast = ((g.anchorPoint .east).1, (g.anchorPoint .south).2) ∧
    g.anchorPoint .southWest = ((g.anchorPoint .west).1, (g.anchorPoint .south).2) := by
  have ca : g.cornerA = g.a := by simp only [NodeGeom.cornerA, h]; rfl
  have cb : g.cornerB = g.b := by simp only [NodeGeom.cornerB, h]; rfl
  simp only [NodeGeom.anchorPoint, ca, cb, and_self]

/-- The two sides of an axis are opposite displacements of the centre: a
sign error puts `west` where `east` belongs and this is the conjunct that
fails. The `_exact` sibling of `offset_opposite_exact`. Spelled through
bare `Int` binders because `omega` does not read an `Sp`-typed structure
field — the workaround `Ir.Pic.labelInkSpan_covers_anchor` records. -/
public theorem anchorPoint_opposite_exact (g : NodeGeom) :
    (g.anchorPoint .east).1 - g.x = g.x - (g.anchorPoint .west).1 ∧
    (g.anchorPoint .north).2 - g.y = g.y - (g.anchorPoint .south).2 ∧
    (g.anchorPoint .center) = (g.x, g.y) := by
  have flip : ∀ v d : Int, v + d - v = v - (v - d) := by intro v d; omega
  exact ⟨flip g.x g.a, flip g.y g.b, rfl⟩

/-- **An anchor lies on its own node's border, never outside it.** Every
name this subset resolves is a point of the box the node registered, for
every anchor in the vocabulary — so an edge anchored by name starts inside
the region a relative placement parts, and the placement theorems
(`placeRight_border_exact` and its three siblings) reason about the right
box for an anchored endpoint too. `Ir.Pic.nodeExtent_covers` is the other
half of the pair: that same box holds the label's ink.

The registered `_between` shape, the two named bounds being the extent
box's own corners. A containment rather than an equality because it has to
hold for all twelve at once: a circle's corners stand at the radius times
`diag45`, strictly inside the bounding box, and the `base` family stands
wherever the face put the baseline — held in by `NodeGeom.baseY`, which is
why this needs no hypothesis about the measurement. Every arithmetic step
is a lemma over bare `Int` binders applied to the fields, because `omega`
does not read an `Sp`-typed structure field. -/
public theorem anchorPoint_between (g : NodeGeom) (ha : 0 ≤ g.a) (hb : 0 ≤ g.b)
    (an : NodeAnchor) :
    Ir.Pic.Box.le (g.anchorPoint an, g.anchorPoint an)
      (Ir.Pic.nodeExtentBox g.x g.y g.a g.b) := by
  have key : ∀ p : Sp × Sp, g.x - g.a ≤ p.1 → p.1 ≤ g.x + g.a →
      g.y - g.b ≤ p.2 → p.2 ≤ g.y + g.b →
      Ir.Pic.Box.le ((p, p)) (Ir.Pic.nodeExtentBox g.x g.y g.a g.b) :=
    fun _ h1 h2 h3 h4 => ⟨h1, h3, h2, h4⟩
  have mid : ∀ v d : Int, 0 ≤ d → v - d ≤ v ∧ v ≤ v + d := by intro v d h; omega
  have hi : ∀ v d : Int, 0 ≤ d → v - d ≤ v + d ∧ v + d ≤ v + d := by intro v d h; omega
  have lo : ∀ v d : Int, 0 ≤ d → v - d ≤ v - d ∧ v - d ≤ v + d := by intro v d h; omega
  have cn : ∀ v d c : Int, 0 ≤ c → c ≤ d →
      (v - d ≤ v + c ∧ v + c ≤ v + d) ∧ (v - d ≤ v - c ∧ v - c ≤ v + d) := by
    intro v d c h1 h2; omega
  have dg : ∀ d : Int, 0 ≤ d → 0 ≤ d * 707 / 1000 ∧ d * 707 / 1000 ≤ d := by
    intro d h; omega
  have clamp : ∀ v d p : Int, 0 ≤ d →
      v - d ≤ max (v - d) (min (v + d) p) ∧ max (v - d) (min (v + d) p) ≤ v + d := by
    intro v d p h; omega
  have hca : 0 ≤ g.cornerA ∧ g.cornerA ≤ g.a := by
    simp only [NodeGeom.cornerA, diag45]
    split
    · exact dg g.a ha
    · exact ⟨ha, Int.le_refl _⟩
  have hcb : 0 ≤ g.cornerB ∧ g.cornerB ≤ g.b := by
    simp only [NodeGeom.cornerB, diag45]
    split
    · exact dg g.b hb
    · exact ⟨hb, Int.le_refl _⟩
  have hbase : g.y - g.b ≤ g.baseY ∧ g.baseY ≤ g.y + g.b := by
    simp only [NodeGeom.baseY]; exact clamp g.y g.b g.base hb
  have cx := cn g.x g.a g.cornerA hca.1 hca.2
  have cy := cn g.y g.b g.cornerB hcb.1 hcb.2
  cases an
  · exact key _ (mid g.x g.a ha).1 (mid g.x g.a ha).2 (mid g.y g.b hb).1 (mid g.y g.b hb).2
  · exact key _ (mid g.x g.a ha).1 (mid g.x g.a ha).2 (hi g.y g.b hb).1 (hi g.y g.b hb).2
  · exact key _ (mid g.x g.a ha).1 (mid g.x g.a ha).2 (lo g.y g.b hb).1 (lo g.y g.b hb).2
  · exact key _ (hi g.x g.a ha).1 (hi g.x g.a ha).2 (mid g.y g.b hb).1 (mid g.y g.b hb).2
  · exact key _ (lo g.x g.a ha).1 (lo g.x g.a ha).2 (mid g.y g.b hb).1 (mid g.y g.b hb).2
  · exact key _ cx.1.1 cx.1.2 cy.1.1 cy.1.2
  · exact key _ cx.2.1 cx.2.2 cy.1.1 cy.1.2
  · exact key _ cx.1.1 cx.1.2 cy.2.1 cy.2.2
  · exact key _ cx.2.1 cx.2.2 cy.2.1 cy.2.2
  · exact key _ (mid g.x g.a ha).1 (mid g.x g.a ha).2 hbase.1 hbase.2
  · exact key _ (hi g.x g.a ha).1 (hi g.x g.a ha).2 hbase.1 hbase.2
  · exact key _ (lo g.x g.a ha).1 (lo g.x g.a ha).2 hbase.1 hbase.2

/-- A `(name.anchor)` endpoint split into its two halves. pgf reads
everything after the first `.` as the anchor name (`\pgfpointanchor`), so a
node's own name carries no dot. -/
private def splitAnchor (s : String) : Option (String × String) :=
  match s.splitOn "." with
  | [nm, an] => if nm.isEmpty || an.isEmpty then none else some (nm, an)
  | _ => none

/-- Shapes and named losses, accumulated across the unrolled walk. A
diagnostic dedupes on its message: one construct looped over forty times
is one problem, not forty. -/
public structure Ev where
  shapes : Array Ir.Pic.Shape := #[]
  diags : Array PDiag := #[]
  /-- The box a `\useasboundingbox` declared (`Ir.Pic.Picture.declared`). -/
  declared : Option Ir.Pic.Box := none
  /-- Each placed node's border, text extent plus `inner sep`
  (`Ir.Pic.Picture.borders`). -/
  borders : Array Ir.Pic.Box := #[]
  /-- Named nodes seen so far, latest first: what a `\draw` endpoint's
  `(name)` resolves against. -/
  nodes : List (String × NodeGeom) := []
  /-- Did some path or node read the picture's inherited options? If
  nothing did, the picture's own bracket names them rather than dropping
  them: `\fill`'s bracket is a colour spelling, not a key list, so a
  picture of nothing but fills reads no keys at all. -/
  readOpts : Bool := false
  /-- Did some construct the subset could not reach swallow declarations?
  A node inside an `\ifnum` whose test the walk cannot compute is a
  different refusal from a node nothing declared: the first traces to a
  named gap, the second to the document. Set only where that gap was
  named, so the demotion below can never be the whole story. -/
  gapped : Bool := false
  /-- How many nodes this run refused because the node they are placed
  relative to was not in scope yet. The walk is re-run with what it
  learned (`evalFixed`), so a node placed relative to one declared later
  resolves; a count that stops falling is a cycle or a name no node
  carries, and the refusals the final run carries name it. -/
  deferred : Nat := 0

private def Ev.diag (ev : Ev) (d : PDiag) : Ev :=
  if ev.diags.any (·.2 == d.2) then ev else { ev with diags := ev.diags.push d }

/-- The evaluated marks and authored bounds passed to both backends.
Node anchor borders and measured text remain separate: a declared text
height or negative padding may deliberately put text outside its border. -/
public def Ev.toPicture (ev : Ev) (baseline : Option Sp := none) : Ir.Pic.Picture :=
  { shapes := ev.shapes, declared := ev.declared, borders := ev.borders, baseline }

/-- Every emitted label's measured text lies in the reserved picture
extent, unless the author explicitly replaced that extent. This projects
the IR hull contract onto the actual picture producer; it does not claim
that an authored node border encloses its text. -/
public theorem Ev.labelExtent_covers (ev : Ev) (m : Ir.Pic.LabelMetric)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (baseline : Option Sp)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ ev.shapes)
    (hd : ev.declared = none) :
    Ir.Pic.Box.le (Ir.Pic.labelTextBox x y align (m content scale))
      ((ev.toPicture baseline).box m) := by
  have cover := (Ir.Pic.Picture.box_covers (ev.toPicture baseline) m hd).1 _ hs
  apply Ir.Pic.Box.le_trans (b := Ir.Pic.labelGlyphBox x y align (m content scale)) _ cover
  exact ⟨Int.le_refl _, Int.min_le_right _ _, Int.le_refl _, Int.le_max_right _ _⟩

/-- `(x,y) rectangle (x',y')` (or `++(dx,dy)`, relative) from token `i` to
the end: the rectangle's corners in sp, sorted — `(x0, y0, x1, y1)` with
`x0 ≤ x1` and `y0 ≤ y1`. `what` names the statement and `cost` what a
refusal costs, so each caller's diagnostic says its own loss. -/
private def readRect (cx : Cx) (env : List (String × Val)) (ts : Array Tok) (i0 : Nat)
    (what cost : String) : Except PDiag (Sp × Sp × Sp × Sp) := Id.run do
  let mut i := i0
  let c1 ← match readCoord ts i with
    | .ok v => pure v
    | .error e => return .error (.E0333, s!"in {what}, {e}; {cost}")
  let ((x1s, y1s), i1) := c1
  i := i1
  unless ts[i]? == some (.ident "rectangle") do
    return .error (.W0334, s!"{what} with \
{((ts[i]?).map tokText).getD "no shape operation"} is outside the rendered picture \
subset; {cost}")
  i := i + 1
  let mut relative := false
  if ts[i]? == some (.sym '+') && ts[i+1]? == some (.sym '+') then
    relative := true
    i := i + 2
  let c2 ← match readCoord ts i with
    | .ok v => pure v
    | .error e => return .error (.E0333, s!"in {what}, {e}; {cost}")
  let ((x2s, y2s), i2) := c2
  if h : i2 < ts.size then
    return .error (.W0334, s!"{what} continues with {tokText ts[i2]}, outside the \
rendered picture subset; {cost}")
  let vals ← match evalNum env x1s, evalNum env y1s, evalNum env x2s, evalNum env y2s with
    | .ok a, .ok b, .ok c, .ok d => pure (a, b, c, d)
    | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e =>
      return .error (.E0333, s!"in {what}, {e}; {cost}")
  let (x1m, y1m, x2m, y2m) := vals
  let (x2m, y2m) := if relative then (x1m + x2m, y1m + y2m) else (x2m, y2m)
  let (x1, y1) := (cx.toSp x1m, cx.toSp y1m)
  let (x2, y2) := (cx.toSp x2m, cx.toSp y2m)
  return .ok (min x1 x2, min y1 y2, max x1 x2, max y1 y2)

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
  match readRect cx env ts i "'\\fill'" "the shape is not drawn" with
  | .ok (x0, y0, x1, y1) => return .ok (.rect x0 y0 (x1 - x0) (y1 - y0) color)
  | .error d => return .error d

/-- `\useasboundingbox (a) rectangle (b);`: the declared box, corners sorted.
The one path shape the declaration takes here is the rectangle, read by the
same reader `\fill` uses, so the two cannot disagree about a corner. -/
private def evalBBox (cx : Cx) (env : List (String × Val)) (toks : Array Tok) :
    Except PDiag Ir.Pic.Box := do
  let (x0, y0, x1, y1) ← readRect cx env (toks.filter (· != .space)) 0
    "'\\useasboundingbox'" "the declared box is ignored"
  return ((x0, y0), (x1, y1))

/-- One line of a node label: its inline content and the size it sets at,
per mille of the node's own. A label is one line per `\\`, because
`Ir.Pic.Shape.label` carries one size and one anchor — so a second line is
a second shape, stacked by `nodeLineLead`, not a break inside one. -/
public abbrev LabelLine := Array Ir.Inline × Nat

/-- The baseline-to-baseline distance between a node label's lines: the
engine's own leading over the size the *following* line sets at, as TeX's
`\baselineskip` is the value current where the line ends. Reusing
`Ir.leadingFor` rather than restating `plain.tex`'s 1.2 keeps one source for
the engine's vertical rhythm — a second constant here would drift from the
one every paragraph uses.

The size is the document's body size times the label's scale, the same
size the artifact's label metric reads. -/
private def nodeLineLead (bodySize : Sp) (scale : Nat) : Sp :=
  Ir.leadingFor (bodySize * (scale : Int) / 1000)

/-- The stand-in a label sets when its salvage comes to nothing and a loss
was named: the same bracketed ellipsis a degraded formula inks, for the
same reason — a blank tells a reader nothing stood there.
`nodeLabel_accounts` is the statement that the case is never silent. -/
public def nodeFloorPlaceholder : String := String.ofList Ir.mathFloorPlaceholder

/-- Commands whose content is invisible by definition: a phantom sets a box
of its argument's size and no ink. Read rather than refused, so a
`\vphantom{p}Member` label is `Member` and a body of nothing but a phantom
is honestly empty — the placeholder would claim ink where TeX shows none.
The height a phantom props is not lost either: this subset measures no
node body's extent at all (see the emission note in `evalNode`), so there
is no height here to keep. -/
public def phantomCtrl : List String := ["vphantom", "hphantom", "phantom"]

/-- What a node body's salvage is in the middle of. The modes let the walk
read one token at a time, so a construct spanning several of them needs no
lookahead and the recursion stays structural — the shape `step` already
uses for the statement machine. -/
private inductive SalMode where
  | text
  /-- An optional `[...]` run may stand here: it belongs to the construct
  just read (`\\[2ex]` is how an author spaces a label's lines, and
  `\textcolor[rgb]{...}` names a colour model), so it is dropped where it
  appears. `then_` is how many naming groups follow it. -/
  | optMaybe (then_ : Nat)
  /-- Inside that run, dropping to its `]`. -/
  | optDrop (then_ : Nat)
  /-- The next `n` groups name rather than carry (`Ir.floorNamedArgs`), so
  they are dropped instead of salvaged: `\ref{key}`'s key is not a word the
  label meant to say. -/
  | dropArgs (n : Nat)
  /-- `\textcolor`'s first group: the palette role. -/
  | colorRole
  /-- `\textcolor`'s second group, to set in the role it named. -/
  | colorBody (c : Ir.Color) (role : Option String)
  /-- A text command's argument (`\textbf{...}`, read from `Cx.argStyles`):
  the next group, or the one word standing there, sets in the style the
  command names — what the same command does in a paragraph. -/
  | styleBody (st : Ir.Style)
  deriving Repr, BEq, Inhabited

/-- A node label under construction: the lines already closed, the current
line's inlines and its pending text run, the size that line sets at, and
the losses named so far. `fresh` is whether the current line has had
anything contributed yet — a size switch may only open a line, since a
label shape carries one size. -/
private structure Sal where
  lines : Array LabelLine := #[]
  out : Array Ir.Inline := #[]
  text : String := ""
  scale : Nat := 1000
  styles : Array Ir.Style := #[]
  consumeNocorr : Bool := false
  next : Option Tok := none
  fresh : Bool := true
  /-- How many groups deep the walk stands. A size switch inside a group is
  the group's own, and a label shape carries one size, so only a switch at
  the top of a line can be honoured — one inside a group is named rather
  than applied to the line or dropped in silence. -/
  depth : Nat := 0
  /-- Whether closing a line trims its ends. A label's own lines are
  trimmed at both, as TikZ sets a node's text; a spliced body's are not,
  because the body's edges stand inside a line, and `splice` trims only
  the ends a `\\` inside the body made. -/
  trim : Bool := true
  diags : Array PDiag := #[]
  mode : SalMode := .text
  deriving Inhabited

namespace Sal

/-- Add readable characters to the current line. -/
private def str (s : Sal) (t : String) : Sal :=
  if t.isEmpty then s else { s with text := s.text ++ t, fresh := false }

/-- Close the pending text run, so an inline can follow it in order. -/
private def flush (s : Sal) : Sal :=
  if s.text.isEmpty then s
  else
    let xs := s.styles.foldr (fun st inner => #[.styled st inner]) #[.text s.text]
    { s with out := xs.foldl Array.push s.out, text := "" }

/-- Add elaborated inlines under the declarations in force. -/
private def inlines (s : Sal) (xs : Array Ir.Inline) : Sal :=
  if xs.isEmpty then s
  else
    let f := s.flush
    let xs := f.styles.foldr (fun st inner => #[.styled st inner]) xs
    { f with out := xs.foldl Array.push f.out, fresh := false }

/-- Add one elaborated inline (a math span, a coloured group). -/
private def inline (s : Sal) (i : Ir.Inline) : Sal :=
  s.inlines #[i]

private def addDiags (s : Sal) (ds : Array PDiag) : Sal :=
  { s with diags := ds.foldl Array.push s.diags }

/-- Back to reading content: a mode the token at hand does not continue. -/
private def mode0 (s : Sal) : Sal := { s with mode := .text }

/-- Name one construct the subset could not read. The label keeps what it
can read; the diagnostic says what was not drawn. -/
private def refuse (s : Sal) (what : String) : Sal :=
  { s with diags := s.diags.push (.W0334, s!"{what} in a node body is outside \
the rendered picture subset; the label sets the text it can read") }

/-- Space trimmed off a line's left end, its right end, or both, as the
braces' inner space is in TeX. Only drops characters, so it cannot invent
ink. -/
private def trimEnds (left right : Bool) (xs : Array Ir.Inline) : Array Ir.Inline :=
  let trimL (t : String) : String := String.ofList (t.toList.dropWhile (· == ' '))
  let trimR (t : String) : String :=
    String.ofList ((t.toList.reverse.dropWhile (· == ' ')).reverse)
  let n := xs.size
  let xs := xs.mapIdx fun i inl =>
    if let .text f := inl then
      let f := if left && i == 0 then trimL f else f
      .text (if right && i + 1 == n then trimR f else f)
    else inl
  xs.filter (· != .text "")

/-- Close the current line and start the next: what `\\` does. -/
private def newline (s : Sal) : Sal :=
  let s := s.flush
  { s with lines := s.lines.push (trimEnds s.trim s.trim s.out, s.scale)
           out := #[], text := "", scale := 1000, fresh := true, mode := .text }

/-- A nested group's own salvage, sharing the losses named so far and the
line's size but not its content. -/
private def sub (s : Sal) : Sal := { scale := s.scale, diags := s.diags, depth := s.depth }

/-- The salvage a styled or coloured body is walked in (`splice`): one
group deeper, so a size switch inside it is named rather than set, and
with its lines' ends untrimmed, since the body's edges are inside a line. -/
private def inner (s : Sal) : Sal := { s.sub with depth := s.depth + 1, trim := false }

/-- Splice a nested body's salvage into this label, every line of it
wrapped (`wrap`, a style or a colour): the body's first line continues the
current one, and each later line — a `\\` inside the body — closes the
current line and opens the next, as the break does in TeX. So a break
inside `\textbf{…}` is a real break whose both lines are bold, where
merging the lines would have been a loss nothing named. The body was
walked untrimmed (`inner`), so a space just inside its braces stays, as it
does in a paragraph, and only the ends a break made are trimmed here. An
empty line wraps nothing, so no empty wrapper ships; the body's own losses
join this label's. The body was walked one group deeper, so no size switch
inside it set a line's size — a size it asked for was named instead. -/
private def splice (s : Sal) (body : Sal)
    (wrap : Bool → Bool → Array Ir.Inline → Array Ir.Inline) : Sal := Id.run do
  let body := body.newline
  let n := body.lines.size
  let mut s := s.addDiags (body.diags.extract s.diags.size body.diags.size)
  for k in [0:n] do
    if let some (xs, _) := body.lines[k]? then
      if k > 0 then s := s.newline
      let xs := trimEnds (0 < k) (k + 1 < n) xs
      unless xs.isEmpty do s := s.inlines (wrap (k == 0) (k + 1 == n) xs)
  return { s with mode := .text }

/-- Does this label ship ink? The inlines it ships, counted across its
lines: an empty line contributes none, so a label of nothing but blank
lines is inkless — which is what `labelFloor` pays for. `inked` counts
inlines rather than glyphs, and that is exact for what it guards: every
inline the salvage pushes is a non-empty text run, a math span (which
carries its own floor) or a non-empty coloured or styled group (`splice`
wraps no empty line). -/
private def inkCount (ls : Array LabelLine) : Nat := ls.foldl (fun n l => n + l.1.size) 0

private def inked (ls : Array LabelLine) : Bool := 0 < inkCount ls

/-- Has the machine come to rest? `.text` has, and so has `.optMaybe 0` —
a trailing option run *may* follow a construct and need not. Every other
mode means a construct the body opened and never closed, which is why
`nodeLabel` names it: a mode pending at the end of a body has eaten the
rest of that body, and eating it silently is the very loss the floor
exists to prevent. -/
private def settled : SalMode → Bool
  | .text => true
  | .optMaybe k => k == 0
  | .optDrop _ | .dropArgs _ | .colorRole | .colorBody _ _ | .styleBody _ => false

/-- Settle a mode this token does not continue, so the content arm reads it
instead. Idempotent on `.text`, which is why `salOne` may apply it twice and
so hand a token from a construct's option position to its argument position
to the line. A colour whose body never came is named here rather than
dropped in silence: the mathematics of it is that the *role* was read and
the group it was to paint was not. -/
private def settle (t : Tok) (s : Sal) : Sal :=
  match s.mode, t with
  -- A starred command's star is part of its name (`\hspace*{1pt}`), and a
  -- space before an argument is the command's, as TeX reads it.
  | .optMaybe _, .sym '[' => s
  | .optMaybe _, .sym '*' => s
  | .optMaybe _, .space => s
  | .optMaybe k, _ => if k == 0 then s.mode0 else { s with mode := .dropArgs k }
  | .optDrop _, _ => s
  | .dropArgs _, .space => s
  | .dropArgs _, .group _ => s
  | .dropArgs _, _ => s.mode0
  | .colorRole, .space => s
  | .colorRole, .group _ => s
  | .colorRole, .sym '[' => { (s.refuse "a colour model") with mode := .optDrop 1 }
  | .colorRole, _ => (s.refuse "a colour with no role").mode0
  | .colorBody _ _, .space => s
  | .colorBody _ _, .group _ => s
  | .colorBody _ _, _ => (s.refuse "a colour with no body").mode0
  -- A text command's argument is a group or the one word standing there, as
  -- the elaborator reads it; anything else (a command, math, an
  -- environment) is not an argument this subset can style, so the style is
  -- named and the token goes on to be read as content.
  | .styleBody _, .space => s
  | .styleBody _, .group _ => s
  | .styleBody _, .ident _ => s
  | .styleBody _, .num _ => s
  | .styleBody _, .sym _ => s
  | .styleBody _, _ => (s.refuse "a text style whose argument is not a group").mode0
  | .text, _ => s

end Sal

/-- The mode a control sequence the subset cannot draw puts the salvage
into, and the loss it names. Five are read rather than refused, because
nothing a reader can see is lost: `\\` opens a line, a phantom is
invisible by definition, a size switch opening a line sets that line's
size, `\textcolor` sets its body in the role it names, and a text command
(`\textbf`, `\emph`, `\textsc`, …) sets its argument in its style.
Everything else drops its own name — and the arguments `Ir.floorNamedArgs`
says name rather than carry, so a key or a length never rides onto the
page as ink — and keeps what its content groups say.

`Ir.floorNamedArgs` is the math floor's own table, read here rather than
restated: which arguments of a command are names is one fact about LaTeX,
and a second list would drift from the first. The text commands are the
elaborator's own table for the same reason (`Cx.argStyles`), and a size
switch is a step of the document's own ladder (`Cx.ladder`). -/
private def salCtrl (cx : Cx) (env : List (String × Val))
    (n : String) (s : Sal) : Sal :=
  match env.lookup n with
  | some v => s.str v.text
  | none =>
    if n == "nocorr" && s.consumeNocorr then s
    else if n == "\\" then { s.newline with mode := .optMaybe 0 }
    else if phantomCtrl.contains n then { s with mode := .optMaybe 1 }
    else if n == "textcolor" then { s with mode := .colorRole }
    else match cx.argStyles.lookup n with
    | some st => { s with mode := .styleBody st }
    | none =>
    match cx.ladder.lookup n with
      | some k =>
        if s.fresh && s.depth == 0 then { s with scale := k }
        else
          (s.refuse s!"the size '\\{n}' inside a label line").mode0
      | none =>
      match cx.declStyles.lookup n with
        | some st =>
          let s := s.flush
          { s with styles := s.styles.push st }
        | none =>
          let s := s.refuse s!"unknown macro '\\{n}'"
          match Ir.floorNamedArgs.lookup n with
          | some arity => { s with mode := .optMaybe arity }
          | none => { s with mode := .optMaybe 0 }

private def fontCmdNocorr : Tok → Bool
  | .ctrl "nocorr" => true
  | _ => false

private def fontCmdEdges (body : List Tok) (next? : Option Tok) : Bool × Bool :=
  Ir.fontCmdEdges (· == .space) fontCmdNocorr
    (fun
      | some (.sym ',') | some (.sym '.') => false
      | _ => true)
    body next?

mutual

/-- Salvage a node body's tokens into label lines: one fold, the only
recursion into a pre-matched group subtree, so totality is structural. -/
private def salList (cx : Cx) (env : List (String × Val)) : List Tok → Sal → Sal
  | [], s => s
  | t :: rest, s => salList cx env rest (salOne cx env t { s with next := rest.head? })

/-- One token. The mode settles first — twice, because a construct's own
run can hand the same token from one mode to the next (`\hspace` opens
`optMaybe 1`, and a `*` then has to stay with the *name* rather than count
as the argument) — and `.text` is a fixed point, so two passes reach it.
After settling, the content arm runs at most once per token and the walk
needs no lookahead beyond `Sal.next`, the token after a text-command
argument. -/
private def salOne (cx : Cx) (env : List (String × Val)) (t : Tok) (s : Sal) : Sal :=
  let s : Sal := Sal.settle t (Sal.settle t s)
  match s.mode with
  -- Only a `[`, a `*` or a space reaches here: settling sent every other
  -- token on. A star belongs to the name it follows, as in LaTeX.
  | .optMaybe k => if t == .sym '[' then { s with mode := .optDrop k } else s
  -- `]` closes the run and leaves another one possible: the options trail
  -- the named arguments in `\raisebox{lift}[h][d]{body}`, so sweeping only
  -- one left the second on the page.
  | .optDrop k => if t == .sym ']' then { s with mode := .optMaybe k } else s
  -- Only a group reaches here, so only a group counts as an argument: a
  -- counter any token satisfies spent `\color`'s drop on the `\textcolor`
  -- that followed it and set the colour name as ink.
  | .dropArgs n => { s with mode := .optMaybe (if n ≤ 1 then 0 else n - 1) }
  | .colorRole =>
    match t with
    | .group g =>
      match evalColor cx env g.toArray with
      | .ok c =>
        let role : Option String := match g.filter (· != .space) with
          | [.ident w] => if cx.pal.entries.any (·.1 == w) then some w else none
          | _ => none
        { s with mode := .colorBody c role }
      | .error e => { (s.refuse s!"the colour ({e})") with mode := .text }
    | _ => s
  | .colorBody c role =>
    match t with
    | .group g => s.splice (salList cx env g s.inner) fun _ _ xs => #[.colored c role xs]
    | _ => s
  -- Only a space, a group or one word reaches here (`Sal.settle`): the
  -- group is the argument, and a word standing where it would be is the
  -- argument too, as the elaborator reads `\textbf x`.
  | .styleBody st =>
    let add (s : Sal) (raw : List Tok) (inner : Array Ir.Inline) : Sal :=
      { (s.inlines (Ir.fontCmdInlines st (fontCmdEdges raw s.next) inner)) with mode := .text }
    match t with
    | .group g =>
      let edges := fontCmdEdges g s.next
      s.splice (salList cx env g { s.inner with consumeNocorr := true }) fun first last xs =>
        Ir.fontCmdInlines st (edges.1 && first, edges.2 && last) xs
    | .ident w => add s [.ident w] #[.text w]
    | .num m => add s [.num m] #[.text (milliString m)]
    | .sym c => add s [.sym c] #[.text (String.singleton c)]
    | _ => s
  | .text =>
    match t with
    | .ident w => s.str w
    | .num m => s.str (milliString m)
    | .space => s.str " "
    | .sym c => s.str (String.singleton c)
    -- A group is grouping: its content is the line's, and a size it set is
    -- the group's own, as TeX scopes a size switch.
    | .group g =>
      let nested : Sal := { s with depth := s.depth + 1 }
      let nested : Sal := { nested with consumeNocorr := false }
      let inner := salList cx env g nested
      let inner := if inner.styles == s.styles then inner else inner.flush
      let inner : Sal := { inner with mode := .text }
      let inner : Sal := { inner with scale := s.scale }
      let inner : Sal := { inner with styles := s.styles }
      let inner : Sal := { inner with depth := s.depth }
      let inner : Sal := { inner with consumeNocorr := s.consumeNocorr }
      { inner with next := s.next }
    | .math d body =>
      let (inl, ds) := cx.math d body.toArray
      (s.inline inl).addDiags ds
    | .other what => s.refuse what
    | .ctrl n => salCtrl cx env n s

end

/-- The lines a label actually ships: its salvage, or the declared
placeholder when the salvage kept nothing and a loss was named. The same
shape `Ir.floorInk` gives a degraded formula, and for the same reason — a
blank page region is not an honest floor, because it tells a reader nothing
stood there. -/
public def labelFloor (lines : Array LabelLine) (named : Bool) : Array LabelLine :=
  if Sal.inked lines || !named then lines
  else #[(#[.text nodeFloorPlaceholder], 1000)]

/-- **A label that named a loss ships ink.** The registered `_accounts`
shape: an empty result is paid for by a write. Before it the engine did the
reverse — one unreadable macro in one body dropped the whole label, so a
diagram of such nodes shipped an outline with nothing inside it while every
warning said so where no reader looks.

What it does not say, since the distinction matters: it is one-sided. It
holds for a salvage that kept nothing at all, because the placeholder then
pays for it. `nodeLabel_source_mem` bounds the result by its actual text
sources, including elaborated mathematics. The whole-label rows in
`pictureNodeFloorChecks` cover selection: naming arguments are discarded
and readable content is kept. -/
public theorem labelFloor_accounts (lines : Array LabelLine) (named : Bool) (h : named) :
    (0 < (labelFloor lines named).foldl (fun n l => n + l.1.size) 0 : Bool) := by
  unfold labelFloor
  split
  · rename_i hc
    apply decide_eq_true
    have hi : Sal.inked lines := by
      simpa only [h, Bool.not_true, Bool.or_false] using hc
    have hk : 0 < Sal.inkCount lines := of_decide_eq_true hi
    simpa only [Sal.inkCount] using hk
  · decide

/-- A node body's label lines. Words, numbers and bound macros become text,
a math span elaborates through `Cx.math`, a text command sets its argument
in the style the elaborator's own table gives it (`Cx.argStyles`), `\\`
opens a line, and a construct the subset cannot draw drops its own spelling
and keeps what it says (`salCtrl`).

**A body the subset cannot fully read still ships the text it can read.**
Dropping a label whole is the worse recovery: the reader sees an empty
diagram and has no way to know a word stood there, while the diagnostic
that would have told them is the thing they never see. This is the same
judgement `Ir.mathFloor` makes for a formula the engine cannot set, one
module over — and the same placeholder closes it, so a named loss never
ships a blank (`labelFloor_accounts`). -/
public def nodeLabel (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    Array LabelLine × Array PDiag :=
  let walked := salList cx env toks {}
  -- A construct the body opened and never closed has eaten the rest of the
  -- body: an unterminated `[...]`, a `\textcolor` whose body never came, a
  -- naming argument that is not there. Named here, at the one place that
  -- can see the machine come to rest, because the alternative is the loss
  -- this floor exists to prevent — content gone with nothing said.
  let s := if Sal.settled walked.mode then walked
           else walked.refuse "a node body that ends mid-construct"
  let s := s.newline
  (labelFloor s.lines (!s.diags.isEmpty), s.diags)

/-- The page side of `labelFloor_accounts`: a node body whose salvage named
a loss ships ink, whatever the body was. -/
public theorem nodeLabel_accounts (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    ¬ (nodeLabel cx env toks).2.isEmpty →
      (0 < (nodeLabel cx env toks).1.foldl (fun n l => n + l.1.size) 0 : Bool) := by
  intro hd
  simp only [nodeLabel] at hd ⊢
  exact labelFloor_accounts _ _ (by simpa using hd)

private def textFrom (P : Char → Prop) (s : String) : Prop :=
  ∀ c ∈ s.toList, P c

private def inlinesFrom (P : Char → Prop) (xs : Array Ir.Inline) : Prop :=
  ∀ i ∈ xs, textFrom P (Ir.plainTextOne i)

private def linesFrom (P : Char → Prop) (lines : Array LabelLine) : Prop :=
  ∀ line ∈ lines, inlinesFrom P line.1

private def Sal.from (P : Char → Prop) (s : Sal) : Prop :=
  linesFrom P s.lines ∧ inlinesFrom P s.out ∧ textFrom P s.text

@[simp] private theorem textFrom_empty (P : Char → Prop) : textFrom P "" := by
  simp [textFrom]

@[simp] private theorem textFrom_append (P : Char → Prop) (s t : String) :
    textFrom P (s ++ t) ↔ textFrom P s ∧ textFrom P t := by
  simp only [textFrom, String.toList_append, List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨hs, ht⟩ c (hc | hc)
    · exact hs c hc
    · exact ht c hc

private theorem plainTextList_from (P : Char → Prop) (xs : List Ir.Inline) :
    textFrom P (Ir.plainTextList xs) ↔
      ∀ i ∈ xs, textFrom P (Ir.plainTextOne i) := by
  induction xs with
  | nil => simp [Ir.plainTextList]
  | cons i xs ih => simp [Ir.plainTextList, ih]

private theorem plainText_from (P : Char → Prop) (xs : Array Ir.Inline) :
    textFrom P (Ir.plainText xs) ↔ inlinesFrom P xs := by
  simpa [Ir.plainText, inlinesFrom] using plainTextList_from P xs.toList

@[simp] private theorem inlinesFrom_empty (P : Char → Prop) :
    inlinesFrom P #[] := by
  simp [inlinesFrom]

@[simp] private theorem linesFrom_empty (P : Char → Prop) :
    linesFrom P #[] := by
  simp [linesFrom]

@[simp] private theorem inlinesFrom_singleton (P : Char → Prop) (i : Ir.Inline) :
    inlinesFrom P #[i] ↔ textFrom P (Ir.plainTextOne i) := by
  simp [inlinesFrom]

@[simp] private theorem inlinesFrom_append (P : Char → Prop) (xs ys : Array Ir.Inline) :
    inlinesFrom P (xs ++ ys) ↔ inlinesFrom P xs ∧ inlinesFrom P ys := by
  simp only [inlinesFrom, Array.mem_append]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨hx, hy⟩ i (hi | hi)
    · exact hx i hi
    · exact hy i hi

@[simp] private theorem textFrom_styled (P : Char → Prop) (st : Ir.Style)
    (xs : Array Ir.Inline) :
    textFrom P (Ir.plainTextOne (.styled st xs)) ↔ inlinesFrom P xs :=
  plainText_from P xs

@[simp] private theorem textFrom_colored (P : Char → Prop) (c : Ir.Color)
    (role : Option String) (xs : Array Ir.Inline) :
    textFrom P (Ir.plainTextOne (.colored c role xs)) ↔ inlinesFrom P xs :=
  plainText_from P xs

private theorem styles_from (P : Char → Prop) (sts : Array Ir.Style)
    (xs : Array Ir.Inline) (hx : inlinesFrom P xs) :
    inlinesFrom P (sts.foldr (fun st inner => #[.styled st inner]) xs) := by
  apply Array.foldr_induction (motive := fun _ acc => inlinesFrom P acc) hx
  intro i acc hacc
  simpa using hacc

private theorem appendRun_from (P : Char → Prop) (xs ys : Array Ir.Inline)
    (hx : inlinesFrom P xs) (hy : inlinesFrom P ys) :
    inlinesFrom P (ys.foldl Array.push xs) := by
  have eq : ys.foldl Array.push xs = xs ++ ys := by
    simpa using (Array.foldl_push_eq_append (as := ys) (bs := xs) (f := id) rfl)
  rw [eq]
  exact (inlinesFrom_append P xs ys).mpr ⟨hx, hy⟩

private theorem Sal.str_from (P : Char → Prop) (s : Sal) (t : String)
    (hs : s.from P) (ht : textFrom P t) : (s.str t).from P := by
  unfold str
  split
  · exact hs
  · exact ⟨hs.1, hs.2.1, (textFrom_append P s.text t).mpr ⟨hs.2.2, ht⟩⟩

private theorem Sal.flush_from (P : Char → Prop) (s : Sal)
    (hs : s.from P) : s.flush.from P := by
  unfold flush
  split
  · exact hs
  · exact ⟨hs.1, appendRun_from P _ _ hs.2.1
      (styles_from P _ _ (by simpa [Ir.plainTextOne] using hs.2.2)), textFrom_empty P⟩

private theorem Sal.inlines_from (P : Char → Prop) (s : Sal) (xs : Array Ir.Inline)
    (hs : s.from P) (hx : inlinesFrom P xs) : (s.inlines xs).from P := by
  unfold inlines
  split
  · exact hs
  · have hf := s.flush_from P hs
    exact ⟨hf.1, appendRun_from P _ _ hf.2.1 (styles_from P _ _ hx), hf.2.2⟩

private theorem Sal.inline_from (P : Char → Prop) (s : Sal) (i : Ir.Inline)
    (hs : s.from P) (hi : textFrom P (Ir.plainTextOne i)) :
    (s.inline i).from P :=
  s.inlines_from P _ hs ((inlinesFrom_singleton P i).mpr hi)

private theorem Sal.trimEnds_from (P : Char → Prop) (left right : Bool)
    (xs : Array Ir.Inline) (hx : inlinesFrom P xs) :
    inlinesFrom P (Sal.trimEnds left right xs) := by
  have trimL (s : String) (h : textFrom P s) :
      textFrom P (String.ofList (s.toList.dropWhile (· == ' '))) := by
    intro c hc
    exact h c (List.dropWhile_subset _ (by simpa using hc))
  have trimR (s : String) (h : textFrom P s) :
      textFrom P (String.ofList ((s.toList.reverse.dropWhile (· == ' ')).reverse)) := by
    intro c hc
    apply h c
    exact List.mem_reverse.mp (List.dropWhile_subset _ (by simpa using hc))
  intro i hi
  obtain ⟨k, hk, rfl⟩ := Array.exists_of_mem_mapIdx (Array.mem_filter.mp hi).1
  have h := hx xs[k] (Array.getElem_mem hk)
  split
  · rename_i text he
    have ht : textFrom P text := by simpa [he, Ir.plainTextOne] using h
    dsimp only [Ir.plainTextOne]
    split
    · apply trimR
      split
      · exact trimL _ ht
      · exact ht
    · split
      · exact trimL _ ht
      · exact ht
  · exact h

private theorem Sal.newline_from (P : Char → Prop) (s : Sal) (hs : s.from P) :
    s.newline.from P := by
  have hf := s.flush_from P hs
  refine ⟨?_, inlinesFrom_empty P, textFrom_empty P⟩
  intro line hl
  rcases Array.mem_push.mp hl with h | h
  · exact hf.1 line h
  · subst line
    exact trimEnds_from P _ _ _ hf.2.1

@[simp] private theorem Sal.inner_from (P : Char → Prop) (s : Sal) :
    s.inner.from P := by
  simp [inner, sub, Sal.from]

private theorem fontCmdInlines_from (P : Char → Prop) (st : Ir.Style)
    (edges : Bool × Bool) (xs : Array Ir.Inline) (hx : inlinesFrom P xs) :
    inlinesFrom P (Ir.fontCmdInlines st edges xs) := by
  rcases edges with ⟨l, r⟩
  cases l <;> cases r <;>
    simp [Ir.fontCmdInlines, inlinesFrom, Ir.plainTextOne,
      plainTextList_from, Ir.plainTextList] <;> exact hx

private theorem Sal.settle_from (P : Char → Prop) (s : Sal) (t : Tok)
    (hs : s.from P) : (Sal.settle t s).from P := by
  unfold Sal.settle
  split <;> (try split) <;> exact hs

/-- Content safety for the existing splice loop. Consumption is accounted
for by `salList_from`'s induction over the source tree. -/
private theorem Sal.splice_from (P : Char → Prop) (s body : Sal)
    (wrap : Bool → Bool → Array Ir.Inline → Array Ir.Inline)
    (hs : s.from P) (hb : body.from P)
    (hw : ∀ first last xs, inlinesFrom P xs → inlinesFrom P (wrap first last xs)) :
    (s.splice body wrap).from P := by
  have hbody := body.newline_from P hb
  unfold Sal.splice
  dsimp only
  refine Loop.bind_of_inv (fun s : Sal => s.from P) (fun s : Sal => s.from P) _ _ ?_ ?_
  · apply Loop.forIn_range_inv
    · exact hs
    · intro k _ _ s hs
      split
      · rename_i xs scale heq
        have hl : inlinesFrom P xs := hbody.1 (xs, scale) (Array.mem_of_getElem? heq)
        split
        · split
          · exact s.newline_from P hs
          · apply Sal.inlines_from
            · exact s.newline_from P hs
            · exact hw _ _ _ (Sal.trimEnds_from P _ _ _ hl)
        · split
          · exact hs
          · exact Sal.inlines_from P _ _ hs (hw _ _ _ (Sal.trimEnds_from P _ _ _ hl))
      · exact hs
  · intro s hs
    exact hs

/-- A literal source token, before any salvage decision. A number's
spelling is the token reader's canonical `milliString`, since `Tok.num`
retains its value rather than its original spelling. -/
public inductive LabelLiteral where
  | word (text : String)
  | number (milli : Int)
  | symbol (char : Char)
  | space
  deriving Repr, BEq

public def LabelLiteral.text : LabelLiteral → String
  | .word s => s
  | .number m => milliString m
  | .symbol c => String.singleton c
  | .space => " "

/-- An independently enumerable input to a node label. A substitution
retains its declaration name and value; a math input retains its original
body and display mode, not a certificate attached to the produced inline. -/
public inductive LabelInput where
  | literal (source : LabelLiteral)
  | substitution (name : String) (value : Val)
  | math (display : Bool) (body : List Parse.Raw)
  deriving Repr, BEq

public def LabelInput.text (cx : Cx) : LabelInput → String
  | .literal source => source.text
  | .substitution _ value => value.text
  | .math d body => Ir.plainTextOne (cx.math d body.toArray).1

mutual

/-- The independent source census: flatten source groups and resolve
declared substitutions. It reads no salvage state, output or diagnostic.
In particular it enumerates math *inputs* without invoking the callback.
This walk is over `Tok`, whose group tree is not the document IR. -/
public def labelInputList (env : List (String × Val)) (acc : Array LabelInput) :
    List Tok → Array LabelInput
  | [] => acc
  | t :: rest => labelInputList env (labelInputOne env acc t) rest

public def labelInputOne (env : List (String × Val)) (acc : Array LabelInput) :
    Tok → Array LabelInput
  | .ident w => acc.push (.literal (.word w))
  | .num m => acc.push (.literal (.number m))
  | .sym c => acc.push (.literal (.symbol c))
  | .space => acc.push (.literal .space)
  | .ctrl n => match env.lookup n with
    | some v => acc.push (.substitution n v)
    | none => acc
  | .group ts => labelInputList env acc ts
  | .math d ts => acc.push (.math d ts)
  | .other _ => acc

end

mutual

/-- The census preserves its initial sources exactly, including through
nested groups. This equation exposes its accumulator to consumers. -/
public theorem labelInputList_prefix_exact (env : List (String × Val))
    (initial acc : Array LabelInput) (ts : List Tok) :
    labelInputList env (initial ++ acc) ts =
      initial ++ labelInputList env acc ts := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    rw [labelInputList, labelInputOne_prefix_exact, labelInputList_prefix_exact]
    rfl

public theorem labelInputOne_prefix_exact (env : List (String × Val))
    (initial acc : Array LabelInput) (t : Tok) :
    labelInputOne env (initial ++ acc) t = initial ++ labelInputOne env acc t := by
  cases t with
  | group ts => exact labelInputList_prefix_exact env initial acc ts
  | ctrl n => simp only [labelInputOne]; split <;> simp only [Array.append_push]
  | _ => simp only [labelInputOne, Array.append_push]

end

public def labelInputText (cx : Cx) (inputs : Array LabelInput) : String :=
  String.join (inputs.toList.map (LabelInput.text cx))

public theorem labelInputText_append (cx : Cx) (a b : Array LabelInput) :
    labelInputText cx (a ++ b) = labelInputText cx a ++ labelInputText cx b := by
  simp [labelInputText, String.join_append]

/-- A character in the census text has an actual input witness. -/
public theorem labelInputText_mem (cx : Cx) (inputs : Array LabelInput) (c : Char) :
    c ∈ (labelInputText cx inputs).toList ↔
      ∃ input ∈ inputs, c ∈ (input.text cx).toList := by
  cases inputs with
  | mk inputs =>
    induction inputs with
    | nil => simp [labelInputText]
    | cons input inputs ih =>
      simp only [labelInputText, List.map_cons, String.join_cons,
        String.toList_append, List.mem_append] at ih ⊢
      simp_all

/-- Potential readable label characters. This projection of the source
census allows arbitrary math callback output. Salvage may discard sources
used as options or names, so the bound is containment, not equality. -/
public def labelSources (cx : Cx) (env : List (String × Val)) (ts : List Tok) : String :=
  labelInputText cx (labelInputList env #[] ts)

public def labelSource (cx : Cx) (env : List (String × Val)) (t : Tok) : String :=
  labelInputText cx (labelInputOne env #[] t)

/-- The single-token equation of the independently collected text. -/
public theorem labelSource_exact (cx : Cx) (env : List (String × Val)) (t : Tok) :
    labelSource cx env t = match t with
      | .ident w => w
      | .num m => milliString m
      | .sym c => String.singleton c
      | .space => " "
      | .ctrl n => match env.lookup n with
        | some v => v.text
        | none => ""
      | .group ts => labelSources cx env ts
      | .math d ts => Ir.plainTextOne (cx.math d ts.toArray).1
      | .other _ => "" := by
  cases t <;> simp [labelSource, labelInputOne, labelInputText, LabelInput.text,
    LabelLiteral.text, labelSources]
  split <;> simp [LabelInput.text, *]

public theorem labelSources_cons (cx : Cx) (env : List (String × Val)) (t : Tok) (ts : List Tok) :
    labelSources cx env (t :: ts) = labelSource cx env t ++ labelSources cx env ts := by
  unfold labelSources labelSource
  change labelInputText cx (labelInputList env (labelInputOne env #[] t ++ #[]) ts) = _
  rw [labelInputList_prefix_exact, labelInputText_append]

/-- The closed vocabulary of text the label reader may generate. -/
public inductive LabelGenerated where
  | nodeFloor
  deriving Repr, BEq

public def LabelGenerated.text : LabelGenerated → String
  | .nodeFloor => nodeFloorPlaceholder

public inductive LabelOrigin where
  | source (input : LabelInput)
  | generated (kind : LabelGenerated)
  deriving Repr, BEq

public def LabelOrigin.text (cx : Cx) : LabelOrigin → String
  | .source input => input.text cx
  | .generated kind => kind.text

/-- Source permission depends only on the input census. The one generated
fallback is permitted only when the run names a loss. Neither permission
uses a source tag supplied by the salvage implementation. -/
public def LabelOrigin.Permitted (env : List (String × Val)) (toks : List Tok)
    (named : Bool) : LabelOrigin → Prop
  | .source input => input ∈ labelInputList env #[] toks
  | .generated .nodeFloor => named = true

private theorem salCtrl_from (P : Char → Prop) (cx : Cx) (env : List (String × Val))
    (n : String) (s : Sal) (hs : s.from P)
    (ht : textFrom P (labelSource cx env (.ctrl n))) :
    (salCtrl cx env n s).from P := by
  unfold salCtrl
  split
  · rename_i v hv
    exact s.str_from P _ hs (by simpa only [labelSource_exact, hv] using ht)
  · repeat' first
      | exact hs
      | exact s.newline_from P hs
      | exact s.flush_from P hs
      | split

mutual

private theorem salList_from (P : Char → Prop) (cx : Cx) (env : List (String × Val))
    (ts : List Tok) (s : Sal) (hs : s.from P)
    (ht : textFrom P (labelSources cx env ts)) :
    (salList cx env ts s).from P := by
  cases ts with
  | nil => exact hs
  | cons t ts =>
    rw [labelSources_cons] at ht
    have ⟨head, tail⟩ := (textFrom_append P _ _).mp ht
    exact salList_from P cx env ts _ (salOne_from P cx env t _ hs head) tail

private theorem salOne_from (P : Char → Prop) (cx : Cx) (env : List (String × Val))
    (t : Tok) (s : Sal) (hs : s.from P)
    (ht : textFrom P (labelSource cx env t)) :
    (salOne cx env t s).from P := by
  rw [labelSource_exact] at ht
  have hs := Sal.settle_from P _ t (Sal.settle_from P _ t hs)
  unfold salOne
  generalize Sal.settle t (Sal.settle t s) = settled at hs ⊢
  dsimp only
  cases hm : settled.mode with
  | optMaybe k => dsimp only; split <;> exact hs
  | optDrop k => dsimp only; split <;> exact hs
  | dropArgs n => exact hs
  | colorRole =>
    cases t <;> try exact hs
    dsimp only
    split <;> exact hs
  | colorBody c role =>
    cases t with
    | group g =>
      apply Sal.splice_from P _ _ _ hs
      · exact salList_from P cx env g _ (Sal.inner_from P settled) ht
      · intro first last xs hx
        simpa using hx
    | _ => exact hs
  | styleBody st =>
    cases t with
    | group g =>
      apply Sal.splice_from P _ _ _ hs
      · exact salList_from P cx env g _ (Sal.inner_from P settled) ht
      · intro first last xs hx
        exact fontCmdInlines_from P _ _ _ hx
    | ident w =>
      apply Sal.inlines_from P _ _ hs
      apply fontCmdInlines_from
      simpa [Ir.plainTextOne] using ht
    | num m =>
      apply Sal.inlines_from P _ _ hs
      apply fontCmdInlines_from
      simpa [Ir.plainTextOne] using ht
    | sym c =>
      apply Sal.inlines_from P _ _ hs
      apply fontCmdInlines_from
      simpa [Ir.plainTextOne] using ht
    | _ => exact hs
  | text =>
    cases t with
    | ident w => exact Sal.str_from P _ _ hs ht
    | num m => exact Sal.str_from P _ _ hs ht
    | space => exact Sal.str_from P _ _ hs ht
    | sym c => exact Sal.str_from P _ _ hs ht
    | group g =>
      have hi := salList_from P cx env g
        { settled with depth := settled.depth + 1, consumeNocorr := false, mode := .text } hs ht
      dsimp only
      split
      · exact hi
      · exact Sal.flush_from P _ hi
    | math d body => exact Sal.inline_from P _ _ hs ht
    | other _ => exact hs
    | ctrl n =>
      exact salCtrl_from P cx env n _ hs (by simpa only [labelSource_exact] using ht)

end

private theorem labelFloor_from (P : Char → Prop) (lines : Array LabelLine)
    (named : Bool) (hs : linesFrom P lines)
    (hp : named = true → textFrom P nodeFloorPlaceholder) :
    linesFrom P (labelFloor lines named) := by
  unfold labelFloor
  split
  · exact hs
  · rename_i h
    have hn : named = true := by
      cases named <;> simp_all
    simpa [linesFrom, inlinesFrom, Ir.plainTextOne] using hp hn

private theorem nodeLabel_from (P : Char → Prop) (cx : Cx) (env : List (String × Val))
    (toks : List Tok) (ht : textFrom P (labelSources cx env toks))
    (hp : (!(nodeLabel cx env toks).2.isEmpty) = true → textFrom P nodeFloorPlaceholder) :
    linesFrom P (nodeLabel cx env toks).1 := by
  let walked := salList cx env toks {}
  have hw : walked.from P := salList_from P cx env toks {} (by simp [Sal.from]) ht
  let closed := if Sal.settled walked.mode then walked
    else walked.refuse "a node body that ends mid-construct"
  have hc : closed.from P := by
    dsimp only [closed]
    split <;> exact hw
  exact labelFloor_from P _ _ (Sal.newline_from P closed hc).1 hp

/-- **Every output character has a permitted, typed origin.** The source
census is computed independently from the token tree and declarations.
Its witnesses distinguish literal tokens, resolved substitutions and
math inputs; math text is read from the callback applied to that very
input. The only generated text is the closed `nodeFloor` case, and its
witness requires a diagnostic from this run.

This quantifies over every context, binding environment and token tree,
including malformed bodies, literal brackets and arbitrary math callback
output. It bounds the actual `salList`/`salOne` salvage, its style/colour
splice loop and its final floor. It makes no claim that every source is
selected, nor that each occurrence has a unique origin. -/
public theorem nodeLabel_mem (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    ∀ line ∈ (nodeLabel cx env toks).1,
      ∀ c ∈ (Ir.plainText line.1).toList,
        ∃ origin : LabelOrigin,
          origin.Permitted env toks (!(nodeLabel cx env toks).2.isEmpty) ∧
          c ∈ (origin.text cx).toList := by
  let P := fun c => ∃ origin : LabelOrigin,
    origin.Permitted env toks (!(nodeLabel cx env toks).2.isEmpty) ∧
    c ∈ (origin.text cx).toList
  have ht : textFrom P (labelSources cx env toks) := by
    intro c hc
    obtain ⟨input, hi, hc⟩ := (labelInputText_mem cx _ c).mp hc
    exact ⟨.source input, hi, hc⟩
  have hp : (!(nodeLabel cx env toks).2.isEmpty) = true →
      textFrom P nodeFloorPlaceholder := by
    intro hn c hc
    exact ⟨.generated .nodeFloor, hn, hc⟩
  have h := nodeLabel_from P cx env toks ht hp
  intro line hl
  exact (plainText_from P line.1).mpr (h line hl)

/-- A run without a diagnostic needs only genuine input witnesses; the
generated fallback cannot account for any of its characters. -/
public theorem nodeLabel_clean_mem (cx : Cx) (env : List (String × Val)) (toks : List Tok)
    (clean : (nodeLabel cx env toks).2.isEmpty = true) :
    ∀ line ∈ (nodeLabel cx env toks).1,
      ∀ c ∈ (Ir.plainText line.1).toList,
        ∃ input ∈ labelInputList env #[] toks, c ∈ (input.text cx).toList := by
  intro line hl c hc
  obtain ⟨origin, ho, hc⟩ := nodeLabel_mem cx env toks line hl c hc
  cases origin with
  | source input => exact ⟨input, ho, hc⟩
  | generated kind =>
    cases kind
    simp [LabelOrigin.Permitted, clean] at ho

/-- Every character returned by the label reader comes from literal text,
a resolved macro value, the math elaborator's output, or the declared
fallback. This holds inside all style and colour wrappers and across line
breaks. Literal punctuation remains content; command names and parser
markers cannot become a source merely because the reader encountered them.

The bound is on provenance, not selection: options may carry readable
characters which the reader intentionally discards. `nodeLabel_accounts`
covers the separate guarantee that a named loss leaves visible ink. -/
public theorem nodeLabel_source_mem (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    ∀ line ∈ (nodeLabel cx env toks).1,
      ∀ c ∈ (Ir.plainText line.1).toList,
        c ∈ (labelSources cx env toks).toList ∨ c ∈ Ir.mathFloorPlaceholder := by
  let P := fun c => c ∈ (labelSources cx env toks).toList ∨ c ∈ Ir.mathFloorPlaceholder
  have h := nodeLabel_from P cx env toks
    (fun _ hc => Or.inl hc)
    (fun _ _ hc => Or.inr (by simpa [nodeFloorPlaceholder] using hc))
  intro line hl
  exact (plainText_from P line.1).mpr (h line hl)

/-- A label's lines as shapes, stacked so the block centres on the anchor:
one `Ir.Pic.Shape.label` per line, baselines `nodeLineLead` apart, each at
the size its line opened with. A label shape carries one size and one
anchor, so a multi-line label is several of them — `\\` is a real break,
not a degradation, and layout sets one line per label shape. An empty line
ships no shape: a blank contributes its height, which this subset does not
measure, and no ink. -/
public def stackLabels (x y : Sp) (bodySize : Sp) (scale : Nat) (color : Ir.Color)
    (align : Ir.Pic.LabelAlign) (lines : Array LabelLine)
    (acc : Array Ir.Pic.Shape) : Array Ir.Pic.Shape := Id.run do
  -- Each gap is the leading of the line *below* it, so a smaller second
  -- line sits closer; the block then shifts up by half its own height, so
  -- its middle is the node's anchor whatever the sizes are.
  let mut tops : Array Sp := #[]
  let mut acc0 : Sp := 0
  for k in [0:lines.size] do
    if let some (_, rel) := lines[k]? then
      if k > 0 then acc0 := acc0 - nodeLineLead bodySize (scale * rel / 1000)
      tops := tops.push acc0
  let shift := (tops[tops.size - 1]?.getD 0) / 2
  let mut out := acc
  for k in [0:lines.size] do
    if let some (content, rel) := lines[k]? then
      unless content.isEmpty do
        let dy := (tops[k]?.getD 0) - shift
        out := out.push (.label x (y + dy) content color (scale * rel / 1000) align)
  return out

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

/-- A length in a node's options, the font-relative units included: `em` is
the node's em and `ex` its face's x-height at the node's size, which is how
TeX reads them where the key is evaluated (fontdimens 6 and 5). -/
private def readNodeDim (em ex : Sp) (toks : List Tok) : Except String Sp :=
  match toks with
  | [.num m, .ident "em"] => .ok (m * em / 1000)
  | [.num m, .ident "ex"] => .ok (m * ex / 1000)
  | ts => readDim ts

/-- pgf's named line widths, as tikz.code.tex defines them (lines
1575–1581): each is the style `line width=<w>`, so a name and the key it
abbreviates stroke one width. `thin` and `thick` are the IR's own two
widths, read rather than restated. -/
private def lineWidthStyles : List (String × Sp) :=
  [("ultra thin", Dim.pt 1 / 10), ("very thin", Dim.pt 1 / 5),
   ("thin", Ir.Pic.thinWidth), ("semithick", Dim.pt 3 / 5),
   ("thick", Ir.Pic.thickWidth), ("very thick", Dim.pt 6 / 5),
   ("ultra thick", Dim.pt 8 / 5)]

/-- A width entry: a named width or `line width=<length>`, read; `none`
where the entry sets no width. The one reader every stroke site and every
vocabulary check reads, so a width a path strokes and a width a picture's
bracket carries down are the same keys. -/
private def readLineWidth (opt : List Tok) : Option (Except String Sp) :=
  match opt with
  | .ident "line" :: .ident "width" :: .sym '=' :: rest => some (readDim rest)
  | ts => ((keyName ts).bind fun n => lineWidthStyles.lookup n).map .ok

/-- A `font=` value as TikZ runs it before a node's text: switches, each a
size step of the document's ladder (`Cx.ladder`) or a declaration of the
elaborator's table (`Cx.declStyles`), braces being grouping. The last size
written wins, as in TeX; the declarations apply in order; `\selectfont`
selects what they already chose. A switch outside both tables is returned
by name, so the loss names what it could not set and the rest still
applies. -/
private def readFont (cx : Cx) (toks : List Tok) : Option Nat × Array Ir.Style × Array String :=
  Id.run do
  let flat := toks.flatMap fun t => match t with
    | .group g => g
    | t => [t]
  let mut size : Option Nat := none
  let mut sts : Array Ir.Style := #[]
  let mut unread : Array String := #[]
  for t in flat do
    match t with
    | .space | .ctrl "selectfont" => pure ()
    | .ctrl n =>
      match cx.ladder.lookup n, cx.declStyles.lookup n with
      | some k, _ => size := some k
      | none, some st => sts := sts.push st
      | none, none => unread := unread.push s!"\\{n}"
    | t => unread := unread.push (tokText t)
  return (size, sts, unread)

/-- A label's lines set in the declarations a `font=` named, the first
written outermost; an empty line stays empty, so no empty wrapper ships. -/
private def fontLines (sts : Array Ir.Style) (lines : Array LabelLine) : Array LabelLine :=
  if sts.isEmpty then lines
  else lines.map fun (xs, rel) =>
    (if xs.isEmpty then xs else sts.foldr (fun st inner => #[.styled st inner]) xs, rel)

/-- The line alignment an `align=` value chooses (tikz.code.tex, the `align`
choice key), as the side each line stands flush to: `.west` for left,
`.east` for right, `.center` for centred. `left` and `flush left` set lines
broken with `\\` alike, as do their siblings; the spellings differ only in
how TeX breaks a paragraph of declared width. -/
private def textAlignOf : List Tok → Option Ir.Pic.LabelAlign
  | [.ident "left"] | [.ident "flush", .ident "left"] => some .west
  | [.ident "right"] | [.ident "flush", .ident "right"] => some .east
  | [.ident "center"] | [.ident "flush", .ident "center"] => some .center
  | _ => none

/-- A node's centred lines set flush to one side of its text box, as
`align=` asks: each moves to stand that edge on the box's, and the widest
line — the box's width — stays exactly where centring put it, so the block
and the node's extent do not move. A line anchored any other way stands as
it was. -/
private def alignLabels (m : Ir.Pic.LabelMetric) (al : Ir.Pic.LabelAlign)
    (ls : Array Ir.Pic.Shape) : Array Ir.Pic.Shape :=
  let w := ls.foldl (fun w s => match s with
    | .label _ _ content _ sz a => if a == .center then max w (m content sz).w else w
    | .rect .. | .circle .. | .frame .. | .edge .. => w) 0
  ls.map fun s => match s with
    | .label x y c col sz a =>
      if a != .center then s
      else if al == .west then .label (x - w / 2) y c col sz .west
      else if al == .east then .label (x + w / 2) y c col sz .east
      else s
    | .rect .. | .circle .. | .frame .. | .edge .. => s

/-- A relative placement's direction: the `positioning` keys this subset
reads — the four sides and the four corners. Public because the placement
facts range over it: a statement needs a name to talk about. -/
public inductive Dir where
  | left | right | above | below
  | aboveLeft | aboveRight | belowLeft | belowRight
  deriving Repr, BEq, Inhabited

private def dirOf : String → Option Dir
  | "left" => some .left
  | "right" => some .right
  | "above" => some .above
  | "below" => some .below
  | "above left" => some .aboveLeft
  | "above right" => some .aboveRight
  | "below left" => some .belowLeft
  | "below right" => some .belowRight
  | _ => none

/-- The centre-to-centre offset a direction puts between the placed node
and the one it names, given the separation each axis asks for: the
horizontal member for the left-right pair, the vertical for the up-down
pair, and both for a corner — pgf spells the pair vertical first. The
caller adds the two nodes' half-extents to the declared `node distance`,
which is how pgf measures the gap: border to border, not centre to
centre (`positioning` library). -/
public def Dir.offset (d : Dir) (sep : Sp × Sp) : Sp × Sp :=
  match d with
  | .left => (-sep.2, 0)
  | .right => (sep.2, 0)
  | .above => (0, sep.1)
  | .below => (0, -sep.1)
  | .aboveLeft => (-sep.2, sep.1)
  | .aboveRight => (sep.2, sep.1)
  | .belowLeft => (-sep.2, -sep.1)
  | .belowRight => (sep.2, -sep.1)

/-- A node's placement after its coordinate expressions and options have
been read. Relative placement names exactly one geometry to read; absolute
placement reads none. Keeping that dependency explicit lets the resolver's
order contract cover every direction without assuming that arbitrary
source statements commute. -/
public inductive NodePlacement where
  | absolute (x y : Sp)
  | relative (dir : Dir) (target : String) (sep : Sp × Sp)
  deriving Repr, Inhabited

public def NodePlacement.target : NodePlacement → Option String
  | .absolute .. => none
  | .relative _ name _ => some name

/-- Resolve the centre from the declared gap and both nodes' anchor
extents. Failure carries the missing name so the caller can account for
it without recovering a name from diagnostic text. -/
public def NodePlacement.position (p : NodePlacement) (a b : Sp)
    (nodes : List (String × NodeGeom)) : Except String (Sp × Sp) :=
  match p with
  | .absolute x y => .ok (x, y)
  | .relative dir target sep =>
    match nodes.lookup target with
    | none => .error target
    | some g =>
      let (ox, oy) := dir.offset (sep.1 + g.b + b, sep.2 + g.a + a)
      .ok (g.x + ox, g.y + oy)

/-- The measured node and its optional name, before placement. `shape.base`
is the text baseline relative to the node centre; resolution translates
it together with the centre. `evalNode` uses this value for both the
geometry it emits and the geometry later nodes read. -/
public structure NodePlan where
  name : Option String
  placement : NodePlacement
  shape : NodeGeom
  deriving Repr, Inhabited

public def NodePlan.resolve (p : NodePlan) (nodes : List (String × NodeGeom)) :
    Except String NodeGeom :=
  (p.placement.position p.shape.a p.shape.b nodes).map fun (x, y) =>
    { p.shape with x, y, base := y + p.shape.base }

public def NodePlan.register (p : NodePlan) (resolved : Option NodeGeom)
    (nodes : List (String × NodeGeom)) : List (String × NodeGeom) :=
  match p.name, resolved with
  | some name, some g => (name, g) :: nodes
  | _, _ => nodes

/-- Resolve once, then register precisely that geometry if the node has a
name. An unnamed or unresolved node cannot change another node's lookup. -/
public def NodePlan.run (p : NodePlan) (nodes : List (String × NodeGeom)) :
    Except String NodeGeom × List (String × NodeGeom) :=
  let resolved := p.resolve nodes
  (resolved, p.register resolved.toOption nodes)

/-- Two placements are independent when their writes are distinct and
neither reads the other's write. Repeated names and a node placed against
the other node fail these conditions; both are legitimate source programs
whose order can matter. -/
public def NodePlan.Independent (p q : NodePlan) : Prop :=
  (∀ n, p.name = some n → q.name ≠ some n) ∧
  (∀ n, p.placement.target = some n → q.name ≠ some n) ∧
  (∀ n, q.placement.target = some n → p.name ≠ some n)

public theorem NodePlan.register_lookup (p : NodePlan) (g : Option NodeGeom)
    (nodes : List (String × NodeGeom)) (n : String) (h : p.name ≠ some n) :
    (p.register g nodes).lookup n = nodes.lookup n := by
  cases hn : p.name with
  | none => simp [register, hn]
  | some name =>
    have ne : n ≠ name := by intro he; subst name; exact h hn
    have hne : (n == name) = false := beq_eq_false_iff_ne.mpr ne
    cases g <;> simp [register, hn, List.lookup_cons, hne]

public theorem NodePlan.resolve_register (p q : NodePlan) (g : Option NodeGeom)
    (nodes : List (String × NodeGeom))
    (h : ∀ n, p.placement.target = some n → q.name ≠ some n) :
    p.resolve (q.register g nodes) = p.resolve nodes := by
  unfold resolve
  cases hp : p.placement with
  | absolute x y => rfl
  | relative dir target sep =>
    simp only [NodePlacement.position]
    rw [q.register_lookup g nodes target (h target (by simp [NodePlacement.target, hp]))]

public theorem NodePlan.register_order (p q : NodePlan) (pg qg : Option NodeGeom)
    (nodes : List (String × NodeGeom))
    (h : ∀ n, p.name = some n → q.name ≠ some n) (n : String) :
    (p.register pg (q.register qg nodes)).lookup n =
      (q.register qg (p.register pg nodes)).lookup n := by
  cases hp : p.name with
  | none => simp [register, hp]
  | some pn =>
    cases hq : q.name with
    | none => simp [register, hq]
    | some qn =>
      have ne : pn ≠ qn := by intro he; subst qn; exact h pn hp hq
      cases pg <;> cases qg <;> simp [register, hp, hq, List.lookup_cons]
      split <;> split <;> simp_all

/-- Independent measured placements commute for every named lookup, even
when a reference is missing. This is a contract of the resolver `evalNode`
uses, not of arbitrary statements: redefining a node or changing a macro
between nodes can intentionally change the result. -/
public theorem NodePlan.place_order_agree (p q : NodePlan) (nodes : List (String × NodeGeom))
    (h : p.Independent q) (name : String) :
    (q.run (p.run nodes).2).2.lookup name =
      (p.run (q.run nodes).2).2.lookup name := by
  simp only [NodePlan.run]
  rw [NodePlan.resolve_register _ _ _ _ h.2.1,
      NodePlan.resolve_register _ _ _ _ h.2.2]
  exact (NodePlan.register_order _ _ _ _ _ h.1 name).symm

/-- Distinct named absolute placements, as produced by `at (x,y)`, satisfy
the independence premise for all positions and measured shapes. -/
public theorem NodePlan.absolute_independent (pn qn : String) (hne : pn ≠ qn)
    (px py qx qy : Sp) (pg qg : NodeGeom) :
    Independent ⟨some pn, .absolute px py, pg⟩ ⟨some qn, .absolute qx qy, qg⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hq
    exact hne ((Option.some.inj hn).trans (Option.some.inj hq).symm)
  · intro n hn; cases hn
  · intro n hn; cases hn

/-- TikZ's `auto` anchor, including diagonal corners. tikz.code.tex's
`tikz@auto@anchor` ignores normalized tangent components within ±.05;
comparing twenty times the component with the length avoids division.
Swapping sides reverses the tangent before making the same decision. -/
public def autoDir (left : Bool) (dx dy : Sp) : Dir :=
  let x := if left then dx else -dx
  let y := if left then dy else -dy
  let n := isqrt (x * x + y * y)
  if 20 * x > n then
    if 20 * y > n then .aboveLeft
    else if 20 * y < -n then .aboveRight else .above
  else if 20 * x < -n then
    if 20 * y > n then .belowLeft
    else if 20 * y < -n then .belowRight else .below
  else if y > 0 then .left else .right

/-- Reversing a path and swapping its automatic side attach to the same
side of the same label box, for every tangent, including a zero tangent. -/
public theorem autoDir_swap_exact (left : Bool) (dx dy : Sp) :
    autoDir (!left) dx dy = autoDir left (-dx) (-dy) := by
  cases left <;> simp [autoDir]

/-- **A relative placement leaves exactly the declared separation between
the two borders.** pgf's `positioning` rule, as arithmetic over the values
the walk actually threads: the reference node's centre `gx` and half-extent
`ga`, the placed node's half-extent `ownA`, and the separation `s` the
entry or `node distance` declared. `right` puts the placed centre at
`gx + (s + ga + ownA)`, so its near border stands at `gx + ga + s` — the
reference's far border plus `s`, with the two extents accounted and
nothing left over.

This is the invariant whose absence let the first version of this slice
put node *centres* one `node distance` apart, which drew a diagram whose
boxes touched. Stated per axis because the two axes read different members
of the pair; the corner directions are their conjunction
(`offset_corners_exact`). Binders are `Int` so `omega` can read them, as
the convention asks. -/
public theorem placeRight_border_exact (gx ga ownA s : Int) :
    gx + (Dir.right.offset (0, s + ga + ownA)).1 - ownA - (gx + ga) = s := by
  simp [Dir.offset]
  omega

public theorem placeLeft_border_exact (gx ga ownA s : Int) :
    (gx - ga) - (gx + (Dir.left.offset (0, s + ga + ownA)).1 + ownA) = s := by
  simp [Dir.offset]
  omega

public theorem placeAbove_border_exact (gy gb ownB s : Int) :
    gy + (Dir.above.offset (s + gb + ownB, 0)).2 - ownB - (gy + gb) = s := by
  simp [Dir.offset]
  omega

public theorem placeBelow_border_exact (gy gb ownB s : Int) :
    (gy - gb) - (gy + (Dir.below.offset (s + gb + ownB, 0)).2 + ownB) = s := by
  simp [Dir.offset]
  omega

/-- The four sides are two opposite pairs: a sign error in the vocabulary
cannot hide behind a direction nothing tests. -/
public theorem offset_opposite_exact (s : Sp × Sp) :
    Dir.left.offset s = (-(Dir.right.offset s).1, (Dir.right.offset s).2) ∧
      Dir.above.offset s = ((Dir.below.offset s).1, -(Dir.below.offset s).2) := by
  simp [Dir.offset]

/-- Each corner is exactly its two sides: `above left` moves by what
`left` moves along x and what `above` moves along y, so the corner cases
cannot drift from the sides they are named for. -/
public theorem offset_corners_exact (s : Sp × Sp) :
    Dir.aboveLeft.offset s = ((Dir.left.offset s).1, (Dir.above.offset s).2) ∧
      Dir.aboveRight.offset s = ((Dir.right.offset s).1, (Dir.above.offset s).2) ∧
      Dir.belowLeft.offset s = ((Dir.left.offset s).1, (Dir.below.offset s).2) ∧
      Dir.belowRight.offset s = ((Dir.right.offset s).1, (Dir.below.offset s).2) := by
  simp [Dir.offset]

/-- The offset moves along one axis per member of the separation and
invents no distance: every component is `0`, a member of the pair, or its
negation. What stops a direction from quietly scaling the gap. -/
public theorem offset_mem (d : Dir) (s : Sp × Sp) :
    ((d.offset s).1 = 0 ∨ (d.offset s).1 = s.2 ∨ (d.offset s).1 = -s.2) ∧
      ((d.offset s).2 = 0 ∨ (d.offset s).2 = s.1 ∨ (d.offset s).2 = -s.1) := by
  cases d <;> simp [Dir.offset]

/-- A node name written as a coordinate's contents: idents and digit runs
joined, which is how `(a)`, `(a1)` and `(x y)` all spell one name. -/
private def nameOfToks (ts : List Tok) : Option String :=
  let s := ts.foldl (fun acc t => acc ++ (match t with
    | .ident n => n
    | .num m => milliString m
    | .sym c => String.singleton c
    | _ => "")) ""
  if s.isEmpty then none else some s

/-- A relative placement option, in the spellings pgf accepts: `right=of a`
(the `positioning` library), `right of=a` (the older `calc` spelling), and
`right=2cm of a`, whose own length replaces `node distance`. The separation
comes back undivided; the caller turns it into a centre offset once it
knows both nodes' extents. `none` where the entry is not a placement at
all. A bare `right` is *not* one — on a node it is an anchor, which this
subset reads where an edge label declares it. -/
private def readPlace (dist : Sp × Sp) (toks : List Tok) :
    Option (Dir × String × (Sp × Sp)) := do
  let path := keyPath toks
  let rest := (toks.dropWhile (· != .sym '=')).drop 1
  let words := path.splitOn " "
  -- `right of=a`: the older `calc` spelling carries `of` in the key path
  if words.getLast? == some "of" then
    let dir ← dirOf (String.intercalate " " words.dropLast)
    let nm ← nameOfToks rest
    return (dir, nm, dist)
  let dir ← dirOf path
  match rest with
  -- `right=of a`
  | .ident "of" :: tail => (nameOfToks tail).map fun nm => (dir, nm, dist)
  -- `right=2cm of a`: the declared length stands in for `node distance`
  | .num m :: .ident u :: .ident "of" :: tail => do
    let own ← (readDim [.num m, .ident u]).toOption
    let nm ← nameOfToks tail
    some (dir, nm, (own, own))
  | _ => none

/-- `node distance = 1cm and 1cm`, vertical then horizontal as pgf spells
it; one length sets both. `none` where the entry is not that key. -/
private def readNodeDistance (toks : List Tok) : Option (Sp × Sp) := do
  guard (keyPath toks == "node distance")
  let rest := (toks.dropWhile (· != .sym '=')).drop 1
  let parts := rest.splitOn (.ident "and")
  match parts with
  | [a] => (readDim a).toOption.map fun d => (d, d)
  | [a, b] => do
    let v ← (readDim a).toOption
    let h ← (readDim b).toOption
    some (v, h)
  | _ => none

/-- The To-Path keys a path statement reads (`ToSpec.read`), so a bundle or
an outer bracket that sets one reaches every `to` below it. -/
private def toKeyNames : List String :=
  ["out", "in", "bend left", "bend right", "bend angle", "relative", "looseness",
   "out looseness", "in looseness"]

/-- The keys a path statement's option loop reads, so an entry declared for
the whole document or for the picture can be carried into a path's bracket
instead of dropped. A tip counts only where this subset can draw it
(`drawsAsArrow`): an undrawable one is a real loss, and is named once at
the line that declared it rather than at every edge that inherited it. -/
private def readsPathOpt (styles : List (String × Array Tok)) (opt : Array Tok) : Bool :=
  match arrowTipName opt.toList with
  | some tip => drawsAsArrow styles tip
  | none =>
    match opt.toList with
    | .sym '>' :: .sym '=' :: rest =>
      match tipName rest with
      | some tip => drawsAsArrow styles tip
      | none => false
    | ts => ["draw", "dashed", "dotted", "densely dotted",
        "auto", "swap", "'"].contains (keyPath ts) || toKeyNames.contains (keyPath ts) ||
        (readLineWidth ts).isSome

/-- The keys a node statement's option loop reads. A placement and a width
are read through the functions the loop reads them with, so the vocabulary
cannot drift from the loop that consumes it; a `font=` is read whole, and
the loop names any switch in it that it cannot set (`readFont`). -/
private def readsNodeOpt (opt : Array Tok) : Bool :=
  if (readPlace (0, 0) opt.toList).isSome then true
  else match opt.toList with
  | ts => ["circle", "rectangle", "draw", "dashed", "dotted", "densely dotted",
      "text", "fill", "minimum size", "minimum width", "minimum height",
      "inner sep", "inner xsep", "inner ysep", "outer sep", "outer xsep", "outer ysep",
      "node contents", "font", "text height", "text depth", "align"].contains (keyPath ts) ||
      (readLineWidth ts).isSome

/-- An entry some statement of this subset reads: what a declaration made
once for the document, or once for the picture, carries into the brackets
below it. An entry no shape reads is honoured by nobody, so it stays a
named loss at the line that wrote it. -/
public def readsOpt (styles : List (String × Array Tok)) (opt : Array Tok) : Bool :=
  readsPathOpt styles opt || readsNodeOpt opt

/-- The two outer brackets as the shape at hand reads them. Neither was
written at this statement, so an entry for the other shape is not a loss
here — a document-level arrow tip is no complaint at a node — and the
entries no shape reads are named where they were declared. -/
public def outerRead (reads : Array Tok → Bool) (global picture : Array (Array Tok)) :
    Array (Array Tok) × Array (Array Tok) :=
  (global.filter reads, picture.filter reads)

/-- **A picture starts at pgf's line width.** `\pgfpicture` runs
`\pgfsetlinewidth{0.4pt}` before anything the picture declares
(pgfcorescopes.code.tex, `\pgf@picture`), so a width a `\tikzset` line sets
outside every picture reaches none: lualatex strokes such a picture at
0.4 pt. The line's other keys do reach it. -/
public def pictureResets (o : Array Tok) : Bool := (readLineWidth o.toList).isSome

/-- One `\tikzset` line folded into what the document has set so far: its
definitions into the bundles, and the entries the subset reads into the
outermost bracket — a later line's value replacing an earlier one's rather
than standing beside it, the rule `inheritOpts` holds within a bracket and
for the same reason — except a width, which every picture resets
(`pictureResets`). The fold's body as its own function, so
`documentOptsStep_covers` can state what one line contributes without
reducing the fold. -/
public def documentOptsStep (sa : List (String × Array Tok) × Array (Array Tok))
    (keys : Array Tok) : List (String × Array Tok) × Array (Array Tok) :=
  let (after, unread) := readStyleList sa.1 keys
  (after, inheritOpts sa.2 (unread.filter fun o => readsOpt after o && !pictureResets o))

/-- What a document's `\tikzset` lines set for every picture in it: the
entries that are not definitions, that the subset reads, and that no
picture resets, folded in source order. The definitions those lines carry
are `documentStyles`; what neither reads is `unreadKeys`. -/
public def documentOpts (sets : Array (Array Tok)) : Array (Array Tok) :=
  (sets.foldl documentOptsStep ([], #[])).2

/-- **A line's read entry is one the document has set.** An entry of a
`\tikzset` line that is no definition, that the subset reads and that no
picture resets enters the outermost bracket, whatever the lines before it
set — so a tip declared once in the preamble is a key of the document and
not a dropped one. With `outerRead_covers` and `merge_global_covers` this is
the chain from the line that wrote the key to the bracket a statement
reads. -/
public theorem documentOptsStep_covers {styles : List (String × Array Tok)}
    {acc : Array (Array Tok)} {keys o : Array Tok}
    (h : o ∈ (readStyleList styles keys).2)
    (hr : readsOpt (readStyleList styles keys).1 o = true)
    (hw : pictureResets o = false) :
    o ∈ (documentOptsStep (styles, acc) keys).2 := by
  simp only [documentOptsStep, inheritOpts, Array.mem_append, Array.mem_filter]
  exact Or.inr ⟨h, by simp [hr, hw]⟩

/-- **No document-level line sets a picture's width** (`_mem`): every entry
the document's `\tikzset` lines hand the pictures is drawn from those no
picture resets. The defect handed them the line's width, so a document
whose preamble said `semithick` stroked every picture at 0.6 pt where
lualatex strokes 0.4 pt — and the private reference corpus's pictures with
it, on every page. -/
public theorem documentOpts_mem (sets : Array (Array Tok)) {o : Array Tok}
    (h : o ∈ documentOpts sets) : pictureResets o = false := by
  unfold documentOpts at h
  have step : ∀ (sa : List (String × Array Tok) × Array (Array Tok)) (keys : Array Tok),
      (∀ e ∈ sa.2, pictureResets e = false) →
        ∀ e ∈ (documentOptsStep sa keys).2, pictureResets e = false := by
    intro sa keys hsa e he
    simp only [documentOptsStep, inheritOpts, Array.mem_append, Array.mem_filter] at he
    rcases he with ⟨he, _⟩ | ⟨_, hk⟩
    · exact hsa e he
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
      exact hk.2
  have := Array.foldl_induction (as := sets)
    (motive := fun _ sa => ∀ e ∈ sa.2, pictureResets e = false)
    (init := (([] : List (String × Array Tok)), (#[] : Array (Array Tok))))
    (f := documentOptsStep) (by intro e he; simp at he)
    (fun i sa hsa => step sa sets[i] hsa)
  exact this o h

/-- The shape filter keeps what this shape reads: an entry a statement's own
loop would read is not dropped on its way in from an outer bracket. -/
public theorem outerRead_covers {reads : Array Tok → Bool}
    {global picture : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ global) (hr : reads o) : o ∈ (outerRead reads global picture).1 := by
  simp only [outerRead, Array.mem_filter]
  exact ⟨h, hr⟩

/-- What one `\tikzset` key list leaves unread, named for a diagnostic at
the line that wrote it. The elaborator's one caller; the fold the pictures
read is `documentStyles`. A key the engine reads (`setsEngineKey`) is not
among them, nor is one a statement reads (`readsOpt`, carried into every
bracket by `documentOpts`): those are honoured, not dropped. -/
public def unreadKeys (styles : List (String × Array Tok)) (keys : Array Tok) : Array String :=
  let (after, unread) := readStyleList styles keys
  (unread.filter fun e => !setsEngineKey e && !readsOpt after e).filterMap fun e =>
    -- The key's own name, whole: the path before any `/`, which is the name
    -- whether the entry is a bare key or a definition the subset has no
    -- loop for. Naming the entry's *first token* reported `every` for
    -- `every label` and `edge` for `edge-muted` — a message about a key
    -- nothing in the document is called.
    (keyName ((e.toList.filter (· != .space)).takeWhile
      (fun t => !isSym '/' t))).map (fun n => s!"'{n}'")
      |>.orElse fun _ => (e[0]?).map tokText

/-- One part of a `\node` statement's prologue: everything before the
body. pgf reads `[keys]`, `(name)` and `at (coord)` in any order and any
number of times, ending at the `{text}` (TikZ manual §17.2, the node
specification), so a prologue is a *fold* over these rather than a fixed
sequence — a second bracket is ordinary pgf, and so is a bracket standing
after `at`. -/
public inductive Part where
  | brack (inner : Array Tok)
  | name (n : String)
  | atCoord (xs ys : Array Tok)
  deriving Repr, Inhabited

/-- A node's prologue as read so far. -/
public structure Prologue where
  /-- Every option bracket's inner tokens, in source order: a later
  bracket's keys stand later, so precedence stays the merge's own rule
  (`mergeOpts`) and is not this reader's to decide. -/
  brackets : Array (Array Tok) := #[]
  name : Option String := none
  /-- The `at (x, y)` coordinate's two expression slices. -/
  at? : Option (Array Tok × Array Tok) := none
  deriving Repr, Inhabited

/-- Fold one part in. The shape is what makes the reader order-free by
construction rather than by inspection: each part touches one field, so no
part can be the one a position forgot. -/
public def Prologue.step (p : Prologue) : Part → Prologue
  | .brack inner => { p with brackets := p.brackets.push inner }
  | .name n => { p with name := p.name.orElse fun _ => some n }
  | .atCoord xs ys => { p with at? := some (xs, ys) }

/-- **A name is the node's whichever side of the bracket it stands on, and
a bracket is the node's whichever side of `at`.** Folding two different
parts in either order leaves the same prologue: the registered `_agree`
shape over the spellings pgf reads alike.

The defect this closes was a reader one position short of a loop — one
bracket, and only before `at` — so `\node[keys] (n) [keys] {text}` and
`\node (n) at (c) [keys] {text}`, both of which pgf compiles without
complaint, reached the body arm with a `[` where a `{` was expected and
were refused for *needing a body they had written*. Three errors on the
private reference corpus read as a missing label. Stated as commutation
rather than as a list of accepted orders, because the list is what the old
reader was. -/
public theorem prologue_swap_agree (p : Prologue) (inner : Array Tok) (n : String)
    (xs ys : Array Tok) :
    (p.step (.brack inner)).step (.name n) = (p.step (.name n)).step (.brack inner) ∧
    (p.step (.brack inner)).step (.atCoord xs ys)
      = (p.step (.atCoord xs ys)).step (.brack inner) ∧
    (p.step (.name n)).step (.atCoord xs ys)
      = (p.step (.atCoord xs ys)).step (.name n) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Nothing a bracket said is lost to a later part: a fold step either
leaves the bracket list alone or appends to it, and never rewrites it — so
a key cannot be dropped by what was written after it. The `_covers` half of
the pair above. -/
public theorem prologue_brackets_covers (p : Prologue) (part : Part) :
    (p.step part).brackets = p.brackets ∨
      ∃ inner, (p.step part).brackets = p.brackets.push inner := by
  cases part
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- A `(name)` group at `i`: the name and the index past its `)`. A name
holding a `,` is a coordinate, not a name. -/
private def readName (ts : Array Tok) (i : Nat) : Option (String × Nat) := Id.run do
  unless ts[i]? == some (.sym '(') do return none
  let mut j := i + 1
  let mut inner : Array Tok := #[]
  for _ in [i+1:ts.size + 1] do
    if h : j < ts.size then
      if ts[j] == .sym ')' || ts[j] == .sym '(' then break
      inner := inner.push ts[j]
      j := j + 1
    else break
  unless ts[j]? == some (.sym ')') do return none
  match nameOfToks inner.toList with
  | some nm => if nm.contains ',' then return none else return some (nm, j + 1)
  | none => return none

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
  let mut width : Sp := Ir.Pic.thinWidth
  -- The declarations a `font=` named, wrapping every label line.
  let mut fontStyles : Array Ir.Style := #[]
  -- `text height=`/`text depth=` as written: font-relative units resolve
  -- against the node's own face, once its label is measured.
  let mut textHt : Option (List Tok) := none
  let mut textDp : Option (List Tok) := none
  -- `align=`: the side the text's lines stand flush to (centred by default).
  let mut textAlign : Ir.Pic.LabelAlign := .center
  let mut minW : Sp := 0
  let mut minH : Sp := 0
  -- `inner sep` as the document set it, per axis; `none` is pgf's default,
  -- resolved below against this node's own em.
  let mut xsep : Option Sp := none
  let mut ysep : Option Sp := none
  -- `outer sep` likewise; `none` is pgf's `auto`, half the line width.
  let mut oxsep : Option Sp := none
  let mut oysep : Option Sp := none
  let mut own : Array (Array Tok) := #[]
  -- pgf reads `[keys]`, `(name)` and `at (coord)` in any order and any
  -- number of times, up to the `{text}` (TikZ manual §17.2). So the
  -- prologue is a loop over the three parts, folded through
  -- `Prologue.step` — whose `prologue_swap_agree` is why no position can
  -- be the one a part was forgotten in.
  let mut pro : Prologue := {}
  let mut bad : Option PDiag := none
  for _ in [0:ts.size + 1] do
    if h : i < ts.size then
      if ts[i] == .sym '[' then
        let mut j := i + 1
        let mut inner : Array Tok := #[]
        for _ in [i+1:ts.size + 1] do
          if h2 : j < ts.size then
            if ts[j] == .sym ']' then break
            inner := inner.push ts[j]
            j := j + 1
          else break
        unless ts[j]? == some (.sym ']') do
          bad := some (.E0333, "'\\node' options miss their ']'; the node is not drawn")
          break
        pro := pro.step (.brack inner)
        i := j + 1
      else if ts[i] == .ident "at" then
        match readCoord ts (i + 1) with
        | .error e =>
          bad := some (.E0333, s!"in '\\node', {e}; the node is not drawn")
          break
        | .ok ((xs, ys), i2) =>
          pro := pro.step (.atCoord xs ys)
          i := i2
      else
        match readName ts i with
        | some (nm, i2) =>
          pro := pro.step (.name nm)
          i := i2
        | none => break
    else break
  if let some d := bad then return ev.diag d
  for inner in pro.brackets do
    own := own ++ expandOpts cx.styles inner
  let nodeName : Option String := pro.name
  ev := { ev with readOpts := true }
  let dsc : Sp × Sp := (cx.dist.1 * cx.scale / 1000, cx.dist.2 * cx.scale / 1000)
  let mut place : Option (Dir × String × (Sp × Sp)) := none
  let mut contents : Option (Array LabelLine) := none
  let (gOuter, pOuter) := outerRead readsNodeOpt cx.global cx.opts
  for opt in mergeOpts gOuter pOuter (cx.everyNode ++ cx.everyText) own do
    match readPlace dsc opt.toList with
    | some p => place := some p
    | none =>
    match readLineWidth opt.toList with
    | some (.ok w) => width := w
    | some (.error e) =>
      ev := ev.diag (.W0334, s!"in 'line width', {e}; the option is dropped")
    | none =>
    match opt.toList with
    | .ident "font" :: .sym '=' :: rest =>
      -- The key replaces what an earlier `font=` set, as TikZ's does.
      let (sz, sts, unread) := readFont cx rest
      scale := (sz.map fun k => k * factor / 1000).getD factor
      fontStyles := sts
      for w in unread do
        ev := ev.diag (.W0334, s!"node option 'font={w}' is outside the rendered \
picture subset; the switch is dropped")
    | .ident "text" :: .ident "height" :: .sym '=' :: rest => textHt := some rest
    | .ident "text" :: .ident "depth" :: .sym '=' :: rest => textDp := some rest
    | .ident "align" :: .sym '=' :: rest =>
      match textAlignOf rest with
      | some a => textAlign := a
      | none =>
        ev := ev.diag (.W0334, s!"node option 'align={String.join (rest.map tokText)}' \
is outside the rendered picture subset; the lines stay centred")
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
    -- `inner sep` moves the node's *border*: pgf manual §17.2.2 has it
    -- padding the text on every side, and §17.5.2's anchors sit on the
    -- border. So it moves where an anchor stands, how far a relative
    -- placement parts two nodes, and a drawn outline around its text; a
    -- declared minimum, where larger, is the outline instead.
    | .ident "inner" :: .ident "sep" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => xsep := some d; ysep := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'inner sep', {e}; the option \
is dropped")
    | .ident "inner" :: .ident "xsep" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => xsep := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'inner xsep', {e}; the option \
is dropped")
    | .ident "inner" :: .ident "ysep" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => ysep := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'inner ysep', {e}; the option \
is dropped")
    -- `outer sep` moves the anchors past the border and never the drawn
    -- path (pgfmoduleshapes.code.tex); `auto` is its initial value, half
    -- the node's line width.
    | .ident "outer" :: .ident "sep" :: .sym '=' :: rest =>
      match rest, readDim rest with
      | [.ident "auto"], _ => oxsep := none; oysep := none
      | _, .ok d => oxsep := some d; oysep := some d
      | _, .error e => ev := ev.diag (.W0334, s!"in 'outer sep', {e}; the option \
is dropped")
    | .ident "outer" :: .ident "xsep" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => oxsep := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'outer xsep', {e}; the option \
is dropped")
    | .ident "outer" :: .ident "ysep" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => oysep := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'outer ysep', {e}; the option \
is dropped")
    -- `node contents={...}`: the body a bundle carries, so a use site can
    -- write `\node[bundle] (n);` with nothing of its own (pgf manual
    -- §17.2.1). A body written at the use site wins.
    | .ident "node" :: .ident "contents" :: .sym '=' :: rest =>
      -- `node contents={x}` and `node contents=x` alike: pgf takes the
      -- braces off a single group, and a bare run is the body itself.
      let g : List Tok := if let [.group inner] := rest then inner else rest
      let (ls, ds) := nodeLabel cx env g
      contents := some ls
      ev := ds.foldl Ev.diag ev
    | [] => pure ()
    | o :: rest =>
      ev := ev.diag (.W0334, s!"node option {optName (o :: rest)} is outside the rendered \
picture subset; the option is dropped")
  -- pgf places a node with no `at` at the path's current point, which at
  -- the start of a node statement is the origin; a relative placement
  -- (`right=of a`) puts it one `node distance` from the node it names.
  -- Resolution reads the node table the run was seeded with, so
  -- declaration order does not decide it (`evalFixed`): a reference to a
  -- node written later resolves on the next run, and only a name no node
  -- carries — or a cycle — is refused, by that name.
  let atCoord : Option (Array Tok × Array Tok) := pro.at?
  let unresolved : Bool :=
    atCoord.isNone && (match place with
      | some (_, target, _) => (ev.nodes.lookup target).isNone
      | none => false)
  let dimF (d : Sp) : Sp :=
    if cx.transformShape then d * cx.scale / 1000 else d
  let bodyOf : Except PDiag (Array LabelLine × Array PDiag) :=
    match ts[i]? with
    | some (.group body) =>
      if h : i + 1 < ts.size then
        .error (.W0334, s!"'\\node' continues with {tokText ts[i+1]}, \
outside the rendered picture subset; the label is not drawn")
      else
        .ok (nodeLabel cx env body)
    | _ =>
      match contents with
      | some c => .ok (c, #[])
      | none =>
        .error (.E0333, "'\\node' needs a '{text}' body; the label is not drawn")
  let bodyOf := bodyOf.map fun (ls, ds) => (fontLines fontStyles ls, ds)
  -- The label's lines set at the origin: the one set of shapes the node's
  -- extent, its baseline and its text box are all read off, through the
  -- face the driver resolved (`Cx.metric`) — the measurement the picture's
  -- box reads (`Ir.Pic.Shape.inkBox`), so neither can drift from it.
  let shapes0 : Array Ir.Pic.Shape :=
    match bodyOf with
    | .ok (lines, _) => stackLabels 0 0 cx.bodySize scale color .center lines #[]
    | .error _ => #[]
  -- The half-extents the anchors stand on: the face's band around each line
  -- (`Ir.Pic.labelInkBox`), which is where the engine seats the letters.
  let inkHalf : Sp × Sp :=
    let bands := shapes0.filterMap fun s => match s with
      | .label lx ly content _ sz al => some (Ir.Pic.labelInkBox lx ly al (cx.metric content sz))
      | .rect .. | .circle .. | .frame .. | .edge .. => none
    let ((bx0, by0), (bx1, by1)) := Ir.Pic.Box.hull bands
    (max (-bx0) bx1, max (-by0) by1)
  -- Each line's baseline and measurement. The label's *first* line is the
  -- node's baseline, as it is for any TeX box: what the `base` family of
  -- anchors reads.
  let lineInks : Array (Sp × Ir.Pic.LabelInk) := shapes0.filterMap fun s =>
    match s with
    | .label _ ly content _ sz al =>
      let m := cx.metric content sz
      some (Ir.Pic.labelBaseline ly al m, m)
    | .rect .. | .circle .. | .frame .. | .edge .. => none
  let baseOff : Sp := (lineInks[0]?.map (·.1)).getD 0
  -- The border is the text *plus* `inner sep` (pgf manual §17.2.2), so an
  -- anchor stands clear of the letters rather than on them. The default is
  -- font-relative and this node's own size is its em, which is why it is
  -- resolved here and not a constant; its ex is the face's.
  let em : Sp := cx.bodySize * (scale : Int) / 1000
  let ex : Sp := (lineInks[0]?.map (·.2.ex)).getD 0
  let sepX : Sp := xsep.getD (innerSep em)
  let sepY : Sp := ysep.getD (innerSep em)
  -- **The node's text box** (pgf's `\pgfnodeparttextbox`), around the
  -- node's centre: how far the glyphs of its lines reach above and below
  -- them, or the height and depth `text height`/`text depth` declare
  -- (tikz.code.tex, `\tikz@fig@continue`, which sets the box's `\ht` and
  -- `\dp`). A declared box is TikZ's to the letter: the node centres it, so
  -- its baseline stands half the height less the depth below the centre
  -- and every anchor is one inner sep beyond it. So is the glyphs' own box
  -- of a drawn node outlined around its text (`nodeOutline`): its outline,
  -- the anchors on it and the edges from them follow the node's position
  -- and never its letters (`nodeOutline_seat_exact`), and the letters sit
  -- one inner sep inside it on every side. Any other undeclared box keeps
  -- the engine's placement — the face's band centred on the node, the same
  -- seat for every label whatever its letters (`Ir.Pic.labelBaseline`), and
  -- the anchors on that band's border — and the room the picture reserves
  -- is the glyphs' own box, so a label with no descender keeps one inner
  -- sep below it and not the face's descent as well.
  let glyphs : Sp × Sp := lineInks.foldl (fun (lo, hi) (b, m) =>
    (min lo (b - m.boxDepth), max hi (b + m.boxHeight))) (baseOff, baseOff)
  let dimOf (ts : Option (List Tok)) : Option Sp :=
    ts.bind fun ts => (readNodeDim em ex ts).toOption
  let declHt := dimOf textHt
  let declDp := dimOf textDp
  for (key, ts) in [("text height", textHt), ("text depth", textDp)] do
    if let some ts := ts then
      if let .error e := readNodeDim em ex ts then
        ev := ev.diag (.W0334, s!"in '{key}', {e}; the option is dropped")
  -- A node declaring both minimums (a circle, its size) keeps the declared
  -- outline and the anchors it always had; any other drawn one is outlined.
  let declaredExtent : Bool := if isCircle then max minW minH > 0 else minW > 0 && minH > 0
  let outlined : Bool := (draw.isSome || fillCol.isSome) && !declaredExtent
  let (base, boxLo, boxHi, halfB) : Sp × Sp × Sp × Sp :=
    if declHt.isNone && declDp.isNone && !outlined then (baseOff, glyphs.1, glyphs.2, inkHalf.2)
    else
      let ht := declHt.getD (glyphs.2 - baseOff)
      let dp := declDp.getD (baseOff - glyphs.1)
      let (b0, lo, hi) := textSeat ht dp
      (b0, lo, hi, (ht + dp) / 2)
  -- The drawn outline's width and height (`nodeOutline`, centred on the
  -- node by `nodeOutline_seat_exact`), where the node has one.
  let outline? : Option (Sp × Sp) :=
    if outlined then
      let (_, w, h) := nodeOutline isCircle (dimF minW) (dimF minH) 0 inkHalf.1 boxLo boxHi sepX sepY
      some (w, h)
    else none
  -- The placed node's own half-extents, its side of the border-to-border
  -- gap a relative placement leaves: its drawn outline's where it has one,
  -- else the declared minimum, or the label's own reach where the text
  -- stands proud of it (`Ir.Pic.nodeExtent`, whose `nodeExtent_covers` is
  -- why a placement parts text and not centres).
  let declA : Sp := if isCircle then dimF (max minW minH) / 2 else dimF minW / 2
  let declB : Sp := if isCircle then dimF (max minW minH) / 2 else dimF minH / 2
  let ownA : Sp := match outline? with
    | some (w, _) => w / 2
    | none => borderHalf declA inkHalf.1 sepX
  let ownB : Sp := match outline? with
    | some (_, h) => h / 2
    | none => borderHalf declB halfB sepY
  -- **pgf's anchors stand one outer sep beyond its border** (the
  -- rectangle's `\northeast`/`\southwest` add `outer xsep`/`outer ysep`, the
  -- circle's `\radius` the larger of the two; `auto`, their initial value,
  -- is half the node's line width), while the drawn path stays on the
  -- border: so an edge meets a drawn outline at its stroke's outer edge, and
  -- a relative placement parts two drawn nodes by the node distance and both
  -- outer seps. An undrawn node keeps its anchors on its border: pgf puts
  -- them half a line width out there too, a remainder PLAN records beside
  -- the engine's point, which sets a label 0.37% wider than TeX's
  -- (`Dim.mm`: the big point).
  let pgfBorder : Bool := draw.isSome || fillCol.isSome
  let (outA, outB) : Sp × Sp :=
    if !pgfBorder then (0, 0)
    else
      let ox := oxsep.getD (width / 2)
      let oy := oysep.getD (width / 2)
      if isCircle then (max ox oy, max ox oy) else (ox, oy)
  let anchA : Sp := ownA + outA
  let anchB : Sp := ownB + outB
  let placement : Except PDiag NodePlacement :=
    match atCoord with
    | some (xs, ys) =>
      match evalNum env xs, evalNum env ys with
      | .ok xm, .ok ym => .ok (.absolute (cx.toSp xm) (cx.toSp ym))
      | .error e, _ | _, .error e =>
        .error (.E0333, s!"in '\\node', {e}; the node is not drawn")
    | none =>
      match place with
      | none => .ok (.absolute 0 0)
      | some (dir, target, sep) => .ok (.relative dir target sep)
  let pos : Except PDiag (NodeGeom × List (String × NodeGeom)) := do
    let placement ← placement
    let plan : NodePlan :=
      { name := nodeName, placement
        shape := { x := 0, y := 0, a := anchA, b := anchB, circle := isCircle, base } }
    let (resolved, nodes) := plan.run ev.nodes
    match resolved with
    | .ok geom => return (geom, nodes)
    | .error target =>
      if ev.gapped || cx.parseGap then
        .error (.W0334, s!"'{target}' is declared inside a construct outside \
the rendered picture subset, so no node carries it; the node is not drawn")
      else
        .error (.E0333, s!"in '\\node', no node is named '{target}' to place \
this one against; the node is not drawn")
  -- The body: its own `{...}` group, or what a `node contents=` key
  -- supplied — a style that carries the body is how pgf lets a bundle
  -- draw a node with nothing written at the use site.
  --
  -- **A body the subset cannot read costs the construct, never the label
  -- and never the node.** A node's position and outline are functions of
  -- its options alone, and a name is what every relative placement and
  -- every edge resolves against — so refusing the whole node for one
  -- unreadable inline used to take every node placed against it, and every
  -- edge touching it, with it. The label is the same judgement one level
  -- in: `nodeLabel` keeps the text the body says and names what it could
  -- not draw, because an empty diagram tells a reader nothing where a
  -- degraded word tells them almost everything.
  match pos with
  | .ok (geom, nodes) =>
        let sx := geom.x
        let sy := geom.y
        -- pgf's natural bounding box includes the node's shape — its text
        -- box plus `inner sep`, or the declared minimum where larger —
        -- whether or not a path paints it (§17.2.2); a drawn outline is
        -- that shape.
        let border : Ir.Pic.Box :=
          if outline?.isSome then ((sx - ownA, sy - ownB), (sx + ownA, sy + ownB))
          else
            ((sx - ownA, sy + min (boxLo - sepY) (-declB)),
             (sx + ownA, sy + max (boxHi + sepY) declB))
        -- The resolver registered the same geometry the node now uses.
        -- pgf anchors on a named shape even when its path is never painted.
        ev := { ev with borders := ev.borders.push border, nodes }
        -- The node's outline, before its label so the fill paints under
        -- the text. A declared extent is the declared minimum (pgf manual
        -- §"Shapes": extent = max(minimum, text extent + 2·inner sep) per
        -- axis, and the minimum is the whole answer when it dominates the
        -- body — a body wider than both declared minimums stands proud of
        -- the border); an undeclared one is `nodeOutline`'s, centred on the
        -- node. pgf draws a node's path only when `draw` or `fill` asks it
        -- to. Minimums scale with the picture only under `transform shape`
        -- (§25.4); the line width is graphic state and never scales.
        if draw.isSome || fillCol.isSome then
          let stroke : Option Ir.Pic.Stroke := draw.map fun c =>
            { color := c.getD Ir.Color.black
              width := width
              dash := dash }
          match outline? with
          | some (w, h) =>
            let shape : Ir.Pic.Shape :=
              if isCircle then .circle sx sy (w / 2) stroke fillCol
              else .frame (sx - w / 2) (sy - h / 2) w h stroke fillCol
            ev := { ev with shapes := ev.shapes.push shape }
          | none =>
            let shape : Ir.Pic.Shape :=
              if isCircle then .circle sx sy (dimF (max minW minH) / 2) stroke fillCol
              else .frame (sx - dimF minW / 2) (sy - dimF minH / 2) (dimF minW) (dimF minH)
                stroke fillCol
            ev := { ev with shapes := ev.shapes.push shape }
        match bodyOf with
        | .error d => return ev.diag d
        | .ok (lines, mdiags) =>
          ev := mdiags.foldl Ev.diag ev
          -- A declared text box moves the letters to its baseline; the
          -- engine's own placement moves nothing. `align=` then stands
          -- each line flush within the box.
          let placed := alignLabels cx.metric textAlign
            (stackLabels sx (sy + (base - baseOff)) cx.bodySize scale color .center lines #[])
          ev := { ev with shapes := ev.shapes ++ placed }
          return ev
  | .error d =>
    return (if unresolved then { ev with deferred := ev.deferred + 1 } else ev).diag d

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

/-- A name that resolved to nothing. Which refusal it is depends on *why*
there is no such node: a declaration the walk could not reach is a gap in
the rendered subset (`W0334`, `pending`), and a name nothing declared is the
document's (`E0333`, `dropped`). Reporting both as the second is what made
one unreadable conditional read as five separate errors, each naming a node
the author had written.

This is not a demotion of a loss but a correction of the code: the loss was
always `pending` where the cause is a construct outside the subset, and the
walk was classifying by the symptom — a missing name — rather than by the
cause. The gate's premise is structural: `Ev.gapped` and `Cx.parseGap` are
set only where a `W0334` naming that construct was raised, so the quiet
answer can never be the whole story a reader gets.
-- premise: unreachedName_accounts — the gate reads a flag set only beside a
-- named gap, so a picture with no gap cannot take this path. -/
public def unreachedName (gapped : Bool) (what : String) : PDiag :=
  if gapped then
    (.W0334, s!"{what} is declared inside a construct outside the rendered \
picture subset, so no node carries it; the edge is not drawn")
  else (.E0333, s!"in '\\draw', no node is named '{what}'; the edge is not drawn")

/-- **A quiet refusal is paid for by a named gap.** The registered
`_accounts` shape: the pending answer is reachable only when a construct
outside the subset was named, so the two codes stay one code one meaning and
the reader is never left with the softer of the two alone. -/
public theorem unreachedName_accounts (gapped : Bool) (what : String)
    (h : (unreachedName gapped what).1 = .W0334) : gapped = true := by
  cases gapped
  · simp only [unreachedName, Bool.false_eq_true] at h
    exact absurd h (by simp)
  · rfl

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

/-- The To-Path library's settings for one `to` (pgf's
tikzlibrarytopaths.code.tex, TeX Live 2026). Tangents are whole degrees;
`rel` reads them against the chord (`relative`, which `bend left`/`bend
right` turn on); `bend` is the angle the value-less bend keys read
(`\def\tikz@to@bend{30}`, line 119); each end's looseness is in milli
(`\def\tikz@to@out@looseness{1}`, line 124); `curved` is
`\tikz@to@switch@on`, without which a `to` is the straight line. A curve
switched on by one tangent keeps the library's other one
(`\def\tikz@to@out{45}`, `\def\tikz@to@in{135}`, lines 121–122). -/
private structure ToSpec where
  outA : Int := 45
  inA : Int := 135
  rel : Bool := false
  bend : Int := 30
  outL : Int := 1000
  inL : Int := 1000
  curved : Bool := false

/-- `bend left=α` and `bend right=α` (lines 30–53): the angle becomes the
bend, `out` is it or its negation, `in` is 180 − `out`, and both read
against the chord. -/
private def ToSpec.bendTo (s : ToSpec) (left : Bool) (b : Int) : ToSpec :=
  let o := if left then b else -b
  { s with bend := b, outA := o, inA := 180 - o, rel := true, curved := true }

/-- One option entry read as a To-Path key, in the order the library applies
them. `none` when the entry is no To-Path key; the error is a value that
does not evaluate. -/
private def ToSpec.read (s : ToSpec) (env : List (String × Val)) (opt : Array Tok) :
    Option (Except String ToSpec) :=
  let num (rest : List Tok) (k : Int → ToSpec) : Option (Except String ToSpec) :=
    some ((evalNum env rest.toArray).map k)
  let deg (m : Int) : Int := (m + 500) / 1000
  match opt.toList with
  | .ident "out" :: .sym '=' :: rest => num rest fun m => { s with outA := deg m, curved := true }
  | .ident "in" :: .sym '=' :: rest => num rest fun m => { s with inA := deg m, curved := true }
  | [.ident "bend", .ident "left"] => some (.ok (s.bendTo true s.bend))
  | [.ident "bend", .ident "right"] => some (.ok (s.bendTo false s.bend))
  | .ident "bend" :: .ident "left" :: .sym '=' :: rest => num rest fun m => s.bendTo true (deg m)
  | .ident "bend" :: .ident "right" :: .sym '=' :: rest => num rest fun m => s.bendTo false (deg m)
  | .ident "bend" :: .ident "angle" :: .sym '=' :: rest => num rest fun m => { s with bend := deg m }
  | [.ident "relative"] | [.ident "relative", .sym '=', .ident "true"] =>
    some (.ok { s with rel := true })
  | [.ident "relative", .sym '=', .ident "false"] => some (.ok { s with rel := false })
  | .ident "looseness" :: .sym '=' :: rest =>
    num rest fun m => { s with outL := m, inL := m, curved := true }
  | .ident "out" :: .ident "looseness" :: .sym '=' :: rest =>
    num rest fun m => { s with outL := m, curved := true }
  | .ident "in" :: .ident "looseness" :: .sym '=' :: rest =>
    num rest fun m => { s with inL := m, curved := true }
  | _ => none

/-- `p` turned about `c` by `deg`: where pgf's relative curve looks from a
node's centre (lines 262–296 rotate the other endpoint about this one before
asking the shape for its border). Milli trigonometry, one rounding per axis. -/
private def turnAbout (c p : Sp × Sp) (deg : Int) : Sp × Sp :=
  let dx := p.1 - c.1
  let dy := p.2 - c.2
  (c.1 + (dx * cosDeg deg - dy * sinDeg deg) / 1000,
   c.2 + (dx * sinDeg deg + dy * cosDeg deg) / 1000)

/-- A relative curve's control point (lines 318–352): in the frame whose
x-axis runs along the chord `v` from the start's border to the target's,
`dist` along the declared angle, where `dist` is 0.3915·‖v‖ scaled by the
end's looseness — so the offset is the chord itself turned by the angle and
scaled, which needs neither a square root nor an arctangent. -/
private def turnedControl (px py vx vy deg loose : Int) : Int × Int :=
  (px + (vx * cosDeg deg - vy * sinDeg deg) * 3915 * loose / 10000000000,
   py + (vx * sinDeg deg + vy * cosDeg deg) * 3915 * loose / 10000000000)

/-- **A bent edge leaves at its angle to its chord.** The control offset is
the chord turned by the declared angle — `(vₓ cos α − v_y sin α, vₓ sin α +
v_y cos α)` over the milli table — times the To-Path factor 0.3915 and the
looseness, inside one rounding per axis. pgf builds the same point as
`\pgfpointpolar{α}{dist}` under the transform `[n −n⊥]` of the unit chord
`n`, and `dist·n` is `0.3915·looseness·v`. The same function builds both
ends, the arrival one from the target with `in`, as the library does. -/
private theorem turnedControl_between (px py vx vy deg loose : Int) :
    10000000000 * ((turnedControl px py vx vy deg loose).1 - px) ≤
      (vx * cosDeg deg - vy * sinDeg deg) * 3915 * loose ∧
    (vx * cosDeg deg - vy * sinDeg deg) * 3915 * loose <
      10000000000 * ((turnedControl px py vx vy deg loose).1 - px) + 10000000000 ∧
    10000000000 * ((turnedControl px py vx vy deg loose).2 - py) ≤
      (vx * sinDeg deg + vy * cosDeg deg) * 3915 * loose ∧
    (vx * sinDeg deg + vy * cosDeg deg) * 3915 * loose <
      10000000000 * ((turnedControl px py vx vy deg loose).2 - py) + 10000000000 := by
  simp only [turnedControl]
  generalize (vx * cosDeg deg - vy * sinDeg deg) * 3915 * loose = d
  generalize (vx * sinDeg deg + vy * cosDeg deg) * 3915 * loose = e
  omega

/-- One path operation between two endpoints: pgf manual §14.13 (to
paths) — `--` and a bare `to` are the straight line; a `to` whose keys
switched the curve on is the cubic its `ToSpec` describes, the control
points 0.3915·‖d‖·looseness along the departure and arrival tangents (the
To-Path library's own factor), absolute or against the chord. -/
private inductive DrawOp where
  | straight
  | curve (spec : ToSpec)
  /-- `rectangle`: the box the current point and the next corner span, a
  closed subpath of its own (pgf manual §14.4). -/
  | rect
  /-- `-- cycle`: the side back to the current subpath's start, closing it
  (pgf manual §14.2). -/
  | cycle

/-- A path node's resolved text and attachment. Separation is per axis,
as in pgf's rectangle shape; an undeclared outer separation reads the
path's eventual stroke width. -/
private structure EdgeLabel where
  lines : Array LabelLine
  color : Ir.Color
  scale : Nat
  placement : Option Dir
  autoLeft : Option Bool
  align : Ir.Pic.LabelAlign
  inner : Sp × Sp
  outer : Option Sp × Option Sp

/-- Move an already measured label without changing its text or baseline
rule. Other shapes are unchanged: this is the final step of path-label
placement, after the path itself has been resolved. -/
public def translateLabel (offset : Sp × Sp) : Ir.Pic.Shape → Ir.Pic.Shape
  | .label x y content color size align =>
    .label (x + offset.1) (y + offset.2) content color size align
  | s@(.rect ..) | s@(.circle ..) | s@(.frame ..) | s@(.edge ..) => s

/-- The emitted label's text box is exactly the translated IR box.
Attachments can therefore use `Box.attachOffset_contract` without a
second, backend-dependent measurement. -/
public theorem translateLabel_box_projects (offset : Sp × Sp) (x y : Sp)
    (content : Array Ir.Inline) (color : Ir.Color) (size : Nat)
    (align : Ir.Pic.LabelAlign) (metric : Ir.Pic.LabelMetric) :
    match translateLabel offset (.label x y content color size align) with
    | .label u v text _ scale al =>
      let box := Ir.Pic.labelTextBox x y align (metric content size)
      Ir.Pic.labelTextBox u v al (metric text scale) =
        ((box.1.1 + offset.1, box.1.2 + offset.2),
         (box.2.1 + offset.1, box.2.2 + offset.2))
    | .rect .. | .circle .. | .frame .. | .edge .. => False :=
  Ir.Pic.labelTextBox_translate_exact x y align (metric content size) offset

/-- Stack and align once, then attach the whole measured text box. All
path operations use this translation: individual lines retain their
leading, and both backends receive the same coordinates and baselines.
The anchor is the path point; direction is explicit or its local tangent's
automatic side. pgfmoduleshapes.code.tex declares inner sep=.3333em and
outer sep=.5\pgflinewidth; the caller resolves the font-relative inner sep.
`Ir.Pic.Box.attachOffset_contract` guarantees each requested clearance. -/
private def EdgeLabel.place (label : EdgeLabel) (cx : Cx) (width : Sp)
    (anchor tangent : Sp × Sp) : Array Ir.Pic.Shape :=
  let lines := alignLabels cx.metric label.align
    (stackLabels 0 0 cx.bodySize label.scale label.color .center label.lines #[])
  let direction := label.placement.orElse fun _ =>
    label.autoLeft.map fun left => autoDir left tangent.1 tangent.2
  let offset := match direction with
    | none => anchor
    | some dir =>
      let box := Ir.Pic.Box.hull (lines.filterMap fun (shape : Ir.Pic.Shape) => match shape with
        | .label x y content _ size align =>
          some (Ir.Pic.labelTextBox x y align (cx.metric content size))
        | .rect .. | .circle .. | .frame .. | .edge .. => none)
      let gap := (label.inner.1 + label.outer.1.getD (width / 2),
                  label.inner.2 + label.outer.2.getD (width / 2))
      box.attachOffset anchor (dir.offset (1, 1)) gap
  lines.map (translateLabel offset)

/-- `\draw[opts] (a) -- (b) to[out=α,in=β] (c) ...;` — a stroked edge
chain between named nodes and coordinates, border-anchored at named
endpoints (along the declared tangent for a curve), with `rectangle`
outlines and `-- cycle` closing a subpath. Options: `thick`,
`dashed`/`dotted` (and the densely form), an arrow spec (`->`/`-latex`,
both the triangle tip), a colour, and declared style bundles; an in-path
`node[...] {...}` is an edge label at the segment's midpoint. Anything
else outside the subset loses only itself where an option, and the edge
by name where a path operation. -/
private def evalDraw (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) (isPath : Bool := false) : Ev := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut ev := ev
  let mut color := Ir.Color.black
  let mut dash : Ir.Pic.Dash := .solid
  let mut width : Sp := Ir.Pic.thinWidth
  let mut arrow := false
  -- `\path` paints nothing of itself; an `edge` operation or an explicit
  -- `draw` key is what makes it stroke (pgf's `every edge` carries `draw`).
  let mut strokes := !isPath
  -- Did one of the chain's operation brackets already declare a stroke?
  -- The subset draws one stroke per edge, so a second declaration is a
  -- loss to name rather than resolve in silence.
  let mut opStroke := false
  -- `auto`/`swap` (pgf manual §17.8): whether an in-path label stands beside
  -- the path, and on which side of its direction. Set at any level — the
  -- document's `\tikzset`, the picture's bracket, `every path`, or this
  -- statement's own — because that is where pgf reads it; a label's own
  -- bracket still wins, as every inner setting does.
  let mut autoOn := false
  let mut autoLeft := true
  -- The To-Path keys the statement sets: every `to` and `edge` of the chain
  -- starts from them, and its own bracket refines them.
  let mut toSpec : ToSpec := {}
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
  let (gOuter, pOuter) := outerRead (readsPathOpt cx.styles) cx.global cx.opts
  for opt in mergeOpts gOuter pOuter cx.everyPath own do
    match arrowTipName opt.toList with
    | some tip =>
      if drawsAsArrow cx.styles tip then arrow := true
      else
        ev := ev.diag (.W0334, s!"arrow tip '{tip}' is outside the rendered \
picture subset; the edge is drawn without a head")
    | none =>
    match readLineWidth opt.toList with
    | some (.ok w) => width := w
    | some (.error e) =>
      ev := ev.diag (.W0334, s!"in 'line width', {e}; the option is dropped")
    | none =>
    match opt.toList with
    | [.ident "draw"] => strokes := true
    -- `auto` puts an in-path label beside the path instead of on it;
    -- `auto=left`/`auto=right` name the side and `auto=false` turns it off.
    -- `swap` (and its `'` shorthand) flips whichever side is in force.
    | [.ident "auto"] => autoOn := true
    | [.ident "auto", .sym '=', .ident "left"] => autoOn := true; autoLeft := true
    | [.ident "auto", .sym '=', .ident "right"] => autoOn := true; autoLeft := false
    | [.ident "auto", .sym '=', .ident "false"] => autoOn := false
    | [.ident "swap"] | [.sym '\''] => autoLeft := !autoLeft
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
      strokes := true
    | [] => pure ()
    | o :: rest =>
      match toSpec.read env opt with
      | some (.ok s) => toSpec := s
      | some (.error e) =>
        return ev.diag (.E0333, s!"in '\\draw' option '{keyPath opt.toList}', {e}; \
the edge is not drawn")
      | none =>
      -- A remaining option is a colour spelling, or names itself.
      match evalColor cx env opt with
      | .ok c => color := c
      | .error _ =>
        ev := ev.diag (.W0334, s!"draw option {optName (o :: rest)} is outside the \
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
      -- `(n.west)`: an anchor on a named node, which is a point rather than
      -- a border — pgf uses the named anchor exactly, with no shortening
      -- toward the other endpoint.
      match splitAnchor nm with
      | some (base, an) =>
        match ev.nodes.lookup base with
        | none =>
          return .error (unreachedName (ev.gapped || cx.parseGap) base)
        | some g =>
          match nodeAnchorOf an with
          | some a =>
            let (px, py) := g.anchorPoint a
            return .ok (.point px py, j + 1)
          | none =>
            return .error (.W0334, s!"node anchor '{an}' is outside the rendered \
picture subset; the edge is not drawn")
      | none =>
        return .error (unreachedName (ev.gapped || cx.parseGap) nm)
  let mut pts : Array Anchor := #[]
  let mut ops : Array (DrawOp × Option EdgeLabel) := #[]
  match readAnchor i with
  | .error d => return ev.diag d
  | .ok (a, i2) =>
    pts := pts.push a
    i := i2
  let factor : Nat := if cx.transformShape && cx.scale > 0 then cx.scale.toNat else 1000
  for _ in [0:ts.size + 1] do
    if h : i < ts.size then
      -- the path operation: `--` (closing with `cycle`), `rectangle`, or
      -- `to` with its optional tangents
      let mut op := DrawOp.straight
      if ts[i]? == some (.sym '-') && ts[i+1]? == some (.sym '-') then
        i := i + 2
        if ts[i]? == some (.ident "cycle") then
          op := .cycle
          i := i + 1
      else if ts[i]? == some (.ident "rectangle") then
        op := .rect
        i := i + 1
      else if ts[i]? == some (.ident "to") || ts[i]? == some (.ident "edge") then
        -- `edge` is `to` with `every edge`'s `draw` in force: the same
        -- operation, and the reason a `\path` of edges paints.
        if ts[i]? == some (.ident "edge") then strokes := true
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
          let mut spec := toSpec
          -- Through the same expansion a node's and a path's bracket goes
          -- through, so a bundle applied on an edge operation is the bundle
          -- it names. Reading this one bracket raw was the last place a
          -- declared name reached no reader (`styleName_agree`'s use side).
          for opt in expandOpts cx.styles inner do
            match spec.read env opt with
            | some (.ok s) => spec := s
            | some (.error e) =>
              return ev.diag (.E0333, s!"in '{keyPath opt.toList}=', {e}; the \
edge is not drawn")
            | none =>
            match readLineWidth opt.toList with
            | some (.ok w) =>
              if opStroke then ev := ev.diag (.W0334, "a chain whose \
operations declare more than one stroke is outside the rendered picture \
subset; the last one is drawn")
              opStroke := true
              width := w
            | some (.error e) =>
              ev := ev.diag (.W0334, s!"in 'line width', {e}; the option is dropped")
            | none =>
            match opt.toList with
            -- An operation's own bracket carries stroke keys too, and on
            -- `\path (a) edge [dashed] (b)` they are the whole point: the
            -- dash is what the diagram means by that edge. The subset has
            -- one stroke per edge shape, so a chain whose operations
            -- declare *different* strokes can only draw one — named, not
            -- silently resolved.
            | [.ident "dashed"] =>
              if opStroke then ev := ev.diag (.W0334, "a chain whose \
operations declare more than one stroke is outside the rendered picture \
subset; the last one is drawn")
              opStroke := true
              dash := .dashed
            | [.ident "dotted"] | [.ident "densely", .ident "dotted"] =>
              if opStroke then ev := ev.diag (.W0334, "a chain whose \
operations declare more than one stroke is outside the rendered picture \
subset; the last one is drawn")
              opStroke := true
              dash := .dotted
            | .ident "draw" :: .sym '=' :: rest =>
              match evalColor cx env rest.toArray with
              | .ok c =>
                if opStroke then ev := ev.diag (.W0334, "a chain whose \
operations declare more than one stroke is outside the rendered picture \
subset; the last one is drawn")
                opStroke := true
                color := c
                strokes := true
              | .error e =>
                ev := ev.diag (.E0333, s!"in an edge's 'draw=', {e}; the \
colour is dropped")
            | [] => pure ()
            | o :: rest =>
              ev := ev.diag (.W0334, s!"'to' option {optName (o :: rest)} is outside the \
rendered picture subset; the option is dropped")
          op := if spec.curved then .curve spec else .straight
        else if toSpec.curved then op := .curve toSpec
      else
        return ev.diag (.W0334, s!"'\\draw' continues with {tokText ts[i]}, \
outside the rendered picture subset; the edge is not drawn")
      -- an in-path `node[...] {...}`: an edge label at the segment's
      -- midpoint; placement attaches the whole text box there
      let mut mid : Option EdgeLabel := none
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
        let mut mstyles : Array Ir.Style := #[]
        -- `none` is "this label declared no placement": it then takes the
        -- side `auto` computes from the path's direction, or the path's
        -- midpoint where no `auto` is in force.
        let mut malign : Option Dir := none
        let mut mAuto := autoOn
        let mut mLeft := autoLeft
        -- Keep dimension keys separate from text-font keys. PGF's `font=`
        -- and body switches change the text box, not its dimension font.
        let mut mseps : Array (String × List Tok) := #[]
        -- `align=`: the side the label's lines stand flush to.
        let mut mtext : Ir.Pic.LabelAlign := .center
        -- An edge label is a node: what `every text node part` declared
        -- reaches its text, and its own bracket follows.
        let mut mopts : Array (Array Tok) := cx.everyText
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
          mopts := mopts ++ expandOpts cx.styles inner
        for opt in mopts do
          match opt.toList with
          | .ident "font" :: .sym '=' :: rest =>
            let (sz, sts, unread) := readFont cx rest
            mscale := (sz.map fun k => k * factor / 1000).getD factor
            mstyles := sts
            for w in unread do
              ev := ev.diag (.W0334, s!"edge node option 'font={w}' is outside \
the rendered picture subset; the switch is dropped")
          | .ident "text" :: .sym '=' :: rest =>
            match evalColor cx env rest.toArray with
            | .ok c => mcolor := c
            | .error e =>
              ev := ev.diag (.E0333, s!"in an edge node, {e}; the colour is \
dropped")
          | .ident "align" :: .sym '=' :: rest =>
            match textAlignOf rest with
            | some a => mtext := a
            | none =>
              ev := ev.diag (.W0334, s!"edge node option 'align={String.join (rest.map tokText)}' \
is outside the rendered picture subset; the lines stay centred")
          | .ident "inner" :: .ident "sep" :: .sym '=' :: rest =>
            mseps := mseps.push ("inner sep", rest)
          | .ident "inner" :: .ident "xsep" :: .sym '=' :: rest =>
            mseps := mseps.push ("inner xsep", rest)
          | .ident "inner" :: .ident "ysep" :: .sym '=' :: rest =>
            mseps := mseps.push ("inner ysep", rest)
          | .ident "outer" :: .ident "sep" :: .sym '=' :: rest =>
            mseps := mseps.push ("outer sep", rest)
          | .ident "outer" :: .ident "xsep" :: .sym '=' :: rest =>
            mseps := mseps.push ("outer xsep", rest)
          | .ident "outer" :: .ident "ysep" :: .sym '=' :: rest =>
            mseps := mseps.push ("outer ysep", rest)
          -- The label's own side, on top of whatever the path set.
          | [.ident "swap"] | [.sym '\''] => mLeft := !mLeft
          | [.ident "auto"] => mAuto := true
          | [.ident "auto", .sym '=', .ident "left"] => mAuto := true; mLeft := true
          | [.ident "auto", .sym '=', .ident "right"] => mAuto := true; mLeft := false
          | [.ident "auto", .sym '=', .ident "false"] => mAuto := false
          | [] => pure ()
          | o :: rest =>
            match (keyName (o :: rest)).bind dirOf with
            | some d => malign := some d
            | none =>
              ev := ev.diag (.W0334, s!"edge node option {optName (o :: rest)} is outside \
the rendered picture subset; the option is dropped")
        match ts[i]? with
        | some (.group body) =>
          let (lines, mdiags) := nodeLabel cx env body
          ev := mdiags.foldl Ev.diag ev
          let lines := fontLines mstyles lines
          let em := cx.bodySize * (factor : Int) / 1000
          let ex := (cx.metric #[.text "x"] factor).ex
          let mut inner := (innerSep em, innerSep em)
          let mut outer : Option Sp × Option Sp := (none, none)
          for (key, value) in mseps do
            match readNodeDim em ex value with
            | .error e =>
              ev := ev.diag (.W0334, s!"in edge node '{key}', {e}; the option is dropped")
            | .ok v =>
              match key with
              | "inner sep" => inner := (v, v)
              | "inner xsep" => inner := (v, inner.2)
              | "inner ysep" => inner := (inner.1, v)
              | "outer sep" => outer := (some v, some v)
              | "outer xsep" => outer := (some v, outer.2)
              | _ => outer := (outer.1, some v)
          mid := some { lines, color := mcolor, scale := mscale, placement := malign
                        autoLeft := if mAuto then some mLeft else none
                        align := mtext, inner, outer }
          i := i + 1
        | _ =>
          return ev.diag (.E0333, "an edge 'node' needs a '{text}' body; the \
edge is not drawn")
      -- `cycle` names no endpoint: its segment ends where the subpath began,
      -- which the segment walk below knows; the chain's first point stands
      -- in its slot.
      if op matches .cycle then
        pts := pts.push (pts[0]?.getD (.point 0 0))
        ops := ops.push (op, mid)
      else
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
      width := width
      dash := dash }
  let mut segs : Array Ir.Pic.PathSeg := #[]
  let mut tip : Option Ir.Pic.Tip := none
  let mut labels : Array Ir.Pic.Shape := #[]
  -- A rectangle's outline: a closed frame, which both backends stroke as
  -- one path with every corner joined.
  let mut frames : Array Ir.Pic.Shape := #[]
  -- Where the current subpath began (its index in `segs` and its first
  -- point) and where it stands now: what `cycle` closes back to.
  let mut subStart : Option (Nat × Sp × Sp) := none
  let mut cur : Option (Sp × Sp) := none
  for k in [0:ops.size] do
    match pts[k]?, pts[k+1]?, ops[k]? with
    | some a, some c, some (op, mid) =>
      let last := k + 1 == ops.size
      match op with
      | .rect =>
        let (x1, y1) := a.center
        let (x2, y2) := c.center
        if strokes then
          frames := frames.push (.frame (min x1 x2) (min y1 y2) (max x1 x2 - min x1 x2)
            (max y1 y2 - min y1 y2) (some stroke) none)
        -- A node on a rectangle stands on its diagonal, as on a straight side.
        if let some label := mid then
          labels := labels ++ label.place cx width
            ((x1 + x2) / 2, (y1 + y2) / 2) (x2 - x1, y2 - y1)
        subStart := none
        cur := some (x2, y2)
      | .cycle =>
        match subStart, cur with
        | some (f, sx, sy), some (ex, ey) =>
          -- The closing side, then the first side split at its midpoint when
          -- it is straight, so the subpath runs from that midpoint round to
          -- it: every corner is interior and the PDF joins it, where a path
          -- that ended on its first corner would cap it twice.
          segs := segs.push (.line ex ey sx sy)
          if let some (.line _ _ x2 y2) := segs[f]? then
            let mx := (sx + x2) / 2
            let my := (sy + y2) / 2
            segs := (segs.set! f (.line mx my x2 y2)).push (.line sx sy mx my)
          if let some label := mid then
            labels := labels ++ label.place cx width
              ((ex + sx) / 2, (ey + sy) / 2) (sx - ex, sy - ey)
          subStart := none
          cur := some (sx, sy)
        | _, _ => pure ()
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
        -- A side that does not start where the last ended opens a subpath,
        -- as pgf moves to a node's border toward the next point.
        if subStart.isNone || cur != some p1 then subStart := some (segs.size - 1, p1.1, p1.2)
        cur := some p2
        if let some label := mid then
          labels := labels ++ label.place cx width
            ((p1.1 + p2.1) / 2, (p1.2 + p2.2) / 2) (p2.1 - p1.1, p2.2 - p1.2)
      | .curve spec =>
        -- Absolute tangents anchor each end on its border along its own
        -- angle and aim the controls along those angles. Relative ones
        -- (lines 246–358) turn the other centre about this one to find
        -- the border, then aim the controls in the frame of the chord
        -- between the two borders.
        let (p1, p2) :=
          if spec.rel then
            (a.toward (turnAbout a.center c.center spec.outA),
             c.toward (turnAbout c.center a.center (180 + spec.inA)))
          else (a.towardDir spec.outA, c.towardDir spec.inA)
        let ddx := p2.1 - p1.1
        let ddy := p2.2 - p1.2
        let (c1, c2) :=
          if spec.rel then
            (turnedControl p1.1 p1.2 ddx ddy spec.outA spec.outL,
             turnedControl p2.1 p2.2 ddx ddy spec.inA spec.inL)
          else
            -- control distance 0.3915·‖d‖·looseness: the To-Path library's factor
            let len := isqrt (ddx * ddx + ddy * ddy)
            (curveControl p1.1 p1.2 (len * 3915 * spec.outL / 10000000) spec.outA,
             curveControl p2.1 p2.2 (len * 3915 * spec.inL / 10000000) spec.inA)
        segs := segs.push (.cubic p1.1 p1.2 c1.1 c1.2 c2.1 c2.2 p2.1 p2.2)
        if subStart.isNone || cur != some p1 then subStart := some (segs.size - 1, p1.1, p1.2)
        cur := some p2
        if last && arrow then
          -- the tip rides the arrival tangent; the curve keeps its
          -- endpoint and the filled tip covers its last reach
          tip := (tipAt p2.1 p2.2 (p2.1 - c2.1) (p2.2 - c2.2) stroke.width).map (·.1)
        if let some label := mid then
          -- B(½) and its local tangent B′(½), with the common positive
          -- factor 3/4 omitted: the chord can point to a different side.
          labels := labels ++ label.place cx width
            ((p1.1 + 3 * c1.1 + 3 * c2.1 + p2.1) / 8,
             (p1.2 + 3 * c1.2 + 3 * c2.2 + p2.2) / 8)
            (-p1.1 - c1.1 + c2.1 + p2.1, -p1.2 - c1.2 + c2.2 + p2.2)
    | _, _, _ => pure ()
  -- A `\path` whose operations never asked to draw paints nothing of its
  -- own; its in-path labels still stand, as pgf sets them. A chain of
  -- nothing but rectangles strokes no edge of its own.
  let withEdge := if strokes && !segs.isEmpty then (ev.shapes ++ frames).push (.edge segs stroke tip)
    else ev.shapes ++ frames
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

/-- An `\ifnum` test split into its two sides and its relation, at paren
depth zero. TeX's ⟨relation⟩ is one of `<`, `=`, `>` (TeXbook chapter 20),
and the first one at depth zero is it — a pgfmath expression holds no
relation of its own, so there is nothing to disambiguate. -/
private def splitRel (toks : Array Tok) : Option (Array Tok × Char × Array Tok) := Id.run do
  let mut depth := 0
  for k in [0:toks.size] do
    if let some t := toks[k]? then
      match t with
      | .sym '(' => depth := depth + 1
      | .sym ')' => depth := depth - 1
      | .sym c =>
        if depth == 0 && (c == '<' || c == '>' || c == '=') then
          return some (toks.extract 0 k, c, toks.extract (k + 1) toks.size)
      | _ => pure ()
  return none

/-- Which branch a test takes, given both sides evaluated: TeX's three
integer relations and nothing else. -/
public def relHolds (rel : Char) (a b : Int) : Bool :=
  if rel == '<' then a < b else if rel == '>' then a > b else a == b

/-- **A test takes exactly one branch, and the three relations are the
trichotomy.** Exactly one of `<`, `=`, `>` holds of any two integers, so a
conditional can never ship both sides' ink and can never ship neither — a
picture's ink is a function of the test's value alone. The defect this
states away is the recovery it replaced: an `\ifnum` was named and skipped
to the next `;`, so every statement of *both* branches after the first was
drawn, which is wrong ink rather than missing ink. The registered `_exact`
shape. -/
public theorem relTrichotomy_exact (a b : Int) :
    (relHolds '<' a b = true) = !(relHolds '>' a b || relHolds '=' a b) ∧
    (relHolds '>' a b = true) = !(relHolds '<' a b || relHolds '=' a b) ∧
    (relHolds '=' a b = true) = !(relHolds '<' a b || relHolds '>' a b) := by
  simp only [relHolds]
  refine ⟨?_, ?_, ?_⟩ <;> (by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp_all <;> omega)

/-- Which branch a conditional whose test this walk cannot compute ships:
the one that draws, preferring the first where both do. A reader shown one
coherent reading of a diagram has lost almost nothing, and a reader shown an
empty box has lost the diagram — the recorded ordering the math and
node-label floors already follow ("native first; imperfectly-but-visibly
beats not at all"). Drawing *neither* is the worse recovery twice over: the
picture ships no ink at all, and an all-refused picture is what routes whole
to the external boundary, where an empty page is the one degradation that
tells a reader nothing.

Preferring the drawing branch rather than always the first is what the
reference corpus taught: a guard is as often written
`\ifdefined\x \else <content> \fi` — the interesting side in the `\else`
— as the other way round, and always taking `then` cost that diagram a
whole overlay step, measured as a page that stopped existing.

The recovery this replaced drew statement-for-statement from *both*
branches, which is not a reading of the diagram at all. So the floor is one
branch, and the assumption is named where the test was written. -/
public def condFloorTakesThen (thenS : List Stmt) : Bool := !thenS.isEmpty

/-- The branch the floor ships, as a value the statements below range over.
The evaluator reads `condFloorTakesThen` at its branch point, so this is the
same decision applied and not a second description of it. -/
public def condFloor (thenS elseS : List Stmt) : List Stmt :=
  if condFloorTakesThen thenS then thenS else elseS

/-- **An unreadable test still ships a branch.** The registered `_accounts`
shape and a sibling of `labelFloor_accounts`: where either branch holds a
statement, the floor ships statements — so a conditional the walk could not
compute never silently empties a picture. Both branches empty is the one
case that ships nothing, and then there was nothing to ship. -/
public theorem condFloor_accounts (thenS elseS : List Stmt)
    (h : ¬ (thenS.isEmpty ∧ elseS.isEmpty)) : (condFloor thenS elseS) ≠ [] := by
  simp only [condFloor, condFloorTakesThen, List.isEmpty_iff, not_and] at *
  cases thenS with
  | nil => exact h rfl
  | cons a as => simp

/-- The floor is one of the two branches, never a mixture: the shape of the
defect it replaced, which shipped statements from both. -/
public theorem condFloor_mem (thenS elseS : List Stmt) :
    condFloor thenS elseS = thenS ∨ condFloor thenS elseS = elseS := by
  simp only [condFloor]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Which branch a decided test draws, in words. -/
private def condDrawnWords (holds : Bool) : String :=
  if holds then "the branch before '\\else' is drawn" else "only the '\\else' branch is drawn"

mutual

/-- Evaluate statements in order, threading the macro environment: a
`\pgfmathsetmacro` binds for the statements after it in its own scope. -/
private def evalList (cx : Cx) : List Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | [], env, ev => (env, ev)
  | s :: rest, env, ev =>
    let (env2, ev2) := evalOne cx s env ev
    evalList cx rest env2 ev2

private def evalOne (cx : Cx) : Stmt → List (String × Val) → Ev →
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
  | .path toks, env, ev => (env, evalDraw cx env toks ev (isPath := true))
  | .bbox toks, env, ev =>
    match evalBBox cx env toks with
    | .ok b =>
      -- pgf never shrinks a box already established (§15.8): what the
      -- marks before the declaration reached stays inside it, and a
      -- second declaration joins the first.
      let before := ev.shapes.map (Ir.Pic.Shape.inkBox cx.metric) ++ ev.borders
      let b := if before.isEmpty then b else Ir.Pic.Box.join (Ir.Pic.Box.hull before) b
      let b := match ev.declared with
        | some d => Ir.Pic.Box.join d b
        | none => b
      (env, { ev with declared := some b })
    | .error d => (env, ev.diag d)
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
  -- A conditional: one branch runs, the other is not evaluated at all — so
  -- a node it declared never registers, which is a *named* gap and not a
  -- name the document forgot (`Ev.gapped`). Only the arithmetic tests are
  -- computable here; every other one is a fact about TeX's own state or its
  -- control-sequence table, so its answer is not known and the floor stands
  -- instead (`condFloor`): one coherent reading of the diagram,
  -- named where the test was written.
  | .cond kind test thenS elseS, env, ev =>
    match kind with
    | .always v =>
      let ev := ev.diag (.N0114, s!"'\\{if v then "iftrue" else "iffalse"}' is \
{if v then "true" else "false"} by definition, so {condDrawnWords v}")
      if v then
        let (_, ev2) := evalList cx thenS env ev
        (env, ev2)
      else
        let (_, ev2) := evalList cx elseS env ev
        (env, ev2)
    | .mode n v =>
      let ev := ev.diag (.N0114, s!"'\\{n}' {if v then "holds" else "fails"} at a picture's \
statements, which pgf sets in a horizontal box, so {condDrawnWords v}")
      if v then
        let (_, ev2) := evalList cx thenS env ev
        (env, ev2)
      else
        let (_, ev2) := evalList cx elseS env ev
        (env, ev2)
    | .opaque n =>
      let ev := { ev with gapped := true }.diag
        (.W0334, s!"'\\{n}' is outside the rendered picture subset; the branch \
that draws is drawn")
      if condFloorTakesThen thenS then
        let (_, ev2) := evalList cx thenS env ev
        (env, ev2)
      else
        let (_, ev2) := evalList cx elseS env ev
        (env, ev2)
    | .num n =>
      match splitRel (test.filter (· != .space)) with
      | none =>
        let ev := { ev with gapped := true }.diag
          (.W0334, s!"an '\\{n}' without a '<', '=' or '>' test is outside the \
rendered picture subset; the branch that draws is drawn")
        if condFloorTakesThen thenS then
          let (_, ev2) := evalList cx thenS env ev
          (env, ev2)
        else
          let (_, ev2) := evalList cx elseS env ev
          (env, ev2)
      | some (lhs, rel, rhs) =>
        match evalNum env lhs, evalNum env rhs with
        | .ok a, .ok b =>
          let holds := relHolds rel a b
          -- Computed, not assumed: named all the same, so a reader can see
          -- which values the picture's own walk decided a branch from.
          let ev := ev.diag (.N0114, s!"'\\{n}' is computed from the picture's own values \
and {if holds then "holds" else "fails"} here, so {condDrawnWords holds}")
          if holds then
            let (_, ev2) := evalList cx thenS env ev
            (env, ev2)
          else
            let (_, ev2) := evalList cx elseS env ev
            (env, ev2)
        | .error e, _ | _, .error e =>
          let ev := { ev with gapped := true }.diag
            (.W0334, s!"in an '\\{n}' test, {e}; the branch that draws is drawn")
          if condFloorTakesThen thenS then
            let (_, ev2) := evalList cx thenS env ev
            (env, ev2)
          else
            let (_, ev2) := evalList cx elseS env ev
            (env, ev2)

/-- One body evaluation per item: the recursion is on the item list, the
body a fixed subterm of its `\foreach`, so the unrolling is bounded by the
expanded list — which `range` bounded before any value existed. -/
private def evalForeach (cx : Cx) (vars : Array String) (body : List Stmt) :
    List (Array Val) → List (String × Val) → Ev → Ev
  | [], _, ev => ev
  | item :: rest, env, ev =>
    let (_, ev2) := evalList cx body (bindVars vars item env) ev
    evalForeach cx vars body rest env ev2

end

/-- The node table with each name once, the latest registration kept: what
a re-run is seeded with, so the table cannot grow without bound across the
runs `evalFixed` makes. -/
private def dedupNodes (ns : List (String × NodeGeom)) :
    List (String × NodeGeom) := Id.run do
  let mut seen : Array String := #[]
  let mut out : Array (String × NodeGeom) := #[]
  for (n, g) in ns do
    unless seen.contains n do
      seen := seen.push n
      out := out.push (n, g)
  return out.toList

/-- Retry unresolved references using the previous pass's node table.

The walk stops when all references resolve or their unresolved count
ceases to fall. The first pass's count bounds the number of retries.
This permits forward references without claiming that arbitrary source
permutations agree: repeated names and macro assignments are ordered
writes. `NodePlan.place_order_agree` gives the local commutation contract
for resolved operations whose reads and writes are independent.

The common case costs one run. A picture whose placements all read
backwards — every picture written the way TikZ demands — defers nothing and
returns immediately, so no existing document pays for this. -/
public def evalFixed (cx : Cx) (sts : List Stmt) : Ev := Id.run do
  let (_, ev0) := evalList cx sts [] {}
  if ev0.deferred == 0 then return ev0
  let mut prev := ev0
  for _ in [0:ev0.deferred] do
    let (_, ev) := evalList cx sts [] { nodes := dedupNodes prev.nodes }
    if ev.deferred == 0 || ev.deferred ≥ prev.deferred then return ev
    prev := ev
  return prev

/-- Every label resolved from the source fits the picture's reserved
extent under the resolving context's metric. Explicit bounding boxes are
authoritative; node borders need not enclose text when the author changes
text dimensions or uses negative padding. The shared IR hull, projected
through the actual producer, covers all alignments, sizes and placements. -/
public theorem nodeExtent_covers (cx : Cx) (sts : List Stmt)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (baseline : Option Sp)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ (evalFixed cx sts).shapes)
    (hd : (evalFixed cx sts).declared = none) :
    Ir.Pic.Box.le (Ir.Pic.labelTextBox x y align (cx.metric content scale))
      (((evalFixed cx sts).toPicture baseline).box cx.metric) :=
  Ev.labelExtent_covers _ _ _ _ _ _ _ _ _ hs hd

/-- A document macro as the picture walk uses it: how many arguments it
takes, and its body's tokens. -/
private structure Macro where
  arity : Nat
  body : List Tok
  deriving Repr, Inhabited

/-- The control words this walk owns, so a document that redefined one does
not redefine the picture language out from under itself. `\node`, `\draw`
and their siblings are the statement heads `step` reads; `\else`/`\fi` close
a conditional and `condKindOf` opens one. A macro of such a name is left to
the walk and named where it stands, which is the honest answer: expanding
it would silently delete the construct, and honouring the redefinition
would need a picture language this walk does not have. Read off the one
place the vocabulary lives (`step`), so the two cannot drift. -/
public def walkCtrls : List String :=
  ["fill", "node", "draw", "path", "foreach", "pgfmathsetmacro",
   "pgfmathtruncatemacro", "else", "fi"]

/-- Does this walk give the name a meaning of its own? -/
private def walkOwns (n : String) : Bool := walkCtrls.contains n || (condKindOf n).isSome

/-- The names a picture binds for itself: a `\foreach` variable and a
`\pgfmathsetmacro` target. pgf binds them in the picture's own scope, so
they are the picture's whatever the document also called them — which is
why they are cut from the macro table before a single expansion happens.
A scan over the token stream rather than over the parsed statements,
because the binding has to be known before the stream is rewritten. -/
private def boundNames (ts : Array Tok) : List String := Id.run do
  let mut out : List String := []
  let mut inVars := false
  for k in [0:ts.size] do
    match ts[k]? with
    | some (.ctrl "foreach") => inVars := true
    | some (.ctrl "pgfmathsetmacro") | some (.ctrl "pgfmathtruncatemacro") =>
      match ts[k+1]?, ts[k+2]? with
      | some (.group [.ctrl n]), _ => out := n :: out
      | some .space, some (.group [.ctrl n]) => out := n :: out
      | _, _ => pure ()
    | some (.ctrl v) => if inVars then out := v :: out
    | some (.ident "in") => inVars := false
    | _ => pure ()
  return out

mutual

/-- `#k` replaced by the k-th argument, through the body's own tree. An
accumulator rather than an append of the recursive call, so the walk costs
one copy and not one per token. -/
private def substList (args : Array (List Tok)) (acc : Array Tok) :
    List Tok → Array Tok
  | [] => acc
  | .sym '#' :: .num m :: rest =>
    substList args (((args[(m / 1000 - 1).toNat]?).getD []).foldl Array.push acc) rest
  | t :: rest => substList args (acc.push (substTok args t)) rest

private def substTok (args : Array (List Tok)) : Tok → Tok
  | .group g => .group (substList args #[] g).toList
  | .ctrl n => .ctrl n
  | .ident s => .ident s
  | .num m => .num m
  | .sym c => .sym c
  | .space => .space
  | .math d b => .math d b
  | .other w => .other w

end

/-- Does `n` open an arithmetic conditional, whose test the walk computes? -/
private def numCondHead (n : String) : Bool :=
  (condKindOf n) matches some (.num _)

/-- How many tokens after an arithmetic conditional's head its test takes,
as the walk's own reader closes it (`step`'s `icond` arm): through the
right side of a relation, up to the space that ends it, or none at all when
an `\else` or `\fi` comes first. `sawRel`: a relation has been read; `last`:
the latest token the test holds. -/
private def numTestLen : List Tok → Nat → Bool → Option Tok → Nat
  | [], n, _, _ => n
  | .space :: rest, n, sawRel, last =>
    let ready := sawRel && (match last with
      | some (.sym c) => c != '<' && c != '>' && c != '='
      | some _ => true
      | none => false)
    if ready then n else numTestLen rest (n + 1) sawRel last
  | .ctrl "else" :: _, n, _, _ => n
  | .ctrl "fi" :: _, n, _, _ => n
  | t :: rest, n, sawRel, _ =>
    let rel := match t with
      | .sym c => c == '<' || c == '>' || c == '='
      | _ => false
    numTestLen rest (n + 1) (sawRel || rel) (some t)

mutual

/-- One expansion level over the whole stream: every name in the table
replaced by its body with its arguments substituted, and the bodies' own
groups walked so a macro inside a group expands too.

**Arity 0, 1 and 2, and a name is otherwise left standing.** The bound is
not a taste: each arm's recursive call has to be on a strictly shorter list
for the walk to terminate by a measure the checker can see, and consuming a
*computed* number of argument groups is exactly the shape whose measure it
cannot. Three arities cover the picture idiom (a bare alias, a one-word
wrapper, a two-word one); a wider macro is left in place, so `salCtrl`
names it and the label keeps the words it can read — a named loss rather
than a body substituted against the wrong arguments. -/
private def expandList (tbl : List (String × Macro)) (acc : Array Tok) :
    List Tok → Nat → Array Tok
  | [], _ => acc
  -- The test of an arithmetic conditional is read as written: a document
  -- macro there is not expanded from this table, which says what a name
  -- means somewhere in the document and not where the picture stands. The
  -- conditional pass decided every test it could read at the picture's
  -- site before this walk ran, so what is left here is a test over the
  -- picture's own values, or one the walk names and floors.
  | t :: rest, skip + 1 => expandList tbl (acc.push t) rest skip
  -- A space between a name and its argument is the name's, as TeX reads it.
  | .ctrl n :: .space :: rest, 0 =>
    if numCondHead n then
      expandList tbl (acc.push (.ctrl n)) (.space :: rest) (numTestLen (.space :: rest) 0 false none)
    else expandList tbl acc (.ctrl n :: rest) 0
  | .ctrl n :: .group a :: .group b :: rest, 0 =>
    if numCondHead n then
      expandList tbl (acc.push (.ctrl n)) (.group a :: .group b :: rest)
        (numTestLen (.group a :: .group b :: rest) 0 false none)
    else
    match tbl.lookup n with
    | some m =>
      if m.arity == 2 then
        expandList tbl ((substList #[a, b] #[] m.body).foldl Array.push acc) rest 0
      else if m.arity == 1 then
        expandList tbl ((substList #[a] #[] m.body).foldl Array.push acc)
          (.group b :: rest) 0
      else if m.arity == 0 then
        expandList tbl (m.body.foldl Array.push acc) (.group a :: .group b :: rest) 0
      else expandList tbl (acc.push (.ctrl n)) (.group a :: .group b :: rest) 0
    | none => expandList tbl (acc.push (.ctrl n)) (.group a :: .group b :: rest) 0
  | .ctrl n :: .group a :: rest, 0 =>
    if numCondHead n then
      expandList tbl (acc.push (.ctrl n)) (.group a :: rest)
        (numTestLen (.group a :: rest) 0 false none)
    else
    match tbl.lookup n with
    | some m =>
      if m.arity == 1 then
        expandList tbl ((substList #[a] #[] m.body).foldl Array.push acc) rest 0
      else if m.arity == 0 then
        expandList tbl (m.body.foldl Array.push acc) (.group a :: rest) 0
      else expandList tbl (acc.push (.ctrl n)) (.group a :: rest) 0
    | none => expandList tbl (acc.push (.ctrl n)) (.group a :: rest) 0
  | .ctrl n :: rest, 0 =>
    if numCondHead n then
      expandList tbl (acc.push (.ctrl n)) rest (numTestLen rest 0 false none)
    else
    match tbl.lookup n with
    | some m =>
      if m.arity == 0 then expandList tbl (m.body.foldl Array.push acc) rest 0
      else expandList tbl (acc.push (.ctrl n)) rest 0
    | none => expandList tbl (acc.push (.ctrl n)) rest 0
  | t :: rest, 0 => expandList tbl (acc.push (expandTok tbl t)) rest 0

private def expandTok (tbl : List (String × Macro)) : Tok → Tok
  | .group g => .group (expandList tbl #[] g 0).toList
  | .ctrl n => .ctrl n
  | .ident s => .ident s
  | .num m => .num m
  | .sym c => .sym c
  | .space => .space
  | .math d b => .math d b
  | .other w => .other w

end

/-- **A document's macros reach its picture before the walk reads it.**
Expansion precedes execution, as it does in TeX: the stream the statement
reader and the label salvage see is one a macro has already been taken out
of, so a macro works in a node body, an edge label, a coordinate and a
conditional's test alike, and neither the mode machine nor the salvage has
to learn a table. The salvage's `nodeLabel_mem` now reads an independent
census of that expanded source and proves provenance through the actual
mode machine. Keeping macro expansion outside it leaves the shrinking
declaration table with the token rewrite that consumes it.

**The bound is the table, not a budget.** One pass resolves one level of
nesting, so a chain of distinct names is exhausted in as many passes as the
table has entries; the loop stops earlier the moment a pass changes
nothing. A cycle therefore leaves its name standing and is *named* by the
salvage rather than hanging the run — which is what a fuel parameter would
have bought, at the cost of a number nobody can justify. -/
private def expandMacros (tbl : List (String × Macro)) (ts : Array Tok) : Array Tok :=
  Id.run do
  if tbl.isEmpty then return ts
  let mut out := ts
  for _ in [0:tbl.length] do
    let next := expandList tbl #[] out.toList 0
    if next == out then break
    out := next
  return out

mutual

/-- The highest `#k` a body references, through the body's own tree, which
is the macro's arity when the definer's spelling does not carry one
(TeXbook chapter 20: a macro's parameters are `#1`–`#9` and its body is
what references them). A tree walk and not a flat scan: `\textcolor{role}
{#1}` keeps its parameter one group in, which is where a wrapper macro
always puts it. -/
private def refArityList (acc : Nat) (prevHash : Bool) : List Tok → Nat
  | [] => acc
  | .sym '#' :: rest => refArityList acc true rest
  | .num m :: rest =>
    refArityList (if prevHash then max acc (m / 1000).toNat else acc) false rest
  | t :: rest => refArityList (max acc (refArityTok t)) false rest

private def refArityTok : Tok → Nat
  | .group g => refArityList 0 false g
  | .ctrl _ => 0
  | .ident _ => 0
  | .num _ => 0
  | .sym _ => 0
  | .space => 0
  | .math _ _ => 0
  | .other _ => 0

end

/-- The arity a body's own parameter references imply. -/
private def refArity (body : List Tok) : Nat := refArityList 0 false body

/-- One document macro, read from its definition as the document wrote it.

The four definer families share one shape — a head, the name, the
arity or parameter text, then the body as the *last* group
(`\newcommand{\c}[n][d]{defn}` and its siblings, clsguide;
`\DeclareDocumentCommand{\c}{spec}{defn}`, xparse; `\def\c<param>{defn}`,
TeXbook chapter 20; the native `\define`) — so the body is read by that
shape rather than by recognising which family wrote it. The arity is the
first all-digit `[k]` run before the body where the spelling carries one,
and otherwise the body's own highest `#k`: a family that states its arity
is believed, and one that does not is read the way TeX reads it. The cost
is a macro whose declared parameter its body never uses, which reads as
arity zero and leaves its argument standing as content — a visible wrong,
not a silent one.

Read with the real lexer and parser because the body is a *tree* — braces,
control words, math — and the definition arrives as the source text of one.
The engine's own re-emission is source the document could have written, so
this is a LaTeX reader and not a reader of a private spelling. -/
private def readMacro (line : String) : Option Macro := Id.run do
  let (toks, _) := Lex.lex "" line
  let (raws, _) := Parse.parse "" toks
  let mut bodyAt : Option Nat := none
  for k in [0:raws.size] do
    if raws[k]? matches some (.group _ _) then bodyAt := some k
  let some bi := bodyAt | return none
  let some (.group body _) := raws[bi]? | return none
  let bodyToks := (ofRaws body).toList
  -- The declared arity: the first `[k]` run standing before the body.
  let mut declared : Option Nat := none
  for k in [0:bi] do
    match raws[k]?, raws[k+1]?, raws[k+2]? with
    | some (.sym '[' _), some (.word d _), some (.sym ']' _) =>
      if declared.isNone && !d.isEmpty && d.toList.all Char.isDigit then
        declared := d.toNat?
    | _, _, _ => pure ()
  return some { arity := declared.getD (refArity bodyToks), body := bodyToks }

/-- The macro table one picture reads: the document's definitions, less
every name the walk owns and every name the picture binds for itself, and
less any whose definition this reader cannot read. `names` is the document's
reachable set as the elaborator collected it (`Elab.PicCtx.macros`), one
entry per name, in document order.

A font switch is the font reader's (`readFont`), as it is the elaborator's:
a size name means its step of the document's ladder, which is where the
elaborator reads a venue's `\@setfontsize` redefinition out, so expanding
the redefinition here would set a picture's `font=\small` by a body the
paragraphs never run. -/
private def macroTable (ladder : List (String × Nat)) (declStyles : List (String × Ir.Style))
    (names : Array (String × String)) (ts : Array Tok) :
    List (String × Macro) := Id.run do
  let bound := boundNames ts
  let mut out : List (String × Macro) := []
  for (n, line) in names do
    unless walkOwns n || bound.contains n || (ladder.lookup n).isSome ||
        (declStyles.lookup n).isSome do
      if let some m := readMacro line then out := (n, m) :: out
  return out

/-- `baseline=` (pgf manual §12.2.1) as a height in picture coordinates:
the bare key is 0pt, a length is itself, and a coordinate is its y —
`(x,y)` through the picture's scale, or a node's anchor such as `(n.base)`,
where the picture's own reading put it. Braces around the value are TeX's
grouping. -/
private def readBaseline (cx : Cx) (nodes : List (String × NodeGeom)) (toks : List Tok) :
    Except String Sp :=
  let toks := if let [.group body] := toks then body.filter (· != Tok.space) else toks
  match toks with
  | [] => .ok 0
  | .sym '(' :: rest =>
    match rest.reverse with
    | .sym ')' :: inner =>
      let inner := inner.reverse.toArray
      match (splitTop inner ',').toList with
      | [_, ys] => (evalNum [] ys).map cx.toSp
      | _ =>
        let nm := String.join (inner.toList.map fun (t : Tok) => match t with
          | .ident s => s
          | .num m => milliString m
          | .sym c => String.singleton c
          | _ => "")
        match nodes.lookup nm, splitAnchor nm with
        | some g, _ => .ok g.y
        | none, some (base, an) =>
          match nodes.lookup base, nodeAnchorOf an with
          | some g, some a => .ok (g.anchorPoint a).2
          | none, _ => .error s!"no node is named '{base}'"
          | some _, none => .error s!"node anchor '{an}' is outside the rendered picture subset"
        | none, none => .error s!"no node is named '{nm}'"
    | _ => .error "the coordinate misses its ')'"
  | ts => readDim ts

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
line that declared it. `argStyles` is the elaborator's text-command table
(`Cx.argStyles`), and it has no default on purpose: a caller that forgot
it would set every styled node label in the regular face, the defect the
parameter exists to close. `ladder` and `declStyles` are the document's
size ladder and the elaborator's declaration table, without defaults for
the same reason: a forgotten ladder sets a venue's `\small` at the engine's
step. `bodySize` is likewise required: label leading and relative lengths
must read the same document size as their artifact measurement. -/
public def elabPicture (pal : Ir.Palette) (raws : Array Parse.Raw)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag :=
      fun d rs => (.math d (Parse.rawSrc rs), #[]))
    (sets : Array (Array Parse.Raw) := #[])
    (metric : Ir.Pic.LabelMetric := fun _ _ => {})
    (macros : Array (String × String) := #[])
    (argStyles : List (String × Ir.Style))
    (ladder : List (String × Nat))
    (declStyles : List (String × Ir.Style)) (bodySize : Sp) :
    Ir.Pic.Picture × Array PDiag := Id.run do
  let raw := ofRaws raws
  let toks := expandMacros (macroTable ladder declStyles macros raw) raw
  let mut scale : Int := 1000
  let mut styles := documentStyles (sets.map fun keys => ofRaws keys)
  -- `node distance` is a key, not a definition: the document's `\tikzset`
  -- lines set it in source order, and the picture's own bracket may reset
  -- it below.
  let mut dist : Sp × Sp := (Dim.mm 10, Dim.mm 10)
  for keys in sets do
    for entry in splitTop (ofRaws keys) ',' do
      if let some d := readNodeDistance (entry.toList.filter (· != .space)) then
        dist := d
  let mut transformShape := false
  let mut inherited : Array (Array Tok) := #[]
  let mut diags : Array PDiag := #[]
  -- `baseline=`'s value, read once the nodes it may name are placed.
  let mut baselineSpec : Option (List Tok) := none
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
        | [.ident "baseline"] => baselineSpec := some []
        | .ident "baseline" :: .sym '=' :: rest => baselineSpec := some rest
        | .ident "node" :: .ident "distance" :: rest =>
          match readNodeDistance (.ident "node" :: .ident "distance" :: rest) with
          | some d => dist := d
          | none =>
            diags := diags.push (.E0333, "in 'node distance', a length like \
'1cm' (or '1cm and 2cm') is needed; it is ignored")
        -- A bare name that resolves is a style applied to the picture
        -- itself: pgf sets it in the picture's scope, so its options are
        -- what the contents inherit (`Cx.opts`, merged by `mergeOpts`).
        -- A name that resolves to no bundle, and any other entry, is a key:
        -- carried to the statements that read it, and named here where no
        -- shape does — the same rule the document's own lines follow, so
        -- one entry means one thing wherever it was written.
        | [.ident n] =>
          match styles.lookup n with
          | some bundle => inherited := inherited ++ splitTop bundle ','
          | none =>
            if readsOpt styles #[.ident n] then inherited := inherited.push #[.ident n]
            else diags := diags.push (outsideOpt [.ident n])
        | [] => pure ()
        | o :: rest =>
          if readsOpt styles (o :: rest).toArray then
            inherited := inherited.push (o :: rest).toArray
          else diags := diags.push (outsideOpt (o :: rest))
    else
      diags := diags.push (.E0333, "the picture's options miss their ']'")
  let st := (parseList (toks.toList.drop i) {}).drain
  let everyOf (n : String) : Array (Array Tok) :=
    match styles.lookup n with
    | some bundle => (splitTop bundle ',').filter fun e => !e.isEmpty
    | none => #[]
  let cx : Cx := { pal := pal, scale := scale
                   styles := styles, transformShape := transformShape
                   global := documentOpts (sets.map fun keys => ofRaws keys)
                   opts := inherited
                   everyNode := everyOf everyNodeKey
                   everyPath := everyOf everyPathKey
                   everyText := everyOf everyTextKey
                   dist := dist
                   math := math
                   argStyles := argStyles
                   ladder := ladder
                   declStyles := declStyles
                   metric := metric
                   bodySize := bodySize
                   -- A declaration the parse skipped is gone before
                   -- evaluation begins, so a name that then resolves to
                   -- nothing traces to that gap (`unreachedName`).
                   parseGap := st.bad.any fun d => d.1 == .W0334 }
  let ev := evalFixed cx st.out.toList
  -- What the inherited entries cost, named at the picture rather than at a
  -- statement, because neither is where they were written. An entry no
  -- shape reads is honoured by nobody, whatever the picture contains; one
  -- some shape reads is lost only where no statement read keys at all (a
  -- picture of nothing but `\fill`, whose bracket is a colour spelling).
  -- Either way the standing rule holds: a key the subset does not use is
  -- never silently dropped.
  let mut unread : Array PDiag := #[]
  let mut baseline : Option Sp := none
  if let some spec := baselineSpec then
    match readBaseline cx ev.nodes spec with
    | .ok y => baseline := some y
    | .error e =>
      unread := unread.push (.E0333, s!"in 'baseline=', {e}; the picture's bottom \
edge stands on the line")
  for opt in inherited do
    match opt.toList with
    | [] => pure ()
    | o :: _ =>
      if !readsOpt styles opt then unread := unread.push (outsideOpt opt.toList)
      else unless ev.readOpts do
        unread := unread.push (.W0334, s!"picture option {optName opt.toList} reached no path \
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
  return (ev.toPicture baseline, out)

/-- The stand-in for a picture whose every construct was refused: one
outlined box carrying the diagnostic code, following the image precedent
(an image that did not load renders as an outlined placeholder of its
requested size; W0601). The size is the image default — 1 in square —
because no honest extent is known, and the outline colour is the image
placeholder's own grey, so the two failure modes read alike. -/
public def placeholder (code : String) : Ir.Pic.Picture :=
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
