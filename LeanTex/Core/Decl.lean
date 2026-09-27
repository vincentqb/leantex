import LeanTex.Core.Diag
import LeanTex.Core.Dim

namespace LeanTex.Core.Decl

open LeanTex.Core LeanTex.Core.Dim

/-- A declaration value. Absolute dimensions resolve here; font-relative
units (ex, em) are not accepted yet — they need the symbolic lengths that
arrive with `\tokens`. -/
inductive Value where
  | str (s : String)
  | dim (sp : Sp)
  | int (n : Int)
  | ident (s : String)
  | block (src : String)
  | color (r g b : UInt8)
  /-- A colour declared in CMYK, components in thousandths: the declared
  model matters to print, so it survives parsing intact. -/
  | cmyk (c m y k : Nat)
  /-- A glue expression, possibly font-relative or scaled from a token. -/
  | glue (g : SymGlue)
  deriving Repr, BEq

def Value.kindName : Value → String
  | .str _ => "string"
  | .dim _ => "dimension"
  | .int _ => "number"
  | .ident _ => "name"
  | .block _ => "block"
  | .color _ _ _ => "color"
  | .cmyk _ _ _ _ => "color"
  | .glue _ => "length"

structure Entry where
  key : String
  value : Value
  deriving Repr, BEq

private def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `#RGB` or `#RRGGBB`. -/
private def parseColor (s : String) : Option Value := do
  let cs := s.toList
  match cs with
  | '#' :: rest =>
    let digits ← rest.mapM hexDigit?
    match digits with
    | [r, g, b] =>
      -- #abc means #aabbcc, as in CSS
      some (.color (UInt8.ofNat (r * 17)) (UInt8.ofNat (g * 17)) (UInt8.ofNat (b * 17)))
    | [r1, r2, g1, g2, b1, b2] =>
      some (.color (UInt8.ofNat (r1 * 16 + r2)) (UInt8.ofNat (g1 * 16 + g2))
        (UInt8.ofNat (b1 * 16 + b2)))
    | _ => none
  | _ => none

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

/-- Split on commas that are not inside braces, brackets, parentheses, or
quotes. Public because a declaration whose entries may refer to earlier
entries has to walk them one at a time. -/
def splitEntries (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur := ""
  let mut depth := 0
  let mut inStr := false
  for c in s.toList do
    if inStr then
      cur := cur.push c
      if c == '"' then inStr := false
    else if c == '"' then
      cur := cur.push c
      inStr := true
    else if c == '{' || c == '[' || c == '(' then
      depth := depth + 1
      cur := cur.push c
    else if c == '}' || c == ']' || c == ')' then
      depth := depth - 1
      cur := cur.push c
    else if c == ',' && depth == 0 then
      out := out ++ [cur]
      cur := ""
    else
      cur := cur.push c
  out := out ++ [cur]
  return out.filterMap fun e =>
    let t := e.trimAscii.toString
    if t.isEmpty then none else some t

/-- Decimal literal as mantissa and scale: "0.5" ↦ (5, 10). -/
def parseDecimal (s : String) : Option (Int × Nat) := Id.run do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  if cs.isEmpty then
    return none
  let mut mantissa : Nat := 0
  let mut scale : Nat := 1
  let mut seenDot := false
  let mut digits := 0
  for c in cs do
    if c == '.' then
      if seenDot then return none
      seenDot := true
    else if c.isDigit then
      mantissa := mantissa * 10 + (c.toNat - '0'.toNat)
      digits := digits + 1
      if seenDot then scale := scale * 10
    else
      return none
  if digits == 0 then
    return none
  return some (if neg then -(mantissa : Int) else mantissa, scale)

/-- sp per unit, expressed as a fraction so conversions stay exact. -/
private def unitScaleBase : String → Option (Int × Nat)
  | "sp" => some (1, 1)
  | "pt" => some (spPerPt, 1)
  | "bp" => some (spPerPt, 1)
  | "in" => some (72 * spPerPt, 1)
  | "cm" => some (7200 * spPerPt, 254)
  | "mm" => some (7200 * spPerPt, 2540)
  | "pc" => some (12 * spPerPt, 1)
  -- the CSS pixel: 1px = 1/96 in exactly (CSS Values and Units 4 §6.2),
  -- so 96 px = 72 pt — the unit a web-facing length (a scroll distance)
  -- is naturally written in
  | "px" => some (72 * spPerPt, 96)
  -- The didot point, TeX's continental unit: 1157 dd = 1238 TeX pt
  -- (TeXbook ch. 10), and 7227 TeX pt = 100 in, so
  -- dd = 1238·7200⁄(1157·7227) of this engine's 1⁄72-inch point —
  -- unreduced, so the relation to `in` is literal in the theorem below.
  | "dd" => some (8913600 * spPerPt, 8361639)
  | "cc" => some (12 * 8913600 * spPerPt, 8361639)
  | _ => none

/-- A `true` unit is its plain counterpart, exactly. TeX's `truept`,
`truein`, … mean "unscaled by magnification": "if you want an unmagnified
unit, you can say `true`" and true dimensions stay constant whatever `\mag`
is (TeXbook ch. 10). This engine has no magnification — every dimension is
already true — so the prefix denotes the identity. Reading it as part of a
unit *name* was the defect: `1.75truein` parsed as a name and E0323 said
"expects a length … got a name". A unit added to the base table gets its
`true` twin here, or `unitScale_true` below fails to extend. -/
private def unitScale : String → Option (Int × Nat)
  | "truesp" => unitScaleBase "sp"
  | "truept" => unitScaleBase "pt"
  | "truebp" => unitScaleBase "bp"
  | "truein" => unitScaleBase "in"
  | "truecm" => unitScaleBase "cm"
  | "truemm" => unitScaleBase "mm"
  | "truepc" => unitScaleBase "pc"
  | "truepx" => unitScaleBase "px"
  | "truedd" => unitScaleBase "dd"
  | "truecc" => unitScaleBase "cc"
  | u => unitScaleBase u

/-- The unit table is one system, not ten constants: bp is the PDF point
(leantex's pt), an inch is 72 of them, a pica 12, cm and mm follow from
1 in = 2.54 cm exactly, sp is the fixed point itself, the CSS pixel is
1⁄96 inch, a cicero is 12 didots, and the didot keeps TeX's own ratio to
the inch (1157 dd = 1238 TeX pt and 7227 TeX pt = 100 in, TeXbook ch. 10;
the dd fraction is stored unreduced so its relation below is literal). A
typo in any one entry breaks a relation here. -/
theorem unitScale_consistent :
    unitScale "bp" = unitScale "pt" ∧
    unitScale "pt" = (unitScale "sp").map (fun u => (spPerPt * u.1, u.2)) ∧
    unitScale "in" = (unitScale "pt").map (fun u => (72 * u.1, u.2)) ∧
    unitScale "pc" = (unitScale "pt").map (fun u => (12 * u.1, u.2)) ∧
    unitScale "cm" = (unitScale "in").map (fun u => (100 * u.1, 254 * u.2)) ∧
    unitScale "mm" = (unitScale "cm").map (fun u => (u.1, 10 * u.2)) ∧
    unitScale "px" = (unitScale "in").map (fun u => (u.1, 96 * u.2)) ∧
    unitScale "dd" = (unitScale "in").map (fun u => (123800 * u.1, 8361639 * u.2)) ∧
    unitScale "cc" = (unitScale "dd").map (fun u => (12 * u.1, u.2)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [unitScale, unitScaleBase, spPerPt]

/-- Every `true` unit denotes exactly its plain counterpart — stated over
the whole table, so a unit added without this identity breaks the build,
not a document. -/
theorem unitScale_true :
    unitScale "truesp" = unitScale "sp" ∧ unitScale "truept" = unitScale "pt" ∧
    unitScale "truebp" = unitScale "bp" ∧ unitScale "truein" = unitScale "in" ∧
    unitScale "truecm" = unitScale "cm" ∧ unitScale "truemm" = unitScale "mm" ∧
    unitScale "truepc" = unitScale "pc" ∧ unitScale "truepx" = unitScale "px" ∧
    unitScale "truedd" = unitScale "dd" ∧ unitScale "truecc" = unitScale "cc" := by
  decide

/-- One term's length from its mantissa, scale, and unit name: the shared
arithmetic under `parseLength` and the expression parser. -/
private def lengthOfUnit (mantissa : Int) (scale : Nat) (unit : String) :
    Option Length :=
  if unit == "em" then
    some { em := mantissa * 1000 / scale }
  else if unit == "ex" then
    some { ex := mantissa * 1000 / scale }
  else
    (unitScale unit).map fun (num, den) =>
      Length.ofSp (mantissa * num / (scale * den : Nat))

/-- A single length term: a number with an absolute or font-relative unit. -/
def parseLength (s : String) : Option Length :=
  let s := s.trimAscii.toString
  let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
  let unit := (String.ofList (s.toList.drop digits.length)).trimAscii.toString
  match parseDecimal (String.ofList digits) with
  | none => none
  | some (mantissa, scale) => lengthOfUnit mantissa scale unit

/-- `<len> [plus <len>] [minus <len>]`, TeX's glue spelling. -/
def parseGlue (s : String) : Option SymGlue := do
  let words := (s.trimAscii.toString.splitOn " ").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  match words with
  | [] => none
  | base :: rest =>
    let g : SymGlue := { width := ← parseLength base }
    let rec go (g : SymGlue) : List String → Option SymGlue
      | [] => some g
      | "plus" :: v :: tl => do
        let l ← parseLength v
        go { g with stretch := l } tl
      | "minus" :: v :: tl => do
        let l ← parseLength v
        go { g with shrink := l } tl
      | _ => none
    go g rest

/-- A scale factor `0.6 * name`, resolved against already-declared tokens. -/
def parseScaled (tokens : Array (String × SymGlue)) (s : String) : Option Value :=
  match s.splitOn "*" with
  | [factor, name] => do
    let (mantissa, scale) ← parseDecimal (factor.trimAscii.toString)
    let key := name.trimAscii.toString
    let (_, g) ← tokens.find? (·.1 == key)
    some (.glue (g.scale mantissa scale))
  | _ => none

/-! # Length expressions

`\dimexpr`'s shape over declared tokens and literals: terms added and
subtracted, a term scaled by a numeric factor, parentheses for grouping
(e-TeX manual, the `⟨expr⟩` grammar: "an expression consists of one or
more terms … to be added or subtracted; a term … consists of a factor …
optionally multiplied and/or divided by numeric factors; a factor … is
either a parenthesized subexpression or a quantity"). TeX's coefficient
form rides along: `2\cardbleed` is a ⟨factor⟩ before an internal dimen
(TeXbook ch. 24, ⟨dimen⟩ syntax), so `cardheight + 2 cardbleed` reads as
`cardheight + 2 * cardbleed`. Division by a numeric factor folds into the
same scaling (`a / n` is `.scale 1 n a`), and a parenthesized numeric
subexpression such as `(3+1)` evaluates as a scalar before it scales or
divides. One rounding rule for the whole language, TeX's: `\divide`
truncates toward zero (TeXbook ch. 24) and so does coefficient scaling
(`xn_over_d`, TeX §107); e-TeX's `\dimexpr` division rounds to nearest
instead (e-TeX manual §3.5) and is therefore refused by name, never
mapped onto arithmetic that would disagree with its source. Scaling by a
decimal keeps `Length.scale`'s semantics, now truncation throughout.

Token references resolve eagerly, against the values declared so far —
the same rule `\tokens` and TeX's `\setlength{\x}{2\x}` follow — so a
reference is one lookup into ground values, never a recursive walk: a
cycle is unrepresentable, and a forward or unknown name is diagnosed by
name (`eval_absent_named`), never defaulted to zero. -/

/-- A length expression over literals and declared token names. -/
inductive LenExpr where
  | lit (l : Length)
  | tok (name : String)
  | scale (num : Int) (den : Nat) (e : LenExpr)
  | add (a b : LenExpr)
  | sub (a b : LenExpr)
  deriving Repr, BEq

namespace LenExpr

/-- Whether an expression reads a token name: what its value may depend on. -/
def reads : LenExpr → String → Bool
  | .lit _, _ => false
  | .tok m, n => m == n
  | .scale _ _ e, n => e.reads n
  | .add a b, n | .sub a b, n => a.reads n || b.reads n

/-- Evaluate against a lookup of declared tokens. Structural recursion:
the checker's acceptance is the termination proof, and an unknown name is
an error carrying that name. The matches are explicit so the exactness
proof below can follow them case by case. -/
def eval (look : String → Option SymGlue) : LenExpr → Except String SymGlue
  | .lit l => .ok { width := l }
  | .tok n =>
    match look n with
    | some g => .ok g
    | none => .error n
  | .scale num den e =>
    match eval look e with
    | .ok g => .ok (g.scale num den)
    | .error m => .error m
  | .add a b =>
    match eval look a, eval look b with
    | .ok ga, .ok gb => .ok (ga.add gb)
    | .error m, _ => .error m
    | _, .error m => .error m
  | .sub a b =>
    match eval look a, eval look b with
    | .ok ga, .ok gb => .ok (ga.sub gb)
    | .error m, _ => .error m
    | _, .error m => .error m

/-- Resolution is deterministic and local: the answer depends only on what
the expression's own names resolve to — one document, one answer, however
the rest of the environment is stated or ordered. -/
theorem eval_names_agree (l₁ l₂ : String → Option SymGlue) (e : LenExpr)
    (h : ∀ n, e.reads n → l₁ n = l₂ n) : eval l₁ e = eval l₂ e := by
  induction e with
  | lit l => rfl
  | tok n => simp [eval, h n (by simp [reads])]
  | scale num den e ih =>
    simp only [eval, ih (fun n hn => h n (by simpa [reads] using hn))]
  | add a b iha ihb =>
    simp only [eval,
      iha (fun n hn => h n (by simp [reads, hn])),
      ihb (fun n hn => h n (by simp [reads, hn]))]
  | sub a b iha ihb =>
    simp only [eval,
      iha (fun n hn => h n (by simp [reads, hn])),
      ihb (fun n hn => h n (by simp [reads, hn]))]

/-- The same expression evaluated in ℤ, over any one fixed-point component
(the sp part, the em part, …): the arithmetic the engine owes exactness
to. Sums and differences are integer sums and differences; scaling is
`(· * num).tdiv den` with the truncation `Length.scale` uses — the one
stated rounding, TeX's own (`\divide` and `xn_over_d` both truncate
toward zero; only e-TeX's `\dimexpr` division rounds to nearest, which is
why that spelling is refused rather than mapped). -/
def evalInt (look : String → Option Int) : LenExpr → (Length → Int) → Except String Int
  | .lit l, part => .ok (part l)
  | .tok n, _ =>
    match look n with
    | some v => .ok v
    | none => .error n
  | .scale num den e, part =>
    match evalInt look e part with
    | .ok v => .ok ((v * num).tdiv den)
    | .error m => .error m
  | .add a b, part =>
    match evalInt look a part, evalInt look b part with
    | .ok va, .ok vb => .ok (va + vb)
    | .error m, _ => .error m
    | _, .error m => .error m
  | .sub a b, part =>
    match evalInt look a part, evalInt look b part with
    | .ok va, .ok vb => .ok (va - vb)
    | .error m, _ => .error m
    | _, .error m => .error m

/-- Arithmetic is exact in sp: the width's sp component of an evaluated
expression is the same expression evaluated in ℤ over the sp components —
no drift is introduced anywhere, and the only rounding is the stated
truncation in `scale`. (The same proof shape holds for every component;
sp is the one
print geometry rides on.) -/
theorem eval_exact_sp (look : String → Option SymGlue) (e : LenExpr) :
    (eval look e).map (fun g => g.width.sp)
      = evalInt (fun n => (look n).map (fun g => g.width.sp)) e (fun l => l.sp) := by
  induction e with
  | lit l => rfl
  | tok n => simp only [eval, evalInt]; cases look n <;> rfl
  | scale num den e ih =>
    simp only [eval, evalInt]
    cases h : eval look e with
    | error m => rw [h] at ih; simp [← ih, Except.map]
    | ok g => rw [h] at ih; simp [← ih, Except.map, SymGlue.scale, Length.scale]
  | add a b iha ihb =>
    simp only [eval, evalInt]
    cases ha : eval look a with
    | error m => rw [ha] at iha; simp [← iha, Except.map]
    | ok ga =>
      rw [ha] at iha
      cases hb : eval look b with
      | error m => rw [hb] at ihb; simp [← iha, ← ihb, Except.map]
      | ok gb =>
        rw [hb] at ihb
        simp [← iha, ← ihb, Except.map, SymGlue.add, Length.add]
  | sub a b iha ihb =>
    simp only [eval, evalInt]
    cases ha : eval look a with
    | error m => rw [ha] at iha; simp [← iha, Except.map]
    | ok ga =>
      rw [ha] at iha
      cases hb : eval look b with
      | error m => rw [hb] at ihb; simp [← iha, ← ihb, Except.map]
      | ok gb =>
        rw [hb] at ihb
        simp [← iha, ← ihb, Except.map, SymGlue.sub, Length.sub]

/-- Absent is diagnosed, never defaulted: an unknown token name in an
expression errors *as that name* — it never resolves to zero. -/
theorem eval_absent_named (look : String → Option SymGlue) (n : String)
    (h : look n = none) : eval look (.tok n) = .error n := by
  simp [eval, h]

end LenExpr

/-- The expression tokenizer's alphabet. -/
private inductive ETok where
  | num (mantissa : Int) (scale : Nat)
  | ident (s : String)
  | plus | minus | times | divide | lparen | rparen
  deriving Repr, BEq

/-- Scan a length expression into tokens. Numbers are unsigned here — a
sign is an operator, resolved by position. `none` when a character fits no
token: the caller falls back to its own diagnostic. -/
private def exprToks (s : String) : Option (Array ETok) := Id.run do
  let cs : Array Char := s.toList.toArray
  let mut out : Array ETok := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == ' ' || c == '\t' then
        i := i + 1
      else if c.isDigit || c == '.' then
        let mut j := i
        for _ in [i:cs.size] do
          if h' : j < cs.size then
            if cs[j].isDigit || cs[j] == '.' then j := j + 1 else break
          else break
        let some (m, sc) := parseDecimal (String.ofList (cs.extract i j).toList)
          | return none
        out := out.push (.num m sc)
        i := j
      else if c.isAlpha || c == '_' then
        let mut j := i
        for _ in [i:cs.size] do
          if h' : j < cs.size then
            if cs[j].isAlphanum || cs[j] == '_' then j := j + 1 else break
          else break
        out := out.push (.ident (String.ofList (cs.extract i j).toList))
        i := j
      else if c == '+' then out := out.push .plus; i := i + 1
      else if c == '-' then out := out.push .minus; i := i + 1
      else if c == '*' then out := out.push .times; i := i + 1
      else if c == '/' then out := out.push .divide; i := i + 1
      else if c == '(' then out := out.push .lparen; i := i + 1
      else if c == ')' then out := out.push .rparen; i := i + 1
      else return none
  return some out

/-- An operand mid-parse: a bare number, or a length expression. A number
becomes a length only through a unit or a token it scales. -/
private inductive EVal where
  | scalar (mantissa : Int) (scale : Nat)
  | len (e : LenExpr)

private def applyBinOp (op : Char) (a b : EVal) : Except String EVal :=
  match op, a, b with
  | '+', .len x, .len y => .ok (.len (.add x y))
  | '-', .len x, .len y => .ok (.len (.sub x y))
  | '+', .scalar m s, .scalar m' s' => .ok (.scalar (m * s' + m' * s) (s * s'))
  | '-', .scalar m s, .scalar m' s' => .ok (.scalar (m * s' - m' * s) (s * s'))
  | '*', .scalar m s, .len e => .ok (.len (.scale m s e))
  | '*', .len e, .scalar m s => .ok (.len (.scale m s e))
  | '*', .scalar m s, .scalar m' s' => .ok (.scalar (m * m') (s * s'))
  | '*', .len _, .len _ => .error "a length times a length has no meaning"
  | '/', _, .scalar 0 _ => .error "division by zero"
  | '/', .len e, .scalar m s =>
    .ok (.len (.scale (if m < 0 then -(s : Int) else (s : Int)) m.natAbs e))
  | '/', .scalar m s, .scalar m' s' =>
    .ok (.scalar (if m' < 0 then -(m * s') else m * s') (s * m'.natAbs))
  | '/', _, .len _ => .error "dividing by a length has no meaning"
  | _, _, _ => .error "a bare number in a length expression needs a unit"

private def opPrec (op : Char) : Nat :=
  if op == 'u' then 3 else if op == '*' || op == '/' then 2 else 1

/-- Pop and apply one operator from the stack. -/
private def popOne (vals : Array EVal) (op : Char) : Except String (Array EVal) := do
  if op == 'u' then
    match vals.back? with
    | some (.scalar m s) => return vals.pop.push (.scalar (-m) s)
    | some (.len e) => return vals.pop.push (.len (.scale (-1) 1 e))
    | none => throw "malformed expression"
  else
    match vals.back?, vals.pop.back? with
    | some b, some a => return (vals.pop.pop).push (← applyBinOp op a b)
    | _, _ => throw "malformed expression"

/-- Stack `c`, first draining every operator already on the stack that
binds at least as tightly (never past a `(`): shunting-yard's precedence
rule at one site, so the additive and multiplicative arms cannot drain by
two rules that drift apart. -/
private def pushOp (vals : Array EVal) (ops : Array Char) (c : Char) :
    Except String (Array EVal × Array Char) := do
  let mut vals := vals
  let mut ops := ops
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some top =>
      if top != '(' && opPrec top ≥ opPrec c then
        vals ← popOne vals top
        ops := ops.pop
      else break
    | none => break
  return (vals, ops.push c)

/-- Parse a token stream into an expression: shunting-yard with unary
minus, the implicit coefficient (`2 cardbleed`), and units bound where
their number stands (`1.5ex`, spaces allowed as in TeX's `2.5 \x`). Loops
are bounded by the token count — termination by construction. -/
private def exprParse (toks : Array ETok) : Except String LenExpr := do
  let mut vals : Array EVal := #[]
  let mut ops : Array Char := #[]
  let mut prevOperand := false
  for t in toks do
    match t with
    | .num m s =>
      if prevOperand then throw "malformed expression"
      vals := vals.push (.scalar m s)
      prevOperand := true
    | .ident n =>
      match vals.back?, prevOperand with
      | some (.scalar m s), true =>
        -- The number before it binds: a unit makes a literal, a token
        -- name a coefficient (TeXbook ch. 24's ⟨factor⟩⟨internal dimen⟩).
        match lengthOfUnit m s n with
        | some l => vals := vals.pop.push (.len (.lit l))
        | none => vals := vals.pop.push (.len (.scale m s (.tok n)))
      | _, true => throw "malformed expression"
      | _, false =>
        vals := vals.push (.len (.tok n))
        prevOperand := true
    | .plus | .minus =>
      let isMinus := t == ETok.minus
      if prevOperand then
        let (vals', ops') ← pushOp vals ops (if isMinus then '-' else '+')
        vals := vals'
        ops := ops'
        prevOperand := false
      else if isMinus then
        -- Unary: highest precedence, applied to the next operand alone.
        ops := ops.push 'u'
      -- A unary plus says nothing; it is skipped.
    | .times | .divide =>
      unless prevOperand do throw "malformed expression"
      let (vals', ops') ← pushOp vals ops (if t == ETok.divide then '/' else '*')
      vals := vals'
      ops := ops'
      prevOperand := false
    | .lparen =>
      if prevOperand then throw "malformed expression"
      ops := ops.push '('
      prevOperand := false
    | .rparen =>
      unless prevOperand do throw "malformed expression"
      let mut closed := false
      for _ in [0:ops.size + 1] do
        match ops.back? with
        | some '(' =>
          ops := ops.pop
          closed := true
          break
        | some top =>
          vals ← popOne vals top
          ops := ops.pop
        | none => break
      unless closed do throw "unbalanced ')'"
      prevOperand := true
  unless prevOperand do throw "malformed expression"
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some '(' => throw "unbalanced '('"
    | some top =>
      vals ← popOne vals top
      ops := ops.pop
    | none => break
  match vals.back?, vals.size with
  | some (.len e), 1 => return e
  | some (.scalar _ _), 1 => throw "a bare number in a length expression needs a unit"
  | _, _ => throw "malformed expression"

/-- Read a length expression against the declared tokens: `a + b`,
`a - b`, `2 b`, `0.5 * b` and `a / 2`, parentheses (a parenthesized
numeric subexpression is a scalar factor), literals with units. The error
is worth surfacing — an unknown token name errors as itself. -/
def parseLengthExpr (tokens : Array (String × SymGlue)) (s : String) :
    Except String SymGlue := do
  let some toks := exprToks s.trimAscii.toString
    | throw "malformed expression"
  let e ← exprParse toks
  match e.eval (fun n => (tokens.find? (·.1 == n)).map (·.2)) with
  | .ok g => return g
  | .error n => throw s!"'{n}' is not a declared token"

/-- Whether a string looks like a length expression rather than a single
value: an operator or a parenthesis somewhere, or a coefficient directly
against a name (`2cardbleed`). Routing, not validation — the parser has
the final say. -/
def looksLikeExpr (s : String) : Bool := Id.run do
  let cs := s.toList
  let mut prevDigit := false
  let mut i := 0
  for c in cs do
    if c == '(' || c == ')' || c == '*' || c == '/' then return true
    if (c == '+' || c == '-') && i > 0 then return true
    if prevDigit && (c.isAlpha || c == '_') then
      -- a digit running into letters is a unit or a coefficient; only the
      -- coefficient names an expression
      let rest := String.ofList (cs.drop i)
      let unit := String.ofList (rest.toList.takeWhile fun c => c.isAlphanum || c == '_')
      if (lengthOfUnit 1 1 unit).isNone then return true
    prevDigit := c.isDigit
    i := i + 1
  return false

/-- `cmyk(c, m, y, k)`: xcolor's cmyk model, four decimals in [0, 1],
carried in thousandths. Print declares in CMYK because that is what a
press mixes; the value survives as declared. -/
private def parseCmyk (s : String) : Option Value := do
  let inner := ((s.drop "cmyk(".length).toString.dropEnd 1).toString
  let parts := (inner.splitOn ",").map (·.trimAscii.toString)
  let vals ← parts.mapM fun p => do
    let (m, sc) ← parseDecimal p
    let v := m * 1000 / sc
    if 0 ≤ v && v ≤ 1000 then some v.toNat else none
  match vals with
  | [c, m, y, k] => some (.cmyk c m y k)
  | _ => none

/-- `digits:digits` is a name, not a malformed dimension: the slides stage
spellings (`\page{ size = 16:9 }`) parse as idents and the consuming
declaration decides what the name means — an unknown one keeps its own
refusal (E0324 for `size`) instead of a parse error here. -/
private def isRatioName (s : String) : Bool :=
  match s.splitOn ":" with
  | [a, b] =>
    !a.isEmpty && !b.isEmpty &&
      a.toList.all (·.isDigit) && b.toList.all (·.isDigit)
  | _ => false

def parseValue (raw : String) (tokens : Array (String × SymGlue) := #[]) : Option Value :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    some (.str (String.ofList (s.toList.drop 1).dropLast))
  else if s.startsWith "#" then
    parseColor s
  else if s.startsWith "cmyk(" && s.endsWith ")" then
    parseCmyk s
  else if s.startsWith "{" && s.endsWith "}" && s.length ≥ 2 then
    -- Nested blocks stay opaque; the declaration decides whether it takes one.
    some (.block (String.ofList (s.toList.drop 1).dropLast |>.trimAscii.toString))
  else if (s.splitOn "*").length == 2 then
    -- The factor may scale one name, or a whole subexpression.
    parseScaled tokens s <|>
      (if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue else none)
  else if (s.splitOn " plus ").length > 1 || (s.splitOn " minus ").length > 1 then
    (parseGlue s).map Value.glue
  else if s.endsWith "em" || s.endsWith "ex" then
    (parseLength s).map fun l => Value.glue { width := l }
  else if let some (_, g) := tokens.find? (·.1 == s) then
    some (.glue g)
  else if s == "fill" || s == "fil" then
    -- LaTeX's \fill: zero width, first-order infinite stretch
    -- (`0pt plus 1fill`, ltspace.dtx). A declared token of the same name
    -- wins above, as any redeclaration does.
    some (.glue { fil := true })
  else
    -- dimension: digits then a unit suffix
    let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
    let unit := String.ofList (s.toList.drop digits.length) |>.trimAscii.toString
    match parseDecimal (String.ofList digits), unitScale unit with
    | some (mantissa, scale), some (num, den) =>
      some (.dim (mantissa * num / (scale * den : Nat)))
    | some (mantissa, 1), none =>
      if unit.isEmpty then some (.int mantissa)
      else if isRatioName s then some (.ident s)
      else if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue
      else none
    | _, _ =>
      if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue
      else if !s.isEmpty && s.toList.all isIdentChar then some (.ident s) else none

/-- Parse a `key = value, ...` block. Reports malformed entries; the caller
validates keys, so an unknown key is not an error here. -/
def parseBlock (file : String) (src : String) (pos : Pos) (what : String)
    (tokens : Array (String × SymGlue) := #[]) : Array Entry × Array Diag := Id.run do
  let mut entries : Array Entry := #[]
  let mut diags : Array Diag := #[]
  for entry in splitEntries src do
    match entry.splitOn "=" with
    | key :: rest =>
      let key := key.trimAscii.toString
      let valueSrc := String.intercalate "=" rest |>.trimAscii.toString
      -- Keys admit '-' beyond the ident alphabet (`mark-gap`); values do
      -- not — there '-' is subtraction, and the expression parser owns it.
      if key.isEmpty || !key.toList.all (fun c => isIdentChar c || c == '-') then
        diags := diags.push (Diag.of .E0320
          s!"invalid key in '\\{what}': {entry.quote}" (some ⟨file, pos⟩)
          (help := "entries look like: key = value"))
      else if valueSrc.isEmpty then
        diags := diags.push (Diag.of .E0320
          s!"'{key}' in '\\{what}' has no value" (some ⟨file, pos⟩)
          (help := "entries look like: key = value"))
      else
        match parseValue valueSrc tokens with
        | some v => entries := entries.push ⟨key, v⟩
        | none =>
          let detail := if looksLikeExpr valueSrc then
              match parseLengthExpr tokens valueSrc with
              | .error e => s!": {e}"
              | .ok _ => ""
            else ""
          diags := diags.push (Diag.of .E0321
            s!"cannot read value for '{key}' in '\\{what}': {valueSrc.quote}{detail}"
            (some ⟨file, pos⟩) (help :=
              "values are \"strings\", dimensions (10pt, 0.5in), length expressions \
(a + 2b), numbers, names, or #RRGGBB colors"))
    | [] => pure ()
  return (entries, diags)

/-- Split one `key = value` entry. -/
def splitEntry (entry : String) : Option (String × String) :=
  match entry.splitOn "=" with
  | key :: rest =>
    let k := key.trimAscii.toString
    let v := (String.intercalate "=" rest).trimAscii.toString
    if k.isEmpty || v.isEmpty then none else some (k, v)
  | [] => none

/-- Reject keys the declaration does not define, naming the ones it does. -/
def unknownKey (file : String) (what key : String) (known : List String)
    (pos : Pos) : Diag :=
  Diag.of .E0322 s!"'\\{what}' has no key '{key}'" (some ⟨file, pos⟩)
    (help := s!"known keys: {String.intercalate ", " known}")

def wrongType (file : String) (what key expected : String) (got : Value)
    (pos : Pos) : Diag :=
  Diag.of .E0323 s!"'{key}' in '\\{what}' expects {expected}, got a {got.kindName}"
    (some ⟨file, pos⟩)

end LeanTex.Core.Decl
