module

public import LeanTex.Core.Parse
public import LeanTex.Core.Ir
import LeanTex.Core.Decl
import LeanTex.Core.Loop
import LeanTex.Core.GfxAffine
import LeanTex.Core.TikzCommands

/-! The rendered `tikzpicture` and `tikzcd` subsets, evaluated at elaboration into concrete shapes:
statements, pgfmath arithmetic, loops, colours, paths and nodes. -/

namespace LeanTex.Core.Picture

open LeanTex.Core LeanTex.Core.Dim

/-- A diagnostic the picture walk raises, positioned later by the elaborator. -/
public abbrev PDiag := DiagCode × String

/-- Whether a diagnostic names a content loss, one whose floor is not inert. -/
public def namesLoss (ds : Array PDiag) : Bool :=
  ds.any fun d => d.1.floor != .inert

/-- One micro-token of picture source: lexer words re-split into numbers, identifiers and symbols,
braces as groups. -/
public inductive Tok where
  | ctrl (name : String)
  | ident (s : String)
  /-- A number literal in thousandths, and its spelling as written. -/
  | num (milli : Int) (text : String)
  | sym (c : Char)
  | space
  | group (body : List Tok)
  /-- A math span, carried whole for the elaborator's math layer, with its opener's source site. -/
  | math (display : Bool) (body : List Parse.Raw) (site : Option Span)
  /-- Source the subset cannot tokenise, named for its diagnostic. -/
  | other (what : String)
  deriving Repr, BEq, Inhabited

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
        | some (m, sc) => out := out.push (.num (m * 1000 / sc) lit)
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

/-- The control word a `scope` environment becomes (`ofRawOne`). -/
public def scopeCtrl : String := "scope env"

mutual

private def ofRawList (site : Pos → Option Span) (acc : Array Tok) :
    List Parse.Raw → Array Tok
  | [] => acc
  | r :: rest => ofRawList site (ofRawOne site acc r) rest

private def ofRawOne (site : Pos → Option Span) (acc : Array Tok) : Parse.Raw → Array Tok
  | .word s _ => splitWord acc s
  | .space => acc.push .space
  | .par _ => acc.push .space
  | .ctrl n _ => acc.push (.ctrl n)
  | .sym c _ => acc.push (.sym c)
  | .group body _ => acc.push (.group (ofRawList site #[] body.toList).toList)
  | .math d body p => acc.push (.math d body.toList (site p))
  -- A scope is its body as one group behind a control word no document can spell.
  | .env "scope" body _ => (acc.push (.ctrl scopeCtrl)).push (.group (ofRawList site #[] body.toList).toList)
  | .env n _ _ => acc.push (.other s!"environment '{n}'")
  | .verb _ _ _ => acc.push (.other "verbatim")

end

/-- Picture tokens from source whose positions `site` places in a file. -/
public def ofRawsAt (site : Pos → Option Span) (raws : Array Parse.Raw) : Array Tok :=
  ofRawList site #[] raws.toList

/-- Source whose positions index no file the walk can name: its formulas
carry no site. -/
public def ofRaws (raws : Array Parse.Raw) : Array Tok :=
  ofRawsAt (fun _ => none) raws

/-- A document setting's tokens, its formulas sited in the file that wrote the setting. -/
public def ofSetting (setting : Span × Array Parse.Raw) : Array Tok :=
  ofRawsAt (fun p => some ⟨setting.1.file, p⟩) setting.2

/-- A bound macro's value: a number in milli or a length in sp, each with the text pgf prints for
it, or text (a pgfmath string or a list item's raw text). -/
public inductive Val where
  | num (m : Int) (text : String)
  | len (sp : Sp) (text : String)
  | str (s : String)
  deriving Repr, BEq, Inhabited

/-- A milli value at three decimals at most, an integer without a point. -/
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

/-- A dimension's points as TeX's `\the` prints them, the unit dropped. -/
public def texPoints (s : Sp) : String :=
  let (whole, digits) := Decl.texScaledParts s.natAbs
  (if s < 0 then "-" else "") ++ toString whole ++ "." ++ String.join (digits.map toString)

/-- The scaled points TeX reads from a decimal given in thousandths. -/
private def milliSp (m : Int) : Sp :=
  let n := m.natAbs
  let fr := n % 1000
  let s : Int := (n / 1000 * 65536 + Decl.roundDecimals [fr / 100, fr / 10 % 10, fr % 10] : Nat)
  if m < 0 then -s else s

/-- A number pgfmath computed, as it prints one: TeX's points of the dimension holding it. -/
public def Val.computed (m : Int) : Val := .num m (texPoints (milliSp m))

/-- A number pgffor's `...` computed, as it prints one: TeX's points, a trailing `.0` dropped. -/
private def rangeItem (m : Int) : Val :=
  let t := texPoints (milliSp m)
  .num m (if t.endsWith ".0" then (t.dropEnd 2).toString else t)

/-- A length as pgf prints a length macro: its points as TeX prints them, then `pt`. -/
public def lenString (sp : Sp) : String := texPoints sp ++ "pt"

/-- A length pgfmath computed, as a length macro prints it. -/
public def Val.length (sp : Sp) : Val := .len sp (lenString sp)

public def Val.text : Val → String
  | .num _ t => t
  | .len _ t => t
  | .str s => s

/-- A literal like `0.5cm` as a length, or `none` for a font-relative or unknown unit. -/
public def unitLen? (m : Int) (u : String) : Option Sp :=
  (Decl.parseLength (milliString m ++ u)).bind fun l =>
    if l.em == 0 && l.ex == 0 then some l.sp else none

/-- A unitless milli value read as points where units are declared beside it, as pgfmath reads it. -/
public def milliPt (m : Int) : Sp :=
  let n := m * Dim.spPerPt
  if n < 0 then -((-n + 500) / 1000) else (n + 500) / 1000

/-- A length's points in milli, what a length means where a plain number is asked. -/
public def spMilliPt (sp : Sp) : Int :=
  let n := sp * 1000
  if n < 0 then -((-n + 32768) / 65536) else (n + 32768) / 65536

private def tokText : Tok → String
  | .ctrl n => s!"'\\{n}'"
  | .ident s => s!"'{s}'"
  | .num _ t => s!"'{t}'"
  | .sym c => s!"'{c}'"
  | .space => "a space"
  | .group _ => "'{...}'"
  | .math _ _ _ => "math"
  | .other what => what

private inductive Rp where
  | push (v : Val)
  | neg
  | add | sub | mul | div
  | lt | gt
  | fmax | fmin | fite
  deriving Repr, BEq

private def prec : Rp → Nat
  | .neg => 4
  | .mul | .div => 3
  | .add | .sub => 2
  | .lt | .gt => 1
  | _ => 0

/-- A leading-zero integer as pgfmath's parser reads one: in octal, spelled in decimal. -/
private def octalLit? (t : String) : Option Val :=
  let ds := t.toList
  if ds.length ≥ 2 && ds.head? == some '0' && ds.all (fun c => '0' ≤ c && c ≤ '7') then
    let v : Nat := ds.foldl (fun a c => a * 8 + (c.toNat - 48)) 0
    some (.num (v * 1000) (toString v))
  else none

private def evalTokens (env : List (String × Val)) (toks : Array Tok) :
    Except String Val := Id.run do
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
      | .num m text =>
        match toks[i]? with
        | some (.ident u) =>
          match unitLen? m u with
          | some sp =>
            i := i + 1
            out := out.push (.push (.len sp (text ++ u)))
          | none => out := out.push (.push ((octalLit? text).getD (.num m text)))
        | _ => out := out.push (.push ((octalLit? text).getD (.num m text)))
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
      | .math _ _ _ => return .error "math in an expression"
      | .other what => return .error s!"{what} in an expression"
  let (o2, p2) := flushTo out ops 1
  out := o2
  for op in p2.reverse do
    if op == .fmax || op == .fmin || op == .fite then
      return .error "unclosed '('"
    out := out.push op
  let mut stack : Array Val := #[]
  let q (v : Val) : Except String (Int × Bool) :=
    match v with
    | .num m _ => .ok (m, false)
    | .len sp _ => .ok (sp, true)
    | .str s => .error s!"'{s}' where a number is needed"
  -- Where either operand is a length both are, a unitless one read as points (pgfmath).
  let common (a b : Int × Bool) : Int × Int × Bool :=
    if a.2 || b.2 then
      ((if a.2 then a.1 else milliPt a.1), (if b.2 then b.1 else milliPt b.1), true)
    else (a.1, b.1, false)
  let mk (v : Int) (isLen : Bool) : Val := if isLen then .length v else .computed v
  for r in out do
    match r with
    | .push v => stack := stack.push v
    | .neg =>
      match stack.back? with
      | some a =>
        match q a with
        | .ok (m, l) => stack := stack.pop.push (mk (-m) l)
        | .error e => return .error e
      | none => return .error "misplaced '-'"
    | .fite =>
      match stack.back?, stack.pop.back?, stack.pop.pop.back? with
      | some no, some yes, some c =>
        let stack' := stack.pop.pop.pop
        match q c with
        | .ok (m, _) => stack := stack'.push (if m != 0 then yes else no)
        | .error e => return .error e
      | _, _, _ => return .error "'ifthenelse' needs (condition, value, value)"
    | op =>
      match stack.back? with
      | some bv =>
        match stack.pop.back? with
        | some av =>
          let stack' := stack.pop.pop
          match q av, q bv with
          | .ok a, .ok b =>
            let (x, y, l) := common a b
            match op with
            | .add => stack := stack'.push (mk (x + y) l)
            | .sub => stack := stack'.push (mk (x - y) l)
            | .mul =>
              -- A length times a number scales it; two lengths multiply their points; two numbers, milli.
              let v := if a.2 && b.2 then a.1 * b.1 / 65536 else a.1 * b.1 / 1000
              stack := stack'.push (mk v (a.2 || b.2))
            | .fmax => stack := stack'.push (mk (max x y) l)
            | .fmin => stack := stack'.push (mk (min x y) l)
            | .lt => stack := stack'.push (if x < y then .num 1000 "1" else .num 0 "0")
            | .gt => stack := stack'.push (if x > y then .num 1000 "1" else .num 0 "0")
            | .div =>
              if b.1 == 0 then return .error "division by zero"
              else if a.2 && !b.2 then stack := stack'.push (.length (a.1 * 1000 / b.1))
              else stack := stack'.push (.computed (x * 1000 / y))
            | _ => return .error "malformed expression"
          | .error e, _ | _, .error e => return .error e
        | none => return .error "operator missing an operand"
      | none => return .error "operator missing an operand"
  match stack.toList with
  | [v] => return .ok v
  | [] => return .error "empty expression"
  | _ => return .error "malformed expression"

/-- A macro's text as the walk splits source words. -/
private def textToks (acc : Array Tok) (s : String) : Array Tok := Id.run do
  let mut out := acc
  let mut first := true
  for w in s.splitOn " " do
    unless first do out := out.push .space
    first := false
    out := splitWord out w
  return out

/-- An expression as pgfmath reads one, a macro bound to a number standing as its text. -/
private def spliceNumbers (env : List (String × Val)) (toks : Array Tok) : Array Tok := Id.run do
  let mut out : Array Tok := #[]
  for t in toks do
    match t with
    | .ctrl n =>
      match env.lookup n with
      | some (.num _ text) => out := textToks out text
      | _ => out := out.push t
    | _ => out := out.push t
  return out

/-- pgfmath's fast lane: a number followed by points alone stands as written. -/
private def fastLane? (toks : Array Tok) : Option Val :=
  match toks.toList with
  | .num m t :: rest =>
    if rest.all (· == .sym '.') then some (.num m (rest.foldl (fun s _ => s.push '.') t)) else none
  | _ => none

/-- An expression's value as pgfmath computes and spells it. -/
private def evalExpr (env : List (String × Val)) (toks : Array Tok) : Except String Val :=
  let toks := spliceNumbers env toks
  match fastLane? toks with
  | some v => .ok v
  | none => evalTokens env toks

private def evalNum (env : List (String × Val)) (toks : Array Tok) : Except String Int :=
  match evalExpr env toks with
  | .ok (.num m _) => .ok m
  | .ok (.len sp _) => .ok (spMilliPt sp)
  | .ok (.str s) => .error s!"'{s}' where a number is needed"
  | .error e => .error e

private def evalComp (env : List (String × Val)) (toks : Array Tok) :
    Except String (Int × Bool) :=
  match evalExpr env toks with
  | .ok (.num m _) => .ok (m, false)
  | .ok (.len sp _) => .ok (sp, true)
  | .ok (.str s) => .error s!"'{s}' where a number is needed"
  | .error e => .error e

/-- How many values `{a,...,b}` with step `step` enumerates; `none` when the range would not terminate. -/
public def rangeCount (a step b : Int) : Option Nat :=
  if step > 0 && a ≤ b then some (((b - a) / step).toNat + 1)
  else if step < 0 && b ≤ a then some (((a - b) / (-step)).toNat + 1)
  else none

/-- The enumerated values, indexed off the count: total by construction. -/
public def range (a step b : Int) : Option (Array Int) :=
  (rangeCount a step b).map fun n => (Array.range n).map fun i => a + step * Int.ofNat i

public theorem range_size (a step b : Int) (n : Nat) (h : rangeCount a step b = some n) :
    (range a step b).map (·.size) = some n := by
  simp [range, h]

public theorem range_get (a step b : Int) (xs : Array Int) (hx : range a step b = some xs)
    (i : Nat) (h : i < xs.size) : xs[i] = a + step * i := by
  simp only [range, Option.map_eq_some_iff] at hx
  obtain ⟨n, _, hmap⟩ := hx
  subst hmap
  simp

public theorem range_unit_size (a b : Int) (hab : a ≤ b) :
    (range (1000 * a) 1000 (1000 * b)).map (·.size) = some ((b - a).toNat + 1) := by
  have hc : rangeCount (1000 * a) 1000 (1000 * b) = some ((b - a).toNat + 1) := by
    have hcond : (decide ((1000:Int) > 0) && decide ((1000:Int) * a ≤ 1000 * b)) = true := by
      simp [hab]
    simp only [rangeCount, hcond, Option.some.injEq, ite_true]
    omega
  exact range_size _ _ _ _ hc

/-- How a TeX conditional's test is read: arithmetic, constant, the picture's mode, or opaque and
refused by name. -/
public inductive CondKind where
  | num (name : String)
  | always (v : Bool)
  | mode (name : String) (v : Bool)
  | opaque (name : String)
  deriving Repr, BEq, Inhabited

private def pictureMode (n : String) : Option Bool :=
  if n == "ifhmode" || n == "ifinner" then some true
  else if n == "ifvmode" || n == "ifmmode" then some false
  else none

private def condKindOf (n : String) : Option CondKind :=
  if n == "ifnum" || n == "ifdim" then some (.num n)
  else if n == "iftrue" then some (.always true)
  else if n == "iffalse" then some (.always false)
  else if let some v := pictureMode n then some (.mode n v)
  else if n.startsWith "if" && n.length > 2 then some (.opaque n)
  else none

private def condTakesNoTest (n : String) : Bool :=
  n == "iftrue" || n == "iffalse" || n == "ifmmode" || n == "ifhmode" ||
    n == "ifvmode" || n == "ifinner"

/-- How a `\pgfmathset…macro` stores its value: as pgfmath prints it, truncated toward zero to a
whole unit, or as a length. -/
public inductive SetMode where
  | plain
  | trunc
  | length
  deriving Repr, BEq, Inhabited

/-- One parsed picture statement; paths and nodes keep their tokens for evaluation per loop iteration. -/
public inductive Stmt where
  | fill (toks : Array Tok)
  | node (toks : Array Tok)
  | draw (toks : Array Tok)
  /-- `\path (a) edge (b);`: a path whose `edge` operations draw (pgf's `every edge`). -/
  | path (toks : Array Tok)
  /-- `\useasboundingbox`: the rectangle, joined with the box already established, is the picture's
  box from here on (pgf manual §15.8). -/
  | bbox (toks : Array Tok)
  /-- `\pgfmathsetmacro`, `\pgfmathtruncatemacro` and
  `\pgfmathsetlengthmacro`, by `mode`. -/
  | set (name : String) (expr : Array Tok) (mode : SetMode)
  | foreach (vars : Array String) (list : Array Tok) (body : List Stmt)
  /-- A TeX conditional, its test kept for evaluation where its macros are bound. -/
  | cond (kind : CondKind) (test : Array Tok) (thenS : List Stmt) (elseS : List Stmt)
  /-- `\coordinate (name) at (…);`: a named node of no extent (TikZ manual §17.2.1). -/
  | coordinate (toks : Array Tok)
  /-- `\filldraw[…] …;` — `\path[fill, draw]`. -/
  | filldraw (toks : Array Tok)
  /-- A TeX group of statements, or `\textcolor{c}{…}` with its colour; declarations stay inside. -/
  | grouped (color : Option (Array Tok)) (body : List Stmt)
  /-- `\color{c}`: the default ink for the statements after it in its group. -/
  | setColor (spec : Array Tok)
  /-- A font declaration (`\bfseries`, `\small`): every node's text after
  it in its group sets in it. -/
  | setDecl (name : String)
  /-- `\begin{scope}[opts] … \end{scope}` (TikZ manual §12.3.1): a group
  whose options transform its coordinates and set keys for its statements. -/
  | scope (opts : Array Tok) (body : List Stmt)
  /-- `\shade` and `\shadedraw`: the path painted with a shading (pgf manual §15.7). -/
  | shade (toks : Array Tok) (draw : Bool)
  /-- `\clip`: what follows in its scope paints inside the path (pgf manual §15.9). -/
  | clip (toks : Array Tok)
  deriving Repr, Inhabited

private inductive StKind where
  | fill
  | node
  | draw
  | path
  | bbox
  | coordinate
  | filldraw
  | shade
  | shadedraw
  | clip
  deriving Repr, BEq, Inhabited

private def StKind.name : StKind → String
  | .fill => "fill"
  | .node => "node"
  | .draw => "draw"
  | .path => "path"
  | .bbox => "useasboundingbox"
  | .coordinate => "coordinate"
  | .filldraw => "filldraw"
  | .shade => "shade"
  | .shadedraw => "shadedraw"
  | .clip => "clip"

private inductive Mode where
  | top
  | stmt (kind : StKind) (acc : Array Tok)
  | sname (mode : SetMode)
  | sexpr (name : String) (mode : SetMode)
  | fvars (vars : Array String)
  | flist (vars : Array String)
  | fbody (vars : Array String) (list : Array Tok)
  | tcolor
  | tbody (spec : Array Tok)
  | scolor
  | scopeBody
  | scopeHead (bracket : Bool)
  | skip
  /-- After a conditional opener, collecting its test: an arithmetic test ends at the space after its
  second number, any other at its first space. -/
  | icond (kind : CondKind) (test : Array Tok) (sawRel : Bool)
  deriving Repr, Inhabited

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
  pending : Array (Array String × Array Tok) := #[]
  conds : Array CondFrame := #[]
  mode : Mode := .top
  scopeOpts : Array Tok := #[]
  declNames : List String := []

private def subpaths (acc : Array Tok) : Array (Array Tok) := Id.run do
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
  -- A path may end at a coordinate, a move that draws nothing (pgf manual §14).
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

private def PSt.emit (st : PSt) (ss : List Stmt) : PSt :=
  match st.conds.back? with
  | none => { st with out := ss.foldl Array.push st.out }
  | some f =>
    let f2 : CondFrame := { f with taken := ss.foldl Array.push f.taken }
    { st with conds := st.conds.pop.push f2 }

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

private def PSt.elseHere (st : PSt) : PSt :=
  match st.conds.back? with
  | none => (st.outside "an '\\else' with no conditional open")
  | some f =>
    if f.inElse then st.diag .E0333 "a second '\\else' in one conditional; the \
conditional is not drawn"
    else
      let f2 : CondFrame := { f with thenS := f.taken, taken := #[], inElse := true }
      { st with conds := st.conds.pop.push f2 }

private def PSt.fiHere (st : PSt) : PSt :=
  match st.conds.back? with
  | none => (st.outside "a '\\fi' with no conditional open")
  | some f =>
    let thenS := if f.inElse then f.thenS else f.taken
    let elseS := if f.inElse then f.taken else #[]
    let st := { st with conds := st.conds.pop }
    st.finishMany [.cond f.kind f.test thenS.toList elseS.toList]

private def PSt.drain (st : PSt) : PSt := Id.run do
  let mut st := st
  for _ in [0:st.conds.size] do
    if st.conds.isEmpty then break
    st := { st.fiHere with mode := .top }
  if st.conds.isEmpty then return st
  return st.diag .E0333 "a conditional in this picture is never closed by \
'\\fi'; its statements are not drawn"

private def step (t : Tok) (st : PSt) : PSt :=
  match st.mode with
  | .top =>
    match t with
    | .ctrl "fill" => { st with mode := .stmt .fill #[] }
    | .ctrl "node" => { st with mode := .stmt .node #[] }
    | .ctrl "draw" => { st with mode := .stmt .draw #[] }
    | .ctrl "path" => { st with mode := .stmt .path #[] }
    | .ctrl "useasboundingbox" => { st with mode := .stmt .bbox #[] }
    | .ctrl "coordinate" => { st with mode := .stmt .coordinate #[] }
    | .ctrl "filldraw" => { st with mode := .stmt .filldraw #[] }
    | .ctrl "shade" => { st with mode := .stmt .shade #[] }
    | .ctrl "shadedraw" => { st with mode := .stmt .shadedraw #[] }
    | .ctrl "clip" => { st with mode := .stmt .clip #[] }
    | .ctrl "textcolor" => { st with mode := .tcolor }
    | .ctrl "color" => { st with mode := .scolor }
    | .ctrl "scope env" => { st with mode := .scopeBody }
    | .ctrl "foreach" => { st with mode := .fvars #[] }
    | .ctrl "pgfmathsetmacro" => { st with mode := .sname .plain }
    | .ctrl "pgfmathtruncatemacro" => { st with mode := .sname .trunc }
    | .ctrl "pgfmathsetlengthmacro" => { st with mode := .sname .length }
    | .ctrl "else" => st.elseHere
    | .ctrl "fi" => st.fiHere
    | .ctrl name =>
      match condKindOf name with
      | some k =>
        if condTakesNoTest name then
          { st with conds := st.conds.push { kind := k, test := #[] }, mode := .top }
        else { st with mode := .icond k #[] false }
      | none =>
        if st.declNames.contains name then st.finish (.setDecl name)
        else { (st.outside s!"'\\{name}'") with mode := .skip }
    | .sym ';' | .space => st
    | .other what => { (st.outside what) with mode := .skip }
    | .math _ _ _ => { (st.outside "math") with mode := .skip }
    | .ident s => { (st.outside s!"'{s}'") with mode := .skip }
    | .num _ _ => { (st.outside "a bare number") with mode := .skip }
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
        | .coordinate => st.finish (.coordinate acc)
        | .filldraw => st.finish (.filldraw acc)
        | .shade => st.finish (.shade acc false)
        | .shadedraw => st.finish (.shade acc true)
        | .clip => st.finish (.clip acc)
    | _ => { st with mode := .stmt kind (acc.push t) }
  | .sname setMode =>
    match t with
    | .space => st
    | .group g =>
      match g.filter (· != .space) with
      | [.ctrl name] => { st with mode := .sexpr name setMode }
      | _ => { st.diag .E0333 "'\\pgfmathsetmacro' needs '{\\name}' first" with mode := .top }
    | _ =>
      { st.diag .E0333 "'\\pgfmathsetmacro' needs '{\\name}' first" with mode := .top }
  | .sexpr name setMode =>
    match t with
    | .space => st
    | .group g => st.finish (.set name g.toArray setMode)
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
    | .ctrl "coordinate" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .coordinate #[] }
    | .ctrl "filldraw" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .filldraw #[] }
    | .ctrl "shade" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .shade #[] }
    | .ctrl "shadedraw" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .shadedraw #[] }
    | .ctrl "clip" =>
      { st with pending := st.pending.push (vars, list), mode := .stmt .clip #[] }
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
    -- `.group` never reaches here: `parseTok` owns that arm.
    | _ =>
      { (st.outside "this '\\foreach' body")
        with mode := .skip, pending := #[] }
  | .tcolor =>
    match t with
    | .space => st
    | .group spec => { st with mode := .tbody spec.toArray }
    | _ => { (st.outside "a '\\textcolor' without its colour group") with mode := .skip }
  -- `.group` never reaches here: `parseTok` owns that arm.
  | .tbody _ =>
    match t with
    | .space => st
    | _ => { (st.outside "a '\\textcolor' without its body group") with mode := .skip }
  | .scopeBody =>
    match t with
    | .space => st
    | _ => { (st.outside "a 'scope' without its body") with mode := .skip }
  -- `parseTok` reads a scope head's first token; nothing else reaches here.
  | .scopeHead false => st
  | .scopeHead true =>
    match t with
    | .sym ']' => { st with mode := .top }
    | t => { st with scopeOpts := st.scopeOpts.push t }
  | .scolor =>
    match t with
    | .space => st
    | .group spec => st.finish (.setColor spec.toArray)
    | _ => { (st.outside "a '\\color' without its colour group") with mode := .skip }
  | .skip =>
    match t with
    | .sym ';' => { st with mode := .top }
    | _ => st
  | .icond kind test sawRel =>
    let close (st : PSt) : PSt :=
      { st with conds := st.conds.push { kind := kind, test := test }, mode := .top }
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
    -- `\else` or `\fi` straight after the test: an empty then-branch, or no branch at all.
    | .ctrl "else" => (close st).elseHere
    | .ctrl "fi" => (close st).fiHere
    | _ => { st with mode := .icond kind (test.push t) sawRel }

mutual

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
    let sub := parseList g { declNames := st.declNames }
    { st with bad := st.bad ++ sub.bad }.finish (.foreach vars list sub.out.toList)
  | .tbody spec, .group g =>
    let sub := parseList g { declNames := st.declNames }
    { st with bad := st.bad ++ sub.bad }.finish (.grouped (some spec) sub.out.toList)
  | .top, .group g =>
    let sub := parseList g { declNames := st.declNames }
    { st with bad := st.bad ++ sub.bad }.finish (.grouped none sub.out.toList)
  | .scopeBody, .group g =>
    let sub := parseList g { declNames := st.declNames, mode := .scopeHead false }
    { st with bad := st.bad ++ sub.bad, mode := .top }.finish (.scope sub.scopeOpts sub.out.toList)
  | .scopeHead false, .group g =>
    let sub := parseList g { declNames := st.declNames }
    { st with bad := st.bad ++ sub.bad, mode := .top }.finish (.grouped none sub.out.toList)
  | .scopeHead false, .space => st
  | .scopeHead false, .sym '[' => { st with mode := .scopeHead true }
  | .scopeHead false, t => step t { st with mode := .top }
  | _, _ => step t st

end

/-- The evaluation context: the palette, the picture's scale and styles, and what the elaborator hands down. -/
public structure Cx where
  pal : Ir.Palette
  scale : Int := 1000
  styles : List (String × Array Tok) := []
  transformShape : Bool := false
  /-- What the document's `\tikzset` lines set for every picture (`documentOpts`), the outermost
  bracket every statement inherits. -/
  global : Array (Array Tok) := #[]
  /-- The picture-level option entries its contents inherit. -/
  opts : Array (Array Tok) := #[]
  /-- What `every node/.style` declared, between the picture's entries and the node's own. -/
  everyNode : Array (Array Tok) := #[]
  /-- What `every path/.style={...}` declared: the same level for a path. -/
  everyPath : Array (Array Tok) := #[]
  /-- What `every text node part/.style` declared, at the level of `every node`. -/
  everyText : Array (Array Tok) := #[]
  /-- `node distance` between relatively placed nodes' facing borders, vertical then horizontal; pgf's
  default 1 cm. -/
  dist : Sp × Sp := (Dim.mm 10, Dim.mm 10)
  /-- Whether the parse named a construct outside the subset, to which an unresolved name then traces. -/
  parseGap : Bool := false
  /-- How a math span in a node body elaborates, provided by the elaborator. -/
  math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag
  /-- The one-argument text commands and the style each names, the elaborator's own table. -/
  argStyles : List (String × Ir.Style) := []
  /-- The document's size ladder, per mille of the body. -/
  ladder : List (String × Nat) := Ir.sizeScale
  /-- The font declarations and the style each names, the elaborator's own table. -/
  declStyles : List (String × Ir.Style) := []
  /-- The document's body size. -/
  bodySize : Sp := Ir.baseFontSize
  /-- How a label's content measures at a per-mille size, provided by the driver through the elaborator. -/
  metric : Ir.Pic.LabelMetric := fun _ _ => {}
  /-- The current colour (pgf's `.`), black until a colour option, `\color` or `\textcolor` sets it. -/
  ink : Ir.Color := Ir.Color.black
  /-- The font declarations in force, innermost last. -/
  decls : Array String := #[]
  /-- The coordinate transformation in force, from the points a statement spells to the canvas. -/
  xf : Gfx.Affine := Gfx.Affine.unit
  /-- Whether the document loads arrows.meta, which makes `To` its Computer Modern arrow. -/
  metaArrows : Bool := false
  /-- A node's text with the document's definitions of TikZ's installed commands applied, as TikZ
  restores them there (`\tikz@uninstallcommands`). -/
  nodeText : List Tok → List Tok := id

/-- Picture milli-units to sp: one TikZ unit is 1 cm, times the declared scale. -/
public def Cx.toSp (cx : Cx) (m : Int) : Sp :=
  m * cx.scale * Dim.mm 10 / 1000000

/-- The size the declarations in force set a node's text at, per mille of the body, under the
node's own factor. -/
public def Cx.declScale (cx : Cx) (factor : Nat) : Nat :=
  let declSize : Option Nat :=
    cx.decls.foldl (fun z n => (cx.ladder.lookup n).orElse fun _ => z) none
  (declSize.map fun k => k * factor / 1000).getD factor

private def roundRat (q : Rat) : Sp := (q + 1 / 2).floor

/-- A point a statement spells, in sp, on the canvas (`Cx.xf`). -/
public def Cx.place (cx : Cx) (x y : Sp) : Sp × Sp :=
  let (u, v) := cx.xf.apply ((x : Rat), (y : Rat))
  (roundRat u, roundRat v)

/-- A displacement on the canvas: the transformation's linear part alone, as
pgf moves a relative coordinate. -/
public def Cx.placeVec (cx : Cx) (x y : Sp) : Sp × Sp :=
  let m := cx.xf
  (roundRat (m.a * x + m.c * y), roundRat (m.b * x + m.d * y))

/-- Does the transformation keep the axes — no turn and no shear — so a
rectangle stays a rectangle and an ellipse an axis-aligned one? -/
public def Cx.axisAligned (cx : Cx) : Bool := cx.xf.b == 0 && cx.xf.c == 0

/-- A coordinate component in sp: a number of the 1 cm unit vector or a length, both through the scale. -/
public def Cx.compSp (cx : Cx) (v : Int × Bool) : Sp :=
  if v.2 then v.1 * cx.scale / 1000 else cx.toSp v.1

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

private def addStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  (n, expandBody styles g) :: styles

private def appendStyle (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  let added := expandBody styles g
  match styles.lookup n with
  | some prior =>
    if added.isEmpty then styles
    else if prior.isEmpty then (n, added) :: styles
    else (n, prior.push (.sym ',') ++ added) :: styles
  | none => (n, added) :: styles

private def tipKey (n : String) : String := ".tip " ++ n

private def declareTip (styles : List (String × Array Tok)) (n : String) (g : List Tok) :
    List (String × Array Tok) :=
  (tipKey n, g.toArray) :: styles

private def everyNodeKey : String := "every node"
private def everyPathKey : String := "every path"
private def everyTextKey : String := "every text node part"

private def isSym (c : Char) : Tok → Bool
  | .sym d => d == c
  | _ => false

private def splitSym (c : Char) : List Tok → Option (List Tok × List Tok)
  | [] => none
  | t :: rest =>
    if isSym c t then some ([], rest)
    else (splitSym c rest).map fun (pre, post) => (t :: pre, post)

private theorem splitSym_append (c : Char) : ∀ (q r : List Tok),
    (∀ t ∈ q, isSym c t = false) → splitSym c (q ++ (.sym c :: r)) = some (q, r)
  | [], r, _ => by simp [splitSym, isSym]
  | t :: q, r, h => by
    have ht : isSym c t = false := h t (List.mem_cons_self ..)
    have hq : ∀ u ∈ q, isSym c u = false := fun u hu => h u (List.mem_cons_of_mem _ hu)
    simp only [List.cons_append, splitSym, ht, Bool.false_eq_true,
      splitSym_append c q r hq, Option.map_some, ite_false]

private def identPath : List Tok → Option String
  | [.ident n] => some n
  | .ident n :: rest => (identPath rest).map fun s => n ++ " " ++ s
  | _ => none

private def wordTok : Tok → Bool
  | .ident _ => true
  | .num _ _ => true
  | _ => false

private def keyTokText : Tok → Option String
  | .ident s => some s
  | .num _ t => some t
  | .space => some " "
  | .sym c => if c == '/' || c == ',' || c == '=' then none else some (String.singleton c)
  | .ctrl _ | .group _ | .math _ _ _ | .other _ => none

/-- A key path's name in pgf's grammar, the one reader for both a definition and its use. -/
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

private def treeStyleKey (n : String) : Bool :=
  n == "level" || n == "edge from parent" || n == "every child" || n == "every child node" ||
    (match n.splitOn " " with
     | ["level", k] => !k.isEmpty && k.all Char.isDigit
     | _ => false)

private def readableKey (n : String) : Bool :=
  n == everyNodeKey || n == everyPathKey || n == everyTextKey || treeStyleKey n ||
    !n.contains ' '

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

private def tipName : List Tok → Option String
  | [.group g] => identPath (g.filter (· != .space))
  | ts => identPath ts

private def arrowTipName : List Tok → Option String
  | [.sym '-', .sym '>'] => some ">"
  | [.sym '-', t] => tipName [t]
  | _ => none

private def arrowSpec (ts : List Tok) : Option (Option String × Option String) :=
  let isDash : Tok → Bool := fun t => t == .sym '-'
  (ts.findIdx? isDash).bind fun k =>
    let pre := ts.take k
    let post := ts.drop (k + 1)
    if post.any isDash then none else
    let side (xs : List Tok) (head : Char) : Option (Option String) :=
      match xs with
      | [] => some none
      | [.sym c] => if c == head then some (some (String.singleton c)) else none
      | xs => (tipName xs).map some
    match side pre '<', side post '>' with
    | some a, some b => some (a, b)
    | _, _ => none

private inductive TipKind where
  | to
  | cmRightarrow
  | latex
  | stealthOld
  | latexMeta
  | stealth
  deriving BEq

private def tipKindOf (metaLib : Bool) : String → Option TipKind
  | ">" | "<" | "To" => some (if metaLib then .cmRightarrow else .to)
  | "to" => some .to
  | "Computer Modern Rightarrow" => some .cmRightarrow
  | "latex" => some .latex
  | "stealth" => some .stealthOld
  | "Latex" => some .latexMeta
  | "Stealth" => some .stealth
  | _ => none

private def groupNames (line : String) : List String :=
  match line.splitOn "{" with
  | _ :: rest :: _ =>
    ((rest.splitOn "}").headD "").splitOn "," |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  | _ => []

/-- The TikZ libraries a picture preamble loads, with `cd` for a load of tikz-cd. -/
public def preambleLibraries (pre : String) : List String :=
  (pre.splitOn "\n").flatMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith "\\usetikzlibrary" then groupNames line
    else if line.startsWith "\\usepackage" || line.startsWith "\\RequirePackage" then
      let pkgLine := match line.splitOn "]" with
        | [one] => one
        | _ :: rest => "]".intercalate rest
        | [] => line
      if (groupNames pkgLine).contains "tikz-cd" then ["cd"] else []
    else []

/-- Whether the preamble makes `->` arrows.meta's Computer Modern arrow: arrows.meta itself, or the
cd library. -/
public def metaArrowsOf (pre : String) : Bool :=
  (preambleLibraries pre).any fun l => l == "arrows.meta" || l == "cd"

private def drawsAsArrow (styles : List (String × Array Tok)) (n : String) : Bool :=
  (tipKindOf false n).isSome || (styles.lookup (tipKey n)).isSome

/-- Reads a `\tikzset` key list: known definitions fold into the bundles in order, every other
entry comes back unread. -/
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

/-- The bundles a document's `\tikzset` lines define, folded in source order. -/
@[expose] public def documentStyles (sets : Array (Array Tok)) : List (String × Array Tok) := Id.run do
  let mut styles : List (String × Array Tok) := []
  for keys in sets do
    styles := (readStyleList styles keys).1
  return styles

private def keyPath (toks : List Tok) : String :=
  (keyName (toks.takeWhile (· != .sym '='))).getD ""

private def engineKeyNames : List String := ["node distance"]

private def setsEngineKey (entry : Array Tok) : Bool :=
  engineKeyNames.contains (keyPath entry.toList)

private def expandOpts (styles : List (String × Array Tok)) (inner : Array Tok) :
    Array (Array Tok) := Id.run do
  let mut opts : Array (Array Tok) := #[]
  for opt in splitTop (inner.filter (· != .space)) ',' do
    match (keyName opt.toList).bind fun n => styles.lookup n with
    | some bundle => opts := opts ++ splitTop bundle ','
    | none => opts := opts.push opt
  return opts

/-- The key an option entry sets: its tokens up to the `=`. -/
public def optKey (opt : Array Tok) : String := Id.run do
  let mut s := ""
  for t in opt do
    if t == .sym '=' then break
    unless t == .space do s := s ++ tokText t
  return s

/-- The picture's inherited entries merged with a path's or node's own, dropping an inherited entry
the inner bracket sets again. -/
public def inheritOpts (outer inner : Array (Array Tok)) : Array (Array Tok) :=
  let names := inner.map optKey
  outer.filter (fun o => !names.contains (optKey o)) ++ inner

public theorem inherit_inner_exact {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner)
    (hk : ∃ e ∈ inner, optKey e = optKey o) : o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨_, hp⟩ | h
  · obtain ⟨e, he, hek⟩ := hk
    simp at hp
    exact absurd hek (hp e he)
  · exact h

public theorem inherit_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ inner) : o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append]
  exact Or.inr h

public theorem inherit_mem {outer inner : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ inheritOpts outer inner) : o ∈ outer ∨ o ∈ inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter] at hm
  rcases hm with ⟨h, _⟩ | h
  · exact Or.inl h
  · exact Or.inr h

/-- One bracket's entries under its four levels, document < picture < every X < its own, each
beating those outside it. -/
public def mergeOpts (global picture every own : Array (Array Tok)) : Array (Array Tok) :=
  inheritOpts (inheritOpts (inheritOpts global picture) every) own

public theorem merge_own_exact {global picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts global picture every own)
    (hk : ∃ e ∈ own, optKey e = optKey o) : o ∈ own :=
  inherit_inner_exact hm hk

public theorem merge_every_exact {global picture every own : Array (Array Tok)} {o : Array Tok}
    (hm : o ∈ mergeOpts global picture every own)
    (hk : ∃ e ∈ every, optKey e = optKey o)
    (ho : ¬ ∃ e ∈ own, optKey e = optKey o) : o ∈ every := by
  rcases inherit_mem hm with h | h
  · exact inherit_inner_exact h hk
  · exact absurd ⟨o, h, rfl⟩ ho

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

public theorem merge_covers {global picture every own : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ own) : o ∈ mergeOpts global picture every own :=
  inherit_covers h

public theorem inherit_outer_covers {outer inner : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ outer) (hk : ∀ e ∈ inner, optKey e ≠ optKey o) :
    o ∈ inheritOpts outer inner := by
  simp only [inheritOpts, Array.mem_append, Array.mem_filter]
  refine Or.inl ⟨h, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Array.contains_eq_mem,
    decide_eq_false_iff_not, Array.mem_map, not_exists, not_and]
  exact fun e he => hk e he

public theorem merge_picture_covers {global picture every own : Array (Array Tok)}
    {o : Array Tok}
    (h : o ∈ picture) (he : ∀ e ∈ every, optKey e ≠ optKey o)
    (ho : ∀ e ∈ own, optKey e ≠ optKey o) :
    o ∈ mergeOpts global picture every own :=
  inherit_outer_covers (inherit_outer_covers (inherit_covers h) he) ho

public theorem merge_global_covers {global picture every own : Array (Array Tok)}
    {o : Array Tok}
    (h : o ∈ global) (hp : ∀ e ∈ picture, optKey e ≠ optKey o)
    (he : ∀ e ∈ every, optKey e ≠ optKey o)
    (ho : ∀ e ∈ own, optKey e ≠ optKey o) :
    o ∈ mergeOpts global picture every own :=
  inherit_outer_covers (inherit_outer_covers (inherit_outer_covers h hp) he) ho

private def optName (opt : List Tok) : String :=
  let key := keyPath opt
  if key.isEmpty then (opt.head?.map tokText).getD "an empty option" else s!"'{key}'"

private def outsideOpt (opt : List Tok) : PDiag :=
  (.W0334, s!"picture option {optName opt} is outside the \
rendered picture subset; the option is dropped")

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
    | .num m _ =>
      match pct m with
      | .ok p => s := s ++ p
      | .error e => return .error e
    | .ctrl n =>
      match env.lookup n with
      | some (.num m _) =>
        match pct m with
        | .ok p => s := s ++ p
        | .error e => return .error e
      | some (.str v) => s := s ++ v
      | some (.len _ _) => return .error s!"the length '\\{n}' in a colour"
      | none => return .error s!"unknown macro '\\{n}' in a colour"
    | t => return .error s!"{tokText t} in a colour"
  match cx.pal.resolve s with
  | some c => return .ok c
  | none => return .error s!"colour '{s}' does not resolve against the palette"

private def readCoordBody (toks : Array Tok) (i : Nat) :
    Except String (Array Tok × Nat) := Id.run do
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
  return .ok (inner, j + 1)

private def readCoord (toks : Array Tok) (i : Nat) :
    Except String ((Array Tok × Array Tok) × Nat) := do
  let (inner, next) ← readCoordBody toks i
  match (splitTop inner ',').toList with
  | [xs, ys] => return ((xs, ys), next)
  | _ => throw "a coordinate needs exactly 'x, y'"

/-- Integer square root of an `Int` (callers pass sums of squares). -/
public def isqrt (n : Int) : Int := (Nat.sqrt n.toNat : Nat)

/-- Where the ray from a rectangle's centre toward `(qx, qy)` crosses its border (pgf's
`\pgfpointshapeborder`); the centre for no direction. -/
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

private theorem ediv_le_of_le_mul {x c q : Int} (hc : 0 < c) (h : x ≤ c * q) :
    x / c ≤ q := by
  have h2 := Int.ediv_le_ediv hc h
  rwa [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hc)] at h2

private theorem le_ediv_of_mul_le {x c q : Int} (hc : 0 < c) (h : c * q ≤ x) :
    q ≤ x / c := by
  have h2 := Int.ediv_le_ediv hc h
  rwa [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hc)] at h2

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

/-- Where the ray from a circle's centre toward `(qx, qy)` meets its border; the centre for no direction. -/
public def circleBorder (cx cy r qx qy : Int) : Int × Int :=
  let dx := qx - cx
  let dy := qy - cy
  let n := isqrt (dx * dx + dy * dy)
  if n = 0 then (cx, cy)
  else (cx + r * dx / n, cy + r * dy / n)

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

/-- Where the ray from an ellipse's centre toward `q` meets it (pgf's `\pgfpointborderellipse`). -/
public def ellipseBorder (cx cy a b qx qy : Int) : Int × Int :=
  let dx := qx - cx
  let dy := qy - cy
  let n := isqrt ((dx * b) * (dx * b) + (dy * a) * (dy * a))
  if n == 0 then (cx, cy) else (cx + dx * a * b / n, cy + dy * a * b / n)

/-- Where the ray from a diamond's centre toward `q` meets its border, `|x|/a + |y|/b = 1`. -/
public def diamondBorder (cx cy a b qx qy : Int) : Int × Int :=
  let dx := qx - cx
  let dy := qy - cy
  let n : Int := (dx.natAbs : Int) * b + (dy.natAbs : Int) * a
  if n == 0 then (cx, cy) else (cx + dx * a * b / n, cy + dy * a * b / n)

public theorem diamondBorder_axis_exact (cx cy a b d : Int) (hb : 0 < b) (hd : 0 < d) :
    diamondBorder cx cy a b (cx + d) cy = (cx + a, cy) := by
  have hx : cx + d - cx = d := by omega
  have hy : cy - cy = 0 := by omega
  have habs : ((d.natAbs : Nat) : Int) = d := Int.natAbs_of_nonneg (by omega)
  have hne : d * b ≠ 0 := by
    have := Int.mul_pos hd hb
    omega
  have hq : d * a * b / (d * b) = a := by
    rw [Int.mul_comm d a, Int.mul_assoc]
    exact Int.mul_ediv_cancel a hne
  unfold diamondBorder
  simp only [hx, hy, habs, Int.natAbs_zero, Int.natCast_zero, Int.zero_mul, Int.add_zero]
  have hb0 : (d * b == 0) = false := by simpa using hne
  simp only [hb0, Bool.false_eq_true, ↓reduceIte, hq, Int.zero_ediv, Int.add_zero]

/-- `inner sep`'s default in ten-thousandths of an em: pgf's `0.3333em` (TikZ manual §17.2.2). -/
private def innerSepDefault : Int := 3333

/-- One inner sep at this em. -/
public def innerSep (em : Sp) : Sp := em * innerSepDefault / 10000

/-- A node's shape: pgf's `rectangle` and `circle`, and `shapes.geometric`'s `ellipse` and
default-aspect `diamond`. -/
public inductive NodeShape where
  | rectangle
  | circle
  | ellipse
  | diamond
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A drawn node's outline as pgf draws it, centred on the text box: its shape circumscribing the
text box padded by the inner seps, or the minimum size where larger. -/
public def nodeOutline (shape : NodeShape) (minW minH sy textHalfW lo hi sepX sepY : Sp) :
    Sp × Sp × Sp :=
  let mid := sy + (lo + hi) / 2
  let tx := textHalfW + sepX
  let ty := (hi - lo) / 2 + sepY
  match shape with
  | .rectangle => (mid, max minW (2 * tx), max minH (2 * ty))
  | .circle =>
    let d := max (max minW minH) (2 * isqrt (tx * tx + ty * ty))
    (mid, d, d)
  -- An ellipse's radii: the half extents one inner sep out, times pgf's 1.4142136 (`\radius`).
  | .ellipse =>
    (mid, max minW (2 * (tx * 14142136 / 10000000)), max minH (2 * (ty * 14142136 / 10000000)))
  -- A default-aspect diamond reaches the sum of the half extents on both axes (`\outernortheast`).
  | .diamond => (mid, max minW (2 * (tx + ty)), max minH (2 * (tx + ty)))

public theorem nodeOutline_covers (minW minH sy textHalfW lo hi sepX sepY : Int) :
    (nodeOutline .rectangle minW minH sy textHalfW lo hi sepX sepY).1 = sy + (lo + hi) / 2 ∧
      2 * (textHalfW + sepX) ≤ (nodeOutline .rectangle minW minH sy textHalfW lo hi sepX sepY).2.1 ∧
      2 * ((hi - lo) / 2 + sepY) ≤ (nodeOutline .rectangle minW minH sy textHalfW lo hi sepX sepY).2.2 ∧
      minW ≤ (nodeOutline .rectangle minW minH sy textHalfW lo hi sepX sepY).2.1 ∧
      minH ≤ (nodeOutline .rectangle minW minH sy textHalfW lo hi sepX sepY).2.2 := by
  simp only [nodeOutline, true_and]
  have step : ∀ mW mH t u : Int, 2 * t ≤ max mW (2 * t) ∧ 2 * u ≤ max mH (2 * u) ∧
      mW ≤ max mW (2 * t) ∧ mH ≤ max mH (2 * u) := by
    intros; omega
  exact step minW minH (textHalfW + sepX) ((hi - lo) / 2 + sepY)

/-- Where pgf seats a node's text box, centred on the node: its baseline and lower and upper
edges, relative to the node. -/
public def textSeat (ht dp : Sp) : Sp × Sp × Sp :=
  let b := -((ht - dp) / 2)
  (b, b - dp, b + ht)

public theorem nodeOutline_seat_exact (shape : NodeShape) (minW minH sy textHalfW ht dp sepX sepY : Int) :
    (nodeOutline shape minW minH sy textHalfW (textSeat ht dp).2.1 (textSeat ht dp).2.2
      sepX sepY).1 = sy := by
  have step : ∀ s h d : Int, s + ((-((h - d) / 2) - d) + (-((h - d) / 2) + h)) / 2 = s := by
    intro s h d; omega
  cases shape <;> exact step sy ht dp

/-- A node's border half-extent: its text plus one inner sep, or the declared minimum where larger
(TikZ manual §17.2.2). -/
public def borderHalf (decl ink sep : Sp) : Sp := max decl (ink + sep)

public theorem borderHalf_between (decl ink sep : Sp) (hd : decl ≤ ink + sep)
    (hs : 0 < sep) : ink < borderHalf decl ink sep ∧ borderHalf decl ink sep ≤ ink + sep := by
  have step : ∀ d i s : Int, d ≤ i + s → 0 < s → i < max d (i + s) ∧ max d (i + s) ≤ i + s := by
    intro d i s h1 h2; omega
  exact step decl ink sep hd hs

/-- A named node's anchoring geometry: centre, border half-extents and shape. -/
public structure NodeGeom where
  x : Sp
  y : Sp
  a : Sp := 0
  b : Sp := 0
  shape : NodeShape := .rectangle
  /-- Where the node's own text baseline stands, which the `base` anchors read. -/
  base : Sp := 0
  deriving Repr, BEq, Inhabited

/-- A named anchor on a node's border: the `rectangle` shape's own `\anchor` declarations, the
`mid` family aside. -/
public inductive NodeAnchor where
  | center
  | north | south | east | west
  | northEast | northWest | southEast | southWest
  | base | baseEast | baseWest
  deriving Repr, BEq, Inhabited

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

/-- Milli cosine of 45°, where a circle's corner anchors stand. -/
private def diag45 : Int := 707

/-- The horizontal reach of a corner anchor: a rectangle's border, 0.707 of a circle's or
ellipse's radius, a diamond's mid-side. -/
public def NodeGeom.cornerA (g : NodeGeom) : Sp :=
  match g.shape with
  | .rectangle => g.a
  | .circle | .ellipse => g.a * diag45 / 1000
  | .diamond => g.a / 2

/-- The vertical reach of a corner anchor. -/
public def NodeGeom.cornerB (g : NodeGeom) : Sp :=
  match g.shape with
  | .rectangle => g.b
  | .circle | .ellipse => g.b * diag45 / 1000
  | .diamond => g.b / 2

/-- The baseline the `base` anchors stand on, held inside the node's own extent. -/
public def NodeGeom.baseY (g : NodeGeom) : Sp :=
  max (g.y - g.b) (min (g.y + g.b) g.base)

/-- Where a named anchor stands, from the centre and the half-extents the node registered. -/
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

public theorem anchorPoint_corners_exact (g : NodeGeom) (h : g.shape = .rectangle) :
    g.anchorPoint .northEast = ((g.anchorPoint .east).1, (g.anchorPoint .north).2) ∧
    g.anchorPoint .northWest = ((g.anchorPoint .west).1, (g.anchorPoint .north).2) ∧
    g.anchorPoint .southEast = ((g.anchorPoint .east).1, (g.anchorPoint .south).2) ∧
    g.anchorPoint .southWest = ((g.anchorPoint .west).1, (g.anchorPoint .south).2) := by
  have ca : g.cornerA = g.a := by simp [NodeGeom.cornerA, h]
  have cb : g.cornerB = g.b := by simp [NodeGeom.cornerB, h]
  simp only [NodeGeom.anchorPoint, ca, cb, and_self]

public theorem anchorPoint_opposite_exact (g : NodeGeom) :
    (g.anchorPoint .east).1 - g.x = g.x - (g.anchorPoint .west).1 ∧
    (g.anchorPoint .north).2 - g.y = g.y - (g.anchorPoint .south).2 ∧
    (g.anchorPoint .center) = (g.x, g.y) := by
  have flip : ∀ v d : Int, v + d - v = v - (v - d) := by intro v d; omega
  exact ⟨flip g.x g.a, flip g.y g.b, rfl⟩

public theorem anchorPoint_between (g : NodeGeom) (ha : 0 ≤ g.a) (hb : 0 ≤ g.b)
    (an : NodeAnchor) :
    Gfx.Box.le (g.anchorPoint an, g.anchorPoint an)
      (Ir.Pic.nodeExtentBox g.x g.y g.a g.b) := by
  have key : ∀ p : Sp × Sp, g.x - g.a ≤ p.1 → p.1 ≤ g.x + g.a →
      g.y - g.b ≤ p.2 → p.2 ≤ g.y + g.b →
      Gfx.Box.le ((p, p)) (Ir.Pic.nodeExtentBox g.x g.y g.a g.b) :=
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
  have hf : ∀ d : Int, 0 ≤ d → 0 ≤ d / 2 ∧ d / 2 ≤ d := by
    intro d h; omega
  have hca : 0 ≤ g.cornerA ∧ g.cornerA ≤ g.a := by
    unfold NodeGeom.cornerA diag45
    cases g.shape with
    | rectangle => exact ⟨ha, Int.le_refl _⟩
    | circle => exact dg g.a ha
    | ellipse => exact dg g.a ha
    | diamond => exact hf g.a ha
  have hcb : 0 ≤ g.cornerB ∧ g.cornerB ≤ g.b := by
    unfold NodeGeom.cornerB diag45
    cases g.shape with
    | rectangle => exact ⟨hb, Int.le_refl _⟩
    | circle => exact dg g.b hb
    | ellipse => exact dg g.b hb
    | diamond => exact hf g.b hb
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

private def splitAnchor (s : String) : Option (String × String) :=
  match s.splitOn "." with
  | [nm, an] => if nm.isEmpty || an.isEmpty then none else some (nm, an)
  | _ => none

/-- A `label=` or `pin=` node placed against another once it stands (TikZ manual §17.10). -/
public structure After where
  main : NodeGeom
  pin : Bool
  spec : List Tok
  dist : Option Sp
  deriving Repr, Inhabited

/-- Shapes and named losses accumulated across the unrolled walk, each diagnostic once. -/
public structure Ev where
  shapes : Array Ir.Pic.Shape := #[]
  diags : Array PDiag := #[]
  /-- The box a `\useasboundingbox` declared (`Ir.Pic.Picture.declared`). -/
  declared : Option Ir.Pic.Box := none
  /-- The boxes the picture's bounds read: each placed node's border, and a clip's hull in place of
  what it clips. -/
  borders : Array Ir.Pic.Box := #[]
  /-- Named nodes so far, latest first, which a path endpoint resolves against. -/
  nodes : List (String × NodeGeom) := []
  /-- Whether some path or node read the picture's inherited options. -/
  readOpts : Bool := false
  /-- Whether a construct the subset could not reach swallowed declarations. -/
  gapped : Bool := false
  /-- How many nodes this run could not place, their `at` or relative target not yet resolved. -/
  deferred : Nat := 0
  /-- The clip the statement just evaluated set, applied to what follows in its scope. -/
  clipGeom : Option Gfx.Geom := none
  /-- The labels and pins the node just evaluated asked for. -/
  after : Array After := #[]

private def Ev.diag (ev : Ev) (d : PDiag) : Ev :=
  if ev.diags.any (·.2 == d.2) then ev else { ev with diags := ev.diags.push d }

/-- The evaluated marks and authored bounds both backends read. -/
public def Ev.toPicture (ev : Ev) (baseline : Option Sp := none) : Ir.Pic.Picture :=
  { shapes := ev.shapes, declared := ev.declared, borders := ev.borders, baseline }

/-- A placed node's name into the table and, unless it is a coordinate, its border into the
picture's box. -/
public def Ev.place (ev : Ev) (coordinate : Bool) (border : Ir.Pic.Box)
    (nodes : List (String × NodeGeom)) : Ev :=
  if coordinate then { ev with nodes } else { ev with borders := ev.borders.push border, nodes }

public theorem coordinate_exact (ev : Ev) (border : Ir.Pic.Box)
    (nodes : List (String × NodeGeom)) :
    (ev.place true border nodes).nodes = nodes ∧ (ev.place true border nodes).borders = ev.borders ∧
      (ev.place false border nodes).borders = ev.borders.push border := ⟨rfl, rfl, rfl⟩

public theorem Ev.labelExtent_covers (ev : Ev) (m : Ir.Pic.LabelMetric)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (baseline : Option Sp)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ ev.shapes)
    (hd : ev.declared = none) :
    Gfx.Box.le (Ir.Pic.labelTextBox x y align (m content scale))
      ((ev.toPicture baseline).box m) := by
  have cover := (Ir.Pic.Picture.box_covers (ev.toPicture baseline) m hd).1 _ hs
  apply Gfx.Box.le_trans (b := Ir.Pic.labelGlyphBox x y align (m content scale)) _ cover
  exact ⟨Int.le_refl _, Int.min_le_right _ _, Int.le_refl _, Int.le_max_right _ _⟩

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
  let vals ← match evalComp env x1s, evalComp env y1s, evalComp env x2s, evalComp env y2s with
    | .ok a, .ok b, .ok c, .ok d => pure (a, b, c, d)
    | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e =>
      return .error (.E0333, s!"in {what}, {e}; {cost}")
  let (x1c, y1c, x2c, y2c) := vals
  -- A relative corner adds in the unit it was written in, so two unitless components round once.
  let addComp (a b : Int × Bool) : Sp :=
    if !a.2 && !b.2 then cx.toSp (a.1 + b.1) else cx.compSp a + cx.compSp b
  let (x1, y1) := (cx.compSp x1c, cx.compSp y1c)
  let (x2, y2) := if relative then (addComp x1c x2c, addComp y1c y2c)
    else (cx.compSp x2c, cx.compSp y2c)
  let cs := #[cx.place x1 y1, cx.place x2 y1, cx.place x2 y2, cx.place x1 y2]
  let xs := cs.map (·.1)
  let ys := cs.map (·.2)
  let x0 := xs.foldl min (xs[0]?.getD 0)
  let y0 := ys.foldl min (ys[0]?.getD 0)
  return .ok (x0, y0, xs.foldl max (xs[0]?.getD 0), ys.foldl max (ys[0]?.getD 0))

private def fillIsRect (toks : Array Tok) : Bool := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  if ts[0]? == some (.sym '[') then
    match ts.toList.findIdx? (· == .sym ']') with
    | some j => i := j + 1
    | none => return true
  match readCoordBody ts i with
  | .error _ => return true
  | .ok (_, i1) =>
    unless ts[i1]? == some (.ident "rectangle") do return false
    let i2 := if ts[i1 + 1]? == some (.sym '+') && ts[i1 + 2]? == some (.sym '+') then i1 + 3
      else i1 + 1
    match readCoordBody ts i2 with
    | .error _ => return true
    | .ok (_, i3) => return i3 == ts.size

private def evalFill (cx : Cx) (env : List (String × Val)) (toks : Array Tok) :
    Except PDiag Ir.Pic.Shape := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut color := cx.ink
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

private def evalBBox (cx : Cx) (env : List (String × Val)) (toks : Array Tok) :
    Except PDiag Ir.Pic.Box := do
  let (x0, y0, x1, y1) ← readRect cx env (toks.filter (· != .space)) 0
    "'\\useasboundingbox'" "the declared box is ignored"
  return ((x0, y0), (x1, y1))

/-- One line of a node label: its content and its size per mille of the node's own. -/
public abbrev LabelLine := Array Ir.Inline × Nat

private def nodeLineLead (bodySize : Sp) (scale : Nat) : Sp :=
  Ir.leadingFor (bodySize * (scale : Int) / 1000)

/-- The placeholder a label sets when its salvage kept nothing and a loss was named. -/
public def nodeFloorPlaceholder : String := String.ofList Ir.mathFloorPlaceholder

/-- Commands whose content is invisible by definition: a phantom sets no ink, so its body reads as empty. -/
public def phantomCtrl : List String := ["vphantom", "hphantom", "phantom"]

private inductive SalMode where
  | text
  | optMaybe (then_ : Nat)
  | optDrop (then_ : Nat)
  | dropArgs (n : Nat)
  | colorRole
  | colorBody (c : Ir.Color) (role : Option Ir.ColorRef)
  | styleBody (st : Ir.Style)
  deriving Repr, BEq, Inhabited

private structure Sal where
  lines : Array LabelLine := #[]
  out : Array Ir.Inline := #[]
  text : String := ""
  scale : Nat := 1000
  styles : Array Ir.Style := #[]
  consumeNocorr : Bool := false
  next : Option Tok := none
  fresh : Bool := true
  depth : Nat := 0
  trim : Bool := true
  diags : Array PDiag := #[]
  mode : SalMode := .text
  deriving Inhabited

namespace Sal

private def str (s : Sal) (t : String) : Sal :=
  if t.isEmpty then s else { s with text := s.text ++ t, fresh := false }

private def flush (s : Sal) : Sal :=
  if s.text.isEmpty then s
  else
    let xs := s.styles.foldr (fun st inner => #[.styled st inner]) #[.text s.text]
    { s with out := xs.foldl Array.push s.out, text := "" }

private def inlines (s : Sal) (xs : Array Ir.Inline) : Sal :=
  if xs.isEmpty then s
  else
    let f := s.flush
    let xs := f.styles.foldr (fun st inner => #[.styled st inner]) xs
    { f with out := xs.foldl Array.push f.out, fresh := false }

private def inline (s : Sal) (i : Ir.Inline) : Sal :=
  s.inlines #[i]

private def addDiags (s : Sal) (ds : Array PDiag) : Sal :=
  { s with diags := ds.foldl Array.push s.diags }

private def mode0 (s : Sal) : Sal := { s with mode := .text }

private def refuse (s : Sal) (what : String) : Sal :=
  { s with diags := s.diags.push (.W0334, s!"{what} in a node body is outside \
the rendered picture subset; the label sets the text it can read") }

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

private def newline (s : Sal) : Sal :=
  let s := s.flush
  { s with lines := s.lines.push (trimEnds s.trim s.trim s.out, s.scale)
           out := #[], text := "", scale := 1000, fresh := true, mode := .text }

private def sub (s : Sal) : Sal := { scale := s.scale, diags := s.diags, depth := s.depth }

private def inner (s : Sal) : Sal := { s.sub with depth := s.depth + 1, trim := false }

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

private def inkCount (ls : Array LabelLine) : Nat := ls.foldl (fun n l => n + l.1.size) 0

private def inked (ls : Array LabelLine) : Bool := 0 < inkCount ls

private def settled : SalMode → Bool
  | .text => true
  | .optMaybe k => k == 0
  | .optDrop _ | .dropArgs _ | .colorRole | .colorBody _ _ | .styleBody _ => false

private def settle (t : Tok) (s : Sal) : Sal :=
  match s.mode, t with
  -- A starred command's star is part of its name, and a space before an argument is the command's.
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
  | .styleBody _, .space => s
  | .styleBody _, .group _ => s
  | .styleBody _, .ident _ => s
  | .styleBody _, .num _ _ => s
  | .styleBody _, .sym _ => s
  | .styleBody _, _ => (s.refuse "a text style whose argument is not a group").mode0
  | .text, _ => s

end Sal

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

private def locatedAt (site : Option Span) (inl : Ir.Inline) : Ir.Inline :=
  match site with
  | some span => .located span #[inl]
  | none => inl

private theorem locatedAt_text (site : Option Span) :
    Ir.Conserves Ir.plainTextOne (locatedAt site) := by
  intro inl
  unfold locatedAt
  split <;> simp [Ir.plainTextOne, Ir.plainTextList]

private def fontCmdEdges (body : List Tok) (next? : Option Tok) : Bool × Bool :=
  Ir.fontCmdEdges (· == .space) fontCmdNocorr
    (fun
      | some (.sym ',') | some (.sym '.') => false
      | _ => true)
    body next?

mutual

private def salList (cx : Cx) (env : List (String × Val)) : List Tok → Sal → Sal
  | [], s => s
  | t :: rest, s => salList cx env rest (salOne cx env t { s with next := rest.head? })

private def salOne (cx : Cx) (env : List (String × Val)) (t : Tok) (s : Sal) : Sal :=
  let s : Sal := Sal.settle t (Sal.settle t s)
  match s.mode with
  | .optMaybe k => if t == .sym '[' then { s with mode := .optDrop k } else s
  | .optDrop k => if t == .sym ']' then { s with mode := .optMaybe k } else s
  | .dropArgs n => { s with mode := .optMaybe (if n ≤ 1 then 0 else n - 1) }
  | .colorRole =>
    match t with
    | .group g =>
      match evalColor cx env g.toArray with
      | .ok c =>
        let role : Option Ir.ColorRef := match g.filter (· != .space) with
          | [.ident w] => cx.pal.refOf? w
          | _ => none
        { s with mode := .colorBody c role }
      | .error e => { (s.refuse s!"the colour ({e})") with mode := .text }
    | _ => s
  | .colorBody c role =>
    match t with
    | .group g => s.splice (salList cx env g s.inner) fun _ _ xs => #[.colored c role xs]
    | _ => s
  | .styleBody st =>
    let add (s : Sal) (raw : List Tok) (inner : Array Ir.Inline) : Sal :=
      { (s.inlines (Ir.fontCmdInlines st (fontCmdEdges raw s.next) inner)) with mode := .text }
    match t with
    | .group g =>
      let edges := fontCmdEdges g s.next
      s.splice (salList cx env g { s.inner with consumeNocorr := true }) fun first last xs =>
        Ir.fontCmdInlines st (edges.1 && first, edges.2 && last) xs
    | .ident w => add s [.ident w] #[.text w]
    | .num m t => add s [.num m t] #[.text t]
    | .sym c => add s [.sym c] #[.text (String.singleton c)]
    | _ => s
  | .text =>
    match t with
    | .ident w => s.str w
    | .num _ t => s.str t
    | .space => s.str " "
    | .sym c => s.str (String.singleton c)
    -- A group's content joins the line and its styles end with it; a size switch inside one is refused.
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
    | .math d body site =>
      let (inl, ds) := cx.math d body.toArray
      (s.inline (locatedAt site inl)).addDiags ds
    | .other what => s.refuse what
    | .ctrl n => salCtrl cx env n s

end

/-- The lines a label ships: its salvage, or the placeholder when it kept nothing and a loss was named. -/
public def labelFloor (lines : Array LabelLine) (named : Bool) : Array LabelLine :=
  if Sal.inked lines || !named then lines
  else #[(#[.text nodeFloorPlaceholder], 1000)]

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

/-- A node body's label lines: what the subset can read of it, a construct it cannot draw named
and its words kept. -/
public def nodeLabel (cx : Cx) (env : List (String × Val)) (toks : List Tok) :
    Array LabelLine × Array PDiag :=
  let walked := salList cx env toks {}
  let s := if Sal.settled walked.mode then walked
           else walked.refuse "a node body that ends mid-construct"
  let s := s.newline
  (labelFloor s.lines (!s.diags.isEmpty), s.diags)

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
    (role : Option Ir.ColorRef) (xs : Array Ir.Inline) :
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

/-- A literal source token before any salvage decision, a number as it was spelled. -/
public inductive LabelLiteral where
  | word (text : String)
  | number (text : String)
  | symbol (char : Char)
  | space
  deriving Repr, BEq

public def LabelLiteral.text : LabelLiteral → String
  | .word s => s
  | .number t => t
  | .symbol c => String.singleton c
  | .space => " "

/-- An independently enumerable input to a node label: a literal, a substitution, or a math input. -/
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

/-- The label's source census: groups flattened and declared substitutions resolved, reading no salvage state. -/
public def labelInputList (env : List (String × Val)) (acc : Array LabelInput) :
    List Tok → Array LabelInput
  | [] => acc
  | t :: rest => labelInputList env (labelInputOne env acc t) rest

public def labelInputOne (env : List (String × Val)) (acc : Array LabelInput) :
    Tok → Array LabelInput
  | .ident w => acc.push (.literal (.word w))
  | .num _ t => acc.push (.literal (.number t))
  | .sym c => acc.push (.literal (.symbol c))
  | .space => acc.push (.literal .space)
  | .ctrl n => match env.lookup n with
    | some v => acc.push (.substitution n v)
    | none => acc
  | .group ts => labelInputList env acc ts
  | .math d ts _ => acc.push (.math d ts)
  | .other _ => acc

end

mutual

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

/-- The characters a label's sources could contribute, a bound on what the salvage keeps. -/
public def labelSources (cx : Cx) (env : List (String × Val)) (ts : List Tok) : String :=
  labelInputText cx (labelInputList env #[] ts)

public def labelSource (cx : Cx) (env : List (String × Val)) (t : Tok) : String :=
  labelInputText cx (labelInputOne env #[] t)

public theorem labelSource_exact (cx : Cx) (env : List (String × Val)) (t : Tok) :
    labelSource cx env t = match t with
      | .ident w => w
      | .num _ t => t
      | .sym c => String.singleton c
      | .space => " "
      | .ctrl n => match env.lookup n with
        | some v => v.text
        | none => ""
      | .group ts => labelSources cx env ts
      | .math d ts _ => Ir.plainTextOne (cx.math d ts.toArray).1
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

/-- Which origins a label character may have: its sources, or the placeholder when the run names a loss. -/
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
    | num m t =>
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
    | num m t => exact Sal.str_from P _ _ hs ht
    | space => exact Sal.str_from P _ _ hs ht
    | sym c => exact Sal.str_from P _ _ hs ht
    | group g =>
      have hi := salList_from P cx env g
        { settled with depth := settled.depth + 1, consumeNocorr := false, mode := .text } hs ht
      dsimp only
      split
      · exact hi
      · exact Sal.flush_from P _ hi
    | math d body _ =>
      exact Sal.inline_from P _ _ hs (by rw [locatedAt_text _ _]; exact ht)
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

/-- A label's lines as shapes, one per line, `nodeLineLead` apart and centred on the anchor; an
empty line ships none. -/
public def stackLabels (x y : Sp) (bodySize : Sp) (scale : Nat) (color : Ir.Color)
    (align : Ir.Pic.LabelAlign) (lines : Array LabelLine)
    (acc : Array Ir.Pic.Shape) : Array Ir.Pic.Shape := Id.run do
  -- Each gap is the leading of the line below it, so a smaller second line sits closer.
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

private def readDim (toks : List Tok) : Except String Sp :=
  match toks with
  | [.num m _, .ident u] =>
    match u with
    | "mm" => .ok (m * Dim.mm 10 / 10000)
    | "cm" => .ok (m * Dim.mm 10 / 1000)
    | "pt" => .ok (m * Dim.pt 1 / 1000)
    | "in" => .ok (m * Dim.inch 1 / 1000)
    | u => .error s!"the unit '{u}' is outside the rendered picture subset"
  | _ => .error "a length like '8mm' is needed"

private def readNodeDim (em ex : Sp) (toks : List Tok) : Except String Sp :=
  match toks with
  | [.num m _, .ident "em"] => .ok (m * em / 1000)
  | [.num m _, .ident "ex"] => .ok (m * ex / 1000)
  | ts => readDim ts

private def lineWidthStyles : List (String × Sp) :=
  [("ultra thin", Dim.pt 1 / 10), ("very thin", Dim.pt 1 / 5),
   ("thin", Ir.Pic.thinWidth), ("semithick", Dim.pt 3 / 5),
   ("thick", Ir.Pic.thickWidth), ("very thick", Dim.pt 6 / 5),
   ("ultra thick", Dim.pt 8 / 5)]

private def readLineWidth (opt : List Tok) : Option (Except String Sp) :=
  match opt with
  | .ident "line" :: .ident "width" :: .sym '=' :: rest => some (readDim rest)
  | ts => ((keyName ts).bind fun n => lineWidthStyles.lookup n).map .ok

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

private def fontLines (sts : Array Ir.Style) (lines : Array LabelLine) : Array LabelLine :=
  if sts.isEmpty then lines
  else lines.map fun (xs, rel) =>
    (if xs.isEmpty then xs else sts.foldr (fun st inner => #[.styled st inner]) xs, rel)

private def textAlignOf : List Tok → Option Ir.Pic.LabelAlign
  | [.ident "left"] | [.ident "flush", .ident "left"] => some .west
  | [.ident "right"] | [.ident "flush", .ident "right"] => some .east
  | [.ident "center"] | [.ident "flush", .ident "center"] => some .center
  | _ => none

private def alignLabels (m : Ir.Pic.LabelMetric) (al : Ir.Pic.LabelAlign)
    (ls : Array Ir.Pic.Shape) : Array Ir.Pic.Shape :=
  let w := ls.foldl (fun w s => match s with
    | .label _ _ content _ sz a => if a == .center then max w (m content sz).w else w
    | .ink _ => w) 0
  ls.map fun s => match s with
    | .label x y c col sz a =>
      if a != .center then s
      else if al == .west then .label (x - w / 2) y c col sz .west
      else if al == .east then .label (x + w / 2) y c col sz .east
      else s
    | .ink _ => s

/-- A relative placement's direction: the four sides and four corners of the `positioning` keys. -/
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

/-- The centre-to-centre offset a direction puts between the placed node and the one it names. -/
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

/-- The anchor a bare direction key stands on the coordinate, and the shift a length after it
gives (TikZ manual §17.5.2). -/
public def dirAnchor (d : Dir) (len : Sp) : NodeAnchor × (Sp × Sp) :=
  match d with
  | .above => (.south, (0, len))
  | .below => (.north, (0, -len))
  | .left => (.east, (-len, 0))
  | .right => (.west, (len, 0))
  | .aboveLeft => (.southEast, (-len, len))
  | .aboveRight => (.southWest, (len, len))
  | .belowLeft => (.northEast, (-len, -len))
  | .belowRight => (.northWest, (len, -len))

/-- A node's placement once its coordinates and options are read: absolute, or relative to one named geometry. -/
public inductive NodePlacement where
  | absolute (x y : Sp)
  | relative (dir : Dir) (target : String) (sep : Sp × Sp)
  deriving Repr, Inhabited

public def NodePlacement.target : NodePlacement → Option String
  | .absolute .. => none
  | .relative _ name _ => some name

/-- The centre from the declared gap and both nodes' extents; a failure carries the missing name. -/
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

/-- A measured node and its optional name, before placement. -/
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

/-- Resolves once, then registers that geometry under the node's name, if any. -/
public def NodePlan.run (p : NodePlan) (nodes : List (String × NodeGeom)) :
    Except String NodeGeom × List (String × NodeGeom) :=
  let resolved := p.resolve nodes
  (resolved, p.register resolved.toOption nodes)

/-- Two placements are independent when their writes are distinct and neither reads the other's. -/
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

public theorem NodePlan.place_order_agree (p q : NodePlan) (nodes : List (String × NodeGeom))
    (h : p.Independent q) (name : String) :
    (q.run (p.run nodes).2).2.lookup name =
      (p.run (q.run nodes).2).2.lookup name := by
  simp only [NodePlan.run]
  rw [NodePlan.resolve_register _ _ _ _ h.2.1,
      NodePlan.resolve_register _ _ _ _ h.2.2]
  exact (NodePlan.register_order _ _ _ _ _ h.1 name).symm

public theorem NodePlan.absolute_independent (pn qn : String) (hne : pn ≠ qn)
    (px py qx qy : Sp) (pg qg : NodeGeom) :
    Independent ⟨some pn, .absolute px py, pg⟩ ⟨some qn, .absolute qx qy, qg⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hq
    exact hne ((Option.some.inj hn).trans (Option.some.inj hq).symm)
  · intro n hn; cases hn
  · intro n hn; cases hn

/-- TikZ's `auto` anchor direction, ignoring tangent components within ±.05 (tikz.code.tex). -/
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

public theorem autoDir_swap_exact (left : Bool) (dx dy : Sp) :
    autoDir (!left) dx dy = autoDir left (-dx) (-dy) := by
  cases left <;> simp [autoDir]

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

public theorem offset_opposite_exact (s : Sp × Sp) :
    Dir.left.offset s = (-(Dir.right.offset s).1, (Dir.right.offset s).2) ∧
      Dir.above.offset s = ((Dir.below.offset s).1, -(Dir.below.offset s).2) := by
  simp [Dir.offset]

public theorem offset_corners_exact (s : Sp × Sp) :
    Dir.aboveLeft.offset s = ((Dir.left.offset s).1, (Dir.above.offset s).2) ∧
      Dir.aboveRight.offset s = ((Dir.right.offset s).1, (Dir.above.offset s).2) ∧
      Dir.belowLeft.offset s = ((Dir.left.offset s).1, (Dir.below.offset s).2) ∧
      Dir.belowRight.offset s = ((Dir.right.offset s).1, (Dir.below.offset s).2) := by
  simp [Dir.offset]

public theorem offset_mem (d : Dir) (s : Sp × Sp) :
    ((d.offset s).1 = 0 ∨ (d.offset s).1 = s.2 ∨ (d.offset s).1 = -s.2) ∧
      ((d.offset s).2 = 0 ∨ (d.offset s).2 = s.1 ∨ (d.offset s).2 = -s.1) := by
  cases d <;> simp [Dir.offset]

private def nameOfToks (ts : List Tok) : Option String :=
  let s := ts.foldl (fun acc t => acc ++ (match t with
    | .ident n => n
    | .num _ t => t
    | .sym c => String.singleton c
    | _ => "")) ""
  if s.isEmpty then none else some s

private def readPlace (dist : Sp × Sp) (toks : List Tok) :
    Option (Dir × String × (Sp × Sp)) := do
  let path := keyPath toks
  let rest := (toks.dropWhile (· != .sym '=')).drop 1
  let words := path.splitOn " "
  if words.getLast? == some "of" then
    let dir ← dirOf (String.intercalate " " words.dropLast)
    let nm ← nameOfToks rest
    return (dir, nm, dist)
  let dir ← dirOf path
  match rest with
  | .ident "of" :: tail => (nameOfToks tail).map fun nm => (dir, nm, dist)
  | .num m t :: .ident u :: .ident "of" :: tail => do
    let own ← (readDim [.num m t, .ident u]).toOption
    let nm ← nameOfToks tail
    some (dir, nm, (own, own))
  | _ => none

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

private def toKeyNames : List String :=
  ["out", "in", "bend left", "bend right", "bend angle", "relative", "looseness",
   "out looseness", "in looseness"]

private def readsPathOpt (styles : List (String × Array Tok)) (opt : Array Tok) : Bool :=
  match arrowSpec opt.toList with
  | some (a, b) => a.all (drawsAsArrow styles) && b.all (drawsAsArrow styles)
  | none =>
    match opt.toList with
    | .sym '>' :: .sym '=' :: rest =>
      match tipName rest with
      | some tip => drawsAsArrow styles tip
      | none => false
    | ts => ["draw", "dashed", "dotted", "densely dotted", "fill", "color",
        "auto", "swap", "'", "shorten<", "shorten>", "rounded corners", "sharp corners",
        "opacity", "fill opacity", "draw opacity", "shade", "shading", "shading angle",
        "top color", "bottom color", "left color", "right color", "middle color",
        "inner color", "outer color", "ball color", "decorate", "decoration"].contains
        (keyPath ts) ||
        toKeyNames.contains (keyPath ts) || (readLineWidth ts).isSome

private def fillBracketIsKeys (cx : Cx) (env : List (String × Val)) (toks : Array Tok) : Bool :=
  let ts := toks.filter (· != .space)
  if ts[0]? != some (.sym '[') then false else
  match ts.toList.findIdx? (· == .sym ']') with
  | none => false
  | some j =>
    let inner := ts.extract 1 j
    inner.contains (.sym '=') || inner.contains (.sym ',') ||
      ((evalColor cx env inner) matches .error _ && readsPathOpt cx.styles inner)

private def readsNodeOpt (opt : Array Tok) : Bool :=
  if (readPlace (0, 0) opt.toList).isSome then true
  else match opt.toList with
  | ts => ["circle", "rectangle", "ellipse", "diamond", "shape", "label", "pin",
      "label distance", "pin distance", "fit", "draw", "dashed", "dotted", "densely dotted",
      "text", "fill", "minimum size", "minimum width", "minimum height",
      "inner sep", "inner xsep", "inner ysep", "outer sep", "outer xsep", "outer ysep",
      "node contents", "font", "text height", "text depth", "align", "anchor"].contains
        (keyPath ts) ||
      (dirOf (keyPath ts)).isSome || (readLineWidth ts).isSome

private def treeKeyNames : List String :=
  ["grow", "grow'", "level distance", "sibling distance", "parent anchor", "child anchor",
   "missing"]

/-- Whether some statement of this subset reads an entry, which an outer declaration then carries in. -/
public def readsOpt (styles : List (String × Array Tok)) (opt : Array Tok) : Bool :=
  readsPathOpt styles opt || readsNodeOpt opt || treeKeyNames.contains (keyPath opt.toList)

/-- The two outer brackets as the shape at hand reads them. -/
public def outerRead (reads : Array Tok → Bool) (global picture : Array (Array Tok)) :
    Array (Array Tok) × Array (Array Tok) :=
  (global.filter reads, picture.filter reads)

/-- Whether an entry sets a width, which every picture resets to pgf's 0.4 pt (`\pgf@picture`). -/
public def pictureResets (o : Array Tok) : Bool := (readLineWidth o.toList).isSome

/-- One `\tikzset` line folded into what the document has set so far, a later value replacing an
earlier one. -/
public def documentOptsStep (sa : List (String × Array Tok) × Array (Array Tok))
    (keys : Array Tok) : List (String × Array Tok) × Array (Array Tok) :=
  let (after, unread) := readStyleList sa.1 keys
  (after, inheritOpts sa.2 (unread.filter fun o => readsOpt after o && !pictureResets o))

/-- What a document's `\tikzset` lines set for every picture: read entries that are no definition
and that no picture resets. -/
public def documentOpts (sets : Array (Array Tok)) : Array (Array Tok) :=
  (sets.foldl documentOptsStep ([], #[])).2

public theorem documentOptsStep_covers {styles : List (String × Array Tok)}
    {acc : Array (Array Tok)} {keys o : Array Tok}
    (h : o ∈ (readStyleList styles keys).2)
    (hr : readsOpt (readStyleList styles keys).1 o = true)
    (hw : pictureResets o = false) :
    o ∈ (documentOptsStep (styles, acc) keys).2 := by
  simp only [documentOptsStep, inheritOpts, Array.mem_append, Array.mem_filter]
  exact Or.inr ⟨h, by simp [hr, hw]⟩

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

public theorem outerRead_covers {reads : Array Tok → Bool}
    {global picture : Array (Array Tok)} {o : Array Tok}
    (h : o ∈ global) (hr : reads o) : o ∈ (outerRead reads global picture).1 := by
  simp only [outerRead, Array.mem_filter]
  exact ⟨h, hr⟩

/-- What one `\tikzset` key list leaves unread, named at the line that wrote it. -/
public def unreadKeys (styles : List (String × Array Tok)) (keys : Array Tok) : Array String :=
  let (after, unread) := readStyleList styles keys
  (unread.filter fun e => !setsEngineKey e && !readsOpt after e).filterMap fun e =>
    (keyName ((e.toList.filter (· != .space)).takeWhile
      (fun t => !isSym '/' t))).map (fun n => s!"'{n}'")
      |>.orElse fun _ => (e[0]?).map tokText

/-- One part of a `\node` statement's prologue, read in any order and any number of times (TikZ manual §17.2). -/
public inductive Part where
  | brack (inner : Array Tok)
  | name (n : String)
  /-- `at (…)`: the coordinate's contents, read where the node is placed. -/
  | atCoord (inner : Array Tok)
  deriving Repr, Inhabited

/-- A node's prologue as read so far. -/
public structure Prologue where
  /-- Every option bracket's inner tokens, in source order. -/
  brackets : Array (Array Tok) := #[]
  name : Option String := none
  /-- The `at (…)` coordinate's contents. -/
  at? : Option (Array Tok) := none
  deriving Repr, Inhabited

/-- Folds one part in; each part touches one field. -/
public def Prologue.step (p : Prologue) : Part → Prologue
  | .brack inner => { p with brackets := p.brackets.push inner }
  | .name n => { p with name := p.name.orElse fun _ => some n }
  | .atCoord inner => { p with at? := some inner }

public theorem prologue_swap_agree (p : Prologue) (inner : Array Tok) (n : String)
    (at_ : Array Tok) :
    (p.step (.brack inner)).step (.name n) = (p.step (.name n)).step (.brack inner) ∧
    (p.step (.brack inner)).step (.atCoord at_)
      = (p.step (.atCoord at_)).step (.brack inner) ∧
    (p.step (.name n)).step (.atCoord at_)
      = (p.step (.atCoord at_)).step (.name n) := by
  exact ⟨rfl, rfl, rfl⟩

public theorem prologue_brackets_covers (p : Prologue) (part : Part) :
    (p.step part).brackets = p.brackets ∨
      ∃ inner, (p.step part).brackets = p.brackets.push inner := by
  cases part
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

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

private def readPrologue (ts : Array Tok) (i0 : Nat) : Prologue × Nat × Option PDiag := Id.run do
  let mut i := i0
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
        match readCoordBody ts (i + 1) with
        | .error e =>
          bad := some (.E0333, s!"in '\\node', {e}; the node is not drawn")
          break
        | .ok (inner, i2) =>
          pro := pro.step (.atCoord inner)
          i := i2
      else
        match readName ts i with
        | some (nm, i2) =>
          pro := pro.step (.name nm)
          i := i2
        | none => break
    else break
  return (pro, i, bad)

private def nodeNameOf (toks : Array Tok) : Option String :=
  (readPrologue (toks.filter (· != .space)) 0).1.name

-- premise: unreachedName_accounts — the flag is set only beside a named gap
/-- A name that resolved to nothing: a gap in the subset (W0334) where a construct outside it was
named, else the document's own error (E0333). -/
public def unreachedName (gapped : Bool) (what : String) (site : String := "'\\draw'")
    (cost : String := "the edge is not drawn") : PDiag :=
  if gapped then
    (.W0334, s!"{what} is declared inside a construct outside the rendered \
picture subset, so no node carries it; {cost}")
  else (.E0333, s!"in {site}, no node is named '{what}'; {cost}")

public theorem unreachedName_accounts (gapped : Bool) (what site cost : String)
    (h : (unreachedName gapped what site cost).1 = .W0334) : gapped = true := by
  cases gapped
  · simp only [unreachedName, Bool.false_eq_true] at h
    exact absurd h (by simp)
  · rfl

private inductive Anchor where
  | node (g : NodeGeom)
  | point (x y : Sp)

private def Anchor.center : Anchor → Sp × Sp
  | .node g => (g.x, g.y)
  | .point x y => (x, y)

public inductive CoordMode where
  | absolute
  | offset
  | advance
  deriving BEq

/-- A relative coordinate step (TikZ §13.4.3): `+` keeps the reference, `++` moves it; the
endpoint, then the reference. -/
public def coordStep (mode : CoordMode) (base p : Int × Int) :
    (Int × Int) × (Int × Int) :=
  match mode with
  | .absolute => (p, p)
  | .offset => ((base.1 + p.1, base.2 + p.2), base)
  | .advance =>
    let q := (base.1 + p.1, base.2 + p.2)
    (q, q)

public theorem coordStep_offset_exact (base p : Int × Int) :
    (coordStep .offset base p).1 = (base.1 + p.1, base.2 + p.2) ∧
    (coordStep .offset base p).2 = base := by
  simp [coordStep]

public theorem coordStep_advance_exact (base p q : Int × Int) :
    coordStep .advance (coordStep .advance base p).2 q =
      coordStep .advance base (p.1 + q.1, p.2 + q.2) := by
  simp [coordStep, Int.add_assoc]

/-- The corner of `|-` (x from the start, y from the end) or `-|` (TikZ §14.2). -/
public def orthogonalCorner (verticalFirst : Bool) (p q : Int × Int) : Int × Int :=
  if verticalFirst then (p.1, q.2) else (q.1, p.2)

public theorem orthogonalCorner_exact (verticalFirst : Bool) (p q : Int × Int) :
    let c := orthogonalCorner verticalFirst p q
    if verticalFirst then c.1 = p.1 ∧ c.2 = q.2
    else c.1 = q.1 ∧ c.2 = p.2 := by
  cases verticalFirst <;> simp [orthogonalCorner]

private def anchorBody (cx : Cx) (env : List (String × Val)) (ev : Ev)
    (inner : Array Tok) (site : String := "'\\draw'") (cost : String := "the edge is not drawn")
    (displacement : Bool := false) : Except PDiag Anchor := do
  match (splitTop inner ',').toList with
  | [xs, ys] =>
    let x ← (evalComp env xs).mapError fun e => (.E0333, s!"in {site}, {e}; {cost}")
    let y ← (evalComp env ys).mapError fun e => (.E0333, s!"in {site}, {e}; {cost}")
    -- A point goes through the transformation in force, a displacement through its linear part.
    let (px, py) := if displacement then cx.placeVec (cx.compSp x) (cx.compSp y)
      else cx.place (cx.compSp x) (cx.compSp y)
    return .point px py
  | _ =>
    let mut expanded : Array Tok := #[]
    for t in inner do
      match t with
      | .ctrl n =>
        match env.lookup n with
        | some v => expanded := expanded.push (.ident v.text)
        | none =>
          throw (.E0333, s!"in {site}, unknown macro '\\{n}' in a node name; {cost}")
      | .ident _ | .num _ _ | .sym _ | .space => expanded := expanded.push t
      | .math _ _ _ | .group _ | .other _ =>
        throw (.W0334, s!"coordinate {tokText t} is outside the rendered \
picture subset; {cost}")
    let nm := (nameOfToks expanded.toList).getD ""
    match ev.nodes.lookup nm with
    | some g => return .node g
    | none =>
      match splitAnchor nm with
      | some (base, an) =>
        match ev.nodes.lookup base with
        | none => throw (unreachedName (ev.gapped || cx.parseGap) base site cost)
        | some g =>
          match nodeAnchorOf an with
          | some a =>
            let (x, y) := g.anchorPoint a
            return .point x y
          | none =>
            throw (.W0334, s!"node anchor '{an}' is outside the rendered \
picture subset; {cost}")
      | none => throw (unreachedName (ev.gapped || cx.parseGap) nm site cost)

private def factorEnd (ts : Array Tok) (i : Nat) : Option Nat := Id.run do
  let mut depth : Int := 0
  for k in [i:ts.size] do
    match ts[k]? with
    | some (.sym '(') => depth := depth + 1
    | some (.sym ')') => depth := depth - 1
    | some (.sym '*') => if depth == 0 && ts[k + 1]? == some (.sym '(') then return some k
    | some (.sym c) => if depth == 0 && (c == '+' || c == '-' || c == '!') then return none
    | _ => pure ()
  return none

private def bangAt (ts : Array Tok) (i : Nat) : Option Nat := Id.run do
  let mut depth : Int := 0
  for k in [i:ts.size] do
    match ts[k]? with
    | some (.sym '(') => depth := depth + 1
    | some (.sym ')') => depth := depth - 1
    | some (.sym '!') => if depth == 0 then return some k
    | _ => pure ()
  return none

private def calcAnchor (cx : Cx) (env : List (String × Val)) (ev : Ev)
    (raw : List Parse.Raw) (site : String := "'\\draw'") (cost : String := "the edge is not drawn") :
    Except PDiag Anchor := do
  let ts := (ofRaws raw.toArray).filter (· != .space)
  let mut i := 0
  let mut point : Int × Int := (0, 0)
  let mut subtract := false
  let unsupported : PDiag := (.W0334, "this calc coordinate is outside the \
rendered picture subset; use sums, differences, factors and '!t!' steps of \
'(...)' coordinates")
  let calcErr (e : String) : PDiag := (.E0333, s!"in a calc coordinate, {e}; {cost}")
  for _ in [0:ts.size + 1] do
    let mut factor : Int := 1000
    if let some j := factorEnd ts i then
      factor ← (evalNum env (ts.extract i j)).mapError calcErr
      i := j + 1
    unless ts[i]? == some (.sym '(') do throw unsupported
    let (inner, next) ← (readCoordBody ts i).mapError calcErr
    let mut p := (← anchorBody cx env ev inner site cost).center
    i := next
    for _ in [0:ts.size] do
      unless ts[i]? == some (.sym '!') do break
      let some k := bangAt ts (i + 1) | throw unsupported
      let step := ts.extract (i + 1) k
      -- `!(c)!` projects onto the line (§13.5.4), outside this reader.
      if step[0]? == some (.sym '(') then throw unsupported
      i := k + 1
      unless ts[i]? == some (.sym '(') do throw unsupported
      let (inner2, next2) ← (readCoordBody ts i).mapError calcErr
      let q := (← anchorBody cx env ev inner2 site cost).center
      i := next2
      let dx := q.1 - p.1
      let dy := q.2 - p.2
      match ← (evalComp env step).mapError calcErr with
      | (t, false) => p := (p.1 + dx * t / 1000, p.2 + dy * t / 1000)
      | (d, true) =>
        let n := isqrt (dx * dx + dy * dy)
        let d := d * cx.scale / 1000
        if n != 0 then p := (p.1 + dx * d / n, p.2 + dy * d / n)
    let scaled := if factor == 1000 then p else (p.1 * factor / 1000, p.2 * factor / 1000)
    point := (coordStep .advance point
      (if subtract then (-scaled.1, -scaled.2) else scaled)).1
    if i == ts.size then return .point point.1 point.2
    match ts[i]? with
    | some (.sym '+') => subtract := false
    | some (.sym '-') => subtract := true
    | _ => throw unsupported
    i := i + 1
  throw unsupported

private def readAnchor (cx : Cx) (env : List (String × Val)) (ev : Ev)
    (ts : Array Tok) (start : Nat) (base : Int × Int) :
    Except PDiag (Anchor × Nat × (Int × Int)) := do
  let mut i := start
  let mut mode := CoordMode.absolute
  if ts[i]? == some (.sym '+') then
    i := i + 1
    mode := .offset
    if ts[i]? == some (.sym '+') then
      i := i + 1
      mode := .advance
  let (inner, next) ← (readCoordBody ts i).mapError fun e =>
    (.E0333, s!"in '\\draw', {e}; the edge is not drawn")
  let a ← match inner.toList with
    | [.math false raw _] => calcAnchor cx env ev raw
    | _ => anchorBody cx env ev inner (displacement := mode != .absolute)
  let (point, reference) := coordStep mode base a.center
  return (if mode == .absolute then a else .point point.1 point.2, next, reference)

private def evalNode (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) (coordinate : Bool := false) (defaultName : Option String := none) : Ev :=
    Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut color := cx.ink
  -- `transform shape` opts the node into the picture's scale (pgf manual §25.4).
  let factor : Nat := if cx.transformShape && cx.scale > 0 then cx.scale.toNat else 1000
  let baseStyles : Array Ir.Style := cx.decls.filterMap fun n =>
    if (cx.ladder.lookup n).isSome then none else cx.declStyles.lookup n
  let mut scale : Nat := cx.declScale factor
  let mut ev := ev
  let mut nodeShape : NodeShape := .rectangle
  let mut extras : Array (Bool × List Tok) := #[]
  let mut labelDist : Sp := 0
  let mut pinDist : Option Sp := none
  let mut fitTo : Option (List Tok) := none
  let mut draw : Option (Option Ir.Color) := none
  let mut fillCol : Option Ir.Color := none
  let mut dash : Ir.Pic.Dash := .solid
  let mut width : Sp := Ir.Pic.thinWidth
  let mut fontStyles : Array Ir.Style := #[]
  let mut textHt : Option (List Tok) := none
  let mut textDp : Option (List Tok) := none
  let mut textAlign : Ir.Pic.LabelAlign := .center
  let mut minW : Sp := 0
  let mut minH : Sp := 0
  let mut xsep : Option Sp := none
  let mut ysep : Option Sp := none
  let mut oxsep : Option Sp := none
  let mut oysep : Option Sp := none
  let mut own : Array (Array Tok) := #[]
  let mut anchorAt : Option (NodeAnchor × (Sp × Sp)) := none
  let (pro, i1, bad) := readPrologue ts i
  i := i1
  if let some d := bad then return ev.diag d
  for inner in pro.brackets do
    own := own ++ expandOpts cx.styles inner
  let nodeName : Option String := pro.name.orElse fun _ => defaultName
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
    | [.ident "circle"] => nodeShape := .circle
    | [.ident "rectangle"] => nodeShape := .rectangle
    | [.ident "ellipse"] => nodeShape := .ellipse
    | [.ident "diamond"] => nodeShape := .diamond
    | .ident "shape" :: .sym '=' :: rest =>
      match keyName rest with
      | some "circle" => nodeShape := .circle
      | some "rectangle" => nodeShape := .rectangle
      | some "ellipse" => nodeShape := .ellipse
      | some "diamond" => nodeShape := .diamond
      | _ => ev := ev.diag (.W0334, s!"node option {optName opt.toList} is outside the rendered \
picture subset; the node is a rectangle")
    | .ident "label" :: .sym '=' :: rest => extras := extras.push (false, rest)
    | .ident "pin" :: .sym '=' :: rest => extras := extras.push (true, rest)
    | .ident "label" :: .ident "distance" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => labelDist := d
      | .error e => ev := ev.diag (.W0334, s!"in 'label distance', {e}; the option is dropped")
    | .ident "pin" :: .ident "distance" :: .sym '=' :: rest =>
      match readDim rest with
      | .ok d => pinDist := some d
      | .error e => ev := ev.diag (.W0334, s!"in 'pin distance', {e}; the option is dropped")
    | .ident "fit" :: .sym '=' :: rest => fitTo := some rest
    | [.ident "draw"] => draw := some none
    | [.ident "draw", .sym '=', .ident "none"] => draw := none
    | .ident "draw" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => draw := some (some c)
      | .error e => ev := ev.diag (.E0333, s!"in '\\node', {e}; the colour is dropped")
    | [.ident "fill", .sym '=', .ident "none"] => fillCol := none
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
    -- `inner sep` moves the node's border, not the letters (pgf manual §17.2.2, §17.5.2).
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
    -- `outer sep` moves a painted node's anchors past its border, never the path; `auto` is half the line width.
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
    | .ident "node" :: .ident "contents" :: .sym '=' :: rest =>
      let g : List Tok := if let [.group inner] := rest then inner else rest
      let (ls, ds) := nodeLabel cx env (cx.nodeText g)
      contents := some ls
      ev := ds.foldl Ev.diag ev
    | .ident "anchor" :: .sym '=' :: rest =>
      match nameOfToks rest >>= nodeAnchorOf with
      | some a => anchorAt := some (a, (0, 0))
      | none =>
        ev := ev.diag (.W0334, s!"node option 'anchor={String.join (rest.map tokText)}' \
names an anchor outside the rendered picture subset; the node is centred")
    | [] => pure ()
    | o :: rest =>
      match (keyName ((o :: rest).takeWhile (· != .sym '='))).bind dirOf with
      | some d =>
        let value := ((o :: rest).dropWhile (· != .sym '=')).drop 1
        match (if value.isEmpty then .ok 0 else readDim value) with
        | .ok len => anchorAt := some (dirAnchor d len)
        | .error e =>
          ev := ev.diag (.W0334, s!"in node option {optName (o :: rest)}, {e}; the \
node is placed by its anchor alone")
          anchorAt := some (dirAnchor d 0)
      | none =>
        ev := ev.diag (.W0334, s!"node option {optName (o :: rest)} is outside the rendered \
picture subset; the option is dropped")
  let mut fitBox : Option (Sp × Sp × Sp × Sp) := none
  if let some ft := fitTo then
    let fts := (ft.filter (· != .space)).toArray
    let mut pts : Array (Sp × Sp) := #[]
    let mut j := 0
    for _ in [0:fts.size + 1] do
      if j ≥ fts.size then break
      match readAnchor cx env ev fts j (0, 0) with
      | .ok (a, next, _) =>
        match a with
        | .node g =>
          for an in [NodeAnchor.west, .east, .north, .south] do pts := pts.push (g.anchorPoint an)
        | .point x y => pts := pts.push (x, y)
        j := next
      | .error _ =>
        ev := ev.diag (.E0333, "in 'fit', a node or point it names does not resolve; the node \
fits the rest")
        break
    if let some p0 := pts[0]? then
      let x0 := pts.foldl (fun m p => min m p.1) p0.1
      let x1 := pts.foldl (fun m p => max m p.1) p0.1
      let y0 := pts.foldl (fun m p => min m p.2) p0.2
      let y1 := pts.foldl (fun m p => max m p.2) p0.2
      fitBox := some ((x0 + x1) / 2, (y0 + y1) / 2, x1 - x0, y1 - y0)
      anchorAt := none
  -- A node with no `at` stands at the path's current point, the origin at a statement's start.
  let atAnchor : Option (Except PDiag Anchor) := match fitBox with
    | some (fx, fy, _, _) => some (.ok (.point fx fy))
    | none => pro.at?.map fun inner =>
      match inner.toList with
      | [.math false raw _] => calcAnchor cx env ev raw "'\\node'" "the node is not drawn"
      | _ => anchorBody cx env ev inner "'\\node'" "the node is not drawn"
  let unresolved : Bool :=
    (atAnchor matches some (.error _)) ||
    (atAnchor.isNone && (match place with
      | some (_, target, _) => (ev.nodes.lookup target).isNone
      | none => false))
  let dimF (d : Sp) : Sp :=
    if cx.transformShape then d * cx.scale / 1000 else d
  let bodyOf : Except PDiag (Array LabelLine × Array PDiag) :=
    if coordinate then .ok (#[], #[]) else
    match ts[i]? with
    | some (.group body) =>
      if h : i + 1 < ts.size then
        .error (.W0334, s!"'\\node' continues with {tokText ts[i+1]}, \
outside the rendered picture subset; the label is not drawn")
      else
        .ok (nodeLabel cx env (cx.nodeText body))
    | _ =>
      match contents with
      | some c => .ok (c, #[])
      | none =>
        .error (.E0333, "'\\node' needs a '{text}' body; the label is not drawn")
  let bodyOf := bodyOf.map fun (ls, ds) => (fontLines (baseStyles ++ fontStyles) ls, ds)
  let shapes0 : Array Ir.Pic.Shape :=
    match bodyOf with
    | .ok (lines, _) => stackLabels 0 0 cx.bodySize scale color .center lines #[]
    | .error _ => #[]
  let inkHalf : Sp × Sp :=
    let bands := shapes0.filterMap fun s => match s with
      | .label lx ly content _ sz al => some (Ir.Pic.labelInkBox lx ly al (cx.metric content sz))
      | .ink _ => none
    let ((bx0, by0), (bx1, by1)) := Gfx.Box.hull bands
    match fitBox with
    | some (_, _, fw, _) => (fw / 2, max (-by0) by1)
    | none => (max (-bx0) bx1, max (-by0) by1)
  -- The label's first line is the node's baseline, as for any TeX box.
  let lineInks : Array (Sp × Ir.Pic.LabelInk) := shapes0.filterMap fun s =>
    match s with
    | .label _ ly content _ sz al =>
      let m := cx.metric content sz
      some (Ir.Pic.labelBaseline ly al m, m)
    | .ink _ => none
  let baseOff : Sp := (lineInks[0]?.map (·.1)).getD 0
  let em : Sp := cx.bodySize * (scale : Int) / 1000
  let ex : Sp := (lineInks[0]?.map (·.2.ex)).getD 0
  let sepX : Sp := if coordinate then 0 else xsep.getD (innerSep em)
  let sepY : Sp := if coordinate then 0 else ysep.getD (innerSep em)
  let glyphs : Sp × Sp := lineInks.foldl (fun (lo, hi) (b, m) =>
    (min lo (b - m.boxDepth), max hi (b + m.boxHeight))) (baseOff, baseOff)
  let dimOf (ts : Option (List Tok)) : Option Sp :=
    ts.bind fun ts => (readNodeDim em ex ts).toOption
  let declHt := match fitBox with
    | some (_, _, _, fh) => some (fh / 2)
    | none => dimOf textHt
  let declDp := match fitBox with
    | some (_, _, _, fh) => some (fh - fh / 2)
    | none => dimOf textDp
  for (key, ts) in [("text height", textHt), ("text depth", textDp)] do
    if let some ts := ts then
      if let .error e := readNodeDim em ex ts then
        ev := ev.diag (.W0334, s!"in '{key}', {e}; the option is dropped")
  let declaredExtent : Bool := match nodeShape with
    | .circle => max minW minH > 0
    | .rectangle => minW > 0 && minH > 0
    | .ellipse | .diamond => false
  let outlined : Bool :=
    (draw.isSome || fillCol.isSome || nodeShape == .ellipse || nodeShape == .diamond) &&
      !declaredExtent
  let (base, boxLo, boxHi, halfB) : Sp × Sp × Sp × Sp :=
    if declHt.isNone && declDp.isNone && !outlined then (baseOff, glyphs.1, glyphs.2, inkHalf.2)
    else
      let ht := declHt.getD (glyphs.2 - baseOff)
      let dp := declDp.getD (baseOff - glyphs.1)
      let (b0, lo, hi) := textSeat ht dp
      (b0, lo, hi, (ht + dp) / 2)
  let outline? : Option (Sp × Sp) :=
    if outlined then
      let (_, w, h) := nodeOutline nodeShape (dimF minW) (dimF minH) 0 inkHalf.1 boxLo boxHi sepX sepY
      some (w, h)
    else none
  let declA : Sp := if nodeShape == .circle then dimF (max minW minH) / 2 else dimF minW / 2
  let declB : Sp := if nodeShape == .circle then dimF (max minW minH) / 2 else dimF minH / 2
  let ownA : Sp := match outline? with
    | some (w, _) => w / 2
    | none => borderHalf declA inkHalf.1 sepX
  let ownB : Sp := match outline? with
    | some (_, h) => h / 2
    | none => borderHalf declB halfB sepY
  -- A drawn or filled node's anchors stand one outer sep past its border, any other node's on it.
  let pgfBorder : Bool := draw.isSome || fillCol.isSome
  let (outA, outB) : Sp × Sp :=
    if !pgfBorder then (0, 0)
    else
      let ox := oxsep.getD (width / 2)
      let oy := oysep.getD (width / 2)
      if nodeShape == .circle then (max ox oy, max ox oy) else (ox, oy)
  let anchA : Sp := ownA + outA
  let anchB : Sp := ownB + outB
  let anchorShift : Sp × Sp := match anchorAt with
    | some (an, (dx, dy)) =>
      let p := ({ x := 0, y := 0, a := anchA, b := anchB, shape := nodeShape, base } :
        NodeGeom).anchorPoint an
      (dx - p.1, dy - p.2)
    | none => (0, 0)
  let placement : Except PDiag NodePlacement :=
    match atAnchor with
    | some (.ok a) =>
      let (x, y) := a.center
      .ok (.absolute (x + anchorShift.1) (y + anchorShift.2))
    | some (.error d) => .error d
    | none =>
      match place with
      | none =>
        let o := cx.place 0 0
        .ok (.absolute (o.1 + anchorShift.1) (o.2 + anchorShift.2))
      | some (dir, target, sep) => .ok (.relative dir target sep)
  let pos : Except PDiag (NodeGeom × List (String × NodeGeom)) := do
    let placement ← placement
    let plan : NodePlan :=
      { name := nodeName, placement
        shape := { x := 0, y := 0, a := anchA, b := anchB, shape := nodeShape, base } }
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
  match pos with
  | .ok (geom, nodes) =>
        let sx := geom.x
        let sy := geom.y
        -- pgf's bounding box includes the node's shape whether or not it is drawn.
        let border : Ir.Pic.Box :=
          if outline?.isSome then ((sx - ownA, sy - ownB), (sx + ownA, sy + ownB))
          else
            ((sx - ownA, sy + min (boxLo - sepY) (-declB)),
             (sx + ownA, sy + max (boxHi + sepY) declB))
        ev := ev.place coordinate border nodes
        for (pin, spec) in extras do
          let x : After := { main := geom, pin, spec, dist := if pin then pinDist else some labelDist }
          ev := { ev with after := ev.after.push x }
        -- The outline before the label, so the fill paints under the text.
        if draw.isSome || fillCol.isSome then
          let stroke : Option Ir.Pic.Stroke := draw.map fun c =>
            { color := c.getD cx.ink
              width := width
              dash := dash }
          let paintOf (w h : Sp) : Ir.Pic.Shape := match nodeShape with
            | .rectangle => .frame (sx - w / 2) (sy - h / 2) w h stroke fillCol
            | .circle => .circle sx sy (w / 2) stroke fillCol
            | .ellipse =>
              .ink (.draw (.ellipse sx sy (w / 2) (h / 2)) (fillCol.map Ir.Pic.solidFill)
                (stroke.map Ir.Pic.strokeOf))
            | .diamond =>
              -- The drawn diamond stands √2 outer seps inside its anchors (`\backgroundpath`).
              let dx := w / 2 + outA - outA * 1414213 / 1000000
              let dy := h / 2 + outB - outB * 1414213 / 1000000
              let sub : Gfx.Subpath :=
                { start := (sx + dx, sy), closed := true
                  segs := #[.line (sx, sy + dy), .line (sx - dx, sy), .line (sx, sy - dy)] }
              .ink (.draw (.path #[sub]) (fillCol.map Ir.Pic.solidFill) (stroke.map Ir.Pic.strokeOf))
          match outline? with
          | some (w, h) => ev := { ev with shapes := ev.shapes.push (paintOf w h) }
          | none =>
            let (w, h) := if nodeShape == .circle then (dimF (max minW minH), dimF (max minW minH))
              else (dimF minW, dimF minH)
            ev := { ev with shapes := ev.shapes.push (paintOf w h) }
        match bodyOf with
        | .error d => return ev.diag d
        | .ok (lines, mdiags) =>
          ev := mdiags.foldl Ev.diag ev
          let placed := alignLabels cx.metric textAlign
            (stackLabels sx (sy + (base - baseOff)) cx.bodySize scale color .center lines #[])
          ev := { ev with shapes := ev.shapes ++ placed }
          return ev
  | .error d =>
    return (if unresolved then { ev with deferred := ev.deferred + 1 } else ev).diag d

/-- Sine of whole degrees 0–90 in milli, ⌊1000·sin d° + ½⌋. -/
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

private def Anchor.toward (a : Anchor) (q : Sp × Sp) : Sp × Sp :=
  match a with
  | .point x y => (x, y)
  | .node g =>
    if g.a ≤ 0 || g.b ≤ 0 then (g.x, g.y)
    else match g.shape with
      | .rectangle => rectBorder g.x g.y g.a g.b q.1 q.2
      | .circle => circleBorder g.x g.y g.a q.1 q.2
      | .ellipse => ellipseBorder g.x g.y g.a g.b q.1 q.2
      | .diamond => diamondBorder g.x g.y g.a g.b q.1 q.2

private inductive TipInk where
  | tri (t : Ir.Pic.Tip)
  | node (n : Gfx.Node Empty)

private def tipAlong (k : TipKind) (q : Sp × Sp) (dx dy lw : Sp) (color : Ir.Color) :
    Option (TipInk × Sp × Sp) :=
  let n := isqrt (dx * dx + dy * dy)
  if n == 0 then none else
  let frame (tipEnd s t : Int) : Sp × Sp :=
    (q.1 + ((s - tipEnd) * dx - t * dy) / n, q.2 + ((s - tipEnd) * dy + t * dx) / n)
  let a : Int := Dim.pt 28 / 100 + lw * 3 / 10 -- 0.28pt + .3\pgflinewidth (pgfcorearrows.code.tex)
  let filled (sub : Gfx.Subpath) : Gfx.Node Empty :=
    .draw (.path #[sub]) (some (Ir.Pic.solidFill color)) none
  match k with
  | .to =>
    let tipEnd : Int := Dim.pt 21 / 100 + lw * 625 / 1000 -- \pgfarrowsrightextend (pgfcorearrows.code.tex)
    let f := frame tipEnd
    let sub : Gfx.Subpath :=
      { start := f (-3 * a) (4 * a), closed := false
        segs := #[.cubic (f (-275 * a / 100) (25 * a / 10)) (f 0 (a / 4)) (f (75 * a / 100) 0),
          .cubic (f 0 (-(a / 4))) (f (-275 * a / 100) (-(25 * a / 10))) (f (-3 * a) (-4 * a))] }
    let st : Gfx.Stroke :=
      { Ir.Pic.strokeOf { color, width := lw * 8 / 10 } with cap := .round, join := .round }
    some (.node (.draw (.path #[sub]) none (some st)), f 0 0)
  | .cmRightarrow =>
    let len : Int := Dim.pt 16 / 10 + lw * 22 / 10 -- length = +1.6pt 2.2 (pgflibraryarrows.meta.code.tex)
    let wid : Int := len * 2096774 / 1000000
    let ia := len - lw
    let ib := wid - lw
    let f := frame (lw / 2)
    let sub : Gfx.Subpath :=
      { start := f (-ia) (ib / 2), closed := false
        segs := #[.cubic (f (-(81731 * ia / 100000)) (ib / 5)) (f (-(41019 * ia / 100000))
            (5833333 * ib / 100000000)) (f 0 0),
          .cubic (f (-(41019 * ia / 100000)) (-(5833333 * ib / 100000000)))
            (f (-(81731 * ia / 100000)) (-(ib / 5))) (f (-ia) (-(ib / 2)))] }
    let st : Gfx.Stroke :=
      { Ir.Pic.strokeOf { color, width := lw } with cap := .round, join := .round }
    some (.node (.draw (.path #[sub]) none (some st)), f (-(lw / 2)) 0)
  | .latex =>
    let f := frame (9 * a)
    some (.node (filled
      { start := f (9 * a) 0, closed := true
        segs := #[.cubic (f (63333 * a / 10000) (a / 2)) (f (2 * a) (2 * a)) (f (-a) (375 * a / 100)),
          .line (f (-a) (-(375 * a / 100))),
          .cubic (f (2 * a) (-(2 * a))) (f (63333 * a / 10000) (-(a / 2))) (f (9 * a) 0)] }), f 0 0)
  | .stealthOld =>
    let f := frame (5 * a)
    some (.node (filled
      { start := f (5 * a) 0, closed := true
        segs := #[.line (f (-3 * a) (4 * a)), .line (f 0 0), .line (f (-3 * a) (-4 * a))] }), f 0 0)
  | .latexMeta =>
    let len : Int := Dim.pt 3 + lw * 45 / 10 -- length = +3pt 4.5 (pgflibraryarrows.meta.code.tex)
    let wid : Int := len * 75 / 100
    let alw : Int := min lw (len / 5)
    if wid ≤ 0 then none else
    let front := alw * isqrt (wid * wid + 9 * len * len) / wid
    let inner := len - front / 2 - alw / 2
    let vx := 3 * len / 10
    let vy := wid * 2333333 / 10000000
    let vn := isqrt (vx * vx + vy * vy)
    let hb := if vx == 0 then wid / 2 else wid / 2 - alw * (vy + vn) / (2 * vx)
    let f := frame (len - alw / 2)
    let sub : Gfx.Subpath :=
      { start := f inner 0, closed := true
        segs := #[.cubic (f (877192 * inner / 1000000) (77922 * hb / 1000000))
            (f (337381 * inner / 1000000) (519480 * hb / 1000000)) (f 0 hb),
          .line (f 0 (-hb)),
          .cubic (f (337381 * inner / 1000000) (-(519480 * hb / 1000000)))
            (f (877192 * inner / 1000000) (-(77922 * hb / 1000000))) (f inner 0)] }
    some (.node (.draw (.path #[sub]) (some (Ir.Pic.solidFill color))
      (some (Ir.Pic.strokeOf { color, width := alw }))), f 0 0)
  | .stealth =>
    let len : Int := Dim.pt 3 + lw * 45 / 10 -- length = +3pt 4.5 (pgflibraryarrows.meta.code.tex)
    let wid : Int := len * 75 / 100
    let ins : Int := len * 325 / 1000
    let alw : Int := min lw ((len - ins) / 4)
    if wid ≤ 0 then none else
    let front := alw * isqrt (wid * wid + 4 * len * len) / (2 * wid)
    let insetMiter := alw * isqrt (wid * wid + 4 * ins * ins) / (2 * wid)
    let a1 := Gfx.Trig.atan2 len (wid / 2)
    let a0 := Gfx.Trig.atan2 ins (wid / 2)
    let half := (a1 - a0) / 2
    let (ch, sh) := Gfx.Trig.cosSin half
    let yc := if sh == 0 then alw / 2 else alw * ch / (2 * sh)
    let (ca, sa) := Gfx.Trig.cosSin (a0 + half)
    let u := Gfx.Trig.unit
    let back := if ins == 0 then alw / 2 else sa * yc / u
    let hw := wid / 2 - ca * yc / u
    let f := frame len
    let dart : Gfx.Subpath :=
      { start := f (len - front) 0, closed := true
        segs := #[.line (f back hw), .line (f (ins + insetMiter) 0), .line (f back (-hw))] }
    some (.node (.draw (.path #[dart]) (some (Ir.Pic.solidFill color))
      (some (Ir.Pic.strokeOf { color, width := alw }))), f (ins + insetMiter - alw / 4) 0)

private def tipArrival (k : TipKind) (p q : Sp × Sp) (lw : Sp) (color : Ir.Color) :
    Option (TipInk × Sp × Sp) :=
  tipAlong k q (q.1 - p.1) (q.2 - p.2) lw color

private def segReverse : Ir.Pic.PathSeg → Ir.Pic.PathSeg
  | .line x1 y1 x2 y2 => .line x2 y2 x1 y1
  | .cubic x1 y1 c1x c1y c2x c2y x2 y2 => .cubic x2 y2 c2x c2y c1x c1y x1 y1

private def sideShaft (startT endT : Option TipKind) (corner : Option (Sp × Sp))
    (p1 p2 : Sp × Sp) (lw : Sp) (color : Ir.Color) :
    Array Ir.Pic.PathSeg × Option TipInk × Option TipInk × (Sp × Sp) :=
  let startHit := startT.bind fun k => tipArrival k (corner.getD p2) p1 lw color
  let q1 : Sp × Sp := match startHit with
    | some (_, bx, byy) => (bx, byy)
    | none => p1
  let departure := corner.getD q1
  let elbow : Array Ir.Pic.PathSeg := match corner with
    | some q => #[.line q1.1 q1.2 q.1 q.2]
    | none => #[]
  let endHit := endT.bind fun k => tipArrival k departure p2 lw color
  let q2 : Sp × Sp := match endHit with
    | some (_, bx, byy) => (bx, byy)
    | none => p2
  (elbow.push (.line departure.1 departure.2 q2.1 q2.2), startHit.map (·.1), endHit.map (·.1), q1)

private theorem reversedTip_exact (k : TipKind) (p q : Sp × Sp) (w : Sp) (c : Ir.Color) :
    (sideShaft (some k) none none p q w c).1 =
        (sideShaft none (some k) none q p w c).1.map segReverse ∧
      (sideShaft (some k) none none p q w c).2.1 = (sideShaft none (some k) none q p w c).2.2.1 ∧
      (sideShaft (some k) none none p q w c).2.2.1 = (sideShaft none (some k) none q p w c).2.1 := by
  simp only [sideShaft, Option.bind_some, Option.bind_none, Option.getD_none, Option.map_none]
  cases tipArrival k q p w c with
  | none => simp [segReverse]
  | some hit =>
    obtain ⟨t, bx, byy⟩ := hit
    simp [segReverse]

private def Anchor.towardDir (a : Anchor) (deg : Int) : Sp × Sp :=
  let c := a.center
  a.toward (c.1 + cosDeg deg, c.2 + sinDeg deg)

private def curveControl (px py dist deg : Int) : Int × Int :=
  (px + dist * cosDeg deg / 1000, py + dist * sinDeg deg / 1000)

private theorem curveControl_tangent (px py dist deg : Int) :
    1000 * ((curveControl px py dist deg).1 - px) ≤ dist * cosDeg deg ∧
    dist * cosDeg deg < 1000 * ((curveControl px py dist deg).1 - px) + 1000 ∧
    1000 * ((curveControl px py dist deg).2 - py) ≤ dist * sinDeg deg ∧
    dist * sinDeg deg < 1000 * ((curveControl px py dist deg).2 - py) + 1000 := by
  simp only [curveControl]
  generalize dist * cosDeg deg = d
  generalize dist * sinDeg deg = e
  omega

private structure ToSpec where
  outA : Int := 45
  inA : Int := 135
  rel : Bool := false
  bend : Int := 30
  outL : Int := 1000
  inL : Int := 1000
  curved : Bool := false

private def ToSpec.bendTo (s : ToSpec) (left : Bool) (b : Int) : ToSpec :=
  let o := if left then b else -b
  { s with bend := b, outA := o, inA := 180 - o, rel := true, curved := true }

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

private def turnAbout (c p : Sp × Sp) (deg : Int) : Sp × Sp :=
  let dx := p.1 - c.1
  let dy := p.2 - c.2
  (c.1 + (dx * cosDeg deg - dy * sinDeg deg) / 1000,
   c.2 + (dx * sinDeg deg + dy * cosDeg deg) / 1000)

private def turnedControl (px py vx vy deg loose : Int) : Int × Int :=
  (px + (vx * cosDeg deg - vy * sinDeg deg) * 3915 * loose / 10000000000,
   py + (vx * sinDeg deg + vy * cosDeg deg) * 3915 * loose / 10000000000)

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

private inductive DrawOp where
  | straight
  | orthogonal (verticalFirst : Bool)
  | curve (spec : ToSpec)
  | rect
  | cycle
  | ellipse (rx ry : Sp)
  | arc (s e : Int) (rx ry : Sp)

private inductive PathMode where
  | draw
  | path
  | fill
  | filldraw
  | shade
  | shadedraw
  | clip
  deriving BEq

private def optLen (cx : Cx) (env : List (String × Val)) (toks : List Tok) : Except String Sp :=
  match readNodeDim cx.bodySize (cx.metric #[.text "x"] 1000).ex toks with
  | .ok d => .ok d
  | .error _ =>
    match evalComp env toks.toArray with
    | .ok (v, true) => .ok v
    | .ok (m, false) => .ok (milliPt m)
    | .error e => .error e

private def optAlpha (env : List (String × Val)) (toks : List Tok) : Except String Gfx.Alpha :=
  match evalNum env toks.toArray with
  | .ok m =>
    let n := (max 0 m).toNat
    .ok ⟨min n 1000, by omega⟩
  | .error e => .error e

private def towardBy (p q : Sp × Sp) (d : Sp) : Sp × Sp :=
  let dx := q.1 - p.1
  let dy := q.2 - p.2
  let n := isqrt (dx * dx + dy * dy)
  if n == 0 then p else (p.1 + dx * d / n, p.2 + dy * d / n)

/-- A rounded corner's control coordinate, 0.5522847 of the way from the curve's end `s` to the
corner `b` (pgf's `\pgfprocess@@specialround`). -/
@[expose] public def cornerControl (s b : Int) : Int := s + (b - s) * 5522847 / 10000000

public theorem roundedCorners_between (s b : Int) :
    min s b ≤ cornerControl s b ∧ cornerControl s b ≤ max s b := by
  unfold cornerControl
  constructor <;> omega

private def roundJoints (r : Sp) (segs : Array Ir.Pic.PathSeg) : Array Ir.Pic.PathSeg := Id.run do
  let mut out : Array Ir.Pic.PathSeg := #[]
  let mut held : Option Ir.Pic.PathSeg := none
  for sg in segs do
    match held, sg with
    | some (.line ax ay bx by'), .line bx2 by2 cx cy =>
      if bx == bx2 && by' == by2 && (ax, ay) != (bx, by') && (cx, cy) != (bx, by') then
        let (sx, sy) := towardBy (bx, by') (ax, ay) r
        let (ex, ey) := towardBy (bx, by') (cx, cy) r
        out := (out.push (.line ax ay sx sy)).push (.cubic sx sy (cornerControl sx bx)
          (cornerControl sy by') (cornerControl ex bx) (cornerControl ey by') ex ey)
        held := some (.line ex ey cx cy)
      else
        out := out.push (.line ax ay bx by')
        held := some sg
    | some h, _ =>
      out := out.push h
      held := some sg
    | none, _ => held := some sg
  if let some h := held then out := out.push h
  return out

private def readArc (cx : Cx) (env : List (String × Val)) (ts : Array Tok) (i : Nat) :
    Except PDiag (Int × Int × Sp × Sp × Nat) := do
  let err (e : String) : PDiag := (.E0333, s!"in an 'arc', {e}; the path is not drawn")
  let num (t : Array Tok) : Except PDiag Int := (evalNum env t).mapError err
  let len (t : Array Tok) : Except PDiag Sp := do
    let v ← (evalComp env t).mapError err
    return cx.compSp v
  if ts[i]? == some (.sym '[') then
    let mut j := i + 1
    let mut inner : Array Tok := #[]
    for _ in [i+1:ts.size + 1] do
      if h : j < ts.size then
        if ts[j] == .sym ']' then break
        inner := inner.push ts[j]
        j := j + 1
      else break
    unless ts[j]? == some (.sym ']') do throw (err "the options miss their ']'")
    let mut sa : Option Int := none
    let mut ea : Option Int := none
    let mut da : Option Int := none
    let mut rx : Option Sp := none
    let mut ry : Option Sp := none
    for opt in splitTop inner ',' do
      let key := keyPath opt.toList
      let rest := ((opt.toList.dropWhile (· != .sym '=')).drop 1).toArray
      if key == "start angle" then sa := some (← num rest)
      else if key == "end angle" then ea := some (← num rest)
      else if key == "delta angle" then da := some (← num rest)
      else if key == "radius" then
        let r ← len rest
        rx := some r
        ry := some r
      else if key == "x radius" then rx := some (← len rest)
      else if key == "y radius" then ry := some (← len rest)
      else throw (.W0334, s!"'arc' option '{key}' is outside the rendered picture subset; \
the path is not drawn")
    let (s0, e0) ← match sa, ea, da with
      | some a, some b, _ => pure (a, b)
      | some a, none, some d => pure (a, a + d)
      | none, some b, some d => pure (b - d, b)
      | _, _, _ => throw (err "two of its start, end and delta angles are needed")
    match rx.orElse (fun _ => ry), ry.orElse (fun _ => rx) with
    | some a, some b => return (s0, e0, a, b, j + 1)
    | _, _ => throw (err "no radius is given")
  let (inner, next) ← (readCoordBody ts i).mapError err
  match (splitTop inner ':').toList with
  | [s0, e0, r] =>
    let a ← num s0
    let b ← num e0
    match r.toList.findIdx? (· == .ident "and") with
    | none =>
      let rr ← len r
      return (a, b, rr, rr, next)
    | some k => return (a, b, ← len (r.extract 0 k), ← len (r.extract (k + 1) r.size), next)
  | _ => throw (err "'(start:end:radius)' is needed")

private def cosSinMilli (m : Int) : Int × Int := Gfx.Trig.cosSin (m * Gfx.Trig.pi / 180000)

private def arcStep (onCanvas : Sp × Sp → Sp × Sp) (acc : Array Ir.Pic.PathSeg × (Sp × Sp)) :
    Gfx.Seg → Array Ir.Pic.PathSeg × (Sp × Sp)
  | .line q =>
    let q' := onCanvas q
    (acc.1.push (.line acc.2.1 acc.2.2 q'.1 q'.2), q')
  | .cubic c1 c2 q =>
    let c1' := onCanvas c1
    let c2' := onCanvas c2
    let q' := onCanvas q
    (acc.1.push (.cubic acc.2.1 acc.2.2 c1'.1 c1'.2 c2'.1 c2'.2 q'.1 q'.2), q')

private theorem arcStep_end (onCanvas : Sp × Sp → Sp × Sp) :
    ∀ (segs : List Gfx.Seg) (acc : Array Ir.Pic.PathSeg × (Sp × Sp)),
      (segs.foldl (arcStep onCanvas) acc).2 =
        ((segs.getLast?.map fun sg => onCanvas sg.endPt).getD acc.2)
  | [], _ => rfl
  | [sg], acc => by cases sg <;> rfl
  | sg :: sg2 :: rest, acc => by
    rw [List.foldl_cons, arcStep_end onCanvas (sg2 :: rest)]
    simp only [List.getLast?_cons_cons]
    cases h : (sg2 :: rest).getLast? with
    | none => simp at h
    | some l => rfl

private def arcPieces (cx : Cx) (p : Sp × Sp) (s e rx ry : Int) :
    Array Ir.Pic.PathSeg × (Sp × Sp) :=
  let u := Gfx.Trig.unit
  let start : Sp × Sp := (rx * (cosSinMilli s).1 / u, ry * (cosSinMilli s).2 / u)
  let last : Sp × Sp := (rx * (cosSinMilli e).1 / u, ry * (cosSinMilli e).2 / u)
  let θ0 := s * Gfx.Trig.pi / 180000
  let Δ := (e - s) * Gfx.Trig.pi / 180000
  let pieces := Gfx.Kit.arcCubics 0 0 rx ry 0 θ0 Δ last
  let onCanvas (q : Sp × Sp) : Sp × Sp :=
    let d := cx.placeVec (q.1 - start.1) (q.2 - start.2)
    (p.1 + d.1, p.2 + d.2)
  pieces.foldl (arcStep onCanvas) (#[], p)

private theorem arc_end_exact (cx : Cx) (p : Sp × Sp) (s e rx ry : Int) :
    (arcPieces cx p s e rx ry).2 =
      let u := Gfx.Trig.unit
      let d := cx.placeVec (rx * (cosSinMilli e).1 / u - rx * (cosSinMilli s).1 / u)
        (ry * (cosSinMilli e).2 / u - ry * (cosSinMilli s).2 / u)
      (p.1 + d.1, p.2 + d.2) := by
  unfold arcPieces
  rw [← Array.foldl_toList, arcStep_end]
  have hl := Gfx.Kit.arcCubics_exact 0 0 rx ry 0 (s * Gfx.Trig.pi / 180000)
    ((e - s) * Gfx.Trig.pi / 180000)
    (rx * (cosSinMilli e).1 / Gfx.Trig.unit, ry * (cosSinMilli e).2 / Gfx.Trig.unit)
  rw [← Array.getLast?_toList] at hl
  cases hp : (Gfx.Kit.arcCubics 0 0 rx ry 0 (s * Gfx.Trig.pi / 180000)
      ((e - s) * Gfx.Trig.pi / 180000)
      (rx * (cosSinMilli e).1 / Gfx.Trig.unit, ry * (cosSinMilli e).2 / Gfx.Trig.unit)).toList.getLast? with
  | none =>
    rw [hp] at hl
    simp at hl
  | some sg =>
    rw [hp] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    simp only [Option.map_some, Option.getD_some, hl]

private def ellipseOnCanvas (cx : Cx) (c : Sp × Sp) (rx ry : Sp) :
    Sum (Sp × Sp × Sp × Sp) Gfx.Subpath :=
  if cx.axisAligned then
    let (ax, _) := cx.placeVec rx 0
    let (_, dy) := cx.placeVec 0 ry
    .inl (c.1, c.2, ax.natAbs, dy.natAbs)
  else
    let base := (Gfx.Kit.ellipse 0 0 rx ry)[0]?.getD { start := (rx, 0), segs := #[], closed := true }
    let on (q : Sp × Sp) : Sp × Sp :=
      let d := cx.placeVec q.1 q.2
      (c.1 + d.1, c.2 + d.2)
    .inr { start := on base.start, closed := true
           segs := base.segs.map fun sg => match sg with
             | .line q => .line (on q)
             | .cubic c1 c2 q => .cubic (on c1) (on c2) (on q) }

private def rectLoop (cx : Cx) (a c : Sp × Sp) : Array Ir.Pic.PathSeg :=
  let m := cx.xf
  let det := m.a * m.d - m.b * m.c
  let (b, d) : (Sp × Sp) × (Sp × Sp) :=
    if det == 0 then ((c.1, a.2), (a.1, c.2)) else
    let ux : Rat := (m.d * (c.1 - a.1) - m.c * (c.2 - a.2)) / det
    let uy : Rat := (-m.b * (c.1 - a.1) + m.a * (c.2 - a.2)) / det
    ((a.1 + roundRat (m.a * ux), a.2 + roundRat (m.b * ux)),
     (a.1 + roundRat (m.c * uy), a.2 + roundRat (m.d * uy)))
  let mx := (a.1 + b.1) / 2
  let my := (a.2 + b.2) / 2
  #[.line mx my b.1 b.2, .line b.1 b.2 c.1 c.2, .line c.1 c.2 d.1 d.2, .line d.1 d.2 a.1 a.2,
    .line a.1 a.2 mx my]

private def readRadii (cx : Cx) (env : List (String × Val)) (ts : Array Tok) (i : Nat) :
    Except PDiag (Sp × Sp × Nat) := do
  let err (e : String) : PDiag := (.E0333, s!"in a 'circle' radius, {e}; the path is not drawn")
  if ts[i]? == some (.sym '[') then
    let mut j := i + 1
    let mut inner : Array Tok := #[]
    for _ in [i+1:ts.size + 1] do
      if h : j < ts.size then
        if ts[j] == .sym ']' then break
        inner := inner.push ts[j]
        j := j + 1
      else break
    unless ts[j]? == some (.sym ']') do throw (err "the options miss their ']'")
    let mut rx : Option Sp := none
    let mut ry : Option Sp := none
    for opt in splitTop inner ',' do
      let key := keyPath opt.toList
      let rest := ((opt.toList.dropWhile (· != .sym '=')).drop 1).toArray
      let v ← (evalComp env rest).mapError err
      if key == "radius" then
        rx := some (cx.compSp v)
        ry := some (cx.compSp v)
      else if key == "x radius" then rx := some (cx.compSp v)
      else if key == "y radius" then ry := some (cx.compSp v)
      else throw (.W0334, s!"'circle' option '{key}' is outside the rendered picture \
subset; the path is not drawn")
    match rx.orElse (fun _ => ry), ry.orElse (fun _ => rx) with
    | some a, some b => return (a, b, j + 1)
    | _, _ => throw (err "no radius is given")
  let (inner, next) ← (readCoordBody ts i).mapError err
  match inner.toList.findIdx? (· == .ident "and") with
  | none =>
    let v ← (evalComp env inner).mapError err
    return (cx.compSp v, cx.compSp v, next)
  | some k =>
    let va ← (evalComp env (inner.extract 0 k)).mapError err
    let vb ← (evalComp env (inner.extract (k + 1) inner.size)).mapError err
    return (cx.compSp va, cx.compSp vb, next)

private def tipNode (st : Ir.Pic.Stroke) (t : Ir.Pic.Tip) : Gfx.Node Empty :=
  .draw (.path #[Ir.Pic.tipSubpath t]) (some (Ir.Pic.solidFill st.color)) none

private def tipInkNode (st : Ir.Pic.Stroke) : TipInk → Gfx.Node Empty
  | .tri t => tipNode st t
  | .node n => n

private def edgeWithTips (segs : Array Ir.Pic.PathSeg) (st : Ir.Pic.Stroke)
    (tips : Array TipInk) : Ir.Pic.Shape :=
  match tips.toList with
  | [] => .edge segs st none
  | [.tri t] => .edge segs st (some t)
  | _ =>
    let path : Gfx.Node Empty := .draw (.path (Ir.Pic.edgeSubpaths segs)) none (some (Ir.Pic.strokeOf st))
    .ink (.group Gfx.Affine.unit #[] Gfx.Alpha.opaque (#[path] ++ tips.map (tipInkNode st)))

mutual

-- conserves: none — a repaint of paints' alpha.
private def alphaOne (fa sa : Gfx.Alpha) : Gfx.Node Empty → Gfx.Node Empty
  | .draw g fl st => .draw g (fl.map ({ · with alpha := fa })) (st.map ({ · with alpha := sa }))
  | .group m clips a kids => .group m clips a (alphaList fa sa #[] kids.toList)
  | .use r m => .use r m
  | .stamp g m fl st => .stamp g m fl st
  | .image i m => .image i m
  | .label l => nomatch l
  | .words w => .words w

private def alphaList (fa sa : Gfx.Alpha) (acc : Array (Gfx.Node Empty)) :
    List (Gfx.Node Empty) → Array (Gfx.Node Empty)
  | [] => acc
  | n :: rest => alphaList fa sa (acc.push (alphaOne fa sa n)) rest

end

/-- The one geometry a filled path, or one holding an ellipse, paints as, filled by the nonzero rule. -/
@[expose] public def paintedGeom (segs : Array Ir.Pic.PathSeg)
    (rects ellipses : Array (Sp × Sp × Sp × Sp)) (extra : Array Gfx.Subpath := #[]) :
    Gfx.Geom :=
  match segs.isEmpty && extra.isEmpty, rects.toList, ellipses.toList with
  | true, [(x, y, w, h)], [] => .rect x y w h
  | true, [], [(ex, ey, rx, ry)] => .ellipse ex ey rx ry
  | _, _, _ =>
    let rectSubs := rects.map fun (x, y, w, h) => Gfx.Kit.rectPath x y w h
    let ellSubs := ellipses.flatMap fun (ex, ey, rx, ry) => Gfx.Kit.ellipse ex ey rx ry
    .path (Ir.Pic.edgeSubpaths segs ++ rectSubs ++ ellSubs ++ extra)

/-- The three shadings TikZ declares: `axis`, `radial` and `ball` (tikz.code.tex). -/
public inductive ShadeKind where
  | axis
  | radial
  | ball
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A path's shading as TikZ's options leave it: its kind, angle in milli-degrees, and colours. -/
public structure ShadeSpec where
  kind : ShadeKind
  angle : Int
  top : Ir.Color
  middle : Ir.Color
  bottom : Ir.Color
  inner : Ir.Color
  outer : Ir.Color
  ball : Ir.Color
  deriving Repr, Inhabited

/-- TikZ's initial shading (tikz.code.tex): the axis shading gray over white, the radial gray to
white, the ball blue. -/
public def ShadeSpec.initial : ShadeSpec :=
  let base (n : String) : Ir.Color := ((default : Ir.Palette).resolve n).getD Ir.Color.black
  { kind := .axis, angle := 0, top := base "gray"
    middle := Ir.Color.mix (base "gray") 50 (base "white"), bottom := base "white"
    inner := base "gray", outer := base "white", ball := base "blue" }

/-- One shading colour key (tikz.code.tex): the colour it sets, the kind it switches to and, for an
edge, the axis angle; `none` for an unknown key. -/
public def ShadeSpec.setColor (s : ShadeSpec) (side : String) (c : Ir.Color) :
    Option ShadeSpec :=
  let mid (t b : Ir.Color) : Ir.Color := Ir.Color.mix t 50 b
  match side with
  | "top" => some { s with top := c, middle := mid c s.bottom, kind := .axis, angle := 0 }
  | "bottom" => some { s with bottom := c, middle := mid s.top c, kind := .axis, angle := 0 }
  | "left" => some { s with top := c, middle := mid c s.bottom, kind := .axis, angle := 90000 }
  | "right" => some { s with bottom := c, middle := mid s.top c, kind := .axis, angle := 90000 }
  | "middle" => some { s with middle := c, kind := .axis }
  | "inner" => some { s with inner := c, kind := .radial }
  | "outer" => some { s with outer := c, kind := .radial }
  | "ball" => some { s with ball := c, kind := .ball }
  | _ => none

/-- A stop `num/den` of the way along a gradient's run, in 65536ths, rounded half up. -/
@[expose] public def stopAt (num den : Nat) (c : Ir.Color) : Gfx.Stop :=
  { offset := ⟨min 65536 ((num * 65536 + den / 2) / den), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    color := c }

/-- A shading's stops as tikz.code.tex declares them, over the axis shading's 100 bp or the 50 bp radius. -/
@[expose] public def ShadeSpec.stops (s : ShadeSpec) : Array Gfx.Stop :=
  match s.kind with
  | .axis => #[stopAt 0 100 s.bottom, stopAt 25 100 s.bottom, stopAt 50 100 s.middle,
      stopAt 75 100 s.top, stopAt 100 100 s.top]
  | .radial => #[stopAt 0 50 s.inner, stopAt 25 50 s.outer, stopAt 50 50 s.outer]
  | .ball => #[stopAt 0 50 (Ir.Color.mix s.ball 15 Ir.Color.white),
      stopAt 9 50 (Ir.Color.mix s.ball 75 Ir.Color.white),
      stopAt 18 50 (Ir.Color.mix s.ball 70 Ir.Color.black),
      stopAt 25 50 (Ir.Color.mix s.ball 50 Ir.Color.black), stopAt 50 50 Ir.Color.black]

private def shadeFrame (angle : Int) (box : Gfx.Box) : Option Gfx.Affine :=
  let ((x0, y0), (x1, y1)) := box
  if x1 ≤ x0 || y1 ≤ y0 then none else
  let u : Rat := Gfx.Trig.unit
  let (ci, si) := cosSinMilli angle
  let c : Rat := ci / u
  let s : Rat := si / u
  let ac : Rat := if c < 0 then -c else c
  let as : Rat := if s < 0 then -s else s
  let w : Rat := x1 - x0
  let h : Rat := y1 - y0
  let half : Rat := Dim.pt 50 -- the shading's middle 50 bp (pgfcoreshade.code.tex)
  let sx := (w * ac + h * as) / ((ac + as) * half)
  let sy := (w * as + h * ac) / ((ac + as) * half)
  some ⟨c * sx, s * sx, -s * sy, c * sy, ((x0 : Rat) + x1) / 2, ((y0 : Rat) + y1) / 2⟩

private def shadeFill (s : ShadeSpec) (box : Gfx.Box) : Option Gfx.Fill :=
  (shadeFrame s.angle box).map fun xf =>
    let r := Dim.pt 50 -- the shading's 100 bp square (pgfcoreshade.code.tex)
    let g : Gfx.Gradient := match s.kind with
      | .axis => .linear (0, -r) (0, r) s.stops xf
      | .radial => .radial (0, 0) 0 (0, 0) r s.stops xf
      | .ball => .radial (-(Dim.pt 10), Dim.pt 10) 0 (0, 0) r s.stops xf -- \pgfqpoint{-10bp}{10bp}
    { paint := .gradient g, rule := .nonzero, alpha := Gfx.Alpha.opaque }

private structure BraceSpec where
  amplitude : Sp := Dim.pt 25 / 10 -- \pgfdecorationsegmentamplitude2.5pt (pgfmoduledecorations.code.tex)
  aspect : Int := 500
  mirror : Bool := false
  raise : Sp := 0

private def readBrace (cx : Cx) (env : List (String × Val)) (rest : List Tok) :
    Except String BraceSpec := do
  let inner : List Tok := match rest with
    | [.group g] => g.filter (· != .space)
    | _ => rest
  let mut b : BraceSpec := {}
  let mut named := false
  for e in splitTop inner.toArray ',' do
    let key := keyPath e.toList
    let value := (e.toList.dropWhile (· != .sym '=')).drop 1
    if key == "brace" then named := true
    else if key == "name" then
      if keyName value == some "brace" then named := true
      else throw s!"the decoration '{String.join (value.map tokText)}' is outside the rendered \
picture subset"
    else if key == "amplitude" then b := { b with amplitude := ← optLen cx env value }
    else if key == "aspect" then b := { b with aspect := ← evalNum env value.toArray }
    else if key == "mirror" then b := { b with mirror := value != [.ident "false"] }
    else if key == "raise" then b := { b with raise := ← optLen cx env value }
    else throw s!"the decoration key '{key}' is outside the rendered picture subset"
  unless named do throw "a decoration other than the brace is outside the rendered picture subset"
  return b

private def braceSegs (b : BraceSpec) (x0 y0 x1 y1 : Sp) : Array Ir.Pic.PathSeg :=
  let dx := x1 - x0
  let dy := y1 - y0
  let d := isqrt (dx * dx + dy * dy)
  if d == 0 then #[.line x0 y0 x1 y1] else
  let a := b.amplitude
  let sd := b.aspect * d / 1000
  let yc := if 2 * a > sd then sd / 2 else a
  let xc := if -2 * a < sd - d then (d - sd) / 2 else a
  let at_ (s t : Int) : Sp × Sp :=
    let t := t + b.raise
    let t := if b.mirror then -t else t
    (x0 + (s * dx - t * dy) / d, y0 + (s * dy + t * dx) / d)
  let cub (p c1 c2 q : Sp × Sp) : Ir.Pic.PathSeg := .cubic p.1 p.2 c1.1 c1.2 c2.1 c2.2 q.1 q.2
  let ln (p q : Sp × Sp) : Ir.Pic.PathSeg := .line p.1 p.2 q.1 q.2
  let p0 := at_ 0 0
  let p1 := at_ yc (a / 2)
  let p2 := at_ (sd - yc) (a / 2)
  let tipP := at_ sd a
  let p3 := at_ (sd + xc) (a / 2)
  let p4 := at_ (d - xc) (a / 2)
  let p5 := at_ d 0
  #[cub p0 (at_ (15 * yc / 100) (3 * a / 10)) (at_ (yc / 2) (a / 2)) p1,
    ln p1 p2,
    cub p2 (at_ (sd - yc / 2) (a / 2)) (at_ (sd - 15 * yc / 100) (7 * a / 10)) tipP,
    cub tipP (at_ (sd + 15 * xc / 100) (7 * a / 10)) (at_ (sd + xc / 2) (a / 2)) p3,
    ln p3 p4,
    cub p4 (at_ (d - xc / 2) (a / 2)) (at_ (d - 15 * xc / 100) (3 * a / 10)) p5]

public theorem circleOp_exact (x y r : Sp) :
    paintedGeom #[] #[] #[(x, y, r, r)] = .ellipse x y r r := rfl

public theorem circlePath_box_exact (x y r : Int) (h : 0 ≤ r) :
    (paintedGeom #[] #[] #[(x, y, r, r)]).hull = some ((x - r, y - r), (x + r, y + r)) := by
  simp only [circleOp_exact, Gfx.Geom.hull, Option.some.injEq, Prod.mk.injEq]
  exact ⟨⟨Int.min_eq_left (by omega), Int.min_eq_left (by omega)⟩,
    Int.max_eq_right (by omega), Int.max_eq_right (by omega)⟩

private structure EdgeLabel where
  lines : Array LabelLine
  color : Ir.Color
  scale : Nat
  placement : Option Dir
  autoLeft : Option Bool
  align : Ir.Pic.LabelAlign
  inner : Sp × Sp
  outer : Option Sp × Option Sp
  atEnd : Bool

/-- Moves a measured label without changing its text or baseline rule; other shapes are unchanged. -/
public def translateLabel (offset : Sp × Sp) : Ir.Pic.Shape → Ir.Pic.Shape
  | .label x y content color size align =>
    .label (x + offset.1) (y + offset.2) content color size align
  | s@(.ink _) => s

public theorem translateLabel_box_projects (offset : Sp × Sp) (x y : Sp)
    (content : Array Ir.Inline) (color : Ir.Color) (size : Nat)
    (align : Ir.Pic.LabelAlign) (metric : Ir.Pic.LabelMetric) :
    match translateLabel offset (.label x y content color size align) with
    | .label u v text _ scale al =>
      let box := Ir.Pic.labelTextBox x y align (metric content size)
      Ir.Pic.labelTextBox u v al (metric text scale) =
        ((box.1.1 + offset.1, box.1.2 + offset.2),
         (box.2.1 + offset.1, box.2.2 + offset.2))
    | .ink _ => False :=
  Ir.Pic.labelTextBox_translate_exact x y align (metric content size) offset

private def EdgeLabel.place (label : EdgeLabel) (cx : Cx) (width : Sp)
    (anchor tangent : Sp × Sp) : Array Ir.Pic.Shape :=
  let lines := alignLabels cx.metric label.align
    (stackLabels 0 0 cx.bodySize label.scale label.color .center label.lines #[])
  let direction := label.placement.orElse fun _ =>
    label.autoLeft.map fun left => autoDir left tangent.1 tangent.2
  let offset := match direction with
    | none => anchor
    | some dir =>
      let box := Gfx.Box.hull (lines.filterMap fun (shape : Ir.Pic.Shape) => match shape with
        | .label x y content _ size align =>
          some (Ir.Pic.labelTextBox x y align (cx.metric content size))
        | .ink _ => none)
      let gap := (label.inner.1 + label.outer.1.getD (width / 2),
                  label.inner.2 + label.outer.2.getD (width / 2))
      Ir.Pic.Box.attachOffset box anchor (dir.offset (1, 1)) gap
  lines.map (translateLabel offset)

private def readEdgeLabel (cx : Cx) (env : List (String × Val))
    (ts : Array Tok) (start : Nat) (before : Ev) (autoOn autoLeft : Bool)
    (trailing : Bool := false) :
    Except Ev (Option EdgeLabel × Nat × Ev) := Id.run do
  let mut i := start
  let mut ev := before
  let factor : Nat := if cx.transformShape && cx.scale > 0 then cx.scale.toNat else 1000
  let mut mid : Option EdgeLabel := none
  if ts[i]? == some (.ident "node") then
    i := i + 1
    unless cx.everyNode.isEmpty do
      ev := ev.diag (.W0334, "an 'every node' key on an edge label is outside \
the rendered picture subset; the keys are dropped")
    let mut mcolor := cx.ink
    let mut mscale : Nat := cx.declScale factor
    let mut mstyles : Array Ir.Style := #[]
    let mut malign : Option Dir := none
    let mut mAuto := autoOn
    let mut mLeft := autoLeft
    let mut atEnd := trailing
    -- `font=` and body switches change the text box, not the dimension font.
    let mut mseps : Array (String × List Tok) := #[]
    let mut mtext : Ir.Pic.LabelAlign := .center
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
        return .error (ev.diag (.E0333, "an edge node's options miss their ']'; the \
edge is not drawn"))
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
      | [.ident "swap"] | [.sym '\''] => mLeft := !mLeft
      | [.ident "auto"] => mAuto := true
      | [.ident "auto", .sym '=', .ident "left"] => mAuto := true; mLeft := true
      | [.ident "auto", .sym '=', .ident "right"] => mAuto := true; mLeft := false
      | [.ident "auto", .sym '=', .ident "false"] => mAuto := false
      | [.ident "midway"] => atEnd := false
      | [] => pure ()
      | o :: rest =>
        match (keyName (o :: rest)).bind dirOf with
        | some d => malign := some d
        | none =>
          ev := ev.diag (.W0334, s!"edge node option {optName (o :: rest)} is outside \
the rendered picture subset; the option is dropped")
    match ts[i]? with
    | some (.group body) =>
      let (lines, mdiags) := nodeLabel cx env (cx.nodeText body)
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
                    align := mtext, inner, outer, atEnd }
      i := i + 1
    | _ =>
      return .error (ev.diag (.E0333, "an edge 'node' needs a '{text}' body; the \
edge is not drawn"))
  return .ok (mid, i, ev)

private def evalDraw (cx : Cx) (env : List (String × Val)) (toks : Array Tok)
    (ev : Ev) (mode : PathMode := .draw) : Ev := Id.run do
  let ts := toks.filter (· != .space)
  let mut i := 0
  let mut ev := ev
  let mut color := cx.ink
  let mut dash : Ir.Pic.Dash := .solid
  let mut width : Sp := Ir.Pic.thinWidth
  let mut startArrow := false
  let mut endArrow := false
  -- `\path` paints nothing of itself; an `edge` or a `draw` key makes it stroke.
  let mut strokes := mode == .draw || mode == .filldraw || mode == .shadedraw
  let mut fills := mode == .fill || mode == .filldraw
  let mut fillColor : Option Ir.Color := none
  let mut shades := mode == .shade || mode == .shadedraw
  let mut shading : ShadeSpec := ShadeSpec.initial
  let mut clips := mode == .clip
  let mut decorate := false
  let mut brace : Option BraceSpec := none
  let mut startName : Option String := none
  let mut endName : Option String := none
  let mut shorthand : Option String := none
  let mut shortenStart : Sp := 0
  let mut shortenEnd : Sp := 0
  let mut rounded : Option Sp := none
  let mut fillAlpha : Gfx.Alpha := Gfx.Alpha.opaque
  let mut strokeAlpha : Gfx.Alpha := Gfx.Alpha.opaque
  let mut opStroke := false
  let mut autoOn := false
  let mut autoLeft := true
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
    match arrowSpec opt.toList with
    | some (st, en) =>
      startArrow := st.any (drawsAsArrow cx.styles)
      endArrow := en.any (drawsAsArrow cx.styles)
      startName := st
      endName := en
      for tip in [st, en] do
        if let some name := tip then
          unless drawsAsArrow cx.styles name do
            ev := ev.diag (.W0334, s!"arrow tip '{name}' is outside the rendered \
picture subset; the edge is drawn without a head")
    | none =>
    match readLineWidth opt.toList with
    | some (.ok w) => width := w
    | some (.error e) =>
      ev := ev.diag (.W0334, s!"in 'line width', {e}; the option is dropped")
    | none =>
    match opt.toList with
    | [.ident "draw"] => strokes := true
    | [.ident "auto"] => autoOn := true
    | [.ident "auto", .sym '=', .ident "left"] => autoOn := true; autoLeft := true
    | [.ident "auto", .sym '=', .ident "right"] => autoOn := true; autoLeft := false
    | [.ident "auto", .sym '=', .ident "false"] => autoOn := false
    | [.ident "swap"] | [.sym '\''] => autoLeft := !autoLeft
    | [.ident "dashed"] => dash := .dashed
    | [.ident "dotted"] | [.ident "densely", .ident "dotted"] => dash := .dotted
    | .sym '>' :: .sym '=' :: rest =>
      match tipName rest with
      | some tip =>
        shorthand := some tip
        unless drawsAsArrow cx.styles tip do
          ev := ev.diag (.W0334, s!"arrow tip '{tip}' is outside the rendered \
picture subset; the edge is drawn without a head")
      | none =>
        ev := ev.diag (.W0334, "'>=' without a tip name is outside the rendered \
picture subset; the option is dropped")
    | [.ident "draw", .sym '=', .ident "none"] => strokes := false
    | .ident "draw" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => color := c
      | .error e =>
        ev := ev.diag (.E0333, s!"in '\\draw', {e}; the colour is dropped")
      strokes := true
    | [.ident "fill"] => fills := true
    | [.ident "fill", .sym '=', .ident "none"] => fills := false
    | .ident "fill" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => fillColor := some c
      | .error e =>
        ev := ev.diag (.E0333, s!"in '\\draw', {e}; the fill colour is dropped")
      fills := true
    | .ident "color" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c => color := c
      | .error e =>
        ev := ev.diag (.E0333, s!"in '\\draw', {e}; the colour is dropped")
    | .ident "shorten" :: .sym '<' :: .sym '=' :: rest =>
      match optLen cx env rest with
      | .ok d => shortenStart := d
      | .error e => ev := ev.diag (.E0333, s!"in 'shorten <=', {e}; it is ignored")
    | .ident "shorten" :: .sym '>' :: .sym '=' :: rest =>
      match optLen cx env rest with
      | .ok d => shortenEnd := d
      | .error e => ev := ev.diag (.E0333, s!"in 'shorten >=', {e}; it is ignored")
    -- pgf's default radius (tikz.code.tex: `rounded corners/.default=4pt`).
    | [.ident "rounded", .ident "corners"] => rounded := some (Dim.pt 4)
    | .ident "rounded" :: .ident "corners" :: .sym '=' :: rest =>
      match optLen cx env rest with
      | .ok d => rounded := some d
      | .error e => ev := ev.diag (.E0333, s!"in 'rounded corners', {e}; corners stay sharp")
    | [.ident "sharp", .ident "corners"] => rounded := none
    | .ident "opacity" :: .sym '=' :: rest =>
      match optAlpha env rest with
      | .ok a => fillAlpha := a; strokeAlpha := a
      | .error e => ev := ev.diag (.E0333, s!"in 'opacity', {e}; it is ignored")
    | .ident "fill" :: .ident "opacity" :: .sym '=' :: rest =>
      match optAlpha env rest with
      | .ok a => fillAlpha := a
      | .error e => ev := ev.diag (.E0333, s!"in 'fill opacity', {e}; it is ignored")
    | .ident "draw" :: .ident "opacity" :: .sym '=' :: rest =>
      match optAlpha env rest with
      | .ok a => strokeAlpha := a
      | .error e => ev := ev.diag (.E0333, s!"in 'draw opacity', {e}; it is ignored")
    | [.ident "shade"] => shades := true
    | [.ident "clip"] => clips := true
    | [.ident "decorate"] => decorate := true
    | .ident "decoration" :: .sym '=' :: rest =>
      match readBrace cx env rest with
      | .ok b => brace := some b
      | .error e => ev := ev.diag (.W0334, s!"{e}; the path is drawn undecorated")
    | .ident "shading" :: .sym '=' :: rest =>
      match keyName rest with
      | some "axis" => shading := { shading with kind := .axis }; shades := true
      | some "radial" => shading := { shading with kind := .radial }; shades := true
      | some "ball" => shading := { shading with kind := .ball }; shades := true
      | _ => ev := ev.diag (.W0334, s!"the shading '{String.join (rest.map tokText)}' is \
outside the rendered picture subset; the option is dropped")
    | .ident "shading" :: .ident "angle" :: .sym '=' :: rest =>
      match evalNum env rest.toArray with
      | .ok m => shading := { shading with angle := m }; shades := true
      | .error e => ev := ev.diag (.E0333, s!"in 'shading angle', {e}; it is ignored")
    | .ident side :: .ident "color" :: .sym '=' :: rest =>
      match evalColor cx env rest.toArray with
      | .ok c =>
        match shading.setColor side c with
        | some s => shading := s; shades := true
        | none => ev := ev.diag (.W0334, s!"draw option '{side} color' is outside the \
rendered picture subset; the option is dropped")
      | .error e => ev := ev.diag (.E0333, s!"in '{side} color', {e}; the colour is dropped")
    | [] => pure ()
    | o :: rest =>
      match toSpec.read env opt with
      | some (.ok s) => toSpec := s
      | some (.error e) =>
        return ev.diag (.E0333, s!"in '\\draw' option '{keyPath opt.toList}', {e}; \
the edge is not drawn")
      | none =>
      match evalColor cx env opt with
      | .ok c => color := c
      | .error _ =>
        ev := ev.diag (.W0334, s!"draw option {optName (o :: rest)} is outside the \
rendered picture subset; the option is dropped")
  let mut pts : Array Anchor := #[]
  let mut ops : Array (DrawOp × Option EdgeLabel) := #[]
  let mut reference : Sp × Sp := (0, 0)
  match readAnchor cx env ev ts i reference with
  | .error d => return ev.diag d
  | .ok (a, i2, base) =>
    pts := pts.push a
    i := i2
    reference := base
  for _ in [0:ts.size + 1] do
    if h : i < ts.size then
      let mut op := DrawOp.straight
      if ts[i]? == some (.sym '-') && ts[i+1]? == some (.sym '-') then
        i := i + 2
        if ts[i]? == some (.ident "cycle") then
          op := .cycle
          i := i + 1
      else if ts[i]? == some (.sym '|') && ts[i+1]? == some (.sym '-') then
        op := .orthogonal true
        i := i + 2
      else if ts[i]? == some (.sym '-') && ts[i+1]? == some (.sym '|') then
        op := .orthogonal false
        i := i + 2
      else if ts[i]? == some (.ident "rectangle") then
        op := .rect
        i := i + 1
      else if ts[i]? == some (.ident "circle") || ts[i]? == some (.ident "ellipse") then
        match readRadii cx env ts (i + 1) with
        | .ok (rx, ry, next) =>
          op := .ellipse rx ry
          i := next
        | .error d => return ev.diag d
      else if ts[i]? == some (.ident "arc") then
        match readArc cx env ts (i + 1) with
        | .ok (sa, ea, rx, ry, next) =>
          op := .arc sa ea rx ry
          i := next
        | .error d => return ev.diag d
      else if ts[i]? == some (.ident "to") || ts[i]? == some (.ident "edge") then
        -- `edge` is `to` with `every edge`'s `draw` in force.
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
      let mut mid : Option EdgeLabel := none
      match readEdgeLabel cx env ts i ev autoOn autoLeft with
      | .error failed => return failed
      | .ok (label, next, after) =>
        mid := label
        i := next
        ev := after
      if op matches .cycle then
        let first := pts[0]?.getD (.point 0 0)
        pts := pts.push first
        reference := first.center
        ops := ops.push (op, mid)
      else if op matches .ellipse _ _ then
        let here := (pts.back?.map Anchor.center).getD (0, 0)
        pts := pts.push (.point here.1 here.2)
        ops := ops.push (op, mid)
      else if let .arc sa ea rx ry := op then
        let here := (pts.back?.map Anchor.center).getD (0, 0)
        let (_, fin) := arcPieces cx here sa ea rx ry
        pts := pts.push (.point fin.1 fin.2)
        reference := fin
        ops := ops.push (op, mid)
      else
        match readAnchor cx env ev ts i reference with
        | .error d => return ev.diag d
        | .ok (a, i2, base) =>
          pts := pts.push a
          i := i2
          reference := base
          match readEdgeLabel cx env ts i ev autoOn autoLeft true with
          | .error failed => return failed
          | .ok (label, next, after) =>
            ev := after
            if mid.isSome && label.isSome then
              return ev.diag (.W0334, "multiple nodes on one path segment are outside \
the rendered picture subset; the edge is not drawn")
            mid := mid.or label
            i := next
          ops := ops.push (op, mid)
    else break
  unless pts.size ≥ 2 do
    return ev.diag (.E0333, "'\\draw' needs two endpoints; the edge is not drawn")
  let stroke : Ir.Pic.Stroke :=
    { color := color
      width := width
      dash := dash }
  let kindOf1 := tipKindOf cx.metaArrows
  let declared (n : String) : TipKind :=
    ((cx.styles.lookup (tipKey n)).bind fun ts => (tipName ts.toList).bind kindOf1).getD .latex
  let shorthandKind : TipKind := if cx.metaArrows then .cmRightarrow else .to
  let kindOf (n : Option String) : TipKind :=
    match n with
    | some ">" | some "<" =>
      (shorthand.bind fun s => (kindOf1 s).orElse fun _ => some (declared s)).getD shorthandKind
    | some s => (kindOf1 s).getD (declared s)
    | none => shorthandKind
  let startKind := kindOf startName
  let endKind := kindOf endName
  let tipFor (kind : TipKind) (p q : Sp × Sp) : Option (TipInk × Sp × Sp) :=
    tipArrival kind p q stroke.width stroke.color
  let mut segs : Array Ir.Pic.PathSeg := #[]
  let mut tip : Option TipInk := none
  let mut startTip : Option TipInk := none
  let mut labels : Array Ir.Pic.Shape := #[]
  let mut frames : Array Ir.Pic.Shape := #[]
  let mut rects : Array (Sp × Sp × Sp × Sp) := #[]
  let mut ellipses : Array (Sp × Sp × Sp × Sp) := #[]
  let mut extraSubs : Array Gfx.Subpath := #[]
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
        if rounded.isSome || !cx.axisAligned then
          segs := segs ++ rectLoop cx (x1, y1) (x2, y2)
        else
          if strokes then
            frames := frames.push (.frame (min x1 x2) (min y1 y2) (max x1 x2 - min x1 x2)
              (max y1 y2 - min y1 y2) (some stroke) none)
          rects := rects.push (min x1 x2, min y1 y2, max x1 x2 - min x1 x2, max y1 y2 - min y1 y2)
        if let some label := mid then
          labels := labels ++ label.place cx width
            (if label.atEnd then (x2, y2) else ((x1 + x2) / 2, (y1 + y2) / 2))
            (x2 - x1, y2 - y1)
        subStart := none
        cur := some (x2, y2)
      | .cycle =>
        match subStart, cur with
        | some (f, sx, sy), some (ex, ey) =>
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
      | .ellipse rx ry =>
        let (x0, y0) := a.center
        match ellipseOnCanvas cx (x0, y0) rx ry with
        | .inl e => ellipses := ellipses.push e
        | .inr sp => extraSubs := extraSubs.push sp
        if let some label := mid then
          labels := labels ++ label.place cx width (x0, y0) (0, 0)
        subStart := none
        cur := some (x0, y0)
      | .arc sa ea rx ry =>
        let p := a.center
        let (pieces, fin) := arcPieces cx p sa ea rx ry
        if subStart.isNone || cur != some p then subStart := some (segs.size, p.1, p.2)
        segs := segs ++ pieces
        cur := some fin
        if last && endArrow then
          if let some (.cubic _ _ _ _ c2x c2y ex ey) := pieces.back? then
            tip := (tipFor endKind (c2x, c2y) (ex, ey)).map (·.1)
        if k == 0 && startArrow then
          if let some (.cubic sx sy c1x c1y _ _ _ _) := pieces.toList.head? then
            startTip := (tipFor startKind (c1x, c1y) (sx, sy)).map (·.1)
        if let some label := mid then
          labels := labels ++ label.place cx width fin (fin.1 - p.1, fin.2 - p.2)
      | .straight | .orthogonal _ =>
        let labelCorner := match op with
          | .orthogonal vertical => some (orthogonalCorner vertical a.center c.center)
          | .straight | .curve _ | .rect | .cycle | .ellipse _ _ | .arc _ _ _ _ => none
        let corner := labelCorner.filter fun q => q != a.center && q != c.center
        let p1 := a.toward (corner.getD c.center)
        let p2 := c.toward (corner.getD a.center)
        let p1 := if k == 0 && shortenStart != 0 then towardBy p1 (corner.getD p2) shortenStart
          else p1
        let p2 := if last && shortenEnd != 0 then towardBy p2 (corner.getD p1) shortenEnd else p2
        let (side, sTip, eTip, p1) :=
          sideShaft (if k == 0 && startArrow then some startKind else none)
            (if last && endArrow then some endKind else none) corner p1 p2 stroke.width
            stroke.color
        if let some t := sTip then startTip := some t
        if let some t := eTip then tip := some t
        let first := segs.size
        segs := segs ++ side
        let departure := corner.getD p1
        if subStart.isNone || cur != some p1 then subStart := some (first, p1.1, p1.2)
        cur := some p2
        if let some label := mid then
          labels := labels ++ label.place cx width
            (if label.atEnd then p2 else
              labelCorner.getD ((p1.1 + p2.1) / 2, (p1.2 + p2.2) / 2))
            (p2.1 - departure.1, p2.2 - departure.2)
      | .curve spec =>
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
        if k == 0 && startArrow then
          startTip := (tipFor startKind c1 p1).map (·.1)
        if last && endArrow then
          tip := (tipFor endKind c2 p2).map (·.1)
        if let some label := mid then
          labels := labels ++ label.place cx width
            (if label.atEnd then p2 else
              ((p1.1 + 3 * c1.1 + 3 * c2.1 + p2.1) / 8,
               (p1.2 + 3 * c1.2 + 3 * c2.2 + p2.2) / 8))
            (if label.atEnd then (p2.1 - c2.1, p2.2 - c2.2) else
              (-p1.1 - c1.1 + c2.1 + p2.1, -p1.2 - c1.2 + c2.2 + p2.2))
    | _, _, _ => pure ()
  let tips : Array TipInk := startTip.toArray ++ tip.toArray
  if decorate then
    match brace, segs.toList, rects.isEmpty && ellipses.isEmpty && extraSubs.isEmpty with
    | some b, [.line x0 y0 x1 y1], true => segs := braceSegs b x0 y0 x1 y1
    | some _, _, _ => ev := ev.diag (.W0334, "a brace along anything but one straight side is \
outside the rendered picture subset; the path is drawn undecorated")
    | none, _, _ => ev := ev.diag (.W0334, "'decorate' without a decoration this subset draws \
is outside the rendered picture subset; the path is drawn undecorated")
  if let some r := rounded then segs := roundJoints r segs
  let geom := paintedGeom segs rects ellipses extraSubs
  let painted : Array Ir.Pic.Shape :=
    if fills || shades || !ellipses.isEmpty || !extraSubs.isEmpty then
      -- Filled, then shaded, then stroked once, as tikz.code.tex paints them.
      let fill := if fills then some (Ir.Pic.solidFill (fillColor.getD color)) else none
      let shade := if shades then geom.hull.bind (shadeFill shading) else none
      let st := if strokes then some (Ir.Pic.strokeOf stroke) else none
      let draws : Array (Gfx.Node Empty) := match shade with
        | some sh => (if fill.isSome then #[.draw geom fill none] else #[]).push (.draw geom (some sh) st)
        | none => if fill.isNone && st.isNone then #[] else #[.draw geom fill st]
      let marks := if tips.isEmpty || !strokes then draws else draws ++ tips.map (tipInkNode stroke)
      match marks.toList with
      | [] => #[]
      | [d] => #[.ink d]
      | _ => #[.ink (.group Gfx.Affine.unit #[] Gfx.Alpha.opaque marks)]
    else if strokes && !segs.isEmpty then frames.push (edgeWithTips segs stroke tips)
    else frames
  let painted := if fillAlpha == Gfx.Alpha.opaque && strokeAlpha == Gfx.Alpha.opaque then painted
    else painted.map fun sh => match sh with
      | .ink n => .ink (alphaOne fillAlpha strokeAlpha n)
      | .label .. => sh
  return { ev with shapes := ev.shapes ++ painted ++ labels
                   clipGeom := if clips then some geom else ev.clipGeom }

/-- One node of a tree as the flattening walk read it: parent index, level, sibling place, child
options and body parts. -/
public structure TreeItem where
  parent : Option Nat := none
  level : Nat := 0
  index : Nat := 1
  childOpts : Array Tok := #[]
  node : Array Tok := #[]
  coordinate : Bool := true
  pathOpts : Array Tok := #[]
  edgeOpts : Array Tok := #[]
  edgeNodes : Array Tok := #[]
  /-- How many children it has: pgf's `\tikznumberofchildren`. -/
  children : Nat := 0
  deriving Repr, Inhabited

private inductive TMode where
  | start
  | prologue (bracket : Bool) (paren : Nat)
  | cprologue (paren : Nat)
  | tail
  | pathBracket
  | child (bracket : Bool)
  | edge (stage : Nat)
  | edgeBracket
  | edgeNodes
  | skipping
  deriving Repr, Inhabited

private structure TSt where
  items : Array TreeItem := #[{}]
  tree : Bool := false
  cur : Nat := 0
  mode : TMode := .start
  pendingOpts : Array Tok := #[]
  bad : Array PDiag := #[]
  deriving Inhabited

private def TSt.modifyCur (st : TSt) (f : TreeItem → TreeItem) : TSt :=
  { st with items := st.items.modify st.cur f }

private def TSt.diag (st : TSt) (d : PDiag) : TSt :=
  if st.bad.any (·.2 == d.2) then st else { st with bad := st.bad.push d }

private def TSt.pushChild (st : TSt) : TSt × Nat :=
  let parent := st.cur
  let p := st.items[parent]?.getD {}
  let idx := p.children + 1
  let item : TreeItem :=
    { parent := some parent, level := p.level + 1, index := idx, childOpts := st.pendingOpts }
  let items := (st.items.modify parent fun q => { q with children := idx }).push item
  ({ st with items, pendingOpts := #[] }, items.size - 1)

private def treeTail (t : Tok) (st : TSt) : TSt :=
  match t with
  | .space => st
  | .sym '[' => { st with mode := .pathBracket }
  | .ident "child" => { st with mode := .child false, pendingOpts := #[], tree := true }
  | .ident "edge" => { st with mode := .edge 0 }
  | t => { st.diag (.W0334, s!"a tree continues with {tokText t}, outside the rendered \
picture subset; it is dropped") with mode := .skipping }

private def treeStep (t : Tok) (st : TSt) : TSt :=
  let push (st : TSt) : TSt := st.modifyCur fun i => { i with node := i.node.push t }
  match st.mode with
  | .start =>
    match t with
    | .space => st
    | .ident "node" =>
      { st.modifyCur (fun i => { i with coordinate := false }) with mode := .prologue false 0 }
    | .ident "coordinate" => { st with mode := .cprologue 0 }
    | t => treeTail t { st with mode := .tail }
  | .prologue true paren =>
    if t == .sym ']' then { push st with mode := .prologue false paren } else push st
  | .prologue false (paren + 1) =>
    match t with
    | .sym '(' => { push st with mode := .prologue false (paren + 2) }
    | .sym ')' => { push st with mode := .prologue false paren }
    | _ => push st
  | .prologue false 0 =>
    match t with
    | .space => st
    | .ident "child" | .ident "edge" => treeTail t { st with mode := .tail }
    | .group _ => { push st with mode := .tail }
    | .sym '[' => { push st with mode := .prologue true 0 }
    | .sym '(' => { push st with mode := .prologue false 1 }
    | _ => push st
  | .cprologue (paren + 1) =>
    match t with
    | .sym '(' => { push st with mode := .cprologue (paren + 2) }
    | .sym ')' => { push st with mode := .cprologue paren }
    | _ => push st
  | .cprologue 0 =>
    match t with
    | .space => st
    | .ident "child" | .ident "edge" | .sym '[' => treeTail t { st with mode := .tail }
    | .sym '(' => { push st with mode := .cprologue 1 }
    | _ => push st
  | .tail => treeTail t st
  | .pathBracket =>
    match t with
    | .sym ']' =>
      { st.modifyCur (fun i => { i with pathOpts := i.pathOpts.push (.sym ',') }) with mode := .tail }
    | t => st.modifyCur fun i => { i with pathOpts := i.pathOpts.push t }
  | .child true =>
    match t with
    | .sym ']' => { st with mode := .child false, pendingOpts := st.pendingOpts.push (.sym ',') }
    | t => { st with pendingOpts := st.pendingOpts.push t }
  | .child false =>
    match t with
    | .space => st
    | .sym '[' => { st with mode := .child true }
    | .ident "foreach" =>
      { st.diag (.W0334, "'child foreach' is outside the rendered picture subset; those \
children are not drawn") with mode := .skipping }
    -- A child with no body is a coordinate (pgf's `\tikz@collect@child@code{}`).
    | t => treeTail t { st.pushChild.1 with mode := .tail }
  | .edge stage =>
    match stage, t with
    | _, .space => st
    | 0, .ident "from" => { st with mode := .edge 1 }
    | 1, .ident "parent" => { st with mode := .edge 2 }
    | 2, .sym '[' => { st with mode := .edgeBracket }
    | 2, .ident "node" =>
      { st.modifyCur (fun i => { i with edgeNodes := i.edgeNodes.push t }) with mode := .edgeNodes }
    | _, t => { st.diag (.W0334, s!"a tree's 'edge' continues with {tokText t}, outside the \
rendered picture subset; it is dropped") with mode := .skipping }
  | .edgeBracket =>
    match t with
    | .sym ']' =>
      { st.modifyCur (fun i => { i with edgeOpts := i.edgeOpts.push (.sym ',') }) with mode := .edge 2 }
    | t => st.modifyCur fun i => { i with edgeOpts := i.edgeOpts.push t }
  | .edgeNodes => st.modifyCur fun i => { i with edgeNodes := i.edgeNodes.push t }
  | .skipping =>
    match t with
    | .ident "child" => { st with mode := .child false, pendingOpts := #[] }
    | _ => st

mutual

private def treeList : List Tok → TSt → TSt
  | [], st =>
    match st.mode with
    | .child false => { st.pushChild.1 with mode := .tail }
    | _ => st
  | t :: rest, st => treeList rest (treeTok t st)

private def treeTok (t : Tok) (st : TSt) : TSt :=
  match st.mode, t with
  | .child false, .group g =>
    let parent := st.cur
    let (st1, idx) := st.pushChild
    let sub := treeList g { st1 with cur := idx, mode := .start }
    { sub with cur := parent, mode := .tail }
  | _, _ => treeStep t st

end

/-- A `\node` statement's tree: the root and every child in preorder, or `none` where it reads no `child`. -/
public def flattenTree (toks : Array Tok) : Option (Array TreeItem × Array PDiag) :=
  let st := treeList (.ident "node" :: toks.toList) {}
  if st.tree then some (st.items, st.bad) else none

private structure TreeCfg where
  grow : Int := -90
  swap : Bool := false
  special : Int := -1
  levelDist : Sp := Dim.mm 15  -- tikz.code.tex: \tikzleveldistance=15mm
  siblingDist : Sp := Dim.mm 15  -- tikz.code.tex: \tikzsiblingdistance=15mm
  parentAnchor : Option String := none
  childAnchor : Option String := none
  scope : Array (Array Tok) := #[]
  deriving Inhabited

private def growAngle (env : List (String × Val)) (toks : List Tok) : Option Int :=
  match keyName toks with
  | some "down" | some "south" => some (-90)
  | some "up" | some "north" => some 90
  | some "left" | some "west" => some 180
  | some "right" | some "east" => some 0
  | some "north east" => some 45
  | some "north west" => some 135
  | some "south east" => some (-45)
  | some "south west" => some (-135)
  | _ =>
    match evalNum env toks.toArray with
    | .ok m => some (if m < 0 then -((-m) / 1000) else m / 1000)
    | .error _ => none

private def treeLen (cx : Cx) (env : List (String × Val)) (toks : List Tok) : Except String Sp :=
  optLen cx env toks

private def treeKey (cx : Cx) (env : List (String × Val)) (level : Nat) (cfg : TreeCfg)
    (entry : Array Tok) : Option (Except PDiag TreeCfg) :=
  let e := entry.toList.filter (· != .space)
  let key := keyPath e
  let value := (e.dropWhile (· != .sym '=')).drop 1
  if key == "grow" || key == "grow'" then
    some (match growAngle env value with
      | some a => .ok { cfg with grow := a, swap := key == "grow'", special := level }
      | none => .error (.W0334, s!"tree option {optName e} names a direction outside the \
rendered picture subset; the tree grows as before"))
  else if key == "level distance" || key == "sibling distance" then
    some (match treeLen cx env value with
      | .ok d =>
        let d := d * cx.scale / 1000
        .ok (if key == "level distance" then { cfg with levelDist := d }
          else { cfg with siblingDist := d })
      | .error err => .error (.E0333, s!"in '{key}', {err}; it is ignored"))
  else if key == "parent anchor" || key == "child anchor" then
    let set (a : Option String) : TreeCfg :=
      if key == "parent anchor" then { cfg with parentAnchor := a } else { cfg with childAnchor := a }
    some (match nameOfToks value with
      | some "border" => .ok (set none)
      | some a =>
        if (nodeAnchorOf a).isSome then .ok (set (some a))
        else .error (.W0334, s!"tree option {optName e} names an anchor outside the rendered \
picture subset; the edge meets the border")
      | none => .error (.E0333, s!"'{key}' needs an anchor name; it is ignored"))
  else if key == "missing" then some (.ok cfg)
  else none

private def applyTree (cx : Cx) (env : List (String × Val)) (level : Nat) (cfg : TreeCfg)
    (entries : Array (Array Tok)) (ev : Ev) : TreeCfg × Ev := Id.run do
  let mut cfg := cfg
  let mut ev := ev
  for entry in entries do
    let e := entry.filter (· != .space)
    unless e.isEmpty do
      match treeKey cx env level cfg e with
      | some (.ok c) => cfg := c
      | some (.error d) => ev := ev.diag d
      | none =>
        if readsOpt cx.styles e then cfg := { cfg with scope := inheritOpts cfg.scope #[e] }
        else ev := ev.diag (outsideOpt e.toList)
  return (cfg, ev)

/-- The `k`-th of `n` siblings' signed distance across the growth direction, `(2k − n − 1)·sd / 2`. -/
@[expose] public def siblingSpread (sd : Sp) (n k : Nat) : Sp :=
  (2 * (k : Int) - ((n : Int) + 1)) * sd / 2

/-- A child's offset from its parent's centre, pgf's `\tikz@grow@direction`: level distance along
the growth and, where `spread` holds, siblings spread across it. -/
public def growthOffset (grow : Int) (swap spread : Bool) (ld sd : Sp) (n k : Nat) : Sp × Sp :=
  let along : Sp × Sp := (cosDeg grow * ld / 1000, sinDeg grow * ld / 1000)
  if !spread then along else
  let across := if swap then grow - 90 else grow + 90
  let t := siblingSpread sd n k
  (along.1 + cosDeg across * t / 1000, along.2 + sinDeg across * t / 1000)

public theorem Tree.children_between (sd : Int) (n k : Nat) (hsd : 0 ≤ sd) (hk : 1 ≤ k)
    (hn : k ≤ n) :
    siblingSpread sd n 1 ≤ siblingSpread sd n k ∧ siblingSpread sd n k ≤ siblingSpread sd n n := by
  unfold siblingSpread
  constructor
  · apply Int.ediv_le_ediv (by decide)
    apply Int.mul_le_mul_of_nonneg_right _ hsd
    omega
  · apply Int.ediv_le_ediv (by decide)
    apply Int.mul_le_mul_of_nonneg_right _ hsd
    omega

private def treeStyle (cx : Cx) (name : String) (arg : Nat := 0) : Array (Array Tok) :=
  match cx.styles.lookup name with
  | none => #[]
  | some body =>
    let subst : Array Tok := Id.run do
      let mut out : Array Tok := #[]
      let mut k := 0
      for _ in [0:body.size + 1] do
        if h : k < body.size then
          if body[k] == .sym '#' && (body[k + 1]? matches some (.num 1000 _)) then
            out := out.push (.num ((arg : Int) * 1000) (toString arg))
            k := k + 2
          else
            out := out.push body[k]
            k := k + 1
        else break
      return out
    (splitTop (subst.filter (· != .space)) ',').filter (!·.isEmpty)

private def bracketOf (entries : Array (Array Tok)) : Array Tok := Id.run do
  if entries.isEmpty then return #[]
  let mut out : Array Tok := #[.sym '[']
  let mut first := true
  for e in entries do
    unless first do out := out.push (.sym ',')
    first := false
    out := out ++ e
  return out.push (.sym ']')

private def nameCoord (name : String) (anchor : Option String) : Array Tok :=
  #[.sym '(', .ident name] ++ ((anchor.map fun a => #[.sym '.', .ident a]).getD #[]) ++
    #[.sym ')']

private def evalTree (cx : Cx) (env : List (String × Val)) (items : Array TreeItem)
    (bad : Array PDiag) (ev : Ev) : Ev := Id.run do
  let mut ev := bad.foldl Ev.diag ev
  let before := ev.shapes.size
  let mut edges : Array Ir.Pic.Shape := #[]
  let mut base : TreeCfg := {}
  let outer := cx.global ++ cx.opts
  for e in outer do
    match treeKey cx env 0 base e with
    | some (.ok c) => base := c
    | some (.error d) => ev := ev.diag d
    | none => pure ()
  let edgeStyle : Array (Array Tok) :=
    if (cx.styles.lookup "edge from parent").isSome then treeStyle cx "edge from parent"
    else #[#[.ident "draw"]]
  let childNode := bracketOf (treeStyle cx "every child node")
  let mut names : Array String := #[]
  let mut cfgs : Array TreeCfg := #[]
  for it in items do
    let own := expandOpts cx.styles it.pathOpts
    match it.parent with
    | none =>
      let name := (nodeNameOf it.node).getD s!"tree {ev.nodes.length}"
      ev := evalNode cx env it.node ev (coordinate := it.coordinate) (defaultName := some name)
      let (c, ev2) := applyTree cx env 0 base own ev
      ev := ev2
      names := names.push name
      cfgs := cfgs.push c
    | some p =>
      let pname := names[p]?.getD ""
      let level := it.level
      let childOpts := expandOpts cx.styles it.childOpts
      let (c1, ev1) := applyTree cx env level (cfgs[p]?.getD base)
        (treeStyle cx "level" level ++ treeStyle cx s!"level {level}") ev
      let (c2, ev2) := applyTree cx env level c1 (treeStyle cx "every child" ++ childOpts) ev1
      let missing := childOpts.any fun e =>
        let e := e.toList.filter (· != .space)
        e == [.ident "missing"] || e == [.ident "missing", .sym '=', .ident "true"]
      let name := (nodeNameOf it.node).getD s!"{pname}-{it.index}"
      ev := ev2
      let (c3, ev3) := applyTree cx env level c2 own ev
      ev := ev3
      match ev.nodes.lookup pname with
      | none => pure ()
      | some g =>
        unless missing do
          let n := (items[p]?.map (·.children)).getD 1
          let off := growthOffset c2.grow c2.swap ((level : Int) != c2.special) c2.levelDist
            c2.siblingDist n it.index
          let off := cx.placeVec off.1 off.2
          let cxN := { cx with opts := inheritOpts cx.opts c2.scope,
                               xf := { cx.xf with e := g.x + off.1, f := g.y + off.2 } }
          ev := evalNode cxN env (childNode ++ it.node) ev (coordinate := it.coordinate)
            (defaultName := some name)
          if (ev.nodes.lookup name).isSome then
            let path := bracketOf (edgeStyle ++ expandOpts cx.styles it.edgeOpts) ++
              nameCoord pname c3.parentAnchor ++ #[.sym '-', .sym '-'] ++ it.edgeNodes ++
              nameCoord name c3.childAnchor
            let drawn := evalDraw { cx with opts := inheritOpts cx.opts c3.scope } env path
              { ev with shapes := #[] } (mode := .path)
            edges := edges ++ drawn.shapes
            ev := { drawn with shapes := ev.shapes }
      names := names.push name
      cfgs := cfgs.push c3
  return { ev with shapes := ev.shapes.extract 0 before ++ edges ++
    ev.shapes.extract before ev.shapes.size }

private inductive Item where
  | vals (vs : Array Val)
  | dots
  deriving Repr, BEq

/-- A list item's text as written, a macro in it read as its text. -/
private def itemText (env : List (String × Val)) (toks : Array Tok) : String :=
  toks.foldl (fun acc tok => acc ++ (match tok with
    | .ctrl n => ((env.lookup n).map Val.text).getD ("\\" ++ n)
    | .ident s => s
    | .num _ t => t
    | .sym c => String.singleton c
    | .space => " "
    | _ => "")) ""

private def readItems (env : List (String × Val)) (toks : Array Tok) :
    Except String (Array Item) := Id.run do
  let mut out : Array Item := #[]
  for rawPart in splitTop toks ',' do
    let part := rawPart.filter (· != .space)
    if part == #[.sym '.', .sym '.', .sym '.'] then
      out := out.push .dots
    else if part.isEmpty then
      pure ()
    else
      let mut vs : Array Val := #[]
      for rawSub in splitTop rawPart '/' do
        let sub := rawSub.filter (· != .space)
        -- pgffor binds the item's text past its leading spaces; its value is read where it is used.
        let text := itemText env (rawSub.toList.dropWhile (· == .space)).toArray
        match evalExpr env sub with
        | .ok (.num m _) => vs := vs.push (.num m text)
        | .ok (.len sp _) => vs := vs.push (.len sp text)
        | .ok v => vs := vs.push v
        | .error e =>
          match sub.toList.filter (· != .space) with
          | name@(.ident _ :: rest) =>
            if rest.all (fun t => match t with
                | .ident _ | .num _ _ | .sym '.' | .sym '-' | .sym '_' => true
                | _ => false) then
              vs := vs.push (.str ((nameOfToks name).getD ""))
            else return .error e
          | _ => return .error e
      out := out.push (.vals vs)
  return .ok out

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
          | some #[Val.num a _] => pure a
          | _ => return .error "'...' needs a number before it"
        let bound ← match items[i+1]? with
          | some (.vals #[Val.num b _]) => pure b
          | _ => return .error "'...' needs a number bound after it"
        let step ← if out.size ≥ 2 then
            match out[out.size - 2]? with
            | some #[Val.num p2 _] =>
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
              out := out.push #[rangeItem v]
            i := i + 2
          | none =>
            return .error s!"the range '{milliString prev}, ..., {milliString bound}' \
(step {milliString step}) never reaches its bound"
    else break
  return .ok out

private def bindVars (vars : Array String) (item : Array Val)
    (env : List (String × Val)) : List (String × Val) := Id.run do
  let mut out := env
  let last := item.back?.getD (.num 0 "0")
  for k in [0:vars.size] do
    if h : k < vars.size then
      out := (vars[k], (item[k]?).getD last) :: out
  return out

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

public theorem relTrichotomy_exact (a b : Int) :
    (relHolds '<' a b = true) = !(relHolds '>' a b || relHolds '=' a b) ∧
    (relHolds '>' a b = true) = !(relHolds '<' a b || relHolds '=' a b) ∧
    (relHolds '=' a b = true) = !(relHolds '<' a b || relHolds '>' a b) := by
  simp only [relHolds]
  refine ⟨?_, ?_, ?_⟩ <;> (by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp_all <;> omega)

/-- Whether an unreadable conditional ships its first branch, which it does whenever that branch
holds a statement. -/
public def condFloorTakesThen (thenS : List Stmt) : Bool := !thenS.isEmpty

/-- The branch the floor ships. -/
public def condFloor (thenS elseS : List Stmt) : List Stmt :=
  if condFloorTakesThen thenS then thenS else elseS

public theorem condFloor_accounts (thenS elseS : List Stmt)
    (h : ¬ (thenS.isEmpty ∧ elseS.isEmpty)) : (condFloor thenS elseS) ≠ [] := by
  simp only [condFloor, condFloorTakesThen, List.isEmpty_iff, not_and] at *
  cases thenS with
  | nil => exact h rfl
  | cons a as => simp

public theorem condFloor_mem (thenS elseS : List Stmt) :
    condFloor thenS elseS = thenS ∨ condFloor thenS elseS = elseS := by
  simp only [condFloor]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private def scopeKeyXf (cx : Cx) (env : List (String × Val)) (entry : List Tok) :
    Option (Except String Gfx.Affine) :=
  let key := keyPath entry
  let value := (entry.dropWhile (· != .sym '=')).drop 1
  let factor : Except String Rat := (evalNum env value.toArray).map fun m => (m : Rat) / 1000
  if key == "shift" then
    some (do
      let inner := match value with
        | [.group g] => (g.filter (· != .space)).toArray
        | ts => ts.toArray
      let (body, _) ← readCoordBody inner 0
      match (splitTop body ',').toList with
      | [xs, ys] =>
        let x ← evalComp env xs
        let y ← evalComp env ys
        return Gfx.Affine.translate (cx.compSp x) (cx.compSp y)
      | _ => throw "'shift' needs a '(x, y)' coordinate")
  else if key == "xshift" then some ((optLen cx env value).map fun d => Gfx.Affine.translate d 0)
  else if key == "yshift" then some ((optLen cx env value).map fun d => Gfx.Affine.translate 0 d)
  else if key == "scale" then some (factor.map fun f => Gfx.Affine.scale f f)
  else if key == "xscale" then some (factor.map fun f => Gfx.Affine.scale f 1)
  else if key == "yscale" then some (factor.map fun f => Gfx.Affine.scale 1 f)
  else if key == "rotate" then
    some ((evalNum env value.toArray).map fun m =>
      let (c, s) := cosSinMilli m
      let u : Rat := Gfx.Trig.unit
      ⟨c / u, s / u, -s / u, c / u, 0, 0⟩)
  else none

private def scopeXf (cx : Cx) (env : List (String × Val)) (entries : Array (Array Tok)) :
    Gfx.Affine × Array PDiag := Id.run do
  let mut m := Gfx.Affine.unit
  let mut ds : Array PDiag := #[]
  for e in entries do
    match scopeKeyXf cx env (e.toList.filter (· != .space)) with
    | some (.ok k) => m := m.compose k
    | some (.error err) => ds := ds.push (.E0333, s!"in a 'scope' key '{keyPath e.toList}', {err}; \
it is ignored")
    | none => pure ()
  return (m, ds)

private def scopeKeys (cx : Cx) (env : List (String × Val)) (entries : Array (Array Tok)) :
    Cx × Array PDiag := Id.run do
  let mut cx := cx
  let mut ds : Array PDiag := #[]
  for e in entries do
    let e := e.filter (· != .space)
    if e.isEmpty then continue
    if (scopeKeyXf cx env e.toList).isSome then continue
    match readOneDef cx.styles e.toList with
    | some st =>
      let everyOf (n : String) : Array (Array Tok) :=
        match st.lookup n with
        | some bundle => (splitTop bundle ',').filter fun x => !x.isEmpty
        | none => #[]
      cx := { cx with styles := st, everyNode := everyOf everyNodeKey,
                      everyPath := everyOf everyPathKey, everyText := everyOf everyTextKey }
    | none =>
      if e.toList == [.ident "transform", .ident "shape"] then cx := { cx with transformShape := true }
      else
      let colour := match e.toList with
        | .ident "color" :: .sym '=' :: rest => evalColor cx env rest.toArray
        | _ => evalColor cx env e
      match colour with
      | .ok c => cx := { cx with ink := c }
      | .error _ =>
        if readsOpt cx.styles e then cx := { cx with opts := inheritOpts cx.opts #[e] }
        else ds := ds.push (outsideOpt e.toList)
  return (cx, ds)

private def scopeCx (cx : Cx) (env : List (String × Val)) (opts : Array Tok) :
    Cx × Array PDiag :=
  let entries := expandOpts cx.styles opts
  let (m, ds) := scopeXf cx env entries
  let (cx2, ds2) := scopeKeys cx env entries
  ({ cx2 with xf := cx.xf.compose m }, ds ++ ds2)

private theorem scope_compose_exact (cx : Cx) (env : List (String × Val)) (opts : Array Tok)
    (p : Rat × Rat) :
    (scopeCx cx env opts).1.xf.apply p =
      cx.xf.apply ((scopeXf cx env (expandOpts cx.styles opts)).1.apply p) := by
  simp only [scopeCx]
  exact Gfx.Affine.apply_compose_exact _ _ p

private def condDrawnWords (holds : Bool) : String :=
  if holds then "the branch before '\\else' is drawn" else "only the '\\else' branch is drawn"

private def inkOf : Ir.Pic.Shape → Option (Gfx.Node Empty)
  | .ink n => some n
  | .label .. => none

private def isLabelShape : Ir.Pic.Shape → Bool
  | .label .. => true
  | .ink _ => false

private def labelAutoAnchor (ux uy : Int) (swap : Bool) : NodeAnchor :=
  let px := ux > 50
  let nx := ux < -50
  let py := uy > 50
  let ny := uy < -50
  if !swap then
    if px then (if py then .southEast else if ny then .southWest else .south)
    else if nx then (if py then .northEast else if ny then .northWest else .north)
    else (if uy > 0 then .east else .west)
  else
    if px then (if py then .northWest else if ny then .northEast else .north)
    else if nx then (if py then .southWest else if ny then .southEast else .south)
    else (if uy > 0 then .west else .east)

private def clipFlush (g : Gfx.Geom) (run : Array (Gfx.Node Empty))
    (acc : Array Ir.Pic.Shape) : Array Ir.Pic.Shape :=
  if run.isEmpty then acc
  else acc.push (.ink (.group Gfx.Affine.unit #[{ geom := g, rule := .nonzero }] Gfx.Alpha.opaque run))

private def clipRuns (g : Gfx.Geom) (run : Array (Gfx.Node Empty))
    (acc : Array Ir.Pic.Shape) : List Ir.Pic.Shape → Array Ir.Pic.Shape
  | [] => clipFlush g run acc
  | .ink n :: rest => clipRuns g (run.push n) acc rest
  | s@(.label ..) :: rest => clipRuns g #[] ((clipFlush g run acc).push s) rest

private def clipAfter (cx : Cx) (before : Ev) (g : Gfx.Geom) (inner : Ev) : Ev :=
  let labels := inner.shapes.filter isLabelShape
  let inside (s : Ir.Pic.Shape) : Bool := match s, g with
    | .label x y content _ scale align, .rect rx ry rw rh =>
      let ((a, b), (c, d)) := Ir.Pic.labelGlyphBox x y align (cx.metric content scale)
      rx ≤ a && ry ≤ b && c ≤ rx + rw && d ≤ ry + rh
    | _, _ => false
  let ev := { inner with shapes := before.shapes ++ clipRuns g #[] #[] inner.shapes.toList
                         borders := before.borders ++ g.hull.toArray }
  if labels.all inside then ev
  else ev.diag (.W0334, "a node after a '\\clip' is set whole; the clip reaches only the \
picture's paths")

private theorem clipFlush_mem (g : Gfx.Geom) (run : Array (Gfx.Node Empty))
    (acc : Array Ir.Pic.Shape) :
    (∀ s ∈ acc, s ∈ clipFlush g run acc) ∧
      (run.isEmpty = false → Ir.Pic.Shape.ink (.group Gfx.Affine.unit
        #[{ geom := g, rule := .nonzero }] Gfx.Alpha.opaque run) ∈ clipFlush g run acc) := by
  unfold clipFlush
  split
  · rename_i h
    exact ⟨fun _ hs => hs, fun hne => by simp [h] at hne⟩
  · exact ⟨fun _ hs => Array.mem_push.mpr (.inl hs), fun _ => Array.mem_push_self⟩

private theorem run_nonempty {α : Type} (run : Array α) (a : α) (h : a ∈ run) :
    run.isEmpty = false := by
  cases hr : run.isEmpty with
  | false => rfl
  | true => simp [Array.isEmpty_iff.mp hr] at h

private theorem clipRuns_covers (g : Gfx.Geom) :
    ∀ (run : Array (Gfx.Node Empty)) (acc : Array Ir.Pic.Shape) (ss : List Ir.Pic.Shape),
      (∀ s ∈ acc, s ∈ clipRuns g run acc ss) ∧
      (∀ n ∈ run, ∃ r, n ∈ r ∧ Ir.Pic.Shape.ink (.group Gfx.Affine.unit
          #[{ geom := g, rule := .nonzero }] Gfx.Alpha.opaque r) ∈ clipRuns g run acc ss) ∧
      (∀ s ∈ ss, isLabelShape s → s ∈ clipRuns g run acc ss) ∧
      (∀ n, Ir.Pic.Shape.ink n ∈ ss → ∃ r, n ∈ r ∧ Ir.Pic.Shape.ink (.group Gfx.Affine.unit
          #[{ geom := g, rule := .nonzero }] Gfx.Alpha.opaque r) ∈ clipRuns g run acc ss)
  | run, acc, [] => by
    obtain ⟨hkeep, hgroup⟩ := clipFlush_mem g run acc
    exact ⟨hkeep, fun n hn => ⟨run, hn, hgroup (run_nonempty run n hn)⟩,
      fun s hs => by simp at hs, fun n hn => by simp at hn⟩
  | run, acc, .ink m :: rest => by
    obtain ⟨hacc, hrun, hlab, hink⟩ := clipRuns_covers g (run.push m) acc rest
    refine ⟨hacc, fun n hn => hrun n (Array.mem_push.mpr (.inl hn)), fun s hs hl => ?_,
      fun n hn => ?_⟩
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp [isLabelShape] at hl
      · exact hlab s hs hl
    · simp only [List.mem_cons] at hn
      rcases hn with hn | hn
      · have he : n = m := Ir.Pic.Shape.ink.inj hn
        subst he
        exact hrun n (Array.mem_push_self)
      · exact hink n hn
  | run, acc, (.label x y content color scale align) :: rest => by
    obtain ⟨hacc, _, hlab, hink⟩ := clipRuns_covers g #[]
      ((clipFlush g run acc).push (.label x y content color scale align)) rest
    obtain ⟨hkeep, hgroup⟩ := clipFlush_mem g run acc
    have hin : ∀ s ∈ clipFlush g run acc, s ∈
        clipRuns g #[] ((clipFlush g run acc).push (.label x y content color scale align))
          rest := fun s hs => hacc s (Array.mem_push.mpr (.inl hs))
    refine ⟨fun s hs => hin s (hkeep s hs), fun n hn => ⟨run, hn, hin _
      (hgroup (run_nonempty run n hn))⟩, fun s hs hl => ?_, fun n hn => ?_⟩
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hacc _ (Array.mem_push_self)
      · exact hlab s hs hl
    · simp only [List.mem_cons] at hn
      rcases hn with hn | hn
      · cases hn
      · exact hink n hn

private theorem clip_covers (cx : Cx) (before inner : Ev) (g : Gfx.Geom) :
    (∀ s ∈ before.shapes, s ∈ (clipAfter cx before g inner).shapes) ∧
    (∀ s ∈ inner.shapes, isLabelShape s → s ∈ (clipAfter cx before g inner).shapes) ∧
    (∀ n, Ir.Pic.Shape.ink n ∈ inner.shapes →
      ∃ r, n ∈ r ∧ Ir.Pic.Shape.ink (.group Gfx.Affine.unit #[{ geom := g, rule := .nonzero }]
        Gfx.Alpha.opaque r) ∈ (clipAfter cx before g inner).shapes) := by
  have hdiag : ∀ (e : Ev) (d : PDiag), (e.diag d).shapes = e.shapes := by
    intro e d
    unfold Ev.diag
    split <;> rfl
  have hshapes : (clipAfter cx before g inner).shapes =
      before.shapes ++ clipRuns g #[] #[] inner.shapes.toList := by
    unfold clipAfter
    dsimp only
    split
    · rfl
    · exact hdiag _ _
  obtain ⟨_, _, hlab, hink⟩ := clipRuns_covers g #[] #[] inner.shapes.toList
  refine ⟨fun s hs => ?_, fun s hs hl => ?_, fun n hn => ?_⟩
  · rw [hshapes]
    exact Array.mem_append_left _ hs
  · rw [hshapes]
    exact Array.mem_append_right _ (hlab s (Array.mem_toList_iff.mpr hs) hl)
  · obtain ⟨r, hr, hg⟩ := hink n (Array.mem_toList_iff.mpr hn)
    rw [hshapes]
    exact ⟨r, hr, Array.mem_append_right _ hg⟩

mutual

private def leaksOne : Stmt → Bool
  | .grouped _ body => leaksList body
  | .cond _ _ t e => leaksList t || leaksList e
  | .foreach _ _ body => leaksList body
  | .clip _ | .scope _ _ | .fill _ | .node _ | .draw _ | .path _ | .bbox _ | .set _ _ _
  | .coordinate _ | .filldraw _ | .setColor _ | .setDecl _ | .shade _ _ => false

private def leaksList : List Stmt → Bool
  | [] => false
  | s :: rest => (s matches .clip _) || leaksOne s || leaksList rest

end

private def labelAngleOf : String → Option Int
  | "right" => some 0
  | "above right" => some 45000
  | "above" => some 90000
  | "above left" => some 135000
  | "left" => some 180000
  | "below left" => some 225000
  | "below" => some 270000
  | "below right" => some 315000
  | _ => none

private def readExtra (env : List (String × Val)) (spec : List Tok) :
    Except String (Array Tok × Option Int × List Tok) := do
  let ts := match spec.filter (· != .space) with
    | [.group g] => g
    | _ => spec
  let ts := ts.dropWhile (· == .space)
  let (opts, rest) : List Tok × List Tok :=
    if ts.head? == some (.sym '[') then
      ((ts.drop 1).takeWhile (· != .sym ']'), ((ts.drop 1).dropWhile (· != .sym ']')).drop 1)
    else ([], ts)
  let (pos, text) : List Tok × List Tok :=
    match rest.findIdx? (· == .sym ':') with
    | some k => (rest.take k, rest.drop (k + 1))
    | none => ([], rest)
  let text := match text.filter (· != .space) with
    | [.group g] => g
    | _ => text
  let angle : Option Int ← match keyName (pos.filter (· != .space)) with
    | none => pure (some 90000)
    | some "center" => pure none
    | some n =>
      match labelAngleOf n with
      | some a => pure (some a)
      | none => (evalNum env pos.toArray).map some
  return (opts.toArray, angle, text)

private def sectorAnchor (m : Int) : NodeAnchor :=
  let d := ((m / 1000) % 360 + 360) % 360
  if d < 4 then .west else if d < 87 then .southWest else if d < 94 then .south
  else if d < 177 then .southEast else if d < 184 then .east else if d < 267 then .northEast
  else if d < 274 then .north else if d < 357 then .northWest else .west

private def anchorSpelling : NodeAnchor → List String
  | .center => ["center"]
  | .north => ["north"]
  | .south => ["south"]
  | .east => ["east"]
  | .west => ["west"]
  | .northEast => ["north", "east"]
  | .northWest => ["north", "west"]
  | .southEast => ["south", "east"]
  | .southWest => ["south", "west"]
  | .base => ["base"]
  | .baseEast => ["base", "east"]
  | .baseWest => ["base", "west"]

private def drainAfter (cx : Cx) (env : List (String × Val)) (ev : Ev) : Ev := Id.run do
  let pend := ev.after
  let mut ev := { ev with after := #[] }
  let ex := (cx.metric #[.text "x"] 1000).ex
  let at0 : Cx := { cx with xf := Gfx.Affine.unit, scale := 1000 }
  for x in pend do
    let what := if x.pin then "pin" else "label"
    match readExtra env x.spec with
    | .error e => ev := ev.diag (.E0333, s!"in a node's '{what}', {e}; it is not drawn")
    | .ok (opts, angle, text) =>
      let g := x.main
      let dist : Sp := x.dist.getD (3 * ex)
      let (pt, an) : (Sp × Sp) × NodeAnchor := match angle with
        | none => ((g.x, g.y), .center)
        | some m =>
          let (c, s) := cosSinMilli m
          let border := (Anchor.node g).toward (g.x + c / 1024, g.y + s / 1024)
          let dx := border.1 - g.x
          let dy := border.2 - g.y
          let n := isqrt (dx * dx + dy * dy)
          if n == 0 then
            let u := Gfx.Trig.unit
            ((g.x + dist * c / u, g.y + dist * s / u), sectorAnchor m)
          else
            ((border.1 + dist * dx / n, border.2 + dist * dy / n),
             labelAutoAnchor (dy * 1000 / n) (-(dx * 1000 / n)) false)
      let mut toks : Array Tok := #[.sym '[', .ident "anchor", .sym '=']
      for w in anchorSpelling an do toks := toks.push (.ident w)
      unless opts.isEmpty do
        toks := toks.push (.sym ',')
        for t in opts do toks := toks.push t
      for t in [Tok.sym ']', .ident "at", .sym '(', .ctrl " extra x", .sym ',', .ctrl " extra y",
          .sym ')', .group text] do
        toks := toks.push t
      let env' := (" extra x", Val.length pt.1) :: (" extra y", Val.length pt.2) :: env
      let bordersBefore := ev.borders.size
      ev := evalNode at0 env' toks ev
      unless ev.after.isEmpty do
        ev := { ev with after := #[] }.diag (.W0334, s!"a {what}'s own label or pin is outside \
the rendered picture subset; it is dropped")
      if x.pin then
        if let some ((bx0, by0), (bx1, by1)) := ev.borders[bordersBefore]? then
          let pg : NodeGeom :=
            { x := (bx0 + bx1) / 2, y := (by0 + by1) / 2, a := (bx1 - bx0) / 2, b := (by1 - by0) / 2 }
          let p1 := (Anchor.node g).toward (pg.x, pg.y)
          let p2 := (Anchor.node pg).toward (g.x, g.y)
          -- `every pin edge` is `help lines`: xcolor's gray at 0.2 pt.
          let help : Ir.Pic.Stroke :=
            { color := { r := 128, g := 128, b := 128 }
              width := Dim.pt 2 / 10 -- help lines/.style={color=gray,line width=0.2pt} (tikz.code.tex)
              dash := .solid }
          ev := { ev with shapes := ev.shapes.push (.edge #[.line p1.1 p1.2 p2.1 p2.2] help none) }
  return ev

mutual

private def evalList (cx : Cx) : List Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | [], env, ev => (env, ev)
  -- A colour or a font declared among statements holds for the rest of
  -- their group, as TeX's own declarations do.
  | .setColor spec :: rest, env, ev =>
    match evalColor cx env spec with
    | .ok c => evalList { cx with ink := c } rest env ev
    | .error e =>
      evalList cx rest env (ev.diag (.E0333, s!"in '\\color', {e}; the colour is dropped"))
  | .setDecl n :: rest, env, ev => evalList { cx with decls := cx.decls.push n } rest env ev
  | s :: rest, env, ev =>
    let (env2, ev2) := evalOne cx s env ev
    let ev2 := if leaksOne s && !rest.isEmpty then
        ev2.diag (.W0334, "a '\\clip' inside a group, a branch or a loop lasts to the end of \
its scope in pgf; the statements after it are drawn unclipped")
      else ev2
    match ev2.clipGeom with
    | some g =>
      let (env3, inner) := evalList cx rest env2 { ev2 with clipGeom := none, shapes := #[] }
      (env3, clipAfter cx ev2 g inner)
    | none => evalList cx rest env2 ev2
  -- The context changes inside a group, so the measure is stated over the statements alone.
  termination_by ss _ _ => (sizeOf ss, 0, 0)

private def evalOne (cx : Cx) : Stmt → List (String × Val) → Ev →
    List (String × Val) × Ev
  | .fill toks, env, ev =>
    -- A fill of anything but one rectangle is a path filled (TikZ manual §14.1).
    if !fillIsRect toks || fillBracketIsKeys cx env toks || !cx.axisAligned then
      (env, evalDraw cx env toks ev (mode := .fill)) else
    match evalFill cx env toks with
    | .ok shape =>
      let ev := if cx.everyPath.isEmpty then ev else
        ev.diag (.W0334, "an 'every path' key on a '\\fill' is outside the \
rendered picture subset; the keys are dropped")
      (env, { ev with shapes := ev.shapes.push shape })
    | .error d => (env, ev.diag d)
  | .node toks, env, ev =>
    match flattenTree toks with
    | some (items, bad) => (env, drainAfter cx env (evalTree cx env items bad ev))
    | none => (env, drainAfter cx env (evalNode cx env toks ev))
  | .coordinate toks, env, ev => (env, drainAfter cx env (evalNode cx env toks ev (coordinate := true)))
  | .shade toks draw, env, ev =>
    (env, evalDraw cx env toks ev (mode := if draw then .shadedraw else .shade))
  | .clip toks, env, ev => (env, evalDraw cx env toks ev (mode := .clip))
  | .draw toks, env, ev => (env, evalDraw cx env toks ev)
  | .path toks, env, ev => (env, evalDraw cx env toks ev (mode := .path))
  | .filldraw toks, env, ev => (env, evalDraw cx env toks ev (mode := .filldraw))
  -- A group's declarations stay inside it, its macros too (TeXbook ch. 5).
  | .grouped color body, env, ev =>
    match color with
    | none =>
      let (_, ev2) := evalList cx body env ev
      (env, ev2)
    | some spec =>
      match evalColor cx env spec with
      | .ok c =>
        let (_, ev2) := evalList { cx with ink := c } body env ev
        (env, ev2)
      | .error e =>
        let (_, ev2) := evalList cx body env
          (ev.diag (.E0333, s!"in '\\textcolor', {e}; the colour is dropped"))
        (env, ev2)
  | .setColor _, env, ev => (env, ev)
  | .setDecl _, env, ev => (env, ev)
  | .scope opts body, env, ev =>
    let (cx2, ds) := scopeCx cx env opts
    let (_, ev2) := evalList cx2 body env (ds.foldl Ev.diag ev)
    (env, ev2)
  | .bbox toks, env, ev =>
    match evalBBox cx env toks with
    | .ok b =>
      -- pgf never shrinks a box already established (§15.8).
      let before := ev.shapes.map (Ir.Pic.Shape.inkBox cx.metric) ++ ev.borders
      let b := if before.isEmpty then b else Gfx.Box.join (Gfx.Box.hull before) b
      let b := match ev.declared with
        | some d => Gfx.Box.join d b
        | none => b
      (env, { ev with declared := some b })
    | .error d => (env, ev.diag d)
  | .set name expr setMode, env, ev =>
    -- Truncation toward zero, as `\pgfmathtruncatemacro` does; `Int` division floors a negative.
    let floorUnit (m : Int) : Int := if m ≥ 0 then m / 1000 * 1000 else -((-m) / 1000 * 1000)
    match evalExpr env expr, setMode with
    | .ok (.num m t), .plain => ((name, Val.num m t) :: env, ev)
    | .ok (.num m _), .trunc =>
      ((name, Val.num (floorUnit m) (milliString (floorUnit m))) :: env, ev)
    -- A unitless length is points, as `\pgfmathsetlengthmacro` reads it.
    | .ok (.num m _), .length => ((name, Val.length (milliPt m)) :: env, ev)
    | .ok (.len sp _), .plain => ((name, Val.num (spMilliPt sp) (texPoints sp)) :: env, ev)
    | .ok (.len sp _), .trunc =>
      let m := floorUnit (spMilliPt sp)
      ((name, Val.num m (milliString m)) :: env, ev)
    | .ok (.len sp _), .length => ((name, Val.length sp) :: env, ev)
    | .ok (.str s), .plain => ((name, Val.str s) :: env, ev)
    | .ok (.str s), .trunc =>
      (env, ev.diag (.E0333, s!"in '\\pgfmathtruncatemacro' of '\\{name}', '{s}' \
where a number is needed; the macro is not set"))
    | .ok (.str s), .length =>
      (env, ev.diag (.E0333, s!"in '\\pgfmathsetlengthmacro' of '\\{name}', '{s}' \
where a length is needed; the macro is not set"))
    | .error e, _ =>
      (env, ev.diag (.E0333, s!"in '\\pgfmathsetmacro' of '\\{name}', {e}; the macro \
is not set"))
  | .foreach vars list body, env, ev =>
    match readItems env list with
    | .error e => (env, ev.diag (.E0333, s!"in a '\\foreach' list, {e}"))
    | .ok items =>
      match expandItems items with
      | .error e => (env, ev.diag (.E0333, s!"in a '\\foreach' list, {e}"))
      | .ok expanded =>
        -- The loop's bindings are scoped to its body: the caller's environment comes back.
        (env, evalForeach cx vars body expanded.toList env ev)
  -- One branch runs and the other is not evaluated, so its nodes never register.
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
  termination_by s _ _ => (sizeOf s, 0, 0)

private def evalForeach (cx : Cx) (vars : Array String) (body : List Stmt) :
    List (Array Val) → List (String × Val) → Ev → Ev
  | [], _, ev => ev
  | item :: rest, env, ev =>
    let (_, ev2) := evalList cx body (bindVars vars item env) ev
    evalForeach cx vars body rest env ev2
  termination_by items _ _ => (sizeOf body, 1, sizeOf items)

end

private theorem colorGroup_exact (cx : Cx) (spec : Array Tok) (body : List Stmt)
    (env : List (String × Val)) (ev : Ev) (c : Ir.Color) (h : evalColor cx env spec = .ok c) :
    evalOne cx (.grouped (some spec) body) env ev =
      (env, (evalList { cx with ink := c } body env ev).2) := by
  rw [evalOne]
  simp only [h]

private def dedupNodes (ns : List (String × NodeGeom)) :
    List (String × NodeGeom) := Id.run do
  let mut seen : Array String := #[]
  let mut out : Array (String × NodeGeom) := #[]
  for (n, g) in ns do
    unless seen.contains n do
      seen := seen.push n
      out := out.push (n, g)
  return out.toList

/-- Re-runs the walk with the previous pass's node table until unresolved references stop falling. -/
public def evalFixed (cx : Cx) (sts : List Stmt) : Ev := Id.run do
  let (_, ev0) := evalList cx sts [] {}
  if ev0.deferred == 0 then return ev0
  let mut prev := ev0
  for _ in [0:ev0.deferred] do
    let (_, ev) := evalList cx sts [] { nodes := dedupNodes prev.nodes }
    if ev.deferred == 0 || ev.deferred ≥ prev.deferred then return ev
    prev := ev
  return prev

public theorem nodeExtent_covers (cx : Cx) (sts : List Stmt)
    (x y : Sp) (content : Array Ir.Inline) (color : Ir.Color)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (baseline : Option Sp)
    (hs : Ir.Pic.Shape.label x y content color scale align ∈ (evalFixed cx sts).shapes)
    (hd : (evalFixed cx sts).declared = none) :
    Gfx.Box.le (Ir.Pic.labelTextBox x y align (cx.metric content scale))
      (((evalFixed cx sts).toPicture baseline).box cx.metric) :=
  Ev.labelExtent_covers _ _ _ _ _ _ _ _ _ hs hd

private structure Macro where
  arity : Nat
  body : List Tok
  deriving Repr, Inhabited

private def walkOwns (n : String) : Bool :=
  TikzCommands.walkOwned.contains n || (condKindOf n).isSome

private def boundNames (ts : Array Tok) : List String := Id.run do
  let mut out : List String := []
  let mut inVars := false
  for k in [0:ts.size] do
    match ts[k]? with
    | some (.ctrl "foreach") => inVars := true
    | some (.ctrl "pgfmathsetmacro") | some (.ctrl "pgfmathtruncatemacro")
      | some (.ctrl "pgfmathsetlengthmacro") =>
      match ts[k+1]?, ts[k+2]? with
      | some (.group [.ctrl n]), _ => out := n :: out
      | some .space, some (.group [.ctrl n]) => out := n :: out
      | _, _ => pure ()
    | some (.ctrl v) => if inVars then out := v :: out
    | some (.ident "in") => inVars := false
    | _ => pure ()
  return out

mutual

private def substList (args : Array (List Tok)) (acc : Array Tok) :
    List Tok → Array Tok
  | [] => acc
  | .sym '#' :: .num m _ :: rest =>
    substList args (((args[(m / 1000 - 1).toNat]?).getD []).foldl Array.push acc) rest
  | t :: rest => substList args (acc.push (substTok args t)) rest

private def substTok (args : Array (List Tok)) : Tok → Tok
  | .group g => .group (substList args #[] g).toList
  | .ctrl n => .ctrl n
  | .ident s => .ident s
  | .num m t => .num m t
  | .sym c => .sym c
  | .space => .space
  | .math d b p => .math d b p
  | .other w => .other w

end

private def numCondHead (n : String) : Bool :=
  (condKindOf n) matches some (.num _)

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

private def expandList (tbl : List (String × Macro)) (acc : Array Tok) :
    List Tok → Nat → Array Tok
  | [], _ => acc
  -- An arithmetic conditional's test is read as written, its macros unexpanded.
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
  | .num m t => .num m t
  | .sym c => .sym c
  | .space => .space
  | .math d b p => .math d b p
  | .other w => .other w

end

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

private def refArityList (acc : Nat) (prevHash : Bool) : List Tok → Nat
  | [] => acc
  | .sym '#' :: rest => refArityList acc true rest
  | .num m _ :: rest =>
    refArityList (if prevHash then max acc (m / 1000).toNat else acc) false rest
  | t :: rest => refArityList (max acc (refArityTok t)) false rest

private def refArityTok : Tok → Nat
  | .group g => refArityList 0 false g
  | .ctrl _ => 0
  | .ident _ => 0
  | .num _ _ => 0
  | .sym _ => 0
  | .space => 0
  | .math _ _ _ => 0
  | .other _ => 0

end

private def refArity (body : List Tok) : Nat := refArityList 0 false body

private def readMacro (line : String) : Option Macro := Id.run do
  let (toks, _) := Lex.lex "" line
  let (raws, _) := Parse.parse "" toks
  let mut bodyAt : Option Nat := none
  for k in [0:raws.size] do
    if raws[k]? matches some (.group _ _) then bodyAt := some k
  let some bi := bodyAt | return none
  let some (.group body _) := raws[bi]? | return none
  let bodyToks := (ofRaws body).toList
  let mut declared : Option Nat := none
  for k in [0:bi] do
    match raws[k]?, raws[k+1]?, raws[k+2]? with
    | some (.sym '[' _), some (.word d _), some (.sym ']' _) =>
      if declared.isNone && !d.isEmpty && d.toList.all Char.isDigit then
        declared := d.toNat?
    | _, _, _ => pure ()
  return some { arity := declared.getD (refArity bodyToks), body := bodyToks }

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

/-- The document's definitions of TikZ's installed commands, which TikZ restores inside node text. -/
private def nodeMacroTable (names : Array (String × String)) (ts : Array Tok) :
    List (String × Macro) := Id.run do
  let bound := boundNames ts
  let mut out : List (String × Macro) := []
  for (n, line) in names do
    if TikzCommands.installed.contains n && !bound.contains n then
      if let some m := readMacro line then out := (n, m) :: out
  return out

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
      | [_, ys] => (evalComp [] ys).map ({ cx with scale := 1000 }).compSp
      | _ =>
        let nm := String.join (inner.toList.map fun (t : Tok) => match t with
          | .ident s => s
          | .num _ t => t
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

/-- Elaborates one `tikzpicture` body: its options, statements and unrolled evaluation, everything
outside the subset named. -/
public def elabPicture (pal : Ir.Palette) (raws : Array Parse.Raw)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag :=
      fun d rs => (.math d (Parse.rawSrc rs), #[]))
    (sets : Array (Span × Array Parse.Raw) := #[])
    (metric : Ir.Pic.LabelMetric := fun _ _ => {})
    (macros : Array (String × String) := #[])
    (argStyles : List (String × Ir.Style))
    (ladder : List (String × Nat))
    (declStyles : List (String × Ir.Style)) (bodySize : Sp)
    (locate : Pos → Option Span := fun _ => none) (metaArrows : Bool := false)
    (outerDecls : Array String := #[]) :
    Ir.Pic.Picture × Array PDiag := Id.run do
  let raw := ofRawsAt locate raws
  let toks := expandMacros (macroTable ladder declStyles macros raw) raw
  let nodeTable := nodeMacroTable macros raw
  let mut scale : Int := 1000
  let mut styles := documentStyles (sets.map ofSetting)
  let mut dist : Sp × Sp := (Dim.mm 10, Dim.mm 10)
  for setting in sets do
    for entry in splitTop (ofSetting setting) ',' do
      if let some d := readNodeDistance (entry.toList.filter (· != .space)) then
        dist := d
  let mut transformShape := false
  let mut ink0 : Option Ir.Color := none
  let probe : Cx := { pal := pal, math := math }
  let mut inherited : Array (Array Tok) := #[]
  let mut diags : Array PDiag := #[]
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
        -- `transform shape`: nodes take the picture's scale (pgf manual §25.4).
        | [.ident "transform", .ident "shape"] => transformShape := true
        | [.ident "baseline"] => baselineSpec := some []
        | .ident "baseline" :: .sym '=' :: rest => baselineSpec := some rest
        | .ident "node" :: .ident "distance" :: rest =>
          match readNodeDistance (.ident "node" :: .ident "distance" :: rest) with
          | some d => dist := d
          | none =>
            diags := diags.push (.E0333, "in 'node distance', a length like \
'1cm' (or '1cm and 2cm') is needed; it is ignored")
        -- A bare name that resolves is a style applied in the picture's own scope.
        | [.ident n] =>
          match styles.lookup n with
          | some bundle => inherited := inherited ++ splitTop bundle ','
          | none =>
            if readsOpt styles #[.ident n] then inherited := inherited.push #[.ident n]
            else match evalColor probe [] #[.ident n] with
              | .ok c => ink0 := some c
              | .error _ => diags := diags.push (outsideOpt [.ident n])
        | [] => pure ()
        | .ident "color" :: .sym '=' :: rest =>
          match evalColor probe [] rest.toArray with
          | .ok c => ink0 := some c
          | .error e => diags := diags.push (.E0333, s!"in the picture's 'color=', {e}; it is ignored")
        | o :: rest =>
          if readsOpt styles (o :: rest).toArray then
            inherited := inherited.push (o :: rest).toArray
          else match evalColor probe [] (o :: rest).toArray with
            | .ok c => ink0 := some c
            | .error _ => diags := diags.push (outsideOpt (o :: rest))
    else
      diags := diags.push (.E0333, "the picture's options miss their ']'")
  -- `\selectfont` selects what the declarations before it chose.
  let declNames := "selectfont" :: ladder.map (·.1) ++ declStyles.map (·.1)
  let st := (parseList (toks.toList.drop i) { declNames }).drain
  let everyOf (n : String) : Array (Array Tok) :=
    match styles.lookup n with
    | some bundle => (splitTop bundle ',').filter fun e => !e.isEmpty
    | none => #[]
  let cx : Cx := { pal := pal, scale := scale, metaArrows := metaArrows
                   styles := styles, transformShape := transformShape
                   global := documentOpts (sets.map ofSetting)
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
                   decls := outerDecls
                   ink := ink0.getD Ir.Color.black
                   parseGap := st.bad.any fun d => d.1 == .W0334
                   nodeText := fun ts => (expandMacros nodeTable ts.toArray).toList }
  let ev := evalFixed cx st.out.toList
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
  let mut seen : Array String := #[]
  let mut out : Array PDiag := #[]
  for d in all do
    unless seen.contains d.2 do
      seen := seen.push d.2
      out := out.push d
  return (ev.toPicture baseline, out)

/-- The stand-in for a picture whose every construct was refused: a 1 in outlined box carrying the
code, as an image placeholder is drawn. -/
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


namespace Cd

/-- tikz-cd's row separations by name, in milli-em (tikzlibrarycd.code.tex); `colSepEm` holds the
columns'. -/
public def rowSepEm : List (String × Int) :=
  [("huge", 3600), ("large", 2700), ("normal", 1800), ("scriptsize", 1350), ("small", 900),
   ("tiny", 450)]

public def colSepEm : List (String × Int) :=
  [("huge", 4800), ("large", 3600), ("normal", 2400), ("scriptsize", 1800), ("small", 1200),
   ("tiny", 600)]

/-- One arrow label as written: its math, and the keys around it (`swap`,
`description`, a colour). -/
structure Label where
  content : Array Parse.Raw
  swap : Bool := false
  description : Bool := false
  keys : Array (Array Tok) := #[]
  deriving Inhabited

/-- One arrow as its cell wrote it: the target's offset in rows and columns,
its keys, and its labels. -/
structure Arrow where
  dr : Int := 0
  dc : Int := 0
  keys : Array (Array Tok) := #[]
  labels : Array Label := #[]
  deriving Inhabited

private def trimRaws (rs : Array Parse.Raw) : Array Parse.Raw :=
  let a := rs.toList.dropWhile (· matches .space)
  (a.reverse.dropWhile (· matches .space)).reverse.toArray

private def splitEntries (raws : Array Parse.Raw) : Array (Array Parse.Raw) := Id.run do
  let mut out : Array (Array Parse.Raw) := #[]
  let mut cur : Array Parse.Raw := #[]
  for r in raws do
    match r with
    | .word s p =>
      let mut first := true
      for piece in s.splitOn "," do
        unless first do
          out := out.push (trimRaws cur)
          cur := #[]
        first := false
        unless piece.isEmpty do cur := cur.push (.word piece p)
    | r => cur := cur.push r
  out := out.push (trimRaws cur)
  return out.filter (!·.isEmpty)

private def readBracket (raws : Array Parse.Raw) (i : Nat) : Option (Array Parse.Raw × Nat) := Id.run do
  unless raws[i]? matches some (.sym '[' _) do return none
  let mut depth : Nat := 0
  let mut inner : Array Parse.Raw := #[]
  for k in [i + 1:raws.size] do
    match raws[k]? with
    | some (.sym '[' p) =>
      depth := depth + 1
      inner := inner.push (.sym '[' p)
    | some (.sym ']' p) =>
      if depth == 0 then return some (inner, k + 1)
      depth := depth - 1
      inner := inner.push (.sym ']' p)
    | some r => inner := inner.push r
    | none => pure ()
  return none

private def skipSp (raws : Array Parse.Raw) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:raws.size] do
    if raws[j]? matches some .space then j := j + 1 else break
  return j

private def dirOf (s : String) : Option (Int × Int) :=
  if s.isEmpty then none else
  s.toList.foldl (fun acc c => acc.bind fun (r, k) => match c with
    | 'r' => some (r, k + 1)
    | 'l' => some (r, k - 1)
    | 'd' => some (r + 1, k)
    | 'u' => some (r - 1, k)
    | _ => none) (some (0, 0))

private def keyEntries (raws : Array Parse.Raw) : Array (Array Tok) :=
  (splitTop ((ofRaws raws).filter (· != .space)) ',').filter (!·.isEmpty)

private def quotedLabel (entry : Array Parse.Raw) : Option Label := Id.run do
  match (entry[0]? : Option Parse.Raw) with
  | some (.word s p) =>
    unless s.startsWith "\"" do return none
    let body := (s.drop 1).toString
    match body.splitOn "\"" with
    | inner :: rest@(_ :: _) =>
      let after := "\"".intercalate rest
      return some (labelTail #[.word inner p] after (entry.extract 1 entry.size) p)
    | _ =>
      let mut content : Array Parse.Raw := if body.isEmpty then #[] else #[.word body p]
      for k in [1:entry.size] do
        match entry[k]? with
        | some (.word w q) =>
          match w.splitOn "\"" with
          | before :: rest@(_ :: _) =>
            unless before.isEmpty do content := content.push (.word before q)
            return some (labelTail content ("\"".intercalate rest) (entry.extract (k + 1) entry.size) q)
          | _ => content := content.push (.word w q)
        | some r => content := content.push r
        | none => pure ()
      return some { content }
  | _ => return none
where
  labelTail (content : Array Parse.Raw) (after : String) (rest : Array Parse.Raw) (p : Pos) : Label := Id.run do
    let mut l : Label := { content }
    let mut tail := after
    if tail.startsWith "'" then
      l := { l with swap := true }
      tail := (tail.drop 1).toString
    let mut raws : Array Parse.Raw := if tail.isEmpty then #[] else #[.word tail p]
    for r in rest do
      match r with
      | .group g _ => raws := raws ++ g
      | r => raws := raws.push r
    for e in keyEntries raws do
      match keyPath e.toList with
      | "description" => l := { l with description := true }
      | "swap" | "'" => l := { l with swap := !l.swap }
      | _ => l := { l with keys := l.keys.push e }
    return l

private def arrowEntry (a : Arrow) (entry : Array Parse.Raw) : Arrow :=
  match quotedLabel entry with
  | some l => { a with labels := a.labels.push l }
  | none =>
    let es := keyEntries entry
    match es.toList with
    | [e] =>
      match (keyName e.toList).bind dirOf with
      | some (r, k) => { a with dr := a.dr + r, dc := a.dc + k }
      | none => { a with keys := a.keys.push e }
    | _ => { a with keys := a.keys ++ es }

private def splitCell (raws : Array Parse.Raw) : Array Parse.Raw × Array Arrow := Id.run do
  let shortcuts : List (String × String) :=
    [("rar", "r"), ("lar", "l"), ("dar", "d"), ("uar", "u"), ("drar", "dr"), ("dlar", "dl"),
     ("urar", "ur"), ("ular", "ul")]
  let mut content : Array Parse.Raw := #[]
  let mut arrows : Array Arrow := #[]
  let mut i := 0
  for _ in [0:raws.size + 1] do
    match (raws[i]? : Option Parse.Raw) with
    | none => break
    | some (.ctrl n p) =>
      let short := List.lookup n shortcuts
      if n == "arrow" || n == "ar" || short.isSome then
        let mut a : Arrow := {}
        if let some d := short then
          if let some (r, k) := dirOf d then a := { a with dr := r, dc := k }
        let mut j := skipSp raws (i + 1)
        if let some (inner, next) := readBracket raws j then
          for e in splitEntries inner do a := arrowEntry a e
          j := skipSp raws next
        -- tikz-cd's legacy spelling: a direction group, then labels.
        if short.isNone then
          if let some (.group g _) := raws[j]? then
            if let some (r, k) := dirOf (Parse.rawSrc g).trimAscii.toString then
              a := { a with dr := a.dr + r, dc := a.dc + k }
            j := skipSp raws (j + 1)
            for _ in [0:raws.size] do
              let (lkeys, k) := match readBracket raws j with
                | some (inner, next) => (keyEntries inner, skipSp raws next)
                | none => (#[], j)
              match raws[k]? with
              | some (.group lbl _) =>
                let mut l : Label := { content := lbl }
                for e in lkeys do
                  match keyPath e.toList with
                  | "description" => l := { l with description := true }
                  | "swap" | "'" => l := { l with swap := !l.swap }
                  | _ => l := { l with keys := l.keys.push e }
                a := { a with labels := a.labels.push l }
                j := skipSp raws (k + 1)
              | _ => break
        arrows := arrows.push a
        i := j
      else
        content := content.push (.ctrl n p)
        i := i + 1
    | some r =>
      content := content.push r
      i := i + 1
  return (trimRaws content, arrows)

private def splitRows (raws : Array Parse.Raw) (amp : Bool) : Array (Array (Array Parse.Raw)) := Id.run do
  let mut rows : Array (Array (Array Parse.Raw)) := #[]
  let mut row : Array (Array Parse.Raw) := #[]
  let mut cell : Array Parse.Raw := #[]
  for r in raws do
    let ends := match r with
      | .sym '&' _ => !amp
      | .ctrl "&" _ => amp
      | _ => false
    if r matches .ctrl "\\" _ then
      rows := rows.push (row.push cell)
      row := #[]
      cell := #[]
    else if ends then
      row := row.push cell
      cell := #[]
    else cell := cell.push r
  let last := row.push cell
  unless last.all (fun c => (trimRaws c).isEmpty) do rows := rows.push last
  return rows

/-- Every row as wide as the widest, short rows padded with empty cells: the
grid a matrix lays out. -/
public def padRows (rows : Array (Array (Array Parse.Raw))) : Array (Array (Array Parse.Raw)) :=
  let width := rows.foldl (fun w r => max w r.size) 0
  rows.map fun r => r ++ Array.replicate (width - r.size) #[]

public theorem cells_rectangular (rows : Array (Array (Array Parse.Raw))) :
    ∀ r ∈ padRows rows, r.size = rows.foldl (fun w r => max w r.size) 0 := by
  intro r hr
  simp only [padRows, Array.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have hle : r0.size ≤ rows.foldl (fun w r => max w r.size) 0 := by
    have key : ∀ (l : List (Array (Array Parse.Raw))) (w : Nat),
        (∀ x ∈ l, x.size ≤ l.foldl (fun w r => max w r.size) w) ∧
        w ≤ l.foldl (fun w r => max w r.size) w := by
      intro l
      induction l with
      | nil => intro w; simp
      | cons x xs ih =>
        intro w
        have h := ih (max w x.size)
        refine ⟨fun y hy => ?_, Nat.le_trans (Nat.le_max_left _ _) h.2⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Nat.le_trans (Nat.le_max_right _ _) h.2
        · exact h.1 y hy
    rw [← Array.foldl_toList]
    exact (key rows.toList 0).1 r0 (Array.mem_toList_iff.mpr hr0)
  simp only [Array.size_append, Array.size_replicate]
  omega

/-- Where a cell's border meets the ray from its centre toward `q`: the `asymmetrical rectangle`'s `\anchorborder`. -/
public def cellBorder (x y a up down qx qy : Int) : Int × Int :=
  rectBorder x y a (if qy > y then up else down) qx qy

public theorem arrow_border_exact (x y a up down qx qy : Int) (ha : 0 < a) (hu : 0 < up)
    (hd : 0 < down) :
    let b := if qy > y then up else down
    ((cellBorder x y a up down qx qy).1 = x - a ∨ (cellBorder x y a up down qx qy).1 = x + a ∨
      (cellBorder x y a up down qx qy).2 = y - b ∨ (cellBorder x y a up down qx qy).2 = y + b ∨
      (qx = x ∧ qy = y)) ∧
    x - a ≤ (cellBorder x y a up down qx qy).1 ∧ (cellBorder x y a up down qx qy).1 ≤ x + a ∧
    y - b ≤ (cellBorder x y a up down qx qy).2 ∧ (cellBorder x y a up down qx qy).2 ≤ y + b := by
  intro b
  have hb : 0 < b := by
    show 0 < (if qy > y then up else down)
    split <;> assumption
  simp only [cellBorder]
  exact rectBorder_exact x y a b qx qy ha hb

private def cmTo (end_ : Sp × Sp) (dx dy : Int) (lw : Sp) : Gfx.Subpath :=
  let a := 52 * lw / 10
  let b := 12 * lw
  -- The tip's origin stands half a line width behind the end (its tip end).
  let ox := end_.1 - dx * lw / 2000
  let oy := end_.2 - dy * lw / 2000
  let at_ (u v : Int) : Sp × Sp := (ox + (dx * u - dy * v) / 1000, oy + (dy * u + dx * v) / 1000)
  { start := at_ (-a) (b / 2)
    segs := #[.cubic (at_ (-a * 81731 / 100000) (b * 2 / 10)) (at_ (-a * 41019 / 100000)
        (b * 5833333 / 100000000)) (at_ 0 0),
      .cubic (at_ (-a * 41019 / 100000) (-b * 5833333 / 100000000))
        (at_ (-a * 81731 / 100000) (-b * 2 / 10)) (at_ (-a) (-b / 2))]
    closed := false }

private def unitOf (dx dy : Int) : Int × Int :=
  let n := isqrt (dx * dx + dy * dy)
  if n == 0 then (1000, 0) else (dx * 1000 / n, dy * 1000 / n)

private def cubicAtMilli (p0 c1 c2 p1 : Sp × Sp) (t : Int) : (Sp × Sp) × (Sp × Sp) :=
  let s := 1000 - t
  let pt (a b c d : Int) : Int :=
    (a * s * s * s + 3 * b * s * s * t + 3 * c * s * t * t + d * t * t * t) / 1000000000
  let dv (a b c d : Int) : Int :=
    (3 * (b - a) * s * s + 6 * (c - b) * s * t + 3 * (d - c) * t * t) / 1000000
  ((pt p0.1 c1.1 c2.1 p1.1, pt p0.2 c1.2 c2.2 p1.2),
   (dv p0.1 c1.1 c2.1 p1.1, dv p0.2 c1.2 c2.2 p1.2))

private def centreFor (p : Sp × Sp) (a b : Sp) : NodeAnchor → Sp × Sp
  | .center | .base | .baseEast | .baseWest => p
  | .north => (p.1, p.2 - b)
  | .south => (p.1, p.2 + b)
  | .east => (p.1 - a, p.2)
  | .west => (p.1 + a, p.2)
  | .northEast => (p.1 - a, p.2 - b)
  | .northWest => (p.1 + a, p.2 - b)
  | .southEast => (p.1 - a, p.2 + b)
  | .southWest => (p.1 + a, p.2 + b)

private def labelAt (x0 b : Sp) (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (m : Ir.Pic.LabelInk) : Ir.Pic.Shape :=
  let tall := m.height + m.depth
  .label x0 (b + m.height - tall + tall / 2) content color scale .west

private def outside (what : String) : PDiag :=
  (.W0334, s!"{what} is outside the rendered diagram subset; it is dropped")

private def cellOptions (raws : Array Parse.Raw) : Option (Array Parse.Raw × Array Parse.Raw) :=
  let i := skipSp raws 0
  match raws[i]? with
  | some (.word "|" _) =>
    (readBracket raws (skipSp raws (i + 1))).bind fun (inner, next) =>
      match raws[next]? with
      | some (.word w p) =>
        if w == "|" then some (inner, raws.extract (next + 1) raws.size)
        else if w.startsWith "|" then
          some (inner, #[Parse.Raw.word (w.drop 1).toString p] ++ raws.extract (next + 1) raws.size)
        else none
      | _ => none
  | _ => none

private def sepValue (names : List (String × Int)) (em ex : Sp) (toks : List Tok) :
    Except String Sp :=
  match (keyName toks).bind (fun n => List.lookup n names) with
  | some m => .ok (m * em / 1000)
  | none => readNodeDim em ex toks

/-- A commutative diagram, natively (tikzlibrarycd.code.tex): math cells laid out as pgf's matrix
lays them, arrows between their borders. -/
public def elabCd (pal : Ir.Palette) (raws : Array Parse.Raw)
    (math : Bool → Array Parse.Raw → Ir.Inline × Array PDiag)
    (metric : Ir.Pic.LabelMetric) (bodySize : Sp) (ground : Ir.Color) (size : Nat := 1000) :
    Ir.Pic.Picture × Array PDiag := Id.run do
  let mut diags : Array PDiag := #[]
  let note (d : PDiag) (ds : Array PDiag) : Array PDiag :=
    if ds.any (·.2 == d.2) then ds else ds.push d
  let cx : Cx := { pal := pal, math := math, metric := metric, bodySize := bodySize }
  let probe := metric #[.text "x"] size
  let em : Sp := bodySize * (size : Int) / 1000
  let ex : Sp := probe.ex
  let mut i := skipSp raws 0
  let mut amp := false
  let mut rowSep : Sp := 1800 * em / 1000
  let mut colSep : Sp := 2400 * em / 1000
  if let some (inner, next) := readBracket raws i then
    i := next
    for e in keyEntries inner do
      let key := keyPath e.toList
      let value := (e.toList.dropWhile (· != .sym '=')).drop 1
      if key == "ampersand replacement" then amp := true
      else if key == "row sep" || key == "column sep" || key == "sep" then
        match (if key == "column sep" then sepValue colSepEm em ex value
               else sepValue rowSepEm em ex value),
              sepValue colSepEm em ex value with
        | .ok r, .ok c =>
          if key != "column sep" then rowSep := r
          if key != "row sep" then colSep := c
        | .error err, _ | _, .error err =>
          diags := note (.E0333, s!"in the diagram's '{key}', {err}; it is ignored") diags
      else diags := note (outside s!"diagram option {optName e.toList}") diags
  let grid := padRows (splitRows (raws.extract i raws.size) amp)
  let mut cells : Array (Array (Option (Ir.Inline × Ir.Pic.LabelInk))) := #[]
  let mut arrowsAt : Array (Nat × Nat × Arrow) := #[]
  for h : r in [0:grid.size] do
    let mut row : Array (Option (Ir.Inline × Ir.Pic.LabelInk)) := #[]
    for h2 : c in [0:grid[r].size] do
      let (content, arrows) := splitCell grid[r][c]
      -- A cell's own node options are named, never set as the cell's mathematics.
      let mut content := content
      if let some (opts, rest) := cellOptions content then
        diags := note (outside s!"the cell options '|[{Parse.rawSrc opts}]|'") diags
        content := rest
      for a in arrows do arrowsAt := arrowsAt.push (r, c, a)
      if content.isEmpty then row := row.push none
      else
        let (inl, ds) := math false content
        diags := ds.foldl (fun acc d => note d acc) diags
        row := row.push (some (inl, metric #[inl] size))
    cells := cells.push row
  let width := (cells[0]?.map (·.size)).getD 0
  let xsep : Sp := ex
  let ysep : Sp := 85 * ex / 100
  let axisOf (m : Ir.Pic.LabelInk) : Sp := m.axis
  let halfOf (m : Ir.Pic.LabelInk) : Sp := m.w / 2 + xsep
  let upOf (m : Ir.Pic.LabelInk) : Sp := m.boxHeight + ysep - axisOf m
  let downOf (m : Ir.Pic.LabelInk) : Sp := m.boxDepth + ysep + axisOf m
  let colHalf : Array Sp := (Array.range width).map fun c =>
    cells.foldl (fun w row => match row[c]? with
      | some (some (_, m)) => max w (halfOf m)
      | _ => w) 0
  let rowUp : Array Sp := cells.map fun row => row.foldl (fun w cell => match cell with
      | some (_, m) => max w (upOf m)
      | none => w) 0
  let rowDown : Array Sp := cells.map fun row => row.foldl (fun w cell => match cell with
      | some (_, m) => max w (downOf m)
      | none => w) 0
  let mut xs : Array Sp := #[]
  let mut x : Sp := 0
  for c in [0:width] do
    if c > 0 then x := x + colHalf.getD (c - 1) 0 + colSep + colHalf.getD c 0
    xs := xs.push x
  let mut ys : Array Sp := #[]
  let mut y : Sp := 0
  for r in [0:cells.size] do
    if r > 0 then y := y - rowDown.getD (r - 1) 0 - rowSep - rowUp.getD r 0
    ys := ys.push y
  let mut shapes : Array Ir.Pic.Shape := #[]
  let mut borders : Array Ir.Pic.Box := #[]
  for r in [0:cells.size] do
    for c in [0:width] do
      if let some (some (inl, m)) := cells[r]?.bind (·[c]?) then
        let cx0 := xs.getD c 0
        let base := ys.getD r 0 - axisOf m
        shapes := shapes.push (labelAt (cx0 - m.w / 2) base #[inl] cx.ink size m)
        borders := borders.push ((cx0 - halfOf m, base - m.boxDepth - ysep),
          (cx0 + halfOf m, base + m.boxHeight + ysep))
  let geomOf (r c : Nat) : Option (Sp × Sp × Sp × Sp × Sp) :=
    match cells[r]?.bind (·[c]?) with
    | some (some (_, m)) => some (xs.getD c 0, ys.getD r 0, halfOf m, upOf m, downOf m)
    | _ => none
  for (r, c, a) in arrowsAt do
    let tr : Int := r + a.dr
    let tc : Int := c + a.dc
    let target := if tr < 0 || tc < 0 then none else geomOf tr.toNat tc.toNat
    match geomOf r c, target with
    | some (sx, sy, sa, su, sd), some (tx, ty, ta, tu, td) =>
      let mut color := cx.ink
      let mut lw : Sp := if probe.rule > 0 then probe.rule else Ir.Pic.thinWidth
      let mut dash : Array Sp := #[]
      let mut spec : ToSpec := {}
      let mut draws := true
      let mut swapAll := false
      let mut startAt : Option NodeAnchor := none
      let mut endAt : Option NodeAnchor := none
      for e in a.keys do
        let key := keyPath e.toList
        let value := (e.toList.dropWhile (· != .sym '=')).drop 1
        match spec.read [] e with
        | some (.ok s) => spec := s
        | some (.error err) => diags := note (.E0333, s!"in an arrow's '{key}', {err}") diags
        | none =>
        if key == "dashed" then dash := #[7 * lw, 4 * lw]
        else if key == "swap" || key == "'" then swapAll := !swapAll
        else if key == "phantom" then draws := false
        else if key == "start anchor" || key == "end anchor" then
          match nameOfToks value >>= nodeAnchorOf with
          | some an => if key == "start anchor" then startAt := some an else endAt := some an
          | none => diags := note (outside s!"arrow option {optName e.toList}") diags
        else if let some (.ok w) := readLineWidth e.toList then lw := w
        else
          match evalColor cx [] e with
          | .ok col => color := col
          | .error _ => diags := note (outside s!"arrow option {optName e.toList}") diags
      let anchorOf (x y a up down : Sp) : NodeAnchor → Sp × Sp
        | .center => (x, y)
        | .north => (x, y + up)
        | .south => (x, y - down)
        | .east => (x + a, y)
        | .west => (x - a, y)
        | .northEast => (x + a, y + up)
        | .northWest => (x - a, y + up)
        | .southEast => (x + a, y - down)
        | .southWest => (x - a, y - down)
        | .base | .baseEast | .baseWest => (x, y)
      let toward (x y a up down : Sp) (q : Sp × Sp) : Sp × Sp :=
        cellBorder x y a up down q.1 q.2
      let (p1, p2) :=
        if spec.curved then
          (match startAt with
            | some an => anchorOf sx sy sa su sd an
            | none => toward sx sy sa su sd (turnAbout (sx, sy) (tx, ty) spec.outA),
           match endAt with
            | some an => anchorOf tx ty ta tu td an
            | none => toward tx ty ta tu td (turnAbout (tx, ty) (sx, sy) (180 + spec.inA)))
        else
          (match startAt with
            | some an => anchorOf sx sy sa su sd an
            | none => toward sx sy sa su sd (tx, ty),
           match endAt with
            | some an => anchorOf tx ty ta tu td an
            | none => toward tx ty ta tu td (sx, sy))
      let (c1, c2) : (Sp × Sp) × (Sp × Sp) :=
        if spec.curved then
          let vx := p2.1 - p1.1
          let vy := p2.2 - p1.2
          (turnedControl p1.1 p1.2 vx vy spec.outA spec.outL,
           turnedControl p2.1 p2.2 vx vy spec.inA spec.inL)
        else (p1, p2)
      -- The tip follows the arrival tangent; the shaft stops one line width short.
      let (dx, dy) := if spec.curved then unitOf (p2.1 - c2.1) (p2.2 - c2.2)
        else unitOf (p2.1 - p1.1) (p2.2 - p1.2)
      let shaftEnd : Sp × Sp := (p2.1 - dx * lw / 1000, p2.2 - dy * lw / 1000)
      let stroke : Gfx.Stroke :=
        { Ir.Pic.strokeOf { color, width := lw } with dash, cap := .butt }
      if draws then
        let shaft : Gfx.Subpath :=
          if spec.curved then
            { start := p1, segs := #[.cubic c1 c2 shaftEnd], closed := false }
          else { start := p1, segs := #[.line shaftEnd], closed := false }
        let tipStroke : Gfx.Stroke := { stroke with dash := #[], cap := .round, join := .round }
        shapes := shapes.push (.ink (.group Gfx.Affine.unit #[] Gfx.Alpha.opaque
          #[.draw (.path #[shaft]) none (some stroke),
            .draw (.path #[cmTo p2 dx dy lw]) none (some tipStroke)]))
      for l in a.labels do
        let (pos, tan) :=
          if spec.curved then cubicAtMilli p1 c1 c2 p2 500
          else (((p1.1 + p2.1) / 2, (p1.2 + p2.2) / 2), (p2.1 - p1.1, p2.2 - p1.2))
        let (ux, uy) := unitOf tan.1 tan.2
        let mut lcolor := color
        for e in l.keys do
          match evalColor cx [] e with
          | .ok col => lcolor := col
          | .error _ => diags := note (outside s!"label option {optName e.toList}") diags
        let script : Nat := if probe.script > 0 then probe.script else 700
        let scale : Nat := if draws then script * size / 1000 else size
        let (inl, ds) := math false l.content
        diags := ds.foldl (fun acc d => note d acc) diags
        let m := metric #[inl] scale
        let sep := ex / 2
        let ha := m.w / 2 + sep
        let hb := (m.boxHeight + m.boxDepth) / 2 + sep
        let an : NodeAnchor :=
          if l.description || !draws then .center else labelAutoAnchor ux uy (l.swap != swapAll)
        let ctr := centreFor pos ha hb an
        let base := ctr.2 - (m.boxHeight - m.boxDepth) / 2
        if l.description then
          shapes := shapes.push (.rect (ctr.1 - ha) (ctr.2 - hb) (2 * ha) (2 * hb) ground)
        shapes := shapes.push (labelAt (ctr.1 - m.w / 2) base #[inl] lcolor scale m)
        borders := borders.push ((ctr.1 - ha, ctr.2 - hb), (ctr.1 + ha, ctr.2 + hb))
    | _, _ =>
      diags := note (.E0333, s!"an arrow from row {r + 1}, column {c + 1} reaches no cell; \
it is not drawn") diags
  -- tikz-cd's `every diagram` runs the baseline through the matrix's centre, `1-row diagram` on its row's base.
  let baseline : Option Sp :=
    if ys.isEmpty then none
    else if cells.size == 1 then
      let axis := ((cells.getD 0 #[]).findSome? fun cell => cell.map (·.2.axis)).getD probe.axis
      some (ys.getD 0 0 - axis)
    else
      some ((ys.getD 0 0 + rowUp.getD 0 0 + ys.getD (ys.size - 1) 0 -
        rowDown.getD (ys.size - 1) 0) / 2)
  return ({ shapes, borders, baseline }, diags)

end Cd

end LeanTex.Core.Picture
