module

public import LeanTex.Core.Parse
public import LeanTex.Core.Ir

/-! The reader of beamer's block templates: runs the `block begin`/`block end` pair as TeX runs it,
in TeX's box-and-rule vocabulary, and lowers the lists it builds onto `Ir.BlockShape`. -/

namespace LeanTex.Core.BlockTemplate

open LeanTex.Core
open LeanTex.Core.Dim
open LeanTex.Core.Parse (Raw)

/-- One token of a template's flat list, `body` standing for the block's body. -/
public inductive Tok where
  | ctrl (n : String)
  | word (s : String)
  | sym (c : Char)
  | space
  | par
  | bg
  | eg
  | body
  deriving Repr, BEq, Inhabited

/-- Does TeX read a line end after this raw as a space (TeXbook ch. 8)? -/
private def endsMidLine : Raw → Bool
  | .ctrl n _ => !(n.all fun c => c.isAlpha || c == '@')
  | .space | .par _ => false
  | .word .. | .sym .. | .group .. | .math .. | .env .. | .verb .. => true

/-- A text's raws with the spaces TeX reads at its braces' line ends, which the lexer omits. -/
public def edged (edges : Bool × Bool) (raws : Array Raw) : Array Raw :=
  let raws := if edges.1 then raws.foldl (·.push ·) #[Raw.space] else raws
  if edges.2 && raws.back?.all endsMidLine then raws.push .space else raws

mutual

-- conserves: none — a token reading of template code
private def flatList (acc : Array Tok) : List Raw → Array Tok
  | [] => acc
  | r :: rest => flatList (flatOne acc r) rest

private def flatOne (acc : Array Tok) : Raw → Array Tok
  | .word s _ => acc.push (.word s)
  | .space => acc.push .space
  | .par _ => acc.push .par
  | .ctrl n _ =>
    if n == "bgroup" then acc.push .bg
    else if n == "egroup" then acc.push .eg
    else acc.push (.ctrl n)
  | .sym c _ => acc.push (.sym c)
  | .group body p =>
    let acc := flatList (if p.openEol then (acc.push .bg).push .space else acc.push .bg) body.toList
    let acc := if p.closeEol && body.back?.all endsMidLine then acc.push .space else acc
    acc.push .eg
  | .math _ _ _ => acc.push (.ctrl "$…$")
  | .env n _ _ => acc.push (.ctrl ("begin{" ++ n ++ "}"))
  | .verb _ _ _ => acc.push (.ctrl "verb")

end

/-- The template code as one flat list. -/
public def flatten (raws : Array Raw) : Array Tok := flatList #[] raws.toList

/-- A document macro a template may call: its definition order, arity and replacement text. -/
public structure Macro where
  serial : Nat
  arity : Nat
  body : Array Raw
  /-- The default of an optional first argument, `\newcommand`'s `[…]`. -/
  optional : Option (Array Raw) := none
  deriving Inhabited

/-- The arguments of a call from the head of `l` and the tokens they take; with `optional`, a
leading `[…]` or the default. -/
private def callArgs (l : List Tok) (arity : Nat) (optional : Option (Array Tok) := none) :
    Option (Array (Array Tok) × Nat) := Id.run do
  let toks := l.toArray
  let mut args : Array (Array Tok) := #[]
  let mut k := 0
  let mut braced := arity
  if let some dflt := optional then
    if arity == 0 then return none
    braced := arity - 1
    let mut j := k
    for _ in [k:toks.size] do
      if toks[j]? == some .space then j := j + 1 else break
    if toks[j]? == some (.sym '[') then
      let mut depth := 0
      let mut arg : Array Tok := #[]
      let mut m := j + 1
      let mut closed := false
      for _ in [j + 1:toks.size] do
        match toks[m]? with
        | some .bg => depth := depth + 1; arg := arg.push .bg
        | some .eg =>
          if depth == 0 then return none
          depth := depth - 1
          arg := arg.push .eg
        | some (.sym ']') =>
          if depth == 0 then closed := true; break
          arg := arg.push (.sym ']')
        | some t => arg := arg.push t
        | none => break
        m := m + 1
      unless closed do return none
      args := args.push arg
      k := m + 1
    else
      args := args.push dflt
      k := j
  for _ in [0:braced] do
    let mut j := k
    for _ in [k:toks.size] do
      if toks[j]? == some .space then j := j + 1 else break
    unless toks[j]? == some .bg do return none
    let mut depth := 0
    let mut arg : Array Tok := #[]
    let mut m := j + 1
    let mut closed := false
    for _ in [j + 1:toks.size] do
      match toks[m]? with
      | some .bg => depth := depth + 1; arg := arg.push .bg
      | some .eg =>
        if depth == 0 then closed := true; break
        depth := depth - 1
        arg := arg.push .eg
      | some t => arg := arg.push t
      | none => break
      m := m + 1
    unless closed do return none
    args := args.push arg
    k := m + 1
  return some (args, k)

/-- A replacement text's `#k`, each its argument's tokens. -/
private def substParams (args : Array (Array Tok)) : List Tok → Array Tok → Array Tok
  | [], acc => acc
  | .sym '#' :: .word w :: rest, acc =>
    match w.toList with
    | c :: cs =>
      if c >= '1' && c <= '9' then
        match args[c.toNat - '1'.toNat]? with
        | some arg =>
          let acc := acc ++ arg
          substParams args rest (if cs.isEmpty then acc else acc.push (.word (String.ofList cs)))
        | none => substParams args rest ((acc.push (.sym '#')).push (.word w))
      else substParams args rest ((acc.push (.sym '#')).push (.word w))
    | [] => substParams args rest ((acc.push (.sym '#')).push (.word w))
  | t :: rest, acc => substParams args rest (acc.push t)

/-- The document's macros expanded where the template calls them; a text expands only macros
defined before it, so expansion ends. -/
public def expandList (defs : String → Option Macro) (bound : Nat) :
    List Tok → Array Tok → Array Tok
  | [], acc => acc
  | .ctrl n :: rest, acc =>
    match defs n with
    | some m =>
      if _h : m.serial < bound then
        match callArgs rest m.arity (m.optional.map flatten) with
        | some (args, k) =>
          let body := substParams args (flatten m.body).toList #[]
          let expanded := expandList defs m.serial body.toList #[]
          expandList defs bound (rest.drop k) (acc ++ expanded)
        | none => expandList defs bound rest (acc.push (.ctrl n))
      else expandList defs bound rest (acc.push (.ctrl n))
    | none => expandList defs bound rest (acc.push (.ctrl n))
  | t :: rest, acc => expandList defs bound rest (acc.push t)
termination_by l _ => (bound, l.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

/-- Which extent of a box a dimension reads. -/
public inductive Ext where
  | ht
  | dp
  | wd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A dimension as a template writes it: a linear form over a length, the measure, box extents,
`\parskip`, the leading and the cap height; `font` is the font its terms were read in. -/
public structure Dimen where
  len : SymLength := {}
  line : Int := 0
  ext : List (Nat × Ext × Int) := []
  parskip : Int := 0
  lead : Int := 0
  cap : Int := 0
  font : Option (Option String) := none
  deriving Repr, BEq, Inhabited

/-- Does the dimension read a font: an em, an ex, the leading or the cap
height. -/
public def Dimen.fonted (d : Dimen) : Bool :=
  d.len.em != 0 || d.len.ex != 0 || d.lead != 0 || d.cap != 0

/-- The font forgotten where nothing reads one. -/
private def Dimen.norm (d : Dimen) : Dimen := if d.fonted then d else { d with font := none }

/-- Extents merged by box and extent, zero coefficients dropped. -/
private def mergeExt (xs : List (Nat × Ext × Int)) : List (Nat × Ext × Int) :=
  let keys := (xs.map fun (b, e, _) => (b, e)).eraseDups
  (keys.filterMap fun (b, e) =>
    let c := (xs.filter fun (b', e', _) => b' == b && e' == e).foldl (fun s (_, _, k) => s + k) 0
    if c == 0 then none else some (b, e, c))

/-- Two dimensions added; `none` where both read a font and not the same one. -/
public def Dimen.add? (a b : Dimen) : Option Dimen :=
  if a.fonted && b.fonted && a.font != b.font then none
  else some (Dimen.norm
    { len := a.len.add b.len, line := a.line + b.line, ext := mergeExt (a.ext ++ b.ext)
      parskip := a.parskip + b.parskip, lead := a.lead + b.lead, cap := a.cap + b.cap
      font := if a.fonted then a.font else b.font })

public def Dimen.neg (a : Dimen) : Dimen :=
  { len := { sp := -a.len.sp, em := -a.len.em, ex := -a.len.ex }, line := -a.line
    ext := a.ext.map fun (b, e, k) => (b, e, -k), parskip := -a.parskip, lead := -a.lead
    cap := -a.cap, font := a.font }

/-- e-TeX's quotient (`\dimexpr`'s `/`): rounded to the nearest, a half away
from zero (e-TeX manual §3.5). -/
private def roundDiv (x : Int) (n : Nat) : Int :=
  if n == 0 then 0 else
  let q : Int := ((2 * x.natAbs + n) / (2 * n) : Nat)
  if x < 0 then -q else q

/-- The dimension times `num / den`, each term rounded as e-TeX rounds its quotient. -/
private def Dimen.scale? (d : Dimen) (num : Int) (den : Nat) : Option Dimen :=
  if den == 0 || d.ext.any (fun (_, _, k) => (k * num) % (den : Int) != 0) then none
  else
    let f (v : Int) : Int := roundDiv (v * num) den
    some (Dimen.norm
      { len := { sp := .ofUnits (f d.len.sp.units), em := f d.len.em, ex := f d.len.ex }
        line := f d.line
        ext := mergeExt (d.ext.map fun (b, e, k) => (b, e, k * num / (den : Int)))
        parskip := f d.parskip, lead := f d.lead, cap := f d.cap, font := d.font })

/-- The length alone, when the dimension is one. -/
public def Dimen.length? (d : Dimen) : Option SymLength :=
  if d.line == 0 && d.ext.isEmpty && d.parskip == 0 && d.lead == 0 && d.cap == 0
  then some d.len else none

/-- What a colour command selects: a channel of the latest beamer colour element setting it, or
a colour by name. -/
public inductive Paint where
  | beamer (chain : List String) (channel : String)
  | named (name : String)
  deriving Repr, BEq, Inhabited

/-- An item a body's list may end on past its last line: TeX's glue, kern
and penalty nodes (`\lastnodetype` 11, 12 and 13). -/
public inductive TailKind where
  | glue
  | kern
  | penalty
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One node of a list a template builds; lines, boxes and the body carry identities their
extents are read by. -/
public inductive Node where
  | vskip (s : Ir.BlockSkip)
  | whatsit
  | line (id : Nat) (parskip : Bool) (hsize : Dimen) (kids : Array Node)
  | box (id : Nat) (vertical : Bool) (hsize : Dimen) (kids : Array Node) (endDepth : Dimen)
  | sized (id : Nat) (vertical : Bool) (to : Dimen) (kids : Array Node)
  | lap (right : Bool) (kids : Array Node)
  | raised (lift : Dimen) (ht dp : Option Dimen) (kids : Array Node)
  | rule (w h d : Option Dimen) (paint : Option Paint) (font : Option String)
  | hskip (d : Dimen) (font : Option String) (kern : Bool)
  | space (font : Option String)
  | strut (font : Option String)
  | title (font : Option String) (paint : Option Paint)
  | body (id : Nat) (font : Option String) (paint : Option Paint)
  | hrule
  | penalty (n : Int)
  | tail (k : Nat) (kind : TailKind)
  | vss
  | prevdepth (d : Dimen)
  | unboxed (id : Nat) (kids : Array Node) (atDepth endDepth : Dimen)
  | moved (d : Dimen) (n : Node)
  deriving Repr, BEq, Inhabited

/-- The identity of the box before the block, whose depth the block's list opens on. -/
private def priorId : Nat := 0

/-- TeX's `\prevdepth` that suppresses the next interline glue, `-1000pt`
(`\nointerlineskip`, a fresh box's list, a rule). -/
private def ignoreDepth : Dimen := { len := { sp := -1000 * Dim.pt 1 } }

/-- What a `\last…` register holds: the body's trailing item, a skip or penalty the template
set, or TeX's zero. -/
private inductive Val where
  | tail (k : Nat) (kind : TailKind)
  | skip (s : Ir.BlockSkip)
  | penalty (n : Int)
  | none
  deriving BEq, Inhabited

/-- What a group restores: font, colour, `\hsize`, the beamer colour elements in force, and the
length registers it assigned. -/
private structure Scope where
  font : Option String := none
  paint : Option Paint := none
  hsize : Dimen := { line := 1000 }
  channels : List String := []
  dimens : List (String × Dimen) := []
  /-- Scratch registers holding the node a `\last…` read. -/
  vals : List (String × Val) := []
  /-- The `\newif` flags the template set (`\Xtrue`, `\Xfalse`). -/
  flags : List (String × Bool) := []
  deriving Inhabited

/-- A list under construction: vertical or horizontal, its nodes, and the
paragraph open in it. -/
private structure Lst where
  vertical : Bool := true
  nodes : Array Node := #[]
  para : Option (Array Node) := none
  paraParskip : Bool := false
  /-- An enclosing box holds this list: its paragraphs spend `\parskip` only after a node. -/
  inner : Bool := false
  /-- TeX's `\prevdepth` in a vertical list. -/
  prev : Dimen := ignoreDepth
  deriving Inhabited

private inductive FrameKind where
  | group (simple : Bool)
  | box (target : Option (String × Bool)) (id : Nat) (vertical : Bool) (to : Option Dimen)
  | lap (right : Bool)
  | raise (lift : Dimen) (ht dp : Option Dimen)
  deriving Inhabited

private structure Frame where
  kind : FrameKind
  saved : Scope
  outer : Lst
  /-- The `\moveleft`/`\moveright` shift the box this frame builds takes. -/
  move : Option Dimen := none
  /-- The box registers the group assigned locally, with what each held where it opened. -/
  boxes : List (String × Option (Option Node)) := []
  deriving Inhabited

/-- A conditional the reader decided, waiting for its `\else` or `\fi`. -/
private inductive Pending where
  | thenArm
  | elseArm
  deriving BEq, Inhabited

/-- A template token list as TeX's scanner reads it, a character at a time. -/
private inductive STok where
  | ch (c : Char)
  | cs (n : String)
  | sp
  | stop
  deriving BEq, Inhabited

private structure Chars where
  chars : Array STok := #[]
  owner : Array (Nat × Bool) := #[]
  start : Array Nat := #[]
  deriving Inhabited

private def Chars.of (toks : Array Tok) : Chars := Id.run do
  let mut c : Chars := {}
  for i in [0:toks.size] do
    c := { c with start := c.start.push c.chars.size }
    let pieces : List STok := match toks[i]? with
      | some (.word w) => w.toList.map STok.ch
      | some (.sym ch) => [.ch ch]
      | some (.ctrl n) => [.cs n]
      | some .space => [.sp]
      | _ => [.stop]
    let mut first := true
    for p in pieces do
      c := { c with chars := c.chars.push p, owner := c.owner.push (i, first) }
      first := false
  return c

private structure St where
  scope : Scope := {}
  lst : Lst := {}
  frames : List Frame := []
  regs : List (String × Option Node) := []
  nextId : Nat := priorId + 1
  conds : List Pending := []
  unread : Array String := #[]
  /-- Length registers assigned with `\global`, by name. -/
  dimens : List (String × Dimen) := []
  /-- Registers `\newdimen` declares in the template itself. -/
  declared : List String := []
  /-- The document's length registers: `none` for no register, `some none` for an unknown value. -/
  lengths : String → Option (Option Dimen) := fun _ => none
  /-- The document's `\newif` flags, as they stand where the body begins. -/
  flags : String → Option Bool := fun _ => none
  /-- The template's characters, as dimensions are read. -/
  chars : Chars := {}
  /-- A `\moveleft`/`\moveright` shift the next box takes. -/
  move : Option Dimen := none
  /-- The identities of boxes TeX packs from zero, whose extents never fall below it. -/
  packed : List Nat := []
  /-- A `\global` prefix the next `\setbox` takes. -/
  globalNext : Bool := false
  deriving Inhabited

private def St.miss (s : St) (what : String) : St :=
  if s.unread.contains what then s else { s with unread := s.unread.push what }

/-- A `\newif` flag's value: as the template set it, else as the document
did. -/
private def St.flag? (s : St) (x : String) : Option Bool :=
  (s.scope.flags.lookup x).orElse fun _ => s.flags x

/-- The flag `\ifX` tests and its value, for a flag the document declares. -/
private def St.flagTest (s : St) (n : String) : Option Bool :=
  if n.startsWith "if" && n.length > 2 then s.flag? (n.drop 2).toString else none

/-- The flag `\Xtrue` or `\Xfalse` sets, and to what. -/
private def St.flagSet (s : St) (n : String) : Option (String × Bool) :=
  let t := (n.dropEnd 4).toString
  let f := (n.dropEnd 5).toString
  if n.endsWith "true" && (s.flag? t).isSome then some (t, true)
  else if n.endsWith "false" && (s.flag? f).isSome then some (f, false)
  else none

private def skipSp (toks : Array Tok) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:toks.size] do
    if toks[j]? == some .space then j := j + 1 else break
  return j

/-- The tokens of a braced argument at `i`, and the index after it. -/
private def readArg (toks : Array Tok) (i : Nat) : Option (Array Tok × Nat) := Id.run do
  let j := skipSp toks i
  unless toks[j]? == some .bg do return none
  let mut depth := 0
  let mut out : Array Tok := #[]
  let mut k := j + 1
  for _ in [j + 1:toks.size] do
    match toks[k]? with
    | some .bg => depth := depth + 1; out := out.push .bg
    | some .eg =>
      if depth == 0 then return some (out, k + 1)
      depth := depth - 1
      out := out.push .eg
    | some t => out := out.push t
    | none => return none
    k := k + 1
  return none

/-- The words of a token run, joined as source. -/
private def wordsOf (toks : Array Tok) : String :=
  String.join (toks.toList.map fun
    | .word s => s
    | .space => " "
    | .sym c => String.singleton c
    | .ctrl n => "\\" ++ n
    | _ => "")

/-- An optional `[...]` at `i`: its words, and the index after it. -/
private def readOpt (toks : Array Tok) (i : Nat) : Option String × Nat := Id.run do
  let j := skipSp toks i
  unless toks[j]? == some (.sym '[') do return (none, i)
  let mut out : Array Tok := #[]
  let mut k := j + 1
  for _ in [j + 1:toks.size] do
    match toks[k]? with
    | some (.sym ']') => return (some (wordsOf out).trimAscii.toString, k + 1)
    | some t => out := out.push t
    | none => return (none, i)
    k := k + 1
  return (none, i)

/-- The measure a dimension register names: `\linewidth` and its kin, all
the box's `\hsize` where a block stands. -/
private def measureRegs : List String := ["linewidth", "textwidth", "hsize", "columnwidth"]

/-- A box register's current box, by name: `none` for a register holding
no box (never set, or emptied by `\box`). -/
private def St.boxOf (s : St) (reg : String) : Option Node :=
  (s.regs.lookup reg).join

/-- A box register assigned as `\setbox` assigns it: in the group, or at every level. -/
private def St.setBox (s : St) (reg : String) (v : Option Node) (global : Bool) : St :=
  let regs := (reg, v) :: s.regs.filter (·.1 != reg)
  if global then
    { s with regs := regs
             frames := s.frames.map fun fr => { fr with boxes := fr.boxes.filter (·.1 != reg) } }
  else match s.frames with
    | fr :: rest =>
      let fr := if fr.boxes.any (·.1 == reg) then fr
        else { fr with boxes := (reg, s.regs.lookup reg) :: fr.boxes }
      { s with regs := regs, frames := fr :: rest }
    | [] => { s with regs := regs }

/-- A box register emptied by its use (`\box`, `\unvbox`): not an
assignment, so no group's end restores what it held (tex.web §1079). -/
private def St.voidBox (s : St) (reg : String) : St :=
  { s with regs := (reg, none) :: s.regs.filter (·.1 != reg) }

/-- What a closing group restores: the box registers it assigned locally. -/
private def St.restoreBoxes (s : St) (fr : Frame) : St :=
  { s with regs := fr.boxes.foldl (fun regs (reg, prev) =>
      let regs := regs.filter (·.1 != reg)
      match prev with
      | some v => (reg, v) :: regs
      | none => regs) s.regs }

private def Node.id? : Node → Option Nat
  | .box id .. => some id
  | _ => none

/-- A length register's value where the template stands: `none` for no register, `some none`
for an unknown value. -/
private def St.dimen? (s : St) (n : String) : Option (Option Dimen) :=
  match s.scope.dimens.lookup n with
  | some d => some (some d)
  | none =>
    match s.dimens.lookup n with
    | some d => some (some d)
    | none => if s.declared.contains n then some (some {}) else s.lengths n

/-- Assign a length register, as TeX does: in the group, or at every level. -/
private def St.assign (s : St) (n : String) (v : Dimen) (global : Bool) : St :=
  if global then
    let drop (sc : Scope) : Scope := { sc with dimens := sc.dimens.filter (·.1 != n) }
    { s with dimens := (n, v) :: s.dimens.filter (·.1 != n), scope := drop s.scope
             frames := s.frames.map fun fr => { fr with saved := drop fr.saved } }
  else { s with scope := { s.scope with dimens := (n, v) :: s.scope.dimens.filter (·.1 != n) } }

private def Chars.get (c : Chars) (k : Nat) : STok := c.chars[k]?.getD .stop

/-- The first character of token `i`. -/
private def Chars.first (c : Chars) (i : Nat) : Nat := c.start[i]?.getD c.chars.size

/-- The token a read ending before character `k` stops at: `none` inside a
word. -/
private def Chars.tokAt (c : Chars) (k : Nat) : Option Nat :=
  if k ≥ c.chars.size then some c.start.size
  else match c.owner[k]? with
    | some (i, true) => some i
    | _ => none

private def Chars.skipSp (c : Chars) (k : Nat) : Nat := Id.run do
  let mut j := k
  for _ in [k:c.chars.size] do
    if c.get j == .sp then j := j + 1 else break
  return j

/-- The one optional space TeX takes after a number or a unit. -/
private def Chars.optSp (c : Chars) (k : Nat) : Nat := if c.get k == .sp then k + 1 else k

/-- A keyword past spaces, either case, as TeX's keyword scan reads one (tex.web §407):
the index after it. -/
private def Chars.keyword (c : Chars) (k : Nat) (w : String) : Option Nat := Id.run do
  let mut j := c.skipSp k
  for x in w.toList do
    match c.get j with
    | .ch y => if y.toLower == x then j := j + 1 else return none
    | _ => return none
  return some j

/-- Optional signs and spaces: the sign they make, and the index after. -/
private def Chars.signs (c : Chars) (k : Nat) : Int × Nat := Id.run do
  let mut neg := false
  let mut j := k
  for _ in [k:c.chars.size] do
    match c.get j with
    | .sp | .ch '+' => j := j + 1
    | .ch '-' => neg := !neg; j := j + 1
    | _ => break
  return (if neg then -1 else 1, j)

/-- A decimal constant: digits around one `.` or `,` (none where `whole`),
as a mantissa over a power of ten, and the index after it. -/
private def Chars.decimal (c : Chars) (k : Nat) (whole : Bool := false) :
    Option ((Int × Nat) × Nat) := Id.run do
  let mut m : Int := 0
  let mut scale : Nat := 1
  let mut dot := false
  let mut digits := 0
  let mut j := k
  for _ in [k:c.chars.size] do
    match c.get j with
    | .ch d =>
      if d.isDigit then
        m := m * 10 + ((d.toNat - '0'.toNat : Nat) : Int)
        if dot then scale := scale * 10
        digits := digits + 1
        j := j + 1
      else if (d == '.' || d == ',') && !dot && !whole then
        dot := true
        j := j + 1
      else break
    | _ => break
  if digits == 0 then return none
  return some ((m, scale), j)

/-- A mantissa over a power of ten as decimal source: 25 over 10 is `2.5`. -/
private def decimalSrc (m : Int) (scale : Nat) : String :=
  let digits := (toString scale).length - 1
  let s := toString m.natAbs
  let s := "".pushn '0' (digits + 1 - min s.length (digits + 1)) ++ s
  if digits == 0 then s
  else ((s.dropEnd digits).toString ++ "." ++ (s.takeEnd digits).toString)

/-- The units TeX names by keyword. -/
private def unitWords : List String :=
  ["em", "ex", "pt", "pc", "in", "bp", "cm", "mm", "dd", "cc", "sp"]

/-- An internal dimension at `k`, read as TeX reads it, and the index after it. -/
private def St.internalAt (s : St) (c : Chars) (k : Nat) : Option (Dimen × Nat) :=
  let font := s.scope.font
  match c.get k with
  | .cs n =>
    if measureRegs.contains n then some ({ line := 1000 }, k + 1)
    else if n == "z@" then some ({}, k + 1)
    else if n == "p@" then some ({ len := { sp := Dim.pt 1 } }, k + 1)
    else if n == "parskip" then some ({ parskip := 1000 }, k + 1)
    -- `\prevdepth` reads only in a vertical list, as TeX's does.
    else if n == "prevdepth" then
      if s.lst.vertical && s.lst.para.isNone then some (s.lst.prev, k + 1) else none
    else if n == "baselineskip" then some ({ lead := 1000, font := some font }, k + 1)
    else if n == "fontcharht" then
      let j := c.skipSp (k + 1)
      if c.get j != .cs "font" then none else
      let j := c.skipSp (j + 1)
      match c.get j, c.get (j + 1) with
      | .ch '`', .ch 'H' => some ({ cap := 1000, font := some font }, c.optSp (j + 2))
      | _, _ => none
    else if n == "ht" || n == "dp" || n == "wd" then
      let e : Ext := if n == "ht" then .ht else if n == "dp" then .dp else .wd
      let j := c.skipSp (k + 1)
      match c.get j with
      | .cs r =>
        -- A register with no box reads zero (TeX: a void box is 0pt).
        match (s.boxOf r).bind Node.id? with
        | some id => some ({ ext := [(id, e, 1)] }, j + 1)
        | none => some ({}, j + 1)
      | _ => none
    else match s.dimen? n with
      | some (some d) => some (d, k + 1)
      | _ => none
  | _ => none

/-- An unsigned dimension at `k`: an internal one, or a factor and its unit,
a keyword or an internal dimension. -/
private def St.unsignedAt (s : St) (c : Chars) (k : Nat) : Option (Dimen × Nat) := Id.run do
  let font := s.scope.font
  if let .cs _ := c.get k then return s.internalAt c k
  let some ((m, scale), j) := c.decimal k | return none
  let j := c.skipSp j
  if let some (d, j') := s.internalAt c j then return (d.scale? m scale).map (·, j')
  -- `true` scales a physical unit by the magnification, never a font's.
  let (true?, j) := match c.keyword j "true" with
    | some j' => (true, j')
    | none => (false, j)
  for u in unitWords do
    if let some j' := c.keyword j u then
      let fonted := u == "em" || u == "ex"
      if true? && fonted then return none
      match Decl.parseLength (decimalSrc m scale ++ u) with
      | some l => return some ({ len := l, font := if fonted then some font else none }, c.optSp j')
      | none => return none
  return none

/-- One level of `\dimexpr`'s evaluation. -/
private structure ExprLevel where
  sum : Dimen := {}
  sign : Int := 1
  term : Option Dimen := none
  paren : Bool
  outer : Int := 1

/-- The level's value: its sum and its last term. -/
private def ExprLevel.value? (l : ExprLevel) : Option Dimen :=
  l.term.bind fun t => (l.sum.add? (if l.sign < 0 then t.neg else t)).map fun v =>
    if l.outer < 0 then v.neg else v

/-- `\dimexpr`'s expression from `k` (e-TeX manual §3.5), ending at `\relax` or before
anything that continues no expression. -/
private def St.exprAt (s : St) (c : Chars) (k : Nat) : Option (Dimen × Nat) := Id.run do
  let mut stack : List ExprLevel := [{ paren := false }]
  let mut j := k
  let mut expect := true
  for _ in [0:2 * c.chars.size + 2] do
    let some top := stack.head? | return none
    j := c.skipSp j
    if expect then
      let (sign, j1) := c.signs j
      match c.get j1 with
      -- A sign never belongs to a parenthesis: e-TeX stops on it as a missing number.
      | .ch '(' =>
        if j1 != j then return none
        stack := { paren := true, outer := sign } :: stack; j := j1 + 1
      | .cs "dimexpr" => stack := { paren := false, outer := sign } :: stack; j := j1 + 1
      | _ =>
        let some (f, j2) := s.unsignedAt c j1 | return none
        stack := { top with term := some (if sign < 0 then f.neg else f) } :: stack.tail
        j := j2
        expect := false
    else
      let some t := top.term | return none
      match c.get j with
      | .ch '*' =>
        let (sg, j1) := c.signs (j + 1)
        let some ((n, _), j2) := c.decimal j1 (whole := true) | return none
        let some t' := t.scale? (sg * n) 1 | return none
        stack := { top with term := some t' } :: stack.tail
        j := c.optSp j2
      | .ch '/' =>
        let (sg, j1) := c.signs (j + 1)
        let some ((n, _), j2) := c.decimal j1 (whole := true) | return none
        let some t' := t.scale? sg n.toNat | return none
        stack := { top with term := some t' } :: stack.tail
        j := c.optSp j2
      | .ch '+' | .ch '-' =>
        let some sum := top.sum.add? (if top.sign < 0 then t.neg else t) | return none
        stack := { top with sum := sum, sign := if c.get j == .ch '-' then -1 else 1
                            term := none } :: stack.tail
        j := j + 1
        expect := true
      | .ch ')' =>
        unless top.paren do return none
        let some v := top.value? | return none
        match stack.tail with
        | below :: rest => stack := { below with term := some v } :: rest; j := j + 1
        | [] => return none
      | .cs "relax" =>
        if top.paren then return none
        let some v := top.value? | return none
        match stack.tail with
        | [] => return some (v, j + 1)
        | below :: rest => stack := { below with term := some v } :: rest; j := j + 1
      | _ =>
        if stack.length != 1 then return none
        return top.value?.map (·, j)
  return none

/-- A dimension at `k`: optional signs, then `\dimexpr`'s expression or an
unsigned dimension. -/
private def St.dimenAt (s : St) (c : Chars) (k : Nat) : Option (Dimen × Nat) :=
  let (sign, j) := c.signs k
  let signed (d : Dimen) : Dimen := if sign < 0 then d.neg else d
  if c.get j == .cs "dimexpr" then (s.exprAt c (j + 1)).map fun (d, j') => (signed d, j')
  else (s.unsignedAt c j).map fun (d, j') => (signed d, j')

/-- A dimension at token `i` of the list `c` reads, after an optional `=`:
`none` where it is not one this reading holds, or where it ends inside a
word. -/
private def St.readDimen (s : St) (c : Chars) (i : Nat) : Option (Dimen × Nat) :=
  let k := c.skipSp (c.first i)
  let k := if c.get k == .ch '=' then k + 1 else k
  (s.dimenAt c k).bind fun (d, k') => (c.tokAt k').map (d, ·)

/-- The skip registers a template may read, as `Ir.skipAmount` names them. -/
private def skipRegs : List String := ["smallskipamount", "medskipamount", "bigskipamount"]

/-- A glue at token `i`: a skip register, or `<dimen> [plus <dimen>] [minus
<dimen>]` with plain lengths. -/
private def St.readGlue (s : St) (c : Chars) (i : Nat) : Option (Ir.BlockSkip × Nat) := Id.run do
  let k := c.skipSp (c.first i)
  match c.get k with
  | .cs n =>
    if skipRegs.contains n then return (c.tokAt (k + 1)).map (.register n, ·)
    if n == "z@skip" then return (c.tokAt (k + 1)).map (.glue {}, ·)
  | _ => pure ()
  let some (w, k) := s.dimenAt c k | return none
  let some wl := w.length? | return none
  let mut g : SymGlue := { width := wl }
  let mut k := k
  for _ in [0:2] do
    if let some k1 := c.keyword k "plus" then
      let some (d, k2) := s.dimenAt c k1 | return none
      let some l := d.length? | return none
      g := { g with stretch := l }
      k := k2
    else if let some k1 := c.keyword k "minus" then
      let some (d, k2) := s.dimenAt c k1 | return none
      let some l := d.length? | return none
      g := { g with shrink := l }
      k := k2
    else break
  return (c.tokAt k).map (.glue g, ·)

/-- A rule's `width`, `height` and `depth` keywords from token `i`, in any
order. -/
private def St.readRuleSpec (s : St) (c : Chars) (i : Nat) :
    Option ((Option Dimen × Option Dimen × Option Dimen) × Nat) := Id.run do
  let mut w : Option Dimen := none
  let mut h : Option Dimen := none
  let mut d : Option Dimen := none
  let mut k := c.first i
  for _ in [0:6] do
    if let some k1 := c.keyword k "width" then
      let some (v, k2) := s.dimenAt c k1 | return none
      w := some v; k := k2
    else if let some k1 := c.keyword k "height" then
      let some (v, k2) := s.dimenAt c k1 | return none
      h := some v; k := k2
    else if let some k1 := c.keyword k "depth" then
      let some (v, k2) := s.dimenAt c k1 | return none
      d := some v; k := k2
    else break
  return (c.tokAt k).map ((w, h, d), ·)

mutual

-- conserves: none — a template list's last node; no document content
private def lastIn (acc : Option Node) : List Node → Option Node
  | [] => acc
  | n :: rest => lastIn ((lastOf n).orElse fun _ => acc) rest

private def lastOf : Node → Option Node
  | .prevdepth _ => none
  | .unboxed _ kids _ _ => lastIn none kids.toList
  | n => some n

end

mutual

-- conserves: none — a template list less its last node; no document content
private def dropLastIn : List Node → Option (List Node)
  | [] => none
  | n :: rest =>
    match dropLastIn rest with
    | some rest' => some (n :: rest')
    | none => (dropLastOf n).map (· ++ rest)

private def dropLastOf : Node → Option (List Node)
  | .prevdepth _ => none
  | .unboxed id kids atD e => (dropLastIn kids.toList).map fun ks => [.unboxed id ks.toArray atD e]
  | _ => some []

end

/-- TeX's node type of a node standing last (`\lastnodetype`): 1 a line or an
`\hbox`, 2 a `\vbox`, 3 a rule, 9 a colour change, 11 glue, 12 a kern, 13 a
penalty. -/
private def Node.typeOf : Node → Int
  | .title .. => 0
  | .line .. | .body .. | .lap .. | .raised .. => 1
  | .box _ v .. | .sized _ v .. => if v then 2 else 1
  | .moved _ n => n.typeOf
  | .rule .. | .strut .. | .hrule => 3
  | .whatsit => 9
  | .hskip _ _ true => 12
  | .vskip .. | .hskip _ _ false | .space .. | .vss | .tail _ .glue => 11
  | .tail _ .kern => 12
  | .penalty .. | .tail _ .penalty => 13
  | .prevdepth .. | .unboxed .. => -1

/-- The current list's nodes: the open paragraph's, else the list's own. -/
private def St.current (s : St) : Array Node := s.lst.para.getD s.lst.nodes

/-- The current list's last node. -/
private def St.lastNode (s : St) : Option Node := lastIn none s.current.toList

/-- The current list less its last node, where that node is `pick`'s, as
`\unskip`, `\unkern` and `\unpenalty` take theirs. -/
private def St.dropLast (s : St) (pick : Node → Bool) : St :=
  match s.lastNode with
  | some n =>
    if !pick n then s else
    match dropLastIn s.current.toList with
    | some rest =>
      match s.lst.para with
      | some _ => { s with lst := { s.lst with para := some rest.toArray } }
      | none => { s with lst := { s.lst with nodes := rest.toArray } }
    | none => s
  | none => s

/-- What a `\last…` reads off the current list's last node: `skip` its glue,
`kern` its kern, else its penalty. -/
private def St.lastVal (s : St) (what : String) : Val :=
  match what, s.lastNode with
  | "lastskip", some (.vskip g) => .skip g
  | "lastskip", some (.tail k .glue) => .tail k .glue
  | "lastkern", some (.tail k .kern) => .tail k .kern
  | "lastpenalty", some (.penalty n) => .penalty n
  | "lastpenalty", some (.tail k .penalty) => .tail k .penalty
  | _, _ => .none

/-- The kernel's scratch registers a template may load a node's value into. -/
private def scratchRegs : List String :=
  ["skip@", "dimen@", "count@", "@tempskipa", "@tempskipb", "@tempdima", "@tempdimb",
   "@tempcnta", "@tempcntb"]

/-- An integer at `k`, TeX's ⟨number⟩, and the index after it. -/
private def St.intAt (s : St) (c : Chars) (k : Nat) : Option (Int × Nat) :=
  let (sign, j) := c.signs k
  match c.get j with
  | .cs "lastnodetype" => some (sign * (s.lastNode.map Node.typeOf).getD (-1), j + 1)
  | .cs r =>
    match s.scope.vals.lookup r with
    | some (.penalty n) => some (sign * n, j + 1)
    | _ => none
  | _ => (c.decimal j (whole := true)).map fun ((n, _), j') => (sign * n, c.optSp j')

/-- A relation at `k` past spaces: `<`, `=` or `>`, and the index after it. -/
private def Chars.relAt (c : Chars) (k : Nat) : Option (Char × Nat) :=
  let j := c.skipSp k
  match c.get j with
  | .ch '<' => some ('<', j + 1)
  | .ch '=' => some ('=', j + 1)
  | .ch '>' => some ('>', j + 1)
  | _ => none

/-- Whether a length is known to be at least or at most zero, and strictly, from the signs of
its terms. -/
private def Dimen.signs (d : Dimen) (packed : List Nat) : (Bool × Bool) × (Bool × Bool) :=
  let fixed := d.len.sp
  let pos := [d.len.em, d.len.ex, d.line, d.parskip, d.lead, d.cap]
  let known := d.ext.all fun (id, e, _) => packed.contains id && e != .wd
  let terms := pos ++ d.ext.map (·.2.2)
  let nonneg := known && terms.all (· ≥ 0) && fixed ≥ 0
  let nonpos := known && terms.all (· ≤ 0) && fixed ≤ 0
  ((nonneg, nonpos), (nonneg && fixed > 0, nonpos && fixed < 0))

/-- `\ifdim`'s comparison of two lengths, where the sign their difference
is known to take decides it (`Dimen.signs`): a length at least zero is
never below zero. -/
private def ifDimHolds (a b : Dimen) (rel : Char) (packed : List Nat) : Option Bool := do
  let d ← a.add? b.neg
  let ((nonneg, nonpos), (pos, neg)) := d.signs packed
  match rel with
  | '<' => if neg then some true else if nonneg then some false else none
  | '>' => if pos then some true else if nonpos then some false else none
  | '=' => if nonneg && nonpos then some true else if pos || neg then some false else none
  | _ => none

/-- Close the open paragraph of the current list, as `\par` does: its line
joins the list, whose `\prevdepth` is then the line's depth. -/
private def St.closePara (s : St) : St :=
  match s.lst.para with
  | some kids =>
    -- TeX's `\par` takes the paragraph's final glue off its list (tex.web §1096).
    let kids := if kids.back? matches some (.space ..) | some (.hskip _ _ false) then kids.pop
      else kids
    let id := s.nextId
    { s with nextId := id + 1, packed := id :: s.packed, lst := { s.lst with
        nodes := s.lst.nodes.push (.line id s.lst.paraParskip s.scope.hsize kids), para := none
        prev := { ext := [(id, .dp, 1)] } } }
  | none => s

/-- Horizontal material: in a vertical list it opens a paragraph, spending `\parskip` unless it
opens an empty box's list. -/
private def St.pushH (s : St) (n : Node) : St :=
  if s.move.isSome then s.miss "\\moveleft or \\moveright before something other than a box" else
  if s.lst.vertical then
    match s.lst.para with
    | some kids => { s with lst := { s.lst with para := some (kids.push n) } }
    | none =>
      let parskip := !s.lst.inner || !s.lst.nodes.isEmpty
      { s with lst := { s.lst with para := some #[n], paraParskip := parskip } }
  else { s with lst := { s.lst with nodes := s.lst.nodes.push n } }

/-- Start a paragraph with nothing in it yet (`\noindent`, `\leavevmode`). -/
private def St.startPara (s : St) : St :=
  if s.lst.vertical && s.lst.para.isNone then
    let parskip := !s.lst.inner || !s.lst.nodes.isEmpty
    { s with lst := { s.lst with para := some #[], paraParskip := parskip } }
  else s

/-- Vertical material: it ends the paragraph; in a horizontal box it is
TeX's error, named. -/
private def St.pushV (s : St) (n : Node) (what : String) : St :=
  if s.move.isSome then s.miss "\\moveleft or \\moveright before something other than a box" else
  if s.lst.vertical then
    let s := s.closePara
    { s with lst := { s.lst with nodes := s.lst.nodes.push n } }
  else s.miss (what ++ " in a horizontal box")

/-- The identity a box's extents are read by. -/
private def Node.boxId? : Node → Option Nat
  | .box id .. | .sized id .. => some id
  | .moved _ n => n.boxId?
  | _ => none

/-- A box (or lap) finished in the list it stands in: in vertical mode it
joins the list itself, shifted as a pending `\moveleft` says, and the list's
`\prevdepth` is its depth; in horizontal mode it joins the line. -/
private def St.place (s : St) (n : Node) : St :=
  if s.lst.vertical && s.lst.para.isNone then
    let n := match s.move with
      | some d => Node.moved d n
      | none => n
    let prev := match n.boxId? with
      | some id => { ext := [(id, .dp, 1)] }
      | none => s.lst.prev
    { s with move := none, lst := { s.lst with nodes := s.lst.nodes.push n, prev := prev } }
  else s.pushH n

/-- A colour change: a node of the list it stands in. -/
private def St.paint (s : St) (p : Paint) : St :=
  let s := { s with scope := { s.scope with paint := some p } }
  if s.lst.vertical then
    match s.lst.para with
    | some kids => { s with lst := { s.lst with para := some (kids.push .whatsit) } }
    | none => { s with lst := { s.lst with nodes := s.lst.nodes.push .whatsit } }
  else { s with lst := { s.lst with nodes := s.lst.nodes.push .whatsit } }

/-- Open a frame: a group keeps the list; a box or a lap starts its own. -/
private def St.open (s : St) (kind : FrameKind) : St :=
  let fr : Frame := { kind := kind, saved := s.scope, outer := s.lst }
  match kind with
  | .group _ => { s with frames := fr :: s.frames }
  | .box _ _ vertical _ =>
    { s with frames := { fr with move := s.move } :: s.frames, move := none
             lst := { vertical := vertical, inner := true } }
  | .lap _ | .raise .. =>
    { s with frames := fr :: s.frames, lst := { vertical := false, inner := true } }

/-- Close the innermost frame at its closing brace. -/
private def St.close (s : St) (simple : Bool) : St :=
  match s.frames with
  | [] => s.miss "a closing brace with no group open"
  | fr :: rest =>
    match fr.kind with
    | .group simple' =>
      if simple != simple' then s.miss "\\begingroup and a brace closing each other"
      else { s with frames := rest, scope := fr.saved }.restoreBoxes fr
    | .box target id vertical to =>
      if simple then s.miss "\\endgroup closing a box" else
      if s.move.isSome then s.miss "\\moveleft or \\moveright before something other than a box" else
      let s := s.closePara
      let node := match to with
        | some h => Node.sized id vertical h s.lst.nodes
        | none => Node.box id vertical s.scope.hsize s.lst.nodes s.lst.prev
      let s := ({ s with frames := rest, scope := fr.saved, lst := fr.outer
                         packed := if vertical then s.packed else id :: s.packed } : St).restoreBoxes fr
      match target with
      | some (r, global) =>
        if fr.move.isSome then s.miss "\\moveleft or \\moveright before a box register's assignment"
        else s.setBox r (some node) global
      | none => { s with move := fr.move }.place node
    | .lap right =>
      if simple then s.miss "\\endgroup closing a lap" else
      let node := Node.lap right s.lst.nodes
      let s := ({ s with frames := rest, scope := fr.saved, lst := fr.outer } : St).restoreBoxes fr
      s.place node
    | .raise lift ht dp =>
      if simple then s.miss "\\endgroup closing a \\raisebox" else
      let node := Node.raised lift ht dp s.lst.nodes
      let s := ({ s with frames := rest, scope := fr.saved, lst := fr.outer } : St).restoreBoxes fr
      s.pushH node

/-- TeX's conditional heads: an `\if…` among them opens a conditional the
skip counts; any other `\if…` word the reader does not read. -/
private def condHeads : List String :=
  ["if", "ifcat", "ifnum", "ifdim", "ifodd", "ifvmode", "ifhmode", "ifmmode", "ifinner",
   "ifvoid", "ifhbox", "ifvbox", "ifx", "ifeof", "iftrue", "iffalse", "ifcase",
   "ifdefined", "ifcsname", "iffontchar"]

/-- From `i`, the index past the matching `\else` (`true`) or `\fi`, nested conditionals
skipped whole. -/
private def skipArm (flags : String → Option Bool) (toks : Array Tok) (i : Nat) :
    Option (Nat × Bool) := Id.run do
  let mut depth := 0
  let mut k := i
  for _ in [i:toks.size] do
    match toks[k]? with
    | some (.ctrl n) =>
      if condHeads.contains n || (n.startsWith "if" && n.length > 2 && (flags (n.drop 2).toString).isSome)
      then depth := depth + 1
      else if n == "fi" then
        if depth == 0 then return some (k + 1, false)
        depth := depth - 1
      else if n == "else" && depth == 0 then return some (k + 1, true)
    | some _ => pure ()
    | none => return none
    k := k + 1
  return none

/-- Control words that change nothing a block's lists show here: penalties
(a frame is not broken inside a block), and expansion no-ops. -/
private def inert : List String :=
  ["relax", "noframebreak", "@empty", "empty", "protect"]

/-- An assignment to a length register at token `i`, the register's name
just read: `\X = <dimen>` in the group, or at every level where `global`;
`\advance\X by <dimen>` adds to its value. -/
private def St.assignAt (s : St) (n : String) (i : Nat) (global advance : Bool) : St × Nat :=
  let i := if advance then
      let j := s.chars.skipSp (s.chars.first i)
      match s.chars.keyword j "by", s.chars.tokAt j with
      | some k, _ => (s.chars.tokAt k).getD i
      | none, some t => t
      | none, none => i
    else i
  match s.readDimen s.chars i with
  | some (d, k) =>
    if !advance then (s.assign n d global, k)
    else match s.dimen? n with
      | some (some cur) =>
        match cur.add? d with
        | some v => (s.assign n v global, k)
        | none => (s.miss s!"\\advance\\{n} by a length in another font", k)
      | _ => (s.miss s!"\\advance\\{n} of a value this reading does not hold", k)
  | none => (s.miss s!"\\{n} set to a length it cannot read", i)

/-- A box specification at token `i`: an optional `to` and its height, then
the brace opening the box's list — the height, and the index past the
brace. -/
private def St.boxSpecAt (s : St) (toks : Array Tok) (i : Nat) : Option (Option Dimen × Nat) :=
  let j := skipSp toks i
  if toks[j]? == some .bg then some (none, j + 1) else do
  let k ← s.chars.keyword (s.chars.first j) "to"
  let (d, k') ← s.dimenAt s.chars k
  let t ← s.chars.tokAt k'
  if toks[skipSp toks t]? == some .bg then some (some d, skipSp toks t + 1) else none

/-- The tokens of an optional `[...]` at `i`, and the index after it. -/
private def readOptToks (toks : Array Tok) (i : Nat) : Option (Array Tok) × Nat := Id.run do
  let j := skipSp toks i
  unless toks[j]? == some (.sym '[') do return (none, i)
  let mut out : Array Tok := #[]
  let mut k := j + 1
  for _ in [j + 1:toks.size] do
    match toks[k]? with
    | some (.sym ']') => return (some out, k + 1)
    | some t => out := out.push t
    | none => return (none, i)
    k := k + 1
  return (none, i)

/-- The interpreter's loop over a flat list from `s0`; a macro calling itself takes a node off
its list first, so the calls end. -/
private def runToks (defs : String → Option Macro) (titled : Bool) (tail : Array TailKind)
    (bound : Nat) (toks : Array Tok) (s0 : St) : St := Id.run do
  let mut s : St := { s0 with chars := Chars.of toks }
  let mut i := 0
  for _ in [0:toks.size] do
    if i ≥ toks.size then break
    let some t := toks[i]? | break
    match t with
    | .sym '%' => i := i + 1
    | .space =>
      if s.lst.para.isSome || !s.lst.vertical then s := s.pushH (.space s.scope.font)
      i := i + 1
    | .par => s := s.closePara; i := i + 1
    | .body =>
      let id := s.nextId
      s := { s with nextId := id + 1, packed := id :: s.packed }
      s := s.pushV (.body id s.scope.font s.scope.paint) "the body"
      s := { s with lst := { s.lst with prev := { ext := [(id, .dp, 1)] } } }
      for k in [0:tail.size] do
        s := s.pushV (.tail k (tail[k]?.getD .glue)) "the body"
      i := i + 1
    | .bg => s := s.open (.group false); i := i + 1
    | .eg => s := s.close false; i := i + 1
    | .word w => s := s.miss s!"the text '{w}'"; i := i + 1
    | .sym c => s := s.miss s!"the text '{c}'"; i := i + 1
    | .ctrl n =>
      if inert.contains n then i := i + 1 else
      match n with
      | "par" => s := s.closePara; i := i + 1
      | "begingroup" => s := s.open (.group true); i := i + 1
      | "endgroup" => s := s.close true; i := i + 1
      | "noindent" | "leavevmode" | "indent" => s := s.startPara; i := i + 1
      | "strut" => s := s.pushH (.strut s.scope.font); i := i + 1
      | "insertblocktitle" =>
        s := s.pushH (.title s.scope.font s.scope.paint); i := i + 1
      | "smallskip" | "medskip" | "bigskip" =>
        let reg := (n.dropEnd 4).toString ++ "skipamount"
        s := s.pushV (.vskip (.register reg)) s!"\\{n}"
        i := i + 1
      | "vskip" =>
        match toks[skipSp toks (i + 1)]? with
        | some (.ctrl r) =>
          match s.scope.vals.lookup r with
          | some (.tail k .glue) => s := s.pushV (.tail k .glue) "\\vskip"; i := skipSp toks (i + 1) + 1
          | some (.skip g) => s := s.pushV (.vskip g) "\\vskip"; i := skipSp toks (i + 1) + 1
          | some _ => s := s.miss "\\vskip of a register holding no glue"; i := i + 1
          | none =>
            match s.readGlue s.chars (i + 1) with
            | some (g, k) => s := s.pushV (.vskip g) "\\vskip"; i := k
            | none => s := s.miss "\\vskip with a glue it cannot read"; i := i + 1
        | _ =>
          match s.readGlue s.chars (i + 1) with
          | some (g, k) => s := s.pushV (.vskip g) "\\vskip"; i := k
          | none => s := s.miss "\\vskip with a glue it cannot read"; i := i + 1
      | "vspace" =>
        let j := skipSp toks (i + 1)
        let j := if toks[j]? == some (.word "*") then j + 1 else j
        match readArg toks j with
        | some (arg, k) =>
          match s.readGlue (Chars.of arg) 0 with
          | some (g, _) => s := s.pushV (.vskip g) "\\vspace"
          | none => s := s.miss "\\vspace with a glue it cannot read"
          i := k
        | none => s := s.miss "\\vspace"; i := i + 1
      | "hskip" | "kern" | "hspace" =>
        if n == "kern" && s.lst.vertical && s.lst.para.isNone then
          match toks[skipSp toks (i + 1)]? with
          | some (.ctrl r) =>
            match s.scope.vals.lookup r with
            | some (.tail k .kern) => s := s.pushV (.tail k .kern) "\\kern"; i := skipSp toks (i + 1) + 1
            | _ => s := s.miss "a vertical \\kern"; i := i + 1
          | _ => s := s.miss "a vertical \\kern"; i := i + 1
        else
          let (dim, k) : Option Dimen × Nat :=
            if n == "hspace" then
              match readArg toks (i + 1) with
              | some (arg, k) => ((s.readDimen (Chars.of arg) 0).map (·.1), k)
              | none => (none, i + 1)
            else match s.readGlue s.chars (i + 1) with
              | some (.glue g, k) =>
                if g.stretch == {} && g.shrink == {} then
                  (some (Dimen.norm { len := g.width, font := some s.scope.font }), k)
                else (none, k)
              | _ => (none, i + 1)
          match dim with
          | some d => s := s.pushH (.hskip d s.scope.font (n == "kern"))
          | none => s := s.miss s!"\\{n} with stretch or an unreadable length"
          i := k
      | "hsize" =>
        match s.readDimen s.chars (i + 1) with
        | some (d, k) => s := { s with scope := { s.scope with hsize := d } }; i := k
        | none => s := s.miss "\\hsize set to a length it cannot read"; i := i + 1
      | "global" =>
        if toks[skipSp toks (i + 1)]? == some (.ctrl "setbox") then
          s := { s with globalNext := true }; i := skipSp toks (i + 1)
        else
        let j := skipSp toks (i + 1)
        let (j, advance) :=
          if toks[j]? == some (.ctrl "advance") then (skipSp toks (j + 1), true) else (j, false)
        match toks[j]? with
        | some (.ctrl "hsize") => s := s.miss "\\global\\hsize"; i := j + 1
        | some (.ctrl r) =>
          if (s.dimen? r).isSome then
            let (s', k) := s.assignAt r (j + 1) true advance
            s := s'
            i := k
          else s := s.miss s!"\\{n}"; i := i + 1
        | _ => s := s.miss s!"\\{n}"; i := i + 1
      | "advance" =>
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl "hsize") =>
          let k0 := s.chars.skipSp (s.chars.first (j + 1))
          let j' := match s.chars.keyword k0 "by" with
            | some k => (s.chars.tokAt k).getD (j + 1)
            | none => j + 1
          match s.readDimen s.chars j' with
          | some (d, k) =>
            match s.scope.hsize.add? d with
            | some h => s := { s with scope := { s.scope with hsize := h } }; i := k
            | none => s := s.miss "\\advance\\hsize by a length in another font"; i := k
          | none => s := s.miss "\\advance\\hsize by a length it cannot read"; i := j'
        | some (.ctrl r) =>
          if (s.dimen? r).isSome then
            let (s', k) := s.assignAt r (j + 1) false true
            s := s'
            i := k
          else s := s.miss s!"\\{n}"; i := i + 1
        | _ => s := s.miss s!"\\{n}"; i := i + 1
      | "newdimen" =>
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl r) =>
          s := { s with declared := r :: s.declared, dimens := s.dimens.filter (·.1 != r) }
          i := j + 1
        | _ => s := s.miss "\\newdimen"; i := i + 1
      | "usebeamerfont" =>
        let j := skipSp toks (i + 1)
        let j := if toks[j]? == some (.word "*") then j + 1 else j
        match readArg toks j with
        | some (arg, k) =>
          s := { s with scope := { s.scope with font := some (wordsOf arg).trimAscii.toString } }
          i := k
        | none => s := s.miss "\\usebeamerfont"; i := i + 1
      | "usebeamercolor" =>
        let j := skipSp toks (i + 1)
        let starred := toks[j]? == some (.word "*")
        let j := if starred then j + 1 else j
        let (ch, j) := readOpt toks j
        match readArg toks j with
        | some (arg, k) =>
          let el := (wordsOf arg).trimAscii.toString
          let bind (s : St) (el : String) : St × List String :=
            let chain := el :: s.scope.channels.filter (· != el)
            ({ s with scope := { s.scope with channels := chain } }, chain)
          -- The starred form first uses normal text's foreground.
          if starred then
            let (s', chain) := bind s "normal text"
            s := s'.paint (.beamer chain "fg")
          let (s', chain) := bind s el
          s := s'
          match ch with
          | some c =>
            if c == "fg" || c == "bg" then s := s.paint (.beamer chain c)
            else s := s.miss s!"\\usebeamercolor[{c}]"
          | none => pure ()
          -- xcolor's `\color` ends ignoring spaces (beamerbasecolor.sty).
          i := if ch.isSome then skipSp toks k else k
        | none => s := s.miss "\\usebeamercolor"; i := i + 1
      | "color" =>
        let (model, j) := readOpt toks (i + 1)
        match model, readArg toks j with
        | none, some (arg, k) =>
          let name := (wordsOf arg).trimAscii.toString
          let p : Paint := if name.endsWith ".fg" then .beamer [(name.dropEnd 3).toString] "fg"
            else if name.endsWith ".bg" then .beamer [(name.dropEnd 3).toString] "bg"
            else if (name == "fg" || name == "bg") && !s.scope.channels.isEmpty then
              .beamer s.scope.channels name
            else .named name
          s := s.paint p
          i := skipSp toks k
        | _, _ => s := s.miss "\\color"; i := i + 1
      | "vrule" =>
        match s.readRuleSpec s.chars (i + 1) with
        | some ((w, h, d), k) =>
          let w := w.orElse fun _ => some { len := { sp := Dim.pt 4 / 10 } }
          s := s.pushH (.rule w h d s.scope.paint s.scope.font)
          i := k
        | none => s := s.miss "\\vrule with a dimension it cannot read"; i := i + 1
      | "hrule" =>
        match s.readRuleSpec s.chars (i + 1) with
        | some (_, k) => s := s.pushV .hrule "\\hrule"; i := k
        | none => s := s.miss "\\hrule with a dimension it cannot read"; i := i + 1
      | "llap" | "rlap" =>
        let j := skipSp toks (i + 1)
        if toks[j]? == some .bg then
          s := s.open (.lap (n == "rlap")); i := j + 1
        else s := s.miss s!"\\{n} without a braced argument"; i := i + 1
      | "vbox" | "hbox" | "vtop" =>
        if n == "vtop" then s := s.miss "\\vtop"; i := i + 1
        else match s.boxSpecAt toks (i + 1) with
          | some (to, k) =>
            s := s.open (.box none s.nextId (n == "vbox") to)
            s := { s with nextId := s.nextId + 1 }
            i := k
          | none => s := s.miss s!"\\{n} with a size spec it cannot read"; i := i + 1
      | "setbox" =>
        let global := s.globalNext
        s := { s with globalNext := false }
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl r) =>
          let j := skipSp toks (j + 1)
          let j := if toks[j]? == some (.word "=") || toks[j]? == some (.sym '=') then
            skipSp toks (j + 1) else j
          match toks[j]? with
          | some (.ctrl b) =>
            let j' := skipSp toks (j + 1)
            let spec := if b == "vbox" || b == "hbox" then s.boxSpecAt toks (j + 1) else none
            if let some (to, k) := spec then
              s := s.open (.box (some (r, global)) s.nextId (b == "vbox") to)
              s := { s with nextId := s.nextId + 1 }
              i := k
            else if b == "box" || b == "copy" then
              match toks[j']? with
              | some (.ctrl src) =>
                let v := s.boxOf src
                let s1 := if b == "box" then s.voidBox src else s
                s := s1.setBox r v global
                i := j' + 1
              | _ => s := s.miss "\\setbox"; i := i + 1
            else s := s.miss s!"\\setbox from \\{b}"; i := i + 1
          | _ => s := s.miss "\\setbox"; i := i + 1
        | _ => s := s.miss "\\setbox"; i := i + 1
      | "box" | "copy" | "usebox" =>
        let (reg, k) : Option String × Nat :=
          if n == "usebox" then
            match readArg toks (i + 1) with
            | some (arg, k) =>
              match arg.toList.filter (· != .space) with
              | [.ctrl r] => (some r, k)
              | _ => (none, k)
            | none => (none, i + 1)
          else match toks[skipSp toks (i + 1)]? with
            | some (.ctrl r) => (some r, skipSp toks (i + 1) + 1)
            | _ => (none, i + 1)
        match reg with
        | some r =>
          match s.boxOf r with
          | some node =>
            let s1 := if n == "box" then s.voidBox r else s
            s := s1.place node
          | none => pure ()
          i := k
        | none => s := s.miss s!"\\{n}"; i := k
      | "unvbox" | "unvcopy" =>
        -- `\unvbox` leaves `\prevdepth` as it was.
        match toks[skipSp toks (i + 1)]? with
        | some (.ctrl r) =>
          match s.boxOf r with
          | some (.box id true _ kids e) =>
            let s1 := if n == "unvbox" then s.voidBox r else s
            s := s1.pushV (.unboxed id kids s1.lst.prev e) s!"\\{n}"
          | some _ => s := s.miss s!"\\{n} of a box it cannot set back"
          | none => pure ()
          i := skipSp toks (i + 1) + 1
        | _ => s := s.miss s!"\\{n}"; i := i + 1
      | "prevdepth" | "nointerlineskip" =>
        if !(s.lst.vertical && s.lst.para.isNone) then
          s := s.miss s!"\\{n} outside a vertical list"; i := i + 1
        else
          let read : Option (Dimen × Nat) :=
            if n == "nointerlineskip" then some (ignoreDepth, i + 1) else s.readDimen s.chars (i + 1)
          match read with
          | some (d, k) =>
            s := s.pushV (.prevdepth d) s!"\\{n}"
            s := { s with lst := { s.lst with prev := d } }
            i := k
          | none => s := s.miss "\\prevdepth set to a length it cannot read"; i := i + 1
      | "ignorespaces" => i := skipSp toks (i + 1)
      | "nobreak" | "allowbreak" =>
        if s.lst.vertical && s.lst.para.isNone then
          s := s.pushV (.penalty (if n == "nobreak" then 10000 else 0)) s!"\\{n}"
        i := i + 1
      | "penalty" =>
        let vertical := s.lst.vertical && s.lst.para.isNone
        match toks[skipSp toks (i + 1)]? with
        | some (.ctrl r) =>
          if vertical then
            match s.scope.vals.lookup r with
            | some (.tail k .penalty) => s := s.pushV (.tail k .penalty) "\\penalty"
            | some (.penalty v) => s := s.pushV (.penalty v) "\\penalty"
            | some .none => s := s.pushV (.penalty 0) "\\penalty"
            | _ => s := s.miss "\\penalty of a register holding no penalty"
          i := skipSp toks (i + 1) + 1
        | _ =>
          match s.intAt s.chars (s.chars.skipSp (s.chars.first (i + 1))) with
          | some (v, k) =>
            match s.chars.tokAt k with
            | some t =>
              if vertical then s := s.pushV (.penalty v) "\\penalty"
              i := t
            | none => s := s.miss "\\penalty"; i := i + 1
          | none => s := s.miss "\\penalty"; i := i + 1
      | "unskip" | "unkern" | "unpenalty" =>
        let pick : Node → Bool := match n with
          | "unskip" => fun x => (x matches .vskip .. | .hskip _ _ false | .space .. | .tail _ .glue)
          | "unkern" => fun x => (x matches .hskip _ _ true | .tail _ .kern)
          | _ => fun x => (x matches .penalty .. | .tail _ .penalty)
        s := s.dropLast pick
        i := i + 1
      | "moveleft" | "moveright" =>
        if !(s.lst.vertical && s.lst.para.isNone) then
          s := s.miss s!"\\{n} outside a vertical list"; i := i + 1
        else
          match s.readDimen s.chars (i + 1) with
          | some (d, k) => s := { s with move := some (if n == "moveleft" then d.neg else d) }; i := k
          | none => s := s.miss s!"\\{n} by a length it cannot read"; i := i + 1
      | "vss" => s := s.pushV .vss "\\vss"; i := i + 1
      | "raisebox" =>
        match readArg toks (i + 1) with
        | some (arg, k) =>
          match s.readDimen (Chars.of arg) 0 with
          | some (lift, _) =>
            let (ht, k) := readOptToks toks k
            let (dp, k) := readOptToks toks k
            let dim (o : Option (Array Tok)) : Option (Option Dimen) :=
              o.map fun ts => (s.readDimen (Chars.of ts) 0).map (·.1)
            match dim ht, dim dp with
            | some none, _ | _, some none => s := s.miss "\\raisebox sized by a length it cannot read"; i := k
            | h, d =>
              let j := skipSp toks k
              if toks[j]? == some .bg then
                s := s.open (.raise lift h.join d.join); i := j + 1
              else s := s.miss "\\raisebox without its content"; i := k
          | none => s := s.miss "\\raisebox by a length it cannot read"; i := k
        | none => s := s.miss "\\raisebox"; i := i + 1
      | "ifnum" | "ifdim" =>
        let k0 := s.chars.skipSp (s.chars.first (i + 1))
        let decided : Option (Bool × Nat) :=
          if n == "ifnum" then do
            let (a, k1) ← s.intAt s.chars k0
            let (rel, k2) ← s.chars.relAt k1
            let (b, k3) ← s.intAt s.chars (s.chars.skipSp k2)
            let t ← s.chars.tokAt k3
            let holds := match rel with
              | '<' => a < b
              | '=' => a == b
              | _ => a > b
            pure (holds, t)
          else do
            let (a, k1) ← s.dimenAt s.chars k0
            let (rel, k2) ← s.chars.relAt k1
            let (b, k3) ← s.dimenAt s.chars (s.chars.skipSp k2)
            let t ← s.chars.tokAt k3
            let holds ← ifDimHolds a b rel s.packed
            pure (holds, t)
        match decided with
        | some (true, t) => s := { s with conds := .thenArm :: s.conds }; i := t
        | some (false, t) =>
          match skipArm s.flag? toks t with
          | some (k', true) => s := { s with conds := .elseArm :: s.conds }; i := k'
          | some (k', false) => i := k'
          | none => s := s.miss s!"\\{n} without \\fi"; i := toks.size
        | none => s := s.miss s!"\\{n} of a comparison it cannot decide"; i := i + 1
      | "newbox" =>
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl r) => s := s.setBox r none true; i := j + 1
        | _ => s := s.miss "\\newbox"; i := i + 1
      | "ifx" =>
        let j := skipSp toks (i + 1)
        let k := skipSp toks (j + 1)
        let pair := match toks[j]?, toks[k]? with
          | some (.ctrl a), some (.ctrl b) => some (a, b)
          | _, _ => none
        let titleTest := match pair with
          | some ("insertblocktitle", e) | some (e, "insertblocktitle") => e == "@empty" || e == "empty"
          | _ => false
        if !titleTest then s := s.miss "\\ifx"; i := i + 1
        else
          -- The test is true where the title is empty.
          if !titled then
            s := { s with conds := .thenArm :: s.conds }; i := k + 1
          else
            match skipArm s.flag? toks (k + 1) with
            | some (k', true) => s := { s with conds := .elseArm :: s.conds }; i := k'
            | some (k', false) => i := k'
            | none => s := s.miss "\\ifx without \\fi"; i := toks.size
      | "else" =>
        match s.conds with
        | .thenArm :: rest =>
          match skipArm s.flag? toks (i + 1) with
          | some (k', false) => s := { s with conds := rest }; i := k'
          | _ => s := s.miss "\\else without its \\fi"; i := toks.size
        | _ => s := s.miss "\\else"; i := i + 1
      | "fi" =>
        match s.conds with
        | _ :: rest => s := { s with conds := rest }; i := i + 1
        | [] => s := s.miss "\\fi"; i := i + 1
      | _ =>
        if let some holds := s.flagTest n then
          if holds then s := { s with conds := .thenArm :: s.conds }; i := i + 1
          else
            match skipArm s.flag? toks (i + 1) with
            | some (k', true) => s := { s with conds := .elseArm :: s.conds }; i := k'
            | some (k', false) => i := k'
            | none => s := s.miss s!"\\{n} without \\fi"; i := toks.size
        else if let some (x, b) := s.flagSet n then
          s := { s with scope := { s.scope with flags := (x, b) :: s.scope.flags.filter (·.1 != x) } }
          i := i + 1
        else if (s.dimen? n).isSome then
          let (s', k) := s.assignAt n (i + 1) false false
          s := s'
          i := k
        else if scratchRegs.contains n then
          let j := skipSp toks (i + 1)
          let j := if toks[j]? == some (.sym '=') then skipSp toks (j + 1) else j
          match toks[j]? with
          | some (.ctrl what) =>
            if what == "lastskip" || what == "lastkern" || what == "lastpenalty" then
              s := { s with scope := { s.scope with
                vals := (n, s.lastVal what) :: s.scope.vals.filter (·.1 != n) } }
              i := j + 1
            else s := s.miss s!"\\{n} set to a value it cannot read"; i := i + 1
          | _ => s := s.miss s!"\\{n} set to a value it cannot read"; i := i + 1
        else match defs n with
          | some m =>
            if m.arity != 0 then s := s.miss s!"\\{n} run where the template stands, with arguments"; i := i + 1
            else if h : s.lst.nodes.size < bound then
              let depth := (s.frames.length, s.conds.length)
              let body := expandList defs m.serial (flatten m.body).toList #[]
              let s' := runToks defs titled tail s.lst.nodes.size body s
              s := if (s'.frames.length, s'.conds.length) == depth then s'
                else s'.miss s!"\\{n} leaving a group or a conditional open"
              i := i + 1
            else s := s.miss s!"\\{n} run again on a list it does not shorten"; i := i + 1
          | none =>
            s := s.miss s!"\\{n}"
            i := i + 1
  return { s with chars := s0.chars }
termination_by bound

/-- The interpreter's main loop over the flat list: the block's own list
opens on the depth of the box before the block. -/
private def run (defs : String → Option Macro) (toks : Array Tok) (titled : Bool)
    (tail : Array TailKind) (lengths : String → Option (Option Dimen))
    (flags : String → Option Bool) : St := Id.run do
  let s0 : St := { lengths, flags, lst := { prev := { ext := [(priorId, .dp, 1)] } } }
  let mut s := runToks defs titled tail (toks.size + tail.size + 2) toks s0
  s := s.closePara
  unless s.frames.isEmpty do s := s.miss "a group the template never closes"
  unless s.conds.isEmpty do s := s.miss "a conditional the template never closes"
  return s

/-- A template rule as read, before its colour is a palette entry. -/
public structure EdgeRead where
  span : Ir.BlockSpan
  side : Ir.FlushSide
  width : SymLength
  sep : SymLength
  hang : Bool
  paint : Option Paint
  reach : Ir.BlockReach := .box
  deriving Repr, BEq, Inhabited

/-- What a template pair sets, read: `Ir.BlockShape` but for its rules' colours, with the font
elements and colours of title and body. -/
public structure Read where
  before : Array Ir.BlockSkip := #[]
  title : Ir.BlockTitleBox := {}
  bare : Option Ir.BlockBare := none
  between : Array Ir.BlockSkip := #[]
  after : Array Ir.BlockSkip := #[]
  whole : Option Bool := none
  edges : Array EdgeRead := #[]
  titleFont : Option String := none
  titlePaint : Option Paint := none
  bodyFont : Option String := none
  bodyPaint : Option Paint := none
  deriving Repr, BEq, Inhabited

/-- One arm's lists, lowered. -/
private structure Arm where
  before : Array Ir.BlockSkip := #[]
  title : Option Ir.BlockTitleBox := none
  between : Array Ir.BlockSkip := #[]
  after : Array Ir.BlockSkip := #[]
  whole : Option Bool := none
  edges : Array EdgeRead := #[]
  titleFont : Option String := none
  titlePaint : Option Paint := none
  bodyFont : Option String := none
  bodyPaint : Option Paint := none
  deriving Repr, BEq, Inhabited

/-- A title paragraph's line, the title between optional struts: whether both ends are strutted,
and the title's font element and paint. -/
private def titleLine (kids : Array Node) : Except String (Bool × Option String × Option Paint) :=
  let core := kids.filter (· != .whatsit)
  match core.toList with
  | [.title f p] => .ok (false, f, p)
  | [.strut _, .title f p, .strut _] => .ok (true, f, p)
  | [.strut _, .title _ _] | [.title _ _, .strut _] => .error "a title line strutted at one end only"
  | _ => .error "a title line holding more than the title and its struts"

/-- Whether a title line's struts are set in its title's own font, as a rule
reaching by its lines reads them. -/
private def strutsInFont (kids : Array Node) : Bool :=
  match (kids.filter (· != .whatsit)).toList with
  | [.strut a, .title f _, .strut b] => a == f && b == f
  | _ => true

/-- What a box's vertical list holds: an optional title paragraph, then
skips and the body (the box holding title and body), or the title alone
(the title's box). -/
private inductive Content where
  | titleBox (strut parskip : Bool) (font : Option String) (paint : Option Paint) (strutFont : Bool)
  | whole (title : Option (Bool × Bool × Option String × Option Paint))
      (between : Array Ir.BlockSkip) (bodyParskip : Bool) (font : Option String)
      (paint : Option Paint) (after : Array Ir.BlockSkip)

private def boxContent (kids : Array Node) : Except String Content := Id.run do
  let items := kids.filter fun n => n != .whatsit && !(n matches .penalty ..) && !(n matches .tail ..)
  let bodyIdx := kids.findIdx? (· matches .body ..)
  match items.toList with
  | [.line _ pk _ line] =>
    match titleLine line with
    | .ok (st, f, p) => return .ok (.titleBox st pk f p (strutsInFont line))
    | .error e => return .error e
  | _ =>
    let mut title : Option (Bool × Bool × Option String × Option Paint) := none
    let mut between : Array Ir.BlockSkip := #[]
    let mut after : Array Ir.BlockSkip := #[]
    let mut body : Option (Option String × Option Paint) := none
    for n in items do
      match n with
      | .line _ pk _ line =>
        if title.isSome || body.isSome then return .error "a line beside the body in its box"
        match titleLine line with
        | .ok (st, f, p) => title := some (st, pk, f, p)
        | .error e => return .error e
      | .vskip g => if body.isSome then after := after.push g else between := between.push g
      | .body _ f p =>
        if body.isSome then return .error "the body twice" else body := some (f, p)
      | _ => return .error "a box holding more than the title, skips and the body"
    match body with
    | none => return .error "a box holding neither the title alone nor the body"
    | some (f, p) =>
      let bodyParskip := match bodyIdx with
        | some k => k > 0
        | none => false
      return .ok (.whole title between bodyParskip f p after)

/-- A rule's reach beside its box: the box's extents, nothing for an emptied register, or the
title box's lines bounded by struts of the title's font; any other reach is refused. -/
private def reachOf (id : Nat) (title : Option (Option String × Bool × Bool × Bool))
    (h d : Option Dimen) :
    Except String (Option Ir.BlockReach) :=
  match h, d with
  | some h, some d =>
    if h == { ext := [(id, .ht, 1)] } && d == { ext := [(id, .dp, 1)] } then .ok (some .box)
    else if h == {} && d == {} then .ok none
    else match title with
      | none => .error "a rule whose height and depth are not its box's"
      | some (font, parskip, strut, strutFont) =>
        let metric (x : Dimen) : Option Ir.BlockMetric :=
          if x.line == 0 && x.len.em == 0 && x.len.ex == 0 && (!x.fonted || x.font == some font)
          then some { lead := x.lead, cap := x.cap, sp := x.len.sp.units } else none
        let lines := h.ext.length == 2 && h.ext.contains (id, .ht, 1) && h.ext.contains (id, .dp, 1)
        match metric h, metric d with
        | some mh, some md =>
          if !lines || !d.ext.isEmpty then
            .error "a rule beside the title's box reading other than its height and depth"
          else if h.parskip != (if parskip then -1000 else 0) || d.parskip != 0 then
            .error "a rule beside the title's box reading another skip than the one its list opens on"
          else if !strut then
            .error "a rule beside the title's box reaching by lines no strut bounds"
          else if !strutFont then
            .error "a rule beside the title's box reaching by lines struts of another font bound"
          else .ok (some (.lines mh md))
        | _, _ => .error "a rule beside the title's box measured in another font than its title's"
  | _, _ => .error "a rule running to its line"

/-- The rules beside one box in its line: `\llap{…\vrule…\hskip S}` before it hangs left,
`\vrule\hskip S` before it stands inside the line, and their mirrors after it. -/
private def edgesOf (span : Ir.BlockSpan) (id : Nat)
    (title : Option (Option String × Bool × Bool × Bool))
    (hsize : Dimen) (lineHsize : Dimen) (before after : List Node) :
    Except String (Array EdgeRead) := Id.run do
  let lenOf (d : Dimen) : Except String SymLength :=
    match d.length? with
    | some l =>
      if (l.em == 0 && l.ex == 0) || d.font == some none then .ok l
      else .error "a rule measured in a font of its own"
    | none => .error "a rule or space measured against a box"
  let side (onRight : Bool) (nodes : List Node) : Except String (Option EdgeRead × SymLength) := do
    let sideName : Ir.FlushSide := if onRight then .right else .left
    let ns := nodes.filter (· != .whatsit)
    match ns with
    | [] => return (none, {})
    | [.lap r kids] =>
      if r != onRight then throw "a lap reaching over its box"
      let inner := (kids.filter (· != .whatsit)).toList
      let outward := if onRight then inner else inner.reverse
      match outward with
      | [.rule (some w) h d p _] =>
        let some reach ← reachOf id title h d | return (none, {})
        return (some { span, side := sideName, width := ← lenOf w, sep := {}, hang := true,
                        paint := p, reach }, {})
      | [.hskip g _ _, .rule (some w) h d p _] =>
        let some reach ← reachOf id title h d | return (none, {})
        return (some { span, side := sideName, width := ← lenOf w, sep := ← lenOf g,
                        hang := true, paint := p, reach }, {})
      | _ => throw "a lap holding more than a rule and its space"
    | _ =>
      let outward := if onRight then ns else ns.reverse
      match outward with
      | [.hskip g _ _, .rule (some w) h d p _] =>
        let some reach ← reachOf id title h d
          | throw "a rule beside its box that draws nothing but still takes room"
        let wl ← lenOf w
        let gl ← lenOf g
        return (some { span, side := sideName, width := wl, sep := gl, hang := false,
                        paint := p, reach }, wl.add gl)
      | [.rule (some w) h d p _] =>
        let some reach ← reachOf id title h d
          | throw "a rule beside its box that draws nothing but still takes room"
        let wl ← lenOf w
        return (some { span, side := sideName, width := wl, sep := {}, hang := false,
                        paint := p, reach }, wl)
      | _ => throw "a line holding more than its box and the rules beside it"
  match side false before, side true after with
  | .ok (l, li), .ok (r, ri) =>
    -- The box and the rules inside its line fill the line exactly.
    match hsize.add? (Dimen.norm { len := li.add ri, font := some none }) with
    | some used =>
      if used != lineHsize then return .error "a box and its rules that do not fill their line"
      return .ok ((l.toList ++ r.toList).toArray)
    | none => return .error "a box and its rules that do not fill their line"
  | .error e, _ | _, .error e => return .error e

mutual

-- conserves: none — the body's items a set-back box holds; no document content
private def tailsIn (acc : Array Nat) : List Node → Option (Array Nat)
  | [] => some acc
  | n :: rest => (tailsOf acc n).bind (tailsIn · rest)

private def tailsOf (acc : Array Nat) : Node → Option (Array Nat)
  | .tail k _ => some (acc.push k)
  | .unboxed _ kids _ _ => tailsIn acc kids.toList
  | _ => none

end

/-- Two rules' paints as one colour: a colour by name, or the channel of each rule's own element. -/
private def Paint.sameAs : Option Paint → Option Paint → Bool
  | some (.beamer (a :: _) ca), some (.beamer (b :: _) cb) => a == b && ca == cb
  | a, b => a == b

/-- A length that is zero. -/
private def Dimen.zero? (d : Dimen) : Bool := Dimen.norm d == ({} : Dimen)

/-- Two lengths that are one: their difference is zero term by term. -/
private def Dimen.same (a b : Dimen) : Bool := match a.add? b.neg with
  | some d => d.zero?
  | none => false

/-- A title metric as the length it reads in the title's font. -/
private def metricDimen (m : Ir.BlockMetric) (font : Option String) : Dimen :=
  Dimen.norm { len := { sp := .ofUnits m.sp }, lead := m.lead, cap := m.cap, font := some font }

/-- The rule a box of no size sets on its baseline: its shift, the rule's lift, size and paint. -/
private def overlayRule (n : Node) :
    Option (Dimen × Dimen × Option Dimen × Option Dimen × Option Dimen × Option Paint) :=
  let real (ks : Array Node) : List Node := (ks.filter (· != .whatsit)).toList
  match n with
  | .moved shift (.sized _ true to kids) =>
    if !to.zero? then none else
    let hkids := match real kids with
      | [.vss, .box _ false _ hk _] | [.box _ false _ hk _, .vss] => some hk
      | _ => none
    let after (ns : List Node) : Bool := ns.all fun x => x matches .space _ | .hskip ..
    match hkids.map real with
    | some (.raised lift (some h0) (some d0) rk :: tail) =>
      if !h0.zero? || !d0.zero? || !after tail then none else
      match real rk with
      | .rule w h d p _ :: tail => if after tail then some (shift, lift, w, h, d, p) else none
      | _ => none
    | _ => none
  | _ => none

/-- One arm's top-level list lowered: skips, the title's line or a box line, skips, the body or
its box, skips, with a set-back body's rule beside the whole block. -/
private def lowerArm (nodes : Array Node) (tailSize : Nat) : Except String Arm := Id.run do
  let mut arm : Arm := {}
  let mut seenTitle := false
  let mut seenBody := false
  let mut titleLine? : Option Nat := none
  let mut unboxed : Option (Nat × Dimen) := none
  let mut owed := false
  let mut joinedFlush := false
  let mut ruled := false
  let mut tails : Array Nat := #[]
  let mut tailFirst := false
  for n in nodes do
    let flush := joinedFlush
    joinedFlush := false
    match n with
    | .whatsit | .penalty _ => joinedFlush := flush
    | .tail k _ => tails := tails.push k
    | .vskip g =>
      if seenBody then arm := { arm with after := arm.after.push g }
      else if seenTitle then arm := { arm with between := arm.between.push g }
      else arm := { arm with before := arm.before.push g }
    | .body _ f p =>
      if seenBody then return .error "the body twice"
      seenBody := true
      arm := { arm with bodyFont := f, bodyPaint := p }
    | .prevdepth d =>
      match unboxed with
      | some (_, e) =>
        if d == ignoreDepth then joinedFlush := true
        else if Dimen.same d e then owed := false
        else return .error "\\prevdepth set after the body to another depth than its last line's"
      | none => return .error "\\prevdepth set outside the box holding the body"
    | .unboxed id kids atD e =>
      match kids.findIdx? (· matches .body ..) with
      | some bi =>
        if seenBody then return .error "the body twice"
        let before := kids.extract 0 bi
        let opens := (before.filterMap fun x => match x with
          | .prevdepth d => some d
          | _ => none).back?.getD ignoreDepth
        if !Dimen.same opens atD then
          return .error "a body set back on another depth than the list it joins stood on"
        if !before.any (fun x => !(x matches .prevdepth ..)) then
          return .error "a body set back without the \\parskip its list spends"
        if before.any (fun x => !(x matches .prevdepth .. | .penalty .. | .whatsit)) then
          return .error "a box holding more before the body than penalties"
        for x in kids.extract (bi + 1) kids.size do
          match x with
          | .tail k _ => tails := tails.push k
          | _ => return .error "a box holding more after the body than the items it ends on"
        match kids[bi]? with
        | some (.body _ f p) => arm := { arm with bodyFont := f, bodyPaint := p }
        | _ => pure ()
        seenBody := true
        unboxed := some (id, e)
        owed := true
      | none =>
        if !seenBody then return .error "a box set back before the body"
        match tailsIn tails kids.toList with
        | some ts => tails := ts
        | none => return .error "a box set back after the body holding more than its items"
    | .moved .. | .sized .. =>
      match overlayRule n, unboxed, titleLine? with
      | some (shift, lift, some w, some h, some d, paint), some (bid, e), some tl =>
        if !flush then return .error "a box beside the body joined by the interline glue"
        if ruled then return .error "two rules beside the body"
        match arm.edges.findIdx? (fun x => x.span == .title && x.side == .left &&
            x.reach matches .lines ..) with
        | some idx =>
          match arm.edges[idx]? with
          | some te =>
            match te.reach with
            | .lines _ md =>
              let depth := metricDimen md arm.titleFont
              let stands := (lift.add? depth).map (Dimen.same · e) == some true
              let reaches := Dimen.same h { ext := [(tl, .dp, 1), (bid, .ht, 1)] }
              let bodyLen (l : SymLength) : Dimen := Dimen.norm { len := l, font := some none }
              let placed := Dimen.same shift.neg (bodyLen (te.width.add te.sep)) &&
                Dimen.same w (bodyLen te.width)
              if !d.zero? then return .error "a rule beside the body reaching below its baseline"
              else if !stands then
                return .error "a rule beside the body standing elsewhere than its title's rule's depth below its last line"
              else if !reaches then
                return .error "a rule beside the body reaching elsewhere than the title's rule"
              else if !placed || !Paint.sameAs paint te.paint then
                return .error "a rule beside the body at another place, width or paint than its title's"
              else
                arm := { arm with edges := arm.edges.modify idx fun x => { x with span := .whole } }
                ruled := true
                owed := true
                tailFirst := tailFirst || !tails.isEmpty
            | .box => return .error "a rule beside the body continuing a title's rule its box bounds"
          | none => return .error "a rule beside the body with no title's rule to continue"
        | none => return .error "a rule beside the body with no title's rule to continue"
      | _, _, _ => return .error "a box beside the body other than a rule standing on its last line"
    | .line id _ lineHsize kids =>
      if seenBody then return .error "a line after the body"
      if seenTitle then return .error "a second title line"
      titleLine? := some id
      match titleLine kids with
      | .ok (st, f, p) =>
        seenTitle := true
        arm := { arm with title := some { boxed := false, strut := st, parskip := true }
                          titleFont := f, titlePaint := p }
      | .error _ =>
        let boxIdx := kids.findIdx? (· matches .box ..)
        let some bi := boxIdx | return .error "a line holding neither the title nor a box"
        let some (.box id vertical hsize inner _) := kids[bi]? | return .error "a box line"
        if !vertical then return .error "a horizontal box holding the title"
        let before := (kids.extract 0 bi).toList
        let after := (kids.extract (bi + 1) kids.size).toList
        match boxContent inner with
        | .error e => return .error e
        | .ok (.titleBox st pk f p sf) =>
          match edgesOf .title id (some (f, pk, st, sf)) hsize lineHsize before after with
          | .error e => return .error e
          | .ok es =>
            seenTitle := true
            arm := { arm with title := some { boxed := true, strut := st, parskip := pk }
                              titleFont := f, titlePaint := p, edges := arm.edges ++ es }
        | .ok (.whole title between bodyParskip bf bp after') =>
          match edgesOf .whole id none hsize lineHsize before after with
          | .error e => return .error e
          | .ok es =>
            seenTitle := true
            seenBody := true
            for x in inner do
              if let .tail k _ := x then tails := tails.push k
            arm := { arm with between := arm.between ++ between, whole := some bodyParskip
                              edges := arm.edges ++ es, bodyFont := bf, bodyPaint := bp
                              after := arm.after ++ after' }
            match title with
            | some (st, pk, f, p) =>
              arm := { arm with title := some { boxed := false, strut := st, parskip := pk }
                                titleFont := f, titlePaint := p }
            | none => pure ()
    | .box .. => return .error "a box standing on its own in the block's list"
    | .lap .. => return .error "a lap standing on its own in the block's list"
    | .hrule => return .error "\\hrule"
    | _ => return .error "material outside a paragraph"
  if !seenBody then return .error "a template that never sets the body"
  if owed then return .error "a body set back without the depth below its last line after it"
  if tails != Array.range tailSize then
    return .error "the items the body ends on set back otherwise than in their order, every one"
  if tailFirst then return .error "a rule beside the body standing below the items the body ends on"
  return .ok arm

/-- How many items a template's run may take off the end of its list, each macro counted once. -/
private def removalsIn (defs : String → Option Macro) (bound : Nat) (path : List String)
    (memo : Std.HashMap String Nat) : List Tok → Nat × Std.HashMap String Nat
  | [] => (0, memo)
  | .ctrl n :: rest =>
    let (here, memo) :=
      if n == "unskip" || n == "unkern" || n == "unpenalty" then (1, memo)
      else match memo[n]? with
        | some c => (c, memo)
        | none =>
          match defs n with
          | some m =>
            if _h : path.length < bound ∧ !path.contains n then
              let (c, memo) := removalsIn defs bound (n :: path) memo (flatten m.body).toList
              (c, memo.insert n c)
            else (0, memo)
          | none => (0, memo)
    let (r, memo) := removalsIn defs bound path memo rest
    (here + r, memo)
  | _ :: rest => removalsIn defs bound path memo rest
termination_by l => (bound - path.length, l.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; have := _h.1; omega)
    | (apply Prod.Lex.right; omega)

/-- The most items a template may take off the list's end without calling
itself that the reader runs it over; one that may take more is named. -/
private def removalsHeld : Nat := 64

/-- The body list ends the reader runs the pair over: up to two glue, kern and penalty items,
and one of each kind past what the run may take off. -/
private def tailVariants (removals : Nat) : List (Array TailKind) :=
  let one := [TailKind.glue, .kern, .penalty]
  let long := removals + 1
  [#[]] ++ one.map (#[·]) ++ (one.flatMap fun a => one.map fun b => #[a, b]) ++
    one.map (fun k => Array.replicate long k) ++
    [(Array.range long).map fun i => if i % 2 == 0 then TailKind.penalty else .glue]

/-- A block template pair read: both arms of the title test, over every body end, held to one
shape. -/
public def read (beginRaws endRaws : Array Raw) (defs : String → Option Macro := fun _ => none)
    (bound : Nat := 0) (lengths : String → Option (Option Dimen) := fun _ => none)
    (flags : String → Option Bool := fun _ => none) :
    Except (Array String) Read :=
  let opening := flatten beginRaws
  let closing := flatten endRaws
  let flat := #[Tok.par] ++ opening ++ #[Tok.body, Tok.par] ++ closing
  let toks := expandList defs bound flat.toList #[]
  let removals := (removalsIn defs bound [] {} toks.toList).1
  if removals > removalsHeld then
    .error #[s!"a template that may take more than {removalsHeld} items off the body's end"] else
  let runs := (tailVariants removals).map fun tail =>
    (tail, run defs toks true tail lengths flags, run defs toks false tail lengths flags)
  let unread := runs.foldl (fun acc (_, t, u) =>
    (t.unread ++ u.unread).foldl (fun acc w => if acc.contains w then acc else acc.push w) acc) #[]
  if !unread.isEmpty then .error unread else
  let lowered := runs.map fun (tail, t, u) =>
    (lowerArm t.lst.nodes tail.size, lowerArm u.lst.nodes tail.size)
  let same (a b : Except String Arm) : Bool := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false
  match lowered with
  | [] => .error #["a template the reader runs over no body"]
  | (t0, u0) :: rest =>
  if rest.any (fun (t, u) => !same t t0 || !same u u0) then
    match (lowered.filterMap fun (t, u) => match t, u with
      | .error e, _ | _, .error e => some e
      | _, _ => none).head? with
    | some e => .error #[e]
    | none => .error #["a template that sets the body otherwise as the items its list ends on differ"]
  else
  match t0, u0 with
  | .error e, _ | _, .error e => .error #[e]
  | .ok t, .ok u =>
    match t.title with
    | none => .error #["a template that never sets the title"]
    | some title =>
      -- The untitled arm draws no rule reaching by the title's lines.
      let lineRule (e : EdgeRead) : Bool := e.span == .whole && e.reach matches .lines ..
      let titleEdges := t.edges.filter fun e => e.span == .title || lineRule e
      let wholeEdges (a : Arm) := a.edges.filter fun e => e.span == .whole && !lineRule e
      let untitledBox := u.title.isSome
      if t.after != u.after then .error #["skips below the body the untitled arm sets otherwise"]
      else if t.whole.isSome != u.whole.isSome || wholeEdges t != wholeEdges u then
        .error #["a box around the body the untitled arm sets otherwise"]
      else if untitledBox && (u.title != t.title || u.edges != t.edges || u.between != t.between ||
          u.before != t.before) then
        .error #["an empty title box the untitled arm sets otherwise"]
      else if titleEdges.any (fun _ => !title.boxed) then
        .error #["a rule beside a title with no box of its own"]
      else
        let spansides := t.edges.map fun e => (e.span, e.side)
        if spansides.toList.eraseDups.length != spansides.size then
          .error #["two rules on one side of one box"]
        else if t.edges.any fun e => lineRule e && !e.hang then
          .error #["a rule reaching by the block's lines inside its line"]
        else .ok
          { before := t.before, title := title
            bare := if untitledBox then none else some { before := u.before, between := u.between }
            between := t.between, after := t.after
            whole := if t.title.isSome && !untitledBox then u.whole else t.whole
            edges := t.edges, titleFont := t.titleFont, titlePaint := t.titlePaint
            bodyFont := t.bodyFont, bodyPaint := t.bodyPaint }

end LeanTex.Core.BlockTemplate
