module

public import LeanTex.Core.Parse
public import LeanTex.Core.Ir

/-!
The reader of beamer's block templates (`block begin` and `block end`, and
their alerted and example pairs): an interpretation of what the pair writes
in TeX's box-and-rule vocabulary, run as TeX runs it, into the record both
backends set a block by (`Ir.BlockShape`).

beamer's block environment is `\par\usebeamertemplate{block begin}` before
the body and `\par\usebeamertemplate{block end}` after it
(beamerbaselocalstructure.sty), so the reader runs the two templates around a
marker for the body, once with a title and once without — the two arms of
beamer's own `\ifx\insertblocktitle\@empty` test — and keeps the lists TeX
would build: vertical skips, paragraphs and their lines, boxes built with
`\setbox` and placed with `\box` or `\copy`, `\llap`/`\rlap` and their
rules, `\strut`, the colour and font selections. The semantics are TeX's
own, where they decide what the page shows: a `\usebeamercolor[fg]` puts a
colour change on the list it stands in, so a paragraph after it in a fresh
box spends `\parskip` (tex.web §1091, where a paragraph starts); `\box` empties its
register, so a rule after it reading `\ht` of the box has no height; a box
opened by `\vbox\bgroup` in `block begin` closes at the `\egroup` in `block
end`, holding the body. The reader then lowers the lists onto the record:
skips before the title, the title's box, the box holding title and body,
skips after the body, and the rules beside those boxes. A construct outside
the vocabulary, or lists of a shape the record cannot hold, is named — the
whole template is then not read, and the default inner theme's pair stands.
-/

namespace LeanTex.Core.BlockTemplate

open LeanTex.Core
open LeanTex.Core.Dim
open LeanTex.Core.Parse (Raw)

/-! ## Tokens

A template runs as a flat token list, as TeX reads one: a brace group is its
two braces around its content, `\bgroup` and `\egroup` are the braces they
stand for, so a box opened in `block begin` can close in `block end`. -/

/-- One token of a template's flat list. `body` is the block's body, where
the environment runs it. -/
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

mutual

-- conserves: none — a token reading of template code, not a walk over document content.
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
  | .group body _ => (flatList (acc.push .bg) body.toList).push .eg
  | .math _ _ _ => acc.push (.ctrl "$…$")
  | .env n _ _ => acc.push (.ctrl ("begin{" ++ n ++ "}"))
  | .verb _ _ _ => acc.push (.ctrl "verb")

end

/-- The template code as one flat list. -/
public def flatten (raws : Array Raw) : Array Tok := flatList #[] raws.toList

/-- A document macro a template may call: the order its definition was
made in (`serial`), its arity and its replacement text, `#k` standing for
its arguments. -/
public structure Macro where
  serial : Nat
  arity : Nat
  body : Array Raw
  deriving Inhabited

/-- The braced arguments of a call from the head of `l`, and the tokens
they take, spaces between them included. -/
private def callArgs (l : List Tok) (arity : Nat) : Option (Array (Array Tok) × Nat) := Id.run do
  let toks := l.toArray
  let mut args : Array (Array Tok) := #[]
  let mut k := 0
  for _ in [0:arity] do
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

/-- **The document's macros, expanded where the template calls them**, as TeX
expands them when the template runs: each call's arguments bound into its
replacement text, which is expanded in turn. A text expands only the
macros defined before it (`Macro.serial` below the text's own), the order
definitions were made in, so expansion ends. -/
public def expandList (defs : String → Option Macro) (bound : Nat) :
    List Tok → Array Tok → Array Tok
  | [], acc => acc
  | .ctrl n :: rest, acc =>
    match defs n with
    | some m =>
      if _h : m.serial < bound then
        match callArgs rest m.arity with
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

/-! ## What the lists hold -/

/-- Which extent of a box a dimension reads. -/
public inductive Ext where
  | ht
  | dp
  | wd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A dimension as a template writes it: a linear form over a length (its
`em` and `ex`), the measure `\linewidth` in thousandths, box extents by the
box's identity, and, in thousandths, `\parskip` (`parskip`), the
`\baselineskip` in force (`lead`) and the cap height `\fontcharht\font`H`
(`cap`). `font` is the font element in force where the terms that read a
font were read, `none` while there are none: TeX fixes a register's value
where it is assigned. -/
public structure Dimen where
  len : Length := {}
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

/-- The dimension times `num / den`, each term rounded as e-TeX rounds; a box
extent keeps a whole coefficient, or the dimension is not one this reading
holds. -/
private def Dimen.scale? (d : Dimen) (num : Int) (den : Nat) : Option Dimen :=
  if den == 0 || d.ext.any (fun (_, _, k) => (k * num) % (den : Int) != 0) then none
  else
    let f (v : Int) : Int := roundDiv (v * num) den
    some (Dimen.norm
      { len := { sp := f d.len.sp, em := f d.len.em, ex := f d.len.ex }, line := f d.line
        ext := mergeExt (d.ext.map fun (b, e, k) => (b, e, k * num / (den : Int)))
        parskip := f d.parskip, lead := f d.lead, cap := f d.cap, font := d.font })

/-- The length alone, when the dimension is one. -/
public def Dimen.length? (d : Dimen) : Option Length :=
  if d.line == 0 && d.ext.isEmpty && d.parskip == 0 && d.lead == 0 && d.cap == 0
  then some d.len else none

/-- What a colour command selects: a channel as the beamer colour elements in
force bind it, the latest first — `\usebeamercolor[fg]{block title}`, or
`\color{bg}` after `\usebeamercolor`s, read the channel of the latest element
that sets it (beamerbasecolor.sty) — or a colour by name (`\color{name}`). -/
public inductive Paint where
  | beamer (chain : List String) (channel : String)
  | named (name : String)
  deriving Repr, BEq, Inhabited

/-- One node of a list a template builds. `line` is a paragraph's one line
in a vertical list, with whether `\parskip` stands before it; `box` a box
built by `\vbox`/`\hbox` (`vertical`), its measure and its list; `lap` an
`\llap` (`right` false) or `\rlap`. A rule's dimensions are `none` where it
runs to its box. The font element in force rides with every node whose
lengths or ink read it. -/
public inductive Node where
  | vskip (s : Ir.BlockSkip)
  | whatsit
  | line (parskip : Bool) (hsize : Dimen) (kids : Array Node)
  | box (id : Nat) (vertical : Bool) (hsize : Dimen) (kids : Array Node)
  | lap (right : Bool) (kids : Array Node)
  | rule (w h d : Option Dimen) (paint : Option Paint) (font : Option String)
  | hskip (d : Dimen) (font : Option String)
  | strut (font : Option String)
  | title (font : Option String) (paint : Option Paint)
  | body (font : Option String) (paint : Option Paint)
  | hrule
  deriving Repr, BEq, Inhabited

/-! ## The interpreter -/

/-- What a group restores: the font element, the colour, `\hsize`, the beamer
colour elements in force, the latest first, through which the colour names
`fg` and `bg` read their channels — `\usebeamercolor` rebinds with
`\colorlet` each channel its element sets and keeps the other
(beamerbasecolor.sty) — and the length registers the group assigned. -/
private structure Scope where
  font : Option String := none
  paint : Option Paint := none
  hsize : Dimen := { line := 1000 }
  channels : List String := []
  dimens : List (String × Dimen) := []
  deriving Inhabited

/-- A list under construction: vertical or horizontal, its nodes, and the
paragraph open in it. -/
private structure Lst where
  vertical : Bool := true
  nodes : Array Node := #[]
  para : Option (Array Node) := none
  paraParskip : Bool := false
  /-- An enclosing box holds this list: its paragraphs spend `\parskip`
  only after a node. The block's own list, the frame's, never opens
  empty. -/
  inner : Bool := false
  deriving Inhabited

private inductive FrameKind where
  | group (simple : Bool)
  | box (target : Option String) (id : Nat) (vertical : Bool)
  | lap (right : Bool)
  deriving Inhabited

private structure Frame where
  kind : FrameKind
  saved : Scope
  outer : Lst
  deriving Inhabited

/-- A conditional the reader decided, waiting for its `\else` or `\fi`. -/
private inductive Pending where
  | thenArm
  | elseArm
  deriving BEq, Inhabited

/-- A template token list as TeX's scanner reads it, a character at a time:
each character of a word, a control word, a space, and `stop` for what no
dimension reads (a brace, a paragraph end, the body). `owner` is the token
each character stands in and whether it opens it; `start` where each token's
characters begin. -/
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
  nextId : Nat := 0
  conds : List Pending := []
  unread : Array String := #[]
  /-- Length registers assigned with `\global`, by name. -/
  dimens : List (String × Dimen) := []
  /-- Registers `\newdimen` declares in the template itself. -/
  declared : List String := []
  /-- The document's length registers: `none` for a name that is none,
  `some none` for one whose value where the block stands this reading does
  not hold. -/
  lengths : String → Option (Option Dimen) := fun _ => none
  /-- The template's characters, as dimensions are read. -/
  chars : Chars := {}
  deriving Inhabited

private def St.miss (s : St) (what : String) : St :=
  if s.unread.contains what then s else { s with unread := s.unread.push what }

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

private def Node.id? : Node → Option Nat
  | .box id _ _ _ => some id
  | _ => none

/-- A length register's value where the template stands: its group's own
value, its global one, the value it was declared with. `none` for a name no
register has; `some none` for a register whose value this reading does not
hold. -/
private def St.dimen? (s : St) (n : String) : Option (Option Dimen) :=
  match s.scope.dimens.lookup n with
  | some d => some (some d)
  | none =>
    match s.dimens.lookup n with
    | some d => some (some d)
    | none => if s.declared.contains n then some (some {}) else s.lengths n

/-- Assign a length register, as TeX does: in the group, or, `\global`, at
every level — a global assignment outlives every group's own value. -/
private def St.assign (s : St) (n : String) (v : Dimen) (global : Bool) : St :=
  if global then
    let drop (sc : Scope) : Scope := { sc with dimens := sc.dimens.filter (·.1 != n) }
    { s with dimens := (n, v) :: s.dimens.filter (·.1 != n), scope := drop s.scope
             frames := s.frames.map fun fr => { fr with saved := drop fr.saved } }
  else { s with scope := { s.scope with dimens := (n, v) :: s.scope.dimens.filter (·.1 != n) } }

/-! ## Reading dimensions

TeX reads a dimension a character at a time (TeXbook ch. 24), where the
template's token list keeps a word whole: a dimension is read over the
characters (`Chars`), and must end where a token does. -/

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

/-- An internal dimension at `k`: a measure register, `\z@`, `\p@`, a box's
extent read now as TeX reads it, a length register, `\parskip`, and
`\baselineskip` and `\fontcharht\font`H` in the font in force — and the
index after it. -/
private def St.internalAt (s : St) (c : Chars) (k : Nat) : Option (Dimen × Nat) :=
  let font := s.scope.font
  match c.get k with
  | .cs n =>
    if measureRegs.contains n then some ({ line := 1000 }, k + 1)
    else if n == "z@" then some ({}, k + 1)
    else if n == "p@" then some ({ len := { sp := Dim.spPerPt } }, k + 1)
    else if n == "parskip" then some ({ parskip := 1000 }, k + 1)
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
  let j := (c.keyword j "true").getD j
  for u in unitWords do
    if let some j' := c.keyword j u then
      match Decl.parseLength (decimalSrc m scale ++ u) with
      | some l =>
        let fonted := l.em != 0 || l.ex != 0
        return some ({ len := l, font := if fonted then some font else none }, c.optSp j')
      | none => return none
  return none

/-- One level of `\dimexpr`'s evaluation: the sum so far, the sign of the
term being read and the term, whether `)` or `\relax` closes the level, and
the sign its value takes as a factor of the level below. -/
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

/-- `\dimexpr`'s expression from `k`, after the `\dimexpr` (e-TeX manual
§3.5): terms joined by `+` and `-`, a term a factor times or over integers,
and a factor a dimension, a parenthesized expression or a nested
`\dimexpr`. It ends at `\relax`, which it takes, or before anything that
continues no expression. The levels are a stack, so the read is one pass
over the characters. -/
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
      | .ch '(' => stack := { paren := true, outer := sign } :: stack; j := j1 + 1
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
        -- Anything else ends the outermost expression, and stays unread.
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

/-- Close the open paragraph of the current list, as `\par` does. -/
private def St.closePara (s : St) : St :=
  match s.lst.para with
  | some kids =>
    { s with lst := { s.lst with
        nodes := s.lst.nodes.push (.line s.lst.paraParskip s.scope.hsize kids), para := none } }
  | none => s

/-- Horizontal material: in a vertical list it opens a paragraph (beamer's
`\parindent` is zero, so no indent box), which spends `\parskip` unless it
opens an empty box's list. -/
private def St.pushH (s : St) (n : Node) : St :=
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
  if s.lst.vertical then
    let s := s.closePara
    { s with lst := { s.lst with nodes := s.lst.nodes.push n } }
  else s.miss (what ++ " in a horizontal box")

/-- A box (or lap) finished in the list it stands in: in vertical mode it
joins the list itself, in horizontal mode the line. -/
private def St.place (s : St) (n : Node) : St :=
  if s.lst.vertical && s.lst.para.isNone then
    { s with lst := { s.lst with nodes := s.lst.nodes.push n } }
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
  | .box _ _ vertical =>
    { s with frames := fr :: s.frames, lst := { vertical := vertical, inner := true } }
  | .lap _ => { s with frames := fr :: s.frames, lst := { vertical := false, inner := true } }

/-- Close the innermost frame at its closing brace. -/
private def St.close (s : St) (simple : Bool) : St :=
  match s.frames with
  | [] => s.miss "a closing brace with no group open"
  | fr :: rest =>
    match fr.kind with
    | .group simple' =>
      if simple != simple' then s.miss "\\begingroup and a brace closing each other"
      else { s with frames := rest, scope := fr.saved }
    | .box target id vertical =>
      if simple then s.miss "\\endgroup closing a box" else
      let s := s.closePara
      let node := Node.box id vertical s.scope.hsize s.lst.nodes
      let s := { s with frames := rest, scope := fr.saved, lst := fr.outer }
      match target with
      | some r => { s with regs := (r, some node) :: s.regs }
      | none => s.place node
    | .lap right =>
      if simple then s.miss "\\endgroup closing a lap" else
      let node := Node.lap right s.lst.nodes
      let s := { s with frames := rest, scope := fr.saved, lst := fr.outer }
      s.place node

/-- TeX's conditional heads: an `\if…` among them opens a conditional the
skip counts; any other `\if…` word the reader does not read. -/
private def condHeads : List String :=
  ["if", "ifcat", "ifnum", "ifdim", "ifodd", "ifvmode", "ifhmode", "ifmmode", "ifinner",
   "ifvoid", "ifhbox", "ifvbox", "ifx", "ifeof", "iftrue", "iffalse", "ifcase",
   "ifdefined", "ifcsname", "iffontchar"]

/-- From `i`, past the matching `\else` (`true`) or `\fi`: the index after
it, and which was met. Nested conditionals are skipped whole. -/
private def skipArm (toks : Array Tok) (i : Nat) : Option (Nat × Bool) := Id.run do
  let mut depth := 0
  let mut k := i
  for _ in [i:toks.size] do
    match toks[k]? with
    | some (.ctrl n) =>
      if condHeads.contains n then depth := depth + 1
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
  ["nobreak", "relax", "ignorespaces", "noframebreak", "allowbreak", "unskip", "@empty",
   "empty", "protect"]

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

/-- The interpreter's main loop over the flat list. `titled` is the arm of
`\ifx\insertblocktitle\@empty` this run takes. -/
private def run (toks : Array Tok) (titled : Bool) (lengths : String → Option (Option Dimen)) :
    St := Id.run do
  let mut s : St := { lengths := lengths, chars := Chars.of toks }
  let mut i := 0
  for _ in [0:toks.size] do
    if i ≥ toks.size then break
    let some t := toks[i]? | break
    match t with
    | .space | .sym '%' => i := i + 1
    | .par => s := s.closePara; i := i + 1
    | .body =>
      s := s.pushV (.body s.scope.font s.scope.paint) "the body"
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
          s := s.miss "a vertical \\kern"; i := i + 1
        else
          let (dim, k) : Option Dimen × Nat :=
            if n == "hspace" then
              match readArg toks (i + 1) with
              | some (arg, k) => ((s.readDimen (Chars.of arg) 0).map (·.1), k)
              | none => (none, i + 1)
            else match s.readGlue s.chars (i + 1) with
              | some (.glue g, k) =>
                -- Its ems are the font's in force here, where it was read.
                if g.stretch == {} && g.shrink == {} then
                  (some (Dimen.norm { len := g.width, font := some s.scope.font }), k)
                else (none, k)
              | _ => (none, i + 1)
          match dim with
          | some d => s := s.pushH (.hskip d s.scope.font)
          | none => s := s.miss s!"\\{n} with stretch or an unreadable length"
          i := k
      | "hsize" =>
        match s.readDimen s.chars (i + 1) with
        | some (d, k) => s := { s with scope := { s.scope with hsize := d } }; i := k
        | none => s := s.miss "\\hsize set to a length it cannot read"; i := i + 1
      | "advance" | "global" =>
        let global := n == "global"
        let j := skipSp toks (i + 1)
        let (j, advance) := if global then
            if toks[j]? == some (.ctrl "advance") then (skipSp toks (j + 1), true) else (j, false)
          else (j, true)
        match toks[j]? with
        | some (.ctrl "hsize") =>
          if global then s := s.miss "\\global\\hsize"; i := j + 1
          else
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
            let (s', k) := s.assignAt r (j + 1) global advance
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
          i := k
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
          i := k
        | _, _ => s := s.miss "\\color"; i := i + 1
      | "vrule" =>
        match s.readRuleSpec s.chars (i + 1) with
        | some ((w, h, d), k) =>
          let w := w.orElse fun _ => some { len := { sp := Dim.spPerPt * 4 / 10 } }
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
        let j := skipSp toks (i + 1)
        if n == "vtop" then s := s.miss "\\vtop"; i := i + 1
        else if toks[j]? == some .bg then
          s := s.open (.box none s.nextId (n == "vbox"))
          s := { s with nextId := s.nextId + 1 }
          i := j + 1
        else s := s.miss s!"\\{n} with a size spec"; i := i + 1
      | "setbox" =>
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl r) =>
          let j := skipSp toks (j + 1)
          let j := if toks[j]? == some (.word "=") || toks[j]? == some (.sym '=') then
            skipSp toks (j + 1) else j
          match toks[j]? with
          | some (.ctrl b) =>
            let j' := skipSp toks (j + 1)
            if (b == "vbox" || b == "hbox") && toks[j']? == some .bg then
              s := s.open (.box (some r) s.nextId (b == "vbox"))
              s := { s with nextId := s.nextId + 1 }
              i := j' + 1
            else if b == "box" || b == "copy" then
              match toks[j']? with
              | some (.ctrl src) =>
                let v := s.boxOf src
                let regs := if b == "box" then (src, none) :: s.regs else s.regs
                s := { s with regs := (r, v) :: regs }
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
            let s1 := if n == "box" then { s with regs := (r, none) :: s.regs } else s
            s := s1.place node
          | none => pure ()
          i := k
        | none => s := s.miss s!"\\{n}"; i := k
      | "newbox" =>
        let j := skipSp toks (i + 1)
        match toks[j]? with
        | some (.ctrl r) => s := { s with regs := (r, none) :: s.regs }; i := j + 1
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
            match skipArm toks (k + 1) with
            | some (k', true) => s := { s with conds := .elseArm :: s.conds }; i := k'
            | some (k', false) => i := k'
            | none => s := s.miss "\\ifx without \\fi"; i := toks.size
      | "else" =>
        match s.conds with
        | .thenArm :: rest =>
          match skipArm toks (i + 1) with
          | some (k', false) => s := { s with conds := rest }; i := k'
          | _ => s := s.miss "\\else without its \\fi"; i := toks.size
        | _ => s := s.miss "\\else"; i := i + 1
      | "fi" =>
        match s.conds with
        | _ :: rest => s := { s with conds := rest }; i := i + 1
        | [] => s := s.miss "\\fi"; i := i + 1
      | _ =>
        if (s.dimen? n).isSome then
          let (s', k) := s.assignAt n (i + 1) false false
          s := s'
          i := k
        else
          s := s.miss s!"\\{n}"
          i := i + 1
  s := s.closePara
  unless s.frames.isEmpty do s := s.miss "a group the template never closes"
  unless s.conds.isEmpty do s := s.miss "a conditional the template never closes"
  return s

/-! ## Lowering the lists onto the record -/

/-- A template rule as read, before its colour is a palette entry. -/
public structure EdgeRead where
  span : Ir.BlockSpan
  side : Ir.FlushSide
  width : Length
  sep : Length
  hang : Bool
  paint : Option Paint
  reach : Ir.BlockReach := .box
  deriving Repr, BEq, Inhabited

/-- What a template pair sets, read: `Ir.BlockShape` but for its rules'
colours, which a palette resolves, and the font elements and colours the
title and body are set in, which the caller holds to the kind's own. -/
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
  deriving Repr, Inhabited

/-- A title paragraph's line: the title between optional struts, colour
changes beside them. Returns whether it is strutted at both ends. -/
private def titleLine (kids : Array Node) : Except String (Bool × Option String × Option Paint) :=
  let core := kids.filter (· != .whatsit)
  match core.toList with
  | [.title f p] => .ok (false, f, p)
  | [.strut _, .title f p, .strut _] => .ok (true, f, p)
  | _ => .error "a title line holding more than the title and its struts"

/-- What a box's vertical list holds: an optional title paragraph, then
skips and the body (the box holding title and body), or the title alone
(the title's box). -/
private inductive Content where
  | titleBox (strut parskip : Bool) (font : Option String) (paint : Option Paint)
  | whole (title : Option (Bool × Bool × Option String × Option Paint))
      (between : Array Ir.BlockSkip) (bodyParskip : Bool) (font : Option String)
      (paint : Option Paint) (after : Array Ir.BlockSkip)

private def boxContent (kids : Array Node) : Except String Content := Id.run do
  let items := kids.filter (· != .whatsit)
  -- The body's paragraph spends `\parskip` inside the box when any node
  -- stands before it there.
  let bodyIdx := kids.findIdx? (· matches .body ..)
  match items.toList with
  | [.line pk _ line] =>
    match titleLine line with
    | .ok (st, f, p) => return .ok (.titleBox st pk f p)
    | .error e => return .error e
  | _ =>
    let mut title : Option (Bool × Bool × Option String × Option Paint) := none
    let mut between : Array Ir.BlockSkip := #[]
    let mut after : Array Ir.BlockSkip := #[]
    let mut body : Option (Option String × Option Paint) := none
    for n in items do
      match n with
      | .line pk _ line =>
        if title.isSome || body.isSome then return .error "a line beside the body in its box"
        match titleLine line with
        | .ok (st, f, p) => title := some (st, pk, f, p)
        | .error e => return .error e
      | .vskip g => if body.isSome then after := after.push g else between := between.push g
      | .body f p =>
        if body.isSome then return .error "the body twice" else body := some (f, p)
      | _ => return .error "a box holding more than the title, skips and the body"
    match body with
    | none => return .error "a box holding neither the title alone nor the body"
    | some (f, p) =>
      let bodyParskip := match bodyIdx with
        | some k => k > 0
        | none => false
      return .ok (.whole title between bodyParskip f p after)

/-- A rule's reach beside its box (`Ir.BlockReach`): its box's own extents;
nothing at all — a rule reading an emptied register has no height and draws
nothing, as in TeX; or, beside the title's box, whose title is set in
`title`'s font and whose list opens on a `\parskip` where `title`'s flag
says so, the box's lines in that font: its height and depth less that
`\parskip`, one `\baselineskip` per strutted line, and a metric more above
the box's baseline, and a metric below it. -/
private def reachOf (id : Nat) (title : Option (Option String × Bool)) (h d : Option Dimen) :
    Except String (Option Ir.BlockReach) :=
  match h, d with
  | some h, some d =>
    if h == { ext := [(id, .ht, 1)] } && d == { ext := [(id, .dp, 1)] } then .ok (some .box)
    else if h == {} && d == {} then .ok none
    else match title with
      | none => .error "a rule whose height and depth are not its box's"
      | some (font, parskip) =>
        let metric (x : Dimen) : Option Ir.BlockMetric :=
          if x.line == 0 && x.len.em == 0 && x.len.ex == 0 && (!x.fonted || x.font == some font)
          then some { lead := x.lead, cap := x.cap, sp := x.len.sp } else none
        let lines := h.ext.length == 2 && h.ext.contains (id, .ht, 1) && h.ext.contains (id, .dp, 1)
        match metric h, metric d with
        | some mh, some md =>
          if !lines || !d.ext.isEmpty then
            .error "a rule beside the title's box reading other than its height and depth"
          else if h.parskip != (if parskip then -1000 else 0) || d.parskip != 0 then
            .error "a rule beside the title's box reading another skip than the one its list opens on"
          else .ok (some (.lines { mh with lead := mh.lead + 1000 } md))
        | _, _ => .error "a rule beside the title's box measured in another font than its title's"
  | _, _ => .error "a rule running to its line"

/-- The rules beside one box in its line: `\llap{…\vrule…\hskip S}` before
it hangs left, `\vrule\hskip S` before it stands inside the line, and their
mirrors after it. A rule reaches as `reachOf` reads it. -/
private def edgesOf (span : Ir.BlockSpan) (id : Nat) (title : Option (Option String × Bool))
    (hsize : Dimen) (lineHsize : Dimen) (before after : List Node) :
    Except String (Array EdgeRead) := Id.run do
  let lenOf (d : Dimen) : Except String Length :=
    match d.length? with
    | some l =>
      if (l.em == 0 && l.ex == 0) || d.font == some none then .ok l
      else .error "a rule measured in a font of its own"
    | none => .error "a rule or space measured against a box"
  -- One side's nodes, read outward from the box: a hanging lap, or a rule
  -- and the space between it and the box.
  let side (onRight : Bool) (nodes : List Node) : Except String (Option EdgeRead × Length) := do
    let sideName : Ir.FlushSide := if onRight then .right else .left
    let ns := nodes.filter (· != .whatsit)
    match ns with
    | [] => return (none, {})
    | [.lap r kids] =>
      if r != onRight then throw "a lap reaching over its box"
      let inner := (kids.filter (· != .whatsit)).toList
      -- From the box outward: the space, then the rule.
      let outward := if onRight then inner else inner.reverse
      match outward with
      | [.rule (some w) h d p _] =>
        let some reach ← reachOf id title h d | return (none, {})
        return (some { span, side := sideName, width := ← lenOf w, sep := {}, hang := true,
                        paint := p, reach }, {})
      | [.hskip g _, .rule (some w) h d p _] =>
        let some reach ← reachOf id title h d | return (none, {})
        return (some { span, side := sideName, width := ← lenOf w, sep := ← lenOf g,
                        hang := true, paint := p, reach }, {})
      | _ => throw "a lap holding more than a rule and its space"
    | _ =>
      let outward := if onRight then ns else ns.reverse
      match outward with
      | [.hskip g _, .rule (some w) h d p _] =>
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

/-- One arm's top-level list, lowered: skips, the title's line or a box line,
skips, the body or the box holding it, skips. -/
private def lowerArm (nodes : Array Node) : Except String Arm := Id.run do
  let mut arm : Arm := {}
  let mut seenTitle := false
  let mut seenBody := false
  for n in nodes do
    match n with
    | .whatsit => pure ()
    | .vskip g =>
      if seenBody then arm := { arm with after := arm.after.push g }
      else if seenTitle then arm := { arm with between := arm.between.push g }
      else arm := { arm with before := arm.before.push g }
    | .body f p =>
      if seenBody then return .error "the body twice"
      seenBody := true
      arm := { arm with bodyFont := f, bodyPaint := p }
    | .line _ lineHsize kids =>
      if seenBody then return .error "a line after the body"
      if seenTitle then return .error "a second title line"
      -- A bare title paragraph, or a line holding one box and its rules.
      match titleLine kids with
      | .ok (st, f, p) =>
        seenTitle := true
        arm := { arm with title := some { boxed := false, strut := st, parskip := true }
                          titleFont := f, titlePaint := p }
      | .error _ =>
        let boxIdx := kids.findIdx? (· matches .box ..)
        let some bi := boxIdx | return .error "a line holding neither the title nor a box"
        let some (.box id vertical hsize inner) := kids[bi]? | return .error "a box line"
        if !vertical then return .error "a horizontal box holding the title"
        let before := (kids.extract 0 bi).toList
        let after := (kids.extract (bi + 1) kids.size).toList
        match boxContent inner with
        | .error e => return .error e
        | .ok (.titleBox st pk f p) =>
          match edgesOf .title id (some (f, pk)) hsize lineHsize before after with
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
  return .ok arm

/-- **A block template pair, read**: both arms of the title test run and
lowered, and held to one shape — the untitled arm differs from the titled
one only in leaving the title out, with the skips of its own that arm stands
(`Ir.BlockBare`), or in keeping its box empty. `lengths` are the document's
length registers (`St.lengths`). -/
public def read (beginRaws endRaws : Array Raw) (defs : String → Option Macro := fun _ => none)
    (bound : Nat := 0) (lengths : String → Option (Option Dimen) := fun _ => none) :
    Except (Array String) Read :=
  let opening := flatten beginRaws
  let closing := flatten endRaws
  let flat := #[Tok.par] ++ opening ++ #[Tok.body, Tok.par] ++ closing
  let toks := expandList defs bound flat.toList #[]
  let titled := run toks true lengths
  let untitled := run toks false lengths
  let unread := titled.unread ++ untitled.unread.filter (!titled.unread.contains ·)
  if !unread.isEmpty then .error unread else
  match lowerArm titled.lst.nodes, lowerArm untitled.lst.nodes with
  | .error e, _ | _, .error e => .error #[e]
  | .ok t, .ok u =>
    match t.title with
    | none => .error #["a template that never sets the title"]
    | some title =>
      let titleEdges := t.edges.filter (·.span == .title)
      let wholeEdges (a : Arm) := a.edges.filter (·.span == .whole)
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
        else .ok
          { before := t.before, title := title
            bare := if untitledBox then none else some { before := u.before, between := u.between }
            between := t.between, after := t.after
            whole := if t.title.isSome && !untitledBox then u.whole else t.whole
            edges := t.edges, titleFont := t.titleFont, titlePaint := t.titlePaint
            bodyFont := t.bodyFont, bodyPaint := t.bodyPaint }

/-! ## The native spelling -/

/-- A thousandths value as its shortest decimal: 2500 is `2.5`. -/
private def milliText (m : Int) : String :=
  let ip := m.natAbs / 1000
  let fr := m.natAbs % 1000
  let sign := if m < 0 then "-" else ""
  if fr == 0 then s!"{sign}{ip}"
  else
    let frs := toString fr
    let frs := ("".pushn '0' (3 - frs.length)) ++ frs
    s!"{sign}{ip}.{(frs.dropEndWhile (· == '0')).toString}"

/-- Terms joined as the native declaration joins them: `a + b`, `a - b`. -/
private def joinTerms : List String → String
  | [] => "0pt"
  | p :: ps => ps.foldl (fun acc q =>
      if q.startsWith "-" then acc ++ " - " ++ (q.drop 1).toString else acc ++ " + " ++ q) p

/-- A length as the native declaration writes it: points where they are
exact to the thousandth, else scaled points, and the font-relative parts. -/
private def lengthSrc (l : Length) : String :=
  let part (v : Int) (unit : String) : Option String :=
    if v == 0 then none else some (milliText v ++ unit)
  let pts := if l.sp == 0 then none
    else if (l.sp * 1000) % Dim.spPerPt == 0 then some (milliText (l.sp * 1000 / Dim.spPerPt) ++ "pt")
    else some (toString l.sp ++ "sp")
  joinTerms ([pts, part l.em "em", part l.ex "ex"].filterMap id)

/-- A title metric as the native declaration writes it: its leading in `lh`
and its cap height in `cap`, CSS's names for the two, and a fixed length. -/
private def metricSrc (m : Ir.BlockMetric) : String :=
  let part (v : Int) (unit : String) : Option String :=
    if v == 0 then none else some (milliText v ++ unit)
  joinTerms ([part m.lead "lh", part m.cap "cap",
    if m.sp == 0 then none else some (lengthSrc (.ofSp m.sp))].filterMap id)

private def glueSrc (g : SymGlue) : String :=
  let w := lengthSrc g.width
  let st := if g.stretch == {} then "" else s!" plus {lengthSrc g.stretch}"
  let sh := if g.shrink == {} then "" else s!" minus {lengthSrc g.shrink}"
  w ++ st ++ sh

private def skipsSrc (skips : Array Ir.BlockSkip) : String :=
  String.intercalate " + " (skips.toList.map fun
    | .register n => n
    | .glue g => glueSrc g)

/-- The native `shape = {...}` value for a read template, its rules'
colours the palette entries `color` names, one per rule in order. -/
public def native (r : Read) (colors : Array String) : String :=
  let flags := (if r.title.boxed then ["box"] else []) ++
    (if r.title.strut then ["strut"] else []) ++ (if r.title.parskip then ["parskip"] else [])
  let title := if flags.isEmpty then "plain" else String.intercalate " " flags
  let whole := match r.whole with
    | some true => ", whole = parskip"
    | some false => ", whole = plain"
    | none => ""
  let edges := r.edges.toList.zipIdx.map fun (e, i) =>
    let span := match e.span with | .title => "title" | .whole => "whole"
    let side := match e.side with | .left => "left" | .right => "right"
    let reach := match e.reach with
      | .lines above below => s!", above = {metricSrc above}, below = {metricSrc below}"
      | .box => ""
    s!", edge = \{ span = {span}, side = {side}, width = {lengthSrc e.width}, \
sep = {lengthSrc e.sep}, hang = {e.hang}, color = {colors.getD i "fg"}{reach} }"
  let skips (key : String) (sk : Array Ir.BlockSkip) : String :=
    if sk.isEmpty then "" else s!", {key} = {skipsSrc sk}"
  let untitled := match r.bare with
    | none => "box"
    | some b =>
      let parts := (if b.before.isEmpty then [] else [s!"before = {skipsSrc b.before}"]) ++
        (if b.between.isEmpty then [] else [s!"between = {skipsSrc b.between}"])
      "{" ++ (if parts.isEmpty then "" else " " ++ String.intercalate ", " parts ++ " ") ++ "}"
  s!"\{ title = {title}, untitled = {untitled}\
{skips "before" r.before}{skips "between" r.between}{skips "after" r.after}{whole}\
{String.join edges} }"

end LeanTex.Core.BlockTemplate
