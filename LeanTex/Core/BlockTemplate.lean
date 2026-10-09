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
`em` and `ex` in the font in force where it is read), the measure
`\linewidth` in thousandths, and box extents by the box's identity. -/
public structure Dimen where
  len : Length := {}
  line : Int := 0
  ext : List (Nat × Ext × Int) := []
  deriving Repr, BEq, Inhabited

/-- Extents merged by box and extent, zero coefficients dropped. -/
private def mergeExt (xs : List (Nat × Ext × Int)) : List (Nat × Ext × Int) :=
  let keys := (xs.map fun (b, e, _) => (b, e)).eraseDups
  (keys.filterMap fun (b, e) =>
    let c := (xs.filter fun (b', e', _) => b' == b && e' == e).foldl (fun s (_, _, k) => s + k) 0
    if c == 0 then none else some (b, e, c))

public def Dimen.add (a b : Dimen) : Dimen :=
  { len := a.len.add b.len, line := a.line + b.line, ext := mergeExt (a.ext ++ b.ext) }

public def Dimen.neg (a : Dimen) : Dimen :=
  { len := { sp := -a.len.sp, em := -a.len.em, ex := -a.len.ex }, line := -a.line
    ext := a.ext.map fun (b, e, k) => (b, e, -k) }

/-- The length alone, when the dimension is one. -/
public def Dimen.length? (d : Dimen) : Option Length :=
  if d.line == 0 && d.ext.isEmpty then some d.len else none

/-- What a colour command selects: a beamer colour element's channel
(`\usebeamercolor[fg]{block title}`), or a colour by name (`\color{name}`). -/
public inductive Paint where
  | beamer (element : String) (channel : String)
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

/-- What a group restores: the font element, the colour, `\hsize`. -/
private structure Scope where
  font : Option String := none
  paint : Option Paint := none
  hsize : Dimen := { line := 1000 }
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

private structure St where
  scope : Scope := {}
  lst : Lst := {}
  frames : List Frame := []
  regs : List (String × Option Node) := []
  nextId : Nat := 0
  conds : List Pending := []
  unread : Array String := #[]
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

/-- One term of a dimension at `i`: a length word, a measure register, a
box's extent (`\ht\B`), `\z@`, `\p@`, a decimal factor before a register.
The register's box is read *now*, as TeX reads it. -/
private def readTerm (s : St) (toks : Array Tok) (i : Nat) : Option (Dimen × Nat) := Id.run do
  let j := skipSp toks i
  let reg (k : Nat) (factor : Int) : Option (Dimen × Nat) :=
    match toks[k]? with
    | some (.ctrl n) =>
      if measureRegs.contains n then some ({ line := factor }, k + 1)
      else if n == "z@" then some ({}, k + 1)
      else if n == "p@" then some ({ len := { sp := factor * Dim.spPerPt / 1000 } }, k + 1)
      else
        let ext : Option Ext := match n with
          | "ht" => some .ht
          | "dp" => some .dp
          | "wd" => some .wd
          | _ => none
        match ext, toks[skipSp toks (k + 1)]? with
        | some e, some (.ctrl r) =>
          -- A register with no box reads zero (TeX: a void box is 0pt).
          let k' := skipSp toks (k + 1) + 1
          match (s.boxOf r).bind Node.id? with
          | some id =>
            if factor % 1000 == 0 then some ({ ext := [(id, e, factor / 1000)] }, k')
            else none
          | none => some ({}, k')
        | _, _ => none
    | _ => none
  match toks[j]? with
  | some (.word w) =>
    let (neg, w') := if w.startsWith "-" then (true, (w.drop 1).toString)
      else if w.startsWith "+" then (false, (w.drop 1).toString) else (false, w)
    let sign : Int := if neg then -1 else 1
    match Decl.parseLength w' with
    | some l =>
      some ({ len := { sp := sign * l.sp, em := sign * l.em, ex := sign * l.ex } }, j + 1)
    | none =>
      if w'.isEmpty then reg (skipSp toks (j + 1)) (sign * 1000)
      else (Decl.parseDecimal w').bind fun (m, sc) =>
        reg (skipSp toks (j + 1)) (sign * m * 1000 / (sc : Int))
  | some (.ctrl _) => reg j 1000
  | _ => none

/-- A dimension at `i`, after an optional `=`: one term, or `\dimexpr`'s
sum of terms up to `\relax`. -/
private def readDimen (s : St) (toks : Array Tok) (i : Nat) : Option (Dimen × Nat) := Id.run do
  let j := skipSp toks i
  let j := if toks[j]? == some (.word "=") || toks[j]? == some (.sym '=') then
    skipSp toks (j + 1) else j
  unless toks[j]? == some (.ctrl "dimexpr") do return readTerm s toks j
  let mut acc : Dimen := {}
  let mut k := j + 1
  let mut sign : Int := 1
  for _ in [j + 1:toks.size] do
    let k0 := skipSp toks k
    match toks[k0]? with
    | some (.ctrl "relax") => return some (acc, k0 + 1)
    | some (.sym '+') => sign := 1; k := k0 + 1
    | some (.sym '-') => sign := -1; k := k0 + 1
    | some (.word "+") => sign := 1; k := k0 + 1
    | some (.word "-") => sign := -1; k := k0 + 1
    | some _ =>
      match readTerm s toks k0 with
      | some (d, k') =>
        acc := acc.add (if sign < 0 then d.neg else d)
        sign := 1
        k := k'
      | none => return none
    | none => return some (acc, k0)
  return none

/-- The skip registers a template may read, as `Ir.skipAmount` names them. -/
private def skipRegs : List String := ["smallskipamount", "medskipamount", "bigskipamount"]

/-- A glue at `i`: a skip register, or `<dimen> [plus <dimen>] [minus
<dimen>]` with plain lengths. -/
private def readGlue (s : St) (toks : Array Tok) (i : Nat) : Option (Ir.BlockSkip × Nat) := Id.run do
  let j := skipSp toks i
  match toks[j]? with
  | some (.ctrl n) =>
    if skipRegs.contains n then return some (.register n, j + 1)
    if n == "z@skip" then return some (.glue {}, j + 1)
  | _ => pure ()
  let some (w, k) := readDimen s toks j | return none
  let some wl := w.length? | return none
  let mut g : SymGlue := { width := wl }
  let mut k := k
  for _ in [0:2] do
    let k0 := skipSp toks k
    match toks[k0]? with
    | some (.word "plus") =>
      let some (d, k') := readDimen s toks (k0 + 1) | return none
      let some l := d.length? | return none
      g := { g with stretch := l }
      k := k'
    | some (.word "minus") =>
      let some (d, k') := readDimen s toks (k0 + 1) | return none
      let some l := d.length? | return none
      g := { g with shrink := l }
      k := k'
    | _ => break
  return some (.glue g, k)

/-- A rule's `width`, `height` and `depth` keywords from `i`, in any order. -/
private def readRuleSpec (s : St) (toks : Array Tok) (i : Nat) :
    Option ((Option Dimen × Option Dimen × Option Dimen) × Nat) := Id.run do
  let mut w : Option Dimen := none
  let mut h : Option Dimen := none
  let mut d : Option Dimen := none
  let mut k := i
  for _ in [0:3] do
    let k0 := skipSp toks k
    match toks[k0]? with
    | some (.word "width") =>
      let some (v, k') := readDimen s toks (k0 + 1) | return none
      w := some v; k := k'
    | some (.word "height") =>
      let some (v, k') := readDimen s toks (k0 + 1) | return none
      h := some v; k := k'
    | some (.word "depth") =>
      let some (v, k') := readDimen s toks (k0 + 1) | return none
      d := some v; k := k'
    | _ => break
  return some ((w, h, d), k)

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

/-- The interpreter's main loop over the flat list. `titled` is the arm of
`\ifx\insertblocktitle\@empty` this run takes. -/
private def run (toks : Array Tok) (titled : Bool) : St := Id.run do
  let mut s : St := {}
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
        match readGlue s toks (i + 1) with
        | some (g, k) => s := s.pushV (.vskip g) "\\vskip"; i := k
        | none => s := s.miss "\\vskip with a glue it cannot read"; i := i + 1
      | "vspace" =>
        let j := skipSp toks (i + 1)
        let j := if toks[j]? == some (.word "*") then j + 1 else j
        match readArg toks j with
        | some (arg, k) =>
          match readGlue s arg 0 with
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
              | some (arg, k) => ((readDimen s arg 0).map (·.1), k)
              | none => (none, i + 1)
            else match readGlue s toks (i + 1) with
              | some (.glue g, k) =>
                if g.stretch == {} && g.shrink == {} then (some { len := g.width }, k)
                else (none, k)
              | _ => (none, i + 1)
          match dim with
          | some d => s := s.pushH (.hskip d s.scope.font)
          | none => s := s.miss s!"\\{n} with stretch or an unreadable length"
          i := k
      | "hsize" =>
        match readDimen s toks (i + 1) with
        | some (d, k) => s := { s with scope := { s.scope with hsize := d } }; i := k
        | none => s := s.miss "\\hsize set to a length it cannot read"; i := i + 1
      | "advance" =>
        let j := skipSp toks (i + 1)
        if toks[j]? == some (.ctrl "hsize") then
          let j := skipSp toks (j + 1)
          let j := if toks[j]? == some (.word "by") then j + 1 else j
          match readDimen s toks j with
          | some (d, k) =>
            s := { s with scope := { s.scope with hsize := s.scope.hsize.add d } }; i := k
          | none => s := s.miss "\\advance\\hsize by a length it cannot read"; i := j
        else s := s.miss "\\advance"; i := i + 1
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
        let j := if toks[j]? == some (.word "*") then j + 1 else j
        let (ch, j) := readOpt toks j
        match readArg toks j with
        | some (arg, k) =>
          let el := (wordsOf arg).trimAscii.toString
          match ch with
          | some c =>
            if c == "fg" || c == "bg" then s := s.paint (.beamer el c)
            else s := s.miss s!"\\usebeamercolor[{c}]"
          | none => pure ()
          i := k
        | none => s := s.miss "\\usebeamercolor"; i := i + 1
      | "color" =>
        let (model, j) := readOpt toks (i + 1)
        match model, readArg toks j with
        | none, some (arg, k) =>
          let name := (wordsOf arg).trimAscii.toString
          let p : Paint := if name.endsWith ".fg" then .beamer (name.dropEnd 3).toString "fg"
            else if name.endsWith ".bg" then .beamer (name.dropEnd 3).toString "bg"
            else .named name
          s := s.paint p
          i := k
        | _, _ => s := s.miss "\\color"; i := i + 1
      | "vrule" =>
        match readRuleSpec s toks (i + 1) with
        | some ((w, h, d), k) =>
          let w := w.orElse fun _ => some { len := { sp := Dim.spPerPt * 4 / 10 } }
          s := s.pushH (.rule w h d s.scope.paint s.scope.font)
          i := k
        | none => s := s.miss "\\vrule with a dimension it cannot read"; i := i + 1
      | "hrule" =>
        match readRuleSpec s toks (i + 1) with
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
        if n.startsWith "if" then s := s.miss s!"\\{n}" else s := s.miss s!"\\{n}"
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
  deriving Repr, BEq, Inhabited

/-- What a template pair sets, read: `Ir.BlockShape` but for its rules'
colours, which a palette resolves, and the font elements and colours the
title and body are set in, which the caller holds to the kind's own. -/
public structure Read where
  before : Array Ir.BlockSkip := #[]
  title : Ir.BlockTitleBox := {}
  untitled : Bool := true
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

/-- The rules beside one box in its line: `\llap{…\vrule…\hskip S}` before
it hangs left, `\vrule\hskip S` before it stands inside the line, and their
mirrors after it. A rule reading the box's own extents spans the box; one
reading an emptied register has no height and draws nothing, as in TeX. -/
private def edgesOf (span : Ir.BlockSpan) (id : Nat) (hsize : Dimen) (lineHsize : Dimen)
    (before after : List Node) : Except String (Array EdgeRead) := Id.run do
  let spans (h d : Option Dimen) : Except String Bool :=
    match h, d with
    | some h, some d =>
      if h == { ext := [(id, .ht, 1)] } && d == { ext := [(id, .dp, 1)] } then .ok true
      else if h == {} && d == {} then .ok false
      else .error "a rule whose height and depth are not its box's"
    | _, _ => .error "a rule running to its line"
  let lenOf (d : Dimen) (font : Option String) : Except String Length :=
    match d.length? with
    | some l =>
      if font.isNone || (l.em == 0 && l.ex == 0) then .ok l
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
      | [.rule (some w) h d p f] =>
        if !(← spans h d) then return (none, {})
        return (some { span, side := sideName, width := ← lenOf w f, sep := {}, hang := true,
                        paint := p }, {})
      | [.hskip g gf, .rule (some w) h d p f] =>
        if !(← spans h d) then return (none, {})
        return (some { span, side := sideName, width := ← lenOf w f, sep := ← lenOf g gf,
                        hang := true, paint := p }, {})
      | _ => throw "a lap holding more than a rule and its space"
    | _ =>
      let outward := if onRight then ns else ns.reverse
      match outward with
      | [.hskip g gf, .rule (some w) h d p f] =>
        if !(← spans h d) then throw "a rule beside its box that draws nothing but still takes room"
        let wl ← lenOf w f
        let gl ← lenOf g gf
        return (some { span, side := sideName, width := wl, sep := gl, hang := false,
                        paint := p }, wl.add gl)
      | [.rule (some w) h d p f] =>
        if !(← spans h d) then throw "a rule beside its box that draws nothing but still takes room"
        let wl ← lenOf w f
        return (some { span, side := sideName, width := wl, sep := {}, hang := false,
                        paint := p }, wl)
      | _ => throw "a line holding more than its box and the rules beside it"
  match side false before, side true after with
  | .ok (l, li), .ok (r, ri) =>
    -- The box and the rules inside its line fill the line exactly.
    let used := (Dimen.add hsize { len := li.add ri })
    if used != lineHsize then return .error "a box and its rules that do not fill their line"
    return .ok ((l.toList ++ r.toList).toArray)
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
          match edgesOf .title id hsize lineHsize before after with
          | .error e => return .error e
          | .ok es =>
            seenTitle := true
            arm := { arm with title := some { boxed := true, strut := st, parskip := pk }
                              titleFont := f, titlePaint := p, edges := arm.edges ++ es }
        | .ok (.whole title between bodyParskip bf bp after') =>
          match edgesOf .whole id hsize lineHsize before after with
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
one only in leaving the title out, or in keeping its box empty. -/
public def read (beginRaws endRaws : Array Raw) (defs : String → Option Macro := fun _ => none)
    (bound : Nat := 0) : Except (Array String) Read :=
  let opening := flatten beginRaws
  let closing := flatten endRaws
  let flat := #[Tok.par] ++ opening ++ #[Tok.body, Tok.par] ++ closing
  let toks := expandList defs bound flat.toList #[]
  let titled := run toks true
  let untitled := run toks false
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
      if t.before != u.before then .error #["skips above the title the untitled arm sets otherwise"]
      else if t.after != u.after then .error #["skips below the body the untitled arm sets otherwise"]
      else if t.whole.isSome != u.whole.isSome || wholeEdges t != wholeEdges u then
        .error #["a box around the body the untitled arm sets otherwise"]
      else if untitledBox && (u.title != t.title || u.edges != t.edges || u.between != t.between) then
        .error #["an empty title box the untitled arm sets otherwise"]
      else if titleEdges.any (fun _ => !title.boxed) then
        .error #["a rule beside a title with no box of its own"]
      else
        let spansides := t.edges.map fun e => (e.span, e.side)
        if spansides.toList.eraseDups.length != spansides.size then
          .error #["two rules on one side of one box"]
        else .ok
          { before := t.before, title := title, untitled := untitledBox
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

/-- A length as the native declaration writes it: points where they are
exact to the thousandth, else scaled points, and the font-relative parts. -/
private def lengthSrc (l : Length) : String :=
  let part (v : Int) (unit : String) : Option String :=
    if v == 0 then none else some (milliText v ++ unit)
  let pts := if l.sp == 0 then none
    else if (l.sp * 1000) % Dim.spPerPt == 0 then some (milliText (l.sp * 1000 / Dim.spPerPt) ++ "pt")
    else some (toString l.sp ++ "sp")
  match [pts, part l.em "em", part l.ex "ex"].filterMap id with
  | [] => "0pt"
  | p :: ps => ps.foldl (fun acc q =>
      if q.startsWith "-" then acc ++ " - " ++ (q.drop 1).toString else acc ++ " + " ++ q) p

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
    s!", edge = \{ span = {span}, side = {side}, width = {lengthSrc e.width}, \
sep = {lengthSrc e.sep}, hang = {e.hang}, color = {colors.getD i "fg"} }"
  let skips (key : String) (sk : Array Ir.BlockSkip) : String :=
    if sk.isEmpty then "" else s!", {key} = {skipsSrc sk}"
  s!"\{ title = {title}, untitled = {if r.untitled then "box" else "none"}\
{skips "before" r.before}{skips "between" r.between}{skips "after" r.after}{whole}\
{String.join edges} }"

end LeanTex.Core.BlockTemplate
