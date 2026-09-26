import LeanTex.Core.Parse
import LeanTex.Core.Picture

/-!
The reader of beamer's `title page` template, for the one shape a theme
writes a full-bleed title page in: an overlay `tikzpicture` on the page
(`remember picture,overlay`, TikZ manual §17.13.2), a fill over the whole
page, and nodes pinned to points of the page, each setting one declared
datum through beamer's inserts (beamerbasetitle.sty) or literal content.
What it reads is a spelling of the engine's own title page — the ground
(`titlepagebg`) and one slot per node (`\style{titlepage}{ slot = ... }`) —
and it reads source, never meaning: every value it returns is the template's
own text, evaluated where the native declaration is (palette names, lengths,
font commands). A template of any other shape is not this reader's, and a
node it cannot map is named, never guessed.
-/

namespace LeanTex.Core.TitleTemplate

open LeanTex.Core
open LeanTex.Core.Picture (Tok)

/-- One node of the template, as native source. -/
structure Node where
  /-- The datum the node inserts (`title`, `author`, ...), or `none` for
  literal content. -/
  datum : Option String
  /-- Further data the node sets after its first, each with whether a line
  end stands before it. -/
  more : Array (Bool × String) := #[]
  /-- Literal content, as source (empty for a datum node). -/
  content : String := ""
  font : String := ""
  /-- The size the node's font declares, as source (`size*`'s first
  argument). -/
  size : Option String := none
  ink : Option String := none
  align : Option String := none
  width : Option String := none
  /-- Whether the node stands pinned to a point of the page. A node the
  engine cannot pin — no `at (current page.<point>)`, or several data in
  one node — still sets what it inserts, unpinned: at the title page's
  default place, in its flow. -/
  pinned : Bool := true
  anchor : String := "center"
  pagePoint : String := "center"
  xshift : Option String := none
  yshift : Option String := none
  innerSep : Option String := none
  deriving Repr, BEq, Inhabited

/-- What the template says, and what of it the reader does not model. -/
structure Read where
  ground : Option String := none
  nodes : Array Node := #[]
  /-- The constructs met and not modelled, by name: what the one loss the
  translation names lists. -/
  unread : Array String := #[]
  /-- The theme's own font elements the template selects: each is honoured
  here, so its skip at the declaration is withdrawn. -/
  fonts : Array String := #[]
  /-- Nodes the engine cannot pin as the template does: the data each sets
  (empty for literal content) and whether it is several data in one node.
  What each sets still ships, unpinned. -/
  unplaced : Array (Array String × Bool) := #[]
  /-- Control words met beside a datum and not read, with the datum: the
  datum ships without them. -/
  skipped : Array (String × String) := #[]
  /-- A node sets a datum beside literal text, which no slot holds: the
  datum named here. The template is then not read, and the built-in title
  page sets every datum. -/
  mixed : Option String := none
  deriving Repr, BEq, Inhabited

/-- A custom beamer font element, as `\setbeamerfont` declared it: its font
commands and, apart, the size it declares (beamerbasefont.sty's `size*`). -/
structure Font where
  cmds : String := ""
  size : Option String := none
  /-- What the declaration said that the record does not take. -/
  unread : Array String := #[]
  deriving Repr, BEq, Inhabited

/-- beamer's inserts, by the datum each sets (beamerbasetitle.sty). -/
def insertDatum : String → Option String
  | "inserttitle" | "insertshorttitle" => some "title"
  | "insertsubtitle" | "insertshortsubtitle" => some "subtitle"
  | "insertauthor" | "insertshortauthor" => some "author"
  | "insertinstitute" | "insertshortinstitute" => some "institute"
  | "insertdate" | "insertshortdate" => some "date"
  | _ => none

/-- TeX's integer parameters a template sets inside a node to keep a title
from breaking (`\pretolerance=10000`): configuration of the line breaker,
not ink. -/
def breakParams : List String :=
  ["pretolerance", "tolerance", "hyphenpenalty", "exhyphenpenalty", "linepenalty",
   "emergencystretch"]

private def trimFront : List Tok → List Tok
  | .space :: rest => trimFront rest
  | [] => []
  | t :: rest => t :: rest

private def trim (ts : List Tok) : List Tok :=
  (trimFront (trimFront ts).reverse).reverse

mutual

/-- Source text of micro-tokens, re-lexable, into an accumulator: a control
word is kept apart from a following letter. -/
def srcListInto (acc : String) : List Tok → String
  | [] => acc
  | .ctrl n :: rest@(.ident _ :: _) => srcListInto (acc ++ "\\" ++ n ++ " ") rest
  | t :: rest => srcListInto (srcOneInto acc t) rest

def srcOneInto (acc : String) : Tok → String
  | .ctrl n => acc ++ "\\" ++ n
  | .ident s => acc ++ s
  | .num m =>
    let digits := Picture.milliString m
    acc ++ digits
  | .sym c => acc.push c
  | .space => acc ++ " "
  | .group body => srcListInto (acc ++ "{") body ++ "}"
  | .math _ _ => acc ++ "$...$"
  | .other what => acc ++ what

end

def srcList (ts : List Tok) : String := srcListInto "" ts

def srcOne (t : Tok) : String := srcOneInto "" t

/-- Split at a top-level symbol, brackets and parentheses nesting. -/
def splitTop (c : Char) (ts : List Tok) : List (List Tok) := Id.run do
  let mut out : Array (List Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth : Nat := 0
  for t in ts do
    match t with
    | .sym d =>
      if d == c && depth == 0 then
        out := out.push cur.toList
        cur := #[]
      else
        if d == '[' || d == '(' then depth := depth + 1
        if (d == ']' || d == ')') && depth > 0 then depth := depth - 1
        cur := cur.push t
    | _ => cur := cur.push t
  return (out.push cur.toList).toList

/-- A bracketed run at the head: its inside and what follows it. -/
def takeBracket (lo hi : Char) (ts : List Tok) : Option (List Tok × List Tok) :=
  match trimFront ts with
  | .sym o :: rest =>
    if o != lo then none else Id.run do
      let mut depth : Nat := 0
      let mut inner : Array Tok := #[]
      let mut i := 0
      let arr := rest.toArray
      for t in arr do
        i := i + 1
        match t with
        | .sym d =>
          if d == hi && depth == 0 then
            return some (inner.toList, (arr.extract i arr.size).toList)
          if d == lo then depth := depth + 1
          if d == hi then depth := depth - 1
          inner := inner.push t
        | _ => inner := inner.push t
      return none
  | _ => none

/-- One option entry: its key (words joined by single spaces) and value. -/
def entryOf (ts : List Tok) : String × Option (List Tok) :=
  let (k, v) := ts.span (· != .sym '=')
  let key := String.intercalate " " ((trim k).filterMap fun t => match t with
    | .ident s => some s
    | _ => none)
  match v with
  | _ :: rest => (key, some (trim rest))
  | [] => (key, none)

/-- `current page.<point>`, optionally shifted: `([xshift=…,yshift=…]current
page.south west)` — the page point and the two shifts as source. -/
def pagePointOf (ts : List Tok) : Option (String × Option String × Option String) := do
  let (shifts, rest) := match takeBracket '[' ']' ts with
    | some (inner, after) => (some inner, after)
    | none => (none, ts)
  match trim rest with
  | .ident "current" :: .space :: .ident "page" :: .sym '.' :: pt =>
    let point := String.intercalate " " (pt.filterMap fun t => match t with
      | .ident s => some s
      | _ => none)
    let mut xs : Option String := none
    let mut ys : Option String := none
    for e in (shifts.map (splitTop ',')).getD [] do
      match entryOf e with
      | ("xshift", some v) => xs := some (srcList v)
      | ("yshift", some v) => ys := some (srcList v)
      | _ => none
    return (point, xs, ys)
  | _ => none

/-- The style in force at a point of a node's content: the font commands
declared so far, the size a selected theme font declares, a `\color`, and
a ragged declaration. A group scopes each of them, as TeX's does. -/
structure Style where
  font : String := ""
  size : Option String := none
  ink : Option String := none
  align : Option String := none
  deriving Repr, BEq, Inhabited

/-- What a node's content group sets: each datum it inserts with the style
in force where the insert stands and whether a line end stands between it
and the datum before, whether any other ink stands beside them, the
control words met and not read, and the theme fonts selected. -/
structure Scan where
  data : Array (String × Style × Bool) := #[]
  words : Bool := false
  skipped : Array String := #[]
  used : Array String := #[]
  /-- A line end met since the last datum. -/
  broke : Bool := false
  deriving Repr, Inhabited

/-- NFSS's font-change commands, declaration beside its one-argument form —
fntguide §2.2's table, the one the elaborator reads (`Elab.fontAxes`; a
check holds the two equal). In a node's content, either spelling is the
node's font, as `font=` is. -/
def fontAxes : List (String × String) :=
  [("rmfamily", "textrm"), ("sffamily", "textsf"), ("ttfamily", "texttt"),
   ("mdseries", "textmd"), ("bfseries", "textbf"), ("upshape", "textup"),
   ("itshape", "textit"), ("slshape", "textsl"), ("scshape", "textsc"),
   ("normalfont", "textnormal"), ("em", "emph")]

/-- A font declaration in content: an NFSS axis or a size of the scale. -/
def fontDecl (n : String) : Bool :=
  fontAxes.any (·.1 == n) || Ir.sizeScale.any (·.1 == n)

/-- Control words that end or break a line and set no ink of their own. -/
def lineCtrls : List String := ["par", "\\", "newline", "null"]

/-- **What a node's content sets**, one scan in source order. A datum is
recorded with the style in force where its insert stands; a group scopes
declarations; a font declaration, `\usebeamerfont`, `\color` and a ragged
declaration are read; the breaker's integer parameters and line ends are
transparent; `\usebeamercolor` and any other control word are named and
not read, an argument group of theirs still scanned for data. Anything
else is ink beside the data. -/
def scanList (fonts : List (String × Font)) (st : Style) (acc : Scan) : List Tok → Scan
  | [] => acc
  | .space :: rest => scanList fonts st acc rest
  | .group body :: rest => scanList fonts st (scanList fonts st acc body) rest
  | .ctrl n :: .sym '=' :: .num _ :: rest =>
    if breakParams.contains n then scanList fonts st acc rest
    else scanList fonts st { acc with skipped := acc.skipped.push s!"\\{n}" } rest
  | .ctrl "usebeamerfont" :: .group g :: rest =>
    let name := srcList (trim g)
    match fonts.lookup name with
    | some f =>
      scanList fonts { st with font := st.font ++ f.cmds, size := f.size <|> st.size }
        { acc with used := acc.used.push name } rest
    | none =>
      scanList fonts st
        { acc with skipped := acc.skipped.push s!"\\usebeamerfont\{{name}}" } rest
  | .ctrl "color" :: .group g :: rest =>
    let c := srcList (trim g)
    if c.contains '!' then
      scanList fonts st { acc with skipped := acc.skipped.push s!"\\color\{{c}}" } rest
    else scanList fonts { st with ink := some c } acc rest
  | .ctrl "usebeamercolor" :: .sym '[' :: .ident _ :: .sym ']' :: .group _ :: rest
  | .ctrl "usebeamercolor" :: .group _ :: rest =>
    scanList fonts st { acc with skipped := acc.skipped.push "\\usebeamercolor" } rest
  | .ctrl n :: .group body :: rest =>
    match insertDatum n, fontAxes.find? (·.2 == n) with
    | some d, _ =>
      scanList fonts st (scanList fonts st (push acc d st) body) rest
    | none, some (decl, _) =>
      scanList fonts st (scanList fonts { st with font := st.font ++ s!"\\{decl} " } acc body)
        rest
    | none, none =>
      let (st', acc') := ctrlStep st acc n
      scanList fonts st' (scanList fonts st' acc' body) rest
  | .ctrl n :: rest =>
    let (st', acc') := ctrlStep st acc n
    scanList fonts st' acc' rest
  | _ :: rest => scanList fonts st { acc with words := true } rest
where
  /-- Record a datum, with whether a line end stood before it. -/
  push (acc : Scan) (d : String) (st : Style) : Scan :=
    { acc with data := acc.data.push (d, st, acc.broke), broke := false }
  /-- One bare control word: a datum, a line end, a ragged or font
  declaration, or a construct named and not read. -/
  ctrlStep (st : Style) (acc : Scan) (n : String) : Style × Scan :=
    match insertDatum n with
    | some d => (st, push acc d st)
    | none =>
      if lineCtrls.contains n then (st, { acc with broke := true })
      else if n == "raggedright" then ({ st with align := some "left" }, acc)
      else if n == "raggedleft" then ({ st with align := some "right" }, acc)
      else if n == "centering" then ({ st with align := some "center" }, acc)
      else if fontDecl n then ({ st with font := st.font ++ s!"\\{n} " }, acc)
      else (st, { acc with skipped := acc.skipped.push s!"\\{n}" })

/-- Two opposite corners of the page: the rectangle between them is the
whole page. -/
def opposite (a b : String) : Bool :=
  (a == "south west" && b == "north east") || (a == "north east" && b == "south west") ||
  (a == "north west" && b == "south east") || (a == "south east" && b == "north west")

/-- `\fill[<colour>] (current page.<corner>) rectangle (current page.<corner>)`
over two opposite corners: the page's ground. -/
def fillStmt (rd : Read) (ts : List Tok) : Read :=
  let (color, rest) := match takeBracket '[' ']' ts with
    | some (inner, after) =>
      ((splitTop ',' inner).findSome? fun e => match entryOf e with
        | (_, none) => some (srcList (trim e))
        | ("fill", some v) => some (srcList v)
        | ("color", some v) => some (srcList v)
        | _ => none, after)
    | none => (none, ts)
  let corners : Option (String × String) := do
    let (a, after) ← takeBracket '(' ')' rest
    let after2 ← match trim after with
      | .ident "rectangle" :: after2 => some after2
      | _ => none
    let (b, _) ← takeBracket '(' ')' after2
    let (pa, xa, ya) ← pagePointOf a
    let (pb, xb, yb) ← pagePointOf b
    if xa.isNone && ya.isNone && xb.isNone && yb.isNone then some (pa, pb) else none
  match color, corners with
  | some c, some (pa, pb) =>
    if opposite pa pb then { rd with ground := some c }
    else { rd with unread := rd.unread.push "a fill that does not cover the page" }
  | _, _ => { rd with unread := rd.unread.push "a fill that does not cover the page" }

/-- A node's `font=`: font commands, with `\usebeamerfont{<element>}` read
through the custom elements the theme declared. -/
def fontOf (fonts : List (String × Font)) (ts : List Tok) :
    Option (Font × Array String) := do
  let mut cmds := ""
  let mut size : Option String := none
  let mut unread : Array String := #[]
  let mut used : Array String := #[]
  let mut rest := trim ts
  for _ in [0:ts.length + 1] do
    match rest with
    | [] => break
    | .space :: r => rest := r
    | .ctrl "usebeamerfont" :: r =>
      match trimFront r with
      | .group body :: r' =>
        let name := srcList (trim body)
        let f ← fonts.lookup name
        cmds := cmds ++ f.cmds
        size := f.size <|> size
        unread := unread ++ f.unread
        used := used.push name
        rest := r'
      | _ => failure
    | t@(.ctrl _) :: r =>
      cmds := cmds ++ srcOne t
      rest := r
    | _ => failure
  return ({ cmds := cmds, size := size, unread := unread }, used)

/-- `\node[<options>] (<name>) at (<page point>) {<content>}`. -/
def nodeStmt (fonts : List (String × Font)) (rd : Read) (ts : List Tok) : Read := Id.run do
  let mut rest := ts
  let mut opts : List (List Tok) := []
  let mut coord : Option (List Tok) := none
  let mut content : Option (List Tok) := none
  let mut bad := false
  for _ in [0:ts.length + 1] do
    match trimFront rest with
    | [] => break
    | toks@(.sym '[' :: _) =>
      match takeBracket '[' ']' toks with
      | some (inner, after) =>
        opts := opts ++ splitTop ',' inner
        rest := after
      | none =>
        bad := true
        break
    | toks@(.sym '(' :: _) =>
      match takeBracket '(' ')' toks with
      | some (_, after) => rest := after
      | none =>
        bad := true
        break
    | .ident "at" :: after =>
      match takeBracket '(' ')' after with
      | some (inner, after2) =>
        coord := some inner
        rest := after2
      | none =>
        bad := true
        break
    | .group body :: after =>
      content := some body
      rest := after
    | _ =>
      bad := true
      break
  -- The page point the node is pinned to, when it is pinned: `at (current
  -- page.<point>)`, optionally shifted. A node with no readable pin still
  -- sets what it inserts, unpinned — never dropped with its data.
  let pin : Option (String × Option String × Option String) :=
    if bad then none else
    (coord.bind pagePointOf).filter fun (point, _, _) => (Ir.BoxPoint.ofName? point).isSome
  let some body := content | return { rd with unread := rd.unread.push "a node with no content" }
  let mut n : Node := match pin with
    | some (point, xs, ys) => { datum := none, pagePoint := point, xshift := xs, yshift := ys }
    | none => { datum := none, pinned := false }
  let mut unread := rd.unread
  let mut used := rd.fonts
  for o in opts do
    match entryOf o with
    | ("anchor", some v) =>
      let a := srcList v
      if (Ir.BoxPoint.ofName? a).isSome then n := { n with anchor := a }
      else unread := unread.push s!"anchor={a}"
    | ("align", some v) =>
      let a := srcList v
      if a == "left" || a == "center" || a == "right" then n := { n with align := some a }
      else unread := unread.push s!"align={a}"
    | ("text width", some v) => n := { n with width := some (srcList v) }
    | ("text", some v) =>
      let c := srcList v
      if c.contains '!' then unread := unread.push s!"text={c}"
      else n := { n with ink := some c }
    | ("inner sep", some v) => n := { n with innerSep := some (srcList v) }
    | ("font", some v) =>
      match fontOf fonts v with
      | some (f, names) =>
        n := { n with font := f.cmds, size := f.size }
        unread := unread ++ f.unread
        used := used ++ names
      | none => unread := unread.push s!"font={srcList v}"
    | (k, _) => unless k.isEmpty do unread := unread.push k
  let sc := scanList fonts {} {} body
  used := used ++ sc.used
  -- Each datum takes the node's options, then what its content declared
  -- before it: the content's own font follows `font=`, as TeX reads them.
  let styled (d : String) (s : Style) : Node :=
    { n with datum := some d
             font := if s.font.isEmpty then n.font else (n.font ++ " " ++ s.font).trimAscii.toString
             size := s.size <|> n.size
             ink := s.ink <|> n.ink
             align := n.align <|> s.align }
  if sc.words && !sc.data.isEmpty then
    return { rd with mixed := rd.mixed <|> sc.data[0]?.map (·.1) }
  let rd := { rd with unread := unread, fonts := used }
  match sc.data.toList with
  | [] =>
    let node := { n with content := srcList body }
    return { rd with nodes := rd.nodes.push node
                     unplaced := if node.pinned then rd.unplaced else rd.unplaced.push (#[], false) }
  | (d, s, _) :: later =>
    let data := #[d] ++ later.toArray.map (·.1)
    let rd := { rd with skipped := rd.skipped ++ sc.skipped.map (·, d) }
    if later.all (·.2.1 == s) then
      -- One style for every datum: one slot sets them all, in the node's
      -- order and on the node's lines, pinned as the node is.
      let node := { styled d s with more := later.toArray.map fun (d', _, br) => (br, d') }
      return { rd with nodes := rd.nodes.push node
                       unplaced := if node.pinned then rd.unplaced else rd.unplaced.push (data, false) }
    else
      -- Data the node styles apart are no one slot: each sets unpinned, in
      -- its own style, in the order the node inserts them.
      let nodes := ((d, s, false) :: later).toArray.map fun (d', s', _) =>
        { styled d' s' with pinned := false }
      return { rd with nodes := rd.nodes ++ nodes, unplaced := rd.unplaced.push (data, true) }

/-- The data a node sets, as prose: `the author and the institute`. -/
def dataPhrase (ds : List String) : String :=
  match ds.reverse with
  | [] => "literal text"
  | [a] => s!"the {a}"
  | last :: init =>
    String.intercalate ", " (init.reverse.map (s!"the {·}")) ++ s!" and the {last}"

/-- The one loss a node the engine cannot pin is named by (`W0363`): the
key's suffix (the data it sets), what it sets and where that stands
instead, and the help. -/
def unplacedLoss (data : Array String) (several : Bool) : String × String × Option String :=
  let key := if data.isEmpty then "text" else String.intercalate "+" data.toList
  let help := data[0]?.map fun d =>
    (if several then "pin one datum per node: " else "pin the node to a point of the page: ") ++
      s!"\\node[anchor=west] at (current page.west) \{\\insert{d}}"
  let msg :=
    if several then
      s!"one title-page template node styles {dataPhrase data.toList} apart; each sets \
unpinned, in the title page's flow"
    else match data[0]? with
      | some d =>
        let verb := if data.size > 1 then "set" else "sets"
        s!"the title-page template's {d} node is not pinned to the page; \
{dataPhrase data.toList} {verb} in the title page's flow"
      | none => "a title-page template node of literal text is not pinned to the page; \
it sets in the title page's flow"
  (key, msg, help)

/-- A control word beside a datum that the reader does not read (`W0104`):
the key's suffix and the message; the datum ships without it. -/
def skippedLoss (construct datum : String) : String × String :=
  (construct,
   s!"'{construct}' in the title-page template's {datum} node is not read; the {datum} \
sets without it")

/-- A datum beside literal text (`W0363`): no slot holds the two, so the
template is not read and the built-in title page — the default place of
every datum — stands. The key's suffix, the message, the help. -/
def mixedLoss (datum : String) : String × String × Option String :=
  (datum,
   s!"the title-page template sets the {datum} beside literal text, which no slot holds; \
the built-in title page stands",
   some s!"set the text in a node of its own, and \\insert{datum} alone in another")

/-- **Read a `title page` template of the overlay shape.** `none` when the
template is not one overlay picture on the page — any other shape is not
this reader's, and the caller keeps its refusal. -/
def read (fonts : List (String × Font)) (body : Array Parse.Raw) : Option Read := do
  let mut pic : Option (Array Parse.Raw) := none
  for r in body do
    match r with
    | .env n b _ =>
      if n != "tikzpicture" || pic.isSome then failure
      pic := some b
    | .space | .par _ => pure ()
    | .ctrl n _ => if n != "null" && n != "par" then failure
    | _ => failure
  let b ← pic
  let (opts, stmts) ← takeBracket '[' ']' (Picture.ofRaws b).toList
  let keys := (splitTop ',' opts).map fun e => (entryOf e).1
  unless keys.contains "overlay" && keys.contains "remember picture" do failure
  let mut rd : Read := {}
  for st in splitTop ';' stmts do
    match trim st with
    | [] => pure ()
    | .ctrl "fill" :: rest => rd := fillStmt rd rest
    | .ctrl "node" :: rest => rd := nodeStmt fonts rd rest
    | .ctrl n :: _ => rd := { rd with unread := rd.unread.push s!"\\{n}" }
    | _ => rd := { rd with unread := rd.unread.push "a statement that is not a fill or a node" }
  return rd

/-- The read template as the engine's own declarations: the ground (and the
title's ink, which stands on it) as palette roles, and one slot per node.
The title page the template replaces draws no lineage separator. A node's
ink rides its font template as the palette colour command; the title's is
the title page's own ink role when a ground stands. -/
def native (rd : Read) : String :=
  let titleInk := (rd.nodes.find? (·.datum == some "title")).bind (·.ink)
  let roles := (rd.ground.map (s!"titlepagebg = {·}")).toList ++
    (if rd.ground.isSome then (titleInk.map (s!"titlepagefg = {·}")).toList else [])
  let palette := if roles.isEmpty then "" else
    "\\palette{ " ++ String.intercalate ", " roles ++ " }"
  let slot (n : Node) : String :=
    let ink := match n.ink with
      | some c =>
        if rd.ground.isSome && n.ink == titleInk then "" else s!"\\{c} "
      | none => ""
    let font := n.font ++ (if n.font.isEmpty || ink.isEmpty then "" else " ") ++ ink
    let parts :=
      (match n.datum with
       | some d => [s!"set = {d}" ++ String.join (n.more.toList.map fun (own, d') =>
           (if own then " \\\\ " else " ") ++ d')]
       | none => ["content = {" ++ n.content ++ "}"]) ++
      (if n.pinned then
        [s!"anchor = {n.anchor}", s!"at = {n.pagePoint}"] ++
        (n.xshift.map (s!"xshift = {·}")).toList ++
        (n.yshift.map (s!"yshift = {·}")).toList ++
        (n.width.map (s!"width = {·}")).toList
      else []) ++
      (n.size.map (s!"size = {·}")).toList ++
      (if n.pinned then (n.innerSep.map (s!"inner-sep = {·}")).toList else []) ++
      (n.align.map (s!"align = {·}")).toList ++
      (if font.isEmpty then [] else ["font = {" ++ font.trimAscii.toString ++ "}"])
    "slot = { " ++ String.intercalate ", " parts ++ " }"
  let style := "\\style{titlepage}{ separator = none" ++
    String.join (rd.nodes.toList.map fun n => ", " ++ slot n) ++ " }"
  palette ++ style

end LeanTex.Core.TitleTemplate
