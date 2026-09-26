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
  /-- Literal content, as source (empty for a datum node). -/
  content : String := ""
  font : String := ""
  /-- The size the node's font declares, as source (`size*`'s first
  argument). -/
  size : Option String := none
  ink : Option String := none
  align : Option String := none
  width : Option String := none
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

/-- A control word's effect on a content scan: a datum, a transparent
declaration, or ink. -/
def ctrlEffect (acc : Option String × Nat × Bool × Option String) (n : String) :
    Option String × Nat × Bool × Option String :=
  let (d, k, ink, al) := acc
  match insertDatum n with
  | some dn => (some dn, k + 1, ink, al)
  | none =>
    if n == "par" then acc
    else if n == "raggedright" then (d, k, ink, some "left")
    else if n == "raggedleft" then (d, k, ink, some "right")
    else if n == "centering" then (d, k, ink, some "center")
    else (d, k, true, al)

mutual

/-- What a node's content group sets: `(datum, data count, other ink,
alignment)` — one datum under transparent configuration (spaces, paragraph
ends, a ragged declaration, the breaker's integer parameters), or literal
content. -/
def contentScanList (acc : Option String × Nat × Bool × Option String) :
    List Tok → Option String × Nat × Bool × Option String
  | [] => acc
  | .ctrl n :: .sym '=' :: .num _ :: rest =>
    if breakParams.contains n then contentScanList acc rest
    else
      let (d, k, _, al) := ctrlEffect acc n
      contentScanList (d, k, true, al) rest
  | t :: rest => contentScanList (contentScanOne acc t) rest

def contentScanOne (acc : Option String × Nat × Bool × Option String) :
    Tok → Option String × Nat × Bool × Option String
  | .space => acc
  | .group body => contentScanList acc body
  | .ctrl n => ctrlEffect acc n
  | _ =>
    let (d, k, _, al) := acc
    (d, k, true, al)

end

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
  let some c := coord | return { rd with unread := rd.unread.push "a node not pinned to the page" }
  let some (point, xs, ys) := pagePointOf c
    | return { rd with unread := rd.unread.push "a node not pinned to the page" }
  let some body := content | return { rd with unread := rd.unread.push "a node with no content" }
  if bad || (Ir.BoxPoint.ofName? point).isNone then
    return { rd with unread := rd.unread.push "a node not pinned to the page" }
  let mut n : Node := { datum := none, pagePoint := point, xshift := xs, yshift := ys }
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
  let (datum, count, ink, al) := contentScanList (none, 0, false, none) body
  let aligned := { n with align := n.align <|> al }
  if count == 1 && !ink then
    return { rd with nodes := rd.nodes.push { aligned with datum := datum }, unread := unread
                     fonts := used }
  else if count == 0 then
    return { rd with nodes := rd.nodes.push { aligned with content := srcList body },
                     unread := unread, fonts := used }
  else
    return { rd with unread := unread.push "a node that sets more than one datum" }

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
       | some d => [s!"set = {d}"]
       | none => ["content = {" ++ n.content ++ "}"]) ++
      [s!"anchor = {n.anchor}", s!"at = {n.pagePoint}"] ++
      (n.xshift.map (s!"xshift = {·}")).toList ++
      (n.yshift.map (s!"yshift = {·}")).toList ++
      (n.width.map (s!"width = {·}")).toList ++
      (n.size.map (s!"size = {·}")).toList ++
      (n.innerSep.map (s!"inner-sep = {·}")).toList ++
      (n.align.map (s!"align = {·}")).toList ++
      (if font.isEmpty then [] else ["font = {" ++ font.trimAscii.toString ++ "}"])
    "slot = { " ++ String.intercalate ", " parts ++ " }"
  let style := "\\style{titlepage}{ separator = none" ++
    String.join (rd.nodes.toList.map fun n => ", " ++ slot n) ++ " }"
  palette ++ style

end LeanTex.Core.TitleTemplate
