module

public import LeanTex.Core.Diag
public import LeanTex.Core.Heading
import LeanTex.Core.Loop
import LeanTex.Core.Blank
import LeanTex.Core.Hex
import LeanTex.Core.CiteKey
import LeanTex.Core.CaseFold
import Std.Data.HashMap
public import Std.Data.HashSet

/-! The markdown reader: strict CommonMark [CommonMark] with GFM tables [GFM] into an md AST
carrying `.md` spans, refusing raw HTML outside a closed vocabulary, indented
code and lazy continuation (E0390), and a code file's documentation's dialect. -/

namespace LeanTex.Core.Md

open LeanTex.Core

/-- How a citation names its work: Pandoc's citation modes. -/
public inductive CiteMode where
  /-- `[@key]`: the work inside the citation's brackets. -/
  | normal
  /-- `[-@key]` or `-@key`: the work without its author. -/
  | suppressAuthor
  /-- `@key`: the author in the sentence, the work after it. -/
  | authorInText
  deriving Repr, BEq, DecidableEq, Inhabited

mutual

/-- An inline node; `pos` is its position in the `.md` source. -/
public inductive Inl where
  | text (s : String) (pos : Pos)
  | code (s : String) (pos : Pos)
  | emph (body : Array Inl) (pos : Pos)
  | strong (body : Array Inl) (pos : Pos)
  | link (dest : String) (title : String) (body : Array Inl) (pos : Pos)
  | image (dest : String) (title : String) (alt : Array Inl) (pos : Pos)
  | anchor (key : String) (pos : Pos)
  | soft (pos : Pos)
  | hard (pos : Pos)
  /-- One citation group in Pandoc's syntax: its works in order. -/
  | cite (items : Array CiteItem) (pos : Pos)
  /-- A work cited by the author's own text, doc-gen4's full reference `[text][Key]`. -/
  | citeText (key : String) (body : Array Inl) (pos : Pos)
  /-- A docstring's formula between dollars, md4c's math span: its source as written. -/
  | math (display : Bool) (src : String) (pos : Pos)
  deriving Repr, BEq

/-- One cited work: its key, its mode, and the prefix and suffix written around it. -/
public inductive CiteItem where
  | mk (key : String) (mode : CiteMode) (pre : Array Inl) (post : Array Inl)
  deriving Repr, BEq

end

public instance : Inhabited Inl := ⟨.soft {}⟩

public def CiteItem.key : CiteItem → String
  | .mk k _ _ _ => k

public def CiteItem.mode : CiteItem → CiteMode
  | .mk _ m _ _ => m

public def CiteItem.pre : CiteItem → Array Inl
  | .mk _ _ pre _ => pre

public def CiteItem.post : CiteItem → Array Inl
  | .mk _ _ _ post => post

/-- A metadata value as the reader's YAML subset reads it: a scalar, a sequence of scalars, or a
value outside the subset. -/
public inductive MetaValue where
  | scalar (s : String)
  | list (items : Array String)
  | unread
  deriving Repr, BEq, Inhabited

/-- One top-level key of a metadata block, with its value and the key's position. -/
public structure MetaField where
  key : String
  value : MetaValue
  pos : Pos
  deriving Repr, BEq

/-- A table column's alignment as its GFM delimiter cell spells it. -/
public inductive TableAlign where
  | none
  | left
  | right
  | center
  deriving Repr, BEq, Inhabited

/-- A block node; a list holds one `Array Blk` per item, a
table one cell per column in every row. -/
public inductive Blk where
  | para (body : Array Inl) (pos : Pos)
  | heading (level : Ir.HeadingLevel) (body : Array Inl) (pos : Pos)
  | code (info : String) (text : String) (pos : Pos)
  | rule (pos : Pos)
  | quote (body : Array Blk) (pos : Pos)
  | disclosure (summary : Array Inl) (expanded : Bool) (body : Array Blk) (pos : Pos)
  | list (ordered : Bool) (start : Nat) (tight : Bool) (items : Array (Array Blk))
      (pos : Pos)
  | table (aligns : Array TableAlign) (header : Array (Array Inl))
      (rows : Array (Array (Array Inl))) (pos : Pos)
  /-- A Lean file a fenced `{.lean file="…"}` division includes, with its keys and values. -/
  | lean (attrs : Array (String × String)) (pos : Pos)
  /-- The document's YAML metadata block, as Pandoc reads one: its top-level fields in order. -/
  | metadata (fields : Array MetaField) (pos : Pos)
  /-- Where a `::: {#refs}` division places the reference list: after the division's own blocks. -/
  | refs (pos : Pos)
  deriving Repr, BEq

public instance : Inhabited Blk := ⟨.rule {}⟩

/-- Which markdown a reader reads: a document's strict dialect, or a code file's documentation,
where an indented block is code, a lazy line continues its paragraph and HTML is literal text. -/
public inductive Dialect where
  | document
  | docstring
  deriving Repr, BEq, DecidableEq, Inhabited

def isSpaceOrTab (c : Char) : Bool := c == ' ' || c == '\t'

/-- CommonMark's Unicode whitespace: space, tab, newline,
form feed, carriage return. -/
def isMdSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- ASCII punctuation, the spec's `punctuation` for flanking purposes. -/
def isMdPunct (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".any (· == c)

def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- One source line as characters, with its 1-based line number. -/
structure Line where
  cs : Array Char
  no : Nat
  deriving Inhabited

/-- The reader's line-splitting accumulator. -/
private structure LineAcc where
  out : Array Line
  cur : Array Char
  no : Nat

def splitLines (input : String) : Array Line :=
  let step (a : LineAcc) (c : Char) : LineAcc :=
    if c == '\n' then { out := a.out.push ⟨a.cur, a.no⟩, cur := #[], no := a.no + 1 }
    else if c == '\r' then a
    else { a with cur := a.cur.push c }
  let a := input.foldl step { out := #[], cur := #[], no := 1 }
  if a.cur.isEmpty then a.out else a.out.push ⟨a.cur, a.no⟩

/-- Where the line's content starts and its columns of indent, a tab advancing
to the next multiple of four. -/
def indentAt (cs : Array Char) (from_ : Nat) (col0 : Nat) : Nat × Nat := Id.run do
  let mut i := from_
  let mut col := col0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == ' ' then
        col := col + 1
        i := i + 1
      else if c == '\t' then
        col := col + (4 - col % 4)
        i := i + 1
      else
        return (i, col - col0)
    else
      return (i, col - col0)
  return (i, col - col0)

def isBlankFrom (cs : Array Char) (from_ : Nat) : Bool := Id.run do
  for i in [from_:cs.size] do
    if h : i < cs.size then
      unless isSpaceOrTab cs[i] do return false
  return true

def sliceStr (cs : Array Char) (from_ to_ : Nat) : String := Id.run do
  let mut s := ""
  for i in [from_:min to_ cs.size] do
    if h : i < cs.size then s := s.push cs[i]
  return s

def rstrip (s : String) : String := s.trimAsciiEnd.toString

/-- `#`×1–6 then a space or end of line: the level and the
index past the marker, or `none`. -/
def atxAt (cs : Array Char) (i : Nat) : Option (Ir.HeadingLevel × Nat) := Id.run do
  let mut j := i
  let mut n := 0
  for _ in [0:7] do
    if h : j < cs.size then
      if cs[j] == '#' && n < 7 then
        n := n + 1
        j := j + 1
  let some level := Ir.HeadingLevel.ofRank? n | return none
  match cs[j]? with
  | none => return some (level, j)
  | some c => if isSpaceOrTab c then return some (level, j + 1) else return none

/-- Three or more of one of `* - _`, nothing else but spaces and tabs. -/
def thematicAt (cs : Array Char) (i : Nat) : Bool := Id.run do
  let some c0 := cs[i]? | return false
  unless c0 == '*' || c0 == '-' || c0 == '_' do return false
  let mut n := 0
  for j in [i:cs.size] do
    if h : j < cs.size then
      let c := cs[j]
      if c == c0 then n := n + 1
      else unless isSpaceOrTab c do return false
  return n ≥ 3

/-- A fence: the char, its length, the info string, and the index past it. -/
def fenceAt (cs : Array Char) (i : Nat) : Option (Char × Nat × String) := Id.run do
  let some c0 := cs[i]? | return none
  unless c0 == '`' || c0 == '~' do return none
  let mut n := 0
  let mut j := i
  for _ in [0:cs.size + 1] do
    if h : j < cs.size then
      if cs[j] == c0 then
        n := n + 1
        j := j + 1
  if n < 3 then return none
  let info := (sliceStr cs j cs.size).trimAscii.toString
  -- An info string on a backtick fence may not contain a backtick.
  if c0 == '`' && info.any (· == '`') then return none
  return some (c0, n, info)

/-- At least three colons from `i`: the index past them. -/
def colonsAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    if cs[j]? == some ':' then j := j + 1 else break
  return if j - i ≥ 3 then some j else none

/-- Pandoc's attribute list, `.class #id key=value key="value"`: its classes and its keys with their
values, in order; none where a quote is left open or a word is none of these. -/
def attrsOf (s : String) : Option (Array String × Array (String × String)) := Id.run do
  let mut toks : Array String := #[]
  let mut cur := ""
  let mut quoted := false
  for c in s.toList do
    if quoted then
      cur := cur.push c
      if c == '"' then quoted := false
    else if c == '"' then
      cur := cur.push c
      quoted := true
    else if isSpaceOrTab c then
      unless cur.isEmpty do toks := toks.push cur
      cur := ""
    else cur := cur.push c
  if quoted then return none
  unless cur.isEmpty do toks := toks.push cur
  let mut classes : Array String := #[]
  let mut keys : Array (String × String) := #[]
  for t in toks do
    if t.startsWith "." then classes := classes.push (t.drop 1).toString
    else if !t.startsWith "#" then
      match t.splitOn "=" with
      | k :: rest@(_ :: _) =>
        let v := "=".intercalate rest
        let v := if v.length ≥ 2 && v.startsWith "\"" && v.endsWith "\"" then
          ((v.drop 1).dropEnd 1).toString else v
        keys := keys.push (k, v)
      | _ => return none
  return some (classes, keys)

/-- A Lean inclusion's opening fence: three colons or more, then `{.lean file="…" …}` and nothing
after it; its keys and values. -/
def leanDivAt (cs : Array Char) (i : Nat) : Option (Array (String × String)) := do
  let j ← colonsAt cs i
  let rest := (sliceStr cs j cs.size).trimAscii.toString
  guard (rest.startsWith "{" && rest.endsWith "}")
  let (classes, keys) ← attrsOf ((rest.drop 1).dropEnd 1).toString
  guard (classes.contains "lean" && keys.any (·.1 == "file"))
  return keys

/-- A colon fence alone on its line. -/
def closesDiv (cs : Array Char) (i : Nat) : Bool :=
  match colonsAt cs i with
  | some j => isBlankFrom cs j
  | none => false

/-- Pandoc's reference-list division's opening fence: three colons or more, then an attribute list
holding `#refs` and nothing after it; whether the list holds other attributes too. -/
def refsDivAt (cs : Array Char) (i : Nat) : Option Bool := do
  let j ← colonsAt cs i
  let rest := (sliceStr cs j cs.size).trimAscii.toString
  guard (rest.startsWith "{" && rest.endsWith "}")
  let words := Id.run do
    let mut out : Array String := #[]
    let mut cur := ""
    for ch in ((rest.drop 1).dropEnd 1).toString.toList do
      if isSpaceOrTab ch then
        unless cur.isEmpty do out := out.push cur
        cur := ""
      else cur := cur.push ch
    return if cur.isEmpty then out else out.push cur
  guard (words.contains "#refs")
  return words.size > 1

/-- A YAML flow scalar the metadata reader reads, `none` outside its subset: a quoted scalar with
its escapes, or a plain one with its comment off. -/
def yamlScalar? (s : String) : Option String := Id.run do
  let t := s.trimAscii.toString
  let cs := t.toList.toArray
  match cs[0]? with
  | none => return some ""
  | some '"' =>
    let mut out := ""
    let mut k := 1
    let mut closed := false
    for _ in [0:cs.size + 1] do
      match cs[k]? with
      | none => break
      | some '"' =>
        closed := true
        k := k + 1
        break
      | some '\\' =>
        match cs[k + 1]? with
        | some 'n' => out := out.push '\n'
        | some 't' => out := out.push '\t'
        | some '\\' => out := out.push '\\'
        | some '"' => out := out.push '"'
        | some '/' => out := out.push '/'
        | some ' ' => out := out.push ' '
        | _ => return none
        k := k + 2
      | some ch =>
        out := out.push ch
        k := k + 1
    let tail := (String.ofList (cs.extract k cs.size).toList).trimAscii.toString
    return if closed && (tail.isEmpty || tail.startsWith "#") then some out else none
  | some '\'' =>
    let mut out := ""
    let mut k := 1
    let mut closed := false
    for _ in [0:cs.size + 1] do
      match cs[k]? with
      | none => break
      | some '\'' =>
        if cs[k + 1]? == some '\'' then
          out := out.push '\''
          k := k + 2
        else
          closed := true
          k := k + 1
          break
      | some ch =>
        out := out.push ch
        k := k + 1
    let tail := (String.ofList (cs.extract k cs.size).toList).trimAscii.toString
    return if closed && (tail.isEmpty || tail.startsWith "#") then some out else none
  | some c0 =>
    if "[]{}&*!|>%@`,".any (· == c0) then return none
    if c0 == '-' && (cs[1]?.all isSpaceOrTab) then return none
    -- A plain scalar ends at a comment; `: ` would make it a mapping.
    let mut out := ""
    let mut prev := ' '
    for ch in cs do
      if ch == '#' && isSpaceOrTab prev then break
      if prev == ':' && isSpaceOrTab ch then return none
      out := out.push ch
      prev := ch
    if out.endsWith ":" then return none
    return some out.trimAscii.toString

/-- A YAML flow sequence of scalars on one line, `[a, 'b c', "d"]`; `none` outside the subset. -/
def yamlFlowList? (s : String) : Option (Array String) := Id.run do
  let t := s.trimAscii.toString
  unless t.startsWith "[" && t.endsWith "]" do return none
  let inner := ((t.drop 1).dropEnd 1).toString
  let mut items : Array String := #[]
  let mut cur := ""
  let mut quote : Option Char := none
  for ch in inner.toList do
    match quote with
    | some q =>
      cur := cur.push ch
      if ch == q then quote := none
    | none =>
      if ch == '"' || ch == '\'' then
        quote := some ch
        cur := cur.push ch
      else if ch == '[' || ch == ']' || ch == '{' || ch == '}' then return none
      else if ch == ',' then
        match yamlScalar? cur with
        | some v => items := items.push v
        | none => return none
        cur := ""
      else cur := cur.push ch
  if quote.isSome then return none
  unless cur.trimAscii.isEmpty do
    match yamlScalar? cur with
    | some v => items := items.push v
    | none => return none
  return some items

/-- A line's indentation in spaces, `none` for a line holding a tab before its first character. -/
def yamlIndent (cs : Array Char) : Option Nat := Id.run do
  let mut n := 0
  for ch in cs do
    if ch == ' ' then n := n + 1
    else if ch == '\t' then return none
    else break
  return some n

/-- One metadata value from what follows its key on the key's line and the lines its value holds;
`unread` outside the reader's subset. -/
def yamlValue (inline : String) (body : Array (Array Char)) : MetaValue := Id.run do
  let content := body.filter fun cs => !(isBlankFrom cs 0) &&
    !((sliceStr cs 0 cs.size).trimAscii.startsWith "#")
  let t := inline.trimAscii.toString
  if t.startsWith "|" || t.startsWith ">" then
    let header := (t.drop 1).toString.trimAscii.toString
    unless header.all (fun ch => ch == '-' || ch == '+' || ch.isDigit) do return .unread
    let lines := body.map fun cs => sliceStr cs 0 cs.size
    let ind := (content[0]?.bind yamlIndent).getD 0
    if ind == 0 then return if content.isEmpty then .scalar "" else .unread
    let texts := lines.map fun l => (l.drop ind).toString
    let joined := if t.startsWith "|" then "\n".intercalate texts.toList
      else " ".intercalate (texts.toList.filter (!·.trimAscii.isEmpty))
    return .scalar joined.trimAscii.toString
  if t.isEmpty then
    if content.isEmpty then return .scalar ""
    let mut items : Array String := #[]
    let ind := (content[0]?.bind yamlIndent).getD 0
    for cs in content do
      unless yamlIndent cs == some ind && cs[ind]? == some '-' && (cs[ind + 1]?.all isSpaceOrTab) do
        return .unread
      match yamlScalar? (sliceStr cs (ind + 1) cs.size) with
      | some v => items := items.push v
      | none => return .unread
    return .list items
  if t.startsWith "[" then
    unless content.isEmpty do return .unread
    return match yamlFlowList? t with
      | some items => .list items
      | none => .unread
  match yamlScalar? t with
  | some v =>
    if content.isEmpty then return .scalar v
    if t.startsWith "\"" || t.startsWith "'" then return .unread
    -- A plain scalar folds its more-indented continuation lines.
    let mut out := v
    for cs in content do
      unless (yamlIndent cs).any (· > 0) do return .unread
      match yamlScalar? (sliceStr cs 0 cs.size) with
      | some w => out := out ++ " " ++ w
      | none => return .unread
    return .scalar out
  | none => return .unread

/-- A mapping key at a line's start and the index of the `:` after it: a plain key up to the first
`: `, or a quoted one; `none` where the line opens no key. -/
def yamlKeyAt (cs : Array Char) : Option (String × Nat) := Id.run do
  let q := (cs[0]?).getD ' '
  if q == '"' || q == '\'' then
    let mut k := 1
    let mut close : Option Nat := none
    for _ in [0:cs.size] do
      match cs[k]? with
      | none => break
      | some ch =>
        if q == '"' && ch == '\\' then k := k + 2
        else if ch == q then
          if q == '\'' && cs[k + 1]? == some '\'' then k := k + 2
          else
            close := some k
            break
        else k := k + 1
    let some e := close | return none
    let mut m := e + 1
    for _ in [0:cs.size] do
      if (cs[m]?).any isSpaceOrTab then m := m + 1 else break
    unless cs[m]? == some ':' && (cs[m + 1]?.all isSpaceOrTab) do return none
    return (yamlScalar? (sliceStr cs 0 (e + 1))).bind fun key =>
      if key.isEmpty then none else some (key, m)
  let mut k := 0
  let mut colon : Option Nat := none
  for ch in cs do
    if ch == ':' && (cs[k + 1]?.all isSpaceOrTab) then
      colon := some k
      break
    k := k + 1
  let some c := colon | return none
  let key := (sliceStr cs 0 c).trimAscii.toString
  if key.isEmpty || key.startsWith "-" || key.startsWith "?" then return none
  return some (key, c)

/-- A metadata block's fields, Pandoc's YAML object read over a declared subset: top-level keys,
each with a scalar, a sequence of scalars or an unread value; `none` where the lines hold no
mapping, so they stay markdown. -/
def metaFields (lines : Array Line) : Option (Array MetaField) := Id.run do
  let mut fields : Array MetaField := #[]
  let mut cur : Option (String × String × Pos × Array (Array Char)) := none
  for ln in lines do
    let cs := ln.cs
    let blank := isBlankFrom cs 0
    let comment := (sliceStr cs 0 cs.size).trimAscii.startsWith "#"
    let topLevel := !blank && cs[0]?.any (fun ch => ch != ' ' && ch != '\t')
    let seqItem := cs[0]? == some '-' && (cs[1]?.all isSpaceOrTab)
    if blank || comment || !topLevel || (seqItem && cur.any (·.2.1.trimAscii.isEmpty)) then
      match cur with
      | some (k, v, p, body) => cur := some (k, v, p, body.push cs)
      | none => if blank || comment then continue else return none
      continue
    -- A key line: a plain or a quoted key, then `:` and a space or the line's end.
    let some (key, c) := yamlKeyAt cs | return none
    if let some (k, v, p, body) := cur then
      fields := fields.push { key := k, value := yamlValue v body, pos := p }
    cur := some (key, sliceStr cs (c + 1) cs.size, { line := ln.no, col := 1 }, #[])
  if let some (k, v, p, body) := cur then
    fields := fields.push { key := k, value := yamlValue v body, pos := p }
  return if fields.isEmpty then none else some fields

/-- Whether metadata declares a bibliography: its last `bibliography` key holds a path. -/
public def bibDeclared (fields : Array MetaField) : Bool :=
  match (fields.findRev? (·.key == "bibliography")).map (·.value) with
  | some (MetaValue.scalar v) => !v.trimAscii.isEmpty
  | some (MetaValue.list items) => items.any (!·.trimAscii.isEmpty)
  | _ => false

/-- A metadata block at the document's first line, Pandoc's YAML metadata block: `---`, then no
blank line, the mapping, and `---` or `...`; its fields and the index of the line after it. -/
def metadataAt (lines : Array Line) : Option (Array MetaField × Nat) := do
  let first ← lines[0]?
  guard (rstrip (sliceStr first.cs 0 first.cs.size) == "---")
  let second ← lines[1]?
  guard !(isBlankFrom second.cs 0)
  let closer ← (List.range lines.size).find? fun k => k > 0 &&
    (lines[k]?.any fun l =>
      let t := rstrip (sliceStr l.cs 0 l.cs.size)
      t == "---" || t == "...")
  let fields ← metaFields (lines.extract 1 closer)
  return (fields, closer + 1)

/-- A metadata block closing the document, as Pandoc reads one after a blank line: `---`, no
blank line, the mapping, and `---` or `...` with nothing but blank lines after it; its fields and
the index of its opening line, past `from`. -/
def closingMetadataAt (lines : Array Line) (from_ : Nat) : Option (Array MetaField × Nat) := do
  let fence (k : Nat) : Bool := lines[k]?.any fun l => rstrip (sliceStr l.cs 0 l.cs.size) == "---"
  let blank (k : Nat) : Bool := lines[k]?.all fun l => isBlankFrom l.cs 0
  let last ← (List.range lines.size).reverse.find? (!blank ·)
  guard (lines[last]?.any fun l =>
    let t := rstrip (sliceStr l.cs 0 l.cs.size)
    t == "---" || t == "...")
  let opener ← (List.range last).reverse.find? fence
  guard (opener > from_ && blank (opener - 1) && !blank (opener + 1))
  let fields ← metaFields (lines.extract (opener + 1) last)
  return (fields, opener)

/-- A closing fence for an open one: at most three spaces of indent, the same
char at least as long, nothing after it. -/
def closesFence (cs : Array Char) (ch : Char) (len : Nat) : Bool := Id.run do
  let (i, ind) := indentAt cs 0 0
  if ind > 3 then return false
  let mut n := 0
  let mut j := i
  for _ in [0:cs.size + 1] do
    if h : j < cs.size then
      if cs[j] == ch then
        n := n + 1
        j := j + 1
  if n < len then return false
  return isBlankFrom cs j

/-- A bullet marker: the char and the index past it. -/
def bulletAt (cs : Array Char) (i : Nat) : Option (Char × Nat) := do
  let c ← cs[i]?
  guard (c == '-' || c == '+' || c == '*')
  match cs[i + 1]? with
  | none => some (c, i + 1)
  | some d => if isSpaceOrTab d then some (c, i + 2) else none

/-- An ordered marker: the start number, the delimiter, and
the index past it; at most nine digits. -/
def orderedAt (cs : Array Char) (i : Nat) : Option (Nat × Char × Nat) := Id.run do
  let mut j := i
  let mut n := 0
  let mut digits := 0
  for _ in [0:10] do
    if h : j < cs.size then
      let c := cs[j]
      if isAsciiDigit c && digits < 10 then
        n := n * 10 + (c.toNat - '0'.toNat)
        digits := digits + 1
        j := j + 1
  if digits == 0 || digits > 9 then return none
  let some d := cs[j]? | return none
  unless d == '.' || d == ')' do return none
  match cs[j + 1]? with
  | none => return some (n, d, j + 1)
  | some e => if isSpaceOrTab e then return some (n, d, j + 2) else return none

/-- A setext underline: one run of `=` or of `-`, then only trailing spaces or
tabs; returns the level. -/
def setextAt (cs : Array Char) (i : Nat) : Option Ir.HeadingLevel := Id.run do
  let some c0 := cs[i]? | return none
  unless c0 == '=' || c0 == '-' do return none
  let mut j := i
  for _ in [0:cs.size + 1] do
    if cs[j]? == some c0 then j := j + 1 else break
  unless isBlankFrom cs j do return none
  return some (if c0 == '=' then .h1 else .h2)

/-- Whether the literal's characters stand at `i`, case-folded. -/
def litAtList (cs : Array Char) (i : Nat) : List Char → Bool
  | [] => true
  | c :: rest => (cs[i]?.any fun d => d.toLower == c.toLower) && litAtList cs (i + 1) rest

/-- Is the literal `lit` at `i`, case-folded? -/
def litAt (cs : Array Char) (i : Nat) (lit : String) : Bool := litAtList cs i lit.toList

/-- The index past the first occurrence of `lit` at or after `i`. -/
def findLit (cs : Array Char) (i : Nat) (lit : String) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    if j > cs.size then break
    if litAt cs j lit then return some (j + lit.length)
    j := j + 1
  return none

/-- Whether the consumed span is one comment and nothing else. -/
def commentOnly (cs : Array Char) (start stop : Nat) : Bool :=
  (findLit (cs.extract start stop) 0 "--!>").isNone

/-- The earliest position from which each closing-literal
search is known to fail. -/
structure HtmlMemo where
  noClose : Array (Option Nat) := #[none, none, none, none]
  deriving Inhabited

/-- `findLit`, remembering failure. -/
def findLitM (cs : Array Char) (i : Nat) (k : Nat) (lit : String) (m : HtmlMemo) :
    Option Nat × HtmlMemo :=
  let known : Bool := match m.noClose[k]? with
    | some (some p) => decide (p ≤ i)
    | _ => false
  if known then (none, m)
  else match findLit cs i lit with
    | some e => (some e, m)
    | none => (none, { m with noClose := m.noClose.set! k (some i) })

/-- A tag name: an ASCII letter then letters, digits and `-` (§6.6). -/
def tagNameAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  let some c0 := cs[i]? | return none
  unless isAsciiAlpha c0 do return none
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | some c => if isAsciiAlpha c || isAsciiDigit c || c == '-' then j := j + 1 else break
    | none => break
  return some j

def isAttrStart (c : Char) : Bool := isAsciiAlpha c || c == '_' || c == ':'

def isAttrRest (c : Char) : Bool :=
  isAsciiAlpha c || isAsciiDigit c || c == '_' || c == '.' || c == ':' || c == '-'

/-- A run of whitespace: the index past it. -/
def wsAt (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | some c => if isMdSpace c then j := j + 1 else break
    | none => break
  return j

/-- The characters an unquoted attribute value may not hold (§6.6). -/
def isAttrValueStop (c : Char) : Bool :=
  isMdSpace c || c == '"' || c == '\'' || c == '=' || c == '<' || c == '>' || c == '`'

/-- An attribute value at `i`: quoted or unquoted. -/
def attrValueAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  let some c0 := cs[i]? | return none
  if c0 == '"' || c0 == '\'' then
    let mut j := i + 1
    for _ in [0:cs.size + 1] do
      match cs[j]? with
      | none => return none
      | some c => if c == c0 then return some (j + 1) else j := j + 1
    return none
  if isAttrValueStop c0 then return none
  let mut j := i
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | none => break
    | some c => if isAttrValueStop c then break else j := j + 1
  return some j

/-- One attribute at `i`: its name, lower-cased, and its value as the source
spells it, quotes stripped. -/
def attrAt (cs : Array Char) (i : Nat) : Option ((String × Option String) × Nat) := Id.run do
  let some c0 := cs[i]? | return none
  unless isAttrStart c0 do return none
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | some c => if isAttrRest c then j := j + 1 else break
    | none => break
  let name := (sliceStr cs i j).toLower
  let k := wsAt cs j
  if cs[k]? == some '=' then
    let v := wsAt cs (k + 1)
    match attrValueAt cs v with
    | some e =>
      let quoted := cs[v]? == some '"' || cs[v]? == some '\''
      return some ((name, some (if quoted then sliceStr cs (v + 1) (e - 1) else sliceStr cs v e)), e)
    | none => return some ((name, none), j)
  return some ((name, none), j)

/-- One tag as the §6.6 grammar reads it: name, attributes, whether it
self-closes, and the index past its `>`. -/
structure HtmlTag where
  name : String
  attrs : Array (String × Option String)
  selfClosing : Bool
  stop : Nat

/-- An open tag at `i` (§6.6). -/
def tagAt (cs : Array Char) (i : Nat) : Option HtmlTag := Id.run do
  unless cs[i]? == some '<' do return none
  let some j := tagNameAt cs (i + 1) | return none
  let mut k := j
  let mut attrs : Array (String × Option String) := #[]
  for _ in [0:cs.size + 1] do
    let w := wsAt cs k
    if w == k then break
    match attrAt cs w with
    | some (a, k2) =>
      attrs := attrs.push a
      k := k2
    | none => break
  let e0 := wsAt cs k
  let selfClosing := cs[e0]? == some '/'
  let e := if selfClosing then e0 + 1 else e0
  unless cs[e]? == some '>' do return none
  return some { name := (sliceStr cs (i + 1) j).toLower, attrs, selfClosing, stop := e + 1 }

/-- A closing tag at `i` (§6.6): its name, lower-cased, and
the index past its `>`. -/
def endTagAt (cs : Array Char) (i : Nat) : Option (String × Nat) := do
  guard (cs[i]? == some '<' && cs[i + 1]? == some '/')
  let j ← tagNameAt cs (i + 2)
  let k := wsAt cs j
  guard (cs[k]? == some '>')
  return ((sliceStr cs (i + 2) j).toLower, k + 1)

/-- A complete raw-HTML construct at `i` (§6.6), and the index past it; `none`
means the text is text. -/
def htmlTagAtM (cs : Array Char) (i : Nat) (m : HtmlMemo) : Option Nat × HtmlMemo :=
  if cs[i]? != some '<' then (none, m)
  else match cs[i + 1]? with
    | some '!' =>
      if litAt cs i "<!--" then findLitM cs (i + 2) 0 "-->" m
      else if litAt cs i "<![CDATA[" then findLitM cs (i + 9) 1 "]]>" m
      else if ((cs[i + 2]?).map isAsciiAlpha).getD false then findLitM cs (i + 2) 3 ">" m
      else (none, m)
    | some '?' => findLitM cs (i + 2) 2 "?>" m
    | some '/' => ((endTagAt cs i).map (·.2), m)
    | _ => ((tagAt cs i).map (·.stop), m)

def htmlTagAt (cs : Array Char) (i : Nat) : Option Nat := (htmlTagAtM cs i {}).1

/-- Whether an attribute-free, non-self-closing tag of
exactly `name` stands at `i`. -/
private def bareTagAt (cs : Array Char) (i : Nat) (name : String)
    (closing : Bool := false) : Option Nat :=
  if closing then (endTagAt cs i).bind fun (n, stop) => if n == name then some stop else none
  else (tagAt cs i).bind fun t =>
    if t.name == name && t.attrs.isEmpty && !t.selfClosing then some t.stop else none

/-- The spellings of a disclosure's opening tag the reader accepts: a
non-self-closing `details` with no attribute, or one `open` whose value is
absent, empty or `open` in any case. -/
private def detailsOpen (t : HtmlTag) : Bool :=
  t.name == "details" && !t.selfClosing &&
    match t.attrs.toList with
    | [] => true
    | [(a, v)] => a == "open" && v.all fun s => s.isEmpty || s.toLower == "open"
    | _ => false

/-- The key of an empty target's open tag: an `a` with exactly one `name` or
`id` carrying a value. -/
private def anchorKey? (t : HtmlTag) : Option String :=
  if t.name == "a" && !t.selfClosing then
    match t.attrs.toList with
    | [(attr, some key)] => if attr == "name" || attr == "id" then some key else none
    | _ => none
  else none

/-- A line break as HTML spells one, with no attribute. -/
private def isBr (t : HtmlTag) : Bool := t.name == "br" && t.attrs.isEmpty

theorem litAtList_between {cs : Array Char} :
    ∀ {i : Nat} {l : List Char}, litAtList cs i l = true → i ≤ cs.size →
      i + l.length ≤ cs.size
  | _, [], _, hi => by simpa using hi
  | i, c :: rest, h, _ => by
    simp only [litAtList, Bool.and_eq_true] at h
    obtain ⟨hc, hr⟩ := h
    have hlt : i < cs.size := by
      cases hget : cs[i]? with
      | none => simp [hget] at hc
      | some d => exact (Array.getElem?_eq_some_iff.mp hget).1
    have := litAtList_between hr (by omega)
    simp only [List.length_cons]
    omega

theorem findLit_between {cs : Array Char} {i e : Nat} {lit : String}
    (h : findLit cs i lit = some e) : i + lit.length ≤ e ∧ e ≤ cs.size := by
  unfold findLit at h
  have post : ∀ (st : Option (Option Nat) × Nat),
      (i ≤ st.2 ∧ ∀ r, st.1 = some (some r) → i + lit.length ≤ r ∧ r ≤ cs.size) →
      st.1 = some (some e) → i + lit.length ≤ e ∧ e ≤ cs.size :=
    fun _ hP he => hP.2 e he
  simp only [Id.run_bind] at h
  split at h
  · rename_i r heq
    simp only [Id.run, pure] at h
    subst h
    revert heq
    apply post
    refine Loop.forIn_range_inv (fun (st : Option (Option Nat) × Nat) => i ≤ st.2 ∧
        ∀ r, st.1 = some (some r) → i + lit.length ≤ r ∧ r ≤ cs.size)
      _ _ _ _ ⟨Nat.le_refl _, by simp⟩ ?_
    intro _ _ _ st hst
    split
    · exact ⟨hst.1, fun r hr => by simp [ForInStep.value] at hr⟩
    · split
      · rename_i hj hl
        refine ⟨hst.1, fun r' hr' => ?_⟩
        simp only [Id.run_pure, ForInStep.value, Option.some.injEq] at hr'
        subst hr'
        have := litAtList_between hl (by omega)
        rw [String.length_toList] at this
        exact ⟨by omega, this⟩
      · exact ⟨(by omega : i ≤ st.2 + 1), fun r hr => by simp [ForInStep.value] at hr⟩
  · simp [Id.run, pure] at h

theorem findLitM_between {cs : Array Char} {i k e : Nat} {lit : String} {m m' : HtmlMemo}
    (h : findLitM cs i k lit m = (some e, m')) : i + lit.length ≤ e ∧ e ≤ cs.size := by
  apply findLit_between
  unfold findLitM at h
  cases hf : findLit cs i lit with
  | none => simp only [hf] at h; split at h <;> (try split at h) <;> simp at h
  | some e' => simp only [hf] at h; split at h <;> (try split at h) <;> simp_all

theorem wsAt_between (cs : Array Char) (i : Nat) :
    i ≤ wsAt cs i ∧ wsAt cs i ≤ max i cs.size := by
  unfold wsAt
  simp only [Id.run_bind]
  refine Loop.forIn_range_inv (fun j => i ≤ j ∧ j ≤ max i cs.size) _ _ _ _
    ⟨Nat.le_refl _, Nat.le_max_left _ _⟩ ?_
  intro _ _ _ j hj
  split
  · rename_i c hc
    have : j < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
    split
    · exact ⟨(by omega : i ≤ j + 1), (by omega : j + 1 ≤ max i cs.size)⟩
    · exact hj
  · exact hj

theorem tagNameAt_between {cs : Array Char} {i j : Nat} (h : tagNameAt cs i = some j) :
    i < j ∧ j ≤ cs.size := by
  unfold tagNameAt at h
  split at h
  · rename_i c0 hc0
    have hi : i < cs.size := (Array.getElem?_eq_some_iff.mp hc0).1
    split at h
    · simp only [Id.run_bind] at h
      cases h
      have weaken : ∀ x, i + 1 ≤ x ∧ x ≤ cs.size → i < x ∧ x ≤ cs.size :=
        fun x hx => ⟨by omega, hx.2⟩
      apply weaken
      refine Loop.forIn_range_inv (fun j => i + 1 ≤ j ∧ j ≤ cs.size) _ _ _ _
        ⟨Nat.le_refl _, hi⟩ ?_
      intro _ _ _ b hb
      split
      · rename_i c hc
        have : b < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
        split
        · exact ⟨(by omega : i + 1 ≤ b + 1), (by omega : b + 1 ≤ cs.size)⟩
        · exact hb
      · exact hb
    · simp at h
  · simp at h

theorem attrValueAt_between {cs : Array Char} {i e : Nat} (h : attrValueAt cs i = some e) :
    i ≤ e ∧ e ≤ cs.size := by
  unfold attrValueAt at h
  split at h
  · rename_i c0 hc0
    have hi : i < cs.size := (Array.getElem?_eq_some_iff.mp hc0).1
    split at h
    · simp only [Id.run_bind] at h
      generalize hst : (forIn (m := Id) [0:cs.size + 1]
        ((none : Option (Option Nat)), i + 1) _).run = st at h
      have hP : i + 1 ≤ st.2 ∧ ∀ r, st.1 = some (some r) → i ≤ r ∧ r ≤ cs.size := by
        rw [← hst]
        refine Loop.forIn_range_inv (fun (st : Option (Option Nat) × Nat) => i + 1 ≤ st.2 ∧
          ∀ r, st.1 = some (some r) → i ≤ r ∧ r ≤ cs.size) _ _ _ _ ⟨Nat.le_refl _, by simp⟩ ?_
        intro _ _ _ st hst
        split
        · exact ⟨hst.1, fun r hr => by simp [ForInStep.value] at hr⟩
        · rename_i c hc
          have : st.2 < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
          split
          · refine ⟨hst.1, fun r hr => ?_⟩
            simp only [Id.run_pure, ForInStep.value, Option.some.injEq] at hr
            exact ⟨by omega, by omega⟩
          · exact ⟨(by omega : i + 1 ≤ st.2 + 1), fun r hr => by simp [ForInStep.value] at hr⟩
      split at h
      · rename_i r heq
        simp only [Id.run_pure] at h
        subst h
        exact hP.2 e heq
      · simp at h
    · split at h
      · simp at h
      · simp only [Id.run_bind] at h
        generalize hj : (forIn (m := Id) [0:cs.size + 1] i _).run = j at h
        have hP : i ≤ j ∧ j ≤ cs.size := by
          rw [← hj]
          refine Loop.forIn_range_inv (fun j => i ≤ j ∧ j ≤ cs.size) _ _ _ _
            ⟨Nat.le_refl _, Nat.le_of_lt hi⟩ ?_
          intro _ _ _ b hb
          split
          · exact hb
          · rename_i c hc
            have : b < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
            split
            · exact hb
            · exact ⟨(by omega : i ≤ b + 1), (by omega : b + 1 ≤ cs.size)⟩
        simp only [Id.run_pure, Option.some.injEq] at h
        subst h
        exact hP
  · simp at h

theorem attrAt_between {cs : Array Char} {i e : Nat} {a : String × Option String}
    (h : attrAt cs i = some (a, e)) : i < e ∧ e ≤ cs.size := by
  unfold attrAt at h
  split at h
  · rename_i c0 hc0
    have hi : i < cs.size := (Array.getElem?_eq_some_iff.mp hc0).1
    split at h
    · simp only [Id.run_bind] at h
      generalize hj : (forIn (m := Id) [0:cs.size + 1] (i + 1) _).run = j at h
      have hP : i + 1 ≤ j ∧ j ≤ cs.size := by
        rw [← hj]
        refine Loop.forIn_range_inv (fun j => i + 1 ≤ j ∧ j ≤ cs.size) _ _ _ _
          ⟨Nat.le_refl _, hi⟩ ?_
        intro _ _ _ b hb
        split
        · rename_i c hc
          have : b < cs.size := (Array.getElem?_eq_some_iff.mp hc).1
          split
          · exact ⟨(by omega : i + 1 ≤ b + 1), (by omega : b + 1 ≤ cs.size)⟩
          · exact hb
        · exact hb
      split at h
      · split at h
        · rename_i e' he'
          simp only [Id.run_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have hv := attrValueAt_between he'
          have hk := wsAt_between cs j
          have hv0 := wsAt_between cs (wsAt cs j + 1)
          exact ⟨by omega, hv.2⟩
        · simp only [Id.run_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨by omega, hP.2⟩
      · simp only [Id.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨by omega, hP.2⟩
    · simp at h
  · simp at h

theorem tagAt_between {cs : Array Char} {i : Nat} {t : HtmlTag} (h : tagAt cs i = some t) :
    i < t.stop ∧ t.stop ≤ cs.size := by
  unfold tagAt at h
  split at h
  · split at h
    · rename_i j hj
      have hjb := tagNameAt_between hj
      simp only [Id.run_bind] at h
      generalize hst : (forIn (m := Id) [0:cs.size + 1]
        (j, (#[] : Array (String × Option String))) _).run = st at h
      have hP : j ≤ st.1 := by
        rw [← hst]
        refine Loop.forIn_range_inv (fun (st : Nat × Array (String × Option String)) => j ≤ st.1)
          _ _ _ _ (Nat.le_refl _) ?_
        intro _ _ _ st hst
        split
        · exact hst
        · split
          · rename_i a k2 hk2
            have := attrAt_between hk2
            have := wsAt_between cs st.1
            exact (by omega : j ≤ k2)
          · exact hst
      have he0 := wsAt_between cs st.1
      split at h
      all_goals
        split at h
        · rename_i hgt
          have := (Array.getElem?_eq_some_iff.mp (beq_iff_eq.mp hgt)).1
          simp only [Id.run_pure, Option.some.injEq] at h
          subst h
          dsimp only
          omega
        · simp at h
    · simp at h
  · simp at h

theorem endTagAt_between {cs : Array Char} {i : Nat} {n : String} {stop : Nat}
    (h : endTagAt cs i = some (n, stop)) : i < stop ∧ stop ≤ cs.size := by
  unfold endTagAt at h
  cases hj : tagNameAt cs (i + 2) with
  | none => simp [hj] at h
  | some j =>
    have hjb := tagNameAt_between hj
    have hk := wsAt_between cs j
    simp only [hj] at h
    by_cases hc : cs[i]? = some '<' ∧ cs[i + 1]? = some '/'
    · by_cases hg : cs[wsAt cs j]? = some '>'
      · simp [guard, hc, hg] at h
        obtain ⟨_, rfl⟩ := h
        have := (Array.getElem?_eq_some_iff.mp hg).1
        omega
      · simp [guard, hc, hg, failure] at h
    · simp [guard, hc, failure] at h

theorem htmlTagAtM_between {cs : Array Char} {i next : Nat} {m m' : HtmlMemo}
    (h : htmlTagAtM cs i m = (some next, m')) : i < next ∧ next ≤ cs.size := by
  unfold htmlTagAtM at h
  split at h
  · simp at h
  · split at h
    · split at h
      · have := findLitM_between h
        have hl : "-->".length = 3 := rfl
        omega
      · split at h
        · have := findLitM_between h
          have hl : "]]>".length = 3 := rfl
          omega
        · split at h
          · have := findLitM_between h
            have hl : ">".length = 1 := rfl
            omega
          · simp at h
    · have := findLitM_between h
      have hl : "?>".length = 2 := rfl
      omega
    · simp only [Prod.mk.injEq] at h
      cases he : endTagAt cs i with
      | none => simp [he] at h
      | some r =>
        obtain ⟨n, stop⟩ := r
        simp [he] at h
        obtain ⟨rfl, _⟩ := h
        exact endTagAt_between he
    · simp only [Prod.mk.injEq] at h
      cases ht : tagAt cs i with
      | none => simp [ht] at h
      | some t =>
        simp [ht] at h
        obtain ⟨rfl, _⟩ := h
        exact tagAt_between ht

theorem htmlTagAtM_tag_exact {cs : Array Char} {i : Nat} {m : HtmlMemo}
    (h : cs[i]? = some '<') (hb : cs[i + 1]? ≠ some '!') (hq : cs[i + 1]? ≠ some '?') :
    (htmlTagAtM cs i m).1 =
      if cs[i + 1]? = some '/' then (endTagAt cs i).map (·.2) else (tagAt cs i).map (·.stop) := by
  unfold htmlTagAtM
  simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i heq; exact absurd heq hb
  · rename_i heq; exact absurd heq hq
  · rename_i heq; simp [heq]
  · rename_i _ _ hs
    split
    · rename_i hc; exact absurd hc hs
    · rfl

/-- The tag names §4.6 condition 1 names, whose block runs to a closing tag. -/
def htmlRawTags : List String := ["pre", "script", "style", "textarea"]

/-- The block-level tag names §4.6 condition 6 names. -/
def htmlBlockTags : List String :=
  ["address", "article", "aside", "base", "basefont", "blockquote", "body",
   "caption", "center", "col", "colgroup", "dd", "details", "dialog", "dir",
   "div", "dl", "dt", "fieldset", "figcaption", "figure", "footer", "form",
   "frame", "frameset", "h1", "h2", "h3", "h4", "h5", "h6", "head", "header",
   "hr", "html", "iframe", "legend", "li", "link", "main", "menu", "menuitem",
   "nav", "noframes", "ol", "optgroup", "option", "p", "param", "search",
   "section", "summary", "table", "tbody", "td", "tfoot", "th", "thead",
   "title", "tr", "track", "ul"]

/-- Whether a tag name drawn from `names` stands at `i`. -/
private def namedTagAt (cs : Array Char) (i : Nat) (names : List String) : Bool :=
  match tagNameAt cs i with
  | none => false
  | some j =>
    let nm := (sliceStr cs i j).toLower
    names.contains nm &&
      (match cs[j]? with
       | none => true
       | some c => isMdSpace c || c == '>' || (c == '/' && cs[j + 1]? == some '>'))

/-- Whether an HTML block of §4.6's sixth condition opens at
`i` with the tag `name`. -/
def blockTagStartsAt (cs : Array Char) (i : Nat) (name : String) : Bool :=
  cs[i]? == some '<' &&
    (namedTagAt cs (i + 1) [name] || (cs[i + 1]? == some '/' && namedTagAt cs (i + 2) [name]))

/-- How an HTML block ends (§4.6): at a line holding one of
these literals, or at a blank line. -/
inductive HtmlEnd where
  | lit (ends : List String)
  | blank
  deriving Repr, Inhabited

/-- The HTML block starting at `i`, by §4.6 condition: how it ends, and whether
it may interrupt a paragraph. -/
def htmlBlockKind (cs : Array Char) (i : Nat) : Option (HtmlEnd × Bool) := Id.run do
  unless cs[i]? == some '<' do return none
  if namedTagAt cs (i + 1) htmlRawTags then
    return some (.lit ["</pre>", "</script>", "</style>", "</textarea>"], true)
  if litAt cs i "<!--" then return some (.lit ["-->"], true)
  if litAt cs i "<?" then return some (.lit ["?>"], true)
  if litAt cs i "<![CDATA[" then return some (.lit ["]]>"], true)
  if cs[i + 1]? == some '!' && ((cs[i + 2]?).map isAsciiAlpha).getD false then
    return some (.lit [">"], true)
  if namedTagAt cs (i + 1) htmlBlockTags then return some (.blank, true)
  if cs[i + 1]? == some '/' && namedTagAt cs (i + 2) htmlBlockTags then
    return some (.blank, true)
  match htmlTagAt cs i with
  | some j => if isBlankFrom cs j then return some (.blank, false) else return none
  | none => return none

/-- Whether a line, from `i`, holds an end literal of its HTML block. -/
def htmlEndsIn (cs : Array Char) (i : Nat) (e : HtmlEnd) : Bool := Id.run do
  match e with
  | .blank => return false
  | .lit ends =>
    for k in [i:cs.size] do
      if ends.any (litAt cs k ·) then return true
    return false

/-- Whether an HTML block that may interrupt a paragraph,
conditions 1–6, starts at `i`. -/
def htmlBlockInterruptAt (cs : Array Char) (i : Nat) : Bool :=
  match htmlBlockKind cs i with
  | some (_, interrupts) => interrupts
  | none => false

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-- One inline token; a `run` is a delimiter run of `*` or
`_` with its flanking verdicts. -/
inductive ITok where
  | txt (s : String) (pos : Pos)
  | code (s : String) (pos : Pos)
  | soft (pos : Pos)
  | hard (pos : Pos)
  | auto (dest : String) (text : String) (pos : Pos)
  | anchor (key : String) (pos : Pos)
  | run (ch : Char) (len : Nat) (canOpen canClose : Bool) (pos : Pos)
  | bopen (image : Bool) (pos : Pos)
  | bclose (pos : Pos)
  /-- An author-in-text citation's key, its citation in the scan's citation pairs. -/
  | ckey (pos : Pos)
  /-- A run of one or two dollars that may open or close a docstring's math span, at its index. -/
  | dollar (len : Nat) (canOpen canClose : Bool) (at_ : Nat) (pos : Pos)
  deriving Repr

instance : Inhabited ITok := ⟨.soft {}⟩

def ITok.pos : ITok → Pos
  | .txt _ p | .code _ p | .soft p | .hard p | .auto _ _ p
  | .anchor _ p | .run _ _ _ _ p | .bopen _ p | .bclose p | .ckey p | .dollar _ _ _ _ p => p

/-- A resolved link or image: its bracket token indices, whether it is an image,
and its destination and title. -/
structure BPair where
  openTok : Nat
  closeTok : Nat
  image : Bool
  dest : String
  title : String
  deriving Inhabited, Repr

/-- One matched emphasis pair: the runs it joins, the delimiters it takes from
each, and its creation order. -/
structure EPair where
  openTok : Nat
  closeTok : Nat
  strong : Bool
  born : Nat
  deriving Inhabited, Repr

/-- The characters of an inline stretch, each with the `.md`
position it came from. -/
structure Chars where
  cs : Array Char
  ps : Array Pos
  deriving Inhabited

def Chars.size (c : Chars) : Nat := c.cs.size

def Chars.at? (c : Chars) (i : Nat) : Option Char := c.cs[i]?

def Chars.posAt (c : Chars) (i : Nat) : Pos := (c.ps[i]?).getD {}

def Chars.str (c : Chars) (from_ to_ : Nat) : String := Id.run do
  let mut s := ""
  for i in [from_:min to_ c.cs.size] do
    if h : i < c.cs.size then s := s.push c.cs[i]
  return s

/-- A delimiter run's flanking verdicts (CommonMark §6.2). -/
def flanking (before after : Option Char) : Bool × Bool :=
  let wsBefore := (before.map isMdSpace).getD true
  let wsAfter := (after.map isMdSpace).getD true
  let puBefore := (before.map isMdPunct).getD false
  let puAfter := (after.map isMdPunct).getD false
  let left := !wsAfter && (!puAfter || wsBefore || puBefore)
  let right := !wsBefore && (!puBefore || wsAfter || puAfter)
  (left, right)

/-- TeX's special characters, whose escape stays TeX's where a text is TeX. -/
def texSpecial (c : Char) : Bool := "\\{}$&#^_~%".contains c

/-- An ASCII-punctuation backslash escape, or `none` where
the backslash is literal. -/
def escaped? (c : Chars) (i : Nat) : Option Char := do
  guard (c.at? i == some '\\')
  let d ← c.at? (i + 1)
  guard (isMdPunct d)
  some d

/-- The run of dollars at `i`: its length, or 0. -/
def dollarRun (c : Chars) (i : Nat) : Nat := Id.run do
  let mut n := 0
  for _ in [0:c.size + 1] do
    if c.at? (i + n) == some '$' then n := n + 1 else break
  return n

/-- A backtick string at `i`: its length, or 0. -/
def tickRun (c : Chars) (i : Nat) : Nat := Id.run do
  let mut n := 0
  let mut j := i
  for _ in [0:c.size + 1] do
    if c.at? j == some '`' then
      n := n + 1
      j := j + 1
    else break
  return n

/-- Every maximal backtick string of a stretch, as start
positions grouped by length. -/
def tickIndex (c : Chars) : Std.HashMap Nat (Array Nat) := Id.run do
  let mut m : Std.HashMap Nat (Array Nat) := {}
  let mut i := 0
  for _ in [0:c.size + 1] do
    if i ≥ c.size then break
    if c.at? i == some '`' then
      let n := tickRun c i
      let starts := m.getD n #[]
      m := (m.erase n).insert n (starts.push i)
      i := i + n
    else i := i + 1
  return m

/-- The first element of a sorted array at or above `x`. -/
def firstAtLeast (a : Array Nat) (x : Nat) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    if (a[mid]?).getD 0 < x then lo := mid + 1 else hi := mid
  return a[lo]?

/-- A code span opening at `i` with a backtick string of length `n`: the content
and the index past its closer, or `none`. -/
def codeSpanAt (c : Chars) (idx : Std.HashMap Nat (Array Nat)) (i n : Nat) :
    Option (String × Nat) := do
  let j ← firstAtLeast (idx.getD n #[]) (i + n)
  -- Strip one space from each end when both are present and the content is not all spaces.
  let raw := (c.str (i + n) j).toList
  let stripped :=
    if raw.length ≥ 2 && raw.headD 'x' == ' ' && raw.getLastD 'x' == ' '
        && !(raw.all (· == ' ')) then
      (raw.drop 1).dropLast
    else raw
  -- Line endings inside a code span are spaces.
  some (String.ofList (stripped.map (fun ch => if ch == '\n' then ' ' else ch)), j + n)

/-- A run of whitespace in an inline stretch: the index past it. -/
def Chars.ws (c : Chars) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:c.size + 1] do
    if (c.at? j).map isMdSpace == some true then j := j + 1 else break
  return j

/-- An autolink `<scheme:...>` or `<local@domain>` at `i`: the destination, the
link text, and the index past `>`. -/
def autolinkAt (c : Chars) (i : Nat) : Option (String × String × Nat) := Id.run do
  unless c.at? i == some '<' do return none
  let mut j := i + 1
  for _ in [0:c.size + 1] do
    match c.at? j with
    | none => return none
    | some '>' =>
      let body := c.str (i + 1) j
      if body.isEmpty then return none
      -- An absolute URI: a scheme of letters, digits, `+`, `.`, `-`
      -- followed by `:`; no spaces or `<` inside.
      if body.any (fun ch => isMdSpace ch || ch == '<') then return none
      let parts := body.splitOn ":"
      if parts.length ≥ 2 && !(parts.headD "").isEmpty
          && isAsciiAlpha ((parts.headD " ").toList.headD ' ')
          && (parts.headD "").all (fun ch =>
                isAsciiAlpha ch || isAsciiDigit ch || ch == '+' || ch == '.' || ch == '-') then
        return some (body, body, j + 1)
      -- An email autolink: exactly one `@`, and a dot in the domain.
      let atParts := body.splitOn "@"
      if atParts.length == 2 && !(atParts.headD "").isEmpty
          && ((atParts.getLastD "").splitOn ".").length ≥ 2 then
        return some ("mailto:" ++ body, body, j + 1)
      return none
    | some ch =>
      -- No whitespace, control character or `<` inside an autolink (§6.5).
      if isMdSpace ch || ch == '<' || ch.toNat < 0x20 then return none
      j := j + 1
  return none

/-- A link destination and optional title starting at `(`: the destination, the
title, and the index past `)`. -/
def linkTailAt (c : Chars) (i : Nat) : Option (String × String × Nat) := Id.run do
  unless c.at? i == some '(' do return none
  let mut j := c.ws (i + 1)
  let mut dest := ""
  if c.at? j == some '<' then
    let mut k := j + 1
    let mut closed := false
    for _ in [0:c.size + 1] do
      match c.at? k with
      | none => return none
      | some '>' =>
        closed := true
        break
      | some '\n' => return none
      | some '<' => return none
      | some ch =>
        if ch == '\\' then
          match escaped? c k with
          | some d =>
            dest := dest.push d
            k := k + 1
          | none => dest := dest.push ch
        else
          dest := dest.push ch
        k := k + 1
    unless closed do return none
    j := k + 1
  else
    let mut depth := 0
    let mut k := j
    for _ in [0:c.size + 1] do
      match c.at? k with
      | none => break
      | some ch =>
        if isMdSpace ch || ch.toNat < 0x20 then break
        else if ch == '(' then
          depth := depth + 1
          if depth > 32 then return none
          dest := dest.push ch
          k := k + 1
        else if ch == ')' then
          if depth == 0 then break
          else
            depth := depth - 1
            dest := dest.push ch
            k := k + 1
        else if ch == '\\' then
          match escaped? c k with
          | some d =>
            dest := dest.push d
            k := k + 2
          | none =>
            dest := dest.push ch
            k := k + 1
        else
          dest := dest.push ch
          k := k + 1
    j := k
  j := c.ws j
  let mut title := ""
  match c.at? j with
  | some q =>
    if q == '"' || q == '\'' || q == '(' then
      let close := if q == '(' then ')' else q
      let mut k := j + 1
      let mut closed := false
      for _ in [0:c.size + 1] do
        match c.at? k with
        | none => break
        | some ch =>
          if ch == close then
            closed := true
            k := k + 1
            break
          else if q == '(' && ch == '(' then
            -- An unescaped `(` inside a parenthesized title is not a title.
            return none
          else if ch == '\\' then
            match escaped? c k with
            | some d =>
              title := title.push d
              k := k + 2
            | none =>
              title := title.push ch
              k := k + 1
          else
            title := title.push ch
            k := k + 1
      unless closed do return none
      j := k
  | none => pure ()
  j := c.ws j
  unless c.at? j == some ')' do return none
  return some (dest, title, j + 1)

/-- Named and numeric character references (§2.5): the five named ones the
engine needs and the numeric forms. -/
def entityAt (c : Chars) (i : Nat) : Option (String × Nat) := Id.run do
  unless c.at? i == some '&' do return none
  let mut j := i + 1
  let mut body := ""
  for _ in [0:34] do
    match c.at? j with
    | some ';' => break
    | some ch =>
      body := body.push ch
      j := j + 1
    | none => break
  unless c.at? j == some ';' do return none
  let named : List (String × String) :=
    [("amp", "&"), ("lt", "<"), ("gt", ">"), ("quot", "\""), ("apos", "'"),
     ("nbsp", "\u00a0"), ("copy", "\u00a9"), ("auml", "\u00e4"),
     ("ouml", "\u00f6"), ("uuml", "\u00fc"), ("szlig", "\u00df"),
     ("Dagger", "\u2021"), ("dagger", "\u2020"), ("hellip", "\u2026"),
     ("mdash", "\u2014"), ("ndash", "\u2013"), ("ouml;", "\u00f6")]
  if let some (_, v) := named.find? (·.1 == body) then
    return some (v, j + 1)
  match body.toList with
  | '#' :: rest =>
    let hex := rest.headD ' ' == 'x' || rest.headD ' ' == 'X'
    let ds := if hex then rest.drop 1 else rest
    if ds.isEmpty || ds.length > 7 then return none
    let mut n := 0
    for ch in ds do
      let d :=
        if hex then Hex.digit? ch
        else if isAsciiDigit ch then some (ch.toNat - '0'.toNat)
        else none
      match d with
      | none => return none
      | some d => n := n * (if hex then 16 else 10) + d
    -- A null or out-of-range code point is replaced (§2.3, §2.5).
    let cp := if n == 0 || n > 0x10ffff || (n ≥ 0xd800 && n ≤ 0xdfff) then 0xfffd else n
    return some (String.singleton (Char.ofNat cp), j + 1)
  | _ => return none

/-- A link reference definition's destination and title (§4.7). -/
structure LinkDef where
  dest : String
  title : String
  deriving Inhabited, BEq, Repr

/-- A label as links match it (§4.7): case-folded, each run of spaces, tabs and line endings one
space, trimmed. -/
def normLabel (s : String) : String := Id.run do
  let mut out := ""
  let mut gap := false
  for ch in (CaseFold.fold s).toList do
    if isMdSpace ch then gap := true
    else
      if gap && !out.isEmpty then out := out.push ' '
      gap := false
      out := out.push ch
  return out

/-- A link label at `i` (§4.7): its source between the brackets, at most 999 characters, not
blank and holding no unescaped bracket, and the index past its `]`. -/
def labelAt (c : Chars) (i : Nat) : Option (String × Nat) := Id.run do
  unless c.at? i == some '[' do return none
  let mut j := i + 1
  let mut blank := true
  for _ in [0:1000] do
    if j - (i + 1) > 999 then return none
    match c.at? j with
    | none => return none
    | some ']' => return if blank then none else some (c.str (i + 1) j, j + 1)
    | some '[' => return none
    | some '\\' =>
      blank := false
      j := j + (if (c.at? (j + 1)).isSome then 2 else 1)
    | some ch =>
      unless isMdSpace ch do blank := false
      j := j + 1
  return none

/-- The text from `a` to `b` with its backslash escapes and character references read (§2.4, §2.5). -/
def unescapeSpan (c : Chars) (a b : Nat) : String := Id.run do
  let mut out := ""
  let mut j := a
  for _ in [0:b - a + 1] do
    if j ≥ b then break
    match (if j + 1 < b then escaped? c j else none) with
    | some d =>
      out := out.push d
      j := j + 2
    | none =>
      match (if c.at? j == some '&' then entityAt c j else none) with
      | some (v, next) =>
        if next ≤ b then
          out := out ++ v
          j := next
        else
          out := out.push '&'
          j := j + 1
      | none =>
        out := out.push ((c.at? j).getD ' ')
        j := j + 1
  return out

/-- A link destination at `i` (§6.3): `<…>` holding no line ending or unescaped angle bracket, or
a nonempty run holding no space or control character whose unescaped parentheses balance; its
text and the index past it. -/
def destAt (c : Chars) (i : Nat) : Option (String × Nat) := Id.run do
  if c.at? i == some '<' then
    let mut j := i + 1
    for _ in [0:c.size + 1] do
      match c.at? j with
      | none | some '\n' | some '<' => return none
      | some '>' => return some (unescapeSpan c (i + 1) j, j + 1)
      | some _ => j := j + (if (escaped? c j).isSome then 2 else 1)
    return none
  let mut j := i
  let mut depth := 0
  for _ in [0:c.size + 1] do
    match c.at? j with
    | none => break
    | some ch =>
      if ch == ' ' || ch.toNat < 0x20 || ch.toNat == 0x7f then break
      else if (escaped? c j).isSome then j := j + 2
      else if ch == '(' then
        depth := depth + 1
        j := j + 1
      else if ch == ')' then
        if depth == 0 then break
        depth := depth - 1
        j := j + 1
      else j := j + 1
  if j == i || depth != 0 then return none
  return some (unescapeSpan c i j, j)

/-- A link title at `i` (§6.3): `"…"`, `'…'` or `(…)`, holding no unescaped closer, nor an
unescaped `(` in the third; its text and the index past it. -/
def titleAt (c : Chars) (i : Nat) : Option (String × Nat) := Id.run do
  let some q := c.at? i | return none
  unless q == '"' || q == '\'' || q == '(' do return none
  let close := if q == '(' then ')' else q
  let mut j := i + 1
  for _ in [0:c.size + 1] do
    match c.at? j with
    | none => return none
    | some ch =>
      if (escaped? c j).isSome then j := j + 2
      else if ch == close then return some (unescapeSpan c (i + 1) j, j + 1)
      else if q == '(' && ch == '(' then return none
      else j := j + 1
  return none

/-- The index past Pandoc's `spnl` from `i`: spaces, at most one line ending and spaces, and never
into a blank line. -/
def spnlEnd (c : Chars) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut broke := false
  for _ in [0:c.size + 1] do
    match c.at? j with
    | some ' ' | some '\t' => j := j + 1
    | some '\n' =>
      if broke then break
      broke := true
      j := j + 1
    | _ => break
  return j

/-- The index past the line ending `i` stands before, past spaces and tabs only; the text's end
counts as one. -/
def lineEndAfter (c : Chars) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:c.size + 1] do
    match c.at? j with
    | none => return some j
    | some '\n' => return some (j + 1)
    | some ' ' | some '\t' => j := j + 1
    | some _ => return none
  return none

/-- A link reference definition at `i`, which opens a line of a paragraph's text (§4.7): its
label, destination and title, and the index past the line it ends on; a title past which the line
goes on leaves the definition its destination alone where that ends its line. -/
def linkDefAt (c : Chars) (i : Nat) : Option (String × LinkDef × Nat) := do
  let (label, j) ← labelAt c i
  guard (c.at? j == some ':')
  let (dest, d) ← destAt c (spnlEnd c (j + 1))
  let titled : Option (String × Nat) := do
    let t := spnlEnd c d
    guard (t > d)
    let (title, e) ← titleAt c t
    let f ← lineEndAfter c e
    pure (title, f)
  match titled with
  | some (title, f) => pure (label, { dest, title }, f)
  | none =>
    let f ← lineEndAfter c d
    pure (label, { dest, title := "" }, f)

/-- A work cited by the author's text, doc-gen4's `[text][Key]`: the text's tokens, the key, and
the text's characters. -/
structure ShownRef where
  openTok : Nat
  closeTok : Nat
  key : String
  textFrom : Nat
  textTo : Nat
  pos : Pos

/-- What a scan knows where a citation may open: the indices just past an emphasis run that
closes one the text opened, and just past a citation key, and each braced key's closing brace by
its opening one's index. -/
structure CiteScan where
  closers : Std.HashSet Nat
  keyEnds : Std.HashSet Nat
  braces : Std.HashMap Nat Nat

/-- Each `{` whose balanced `}` the same run of non-space characters holds, by its index: a braced
citation key's braces, matched in one pass. -/
def braceMatches (c : Chars) : Std.HashMap Nat Nat := Id.run do
  let mut out : Std.HashMap Nat Nat := {}
  let mut stack : Array Nat := #[]
  for k in [0:c.size] do
    match c.at? k with
    | some '{' => stack := stack.push k
    | some '}' =>
      if let some o := stack.back? then
        out := out.insert o k
        stack := stack.pop
    | some ch => if isMdSpace ch then stack := #[]
    | none => pure ()
  return out

/-- Whether a citation may open at `i`, Pandoc's `notAfterString`: not after a letter, a digit or
a `.` of a word, nor after an emphasis run that closes, but after another citation's key. -/
def citeMayOpen (c : Chars) (s : CiteScan) (i : Nat) : Bool :=
  if s.keyEnds.contains i then true
  else if s.closers.contains i then false
  else match (if i == 0 then none else c.at? (i - 1)) with
    | none => true
    | some p =>
      -- Smart typography reads `...` as an ellipsis, which no word holds.
      let ellipsis := p == '.' && i ≥ 3 && c.at? (i - 2) == some '.' && c.at? (i - 3) == some '.'
      !(CiteKey.isAlnum p || (p == '.' && !ellipsis))

/-- A citation key at `i`, Pandoc's `citeKey`: whether a `-` before the `@`, outside a dash run,
suppresses the author, the key without its braces, and the index past it. -/
def citeKeyAt (c : Chars) (s : CiteScan) (i : Nat) : Option (Bool × String × Nat) := Id.run do
  unless citeMayOpen c s i do return none
  let dash := c.at? i == some '-'
  if dash && i > 0 && c.at? (i - 1) == some '-' then return none
  let j := if dash then i + 1 else i
  unless c.at? j == some '@' do return none
  let k := j + 1
  if c.at? k == some '{' then
    let some m := s.braces.get? k | return none
    if m ≤ k + 1 then return none
    return some (dash, String.ofList (c.cs.extract (k + 1) m).toList, m + 1)
  let some first := c.at? k | return none
  unless CiteKey.isAlnum first || first == '_' do return none
  let mut key := String.singleton first
  let mut m := k + 1
  let reg (d : Option Char) : Bool := d.any fun d => CiteKey.isAlnum d || d == '_'
  for _ in [0:c.size + 1] do
    match c.at? m with
    | none => break
    | some ch =>
      if CiteKey.isAlnum ch || ch == '_' then
        key := key.push ch
        m := m + 1
      else if CiteKey.internal ch && reg (c.at? (m + 1)) then
        key := key.push ch
        m := m + 1
      else if (ch == ':' || ch == '/') && c.at? (m + 1) == some '/' then
        key := key.push ch
        m := m + 1
      else break
  return some (dash, key, m)

/-- The index past what the citation grammar steps over whole at `k`: an escape, a code span or a
backtick run, a character reference, an autolink, or a bracket the scan already matched. -/
def citeSkipAt (c : Chars) (ticks : Std.HashMap Nat (Array Nat))
    (closeOf : Std.HashMap Nat Nat) (k : Nat) : Option Nat :=
  match c.at? k with
  | some '\\' => if (escaped? c k).isSome then some (k + 2) else none
  | some '`' =>
    let n := tickRun c k
    match codeSpanAt c ticks k n with
    | some (_, next) => some next
    | none => some (k + n)
  | some '&' => (entityAt c k).map (·.2)
  | some '<' => (autolinkAt c k).map (·.2.2)
  | some '[' => (closeOf.get? k).map (· + 1)
  | _ => none

/-- Spaces, then one line ending at most, then spaces: Pandoc's `spnl`. -/
def citeSpnl (c : Chars) (i b : Nat) : Nat := Id.run do
  let mut j := i
  let mut broke := false
  for _ in [0:b - i + 1] do
    match c.at? j with
    | some ' ' | some '\t' => j := j + 1
    | some '\n' =>
      if broke then break
      broke := true
      j := j + 1
    | _ => break
  return min j b

/-- One citation of a bracketed list: its key and mode, and the index ranges of its prefix and
suffix. -/
structure CiteSpan where
  key : String
  mode : CiteMode
  preFrom : Nat
  preTo : Nat
  postFrom : Nat
  postTo : Nat
  deriving Inhabited

/-- Whether emphasis opened in a citation's prefix would close in its suffix: then the key stands
inside the emphasis, not in the list, as Pandoc's inline reading has it. -/
def citeEmphasisSpans (c : Chars) (s : CiteSpan) : Bool := Id.run do
  let mut opener : Option Char := none
  for k in [s.preFrom:s.preTo] do
    match c.at? k with
    | some ch =>
      if (ch == '*' || ch == '_') && !(k > s.preFrom && c.at? (k - 1) == some ch) then
        let mut e := k
        for _ in [k:s.preTo] do
          if c.at? e == some ch then e := e + 1 else break
        let (left, right) := flanking (if k == 0 then none else c.at? (k - 1)) (c.at? e)
        if right && opener == some ch then opener := none
        else if left then opener := some ch
    | none => pure ()
  let some ch := opener | return false
  for k in [s.postFrom:s.postTo] do
    if c.at? k == some ch then
      let (_, right) := flanking (if k == 0 then none else c.at? (k - 1)) (c.at? (k + 1))
      if right then return true
  return false

/-- Pandoc's bracketed citation list over `c[a, b)`, a bracket's content: each citation's prefix,
key and suffix, separated by `;`; `none` where the content is no such list. -/
def citeListAt (c : Chars) (s : CiteScan) (ticks : Std.HashMap Nat (Array Nat))
    (closeOf : Std.HashMap Nat Nat) (a b : Nat) : Option (Array CiteSpan) := Id.run do
  let mut items : Array CiteSpan := #[]
  let mut j := citeSpnl c a b
  for _ in [0:b - a + 1] do
    let preFrom := j
    let mut k := j
    let mut found : Option (Bool × String × Nat) := none
    for _ in [0:b - a + 1] do
      if k ≥ b then break
      match citeSkipAt c ticks closeOf k with
      | some next => k := next
      | none =>
        match c.at? k with
        | some ';' => return none
        | some ch =>
          if ch == '@' || (ch == '-' && c.at? (k + 1) == some '@') then
            match citeKeyAt c s k with
            | some hit =>
              found := some hit
              break
            | none => k := k + 1
          else k := k + 1
        | none => break
    let some (suppress, key, past) := found | return none
    if past > b then return none
    let mut m := past
    for _ in [0:b - a + 1] do
      if m ≥ b then break
      match citeSkipAt c ticks closeOf m with
      | some next => m := next
      | none =>
        if c.at? m == some ';' then break
        m := m + 1
    let stop := min m b
    let mode : CiteMode := if suppress then .suppressAuthor else .normal
    let span : CiteSpan :=
      { key := key, mode := mode, preFrom := preFrom, preTo := k, postFrom := past, postTo := stop }
    if citeEmphasisSpans c span then return none
    items := items.push span
    if stop ≥ b then return some items
    j := citeSpnl c (stop + 1) b
    if j ≥ b then return none
  return none

/-- The suffix of an author-in-text citation's bracket over `c[a, b)` (Pandoc's `bareloc`): a
suffix, then optionally `;` and a list; `none` where the content is no such tail. -/
def citeTailAt (c : Chars) (s : CiteScan) (ticks : Std.HashMap Nat (Array Nat))
    (closeOf : Std.HashMap Nat Nat) (a b : Nat) : Option ((Nat × Nat) × Array CiteSpan) := Id.run do
  if c.at? a == some '^' then return none
  let mut m := a
  for _ in [0:b - a + 1] do
    if m ≥ b then break
    match citeSkipAt c ticks closeOf m with
    | some next => m := next
    | none =>
      if c.at? m == some ';' then break
      m := m + 1
  let stop := min m b
  if stop ≥ b then return some ((a, b), #[])
  match citeListAt c s ticks closeOf (stop + 1) b with
  | some rest => return some ((a, stop), rest)
  | none => return none

/-- The characters of `c[a, b)`, each with its position. -/
def Chars.slice (c : Chars) (a b : Nat) : Chars :=
  { cs := c.cs.extract a b, ps := c.ps.extract a b }

/-- One citation group the scan read: the tokens it spans, from its bracket or its in-text key to
its closing bracket, and its citations. -/
structure CPair where
  openTok : Nat
  closeTok : Nat
  spans : Array CiteSpan
  pos : Pos

/-- A fenced block's info string with its backslash escapes
and character references resolved. -/
def decodeInfo (s : String) : String := Id.run do
  let c : Chars := { cs := s.toList.toArray, ps := #[] }
  let mut out := ""
  let mut i := 0
  for _ in [0:c.size + 1] do
    if i ≥ c.size then break
    match escaped? c i with
    | some d =>
      out := out.push d
      i := i + 2
    | none =>
      match entityAt c i with
      | some (v, next) =>
        out := out ++ v
        i := next
      | none =>
        out := out.push ((c.at? i).getD ' ')
        i := i + 1
  return out

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-- What the reader refuses by design, as the subject its diagnostic carries. -/
inductive Strict where
  | rawHtml
  | indentedCode
  | lazyContinuation
  deriving Repr, BEq, DecidableEq

def Strict.subject : Strict → String
  | .rawHtml => "md:raw-html"
  | .indentedCode => "md:indented-code"
  | .lazyContinuation => "md:lazy-continuation"

def Strict.message : Strict → String
  | .rawHtml => "raw HTML in markdown is refused: document content can never become markup here"
  | .indentedCode => "an indented code block is refused: four spaces of indent mean continuation inside a list and code outside one"
  | .lazyContinuation => "a lazy continuation line is refused: a paragraph line inside a container repeats the container's marker"

def Strict.fixit : Strict → String
  | .rawHtml => "write it in markdown (**bold**, *emphasis*, [text](url), ![alt](src)), quote it as a code span with `...`, or delete the tags"
  | .indentedCode => "fence the block with ``` instead"
  | .lazyContinuation => "indent the line to its container's content column, or repeat a quote's '>'"

def refuse (file : String) (s : Strict) (pos : Pos) : Diag :=
  Diag.of .E0390 s.message (some ⟨file, pos⟩) (some s.fixit) (some s.subject)

/-- What an open tag the inline scan read lowers to: a hard
break, a target, or a disclosure. -/
private def openTagInline (file : String) (cs : Array Char) (p : Pos) (t : HtmlTag) :
    Nat × Option ITok × Option Diag :=
  let refused := (t.stop, none, some (refuse file .rawHtml p))
  if isBr t then (t.stop, some (.hard p), none)
  else match anchorKey? t with
    | none => refused
    | some key =>
      match endTagAt cs t.stop with
      | some (n, next) => if n == "a" then (next, some (.anchor key p), none) else refused
      | none => refused

private theorem openTagInline_exact {file : String} {cs : Array Char} {p : Pos} {t : HtmlTag}
    {next : Nat} {tok : Option ITok} {d : Option Diag}
    (h : openTagInline file cs p t = (next, tok, d)) :
    (next = t.stop ∧ tok = some (.hard p) ∧ d = none) ∨
      (∃ key, endTagAt cs t.stop = some ("a", next) ∧ tok = some (.anchor key p) ∧ d = none) ∨
      (next = t.stop ∧ tok = none ∧ d = some (refuse file .rawHtml p)) := by
  unfold openTagInline at h
  simp only [] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · split at h
    · simp only [Prod.mk.injEq] at h
      exact Or.inr (Or.inr ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
    · rename_i key _
      split at h
      · rename_i n next' he
        split at h
        · rename_i hn
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inl ⟨key, by rw [he, beq_iff_eq.mp hn], rfl, rfl⟩)
        · simp only [Prod.mk.injEq] at h
          exact Or.inr (Or.inr ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
      · simp only [Prod.mk.injEq] at h
        exact Or.inr (Or.inr ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)

/-- Raw HTML at `i` inside an inline stretch: the index past what was consumed,
the token it lowers to, and its refusal; `none` when the `<` is text. -/
def htmlInlineAt (file : String) (cs : Array Char) (i : Nat) (p : Pos) (m : HtmlMemo) :
    Option (Nat × Option ITok × Option Diag) × HtmlMemo :=
  if cs[i + 1]? == some '!' || cs[i + 1]? == some '?' || cs[i + 1]? == some '/' then
    match htmlTagAtM cs i m with
    | (some next, m') =>
      -- premise: mdSurfaceChecks — comments hide only their own text
      if litAt cs i "<!--" && commentOnly cs i next then (some (next, none, none), m')
      else (some (next, none, some (refuse file .rawHtml p)), m')
    | (none, m') => (none, m')
  else ((tagAt cs i).map (openTagInline file cs p), m)

theorem htmlInlineAt_accounts {file : String} {cs : Array Char} {i next : Nat} {p : Pos}
    {m m' : HtmlMemo} {tok : Option ITok} {d : Option Diag}
    (h : htmlInlineAt file cs i p m = (some (next, tok, d), m')) :
    i < next ∧ next ≤ cs.size ∧
      ((tok.isSome ∧ d = none) ∨
        (tok = none ∧ ∃ g, d = some g ∧ g.kind = .E0390 ∧ g.subject = some "md:raw-html" ∧
          g.span = some ⟨file, p⟩) ∨
        (tok = none ∧ d = none ∧ litAt cs i "<!--" = true ∧ commentOnly cs i next = true)) := by
  have refused_named : ∀ {g : Diag}, g = refuse file .rawHtml p →
      g.kind = .E0390 ∧ g.subject = some "md:raw-html" ∧ g.span = some ⟨file, p⟩ := by
    intro g hg
    rw [hg, refuse, Diag.of_record_exact]
    exact ⟨rfl, rfl, rfl⟩
  unfold htmlInlineAt at h
  split at h
  · split at h
    · rename_i n m'' htag
      have hb := htmlTagAtM_between htag
      split at h
      · rename_i hc
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        simp only [Bool.and_eq_true] at hc
        exact ⟨hb.1, hb.2, Or.inr (Or.inr ⟨rfl, rfl, hc.1, hc.2⟩)⟩
      · simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        exact ⟨hb.1, hb.2, Or.inr (Or.inl ⟨rfl, _, rfl, refused_named rfl⟩)⟩
    · simp at h
  · cases ht : tagAt cs i with
    | none => simp [ht] at h
    | some t =>
      have htb := tagAt_between ht
      simp only [ht, Option.map_some, Prod.mk.injEq, Option.some.injEq] at h
      rcases openTagInline_exact h.1 with ⟨rfl, rfl, rfl⟩ | ⟨key, he, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨htb.1, htb.2, Or.inl ⟨rfl, rfl⟩⟩
      · have heb := endTagAt_between he
        exact ⟨by omega, heb.2, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨htb.1, htb.2, Or.inr (Or.inl ⟨rfl, _, rfl, refused_named rfl⟩)⟩

theorem htmlInlineAt_covers {file : String} {cs : Array Char} {i next : Nat} {p : Pos}
    {m m' : HtmlMemo} {tok : ITok} {d : Option Diag}
    (h : htmlInlineAt file cs i p m = (some (next, some tok, d), m')) :
    tok = .hard p ∨ ∃ key, tok = .anchor key p := by
  unfold htmlInlineAt at h
  split at h
  · split at h
    · split at h <;> simp at h
    · simp at h
  · cases ht : tagAt cs i with
    | none => simp [ht] at h
    | some t =>
      simp only [ht, Option.map_some, Prod.mk.injEq, Option.some.injEq] at h
      rcases openTagInline_exact h.1 with ⟨_, h2, _⟩ | ⟨key, _, h2, _⟩ | ⟨_, h2, _⟩
      · exact Or.inl (Option.some.inj h2)
      · exact Or.inr ⟨key, Option.some.inj h2⟩
      · simp at h2

/-- How a text reads citations: not at all, every key where a document declares its bibliography,
or in a Lean docstring only the keys its bibliography holds, with the keys doc-gen4's bracket rule
cites (`docGenKeys`). -/
public structure CiteRead where
  on : Bool := false
  known : Option (Std.HashSet String) := none
  bracketed : Std.HashSet String := {}
  /-- Each bracketed key by its label's matching form, the first in the text's order where two
  match alike. -/
  folded : Std.HashMap String String := {}

/-- Whether a citation of `key` is read: a document's any key, a docstring's a key its bibliography
holds. -/
def CiteRead.takes (cr : CiteRead) (key : String) : Bool := cr.known.all (·.contains key)

/-- The key a docstring's label links to under doc-gen4's appended definitions, matched as links
match labels: the bracketed key it is, else the one whose matching form it shares. -/
def CiteRead.keyFor? (cr : CiteRead) (label : String) : Option String :=
  if cr.bracketed.contains label then some label else cr.folded.get? (normLabel label)

/-- The keys doc-gen4 cites a docstring by (`findAllReferences`), in the order they first stand:
the text from each `[` to the next `]`, the scan going on past that `]`, where the bibliography
holds it. -/
public def docGenKeys (text : String) (known : Std.HashSet String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut seen : Std.HashSet String := {}
  let mut opened : Option String := none
  for ch in text.toList do
    match opened with
    | none => if ch == '[' then opened := some ""
    | some cur =>
      if ch == ']' then
        if known.contains cur && !seen.contains cur then
          out := out.push cur
          seen := seen.insert cur
        opened := none
      else opened := some (cur.push ch)
  return out

/-- How a Lean docstring reads citations against its bibliography's keys: Pandoc's of those keys
alone, and doc-gen4's bracketed ones. -/
public def docGenRead (text : String) (known : Std.HashSet String) : CiteRead :=
  let keys := docGenKeys text known
  { on := true, known := some known, bracketed := keys.foldl (·.insert ·) {}
    folded := keys.foldl (fun m k => if m.contains (normLabel k) then m else m.insert (normLabel k) k) {} }

/-- The scan: characters to a flat token array, brackets resolved against a
stack and refusals raised where seen. -/
def scanInlines (file : String) (c : Chars) (dialect : Dialect := .document)
    (cr : CiteRead := {}) (tex : Bool := false) (refs : Std.HashMap String LinkDef := {}) :
    Array ITok × Array BPair × Array CPair × Array ShownRef × Array Diag := Id.run do
  let cites := cr.on
  let mut toks : Array ITok := #[]
  let mut pairs : Array BPair := #[]
  let mut cpairs : Array CPair := #[]
  let mut shownRefs : Array ShownRef := #[]
  let mut diags : Array Diag := #[]
  -- token index, image, character index, and the in-text citation a bracket may close on
  let mut stack : Array (Nat × Bool × Nat × Option Nat) := #[]
  -- Link openers below this stack depth are inactive (§6.3).
  let mut inactiveBelow : Nat := 0
  let ticks := tickIndex c
  -- Each bracket the scan matched, by its opening character's index.
  let mut closeOf : Std.HashMap Nat Nat := {}
  -- The in-text citation whose bracket may follow, and the token count after its key.
  let mut tailFor : Option (Nat × Nat) := none
  let braces := if cites then braceMatches c else {}
  let mut closers : Std.HashSet Nat := {}
  let mut keyEnds : Std.HashSet Nat := {}
  -- The emphasis openers of each delimiter still waiting for a closer, a closer's estimate.
  let mut starOpen : Nat := 0
  let mut lineOpen : Nat := 0
  let mut hmemo : HtmlMemo := {}
  let mut pending := ""
  let mut pendingPos : Pos := {}
  let mut i := 0
  let flush : Array ITok → String → Pos → Array ITok := fun ts s p =>
    if s.isEmpty then ts else ts.push (.txt s p)
  for _ in [0:c.size + 1] do
    if i ≥ c.size then break
    let p := c.posAt i
    if pending.isEmpty then pendingPos := p
    match c.at? i with
    | none => break
    | some ch =>
      -- An in-text citation's bracket follows it after spaces and one line ending at most.
      if let some (_, n) := tailFor then
        let quiet := toks.size == n || (toks.size == n + 1 && toks.back? matches some (.soft _))
        unless quiet && (ch == ' ' || ch == '\t' || ch == '\n' || ch == '[') do
          tailFor := none
      if ch == '\\' then
        match escaped? c i with
        | some d =>
          if tex then
            -- Where text is TeX, an escape is a piece of its own at its place.
            toks := flush toks pending pendingPos
            pending := ""
            toks := toks.push (.txt (if texSpecial d then "\\" ++ d.toString else d.toString) p)
          else pending := pending.push d
          i := i + 2
        | none =>
          -- A backslash before a line ending is a hard break.
          if c.at? (i + 1) == some '\n' then
            toks := flush toks pending pendingPos
            pending := ""
            toks := toks.push (.hard p)
            i := i + 2
          else
            pending := pending.push '\\'
            i := i + 1
      else if ch == '`' then
        let n := tickRun c i
        match codeSpanAt c ticks i n with
        | some (body, next) =>
          toks := flush toks pending pendingPos
          pending := ""
          toks := toks.push (.code body p)
          i := next
        | none =>
          for _ in [0:n] do pending := pending.push '`'
          i := i + n
      else if ch == '&' then
        match entityAt c i with
        | some (v, next) =>
          if tex then
            toks := flush toks pending pendingPos
            pending := ""
            toks := toks.push (.txt v p)
          else pending := pending ++ v
          i := next
        | none =>
          pending := pending.push '&'
          i := i + 1
      else if ch == '<' then
        match autolinkAt c i with
        | some (dest, text, next) =>
          toks := flush toks pending pendingPos
          pending := ""
          toks := toks.push (.auto dest text p)
          i := next
        | none =>
          if dialect == .docstring then
            pending := pending.push '<'
            i := i + 1
            continue
          -- Only a complete tag (§6.6) is raw HTML; anything else is literal text.
          let (r, m) := htmlInlineAt file c.cs i p hmemo
          hmemo := m
          match r with
          | some (next, tok, d) =>
            if let some tk := tok then
              -- A break sheds the trailing spaces of the text before it.
              toks := flush toks (if tk matches .hard _ then rstrip pending else pending) pendingPos
              pending := ""
              toks := toks.push tk
            if let some dg := d then diags := diags.push dg
            i := next
          | none =>
            pending := pending.push '<'
            i := i + 1
      else if ch == '\n' then
        -- Two or more trailing spaces before the break make it hard.
        let hard := pending.endsWith "  "
        toks := flush toks (rstrip pending) pendingPos
        pending := ""
        toks := toks.push (if hard then .hard p else .soft p)
        i := i + 1
      else if ch == '$' && dialect == .docstring then
        -- md4c's math span: a run of one or two dollars opens where no letter or digit stands
        -- before it and closes where none follows.
        let n := dollarRun c i
        let edge : Option Char → Bool := fun x => x.all fun d => isMdSpace d || isMdPunct d
        let opens := edge (if i == 0 then none else c.at? (i - 1))
        let closes := edge (c.at? (i + n))
        if n ≤ 2 && (opens || closes) then
          toks := flush toks pending pendingPos
          pending := ""
          toks := toks.push (.dollar n opens closes i p)
        else
          for _ in [0:n] do pending := pending.push '$'
        i := i + n
      else if ch == '!' && c.at? (i + 1) == some '[' then
        toks := flush toks pending pendingPos
        pending := ""
        stack := stack.push (toks.size, true, i + 1, none)
        toks := toks.push (.bopen true p)
        i := i + 2
      else if ch == '[' then
        toks := flush toks pending pendingPos
        pending := ""
        stack := stack.push (toks.size, false, i, tailFor.map (·.1))
        tailFor := none
        toks := toks.push (.bopen false p)
        i := i + 1
      else if ch == ']' then
        match stack.back? with
        | none =>
          pending := pending.push ']'
          i := i + 1
        | some (openTok, image, openAt, tail) =>
          let active := image || stack.size - 1 ≥ inactiveBelow
          stack := stack.pop
          inactiveBelow := min inactiveBelow stack.size
          closeOf := closeOf.insert openAt i
          match (if active then linkTailAt c (i + 1) else none) with
          | some (dest, title, next) =>
            toks := flush toks pending pendingPos
            pending := ""
            let closeTok := toks.size
            toks := toks.push (.bclose p)
            pairs := pairs.push
              { openTok, closeTok, image, dest, title }
            -- A citation's note steps over a link whole, its destination included.
            closeOf := closeOf.insert openAt (next - 1)
            -- A link may not contain a link: every link opener still open goes inactive (§6.3).
            unless image do inactiveBelow := stack.size
            i := next
          | none =>
            -- premise: mdCiteChecks — a bracket is a citation group only where Pandoc reads one
            let after := c.at? (i + 1)
            let free := !(after == some '[' || after == some '{')
            let tailFree := free && after != some '('
            let scan : CiteScan := { closers, keyEnds, braces }
            -- A reference (§6.3): `[text][label]`, `[label][]`, or `[label]` before no label, the
            -- label's source and the index past the reference.
            let own : Option String := if i - openAt > 1000 then none else
              (labelAt c openAt).bind fun (l, n) => if n == i + 1 then some l else none
            let collapsed := after == some '[' && c.at? (i + 2) == some ']'
            let reference : Option (String × Nat) :=
              if collapsed then own.map (·, i + 3)
              else if after == some '[' then
                match labelAt c (i + 1) with
                | some found => some found
                | none => own.map (·, i + 1)
              else own.map (·, i + 1)
            -- A label the text defines links to its destination, ahead of doc-gen4's appended ones.
            let defined : Option (LinkDef × Nat) := do
              guard active
              let (l, n) ← reference
              let d ← refs.get? (normLabel l)
              pure (d, n)
            -- doc-gen4's rule: a label matching a key it cites links to the key's entry.
            let docGen : Option (String × Nat) := do
              guard (cites && !image && active && defined.isNone)
              let (l, n) ← reference
              let key ← cr.keyFor? l
              pure (key, n)
            -- A group of Pandoc's is read where its bibliography holds one of its works.
            let normal := if cites && free && docGen.isNone then
                (citeListAt c scan ticks closeOf (openAt + 1) i).filter (·.any (cr.takes ·.key))
              else none
            let closeTok := toks.size + (if pending.isEmpty then 0 else 1)
            let joined : Option (Nat × CPair) := match tail.bind (fun k => (cpairs[k]?).map (k, ·)) with
              | some (k, cp) =>
                match normal with
                | some list => some (k, { cp with closeTok, spans := cp.spans ++ list })
                | none =>
                  if !cites || !tailFree || docGen.isSome then none
                  else match (citeTailAt c scan ticks closeOf (openAt + 1) i).filter
                      (·.2.all (cr.takes ·.key)), cp.spans[0]? with
                    | some ((a, b), rest), some first =>
                      some (k, { cp with closeTok
                                         spans := #[{ first with postFrom := a, postTo := b }] ++ rest })
                    | _, _ => none
              | _ => none
            match joined, normal with
            | some (k, cp), _ =>
              toks := flush toks pending pendingPos
              pending := ""
              toks := toks.push (.bclose p)
              cpairs := cpairs.modify k fun _ => cp
            | none, some list =>
              toks := flush toks pending pendingPos
              pending := ""
              toks := toks.push (.bclose p)
              cpairs := cpairs.push { openTok, closeTok, spans := list,
                                      pos := (toks[openTok]?.map ITok.pos).getD p }
            | none, none =>
              let at_ := (toks[openTok]?.map ITok.pos).getD p
              match defined, docGen with
              | some (d, n), _ =>
                toks := flush toks pending pendingPos
                pending := ""
                toks := toks.push (.bclose p)
                pairs := pairs.push { openTok, closeTok, image, dest := d.dest, title := d.title }
                closeOf := closeOf.insert openAt (n - 1)
                unless image do inactiveBelow := stack.size
                i := n - 1
              | none, some (key, n) =>
                toks := flush toks pending pendingPos
                pending := ""
                toks := toks.push (.bclose p)
                -- Text that is the key itself shows the work's label, as doc-gen4 shows its tag.
                if c.str (openAt + 1) i == key then
                  let work : CiteSpan := { key, mode := .normal, preFrom := openAt + 1,
                                           preTo := openAt + 1, postFrom := i, postTo := i }
                  cpairs := cpairs.push { openTok, closeTok, pos := at_, spans := #[work] }
                else
                  shownRefs := shownRefs.push
                    { openTok, closeTok, key, textFrom := openAt + 1, textTo := i, pos := at_ }
                -- A reference is a link, which no link around it may contain (§6.3).
                inactiveBelow := stack.size
                i := n - 1
              | none, none => pending := pending.push ']'
            i := i + 1
      else if ch == '*' || ch == '_' then
        let mut n := 0
        let mut k := i
        for _ in [0:c.size + 1] do
          if c.at? k == some ch then
            n := n + 1
            k := k + 1
          else break
        let before := if i == 0 then none else c.at? (i - 1)
        let (left, right) := flanking before (c.at? k)
        let canOpen := if ch == '*' then left else
          left && (!right || (before.map isMdPunct).getD false)
        let canClose := if ch == '*' then right else
          right && (!left || ((c.at? k).map isMdPunct).getD false)
        let waiting := if ch == '*' then starOpen else lineOpen
        if canClose && waiting > 0 then
          closers := closers.insert k
          if ch == '*' then starOpen := starOpen - 1 else lineOpen := lineOpen - 1
        else if canOpen then
          if ch == '*' then starOpen := starOpen + 1 else lineOpen := lineOpen + 1
        toks := flush toks pending pendingPos
        pending := ""
        toks := toks.push (.run ch n canOpen canClose p)
        i := k
      else if cites && (ch == '@' || (ch == '-' && c.at? (i + 1) == some '@')) then
        match (citeKeyAt c { closers, keyEnds, braces } i).filter (cr.takes ·.2.1) with
        | some (suppress, key, next) =>
          keyEnds := keyEnds.insert next
          toks := flush toks pending pendingPos
          pending := ""
          let t := toks.size
          toks := toks.push (.ckey p)
          cpairs := cpairs.push { openTok := t, closeTok := t, pos := p, spans := #[
            { key, mode := if suppress then .suppressAuthor else .authorInText,
              preFrom := i, preTo := i, postFrom := next, postTo := next }] }
          tailFor := some (cpairs.size - 1, toks.size)
          i := next
        | none =>
          pending := pending.push ch
          i := i + 1
      else
        pending := pending.push ch
        i := i + 1
  toks := flush toks pending pendingPos
  return (toks, pairs, cpairs, shownRefs, diags)

/-- The innermost resolved link or image region of each token, `0` outside every
one, and the region count. -/
def regions (toks : Array ITok) (pairs : Array BPair) : Array Nat × Nat := Id.run do
  let mut openAt : Array Nat := Array.replicate toks.size 0
  let mut closeAt : Array Bool := Array.replicate toks.size false
  for (bp, k) in pairs.zipIdx do
    if bp.openTok < openAt.size then openAt := openAt.set! bp.openTok (k + 1)
    if bp.closeTok < closeAt.size then closeAt := closeAt.set! bp.closeTok true
  let mut out : Array Nat := Array.replicate toks.size 0
  let mut stack : Array Nat := #[]
  for k in [0:toks.size] do
    if (closeAt[k]?).getD false then stack := stack.pop
    out := out.set! k ((stack.back?).getD 0)
    let o := (openAt[k]?).getD 0
    if o > 0 then stack := stack.push o
  return (out, pairs.size + 1)

/-- CommonMark's delimiter-run match (§6.2), run once per bracket region over that region's runs,
with md4c's math spans: a dollar run closing the latest open one of its length takes everything
between, and a span or a pair closing takes the openers it passes. -/
def matchEmphasis (toks : Array ITok) (reg : Array Nat) (nRegions : Nat) :
    Array EPair × Array Nat × Array (Nat × Nat) := Id.run do
  let mut len : Array Nat := Array.replicate toks.size 0
  let mut orig : Array Nat := Array.replicate toks.size 0
  let mut ch : Array Char := Array.replicate toks.size ' '
  let mut op : Array Bool := Array.replicate toks.size false
  let mut cl : Array Bool := Array.replicate toks.size false
  let mut dollar : Array Bool := Array.replicate toks.size false
  let mut byRegion : Array (Array Nat) := Array.replicate nRegions #[]
  for (t, k) in toks.zipIdx do
    match t with
    | .run c n o e _ =>
      len := len.set! k n
      orig := orig.set! k n
      ch := ch.set! k c
      op := op.set! k o
      cl := cl.set! k e
      let r := (reg[k]?).getD 0
      if r < byRegion.size then byRegion := byRegion.modify r (·.push k)
    | .dollar n o e _ _ =>
      len := len.set! k n
      orig := orig.set! k n
      ch := ch.set! k '$'
      op := op.set! k o
      cl := cl.set! k e
      dollar := dollar.set! k true
      let r := (reg[k]?).getD 0
      if r < byRegion.size then byRegion := byRegion.modify r (·.push k)
    | _ => pure ()
  let rd : Array Nat → Nat → Nat := fun a i => (a[i]?).getD 0
  let rb : Array Bool → Nat → Bool := fun a i => (a[i]?).getD false
  let rc : Array Char → Nat → Char := fun a i => (a[i]?).getD ' '
  let mut out : Array EPair := #[]
  let mut maths : Array (Nat × Nat) := #[]
  let mut born := 0
  for runs in byRegion do
    let mut stack : Array Nat := #[]
    -- The dollar openers still waiting, a subsequence of the stack.
    let mut dollars : Array Nat := #[]
    -- One floor per character, closer-can-open and length mod 3.
    let mut bottom : Array Nat := Array.replicate 12 0
    for ci in runs do
      if rb dollar ci then
        match dollars.back? with
        | some oj =>
          if rb cl ci && rd orig oj == rd orig ci then
            maths := maths.push (oj, ci)
            len := len.set! oj 0
            len := len.set! ci 0
            for _ in [0:stack.size] do
              match stack.back? with
              | some top => if top ≥ oj then stack := stack.pop else break
              | none => break
            -- Spans do not nest: every dollar opener still waiting goes with this one.
            dollars := #[]
          else if rb op ci then
            stack := stack.push ci
            dollars := dollars.push ci
        | none =>
          if rb op ci then
            stack := stack.push ci
            dollars := dollars.push ci
        continue
      if rb cl ci then
        let bkt := (if rc ch ci == '*' then 0 else 6)
          + (if rb op ci then 3 else 0) + rd orig ci % 3
        for _ in [0:rd orig ci] do
          if rd len ci == 0 then break
          let mut found : Option Nat := none
          let mut si := stack.size
          for _ in [0:stack.size] do
            if si == 0 then break
            si := si - 1
            let oi := rd stack si
            if oi < rd bottom bkt then break
            if rc ch oi == rc ch ci then
              -- Rule of three, on the original lengths.
              let ok := !(rb op ci || rb cl oi) || rd orig ci % 3 == 0
                || (rd orig oi + rd orig ci) % 3 != 0
              if ok then
                found := some si
                break
          match found with
          | none =>
            -- No partner for this shape at or above the floor, so none below this closer either.
            bottom := bottom.set! bkt ci
            break
          | some s =>
            let oj := rd stack s
            -- Everything between the pair is removed.
            stack := stack.extract 0 (s + 1)
            for _ in [0:dollars.size] do
              match dollars.back? with
              | some d => if d > oj then dollars := dollars.pop else break
              | none => break
            let strong := rd len oj ≥ 2 && rd len ci ≥ 2
            let use := if strong then 2 else 1
            len := len.set! oj (rd len oj - use)
            len := len.set! ci (rd len ci - use)
            out := out.push { openTok := oj, closeTok := ci, strong, born }
            born := born + 1
            if rd len oj == 0 then stack := stack.pop
      -- What is left of a run that can open is a potential opener.
      if rb op ci && rd len ci > 0 then stack := stack.push ci
  return (out, len, maths)

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-- What an open inline frame will become when its closer arrives. -/
inductive OpenKind where
  | emph
  | strong
  | link (dest title : String)
  | image (dest title : String)
  deriving Repr, Inhabited

private structure OFrame where
  kind : OpenKind
  pos : Pos
  closeTok : Nat
  outer : Array Inl

private instance : Inhabited OFrame :=
  ⟨{ kind := .emph, pos := {}, closeTok := 0, outer := #[] }⟩

private def OFrame.close (f : OFrame) (body : Array Inl) : Array Inl :=
  match f.kind with
  | .emph => f.outer.push (.emph body f.pos)
  | .strong => f.outer.push (.strong body f.pos)
  | .link d t => f.outer.push (.link d t body f.pos)
  | .image d t => f.outer.push (.image d t body f.pos)

/-- The tree from the token array and the two pair tables, in one left-to-right
pass with a frame stack. -/
def buildInlines (toks : Array ITok) (bpairs : Array BPair) (cites : Array (Nat × Nat × Array Inl))
    (epairs : Array EPair) (leftover : Array Nat) : Array Inl := Id.run do
  let mut closingAt : Array (Array EPair) := Array.replicate toks.size #[]
  let mut openingAt : Array (Array EPair) := Array.replicate toks.size #[]
  for e in epairs do
    if e.closeTok < closingAt.size then
      closingAt := closingAt.modify e.closeTok (·.push e)
    if e.openTok < openingAt.size then
      openingAt := openingAt.modify e.openTok (·.push e)
  let mut bopenAt : Array (Option BPair) := Array.replicate toks.size none
  let mut bcloseAt : Array Bool := Array.replicate toks.size false
  for bp in bpairs do
    if bp.openTok < bopenAt.size then bopenAt := bopenAt.set! bp.openTok (some bp)
    if bp.closeTok < bcloseAt.size then bcloseAt := bcloseAt.set! bp.closeTok true
  let mut citeAt : Array (Option (Nat × Array Inl)) := Array.replicate toks.size none
  for (o, cl, nodes) in cites do
    if o < citeAt.size then citeAt := citeAt.modify o fun _ => some (cl, nodes)
  let mut frames : Array OFrame := #[]
  let mut acc : Array Inl := #[]
  -- A citation group's tokens are its node's, read once at its first token.
  let mut resume := 0
  for i in [0:toks.size] do
    if i < resume then continue
    let some t := toks[i]? | continue
    let p := t.pos
    if let some (cl, nodes) := (citeAt[i]?).getD none then
      acc := acc ++ nodes
      resume := cl + 1
      continue
    -- Closes: emphasis innermost first, then a bracket pair.
    let closingE := ((closingAt[i]?).getD #[]).qsort (·.born < ·.born)
    for _ in closingE do
      if let some f := frames.back? then
        frames := frames.pop
        acc := f.close acc
    match t with
    | .txt s _ => acc := acc.push (.text s p)
    | .code s _ => acc := acc.push (.code s p)
    | .soft _ => acc := acc.push (.soft p)
    | .hard _ => acc := acc.push (.hard p)
    | .auto dest text _ => acc := acc.push (.link dest "" #[.text text p] p)
    | .anchor key _ => acc := acc.push (.anchor key p)
    | .ckey _ => pure ()
    | .dollar n _ _ _ _ => acc := acc.push (.text (String.ofList (List.replicate n '$')) p)
    | .bclose _ =>
      if (bcloseAt[i]?).getD false then
        if let some f := frames.back? then
          frames := frames.pop
          acc := f.close acc
      else
        acc := acc.push (.text "]" p)
    | .bopen image _ =>
      match (bopenAt[i]?).getD none with
      | some bp =>
        frames := frames.push
          { kind := if image then .image bp.dest bp.title else .link bp.dest bp.title,
            pos := p, closeTok := bp.closeTok, outer := acc }
        acc := #[]
      | none => acc := acc.push (.text (if image then "![" else "[") p)
    | .run ch _ _ _ _ =>
      let n := (leftover[i]?).getD 0
      if n > 0 then
        acc := acc.push (.text (String.ofList (List.replicate n ch)) p)
      let openingE := ((openingAt[i]?).getD #[]).qsort (·.born > ·.born)
      for e in openingE do
        frames := frames.push
          { kind := if e.strong then .strong else .emph,
            pos := p, closeTok := e.closeTok, outer := acc }
        acc := #[]
  -- Unclosed frames cannot occur: every frame comes from a matched pair.
  for _ in [0:frames.size] do
    if let some f := frames.back? then
      frames := frames.pop
      acc := f.close acc
  return acc

/-- The math spans a match closed, each a node standing for its tokens, and whether each token
stands strictly inside one. -/
def mathNodes (c : Chars) (toks : Array ITok) (maths : Array (Nat × Nat)) :
    Array (Nat × Nat × Array Inl) × Array Bool := Id.run do
  let mut nodes : Array (Nat × Nat × Array Inl) := #[]
  let mut mark : Array Int := Array.replicate (toks.size + 1) 0
  for (o, e) in maths do
    match toks[o]?, toks[e]? with
    | some (.dollar n _ _ a p), some (.dollar _ _ _ b _) =>
      nodes := nodes.push (o, e, #[Inl.math (n == 2) (c.str (a + n) b) p])
      mark := mark.modify (o + 1) (· + 1)
      mark := mark.modify e (· - 1)
    | _, _ => pure ()
  let mut inside : Array Bool := Array.replicate toks.size false
  let mut depth : Int := 0
  for k in [0:toks.size] do
    depth := depth + (mark[k]?).getD 0
    if depth > 0 then inside := inside.set! k true
  return (nodes, inside)

/-- Inline structure for one stretch of text, in three passes, every `@` read as text. -/
def inlinesPlain (file : String) (c : Chars) (dialect : Dialect := .document)
    (refs : Std.HashMap String LinkDef := {}) : Array Inl × Array Diag :=
  let (toks, bpairs, _, _, diags) := scanInlines file c dialect (refs := refs)
  let (reg, nRegions) := regions toks bpairs
  let (epairs, leftover, maths) := matchEmphasis toks reg nRegions
  let (formulas, inside) := mathNodes c toks maths
  let keep (o : Nat) : Bool := !(inside[o]?).getD false
  (buildInlines toks (bpairs.filter (keep ·.openTok)) formulas (epairs.filter (keep ·.openTok))
    leftover, diags)

/-- Inline content without the white space and line endings it opens and closes on. -/
def trimInl (xs : Array Inl) : Array Inl :=
  let blank : Inl → Bool
    | .soft _ | .hard _ => true
    | .text s _ => s.all isMdSpace
    | _ => false
  let ys := (xs.toList.dropWhile blank).reverse.dropWhile blank |>.reverse
  let ys := match ys with
    | .text s p :: rest => Inl.text s.trimAsciiStart.toString p :: rest
    | _ => ys
  let ys := match ys.reverse with
    | .text s p :: rest => (Inl.text s.trimAsciiEnd.toString p :: rest).reverse
    | _ => ys
  ys.toArray

/-- A citation's prefix or suffix: the plain reading of `c[a, b)`, its surrounding white space off;
the main scan already raised what the range holds. -/
def citeNote (file : String) (c : Chars) (dialect : Dialect) (a b : Nat)
    (refs : Std.HashMap String LinkDef := {}) : Array Inl :=
  if b ≤ a then #[] else trimInl (inlinesPlain file (c.slice a b) dialect refs).1

/-- W0392 for each citation group inside another group's prefix or suffix, which the IR's plain
notes cannot hold: Pandoc reads it, here it sets as its text and its work goes uncited. -/
def nestedCites (file : String) (cpairs : Array CPair) : Array Diag := Id.run do
  let order := cpairs.qsort fun a b =>
    a.openTok < b.openTok || (a.openTok == b.openTok && a.closeTok > b.closeTok)
  let mut open_ : Array (CPair × Std.HashSet Nat) := #[]
  let mut out : Array Diag := #[]
  for cp in order do
    for _ in [0:open_.size] do
      match open_.back? with
      | some (top, _) => if top.closeTok < cp.openTok then open_ := open_.pop else break
      | none => break
    if let some (_, places) := open_.back? then
      -- A group's own key, read in-text by the scan before its bracket closed, is no inner one.
      let own := cp.spans.size == 1 && (cp.spans[0]?).any (places.contains ·.preFrom)
      unless own do
        out := out.push (Diag.of .W0392 "a citation inside another citation's prefix or suffix \
sets as its text, and its work is not cited" (some ⟨file, cp.pos⟩)
          (some "close the first citation's brackets before it, or list both in one bracket \
separated by ';'") (subject := some "md:cite-nested"))
    open_ := open_.push (cp, cp.spans.foldl (fun s sp => s.insert sp.preTo) {})
  return out

/-- Inline structure for one stretch of text, in three passes, citations read as `cr` says. -/
def inlines (file : String) (c : Chars) (dialect : Dialect := .document) (cr : CiteRead := {})
    (tex : Bool := false) (refs : Std.HashMap String LinkDef := {}) : Array Inl × Array Diag :=
  let (toks, bpairs, cpairs, shownRefs, diags) := scanInlines file c dialect cr tex refs
  let grouped := (cpairs.filter fun cp => cp.openTok < cp.closeTok).map fun cp =>
    ({ openTok := cp.openTok, closeTok := cp.closeTok, image := false, dest := "", title := "" } :
      BPair)
  let grouped := grouped ++ shownRefs.map fun r =>
    ({ openTok := r.openTok, closeTok := r.closeTok, image := false, dest := "", title := "" } : BPair)
  let (reg, nRegions) := regions toks (bpairs ++ grouped)
  let (epairs, leftover, maths) := matchEmphasis toks reg nRegions
  -- A math span sets its source whole: no link, citation or emphasis inside it stands.
  let (formulas, inside) := mathNodes c toks maths
  let keep (o : Nat) : Bool := !(inside[o]?).getD false
  let bpairs := bpairs.filter (keep ·.openTok)
  let cpairs := cpairs.filter (keep ·.openTok)
  let shownRefs := shownRefs.filter (keep ·.openTok)
  let epairs := epairs.filter (keep ·.openTok)
  let built := cpairs.map fun cp =>
    let node := Inl.cite (cp.spans.map fun s =>
      .mk s.key s.mode (citeNote file c dialect s.preFrom s.preTo refs)
        (citeNote file c dialect s.postFrom s.postTo refs)) cp.pos
    -- An image opener no image followed sets its `!` before the citation its bracket holds.
    let lead : Array Inl := match toks[cp.openTok]? with
      | some (ITok.bopen true p) => #[.text "!" p]
      | _ => #[]
    (cp.openTok, cp.closeTok, lead.push node)
  let shown := shownRefs.map fun r =>
    (r.openTok, r.closeTok, #[Inl.citeText r.key (citeNote file c dialect r.textFrom r.textTo refs) r.pos])
  (buildInlines toks bpairs (built ++ shown ++ formulas) epairs leftover,
    diags ++ nestedCites file cpairs)

/-- The characters of a run of paragraph lines,
newline-separated, each with its source position. -/
def charsOf (lines : Array (String × Pos)) : Chars := Id.run do
  let mut cs : Array Char := #[]
  let mut ps : Array Pos := #[]
  for (s, p) in lines do
    unless cs.isEmpty do
      cs := cs.push '\n'
      ps := ps.push p
    let mut col := p.col
    for ch in s.toList do
      cs := cs.push ch
      ps := ps.push { p with col }
      col := col + 1
  return ⟨cs, ps⟩

def charsOfOne (s : String) (p : Pos) : Chars := charsOf #[(s, p)]

/-- Whether a line may hold a definition's label's end, `]:`. -/
def holdsRefColon (s : String) : Bool := Id.run do
  let mut prev := ' '
  for ch in s.toList do
    if prev == ']' && ch == ':' then return true
    prev := ch
  return false

/-- The link reference definitions a paragraph's lines open with (§4.7), each label in its
matching form, and the lines after them. -/
def paraDefs (pls : Array (String × Pos)) : Array (String × LinkDef) × Array (String × Pos) :=
  Id.run do
  unless pls.any (holdsRefColon ·.1) do return (#[], pls)
  let c := charsOf pls
  let mut defs : Array (String × LinkDef) := #[]
  let mut i := 0
  for _ in [0:c.size + 1] do
    match linkDefAt c i with
    | some (label, d, next) =>
      if next ≤ i then break
      defs := defs.push (normLabel label, d)
      i := next
    | none => break
  if defs.isEmpty then return (#[], pls)
  let mut off := 0
  let mut rest : Array (String × Pos) := #[]
  for (s, p) in pls do
    if off ≥ i then rest := rest.push (s, p)
    off := off + s.length + 1
  return (defs, rest)

/-- A metadata value's markdown as inline content, no citation read. -/
public def metaInlines (file s : String) (pos : Pos) : Array Inl × Array Diag :=
  inlines file (charsOfOne s pos) .document

/-- HTML text with the reader's known character references resolved; `none` for
an unknown, unterminated or C1 reference. -/
private def htmlText (s : String) : Option String := Id.run do
  let c : Chars := { cs := s.toList.toArray, ps := #[] }
  let mut out := ""
  let mut i := 0
  for _ in [0:c.size + 1] do
    if i ≥ c.size then break
    if c.at? i == some '<' then return none
    let entity := entityAt c i
    let unsupported : Bool := match entity with
      | some (v, _) => v.any (fun ch : Char => ch.toNat ≥ 0x80 && ch.toNat ≤ 0x9f)
      | none => c.at? i == some '&' &&
          ((c.at? (i + 1)).any fun ch => isAsciiAlpha ch || ch == '#')
    if unsupported then return none
    match entity with
    | some (v, next) =>
      out := out ++ v
      i := next
    | none =>
      out := out.push ((c.at? i).getD ' ')
      i := i + 1
  return some out

/-- A complete, attribute-free summary on one line, holding text. -/
private def summaryAt (cs : Array Char) (i : Nat) (p : Pos) : Option (Array Inl) := do
  let start ← bareTagAt cs i "summary"
  let closeEnd ← findLit cs start "</summary"
  let stop := closeEnd - "</summary".length
  let next ← bareTagAt cs stop "summary" true
  guard (isBlankFrom cs next)
  let text ← htmlText (sliceStr cs start stop)
  guard (holdsText text)
  -- White space a reference spells sets as a space: a summary is one line.
  let text := text.map fun c => if c == '\n' || c == '\r' || c == '\x0C' || c == '\t' then ' ' else c
  return #[.text text { p with col := start + 1 }]

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-- The table extension's space: a space, a tab, a vertical
tab or a form feed. -/
def isTableSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\x0b' || c == '\x0c'

/-- The index past a run of table spaces at `i`. -/
def tableSpaceEnd (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut k := i
  for _ in [0:cs.size + 1] do
    if (cs[k]?).any isTableSpace then k := k + 1 else break
  return k

/-- A delimiter row at `i`: each column's alignment, or
`none` when the line is not one. -/
def tableDelimAt (cs : Array Char) (i : Nat) : Option (Array TableAlign) := Id.run do
  let mut k := if cs[i]? == some '|' then i + 1 else i
  let mut aligns : Array TableAlign := #[]
  for _ in [0:cs.size + 1] do
    k := tableSpaceEnd cs k
    let left := cs[k]? == some ':'
    if left then k := k + 1
    let dashes := k
    for _ in [0:cs.size + 1] do
      if cs[k]? == some '-' then k := k + 1 else break
    if k == dashes then return none
    let right := cs[k]? == some ':'
    if right then k := k + 1
    k := tableSpaceEnd cs k
    aligns := aligns.push
      (if left && right then .center else if left then .left else if right then .right
       else .none)
    match cs[k]? with
    | none => return some aligns
    | some '|' =>
      k := k + 1
      if tableSpaceEnd cs k ≥ cs.size then return some aligns
    | some _ => return none
  return none

/-- One cell of a row, trimmed, each `\|` read as a pipe, every character
keeping its `.md` position. -/
def tableCell (c : Chars) (start stop : Nat) : Chars := Id.run do
  let blank (ch : Char) : Bool := isMdSpace ch || ch == '\x0b'
  let mut a := start
  let mut b := stop
  for _ in [start:stop] do
    if a < b && (c.at? a).any blank then a := a + 1 else break
  for _ in [start:stop] do
    if a < b && (c.at? (b - 1)).any blank then b := b - 1 else break
  let mut cs : Array Char := #[]
  let mut ps : Array Pos := #[]
  for k in [a:b] do
    unless c.at? k == some '\\' && c.at? (k + 1) == some '|' && k + 1 < b do
      cs := cs.push ((c.at? k).getD ' ')
      ps := ps.push (c.posAt k)
  return ⟨cs, ps⟩

/-- A row's cells, split on every unescaped pipe; empty for a line holding no
cell, which ends a table. -/
def tableCells (c : Chars) : Array Chars := Id.run do
  let mut k := if c.at? 0 == some '|' then tableSpaceEnd c.cs 1 else 0
  let mut cells : Array Chars := #[]
  for _ in [0:c.size + 1] do
    let start := k
    for _ in [0:c.size + 1] do
      match c.at? k with
      | none => break
      | some '|' => break
      | some '\\' => k := k + (if (c.at? (k + 1)).any isMdPunct then 2 else 1)
      | some _ => k := k + 1
    let piped := c.at? k == some '|'
    if k == start && !piped then break
    cells := cells.push (tableCell c start (min k c.size))
    if piped then k := tableSpaceEnd c.cs (k + 1) else break
  return cells

/-- A row's cells as inline content, exactly `n` of them: a missing cell is
empty and an excess one dropped. -/
def tableRow (file : String) (n : Nat) (cells : Array Chars) (dialect : Dialect := .document)
    (cr : CiteRead := {}) (tex : Bool := false) (refs : Std.HashMap String LinkDef := {}) :
    Array (Array Inl) × Array Diag := Id.run do
  let mut row : Array (Array Inl) := #[]
  let mut diags : Array Diag := #[]
  for k in [0:n] do
    match cells[k]? with
    | some c =>
      let (inl, ds) := inlines file c dialect cr tex refs
      row := row.push inl
      diags := diags ++ ds
    | none => row := row.push #[]
  return (row, diags)

end LeanTex.Core.Md



namespace LeanTex.Core.Md

open LeanTex.Core

private inductive FKind where
  | quote
  | list (ordered : Bool) (start : Nat) (marker : Char)
  | item (indent : Nat)
  | disclosure
  deriving Repr, BEq, Inhabited

private structure Frame where
  kind : FKind
  pos : Pos
  outer : Array Blk := #[]
  items : Array (Array Blk) := #[]
  tight : Bool := true
  summary : Option (Array Inl) := none
  /-- A disclosure whose summary line was refused, that
  refusal being its one accounting. -/
  refused : Bool := false
  /-- A disclosure opened by a tag that carries `open`. -/
  expanded : Bool := false

private instance : Inhabited Frame := ⟨{ kind := .quote, pos := {} }⟩

/-- Closes the innermost frame, wrapping what it accumulated
into the node its container denotes. -/
private def closeTop (frames : Array Frame) (acc : Array Blk) : Array Frame × Array Blk :=
  match frames.back? with
  | none => (frames, acc)
  | some f =>
    let rest := frames.pop
    match f.kind with
    | .quote => (rest, f.outer.push (.quote acc f.pos))
    | .disclosure => (rest, f.outer.push (.disclosure (f.summary.getD #[]) f.expanded acc f.pos))
    | .item _ =>
      match rest.back?.map Frame.kind with
      | some (FKind.list _ _ _) =>
        (rest.modify (rest.size - 1) (fun lf => { lf with items := lf.items.push acc }), f.outer)
      | _ => (rest, f.outer ++ acc)
    | .list ord st _ => (rest, f.outer.push (.list ord st f.tight f.items f.pos) ++ acc)

/-- Closes a refused disclosure frame: its summary ships as
a paragraph, then its body. -/
private def closeRefusedDisclosure (frames : Array Frame) (acc : Array Blk) :
    Array Frame × Array Blk :=
  match frames.back? with
  | none => (frames, acc)
  | some f =>
    let outer := match f.summary with
      | some s => f.outer.push (.para s f.pos)
      | none => f.outer
    (frames.pop, outer ++ acc)

/-- Closes the innermost frame where its own closer never came; a disclosure
there is refused unless its summary was. -/
private def closeUnclosed (file : String) (frames : Array Frame) (acc : Array Blk) :
    Array Frame × Array Blk × Option Diag :=
  match frames.back? with
  | some f =>
    if f.kind == .disclosure then
      let (fs, a) := closeRefusedDisclosure frames acc
      -- premise: refusedDisclosureChecks — a refused summary raises one E0390, not two
      (fs, a, if f.refused then none else some (refuse file .rawHtml f.pos))
    else
      let (fs, a) := closeTop frames acc
      (fs, a, none)
  | none => (frames, acc, none)

/-- Closes every innermost list frame, since a line that
opens no item is past the list. -/
private def closeLists (frames : Array Frame) (acc : Array Blk) : Array Frame × Array Blk :=
  Id.run do
  let mut fs := frames
  let mut a := acc
  for _ in [0:frames.size] do
    match fs.back?.map Frame.kind with
    | some (FKind.list _ _ _) =>
      let (fs', a') := closeTop fs a
      fs := fs'
      a := a'
    | _ => break
  return (fs, a)

/-- The leaf open at the innermost container; a fence
carries its opener's indent (§4.5). -/
private inductive Leaf where
  | none
  | para (lines : Array (String × Pos))
  | fenced (ch : Char) (len : Nat) (info : String) (pos : Pos) (indent : Nat)
      (lines : Array String)
  /-- A refused HTML block still open, its lines consumed to its §4.6 end. -/
  | html (e : HtmlEnd)
  | comment (pos : Pos)
  /-- An open table: its rows so far, each read into its cells. -/
  | table (aligns : Array TableAlign) (header : Array (Array Inl))
      (rows : Array (Array (Array Inl))) (pos : Pos)
  /-- An open indented code block of the docstring dialect: its lines, indent removed. -/
  | indented (lines : Array String) (pos : Pos)
  deriving Inhabited

private def Leaf.isPara : Leaf → Bool
  | .para _ => true
  | _ => false

/-- Whether the line at `i` starts a block that interrupts a paragraph. -/
private def interrupts (cs : Array Char) (i : Nat) : Bool :=
  (atxAt cs i).isSome || thematicAt cs i || (fenceAt cs i).isSome
    || cs[i]? == some '>' || htmlBlockInterruptAt cs i
    || (match bulletAt cs i with
        | some (_, j) => !isBlankFrom cs j
        | none => false)
    || (match orderedAt cs i with
        | some (n, _, j) => n == 1 && !isBlankFrom cs j
        | none => false)

/-- `need` columns of indent consumed from `i` at column `col`: the index and
column past them, or `none`. -/
private def consumeIndent (cs : Array Char) (i col need : Nat) : Option (Nat × Nat) :=
  Id.run do
  let mut k := i
  let mut c2 := col
  for _ in [0:need + 1] do
    if c2 - col ≥ need then return some (k, c2)
    match cs[k]? with
    | some ' ' =>
      c2 := c2 + 1
      k := k + 1
    | some '\t' =>
      c2 := c2 + (4 - c2 % 4)
      k := k + 1
    | _ => return Option.none
  if c2 - col ≥ need then return some (k, c2) else return Option.none

/-- Whether the line at `i` starts any block, including markers that may not
interrupt a paragraph. -/
private def startsAnyBlock (cs : Array Char) (i : Nat) : Bool :=
  interrupts cs i || (bulletAt cs i).isSome || (orderedAt cs i).isSome

/-- An indented code line with its block's four columns of indent removed. -/
private def indentedLine (cs : Array Char) (i col : Nat) : String :=
  match consumeIndent cs i col 4 with
  | some (k, c2) => String.ofList (List.replicate (c2 - col - 4) ' ') ++ sliceStr cs k cs.size
  | none => ""

/-- A closed indented code block, its trailing blank lines dropped. -/
private def indentedBlock (lines : Array String) (pos : Pos) : Blk :=
  let kept := (lines.toList.reverse.dropWhile (·.trimAscii.isEmpty)).reverse
  .code "" (kept.foldl (fun s l => s ++ l ++ "\n") "") pos

/-- Definitions joined to those read before them, each label's first standing. -/
private def addDefs (m : Std.HashMap String LinkDef) (dd : Array (String × LinkDef)) :
    Std.HashMap String LinkDef :=
  dd.foldl (fun m (k, d) => if m.contains k then m else m.insert k d) m

/-- One pass over a markdown text: its blocks, the diagnostics the reader raised, and its link
reference definitions, each label's first; a collecting pass reads no inline content. -/
private def blocksPass (dialect : Dialect) (file : String) (input : String) (included : Bool)
    (known : Option (Std.HashSet String)) (tex : Bool) (refs : Std.HashMap String LinkDef)
    (collect : Bool) : Array Blk × Array Diag × Std.HashMap String LinkDef := Id.run do
  let doc := dialect == .document
  let lines := splitLines input
  let mut frames : Array Frame := #[]
  let mut acc : Array Blk := #[]
  -- premise: mdMetadataChecks — only a mapping opening or closing the document is metadata
  let (front?, firstLine) := match (if doc then metadataAt lines else none) with
    | some (fields, next) => (some fields, next)
    | none => (none, 0)
  let (back?, lastLine) := match (if doc then closingMetadataAt lines firstLine else none) with
    | some (fields, opener) => (some fields, opener)
    | none => (none, lines.size)
  let meta? := if front?.isNone && back?.isNone then none
    else some (front?.getD #[] ++ back?.getD #[])
  if let some fields := meta? then acc := acc.push (.metadata fields { line := 1, col := 1 })
  -- premise: mdCiteChecks — citations are read only where a bibliography takes them
  let cites := match known with
    | some keys => if dialect == .docstring then docGenRead input keys else {}
    | none => { on := doc && (included || meta?.any bibDeclared) }
  let mut leaf : Leaf := .none
  let mut defs : Std.HashMap String LinkDef := {}
  let readInl : Chars → Array Inl × Array Diag := fun ch =>
    if collect then (#[], #[]) else inlines file ch dialect cites tex refs
  let mut diags : Array Diag := #[]
  let mut sawBlank := false
  -- The disclosure frame whose summary a blank line ended, separating summary from body (§4.6).
  let mut blankAfterSummary : Option Nat := none
  -- GFM tries a paragraph as a table header once.
  let mut tableVisited : Option Pos := none
  -- The divisions whose closing fence is still to come, each a reference list's or not.
  let mut divs : Array Bool := #[]
  let mut refsSeen := false
  for li in [0:lines.size] do
    if li < firstLine || li ≥ lastLine then continue
    let some ln := lines[li]? | continue
    let cs := ln.cs
    let lpos : Pos := { line := ln.no, col := 1 }
    -- One past the line's last non-space character.
    let inkEnd := Id.run do
      let mut e := 0
      for k in [0:cs.size] do
        if h : k < cs.size then
          unless isSpaceOrTab cs[k] do e := k + 1
      return e
    -- Match the open containers; a fence does not exempt a line.
    let mut i := 0
    let mut col := 0
    let mut matched := 0
    let mut ok := true
    for fi in [0:frames.size] do
      if ok then
        match (frames[fi]?).map Frame.kind with
        | none => pure ()
        | some FKind.quote =>
          let (j, ind) := indentAt cs i col
          if ind ≤ 3 && cs[j]? == some '>' then
            let j := j + 1
            let j := if ((cs[j]?).map isSpaceOrTab).getD false then j + 1 else j
            i := j
            col := 0
            matched := matched + 1
          else
            ok := false
        | some (FKind.item need) =>
          if i ≥ inkEnd then
            i := cs.size
            matched := matched + 1
          else
            match consumeIndent cs i col need with
            | some (k, c2) =>
              i := k
              col := c2
              matched := matched + 1
            | none => ok := false
        | some (FKind.list _ _ _) | some FKind.disclosure => matched := matched + 1
    -- An open fence's closer is tested after the container prefixes (§4.5).
    match leaf with
    | .fenced fch flen finfo fpos find flines =>
      if !ok then
        -- The fence closes with its container, unclosed (§4.5).
        acc := acc.push (.code finfo (flines.foldl (fun s l => s ++ l ++ "\n") "") fpos)
        leaf := .none
      else
        let rest := cs.extract i cs.size
        let (_, cind) := indentAt rest 0 0
        if cind ≤ 3 && closesFence rest fch flen then
          acc := acc.push (.code finfo (flines.foldl (fun s l => s ++ l ++ "\n") "") fpos)
          leaf := .none
        else
          -- Strip up to the opener's own indent, no more.
          let (ci, _) := indentAt rest 0 0
          let strip := min find ci
          leaf := .fenced fch flen finfo fpos find
            (flines.push (sliceStr rest strip rest.size))
        continue
    | .indented ilines ipos =>
      if ok && (isBlankFrom cs i || (indentAt cs i col).2 ≥ 4) then
        leaf := .indented (ilines.push (if isBlankFrom cs i then "" else indentedLine cs i col)) ipos
        continue
      acc := acc.push (indentedBlock ilines ipos)
      leaf := .none
    | .html e =>
      -- The refused block ends with its container, at a blank line, or on its end literal's line.
      if !ok then
        leaf := .none
      else
        match e with
        | .blank =>
          if isBlankFrom cs i then leaf := .none else continue
        | .lit _ =>
          if htmlEndsIn cs i e then leaf := .none
          continue
    | .comment p =>
      if !ok then
        leaf := .none
      else
        let end_ := findLit cs i "-->"
        -- A suffix or an earlier terminator makes this a larger raw block, refused once.
        if !commentOnly cs i (end_.getD cs.size)
            || end_.any (fun next => !isBlankFrom cs next) then
          diags := diags.push (refuse file .rawHtml p)
          leaf := if end_.isSome then .none else .html (.lit ["-->"])
        else if end_.isSome then leaf := .none
        continue
    | _ => pure ()
    let blank := isBlankFrom cs i
    let closePara : Leaf → Array Blk → Pos → Array Blk × Array Diag × Array (String × LinkDef) :=
      fun l a fallback =>
        match l with
        | .para pls =>
          let (dd, rest) := paraDefs pls
          if rest.isEmpty then (a, #[], dd) else
          let (inl, ds) := readInl (charsOf rest)
          (a.push (.para inl ((rest[0]?.map (·.2)).getD fallback)), ds, dd)
        | .table aligns header rows p => (a.push (.table aligns header rows p), #[], #[])
        | _ => (a, #[], #[])
    -- An unmatched container under an open paragraph is lazy when the line starts no block.
    let (jl, indl) := indentAt cs i col
    if !ok && leaf.isPara && !blank && !(indl < 4 && startsAnyBlock cs jl) then
      if doc then diags := diags.push (refuse file .lazyContinuation lpos)
      else
        leaf := match leaf with
          | .para pls => .para (pls.push (sliceStr cs jl cs.size, { line := ln.no, col := jl + 1 }))
          | .none => .none
          | .fenced ch len info p ind ls => .fenced ch len info p ind ls
          | .html e => .html e
          | .comment p => .comment p
          | .table aligns header rows p => .table aligns header rows p
          | .indented ls p => .indented ls p
      continue
    if !ok then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .none
      for _ in [0:frames.size] do
        if frames.size > matched then
          let (fs, a, d) := closeUnclosed file frames acc
          frames := fs
          acc := a
          if let some d := d then diags := diags.push d
    if blank then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .none
      if acc.isEmpty && frames.back?.any (fun f => f.kind == .disclosure && f.summary.isSome) then
        blankAfterSummary := some (frames.size - 1)
      sawBlank := true
      continue
    let mut opened := true
    for _ in [0:cs.size + 1] do
      if opened then
        opened := false
        let (j, ind) := indentAt cs i col
        if ind ≤ 3 && cs[j]? == some '>' then
          let j2 := j + 1
          let j2 := if ((cs[j2]?).map isSpaceOrTab).getD false then j2 + 1 else j2
          let (a, ds, dd) := closePara leaf acc lpos
          defs := addDefs defs dd
          acc := a
          diags := diags ++ ds
          leaf := .none
          -- A quote is past any list whose item did not match this line.
          let (fs, a2) := closeLists frames acc
          frames := fs
          acc := a2
          frames := frames.push { kind := .quote, pos := lpos, outer := acc }
          acc := #[]
          i := j2
          col := 0
          opened := true
        else if ind ≤ 3 && !thematicAt cs j then
          -- A thematic break outranks a list marker (§4.1).
          let startNew : Option (Bool × Nat × Char × Nat × Nat) :=
            match bulletAt cs j, orderedAt cs j with
            | some (m, k), _ => some (false, 1, m, k, 1)
            | none, some (n, d, k) =>
              -- The marker's own width, without the space after it.
              let dg := Id.run do
                let mut q := j
                for _ in [0:11] do
                  match cs[q]? with
                  | some c => if isAsciiDigit c then q := q + 1 else break
                  | none => break
                return q - j
              some (true, n, d, k, dg + 1)
            | none, none => none
          if let some (ordered, start, marker, k, mw) := startNew then
            let emptyItem := isBlankFrom cs k
            let mayInterrupt := !emptyItem && (!ordered || start == 1)
            unless leaf.isPara && !mayInterrupt do
              let (a, ds, dd) := closePara leaf acc lpos
              defs := addDefs defs dd
              acc := a
              diags := diags ++ ds
              leaf := .none
              let sameList :=
                match frames.back? with
                | some f =>
                  match f.kind with
                  | .list o _ m => o == ordered && m == marker
                  | _ => false
                | none => false
              -- A marker of a different kind starts a new list, so the open one closes first.
              unless sameList do
                let (fs, a2) := closeLists frames acc
                frames := fs
                acc := a2
                frames := frames.push
                  { kind := .list ordered start marker, pos := lpos, outer := acc }
                acc := #[]
              -- A blank line between two items of one list makes it loose.
              if sawBlank && sameList && frames.size > 0 then
                frames := frames.modify (frames.size - 1) (fun f => { f with tight := false })
              -- The item's content indent; `sp` counts spaces beyond the marker's one.
              let (k2, sp) := indentAt cs k 0
              let wide := sp ≥ 4
              let markerCols :=
                if emptyItem then mw + 1 else if wide then k - j else (k - j) + sp
              let contentIdx := if emptyItem || wide then k else k2
              frames := frames.push
                { kind := .item (ind + markerCols), pos := lpos, outer := acc }
              acc := #[]
              i := contentIdx
              col := 0
              opened := true
    -- The line opened no item, so it is past the list.
    let (fs, a) := closeLists frames acc
    frames := fs
    acc := a
    -- A blank line between two blocks of one item makes its list loose.
    let summaryAt? := blankAfterSummary.filter fun d =>
      frames[d]?.any (·.kind == .disclosure)
    let start? : Option Nat := if !sawBlank then none
      else if !acc.isEmpty then some (frames.size - 1) else summaryAt?
    if let some start := start? then
      for fi in [0:start + 1] do
        let idx := start - fi
        if let some f := frames[idx]? then
          match f.kind with
          | .list _ _ _ =>
            frames := frames.modify idx (fun lf => { lf with tight := false })
            break
          | .quote => break
          | _ => pure ()
    -- A line of only container markers opens nothing.
    if isBlankFrom cs i then
      sawBlank := false
      blankAfterSummary := none
      continue
    let (j, ind) := indentAt cs i col
    -- An open table takes the line as its next row unless the line starts another block.
    if let .table aligns header rows tpos := leaf then
      let startsBlock := ind ≥ 4 || (atxAt cs j).isSome || thematicAt cs j
        || (fenceAt cs j).isSome || (htmlBlockKind cs j).isSome
      let cells := if startsBlock then #[]
        else tableCells (charsOfOne (sliceStr cs j cs.size) { line := ln.no, col := j + 1 })
      if cells.isEmpty then
        acc := acc.push (.table aligns header rows tpos)
        leaf := .none
      else
        let (row, ds) := if collect then (#[], #[]) else tableRow file aligns.size cells dialect cites tex refs
        diags := diags ++ ds
        leaf := .table aligns header (rows.push row) tpos
        sawBlank := false
        blankAfterSummary := none
        continue
    -- A delimiter row under a paragraph whose last line has as many cells opens a table.
    let tableStart : Option (Array (String × Pos) × Pos × Array Chars × Array TableAlign) :=
      match leaf with
      | .para pls =>
        if ind ≥ 4 || tableVisited == (pls[0]?.map (·.2)) then Option.none
        else match tableDelimAt cs j, pls.back? with
          | some aligns, some (hs, hp) =>
            let cells := tableCells (charsOfOne hs hp)
            if cells.size == aligns.size then some (pls.pop, hp, cells, aligns) else Option.none
          | _, _ => Option.none
      | _ => Option.none
    -- An HTML block of condition 7 is paragraph text under an open paragraph.
    let htmlStart : Option HtmlEnd := if !doc then Option.none else
      (htmlBlockKind cs j).bind fun (e, interrupts) =>
        if leaf.isPara && !interrupts then Option.none else some e
    -- premise: htmlTwinChecks — every spelling of `open` ships the element open
    let detailsTag := (tagAt cs j).filter fun t => doc && detailsOpen t && isBlankFrom cs t.stop
    let opensDetails := detailsTag.isSome
    let closesDetails := doc && (bareTagAt cs j "details" true).any (isBlankFrom cs ·)
    let inDetails := frames.back?.map Frame.kind == some .disclosure
    let summaryLine := inDetails && !leaf.isPara && acc.isEmpty
      && (frames.back?.bind Frame.summary).isNone && !(frames.back?.any (·.refused))
    let summary := if summaryLine then summaryAt cs j lpos else none
    -- premise: refusedDisclosureChecks — each refused summary raises one E0390
    if summaryLine && summary.isNone && ind < 4 && blockTagStartsAt cs j "summary" then
      frames := frames.modify (frames.size - 1) fun f => { f with refused := true }
    if ind ≥ 4 && !leaf.isPara then
      if doc then diags := diags.push (refuse file .indentedCode lpos)
      else
        let (a, ds, dd) := closePara leaf acc lpos
        defs := addDefs defs dd
        acc := a
        diags := diags ++ ds
        leaf := .indented #[indentedLine cs i col] lpos
    else if ind ≥ 4 && leaf.isPara then
      -- Four spaces under an open paragraph is continuation text, not a block start.
      leaf := .para (match leaf with
        | .para pls => pls.push (sliceStr cs j cs.size, { line := ln.no, col := j + 1 })
        | _ => #[(sliceStr cs j cs.size, { line := ln.no, col := j + 1 })])
    else if opensDetails then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      diags := diags ++ ds
      leaf := .none
      frames := frames.push
        { kind := .disclosure, pos := { lpos with col := j + 1 }, outer := a
          expanded := detailsTag.any (!·.attrs.isEmpty) }
      acc := #[]
    else if closesDetails && inDetails then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      diags := diags ++ ds
      leaf := .none
      let summaryless := frames.back?.any (·.summary.isNone)
      if let some f := frames.back? then
        -- premise: refusedDisclosureChecks — a refused summary raises one E0390, not two
        if summaryless && !f.refused then diags := diags.push (refuse file .rawHtml f.pos)
      let (fs, a) := (if summaryless then closeRefusedDisclosure else closeTop) frames a
      frames := fs
      acc := a
    else if let some ss := summary then
      frames := frames.modify (frames.size - 1)
        (fun f => { f with summary := some ss })
    else if let some (level, k) := atxAt cs j then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .none
      let raw := rstrip (sliceStr cs k cs.size)
      let rc := raw.toList.reverse
      let hashes := (rc.takeWhile (· == '#')).length
      let body :=
        if hashes == raw.length then ""
        else if hashes > 0 && (rc.drop hashes).headD 'x' == ' ' then
          rstrip (String.ofList (raw.toList.take (raw.length - hashes)))
        else raw
      let (inl, ds2) := readInl (charsOfOne (body.trimAscii.toString) { line := ln.no, col := k + 1 })
      acc := acc.push (.heading level inl lpos)
      diags := diags ++ ds2
    else if leaf.isPara && (setextAt cs j).isSome then
      -- A `---` line under a paragraph is a setext underline, not a thematic break; under one only
      -- link reference definitions open, it is the paragraph's text (§4.7).
      let level := (setextAt cs j).getD 1
      match leaf with
      | .para pls =>
        let (dd, rest) := paraDefs pls
        if rest.isEmpty then
          leaf := .para (pls.push (sliceStr cs j cs.size, { line := ln.no, col := j + 1 }))
        else
          defs := addDefs defs dd
          let (inl, ds) := readInl (charsOf rest)
          acc := acc.push (.heading level inl ((rest[0]?.map (·.2)).getD lpos))
          diags := diags ++ ds
          leaf := .none
      | _ => leaf := .none
    else if thematicAt cs j then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .none
      acc := acc.push (.rule lpos)
    else if let some attrs := (if doc && ind ≤ 3 then leanDivAt cs j else none) then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a.push (.lean attrs { lpos with col := j + 1 })
      diags := diags ++ ds
      leaf := .none
      divs := divs.push false
    else if let some extra := (if doc && ind ≤ 3 then refsDivAt cs j else none) then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .none
      let p := { lpos with col := j + 1 }
      if refsSeen then
        diags := diags.push (Diag.of .W0392 "a second '::: {#refs}' division holds no list: the \
reference list stands in the first" (some ⟨file, p⟩) (subject := some "md:refs-second"))
      else if extra then
        diags := diags.push (Diag.of .W0392 "the reference list's division sets without its \
other attributes" (some ⟨file, p⟩) (subject := some "md:refs-attrs"))
      divs := divs.push !refsSeen
      refsSeen := true
    else if doc && !divs.isEmpty && ind ≤ 3 && closesDiv cs j then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := if divs.back? == some true then a.push (.refs { lpos with col := j + 1 }) else a
      diags := diags ++ ds
      leaf := .none
      divs := divs.pop
    else if let some (fch, flen, finfo) := fenceAt cs j then
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      leaf := .fenced fch flen (decodeInfo finfo) lpos (j - i) #[]
    else if let some e := htmlStart then
      -- The refusal names the construct's own column, not the line's.
      let (a, ds, dd) := closePara leaf acc lpos
      defs := addDefs defs dd
      acc := a
      diags := diags ++ ds
      let p := { lpos with col := j + 1 }
      -- premise: mdSurfaceChecks — only a comment-only block is consumed without loss
      if litAt cs j "<!--" then
        let end_ := findLit cs (j + 2) "-->"
        if !commentOnly cs j (end_.getD cs.size)
            || end_.any (fun next => !isBlankFrom cs next) then
          diags := diags.push (refuse file .rawHtml p)
          leaf := if end_.isSome then .none else .html (.lit ["-->"])
        else
          leaf := if end_.isSome then .none else .comment p
      else
        diags := diags.push (refuse file .rawHtml p)
        leaf := if htmlEndsIn cs j e then .none else .html e
    else if let some (before, hp, cells, aligns) := tableStart then
      let (a, ds, dd) := closePara (if before.isEmpty then .none else .para before) acc lpos
      defs := addDefs defs dd
      let (header, ds2) := if collect then (#[], #[]) else tableRow file aligns.size cells dialect cites tex refs
      acc := a
      diags := diags ++ ds ++ ds2
      leaf := .table aligns header #[] hp
    else
      let text := sliceStr cs j cs.size
      match leaf with
      | .para pls =>
        -- A delimiter row that opened no table is text.
        if ind < 4 && (tableDelimAt cs j).isSome then tableVisited := pls[0]?.map (·.2)
        leaf := .para (pls.push (text, { line := ln.no, col := j + 1 }))
      | _ => leaf := .para #[(text, { line := ln.no, col := j + 1 })]
    sawBlank := false
    blankAfterSummary := none
  match leaf with
  | .para pls =>
    let (dd, rest) := paraDefs pls
    defs := addDefs defs dd
    unless rest.isEmpty do
      let (inl, ds) := readInl (charsOf rest)
      acc := acc.push (.para inl ((rest[0]?.map (·.2)).getD {}))
      diags := diags ++ ds
  | .fenced _ _ finfo fpos _ flines =>
    acc := acc.push (.code finfo (flines.foldl (fun s l => s ++ l ++ "\n") "") fpos)
  | .indented ilines ipos => acc := acc.push (indentedBlock ilines ipos)
  | .table aligns header rows p => acc := acc.push (.table aligns header rows p)
  | .html _ => pure ()
  | .comment _ => pure ()
  | .none => pure ()
  for _ in [0:frames.size] do
    let (fs, a, d) := closeUnclosed file frames acc
    frames := fs
    acc := a
    if let some d := d then diags := diags.push d
  return (acc, diags, defs)

/-- Blocks for one markdown text in a dialect, and the diagnostics the reader raised; a first pass
reads its link reference definitions, which a link may use before or after they stand (§4.7). -/
public def blocksIn (dialect : Dialect) (file : String) (input : String) (included : Bool := false)
    (known : Option (Std.HashSet String) := none) (tex : Bool := false) :
    Array Blk × Array Diag :=
  let refs := if holdsRefColon input then
      (blocksPass dialect file input included known tex {} true).2.2
    else {}
  let (blocks, diags, _) := blocksPass dialect file input included known tex refs false
  (blocks, diags)

/-- Blocks for one markdown document, and the diagnostics the reader raised. -/
public def blocks (file : String) (input : String) : Array Blk × Array Diag :=
  blocksIn .document file input

/-- The citation keys a text names, Pandoc's `nocite` reading: each `@key`, and `@*` for every
entry. -/
public def citeKeys (s : String) : Array String := Id.run do
  let c := charsOfOne s {}
  let braces := braceMatches c
  let mut keyEnds : Std.HashSet Nat := {}
  let mut out : Array String := #[]
  let mut i := 0
  for _ in [0:c.size + 1] do
    if i ≥ c.size then break
    let scan : CiteScan := { closers := {}, keyEnds, braces }
    if c.at? i == some '@' && c.at? (i + 1) == some '*' && citeMayOpen c scan i then
      out := out.push "*"
      i := i + 2
      keyEnds := keyEnds.insert i
    else if c.at? i == some '@' then
      match citeKeyAt c scan i with
      | some (_, key, next) =>
        out := out.push key
        i := next
        keyEnds := keyEnds.insert i
      | none => i := i + 1
    else i := i + 1
  return out

end LeanTex.Core.Md
