import LeanTex.Core.Diag

/-! # The markdown surface: source → md AST

Markdown has no semantics of its own in this engine: its meaning *is* its
desugaring into the tex-shaped surface AST (`MdDesugar`), which the one
elaborator then reads. This module is only the reader — source text to an
md AST carrying `.md` spans, so every diagnostic downstream names the
markdown line the reader saw.

Dialect: CommonMark-shaped but strict. Three constructs are refused by
design rather than silently diverging, each an `E0390` carrying the class
as its subject:

* `raw-html` — raw HTML passthrough. What keeps the injection-safety
  argument short is that document content can never become markup; a
  passthrough is the one carve-out that would reopen it.
* `indented-code` — a four-space indent as a code block. Measured
  ambiguity: the same indent means continuation inside a list and code
  outside one.
* `lazy-continuation` — a paragraph line inside a container that omits the
  container's own marker.

Each refusal carries a fix-it in its message, and each is a *data*
decision: the verdict rows in `tests/commonmark/verdicts.tsv` say which
spec cases the class touches, so flipping one is a table change plus a
reader arm, never a redesign.

Block structure is one pass over the lines with an explicit container
stack — `Parse.parse`'s frame shape, so totality is immediate and the
checker needs no help. Inline structure is a flat token array plus
CommonMark's delimiter-run algorithm, matched into a pair table and then
built into a tree by the same frame shape. -/

namespace LeanTex.Core.Md

open LeanTex.Core

/-- An inline node. `pos` is the position in the `.md` source. -/
inductive Inl where
  | text (s : String) (pos : Pos)
  | code (s : String) (pos : Pos)
  | emph (body : Array Inl) (pos : Pos)
  | strong (body : Array Inl) (pos : Pos)
  | link (dest : String) (title : String) (body : Array Inl) (pos : Pos)
  | image (dest : String) (title : String) (alt : Array Inl) (pos : Pos)
  | soft (pos : Pos)
  | hard (pos : Pos)
  deriving Repr, BEq

instance : Inhabited Inl := ⟨.soft {}⟩

/-- A block node. A list holds one `Array Blk` per item. -/
inductive Blk where
  | para (body : Array Inl) (pos : Pos)
  | heading (level : Nat) (body : Array Inl) (pos : Pos)
  | code (info : String) (text : String) (pos : Pos)
  | rule (pos : Pos)
  | quote (body : Array Blk) (pos : Pos)
  | list (ordered : Bool) (start : Nat) (tight : Bool) (items : Array (Array Blk))
      (pos : Pos)
  deriving Repr, BEq

instance : Inhabited Blk := ⟨.rule {}⟩

-- ## Character classes

def isSpaceOrTab (c : Char) : Bool := c == ' ' || c == '\t'

/-- CommonMark's Unicode whitespace: space, tab, newline, form feed,
carriage return. -/
def isMdSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- ASCII punctuation, the spec's `punctuation` for flanking purposes. The
spec widens this to Unicode punctuation and symbols; the widening is a
declared verdict row, not a silent narrowing. -/
def isMdPunct (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".any (· == c)

def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

-- ## Lines

/-- One source line as characters, with its 1-based line number. Scanning
is over `Array Char` so every index is O(1); a line is short, and the
whole document allocates one array's worth of characters. -/
structure Line where
  cs : Array Char
  no : Nat
  deriving Inhabited

/-- The reader's line-splitting accumulator: the lines closed so far, the
line being built, and its number. -/
private structure LineAcc where
  out : Array Line
  cur : Array Char
  no : Nat

def splitLines (input : String) : Array Line :=
  -- Folded over the string rather than over `input.toList`: the whole
  -- document is the input here, and materializing it as a cons list is one
  -- allocation per character before the reader has looked at anything. The
  -- accumulator is uniquely owned through the fold, so each `push` appends
  -- in place.
  let step (a : LineAcc) (c : Char) : LineAcc :=
    if c == '\n' then { out := a.out.push ⟨a.cur, a.no⟩, cur := #[], no := a.no + 1 }
    else if c == '\r' then a
    else { a with cur := a.cur.push c }
  let a := input.foldl step { out := #[], cur := #[], no := 1 }
  -- A trailing newline ends the last line; text after it is one more line.
  if a.cur.isEmpty then a.out else a.out.push ⟨a.cur, a.no⟩

/-- Where the line's content starts and how many columns of indent precede
it, counting a tab as advancing to the next multiple of four. -/
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

-- ## Block starts

/-- `#`×1–6 then a space or end of line: the level and the index past the
marker, or `none`. -/
def atxAt (cs : Array Char) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut j := i
  let mut n := 0
  for _ in [0:7] do
    if h : j < cs.size then
      if cs[j] == '#' && n < 7 then
        n := n + 1
        j := j + 1
  if n == 0 || n > 6 then return none
  match cs[j]? with
  | none => return some (n, j)
  | some c => if isSpaceOrTab c then return some (n, j + 1) else return none

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

/-- A closing fence for an open one: at most three spaces of indent, the
same char at least as long, nothing after it. -/
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

/-- An ordered marker: the start number, the delimiter, and the index past
it. At most nine digits, per the spec. -/
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

/-- A setext underline: one run of `=` or of `-`, then only trailing spaces
or tabs (§4.3). Returns the level. Spaces *inside* the run are not an
underline: `Foo` over `- - -` is a paragraph and a thematic break, and
accepting them set it as a heading. -/
def setextAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  let some c0 := cs[i]? | return none
  unless c0 == '=' || c0 == '-' do return none
  let mut j := i
  for _ in [0:cs.size + 1] do
    if cs[j]? == some c0 then j := j + 1 else break
  unless isBlankFrom cs j do return none
  return some (if c0 == '=' then 1 else 2)

-- ## Raw HTML, recognized rather than guessed
--
-- The dialect refuses raw HTML, so what counts *as* raw HTML decides what
-- the reader refuses — and a test wider than the grammar refuses valid
-- CommonMark. Twenty-nine spec cases were refused by a test that fired on
-- any `<` followed by a letter: `<https://example.org>` at the start of a
-- line, and literal text such as `x <y for comparison`. So the tag grammar
-- (§6.6) is implemented, and anything it does not accept is text.

/-- Is the literal `lit` at `i`, case-folded? -/
def litAt (cs : Array Char) (i : Nat) (lit : String) : Bool := Id.run do
  let ls := lit.toList.toArray
  for k in [0:ls.size] do
    if h : k < ls.size then
      match cs[i + k]? with
      | none => return false
      | some c => unless c.toLower == ls[k].toLower do return false
  return true

/-- The index past the first occurrence of `lit` at or after `i`. -/
def findLit (cs : Array Char) (i : Nat) (lit : String) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    if j > cs.size then break
    if litAt cs j lit then return some (j + lit.length)
    j := j + 1
  return none

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

/-- One attribute at `i`, its leading whitespace already consumed. -/
def attrAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  let some c0 := cs[i]? | return none
  unless isAttrStart c0 do return none
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | some c => if isAttrRest c then j := j + 1 else break
    | none => break
  -- An optional value, after optional whitespace either side of `=`.
  let k := wsAt cs j
  if cs[k]? == some '=' then
    let v := wsAt cs (k + 1)
    match attrValueAt cs v with
    | some e => return some e
    | none => return some j
  return some j

/-- A complete raw-HTML construct at `i` (§6.6): an open tag, a closing tag,
a comment, a processing instruction, a declaration, or CDATA. The index past
it, or `none` — and `none` means the text is text. -/
def htmlTagAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  unless cs[i]? == some '<' do return none
  if litAt cs i "<!--" then return findLit cs (i + 4) "-->"
  if litAt cs i "<![CDATA[" then return findLit cs (i + 9) "]]>"
  if litAt cs i "<?" then return findLit cs (i + 2) "?>"
  if cs[i + 1]? == some '!' then
    if ((cs[i + 2]?).map isAsciiAlpha).getD false then
      return findLit cs (i + 2) ">"
    return none
  if cs[i + 1]? == some '/' then
    let some j := tagNameAt cs (i + 2) | return none
    let j := wsAt cs j
    if cs[j]? == some '>' then return some (j + 1) else return none
  let some j := tagNameAt cs (i + 1) | return none
  let mut k := j
  for _ in [0:cs.size + 1] do
    let w := wsAt cs k
    if w == k then break
    match attrAt cs w with
    | some k2 => k := k2
    | none => break
  let e0 := wsAt cs k
  let e := if cs[e0]? == some '/' then e0 + 1 else e0
  if cs[e]? == some '>' then return some (e + 1) else return none

/-- The tag names §4.6 condition 1 names: their block runs to a closing tag,
not to a blank line. -/
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

/-- A tag name at `i` drawn from `names`, ending at whitespace, `>`, `/>` or
the end of the line. -/
private def namedTagAt (cs : Array Char) (i : Nat) (names : List String) : Bool :=
  match tagNameAt cs i with
  | none => false
  | some j =>
    let nm := (sliceStr cs i j).toLower
    names.contains nm &&
      (match cs[j]? with
       | none => true
       | some c => isMdSpace c || c == '>' || (c == '/' && cs[j + 1]? == some '>'))

/-- Does an HTML block start at `i` (§4.6)? Conditions 1–6 by their own
tests; condition 7 is a complete tag with nothing but whitespace after it.
Condition 7 may not interrupt a paragraph, which is `interrupts`' business,
not this one's. -/
def htmlBlockAt (cs : Array Char) (i : Nat) : Bool := Id.run do
  unless cs[i]? == some '<' do return false
  if litAt cs i "<!--" || litAt cs i "<?" || litAt cs i "<![CDATA[" then return true
  if cs[i + 1]? == some '!' && ((cs[i + 2]?).map isAsciiAlpha).getD false then return true
  if namedTagAt cs (i + 1) htmlRawTags then return true
  if namedTagAt cs (i + 1) htmlBlockTags then return true
  if cs[i + 1]? == some '/' && namedTagAt cs (i + 2) htmlBlockTags then return true
  match htmlTagAt cs i with
  | some j => return isBlankFrom cs j
  | none => return false

/-- Conditions 1–6 only: what may interrupt a paragraph. Condition 7 may
not, and reading it as an interrupter refused a paragraph line holding a
bare `<span>`. -/
def htmlBlockInterruptAt (cs : Array Char) (i : Nat) : Bool := Id.run do
  unless cs[i]? == some '<' do return false
  if litAt cs i "<!--" || litAt cs i "<?" || litAt cs i "<![CDATA[" then return true
  if cs[i + 1]? == some '!' && ((cs[i + 2]?).map isAsciiAlpha).getD false then return true
  if namedTagAt cs (i + 1) htmlRawTags then return true
  if namedTagAt cs (i + 1) htmlBlockTags then return true
  if cs[i + 1]? == some '/' && namedTagAt cs (i + 2) htmlBlockTags then return true
  return false

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-! ## Inline structure

CommonMark's inline phase in three passes, each an index loop: a scan into
a flat token array (brackets resolved against a stack as they close), the
delimiter-run match into a pair table, and a tree build over the pairs with
the frame shape `Parse.parse` uses — index loops throughout. -/

/-- One inline token. A `run` is a delimiter run of `*` or `_` with its
flanking verdicts already computed. -/
inductive ITok where
  | txt (s : String) (pos : Pos)
  | code (s : String) (pos : Pos)
  | soft (pos : Pos)
  | hard (pos : Pos)
  | auto (dest : String) (text : String) (pos : Pos)
  | run (ch : Char) (len : Nat) (canOpen canClose : Bool) (pos : Pos)
  | bopen (image : Bool) (pos : Pos)
  | bclose (pos : Pos)
  deriving Repr

instance : Inhabited ITok := ⟨.soft {}⟩

def ITok.pos : ITok → Pos
  | .txt _ p | .code _ p | .soft p | .hard p | .auto _ _ p
  | .run _ _ _ _ p | .bopen _ p | .bclose p => p

/-- A resolved link or image: the token indices of its brackets, whether it
is an image, and its destination and title. -/
structure BPair where
  openTok : Nat
  closeTok : Nat
  image : Bool
  dest : String
  title : String
  deriving Inhabited, Repr

/-- One matched emphasis pair: the run tokens it joins, how many delimiter
characters it consumes from each, and its creation index — the order the
delimiter algorithm produced it, which is innermost first. -/
structure EPair where
  openTok : Nat
  closeTok : Nat
  strong : Bool
  born : Nat
  deriving Inhabited, Repr

/-- The characters of an inline stretch, each with the `.md` position it
came from, so a diagnostic names the line the reader saw. -/
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

/-- A delimiter run's flanking verdicts, from the characters either side
(CommonMark §6.2). -/
def flanking (before after : Option Char) : Bool × Bool :=
  let wsBefore := (before.map isMdSpace).getD true
  let wsAfter := (after.map isMdSpace).getD true
  let puBefore := (before.map isMdPunct).getD false
  let puAfter := (after.map isMdPunct).getD false
  let left := !wsAfter && (!puAfter || wsBefore || puBefore)
  let right := !wsBefore && (!puBefore || wsAfter || puAfter)
  (left, right)

/-- An ASCII-punctuation backslash escape, or `none` where the backslash is
literal. -/
def escaped? (c : Chars) (i : Nat) : Option Char := do
  guard (c.at? i == some '\\')
  let d ← c.at? (i + 1)
  guard (isMdPunct d)
  some d

/-- A code span opening at `i` with a backtick string of length `n`: the
content and the index past the closing string, or `none` when no closing
string of the same length follows. -/
def codeSpanAt (c : Chars) (i n : Nat) : Option (String × Nat) := Id.run do
  let mut j := i + n
  for _ in [0:c.size + 1] do
    if j ≥ c.size then return none
    if c.at? j == some '`' then
      let mut m := 0
      let mut k := j
      for _ in [0:c.size + 1] do
        if c.at? k == some '`' then
          m := m + 1
          k := k + 1
        else break
      if m == n then
        -- Strip one space from each end when both are present and the
        -- content is not all spaces (spec §6.1).
        let raw := (c.str (i + n) j).toList
        let stripped :=
          if raw.length ≥ 2 && raw.headD 'x' == ' ' && raw.getLastD 'x' == ' '
              && !(raw.all (· == ' ')) then
            (raw.drop 1).dropLast
          else raw
        -- Line endings inside a code span are spaces.
        return some (String.ofList (stripped.map (fun ch => if ch == '\n' then ' ' else ch)), k)
      else
        j := k
    else
      j := j + 1
  return none

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

/-- A run of whitespace in an inline stretch: the index past it. Spelled as a
loop that stops, because a bounded `for` used as a while-loop without a break
is the shape that made this phase quadratic: five of these ran to `c.size`
once per token. -/
def Chars.ws (c : Chars) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:c.size + 1] do
    if (c.at? j).map isMdSpace == some true then j := j + 1 else break
  return j

/-- An autolink `<scheme:...>` or `<local@domain>` at `i`: the destination,
the link text, and the index past `>`. -/
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
      if isMdSpace ch then return none
      j := j + 1
  return none

/-- A link destination and optional title starting at `(`: the destination,
the title, and the index past `)`. Angle-bracket destinations and one level
of balanced parentheses, which is what the inline form needs. -/
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
        if isMdSpace ch then break
        else if ch == '(' then
          depth := depth + 1
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
  -- Optional whitespace, then an optional title in `"`, `'` or `(`.
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

/-- Named and numeric character references (§2.5). Only the five the engine
needs by name plus the numeric forms resolve here; anything else stays
literal, a declared verdict row rather than a silent drop. -/
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
        if isAsciiDigit ch then some (ch.toNat - '0'.toNat)
        else if hex && 'a' ≤ ch && ch ≤ 'f' then some (ch.toNat - 'a'.toNat + 10)
        else if hex && 'A' ≤ ch && ch ≤ 'F' then some (ch.toNat - 'A'.toNat + 10)
        else none
      match d with
      | none => return none
      | some d => n := n * (if hex then 16 else 10) + d
    -- A null or out-of-range code point is replaced (§2.3, §2.5).
    let cp := if n == 0 || n > 0x10ffff || (n ≥ 0xd800 && n ≤ 0xdfff) then 0xfffd else n
    return some (String.singleton (Char.ofNat cp), j + 1)
  | _ => return none

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-- What the reader refuses by design, as the subject its diagnostic
carries. A class is data: the verdict table names the spec cases each one
touches, so a dialect decision flips a row and one reader arm. -/
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
  | .rawHtml => "quote the text as a code span with `...`, or delete the tag"
  | .indentedCode => "fence the block with ``` instead"
  | .lazyContinuation => "indent the line to its container's content column, or repeat a quote's '>'"

/-- The refusal, as a diagnostic. The subject is what folds repeats into one
line with a site count (`Diag.tallySites`), so a document with fifty raw
tags reports one error naming fifty sites. -/
def refuse (file : String) (s : Strict) (pos : Pos) : Diag :=
  { kind := .E0390, message := s.message, span := some ⟨file, pos⟩,
    help := some s.fixit, subject := some s.subject }

/-- The scan: characters to a flat token array, with brackets resolved
against a stack as they close and the refusals raised where they are seen. -/
def scanInlines (file : String) (c : Chars) :
    Array ITok × Array BPair × Array Diag := Id.run do
  let mut toks : Array ITok := #[]
  let mut pairs : Array BPair := #[]
  let mut diags : Array Diag := #[]
  let mut stack : Array (Nat × Bool) := #[]   -- token index, image
  -- Link openers below this stack depth are inactive: a link closed while
  -- they were open (§6.3). Lowered as the stack pops below it.
  let mut inactiveBelow : Nat := 0
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
      if ch == '\\' then
        match escaped? c i with
        | some d =>
          pending := pending.push d
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
        match codeSpanAt c i n with
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
          pending := pending ++ v
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
          -- Raw HTML: refused by design, and the text is dropped. Only a
          -- complete tag (§6.6) is raw HTML; anything else is text, which
          -- is why `x <y for comparison` no longer fails the build.
          match htmlTagAt c.cs i with
          | some next =>
            diags := diags.push (refuse file .rawHtml p)
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
      else if ch == '!' && c.at? (i + 1) == some '[' then
        toks := flush toks pending pendingPos
        pending := ""
        stack := stack.push (toks.size, true)
        toks := toks.push (.bopen true p)
        i := i + 2
      else if ch == '[' then
        toks := flush toks pending pendingPos
        pending := ""
        stack := stack.push (toks.size, false)
        toks := toks.push (.bopen false p)
        i := i + 1
      else if ch == ']' then
        -- The nearest opener, and an inline destination after it.
        match stack.back? with
        | none =>
          pending := pending.push ']'
          i := i + 1
        | some (openTok, image) =>
          let active := image || stack.size - 1 ≥ inactiveBelow
          stack := stack.pop
          inactiveBelow := min inactiveBelow stack.size
          match (if active then linkTailAt c (i + 1) else none) with
          | some (dest, title, next) =>
            toks := flush toks pending pendingPos
            pending := ""
            let closeTok := toks.size
            toks := toks.push (.bclose p)
            pairs := pairs.push
              { openTok, closeTok, image, dest, title }
            -- A link may not contain a link: every link opener still open
            -- goes inactive (§6.3), which is one number, not a pass over
            -- the stack — the pass made `[a [b](c)` repeated quadratic.
            -- An image opener stays active: an image's text may hold a
            -- link, and deactivating it lost the image around one.
            unless image do inactiveBelow := stack.size
            i := next
          | none =>
            pending := pending.push ']'
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
        toks := flush toks pending pendingPos
        pending := ""
        toks := toks.push (.run ch n canOpen canClose p)
        i := k
      else
        pending := pending.push ch
        i := i + 1
  toks := flush toks pending pendingPos
  return (toks, pairs, diags)

/-- The bracket region of each token — the *innermost* resolved link or image
around it, `0` outside every one — and the number of regions. Two emphasis
delimiters pair only inside one region, which is how the spec's per-link
pass (§6.3: process emphasis on the link text when the link closes) shows
up in one array. Innermost matters: filled pair by pair, an image's region
overwrote the link inside it, and a delimiter in the link could pair with
one in the image around it. One pass with a stack, so nesting depth costs
nothing. -/
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

/-- CommonMark's delimiter-run match (§6.2, "process emphasis"), run once
per bracket region over that region's runs alone, as cmark does.

Three rules the spec states and a single pass over the whole array got
wrong, each a reproduced defect:

* **The openers-bottom floor is per region.** It is the position below
  which a closer of one (character, original length mod 3, can-also-open)
  shape has been shown to have no partner. Shared across regions, a closer
  inside a link that found no partner raised the floor above a valid
  opener outside it, and `*a [b*](c) d*` stopped pairing.
* **A match removes every delimiter between opener and closer.** The
  potential openers are a stack; matching one pops everything above it.
  Left in place, `*foo _bar* baz_` paired the `_` across the `*` pair and
  built crossing emphasis.
* **The rule of three reads the original run lengths**, and so does the
  floor's shape: a run's remaining length changes as it is consumed, the
  run it came from does not.

Linear: every run is pushed at most once and popped at most once, a search
that passes a stack entry either pops it or is bounded by a floor that then
rises past it, and there are twelve floors per region. -/
def matchEmphasis (toks : Array ITok) (reg : Array Nat) (nRegions : Nat) :
    Array EPair × Array Nat := Id.run do
  let mut len : Array Nat := Array.replicate toks.size 0
  let mut orig : Array Nat := Array.replicate toks.size 0
  let mut ch : Array Char := Array.replicate toks.size ' '
  let mut op : Array Bool := Array.replicate toks.size false
  let mut cl : Array Bool := Array.replicate toks.size false
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
    | _ => pure ()
  let rd : Array Nat → Nat → Nat := fun a i => (a[i]?).getD 0
  let rb : Array Bool → Nat → Bool := fun a i => (a[i]?).getD false
  let rc : Array Char → Nat → Char := fun a i => (a[i]?).getD ' '
  let mut out : Array EPair := #[]
  let mut born := 0
  for runs in byRegion do
    -- The potential openers still alive, bottom to top, as token indices.
    let mut stack : Array Nat := #[]
    -- One floor per (character, closer can also open, original length mod
    -- 3): a closer of that shape examines only openers at or above it.
    let mut bottom : Array Nat := Array.replicate 12 0
    for ci in runs do
      if rb cl ci then
        let bkt := (if rc ch ci == '*' then 0 else 6)
          + (if rb op ci then 3 else 0) + rd orig ci % 3
        for _ in [0:rd orig ci] do
          if rd len ci == 0 then break
          -- The nearest opener of the same character, no lower than the floor.
          let mut found : Option Nat := none
          let mut si := stack.size
          for _ in [0:stack.size] do
            if si == 0 then break
            si := si - 1
            let oi := rd stack si
            if oi < rd bottom bkt then break
            if rc ch oi == rc ch ci then
              -- Rule of three, on the original lengths: when either run
              -- can both open and close, the sum may not be a multiple of
              -- three unless both are.
              let ok := !(rb op ci || rb cl oi) || rd orig ci % 3 == 0
                || (rd orig oi + rd orig ci) % 3 != 0
              if ok then
                found := some si
                break
          match found with
          | none =>
            -- No partner for this shape at or above the floor: nothing
            -- below this closer can ever partner a closer of its shape.
            bottom := bottom.set! bkt ci
            break
          | some s =>
            let oj := rd stack s
            -- Everything between the pair is removed.
            stack := stack.extract 0 (s + 1)
            let strong := rd len oj ≥ 2 && rd len ci ≥ 2
            let use := if strong then 2 else 1
            len := len.set! oj (rd len oj - use)
            len := len.set! ci (rd len ci - use)
            out := out.push { openTok := oj, closeTok := ci, strong, born }
            born := born + 1
            if rd len oj == 0 then stack := stack.pop
      -- What is left of a run that can open is a potential opener.
      if rb op ci && rd len ci > 0 then stack := stack.push ci
  return (out, len)

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

/-- The tree, from the token array and the two pair tables: one left-to-right
pass with a frame stack. A run token that both closes and opens does its
closes first, then its unconsumed delimiter characters as text, then its
opens — outermost first, which is the reverse of the order the matcher
created them in.

The pair tables are indexed by token once, before the pass. Filtered per
token, the four lookups made this walk quadratic: 112 KB of links took
55.3 s, against 0.6 s for the same content as tex. -/
def buildInlines (toks : Array ITok) (bpairs : Array BPair) (epairs : Array EPair)
    (leftover : Array Nat) : Array Inl := Id.run do
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
  let mut frames : Array OFrame := #[]
  let mut acc : Array Inl := #[]
  for i in [0:toks.size] do
    let some t := toks[i]? | continue
    let p := t.pos
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

/-- Inline structure for one stretch of text, in three passes. -/
def inlines (file : String) (c : Chars) : Array Inl × Array Diag :=
  let (toks, bpairs, diags) := scanInlines file c
  let (reg, nRegions) := regions toks bpairs
  let (epairs, leftover) := matchEmphasis toks reg nRegions
  (buildInlines toks bpairs epairs leftover, diags)

/-- The characters of a run of paragraph lines, newline-separated, each
character carrying its source position. -/
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
      ps := ps.push ⟨p.line, col⟩
      col := col + 1
  return ⟨cs, ps⟩

def charsOfOne (s : String) (p : Pos) : Chars := charsOf #[(s, p)]

end LeanTex.Core.Md



namespace LeanTex.Core.Md

open LeanTex.Core

/-! ## Block structure

One pass over the lines with an explicit container stack, the shape
`Parse.parse` uses: a frame holds the accumulator that was open outside it,
and closing a frame wraps the inner blocks into the node its container
denotes. No recursion, so totality is immediate. -/

private inductive FKind where
  | quote
  | list (ordered : Bool) (start : Nat) (marker : Char)
  | item (indent : Nat)
  deriving Repr, BEq, Inhabited

private structure Frame where
  kind : FKind
  pos : Pos
  outer : Array Blk := #[]
  items : Array (Array Blk) := #[]
  tight : Bool := true

private instance : Inhabited Frame := ⟨{ kind := .quote, pos := {} }⟩

/-- Close the innermost frame, wrapping what it accumulated into the node its
container denotes. The one closing definition every site uses, and it drops
nothing: a list's own accumulator — blocks that reached the list frame
outside any item — is carried after the list. Four sites once closed a list
by hand as `outer.push list`, and each discarded that accumulator; when a
frame outlived its items, everything after it shipped nowhere. -/
private def closeTop (frames : Array Frame) (acc : Array Blk) : Array Frame × Array Blk :=
  match frames.back? with
  | none => (frames, acc)
  | some f =>
    let rest := frames.pop
    match f.kind with
    | .quote => (rest, f.outer.push (.quote acc f.pos))
    | .item _ =>
      match rest.back?.map Frame.kind with
      | some (FKind.list _ _ _) =>
        (rest.modify (rest.size - 1) (fun lf => { lf with items := lf.items.push acc }), f.outer)
      | _ => (rest, f.outer ++ acc)
    | .list ord st _ => (rest, f.outer.push (.list ord st f.tight f.items f.pos) ++ acc)

/-- Close every list frame that is innermost. A list frame lives only as long
as its items: a line that opens no item inside it — a thematic break, a
quote, a paragraph — is past the list. -/
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

/-- The leaf open at the innermost container. A fence carries the indent its
opener stood at: §4.5 strips up to that many columns from each content line,
so a fence inside a list item does not ship the item's indent as code. -/
private inductive Leaf where
  | none
  | para (lines : Array (String × Pos))
  | fenced (ch : Char) (len : Nat) (info : String) (pos : Pos) (indent : Nat)
      (lines : Array String)
  deriving Inhabited

private def Leaf.isPara : Leaf → Bool
  | .para _ => true
  | _ => false

/-- Does the line at `i` start a block that interrupts a paragraph? The
spec's interrupter list, which is what decides whether a paragraph ends. -/
private def interrupts (cs : Array Char) (i : Nat) : Bool :=
  (atxAt cs i).isSome || thematicAt cs i || (fenceAt cs i).isSome
    || cs[i]? == some '>' || htmlBlockInterruptAt cs i
    || (match bulletAt cs i with
        | some (_, j) => !isBlankFrom cs j
        | none => false)
    || (match orderedAt cs i with
        | some (n, _, j) => n == 1 && !isBlankFrom cs j
        | none => false)

/-- Does the line at `i` start *any* block? Wider than `interrupts`: a
marker that may not interrupt a paragraph still opens a sibling item when
its own container did not match, which is not a lazy continuation. The two
predicates were one, and the false positive it produced fired on the second
item of every ordered list that did not start at 1. -/
private def startsAnyBlock (cs : Array Char) (i : Nat) : Bool :=
  interrupts cs i || (bulletAt cs i).isSome || (orderedAt cs i).isSome
    || (setextAt cs i).isSome

/-- Blocks for one markdown document, and the diagnostics the reader raised.
The only recursion here is the loop's own index. -/
def blocks (file : String) (input : String) : Array Blk × Array Diag := Id.run do
  let lines := splitLines input
  let mut frames : Array Frame := #[]
  let mut acc : Array Blk := #[]
  let mut leaf : Leaf := .none
  let mut diags : Array Diag := #[]
  let mut sawBlank := false
  for li in [0:lines.size] do
    let some ln := lines[li]? | continue
    let cs := ln.cs
    let lpos : Pos := ⟨ln.no, 1⟩
    -- Match the open containers. A fence does not exempt a line from this:
    -- skipping it left the fence open past its container, so a fence in a
    -- quote or a nested item swallowed every block that followed and the
    -- closing fence, the paragraph and the heading after it all shipped as
    -- code — with no diagnostic.
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
          if isBlankFrom cs i then
            i := cs.size
            matched := matched + 1
          else
            let (_, ind) := indentAt cs i col
            if ind ≥ need then
              let mut k := i
              let mut c2 := col
              for _ in [0:need + 1] do
                if c2 - col < need then
                  match cs[k]? with
                  | some ' ' =>
                    c2 := c2 + 1
                    k := k + 1
                  | some '\t' =>
                    c2 := c2 + (4 - c2 % 4)
                    k := k + 1
                  | _ => pure ()
              i := k
              col := c2
              matched := matched + 1
            else
              ok := false
        | some (FKind.list _ _ _) => matched := matched + 1
    -- An open fenced block, inside the containers that matched: its closer
    -- is tested on the line *after* the container prefixes, and its content
    -- lines keep neither those prefixes nor the opener's own indent (§4.5).
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
    | _ => pure ()
    let blank := isBlankFrom cs i
    -- Closing the open paragraph, wherever a branch below needs it done.
    let closePara : Leaf → Array Blk → Pos → Array Blk × Array Diag :=
      fun l a fallback =>
        match l with
        | .para pls =>
          let (inl, ds) := inlines file (charsOf pls)
          (a.push (.para inl ((pls[0]?.map (·.2)).getD fallback)), ds)
        | _ => (a, #[])
    -- An unmatched container under an open paragraph is a lazy continuation.
    if !ok && leaf.isPara && !blank && !startsAnyBlock cs (indentAt cs i col).1 then
      diags := diags.push (refuse file .lazyContinuation lpos)
    if !ok then
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      leaf := .none
      for _ in [0:frames.size] do
        if frames.size > matched then
          let (fs, a) := closeTop frames acc
          frames := fs
          acc := a
    if blank then
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      leaf := .none
      sawBlank := true
      continue
    -- New containers, as many as the line opens.
    let mut opened := true
    for _ in [0:cs.size + 1] do
      if opened then
        opened := false
        let (j, ind) := indentAt cs i col
        if ind ≤ 3 && cs[j]? == some '>' then
          let j2 := j + 1
          let j2 := if ((cs[j2]?).map isSpaceOrTab).getD false then j2 + 1 else j2
          let (a, ds) := closePara leaf acc lpos
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
          -- A thematic break outranks a list marker (§4.1): tested after the
          -- marker, `* * *` and `- - -` opened three nested empty lists.
          let startNew : Option (Bool × Nat × Char × Nat × Nat) :=
            match bulletAt cs j, orderedAt cs j with
            | some (m, k), _ => some (false, 1, m, k, 1)
            | none, some (n, d, k) =>
              -- The marker's own width, digits and delimiter, without the
              -- space after it: an empty item's content column is measured
              -- from the marker, and counting the space put it one too far.
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
              let (a, ds) := closePara leaf acc lpos
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
              -- A marker of a different kind starts a *new* list, so the
              -- open one closes first. Left open, its frame swallowed every
              -- block that followed: the bullet list stayed on the stack and
              -- an ordered list, a quote, a fence and two more blocks all
              -- landed inside its last item, where the backend shipped none
              -- of them.
              unless sameList do
                let (fs, a2) := closeLists frames acc
                frames := fs
                acc := a2
                frames := frames.push
                  { kind := .list ordered start marker, pos := lpos, outer := acc }
                acc := #[]
              -- A blank line *between two items of one list* makes it loose;
              -- a blank line before the list starts says nothing about it.
              if sawBlank && sameList && frames.size > 0 then
                frames := frames.modify (frames.size - 1) (fun f => { f with tight := false })
              -- The item's content indent, in columns from the line start.
              -- `sp` counts the spaces *beyond* the one the marker consumed,
              -- so five spaces after the marker is `sp ≥ 4`: written `≥ 5`,
              -- `-     foo` set its content as item text where the strict
              -- dialect owes an indented-code refusal.
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
    -- A list frame is never innermost past this point. The line opened no
    -- item inside it, so the line is past the list. Decided after the
    -- containers were read, not predicted before: the prediction was a
    -- second copy of the container loop's marker test, and the copy that
    -- lacked the thematic-break precedence kept a list open under `* * *`
    -- with no item in it, so the rest of the document landed in the list's
    -- own accumulator and shipped nowhere.
    let (fs, a) := closeLists frames acc
    frames := fs
    acc := a
    -- A blank line between two blocks of one item makes its list loose.
    if sawBlank && !acc.isEmpty then
      for fi in [0:frames.size] do
        let idx := frames.size - 1 - fi
        if let some f := frames[idx]? then
          match f.kind with
          | .list _ _ _ =>
            frames := frames.modify idx (fun lf => { lf with tight := false })
            break
          | _ => pure ()
    -- A line that was only container markers opens nothing: `blank` was
    -- measured before they opened, so `- ` or `>` with an empty remainder
    -- opened an empty paragraph, and the next unmarked line was then refused
    -- as a lazy continuation of it.
    if isBlankFrom cs i then
      sawBlank := false
      continue
    -- The leaf.
    let (j, ind) := indentAt cs i col
    if ind ≥ 4 && !leaf.isPara then
      diags := diags.push (refuse file .indentedCode lpos)
    else if ind ≥ 4 && leaf.isPara then
      -- Four spaces under an open paragraph is continuation text, not a
      -- block start: `foo` then `    # bar` is one paragraph. Tested for
      -- block starts first, the indented line became an ATX heading.
      leaf := .para (match leaf with
        | .para pls => pls.push (sliceStr cs j cs.size, ⟨ln.no, j + 1⟩)
        | _ => #[(sliceStr cs j cs.size, ⟨ln.no, j + 1⟩)])
    else if let some (level, k) := atxAt cs j then
      let (a, ds) := closePara leaf acc lpos
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
      let (inl, ds2) := inlines file (charsOfOne (body.trimAscii.toString) ⟨ln.no, k + 1⟩)
      acc := acc.push (.heading level inl lpos)
      diags := diags ++ ds2
    else if leaf.isPara && (setextAt cs j).isSome then
      -- A `---` line under a paragraph is a setext underline, not a
      -- thematic break: the spec gives the heading precedence, and testing
      -- the break first read every level-2 setext heading as a rule and
      -- dropped its title into the paragraph above.
      let level := (setextAt cs j).getD 1
      match leaf with
      | .para pls =>
        let (inl, ds) := inlines file (charsOf pls)
        acc := acc.push (.heading level inl ((pls[0]?.map (·.2)).getD lpos))
        diags := diags ++ ds
      | _ => pure ()
      leaf := .none
    else if thematicAt cs j then
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      leaf := .none
      acc := acc.push (.rule lpos)
    else if let some (fch, flen, finfo) := fenceAt cs j then
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      leaf := .fenced fch flen finfo lpos (j - i) #[]
    else if htmlBlockAt cs j then
      -- The refusal names the construct's own column, not the line's: a
      -- block inside a quote or an item starts after the container prefix,
      -- and a checker reading the refused text back from the source must
      -- land on the tag.
      diags := diags.push (refuse file .rawHtml ⟨ln.no, j + 1⟩)
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      leaf := .none
    else
      let text := sliceStr cs j cs.size
      match leaf with
      | .para pls => leaf := .para (pls.push (text, ⟨ln.no, j + 1⟩))
      | _ => leaf := .para #[(text, ⟨ln.no, j + 1⟩)]
    sawBlank := false
  -- End of input: the leaf, then every frame.
  match leaf with
  | .para pls =>
    let (inl, ds) := inlines file (charsOf pls)
    acc := acc.push (.para inl ((pls[0]?.map (·.2)).getD {}))
    diags := diags ++ ds
  | .fenced _ _ finfo fpos _ flines =>
    acc := acc.push (.code finfo (flines.foldl (fun s l => s ++ l ++ "\n") "") fpos)
  | .none => pure ()
  for _ in [0:frames.size] do
    let (fs, a) := closeTop frames acc
    frames := fs
    acc := a
  return (acc, diags)

end LeanTex.Core.Md
