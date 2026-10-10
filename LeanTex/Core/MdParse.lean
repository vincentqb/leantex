module

public import LeanTex.Core.Diag
public import LeanTex.Core.Heading
import LeanTex.Core.Loop
import Std.Data.HashMap

/-! # The markdown surface: source → md AST

Markdown has no semantics of its own in this engine: its meaning *is* its
desugaring into the tex-shaped surface AST (`MdDesugar`), which the one
elaborator then reads. This module is only the reader — source text to an
md AST carrying `.md` spans, so every diagnostic downstream names the
markdown line the reader saw.

Dialect: CommonMark-shaped but strict, with GitHub Flavored Markdown's
table extension, which the surface AST expresses as a booktabs table. Three
constructs are refused by design rather than silently diverging, each an
`E0390` carrying the class as its subject:

* `raw-html` — raw HTML is parsed. It is never passed through, never
  rendered by another engine, never decided per backend, and never dropped
  in silence. A closed vocabulary lowers at read time onto md constructors
  that already exist, so the elaborator reads it through those nodes' one
  resolving site: a comment-only span ships nothing; a `<br>`, `<br/>` or
  `<br />` with no attribute is a hard break; an empty `<a>` with one `name`
  or `id` is a target; a `<details>` or `<details open>` around a one-line,
  attribute-free, plain-text `<summary>` is a disclosure, which sets
  expanded and names its lost collapse. Every attribute on an accepted
  element is carried by an existing field, honoured exactly by what ships
  (a premise pin), routed, or its element is refused. Everything else is
  one `E0390` at its own `<`, dropping exactly the raw HTML the reader
  consumed: an inline tag's markup, its neighbouring text still shipping, or
  an HTML block's lines. What is proved is the inline scan's step: raw HTML
  lowers to that vocabulary and nothing else (`htmlInlineAt_covers`), and
  each step ships a token, raises one `E0390` at the position the scan reads
  its `<` at, or consumes a comment that hides only itself
  (`htmlInlineAt_accounts`). The loop around that step and the block
  reader's raw-HTML arms are held by evidence over a generated family of
  names, shapes and sites (`mdHtmlAccountsChecks`); their statements are
  pending work. A spelling joins only when it says what markdown cannot, the
  IR already resolves it, and each artifact sets it as it sets its markdown
  spelling (`htmlTwinChecks`) — or, where markdown has none, as rows over
  both artifacts hold it; a loss is named for each artifact that suffers it,
  the markdown twin included, and for no other. `\markdownInput` reads
  through the same `Md.read`, so all of this holds for markdown included in
  tex.
* `indented-code` — a four-space indent as a code block. Measured
  ambiguity: the same indent means continuation inside a list and code
  outside one.
* `lazy-continuation` — a paragraph line inside a container that omits the
  container's own marker.

Each refusal carries a fix-it in its message, and each is a *data*
decision: the verdict rows in `testdata/commonmark/verdicts.tsv` say which
spec cases the class touches, so flipping one is a table change plus a
reader arm, never a redesign.

Why document content can never become markup: whatever the reader makes of
a document, raw HTML included, the surface AST it desugars to lies in the
lowering's declared vocabulary, no formula among it
(`desugar_vocabulary_mem`), author text crossing as words and spaces
(`textRaws_covers`); and the HTML backend escapes every text and attribute
it emits (`Html.escapeText_no_lt`, `Html.escapeAttr_no_quote`). The other
half — that a link's or an image's destination cannot carry an active URL
scheme onto the page — is pending work, held by no theorem yet.

Block structure is one pass over the lines with an explicit container
stack — `Parse.parse`'s frame shape, so totality is immediate and the
checker needs no help. Inline structure is a flat token array plus
CommonMark's delimiter-run algorithm, matched into a pair table and then
built into a tree by the same frame shape. -/

namespace LeanTex.Core.Md

open LeanTex.Core

/-- An inline node. `pos` is the position in the `.md` source. -/
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
  deriving Repr, BEq

public instance : Inhabited Inl := ⟨.soft {}⟩

/-- A table column's alignment as its GFM delimiter cell spells it: `---`
declares none, `:--` left, `--:` right, `:-:` centre. -/
public inductive TableAlign where
  | none
  | left
  | right
  | center
  deriving Repr, BEq, Inhabited

/-- A block node. A list holds one `Array Blk` per item. A table holds one
alignment per column, the header's cells, and its data rows, each exactly
one cell per column. -/
public inductive Blk where
  | para (body : Array Inl) (pos : Pos)
  | heading (level : Ir.HeadingLevel) (body : Array Inl) (pos : Pos)
  | code (info : String) (text : String) (pos : Pos)
  | rule (pos : Pos)
  | quote (body : Array Blk) (pos : Pos)
  | disclosure (summary : Array Inl) (body : Array Blk) (pos : Pos)
  | list (ordered : Bool) (start : Nat) (tight : Bool) (items : Array (Array Blk))
      (pos : Pos)
  | table (aligns : Array TableAlign) (header : Array (Array Inl))
      (rows : Array (Array (Array Inl))) (pos : Pos)
  deriving Repr, BEq

public instance : Inhabited Blk := ⟨.rule {}⟩

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
def setextAt (cs : Array Char) (i : Nat) : Option Ir.HeadingLevel := Id.run do
  let some c0 := cs[i]? | return none
  unless c0 == '=' || c0 == '-' do return none
  let mut j := i
  for _ in [0:cs.size + 1] do
    if cs[j]? == some c0 then j := j + 1 else break
  unless isBlankFrom cs j do return none
  return some (if c0 == '=' then .h1 else .h2)

-- ## Raw HTML, recognized rather than guessed
--
-- The dialect refuses raw HTML, so what counts *as* raw HTML decides what
-- the reader refuses — and a test wider than the grammar refuses valid
-- CommonMark. Twenty-nine spec cases were refused by a test that fired on
-- any `<` followed by a letter: `<https://example.org>` at the start of a
-- line, and literal text such as `x <y for comparison`. So the tag grammar
-- (§6.6) is implemented, and anything it does not accept is text.

/-- The characters of `lit` at `i`, case-folded, one step of the source per
character of the literal: its reach is the literal's length. -/
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

/-- HTML also ends a comment at `--!>`. CommonMark's raw span can extend
past that boundary, so it cannot be discarded as invisible content.
Inspect only the consumed span, never the rest of the paragraph. -/
def commentOnly (cs : Array Char) (start stop : Nat) : Bool :=
  (findLit (cs.extract start stop) 0 "--!>").isNone

/-- What a raw-HTML scan over one stretch remembers: for each of the four
constructs that close on a literal (comment, CDATA, processing instruction,
declaration), the earliest position from which a search for that literal
has already failed. -/
structure HtmlMemo where
  noClose : Array (Option Nat) := #[none, none, none, none]
  deriving Inhabited

/-- `findLit`, remembering failure. A search for literal `k` that found
nothing at or after `p` answers every later search from `q ≥ p` without
scanning, and the inline scan asks at increasing positions — so an unclosed
construct costs one scan in all, not one per opener. Unclosed `<!--`
repeated took 133 s at 78 KB, one scan to the paragraph's end per `<`. -/
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

/-- One attribute at `i`, its leading whitespace already consumed: its name,
lower-cased; its value as the source spells it, quotes stripped and nothing
decoded, so a vocabulary row that carries a value decides its decoding and
owes the check that reads it back; and the index past it. -/
def attrAt (cs : Array Char) (i : Nat) : Option ((String × Option String) × Nat) := Id.run do
  let some c0 := cs[i]? | return none
  unless isAttrStart c0 do return none
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    match cs[j]? with
    | some c => if isAttrRest c then j := j + 1 else break
    | none => break
  let name := (sliceStr cs i j).toLower
  -- An optional value, after optional whitespace either side of `=`.
  let k := wsAt cs j
  if cs[k]? == some '=' then
    let v := wsAt cs (k + 1)
    match attrValueAt cs v with
    | some e =>
      let quoted := cs[v]? == some '"' || cs[v]? == some '\''
      return some ((name, some (if quoted then sliceStr cs (v + 1) (e - 1) else sliceStr cs v e)), e)
    | none => return some ((name, none), j)
  return some ((name, none), j)

/-- One tag as the §6.6 grammar reads it: the name, lower-cased; each
attribute as `attrAt` captured it; whether it closed with `/>`; and the index
past its `>`. The one reading every recognizer projects — the refusal
(`htmlTagAtM`), the disclosure and anchor arms, and the vocabulary — so what
the reader refuses and what it reads cannot drift apart. -/
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

/-- A closing tag at `i` (§6.6): its name, lower-cased, and the index past
its `>`. -/
def endTagAt (cs : Array Char) (i : Nat) : Option (String × Nat) := do
  guard (cs[i]? == some '<' && cs[i + 1]? == some '/')
  let j ← tagNameAt cs (i + 2)
  let k := wsAt cs j
  guard (cs[k]? == some '>')
  return ((sliceStr cs (i + 2) j).toLower, k + 1)

/-- A complete raw-HTML construct at `i` (§6.6): an open tag, a closing tag,
a comment, a processing instruction, a declaration, or CDATA. The index past
it, or `none` — and `none` means the text is text. A comment is `<!-->`,
`<!--->`, or `<!--` … `-->` (0.31.2), so its closer is searched from the
second character. The memo is `findLitM`'s. The two tag arms are `tagAt`
and `endTagAt` themselves (`htmlTagAtM_tag_exact`). -/
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

/-- `htmlTagAtM` with nothing remembered: a block start reads one line. -/
def htmlTagAt (cs : Array Char) (i : Nat) : Option Nat := (htmlTagAtM cs i {}).1

/-- An attribute-free, non-self-closing tag. The entire name must match:
`details-extra` and an attribute that changes visibility are not this node. -/
private def bareTagAt (cs : Array Char) (i : Nat) (name : String)
    (closing : Bool := false) : Option Nat :=
  if closing then (endTagAt cs i).bind fun (n, stop) => if n == name then some stop else none
  else (tagAt cs i).bind fun t =>
    if t.name == name && t.attrs.isEmpty && !t.selfClosing then some t.stop else none

/-- The spellings of a disclosure's opening tag that the reader accepts: a
`details`, not self-closing, with no attribute or with exactly one `open`
whose value is absent, empty, or `open` in any case — every spelling HTML
reads as the open state, which is the expanded state the disclosure sets. -/
private def detailsOpen (t : HtmlTag) : Bool :=
  t.name == "details" && !t.selfClosing &&
    match t.attrs.toList with
    | [] => true
    | [(a, v)] => a == "open" && v.all fun s => s.isEmpty || s.toLower == "open"
    | _ => false

/-- The key of an empty target's open tag: an `a`, not self-closing, with
exactly one attribute, a `name` or an `id` carrying a value. -/
private def anchorKey? (t : HtmlTag) : Option String :=
  if t.name == "a" && !t.selfClosing then
    match t.attrs.toList with
    | [(attr, some key)] => if attr == "name" || attr == "id" then some key else none
    | _ => none
  else none

/-- A line break, as HTML spells one: `<br>`, `<br/>` or `<br />`, any case,
with no attribute. -/
private def isBr (t : HtmlTag) : Bool := t.name == "br" && t.attrs.isEmpty

/-! Every reading above ends past where it started and inside the source, so
a scan that resumes at a reading's stop always advances. Each scanner's
bound is an invariant of its own loop (`Loop.forIn_range_inv`). -/

theorem litAtList_reach {cs : Array Char} :
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
    have := litAtList_reach hr (by omega)
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
        have := litAtList_reach hl (by omega)
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

/-- Does an HTML block of §4.6's sixth condition open at `i` with the tag
`name`: `<name` or `</name`, the name followed by a space, a tab, `>`, `/>`
or the line's end? The test `htmlBlockKind` refuses such a line by, read
where a construct accounts for that refusal, so the two cannot drift. -/
def blockTagStartsAt (cs : Array Char) (i : Nat) (name : String) : Bool :=
  cs[i]? == some '<' &&
    (namedTagAt cs (i + 1) [name] || (cs[i + 1]? == some '/' && namedTagAt cs (i + 2) [name]))

/-- How an HTML block ends (§4.6): at the first line holding one of these
literals, compared case-folded (conditions 1–5), or at a blank line, which
is not part of the block (conditions 6 and 7). -/
inductive HtmlEnd where
  | lit (ends : List String)
  | blank
  deriving Repr, Inhabited

/-- The HTML block starting at `i`, by §4.6 condition: how it ends, and
whether it may interrupt a paragraph — conditions 1–6 may, 7 may not.
`none` means no block starts here. One definition, read by every question
about HTML blocks: whether one starts, whether it interrupts, where it ends. -/
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

/-- Does a line, from `i`, hold an end literal of its HTML block? A scan of
one line, so the cost is the line's. -/
def htmlEndsIn (cs : Array Char) (i : Nat) (e : HtmlEnd) : Bool := Id.run do
  match e with
  | .blank => return false
  | .lit ends =>
    for k in [i:cs.size] do
      if ends.any (litAt cs k ·) then return true
    return false

/-- Conditions 1–6 only: what may interrupt a paragraph. Condition 7 may
not, and reading it as an interrupter refused a paragraph line holding a
bare `<span>`. -/
def htmlBlockInterruptAt (cs : Array Char) (i : Nat) : Bool :=
  match htmlBlockKind cs i with
  | some (_, interrupts) => interrupts
  | none => false

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
  | anchor (key : String) (pos : Pos)
  | run (ch : Char) (len : Nat) (canOpen canClose : Bool) (pos : Pos)
  | bopen (image : Bool) (pos : Pos)
  | bclose (pos : Pos)
  deriving Repr

instance : Inhabited ITok := ⟨.soft {}⟩

def ITok.pos : ITok → Pos
  | .txt _ p | .code _ p | .soft p | .hard p | .auto _ _ p
  | .anchor _ p | .run _ _ _ _ p | .bopen _ p | .bclose p => p

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

/-- Every maximal backtick string of a stretch — a code span's only possible
closers (§6.1) — as start positions in order, grouped by length. Built once
per stretch, so finding a closer is a lookup and not a scan: scanned for,
backtick strings of rising lengths with no closers cost one scan to the end
of the paragraph each. -/
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

/-- A code span opening at `i` with a backtick string of length `n`: the
content and the index past the closing string, or `none` when no closing
string of the same length follows. The closer is the first maximal backtick
string of length `n` after the opener, read off `tickIndex`. -/
def codeSpanAt (c : Chars) (idx : Std.HashMap Nat (Array Nat)) (i n : Nat) :
    Option (String × Nat) := do
  let j ← firstAtLeast (idx.getD n #[]) (i + n)
  -- Strip one space from each end when both are present and the content is
  -- not all spaces (spec §6.1).
  let raw := (c.str (i + n) j).toList
  let stripped :=
    if raw.length ≥ 2 && raw.headD 'x' == ' ' && raw.getLastD 'x' == ' '
        && !(raw.all (· == ' ')) then
      (raw.drop 1).dropLast
    else raw
  -- Line endings inside a code span are spaces.
  some (String.ofList (stripped.map (fun ch => if ch == '\n' then ' ' else ch)), j + n)

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
      -- No whitespace, control character or `<` inside an autolink (§6.5):
      -- stopping at `<` is also what keeps `<a<a<a…` linear.
      if isMdSpace ch || ch == '<' || ch.toNat < 0x20 then return none
      j := j + 1
  return none

/-- A link destination and optional title starting at `(`: the destination,
the title, and the index past `)`. Angle-bracket destinations and balanced
parentheses, which is what the inline form needs.

Three stops the spec states keep each scan bounded by the next construct
rather than by the paragraph (§6.3): an angle destination holds no unescaped
`<`, a parenthesized title no unescaped `(`, and a bare destination nests
parentheses at most 32 deep (the spec asks at least three; cmark's limit).
Without them, `[a](<b`, `[a](b` and `[ (](` repeated each scanned to the
end of the paragraph once per `](`. -/
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

/-- A fenced block's info string with its backslash escapes and character
references resolved (§4.5, §2.4, §2.5: both are recognized in info
strings). `foo\+bar` names the language `foo+bar`; read raw, the listing
lost it. -/
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
  | .rawHtml => "write it in markdown (**bold**, *emphasis*, [text](url), ![alt](src)), quote it as a code span with `...`, or delete the tags"
  | .indentedCode => "fence the block with ``` instead"
  | .lazyContinuation => "indent the line to its container's content column, or repeat a quote's '>'"

/-- The refusal, as a diagnostic. The subject is what folds repeats into one
line with a site count (`Diag.tallySites`), so a document with fifty raw
tags reports one error naming fifty sites. -/
def refuse (file : String) (s : Strict) (pos : Pos) : Diag :=
  Diag.of .E0390 s.message (some ⟨file, pos⟩) (some s.fixit) (some s.subject)

/-- What an open tag the inline scan read lowers to, from that one reading:
a bare break (`isBr`) is a hard break; an empty target — the open tag
`anchorKey?` reads a key from, with its `</a>` straight after — is a target,
whose key the desugaring checks the existing target semantics preserve; any
other open tag ships nothing and is refused at its own `<`. -/
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

/-- The three things an open tag can become, and where its reading stops. -/
private theorem openTagInline_cases {file : String} {cs : Array Char} {p : Pos} {t : HtmlTag}
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

/-- Raw HTML at `i` inside an inline stretch, after the autolink reading
failed: the index past what the reader consumed, the token it lowers to,
and the refusal it raises — or `none`, and the `<` is text. The construct
is read once: an open tag is `tagAt`'s reading, projected by
`openTagInline`; a closing tag, a comment, a processing instruction, a
declaration or CDATA is `htmlTagAtM`'s. A comment-only span ships nothing
and raises nothing; any other construct the vocabulary does not read ships
nothing and is refused at its own `<` (`htmlInlineAt_accounts`); what
lowers is exactly the vocabulary `htmlInlineAt_covers` lists. -/
def htmlInlineAt (file : String) (cs : Array Char) (i : Nat) (p : Pos) (m : HtmlMemo) :
    Option (Nat × Option ITok × Option Diag) × HtmlMemo :=
  if cs[i + 1]? == some '!' || cs[i + 1]? == some '?' || cs[i + 1]? == some '/' then
    match htmlTagAtM cs i m with
    | (some next, m') =>
      -- premise: mdSurfaceChecks — comments hide only their own text.
      if litAt cs i "<!--" && commentOnly cs i next then (some (next, none, none), m')
      else (some (next, none, some (refuse file .rawHtml p)), m')
    | (none, m') => (none, m')
  else ((tagAt cs i).map (openTagInline file cs p), m)

/-- **Every raw construct the inline scan consumes is accounted for.** The
reading advances and stays inside the stretch, and then exactly one of: a
token ships and nothing is raised; nothing ships and one `E0390` names the raw
HTML at `p`, the position the scan reads its `<` at; or nothing ships,
nothing is raised, and the span was a comment that hides only itself. The
third outcome is still the `_accounts` shape, not an unpaid empty result:
`commentOnly` makes the span exactly one HTML comment — no `--!>` closes it
early — and HTML itself shows a comment as nothing, so the empty result is
what the source means, with no lost content to pay for. This is one step of
the scan; the loop that resumes past each step, and the block reader's
raw-HTML arms, hold no statement yet. -/
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
      rcases openTagInline_cases h.1 with ⟨rfl, rfl, rfl⟩ | ⟨key, he, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨htb.1, htb.2, Or.inl ⟨rfl, rfl⟩⟩
      · have heb := endTagAt_between he
        exact ⟨by omega, heb.2, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨htb.1, htb.2, Or.inr (Or.inl ⟨rfl, _, rfl, refused_named rfl⟩)⟩

/-- What the inline scan lowers raw HTML to: exactly this vocabulary, each
token an md node that already exists, so the elaborator reads it through
that node's one resolving site. That each spelling then ships what its
markdown twin ships, in both artifacts, is `htmlTwinChecks`' evidence, not
this theorem's. -/
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
      rcases openTagInline_cases h.1 with ⟨_, h2, _⟩ | ⟨key, _, h2, _⟩ | ⟨_, h2, _⟩
      · exact Or.inl (Option.some.inj h2)
      · exact Or.inr ⟨key, Option.some.inj h2⟩
      · simp at h2

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
  let ticks := tickIndex c
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
          -- Only a complete tag (§6.6) is raw HTML; anything else is
          -- literal text. Pending text is flushed only when a token ships,
          -- so a refused tag or a comment joins the text either side of it.
          let (r, m) := htmlInlineAt file c.cs i p hmemo
          hmemo := m
          match r with
          | some (next, tok, d) =>
            if let some tk := tok then
              -- A break ends its line: the text before it sheds its trailing
              -- spaces, as the text before a two-space break does.
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
    | .anchor key _ => acc := acc.push (.anchor key p)
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
      ps := ps.push { p with col }
      col := col + 1
  return ⟨cs, ps⟩

def charsOfOne (s : String) (p : Pos) : Chars := charsOf #[(s, p)]

/-- HTML text resolves the reader's known character references, but neither
Markdown delimiters nor TeX controls. Unknown or unterminated references and
numeric C1 references are refused: HTML's legacy decoding differs from the
Markdown decoder there. Markup inside the summary is outside this subset. -/
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

/-- A complete, attribute-free summary on one line. Requiring the closing
tag and blank suffix prevents a supported prefix from swallowing markup or
visible text outside it. -/
private def summaryAt (cs : Array Char) (i : Nat) (p : Pos) : Option (Array Inl) := do
  let start ← bareTagAt cs i "summary"
  let closeEnd ← findLit cs start "</summary"
  let stop := closeEnd - "</summary".length
  let next ← bareTagAt cs stop "summary" true
  guard (isBlankFrom cs next)
  let text ← htmlText (sliceStr cs start stop)
  return #[.text text { p with col := start + 1 }]

end LeanTex.Core.Md


namespace LeanTex.Core.Md

open LeanTex.Core

/-! ## Tables

GitHub Flavored Markdown's table, the one GFM leaf block the surface AST
already expresses: it desugars to a booktabs `{tabular}`. The extension's
rules (GFM 0.29, "Tables (extension)"), each a scanner here:

* the delimiter row is cells of hyphens, each with an optional colon either
  side, with pipes between them and optionally around them; the colons give
  the column's alignment;
* a row splits on every pipe a backslash does not escape, *before* any
  inline is read, so `\|` is a pipe even inside a code span, and each cell
  is trimmed;
* the header is the last line of the paragraph the delimiter row stands
  under and carries exactly as many cells; lines before it stay a paragraph;
* a data row's missing cells are empty and its excess cells are dropped;
* the table ends at a blank line, with its container, or where another block
  starts. -/

/-- The table extension's space: a space, a tab, a vertical tab or a form
feed. -/
def isTableSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\x0b' || c == '\x0c'

/-- The index past a run of table spaces at `i`. -/
def tableSpaceEnd (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut k := i
  for _ in [0:cs.size + 1] do
    if (cs[k]?).any isTableSpace then k := k + 1 else break
  return k

/-- A delimiter row at `i`: each column's alignment, or `none` when the
line is not one. -/
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

/-- One cell of a row, `[start, stop)` of the line: trimmed, with each
`\|` read as the pipe it escapes, every kept character carrying its `.md`
position so a diagnostic inside the cell names its column. -/
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

/-- A row's cells, split on every pipe a backslash does not escape, with an
optional pipe at either end. Empty when the line holds no cell — a lone
`|` — which ends a table rather than continuing it. -/
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
empty and an excess one is dropped, as the extension reads a data row. -/
def tableRow (file : String) (n : Nat) (cells : Array Chars) :
    Array (Array Inl) × Array Diag := Id.run do
  let mut row : Array (Array Inl) := #[]
  let mut diags : Array Diag := #[]
  for k in [0:n] do
    match cells[k]? with
    | some c =>
      let (inl, ds) := inlines file c
      row := row.push inl
      diags := diags ++ ds
    | none => row := row.push #[]
  return (row, diags)

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
  | disclosure
  deriving Repr, BEq, Inhabited

private structure Frame where
  kind : FKind
  pos : Pos
  outer : Array Blk := #[]
  items : Array (Array Blk) := #[]
  tight : Bool := true
  summary : Option (Array Inl) := none
  /-- A disclosure whose summary line the reader refused: that refusal, at
  the summary's own `<`, is the construct's one accounting. -/
  refused : Bool := false

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
    | .disclosure => (rest, f.outer.push (.disclosure (f.summary.getD #[]) acc f.pos))
    | .item _ =>
      match rest.back?.map Frame.kind with
      | some (FKind.list _ _ _) =>
        (rest.modify (rest.size - 1) (fun lf => { lf with items := lf.items.push acc }), f.outer)
      | _ => (rest, f.outer ++ acc)
    | .list ord st _ => (rest, f.outer.push (.list ord st f.tight f.items f.pos) ++ acc)

/-- Close a disclosure frame the reader refuses: the summary, when one was
read, ships as a paragraph, then the body, into the accumulator outside it.
No `Blk.disclosure` is built, so nothing downstream names a collapse the
reader never accepted: the refusal at its `<` — or at its summary's, when
the reader refused that line as raw HTML and dropped it — is the construct's
one accounting, and every other word it held still ships, once, in source
order. -/
private def closeRefusedDisclosure (frames : Array Frame) (acc : Array Blk) :
    Array Frame × Array Blk :=
  match frames.back? with
  | none => (frames, acc)
  | some f =>
    let outer := match f.summary with
      | some s => f.outer.push (.para s f.pos)
      | none => f.outer
    (frames.pop, outer ++ acc)

/-- Close the innermost frame where its own closer never came — its
container ended, or the input did. A disclosure is refused there, once, with
`closeRefusedDisclosure` — unless its summary's refusal already accounted
for it; any other frame closes as `closeTop` closes it. -/
private def closeUnclosed (file : String) (frames : Array Frame) (acc : Array Blk) :
    Array Frame × Array Blk × Option Diag :=
  match frames.back? with
  | some f =>
    if f.kind == .disclosure then
      let (fs, a) := closeRefusedDisclosure frames acc
      -- premise: refusedDisclosureChecks — an unclosed disclosure whose summary was refused raises that one E0390 and no second where its container ends
      (fs, a, if f.refused then none else some (refuse file .rawHtml f.pos))
    else
      let (fs, a) := closeTop frames acc
      (fs, a, none)
  | none => (frames, acc, none)

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
  /-- A refused HTML block still open: its lines are the refused construct,
  consumed to its §4.6 end, never re-read as markdown. Re-read, an indented
  line inside a `<table>` was refused a second time as indented code. -/
  | html (e : HtmlEnd)
  | comment (pos : Pos)
  /-- An open table: its rows so far, each already read into its cells. -/
  | table (aligns : Array TableAlign) (header : Array (Array Inl))
      (rows : Array (Array (Array Inl))) (pos : Pos)
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

/-- Consume `need` columns of indent from `i` at column `col`, a tab
advancing to the next multiple of four: the index and column past them, or
`none` when the whitespace runs out first. Walks at most `need` columns. -/
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

/-- Does the line at `i` start *any* block? Wider than `interrupts`: a
marker that may not interrupt a paragraph still opens a sibling item when
its own container did not match, which is not a lazy continuation. The two
predicates were one, and the false positive it produced fired on the second
item of every ordered list that did not start at 1. -/
private def startsAnyBlock (cs : Array Char) (i : Nat) : Bool :=
  interrupts cs i || (bulletAt cs i).isSome || (orderedAt cs i).isSome

/-- Blocks for one markdown document, and the diagnostics the reader raised.
The only recursion here is the loop's own index. -/
public def blocks (file : String) (input : String) : Array Blk × Array Diag := Id.run do
  let lines := splitLines input
  let mut frames : Array Frame := #[]
  let mut acc : Array Blk := #[]
  let mut leaf : Leaf := .none
  let mut diags : Array Diag := #[]
  let mut sawBlank := false
  -- The first line of the paragraph whose header a delimiter row failed to
  -- match: GFM tries a paragraph once.
  let mut tableVisited : Option Pos := none
  for li in [0:lines.size] do
    let some ln := lines[li]? | continue
    let cs := ln.cs
    let lpos : Pos := { line := ln.no, col := 1 }
    -- One past the line's last character that is not a space or a tab: the
    -- line is blank from `i` exactly when `i ≥ inkEnd`.
    let inkEnd := Id.run do
      let mut e := 0
      for k in [0:cs.size] do
        if h : k < cs.size then
          unless isSpaceOrTab cs[k] do e := k + 1
      return e
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
          -- Both tests read at most what this frame consumes: the line's
          -- last non-space character is found once per line, and the
          -- indent is walked only as far as `need`. Measured over the whole
          -- rest of the line at every frame, a list nested k deep cost k
          -- scans of k columns per line, and the deep-list shape grew 2.7×
          -- per doubling.
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
    | .html e =>
      -- The refused block ends with its container, at a blank line for
      -- conditions 6 and 7 (the blank line is read as usual), or on the
      -- line that holds its end literal. Every other line is consumed.
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
        -- A suffix or an earlier HTML terminator makes this a larger raw
        -- block. Refuse it once, then consume it under the raw-block rules.
        if !commentOnly cs i (end_.getD cs.size)
            || end_.any (fun next => !isBlankFrom cs next) then
          diags := diags.push (refuse file .rawHtml p)
          leaf := if end_.isSome then .none else .html (.lit ["-->"])
        else if end_.isSome then leaf := .none
        continue
    | _ => pure ()
    let blank := isBlankFrom cs i
    -- Closing the open paragraph or table, wherever a branch below needs it
    -- done: every site that ends a paragraph ends a table the same way.
    let closePara : Leaf → Array Blk → Pos → Array Blk × Array Diag :=
      fun l a fallback =>
        match l with
        | .para pls =>
          let (inl, ds) := inlines file (charsOf pls)
          (a.push (.para inl ((pls[0]?.map (·.2)).getD fallback)), ds)
        | .table aligns header rows p => (a.push (.table aligns header rows p), #[])
        | _ => (a, #[])
    -- An unmatched container under an open paragraph is a lazy continuation
    -- when the line starts no block. A line indented four columns or more
    -- starts none — indented code cannot interrupt a paragraph — so it is
    -- lazy too: read as a block start, `    - bar` under a quoted paragraph
    -- was refused as indented code with the wrong fix-it. The refused line
    -- is the construct, consumed: the containers and the paragraph stay
    -- open, as the spec's lazy line leaves them, so the line is not read a
    -- second time as a new block and refused again.
    let (jl, indl) := indentAt cs i col
    if !ok && leaf.isPara && !blank && !(indl < 4 && startsAnyBlock cs jl) then
      diags := diags.push (refuse file .lazyContinuation lpos)
      continue
    if !ok then
      let (a, ds) := closePara leaf acc lpos
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
    -- An open table takes the line as its next row unless the line starts
    -- another block; then the table ends and the line reads as usual. A
    -- blank line, a container's end, a quote and a list item closed it above.
    if let .table aligns header rows tpos := leaf then
      let startsBlock := ind ≥ 4 || (atxAt cs j).isSome || thematicAt cs j
        || (fenceAt cs j).isSome || (htmlBlockKind cs j).isSome
      let cells := if startsBlock then #[]
        else tableCells (charsOfOne (sliceStr cs j cs.size) { line := ln.no, col := j + 1 })
      if cells.isEmpty then
        acc := acc.push (.table aligns header rows tpos)
        leaf := .none
      else
        let (row, ds) := tableRow file aligns.size cells
        diags := diags ++ ds
        leaf := .table aligns header (rows.push row) tpos
        sawBlank := false
        continue
    -- A delimiter row under a paragraph whose last line carries as many
    -- cells opens a table, that line its header. A paragraph whose header
    -- once failed to match stays a paragraph (`tableVisited`).
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
    -- An HTML block, by condition: one that may not interrupt a paragraph
    -- (condition 7) is paragraph text under an open one.
    let htmlStart : Option HtmlEnd :=
      (htmlBlockKind cs j).bind fun (e, interrupts) =>
        if leaf.isPara && !interrupts then Option.none else some e
    -- premise: htmlTwinChecks — the expanded disclosure is the open state, and one W0392 per artifact that can collapse it names the loss for both spellings
    let opensDetails := ((tagAt cs j).filter detailsOpen).any (isBlankFrom cs ·.stop)
    let closesDetails := (bareTagAt cs j "details" true).any (isBlankFrom cs ·)
    let inDetails := frames.back?.map Frame.kind == some .disclosure
    let summaryLine := inDetails && !leaf.isPara && acc.isEmpty
      && (frames.back?.bind Frame.summary).isNone && !(frames.back?.any (·.refused))
    let summary := if summaryLine then summaryAt cs j lpos else none
    -- A summary line the reader cannot read is raw HTML, refused below at its
    -- own `<` as an HTML block, by the block test itself: that refusal
    -- accounts for its disclosure, its tag on one line or several.
    -- premise: refusedDisclosureChecks — each refused summary, its tag on one line or spread over two, raises one E0390, at the summary, and its disclosure's body ships
    if summaryLine && summary.isNone && ind < 4 && blockTagStartsAt cs j "summary" then
      frames := frames.modify (frames.size - 1) fun f => { f with refused := true }
    if ind ≥ 4 && !leaf.isPara then
      diags := diags.push (refuse file .indentedCode lpos)
    else if ind ≥ 4 && leaf.isPara then
      -- Four spaces under an open paragraph is continuation text, not a
      -- block start: `foo` then `    # bar` is one paragraph. Tested for
      -- block starts first, the indented line became an ATX heading.
      leaf := .para (match leaf with
        | .para pls => pls.push (sliceStr cs j cs.size, { line := ln.no, col := j + 1 })
        | _ => #[(sliceStr cs j cs.size, { line := ln.no, col := j + 1 })])
    else if opensDetails then
      let (a, ds) := closePara leaf acc lpos
      diags := diags ++ ds
      leaf := .none
      frames := frames.push
        { kind := .disclosure, pos := { lpos with col := j + 1 }, outer := a }
      acc := #[]
    else if closesDetails && inDetails then
      let (a, ds) := closePara leaf acc lpos
      diags := diags ++ ds
      leaf := .none
      let summaryless := frames.back?.any (·.summary.isNone)
      if let some f := frames.back? then
        -- premise: refusedDisclosureChecks — a disclosure whose summary was refused raises that one E0390 and no second at its close
        if summaryless && !f.refused then diags := diags.push (refuse file .rawHtml f.pos)
      let (fs, a) := (if summaryless then closeRefusedDisclosure else closeTop) frames a
      frames := fs
      acc := a
    else if let some ss := summary then
      frames := frames.modify (frames.size - 1)
        (fun f => { f with summary := some ss })
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
      let (inl, ds2) := inlines file
        (charsOfOne (body.trimAscii.toString) { line := ln.no, col := k + 1 })
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
      leaf := .fenced fch flen (decodeInfo finfo) lpos (j - i) #[]
    else if let some e := htmlStart then
      -- The refusal names the construct's own column, not the line's: a
      -- block inside a quote or an item starts after the container prefix,
      -- and a checker reading the refused text back from the source must
      -- land on the tag.
      let (a, ds) := closePara leaf acc lpos
      acc := a
      diags := diags ++ ds
      let p := { lpos with col := j + 1 }
      -- premise: mdSurfaceChecks — only a comment-only block is consumed without loss.
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
      let (a, ds) := closePara (if before.isEmpty then .none else .para before) acc lpos
      let (header, ds2) := tableRow file aligns.size cells
      acc := a
      diags := diags ++ ds ++ ds2
      leaf := .table aligns header #[] hp
    else
      let text := sliceStr cs j cs.size
      match leaf with
      | .para pls =>
        -- A delimiter row that opened no table is text, and its paragraph
        -- can no longer become one.
        if ind < 4 && (tableDelimAt cs j).isSome then tableVisited := pls[0]?.map (·.2)
        leaf := .para (pls.push (text, { line := ln.no, col := j + 1 }))
      | _ => leaf := .para #[(text, { line := ln.no, col := j + 1 })]
    sawBlank := false
  -- End of input: the leaf, then every frame.
  match leaf with
  | .para pls =>
    let (inl, ds) := inlines file (charsOf pls)
    acc := acc.push (.para inl ((pls[0]?.map (·.2)).getD {}))
    diags := diags ++ ds
  | .fenced _ _ finfo fpos _ flines =>
    acc := acc.push (.code finfo (flines.foldl (fun s l => s ++ l ++ "\n") "") fpos)
  | .table aligns header rows p => acc := acc.push (.table aligns header rows p)
  | .html _ => pure ()
  | .comment _ => pure ()
  | .none => pure ()
  for _ in [0:frames.size] do
    let (fs, a, d) := closeUnclosed file frames acc
    frames := fs
    acc := a
    if let some d := d then diags := diags.push d
  return (acc, diags)

end LeanTex.Core.Md
