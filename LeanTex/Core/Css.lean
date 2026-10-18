module

public import Std.Data.HashMap
import Std.Data.HashSet
import LeanTex.Core.KeyVal
import LeanTex.Core.Hex

/-! The CSS an SVG file states (SVG 2 §6): declarations, a selector subset, and the cascade
of CSS Cascading 4 §6 over them. -/

namespace LeanTex.Core.Css

/-- One declaration: its lower-case property, its trimmed value without comments, and its importance. -/
public structure Decl where
  prop : String
  value : String
  important : Bool
  deriving Repr, BEq, Inhabited

/-- What a sheet holds that this reader does not read: a rule's selector outside the subset or an
empty one, text no rule holds, a declaration it cannot read, whose string a line end breaks where
`broken`, or a spelling it refuses. -/
public inductive Unread where
  | selector (text : String)
  | emptySelector
  | stray (text : String)
  | declaration (text : String) (broken : Bool)
  | escape
  | atRule
  | nestedCall (fn : String)
  | openCall (fn : String)
  | call (fn : String)
  | openString
  deriving Repr, BEq, Inhabited

/-- The noun phrase naming what is unread. -/
@[expose] public def Unread.words : Unread → String
  | .selector t => s!"selector '{t}'"
  | .emptySelector => "empty selector"
  | .stray t => s!"text '{t}' outside any rule"
  | .declaration t broken =>
    s!"declaration '{t}'" ++ if broken then ", whose string a line end breaks" else ""
  | .escape => "escape"
  | .atRule => "at-rule"
  | .nestedCall f => s!"nested function in {f}()"
  | .openCall f => s!"unterminated {f}()"
  | .call f => s!"function {f}()"
  | .openString => "unterminated string"

/-- The same noun phrase with its article. -/
@[expose] public def Unread.prose (u : Unread) : String :=
  match u with
  | .selector _ | .stray _ | .declaration .. | .call _ => "the " ++ u.words
  | .emptySelector | .escape | .atRule | .openCall _ | .openString => "an " ++ u.words
  | .nestedCall _ => "a " ++ u.words

/-- What a text says that this reader does not read: a refused spelling, or one outside the subset. -/
public inductive Problem where
  | refused (what : Unread)
  | unsupported (what : Unread)
  deriving Repr, BEq, Inhabited

public inductive Combinator where
  | descendant
  | child
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A compound selector: an optional type (`none` for `*` or no type), classes and ids, all required. -/
public structure Compound where
  type : Option String
  classes : Array String
  ids : Array String
  deriving Repr, BEq, Inhabited

/-- A complex selector, left to right; its last compound is the subject. -/
public structure Selector where
  head : Compound
  rest : Array (Combinator × Compound)
  deriving Repr, BEq, Inhabited

public structure Rule where
  selectors : Array Selector
  decls : Array Decl
  deriving Repr, BEq, Inhabited

@[expose] public def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- A line end (CSS Syntax 3 §3.3): line feed, carriage return or form feed. -/
@[expose] public def isLineEnd (c : Char) : Bool := c == '\n' || c == '\r' || c == '\x0c'

/-- A scan inside an atom: the closers its open blocks expect, innermost first, and the quote of
the string it is in. -/
structure Scan where
  closers : List Char
  quote : Option Char

/-- The closer that mirrors a block's opener (CSS Syntax 3 §5.5.9). -/
@[expose] public def mirror (c : Char) : Option Char :=
  if c == '(' then some ')' else if c == '[' then some ']' else if c == '{' then some '}' else none

/-- The scan a character opens: a string at a quote, a block at an opener. -/
def opening (c : Char) : Option Scan :=
  if c == '"' || c == '\'' then some ⟨[], some c⟩ else (mirror c).map fun m => ⟨[m], none⟩

/-- A scan past one character, `none` once it ends the atom: a string's quote or a line end with no
block around it, or the outermost block's mirror; a closer that mirrors no open block is content. -/
def scanStep (st : Scan) (c : Char) : Option Scan :=
  match st.quote with
  | some q =>
    if c == q || isLineEnd c then
      if st.closers.isEmpty then none else some ⟨st.closers, none⟩
    else some st
  | none =>
    if c == '"' || c == '\'' then some ⟨st.closers, some c⟩
    else match mirror c with
      | some m => some ⟨m :: st.closers, none⟩
      | none =>
        match st.closers with
        | top :: more => if c == top then (if more.isEmpty then none else some ⟨more, none⟩) else some st
        | [] => none

/-- How much text after an atom's first character its scan takes, counted onto `n`, or `none` when
the text ends first; an escape, a backslash and its next character, ends nothing. -/
def scanLen (st : Scan) : List Char → Nat → Option Nat
  | [], _ => none
  | ['\\'], _ => none
  | '\\' :: _ :: rest, n => scanLen st rest (n + 2)
  | c :: rest, n =>
    match scanStep st c with
    | none => some (n + 1)
    | some st' => scanLen st' rest (n + 1)

/-- CSS text onto `acc` as atoms (CSS Syntax 3 §4.3.5, §4.3.7, §5.5.9): a string or a block as its
scan takes it, else to the text's end; an escape, a backslash and its next character; any other
character alone. -/
def atomsGo (acc : Array (List Char)) : List Char → Array (List Char)
  | [] => acc
  | '\\' :: c :: rest => atomsGo (acc.push ['\\', c]) rest
  | c :: rest =>
    match opening c with
    | none => atomsGo (acc.push [c]) rest
    | some st =>
      match scanLen st rest 0 with
      | some k => atomsGo (acc.push (c :: rest.take k)) (rest.drop k)
      | none => acc.push (c :: rest)
termination_by l => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- CSS text as its atoms. -/
public def atoms (s : String) : List (List Char) := (atomsGo #[] s.toList).toList

/-- An atom opens no group: a block is one atom. -/
def noGroup (_ : List Char) : Bool := false

/-- A piece's atoms as its text. -/
def pieceText (piece : Array (List Char)) : String :=
  piece.foldl (fun t a => a.foldl String.push t) ""

/-- Text's atoms cut at each atom that is `sep` alone, each piece as its text. -/
def cutAtoms (sep : Char) (s : String) : Array String :=
  (KeyVal.splitTopAt noGroup noGroup (· == [sep]) (atoms s)).map pieceText

/-- `cutAtoms` in one pass, each atom read as `atomsGo` reads it and set onto the piece `cur`. -/
def cutGo (sep : Char) : List Char → String → Array String → Array String
  | [], cur, out => out.push cur
  | '\\' :: c :: rest, cur, out => cutGo sep rest ((cur.push '\\').push c) out
  | c :: rest, cur, out =>
    match opening c with
    | none => if c == sep then cutGo sep rest "" (out.push cur) else cutGo sep rest (cur.push c) out
    | some st =>
      match scanLen st rest 0 with
      | some k => cutGo sep (rest.drop k) ((rest.take k).foldl String.push (cur.push c)) out
      | none =>
        if c == sep && rest.isEmpty then (out.push cur).push ""
        else out.push (rest.foldl String.push (cur.push c))
termination_by l => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- CSS text with no comments in it (`stripComments` first) cut at each `sep` outside blocks,
strings and escapes, each piece as written: a list's items at `,` (CSS Syntax 3 §5.4.10), a block's
declarations at `;`; `cutAtoms` (`splitList_eq_cutAtoms`). -/
public def splitList (sep : Char) (s : String) : Array String := cutGo sep s.toList "" #[]

/-- Whether an atom is whole: a string its quote or a line end ended, a block its mirror closed, or
any other atom but a lone backslash. -/
public def closedAtom : List Char → Bool
  | c :: b =>
    match opening c with
    | some st => scanLen st b 0 == some b.length
    | none => !(c == '\\' && b.isEmpty)
  | [] => true

/-- The byte at `i` of a text's UTF-8 encoding, 0 past its end. -/
def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/-- Whether a byte encodes a line end. -/
def lineEndByte (b : UInt8) : Bool := b == 10 || b == 13 || b == 12

/-- Whether a byte encodes a quote. -/
def quoteByte (b : UInt8) : Bool := b == 34 || b == 39

/-- The text between two byte offsets, each before an ASCII byte or at an end. -/
def slice (s : String) (b e : Nat) : String := String.Pos.Raw.extract s ⟨b⟩ ⟨e⟩

/-- The byte offset past a comment's closing `*/` at or after `j`, or the text's end. -/
def commentEnd (s : String) (n j : Nat) : { k : Nat // j ≤ k } :=
  if h : j + 1 < n then
    if byteAt s j == 42 && byteAt s (j + 1) == 47 then ⟨j + 2, by omega⟩
    else
      let ⟨k, hk⟩ := commentEnd s n (j + 1)
      ⟨k, by omega⟩
  else ⟨max n j, by omega⟩
termination_by n - j

/-- `stripComments` from byte `i` on, `out` holding the text before `start` with its comments
removed, `quote` the open string's quote byte or 0. -/
def stripGo (s : String) (n i start : Nat) (quote : UInt8) (out : String) (cut : Bool) : String :=
  if h : i < n then
    let c := byteAt s i
    if quote != 0 then
      stripGo s n (i + 1) start (if c == quote || lineEndByte c then 0 else quote) out cut
    else if c == 47 && i + 1 < n && byteAt s (i + 1) == 42 then
      let ⟨j, hj⟩ := commentEnd s n (i + 2)
      have : n - j < n - i := by
        have := Nat.le_max_left n (i + 2)
        omega
      stripGo s n j j 0 ((out ++ slice s start i).push ' ') true
    else stripGo s n (i + 1) start (if quoteByte c then c else 0) out cut
  else if cut then
    let rest := slice s start n
    out ++ rest
  else s
termination_by n - i

/-- `s` with its comments removed: `/* … */`, an unterminated one to the end; a scan over its bytes,
whose markers are all ASCII. -/
public def stripComments (s : String) : String := stripGo s s.utf8ByteSize 0 0 0 "" false

/-- A character a fragment identifier in `url(#…)` may hold. -/
@[expose] public def idChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'

/-- A character a numeric colour function's channels may hold. -/
@[expose] public def channelChar (c : Char) : Bool :=
  c.isDigit || c == '.' || c == '%' || c == 'e' || c == 'E' || c == '+' || c == '-' ||
    c == ',' || c == '/' || c == ' '

/-- Whether a call is one this reader admits: a fragment `url(#id)` or a numeric `rgb()`/`rgba()`. -/
public def admitsCall (name arg : String) : Bool :=
  let n := name.toLower
  if n == "url" then
    let a := arg.trimAscii.toString
    let a := if a.length ≥ 2 && (a.startsWith "\"" && a.endsWith "\"" || a.startsWith "'" && a.endsWith "'")
      then ((a.drop 1).dropEnd 1).toString else a
    a.startsWith "#" && a.length > 1 && (a.drop 1).all idChar
  else if n == "rgb" || n == "rgba" then
    !arg.isEmpty && arg.all channelChar
  else false

/-- The first parenthesis at or after byte `j`, and whether it opens, or the text's end. -/
def parenAt (s : String) (n j : Nat) : { k : Nat // j ≤ k } × Option Bool :=
  if _h : j < n then
    let d := byteAt s j
    if d == 41 then (⟨j, Nat.le_refl _⟩, some false)
    else if d == 40 then (⟨j, Nat.le_refl _⟩, some true)
    else
      let (⟨k, hk⟩, r) := parenAt s n (j + 1)
      (⟨k, by omega⟩, r)
  else (⟨j, Nat.le_refl _⟩, none)
termination_by n - j

/-- Whether a byte encodes an identifier character this reader names a call by. -/
def callNameByte (c : UInt8) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 45 || c == 95

/-- `refusedIn` from byte `i` on, `quote` the open string's quote byte or 0, `ident` the name a
call opening here would have. -/
def refusedGo (s : String) (n i : Nat) (quote : UInt8) (ident : String) : Option Unread :=
  if h : i < n then
    let c := byteAt s i
    if c == 92 then some .escape
    else if c == 64 then some .atRule
    else if quote != 0 then
      refusedGo s n (i + 1) (if c == quote || lineEndByte c then 0 else quote) ident
    else if quoteByte c then refusedGo s n (i + 1) c ""
    else if c == 40 then
      match parenAt s n (i + 1) with
      | (⟨j, hj⟩, some false) =>
        if admitsCall ident (slice s (i + 1) j) then refusedGo s n (j + 1) 0 ""
        else some (.call ident)
      | (_, some true) => some (.nestedCall ident)
      | (_, none) => some (.openCall ident)
    else
      refusedGo s n (i + 1) 0 (if callNameByte c then ident.push (Char.ofNat c.toNat) else "")
  else if quote != 0 then some .openString
  else none
termination_by n - i

/-- The first spelling this reader refuses: an escape or an at-sign anywhere, an unterminated
string, or a function outside strings that is nested, unterminated or not admitted; a scan over
its bytes, whose markers are all ASCII. -/
public def refusedIn (s : String) : Option Unread := refusedGo s s.utf8ByteSize 0 0 ""

/-- `brokenString` from byte `i` on, `quote` the open string's quote byte or 0. -/
def brokenGo (s : String) (n i : Nat) (quote : UInt8) : Bool :=
  if _h : i < n then
    let c := byteAt s i
    if quote != 0 then
      if c == quote then brokenGo s n (i + 1) 0
      else if lineEndByte c then true
      else brokenGo s n (i + 1) quote
    else brokenGo s n (i + 1) (if quoteByte c then c else 0)
  else false
termination_by n - i

/-- Whether a string in `s` is broken by a line end (CSS Syntax 3 §4.3.5); a scan over its bytes. -/
public def brokenString (s : String) : Bool := brokenGo s s.utf8ByteSize 0 0

/-- Text on one line as a diagnostic names it: each run of white space outside strings one blank,
a string as written, a line end that breaks one a blank. -/
public def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut quote : Option Char := none
  let mut gap := false
  let mut esc := false
  for c in s.toList do
    if esc && !isLineEnd c then
      out := out.push c
      esc := false
      continue
    esc := false
    match quote with
    | some q =>
      if isLineEnd c then
        quote := none
        gap := true
      else
        out := out.push c
        if c == '\\' then esc := true
        else if c == q then quote := none
    | none =>
      if isWs c then gap := true
      else
        if gap && !out.isEmpty then out := out.push ' '
        gap := false
        out := out.push c
        if c == '\\' then esc := true
        else if c == '"' || c == '\'' then quote := some c
  return out

/-- A declaration's value without its trailing `!important`, and whether it held one (CSS Syntax 3
§5.5.6). -/
public def importance (value : String) : String × Bool :=
  if !value.contains '!' then (value, false) else
  let parts := splitList '!' value
  match parts.back? with
  | some imp =>
    if parts.size ≥ 2 && imp.trimAscii.toString.toLower == "important" then
      (("!".intercalate parts.pop.toList).trimAscii.toString, true)
    else (value, false)
  | none => (value, false)

/-- A declaration block's declarations, read as written: the caller strips its comments and rules
out its refused spellings. -/
def declsOf (text : String) : Except Unread (Array Decl) := do
  let mut out : Array Decl := #[]
  for part in splitList ';' text do
    let p := part.trimAscii.toString
    if p.isEmpty then continue
    if brokenString part then
      throw (.declaration (oneLine p) true)
    match p.splitOn ":" with
    | prop :: rest@(_ :: _) =>
      let prop := prop.trimAscii.toString.toLower
      let (value, important) := importance (":".intercalate rest).trimAscii.toString
      if prop.isEmpty || !prop.all (fun c => c.isAlphanum || c == '-') then
        throw (.declaration (oneLine p) false)
      out := out.push { prop, value, important }
    | _ => throw (.declaration (oneLine p) false)
  return out

/-- A declaration block's declarations in order; a malformed one is unsupported, a refused spelling refused. -/
public def parseDecls (text : String) : Except Problem (Array Decl) := do
  let text := stripComments text
  if let some what := refusedIn text then throw (.refused what)
  match declsOf text with
  | .ok ds => pure ds
  | .error what => throw (.unsupported what)

/-- A character of a CSS identifier: a letter, digit, `-`, `_` or non-ASCII. -/
@[expose] public def identChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c.toNat ≥ 128

/-- Text past the one blank that may end a hex escape. -/
def dropBlank : List Char → List Char
  | w :: more => if isWs w then more else w :: more
  | [] => []

private theorem dropBlank_length (l : List Char) : (dropBlank l).length ≤ l.length := by
  cases l with
  | nil => simp [dropBlank]
  | cons w more => simp only [dropBlank]; split <;> simp

/-- Escaped text's characters (CSS Syntax 3 §4.3.7): one to six hex digits and a blank after them as
their code point, U+FFFD for none, a surrogate or one past Unicode; an escaped line end as nothing
(§4.3.5); any other escaped character as itself. -/
public def unescape : List Char → List Char
  | [] => []
  | '\\' :: c :: rest =>
    if isLineEnd c then unescape rest
    else if (Hex.digit? c).isSome then
      let more := (rest.takeWhile (Hex.digit? · |>.isSome)).take 5
      let n := (c :: more).foldl (fun n d => n * 16 + (Hex.digit? d).getD 0) 0
      let ch := if n == 0 || (0xD800 ≤ n && n ≤ 0xDFFF) || n > 0x10FFFF then '\uFFFD' else Char.ofNat n
      ch :: unescape (dropBlank (rest.drop more.length))
    else c :: unescape rest
  | ['\\'] => ['\uFFFD']
  | c :: rest => c :: unescape rest
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := dropBlank_length (rest.drop (List.take 5 (List.takeWhile
        (fun x => (Hex.digit? x).isSome) rest)).length); simp at this ⊢; omega)

/-- Text's words, cut at white space outside escapes, a hex escape's ending blank its own (§4.3.7). -/
public def words (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut cur := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '\\' && i + 1 < cs.size then
        cur := (cur.push c).push (cs[i + 1]?.getD c)
        let mut j := i + 2
        if (Hex.digit? (cs[i + 1]?.getD ' ')).isSome then
          for _ in [0:5] do
            if j < cs.size && (Hex.digit? (cs[j]?.getD ' ')).isSome then
              cur := cur.push (cs[j]?.getD ' ')
              j := j + 1
          if j < cs.size && isWs (cs[j]?.getD 'x') then
            cur := cur.push ' '
            j := j + 1
        i := j
      else if isWs c then
        unless cur.isEmpty do out := out.push cur
        cur := ""
        i := i + 1
      else
        cur := cur.push c
        i := i + 1
  unless cur.isEmpty do out := out.push cur
  return out.toList

/-- Whether text is one CSS identifier (CSS Syntax 3 §4.3.11): identifier characters or escapes, not
starting with a digit, a `-` followed by a digit, or a lone `-`. -/
public def identifier (cs : List Char) : Bool :=
  let units : Option (List (Bool × Char)) := go cs
  match units with
  | some ((false, c) :: more) =>
    !c.isDigit && (c != '-' || match more with
      | (esc, d) :: _ => esc || !d.isDigit
      | [] => false)
  | some ((true, _) :: _) => true
  | _ => false
where
  go : List Char → Option (List (Bool × Char))
    | [] => some []
    | '\\' :: c :: rest =>
      if isLineEnd c then none
      else if (Hex.digit? c).isSome then
        let more := (rest.takeWhile (Hex.digit? · |>.isSome)).take 5
        ((true, c) :: ·) <$> go (dropBlank (rest.drop more.length))
      else ((true, c) :: ·) <$> go rest
    | ['\\'] => none
    | c :: rest => if identChar c then ((false, c) :: ·) <$> go rest else none
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := dropBlank_length (rest.drop (List.take 5 (List.takeWhile
          (fun x => (Hex.digit? x).isSome) rest)).length); simp at this ⊢; omega)

/-- One compound selector's text, unless it is outside the subset. -/
public def parseCompound (s : String) : Option Compound := do
  let cs := s.toList
  let typeChars := cs.takeWhile (fun c => identChar c || c == '*')
  let typ := String.ofList typeChars
  let mut rest := cs.drop typeChars.length
  let type : Option String ← if typ.isEmpty || typ == "*" then pure none
    else if typ.all identChar then pure (some typ) else failure
  let mut classes : Array String := #[]
  let mut ids : Array String := #[]
  for _ in [0:cs.length + 1] do
    match rest with
    | [] => break
    | '.' :: more =>
      let name := more.takeWhile identChar
      if name.isEmpty then failure
      classes := classes.push (String.ofList name)
      rest := more.drop name.length
    | '#' :: more =>
      let name := more.takeWhile identChar
      if name.isEmpty then failure
      ids := ids.push (String.ofList name)
      rest := more.drop name.length
    | _ => failure
  if type.isNone && classes.isEmpty && ids.isEmpty && typ != "*" then failure
  return { type, classes, ids }

/-- One complex selector's text: compounds joined by white space (descendant) or `>` (child); one
outside the subset is named whole. -/
public def parseSelector (s : String) : Except Unread Selector := do
  let outside : Unit → Unread := fun _ => .selector (oneLine s)
  let spaced := (s.replace ">" " > ").trimAscii.toString
  let words := (spaced.split isWs).toList.map (·.toString) |>.filter (!·.isEmpty)
  match words with
  | [] => throw .emptySelector
  | first :: more =>
    let some head := parseCompound first | throw (outside ())
    let mut rest : Array (Combinator × Compound) := #[]
    let mut pending := Combinator.descendant
    for w in more do
      if w == ">" then pending := .child
      else
        let some c := parseCompound w | throw (outside ())
        rest := rest.push (pending, c)
        pending := .descendant
    if pending == .child then throw (outside ())
    return { head, rest }

/-- How specific a selector is (Selectors 4 §16): its ids, classes, types. -/
@[expose] public def Selector.specificity (sel : Selector) : Nat × Nat × Nat :=
  let all := #[sel.head] ++ sel.rest.map (·.2)
  (all.foldl (fun n c => n + c.ids.size) 0, all.foldl (fun n c => n + c.classes.size) 0,
    all.foldl (fun n c => n + (if c.type.isSome then 1 else 0)) 0)

/-- A style sheet's rules in order, each the text before a `{` block and the block, the end of the
text closing a block still open (CSS Syntax 3 §5.5.3, §5.5.9), a rule outside the subset dropped and
named and a refused spelling refusing the sheet. -/
public def parseSheet (text : String) : Except Unread (Array Rule × Array Unread) := do
  let text := stripComments text
  if let some what := refusedIn text then throw what
  let mut rules : Array Rule := #[]
  let mut dropped : Array Unread := #[]
  let mut prelude := ""
  for a in atoms text do
    if a.head? != some '{' then
      prelude := a.foldl String.push prelude
    else
      let body := if closedAtom a then (a.drop 1).dropLast else a.drop 1
      let sels := (splitList ',' prelude).map (·.trimAscii.toString)
      match sels.mapM parseSelector, declsOf (String.ofList body) with
      | .ok sels, .ok ds => rules := rules.push { selectors := sels, decls := ds }
      | .error why, _ | _, .error why => dropped := dropped.push why
      prelude := ""
  unless prelude.trimAscii.isEmpty do
    dropped := dropped.push (.stray (oneLine prelude))
  return (rules, dropped)

/-- What a selector reads of an element: its type, classes and id. -/
public structure Subject where
  type : String
  classes : Array String
  id : Option String
  deriving Repr, BEq, Inhabited

@[expose] public def Compound.matches (c : Compound) (e : Subject) : Bool :=
  c.type.all (· == e.type) && c.classes.all (e.classes.contains ·) &&
    c.ids.all (some · == e.id)

/-- Whether the remaining compounds match the ancestors `up`, innermost first. -/
public def matchUp (parts : List (Combinator × Compound)) (up : List Subject) : Bool :=
  match parts with
  | [] => true
  | (comb, c) :: more =>
    match comb with
    | .child =>
      match up with
      | p :: ps => c.matches p && matchUp more ps
      | [] => false
    | .descendant => tryAll c more up
where
  tryAll (c : Compound) (more : List (Combinator × Compound)) : List Subject → Bool
    | [] => false
    | p :: ps => (c.matches p && matchUp more ps) || tryAll c more ps

/-- Does `sel` match the element `e` whose ancestors, innermost first, are
`up`? -/
public def Selector.matches (sel : Selector) (e : Subject) (up : List Subject) : Bool :=
  let comps := #[sel.head] ++ sel.rest.map (·.2)
  let combs := sel.rest.map (·.1)
  match comps.back? with
  | none => false
  | some subject =>
    let pairs := (combs.zip comps.pop).toList.reverse
    subject.matches e && matchUp pairs up

/-- What a compound requires of an element first: an id, else a class, else a type; `none` when universal. -/
@[expose] public def Compound.key (c : Compound) : Option (Nat × String) :=
  match c.ids[0]? with
  | some i => some (0, i)
  | none =>
    match c.classes[0]? with
    | some c => some (1, c)
    | none => c.type.map ((2 : Nat), ·)

/-- The key a selector's subject compound requires (`Compound.key`). -/
@[expose] public def Selector.key (sel : Selector) : Option (Nat × String) :=
  ((sel.rest.back?.map (·.2)).getD sel.head).key

/-- The key the compound nearest the subject requires of an ancestor, if the selector has one. -/
@[expose] public def Selector.upKey (sel : Selector) : Option (Nat × String) :=
  if sel.rest.isEmpty then none
  else ((sel.rest.pop.back?.map (·.2)).getD sel.head).key

/-- Every key an element offers a compound: its id, its classes, its type. -/
@[expose] public def Subject.keys (e : Subject) : Array (Nat × String) :=
  (e.id.map ((0 : Nat), ·)).toArray ++ e.classes.map ((1 : Nat), ·) ++ #[(2, e.type)]

/-- A sheet's rules with each selector filed under the keys it requires, so an element meets only
the selectors it can match. -/
public structure RuleIndex where
  rules : Array Rule
  /-- Each rule's first declaration's index in source order. -/
  offsets : Array Nat
  /-- Selectors with no keyed ancestor compound, by their subject's key. -/
  byKey : Std.HashMap (Nat × String) (Array (Nat × Nat))
  /-- Selectors by their subject's key and the key of the compound nearest it. -/
  byPair : Std.HashMap ((Nat × String) × (Nat × String)) (Array (Nat × Nat))
  universal : Array (Nat × Nat)
  deriving Inhabited

public def RuleIndex.ofRules (rules : Array Rule) : RuleIndex := Id.run do
  let mut offsets : Array Nat := #[]
  let mut total := 0
  let mut byKey : Std.HashMap (Nat × String) (Array (Nat × Nat)) := {}
  let mut byPair : Std.HashMap ((Nat × String) × (Nat × String)) (Array (Nat × Nat)) := {}
  let mut universal : Array (Nat × Nat) := #[]
  for h : i in [0:rules.size] do
    let r := rules[i]
    offsets := offsets.push total
    total := total + r.decls.size
    for h2 : j in [0:r.selectors.size] do
      let sel := r.selectors[j]
      match sel.key, sel.upKey with
      | some k, some u => byPair := byPair.insert (k, u) ((byPair.getD (k, u) #[]).push (i, j))
      | some k, none => byKey := byKey.insert k ((byKey.getD k #[]).push (i, j))
      | none, _ => universal := universal.push (i, j)
  return { rules, offsets, byKey, byPair, universal }

/-- The selectors an element below `up` can match: under its keys, under its keys and an
ancestor's, and the universal ones. -/
public def RuleIndex.candidates (ix : RuleIndex) (e : Subject) (up : List Subject) :
    Array (Nat × Nat) := Id.run do
  let keys := e.keys
  let mut out : Array (Nat × Nat) := keys.foldl (fun acc k => acc ++ ix.byKey.getD k #[]) #[]
  if !ix.byPair.isEmpty then
    let mut ups : Std.HashSet (Nat × String) := {}
    for a in up do
      for k in a.keys do ups := ups.insert k
    let upKeys := ups.toArray
    for k in keys do
      for u in upKeys do
        out := out ++ ix.byPair.getD (k, u) #[]
  return out ++ ix.universal

/-- A declaration's place in the cascade (CSS Cascading 4 §6.1): importance, level, specificity,
source order; the greater key wins. -/
public structure Key where
  important : Bool
  level : Nat
  spec : Nat × Nat × Nat
  order : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Lexicographic order on lists of naturals: the first differing entry
decides, and a proper prefix is below. -/
@[expose] public def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- A key's entries in the order the cascade reads them. -/
@[expose] public def Key.toList (k : Key) : List Nat :=
  [if k.important then 1 else 0, k.level, k.spec.1, k.spec.2.1, k.spec.2.2, k.order]

/-- The cascade's order on keys: lexicographic, importance first. -/
@[expose] public def Key.lt (a b : Key) : Bool := lexLt a.toList b.toList

/-- The best of the candidates onto the best so far; a candidate wins only with a greater key. -/
public def winnerList (best : Option (Key × String)) : List (Key × String) → Option (Key × String)
  | [] => best
  | c :: rest =>
    winnerList (match best with
      | none => some c
      | some b => if Key.lt b.1 c.1 then some c else some b) rest

/-- The cascaded value: the declaration whose key is greatest. -/
@[expose] public def cascade (cands : Array (Key × String)) : Option String :=
  (winnerList none cands.toList).map (·.2)

public theorem lexLt_irrefl : ∀ l : List Nat, lexLt l l = false
  | [] => rfl
  | a :: as => by simp [lexLt, lexLt_irrefl as]

public theorem lexLt_trans : ∀ a b c : List Nat,
    lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans xs ys zs h1 h2⟩

public theorem lexLt_not_trans : ∀ a b c : List Nat, a.length = b.length → b.length = c.length →
    lexLt a b = false → lexLt b c = false → lexLt a c = false
  | [], [], [], _, _, _, _ => rfl
  | [], [], _ :: _, _, h, _, _ => by simp at h
  | [], _ :: _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _, _ => by simp at h
  | x :: xs, y :: ys, z :: zs, l1, l2, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at l1 l2
    simp only [lexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt,
      Bool.and_eq_false_imp, beq_iff_eq] at h1 h2 ⊢
    refine ⟨by omega, fun hxz => ?_⟩
    have hxy : x = y := by omega
    have hyz : y = z := by omega
    exact lexLt_not_trans xs ys zs l1 l2 (h1.2 hxy) (h2.2 hyz)

@[simp] public theorem Key.toList_length (k : Key) : k.toList.length = 6 := rfl

private def winnerStep (best : Option (Key × String)) (c : Key × String) : Option (Key × String) :=
  match best with
  | none => some c
  | some b => if Key.lt b.1 c.1 then some c else some b

private theorem winnerList_cons (best : Option (Key × String)) (c : Key × String)
    (rest : List (Key × String)) : winnerList best (c :: rest) = winnerList (winnerStep best c) rest := by
  cases best <;> rfl

private theorem winnerList_mem (best : Option (Key × String)) (cs : List (Key × String))
    (w : Key × String) (h : winnerList best cs = some w) : best = some w ∨ w ∈ cs := by
  induction cs generalizing best with
  | nil => exact Or.inl h
  | cons c rest ih =>
    rw [winnerList_cons] at h
    rcases ih _ h with hs | hm
    · cases best with
      | none => simp only [winnerStep, Option.some.injEq] at hs; subst hs; simp
      | some b =>
        simp only [winnerStep] at hs
        split at hs
        · simp only [Option.some.injEq] at hs; subst hs; simp
        · exact Or.inl hs
    · exact Or.inr (List.mem_cons_of_mem _ hm)

private theorem winnerList_max (best : Option (Key × String)) (cs : List (Key × String))
    (w : Key × String) (h : winnerList best cs = some w) :
    (∀ c ∈ cs, Key.lt w.1 c.1 = false) ∧ (∀ b, best = some b → Key.lt w.1 b.1 = false) := by
  induction cs generalizing best with
  | nil =>
    refine ⟨by simp, fun b hb => ?_⟩
    simp only [winnerList] at h
    rw [h] at hb
    cases hb
    exact lexLt_irrefl _
  | cons c rest ih =>
    rw [winnerList_cons] at h
    obtain ⟨hrest, hnext⟩ := ih _ h
    cases best with
    | none =>
      exact ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnext x rfl
        · exact hrest x hx, fun _ hb => by cases hb⟩
    | some b =>
      by_cases hlt : Key.lt b.1 c.1 = true
      · have hwc := hnext c (by simp [winnerStep, hlt])
        refine ⟨fun x hx => ?_, fun b' hb => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hwc
          · exact hrest x hx
        · cases hb
          cases hwb : Key.lt w.1 b.1
          · rfl
          · exact absurd (lexLt_trans _ _ _ hwb hlt) (by simp [Key.lt] at hwc ⊢; exact hwc)
      · have hlt' : Key.lt b.1 c.1 = false := by simpa using hlt
        have hwb := hnext b (by simp [winnerStep, hlt'])
        refine ⟨fun x hx => ?_, fun b' hb => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact lexLt_not_trans _ _ _ (by simp) (by simp) hwb hlt'
          · exact hrest x hx
        · cases hb; exact hwb

public theorem cascade_exact (cands : Array (Key × String)) (v : String) (h : cascade cands = some v) :
    ∃ k, (k, v) ∈ cands ∧ ∀ c ∈ cands, Key.lt k c.1 = false := by
  unfold cascade at h
  cases hw : winnerList none cands.toList with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨w.1, ?_, fun c hc => (winnerList_max none _ w hw).1 c (by simpa using hc)⟩
    rcases winnerList_mem none _ w hw with h0 | hm
    · cases h0
    · simpa using hm

private theorem flatten_intercalate (a : List Char) :
    ∀ segs : List (List (List Char)),
      ([a].intercalate segs).flatten = a.intercalate (segs.map List.flatten)
  | [] => by simp
  | [x] => by simp [List.intercalate_singleton]
  | x :: y :: rest => by
    rw [List.intercalate_cons_cons, List.map_cons, List.map_cons, List.intercalate_cons_cons,
      ← List.map_cons, ← flatten_intercalate a (y :: rest)]
    simp

private theorem atomsGo_flatten (acc : Array (List Char)) (l : List Char) :
    (atomsGo acc l).toList.flatten = acc.toList.flatten ++ l := by
  fun_induction atomsGo acc l <;> simp_all

/-- Joined, the atoms of a text are the text. -/
private theorem atoms_flatten (s : String) : (atoms s).flatten = s.toList := by
  simp [atoms, atomsGo_flatten]

private theorem opening_backslash : opening '\\' = none := by decide

private theorem scanLen_bound (st : Scan) (l : List Char) (n m : Nat)
    (h : scanLen st l n = some m) : n < m ∧ m ≤ n + l.length := by
  fun_induction scanLen st l n generalizing m with
  | case1 => simp at h
  | case2 => simp at h
  | case3 st x rest n ih =>
    have := ih m h
    simp only [List.length_cons]
    omega
  | case4 _ c rest n _ _ _ =>
    simp only [Option.some.injEq] at h
    simp only [List.length_cons]
    omega
  | case5 _ c rest n _ _ st' _ ih =>
    have := ih m h
    simp only [List.length_cons]
    omega

/-- A scan's end depends only on the text it took: whatever follows, it ends at the same place. -/
private theorem scanLen_prefix (st : Scan) (l : List Char) (n m : Nat)
    (h : scanLen st l n = some m) (t : List Char) :
    scanLen st (l.take (m - n) ++ t) n = some m := by
  fun_induction scanLen st l n generalizing m with
  | case1 => simp at h
  | case2 => simp at h
  | case3 st x rest n ih =>
    have hb := scanLen_bound st rest (n + 2) m h
    have hk : m - n = (m - (n + 2)) + 2 := by omega
    rw [hk]
    simp only [List.take_succ_cons, List.cons_append]
    rw [scanLen.eq_3]
    exact ih m h
  | case4 st c rest n h1 h2 hs =>
    simp only [Option.some.injEq] at h
    subst h
    have hc : c ≠ '\\' := by
      intro hc
      subst hc
      cases rest with
      | nil => exact h1 rfl rfl
      | cons x r => exact h2 x r rfl rfl
    have hk : n + 1 - n = 1 := by omega
    rw [hk]
    simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append]
    rw [scanLen.eq_4 st n c t (fun hc' _ => hc hc') (fun _ _ hc' _ => hc hc')]
    simp [hs]
  | case5 st c rest n h1 h2 st' hs ih =>
    have hb := scanLen_bound st' rest (n + 1) m h
    have hk : m - n = (m - (n + 1)) + 1 := by omega
    rw [hk]
    simp only [List.take_succ_cons, List.cons_append]
    have hc : c ≠ '\\' := by
      intro hc
      subst hc
      cases rest with
      | nil => exact h1 rfl rfl
      | cons x r => exact h2 x r rfl rfl
    rw [scanLen.eq_4 st n c _ (fun hc' _ => hc hc') (fun _ _ hc' _ => hc hc')]
    simp only [hs]
    exact ih m h

/-- An atom its own last character ends: an escape, a character standing alone, or a string or
block the reader closed. -/
private def Whole (a : List Char) : Prop :=
  (∃ x, a = ['\\', x]) ∨ (∃ c, a = [c] ∧ c ≠ '\\' ∧ opening c = none) ∨
    (∃ c b st, a = c :: b ∧ opening c = some st ∧ scanLen st b 0 = some b.length)

/-- An atom only the text's end ends: a lone backslash, or a string or block still open. -/
private def Open (a : List Char) : Prop :=
  a = ['\\'] ∨ (∃ c b st, a = c :: b ∧ opening c = some st ∧ scanLen st b 0 = none)

/-- Atoms as the reader makes them: each whole but the last, which may be open. -/
private def Made : List (List Char) → Prop
  | [] => True
  | [a] => Whole a ∨ Open a
  | a :: b :: rest => Whole a ∧ Made (b :: rest)

private theorem opening_ne {c : Char} {st : Scan} (h : opening c = some st) : c ≠ '\\' := by
  intro hc
  subst hc
  simp [opening_backslash] at h

private theorem notEsc {c : Char} {rest : List Char} (h : c ≠ '\\') :
    ∀ (c' : Char) (r : List Char), c = '\\' → rest = c' :: r → False :=
  fun _ _ hc _ => h hc

private theorem whole_reads (acc : Array (List Char)) (a tail : List Char) (h : Whole a) :
    atomsGo acc (a ++ tail) = atomsGo (acc.push a) tail := by
  rcases h with ⟨x, rfl⟩ | ⟨c, rfl, hb, ho⟩ | ⟨c, b, st, rfl, ho, hs⟩
  · simp [atomsGo.eq_2]
  · rw [List.cons_append, List.nil_append, atomsGo.eq_3 _ _ _ (notEsc hb)]
    simp [ho]
  · rw [List.cons_append, atomsGo.eq_3 _ _ _ (notEsc (opening_ne ho))]
    have hp := scanLen_prefix st b 0 b.length hs tail
    simp only [Nat.sub_zero, List.take_length] at hp
    simp [ho, hp]

private theorem open_reads (acc : Array (List Char)) (a : List Char) (h : Open a) :
    atomsGo acc a = acc.push a := by
  rcases h with rfl | ⟨c, b, st, rfl, ho, hs⟩
  · rw [atomsGo.eq_3 _ _ _ (fun _ _ _ h => by cases h)]
    simp [opening_backslash, atomsGo.eq_1]
  · rw [atomsGo.eq_3 _ _ _ (notEsc (opening_ne ho))]
    simp [ho, hs]

/-- Atoms as the reader makes them read back as themselves. -/
private theorem made_reads (acc : Array (List Char)) :
    ∀ L : List (List Char), Made L → atomsGo acc L.flatten = acc ++ L.toArray
  | [], _ => by simp [atomsGo.eq_1]
  | [a], h => by
    rcases h with hw | ho
    · simpa [atomsGo.eq_1] using whole_reads acc a [] hw
    · simpa using open_reads acc a ho
  | a :: b :: rest, h => by
    obtain ⟨hw, hrest⟩ := h
    rw [List.flatten_cons, whole_reads acc a _ hw, made_reads (acc.push a) (b :: rest) hrest]
    simp

private theorem made_cons (a : List Char) (L : List (List Char)) (ha : Whole a) (h : Made L) :
    Made (a :: L) := by
  cases L with
  | nil => exact .inl ha
  | cons b rest => exact ⟨ha, h⟩

private theorem made_append :
    ∀ A L : List (List Char), (∀ a ∈ A, Whole a) → Made L → Made (A ++ L)
  | [], _, _, h => h
  | a :: A, L, hA, h =>
    made_cons a (A ++ L) (hA a (by simp)) (made_append A L (fun x hx => hA x (by simp [hx])) h)

private theorem push_whole {acc : Array (List Char)} {a : List Char}
    (hacc : ∀ x ∈ acc.toList, Whole x) (ha : Whole a) : ∀ x ∈ (acc.push a).toList, Whole x := by
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hacc x hx
  · exact ha

/-- The reader's atoms are as it makes them. -/
private theorem atomsGo_made (acc : Array (List Char)) (l : List Char)
    (hacc : ∀ a ∈ acc.toList, Whole a) : Made (atomsGo acc l).toList := by
  fun_induction atomsGo acc l with
  | case1 acc => simpa using made_append acc.toList [] hacc trivial
  | case2 acc c _ ih => exact ih (push_whole hacc (.inl ⟨c, rfl⟩))
  | case3 acc c rest hesc ho ih =>
    by_cases hc : c = '\\'
    · subst hc
      cases rest with
      | nil =>
        rw [atomsGo.eq_1]
        simpa using made_append acc.toList [['\\']] hacc (.inr (.inl rfl))
      | cons x r => exact absurd rfl (hesc x r rfl)
    · exact ih (push_whole hacc (.inr (.inl ⟨c, rfl, hc, ho⟩)))
  | case4 acc c rest _ st ho k hk ih =>
    have hb := scanLen_bound st rest 0 k hk
    have hp := scanLen_prefix st rest 0 k hk []
    have hlen : (rest.take k).length = k := by simp; omega
    simp only [Nat.sub_zero, List.append_nil] at hp
    exact ih (push_whole hacc (.inr (.inr ⟨c, rest.take k, st, rfl, ho, by rw [hlen]; exact hp⟩)))
  | case5 acc c rest _ st ho hk =>
    simpa using made_append acc.toList [c :: rest] hacc (.inr (.inr ⟨c, rest, st, rfl, ho, hk⟩))

private theorem made_prefix : ∀ l1 l2 : List (List Char), Made (l1 ++ l2) → Made l1
  | [], _, _ => trivial
  | [a], l2, h => by
    cases l2 with
    | nil => simpa using h
    | cons b r => exact .inl h.1
  | a :: b :: l1, l2, h => ⟨h.1, made_prefix (b :: l1) l2 h.2⟩

private theorem made_suffix : ∀ l1 l2 : List (List Char), Made (l1 ++ l2) → Made l2
  | [], _, h => h
  | a :: l1, l2, h => by
    apply made_suffix l1 l2
    rw [List.cons_append] at h
    cases hl : (l1 ++ l2) with
    | nil => trivial
    | cons b r =>
      rw [hl] at h
      exact h.2

private theorem made_intercalate (sep : List (List Char)) :
    ∀ L : List (List (List Char)), Made (sep.intercalate L) → ∀ p ∈ L, Made p
  | [], _ => by simp
  | [p], h => by simpa [List.intercalate_singleton] using h
  | p :: q :: rest, h => by
    rw [List.intercalate_cons_cons, List.append_assoc] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact made_prefix _ _ h
    · have h' := made_suffix _ _ (made_suffix _ _ h)
      exact made_intercalate sep (q :: rest) h' x (by simpa using hx)

private theorem foldl_push (a : List Char) (t : String) :
    (a.foldl String.push t).toList = t.toList ++ a := by
  induction a generalizing t with
  | nil => simp
  | cons c rest ih => simp [ih, String.toList_push]

private theorem pieceText_eq (piece : Array (List Char)) :
    pieceText piece = String.ofList (piece.toList.flatMap id) := by
  apply String.toList_inj.mp
  have h : ∀ (l : List (List Char)) (t : String),
      (l.foldl (fun t a => a.foldl String.push t) t).toList = t.toList ++ l.flatten := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih => intro t; simp [ih, foldl_push]
  simp [pieceText, ← Array.foldl_toList, h]

private theorem atomsGo_acc_append (acc' acc : Array (List Char)) (l : List Char) :
    atomsGo (acc' ++ acc) l = acc' ++ atomsGo acc l := by
  fun_induction atomsGo acc l with
  | case1 acc => simp [atomsGo.eq_1]
  | case2 acc c rest ih => simp only [atomsGo.eq_2, Array.push_append, ih]
  | case3 acc c rest hesc ho ih =>
    simp only [atomsGo.eq_3 _ _ _ hesc, ho, Array.push_append, ih]
  | case4 acc c rest hesc st ho k hk ih =>
    simp only [atomsGo.eq_3 _ _ _ hesc, ho, hk, Array.push_append, ih]
  | case5 acc c rest hesc st ho hk =>
    simp [atomsGo.eq_3 _ _ _ hesc, ho, hk]

private theorem atomsGo_acc (acc : Array (List Char)) (l : List Char) :
    atomsGo acc l = acc ++ atomsGo #[] l := by
  simpa using atomsGo_acc_append acc #[] l

private theorem pieceText_push (piece : Array (List Char)) (a : List Char) :
    pieceText (piece.push a) = a.foldl String.push (pieceText piece) := by
  simp [pieceText]

private theorem cutGo_cut (sep : Char) (l : List Char) (cur : String) (out : Array String) :
    ∀ curA outA, cur = pieceText curA → out = outA.map pieceText →
      cutGo sep l cur out = (KeyVal.cutEach (· == [sep]) (atomsGo #[] l).toList curA outA).map
        pieceText := by
  fun_induction cutGo sep l cur out with
  | case1 cur out =>
    intro curA outA hc ho
    subst hc ho
    simp [atomsGo.eq_1, KeyVal.cutEach]
  | case2 c rest cur out ih =>
    intro curA outA hc ho
    rw [atomsGo.eq_2, atomsGo_acc]
    simp only [List.push_toArray, List.nil_append, Array.toList_append, List.cons_append,
      KeyVal.cutEach]
    simp only [List.cons.injEq, reduceCtorEq, and_false, beq_iff_eq, ite_false]
    refine ih (curA.push ['\\', c]) outA ?_ ho
    simp [pieceText_push, hc]
  | case3 c rest cur out hesc ho hs ih =>
    intro curA outA hc hout
    rw [atomsGo.eq_3 _ _ _ hesc]
    simp only [ho]
    rw [atomsGo_acc]
    simp only [List.push_toArray, List.nil_append, Array.toList_append, List.cons_append,
      KeyVal.cutEach]
    have : ([c] == [sep]) = true := by simpa using hs
    simp only [this, ite_true]
    exact ih #[] (outA.push curA) rfl (by simp [hc, hout])
  | case4 c rest cur out hesc ho hs ih =>
    intro curA outA hc hout
    rw [atomsGo.eq_3 _ _ _ hesc]
    simp only [ho]
    rw [atomsGo_acc]
    simp only [List.push_toArray, List.nil_append, Array.toList_append, List.cons_append,
      KeyVal.cutEach]
    have : ([c] == [sep]) = false := by simpa using hs
    simp only [this]
    exact ih (curA.push [c]) outA (by simp [pieceText_push, hc]) hout
  | case5 c rest cur out hesc st ho k hk ih =>
    intro curA outA hc hout
    rw [atomsGo.eq_3 _ _ _ hesc]
    simp only [ho, hk]
    rw [atomsGo_acc]
    simp only [List.push_toArray, List.nil_append, Array.toList_append, List.cons_append,
      KeyVal.cutEach]
    have hb := scanLen_bound st rest 0 k hk
    have hne : rest.take k ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp only [List.length_take]
      omega
    have : ((c :: rest.take k) == [sep]) = false := by
      cases h : rest.take k with
      | nil => exact absurd h hne
      | cons x r => simp
    simp only [this]
    exact ih (curA.push (c :: rest.take k)) outA (by simp [pieceText_push, hc]) hout
  | case6 c rest cur out hesc st ho hk hs =>
    intro curA outA hc hout
    rw [atomsGo.eq_3 _ _ _ hesc]
    simp only [ho, hk]
    obtain ⟨hcs, hr⟩ : c = sep ∧ rest = [] := by simpa using hs
    subst hr hcs
    simp [KeyVal.cutEach, hc, hout, pieceText]
  | case7 c rest cur out hesc st ho hk hs =>
    intro curA outA hc hout
    rw [atomsGo.eq_3 _ _ _ hesc]
    simp only [ho, hk]
    have : ((c :: rest) == [sep]) = false := by
      cases rest with
      | nil => simpa using hs
      | cons x r => simp
    simp [KeyVal.cutEach, this, hc, hout, pieceText_push]

/-- `splitList` cuts as `cutAtoms` does: at each atom that is the separator alone. -/
theorem splitList_eq_cutAtoms (sep : Char) (s : String) : splitList sep s = cutAtoms sep s := by
  unfold splitList cutAtoms atoms
  rw [KeyVal.splitTopAt_ungrouped noGroup noGroup _ (fun _ => rfl) (fun _ => rfl)]
  exact cutGo_cut sep s.toList "" #[] #[] #[] rfl (by simp)

/-- Joined at `sep`, the pieces `splitList` cuts are the text it cut. -/
public theorem splitList_join_id (sep : Char) (s : String) :
    [sep].intercalate ((splitList sep s).toList.map String.toList) = s.toList := by
  have h := KeyVal.splitTopAt_join_id noGroup noGroup [sep] (atoms s)
  have hf := congrArg List.flatten h
  rw [flatten_intercalate, atoms_flatten] at hf
  simp only [splitList_eq_cutAtoms, cutAtoms, pieceText_eq, Array.toList_map, List.map_map,
    Function.comp_def, String.toList_ofList, List.flatMap_id]
  simpa [List.map_map, Function.comp_def] using hf

/-- Each piece's text reads back as the piece's own atoms. -/
private theorem piece_atoms (sep : Char) (s : String) :
    ∀ piece ∈ (KeyVal.splitTopAt noGroup noGroup (· == [sep]) (atoms s)).toList,
      atoms (pieceText piece) = piece.toList := by
  intro piece hpiece
  have hjoin := KeyVal.splitTopAt_join_id noGroup noGroup [sep] (atoms s)
  have hmade : Made piece.toList := by
    refine made_intercalate [[sep]] _ ?_ piece.toList (List.mem_map_of_mem hpiece)
    rw [hjoin]
    exact atomsGo_made #[] s.toList (by simp)
  simp only [atoms, pieceText_eq, String.toList_ofList, List.flatMap_id]
  rw [made_reads #[] piece.toList hmade]
  simp

/-- A piece `splitList` cuts holds no `sep` outside blocks, strings and escapes: cut again, it is
itself. -/
public theorem splitList_fixed_point (sep : Char) (s : String) :
    ∀ p ∈ (splitList sep s).toList, splitList sep p = #[p] := by
  intro p hp
  simp only [splitList_eq_cutAtoms, cutAtoms, Array.toList_map, List.mem_map] at hp
  obtain ⟨piece, hpiece, rfl⟩ := hp
  simp only [splitList_eq_cutAtoms, cutAtoms, piece_atoms sep s piece hpiece]
  rw [KeyVal.splitTopAt_fixed_point _ _ _ _ piece hpiece]
  simp

/-- `splitList` cuts only between atoms, so never inside a string, an escape or a block: the
pieces' atoms joined at the separator are the text's. -/
public theorem splitList_atoms_exact (sep : Char) (s : String) :
    [[sep]].intercalate ((splitList sep s).toList.map atoms) = atoms s := by
  have h := KeyVal.splitTopAt_join_id noGroup noGroup [sep] (atoms s)
  rw [← h]
  congr 1
  simp only [splitList_eq_cutAtoms, cutAtoms, Array.toList_map, List.map_map]
  exact List.map_congr_left fun piece hpiece => by
    simpa [Function.comp_def] using piece_atoms sep s piece hpiece

/-- A scan inside a block whose outermost closer is `m`. -/
private def InBlock (m : Char) (st : Scan) : Prop := st.closers ≠ [] ∧ st.closers.getLast? = some m

/-- A step inside a block stays inside it, or ends the atom at the block's mirror. -/
private theorem scanStep_inBlock (m : Char) (st : Scan) (c : Char) (h : InBlock m st) :
    (∀ st', scanStep st c = some st' → InBlock m st') ∧ (scanStep st c = none → c = m) := by
  obtain ⟨hne, hlast⟩ := h
  rcases st with ⟨closers, quote⟩
  have hempty : closers.isEmpty = false := by
    cases closers with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  cases quote with
  | some q =>
    constructor
    · intro st' hs
      simp only [scanStep] at hs
      split at hs
      · simp only [hempty, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        exact ⟨hne, hlast⟩
      · simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨hne, hlast⟩
    · intro hs
      simp only [scanStep] at hs
      split at hs
      · simp [hempty] at hs
      · simp at hs
  | none =>
    constructor
    · intro st' hs
      simp only [scanStep] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨hne, hlast⟩
      · split at hs
        · next m' _ =>
          simp only [Option.some.injEq] at hs
          subst hs
          refine ⟨List.cons_ne_nil _ _, ?_⟩
          simp only
          rw [List.getLast?_cons, hlast]
          rfl
        · split at hs
          · next top more =>
            split at hs
            · split at hs
              · simp at hs
              · next hmore =>
                simp only [Option.some.injEq] at hs
                subst hs
                have hm : more ≠ [] := by
                  intro h0
                  subst h0
                  simp at hmore
                refine ⟨hm, ?_⟩
                simp only
                cases more with
                | nil => exact absurd rfl hm
                | cons x xs => rwa [List.getLast?_cons_cons] at hlast
            · simp only [Option.some.injEq] at hs
              subst hs
              exact ⟨hne, hlast⟩
          · simp at hs
    · intro hs
      simp only [scanStep] at hs
      split at hs
      · simp at hs
      · split at hs
        · simp at hs
        · split at hs
          · next top more =>
            split at hs
            · next htop =>
              split at hs
              · next hmore =>
                have h0 : more = [] := by simpa using hmore
                subst h0
                simp only [List.getLast?_singleton, Option.some.injEq] at hlast
                have : c = top := by simpa using htop
                rw [this, hlast]
              · simp at hs
            · simp at hs
          · exact absurd rfl hne

/-- Where a scan inside a block ends, the character there is the block's mirror. -/
private theorem scanLen_inBlock (m : Char) (st : Scan) (l : List Char) (n k : Nat)
    (h : scanLen st l n = some k) (hb : InBlock m st) : l[k - n - 1]? = some m := by
  fun_induction scanLen st l n generalizing k with
  | case1 => simp at h
  | case2 => simp at h
  | case3 st x rest n ih =>
    have hbd := scanLen_bound st rest (n + 2) k h
    have hk : k - n - 1 = (k - (n + 2) - 1) + 2 := by omega
    rw [hk]
    simpa using ih k h hb
  | case4 st c rest n _ _ hs =>
    simp only [Option.some.injEq] at h
    subst h
    have := (scanStep_inBlock m st c hb).2 hs
    simp [this]
  | case5 st c rest n _ _ st' hs ih =>
    have hbd := scanLen_bound st' rest (n + 1) k h
    have hk : k - n - 1 = (k - (n + 1) - 1) + 1 := by omega
    rw [hk]
    simpa using ih k h ((scanStep_inBlock m st c hb).1 st' hs)

/-- A block the reader closes ends at its opener's mirror, never at another kind's closer. -/
public theorem closedAtom_mirror (c m : Char) (b : List Char) (hm : mirror c = some m)
    (h : closedAtom (c :: b) = true) : (c :: b).getLast? = some m := by
  have hq : c ≠ '"' ∧ c ≠ '\'' := by
    constructor <;> (intro hc; subst hc; simp [mirror] at hm)
  have ho : opening c = some ⟨[m], none⟩ := by
    simp [opening, hq.1, hq.2, hm]
  simp only [closedAtom, ho, beq_iff_eq] at h
  have hidx := scanLen_inBlock m ⟨[m], none⟩ b 0 b.length h ⟨by simp, by simp⟩
  have hpos := scanLen_bound ⟨[m], none⟩ b 0 b.length h
  cases b with
  | nil => simp at hpos
  | cons x xs =>
    rw [List.getLast?_cons_cons, List.getLast?_eq_getElem?]
    simpa using hidx

end LeanTex.Core.Css
