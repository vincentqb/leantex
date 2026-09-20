import LeanTex.Core.Diag
import LeanTex.Core.LocaleData

/-! BibTeX bibliography files, parsed in the pure core. The grammar is the
one btxdoc.tex and "Tame the BeaST" §2 document: `@type{key, field = value,
…}` entries whose values are `{…}`-balanced groups, `"…"` strings, or bare
numbers and `@string` macro names, concatenated with `#`; `@comment` and
`@preamble` are skipped; everything between entries is comment text by
definition. Reading the file is the driver's effect (`Ir.bibRefs`, the
`imageRefs` shape); this module only ever sees the text. -/

namespace LeanTex.Core.Bib

/-- The file a bibliography (or data) request names: `.bib` is the one
extension, appended when the source does not spell it. Every fulfiller of
the request — the driver's `resolveBibliography`/`resolveData`, the test
harness's `elabFixture` — resolves through this def, so what the tests
fulfil cannot drift from what the driver fulfils. -/
def sourceName (src : String) : String :=
  if src.endsWith ".bib" then src else src ++ ".bib"

/-- One parsed entry: `@kind{key, fields}`. Kind and field names are
lowercased (BibTeX is case-insensitive there, btxdoc §Odds and Ends); the
key keeps its case (keys are case-sensitive in practice: `\cite` must spell
the key as the `.bib` does). Field values are stored raw — brace groups,
TeX accents and all — because case protection (`{DNA}`) must survive until
the style's own case-folding reads it. -/
structure Entry where
  kind : String
  key : String
  fields : Array (String × String)
  pos : Pos
  deriving Repr, BEq

instance : Inhabited Entry :=
  ⟨{ kind := ""
     key := ""
     fields := #[]
     pos := {} }⟩

def Entry.field? (e : Entry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

/-- The parse keeps what it can: a malformed entry is recorded with its
position and the parse resynchronises at the next `@`, so one broken entry
never takes the bibliography down (W0352's contract). -/
structure Parsed where
  entries : Array Entry := #[]
  errors : Array (Pos × String) := #[]
  deriving Repr, Inhabited

private def Parsed.err (out : Parsed) (p : Pos) (msg : String) : Parsed :=
  { out with errors := out.errors.push (p, msg) }

private def Parsed.entry (out : Parsed) (e : Entry) : Parsed :=
  { out with entries := out.entries.push e }

/-- The month macro keys every BibTeX style file defines (plain.bst MACRO
{jan}–{dec}); a `.bib` may use them without declaring them. The rendered
names come from the document's locale (babel ini `months.wide`). -/
def monthKeys : Array String :=
  #["jan", "feb", "mar", "apr", "may", "jun",
    "jul", "aug", "sep", "oct", "nov", "dec"]

def monthMacros (months : Array String) : Array (String × String) :=
  monthKeys.zip months

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Line and column of an index, counted on demand: positions are read only
at entry starts and errors, both rare, so the parse never threads one. -/
private def posOf (cs : Array Char) (i : Nat) : Pos := Id.run do
  let mut line := 1
  let mut col := 1
  for j in [0:min i cs.size] do
    if h : j < cs.size then
      if cs[j] == '\n' then
        line := line + 1
        col := 1
      else
        col := col + 1
  return ⟨line, col⟩

private def skipWs (cs : Array Char) (start : Nat) : Nat := Id.run do
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if isWs cs[j] then j := j + 1 else break
    else break
  return j

/-- The characters of an entry-type or field name: letters and digits plus
the punctuation BibTeX allows in identifiers. -/
private def identChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '+'

private def readWhile (cs : Array Char) (start : Nat) (p : Char → Bool) :
    String × Nat := Id.run do
  let mut j := start
  let mut out := ""
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if p cs[j] then
        out := out.push cs[j]
        j := j + 1
      else break
    else break
  return (out, j)

/-- A cite key: everything up to a comma, whitespace, or a delimiter. -/
private def keyChar (c : Char) : Bool :=
  !isWs c && c != ',' && c != '{' && c != '}' && c != '(' && c != ')' && c != '"'

/-- A `{…}`-balanced group's content, `i` at the opening brace: the content
without the outer braces and the index past the closer, or `none` when the
file ends first. -/
private def readBraced (cs : Array Char) (start : Nat) : Option (String × Nat) := Id.run do
  let mut depth := 0
  let mut out := ""
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      let c := cs[j]
      if c == '{' then
        if depth > 0 then out := out.push c
        depth := depth + 1
        j := j + 1
      else if c == '}' then
        depth := depth - 1
        j := j + 1
        if depth == 0 then return some (out, j)
        out := out.push c
      else
        out := out.push c
        j := j + 1
    else break
  return none

/-- A `"…"` string's content, `i` at the opening quote: braces protect an
inner quote (btxdoc: `"the {"}J{"} spelling"`), so the closer is the first
quote at brace depth zero. -/
private def readQuoted (cs : Array Char) (start : Nat) : Option (String × Nat) := Id.run do
  let mut depth := 0
  let mut out := ""
  let mut j := start + 1
  for _ in [start:cs.size] do
    if h : j < cs.size then
      let c := cs[j]
      if c == '"' && depth == 0 then
        return some (out, j + 1)
      if c == '{' then depth := depth + 1
      if c == '}' then depth := depth - 1
      out := out.push c
      j := j + 1
    else break
  return none

/-- One `#`-concatenation part: a braced group, a quoted string, a bare
number, or a macro name resolved against the `@string` store (an unknown
macro keeps its name as text — visible, never silently empty). -/
private def readValuePart (cs : Array Char) (start : Nat)
    (macros : Array (String × String)) : Option (String × Nat) := Id.run do
  if h : start < cs.size then
    let c := cs[start]
    if c == '{' then return readBraced cs start
    if c == '"' then return readQuoted cs start
    if c.isDigit then
      let (n, j) := readWhile cs start Char.isDigit
      return some (n, j)
    if identChar c then
      let (name, j) := readWhile cs start identChar
      let v := ((macros.find? (·.1 == name.toLower)).map (·.2)).getD name
      return some (v, j)
    return none
  return none

/-- A field value: parts joined by `#`. -/
private def readValue (cs : Array Char) (start : Nat)
    (macros : Array (String × String)) : Option (String × Nat) := Id.run do
  match readValuePart cs start macros with
  | none => return none
  | some (v, j0) =>
    let mut out := v
    let mut j := skipWs cs j0
    for _ in [j0:cs.size] do
      if h : j < cs.size then
        if cs[j] == '#' then
          let k := skipWs cs (j + 1)
          match readValuePart cs k macros with
          | some (v', j') =>
            out := out ++ v'
            j := skipWs cs j'
          | none => return some (out, j)
        else break
      else break
    return some (out, j)

/-- The fields of one entry body, `i` past the key's comma: `name = value`
pairs to the closing delimiter. Returns the fields and the index past the
closer, or an error message with its index. -/
private def readFields (cs : Array Char) (start : Nat) (closer : Char)
    (macros : Array (String × String)) :
    Except (Nat × String) (Array (String × String) × Nat) := Id.run do
  let mut fields : Array (String × String) := #[]
  let mut j := skipWs cs start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if cs[j] == closer then
        return .ok (fields, j + 1)
      let (name, j1) := readWhile cs j identChar
      if name.isEmpty then
        return .error (j, s!"expected a field name or '{closer}'")
      let j2 := skipWs cs j1
      if h2 : j2 < cs.size then
        unless cs[j2] == '=' do
          return .error (j2, s!"expected '=' after '{name}'")
      else
        return .error (j2, "the file ends inside an entry")
      match readValue cs (skipWs cs (j2 + 1)) macros with
      | none => return .error (j2 + 1, s!"unreadable value for '{name}'")
      | some (v, j3) =>
        fields := fields.push (name.toLower, v)
        let j4 := skipWs cs j3
        if h4 : j4 < cs.size then
          if cs[j4] == ',' then
            j := skipWs cs (j4 + 1)
          else if cs[j4] == closer then
            return .ok (fields, j4 + 1)
          else
            return .error (j4, s!"expected ',' or '{closer}' after a field")
        else
          return .error (j4, "the file ends inside an entry")
    else
      return .error (j, "the file ends inside an entry")
  return .error (j, "the file ends inside an entry")

/-- The index of the next `@` at or after `start`: where the parse
resynchronises after a malformed entry, so the rest of the file is kept. -/
private def nextAt (cs : Array Char) (start : Nat) : Nat := Id.run do
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if cs[j] == '@' then return j
      j := j + 1
    else break
  return cs.size

/-- Parse a `.bib` file's text. Total by construction: every loop is bounded
by the input length and the cursor only moves forward. Everything outside
`@…{…}` entries is comment text, as BibTeX defines it; `@comment` and
`@preamble` are consumed and dropped; `@string` feeds the macro store the
later values read. A malformed entry is recorded at its position and
skipped, and the parse continues at the next `@` — one bad entry costs
itself, never the file (W0352). -/
def parse (src : String)
    (macros0 : Array (String × String) := monthMacros Locale.en.months) :
    Parsed := Id.run do
  let cs := src.toList.toArray
  let mut out : Parsed := {}
  let mut macros := macros0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    i := nextAt cs i
    if i ≥ cs.size then break
    let atPos := i
    i := i + 1
    let (kind, j1) := readWhile cs i (·.isAlpha)
    let kind := kind.toLower
    if kind.isEmpty then
      out := out.err (posOf cs atPos) "'@' opens no entry type"
      continue
    let j2 := skipWs cs j1
    if kind == "comment" then
      -- BibTeX treats @comment as ordinary inter-entry text: nothing to read.
      i := j1
      continue
    let opener := if h : j2 < cs.size then cs[j2] else ' '
    if opener != '{' && opener != '(' then
      out := out.err (posOf cs atPos) s!"'@{kind}' opens with no '\{' or '('"
      i := j2
      continue
    let closer := if opener == '(' then ')' else '}'
    if kind == "preamble" then
      match readBraced cs j2 with
      | some (_, j) => i := j
      | none =>
        out := out.err (posOf cs atPos) "'@preamble' never closes"
        i := cs.size
      continue
    if kind == "string" then
      match readFields cs (skipWs cs (j2 + 1)) closer macros with
      | .ok (defs, j) =>
        for (n, v) in defs do
          macros := macros.push (n, v)
        i := j
      | .error (j, msg) =>
        out := out.err (posOf cs j) s!"@string: {msg}"
        i := j
      continue
    -- An ordinary entry: @kind{key, fields}.
    let j3 := skipWs cs (j2 + 1)
    let (key, j4) := readWhile cs j3 keyChar
    if key.isEmpty then
      out := out.err (posOf cs j3) s!"'@{kind}' names no key"
      i := j3
      continue
    let j5 := skipWs cs j4
    let sep := if h : j5 < cs.size then cs[j5] else ' '
    if sep == closer then
      out := out.entry
        { kind
          key
          fields := #[]
          pos := posOf cs atPos }
      i := j5 + 1
      continue
    if sep != ',' then
      out := out.err (posOf cs j5) s!"expected ',' after the key '{key}'"
      i := j5
      continue
    match readFields cs (j5 + 1) closer macros with
    | .ok (fields, j) =>
      out := out.entry
        { kind
          key
          fields
          pos := posOf cs atPos }
      i := j
    | .error (j, msg) =>
      out := out.err (posOf cs j) s!"in '{key}': {msg}"
      i := j
  return out

/-! ## Value text

A stored value is TeX-flavoured: brace groups, `\'{e}` accents, `~` ties,
`--` dashes. `text` renders it as the plain scalars the IR carries. -/

/-- Accent commands over a base letter, precomposed (the NFC forms the
UTF-8 layer already accepts): TeX's `\'e`, `\"{o}`, `\c{c}` spellings.
The closed set covers the Latin-1 letters; a pair outside it keeps its
base letter, so a name never loses a character to an accent the table
does not know. -/
def accentTable : Array (Char × Char × Char) :=
  #[('\'', 'a', 'á'), ('\'', 'e', 'é'), ('\'', 'i', 'í'), ('\'', 'o', 'ó'),
    ('\'', 'u', 'ú'), ('\'', 'y', 'ý'), ('\'', 'c', 'ć'), ('\'', 'n', 'ń'),
    ('\'', 'A', 'Á'), ('\'', 'E', 'É'), ('\'', 'I', 'Í'), ('\'', 'O', 'Ó'),
    ('\'', 'U', 'Ú'),
    ('`', 'a', 'à'), ('`', 'e', 'è'), ('`', 'i', 'ì'), ('`', 'o', 'ò'),
    ('`', 'u', 'ù'),
    ('`', 'A', 'À'), ('`', 'E', 'È'), ('`', 'O', 'Ò'), ('`', 'U', 'Ù'),
    ('"', 'a', 'ä'), ('"', 'e', 'ë'), ('"', 'i', 'ï'), ('"', 'o', 'ö'),
    ('"', 'u', 'ü'), ('"', 'y', 'ÿ'),
    ('"', 'A', 'Ä'), ('"', 'O', 'Ö'), ('"', 'U', 'Ü'),
    ('^', 'a', 'â'), ('^', 'e', 'ê'), ('^', 'i', 'î'), ('^', 'o', 'ô'),
    ('^', 'u', 'û'),
    ('~', 'a', 'ã'), ('~', 'n', 'ñ'), ('~', 'o', 'õ'),
    ('~', 'A', 'Ã'), ('~', 'N', 'Ñ'), ('~', 'O', 'Õ'),
    ('c', 'c', 'ç'), ('c', 'C', 'Ç')]

/-- Word commands that are one character. -/
def charCommands : Array (String × String) :=
  #[("ss", "ß"), ("o", "ø"), ("O", "Ø"), ("ae", "æ"), ("AE", "Æ"),
    ("aa", "å"), ("AA", "Å"), ("l", "ł"), ("L", "Ł"), ("i", "ı")]

def accentOf (mark base : Char) : Char :=
  ((accentTable.find? fun (m, b, _) => m == mark && b == base).map (·.2.2)).getD base

private def isAccentMark (c : Char) : Bool :=
  c == '\'' || c == '`' || c == '"' || c == '^' || c == '~'

/-- The plain text of a stored value: braces dropped, `\'{e}`-style accents
composed, one-character word commands replaced, `~` a space (the tie is not
modelled — stated, not hidden), `---`/`--` the em and en dash, whitespace
runs one space. An unknown `\command` keeps its name as text, so nothing a
value spells goes silently missing. Not handled, deliberately: math (`$…$`
stays literal) and accents outside `accentTable`. -/
def text (v : String) : String := Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut lastWs := true
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if isWs c then
        unless lastWs do out := out.push ' '
        lastWs := true
        i := i + 1
      else if c == '{' || c == '}' then
        i := i + 1
      else if c == '~' then
        unless lastWs do out := out.push ' '
        lastWs := true
        i := i + 1
      else if c == '-' then
        lastWs := false
        if h2 : i + 2 < cs.size then
          if cs[i + 1] == '-' && cs[i + 2] == '-' then
            out := out.push '—'
            i := i + 3
            continue
        if h1 : i + 1 < cs.size then
          if cs[i + 1] == '-' then
            out := out.push '–'
            i := i + 2
            continue
        out := out.push '-'
        i := i + 1
      else if c == '\\' then
        lastWs := false
        if h1 : i + 1 < cs.size then
          let m := cs[i + 1]
          if isAccentMark m then
            -- \'e, \'{e}: the base letter is next, possibly braced.
            let (base, j) :=
              if h2 : i + 2 < cs.size then
                if cs[i + 2] == '{' then
                  if h3 : i + 3 < cs.size then (some cs[i + 3], i + 4)
                  else (none, i + 3)
                else (some cs[i + 2], i + 3)
              else (none, i + 2)
            match base with
            | some b => out := out.push (accentOf m b)
            | none => pure ()
            i := j
          else if m.isAlpha then
            let (name, j) := readWhile cs (i + 1) Char.isAlpha
            match charCommands.find? (·.1 == name) with
            | some (_, r) =>
              out := out ++ r
              i := skipWs cs j
            | none =>
              if name == "c" then
                -- \c{c}: the cedilla takes its letter braced or bare.
                let j1 := skipWs cs j
                let (base, j2) :=
                  if hb : j1 < cs.size then
                    if cs[j1] == '{' then
                      if hb2 : j1 + 1 < cs.size then (some cs[j1 + 1], j1 + 3)
                      else (none, j1 + 2)
                    else (some cs[j1], j1 + 1)
                  else (none, j1)
                match base with
                | some b => out := out.push (accentOf 'c' b)
                | none => pure ()
                i := j2
              else
                -- Unknown command: its name stays visible as text.
                out := out ++ name
                i := j
          else
            -- \&, \%, \_ …: the escaped character itself.
            out := out.push m
            i := i + 2
        else
          i := i + 1
      else
        lastWs := false
        out := out.push c
        i := i + 1
    else break
  return out.trimAscii.toString

/-- BibTeX's `"t" change.case$` (btxhak §change.case$): the sentence case
plainnat's `format.title` applies — everything lowercased except the first
character, a character following `: `, and anything brace-protected. -/
def sentenceCase (v : String) : String := Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut depth := 0
  let mut keepNext := true
  for i in [0:cs.size] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '{' then
        depth := depth + 1
        out := out.push c
      else if c == '}' then
        depth := depth - 1
        out := out.push c
      else if depth > 0 then
        out := out.push c
      else if keepNext then
        out := out.push c
        if !isWs c then keepNext := false
      else
        if c == ':' then
          if h2 : i + 1 < cs.size then
            if isWs cs[i + 1] then keepNext := true
        out := out.push c.toLower
  return out

/-! ## Names

BibTeX names (btxdoc §Names): `First von Last`, `von Last, First`, or
`von Last, Jr, First`, joined by ` and `, with `others` closing an
elided list. -/

structure Name where
  first : String := ""
  von : String := ""
  last : String := ""
  jr : String := ""
  deriving Repr, BEq, Inhabited

/-- Split a value on a depth-0 separator word (` and `, `,`): brace groups
are opaque, as BibTeX reads them. -/
private def splitTop (v : String) (isSep : Array Char → Nat → Option Nat) :
    Array String := Id.run do
  let cs := v.toList.toArray
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '{' then
        depth := depth + 1
        cur := cur.push c
        i := i + 1
      else if c == '}' then
        depth := depth - 1
        cur := cur.push c
        i := i + 1
      else if depth == 0 then
        match isSep cs i with
        | some j =>
          out := out.push cur
          cur := ""
          i := j
        | none =>
          cur := cur.push c
          i := i + 1
      else
        cur := cur.push c
        i := i + 1
    else break
  return out.push cur

private def andAt (cs : Array Char) (i : Nat) : Option Nat := Id.run do
  -- ` and ` as a lone word: whitespace, a·n·d in either case, whitespace.
  if h : i < cs.size then
    unless isWs cs[i] do return none
  else return none
  let j := skipWs cs i
  let la (k : Nat) (want : Char) : Bool :=
    if h : k < cs.size then cs[k].toLower == want else false
  if la j 'a' && la (j + 1) 'n' && la (j + 2) 'd' then
    if h : j + 3 < cs.size then
      if isWs cs[j + 3] then return some (skipWs cs (j + 3))
  return none

private def commaAt (cs : Array Char) (i : Nat) : Option Nat :=
  if h : i < cs.size then
    if cs[i] == ',' then some (i + 1) else none
  else none

/-- The names of an `author` field, in order, raw: split on the word `and`
at brace depth 0. -/
def splitNames (v : String) : Array String :=
  (splitTop v andAt).map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- Does a name token start lowercase? A brace-opening token counts as
caseless and attaches to the Last part, which is where `{van den Berg}`
wants to be. -/
private def startsLower (tok : String) : Bool :=
  match tok.toList.find? Char.isAlpha with
  | some c => c.isLower
  | none => false

private def joinSp (toks : List String) : String :=
  String.intercalate " " toks

/-- Split `von Last`: the von part is the leading run of lowercase-starting
tokens, and Last keeps at least the final token. -/
private def vonLast (toks : List String) : String × String := Id.run do
  let mut von : List String := []
  let mut rest := toks
  for _ in [0:toks.length] do
    match rest with
    | t :: (r₁ :: rs) =>
      if startsLower t then
        von := von ++ [t]
        rest := r₁ :: rs
      else break
    | _ => break
  return (joinSp von, joinSp rest)

/-- One name, split into BibTeX's four parts (btxdoc §Names). The comma
forms are exact; the `First von Last` form takes First as the longest
prefix of uppercase-starting tokens that leaves a Last. Not handled,
stated: pathological mixed-case von parts (`Maria de la Cruz Perez` keeps
`Cruz Perez` whole) and case analysis of brace-opening tokens beyond
"caseless attaches to Last". -/
def parseName (s : String) : Name := Id.run do
  let sections := (splitTop s commaAt).map (·.trimAscii.toString)
  let toks (t : String) : List String :=
    ((splitTop t (fun cs i => Id.run do
      if h : i < cs.size then
        if isWs cs[i] then return some (skipWs cs i)
      return none)).map (·.trimAscii.toString)).toList.filter (!·.isEmpty)
  if sections.size ≥ 2 then
    let (von, last) := vonLast (toks (sections[0]?.getD ""))
    let (jr, first) :=
      if sections.size ≥ 3 then
        (sections[1]?.getD "", sections[2]?.getD "")
      else ("", sections[1]?.getD "")
    return { first := first.trimAscii.toString, von, last, jr }
  let ts := toks s
  let mut first : List String := []
  let mut rest := ts
  for _ in [0:ts.length] do
    match rest with
    | t :: (r₁ :: rs) =>
      if !startsLower t then
        first := first ++ [t]
        rest := r₁ :: rs
      else break
    | _ => break
  let (von, last) := vonLast rest
  return { first := joinSp first, von, last }

/-- `{ff }{vv }{ll}{, jj}`: the full-name order plainnat's `format.names`
prints in the reference list (plainnat.bst FUNCTION {format.names}). -/
def Name.full (n : Name) : String :=
  let parts := [n.first, n.von, n.last].filter (!·.isEmpty)
  joinSp parts ++ (if n.jr.isEmpty then "" else s!", {n.jr}")

/-- `{vv~}{ll}`: the short form `\citet` and the label use. -/
def Name.short (n : Name) : String :=
  joinSp ([n.von, n.last].filter (!·.isEmpty))

/-- plain.bst's name join (FUNCTION {format.names}): two names join with
` and `, more with `, ` and a final `, and `; a closing `others` elides to
`et al.` — appended directly after one name, after a comma otherwise. -/
def andJoin (ns : List String) : String :=
  match ns.reverse with
  | [] => ""
  | [n] => n
  | last :: init =>
    let init := init.reverse
    if last == "others" then
      if init.length == 1 then joinSp init ++ " et al."
      else String.intercalate ", " init ++ ", et al."
    else if init.length == 1 then s!"{joinSp init} and {last}"
    else s!"{String.intercalate ", " init}, and {last}"

/-- The label names `\citet` prints (plainnat.bst FUNCTION
{format.lab.names}): one author's last name; two joined with ` and `;
more, or an elided list, take `et al.`. -/
def labelNames (v : String) : String :=
  let ns := splitNames v
  let short (s : String) : String := text (parseName s).short
  match ns.toList with
  | [] => ""
  | [a] => short a
  | [a, b] => if b == "others" then s!"{short a} et al." else s!"{short a} and {short b}"
  | a :: _ => s!"{short a} et al."

end LeanTex.Core.Bib
