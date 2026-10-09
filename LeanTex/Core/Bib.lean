module

public import LeanTex.Core.Diag
public import LeanTex.Core.LocaleData
public import LeanTex.Core.BibAccent
public import Std.Data.HashMap
import LeanTex.Core.Nfc

/-! BibTeX bibliography files, parsed in the pure core. The grammar is the
one btxdoc.tex and "Tame the BeaST" §2 document: `@type{key, field = value,
…}` entries whose values are `{…}`-balanced groups, `"…"` strings, or bare
numbers and `@string` macro names, concatenated with `#`; `@comment` is
skipped and `@preamble` kept; everything between entries is comment text
by definition. Reading the file is the driver's effect (`Ir.bibRefs`, the
`imageRefs` shape); this module only ever sees the text. -/

namespace LeanTex.Core.Bib

/-- The file a bibliography (or data) request names: `.bib` is the one
extension, appended when the source does not spell it. Every fulfiller of
the request — the driver's `resolveBibliography`/`resolveData`, the test
harness's `elabFixture` — resolves through this def, so what the tests
fulfil cannot drift from what the driver fulfils. -/
public def sourceName (src : String) : String :=
  if src.endsWith ".bib" then src else src ++ ".bib"

/-- One parsed entry: `@kind{key, fields}`. Kind and field names are
lowercased (BibTeX is case-insensitive there, btxdoc §Odds and Ends); the
key keeps its case (keys are case-sensitive in practice: `\cite` must spell
the key as the `.bib` does). Field values are stored raw — brace groups,
TeX accents and all — because case protection (`{DNA}`) must survive until
the style's own case-folding reads it. -/
public structure Entry where
  kind : String
  key : String
  fields : Array (String × String)
  pos : Pos
  deriving Repr, BEq

public instance : Inhabited Entry :=
  ⟨{ kind := ""
     key := ""
     fields := #[]
     pos := {} }⟩

@[expose] public def Entry.field? (e : Entry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

/-- The parse keeps what it can: a malformed entry is recorded with its
position and the parse resynchronises at the next `@`, so one broken entry
never takes the bibliography down (W0352's contract). -/
public structure Parsed where
  entries : Array Entry := #[]
  errors : Array (Pos × String) := #[]
  /-- The `@preamble`s' texts, in order: what the list's fields are typeset
  under (`Bib.preambleMacros`). -/
  preambles : Array String := #[]
  /-- The `@string` store after the file: what the next file of the same
  bibliography reads its values against, as BibTeX and biber read every
  file of a list in turn into one store. -/
  macros : Std.HashMap String String := {}
  /-- Each value part naming a macro no `@string` has defined by then: the
  entry's key and the name, which the value keeps as its text. -/
  undefined : Array (String × String) := #[]
  deriving Inhabited

private def Parsed.err (out : Parsed) (p : Pos) (msg : String) : Parsed :=
  { out with errors := out.errors.push (p, msg) }

private def Parsed.entry (out : Parsed) (e : Entry) : Parsed :=
  { out with entries := out.entries.push e }

/-- The month macro keys every BibTeX style file defines (plain.bst MACRO
{jan}–{dec}); a `.bib` may use them without declaring them. The rendered
names come from the document's locale (babel ini `months.wide`). -/
private def monthKeys : Array String :=
  #["jan", "feb", "mar", "apr", "may", "jun",
    "jul", "aug", "sep", "oct", "nov", "dec"]

public def monthMacros (months : Array String) : Std.HashMap String String :=
  (monthKeys.zip months).foldl (fun m (k, v) => m.insert k v) {}

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Line and column of index `i`, counted forward from a position `p` already
known at index `start ≤ i`: the parse asks for entry starts in increasing
order and resumes from the last one, so it pays for each character once —
counting from the file's start at every entry was quadratic in the file. -/
private def posFrom (cs : Array Char) (start : Nat) (p : Pos) (i : Nat) : Pos := Id.run do
  let mut line := p.line
  let mut col := p.col
  for j in [start:min i cs.size] do
    if h : j < cs.size then
      if cs[j] == '\n' then
        line := line + 1
        col := 1
      else
        col := col + 1
  return { p with line, col }

/-- Line and column of an index, counted from the file's start: what an
error position reads, errors being rare. -/
private def posOf (cs : Array Char) (i : Nat) : Pos := posFrom cs 0 { line := 1, col := 1 } i

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
number, or a macro name resolved against the `@string` store, case
insensitively. An unknown macro keeps its name as text — visible, never
silently empty as BibTeX and biber leave it — and is returned so the parse
can name it. -/
private def readValuePart (cs : Array Char) (start : Nat)
    (macros : Std.HashMap String String) : Option (String × Nat × Option String) := Id.run do
  if h : start < cs.size then
    let c := cs[start]
    if c == '{' then return (readBraced cs start).map fun (v, j) => (v, j, none)
    if c == '"' then return (readQuoted cs start).map fun (v, j) => (v, j, none)
    if c.isDigit then
      let (n, j) := readWhile cs start Char.isDigit
      return some (n, j, none)
    if identChar c then
      let (name, j) := readWhile cs start identChar
      return match macros.get? name.toLower with
        | some v => some (v, j, none)
        | none => some (name, j, some name)
    return none
  return none

/-- A field value: parts joined by `#`, with the macro names among them no
`@string` defines. -/
private def readValue (cs : Array Char) (start : Nat)
    (macros : Std.HashMap String String) : Option (String × Nat × Array String) := Id.run do
  match readValuePart cs start macros with
  | none => return none
  | some (v, j0, u0) =>
    let mut out := v
    let mut undef : Array String := u0.toArray
    let mut j := skipWs cs j0
    for _ in [j0:cs.size] do
      if h : j < cs.size then
        if cs[j] == '#' then
          let k := skipWs cs (j + 1)
          match readValuePart cs k macros with
          | some (v', j', u') =>
            out := out ++ v'
            undef := undef ++ u'.toArray
            j := skipWs cs j'
          | none => return some (out, j, undef)
        else break
      else break
    return some (out, j, undef)

/-- The fields of one entry body, `i` past the key's comma: `name = value`
pairs to the closing delimiter. Returns the fields, the macro names their
values use that no `@string` defines, and the index past the closer, or an
error message with its index. -/
private def readFields (cs : Array Char) (start : Nat) (closer : Char)
    (macros : Std.HashMap String String) :
    Except (Nat × String) (Array (String × String) × Array String × Nat) := Id.run do
  let mut fields : Array (String × String) := #[]
  let mut undef : Array String := #[]
  let mut j := skipWs cs start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if cs[j] == closer then
        return .ok (fields, undef, j + 1)
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
      | some (v, j3, u) =>
        fields := fields.push (name.toLower, v)
        undef := undef ++ u
        let j4 := skipWs cs j3
        if h4 : j4 < cs.size then
          if cs[j4] == ',' then
            j := skipWs cs (j4 + 1)
          else if cs[j4] == closer then
            return .ok (fields, undef, j4 + 1)
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
`@…{…}` entries is comment text, as BibTeX defines it; `@comment` is
consumed and dropped — under `biber`, its delimited body with it, as biber's
reader (btparse) takes the block for a comment where BibTeX reads on, an
entry inside it included — `@preamble` kept as its text (`Parsed.preambles`);
`@string` feeds the macro store the later values read. A malformed entry is recorded at its position and
skipped, and the parse continues at the next `@` — one bad entry costs
itself, never the file (W0352). -/
public def parse (src : String)
    (macros0 : Std.HashMap String String := monthMacros Locale.en.months)
    (biber : Bool := false) : Parsed := Id.run do
  let cs := src.toList.toArray
  let mut out : Parsed := {}
  let mut macros := macros0
  let mut i := 0
  let mut mark : Nat × Pos := (0, { line := 1, col := 1 })
  for _ in [0:cs.size + 1] do
    i := nextAt cs i
    if i ≥ cs.size then break
    let atPos := i
    let atLine := posFrom cs mark.1 mark.2 atPos
    mark := (atPos, atLine)
    i := i + 1
    let (kind, j1) := readWhile cs i (·.isAlpha)
    let kind := kind.toLower
    if kind.isEmpty then
      out := out.err atLine "'@' opens no entry type"
      continue
    let j2 := skipWs cs j1
    if kind == "comment" then
      -- BibTeX treats @comment as ordinary inter-entry text: nothing to read.
      i := j1
      if biber then
        match cs[j2]? with
        | some '{' =>
          match readBraced cs j2 with
          | some (_, j) => i := j
          | none => i := cs.size
        | some '(' => i := ((cs.extract (j2 + 1) cs.size).findIdx? (· == ')')).elim cs.size (j2 + 2 + ·)
        | _ => pure ()
      continue
    let opener := if h : j2 < cs.size then cs[j2] else ' '
    if opener != '{' && opener != '(' then
      out := out.err atLine s!"'@{kind}' opens with no '\{' or '('"
      i := j2
      continue
    let closer := if opener == '(' then ')' else '}'
    if kind == "preamble" then
      -- one value, its parts joined by `#` as a field's are
      let k := skipWs cs (j2 + 1)
      match readValue cs k macros with
      | some (v, j3, _) =>
        let j4 := skipWs cs j3
        if cs[j4]? == some closer then
          out := { out with preambles := out.preambles.push v }
          i := j4 + 1
        else
          out := out.err atLine "'@preamble' holds more than one value"
          i := j4
      | none =>
        match readBraced cs j2 with
        | some (_, j) => i := j
        | none =>
          out := out.err atLine "'@preamble' never closes"
          i := cs.size
      continue
    if kind == "string" then
      match readFields cs (skipWs cs (j2 + 1)) closer macros with
      | .ok (defs, _, j) =>
        for (n, v) in defs do
          macros := macros.insert n v
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
          pos := atLine }
      i := j5 + 1
      continue
    if sep != ',' then
      out := out.err (posOf cs j5) s!"expected ',' after the key '{key}'"
      i := j5
      continue
    match readFields cs (j5 + 1) closer macros with
    | .ok (fields, undef, j) =>
      out := out.entry
        { kind
          key
          fields
          pos := atLine }
      out := { out with undefined := undef.foldl (fun us n => us.push (key, n)) out.undefined }
      i := j
    | .error (j, msg) =>
      out := out.err (posOf cs j) s!"in '{key}': {msg}"
      i := j
  return { out with macros }

/-! ## Value text

A stored value is TeX-flavoured: brace groups, `\'{e}` accents, `~` ties,
`--` dashes. `text` renders it as the plain scalars the IR carries. -/

private def isAccentMark (c : Char) : Bool :=
  c == '\'' || c == '`' || c == '"' || c == '^' || c == '~'

/-- `text` without the trim: a span of a value that math interrupts keeps the
space it opens or closes with — `lead` keeps a leading one too. -/
public def textSpan (v : String) (lead : Bool := false) (keepUnknown : Bool := true) : String :=
    Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut lastWs := !lead
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
                -- Unknown command: its name stays visible as text, unless
                -- the reading drops it.
                if keepUnknown then out := out ++ name
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
  return out

/-- The plain text of a stored value: braces dropped, `\'{e}`-style accents
composed, one-character word commands replaced, `~` a space (the tie is not
modelled — stated, not hidden), `---`/`--` the em and en dash, whitespace
runs one space. An unknown `\command` keeps its name as text, so nothing a
value spells goes silently missing. Math and TeX's quote ligatures are the
reference list's to set (`BibText.fieldInlines`, or the document's own
elaborator where a build reads the fields, `Bib.FieldDoor.read`); accents
outside `accentTable` keep their base letter. -/
public def text (v : String) : String := (textSpan v).trimAscii.toString

/-- A value as biber's sort strings read it (Biber::Utils
`normalise_string_sort`): `text`'s reading, every command's name dropped —
biber decodes the accents and symbols it knows when it reads the file, then
removes each remaining `\\[A-Za-z]+` and every brace. -/
public def sortPlainText (v : String) : String := (textSpan v (keepUnknown := false)).trimAscii.toString

/-- BibTeX's `change.case$` lowering a value (bibtex.web's change-case
procedure): `"t"` (`title`) is the sentence case plainnat's `format.title`
applies, `"l"` lowers everything. At brace depth zero a letter lowercases
unless, under `"t"`, it is the value's first character or follows a colon
and white space; a closing brace forgets the colon. A brace group stays as
written, except a special character — a group opening `{\` — which
lowercases its letters outside its control words and turns the five
foreign-letter words (`\AA`, `\AE`, `\L`, `\O`, `\OE`) into their
lowercase words, unless it stands where a kept letter would. Every letter
changes by its Unicode case (`Nfc.toLower`) — a departure from bibtex
0.99, which reads UTF-8 as bytes and changes only ASCII, so `Ärger` kept
its capital there where `Error` lost its own. The value is read as
BibTeX's `.bib` reader leaves it: surrounding white space trimmed. -/
public def lowerCase (title : Bool) (v : String) : String := Id.run do
  let cs := v.trimAscii.toString.toList.toArray
  let mut out := ""
  let mut depth : Nat := 0
  let mut prevColon := false
  let mut special := false
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      let kept := title && (i == 0 || (prevColon && i > 0 && isWs (cs[i - 1]?.getD 'x')))
      if c == '{' then
        if depth == 0 then
          special := !kept && cs[i + 1]? == some '\\'
        depth := depth + 1
        out := out.push c
        i := i + 1
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then special := false
        prevColon := false
        out := out.push c
        i := i + 1
      else if depth == 0 then
        out := out.push (if kept then c else Nfc.toLower c)
        if c == ':' then prevColon := true
        else if !isWs c then prevColon := false
        i := i + 1
      else if special && c == '\\' then
        let (word, j) := readWhile cs (i + 1) Char.isAlpha
        let word := if ["AA", "AE", "L", "O", "OE"].contains word then word.toLower else word
        out := out.push '\\' ++ word
        i := if word.isEmpty then i + 1 else j
      else
        out := out.push (if special then Nfc.toLower c else c)
        i := i + 1
    else break
  return out

/-- bibtex.web's foreign-letter control words, lowercase ones first: what a
special character's case and its purified letters are read from. -/
private def lowerForeign : List String := ["i", "j", "oe", "ae", "aa", "o", "l", "ss"]
private def upperForeign : List String := ["OE", "AE", "AA", "O", "L"]

/-- BibTeX's `purify$` (bibtex.web): what a sort key or a label reads of a
value — ASCII letters and digits kept, white space, hyphens and ties as one
space each, everything else dropped; a special character `{\\…}` keeps
its own letters, and a foreign letter its control word's (`{\\ss}` is
`ss`, `{\\o}` is `o`, `{\\OE}` is `OE`; `{\\aa}` keeps one `a`). A
letter outside ASCII, which bibtex reads as bytes, is kept as the letter it
is. -/
public def purify (v : String) : String := Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut depth : Nat := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if isWs c || c == '-' || c == '~' then
        out := out.push ' '
        i := i + 1
      else if c.isAlphanum || (c.toNat > 127 && Nfc.isLetter c) then
        out := out.push c
        i := i + 1
      else if c == '{' then
        depth := depth + 1
        if depth == 1 && cs[i + 1]? == some '\\' then
          -- a special character: read to its closing brace
          let mut level : Nat := 1
          let mut k := i + 1
          for _ in [i + 1:cs.size] do
            if hk : k < cs.size then
              if level == 0 then break
              let d := cs[k]
              if d == '\\' then
                let (word, j) := readWhile cs (k + 1) Char.isAlpha
                if (lowerForeign ++ upperForeign).contains word then
                  out := out ++ (if ["oe", "OE", "ae", "AE", "ss"].contains word then word
                    else String.ofList (word.toList.take 1))
                k := if word.isEmpty then k + 1 else j
              else
                if d.isAlphanum || (d.toNat > 127 && Nfc.isLetter d) then out := out.push d
                else if d == '}' then level := level - 1
                else if d == '{' then level := level + 1
                k := k + 1
            else break
          depth := 0
          i := k
        else
          i := i + 1
      else
        if c == '}' && depth > 0 then depth := depth - 1
        i := i + 1
    else break
  return out

/-- `"t" change.case$`: the title's sentence case (`lowerCase`). -/
public def sentenceCase (v : String) : String := lowerCase true v

/-! ## Names

BibTeX names (btxdoc §Names): `First von Last`, `von Last, First`, or
`von Last, Jr, First`, joined by ` and `, with `others` closing an
elided list. -/

public structure Name where
  first : String := ""
  von : String := ""
  last : String := ""
  jr : String := ""
  /-- A per-name `useprefix` (biber's extended name format), over the
  option a document loads biblatex with. -/
  useprefix : Option Bool := none
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
public def splitNames (v : String) : Array String :=
  (splitTop v andAt).map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- The name parts biber's extended name format spells out (biblatex manual
§3.4). -/
private def xnameParts : List String := ["family", "given", "prefix", "suffix"]

/-- A name in biber's extended name format (Biber's parsename_x): `key=value`
items split at commas outside braces — the four name parts and a per-name
`useprefix`; explicit initials and the other per-name options read as
nothing — or `none` for a name in BibTeX's own format, which is any name no
part's key opens an item of with `=`. -/
public def parseNameX? (s : String) : Option Name := Id.run do
  let mut n : Name := {}
  let mut extended := false
  for item in splitTop s commaAt do
    match item.splitOn "=" with
    | k :: v :: rest =>
      let key := k.trimAscii.toString.toLower
      let value := ("=".intercalate (v :: rest)).trimAscii.toString
      if xnameParts.contains key || xnameParts.any (key == · ++ "-i") then extended := true
      if key == "family" then n := { n with last := value }
      else if key == "given" then n := { n with first := value }
      else if key == "prefix" then n := { n with von := value }
      else if key == "suffix" then n := { n with jr := value }
      else if key == "useprefix" then
        n := { n with useprefix := some (value == "true" || value == "1") }
    | _ => pure ()
  return if extended then some n else none

/-- One name's tokens as bibtex.web reads them (§"Break up the name into
tokens"): white space, a hyphen and a tie separate tokens at brace depth 0,
a brace group belongs to the token it opens or continues, and a comma ends
the token before it and splits the name into its parts. Each token carries
the separator before it — the first separator after the previous token, as
bibtex records it — and the commas are the token counts where they stand.
bibtex reads a third comma as an error and goes on; here it ends its token
and splits nothing. -/
private def nameTokens (s : String) : Array (String × Char) × Array Nat := Id.run do
  let mut toks : Array (String × Char) := #[]
  let mut commas : Array Nat := #[]
  let mut cur := ""
  let mut inTok := false
  let mut sep : Char := ' '
  let mut depth : Nat := 0
  for c in s.toList do
    if depth > 0 then
      cur := cur.push c
      if c == '{' then depth := depth + 1
      else if c == '}' then depth := depth - 1
    else if c == '{' then
      inTok := true
      cur := cur.push c
      depth := 1
    else if c == '}' then
      pure ()
    else if c == ',' then
      if inTok then
        toks := toks.push (cur, sep)
        cur := ""
        inTok := false
      if commas.size < 2 then commas := commas.push toks.size
      sep := ','
    else if isWs c || c == '-' || c == '~' then
      if inTok then
        toks := toks.push (cur, sep)
        cur := ""
        inTok := false
        sep := if isWs c then ' ' else c
    else
      inTok := true
      cur := cur.push c
  if inTok then toks := toks.push (cur, sep)
  return (toks, commas)

/-- The case of a brace group's letters from index `start`, at brace level
`level` inside it: the first letter decides, and the group's end without
one is uppercase (not a von token). -/
private def groupLower (cs : Array Char) (start : Nat) : Bool := Id.run do
  let mut level : Nat := 1
  let mut k := start
  for _ in [start:cs.size] do
    if h : k < cs.size then
      if level == 0 then return false
      let d := cs[k]
      if Nfc.isLower d then return true
      if Nfc.isLetter d then return false
      if d == '}' then level := level - 1
      else if d == '{' then level := level + 1
      k := k + 1
    else break
  return false

/-- bibtex.web's `von_token_found`: a token is a von token when its first
letter at brace depth 0 is lowercase. A brace group that is no special
character is skipped whole; a special character — a group whose first
character is a backslash, `{\'e}` — answers for the token, by its
foreign-letter control word (`{\o}` is lowercase, `{\O}` uppercase) or
else by its first letter. A token with no letter is not a von token, which
is where `{Example Consortium}` and `{van den Berg}` stand: whole, in the
last name. A letter outside ASCII decides by its Unicode case, as biber
reads it — bibtex 0.99 reads UTF-8 as bytes and skips them, so it took
`Élodie` in `Élodie Durand` for a particle by its second letter; a letter
of a script without case is no particle. -/
public def vonToken (tok : String) : Bool := Id.run do
  let cs := tok.toList.toArray
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if Nfc.isLower c then return true
      if Nfc.isLetter c then return false
      if c == '{' then
        if i + 3 < cs.size && cs[i + 1]? == some '\\' then
          let (name, j) := readWhile cs (i + 2) Char.isAlpha
          if lowerForeign.contains name then return true
          if upperForeign.contains name then return false
          return groupLower cs j
        -- an ordinary group: skip it whole and read on after it
        let mut level : Nat := 1
        let mut k := i + 1
        for _ in [i + 1:cs.size] do
          if hk : k < cs.size then
            if level == 0 then break
            if cs[k] == '}' then level := level - 1
            else if cs[k] == '{' then level := level + 1
            k := k + 1
          else break
        i := k
      else
        i := i + 1
    else break
  return false

/-- Tokens `a` to `b` (exclusive) of a name, each after the separator it
was written with — a hyphen or a tie as written, a space for white space. -/
private def joinToks (toks : Array (String × Char)) (a b : Nat) : String := Id.run do
  let mut out := ""
  for k in [a:b] do
    match toks[k]? with
    | some (t, sep) =>
      unless k == a do
        out := out.push (if sep == '-' || sep == '~' then sep else ' ')
      out := out ++ t
    | none => pure ()
  return out

/-- The end of a von part that starts at `start` and stops before the last
name's last token `lastEnd - 1` (bibtex.web's
`von_name_ends_and_last_name_starts_stuff`): one past the last von token,
or `start` when there is none. -/
private def vonEnd (toks : Array (String × Char)) (start lastEnd : Nat) : Nat := Id.run do
  let mut e := lastEnd - 1
  for _ in [0:lastEnd] do
    if e > start then
      if vonToken ((toks[e - 1]?.map (·.1)).getD "") then return e
      e := e - 1
    else break
  return (if lastEnd == 0 then 0 else e)

/-- One name, split into BibTeX's four parts exactly as bibtex.web splits
it. `First von Last`: the von part runs from the first von token
(`vonToken`) before the last token to the last such token, and every token
between them is von too; with no von token the last name is the last token
and the tokens a hyphen joins to it (`Jean-Paul Sartre-Smith`). `von Last,
First` and `von Last, Jr, First`: the von part is everything before the
comma up to its last von token, the last name keeping at least one token.
A part keeps each token's separator — a hyphen or a tie as written — so
`Jean-Paul` abbreviates to `J.-P.` (`initials`). -/
public def parseName (s : String) : Name := Id.run do
  let (toks, commas) := nameTokens s
  let n := toks.size
  match commas.toList with
  | [] =>
    let lastEnd := n
    let firstVon := (List.range (n - 1)).find? fun k => vonToken ((toks[k]?.map (·.1)).getD "")
    match firstVon with
    | some vs =>
      let ve := vonEnd toks vs lastEnd
      return { first := joinToks toks 0 vs, von := joinToks toks vs ve,
               last := joinToks toks ve lastEnd }
    | none =>
      -- no von part: the last token, with the tokens a hyphen joins to it
      let mut vs := n - 1
      for _ in [0:n] do
        if vs > 0 && ((toks[vs]?.map (·.2)).getD ' ') == '-' then vs := vs - 1
        else break
      return { first := joinToks toks 0 vs, last := joinToks toks vs n }
  | [c1] =>
    let ve := vonEnd toks 0 c1
    return { first := joinToks toks c1 n, von := joinToks toks 0 ve,
             last := joinToks toks ve c1 }
  | c1 :: c2 :: _ =>
    let ve := vonEnd toks 0 c1
    return { first := joinToks toks c2 n, von := joinToks toks 0 ve,
             last := joinToks toks ve c1, jr := joinToks toks c1 c2 }

/-- A name as biber reads it: in the extended format where it is written in
it, else as bibtex.web splits it. -/
public def parseNameBiber (s : String) : Name := (parseNameX? s).getD (parseName s)

/-- A token's first letter, with the marks a decomposed spelling sets on it
(`E` and U+0301 are `É`): what an abbreviation keeps of the token, any
script's letter counting — bibtex 0.99 took the first byte of `Émile`,
half a character. A token with no letter keeps its first character. -/
private def firstLetter (cs : List Char) : String :=
  match cs.dropWhile (!Nfc.isLetter ·) with
  | c :: rest => String.ofList (c :: rest.takeWhile (Nfc.combiningClass · != 0))
  | [] => String.ofList (cs.take 1)

/-- BibTeX's `{f.}` abbreviation of a name part: each token's first letter
and a period, the tokens joined by their own separators — a hyphen kept,
so `Jean-Paul` is `J.-P.` — a token that opens with a special character
(`{\'E}mile`) abbreviated to that whole group, and one that opens with an
ordinary brace group (`{Ann Marie}`) to the group's first letter
(`firstLetter`). -/
public def initials (part : String) : String := Id.run do
  let (toks, _) := nameTokens part
  let mut out := ""
  for k in [0:toks.size] do
    match toks[k]? with
    | some (t, sep) =>
      unless k == 0 do out := out.push (if sep == '-' then '-' else ' ')
      let cs := t.toList
      let head : String :=
        if cs.head? == some '{' && cs[1]? == some '\\' then Id.run do
          let mut level : Nat := 0
          let mut acc := ""
          for c in cs do
            acc := acc.push c
            if c == '{' then level := level + 1
            else if c == '}' then
              level := level - 1
              if level == 0 then return acc
          return acc
        else firstLetter cs
      out := out ++ head ++ "."
    | none => pure ()
  return out

private def joinSp (toks : List String) : String :=
  String.intercalate " " toks

/-- BibTeX's abbreviation of a name part without periods or separators
(`{v{}}`, `{l{}}`): each token's first letter — a special character
`{\\…}` whole, an ordinary brace group's first letter. -/
public def tokenLetters (part : String) : String := Id.run do
  let (toks, _) := nameTokens part
  let mut out := ""
  for (t, _) in toks do
    let cs := t.toList
    match cs with
    | '{' :: '\\' :: _ =>
      let mut level : Nat := 0
      let mut acc := ""
      for c in cs do
        acc := acc.push c
        if c == '{' then level := level + 1
        else if c == '}' then
          level := level - 1
          if level == 0 then break
      out := out ++ acc
    | _ =>
      if cs.any Nfc.isLetter then out := out ++ firstLetter cs
  return out

/-- BibTeX's `text.length$`: a value's characters, a special character
`{\\…}` counting as one and braces as none (bibtex.web, "Count the
text characters"). -/
public def textLength (v : String) : Nat := Id.run do
  let cs := v.toList.toArray
  let mut count := 0
  let mut depth : Nat := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '{' && depth == 0 && cs[i + 1]? == some '\\' then
        -- a special character: passed over whole, one character
        let mut level : Nat := 0
        for _ in [i:cs.size] do
          if hk : i < cs.size then
            let d := cs[i]
            i := i + 1
            if d == '{' then level := level + 1
            else if d == '}' then
              level := level - 1
              if level == 0 then break
          else break
        count := count + 1
      else
        if c == '{' then depth := depth + 1
        else if c == '}' then depth := depth - 1
        else count := count + 1
        i := i + 1
    else break
  return count

/-- BibTeX's `text.prefix$`: the first `n` characters of a value, a
special character `{\\…}` counting as one and braces as none, the groups
it opens closed. -/
public def textPrefix (v : String) (n : Nat) : String := Id.run do
  let cs := v.toList.toArray
  let mut out := ""
  let mut count := 0
  let mut depth : Nat := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      if count ≥ n then break
      let c := cs[i]
      if c == '{' && depth == 0 && cs[i + 1]? == some '\\' then
        -- a special character: copied whole, one character
        let mut level : Nat := 0
        for _ in [i:cs.size] do
          if hk : i < cs.size then
            let d := cs[i]
            out := out.push d
            i := i + 1
            if d == '{' then level := level + 1
            else if d == '}' then
              level := level - 1
              if level == 0 then break
          else break
        count := count + 1
      else if c == '{' then
        depth := depth + 1
        out := out.push c
        i := i + 1
      else if c == '}' then
        if depth > 0 then
          depth := depth - 1
          out := out.push c
        i := i + 1
      else
        out := out.push c
        count := count + 1
        i := i + 1
    else break
  return out ++ String.ofList (List.replicate depth '}')

/-- `{ff }{vv }{ll}{, jj}`: the full-name order plainnat's `format.names`
prints in the reference list (plainnat.bst FUNCTION {format.names}). -/
public def Name.full (n : Name) : String :=
  let parts := [n.first, n.von, n.last].filter (!·.isEmpty)
  joinSp parts ++ (if n.jr.isEmpty then "" else s!", {n.jr}")

/-- `{vv~}{ll}`: the short form `\citet` and the label use. -/
public def Name.short (n : Name) : String :=
  joinSp ([n.von, n.last].filter (!·.isEmpty))

/-- plain.bst's name join (FUNCTION {format.names}): two names join with
` and `, more with `, ` and a final `, and `; a closing `others` elides to
`et al.` — appended directly after one name, after a comma otherwise. -/
public def andJoin (ns : List String) : String :=
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

/-- The label names a citation prints: every last name, joined as
`andJoin` joins a list, up to `upTo` names, and past it the first with
`et al.` — plainnat.bst FUNCTION {format.lab.names} at its two (one
author's name; two joined with ` and `; more, or an elided list, take
`et al.`), biblatex at its `maxcitenames` of three (`Doe, Roe, and Poe`).
`withVon` keeps a name's von part, as BibTeX's `{vv~}{ll}` does; biblatex's
`useprefix=false` drops it (`de Pome` cites as `Pome`). -/
public def labelNames (v : String) (upTo : Nat := 2) (withVon : Bool := true) : String :=
  let ns := splitNames v
  let short (s : String) : String :=
    let n := parseName s
    text (if withVon then n.short else n.last)
  if ns.size ≤ upTo then andJoin (ns.toList.map fun s => if s == "others" then s else short s)
  else match ns.toList with
    | a :: _ => s!"{short a} et al."
    | [] => ""

/-- `labelNames` in TeX, each name as the `.bib` spells it: what a sort key
reads (`purify`), where `{\\"u}` sorts as `u` — the reading `labelNames`'
composed letters cannot give back. -/
public def labelNamesTeX (v : String) (upTo : Nat := 2) (withVon : Bool := true) : String :=
  let ns := splitNames v
  let short (s : String) : String :=
    let n := parseName s
    if withVon then n.short else n.last
  if ns.size ≤ upTo then andJoin (ns.toList.map fun s => if s == "others" then s else short s)
  else match ns.toList with
    | a :: _ => s!"{short a} et al."
    | [] => ""

/-- The full author list natbib's starred forms print (plainnat.bst
FUNCTION {format.full.names}, the long names each `\bibitem` carries):
every last name, joined as `andJoin` joins a list. -/
public def fullNames (v : String) : String :=
  andJoin ((splitNames v).toList.map fun s =>
    if s == "others" then s else text (parseName s).short)

end LeanTex.Core.Bib
