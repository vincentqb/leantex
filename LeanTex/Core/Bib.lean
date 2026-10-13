module

public import LeanTex.Core.Diag
public import LeanTex.Core.LocaleData
public import LeanTex.Core.BibAccent
public import Std.Data.HashMap
import LeanTex.Core.Nfc

/-! BibTeX bibliography files parsed in the pure core, with
their value text and name parts. -/

namespace LeanTex.Core.Bib

/-- The file a bibliography or data request names, `.bib` appended when the
source does not spell it. -/
public def sourceName (src : String) : String :=
  if src.endsWith ".bib" then src else src ++ ".bib"

/-- One parsed entry: `@kind{key, fields}`, kind and field
names lowercased, the key's case kept. -/
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

/-- The parse result: a malformed entry is recorded and the
parse resynchronises at the next `@`. -/
public structure Parsed where
  entries : Array Entry := #[]
  errors : Array (Pos × String) := #[]
  /-- The `@preamble`s' texts, in order. -/
  preambles : Array String := #[]
  /-- The `@string` store after the file, which the
  bibliography's next file reads against. -/
  macros : Std.HashMap String String := {}
  /-- Each value part naming a macro no `@string` defined by
  then: the entry's key and the name. -/
  undefined : Array (String × String) := #[]
  deriving Inhabited

private def Parsed.err (out : Parsed) (p : Pos) (msg : String) : Parsed :=
  { out with errors := out.errors.push (p, msg) }

private def Parsed.entry (out : Parsed) (e : Entry) : Parsed :=
  { out with entries := out.entries.push e }

/-- The month macro keys every BibTeX style file defines. -/
private def monthKeys : Array String :=
  #["jan", "feb", "mar", "apr", "may", "jun",
    "jul", "aug", "sep", "oct", "nov", "dec"]

public def monthMacros (months : Array String) : Std.HashMap String String :=
  (monthKeys.zip months).foldl (fun m (k, v) => m.insert k v) {}

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Line and column of index `i`, counted forward from
position `p` known at index `start`. -/
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

/-- Line and column of an index, counted from the file's start. -/
private def posOf (cs : Array Char) (i : Nat) : Pos := posFrom cs 0 { line := 1, col := 1 } i

private def skipWs (cs : Array Char) (start : Nat) : Nat := Id.run do
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if isWs cs[j] then j := j + 1 else break
    else break
  return j

/-- The characters of an entry-type or field name. -/
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

/-- A cite key's characters: everything but a comma,
whitespace or a delimiter. -/
private def keyChar (c : Char) : Bool :=
  !isWs c && c != ',' && c != '{' && c != '}' && c != '(' && c != ')' && c != '"'

/-- A `{…}`-balanced group's content and the index past its closer, or `none`
when the file ends first. -/
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

/-- A `"…"` string's content: braces protect an inner quote. -/
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

/-- One `#`-concatenation part: a braced group, a quoted string, a bare number,
or a macro name resolved case-insensitively. -/
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

/-- A field value: parts joined by `#`, with the undefined
macro names among them. -/
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

/-- The fields of one entry body to its closing delimiter, the undefined macro
names, and the index past the closer. -/
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

/-- The index of the next `@` at or after `start`, where the
parse resynchronises. -/
private def nextAt (cs : Array Char) (start : Nat) : Nat := Id.run do
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if cs[j] == '@' then return j
      j := j + 1
    else break
  return cs.size

/-- Parses a `.bib` file's text; text outside `@…{…}` entries is comment. -/
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

private def isAccentMark (c : Char) : Bool :=
  c == '\'' || c == '`' || c == '"' || c == '^' || c == '~'

/-- `text` without the trim; `lead` keeps a leading space too. -/
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
                -- An unknown command's name stays visible as text, unless the reading drops it.
                if keepUnknown then out := out ++ name
                i := j
          else
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

/-- The plain text of a stored value: braces dropped, accents composed, `~` a
space, `---`/`--` the dashes, whitespace folded. -/
public def text (v : String) : String := (textSpan v).trimAscii.toString

/-- A value as biber's sort strings read it: `text`'s reading with every
command's name dropped. -/
public def sortPlainText (v : String) : String := (textSpan v (keepUnknown := false)).trimAscii.toString

/-- BibTeX's `change.case$` lowering a value: `"t"` is title sentence case,
`"l"` lowers everything. -/
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

/-- bibtex.web's foreign-letter control words, lowercase ones first. -/
private def lowerForeign : List String := ["i", "j", "oe", "ae", "aa", "o", "l", "ss"]
private def upperForeign : List String := ["OE", "AE", "AA", "O", "L"]

/-- BibTeX's `purify$`. -/
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

public structure Name where
  first : String := ""
  von : String := ""
  last : String := ""
  jr : String := ""
  /-- A per-name `useprefix`, over the document's option. -/
  useprefix : Option Bool := none
  deriving Repr, BEq, Inhabited

/-- A value split on a depth-0 separator word, brace groups opaque. -/
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

/-- The names of an `author` field, in order: split on `and`
at brace depth 0. -/
public def splitNames (v : String) : Array String :=
  (splitTop v andAt).map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- The name parts biber's extended name format spells out. -/
private def xnameParts : List String := ["family", "given", "prefix", "suffix"]

/-- A name in biber's extended name format: `key=value`
items split at commas outside braces. -/
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

/-- One name's tokens as bibtex.web reads them. -/
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

/-- The case of a brace group's letters from `start`, at brace level `level`:
the first letter decides. -/
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

/-- Whether a token is a von token: its first letter at
brace depth 0 is lowercase. -/
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

/-- Tokens `a` to `b` of a name, each after the separator it
was written with. -/
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

/-- The end of a von part starting at `start` and stopping
before the last name's last token. -/
private def vonEnd (toks : Array (String × Char)) (start lastEnd : Nat) : Nat := Id.run do
  let mut e := lastEnd - 1
  for _ in [0:lastEnd] do
    if e > start then
      if vonToken ((toks[e - 1]?.map (·.1)).getD "") then return e
      e := e - 1
    else break
  return (if lastEnd == 0 then 0 else e)

/-- One name split into BibTeX's four parts exactly as bibtex.web splits it. -/
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

/-- A name as biber reads it: in the extended format where written in it, else
as bibtex.web splits it. -/
public def parseNameBiber (s : String) : Name := (parseNameX? s).getD (parseName s)

/-- A token's first letter, with the marks a decomposed spelling sets on it. -/
private def firstLetter (cs : List Char) : String :=
  match cs.dropWhile (!Nfc.isLetter ·) with
  | c :: rest => String.ofList (c :: rest.takeWhile (Nfc.combiningClass · != 0))
  | [] => String.ofList (cs.take 1)

/-- BibTeX's `{f.}` abbreviation of a name part: each token's first letter and a
period, joined by its separators. -/
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

/-- BibTeX's abbreviation of a name part without periods or separators. -/
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

/-- BibTeX's `text.length$`: a special character counts as
one, braces as none. -/
public def textLength (v : String) : Nat := Id.run do
  let cs := v.toList.toArray
  let mut count := 0
  let mut depth : Nat := 0
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == '{' && depth == 0 && cs[i + 1]? == some '\\' then
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

/-- BibTeX's `text.prefix$`: the first `n` characters, a
special character counting as one. -/
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

/-- `{ff }{vv }{ll}{, jj}`: the full-name order plainnat's
`format.names` prints. -/
public def Name.full (n : Name) : String :=
  let parts := [n.first, n.von, n.last].filter (!·.isEmpty)
  joinSp parts ++ (if n.jr.isEmpty then "" else s!", {n.jr}")

/-- `{vv~}{ll}`: the short form `\citet` and the label use. -/
public def Name.short (n : Name) : String :=
  joinSp ([n.von, n.last].filter (!·.isEmpty))

/-- plain.bst's name join: ` and ` for two, `, ` and a final `, and ` for more,
a closing `others` as `et al.`. -/
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

/-- The label names a citation prints: every last name joined as `andJoin`
joins, up to `upTo` names, else the first with `et al.`. -/
public def labelNames (v : String) (upTo : Nat := 2) (withVon : Bool := true) : String :=
  let ns := splitNames v
  let short (s : String) : String :=
    let n := parseName s
    text (if withVon then n.short else n.last)
  if ns.size ≤ upTo then andJoin (ns.toList.map fun s => if s == "others" then s else short s)
  else match ns.toList with
    | a :: _ => s!"{short a} et al."
    | [] => ""

/-- `labelNames` in TeX, each name as the `.bib` spells it, for sort keys. -/
public def labelNamesTeX (v : String) (upTo : Nat := 2) (withVon : Bool := true) : String :=
  let ns := splitNames v
  let short (s : String) : String :=
    let n := parseName s
    if withVon then n.short else n.last
  if ns.size ≤ upTo then andJoin (ns.toList.map fun s => if s == "others" then s else short s)
  else match ns.toList with
    | a :: _ => s!"{short a} et al."
    | [] => ""

/-- The full author list natbib's starred forms print. -/
public def fullNames (v : String) : String :=
  andJoin ((splitNames v).toList.map fun s =>
    if s == "others" then s else text (parseName s).short)

end LeanTex.Core.Bib
