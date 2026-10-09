module

/-
The matcher behind the privacy gate: does a text name a term of this clone's
denylist? Pure; reading the list, the staged diff, the tree and the unpushed
commits is the gate's own work (scripts/precommit.lean), and the selftests
over invented terms run in `lake test` (Tests/Privacy.lean).

The list lives outside the tree, at `info/private-terms` in the git common
directory, so every worktree shares one copy and no commit carries it. A
line opening with `#` is a comment and a blank line is nothing; any other
line, trimmed, is one term. A term prefixed `case:` matches case-sensitively,
any other case-insensitively, and both with diacritics folded: canonical
decomposition, combining marks dropped.

A term is a sequence of words: its runs of letters and digits, split again
where an identifier's case opens a word (`fooBar`, `HTMLParser`). A text
holds the term where those words stand in order, each pair apart by nothing
or by at most `gapMax` scalars that are neither letters nor digits — white
space and line breaks, `-`, `_`, `.`, `/`, a comment leader on a wrapped
line, the quotes and `++` of a split string literal — so a phrase reads the
same spaced, wrapped, kebab-, snake- or camel-cased, or run together. The
match is a whole word: on either side stands the text's edge, a scalar that
is no letter or digit, or a case change that opens a word. A digit beside a
letter is no boundary.

A term is looked for in several readings of one text, and a hit in any of
them counts, because a term reaches a source file spelled more ways than
one:
* the text as written;
* TeX's spellings of letters undone: accent commands (`\'e`, `\c{c}`),
  letter commands (`\o`, `\ss`), the discretionary hyphen, ties, spacing
  commands and braces, with invisible format characters removed;
* the same after Lean's string escapes (`\\`, `\"`, `\u{…}`, `\uXXXX`,
  `\xHH`), character references (`&#…;`, `&#x…;`, and the named ones of
  Latin-1) and percent-encoding are decoded first, which is how a test's
  string literal, a page or a URL spells its text.

Bytes are cut into lines at LF and NUL, which every encoding read here
keeps; a line that is not UTF-8 is read as lenient UTF-8 and again as
Windows-1252, which spells Latin-1's letters too, so a legacy-encoded file's
accented letter does not split its word into two around U+FFFD. Content
that is not text (a font, an image, a PDF) is read as lenient UTF-8, and
again with every zero byte removed and each other byte read as the
Windows-1252 scalar it spells: how ASCII and Latin-1 text stored as UTF-16
reads, in either byte order and at either alignment. Compressed content is
inflated and read the same ways — a PDF's zlib streams, a PNG's compressed
text, a gzip member, a zip archive's members, and one container inside
another — and a PDF's strings are decoded: their escapes, hex digits and
byte-order mark read, the strings of one array (a `TJ` operand, which
kerning splits mid-word) run together.

What no reading sees: a phrase whose words stand more than `gapMax`
separator scalars apart or with letters between them; text a PDF sets in a
font's glyph codes rather than in characters, which is most page text a TeX
engine writes; an accent command parted from its letter by a line break;
text in any encoding other than UTF-8, UTF-16's Latin-1 range and
Windows-1252; content under any other compression (Brotli, LZW, xz) or past
`decodeCap` bytes; and, in a staged change or an unpushed commit, the
content of a binary file whose path is not UTF-8, which git is asked for by
that path (the tree check reads every blob by its object id).

A hit is reported by where it stands, never by what it says. Where the
location is itself text that may hold a term — a path, a line the gate
prints — `Matcher.mask` replaces each segment taking part in a hit with `…`,
and a text still holding one after that is masked whole.

The rest of the module reads what the gate asks git for: the added lines of
a unified diff, and the per-commit records of `git log`.
-/

public import LeanTex.Core.Nfc
public import LeanTex.Core.Flate.BlockStream
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Privacy

open LeanTex.Core

/-- One term of the list: its words, folded the way a text is, and whether
it keeps case (`case:`). -/
structure Term where
  words : Array (Array Char)
  cased : Bool

/-- White space a phrase may wrap across: ASCII's, the no-break and the
typographic spaces, and the line and paragraph separators. -/
def isSpace (c : Char) : Bool :=
  let n := c.toNat
  if n < 0x80 then n == 0x20 || (0x09 ≤ n && n ≤ 0x0D)
  else n == 0x85 || n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A)
    || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

/-- A combining mark, which the fold drops: a nonzero canonical combining
class, or a scalar of the five combining-mark blocks, where the few marks of
class zero stand. -/
def isMark (c : Char) : Bool :=
  let n := c.toNat
  n ≥ 0x300 && (Nfc.combiningClass c != 0 || n ≤ 0x36F
    || (0x1AB0 ≤ n && n ≤ 0x1AFF) || (0x1DC0 ≤ n && n ≤ 0x1DFF)
    || (0x20D0 ≤ n && n ≤ 0x20FF) || (0xFE20 ≤ n && n ≤ 0xFE2F))

/-- A letter (Unicode's L*) or an ASCII digit: what a match may not touch on
either side. -/
def wordChar (c : Char) : Bool :=
  if c.toNat < 0x80 then c.isAlphanum else Nfc.isLetter c

/-- Unicode simple lowercase, ASCII answered here. -/
def lowerOf (c : Char) : Char :=
  if c.toNat < 0x80 then c.toLower else Nfc.toLower c

/-- A capital: a letter its simple lowercase moves. -/
def isUpper (c : Char) : Bool := lowerOf c != c

/-- A letter that is no capital: a lowercase one, or one of a script
without case. Digits are not letters. -/
def isLowerLetter (c : Char) : Bool :=
  wordChar c && !(c.toNat < 0x80 && c.isDigit) && !isUpper c

/-- The scalar at `i`, or U+0000 past the end: a scalar no reading compares
against. -/
def charAt (cs : Array Char) (i : Nat) : Char :=
  if h : i < cs.size then cs[i] else Char.ofNat 0

/-- A format character no reader sees: the soft hyphen, the zero-width space
and joiners, the word joiner and the byte-order mark. -/
def invisible (c : Char) : Bool :=
  let n := c.toNat
  n == 0xAD || (0x200B ≤ n && n ≤ 0x200D) || n == 0x2060 || n == 0xFEFF

/-- Does an identifier's case open a word at `i`: a capital after a
lowercase letter (`fooBar`), or a capital after a capital and before a
lowercase letter (`HTMLParser`)? -/
def caseBreak (s : Array Char) (i : Nat) : Bool :=
  if i == 0 || s.size ≤ i then false else
    let c := charAt s i
    let p := charAt s (i - 1)
    isUpper c && (isLowerLetter p || (isUpper p && isLowerLetter (charAt s (i + 1))))

/-- May a word open at `i`: at the text's start, after a scalar that is no
letter or digit, or at a case break? -/
def opensAt (s : Array Char) (i : Nat) : Bool :=
  i == 0 || !wordChar (charAt s (i - 1)) || caseBreak s i

/-- May a word close before `j`: at the text's end, before a scalar that is
no letter or digit, or at a case break? -/
def closesAt (s : Array Char) (j : Nat) : Bool :=
  s.size ≤ j || !wordChar (charAt s j) || caseBreak s j

/-- The most scalars two words of a term may stand apart by, none of them a
letter or digit: room for a comment leader on a wrapped line (` -- `) or a
split string literal (`" ++ "`). -/
def gapMax : Nat := 8

/-- A reading folded for matching: each scalar's canonical decomposition with
its marks dropped, every run of white space one space. `breaks` holds, per
newline of the reading, how many folded scalars precede the line it opens.
Every reading keeps the text's newlines one for one, so a folded scalar's
line is one more than the breaks at or below its index. -/
structure Folded where
  chars : Array Char
  breaks : Array Nat

def fold (cs : Array Char) : Folded := Id.run do
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut breaks : Array Nat := #[]
  let mut gap := false
  for c in cs do
    if isSpace c then
      unless gap do
        out := out.push ' '
        gap := true
      if c == '\n' then breaks := breaks.push out.size
    else if c.toNat < 0x80 then
      out := out.push c
      gap := false
    else
      for b in Nfc.decompose c do
        unless isMark b do
          out := out.push b
          gap := false
  return { chars := out, breaks }

/-- The 1-based line folded scalar `i` came from: by binary search, one more
than the breaks at or below `i`. -/
def Folded.lineOf (f : Folded) (i : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := f.breaks.size
  for _ in [0:f.breaks.size + 1] do
    if hi ≤ lo then break
    let mid := (lo + hi) / 2
    if (f.breaks[mid]?).getD 0 ≤ i then lo := mid + 1 else hi := mid
  return lo + 1

/-- A term's words: the runs of letters and digits of its folded scalars,
split again at each case break, lowercased unless the term keeps case. -/
def termWords (raw : String) (cased : Bool) : Array (Array Char) := Id.run do
  let f := (fold (raw.foldl (fun a c => a.push c) #[])).chars
  let mut out : Array (Array Char) := #[]
  let mut cur : Array Char := #[]
  for i in [0:f.size] do
    let c := charAt f i
    if wordChar c && !(caseBreak f i && !cur.isEmpty) then
      cur := cur.push (if cased then c else lowerOf c)
    else
      unless cur.isEmpty do
        out := out.push cur
      cur := if wordChar c then #[if cased then c else lowerOf c] else #[]
  unless cur.isEmpty do
    out := out.push cur
  return out

/-- The list's terms, in file order. A term with no letter or digit is no
term: a bare `case:` line, or one of marks or punctuation alone. -/
def parseTerms (src : String) : Array Term := Id.run do
  let mut out : Array Term := #[]
  for raw in src.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    let cased := l.startsWith "case:"
    let words := termWords (if cased then (l.drop 5).toString else l) cased
    unless words.isEmpty do
      out := out.push { words, cased }
  return out

/-- The list compiled for matching: the terms, and per opening scalar the
terms that open with it — ASCII by index, anything else by hash. -/
structure Matcher where
  terms : Array Term
  ascii : Array (Array Nat)
  other : Std.HashMap Char (Array Nat)

def Matcher.ofTerms (ts : Array Term) : Matcher := Id.run do
  let mut ascii : Array (Array Nat) := Array.replicate 128 #[]
  let mut other : Std.HashMap Char (Array Nat) := {}
  for (t, k) in ts.zipIdx do
    if let some c := (t.words[0]?).bind (·[0]?) then
      if c.toNat < 128 then ascii := ascii.modify c.toNat (·.push k)
      else other := other.insert c ((other.getD c #[]).push k)
  return { terms := ts, ascii, other }

/-- The terms whose first scalar is `c`. -/
def Matcher.opening (m : Matcher) (c : Char) : Array Nat :=
  if c.toNat < 128 then (m.ascii[c.toNat]?).getD #[] else m.other.getD c #[]

/-- The most words one term has: how many segments a hit can span. -/
def Matcher.maxWords (m : Matcher) : Nat :=
  m.terms.foldl (fun n t => max n t.words.size) 0

/-- Does `t` stand at index `i` of `s`: its words in order, compared
case-folded unless it keeps case, each after the first at most `gapMax`
scalars that are no letter or digit past the one before, and a word's close
after the last? The open before it is the caller's to judge. -/
def standsAt (s : Array Char) (i : Nat) (t : Term) : Bool := Id.run do
  let mut j := i
  for (w, k) in t.words.zipIdx do
    if k > 0 then
      for _ in [0:gapMax] do
        if j < s.size && !wordChar (charAt s j) then j := j + 1 else break
    if s.size < j + w.size then return false
    for want in w do
      let got := charAt s j
      if (if t.cased then got else lowerOf got) != want then return false
      j := j + 1
  return closesAt s j

/-- The 1-based lines of one folded reading on which a term opens as a
whole word, ascending, a line once per hit. A case-folded term opens with a
lowercase scalar and a cased one with its own, so the scalar and its
lowercase name every term that can stand at an index. -/
def Matcher.linesIn (m : Matcher) (f : Folded) : Array Nat := Id.run do
  let s := f.chars
  let mut out : Array Nat := #[]
  for i in [0:s.size] do
    if opensAt s i then
      let c := charAt s i
      let lc := lowerOf c
      let stands := fun (k : Nat) => match m.terms[k]? with
        | some t => standsAt s i t
        | none => false
      if (m.opening lc).any stands || (lc != c && (m.opening c).any stands) then
        out := out.push (f.lineOf i)
  return out

/-- The value of one hexadecimal digit. -/
def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The number spelled by `cs[i, j)` in base 16 (or 10), when every scalar
there is a digit of that base and the span is not empty. -/
def numberAt (cs : Array Char) (i j : Nat) (hex : Bool) : Option Nat := Id.run do
  if j ≤ i then return none
  let mut v := 0
  for k in [i:j] do
    let c := charAt cs k
    let d := if hex then hexVal c
      else if c.isDigit then some (c.toNat - '0'.toNat) else none
    match d with
    | some d => v := v * (if hex then 16 else 10) + d
    | none => return none
  return some v

/-- The first index at or after `i` holding `stop`, looked for within the
next `limit` scalars. -/
def findWithin (cs : Array Char) (i limit : Nat) (stop : Char) : Option Nat := Id.run do
  for k in [i:i + limit + 1] do
    if k < cs.size && charAt cs k == stop then return some k
  return none

/-- A decoded scalar as the reading keeps it: a newline written as an escape
is a space, so that the newlines of a reading stay the text's own. -/
def decoded (n : Nat) : Char :=
  let c := Char.ofNat n
  if c == '\n' then ' ' else c

/-- The named character references of Latin-1, in scalar order from U+00A0
(HTML's entity table, the ISO 8859-1 set). -/
def latin1Entities : Array String := #[
  "nbsp", "iexcl", "cent", "pound", "curren", "yen", "brvbar", "sect",
  "uml", "copy", "ordf", "laquo", "not", "shy", "reg", "macr",
  "deg", "plusmn", "sup2", "sup3", "acute", "micro", "para", "middot",
  "cedil", "sup1", "ordm", "raquo", "frac14", "frac12", "frac34", "iquest",
  "Agrave", "Aacute", "Acirc", "Atilde", "Auml", "Aring", "AElig", "Ccedil",
  "Egrave", "Eacute", "Ecirc", "Euml", "Igrave", "Iacute", "Icirc", "Iuml",
  "ETH", "Ntilde", "Ograve", "Oacute", "Ocirc", "Otilde", "Ouml", "times",
  "Oslash", "Ugrave", "Uacute", "Ucirc", "Uuml", "Yacute", "THORN", "szlig",
  "agrave", "aacute", "acirc", "atilde", "auml", "aring", "aelig", "ccedil",
  "egrave", "eacute", "ecirc", "euml", "igrave", "iacute", "icirc", "iuml",
  "eth", "ntilde", "ograve", "oacute", "ocirc", "otilde", "ouml", "divide",
  "oslash", "ugrave", "uacute", "ucirc", "uuml", "yacute", "thorn", "yuml"]

/-- The other named references a page writes around words: markup's five,
Latin Extended-A's letters of the HTML 4 set, and the typographic
punctuation. -/
def otherEntities : List (String × Nat) :=
  [("amp", 0x26), ("lt", 0x3C), ("gt", 0x3E), ("quot", 0x22), ("apos", 0x27),
   ("OElig", 0x152), ("oelig", 0x153), ("Scaron", 0x160), ("scaron", 0x161),
   ("Yuml", 0x178), ("ndash", 0x2013), ("mdash", 0x2014), ("lsquo", 0x2018),
   ("rsquo", 0x2019), ("ldquo", 0x201C), ("rdquo", 0x201D), ("hellip", 0x2026)]

/-- The scalar a named reference spells, if this module knows the name. -/
def entityScalar (name : String) : Option Nat :=
  match latin1Entities.findIdx? (· == name) with
  | some k => some (0xA0 + k)
  | none => (otherEntities.find? (·.1 == name)).map (·.2)

/-- Lenient UTF-8: a well-formed sequence is its scalar, and a byte that
opens none reads as U+FFFD, one byte at a time. -/
def utf8Lenient (bs : ByteArray) : Array Char := Id.run do
  let mut out : Array Char := Array.mkEmpty bs.size
  let mut i := 0
  for _ in [0:bs.size + 1] do
    let some b0 := bs[i]? | break
    let b := b0.toNat
    let (n, lead) :=
      if b < 0x80 then (1, b)
      else if b &&& 0xE0 == 0xC0 then (2, b &&& 0x1F)
      else if b &&& 0xF0 == 0xE0 then (3, b &&& 0x0F)
      else if b &&& 0xF8 == 0xF0 then (4, b &&& 0x07)
      else (0, 0)
    let mut v := lead
    let mut ok : Bool := n > 0
    for k in [1:n] do
      match bs[i + k]? with
      | some c =>
        if c.toNat &&& 0xC0 == 0x80 then v := v * 64 + (c.toNat &&& 0x3F) else ok := false
      | none => ok := false
    if ok then
      out := out.push (Char.ofNat v)
      i := i + n
    else
      out := out.push '�'
      i := i + 1
  return out

/-- Bytes as text: UTF-8 when they are, the lenient reading otherwise. -/
def textOfBytes (bs : ByteArray) : String :=
  match String.fromUTF8? bs with
  | some s => s
  | none => String.ofList (utf8Lenient bs).toList

/-- The run of percent-escaped bytes (`%C3%A9`) starting at `i`, and the
index past it. -/
def percentRun (cs : Array Char) (i : Nat) : ByteArray × Nat := Id.run do
  let mut bytes : ByteArray := .empty
  let mut j := i
  for _ in [0:cs.size + 1] do
    if charAt cs j != '%' then break
    match numberAt cs (j + 1) (j + 3) true with
    | some b =>
      bytes := bytes.push b.toUInt8
      j := j + 3
    | none => break
  return (bytes, j)

/-- Lean's string escapes, character references and percent-encoding
decoded: `\\`, `\"`, `\'`, `\n`/`\t`/`\r` (as spaces), `\u{…}`, `\uXXXX`,
`\xHH`, `&#…;`/`&#x…;`, the named references of `entityScalar`, and runs of
`%XX` read as UTF-8 where they spell it and as Latin-1 bytes where they do
not. Anything else is kept as written. -/
def escapeReading (cs : Array Char) : Array Char := Id.run do
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if cs.size ≤ i then break
    let c := charAt cs i
    let next := charAt cs (i + 1)
    if c == '\\' && (next == '\\' || next == '"' || next == '\'') then
      out := out.push next
      i := i + 2
    else if c == '\\' && (next == 'n' || next == 't' || next == 'r') then
      out := out.push ' '
      i := i + 2
    else if c == '%' then
      let (bytes, past) := percentRun cs i
      if bytes.isEmpty then
        out := out.push c
        i := i + 1
      else
        let spelt := match String.fromUTF8? bytes with
          | some s => s.toList
          | none => bytes.data.toList.map fun (b : UInt8) => Char.ofNat b.toNat
        for d in spelt do
          out := out.push (decoded d.toNat)
        i := past
    else if c != '\\' && c != '&' then
      out := out.push c
      i := i + 1
    else
      let braced := c == '\\' && next == 'u' && charAt cs (i + 2) == '{'
      let entity := c == '&' && next == '#'
      let hexEntity := entity && (charAt cs (i + 2) == 'x' || charAt cs (i + 2) == 'X')
      let named := c == '&' && next.isAlpha
      let spelt : Option (Nat × Nat) :=
        if braced then
          (findWithin cs (i + 3) 6 '}').bind fun j =>
            (numberAt cs (i + 3) j true).map fun n => (n, j + 1)
        else if c == '\\' && next == 'u' then
          (numberAt cs (i + 2) (i + 6) true).map fun n => (n, i + 6)
        else if c == '\\' && next == 'x' then
          (numberAt cs (i + 2) (i + 4) true).map fun n => (n, i + 4)
        else if entity then
          let start := if hexEntity then i + 3 else i + 2
          (findWithin cs start 7 ';').bind fun j =>
            (numberAt cs start j hexEntity).map fun n => (n, j + 1)
        else if named then
          (findWithin cs (i + 1) 7 ';').bind fun j =>
            (entityScalar (String.ofList (cs.extract (i + 1) j).toList)).map fun n => (n, j + 1)
        else none
      match spelt with
      | some (n, past) =>
        out := out.push (decoded n)
        i := past
      | none =>
        out := out.push c
        i := i + 1
  return out

/-- The accents TeX spells with one letter (`\c{c}`, `\v s`): cedilla, caron,
double acute, ogonek, ring, breve, dot and bar below, tie. -/
def letterAccents : List String := ["c", "v", "H", "k", "r", "u", "d", "b", "t"]

/-- The letters TeX spells as a command, and what each spells. -/
def letterCommands : List (String × String) :=
  [("i", "i"), ("j", "j"), ("o", "ø"), ("O", "Ø"), ("l", "ł"), ("L", "Ł"),
   ("ss", "ß"), ("ae", "æ"), ("AE", "Æ"), ("oe", "œ"), ("OE", "Œ"),
   ("aa", "å"), ("AA", "Å")]

/-- The index past the spaces and tabs at `i`: what TeX skips after a
command word. A newline is kept, so the reading keeps its lines. -/
def skipBlanks (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    let c := charAt cs j
    if c == ' ' || c == '\t' then j := j + 1 else break
  return j

/-- TeX's spellings of letters undone: an accent command is dropped (the
fold drops the accent it would set) with the blanks before its argument,
which the accent macro skips as it reads that argument; a letter command
becomes its letter; the discretionary hyphen, the italic correction and
`\@` vanish; a tie or a spacing command is a space; and braces are
dropped, as are invisible format characters. Any other command is kept as
written. -/
def texReading (cs : Array Char) : Array Char := Id.run do
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if cs.size ≤ i then break
    let c := charAt cs i
    if c == '\\' then
      let d := charAt cs (i + 1)
      if "'`^\"~=.".contains d then
        i := skipBlanks cs (i + 2)
      else if "-/@".contains d then
        i := i + 2
      else if ",;:! ".contains d then
        out := out.push ' '
        i := i + 2
      else if d.isAlpha then
        let mut j := i + 1
        for _ in [0:cs.size + 1] do
          if (charAt cs j).isAlpha then j := j + 1 else break
        let word := String.ofList ((cs.extract (i + 1) j).toList)
        let after := charAt cs j
        if letterAccents.contains word && (after == '{' || after == ' ') then
          i := skipBlanks cs j
        else if let some (_, spelt) := letterCommands.find? (·.1 == word) then
          for s in spelt.toList do
            out := out.push s
          i := skipBlanks cs j
        else
          for k in [i:j] do
            out := out.push (charAt cs k)
          i := j
      else
        out := out.push c
        i := i + 1
    else if c == '{' || c == '}' || invisible c then
      i := i + 1
    else if c == '~' then
      out := out.push ' '
      i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

/-- Ascending, without repeats. -/
def ascendingUnique (xs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for x in xs.qsort (· < ·) do
    if out.back? != some x then out := out.push x
  return out

/-- The readings of a text worth folding: the text as written, its TeX
reading where it holds a backslash, a brace, a tie or an invisible format
character, and its escape-then-TeX reading where it holds a backslash, an
ampersand or a percent sign. Any other text reads the same every way. -/
def readingsOf (cs : Array Char) : Array (Array Char) :=
  let tex := cs.any fun c => c == '\\' || c == '{' || c == '}' || c == '~' || invisible c
  let esc := cs.any fun c => c == '\\' || c == '&' || c == '%'
  let withTex := if tex then #[cs, texReading cs] else #[cs]
  if esc then withTex.push (texReading (escapeReading cs)) else withTex

/-- The 1-based lines of a text, as scalars, on which a term stands in any
reading. -/
def Matcher.charLines (m : Matcher) (cs : Array Char) : Array Nat :=
  if m.terms.isEmpty then #[] else
    ascendingUnique ((readingsOf cs).foldl (fun acc r => acc.append (m.linesIn (fold r))) #[])

/-- The 1-based lines of a text on which a term stands, in any reading,
ascending and without repeats. -/
def Matcher.textLines (m : Matcher) (s : String) : Array Nat :=
  m.charLines (s.foldl (fun a c => a.push c) (Array.mkEmpty s.utf8ByteSize))

/-- Does a text name a term anywhere, in any reading? -/
def Matcher.hits (m : Matcher) (s : String) : Bool := !(m.textLines s).isEmpty

/-- Does a path name a term? A path reads like any text, its separators
being no letters. -/
def Matcher.pathHit (m : Matcher) (p : String) : Bool := m.hits p

/-- `segs` joined by `sep`, each segment that takes part in a hit replaced
by `…`: a segment that hits alone, and each run of consecutive segments
that hits while neither run one segment shorter inside it does — hitting
only grows as a run grows, so those are the runs no shorter run inside
hits. A run is at most two segments per word of the longest term and two
more, empty segments between separators included. Whatever still holds a
term after that is masked whole, so the result never names one. -/
def Matcher.mask (m : Matcher) (segs : Array String) (sep : String) : String := Id.run do
  let whole := sep.intercalate segs.toList
  unless m.hits whole do return whole
  let n := segs.size
  let span := min n (2 * m.maxWords + 2)
  let runHits := fun (i len : Nat) => m.hits (sep.intercalate (segs.extract i (i + len)).toList)
  let mut masked : Array Bool := Array.replicate n false
  for len in [1:span + 1] do
    for i in [0:n + 1 - len] do
      if runHits i len && (len == 1 || (!runHits i (len - 1) && !runHits (i + 1) (len - 1))) then
        for k in [i:i + len] do
          masked := masked.set! k true
  let out := sep.intercalate ((segs.zip masked).toList.map fun (s, b) => if b then "…" else s)
  return if m.hits out then "…" else out

/-- A path with each component that takes part in a hit masked. -/
def Matcher.maskPath (m : Matcher) (p : String) : String :=
  m.mask (p.splitOn "/").toArray "/"

/-- A text with each space-separated word that takes part in a hit masked,
line by line: what the gate prints when what it prints may hold a term. -/
def Matcher.redact (m : Matcher) (s : String) : String :=
  if m.terms.isEmpty || !m.hits s then s else
    "\n".intercalate ((s.splitOn "\n").map fun l => m.mask (l.splitOn " ").toArray " ")

/-- Windows-1252's scalars for the bytes 0x80–0x9F, where it differs from
Latin-1; the five bytes it leaves undefined read as Latin-1's controls. -/
def cp1252High : Array Nat := #[
  0x20AC, 0x81, 0x201A, 0x192, 0x201E, 0x2026, 0x2020, 0x2021,
  0x2C6, 0x2030, 0x160, 0x2039, 0x152, 0x8D, 0x17D, 0x8F,
  0x90, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013, 0x2014,
  0x2DC, 0x2122, 0x161, 0x203A, 0x153, 0x9D, 0x17E, 0x178]

/-- The scalar a byte spells in Windows-1252: Latin-1's outside 0x80–0x9F. -/
def cp1252Char (b : UInt8) : Char :=
  let n := b.toNat
  if 0x80 ≤ n && n < 0xA0 then Char.ofNat ((cp1252High[n - 0x80]?).getD n) else Char.ofNat n

/-- Bytes read as Windows-1252, one scalar each. -/
def cp1252 (bs : ByteArray) : Array Char :=
  bs.foldl (fun out b => out.push (cp1252Char b)) (Array.mkEmpty bs.size)

/-- The bytes with every zero byte removed and each other byte read as the
Windows-1252 scalar it spells. -/
def cp1252NonZero (bs : ByteArray) : Array Char :=
  bs.foldl (fun out b => if b == 0 then out else out.push (cp1252Char b)) (Array.mkEmpty bs.size)

/-- Does a zero byte stand anywhere in `bs`? -/
def hasZero (bs : ByteArray) : Bool := bs.foldl (fun z b => z || b == 0) false

/-- The readings of bytes cut into segments at LF and NUL, which both
encodings below keep one for one: a segment that is UTF-8 reads as itself,
and one that is not as lenient UTF-8 in the first reading and as
Windows-1252 in the second. One reading when every segment is UTF-8, and
then it is the bytes' own text. -/
def segmentReadings (bs : ByteArray) : Array String :=
  match String.fromUTF8? bs with
  | some s => #[s]
  | none => Id.run do
    let mut lenient : Array Char := Array.mkEmpty bs.size
    let mut legacy : Array Char := Array.mkEmpty bs.size
    let mut start := 0
    for i in [0:bs.size + 1] do
      let cut := match bs[i]? with
        | some b => b == 10 || b == 0
        | none => true
      if cut then
        let seg := bs.extract start i
        match String.fromUTF8? seg with
        | some t =>
          for c in t.toList do
            lenient := lenient.push c
            legacy := legacy.push c
        | none =>
          lenient := lenient.append (utf8Lenient seg)
          legacy := legacy.append (cp1252 seg)
        if let some b := bs[i]? then
          lenient := lenient.push (Char.ofNat b.toNat)
          legacy := legacy.push (Char.ofNat b.toNat)
        start := i + 1
    return #[String.ofList lenient.toList, String.ofList legacy.toList]

/-! ## Compressed content -/

/-- The most bytes the decompressed readings of one blob take, all streams
together: past it the rest is not read. -/
def decodeCap : Nat := 64 * 1024 * 1024

/-- An ASCII spelling's bytes. -/
def ascii (s : String) : Array UInt8 := s.toUTF8.data

/-- Does `pat` stand in `bs` at `i`? -/
def bytesAt (bs : ByteArray) (i : Nat) (pat : Array UInt8) : Bool := Id.run do
  for k in [0:pat.size] do
    if bs[i + k]? != pat[k]? then return false
  return true

/-- The first index at or past `i` where `pat` stands, or `bs.size`. -/
def findBytes (bs : ByteArray) (i : Nat) (pat : Array UInt8) : Nat := Id.run do
  for j in [i:bs.size] do
    if bytesAt bs j pat then return j
  return bs.size

/-- Two bytes at `i`, least significant first; a byte past the end is 0. -/
def le16 (bs : ByteArray) (i : Nat) : Nat :=
  (bs[i]?.getD 0).toNat + 256 * (bs[i + 1]?.getD 0).toNat

/-- Four bytes at `i`, least significant first. -/
def le32 (bs : ByteArray) (i : Nat) : Nat := le16 bs i + 65536 * le16 bs (i + 2)

/-- Four bytes at `i`, most significant first. -/
def be32 (bs : ByteArray) (i : Nat) : Nat :=
  65536 * (256 * (bs[i]?.getD 0).toNat + (bs[i + 1]?.getD 0).toNat)
    + 256 * (bs[i + 2]?.getD 0).toNat + (bs[i + 3]?.getD 0).toNat

/-- What a deflate stream (RFC 1951) opening at byte `start` of `bs`
inflates to, at most `cap` bytes of it; `none` where none opens there or
it would pass the cap. -/
def inflateAt (bs : ByteArray) (start cap : Nat) : Option ByteArray :=
  match LeanTex.Core.Flate.BlockStream.read { data := bs, bitPos := 8 * start } .empty cap with
  | .ok out => some out
  | .error _ => none

/-- A zlib stream (RFC 1950 §2.2) opening at `start`: the deflate method, a
window the format allows, a header check that holds and no preset
dictionary, then its body inflated (`inflateAt`). -/
def zlibAt (bs : ByteArray) (start cap : Nat) : Option ByteArray := do
  let cmf := (← bs[start]?).toNat
  let flg := (← bs[start + 1]?).toNat
  if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || flg / 32 % 2 == 1 then
    none
  else inflateAt bs (start + 2) cap

/-- Is `bs` a PDF: does its header (ISO 32000-2 §7.5.2) open in its first
1024 bytes? -/
def isPdf (bs : ByteArray) : Bool :=
  findBytes (bs.extract 0 1024) 0 (ascii "%PDF-") < min bs.size 1024

/-- A PDF's object syntax, around and between its streams, and those of its
streams that inflate as zlib (`zlibAt`), within `cap` bytes in all. A
stream's raw data is binary and is left to the blob's own readings. -/
def pdfParts (bs : ByteArray) (cap : Nat) : ByteArray × Array ByteArray := Id.run do
  let kw := ascii "stream"
  let endKw := ascii "endstream"
  let mut objects : ByteArray := .empty
  let mut streams : Array ByteArray := #[]
  let mut left := cap
  let mut i := 0
  for _ in [0:bs.size + 1] do
    if bs.size ≤ i then break
    let j := findBytes bs i kw
    let start :=
      if bs[j + 6]? == some 13 && bs[j + 7]? == some 10 then j + 8
      else if bs[j + 6]? == some 10 then j + 7 else 0
    if bs.size ≤ j || (3 ≤ j && bytesAt bs (j - 3) endKw) || start == 0 then
      objects := objects.append (bs.extract i (j + 6))
      i := j + 6
    else
      objects := objects.append (bs.extract i j)
      if 0 < left then
        if let some out := zlibAt bs start left then
          streams := streams.push out
          left := left - min left out.size
      i := findBytes bs start endKw + 9
  return (objects, streams)

/-- The value of an octal digit's byte. -/
def octalDigit (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 55 then some (b.toNat - 48) else none

/-- A PDF literal string's bytes from just past its `(`, and the index
past its `)` (ISO 32000-2 §7.3.4.2): the escapes `\n` `\r` `\t` `\b` `\f`
`\(` `\)` `\\` read, as are up to three octal digits; a backslash before an
end of line continues the string; balanced parentheses stand for
themselves; any other escaped byte is that byte. -/
def pdfLiteral (bs : ByteArray) (i : Nat) : ByteArray × Nat := Id.run do
  let mut out : ByteArray := .empty
  let mut j := i
  let mut depth := 1
  for _ in [0:bs.size + 1] do
    let some b := bs[j]? | break
    if b == 92 then
      match bs[j + 1]? with
      | none => j := j + 1
      | some e =>
        match octalDigit e with
        | some d =>
          let mut v := d
          let mut k := j + 2
          for _ in [0:2] do
            match (bs[k]?).bind octalDigit with
            | some d' =>
              v := v * 8 + d'
              k := k + 1
            | none => break
          out := out.push (v % 256).toUInt8
          j := k
        | none =>
          if e == 13 then j := if bs[j + 2]? == some 10 then j + 3 else j + 2
          else if e == 10 then j := j + 2
          else
            let c : UInt8 := if e == 110 then 10 else if e == 114 then 13 else if e == 116 then 9
              else if e == 98 then 8 else if e == 102 then 12 else e
            out := out.push c
            j := j + 2
    else if b == 40 then
      depth := depth + 1
      out := out.push b
      j := j + 1
    else if b == 41 then
      depth := depth - 1
      j := j + 1
      if depth == 0 then break
      out := out.push b
    else
      out := out.push b
      j := j + 1
  return (out, j)

/-- A PDF hex string's bytes from just past its `<`, and the index past its
`>` (ISO 32000-2 §7.3.4.3): white space skipped, a final odd digit read as
followed by 0. `none` where any other byte stands before the `>`. -/
def pdfHex (bs : ByteArray) (i : Nat) : Option (ByteArray × Nat) := Id.run do
  let mut out : ByteArray := .empty
  let mut high : Option Nat := none
  let mut j := i
  for _ in [0:bs.size + 1] do
    let some b := bs[j]? | return none
    j := j + 1
    if b == 62 then
      if let some h := high then out := out.push (h * 16).toUInt8
      return some (out, j)
    if b == 32 || b == 9 || b == 10 || b == 13 || b == 12 || b == 0 then continue
    match hexVal (Char.ofNat b.toNat) with
    | some v =>
      match high with
      | some h =>
        out := out.push (h * 16 + v).toUInt8
        high := none
      | none => high := some v
    | none => return none
  return none

/-- UTF-16 big-endian code units read as scalars: a surrogate pair as one,
an unpaired surrogate as U+FFFD. -/
def utf16be (bs : ByteArray) : Array Char := Id.run do
  let mut out : Array Char := Array.mkEmpty (bs.size / 2)
  let mut i := 0
  for _ in [0:bs.size + 1] do
    if bs.size < i + 2 then break
    let u := 256 * (bs[i]?.getD 0).toNat + (bs[i + 1]?.getD 0).toNat
    let l := 256 * (bs[i + 2]?.getD 0).toNat + (bs[i + 3]?.getD 0).toNat
    if 0xD800 ≤ u && u < 0xDC00 && 0xDC00 ≤ l && l < 0xE000 && i + 4 ≤ bs.size then
      out := out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)))
      i := i + 4
    else
      out := out.push (if 0xD800 ≤ u && u < 0xE000 then '�' else Char.ofNat u)
      i := i + 2
  return out

/-- The text a PDF string's bytes spell: UTF-16BE after its byte-order mark
(ISO 32000-2 §7.9.2.2), UTF-8 where they are, and Windows-1252 otherwise,
whose letters are PDFDocEncoding's. -/
def pdfText (bs : ByteArray) : Array Char :=
  if bs[0]? == some 0xFE && bs[1]? == some 0xFF then utf16be (bs.extract 2 bs.size)
  else match String.fromUTF8? bs with
    | some s => s.toList.toArray
    | none => cp1252 bs

/-- The strings of PDF syntax, decoded (`pdfLiteral`, `pdfHex`, `pdfText`),
each on a line of its own — except that the strings of one array, a `TJ`
operand that kerning splits mid-word, run together on one line. A comment
runs to the end of its line. -/
def pdfStrings (bs : ByteArray) : Array Char := Id.run do
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut i := 0
  for _ in [0:bs.size + 1] do
    let some b := bs[i]? | break
    if b == 40 then
      let (str, past) := pdfLiteral bs (i + 1)
      out := out.append (pdfText str)
      if depth == 0 then out := out.push '\n'
      i := past
    else if b == 60 && bs[i + 1]? == some 60 then
      i := i + 2
    else if b == 60 then
      match pdfHex bs (i + 1) with
      | some (str, past) =>
        out := out.append (pdfText str)
        if depth == 0 then out := out.push '\n'
        i := past
      | none => i := i + 1
    else if b == 91 then
      depth := depth + 1
      i := i + 1
    else if b == 93 then
      if 0 < depth then
        depth := depth - 1
        if depth == 0 then out := out.push '\n'
      i := i + 1
    else if b == 37 then
      i := findBytes bs i #[10]
    else
      i := i + 1
  return out

/-- A PNG's compressed text (ISO/IEC 15948 §11.3.4: zTXt, and iTXt with its
compression flag set), inflated; its other text is in the file's own bytes. -/
def pngTexts (bs : ByteArray) (cap : Nat) : Array ByteArray := Id.run do
  unless bytesAt bs 0 #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] do return #[]
  let mut out : Array ByteArray := #[]
  let mut i := 8
  for _ in [0:bs.size + 1] do
    if bs.size < i + 12 then break
    let stop := i + 8 + be32 bs i
    if bs.size < stop then break
    if bytesAt bs (i + 4) (ascii "zTXt") then
      let key := findBytes bs (i + 8) #[0]
      if key < stop then
        if let some t := zlibAt bs (key + 2) cap then out := out.push t
    else if bytesAt bs (i + 4) (ascii "iTXt") then
      let key := findBytes bs (i + 8) #[0]
      if key < stop && bs[key + 1]? == some 1 then
        let lang := findBytes bs (key + 3) #[0]
        let shown := findBytes bs (lang + 1) #[0]
        if shown < stop then
          if let some t := zlibAt bs (shown + 1) cap then out := out.push t
    i := stop + 4
  return out

/-- A gzip member's data (RFC 1952 §2.3), past the header fields its flags
declare — an extra field, a file name, a comment, a header check — and
inflated. The name and the comment are in the file's own bytes. -/
def gzipBody (bs : ByteArray) (cap : Nat) : Option ByteArray :=
  if !(bytesAt bs 0 #[0x1F, 0x8B, 8]) then none else
    let flg := (bs[3]?.getD 0).toNat
    let i := 10
    let i := if flg / 4 % 2 == 1 then i + 2 + le16 bs i else i
    let i := if flg / 8 % 2 == 1 then findBytes bs i #[0] + 1 else i
    let i := if flg / 16 % 2 == 1 then findBytes bs i #[0] + 1 else i
    let i := if flg / 2 % 2 == 1 then i + 2 else i
    inflateAt bs i cap

/-- The members of a zip archive (PKWARE's APPNOTE §4.3.7): each local file
header's data, stored or deflated, within `cap` bytes in all. A member's
name is in the file's own bytes. -/
def zipMembers (bs : ByteArray) (cap : Nat) : Array ByteArray := Id.run do
  let sig : Array UInt8 := #[0x50, 0x4B, 0x03, 0x04]
  let mut out : Array ByteArray := #[]
  let mut left := cap
  let mut i := 0
  for _ in [0:bs.size + 1] do
    let j := findBytes bs i sig
    if bs.size ≤ j || left == 0 then break
    let data := j + 30 + le16 bs (j + 26) + le16 bs (j + 28)
    let method := le16 bs (j + 8)
    let size := le32 bs (j + 18)
    let got : Option ByteArray :=
      if method == 8 then inflateAt bs data left
      else if method == 0 && data + size ≤ bs.size && size ≤ left then
        some (bs.extract data (data + size))
      else none
    if let some member := got then
      out := out.push member
      left := left - min left member.size
    i := j + 4
  return out

/-- The content a container wraps, decompressed, within `cap` bytes: a
PDF's zlib streams (`pdfParts`), a PNG's compressed text, a gzip member, a
zip archive's members. Anything else wraps nothing this module reads. -/
def unwrap (bs : ByteArray) (cap : Nat) : Array ByteArray :=
  if isPdf bs then (pdfParts bs cap).2
  else if bytesAt bs 0 #[0x89, 0x50, 0x4E, 0x47] then pngTexts bs cap
  else if bytesAt bs 0 #[0x1F, 0x8B] then (gzipBody bs cap).toArray
  else if bytesAt bs 0 #[0x50, 0x4B, 0x03, 0x04] then zipMembers bs cap
  else #[]

/-- What a blob's compressed content and a PDF's strings read as: each
chunk a container wraps (`unwrap`), and each chunk one of those wraps in
turn, by segment (`segmentReadings`) and with its zero bytes removed
(`cp1252NonZero`); and a PDF's strings (`pdfStrings`), those of its object
syntax and of each inflated stream with no zero byte, which content and
object streams are. -/
def decodedReadings (bs : ByteArray) : Array (Array Char) := Id.run do
  let pdf := isPdf bs
  let parts := if pdf then pdfParts bs decodeCap else (.empty, unwrap bs decodeCap)
  let mut out : Array (Array Char) := #[]
  if pdf then out := out.push (pdfStrings parts.1)
  let both (c : ByteArray) : Array (Array Char) :=
    ((segmentReadings c).map (·.toList.toArray)).push (cp1252NonZero c)
  for c in parts.2 do
    out := out.append (both c)
    if pdf && !hasZero c then out := out.push (pdfStrings c)
    for d in unwrap c decodeCap do
      out := out.append (both d)
  return out

/-- Where one blob holds a term: the lines of text, read by segment
(`segmentReadings`) where no zero byte stands, or `binary` for a hit in
content that is not text — the bytes as lenient UTF-8 and with their zero
bytes removed (`cp1252NonZero`), or what they decompress to
(`decodedReadings`). -/
structure Hits where
  lines : Array Nat
  binary : Bool

def Hits.any (h : Hits) : Bool := h.binary || !h.lines.isEmpty

def Matcher.blobHits (m : Matcher) (bs : ByteArray) : Hits :=
  if m.terms.isEmpty then { lines := #[], binary := false } else
    let zero := hasZero bs
    let lines := if zero then #[] else
      ascendingUnique ((segmentReadings bs).foldl (fun acc r => acc.append (m.textLines r)) #[])
    let raw := zero && (!(m.linesIn (fold (utf8Lenient bs))).isEmpty
      || !(m.linesIn (fold (cp1252NonZero bs))).isEmpty)
    { lines, binary := raw || (decodedReadings bs).any fun r => !(m.charLines r).isEmpty }

/-! ## What the gate reads from git -/

/-- The byte an octal escape `\ooo` spells, read from `cs[i]` on: up to
three digits, and the index past them. -/
def octalAt (cs : Array Char) (i : Nat) : Nat × Nat := Id.run do
  let mut v := 0
  let mut j := i
  for _ in [0:3] do
    let c := charAt cs j
    if '0' ≤ c && c ≤ '7' then
      v := v * 8 + (c.toNat - '0'.toNat)
      j := j + 1
    else break
  return (v % 256, j)

/-- A path as git quotes one in a diff header when it must (`"b/a\"b"`,
`"b/caf\303\251"`): core.quotePath's C escapes and octal bytes read back,
the bytes then read as UTF-8. A path git did not quote is returned as
written. -/
def unquotePath (s : String) : String := Id.run do
  let cs := s.toList.toArray
  unless cs.size ≥ 2 && charAt cs 0 == '"' && charAt cs (cs.size - 1) == '"' do return s
  let mut bytes : ByteArray := .empty
  let mut i := 1
  for _ in [0:cs.size + 1] do
    if cs.size - 1 ≤ i then break
    let c := charAt cs i
    if c == '\\' then
      let d := charAt cs (i + 1)
      if '0' ≤ d && d ≤ '7' then
        let (v, past) := octalAt cs (i + 1)
        bytes := bytes.push v.toUInt8
        i := past
      else
        let e : Char := match d with
          | 'a' => Char.ofNat 7 | 'b' => Char.ofNat 8 | 't' => '\t' | 'n' => '\n'
          | 'v' => Char.ofNat 11 | 'f' => Char.ofNat 12 | 'r' => '\r'
          | other => other
        bytes := bytes.append e.toString.toUTF8
        i := i + 2
    else
      bytes := bytes.append c.toString.toUTF8
      i := i + 1
  return textOfBytes bytes

/-- The new-file path a `+++ ` header names: `b/` and the path, quoted or
not, a path with a space keeping the tab git closes it with; empty for
`/dev/null` or any header without the pinned `b/` prefix. -/
def headerPath (rest : String) : String :=
  let p := unquotePath (if rest.endsWith "\t" then String.ofList rest.toList.dropLast else rest)
  if p.startsWith "b/" then (p.drop 2).toString else ""

/-- Added lines of a unified=0 diff, with file and new-file line number. A
`+++ ` line is a file header only between a `diff --git` line and the first
hunk after it: inside a hunk it is an added line whose own text begins
`++ `, and reading it as a header once dropped the rest of that hunk, home
path and all. A header git quoted is read back (`headerPath`), so a path
with a quote, a backslash or a control character keeps its added lines. -/
def addedLines (diff : String) : Array (String × Nat × String) := Id.run do
  let mut out : Array (String × Nat × String) := #[]
  let mut file := ""
  let mut line := 0
  let mut inHunk := false
  for l in diff.splitOn "\n" do
    if l.startsWith "diff --git " then
      inHunk := false
      file := ""
    else if !inHunk && l.startsWith "+++ " then
      file := headerPath (l.drop 4).toString
    else if l.startsWith "@@" then
      inHunk := true
      let plus := ((l.splitOn "+").getD 1 "").takeWhile Char.isDigit
      line := (plus.toString.toNat?).getD 0
    else if inHunk && l.startsWith "+" then
      if !file.isEmpty then out := out.push (file, line, (l.drop 1).toString)
      line := line + 1
  return out

/-- Added lines joined into runs, one per stretch of consecutive new-file
lines of one file, each with the line it opens on: a phrase wrapped across
two added lines is one phrase to the privacy gate. -/
def addedRuns (lines : Array (String × Nat × String)) : Array (String × Nat × String) := Id.run do
  let mut out : Array (String × Nat × String) := #[]
  let mut a := 0
  for i in [0:lines.size + 1] do
    let opens := match lines[i]?, lines[i - 1]? with
      | some (f, n, _), some (g, k, _) => i == 0 || f != g || n != k + 1
      | some _, none => true
      | none, _ => true
    if opens && a < i then
      let seg := lines.extract a i
      if let some (f, n, _) := seg[0]? then
        out := out.push (f, n, "\n".intercalate (seg.toList.map (·.2.2)))
      a := i
  return out

/-- The commits of a `git log --format=%x00%H -p` answer, each with its
patch: the format opens every commit with a zero byte, which no line of a
text patch holds. -/
def logPatches (out : String) : Array (String × String) := Id.run do
  let mut res : Array (String × String) := #[]
  for piece in (out.splitOn "\x00").drop 1 do
    match piece.splitOn "\n" with
    | sha :: rest => res := res.push (sha.trimAscii.toString, "\n".intercalate rest)
    | [] => pure ()
  return res

/-- The records of a `git log --format=%x00%H -z` answer with one record a
path (`--name-only`) or a numstat row (`--numstat`), each beside its
commit. Under `-z` a commit reads as an empty field, its sha, then its
records, the first opening with the newline that ends the format line. -/
def logRecords (out : String) : Array (String × String) := Id.run do
  let mut res : Array (String × String) := #[]
  let mut sha : Option String := none
  let mut fresh := true
  for f in out.splitOn "\x00" do
    if f.isEmpty then
      fresh := true
      sha := none
    else if fresh then
      sha := some f.trimAscii.toString
      fresh := false
    else if let some h := sha then
      res := res.push (h, if f.startsWith "\n" then (f.drop 1).toString else f)
  return res

/-- The path of a numstat row git counted no lines in — `-` added, `-`
removed: the content it reads as binary. -/
def binaryRow (row : String) : Option String :=
  match row.splitOn "\t" with
  | "-" :: "-" :: rest => some ("\t".intercalate rest)
  | _ => none

/-- A path whose name says its content is compressed, a container
`unwrap` opens or a document format whose text is stored compressed: the
gate reads its content as a blob even where git diffs it as text. -/
def opaqueName (p : String) : Bool :=
  let low := p.toLower
  [".pdf", ".png", ".gz", ".tgz", ".svgz", ".zip", ".docx", ".xlsx", ".pptx", ".odt",
    ".ods", ".odp", ".epub", ".jar"].any fun e => low.endsWith e

/-- The path of a numstat row whose content the gate reads as a blob: one
git counted no lines in (`binaryRow`), or one `opaqueName` names. -/
def blobRow (row : String) : Option String :=
  match binaryRow row with
  | some p => some p
  | none =>
    match row.splitOn "\t" with
    | _ :: _ :: rest@(_ :: _) =>
      let p := "\t".intercalate rest
      if opaqueName p then some p else none
    | _ => none

/-- Distinct, in the order first seen. -/
def uniq (xs : Array String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

/-- `s` cut at the first `sep`, when it holds one. -/
def splitFirst (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | a :: rest@(_ :: _) => some (a, sep.intercalate rest)
  | _ => none

/-! ## The gate's findings over what git answered

Each finding is one line naming where a term stands — a path (masked), a
line, a commit — and never the term. The gate gathers the answers; these
judge them, so the suite can feed them invented ones. -/

/-- Findings in a diff's added lines: each run of consecutive added lines
of one file, read as one text so a wrapped phrase is one phrase. -/
def Matcher.addedFindings (m : Matcher) (diff : String) (lead : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for (file, start, text) in addedRuns (addedLines diff) do
    for n in m.textLines text do
      out := out.push s!"  {lead}{m.maskPath file}:{start + n - 1}"
  return out

/-- Findings in the added lines of a diff given as bytes: those of each of
its readings (`segmentReadings`), each finding once. -/
def Matcher.diffFindings (m : Matcher) (diff : ByteArray) (lead : String) : Array String :=
  uniq ((segmentReadings diff).foldl (fun acc r => acc.append (m.addedFindings r lead)) #[])

/-- Findings in one blob's content at `path`: its lines, or its binary
content. -/
def Matcher.blobFindings (m : Matcher) (path : String) (bs : ByteArray) (lead : String) :
    Array String := Id.run do
  let h := m.blobHits bs
  let mut out : Array String := #[]
  for n in h.lines do
    out := out.push s!"  {lead}{m.maskPath path}:{n}"
  if h.binary then out := out.push s!"  {lead}{m.maskPath path} (its binary content)"
  return out

/-- Findings in paths, each masked. -/
def Matcher.pathFindings (m : Matcher) (paths : Array String) (lead what : String) :
    Array String :=
  paths.filterMap fun p =>
    if m.pathHit p then some s!"  {lead}{m.maskPath p} ({what})" else none

/-- The commit a finding names: its sha, short. -/
def commitLead (sha : String) : String := s!"commit {(sha.take 12).toString}: "

/-- Findings in unpushed commits, from what git answered for them: each
commit's patch (`logPatches`), the paths each adds (`logRecords` of
`--name-only`), and each binary blob it adds or changes with its content.
A term one commit adds and a later one removes is still found in the first,
which is what a landing would publish. -/
def Matcher.commitFindings (m : Matcher) (patches : Array (String × String))
    (paths : Array (String × String)) (blobs : Array ((String × String) × ByteArray)) :
    Array String := Id.run do
  let mut out : Array String := #[]
  for (sha, patch) in patches do
    out := out.append (m.addedFindings patch (commitLead sha))
  for (sha, p) in paths do
    if m.pathHit p then out := out.push s!"  {commitLead sha}{m.maskPath p} (a path it adds)"
  for ((sha, p), bs) in blobs do
    out := out.append (m.blobFindings p bs (commitLead sha))
  return uniq out

/-- Findings in commit messages, from a `git log -z --format=%H%n%B`
answer: each message's lines, the author never read. -/
def Matcher.messageFindings (m : Matcher) (log : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for r in log.splitOn "\x00" do
    if let some (sha, body) := splitFirst r "\n" then
      for n in m.textLines body do
        out := out.push s!"  {commitLead sha}its message, line {n}"
  return out

/-- The commits of a patch log given as bytes (`logPatches`), from each of
its readings (`segmentReadings`): a commit whose patch is not UTF-8 appears
once per reading, which the findings over them read once. -/
def logPatchesOf (out : ByteArray) : Array (String × String) :=
  (segmentReadings out).foldl (fun acc r => acc.append (logPatches r)) #[]

/-- The records of a `-z` log given as bytes (`logRecords`), from each of
its readings. -/
def logRecordsOf (out : ByteArray) : Array (String × String) :=
  (segmentReadings out).foldl (fun acc r => acc.append (logRecords r)) #[]

/-- Findings in commit messages given as bytes (`messageFindings`), over
each of their readings, each finding once. -/
def Matcher.messageFindingsOf (m : Matcher) (log : ByteArray) : Array String :=
  uniq ((segmentReadings log).foldl (fun acc r => acc.append (m.messageFindings r)) #[])

end Privacy
