module

public import LeanTex.Core.Diag
public import LeanTex.Core.Utf8
public import LeanTex.Core.EncodingOption
import LeanTex.Core.EncodingData

/-! # The encoding a file is read in

A file is UTF-8 unless it says otherwise, and it says so two ways. A
byte-order mark names its encoding outright and wins over any label, as the
WHATWG Encoding Standard's decode has it: EF BB BF is UTF-8, FE FF
UTF-16BE, FF FE UTF-16LE. And a LaTeX document declares one with
`\usepackage[<encoding>]{inputenc}`: pdfLaTeX reads its files in the
encoding named, lualatex ignores it and prints U+FFFD for every byte that is
not UTF-8. The engine honours the declaration, a departure from lualatex on
the axis of content fidelity — the page carries the characters the author
typed, as pdfLaTeX prints them (`inputDecodingChecks` holds the probes'
text to pdfLaTeX's) — for the encodings it carries a table for: `latin1`,
`ansinew` and `cp1252` (Windows-1252), `latin9` (ISO 8859-15) and
`applemac` (Mac OS Roman). `latin1` reads as Windows-1252, as the WHATWG
Encoding Standard reads the label: its graphic characters are ISO 8859-1's,
and its 0x80–0x9F block holds the curly quotes, dashes and euro sign a file
labelled latin1 carries in practice, where ISO 8859-1 and pdfLaTeX's
latin1.def have only control codes and an error. `applemac` reads as Apple's
own Mac OS Roman table, which the WHATWG index-macintosh follows, where
pdfLaTeX's applemac.def keeps the table as it stood before 1998 and spells
some bytes by the nearest LaTeX command. By the command it spells: 0xDB is
€ where it is ¤, 0xC6 the increment sign ∆ where it is the Greek Δ, 0xB5
the micro sign µ where it is the Greek μ, 0xB7 and 0xB8 the operators ∑ and
∏ where they are Σ and Π, 0xD7 ◊ where it is ⋄, 0xDA the fraction slash ⁄
where it is /, 0xDE and 0xDF the ligatures ﬁ and ﬂ where they are the
letters fi and fl, and 0xF0 Apple's logo where it is a command LaTeX leaves
undefined. The bytes it declares as math symbols stop pdfLaTeX in text
("Missing $ inserted"), where the engine sets each as the character. glibc's iconv, which a note's help names for saving a file as
UTF-8, reads 0xC6 as the Greek Δ and 0xF0 as a private scalar of its own,
so those two bytes of a file saved that way show differently than here.

The declaration governs every file the document reads, the file that makes
it and those read before it runs included: inputenc makes each byte past
0x7F an active character whose meaning is looked up where it is typeset,
after the preamble, so pdfLaTeX prints every file's bytes in the declared
encoding. It governs a file only where the file's bytes do not say
otherwise. A file that is valid UTF-8 reads as UTF-8
(`Legacy.choose_valid_exact`): a legacy file almost never is, and an editor
re-saving a file as UTF-8 keeps the declaration it no longer means. A file
that is not reads in the declared encoding, byte by byte, as pdfLaTeX reads
it (`Legacy.decodeAll_exact`) — unless its well-formed UTF-8 sequences
outnumber the bytes UTF-8 cannot claim, which makes it a UTF-8 file with a
few stray bytes: those read in the declared encoding, a guess one warning
per file names, and the rest stays UTF-8. A tie goes to the declaration.

What is not text becomes U+FFFD, and one warning per file lists the byte
offsets: a byte sequence that is not UTF-8, a byte the declared encoding
leaves undefined, a UTF-16 code unit that is not a scalar, and U+0000,
which CommonMark replaces (§2.3) and LaTeX refuses as an invalid character.
A line ends at LF, at CR LF and at a CR alone, as TeX Live's reader and
CommonMark (§2.1) end it, so every reader past the door sees LF (`settle`).
U+FFFD needs a face that draws it. Where no face does, it is the ordinary
glyph-coverage loss (E0405), which refuses the PDF until glyph losses ship a
placeholder: pending work, not a guarantee this module makes.

The laws hold the door's own functions. Text that is UTF-8, starts with no
byte-order mark and holds no CR or U+0000 reads unchanged, under any
declaration (`readTex_valid_id`, `readMarkdown_valid_id`); a leading
byte-order mark changes no text, except that it settles a legacy
declaration's choice (`readTex_bom_exact`, `readMarkdown_bom_exact`).

One note per declaration says what it did to each file it governed. It
stands at the declaration, in place of the package's translation note.
-/

namespace LeanTex.Core.Encoding

open Utf8 (Decoded)

/-- The encoding's name as a reader knows it. -/
public def Legacy.name : Legacy → String
  | .windows1252 => "Windows-1252 (Latin-1)"
  | .iso885915 => "ISO 8859-15 (Latin-9)"
  | .macRoman => "Mac OS Roman"

/-- The encoding's name for `iconv`, in the help that re-encodes a file. -/
public def Legacy.iconv : Legacy → String
  | .windows1252 => "WINDOWS-1252"
  | .iso885915 => "ISO-8859-15"
  | .macRoman => "MACINTOSH"

private def Legacy.table : Legacy → Array (Option Char)
  | .windows1252 => EncodingData.windows1252
  | .iso885915 => EncodingData.iso885915
  | .macRoman => EncodingData.macRoman

/-- The character a byte UTF-8 does not claim stands for in the encoding:
the table from 0x80, none where the encoding has no character. A byte below
0x80 is always a UTF-8 sequence of its own, so the decoder never asks. -/
public def Legacy.high (e : Legacy) (b : UInt8) : Option Char :=
  if b < 0x80 then none else (e.table[b.toNat - 0x80]?).join

/-- The character a byte stands for in the encoding: ASCII below 0x80, as
in every encoding here, and the table above. -/
public def Legacy.char (e : Legacy) (b : UInt8) : Option Char :=
  if b < 0x80 then some (Char.ofNat b.toNat) else e.high b

/-- A byte as it reads in the encoding, U+FFFD where it has no character. -/
public def Legacy.charOr (e : Legacy) (b : UInt8) : Char := (e.char b).getD '\uFFFD'

private def Legacy.allGo (e : Legacy) (bs : ByteArray) (i : Nat) (out : String)
    (bad : Array Nat) : String × Array Nat :=
  if h : i < bs.size then
    match e.char bs[i] with
    | some c => e.allGo bs (i + 1) (out.push c) bad
    | none => e.allGo bs (i + 1) (out.push '\uFFFD') (bad.push i)
  else (out, bad)
termination_by bs.size - i

/-- Every byte read in the encoding, as pdfLaTeX reads a file under the
declaration: U+FFFD where the encoding has no character, its offset
reported. -/
public def Legacy.decodeAll (e : Legacy) (bs : ByteArray) : Decoded :=
  let r := e.allGo bs 0 "" #[]
  ⟨r.1, r.2⟩

private theorem Legacy.allGo_text (e : Legacy) (bs : ByteArray) (i : Nat) (out : String)
    (bad : Array Nat) :
    (e.allGo bs i out bad).1.toList = out.toList ++ (bs.data.toList.drop i).map e.charOr := by
  rw [Legacy.allGo.eq_def]
  by_cases h : i < bs.size
  · have hl : i < bs.data.toList.length := by simpa using h
    have hd : bs.data.toList.drop i = bs[i] :: bs.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hl, ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
    rw [dite_eq_left_of_eq_true (eq_true h), hd, List.map_cons]
    cases hc : e.char bs[i] with
    | some c =>
      simp only []
      rw [Legacy.allGo_text e bs (i + 1), String.toList_push]
      simp [Legacy.charOr, hc]
    | none =>
      simp only []
      rw [Legacy.allGo_text e bs (i + 1), String.toList_push]
      simp [Legacy.charOr, hc]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    have : bs.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [this]
    simp
termination_by bs.size - i

/-- **The declared reading is the encoding's table, byte by byte.** Each
byte is the character the encoding gives it, or U+FFFD where it gives none:
no state carries from one byte to the next, which is pdfLaTeX's reading of
a file under `inputenc`. -/
public theorem Legacy.decodeAll_exact (e : Legacy) (bs : ByteArray) :
    (e.decodeAll bs).text.toList = bs.data.toList.map e.charOr := by
  simp [Legacy.decodeAll, Legacy.allGo_text]

/-- What a file's bytes show about their encoding: each well-formed UTF-8
sequence past ASCII, as its offset and length, and each byte past 0x7F that
no well-formed sequence claims. -/
public structure Evidence where
  sequences : Array (Nat × Nat) := #[]
  strays : Array Nat := #[]
  deriving Repr, BEq

private def evidenceGo (bs : ByteArray) (i : Nat) (ev : Evidence) : Evidence :=
  if h : i < bs.size then
    if bs[i] < 0x80 then evidenceGo bs (i + 1) ev
    else match bs.utf8DecodeChar? i with
      | some c =>
        evidenceGo bs (i + c.utf8Size) { ev with sequences := ev.sequences.push (i, c.utf8Size) }
      | none => evidenceGo bs (i + 1) { ev with strays := ev.strays.push i }
  else ev
termination_by bs.size - i
decreasing_by
  · omega
  · have := c.utf8Size_pos; omega
  · omega

/-- The evidence in the bytes from `start`. -/
public def evidence (bs : ByteArray) (start : Nat) : Evidence := evidenceGo bs start {}

/-- Does the evidence say UTF-8? Its well-formed sequences outnumber the
bytes it cannot claim; a tie is no evidence, and goes to the declaration. -/
public def Evidence.utf8Wins (ev : Evidence) : Bool := ev.sequences.size > ev.strays.size

/-- How a file's bytes were read. -/
public inductive Reading where
  /-- No byte past 0x7F: every encoding here reads it alike. -/
  | ascii
  | utf8
  /-- UTF-16, by its byte-order mark: big-endian or not. -/
  | utf16 (big : Bool)
  | legacy (e : Legacy)
  /-- Not UTF-8, and in no encoding the engine reads: read as UTF-8, each
  byte it does not claim replaced. -/
  | replaced
  deriving Repr, BEq, DecidableEq

public def Reading.name : Reading → String
  | .ascii => "ASCII"
  | .utf8 | .replaced => "UTF-8"
  | .utf16 true => "UTF-16BE"
  | .utf16 false => "UTF-16LE"
  | .legacy e => e.name

/-- Does the reading not depend on the declaration: no byte past 0x7F, or
UTF-16, which its byte-order mark names? -/
public def Reading.alike : Reading → Bool
  | .ascii | .utf16 _ => true
  | .utf8 | .legacy _ | .replaced => false

/-- Is a decoded text more than ASCII? A character past U+007F takes more
than one byte, so the count of characters falls short of the bytes exactly
then; the runtime keeps both counts, so this asks no pass over the text. -/
private def beyondAscii (t : String) : Bool := t.length != t.utf8ByteSize

/-- The offset of each 0x00 from `start`: U+0000 in UTF-8 and in every 8-bit
encoding here, and never part of a longer sequence. -/
private def nulOffsets (bytes : ByteArray) (start : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for h : i in [start:bytes.size] do
    if bytes[i] == 0 then out := out.push i
  return out

/-- A reading under a legacy declaration: the text, how the file read, the
runs of the other reading's evidence the choice overrode — offset and
length — and whether the reading is UTF-8 by its byte-order mark alone. -/
public structure Chosen where
  decoded : Decoded
  reading : Reading
  minority : Array (Nat × Nat)
  byMark : Bool
  deriving Repr

/-- **The reading a declaration gets.** Bytes that are UTF-8 read as UTF-8;
otherwise the evidence decides — UTF-8 with the declared encoding for its
stray bytes when it says UTF-8 or a byte-order mark does, the declared
encoding for every byte otherwise. -/
public def Legacy.choose (e : Legacy) (bs : ByteArray) : Chosen :=
  if bs.validateUTF8 then
    let d := Utf8.read bs
    ⟨d, if beyondAscii d.text then .utf8 else .ascii, #[], false⟩
  else
    let k := Utf8.bomLen bs
    let ev := evidence bs k
    if k > 0 || ev.utf8Wins then
      let read := ev.strays.filter fun o => (e.high (bs[o]?.getD 0)).isSome
      ⟨Utf8.readWith e.high bs, .utf8, read.map ((·, 1)), !ev.utf8Wins⟩
    else ⟨e.decodeAll bs, .legacy e, ev.sequences, false⟩

/-- **A declaration never changes a file that is UTF-8.** Its reading under
any legacy declaration is its UTF-8 reading, with no run overridden. -/
public theorem Legacy.choose_valid_exact (e : Legacy) (bs : ByteArray)
    (h : bs.validateUTF8 = true) :
    (e.choose bs).decoded = Utf8.read bs ∧ (e.choose bs).minority = #[] := by
  simp [Legacy.choose, h]

/-- A document's input-encoding declaration: the option as written, what it
names, the command that loads the package, and where it is written. -/
public structure Declared where
  option : String
  choice : Choice
  /-- `usepackage` or `RequirePackage`, as the document spells the load. -/
  loader : String
  span : Span
  deriving Repr, BEq

/-- The declaration an `inputenc` load with these options makes, or none
when it names no encoding. -/
public def ofCall (loader file : String) (pos : Pos) (options : String) : Option Declared :=
  (lastOption? options).map fun o => ⟨o, ofOption o, loader, ⟨file, pos⟩⟩

/-- The declaration as written, quoted for a message. -/
private def Declared.spelling (d : Declared) : String :=
  s!"'\\{d.loader}[{d.option}]\{inputenc}'"

private def bytesAtGo (bs pat : ByteArray) (i k : Nat) : Bool :=
  if h : k < pat.size then
    if bs[i + k]?.getD 0 != pat[k] then false else bytesAtGo bs pat i (k + 1)
  else true
termination_by pat.size - k

/-- Does `pat` occur in the bytes at `i`? -/
private def bytesAt (bs : ByteArray) (i : Nat) (pat : ByteArray) : Bool :=
  i + pat.size ≤ bs.size && bytesAtGo bs pat i 0

private def mentionsGo (bs pat : ByteArray) (first : UInt8) (i : Nat) : Bool :=
  if h : i < bs.size then
    if bs[i] == first && bytesAt bs i pat then true else mentionsGo bs pat first (i + 1)
  else false
termination_by bs.size - i

/-- Do the bytes mention `pat` anywhere? -/
private def mentions (bs : ByteArray) (pat : ByteArray) : Bool :=
  match pat[0]? with
  | some first => mentionsGo bs pat first 0
  | none => true

/-- The offset of the first line end at or past `i`, LF or CR: where a
comment ends. -/
private def lineEnd (bs : ByteArray) (i : Nat) : Option Nat := Id.run do
  for h : j in [i:bs.size] do
    if bs[j] == 0x0A || bs[j] == 0x0D then return some j
  return none

private def isLetter (b : UInt8) : Bool := (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A)

private def isBlank (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

/-- The text from `i` up to the first `close`, and the offset past it. -/
private def upTo (bs : ByteArray) (i : Nat) (close : UInt8) : String × Nat := Id.run do
  for j in [i:bs.size] do
    if bs[j]? == some close then
      return ((Utf8.decode (bs.extract i j)).text, j + 1)
  return ((Utf8.decode (bs.extract i bs.size)).text, bs.size)

private def skipBlanks (bs : ByteArray) (i : Nat) : Nat := Id.run do
  for j in [i:bs.size] do
    unless isBlank (bs[j]?.getD 0) do return j
  return bs.size

/-- Option text with each comment dropped: a `%` to the end of its line. -/
private def uncommented (s : String) : String :=
  (s.foldl (fun (acc : String × Bool) c =>
    if c == '\n' || c == '\r' then (acc.1.push c, false)
    else if acc.2 || c == '%' then (acc.1, true)
    else (acc.1.push c, false)) ("", false)).1

/-- The package call at `i`, a backslash, where it loads `inputenc`: the
command's name and its options. -/
private def callAt (bs : ByteArray) (i : Nat) : Option (String × String) := do
  let loaders := [("usepackage", "\\usepackage".toUTF8),
    ("RequirePackage", "\\RequirePackage".toUTF8)]
  let (loader, spelled) ← loaders.find? (bytesAt bs i ·.2)
  let j := i + spelled.size
  guard !isLetter (bs[j]?.getD 0)
  let j := skipBlanks bs j
  let (opts, j) := if bs[j]? == some 0x5B then upTo bs (j + 1) 0x5D else ("", j)
  let j := skipBlanks bs j
  guard (bs[j]? == some 0x7B)
  let (pkgs, _) := upTo bs (j + 1) 0x7D
  guard ((((uncommented pkgs).splitOn ",").map (·.trimAscii.toString)).contains "inputenc")
  return (loader, uncommented opts)

/-- **The declaration a file makes for itself**, read from its bytes before
any lexing, so the file can be read in it the first time: the first
`inputenc` load before `\begin{document}`, outside comments. The
declaration is ASCII, whatever the encoding of the rest. It is a guess the
driver checks against execution — a load in a skipped branch or through a
macro is execution's to find — so the scan is only as careful as the
common spelling needs, and a file that never mentions `inputenc` is not
scanned at all. -/
public def declaredIn (file : String) (bytes : ByteArray) : Option Declared := Id.run do
  unless mentions bytes "inputenc".toUTF8 do return none
  let doc := "\\begin{document}".toUTF8
  let mut line := 1
  let mut col := 1
  let mut i := 0
  for _ in [0:bytes.size + 1] do
    if h : i < bytes.size then
      let b := bytes[i]
      if b == 0x0A || b == 0x0D then
        line := line + 1
        col := 1
        i := if b == 0x0D && bytes[i + 1]? == some 0x0A then i + 2 else i + 1
      else if b == 0x25 then
        match lineEnd bytes i with
        | some j => i := j
        | none => return none
      else if b == 0x5C then
        if bytesAt bytes i doc then return none
        if let some (loader, opts) := callAt bytes i then
          return ofCall loader file { line, col } opts
        i := i + 2
        col := col + 2
      else
        i := i + 1
        col := col + 1
    else return none
  return none

/-- The UTF-16 a byte-order mark names: `some true` for big-endian. -/
public def utf16Mark? (bs : ByteArray) : Option Bool :=
  match (bs[0]? : Option UInt8), (bs[1]? : Option UInt8) with
  | some 0xFE, some 0xFF => some true
  | some 0xFF, some 0xFE => some false
  | _, _ => none

private def unitAt (big : Bool) (bs : ByteArray) (i : Nat) : Option Nat :=
  match bs[i]?, bs[i + 1]? with
  | some a, some b => some (if big then a.toNat * 256 + b.toNat else b.toNat * 256 + a.toNat)
  | _, _ => none

/-- UTF-16 from `i`, as the WHATWG decoder reads it: a surrogate pair is one
scalar, and a lone surrogate or a trailing odd byte is U+FFFD, its offset and
length reported. U+0000 stays for `settle`, its offset reported apart. -/
private def utf16Go (big : Bool) (bs : ByteArray) (i : Nat) (out : String)
    (bad : Array (Nat × Nat)) (nuls : Array Nat) : String × Array (Nat × Nat) × Array Nat :=
  if i < bs.size then
    match unitAt big bs i with
    | none => (out.push '\uFFFD', bad.push (i, bs.size - i), nuls)
    | some u =>
      if 0xD800 ≤ u && u ≤ 0xDBFF then
        match unitAt big bs (i + 2) with
        | some v =>
          if 0xDC00 ≤ v && v ≤ 0xDFFF then
            utf16Go big bs (i + 4)
              (out.push (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00)))) bad nuls
          else utf16Go big bs (i + 2) (out.push '\uFFFD') (bad.push (i, 2)) nuls
        | none => utf16Go big bs (i + 2) (out.push '\uFFFD') (bad.push (i, 2)) nuls
      else if 0xDC00 ≤ u && u ≤ 0xDFFF then
        utf16Go big bs (i + 2) (out.push '\uFFFD') (bad.push (i, 2)) nuls
      else if u == 0 then utf16Go big bs (i + 2) (out.push '\x00') bad (nuls.push i)
      else utf16Go big bs (i + 2) (out.push (Char.ofNat u)) bad nuls
  else (out, bad, nuls)
termination_by bs.size - i

/-- The offset past a UTF-16 file's marks: its byte-order mark and every
U+FEFF after it, which a tool doubled and is never content. -/
private def utf16Start (big : Bool) (bs : ByteArray) : Nat := Id.run do
  let mut i := 2
  for _ in [0:bs.size] do
    if unitAt big bs i == some 0xFEFF then i := i + 2 else break
  return i

/-- Is there a CR or a U+0000 at or past byte `i` of the text? An ASCII byte
of a text's UTF-8 is that character (`Utf8.ascii_byte_mem`), so the
bytes answer for the characters. -/
private def unsettledFrom (t : String) (i : Nat) : Bool :=
  if h : i < t.utf8ByteSize then
    let b := t.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using h)
    if b == 0x0D || b == 0x00 then true else unsettledFrom t (i + 1)
  else false
termination_by t.utf8ByteSize - i

private def settleStep (acc : String × Bool) (c : Char) : String × Bool :=
  if c == '\n' then (if acc.2 then (acc.1, false) else (acc.1.push '\n', false))
  else if c == '\r' then (acc.1.push '\n', true)
  else if c == '\x00' then (acc.1.push '\uFFFD', false)
  else (acc.1.push c, false)

/-- `settleStep` over the text's bytes from `i`, `run` the first byte not
yet copied and `cr` saying whether the byte before was a CR: CR, LF and
0x00 are one-byte characters in UTF-8 and never part of a longer one, so
rewriting them byte by byte keeps the text UTF-8, which the validation that
ends `settleBytes` confirms. The bytes between them are copied a run at a
time. -/
private def settleGo (bs : ByteArray) (i run : Nat) (out : ByteArray) (cr : Bool) : ByteArray :=
  if h : i < bs.size then
    let b := bs[i]
    if b == 0x0D then
      settleGo bs (i + 1) (i + 1) ((bs.copySlice run out out.size (i - run) false).push 0x0A) true
    else if b == 0x0A && cr then settleGo bs (i + 1) (i + 1) out false
    else if b == 0x00 then
      settleGo bs (i + 1) (i + 1)
        ((((bs.copySlice run out out.size (i - run) false).push 0xEF).push 0xBF).push 0xBD) false
    else settleGo bs (i + 1) run out false
  else bs.copySlice run out out.size (bs.size - run) false
termination_by bs.size - i

private def settleBytes (t : String) : Option String :=
  let bs := t.toUTF8
  String.fromUTF8? (settleGo bs 0 0 (ByteArray.emptyWithCapacity bs.size) false)

/-- `settle`'s work, where the scan for a CR or a U+0000 has answered: the
door reads that answer once, for the text and for the offsets it names. -/
private def settleIf (dirty : Bool) (t : String) : String :=
  if dirty then
    match settleBytes t with
    | some s => s
    | none => (t.foldl settleStep ("", false)).1
  else t

/-- **Lines end at LF, and U+0000 is U+FFFD.** A CR LF and a CR alone end a
line as LF does: TeX Live's reader ends an input line at each, and
CommonMark 0.31.2 §2.1 defines a line ending as exactly these three. U+0000
is U+FFFD, as CommonMark §2.3 has it and as no encoding here reads it as
text. Every reader past the door sees LF and no U+0000; text with neither
CR nor U+0000 is taken as it stands (`settle_id`). -/
public def settle (t : String) : String := settleIf (unsettledFrom t 0) t

private theorem unsettledFrom_mem (t : String) (i : Nat) (h : unsettledFrom t i = true) :
    '\r' ∈ t.toList ∨ '\x00' ∈ t.toList := by
  rw [unsettledFrom.eq_def] at h
  split at h
  · rename_i hi
    have hs : i < t.toUTF8.size := by
      rw [String.toUTF8_eq_toByteArray, String.size_toByteArray]; exact hi
    have hb : t.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using hi) =
        t.toUTF8[i]'hs := by
      simp [String.getUTF8Byte_eq_getElem, String.toUTF8_eq_toByteArray]
    simp only [hb] at h
    split at h
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | hc
      · exact Or.inl (Utf8.ascii_byte_mem t '\r' (by decide) i hs (by rw [hc]; rfl))
      · exact Or.inr (Utf8.ascii_byte_mem t '\x00' (by decide) i hs (by rw [hc]; rfl))
    · exact unsettledFrom_mem t (i + 1) h
  · exact absurd h (by simp)
termination_by t.utf8ByteSize - i

/-- **Text with no CR and no U+0000 is taken as it stands.** -/
public theorem settle_id (t : String) (hcr : '\r' ∉ t.toList) (hnul : '\x00' ∉ t.toList) :
    settle t = t := by
  have h : unsettledFrom t 0 = false := by
    cases hu : unsettledFrom t 0 with
    | false => rfl
    | true =>
      rcases unsettledFrom_mem t 0 hu with h | h
      · exact absurd h hcr
      · exact absurd h hnul
  simp [settle, settleIf, h]

/-- The position a lexer gives the character after `text`, its lines ended
as `settle` ends them. -/
private def posAfter (text : String) : Pos :=
  (text.foldl (fun (acc : Pos × Bool) c =>
    if c == '\n' then (if acc.2 then acc.1 else acc.1.next true, false)
    else if c == '\r' then (acc.1.next true, true)
    else (acc.1.next false, false)) ({}, false)).1

private def hexByte (b : UInt8) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)
  String.ofList ['0', 'x', digit (b.toNat / 16), digit (b.toNat % 16)]

/-- The bytes of a run, spelled for a message. -/
private def hexRun (bytes : ByteArray) (o n : Nat) : String :=
  " ".intercalate ((List.range n).map fun k => hexByte (bytes[o + k]?.getD 0))

/-- The runs a message names: the first three, each with its bytes where
`withBytes`, and how many more. -/
private def runList (bytes : ByteArray) (runs : Array (Nat × Nat)) (withBytes : Bool) : String :=
  let shown := (runs.extract 0 3).toList.map fun (o, n) =>
    if withBytes then s!"{o} ({hexRun bytes o n})" else s!"{o}"
  let more := runs.size - 3
  match shown.reverse with
  | [] => ""
  | [one] => one
  | last :: rest =>
    if more > 0 then String.intercalate ", " shown ++ s!" and {more} more"
    else String.intercalate ", " rest.reverse ++ " and " ++ last

/-- A run one U+FFFD stands for: its offset, its length, and whether it is
U+0000, which every encoding here encodes and none reads as text. -/
private structure Run where
  offset : Nat
  len : Nat
  nul : Bool

/-- The replaced runs and the U+0000 offsets, merged in offset order: each
array is in reading order, and no U+0000 is inside a replaced run. -/
private def runsOf (bad : Array (Nat × Nat)) (nuls : Array Nat) (nulLen : Nat) :
    Array Run := Id.run do
  let mut out : Array Run := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:bad.size + nuls.size] do
    match bad[i]?, nuls[j]? with
    | some (o, n), some p =>
      if o ≤ p then
        out := out.push ⟨o, n, false⟩
        i := i + 1
      else
        out := out.push ⟨p, nulLen, true⟩
        j := j + 1
    | some (o, n), none =>
      out := out.push ⟨o, n, false⟩
      i := i + 1
    | none, some p =>
      out := out.push ⟨p, nulLen, true⟩
      j := j + 1
    | none, none => break
  return out

/-- Do the U+0000 of a UTF-8 reading look like UTF-16 with no byte-order
mark: at least one byte in eight, nearly all on one parity? -/
private def looksUtf16 (size : Nat) (nuls : Array Nat) : Bool :=
  let even := (nuls.filter (· % 2 == 0)).size
  let odd := nuls.size - even
  !nuls.isEmpty && nuls.size * 8 ≥ size && 10 * max even odd ≥ 9 * nuls.size

private def utf16Help : String :=
  "the file looks like UTF-16 with no byte-order mark: save it as UTF-8"

private def nulAdvice : String := "remove the U+0000 characters: no encoding reads them as text"

/-- W0002, once per file: every run a reading replaced, U+0000 included,
each standing as one U+FFFD; positioned at the first. -/
private def replacedDiag (file encoding help : String) (bytes : ByteArray) (runs : Array Run)
    (pos : Pos) : Diag :=
  let message := match runs.toList with
    | [r] =>
      if r.nul then s!"U+0000 at offset {r.offset} is not text"
      else if r.len == 1 then
        s!"byte {hexByte (bytes[r.offset]?.getD 0)} at offset {r.offset} is not text in {encoding}"
      else s!"the bytes {hexRun bytes r.offset r.len} at offset {r.offset} are not text in \
{encoding}"
    | _ =>
      if runs.all (·.nul) then
        s!"{runs.size} U+0000 characters are not text, at offsets \
{runList bytes (runs.map fun r => (r.offset, r.len)) false}"
      else s!"{runs.size} byte sequences are not text in {encoding}, at offsets \
{runList bytes (runs.map fun r => (r.offset, r.len)) true}"
  { Diag.of .W0002 message (some ⟨file, pos⟩) (help := some help)
      (subject := some ("input-bytes:" ++ file)) (recovery := some (.replacedBy "U+FFFD")) with
    offsets := runs.map (·.offset) }

/-- The warning a reading owes for what it replaced, if anything: `prefixText`
reads the bytes before an offset the way the file was read, which places
the warning, and `help` is read only where a warning needs it. -/
private def lossesDiag (file encoding : String) (bytes : ByteArray) (runs : Array Run)
    (prefixText : Nat → String) (help : Unit → String) : Array Diag :=
  match runs[0]? with
  | none => #[]
  | some r => #[replacedDiag file encoding (help ()) bytes runs (posAfter (prefixText r.offset))]

/-- The help for what a UTF-8 reading replaced, by what the bytes show: no
byte-order mark on UTF-16, U+0000 alone, or `bad` for bytes that are not
UTF-8. -/
private def helpFor (runs : Array Run) (size : Nat) (bad : Unit → String) : String :=
  if looksUtf16 size ((runs.filter (·.nul)).map (·.offset)) then utf16Help
  else if runs.any (!·.nul) then bad ()
  else nulAdvice

/-- A file's bytes as text: the text, the losses the reading names, how the
file read, and the runs its reading took against the other reading's
evidence — in a UTF-8 reading under a legacy declaration, the stray bytes it
read as declared; in a legacy reading, the sequences that are well-formed
UTF-8 too. -/
public structure FileText where
  text : String
  diags : Array Diag
  reading : Reading
  minority : Array (Nat × Nat) := #[]
  deriving Repr

/-- UTF-16 by its mark: the text and its losses. -/
private def utf16Text (file : String) (big : Bool) (bytes : ByteArray) : FileText :=
  let start := utf16Start big bytes
  let (text, bad, nuls) := utf16Go big bytes start "" #[] #[]
  let enc := (Reading.utf16 big).name
  let runs := runsOf bad nuls 2
  let help := fun (_ : Unit) =>
    if runs.any (!·.nul) then s!"correct the code units at those offsets: they are not text in {enc}"
    else nulAdvice
  { text := settle text
    diags := lossesDiag file enc bytes runs
      (fun o => (utf16Go big (bytes.extract 0 o) start "" #[] #[]).1) help
    reading := .utf16 big }

/-- The UTF-8 reading, without a declaration that names a table: `other`
is the advice for a file that is evidently in another encoding. A file
whose well-formed UTF-8 sequences are at least as many as its stray bytes
is not evidently in another one: an 8-bit declaration would read those
sequences as two or three characters each, so the advice there corrects
the stray bytes instead. -/
private def utf8Text (file other : String) (bytes : ByteArray) : FileText :=
  let d := Utf8.read bytes
  let start := Utf8.bomLen bytes
  let dirty := unsettledFrom d.text 0
  let nuls := if dirty then nulOffsets bytes start else #[]
  let ev := if d.bad.isEmpty then {} else evidence bytes start
  let wins := !d.bad.isEmpty && ev.utf8Wins
  let mostlyUtf8 := !ev.sequences.isEmpty && ev.sequences.size ≥ ev.strays.size
  let runs := runsOf (d.bad.map fun o => (o, Utf8.replacedRun bytes o)) nuls 1
  { text := settleIf dirty d.text
    diags := lossesDiag file "UTF-8" bytes runs (fun o => (Utf8.read (bytes.extract 0 o)).text)
      fun _ => helpFor runs (bytes.size - start) fun _ =>
        if mostlyUtf8 then "correct the bytes at those offsets: the rest of the file is UTF-8"
        else other
    reading := if !d.bad.isEmpty then (if wins then .utf8 else .replaced)
      else if beyondAscii d.text then .utf8 else .ascii }

/-- W0004: the stray bytes a UTF-8 reading under a legacy declaration read
as declared, a guess, at the first of them. -/
private def strayDiag (file : String) (e : Legacy) (bytes : ByteArray) (c : Chosen)
    (prefixText : Nat → String) : Array Diag :=
  match c.minority[0]? with
  | none => #[]
  | some (first, _) =>
    let rest := if c.byMark then "in a file its byte-order mark calls UTF-8"
      else "in a file otherwise UTF-8"
    let message := match c.minority.toList with
      | [(o, _)] => s!"byte {hexByte (bytes[o]?.getD 0)} at offset {o} is read as {e.name}, \
as declared, {rest}"
      | _ => s!"{c.minority.size} bytes are read as {e.name}, as declared, {rest}, at offsets \
{runList bytes c.minority true}"
    #[{ Diag.of .W0004 message (some ⟨file, posAfter (prefixText first)⟩)
          (help := some "retype the characters at those offsets in UTF-8: the rest of the \
file is UTF-8")
          (subject := some ("input-mixed:" ++ file)) with
        offsets := c.minority.map (·.1) }]

/-- The reading under a legacy declaration, UTF-8 or the declared one, by
the evidence (`Legacy.choose`). -/
private def legacyText (file : String) (e : Legacy) (bytes : ByteArray) : FileText :=
  let c := e.choose bytes
  let start := Utf8.bomLen bytes
  let dirty := unsettledFrom c.decoded.text 0
  let nuls := if dirty then nulOffsets bytes start else #[]
  let help := fun (enc : String) (runs : Array Run) (_ : Unit) =>
    helpFor runs (bytes.size - start) fun _ =>
      s!"correct the bytes at those offsets: they have no character in {enc}"
  let diags := match c.reading with
    | .legacy _ =>
      let runs := runsOf (c.decoded.bad.map ((·, 1))) nuls 1
      lossesDiag file e.name bytes runs (fun o => (e.decodeAll (bytes.extract 0 o)).text)
        (help e.name runs)
    | _ =>
      let enc := s!"UTF-8 or {e.name}"
      let runs := runsOf (c.decoded.bad.map fun o => (o, Utf8.replacedRun bytes o)) nuls 1
      let prefixText := fun o => (Utf8.readWith e.high (bytes.extract 0 o)).text
      lossesDiag file enc bytes runs prefixText (help enc runs) ++
        strayDiag file e bytes c prefixText
  { text := settleIf dirty c.decoded.text, diags, reading := c.reading, minority := c.minority }

private def texHelp : String :=
  "save the file as UTF-8, or name its encoding: \\usepackage[latin1]{inputenc} reads Latin-1"

/-- **A tex file's text**: in the encoding its byte-order mark names if it
has one, else UTF-8, or the legacy encoding its document declares where
the bytes do not say UTF-8 (`Legacy.choose`). -/
public def readTex (declared : Option Declared) (file : String) (bytes : ByteArray) : FileText :=
  match utf16Mark? bytes with
  | some big => utf16Text file big bytes
  | none =>
    match declared with
    | some d =>
      match d.choice with
      | .legacy e => legacyText file e bytes
      | .unread =>
        utf8Text file (s!"{d.spelling} names an encoding this engine does not read; " ++
          s!"save the file as UTF-8: `iconv -f {d.option} -t UTF-8`") bytes
      | .utf8 => utf8Text file (s!"{d.spelling} reads UTF-8: save the file as UTF-8, or name \
its encoding in that load, as \\usepackage[latin1]\{inputenc} reads Latin-1") bytes
    | none => utf8Text file texHelp bytes

/-- **A tex document's own text**, and the declaration it was read under:
the one its preamble makes (`declaredIn`), honoured before the body is
lexed. A declaration execution finds elsewhere — through an `\input`, a
macro, or not at all where the preamble's sits in a branch never taken —
is the driver's to settle, after the inputs are read. -/
public def readDocument (file : String) (bytes : ByteArray) : FileText × Option Declared :=
  let early := declaredIn file bytes
  (readTex early file bytes, early)

/-- **A markdown file's text**: in the encoding its byte-order mark names if
it has one, else UTF-8, as CommonMark reads it. -/
public def readMarkdown (file : String) (bytes : ByteArray) : FileText :=
  match utf16Mark? bytes with
  | some big => utf16Text file big bytes
  | none => utf8Text file "save the file as UTF-8: `iconv -f <encoding> -t UTF-8`" bytes

private theorem utf16Mark_bom (bs : ByteArray) : utf16Mark? (Utf8.bom ++ bs) = none := by
  have hs : Utf8.bom.size = 3 := rfl
  have h0 : (Utf8.bom ++ bs)[0]? = some 0xEF := by
    rw [getElem?_pos _ 0 (by rw [ByteArray.size_append, hs]; omega),
      ByteArray.getElem_append_left (by rw [hs]; omega)]
    rfl
  simp [utf16Mark?, h0]

private theorem utf16Mark_text (s : String) : utf16Mark? s.toUTF8 = none := by
  unfold utf16Mark?
  split
  · rename_i h _
    exact absurd (Utf8.toUTF8_head_between s _ h) (by decide)
  · rename_i h _
    exact absurd (Utf8.toUTF8_head_between s _ h) (by decide)
  · rfl

/-- Without a declaration that names a table, a file with no UTF-16 mark
reads as UTF-8, its lines and U+0000 settled. -/
private theorem readTex_utf8 (d : Option Declared) (file : String) (bs : ByteArray)
    (hm : utf16Mark? bs = none) (hd : ∀ x e, d = some x → x.choice ≠ .legacy e) :
    (readTex d file bs).text = settle (Utf8.read bs).text := by
  unfold readTex
  rw [hm]
  rcases d with _ | x
  · rfl
  · simp only
    split
    · rename_i e he
      exact absurd he (hd x e rfl)
    · rfl
    · rfl

/-- **A tex file that is UTF-8, starts with no byte-order mark and holds no
CR or U+0000 reads as written, under any declaration.** The door changes
nothing a reader wrote: a declaration's table is never consulted for a file
that is UTF-8. -/
public theorem readTex_valid_id (d : Option Declared) (file : String) (s : String)
    (hhead : s.toList.head? ≠ some '\uFEFF') (hcr : '\r' ∉ s.toList)
    (hnul : '\x00' ∉ s.toList) : (readTex d file s.toUTF8).text = s := by
  have hr : (Utf8.read s.toUTF8).text = s := by rw [Utf8.read_valid_id s hhead]
  have hv : s.toUTF8.validateUTF8 = true :=
    ByteArray.validateUTF8_eq_true_iff.mpr (by simpa using s.isValidUTF8)
  by_cases hl : ∃ x e, d = some x ∧ x.choice = .legacy e
  · obtain ⟨x, e, rfl, he⟩ := hl
    unfold readTex
    rw [utf16Mark_text]
    simp only [he]
    show settle (e.choose s.toUTF8).decoded.text = s
    rw [(Legacy.choose_valid_exact e _ hv).1, hr, settle_id s hcr hnul]
  · rw [readTex_utf8 d file _ (utf16Mark_text s) (fun x e hx he => hl ⟨x, e, hx, he⟩), hr,
      settle_id s hcr hnul]

/-- **A leading byte-order mark changes no tex text** where no declaration
names a table, whose choice a mark settles: the text is the text of the file
without it. -/
public theorem readTex_bom_exact (d : Option Declared) (file : String) (bs : ByteArray)
    (hm : utf16Mark? bs = none) (hd : ∀ x e, d = some x → x.choice ≠ .legacy e) :
    (readTex d file (Utf8.bom ++ bs)).text = (readTex d file bs).text := by
  rw [readTex_utf8 d file _ (utf16Mark_bom bs) hd, readTex_utf8 d file bs hm hd,
    Utf8.read_bom_exact]

/-- **A markdown file that is UTF-8, starts with no byte-order mark and
holds no CR or U+0000 reads as written.** -/
public theorem readMarkdown_valid_id (file : String) (s : String)
    (hhead : s.toList.head? ≠ some '\uFEFF') (hcr : '\r' ∉ s.toList)
    (hnul : '\x00' ∉ s.toList) : (readMarkdown file s.toUTF8).text = s := by
  unfold readMarkdown
  rw [utf16Mark_text]
  show settle (Utf8.read s.toUTF8).text = s
  rw [Utf8.read_valid_id s hhead, settle_id s hcr hnul]

/-- **A leading byte-order mark changes no markdown text.** -/
public theorem readMarkdown_bom_exact (file : String) (bs : ByteArray)
    (hm : utf16Mark? bs = none) :
    (readMarkdown file (Utf8.bom ++ bs)).text = (readMarkdown file bs).text := by
  unfold readMarkdown
  rw [utf16Mark_bom, hm]
  show settle (Utf8.read (Utf8.bom ++ bs)).text = settle (Utf8.read bs).text
  rw [Utf8.read_bom_exact]

/-- One file a document read: the declaration it was read under, if any,
how it read, and the runs its reading took against the other reading's
evidence. -/
public structure Read where
  file : String
  under : Option Declared
  reading : Reading
  minority : Array (Nat × Nat)
  deriving Repr, BEq

/-- What reading a file's bytes made of them, under `under`. -/
public def FileText.read (t : FileText) (file : String) (under : Option Declared) : Read :=
  ⟨file, under, t.reading, t.minority⟩

/-- What the decoding door did across a document's files: the declaration
in force — the first `inputenc` load executed, since a later load's options
are not applied — and each file read, once, in reading order. -/
public structure Ledger where
  declared : Option Declared := none
  reads : Array Read := #[]
  deriving Repr, BEq

/-- The ledger with one more file read; a file read again is the file
already read. -/
public def Ledger.record (l : Ledger) (r : Read) : Ledger :=
  if l.reads.any (·.file == r.file) then l else { l with reads := l.reads.push r }

/-- A declaration as what it reads a file as: no declaration reads as a
UTF-8 one does. -/
private def keyOf (d : Option Declared) : Choice := (d.map (·.choice)).getD .utf8

/-- **Was a file read under a declaration other than the one in force,**
where that changes what it reads as? Then it is read again under the one in
force: the declaration governs every file of the document, whenever it ran. -/
public def Ledger.stale (l : Ledger) : Bool :=
  l.reads.any fun r => !r.reading.alike && keyOf r.under != keyOf l.declared

/-- Names as a message lists them: quoted, the first three and how many
more. -/
private def names (files : Array String) : String :=
  let q := files.toList.map (s!"'{·}'")
  match q.reverse with
  | [] => ""
  | [one] => one
  | last :: rest =>
    if files.size > 3 then String.intercalate ", " (q.take 3) ++ s!" and {files.size - 3} more"
    else String.intercalate ", " rest.reverse ++ " and " ++ last

/-- A verb agreeing with how many files it says something of. -/
private def agree (files : Array String) (singular plural : String) : String :=
  if files.size == 1 then singular else plural

private def offsetList (runs : Array (Nat × Nat)) : String :=
  runList ByteArray.empty runs false

private def alikeHelp : String := "delete the declaration: every file it governs reads alike without it"

/-- The note under a legacy declaration: each file as it read, and a help
that saves the files that need the declaration before deleting it. -/
private def legacyNote (d : Declared) (e : Legacy) (reads : Array Read) :
    String × String :=
  let files (p : Read → Bool) : Array String := (reads.filter p).map (·.file)
  let isLegacy (r : Read) : Bool := match r.reading with | .legacy _ => true | _ => false
  let plainLegacy := files fun r => isLegacy r && r.minority.isEmpty
  let mixedLegacy := reads.filter fun r => isLegacy r && !r.minority.isEmpty
  let strays := files fun r => r.reading == .utf8 && !r.minority.isEmpty
  let utf8Files := files fun r => (r.reading == .utf8 && r.minority.isEmpty) || r.reading == .replaced
  let utf16Files := files fun r => match r.reading with | .utf16 _ => true | _ => false
  let asciiFiles := files (·.reading == .ascii)
  let parts :=
    (if plainLegacy.isEmpty then [] else
      [s!"{names plainLegacy} {agree plainLegacy "reads" "read"} as {e.name}"]) ++
    (mixedLegacy.toList.map fun r =>
      let where_ := if r.minority.size == 1 then "offset" else "offsets"
      s!"'{r.file}' reads as {e.name}, though its bytes at {where_} {offsetList r.minority} \
are well-formed UTF-8 too") ++
    (if strays.isEmpty then [] else
      [s!"{names strays} {agree strays "is" "are"} UTF-8 but for the bytes read as {e.name}"]) ++
    (if utf8Files.isEmpty then [] else
      [s!"{names utf8Files} {agree utf8Files "is" "are"} UTF-8, so the declaration is not \
applied to {agree utf8Files "it" "them"}"]) ++
    (if utf16Files.isEmpty then [] else
      [s!"{names utf16Files} {agree utf16Files "is" "are"} UTF-16 by \
{agree utf16Files "its" "their"} byte-order mark"])
  let legacyFiles := plainLegacy ++ mixedLegacy.map (·.file)
  let actions :=
    (if legacyFiles.isEmpty then [] else
      [s!"save {names legacyFiles} as UTF-8 (`iconv -f {e.iconv} -t UTF-8`)"]) ++
    (if strays.isEmpty then [] else
      [s!"spell in UTF-8 the bytes {names strays} {agree strays "reads" "read"} as {e.name}"])
  let check := if mixedLegacy.isEmpty then "" else "check the text at those offsets, "
  let help := if actions.isEmpty then alikeHelp
    else check ++ ", and ".intercalate actions ++ ", then delete the declaration"
  if parts.isEmpty then
    (s!"{d.spelling} changes nothing: {names asciiFiles} {agree asciiFiles "is" "are"} ASCII, \
which reads alike in {e.name} and UTF-8", alikeHelp)
  else (s!"{d.spelling}: " ++ "; ".intercalate parts, help)

/-- The note under a declaration the engine has no table for: each file as
it read, and a help that converts the files in it before deleting it. -/
private def unreadNote (d : Declared) (reads : Array Read) : String × String :=
  let files (p : Read → Bool) : Array String := (reads.filter p).map (·.file)
  let replacedFiles := files (·.reading == .replaced)
  let utf8Files := files (·.reading == .utf8)
  let utf16Files := files fun r => match r.reading with | .utf16 _ => true | _ => false
  let asciiFiles := files (·.reading == .ascii)
  let parts :=
    (if replacedFiles.isEmpty then [] else
      [s!"{names replacedFiles} {agree replacedFiles "is" "are"} read as UTF-8, \
{agree replacedFiles "its" "their"} other bytes replaced"]) ++
    (if utf8Files.isEmpty then [] else
      [s!"{names utf8Files} {agree utf8Files "is" "are"} UTF-8"]) ++
    (if utf16Files.isEmpty then [] else
      [s!"{names utf16Files} {agree utf16Files "is" "are"} UTF-16 by \
{agree utf16Files "its" "their"} byte-order mark"]) ++
    (if asciiFiles.isEmpty || !(replacedFiles.isEmpty && utf8Files.isEmpty && utf16Files.isEmpty)
      then [] else
      [s!"{names asciiFiles} {agree asciiFiles "is" "are"} ASCII, which reads alike in it and \
UTF-8"])
  (s!"{d.spelling} names an encoding this engine does not read: " ++ "; ".intercalate parts,
    if replacedFiles.isEmpty then alikeHelp else
      s!"save {names replacedFiles} as UTF-8 (`iconv -f {d.option} -t UTF-8`), then delete the \
declaration")

/-- **N0025: what a declaration did**, once, at the declaration: each file
it governed and how that file read. The help follows the files: it saves
the ones that need the declaration before deleting it, and deletes it only
where no file does. -/
public def Ledger.notes (l : Ledger) : Array Diag :=
  match l.declared with
  | none => #[]
  | some d =>
    let reads := l.reads
    let note (mh : String × String) : Array Diag :=
      #[Diag.of .N0025 mh.1 (some d.span) (help := some mh.2)
        (subject := some ("usepackage:inputenc:" ++ d.option))]
    match d.choice with
    | .utf8 => #[]
    | .legacy e => note (legacyNote d e reads)
    | .unread => note (unreadNote d reads)

end LeanTex.Core.Encoding
