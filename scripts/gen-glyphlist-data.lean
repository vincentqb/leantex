/-
Regenerate LeanTex/Core/GlyphListData.lean from testdata/vendor/glyphlist (see its
PROVENANCE.txt), the PDF encodings with ISO 32000-2 Annex D.2's readings.
Usage: lake env lean --run scripts/gen-glyphlist-data.lean
-/

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def dir : System.FilePath := "testdata/vendor/glyphlist"

def output : System.FilePath := "LeanTex/Core/GlyphListData.lean"

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexValue (s : String) : Option Nat :=
  s.toList.foldl (fun acc c => do let a ← acc; let d ← hexDigit c; pure (a * 16 + d)) (some 0)

/-- The vendored sums, checked with `sha256sum -c` from the directory. -/
def checkSums : IO Unit := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["-c", "SHA256SUMS"], cwd := dir }
  unless out.exitCode == 0 do
    die s!"the vendored glyph list sources do not match SHA256SUMS:\n{out.stdout}{out.stderr}"

/-- The glyph list's data rows, verbatim. -/
def aglRows (text : String) : IO (Array String) := do
  let mut rows := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn ";" with
    | [name, scalars] =>
      for s in scalars.splitOn " " do
        unless s.length == 4 && (hexValue s).isSome do die s!"glyphlist: bad scalar in '{line}'"
      rows := rows.push s!"{name};{scalars}"
    | _ => die s!"glyphlist: unexpected row '{line}'"
  return rows

/-- StandardEncoding's names from 8a.enc: the 256 entries of its array. -/
def standardNames (text : String) : IO (Array String) := do
  let body := match text.splitOn "[" with
    | _ :: rest => "[".intercalate rest
    | [] => ""
  let body := (body.splitOn "]").headD ""
  let mut names := #[]
  for line in body.splitOn "\n" do
    let line := ((line.splitOn "%").headD "").trimAscii.toString
    for w in line.splitOn " " do
      if w.startsWith "/" then
        let n := (w.drop 1).toString
        names := names.push (if n == ".notdef" then "" else n)
  unless names.size == 256 do die s!"8a.enc: {names.size} names, expected 256"
  return names

/-- One Python string literal of a codec's decoding table: the scalar it
holds. -/
def pyScalar (lit : String) : Option Nat :=
  let cs := lit.toList
  match cs with
  | [q, c, q'] => if q == q' && (q == '\'' || q == '"') then some c.toNat else none
  | ['\'', '\\', '\\', '\''] => some 92
  | ['\'', '\\', 't', '\''] => some 9
  | ['\'', '\\', 'n', '\''] => some 10
  | ['\'', '\\', 'r', '\''] => some 13
  | ['\'', '\\', '\'', '\''] => some 39
  | '\'' :: '\\' :: 'x' :: rest =>
    match rest with
    | [a, b, '\''] => hexValue (String.ofList [a, b])
    | _ => none
  | '\'' :: '\\' :: 'u' :: rest =>
    match rest with
    | [a, b, c, d, '\''] => hexValue (String.ofList [a, b, c, d])
    | _ => none
  | _ => none

/-- The quoted literal a table row starts with, its quotes kept, a backslash escaping the
next character. -/
def leadingLiteral (line : String) : String := Id.run do
  let cs := line.toList
  match cs with
  | q :: rest =>
    let mut out := [q]
    let mut esc := false
    for c in rest do
      out := out ++ [c]
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == q then return String.ofList out
    return String.ofList out
  | [] => return ""

/-- A codec's decoding table: the 256 scalars, U+FFFE (undefined) as 0. -/
def codecTable (name text : String) : IO (Array Nat) := do
  let body := ((text.splitOn "decoding_table = (").getD 1 "")
  let body := (body.splitOn "\n)").headD ""
  let mut out := #[]
  for line in body.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    match pyScalar (leadingLiteral line) with
    | some v => out := out.push (if v == 0xFFFE then 0 else v)
    | none => die s!"{name}: unreadable table row '{line}'"
  unless out.size == 256 do die s!"{name}: {out.size} rows, expected 256"
  return out

/-- A JavaScript array of string literals, `const <name> = [ … ];`, as
pdf.js spells its tables: the strings in order. -/
def jsStrings (file name text : String) : IO (Array String) := do
  let body := match text.splitOn s!"const {name} = [" with
    | [_, rest] => (rest.splitOn "];").headD ""
    | _ => ""
  if body.isEmpty then die s!"{file}: no table {name}"
  let parts := (body.splitOn "\"").toArray
  let mut out := #[]
  for h : i in [0:parts.size] do
    if i % 2 == 1 then out := out.push parts[i]
    else unless (parts[i].toList.all fun c => c == ',' || c.isWhitespace) do
      die s!"{file}: {name} holds something other than strings: '{parts[i]}'"
  return out

def hex4 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (4 - s.length) ++ s.toUpper

def natArray (xs : Array Nat) : String := Id.run do
  let mut s := "#["
  for h : i in [0:xs.size] do
    if i > 0 then s := s ++ (if i % 8 == 0 then ",\n  " else ", ")
    s := s ++ "0x" ++ hex4 xs[i]
  return s ++ "]"

def stringArray (xs : Array String) : String := Id.run do
  let mut s := "#["
  for h : i in [0:xs.size] do
    if i > 0 then s := s ++ (if i % 6 == 0 then ",\n  " else ", ")
    s := s ++ "\"" ++ xs[i] ++ "\""
  return s ++ "]"

def main : IO Unit := do
  checkSums
  let agl ← aglRows (← IO.FS.readFile (dir / "glyphlist.txt"))
  let std ← standardNames (← IO.FS.readFile (dir / "8a.enc"))
  let cp ← codecTable "cp1252.py" (← IO.FS.readFile (dir / "cp1252.py"))
  let mac ← codecTable "mac_roman.py" (← IO.FS.readFile (dir / "mac_roman.py"))
  let bullet := 0x2022
  let win := cp.mapIdx fun code v =>
    if code == 0o240 then 0x0020
    else if code == 0o255 then 0x002D
    else if v == 0 && code > 0o40 then bullet
    else if code < 0o40 || code == 0o177 then (if code == 0o177 then bullet else 0)
    else v
  let mac := mac.mapIdx fun code v =>
    if code == 0o333 then 0x00A4
    else if code == 0o312 then 0x0020
    else if code < 0o40 || code == 0o177 then 0
    else v
  let encJs ← IO.FS.readFile (dir / "encodings.js")
  let cffJs ← IO.FS.readFile (dir / "cff_parser.js")
  let winNames ← jsStrings "encodings.js" "WinAnsiEncoding" encJs
  let macNames ← jsStrings "encodings.js" "MacRomanEncoding" encJs
  let expert ← jsStrings "encodings.js" "ExpertEncoding" encJs
  let stdJs ← jsStrings "encodings.js" "StandardEncoding" encJs
  let cffStrings ← jsStrings "cff_parser.js" "CFFStandardStrings" cffJs
  let macGlyphs ← jsStrings "fonts_utils.js" "MacStandardGlyphOrdering"
    (← IO.FS.readFile (dir / "fonts_utils.js"))
  unless macGlyphs.size == 258 && macGlyphs[0]? == some ".notdef" && macGlyphs[3]? == some "space" do
    die s!"fonts_utils.js: {macGlyphs.size} Macintosh glyph names, expected 258 from .notdef"
  for (n, xs) in [("WinAnsiEncoding", winNames), ("MacRomanEncoding", macNames),
      ("ExpertEncoding", expert), ("StandardEncoding", stdJs)] do
    unless xs.size == 256 do die s!"encodings.js: {n} has {xs.size} names, expected 256"
  unless stdJs == std do die "encodings.js: StandardEncoding differs from 8a.enc"
  unless cffStrings.size == 391 && cffStrings[0]? == some ".notdef" do
    die s!"cff_parser.js: {cffStrings.size} standard strings, expected 391 from .notdef"
  let text := String.intercalate "\n" [
    "module",
    "",
    "/-",
    "Generated by scripts/gen-glyphlist-data.lean; do not edit by hand. Regenerate with:",
    "  lake env lean --run scripts/gen-glyphlist-data.lean",
    "",
    "Sources, vendored in testdata/vendor/glyphlist (PROVENANCE.txt, SHA256SUMS):",
    "the Adobe Glyph List 2.0 (glyphlist.txt), Adobe StandardEncoding (8a.enc),",
    "Windows code page 1252 and Mac OS Roman (Python's cp1252 and mac_roman",
    "codecs), with the PDF's readings of the two applied as the generator's",
    "header says, and pdf.js's encoding names and CFF standard strings",
    "(encodings.js, cff_parser.js), and its standard Macintosh glyph names",
    "(fonts_utils.js). This module carries only data: `GlyphList`",
    "reads it, and its contracts are checked by the suite.",
    "-/",
    "",
    "namespace LeanTex.Core.GlyphListData",
    "",
    "/-- The Adobe Glyph List's rows, `name;XXXX`, one per line, in the list's order. -/",
    "public def agl : String := \"" ++ String.intercalate "\\n" agl.toList ++ "\"",
    "",
    "/-- StandardEncoding's glyph names by code; `.notdef` is the empty name. -/",
    "public def standardEncoding : Array String :=",
    "  " ++ stringArray std,
    "",
    "/-- WinAnsiEncoding's scalars by code; 0 for none. -/",
    "public def winAnsiEncoding : Array Nat :=",
    "  " ++ natArray win,
    "",
    "/-- MacRomanEncoding's scalars by code; 0 for none. -/",
    "public def macRomanEncoding : Array Nat :=",
    "  " ++ natArray mac,
    "",
    "/-- WinAnsiEncoding's glyph names by code; empty for none. -/",
    "public def winAnsiNames : Array String :=",
    "  " ++ stringArray winNames,
    "",
    "/-- MacRomanEncoding's glyph names by code; empty for none. -/",
    "public def macRomanNames : Array String :=",
    "  " ++ stringArray macNames,
    "",
    "/-- The CFF Expert encoding's glyph names by code; empty for none. -/",
    "public def expertNames : Array String :=",
    "  " ++ stringArray expert,
    "",
    "/-- The CFF standard strings by string identifier, 0 to 390. -/",
    "public def cffStandardStrings : Array String :=",
    "  " ++ stringArray cffStrings,
    "",
    "/-- The standard Macintosh glyph names by their 'post' table index, 0 to 257. -/",
    "public def macGlyphNames : Array String :=",
    "  " ++ stringArray macGlyphs,
    "",
    "end LeanTex.Core.GlyphListData",
    ""]
  IO.FS.writeFile output text
  IO.println s!"wrote {output}: {agl.size} glyph names, three encodings, their names, \
{cffStrings.size} CFF standard strings, {macGlyphs.size} Macintosh glyph names"
