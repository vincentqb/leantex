/-
Regenerate LeanTex/Core/TextSymData.lean: the text symbols and accents
lualatex sets under the TU encoding, each with its Unicode scalar. Run from
the repository root with:

  lake env lean --run scripts/gen-textsym-data.lean

Sources, located with kpsewhich and never vendored:
- tuenc.def (the LaTeX kernel's TU encoding, the one lualatex's fontspec
  selects): `\DeclareUnicodeSymbol{\name}{"hex}` is the scalar a symbol
  command sets; `\DeclareUnicodeCommand{\name}{\iffontchar\font "hex \char
  "hex \else …}` sets that scalar wherever the face carries it;
  `\DeclareUnicodeAccent{\a}{"hex}` is the combining mark an accent command
  adds to its base; `\DeclareUnicodeComposite{\a}{}{"hex}` is what an accent
  over an empty base sets.
- latex.ltx: `\DeclareRobustCommand{\name}{\ifmmode … \else\textsym\fi}` and
  `\protected\def\name{…}` of that shape name a symbol's text form (`\S` is
  `\textsection`); `\let\name\other` aliases a name already found;
  `\DeclareTextCommandDefault\capital…{\a}` (or `{\@tabacckludge a}`) makes a
  capital accent the accent `\a`.

Not rows: a command tuenc.def defines through `\remove@tlig` (a quote the
TeX ligatures must not reach), and a format character — U+200C, whose one
meaning is to break a ligature the engine never forms (Font.lean reads no
ligature lookup).
-/

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def locate (file : String) : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #[file] }
  catch _ =>
    die s!"kpsewhich not found; it locates {file}"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die s!"kpsewhich could not find {file}"
  return path

/-- The file with every TeX comment removed, its lines kept. -/
def uncommented (text : String) : String := Id.run do
  let mut out := ""
  for line in text.splitOn "\n" do
    let mut prev := ' '
    for c in line.toList do
      if c == '%' && prev != '\\' then break
      out := out.push c
      prev := c
    out := out.push '\n'
  return out

/-- The control sequence at `cs[i]` (a backslash): a control word, or one
non-letter; the name and the index after it. -/
def ctrlAt (cs : Array Char) (i : Nat) : Option (String × Nat) := Id.run do
  if cs[i]? != some '\\' then return none
  let mut j := i + 1
  let mut name := ""
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c =>
      if c.isAlpha || c == '@' then
        name := name.push c
        j := j + 1
      else break
    | none => break
  if name.isEmpty then
    return cs[i + 1]?.map fun c => (String.ofList [c], i + 2)
  return some (name, j)

def skipWs (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c => if c.isWhitespace then j := j + 1 else break
    | none => break
  return j

/-- The balanced group opening at `cs[i]`: its body and the index after it. -/
def groupAt (cs : Array Char) (i : Nat) : Option (String × Nat) := Id.run do
  if cs[i]? != some '{' then return none
  let mut depth := 0
  let mut body := ""
  let mut j := i
  for _ in [0:cs.size] do
    match cs[j]? with
    | some c =>
      if c == '{' then
        depth := depth + 1
        if depth > 1 then body := body.push c
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then return some (body, j + 1)
        body := body.push c
      else body := body.push c
      j := j + 1
    | none => return none
  return none

/-- A declaration's name argument: `{\name}` or a bare `\name`. -/
def nameArg (cs : Array Char) (i : Nat) : Option (String × Nat) := do
  let i := skipWs cs i
  if cs[i]? == some '{' then
    let (body, j) ← groupAt cs i
    let bcs := body.trimAscii.toString.toList.toArray
    let (n, k) ← ctrlAt bcs 0
    if k == bcs.size then some (n, j) else none
  else ctrlAt cs i

/-- `"hex` as a scalar. -/
def hexScalar (s : String) : Option Char := do
  let t := s.trimAscii.toString
  guard (t.startsWith "\"")
  let digits := (t.drop 1).toString
  guard (!digits.isEmpty && digits.all fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f'))
  let v := digits.foldl (fun acc c =>
    acc * 16 + (if c.isDigit then c.toNat - '0'.toNat
      else c.toLower.toNat - 'a'.toNat + 10)) 0
  guard (v < 0x110000 && !(0xD800 ≤ v && v ≤ 0xDFFF))
  some (Char.ofNat v)

/-- Every occurrence of the control word `\word` in the file: the index after it. -/
def occurrences (cs : Array Char) (word : String) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:cs.size] do
    if cs[i]! == '\\' then
      if let some (n, j) := ctrlAt cs i then
        if n == word then out := out.push j
  return out

/-- A body `\iffontchar\font "hex \char "hex \else …`: the scalar it sets
where the face carries it. -/
def fontcharScalar (body : String) : Option Char := do
  let words := ((body.replace "\\" " \\").replace "\"" " \"").splitOn " "
    |>.flatMap (·.splitOn "\n") |>.filter (!·.isEmpty)
  match words with
  | "\\iffontchar" :: "\\font" :: rest =>
    let hex := rest.takeWhile (!·.startsWith "\\")
    let v ← hexScalar (String.join hex)
    let afterChar := (rest.dropWhile (· != "\\char")).drop 1
    let v2 ← hexScalar (String.join (afterChar.takeWhile (!·.startsWith "\\")))
    if v == v2 then some v else none
  | _ => none

/-- The text branch of `\ifmmode … \else\name\fi`: the one control word it
sets. -/
def textBranch (body : String) : Option String := do
  let b := body.trimAscii.toString
  guard (b.startsWith "\\ifmmode" && b.endsWith "\\fi")
  let parts := b.splitOn "\\else"
  guard (parts.length == 2)
  let t := ((parts.getD 1 "").dropEnd 3).toString.trimAscii.toString
  let tcs := t.toList.toArray
  let (n, k) ← ctrlAt tcs 0
  if k == tcs.size then some n else none

def hex4 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n) |>.toUpper
  String.ofList (List.replicate (4 - s.length) '0') ++ s

def charLit (c : Char) : String :=
  if c.toNat < 0x10000 then s!"'\\u{hex4 c.toNat}'" else s!"'{String.ofList [c]}'"

def strLit (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- The file's `\ProvidesFile{name} [date version …]` stamp, or the
kernel's `\fmtversion` when it has none; each may span lines. -/
def provides (text : String) : String :=
  let squash (s : String) : String :=
    " ".intercalate ((s.splitOn " ").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
      |>.flatMap (·.splitOn "\n") |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty))
  match (text.splitOn "\\ProvidesFile{")[1]? with
  | some rest =>
    let file := (rest.splitOn "}").headD ""
    let tail := ((rest.splitOn "[")[1]?).getD ""
    s!"{file} {squash ((tail.splitOn "]").headD "")}"
  | none =>
    match (text.splitOn "\\edef\\fmtversion")[1]? with
    | some rest => s!"latex.ltx {squash (((rest.splitOn "{")[1]?).getD "" |>.splitOn "}" |>.headD "")}"
    | none => "(no version line)"

def formatChars : List Char := ['\u200C']

def main : IO UInt32 := do
  let tuText ← IO.FS.readFile (← locate "tuenc.def")
  let ltxText ← IO.FS.readFile (← locate "latex.ltx")
  let tu := (uncommented tuText).toList.toArray
  let ltx := (uncommented ltxText).toList.toArray
  let mut syms : Array (String × Char) := #[]
  let mut accents : Array (String × Char) := #[]
  let mut empties : Array (String × Char) := #[]
  let mut composites : Array (String × String × Char) := #[]
  let push (xs : Array (String × Char)) (n : String) (v : Char) : Array (String × Char) :=
    if xs.any (·.1 == n) || formatChars.contains v || n.any (· == '@') then xs
    else xs.push (n, v)
  for j in occurrences tu "DeclareUnicodeSymbol" do
    if let some (n, k) := nameArg tu j then
      if let some (hex, _) := groupAt tu (skipWs tu k) then
        if let some v := hexScalar hex then syms := push syms n v
  for j in occurrences tu "DeclareUnicodeCommand" do
    if let some (n, k) := nameArg tu j then
      if let some (body, _) := groupAt tu (skipWs tu k) then
        if let some v := fontcharScalar body then syms := push syms n v
  for j in occurrences tu "DeclareUnicodeAccent" do
    if let some (n, k) := nameArg tu j then
      if let some (hex, _) := groupAt tu (skipWs tu k) then
        if let some v := hexScalar hex then accents := push accents n v
  for j in occurrences tu "DeclareUnicodeComposite" do
    if let some (n, k) := nameArg tu j then
      let b := skipWs tu k
      let base? : Option (String × Nat) :=
        if tu[b]? == some '{' then groupAt tu b
        else (ctrlAt tu b).map fun (c, e) => ("\\" ++ c, e)
      if let some (base, k2) := base? then
        if let some (hex, _) := groupAt tu (skipWs tu k2) then
          if let some v := hexScalar hex then
            if base.trimAscii.isEmpty then empties := push empties n v
            else unless composites.any (fun c => c.1 == n && c.2.1 == base) do
              composites := composites.push (n, base, v)
  -- A composite of a command that is not an accent (`\textcommabelow`, an
  -- overlay construction) is not an accent's row.
  composites := composites.filter fun c => accents.any (·.1 == c.1)
  let tuSyms := syms
  let aliasOf (target : String) (xs : Array (String × Char)) : Option Char :=
    (xs.find? (·.1 == target)).map (·.2)
  for word in ["DeclareRobustCommand", "def"] do
    for j in occurrences ltx word do
      if let some (n, k) := nameArg ltx j then
        if let some (body, _) := groupAt ltx (skipWs ltx k) then
          if let some t := textBranch body then
            if let some v := aliasOf t tuSyms then syms := push syms n v
  for j in occurrences ltx "let" do
    if let some (n, k) := ctrlAt ltx (skipWs ltx j) then
      if let some (t, _) := ctrlAt ltx k then
        if let some v := aliasOf t syms then
          unless tuSyms.any (·.1 == n) do syms := push syms n v
  for j in occurrences ltx "DeclareTextCommandDefault" do
    if let some (n, k) := ctrlAt ltx (skipWs ltx j) then
      if n.startsWith "capital" then
        if let some (body, _) := groupAt ltx (skipWs ltx k) then
          let b := (body.replace "\\@tabacckludge" "").trimAscii.toString
          let target := if b.startsWith "\\" then (b.drop 1).toString else b
          if let some v := aliasOf target accents then accents := push accents n v
  if syms.size < 100 || accents.size < 15 then
    die s!"read {syms.size} symbols and {accents.size} accents: the sources changed shape"
  let rows (xs : Array (String × Char)) : String :=
    String.intercalate ",\n   " (xs.toList.map fun (n, v) => s!"({strLit n}, {charLit v})")
  let out := s!"/-
Generated by scripts/gen-textsym-data.lean; do not edit by hand. Regenerate with:
  lake env lean --run scripts/gen-textsym-data.lean

Sources, read from the TeX tree and never vendored:
- {provides tuText}
- {provides ltxText}
Each row is a command and the scalar lualatex sets for it under the TU
encoding; the rules that read them are the generator's header. This module
carries only data: the elaborator reads it through `Elab.escapeOf` and
`Bib.accentOf`, and its contracts are checked by the suite.
-/

namespace LeanTex.Core.TextSymData

/-- The symbol commands: tuenc.def's, then the kernel names that set one of
them in text. -/
def symbols : List (String × Char) :=
  [{rows syms}]

/-- The accent commands and the combining mark each adds to its base. -/
def accents : List (String × Char) :=
  [{rows accents}]

/-- What an accent over an empty base sets. -/
def emptyBase : List (String × Char) :=
  [{rows empties}]

/-- tuenc.def's composites: an accent, its base (a letter, or `\\i`), and the
precomposed scalar it names. The engine composes by NFC instead; the suite
holds that route to every row here. -/
def composites : List (String × String × Char) :=
  [{String.intercalate ",\n   " (composites.toList.map fun (n, b, v) =>
      s!"({strLit n}, {strLit b}, {charLit v})")}]

end LeanTex.Core.TextSymData
"
  IO.FS.writeFile "LeanTex/Core/TextSymData.lean" out
  IO.println s!"wrote LeanTex/Core/TextSymData.lean: {syms.size} symbols, {accents.size} accents, \
{empties.size} empty-base composites, {composites.size} composites"
  return 0
