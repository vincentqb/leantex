import Std.Data.HashMap

/-
Regenerate LeanTex/Core/NfcData.lean from UnicodeData.txt (the Unicode
Character Database file TeX Live ships in `unicode-data`). Run with:

  lake env lean --run scripts/gen-nfc-data.lean [source] [--output path]

Without a source argument the file is located via kpsewhich.
-/

def notice : String := "/-
Generated from UnicodeData.txt (Unicode Character Database); do not edit
by hand. Regenerate with: lake env lean --run scripts/gen-nfc-data.lean

The first three tables are what canonical normalization (UAX #15, NFC)
needs: combining classes, fully-expanded canonical decompositions, and
primary composites (canonical pairs minus the composition exclusions of
UAX #15 §5 and Unicode's CompositionExclusions.txt, whose listed
script-specific set is embedded in the generator; singleton and
non-starter exclusions are derived from the data). Hangul is algorithmic
(Unicode §3.12) and appears in no table. The last two are the general
categories' letter ranges (L*) and the simple lowercase mappings —
`Char.isAlpha`/`Char.toLower` are ASCII-only, and a word boundary that
excludes é neither hyphenates an accented word nor keeps it one box.

Every table is fixed-width lowercase hex with no separators, so the loader
addresses a field by byte offset instead of splitting and re-parsing text:
each entry's widths are on its own docstring below. The separated decimal
form this replaced was parsed when its module loaded, so every process
paid for it, ASCII-only documents included; this form is never split or
parsed, and a process builds the tables only when its text first needs
one (`Nfc.load`).

licence: UNICODE LICENSE V3 (Unicode data files); see
https://www.unicode.org/license.txt
-/
"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def defaultSource : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #["UnicodeData.txt"] }
  catch _ =>
    die "kpsewhich not found; pass the path to UnicodeData.txt"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die "kpsewhich could not find UnicodeData.txt"
  return path

/-- The listed (script-specific) composition exclusions: the codepoints of
CompositionExclusions.txt as of Unicode 3.2, frozen by stability policy —
post-3.1 additions (2ADC, 1D15E-1D164, 1D1BB-1D1C0) are non-starter or
singleton cases derived below, but are listed here too for robustness. -/
def listedExclusions : List (Nat × Nat) :=
  [(0x0958, 0x095F), (0x09DC, 0x09DD), (0x09DF, 0x09DF), (0x0A33, 0x0A33),
   (0x0A36, 0x0A36), (0x0A59, 0x0A5B), (0x0A5E, 0x0A5E), (0x0B5C, 0x0B5D),
   (0x0F43, 0x0F43), (0x0F4D, 0x0F4D), (0x0F52, 0x0F52), (0x0F57, 0x0F57),
   (0x0F5C, 0x0F5C), (0x0F69, 0x0F69), (0x0F76, 0x0F76), (0x0F78, 0x0F78),
   (0x0F93, 0x0F93), (0x0F9D, 0x0F9D), (0x0FA2, 0x0FA2), (0x0FA7, 0x0FA7),
   (0x0FAC, 0x0FAC), (0x0FB9, 0x0FB9), (0xFB1D, 0xFB1D), (0xFB1F, 0xFB1F),
   (0xFB2A, 0xFB36), (0xFB38, 0xFB3C), (0xFB3E, 0xFB3E), (0xFB40, 0xFB41),
   (0xFB43, 0xFB44), (0xFB46, 0xFB4E), (0x2ADC, 0x2ADC), (0x1D15E, 0x1D164),
   (0x1D1BB, 0x1D1C0)]

def isListedExcluded (cp : Nat) : Bool :=
  listedExclusions.any fun (a, b) => a ≤ cp && cp ≤ b

def hexToNat (s : String) : Nat := Id.run do
  let mut v := 0
  for c in s.toList do
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else 0
    v := v * 16 + d
  return v

/-- Full canonical decomposition: expand recursively (the mappings are
acyclic and shallow, so a fuel of 8 covers every chain in the UCD). -/
def expand (canon : Std.HashMap Nat (List Nat)) (fuel : Nat) (cp : Nat) : List Nat :=
  match fuel with
  | 0 => [cp]
  | fuel + 1 =>
    match canon.get? cp with
    | some parts => parts.flatMap (expand canon fuel)
    | none => [cp]

/-- Fixed-width lowercase hex, left-padded. The loader reads a field by
byte offset, so every field of a table is the same width and no separator
is emitted; `die` rather than truncate if a value does not fit. -/
def hexOf (width n : Nat) : IO String := do
  let ds := String.ofList (Nat.toDigits 16 n)
  if ds.length > width then
    die s!"{n} does not fit in {width} hex digits"
  return String.ofList (List.replicate (width - ds.length) '0') ++ ds

def main (args : List String) : IO UInt32 := do
  let mut source : Option String := none
  let mut output := "LeanTex/Core/NfcData.lean"
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--output" :: v :: more => output := v; rest := more
    | "--output" :: [] => die "'--output' needs a path"
    | a :: more => source := some a; rest := more
  let sourcePath ← match source with
    | some p => pure p
    | none => defaultSource
  let text ← IO.FS.readFile sourcePath
  let mut ccc : Array (Nat × Nat) := #[]
  let mut canon : Std.HashMap Nat (List Nat) := {}
  let mut letters : Array (Nat × Nat) := #[]   -- merged L* ranges
  let mut lower : Array (Nat × Nat) := #[]
  let mut rangeFirst : Option Nat := none
  for line in text.splitOn "\n" do
    let fields := line.splitOn ";"
    match fields with
    | code :: name :: cat :: cccF :: _bidi :: decompF :: tailFields =>
      let cp := hexToNat code
      if cp == 0 then continue
      if cat.startsWith "L" then
        if name.endsWith ", First>" then
          rangeFirst := some cp
        else
          let lo := if name.endsWith ", Last>" then rangeFirst.getD cp else cp
          rangeFirst := none
          match letters.back? with
          | some (a, b) =>
            if lo == b + 1 then letters := letters.pop.push (a, cp)
            else letters := letters.push (lo, cp)
          | none => letters := letters.push (lo, cp)
      if let some lc := tailFields[7]? then  -- field 13: simple lowercase
        let lc := lc.trimAscii.toString
        if !lc.isEmpty then
          lower := lower.push (cp, hexToNat lc)
      let c := cccF.toNat?.getD 0
      if c != 0 then
        ccc := ccc.push (cp, c)
      let d := decompF.trimAscii.toString
      -- A canonical decomposition has no <tag>; compatibility ones do.
      if !d.isEmpty && !d.startsWith "<" then
        canon := canon.insert cp ((d.splitOn " ").map hexToNat)
    | _ => pure ()
  let cccOf : Nat → Nat := fun cp =>
    (ccc.find? (·.1 == cp)).map (·.2) |>.getD 0
  -- Full canonical decomposition, recursively expanded.
  let mut decompEntries : Array (Nat × List Nat) := #[]
  for (cp, _) in canon.toList.toArray do
    decompEntries := decompEntries.push (cp, expand canon 8 cp)
  -- Primary composites: immediate canonical pairs, minus exclusions.
  -- UAX #15 §5: listed, singleton (1-element), and non-starter (the first
  -- element or the composite itself is a non-starter) decompositions.
  let mut compEntries : Array (Nat × Nat × Nat) := #[]
  for (cp, parts) in canon.toList.toArray do
    match parts with
    | [a, b] =>
      if !isListedExcluded cp && cccOf a == 0 && cccOf cp == 0 then
        compEntries := compEntries.push (a, b, cp)
    | _ => pure ()
  let mut cccStr := ""
  for (cp, c) in ccc do
    cccStr := cccStr ++ (← hexOf 6 cp) ++ (← hexOf 2 c)
  let mut decompStr := ""
  for (cp, parts) in decompEntries.qsort (fun a b => a.1 < b.1) do
    decompStr := decompStr ++ (← hexOf 6 cp) ++ (← hexOf 1 parts.length)
    for el in parts do
      decompStr := decompStr ++ (← hexOf 6 el)
  let mut compStr := ""
  for (a, b, cp) in compEntries.qsort
      (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 < y.2.1)) do
    compStr := compStr ++ (← hexOf 6 a) ++ (← hexOf 6 b) ++ (← hexOf 6 cp)
  let mut lettersStr := ""
  for (a, b) in letters do
    lettersStr := lettersStr ++ (← hexOf 6 a) ++ (← hexOf 6 b)
  let mut lowerStr := ""
  for (a, b) in lower do
    lowerStr := lowerStr ++ (← hexOf 6 a) ++ (← hexOf 6 b)
  let content := notice
    ++ "namespace LeanTex.Core.NfcData\n\n"
    ++ "/-- Nonzero canonical combining classes, 8 hex digits per entry:\n"
    ++ "6 for the codepoint, 2 for the class. Ascending by codepoint. -/\n"
    ++ s!"def ccc : String := \"{cccStr}\"\n\n"
    ++ "/-- Fully expanded canonical decompositions: 6 hex digits for the\n"
    ++ "codepoint, 1 for the element count, then 6 per element. Ascending by\n"
    ++ "codepoint; the only table whose entries differ in width. -/\n"
    ++ s!"def decomp : String := \"{decompStr}\"\n\n"
    ++ "/-- The primary composites of canonical composition, 18 hex digits\n"
    ++ "per entry: the two elements, then the composite. Ascending. -/\n"
    ++ s!"def comp : String := \"{compStr}\"\n\n"
    ++ "/-- The merged codepoint ranges of general category L*, 12 hex digits\n"
    ++ "per entry: low then high, inclusive. Ascending. -/\n"
    ++ s!"def letters : String := \"{lettersStr}\"\n\n"
    ++ "/-- The simple lowercase mappings, 12 hex digits per entry:\n"
    ++ "codepoint then its lowercase. Ascending. -/\n"
    ++ s!"def lower : String := \"{lowerStr}\"\n\n"
    ++ "end LeanTex.Core.NfcData\n"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}: {ccc.size} ccc, {decompEntries.size} decomps, \
{compEntries.size} composites, {letters.size} letter ranges, {lower.size} lowercase"
  return 0
