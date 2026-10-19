import scripts.GenData
import Std.Data.HashMap

open GenData

/-
Regenerate LeanTex/Core/CaseUpperData.lean from UnicodeData.txt and SpecialCasing.txt (TeX Live's
`unicode-data`, found with kpsewhich without a source).
Usage: lake build scripts.GenData && lake env lean --run scripts/gen-caseupper-data.lean [unicodedata specialcasing] [--output path]
-/

def notice (version : String) : String := s!"/-
Generated from UnicodeData.txt and {version} (Unicode Character Database); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-caseupper-data.lean

Full uppercase mapping: SpecialCasing's unconditional mappings over UnicodeData's simple uppercase.
The table is fixed-width lowercase hex with no separators, read by byte offset when a process first
maps a character (`CaseFold.load`).

licence: UNICODE LICENSE V3 (Unicode data files); see
https://www.unicode.org/license.txt
-/
"

def hexToNat (s : String) : Nat := Id.run do
  let mut v := 0
  for c in s.toList do
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else 0
    v := v * 16 + d
  return v

/-- Fixed-width lowercase hex, left-padded; a value that does not fit dies. -/
def hexOf (width n : Nat) : IO String := do
  let ds := String.ofList (Nat.toDigits 16 n)
  if ds.length > width then
    die s!"{n} does not fit in {width} hex digits"
  return String.ofList (List.replicate (width - ds.length) '0') ++ ds

def main (args : List String) : IO UInt32 := do
  let (sources, output) ← match args with
    | [] => pure (none, "LeanTex/Core/CaseUpperData.lean")
    | ["--output", o] => pure (none, o)
    | [u, s] => pure (some (u, s), "LeanTex/Core/CaseUpperData.lean")
    | [u, s, "--output", o] => pure (some (u, s), o)
    | _ => die "usage: gen-caseupper-data.lean [unicodedata specialcasing] [--output path]"
  let (dataPath, specialPath) ← match sources with
    | some p => pure p
    | none => pure (← locate "UnicodeData.txt" "pass the paths to UnicodeData.txt and SpecialCasing.txt",
        ← locate "SpecialCasing.txt" "pass the paths to UnicodeData.txt and SpecialCasing.txt")
  let mut upper : Std.HashMap Nat (List Nat) := {}
  for line in (← IO.FS.readFile dataPath).splitOn "\n" do
    let fields := (line.splitOn ";").toArray
    if fields.size ≥ 13 && !(fields[12]!.isEmpty) then
      upper := upper.insert (hexToNat fields[0]!) [hexToNat fields[12]!]
  if upper.isEmpty then die s!"no uppercase mapping in {dataPath}"
  let special ← IO.FS.readFile specialPath
  let version := ((special.splitOn "\n").headD "").drop 2 |>.trimAscii.toString
  let mut overrides := 0
  for line in special.splitOn "\n" do
    let body := ((line.splitOn "#").headD "").trimAscii.toString
    match (body.splitOn ";").map (·.trimAscii.toString) with
    | [code, _, _, mapping, ""] =>
      let parts := (mapping.splitOn " ").filter (!·.isEmpty) |>.map hexToNat
      let cp := hexToNat code
      if parts == [cp] then upper := upper.erase cp else upper := upper.insert cp parts
      overrides := overrides + 1
    | _ => pure ()
  if overrides == 0 then die s!"no unconditional mapping in {specialPath}"
  let mut table := ""
  let entries := upper.toArray.qsort (fun a b => a.1 < b.1)
  for (cp, parts) in entries do
    table := table ++ (← hexOf 6 cp) ++ (← hexOf 1 parts.length)
    for p in parts do
      table := table ++ (← hexOf 6 p)
  let header := notice version
  let content := "module\n\n" ++ header
    ++ "namespace LeanTex.Core.CaseUpperData\n\n"
    ++ "/-- The full uppercase mappings: 6 hex digits for the codepoint, 1 for the count of the\n"
    ++ "characters it maps to, then 6 per character. Ascending by codepoint. -/\n"
    ++ s!"public def upper : String := \"{table}\"\n\n"
    ++ "end LeanTex.Core.CaseUpperData\n"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}: {entries.size} uppercase mappings from UnicodeData.txt and {version}"
  return 0
